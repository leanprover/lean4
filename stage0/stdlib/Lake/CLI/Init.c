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
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
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
uint8_t l_String_instDecidableLtRaw___aux__1(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__1___boxed(lean_object*, lean_object*);
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
lean_inc(v___y_448_);
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
lean_inc(v___y_455_);
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
lean_inc(v___y_462_);
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
lean_inc(v___y_469_);
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
lean_inc(v___y_476_);
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
v___x_592_ = lean_panic_fn_borrowed(v___x_591_, v_msg_590_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(lean_object* v_as_847_, size_t v_i_848_, size_t v_stop_849_, lean_object* v_b_850_, lean_object* v___y_851_){
_start:
{
uint8_t v___x_853_; 
v___x_853_ = lean_usize_dec_eq(v_i_848_, v_stop_849_);
if (v___x_853_ == 0)
{
lean_object* v___x_854_; lean_object* v___x_855_; size_t v___x_856_; size_t v___x_857_; 
v___x_854_ = lean_array_uget_borrowed(v_as_847_, v_i_848_);
lean_inc_ref(v___y_851_);
lean_inc(v___x_854_);
v___x_855_ = lean_apply_2(v___y_851_, v___x_854_, lean_box(0));
v___x_856_ = ((size_t)1ULL);
v___x_857_ = lean_usize_add(v_i_848_, v___x_856_);
v_i_848_ = v___x_857_;
v_b_850_ = v___x_855_;
goto _start;
}
else
{
lean_object* v___x_859_; 
v___x_859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_859_, 0, v_b_850_);
return v___x_859_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0___boxed(lean_object* v_as_860_, lean_object* v_i_861_, lean_object* v_stop_862_, lean_object* v_b_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
size_t v_i_boxed_866_; size_t v_stop_boxed_867_; lean_object* v_res_868_; 
v_i_boxed_866_ = lean_unbox_usize(v_i_861_);
lean_dec(v_i_861_);
v_stop_boxed_867_ = lean_unbox_usize(v_stop_862_);
lean_dec(v_stop_862_);
v_res_868_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_as_860_, v_i_boxed_866_, v_stop_boxed_867_, v_b_863_, v___y_864_);
lean_dec_ref(v___y_864_);
lean_dec_ref(v_as_860_);
return v_res_868_;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7(void){
_start:
{
lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_882_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_883_ = lean_array_get_size(v___x_882_);
return v___x_883_;
}
}
static uint8_t _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8(void){
_start:
{
lean_object* v___x_884_; lean_object* v___x_885_; uint8_t v___x_886_; 
v___x_884_ = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7);
v___x_885_ = lean_unsigned_to_nat(0u);
v___x_886_ = lean_nat_dec_lt(v___x_885_, v___x_884_);
return v___x_886_;
}
}
static uint8_t _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9(void){
_start:
{
lean_object* v___x_887_; uint8_t v___x_888_; 
v___x_887_ = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7);
v___x_888_ = lean_nat_dec_le(v___x_887_, v___x_887_);
return v___x_888_;
}
}
static size_t _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10(void){
_start:
{
lean_object* v___x_889_; size_t v___x_890_; 
v___x_889_ = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7);
v___x_890_ = lean_usize_of_nat(v___x_889_);
return v___x_890_;
}
}
static uint8_t _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13(void){
_start:
{
lean_object* v___x_895_; lean_object* v___x_896_; uint8_t v___x_897_; 
v___x_895_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___closed__0));
v___x_896_ = l_Lake_Git_upstreamBranch;
v___x_897_ = lean_string_dec_eq(v___x_896_, v___x_895_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg(lean_object* v_dir_905_, lean_object* v_name_906_, uint8_t v_tmp_907_, uint8_t v_lang_908_, lean_object* v_env_909_, uint8_t v_offline_910_, lean_object* v_a_911_){
_start:
{
lean_object* v___x_916_; lean_object* v___y_918_; lean_object* v___y_935_; lean_object* v___y_936_; lean_object* v___y_940_; lean_object* v___y_941_; lean_object* v___y_945_; lean_object* v___y_946_; uint8_t v_a_947_; lean_object* v___y_951_; lean_object* v___y_952_; lean_object* v___y_953_; lean_object* v___y_954_; lean_object* v___y_1024_; lean_object* v___y_1025_; lean_object* v___y_1026_; lean_object* v___y_1027_; lean_object* v___y_1031_; lean_object* v___y_1032_; lean_object* v___y_1033_; lean_object* v___y_1034_; lean_object* v___y_1035_; lean_object* v___y_1037_; lean_object* v___y_1038_; lean_object* v___y_1039_; lean_object* v___y_1040_; lean_object* v___y_1069_; lean_object* v___y_1070_; lean_object* v___y_1071_; lean_object* v___y_1072_; lean_object* v___y_1073_; lean_object* v___y_1075_; lean_object* v___y_1076_; lean_object* v___y_1077_; lean_object* v___y_1078_; uint8_t v_a_1079_; lean_object* v___y_1106_; lean_object* v___y_1107_; lean_object* v___y_1108_; lean_object* v___y_1109_; lean_object* v___y_1122_; lean_object* v___y_1123_; lean_object* v___y_1124_; lean_object* v___y_1125_; lean_object* v___y_1126_; lean_object* v___y_1127_; lean_object* v___y_1143_; lean_object* v___y_1144_; lean_object* v___y_1145_; lean_object* v___y_1146_; lean_object* v___y_1147_; uint8_t v_a_1148_; lean_object* v___y_1156_; lean_object* v___y_1157_; lean_object* v___y_1158_; lean_object* v___y_1159_; lean_object* v___y_1174_; lean_object* v___y_1175_; lean_object* v___y_1176_; lean_object* v___y_1177_; lean_object* v___y_1178_; lean_object* v___y_1179_; uint8_t v_a_1180_; lean_object* v___y_1214_; lean_object* v___y_1215_; lean_object* v___y_1216_; lean_object* v___y_1217_; lean_object* v___y_1218_; lean_object* v___y_1233_; lean_object* v___y_1234_; lean_object* v___y_1235_; lean_object* v___y_1236_; lean_object* v___y_1237_; lean_object* v___y_1239_; lean_object* v___y_1240_; lean_object* v___y_1241_; lean_object* v___y_1242_; lean_object* v___y_1243_; lean_object* v___y_1244_; lean_object* v___y_1245_; lean_object* v___y_1261_; lean_object* v___y_1262_; lean_object* v___y_1263_; lean_object* v___y_1264_; lean_object* v___y_1265_; lean_object* v___y_1266_; lean_object* v___y_1274_; lean_object* v___y_1275_; lean_object* v___y_1276_; lean_object* v___y_1277_; lean_object* v___y_1278_; lean_object* v___y_1279_; lean_object* v___y_1280_; uint8_t v_a_1281_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v_configFile_1313_; lean_object* v___y_1315_; lean_object* v___y_1316_; lean_object* v___y_1317_; lean_object* v___y_1318_; lean_object* v___y_1319_; lean_object* v_fst_1352_; lean_object* v_snd_1353_; lean_object* v___y_1361_; lean_object* v___y_1362_; uint8_t v_a_1363_; lean_object* v___y_1367_; lean_object* v___y_1368_; uint8_t v___y_1369_; lean_object* v___y_1385_; lean_object* v___y_1386_; uint8_t v_a_1387_; lean_object* v___y_1405_; uint8_t v___x_1406_; lean_object* v___x_1439_; uint8_t v___x_1440_; 
v___x_916_ = l_Lake_defaultConfigFile;
v___x_1311_ = l_Lake_ConfigLang_fileExtension(v_lang_908_);
v___x_1312_ = l_System_FilePath_addExtension(v___x_916_, v___x_1311_);
lean_dec_ref(v___x_1311_);
lean_inc_ref(v_dir_905_);
v_configFile_1313_ = l_Lake_joinRelative(v_dir_905_, v___x_1312_);
v___x_1406_ = l_System_FilePath_pathExists(v_configFile_1313_);
v___x_1439_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1440_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1440_ == 0)
{
goto v___jp_1407_;
}
else
{
lean_object* v___x_1441_; uint8_t v___x_1442_; 
v___x_1441_ = lean_box(0);
v___x_1442_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (v___x_1442_ == 0)
{
if (v___x_1440_ == 0)
{
goto v___jp_1407_;
}
else
{
size_t v___x_1443_; size_t v___x_1444_; lean_object* v___x_1445_; 
v___x_1443_ = ((size_t)0ULL);
v___x_1444_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
v___x_1445_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1439_, v___x_1443_, v___x_1444_, v___x_1441_, v_a_911_);
if (lean_obj_tag(v___x_1445_) == 0)
{
lean_dec_ref(v___x_1445_);
goto v___jp_1407_;
}
else
{
lean_dec_ref(v_configFile_1313_);
lean_dec_ref(v_env_909_);
lean_dec(v_name_906_);
lean_dec_ref(v_dir_905_);
return v___x_1445_;
}
}
}
else
{
size_t v___x_1446_; size_t v___x_1447_; lean_object* v___x_1448_; 
v___x_1446_ = ((size_t)0ULL);
v___x_1447_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
v___x_1448_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1439_, v___x_1446_, v___x_1447_, v___x_1441_, v_a_911_);
if (lean_obj_tag(v___x_1448_) == 0)
{
lean_dec_ref(v___x_1448_);
goto v___jp_1407_;
}
else
{
lean_dec_ref(v_configFile_1313_);
lean_dec_ref(v_env_909_);
lean_dec(v_name_906_);
lean_dec_ref(v_dir_905_);
return v___x_1448_;
}
}
}
v___jp_913_:
{
lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_914_ = lean_box(0);
v___x_915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_915_, 0, v___x_914_);
return v___x_915_;
}
v___jp_917_:
{
if (v_offline_910_ == 0)
{
lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_919_ = lean_box(0);
v___x_920_ = lean_unsigned_to_nat(0u);
v___x_921_ = lean_box(0);
v___x_922_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__4));
lean_inc_ref(v_dir_905_);
v___x_923_ = l_Lake_joinRelative(v_dir_905_, v___x_922_);
lean_inc_ref(v___x_923_);
v___x_924_ = l_Lake_joinRelative(v___x_923_, v___x_916_);
v___x_925_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__0));
v___x_926_ = lean_box(1);
v___x_927_ = l_Lean_Options_empty;
v___x_928_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0));
v___x_929_ = lean_alloc_ctor(0, 14, 3);
lean_ctor_set(v___x_929_, 0, v_env_909_);
lean_ctor_set(v___x_929_, 1, v___x_919_);
lean_ctor_set(v___x_929_, 2, v_dir_905_);
lean_ctor_set(v___x_929_, 3, v___x_920_);
lean_ctor_set(v___x_929_, 4, v___x_921_);
lean_ctor_set(v___x_929_, 5, v___x_922_);
lean_ctor_set(v___x_929_, 6, v___x_923_);
lean_ctor_set(v___x_929_, 7, v___x_916_);
lean_ctor_set(v___x_929_, 8, v___x_924_);
lean_ctor_set(v___x_929_, 9, v___x_925_);
lean_ctor_set(v___x_929_, 10, v___x_926_);
lean_ctor_set(v___x_929_, 11, v___x_927_);
lean_ctor_set(v___x_929_, 12, v___x_928_);
lean_ctor_set(v___x_929_, 13, v___x_928_);
lean_ctor_set_uint8(v___x_929_, sizeof(void*)*14, v_offline_910_);
lean_ctor_set_uint8(v___x_929_, sizeof(void*)*14 + 1, v_offline_910_);
lean_ctor_set_uint8(v___x_929_, sizeof(void*)*14 + 2, v_offline_910_);
v___x_930_ = l_Lean_NameSet_empty;
v___x_931_ = l_Lake_updateManifest(v___x_929_, v___x_930_, v___y_918_);
return v___x_931_;
}
else
{
lean_object* v___x_932_; lean_object* v___x_933_; 
lean_dec_ref(v_env_909_);
lean_dec_ref(v_dir_905_);
v___x_932_ = lean_box(0);
v___x_933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_933_, 0, v___x_932_);
return v___x_933_;
}
}
v___jp_934_:
{
if (lean_obj_tag(v___y_936_) == 0)
{
lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_937_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__2));
lean_inc_ref(v___y_935_);
v___x_938_ = lean_apply_2(v___y_935_, v___x_937_, lean_box(0));
v___y_918_ = v___y_935_;
goto v___jp_917_;
}
else
{
lean_dec_ref(v___y_936_);
v___y_918_ = v___y_935_;
goto v___jp_917_;
}
}
v___jp_939_:
{
switch(v_tmp_907_)
{
case 3:
{
v___y_935_ = v___y_941_;
v___y_936_ = v___y_940_;
goto v___jp_934_;
}
case 4:
{
v___y_935_ = v___y_941_;
v___y_936_ = v___y_940_;
goto v___jp_934_;
}
default: 
{
lean_object* v___x_942_; lean_object* v___x_943_; 
lean_dec(v___y_940_);
lean_dec_ref(v_env_909_);
lean_dec_ref(v_dir_905_);
v___x_942_ = lean_box(0);
v___x_943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_943_, 0, v___x_942_);
return v___x_943_;
}
}
}
v___jp_944_:
{
if (v_a_947_ == 0)
{
lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_948_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__4));
lean_inc_ref(v___y_946_);
v___x_949_ = lean_apply_2(v___y_946_, v___x_948_, lean_box(0));
v___y_940_ = v___y_945_;
v___y_941_ = v___y_946_;
goto v___jp_939_;
}
else
{
v___y_940_ = v___y_945_;
v___y_941_ = v___y_946_;
goto v___jp_939_;
}
}
v___jp_950_:
{
lean_object* v___x_955_; lean_object* v___x_956_; uint8_t v___x_957_; lean_object* v___x_958_; 
v___x_955_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__5));
lean_inc_ref(v_dir_905_);
v___x_956_ = l_Lake_joinRelative(v_dir_905_, v___x_955_);
v___x_957_ = 4;
v___x_958_ = lean_io_prim_handle_mk(v___x_956_, v___x_957_);
lean_dec_ref(v___x_956_);
if (lean_obj_tag(v___x_958_) == 0)
{
lean_object* v_a_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
v_a_959_ = lean_ctor_get(v___x_958_, 0);
lean_inc(v_a_959_);
lean_dec_ref(v___x_958_);
v___x_960_ = l___private_Lake_CLI_Init_0__Lake_gitignoreContents;
v___x_961_ = lean_io_prim_handle_put_str(v_a_959_, v___x_960_);
lean_dec(v_a_959_);
if (lean_obj_tag(v___x_961_) == 0)
{
lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; uint8_t v___x_966_; 
lean_dec_ref(v___x_961_);
v___x_962_ = l_Lake_toolchainFileName;
lean_inc_ref(v_dir_905_);
v___x_963_ = l_Lake_joinRelative(v_dir_905_, v___x_962_);
v___x_964_ = lean_string_utf8_byte_size(v___y_951_);
v___x_965_ = lean_unsigned_to_nat(0u);
v___x_966_ = lean_nat_dec_eq(v___x_964_, v___x_965_);
if (v___x_966_ == 0)
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
lean_dec_ref(v___y_952_);
v___x_967_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__2));
v___x_968_ = lean_string_append(v___y_951_, v___x_967_);
v___x_969_ = l_IO_FS_writeFile(v___x_963_, v___x_968_);
lean_dec_ref(v___x_968_);
lean_dec_ref(v___x_963_);
if (lean_obj_tag(v___x_969_) == 0)
{
lean_dec_ref(v___x_969_);
v___y_940_ = v___y_953_;
v___y_941_ = v___y_954_;
goto v___jp_939_;
}
else
{
lean_object* v_a_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_982_; 
lean_dec(v___y_953_);
lean_dec_ref(v_env_909_);
lean_dec_ref(v_dir_905_);
v_a_970_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_982_ == 0)
{
v___x_972_ = v___x_969_;
v_isShared_973_ = v_isSharedCheck_982_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_a_970_);
lean_dec(v___x_969_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_982_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_974_; uint8_t v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_980_; 
v___x_974_ = lean_io_error_to_string(v_a_970_);
v___x_975_ = 3;
v___x_976_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_976_, 0, v___x_974_);
lean_ctor_set_uint8(v___x_976_, sizeof(void*)*1, v___x_975_);
lean_inc_ref(v___y_954_);
v___x_977_ = lean_apply_2(v___y_954_, v___x_976_, lean_box(0));
v___x_978_ = lean_box(0);
if (v_isShared_973_ == 0)
{
lean_ctor_set(v___x_972_, 0, v___x_978_);
v___x_980_ = v___x_972_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v___x_978_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
}
}
else
{
lean_object* v_githash_983_; lean_object* v___x_984_; uint8_t v___x_985_; 
lean_dec_ref(v___y_951_);
v_githash_983_ = lean_ctor_get(v___y_952_, 1);
lean_inc_ref(v_githash_983_);
lean_dec_ref(v___y_952_);
v___x_984_ = lean_string_utf8_byte_size(v_githash_983_);
lean_dec_ref(v_githash_983_);
v___x_985_ = lean_nat_dec_eq(v___x_984_, v___x_965_);
if (v___x_985_ == 0)
{
uint8_t v___x_986_; lean_object* v___x_987_; uint8_t v___x_988_; 
v___x_986_ = l_System_FilePath_pathExists(v___x_963_);
lean_dec_ref(v___x_963_);
v___x_987_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_988_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_988_ == 0)
{
v___y_945_ = v___y_953_;
v___y_946_ = v___y_954_;
v_a_947_ = v___x_986_;
goto v___jp_944_;
}
else
{
lean_object* v___x_989_; uint8_t v___x_990_; 
v___x_989_ = lean_box(0);
v___x_990_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (v___x_990_ == 0)
{
if (v___x_988_ == 0)
{
v___y_945_ = v___y_953_;
v___y_946_ = v___y_954_;
v_a_947_ = v___x_986_;
goto v___jp_944_;
}
else
{
size_t v___x_991_; size_t v___x_992_; lean_object* v___x_993_; 
v___x_991_ = ((size_t)0ULL);
v___x_992_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
v___x_993_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_987_, v___x_991_, v___x_992_, v___x_989_, v___y_954_);
if (lean_obj_tag(v___x_993_) == 0)
{
lean_dec_ref(v___x_993_);
v___y_945_ = v___y_953_;
v___y_946_ = v___y_954_;
v_a_947_ = v___x_986_;
goto v___jp_944_;
}
else
{
lean_dec(v___y_953_);
lean_dec_ref(v_env_909_);
lean_dec_ref(v_dir_905_);
return v___x_993_;
}
}
}
else
{
size_t v___x_994_; size_t v___x_995_; lean_object* v___x_996_; 
v___x_994_ = ((size_t)0ULL);
v___x_995_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
v___x_996_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_987_, v___x_994_, v___x_995_, v___x_989_, v___y_954_);
if (lean_obj_tag(v___x_996_) == 0)
{
lean_dec_ref(v___x_996_);
v___y_945_ = v___y_953_;
v___y_946_ = v___y_954_;
v_a_947_ = v___x_986_;
goto v___jp_944_;
}
else
{
lean_dec(v___y_953_);
lean_dec_ref(v_env_909_);
lean_dec_ref(v_dir_905_);
return v___x_996_;
}
}
}
}
else
{
lean_dec_ref(v___x_963_);
v___y_940_ = v___y_953_;
v___y_941_ = v___y_954_;
goto v___jp_939_;
}
}
}
else
{
lean_object* v_a_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1009_; 
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
lean_dec_ref(v___y_951_);
lean_dec_ref(v_env_909_);
lean_dec_ref(v_dir_905_);
v_a_997_ = lean_ctor_get(v___x_961_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_999_ = v___x_961_;
v_isShared_1000_ = v_isSharedCheck_1009_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_a_997_);
lean_dec(v___x_961_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1009_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1001_; uint8_t v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1007_; 
v___x_1001_ = lean_io_error_to_string(v_a_997_);
v___x_1002_ = 3;
v___x_1003_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1003_, 0, v___x_1001_);
lean_ctor_set_uint8(v___x_1003_, sizeof(void*)*1, v___x_1002_);
lean_inc_ref(v___y_954_);
v___x_1004_ = lean_apply_2(v___y_954_, v___x_1003_, lean_box(0));
v___x_1005_ = lean_box(0);
if (v_isShared_1000_ == 0)
{
lean_ctor_set(v___x_999_, 0, v___x_1005_);
v___x_1007_ = v___x_999_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v___x_1005_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
}
else
{
lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1022_; 
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
lean_dec_ref(v___y_951_);
lean_dec_ref(v_env_909_);
lean_dec_ref(v_dir_905_);
v_a_1010_ = lean_ctor_get(v___x_958_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1012_ = v___x_958_;
v_isShared_1013_ = v_isSharedCheck_1022_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_dec(v___x_958_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1022_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___x_1014_; uint8_t v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1020_; 
v___x_1014_ = lean_io_error_to_string(v_a_1010_);
v___x_1015_ = 3;
v___x_1016_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1016_, 0, v___x_1014_);
lean_ctor_set_uint8(v___x_1016_, sizeof(void*)*1, v___x_1015_);
lean_inc_ref(v___y_954_);
v___x_1017_ = lean_apply_2(v___y_954_, v___x_1016_, lean_box(0));
v___x_1018_ = lean_box(0);
if (v_isShared_1013_ == 0)
{
lean_ctor_set(v___x_1012_, 0, v___x_1018_);
v___x_1020_ = v___x_1012_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v___x_1018_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
}
v___jp_1023_:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1028_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12));
lean_inc_ref(v___y_1024_);
v___x_1029_ = lean_apply_2(v___y_1024_, v___x_1028_, lean_box(0));
v___y_951_ = v___y_1025_;
v___y_952_ = v___y_1026_;
v___y_953_ = v___y_1027_;
v___y_954_ = v___y_1024_;
goto v___jp_950_;
}
v___jp_1030_:
{
if (lean_obj_tag(v___y_1035_) == 0)
{
lean_dec_ref(v___y_1035_);
v___y_951_ = v___y_1032_;
v___y_952_ = v___y_1033_;
v___y_953_ = v___y_1034_;
v___y_954_ = v___y_1031_;
goto v___jp_950_;
}
else
{
lean_dec_ref(v___y_1035_);
v___y_1024_ = v___y_1031_;
v___y_1025_ = v___y_1032_;
v___y_1026_ = v___y_1033_;
v___y_1027_ = v___y_1034_;
goto v___jp_1023_;
}
}
v___jp_1036_:
{
lean_object* v___x_1041_; uint8_t v___x_1042_; 
v___x_1041_ = l_Lake_Git_upstreamBranch;
v___x_1042_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13);
if (v___x_1042_ == 0)
{
lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1043_ = lean_unsigned_to_nat(0u);
v___x_1044_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(v_dir_905_);
v___x_1045_ = l_Lake_GitRepo_checkoutBranch(v___x_1041_, v_dir_905_, v___x_1044_);
if (lean_obj_tag(v___x_1045_) == 0)
{
lean_object* v_a_1046_; lean_object* v___x_1047_; uint8_t v___x_1048_; 
v_a_1046_ = lean_ctor_get(v___x_1045_, 1);
lean_inc(v_a_1046_);
lean_dec_ref(v___x_1045_);
v___x_1047_ = lean_array_get_size(v_a_1046_);
v___x_1048_ = lean_nat_dec_lt(v___x_1043_, v___x_1047_);
if (v___x_1048_ == 0)
{
lean_dec(v_a_1046_);
v___y_951_ = v___y_1038_;
v___y_952_ = v___y_1039_;
v___y_953_ = v___y_1040_;
v___y_954_ = v___y_1037_;
goto v___jp_950_;
}
else
{
lean_object* v___x_1049_; uint8_t v___x_1050_; 
v___x_1049_ = lean_box(0);
v___x_1050_ = lean_nat_dec_le(v___x_1047_, v___x_1047_);
if (v___x_1050_ == 0)
{
if (v___x_1048_ == 0)
{
lean_dec(v_a_1046_);
v___y_951_ = v___y_1038_;
v___y_952_ = v___y_1039_;
v___y_953_ = v___y_1040_;
v___y_954_ = v___y_1037_;
goto v___jp_950_;
}
else
{
size_t v___x_1051_; size_t v___x_1052_; lean_object* v___x_1053_; 
v___x_1051_ = ((size_t)0ULL);
v___x_1052_ = lean_usize_of_nat(v___x_1047_);
v___x_1053_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1046_, v___x_1051_, v___x_1052_, v___x_1049_, v___y_1037_);
lean_dec(v_a_1046_);
if (lean_obj_tag(v___x_1053_) == 0)
{
lean_dec_ref(v___x_1053_);
v___y_951_ = v___y_1038_;
v___y_952_ = v___y_1039_;
v___y_953_ = v___y_1040_;
v___y_954_ = v___y_1037_;
goto v___jp_950_;
}
else
{
v___y_1031_ = v___y_1037_;
v___y_1032_ = v___y_1038_;
v___y_1033_ = v___y_1039_;
v___y_1034_ = v___y_1040_;
v___y_1035_ = v___x_1053_;
goto v___jp_1030_;
}
}
}
else
{
size_t v___x_1054_; size_t v___x_1055_; lean_object* v___x_1056_; 
v___x_1054_ = ((size_t)0ULL);
v___x_1055_ = lean_usize_of_nat(v___x_1047_);
v___x_1056_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1046_, v___x_1054_, v___x_1055_, v___x_1049_, v___y_1037_);
lean_dec(v_a_1046_);
if (lean_obj_tag(v___x_1056_) == 0)
{
lean_dec_ref(v___x_1056_);
v___y_951_ = v___y_1038_;
v___y_952_ = v___y_1039_;
v___y_953_ = v___y_1040_;
v___y_954_ = v___y_1037_;
goto v___jp_950_;
}
else
{
v___y_1031_ = v___y_1037_;
v___y_1032_ = v___y_1038_;
v___y_1033_ = v___y_1039_;
v___y_1034_ = v___y_1040_;
v___y_1035_ = v___x_1056_;
goto v___jp_1030_;
}
}
}
}
else
{
lean_object* v_a_1057_; lean_object* v___x_1058_; uint8_t v___x_1059_; 
v_a_1057_ = lean_ctor_get(v___x_1045_, 1);
lean_inc(v_a_1057_);
lean_dec_ref(v___x_1045_);
v___x_1058_ = lean_array_get_size(v_a_1057_);
v___x_1059_ = lean_nat_dec_lt(v___x_1043_, v___x_1058_);
if (v___x_1059_ == 0)
{
lean_dec(v_a_1057_);
v___y_1024_ = v___y_1037_;
v___y_1025_ = v___y_1038_;
v___y_1026_ = v___y_1039_;
v___y_1027_ = v___y_1040_;
goto v___jp_1023_;
}
else
{
lean_object* v___x_1060_; uint8_t v___x_1061_; 
v___x_1060_ = lean_box(0);
v___x_1061_ = lean_nat_dec_le(v___x_1058_, v___x_1058_);
if (v___x_1061_ == 0)
{
if (v___x_1059_ == 0)
{
lean_dec(v_a_1057_);
v___y_1024_ = v___y_1037_;
v___y_1025_ = v___y_1038_;
v___y_1026_ = v___y_1039_;
v___y_1027_ = v___y_1040_;
goto v___jp_1023_;
}
else
{
size_t v___x_1062_; size_t v___x_1063_; lean_object* v___x_1064_; 
v___x_1062_ = ((size_t)0ULL);
v___x_1063_ = lean_usize_of_nat(v___x_1058_);
v___x_1064_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1057_, v___x_1062_, v___x_1063_, v___x_1060_, v___y_1037_);
lean_dec(v_a_1057_);
if (lean_obj_tag(v___x_1064_) == 0)
{
lean_dec_ref(v___x_1064_);
v___y_1024_ = v___y_1037_;
v___y_1025_ = v___y_1038_;
v___y_1026_ = v___y_1039_;
v___y_1027_ = v___y_1040_;
goto v___jp_1023_;
}
else
{
v___y_1031_ = v___y_1037_;
v___y_1032_ = v___y_1038_;
v___y_1033_ = v___y_1039_;
v___y_1034_ = v___y_1040_;
v___y_1035_ = v___x_1064_;
goto v___jp_1030_;
}
}
}
else
{
size_t v___x_1065_; size_t v___x_1066_; lean_object* v___x_1067_; 
v___x_1065_ = ((size_t)0ULL);
v___x_1066_ = lean_usize_of_nat(v___x_1058_);
v___x_1067_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1057_, v___x_1065_, v___x_1066_, v___x_1060_, v___y_1037_);
lean_dec(v_a_1057_);
if (lean_obj_tag(v___x_1067_) == 0)
{
lean_dec_ref(v___x_1067_);
v___y_1024_ = v___y_1037_;
v___y_1025_ = v___y_1038_;
v___y_1026_ = v___y_1039_;
v___y_1027_ = v___y_1040_;
goto v___jp_1023_;
}
else
{
v___y_1031_ = v___y_1037_;
v___y_1032_ = v___y_1038_;
v___y_1033_ = v___y_1039_;
v___y_1034_ = v___y_1040_;
v___y_1035_ = v___x_1067_;
goto v___jp_1030_;
}
}
}
}
}
else
{
v___y_951_ = v___y_1038_;
v___y_952_ = v___y_1039_;
v___y_953_ = v___y_1040_;
v___y_954_ = v___y_1037_;
goto v___jp_950_;
}
}
v___jp_1068_:
{
if (lean_obj_tag(v___y_1073_) == 0)
{
lean_dec_ref(v___y_1073_);
v___y_1037_ = v___y_1069_;
v___y_1038_ = v___y_1070_;
v___y_1039_ = v___y_1071_;
v___y_1040_ = v___y_1072_;
goto v___jp_1036_;
}
else
{
lean_dec_ref(v___y_1073_);
v___y_1024_ = v___y_1069_;
v___y_1025_ = v___y_1070_;
v___y_1026_ = v___y_1071_;
v___y_1027_ = v___y_1072_;
goto v___jp_1023_;
}
}
v___jp_1074_:
{
if (v_a_1079_ == 0)
{
lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1080_ = lean_unsigned_to_nat(0u);
v___x_1081_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(v_dir_905_);
v___x_1082_ = l_Lake_GitRepo_quietInit(v_dir_905_, v___x_1081_);
if (lean_obj_tag(v___x_1082_) == 0)
{
lean_object* v_a_1083_; lean_object* v___x_1084_; uint8_t v___x_1085_; 
v_a_1083_ = lean_ctor_get(v___x_1082_, 1);
lean_inc(v_a_1083_);
lean_dec_ref(v___x_1082_);
v___x_1084_ = lean_array_get_size(v_a_1083_);
v___x_1085_ = lean_nat_dec_lt(v___x_1080_, v___x_1084_);
if (v___x_1085_ == 0)
{
lean_dec(v_a_1083_);
v___y_1037_ = v___y_1075_;
v___y_1038_ = v___y_1076_;
v___y_1039_ = v___y_1077_;
v___y_1040_ = v___y_1078_;
goto v___jp_1036_;
}
else
{
lean_object* v___x_1086_; uint8_t v___x_1087_; 
v___x_1086_ = lean_box(0);
v___x_1087_ = lean_nat_dec_le(v___x_1084_, v___x_1084_);
if (v___x_1087_ == 0)
{
if (v___x_1085_ == 0)
{
lean_dec(v_a_1083_);
v___y_1037_ = v___y_1075_;
v___y_1038_ = v___y_1076_;
v___y_1039_ = v___y_1077_;
v___y_1040_ = v___y_1078_;
goto v___jp_1036_;
}
else
{
size_t v___x_1088_; size_t v___x_1089_; lean_object* v___x_1090_; 
v___x_1088_ = ((size_t)0ULL);
v___x_1089_ = lean_usize_of_nat(v___x_1084_);
v___x_1090_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1083_, v___x_1088_, v___x_1089_, v___x_1086_, v___y_1075_);
lean_dec(v_a_1083_);
if (lean_obj_tag(v___x_1090_) == 0)
{
lean_dec_ref(v___x_1090_);
v___y_1037_ = v___y_1075_;
v___y_1038_ = v___y_1076_;
v___y_1039_ = v___y_1077_;
v___y_1040_ = v___y_1078_;
goto v___jp_1036_;
}
else
{
v___y_1069_ = v___y_1075_;
v___y_1070_ = v___y_1076_;
v___y_1071_ = v___y_1077_;
v___y_1072_ = v___y_1078_;
v___y_1073_ = v___x_1090_;
goto v___jp_1068_;
}
}
}
else
{
size_t v___x_1091_; size_t v___x_1092_; lean_object* v___x_1093_; 
v___x_1091_ = ((size_t)0ULL);
v___x_1092_ = lean_usize_of_nat(v___x_1084_);
v___x_1093_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1083_, v___x_1091_, v___x_1092_, v___x_1086_, v___y_1075_);
lean_dec(v_a_1083_);
if (lean_obj_tag(v___x_1093_) == 0)
{
lean_dec_ref(v___x_1093_);
v___y_1037_ = v___y_1075_;
v___y_1038_ = v___y_1076_;
v___y_1039_ = v___y_1077_;
v___y_1040_ = v___y_1078_;
goto v___jp_1036_;
}
else
{
v___y_1069_ = v___y_1075_;
v___y_1070_ = v___y_1076_;
v___y_1071_ = v___y_1077_;
v___y_1072_ = v___y_1078_;
v___y_1073_ = v___x_1093_;
goto v___jp_1068_;
}
}
}
}
else
{
lean_object* v_a_1094_; lean_object* v___x_1095_; uint8_t v___x_1096_; 
v_a_1094_ = lean_ctor_get(v___x_1082_, 1);
lean_inc(v_a_1094_);
lean_dec_ref(v___x_1082_);
v___x_1095_ = lean_array_get_size(v_a_1094_);
v___x_1096_ = lean_nat_dec_lt(v___x_1080_, v___x_1095_);
if (v___x_1096_ == 0)
{
lean_dec(v_a_1094_);
v___y_1024_ = v___y_1075_;
v___y_1025_ = v___y_1076_;
v___y_1026_ = v___y_1077_;
v___y_1027_ = v___y_1078_;
goto v___jp_1023_;
}
else
{
lean_object* v___x_1097_; uint8_t v___x_1098_; 
v___x_1097_ = lean_box(0);
v___x_1098_ = lean_nat_dec_le(v___x_1095_, v___x_1095_);
if (v___x_1098_ == 0)
{
if (v___x_1096_ == 0)
{
lean_dec(v_a_1094_);
v___y_1024_ = v___y_1075_;
v___y_1025_ = v___y_1076_;
v___y_1026_ = v___y_1077_;
v___y_1027_ = v___y_1078_;
goto v___jp_1023_;
}
else
{
size_t v___x_1099_; size_t v___x_1100_; lean_object* v___x_1101_; 
v___x_1099_ = ((size_t)0ULL);
v___x_1100_ = lean_usize_of_nat(v___x_1095_);
v___x_1101_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1094_, v___x_1099_, v___x_1100_, v___x_1097_, v___y_1075_);
lean_dec(v_a_1094_);
if (lean_obj_tag(v___x_1101_) == 0)
{
lean_dec_ref(v___x_1101_);
v___y_1024_ = v___y_1075_;
v___y_1025_ = v___y_1076_;
v___y_1026_ = v___y_1077_;
v___y_1027_ = v___y_1078_;
goto v___jp_1023_;
}
else
{
v___y_1069_ = v___y_1075_;
v___y_1070_ = v___y_1076_;
v___y_1071_ = v___y_1077_;
v___y_1072_ = v___y_1078_;
v___y_1073_ = v___x_1101_;
goto v___jp_1068_;
}
}
}
else
{
size_t v___x_1102_; size_t v___x_1103_; lean_object* v___x_1104_; 
v___x_1102_ = ((size_t)0ULL);
v___x_1103_ = lean_usize_of_nat(v___x_1095_);
v___x_1104_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1094_, v___x_1102_, v___x_1103_, v___x_1097_, v___y_1075_);
lean_dec(v_a_1094_);
if (lean_obj_tag(v___x_1104_) == 0)
{
lean_dec_ref(v___x_1104_);
v___y_1024_ = v___y_1075_;
v___y_1025_ = v___y_1076_;
v___y_1026_ = v___y_1077_;
v___y_1027_ = v___y_1078_;
goto v___jp_1023_;
}
else
{
v___y_1069_ = v___y_1075_;
v___y_1070_ = v___y_1076_;
v___y_1071_ = v___y_1077_;
v___y_1072_ = v___y_1078_;
v___y_1073_ = v___x_1104_;
goto v___jp_1068_;
}
}
}
}
}
else
{
v___y_951_ = v___y_1076_;
v___y_952_ = v___y_1077_;
v___y_953_ = v___y_1078_;
v___y_954_ = v___y_1075_;
goto v___jp_950_;
}
}
v___jp_1105_:
{
uint8_t v___x_1110_; lean_object* v___x_1111_; uint8_t v___x_1112_; 
lean_inc_ref(v_dir_905_);
v___x_1110_ = l_Lake_GitRepo_insideWorkTree(v_dir_905_);
v___x_1111_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1112_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1112_ == 0)
{
v___y_1075_ = v___y_1109_;
v___y_1076_ = v___y_1106_;
v___y_1077_ = v___y_1107_;
v___y_1078_ = v___y_1108_;
v_a_1079_ = v___x_1110_;
goto v___jp_1074_;
}
else
{
lean_object* v___x_1113_; uint8_t v___x_1114_; 
v___x_1113_ = lean_box(0);
v___x_1114_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (v___x_1114_ == 0)
{
if (v___x_1112_ == 0)
{
v___y_1075_ = v___y_1109_;
v___y_1076_ = v___y_1106_;
v___y_1077_ = v___y_1107_;
v___y_1078_ = v___y_1108_;
v_a_1079_ = v___x_1110_;
goto v___jp_1074_;
}
else
{
size_t v___x_1115_; size_t v___x_1116_; lean_object* v___x_1117_; 
v___x_1115_ = ((size_t)0ULL);
v___x_1116_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
v___x_1117_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1111_, v___x_1115_, v___x_1116_, v___x_1113_, v___y_1109_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_dec_ref(v___x_1117_);
v___y_1075_ = v___y_1109_;
v___y_1076_ = v___y_1106_;
v___y_1077_ = v___y_1107_;
v___y_1078_ = v___y_1108_;
v_a_1079_ = v___x_1110_;
goto v___jp_1074_;
}
else
{
lean_dec(v___y_1108_);
lean_dec_ref(v___y_1107_);
lean_dec_ref(v___y_1106_);
lean_dec_ref(v_env_909_);
lean_dec_ref(v_dir_905_);
return v___x_1117_;
}
}
}
else
{
size_t v___x_1118_; size_t v___x_1119_; lean_object* v___x_1120_; 
v___x_1118_ = ((size_t)0ULL);
v___x_1119_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
v___x_1120_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1111_, v___x_1118_, v___x_1119_, v___x_1113_, v___y_1109_);
if (lean_obj_tag(v___x_1120_) == 0)
{
lean_dec_ref(v___x_1120_);
v___y_1075_ = v___y_1109_;
v___y_1076_ = v___y_1106_;
v___y_1077_ = v___y_1107_;
v___y_1078_ = v___y_1108_;
v_a_1079_ = v___x_1110_;
goto v___jp_1074_;
}
else
{
lean_dec(v___y_1108_);
lean_dec_ref(v___y_1107_);
lean_dec_ref(v___y_1106_);
lean_dec_ref(v_env_909_);
lean_dec_ref(v_dir_905_);
return v___x_1120_;
}
}
}
}
v___jp_1121_:
{
lean_object* v___x_1128_; 
v___x_1128_ = l_IO_FS_writeFile(v___y_1122_, v___y_1127_);
lean_dec_ref(v___y_1127_);
lean_dec_ref(v___y_1122_);
if (lean_obj_tag(v___x_1128_) == 0)
{
lean_dec_ref(v___x_1128_);
v___y_1106_ = v___y_1123_;
v___y_1107_ = v___y_1125_;
v___y_1108_ = v___y_1126_;
v___y_1109_ = v___y_1124_;
goto v___jp_1105_;
}
else
{
lean_object* v_a_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1141_; 
lean_dec(v___y_1126_);
lean_dec_ref(v___y_1125_);
lean_dec_ref(v___y_1123_);
lean_dec_ref(v_env_909_);
lean_dec_ref(v_dir_905_);
v_a_1129_ = lean_ctor_get(v___x_1128_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1128_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1131_ = v___x_1128_;
v_isShared_1132_ = v_isSharedCheck_1141_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_a_1129_);
lean_dec(v___x_1128_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1141_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v___x_1133_; uint8_t v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1139_; 
v___x_1133_ = lean_io_error_to_string(v_a_1129_);
v___x_1134_ = 3;
v___x_1135_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1135_, 0, v___x_1133_);
lean_ctor_set_uint8(v___x_1135_, sizeof(void*)*1, v___x_1134_);
lean_inc_ref(v___y_1124_);
v___x_1136_ = lean_apply_2(v___y_1124_, v___x_1135_, lean_box(0));
v___x_1137_ = lean_box(0);
if (v_isShared_1132_ == 0)
{
lean_ctor_set(v___x_1131_, 0, v___x_1137_);
v___x_1139_ = v___x_1131_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v___x_1137_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
}
v___jp_1142_:
{
if (v_a_1148_ == 0)
{
uint8_t v___x_1149_; uint8_t v___x_1150_; 
v___x_1149_ = 4;
v___x_1150_ = l_Lake_instDecidableEqInitTemplate(v_tmp_907_, v___x_1149_);
if (v___x_1150_ == 0)
{
lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1151_ = l___private_Lake_CLI_Init_0__Lake_dotlessName(v_name_906_);
v___x_1152_ = l___private_Lake_CLI_Init_0__Lake_readmeFileContents(v___x_1151_);
lean_dec_ref(v___x_1151_);
v___y_1122_ = v___y_1143_;
v___y_1123_ = v___y_1144_;
v___y_1124_ = v___y_1145_;
v___y_1125_ = v___y_1146_;
v___y_1126_ = v___y_1147_;
v___y_1127_ = v___x_1152_;
goto v___jp_1121_;
}
else
{
lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1153_ = l___private_Lake_CLI_Init_0__Lake_dotlessName(v_name_906_);
v___x_1154_ = l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents(v___x_1153_);
lean_dec_ref(v___x_1153_);
v___y_1122_ = v___y_1143_;
v___y_1123_ = v___y_1144_;
v___y_1124_ = v___y_1145_;
v___y_1125_ = v___y_1146_;
v___y_1126_ = v___y_1147_;
v___y_1127_ = v___x_1154_;
goto v___jp_1121_;
}
}
else
{
lean_dec_ref(v___y_1143_);
lean_dec(v_name_906_);
v___y_1106_ = v___y_1144_;
v___y_1107_ = v___y_1146_;
v___y_1108_ = v___y_1147_;
v___y_1109_ = v___y_1145_;
goto v___jp_1105_;
}
}
v___jp_1155_:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; uint8_t v___x_1162_; lean_object* v___x_1163_; uint8_t v___x_1164_; 
v___x_1160_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__14));
lean_inc_ref(v_dir_905_);
v___x_1161_ = l_Lake_joinRelative(v_dir_905_, v___x_1160_);
v___x_1162_ = l_System_FilePath_pathExists(v___x_1161_);
v___x_1163_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1164_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1164_ == 0)
{
v___y_1143_ = v___x_1161_;
v___y_1144_ = v___y_1156_;
v___y_1145_ = v___y_1159_;
v___y_1146_ = v___y_1157_;
v___y_1147_ = v___y_1158_;
v_a_1148_ = v___x_1162_;
goto v___jp_1142_;
}
else
{
lean_object* v___x_1165_; uint8_t v___x_1166_; 
v___x_1165_ = lean_box(0);
v___x_1166_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (v___x_1166_ == 0)
{
if (v___x_1164_ == 0)
{
v___y_1143_ = v___x_1161_;
v___y_1144_ = v___y_1156_;
v___y_1145_ = v___y_1159_;
v___y_1146_ = v___y_1157_;
v___y_1147_ = v___y_1158_;
v_a_1148_ = v___x_1162_;
goto v___jp_1142_;
}
else
{
size_t v___x_1167_; size_t v___x_1168_; lean_object* v___x_1169_; 
v___x_1167_ = ((size_t)0ULL);
v___x_1168_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
v___x_1169_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1163_, v___x_1167_, v___x_1168_, v___x_1165_, v___y_1159_);
if (lean_obj_tag(v___x_1169_) == 0)
{
lean_dec_ref(v___x_1169_);
v___y_1143_ = v___x_1161_;
v___y_1144_ = v___y_1156_;
v___y_1145_ = v___y_1159_;
v___y_1146_ = v___y_1157_;
v___y_1147_ = v___y_1158_;
v_a_1148_ = v___x_1162_;
goto v___jp_1142_;
}
else
{
lean_dec_ref(v___x_1161_);
lean_dec(v___y_1158_);
lean_dec_ref(v___y_1157_);
lean_dec_ref(v___y_1156_);
lean_dec_ref(v_env_909_);
lean_dec(v_name_906_);
lean_dec_ref(v_dir_905_);
return v___x_1169_;
}
}
}
else
{
size_t v___x_1170_; size_t v___x_1171_; lean_object* v___x_1172_; 
v___x_1170_ = ((size_t)0ULL);
v___x_1171_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
v___x_1172_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1163_, v___x_1170_, v___x_1171_, v___x_1165_, v___y_1159_);
if (lean_obj_tag(v___x_1172_) == 0)
{
lean_dec_ref(v___x_1172_);
v___y_1143_ = v___x_1161_;
v___y_1144_ = v___y_1156_;
v___y_1145_ = v___y_1159_;
v___y_1146_ = v___y_1157_;
v___y_1147_ = v___y_1158_;
v_a_1148_ = v___x_1162_;
goto v___jp_1142_;
}
else
{
lean_dec_ref(v___x_1161_);
lean_dec(v___y_1158_);
lean_dec_ref(v___y_1157_);
lean_dec_ref(v___y_1156_);
lean_dec_ref(v_env_909_);
lean_dec(v_name_906_);
lean_dec_ref(v_dir_905_);
return v___x_1172_;
}
}
}
}
v___jp_1173_:
{
if (v_a_1180_ == 0)
{
uint8_t v___x_1181_; uint8_t v___x_1182_; 
v___x_1181_ = 1;
v___x_1182_ = l_Lake_instDecidableEqInitTemplate(v_tmp_907_, v___x_1181_);
if (v___x_1182_ == 0)
{
lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1183_ = l___private_Lake_CLI_Init_0__Lake_mainFileContents(v___y_1179_);
v___x_1184_ = l_IO_FS_writeFile(v___y_1176_, v___x_1183_);
lean_dec_ref(v___x_1183_);
lean_dec_ref(v___y_1176_);
if (lean_obj_tag(v___x_1184_) == 0)
{
lean_dec_ref(v___x_1184_);
v___y_1156_ = v___y_1174_;
v___y_1157_ = v___y_1177_;
v___y_1158_ = v___y_1178_;
v___y_1159_ = v___y_1175_;
goto v___jp_1155_;
}
else
{
lean_object* v_a_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1197_; 
lean_dec(v___y_1178_);
lean_dec_ref(v___y_1177_);
lean_dec_ref(v___y_1174_);
lean_dec_ref(v_env_909_);
lean_dec(v_name_906_);
lean_dec_ref(v_dir_905_);
v_a_1185_ = lean_ctor_get(v___x_1184_, 0);
v_isSharedCheck_1197_ = !lean_is_exclusive(v___x_1184_);
if (v_isSharedCheck_1197_ == 0)
{
v___x_1187_ = v___x_1184_;
v_isShared_1188_ = v_isSharedCheck_1197_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_a_1185_);
lean_dec(v___x_1184_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1197_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v___x_1189_; uint8_t v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1195_; 
v___x_1189_ = lean_io_error_to_string(v_a_1185_);
v___x_1190_ = 3;
v___x_1191_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1191_, 0, v___x_1189_);
lean_ctor_set_uint8(v___x_1191_, sizeof(void*)*1, v___x_1190_);
lean_inc_ref(v___y_1175_);
v___x_1192_ = lean_apply_2(v___y_1175_, v___x_1191_, lean_box(0));
v___x_1193_ = lean_box(0);
if (v_isShared_1188_ == 0)
{
lean_ctor_set(v___x_1187_, 0, v___x_1193_);
v___x_1195_ = v___x_1187_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v___x_1193_);
v___x_1195_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
return v___x_1195_;
}
}
}
}
else
{
lean_object* v___x_1198_; lean_object* v___x_1199_; 
lean_dec(v___y_1179_);
v___x_1198_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_exeFileContents___closed__0));
v___x_1199_ = l_IO_FS_writeFile(v___y_1176_, v___x_1198_);
lean_dec_ref(v___y_1176_);
if (lean_obj_tag(v___x_1199_) == 0)
{
lean_dec_ref(v___x_1199_);
v___y_1156_ = v___y_1174_;
v___y_1157_ = v___y_1177_;
v___y_1158_ = v___y_1178_;
v___y_1159_ = v___y_1175_;
goto v___jp_1155_;
}
else
{
lean_object* v_a_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1212_; 
lean_dec(v___y_1178_);
lean_dec_ref(v___y_1177_);
lean_dec_ref(v___y_1174_);
lean_dec_ref(v_env_909_);
lean_dec(v_name_906_);
lean_dec_ref(v_dir_905_);
v_a_1200_ = lean_ctor_get(v___x_1199_, 0);
v_isSharedCheck_1212_ = !lean_is_exclusive(v___x_1199_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1202_ = v___x_1199_;
v_isShared_1203_ = v_isSharedCheck_1212_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_a_1200_);
lean_dec(v___x_1199_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1212_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1204_; uint8_t v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1210_; 
v___x_1204_ = lean_io_error_to_string(v_a_1200_);
v___x_1205_ = 3;
v___x_1206_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1206_, 0, v___x_1204_);
lean_ctor_set_uint8(v___x_1206_, sizeof(void*)*1, v___x_1205_);
lean_inc_ref(v___y_1175_);
v___x_1207_ = lean_apply_2(v___y_1175_, v___x_1206_, lean_box(0));
v___x_1208_ = lean_box(0);
if (v_isShared_1203_ == 0)
{
lean_ctor_set(v___x_1202_, 0, v___x_1208_);
v___x_1210_ = v___x_1202_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v___x_1208_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
}
}
}
else
{
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1176_);
v___y_1156_ = v___y_1174_;
v___y_1157_ = v___y_1177_;
v___y_1158_ = v___y_1178_;
v___y_1159_ = v___y_1175_;
goto v___jp_1155_;
}
}
v___jp_1213_:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; uint8_t v___x_1221_; lean_object* v___x_1222_; uint8_t v___x_1223_; 
v___x_1219_ = l___private_Lake_CLI_Init_0__Lake_mainFileName;
lean_inc_ref(v_dir_905_);
v___x_1220_ = l_Lake_joinRelative(v_dir_905_, v___x_1219_);
v___x_1221_ = l_System_FilePath_pathExists(v___x_1220_);
v___x_1222_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1223_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1223_ == 0)
{
v___y_1174_ = v___y_1215_;
v___y_1175_ = v___y_1214_;
v___y_1176_ = v___x_1220_;
v___y_1177_ = v___y_1216_;
v___y_1178_ = v___y_1217_;
v___y_1179_ = v___y_1218_;
v_a_1180_ = v___x_1221_;
goto v___jp_1173_;
}
else
{
lean_object* v___x_1224_; uint8_t v___x_1225_; 
v___x_1224_ = lean_box(0);
v___x_1225_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (v___x_1225_ == 0)
{
if (v___x_1223_ == 0)
{
v___y_1174_ = v___y_1215_;
v___y_1175_ = v___y_1214_;
v___y_1176_ = v___x_1220_;
v___y_1177_ = v___y_1216_;
v___y_1178_ = v___y_1217_;
v___y_1179_ = v___y_1218_;
v_a_1180_ = v___x_1221_;
goto v___jp_1173_;
}
else
{
size_t v___x_1226_; size_t v___x_1227_; lean_object* v___x_1228_; 
v___x_1226_ = ((size_t)0ULL);
v___x_1227_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
v___x_1228_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1222_, v___x_1226_, v___x_1227_, v___x_1224_, v___y_1214_);
if (lean_obj_tag(v___x_1228_) == 0)
{
lean_dec_ref(v___x_1228_);
v___y_1174_ = v___y_1215_;
v___y_1175_ = v___y_1214_;
v___y_1176_ = v___x_1220_;
v___y_1177_ = v___y_1216_;
v___y_1178_ = v___y_1217_;
v___y_1179_ = v___y_1218_;
v_a_1180_ = v___x_1221_;
goto v___jp_1173_;
}
else
{
lean_dec_ref(v___x_1220_);
lean_dec(v___y_1218_);
lean_dec(v___y_1217_);
lean_dec_ref(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec_ref(v_env_909_);
lean_dec(v_name_906_);
lean_dec_ref(v_dir_905_);
return v___x_1228_;
}
}
}
else
{
size_t v___x_1229_; size_t v___x_1230_; lean_object* v___x_1231_; 
v___x_1229_ = ((size_t)0ULL);
v___x_1230_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
v___x_1231_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1222_, v___x_1229_, v___x_1230_, v___x_1224_, v___y_1214_);
if (lean_obj_tag(v___x_1231_) == 0)
{
lean_dec_ref(v___x_1231_);
v___y_1174_ = v___y_1215_;
v___y_1175_ = v___y_1214_;
v___y_1176_ = v___x_1220_;
v___y_1177_ = v___y_1216_;
v___y_1178_ = v___y_1217_;
v___y_1179_ = v___y_1218_;
v_a_1180_ = v___x_1221_;
goto v___jp_1173_;
}
else
{
lean_dec_ref(v___x_1220_);
lean_dec(v___y_1218_);
lean_dec(v___y_1217_);
lean_dec_ref(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec_ref(v_env_909_);
lean_dec(v_name_906_);
lean_dec_ref(v_dir_905_);
return v___x_1231_;
}
}
}
}
v___jp_1232_:
{
switch(v_tmp_907_)
{
case 0:
{
v___y_1214_ = v___y_1237_;
v___y_1215_ = v___y_1233_;
v___y_1216_ = v___y_1234_;
v___y_1217_ = v___y_1235_;
v___y_1218_ = v___y_1236_;
goto v___jp_1213_;
}
case 1:
{
v___y_1214_ = v___y_1237_;
v___y_1215_ = v___y_1233_;
v___y_1216_ = v___y_1234_;
v___y_1217_ = v___y_1235_;
v___y_1218_ = v___y_1236_;
goto v___jp_1213_;
}
default: 
{
lean_dec(v___y_1236_);
v___y_1156_ = v___y_1233_;
v___y_1157_ = v___y_1234_;
v___y_1158_ = v___y_1235_;
v___y_1159_ = v___y_1237_;
goto v___jp_1155_;
}
}
}
v___jp_1238_:
{
lean_object* v___x_1246_; 
v___x_1246_ = l_IO_FS_writeFile(v___y_1241_, v___y_1245_);
lean_dec_ref(v___y_1245_);
lean_dec_ref(v___y_1241_);
if (lean_obj_tag(v___x_1246_) == 0)
{
lean_dec_ref(v___x_1246_);
v___y_1233_ = v___y_1240_;
v___y_1234_ = v___y_1242_;
v___y_1235_ = v___y_1243_;
v___y_1236_ = v___y_1244_;
v___y_1237_ = v___y_1239_;
goto v___jp_1232_;
}
else
{
lean_object* v_a_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1259_; 
lean_dec(v___y_1244_);
lean_dec(v___y_1243_);
lean_dec_ref(v___y_1242_);
lean_dec_ref(v___y_1240_);
lean_dec_ref(v_env_909_);
lean_dec(v_name_906_);
lean_dec_ref(v_dir_905_);
v_a_1247_ = lean_ctor_get(v___x_1246_, 0);
v_isSharedCheck_1259_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1249_ = v___x_1246_;
v_isShared_1250_ = v_isSharedCheck_1259_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_a_1247_);
lean_dec(v___x_1246_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1259_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1251_; uint8_t v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1257_; 
v___x_1251_ = lean_io_error_to_string(v_a_1247_);
v___x_1252_ = 3;
v___x_1253_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1253_, 0, v___x_1251_);
lean_ctor_set_uint8(v___x_1253_, sizeof(void*)*1, v___x_1252_);
lean_inc_ref(v___y_1239_);
v___x_1254_ = lean_apply_2(v___y_1239_, v___x_1253_, lean_box(0));
v___x_1255_ = lean_box(0);
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 0, v___x_1255_);
v___x_1257_ = v___x_1249_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v___x_1255_);
v___x_1257_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
return v___x_1257_;
}
}
}
}
v___jp_1260_:
{
uint8_t v___x_1267_; uint8_t v___x_1268_; 
v___x_1267_ = 4;
v___x_1268_ = l_Lake_instDecidableEqInitTemplate(v_tmp_907_, v___x_1267_);
if (v___x_1268_ == 0)
{
uint8_t v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; 
v___x_1269_ = 1;
lean_inc_n(v___y_1265_, 2);
v___x_1270_ = l_Lean_Name_toString(v___y_1265_, v___x_1269_);
v___x_1271_ = l___private_Lake_CLI_Init_0__Lake_libRootFileContents(v___x_1270_, v___y_1265_);
lean_dec_ref(v___x_1270_);
v___y_1239_ = v___y_1266_;
v___y_1240_ = v___y_1262_;
v___y_1241_ = v___y_1261_;
v___y_1242_ = v___y_1263_;
v___y_1243_ = v___y_1264_;
v___y_1244_ = v___y_1265_;
v___y_1245_ = v___x_1271_;
goto v___jp_1238_;
}
else
{
lean_object* v___x_1272_; 
lean_inc(v___y_1265_);
v___x_1272_ = l___private_Lake_CLI_Init_0__Lake_mathLibRootFileContents(v___y_1265_);
v___y_1239_ = v___y_1266_;
v___y_1240_ = v___y_1262_;
v___y_1241_ = v___y_1261_;
v___y_1242_ = v___y_1263_;
v___y_1243_ = v___y_1264_;
v___y_1244_ = v___y_1265_;
v___y_1245_ = v___x_1272_;
goto v___jp_1238_;
}
}
v___jp_1273_:
{
if (v_a_1281_ == 0)
{
lean_object* v___x_1282_; 
v___x_1282_ = l_IO_FS_createDirAll(v___y_1274_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v___x_1283_; lean_object* v___x_1284_; 
lean_dec_ref(v___x_1282_);
v___x_1283_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_basicFileContents___closed__0));
v___x_1284_ = l_IO_FS_writeFile(v___y_1277_, v___x_1283_);
lean_dec_ref(v___y_1277_);
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_dec_ref(v___x_1284_);
v___y_1261_ = v___y_1276_;
v___y_1262_ = v___y_1275_;
v___y_1263_ = v___y_1278_;
v___y_1264_ = v___y_1279_;
v___y_1265_ = v___y_1280_;
v___y_1266_ = v_a_911_;
goto v___jp_1260_;
}
else
{
lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1297_; 
lean_dec(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
lean_dec_ref(v___y_1276_);
lean_dec_ref(v___y_1275_);
lean_dec_ref(v_env_909_);
lean_dec(v_name_906_);
lean_dec_ref(v_dir_905_);
v_a_1285_ = lean_ctor_get(v___x_1284_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1287_ = v___x_1284_;
v_isShared_1288_ = v_isSharedCheck_1297_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_dec(v___x_1284_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1297_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1289_; uint8_t v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1295_; 
v___x_1289_ = lean_io_error_to_string(v_a_1285_);
v___x_1290_ = 3;
v___x_1291_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1291_, 0, v___x_1289_);
lean_ctor_set_uint8(v___x_1291_, sizeof(void*)*1, v___x_1290_);
lean_inc_ref(v_a_911_);
v___x_1292_ = lean_apply_2(v_a_911_, v___x_1291_, lean_box(0));
v___x_1293_ = lean_box(0);
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 0, v___x_1293_);
v___x_1295_ = v___x_1287_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v___x_1293_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
}
else
{
lean_object* v_a_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1310_; 
lean_dec(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
lean_dec_ref(v___y_1277_);
lean_dec_ref(v___y_1276_);
lean_dec_ref(v___y_1275_);
lean_dec_ref(v_env_909_);
lean_dec(v_name_906_);
lean_dec_ref(v_dir_905_);
v_a_1298_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1310_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1300_ = v___x_1282_;
v_isShared_1301_ = v_isSharedCheck_1310_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_a_1298_);
lean_dec(v___x_1282_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1310_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1302_; uint8_t v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1308_; 
v___x_1302_ = lean_io_error_to_string(v_a_1298_);
v___x_1303_ = 3;
v___x_1304_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1304_, 0, v___x_1302_);
lean_ctor_set_uint8(v___x_1304_, sizeof(void*)*1, v___x_1303_);
lean_inc_ref(v_a_911_);
v___x_1305_ = lean_apply_2(v_a_911_, v___x_1304_, lean_box(0));
v___x_1306_ = lean_box(0);
if (v_isShared_1301_ == 0)
{
lean_ctor_set(v___x_1300_, 0, v___x_1306_);
v___x_1308_ = v___x_1300_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v___x_1306_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
}
}
else
{
lean_dec_ref(v___y_1277_);
lean_dec_ref(v___y_1274_);
v___y_1261_ = v___y_1276_;
v___y_1262_ = v___y_1275_;
v___y_1263_ = v___y_1278_;
v___y_1264_ = v___y_1279_;
v___y_1265_ = v___y_1280_;
v___y_1266_ = v_a_911_;
goto v___jp_1260_;
}
}
v___jp_1314_:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; 
lean_inc(v___y_1319_);
lean_inc(v___y_1318_);
lean_inc(v_name_906_);
v___x_1320_ = l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents(v_tmp_907_, v_lang_908_, v_name_906_, v___y_1318_, v___y_1319_);
v___x_1321_ = l_IO_FS_writeFile(v_configFile_1313_, v___x_1320_);
lean_dec_ref(v___x_1320_);
lean_dec_ref(v_configFile_1313_);
if (lean_obj_tag(v___x_1321_) == 0)
{
lean_dec_ref(v___x_1321_);
if (lean_obj_tag(v___y_1315_) == 1)
{
lean_object* v_val_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; uint8_t v___x_1327_; lean_object* v___x_1328_; uint8_t v___x_1329_; 
v_val_1322_ = lean_ctor_get(v___y_1315_, 0);
lean_inc_n(v_val_1322_, 2);
lean_dec_ref(v___y_1315_);
v___x_1323_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0));
v___x_1324_ = l_System_FilePath_withExtension(v_val_1322_, v___x_1323_);
v___x_1325_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__15));
lean_inc_ref(v___x_1324_);
v___x_1326_ = l_Lake_joinRelative(v___x_1324_, v___x_1325_);
v___x_1327_ = l_System_FilePath_pathExists(v___x_1326_);
v___x_1328_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1329_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1329_ == 0)
{
v___y_1274_ = v___x_1324_;
v___y_1275_ = v___y_1316_;
v___y_1276_ = v_val_1322_;
v___y_1277_ = v___x_1326_;
v___y_1278_ = v___y_1317_;
v___y_1279_ = v___y_1319_;
v___y_1280_ = v___y_1318_;
v_a_1281_ = v___x_1327_;
goto v___jp_1273_;
}
else
{
lean_object* v___x_1330_; uint8_t v___x_1331_; 
v___x_1330_ = lean_box(0);
v___x_1331_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (v___x_1331_ == 0)
{
if (v___x_1329_ == 0)
{
v___y_1274_ = v___x_1324_;
v___y_1275_ = v___y_1316_;
v___y_1276_ = v_val_1322_;
v___y_1277_ = v___x_1326_;
v___y_1278_ = v___y_1317_;
v___y_1279_ = v___y_1319_;
v___y_1280_ = v___y_1318_;
v_a_1281_ = v___x_1327_;
goto v___jp_1273_;
}
else
{
size_t v___x_1332_; size_t v___x_1333_; lean_object* v___x_1334_; 
v___x_1332_ = ((size_t)0ULL);
v___x_1333_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
v___x_1334_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1328_, v___x_1332_, v___x_1333_, v___x_1330_, v_a_911_);
if (lean_obj_tag(v___x_1334_) == 0)
{
lean_dec_ref(v___x_1334_);
v___y_1274_ = v___x_1324_;
v___y_1275_ = v___y_1316_;
v___y_1276_ = v_val_1322_;
v___y_1277_ = v___x_1326_;
v___y_1278_ = v___y_1317_;
v___y_1279_ = v___y_1319_;
v___y_1280_ = v___y_1318_;
v_a_1281_ = v___x_1327_;
goto v___jp_1273_;
}
else
{
lean_dec_ref(v___x_1326_);
lean_dec_ref(v___x_1324_);
lean_dec(v_val_1322_);
lean_dec(v___y_1319_);
lean_dec(v___y_1318_);
lean_dec_ref(v___y_1317_);
lean_dec_ref(v___y_1316_);
lean_dec_ref(v_env_909_);
lean_dec(v_name_906_);
lean_dec_ref(v_dir_905_);
return v___x_1334_;
}
}
}
else
{
size_t v___x_1335_; size_t v___x_1336_; lean_object* v___x_1337_; 
v___x_1335_ = ((size_t)0ULL);
v___x_1336_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
v___x_1337_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1328_, v___x_1335_, v___x_1336_, v___x_1330_, v_a_911_);
if (lean_obj_tag(v___x_1337_) == 0)
{
lean_dec_ref(v___x_1337_);
v___y_1274_ = v___x_1324_;
v___y_1275_ = v___y_1316_;
v___y_1276_ = v_val_1322_;
v___y_1277_ = v___x_1326_;
v___y_1278_ = v___y_1317_;
v___y_1279_ = v___y_1319_;
v___y_1280_ = v___y_1318_;
v_a_1281_ = v___x_1327_;
goto v___jp_1273_;
}
else
{
lean_dec_ref(v___x_1326_);
lean_dec_ref(v___x_1324_);
lean_dec(v_val_1322_);
lean_dec(v___y_1319_);
lean_dec(v___y_1318_);
lean_dec_ref(v___y_1317_);
lean_dec_ref(v___y_1316_);
lean_dec_ref(v_env_909_);
lean_dec(v_name_906_);
lean_dec_ref(v_dir_905_);
return v___x_1337_;
}
}
}
}
else
{
lean_dec(v___y_1315_);
v___y_1233_ = v___y_1316_;
v___y_1234_ = v___y_1317_;
v___y_1235_ = v___y_1319_;
v___y_1236_ = v___y_1318_;
v___y_1237_ = v_a_911_;
goto v___jp_1232_;
}
}
else
{
lean_object* v_a_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1350_; 
lean_dec(v___y_1319_);
lean_dec(v___y_1318_);
lean_dec_ref(v___y_1317_);
lean_dec_ref(v___y_1316_);
lean_dec(v___y_1315_);
lean_dec_ref(v_env_909_);
lean_dec(v_name_906_);
lean_dec_ref(v_dir_905_);
v_a_1338_ = lean_ctor_get(v___x_1321_, 0);
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1321_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1340_ = v___x_1321_;
v_isShared_1341_ = v_isSharedCheck_1350_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_a_1338_);
lean_dec(v___x_1321_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1350_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v___x_1342_; uint8_t v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1348_; 
v___x_1342_ = lean_io_error_to_string(v_a_1338_);
v___x_1343_ = 3;
v___x_1344_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1344_, 0, v___x_1342_);
lean_ctor_set_uint8(v___x_1344_, sizeof(void*)*1, v___x_1343_);
lean_inc_ref(v_a_911_);
v___x_1345_ = lean_apply_2(v_a_911_, v___x_1344_, lean_box(0));
v___x_1346_ = lean_box(0);
if (v_isShared_1341_ == 0)
{
lean_ctor_set(v___x_1340_, 0, v___x_1346_);
v___x_1348_ = v___x_1340_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v___x_1346_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
}
}
v___jp_1351_:
{
lean_object* v_lean_1354_; lean_object* v_toolchain_1355_; lean_object* v___x_1356_; 
v_lean_1354_ = lean_ctor_get(v_env_909_, 1);
v_toolchain_1355_ = lean_ctor_get(v_env_909_, 18);
lean_inc_ref(v_toolchain_1355_);
v___x_1356_ = l_Lake_ToolchainVer_ofString(v_toolchain_1355_);
if (lean_obj_tag(v___x_1356_) == 0)
{
lean_object* v_ver_1357_; lean_object* v___x_1358_; 
v_ver_1357_ = lean_ctor_get(v___x_1356_, 1);
lean_inc_ref(v_ver_1357_);
lean_dec_ref(v___x_1356_);
v___x_1358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1358_, 0, v_ver_1357_);
lean_inc_ref(v_lean_1354_);
lean_inc_ref(v_toolchain_1355_);
v___y_1315_ = v_snd_1353_;
v___y_1316_ = v_toolchain_1355_;
v___y_1317_ = v_lean_1354_;
v___y_1318_ = v_fst_1352_;
v___y_1319_ = v___x_1358_;
goto v___jp_1314_;
}
else
{
lean_object* v___x_1359_; 
lean_dec_ref(v___x_1356_);
v___x_1359_ = lean_box(0);
lean_inc_ref(v_lean_1354_);
lean_inc_ref(v_toolchain_1355_);
v___y_1315_ = v_snd_1353_;
v___y_1316_ = v_toolchain_1355_;
v___y_1317_ = v_lean_1354_;
v___y_1318_ = v_fst_1352_;
v___y_1319_ = v___x_1359_;
goto v___jp_1314_;
}
}
v___jp_1360_:
{
if (v_a_1363_ == 0)
{
lean_object* v___x_1364_; 
v___x_1364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1364_, 0, v___y_1361_);
v_fst_1352_ = v___y_1362_;
v_snd_1353_ = v___x_1364_;
goto v___jp_1351_;
}
else
{
lean_object* v___x_1365_; 
lean_dec_ref(v___y_1361_);
v___x_1365_ = lean_box(0);
v_fst_1352_ = v___y_1362_;
v_snd_1353_ = v___x_1365_;
goto v___jp_1351_;
}
}
v___jp_1366_:
{
if (v___y_1369_ == 0)
{
lean_object* v___x_1370_; lean_object* v___x_1371_; uint8_t v___x_1372_; lean_object* v___x_1373_; uint8_t v___x_1374_; 
lean_dec_ref(v___y_1367_);
lean_inc(v_name_906_);
v___x_1370_ = l_Lake_toUpperCamelCase(v_name_906_);
lean_inc(v___x_1370_);
v___x_1371_ = l_Lean_modToFilePath(v_dir_905_, v___x_1370_, v___y_1368_);
v___x_1372_ = l_System_FilePath_pathExists(v___x_1371_);
v___x_1373_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1374_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1374_ == 0)
{
v___y_1361_ = v___x_1371_;
v___y_1362_ = v___x_1370_;
v_a_1363_ = v___x_1372_;
goto v___jp_1360_;
}
else
{
lean_object* v___x_1375_; uint8_t v___x_1376_; 
v___x_1375_ = lean_box(0);
v___x_1376_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (v___x_1376_ == 0)
{
if (v___x_1374_ == 0)
{
v___y_1361_ = v___x_1371_;
v___y_1362_ = v___x_1370_;
v_a_1363_ = v___x_1372_;
goto v___jp_1360_;
}
else
{
size_t v___x_1377_; size_t v___x_1378_; lean_object* v___x_1379_; 
v___x_1377_ = ((size_t)0ULL);
v___x_1378_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
v___x_1379_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1373_, v___x_1377_, v___x_1378_, v___x_1375_, v_a_911_);
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_dec_ref(v___x_1379_);
v___y_1361_ = v___x_1371_;
v___y_1362_ = v___x_1370_;
v_a_1363_ = v___x_1372_;
goto v___jp_1360_;
}
else
{
lean_dec_ref(v___x_1371_);
lean_dec(v___x_1370_);
lean_dec_ref(v_configFile_1313_);
lean_dec_ref(v_env_909_);
lean_dec(v_name_906_);
lean_dec_ref(v_dir_905_);
return v___x_1379_;
}
}
}
else
{
size_t v___x_1380_; size_t v___x_1381_; lean_object* v___x_1382_; 
v___x_1380_ = ((size_t)0ULL);
v___x_1381_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
v___x_1382_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1373_, v___x_1380_, v___x_1381_, v___x_1375_, v_a_911_);
if (lean_obj_tag(v___x_1382_) == 0)
{
lean_dec_ref(v___x_1382_);
v___y_1361_ = v___x_1371_;
v___y_1362_ = v___x_1370_;
v_a_1363_ = v___x_1372_;
goto v___jp_1360_;
}
else
{
lean_dec_ref(v___x_1371_);
lean_dec(v___x_1370_);
lean_dec_ref(v_configFile_1313_);
lean_dec_ref(v_env_909_);
lean_dec(v_name_906_);
lean_dec_ref(v_dir_905_);
return v___x_1382_;
}
}
}
}
else
{
lean_object* v___x_1383_; 
v___x_1383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1383_, 0, v___y_1367_);
lean_inc(v_name_906_);
v_fst_1352_ = v_name_906_;
v_snd_1353_ = v___x_1383_;
goto v___jp_1351_;
}
}
v___jp_1384_:
{
uint8_t v___x_1388_; uint8_t v___x_1389_; 
v___x_1388_ = 1;
v___x_1389_ = l_Lake_instDecidableEqInitTemplate(v_tmp_907_, v___x_1388_);
if (v___x_1389_ == 0)
{
v___y_1367_ = v___y_1385_;
v___y_1368_ = v___y_1386_;
v___y_1369_ = v_a_1387_;
goto v___jp_1366_;
}
else
{
v___y_1367_ = v___y_1385_;
v___y_1368_ = v___y_1386_;
v___y_1369_ = v___x_1389_;
goto v___jp_1366_;
}
}
v___jp_1390_:
{
lean_object* v___x_1391_; lean_object* v___x_1392_; uint8_t v___x_1393_; lean_object* v___x_1394_; uint8_t v___x_1395_; 
v___x_1391_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__16));
lean_inc(v_name_906_);
v___x_1392_ = l_Lean_modToFilePath(v_dir_905_, v_name_906_, v___x_1391_);
v___x_1393_ = l_System_FilePath_pathExists(v___x_1392_);
v___x_1394_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1395_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1395_ == 0)
{
v___y_1385_ = v___x_1392_;
v___y_1386_ = v___x_1391_;
v_a_1387_ = v___x_1393_;
goto v___jp_1384_;
}
else
{
lean_object* v___x_1396_; uint8_t v___x_1397_; 
v___x_1396_ = lean_box(0);
v___x_1397_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (v___x_1397_ == 0)
{
if (v___x_1395_ == 0)
{
v___y_1385_ = v___x_1392_;
v___y_1386_ = v___x_1391_;
v_a_1387_ = v___x_1393_;
goto v___jp_1384_;
}
else
{
size_t v___x_1398_; size_t v___x_1399_; lean_object* v___x_1400_; 
v___x_1398_ = ((size_t)0ULL);
v___x_1399_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
v___x_1400_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1394_, v___x_1398_, v___x_1399_, v___x_1396_, v_a_911_);
if (lean_obj_tag(v___x_1400_) == 0)
{
lean_dec_ref(v___x_1400_);
v___y_1385_ = v___x_1392_;
v___y_1386_ = v___x_1391_;
v_a_1387_ = v___x_1393_;
goto v___jp_1384_;
}
else
{
lean_dec_ref(v___x_1392_);
lean_dec_ref(v_configFile_1313_);
lean_dec_ref(v_env_909_);
lean_dec(v_name_906_);
lean_dec_ref(v_dir_905_);
return v___x_1400_;
}
}
}
else
{
size_t v___x_1401_; size_t v___x_1402_; lean_object* v___x_1403_; 
v___x_1401_ = ((size_t)0ULL);
v___x_1402_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
v___x_1403_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1394_, v___x_1401_, v___x_1402_, v___x_1396_, v_a_911_);
if (lean_obj_tag(v___x_1403_) == 0)
{
lean_dec_ref(v___x_1403_);
v___y_1385_ = v___x_1392_;
v___y_1386_ = v___x_1391_;
v_a_1387_ = v___x_1393_;
goto v___jp_1384_;
}
else
{
lean_dec_ref(v___x_1392_);
lean_dec_ref(v_configFile_1313_);
lean_dec_ref(v_env_909_);
lean_dec(v_name_906_);
lean_dec_ref(v_dir_905_);
return v___x_1403_;
}
}
}
}
v___jp_1404_:
{
if (lean_obj_tag(v___y_1405_) == 0)
{
lean_dec_ref(v___y_1405_);
goto v___jp_1390_;
}
else
{
lean_dec_ref(v_configFile_1313_);
lean_dec_ref(v_env_909_);
lean_dec(v_name_906_);
lean_dec_ref(v_dir_905_);
return v___y_1405_;
}
}
v___jp_1407_:
{
if (v___x_1406_ == 0)
{
lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; 
v___x_1408_ = lean_unsigned_to_nat(0u);
v___x_1409_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(v_dir_905_);
v___x_1410_ = l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow(v_dir_905_, v_tmp_907_, v___x_1409_);
if (lean_obj_tag(v___x_1410_) == 0)
{
lean_object* v_a_1411_; lean_object* v___x_1412_; uint8_t v___x_1413_; 
v_a_1411_ = lean_ctor_get(v___x_1410_, 1);
lean_inc(v_a_1411_);
lean_dec_ref(v___x_1410_);
v___x_1412_ = lean_array_get_size(v_a_1411_);
v___x_1413_ = lean_nat_dec_lt(v___x_1408_, v___x_1412_);
if (v___x_1413_ == 0)
{
lean_dec(v_a_1411_);
goto v___jp_1390_;
}
else
{
lean_object* v___x_1414_; uint8_t v___x_1415_; 
v___x_1414_ = lean_box(0);
v___x_1415_ = lean_nat_dec_le(v___x_1412_, v___x_1412_);
if (v___x_1415_ == 0)
{
if (v___x_1413_ == 0)
{
lean_dec(v_a_1411_);
goto v___jp_1390_;
}
else
{
size_t v___x_1416_; size_t v___x_1417_; lean_object* v___x_1418_; 
v___x_1416_ = ((size_t)0ULL);
v___x_1417_ = lean_usize_of_nat(v___x_1412_);
v___x_1418_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1411_, v___x_1416_, v___x_1417_, v___x_1414_, v_a_911_);
lean_dec(v_a_1411_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_dec_ref(v___x_1418_);
goto v___jp_1390_;
}
else
{
v___y_1405_ = v___x_1418_;
goto v___jp_1404_;
}
}
}
else
{
size_t v___x_1419_; size_t v___x_1420_; lean_object* v___x_1421_; 
v___x_1419_ = ((size_t)0ULL);
v___x_1420_ = lean_usize_of_nat(v___x_1412_);
v___x_1421_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1411_, v___x_1419_, v___x_1420_, v___x_1414_, v_a_911_);
lean_dec(v_a_1411_);
if (lean_obj_tag(v___x_1421_) == 0)
{
lean_dec_ref(v___x_1421_);
goto v___jp_1390_;
}
else
{
v___y_1405_ = v___x_1421_;
goto v___jp_1404_;
}
}
}
}
else
{
lean_object* v_a_1422_; lean_object* v___x_1423_; uint8_t v___x_1424_; 
v_a_1422_ = lean_ctor_get(v___x_1410_, 1);
lean_inc(v_a_1422_);
lean_dec_ref(v___x_1410_);
v___x_1423_ = lean_array_get_size(v_a_1422_);
v___x_1424_ = lean_nat_dec_lt(v___x_1408_, v___x_1423_);
if (v___x_1424_ == 0)
{
lean_object* v___x_1425_; lean_object* v___x_1426_; 
lean_dec(v_a_1422_);
lean_dec_ref(v_configFile_1313_);
lean_dec_ref(v_env_909_);
lean_dec(v_name_906_);
lean_dec_ref(v_dir_905_);
v___x_1425_ = lean_box(0);
v___x_1426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1426_, 0, v___x_1425_);
return v___x_1426_;
}
else
{
lean_object* v___x_1427_; uint8_t v___x_1428_; 
v___x_1427_ = lean_box(0);
v___x_1428_ = lean_nat_dec_le(v___x_1423_, v___x_1423_);
if (v___x_1428_ == 0)
{
if (v___x_1424_ == 0)
{
lean_dec(v_a_1422_);
lean_dec_ref(v_configFile_1313_);
lean_dec_ref(v_env_909_);
lean_dec(v_name_906_);
lean_dec_ref(v_dir_905_);
goto v___jp_913_;
}
else
{
size_t v___x_1429_; size_t v___x_1430_; lean_object* v___x_1431_; 
v___x_1429_ = ((size_t)0ULL);
v___x_1430_ = lean_usize_of_nat(v___x_1423_);
v___x_1431_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1422_, v___x_1429_, v___x_1430_, v___x_1427_, v_a_911_);
lean_dec(v_a_1422_);
if (lean_obj_tag(v___x_1431_) == 0)
{
lean_dec_ref(v___x_1431_);
lean_dec_ref(v_configFile_1313_);
lean_dec_ref(v_env_909_);
lean_dec(v_name_906_);
lean_dec_ref(v_dir_905_);
goto v___jp_913_;
}
else
{
v___y_1405_ = v___x_1431_;
goto v___jp_1404_;
}
}
}
else
{
size_t v___x_1432_; size_t v___x_1433_; lean_object* v___x_1434_; 
v___x_1432_ = ((size_t)0ULL);
v___x_1433_ = lean_usize_of_nat(v___x_1423_);
v___x_1434_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1422_, v___x_1432_, v___x_1433_, v___x_1427_, v_a_911_);
lean_dec(v_a_1422_);
if (lean_obj_tag(v___x_1434_) == 0)
{
lean_dec_ref(v___x_1434_);
lean_dec_ref(v_configFile_1313_);
lean_dec_ref(v_env_909_);
lean_dec(v_name_906_);
lean_dec_ref(v_dir_905_);
goto v___jp_913_;
}
else
{
v___y_1405_ = v___x_1434_;
goto v___jp_1404_;
}
}
}
}
}
else
{
lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; 
lean_dec_ref(v_configFile_1313_);
lean_dec_ref(v_env_909_);
lean_dec(v_name_906_);
lean_dec_ref(v_dir_905_);
v___x_1435_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__18));
lean_inc_ref(v_a_911_);
v___x_1436_ = lean_apply_2(v_a_911_, v___x_1435_, lean_box(0));
v___x_1437_ = lean_box(0);
v___x_1438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1438_, 0, v___x_1437_);
return v___x_1438_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___boxed(lean_object* v_dir_1449_, lean_object* v_name_1450_, lean_object* v_tmp_1451_, lean_object* v_lang_1452_, lean_object* v_env_1453_, lean_object* v_offline_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_){
_start:
{
uint8_t v_tmp_boxed_1457_; uint8_t v_lang_boxed_1458_; uint8_t v_offline_boxed_1459_; lean_object* v_res_1460_; 
v_tmp_boxed_1457_ = lean_unbox(v_tmp_1451_);
v_lang_boxed_1458_ = lean_unbox(v_lang_1452_);
v_offline_boxed_1459_ = lean_unbox(v_offline_1454_);
v_res_1460_ = l___private_Lake_CLI_Init_0__Lake_initPkg(v_dir_1449_, v_name_1450_, v_tmp_boxed_1457_, v_lang_boxed_1458_, v_env_1453_, v_offline_boxed_1459_, v_a_1455_);
lean_dec_ref(v_a_1455_);
return v_res_1460_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__1(lean_object* v_s_1461_, lean_object* v_pos_1462_){
_start:
{
lean_object* v_str_1463_; lean_object* v_startInclusive_1464_; lean_object* v_endExclusive_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; uint8_t v___x_1469_; 
v_str_1463_ = lean_ctor_get(v_s_1461_, 0);
v_startInclusive_1464_ = lean_ctor_get(v_s_1461_, 1);
v_endExclusive_1465_ = lean_ctor_get(v_s_1461_, 2);
v___x_1466_ = lean_nat_add(v_startInclusive_1464_, v_pos_1462_);
v___x_1467_ = lean_unsigned_to_nat(0u);
v___x_1468_ = lean_nat_sub(v_endExclusive_1465_, v___x_1466_);
v___x_1469_ = lean_nat_dec_eq(v___x_1467_, v___x_1468_);
lean_dec(v___x_1468_);
if (v___x_1469_ == 0)
{
uint32_t v___x_1470_; uint32_t v___x_1471_; uint8_t v___x_1472_; 
v___x_1470_ = lean_string_utf8_get_fast(v_str_1463_, v___x_1466_);
v___x_1471_ = 46;
v___x_1472_ = lean_uint32_dec_eq(v___x_1470_, v___x_1471_);
if (v___x_1472_ == 0)
{
lean_dec(v___x_1466_);
return v_pos_1462_;
}
else
{
lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; uint8_t v___x_1476_; 
v___x_1473_ = lean_string_utf8_next_fast(v_str_1463_, v___x_1466_);
v___x_1474_ = lean_nat_sub(v___x_1473_, v___x_1466_);
lean_dec(v___x_1466_);
v___x_1475_ = lean_nat_add(v_pos_1462_, v___x_1474_);
lean_dec(v___x_1474_);
v___x_1476_ = l_String_instDecidableLtRaw___aux__1(v_pos_1462_, v___x_1475_);
if (v___x_1476_ == 0)
{
lean_dec(v___x_1475_);
return v_pos_1462_;
}
else
{
lean_dec(v_pos_1462_);
v_pos_1462_ = v___x_1475_;
goto _start;
}
}
}
else
{
lean_dec(v___x_1466_);
return v_pos_1462_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__1___boxed(lean_object* v_s_1478_, lean_object* v_pos_1479_){
_start:
{
lean_object* v_res_1480_; 
v_res_1480_ = l_String_Slice_Pos_skipWhile___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__1(v_s_1478_, v_pos_1479_);
lean_dec_ref(v_s_1478_);
return v_res_1480_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1481_; lean_object* v___f_1482_; 
v___x_1481_ = lean_alloc_closure((void*)(l_instDecidableEqChar___boxed), 2, 0);
v___f_1482_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1482_, 0, v___x_1481_);
return v___f_1482_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__1___boxed__const__1(void){
_start:
{
uint32_t v___x_1483_; lean_object* v___x_1484_; 
v___x_1483_ = 92;
v___x_1484_ = lean_box_uint32(v___x_1483_);
return v___x_1484_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1485_ = lean_box(0);
v___x_1486_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__1___boxed__const__1;
v___x_1487_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1487_, 0, v___x_1486_);
lean_ctor_set(v___x_1487_, 1, v___x_1485_);
return v___x_1487_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__2___boxed__const__1(void){
_start:
{
uint32_t v___x_1488_; lean_object* v___x_1489_; 
v___x_1488_ = 47;
v___x_1489_ = lean_box_uint32(v___x_1488_);
return v___x_1489_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1490_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__1);
v___x_1491_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__2___boxed__const__1;
v___x_1492_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1492_, 0, v___x_1491_);
lean_ctor_set(v___x_1492_, 1, v___x_1490_);
return v___x_1492_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg(lean_object* v_s_1493_, lean_object* v_a_1494_, uint8_t v_b_1495_){
_start:
{
lean_object* v_str_1496_; lean_object* v_startInclusive_1497_; lean_object* v_endExclusive_1498_; lean_object* v___x_1499_; uint8_t v___x_1500_; 
v_str_1496_ = lean_ctor_get(v_s_1493_, 0);
v_startInclusive_1497_ = lean_ctor_get(v_s_1493_, 1);
v_endExclusive_1498_ = lean_ctor_get(v_s_1493_, 2);
v___x_1499_ = lean_nat_sub(v_endExclusive_1498_, v_startInclusive_1497_);
v___x_1500_ = lean_nat_dec_eq(v_a_1494_, v___x_1499_);
lean_dec(v___x_1499_);
if (v___x_1500_ == 0)
{
lean_object* v___x_1501_; uint32_t v___x_1502_; lean_object* v___f_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; uint8_t v___x_1506_; 
v___x_1501_ = lean_nat_add(v_startInclusive_1497_, v_a_1494_);
lean_dec(v_a_1494_);
v___x_1502_ = lean_string_utf8_get_fast(v_str_1496_, v___x_1501_);
v___f_1503_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__0);
v___x_1504_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__2);
v___x_1505_ = lean_box_uint32(v___x_1502_);
v___x_1506_ = l_List_elem___redArg(v___f_1503_, v___x_1505_, v___x_1504_);
if (v___x_1506_ == 0)
{
lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1507_ = lean_string_utf8_next_fast(v_str_1496_, v___x_1501_);
lean_dec(v___x_1501_);
v___x_1508_ = lean_nat_sub(v___x_1507_, v_startInclusive_1497_);
v_a_1494_ = v___x_1508_;
v_b_1495_ = v___x_1506_;
goto _start;
}
else
{
lean_dec(v___x_1501_);
return v___x_1506_;
}
}
else
{
lean_dec(v_a_1494_);
return v_b_1495_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___boxed(lean_object* v_s_1510_, lean_object* v_a_1511_, lean_object* v_b_1512_){
_start:
{
uint8_t v_b_boxed_1513_; uint8_t v_res_1514_; lean_object* v_r_1515_; 
v_b_boxed_1513_ = lean_unbox(v_b_1512_);
v_res_1514_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg(v_s_1510_, v_a_1511_, v_b_boxed_1513_);
lean_dec_ref(v_s_1510_);
v_r_1515_ = lean_box(v_res_1514_);
return v_r_1515_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0(lean_object* v_s_1516_){
_start:
{
lean_object* v_searcher_1517_; uint8_t v___x_1518_; uint8_t v___x_1519_; 
v_searcher_1517_ = lean_unsigned_to_nat(0u);
v___x_1518_ = 0;
v___x_1519_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg(v_s_1516_, v_searcher_1517_, v___x_1518_);
return v___x_1519_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0___boxed(lean_object* v_s_1520_){
_start:
{
uint8_t v_res_1521_; lean_object* v_r_1522_; 
v_res_1521_ = l_String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0(v_s_1520_);
lean_dec_ref(v_s_1520_);
v_r_1522_ = lean_box(v_res_1521_);
return v_r_1522_;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__1(void){
_start:
{
lean_object* v___x_1524_; lean_object* v___f_1525_; 
v___x_1524_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
v___f_1525_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1525_, 0, v___x_1524_);
return v___f_1525_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName(lean_object* v_pkgName_1545_, lean_object* v_a_1546_){
_start:
{
uint8_t v___y_1559_; lean_object* v___x_1574_; lean_object* v___x_1575_; uint8_t v___x_1576_; 
v___x_1574_ = lean_string_utf8_byte_size(v_pkgName_1545_);
v___x_1575_ = lean_unsigned_to_nat(0u);
v___x_1576_ = lean_nat_dec_eq(v___x_1574_, v___x_1575_);
if (v___x_1576_ == 0)
{
lean_object* v___x_1577_; lean_object* v___x_1578_; uint8_t v___x_1579_; 
lean_inc_ref(v_pkgName_1545_);
v___x_1577_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1577_, 0, v_pkgName_1545_);
lean_ctor_set(v___x_1577_, 1, v___x_1575_);
lean_ctor_set(v___x_1577_, 2, v___x_1574_);
v___x_1578_ = l_String_Slice_Pos_skipWhile___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__1(v___x_1577_, v___x_1575_);
lean_dec_ref(v___x_1577_);
v___x_1579_ = lean_nat_dec_eq(v___x_1578_, v___x_1574_);
lean_dec(v___x_1578_);
v___y_1559_ = v___x_1579_;
goto v___jp_1558_;
}
else
{
v___y_1559_ = v___x_1576_;
goto v___jp_1558_;
}
v___jp_1548_:
{
lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; uint8_t v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1549_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__0));
v___x_1550_ = lean_string_append(v___x_1549_, v_pkgName_1545_);
lean_dec_ref(v_pkgName_1545_);
v___x_1551_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__6));
v___x_1552_ = lean_string_append(v___x_1550_, v___x_1551_);
v___x_1553_ = 3;
v___x_1554_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1554_, 0, v___x_1552_);
lean_ctor_set_uint8(v___x_1554_, sizeof(void*)*1, v___x_1553_);
v___x_1555_ = lean_array_get_size(v_a_1546_);
v___x_1556_ = lean_array_push(v_a_1546_, v___x_1554_);
v___x_1557_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1555_);
lean_ctor_set(v___x_1557_, 1, v___x_1556_);
return v___x_1557_;
}
v___jp_1558_:
{
if (v___y_1559_ == 0)
{
lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; uint8_t v___x_1563_; 
v___x_1560_ = lean_unsigned_to_nat(0u);
v___x_1561_ = lean_string_utf8_byte_size(v_pkgName_1545_);
lean_inc_ref(v_pkgName_1545_);
v___x_1562_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1562_, 0, v_pkgName_1545_);
lean_ctor_set(v___x_1562_, 1, v___x_1560_);
lean_ctor_set(v___x_1562_, 2, v___x_1561_);
v___x_1563_ = l_String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0(v___x_1562_);
lean_dec_ref(v___x_1562_);
if (v___x_1563_ == 0)
{
lean_object* v___f_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; uint8_t v___x_1567_; 
v___f_1564_ = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__1, &l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__1_once, _init_l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__1);
v___x_1565_ = l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents_spec__0(v_pkgName_1545_, v___x_1560_);
v___x_1566_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__8));
v___x_1567_ = l_List_elem___redArg(v___f_1564_, v___x_1565_, v___x_1566_);
if (v___x_1567_ == 0)
{
lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1568_ = lean_box(0);
v___x_1569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1569_, 0, v___x_1568_);
lean_ctor_set(v___x_1569_, 1, v_a_1546_);
return v___x_1569_;
}
else
{
lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1570_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__10));
v___x_1571_ = lean_array_get_size(v_a_1546_);
v___x_1572_ = lean_array_push(v_a_1546_, v___x_1570_);
v___x_1573_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1573_, 0, v___x_1571_);
lean_ctor_set(v___x_1573_, 1, v___x_1572_);
return v___x_1573_;
}
}
else
{
goto v___jp_1548_;
}
}
else
{
goto v___jp_1548_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___boxed(lean_object* v_pkgName_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_){
_start:
{
lean_object* v_res_1583_; 
v_res_1583_ = l___private_Lake_CLI_Init_0__Lake_validatePkgName(v_pkgName_1580_, v_a_1581_);
return v_res_1583_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0(lean_object* v_s_1584_, lean_object* v_inst_1585_, lean_object* v_R_1586_, lean_object* v_a_1587_, uint8_t v_b_1588_, lean_object* v_c_1589_){
_start:
{
uint8_t v___x_1590_; 
v___x_1590_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg(v_s_1584_, v_a_1587_, v_b_1588_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___boxed(lean_object* v_s_1591_, lean_object* v_inst_1592_, lean_object* v_R_1593_, lean_object* v_a_1594_, lean_object* v_b_1595_, lean_object* v_c_1596_){
_start:
{
uint8_t v_b_boxed_1597_; uint8_t v_res_1598_; lean_object* v_r_1599_; 
v_b_boxed_1597_ = lean_unbox(v_b_1595_);
v_res_1598_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0(v_s_1591_, v_inst_1592_, v_R_1593_, v_a_1594_, v_b_boxed_1597_, v_c_1596_);
lean_dec_ref(v_s_1591_);
v_r_1599_ = lean_box(v_res_1598_);
return v_r_1599_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__0(lean_object* v_a_1600_, lean_object* v_dir_1601_, lean_object* v_name_1602_, uint8_t v_tmp_1603_, uint8_t v_lang_1604_, lean_object* v_env_1605_, uint8_t v_offline_1606_){
_start:
{
lean_object* v___x_1611_; lean_object* v___y_1613_; lean_object* v___y_1630_; lean_object* v___y_1631_; lean_object* v___y_1635_; lean_object* v___y_1636_; lean_object* v___y_1640_; lean_object* v___y_1641_; uint8_t v_a_1642_; lean_object* v___y_1646_; lean_object* v___y_1647_; lean_object* v___y_1648_; lean_object* v___y_1649_; lean_object* v___y_1719_; lean_object* v___y_1720_; lean_object* v___y_1721_; lean_object* v___y_1722_; lean_object* v___y_1726_; lean_object* v___y_1727_; lean_object* v___y_1728_; lean_object* v___y_1729_; lean_object* v___y_1730_; lean_object* v___y_1732_; lean_object* v___y_1733_; lean_object* v___y_1734_; lean_object* v___y_1735_; lean_object* v___y_1764_; lean_object* v___y_1765_; lean_object* v___y_1766_; lean_object* v___y_1767_; lean_object* v___y_1768_; lean_object* v___y_1770_; lean_object* v___y_1771_; lean_object* v___y_1772_; lean_object* v___y_1773_; uint8_t v_a_1774_; lean_object* v___y_1801_; lean_object* v___y_1802_; lean_object* v___y_1803_; lean_object* v___y_1804_; lean_object* v___y_1817_; lean_object* v___y_1818_; lean_object* v___y_1819_; lean_object* v___y_1820_; lean_object* v___y_1821_; lean_object* v___y_1822_; lean_object* v___y_1838_; lean_object* v___y_1839_; lean_object* v___y_1840_; lean_object* v___y_1841_; lean_object* v___y_1842_; uint8_t v_a_1843_; lean_object* v___y_1851_; lean_object* v___y_1852_; lean_object* v___y_1853_; lean_object* v___y_1854_; lean_object* v___y_1869_; lean_object* v___y_1870_; lean_object* v___y_1871_; lean_object* v___y_1872_; lean_object* v___y_1873_; lean_object* v___y_1874_; uint8_t v_a_1875_; lean_object* v___y_1909_; lean_object* v___y_1910_; lean_object* v___y_1911_; lean_object* v___y_1912_; lean_object* v___y_1913_; lean_object* v___y_1928_; lean_object* v___y_1929_; lean_object* v___y_1930_; lean_object* v___y_1931_; lean_object* v___y_1932_; lean_object* v___y_1934_; lean_object* v___y_1935_; lean_object* v___y_1936_; lean_object* v___y_1937_; lean_object* v___y_1938_; lean_object* v___y_1939_; lean_object* v___y_1940_; lean_object* v___y_1956_; lean_object* v___y_1957_; lean_object* v___y_1958_; lean_object* v___y_1959_; lean_object* v___y_1960_; lean_object* v___y_1961_; lean_object* v___y_1969_; lean_object* v___y_1970_; lean_object* v___y_1971_; lean_object* v___y_1972_; lean_object* v___y_1973_; lean_object* v___y_1974_; lean_object* v___y_1975_; uint8_t v_a_1976_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v_configFile_2008_; lean_object* v___y_2010_; lean_object* v___y_2011_; lean_object* v___y_2012_; lean_object* v___y_2013_; lean_object* v___y_2014_; lean_object* v_fst_2047_; lean_object* v_snd_2048_; lean_object* v___y_2056_; lean_object* v___y_2057_; uint8_t v_a_2058_; lean_object* v___y_2062_; lean_object* v___y_2063_; uint8_t v___y_2064_; lean_object* v___y_2080_; lean_object* v___y_2081_; uint8_t v_a_2082_; lean_object* v___y_2100_; uint8_t v___x_2101_; lean_object* v___x_2134_; uint8_t v___x_2135_; 
v___x_1611_ = l_Lake_defaultConfigFile;
v___x_2006_ = l_Lake_ConfigLang_fileExtension(v_lang_1604_);
v___x_2007_ = l_System_FilePath_addExtension(v___x_1611_, v___x_2006_);
lean_dec_ref(v___x_2006_);
lean_inc_ref(v_dir_1601_);
v_configFile_2008_ = l_Lake_joinRelative(v_dir_1601_, v___x_2007_);
v___x_2101_ = l_System_FilePath_pathExists(v_configFile_2008_);
v___x_2134_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_2135_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_2135_ == 0)
{
goto v___jp_2102_;
}
else
{
lean_object* v___x_2136_; uint8_t v___x_2137_; 
v___x_2136_ = lean_box(0);
v___x_2137_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (v___x_2137_ == 0)
{
if (v___x_2135_ == 0)
{
goto v___jp_2102_;
}
else
{
size_t v___x_2138_; size_t v___x_2139_; lean_object* v___x_2140_; 
v___x_2138_ = ((size_t)0ULL);
v___x_2139_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
v___x_2140_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_2134_, v___x_2138_, v___x_2139_, v___x_2136_, v_a_1600_);
if (lean_obj_tag(v___x_2140_) == 0)
{
lean_dec_ref(v___x_2140_);
goto v___jp_2102_;
}
else
{
lean_dec_ref(v_configFile_2008_);
lean_dec_ref(v_env_1605_);
lean_dec(v_name_1602_);
lean_dec_ref(v_dir_1601_);
return v___x_2140_;
}
}
}
else
{
size_t v___x_2141_; size_t v___x_2142_; lean_object* v___x_2143_; 
v___x_2141_ = ((size_t)0ULL);
v___x_2142_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
v___x_2143_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_2134_, v___x_2141_, v___x_2142_, v___x_2136_, v_a_1600_);
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_dec_ref(v___x_2143_);
goto v___jp_2102_;
}
else
{
lean_dec_ref(v_configFile_2008_);
lean_dec_ref(v_env_1605_);
lean_dec(v_name_1602_);
lean_dec_ref(v_dir_1601_);
return v___x_2143_;
}
}
}
v___jp_1608_:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1609_ = lean_box(0);
v___x_1610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1609_);
return v___x_1610_;
}
v___jp_1612_:
{
if (v_offline_1606_ == 0)
{
lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; 
v___x_1614_ = lean_box(0);
v___x_1615_ = lean_unsigned_to_nat(0u);
v___x_1616_ = lean_box(0);
v___x_1617_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__4));
lean_inc_ref(v_dir_1601_);
v___x_1618_ = l_Lake_joinRelative(v_dir_1601_, v___x_1617_);
lean_inc_ref(v___x_1618_);
v___x_1619_ = l_Lake_joinRelative(v___x_1618_, v___x_1611_);
v___x_1620_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__0));
v___x_1621_ = lean_box(1);
v___x_1622_ = l_Lean_Options_empty;
v___x_1623_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0));
v___x_1624_ = lean_alloc_ctor(0, 14, 3);
lean_ctor_set(v___x_1624_, 0, v_env_1605_);
lean_ctor_set(v___x_1624_, 1, v___x_1614_);
lean_ctor_set(v___x_1624_, 2, v_dir_1601_);
lean_ctor_set(v___x_1624_, 3, v___x_1615_);
lean_ctor_set(v___x_1624_, 4, v___x_1616_);
lean_ctor_set(v___x_1624_, 5, v___x_1617_);
lean_ctor_set(v___x_1624_, 6, v___x_1618_);
lean_ctor_set(v___x_1624_, 7, v___x_1611_);
lean_ctor_set(v___x_1624_, 8, v___x_1619_);
lean_ctor_set(v___x_1624_, 9, v___x_1620_);
lean_ctor_set(v___x_1624_, 10, v___x_1621_);
lean_ctor_set(v___x_1624_, 11, v___x_1622_);
lean_ctor_set(v___x_1624_, 12, v___x_1623_);
lean_ctor_set(v___x_1624_, 13, v___x_1623_);
lean_ctor_set_uint8(v___x_1624_, sizeof(void*)*14, v_offline_1606_);
lean_ctor_set_uint8(v___x_1624_, sizeof(void*)*14 + 1, v_offline_1606_);
lean_ctor_set_uint8(v___x_1624_, sizeof(void*)*14 + 2, v_offline_1606_);
v___x_1625_ = l_Lean_NameSet_empty;
v___x_1626_ = l_Lake_updateManifest(v___x_1624_, v___x_1625_, v___y_1613_);
return v___x_1626_;
}
else
{
lean_object* v___x_1627_; lean_object* v___x_1628_; 
lean_dec_ref(v_env_1605_);
lean_dec_ref(v_dir_1601_);
v___x_1627_ = lean_box(0);
v___x_1628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1628_, 0, v___x_1627_);
return v___x_1628_;
}
}
v___jp_1629_:
{
if (lean_obj_tag(v___y_1631_) == 0)
{
lean_object* v___x_1632_; lean_object* v___x_1633_; 
v___x_1632_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__2));
lean_inc_ref(v___y_1630_);
v___x_1633_ = lean_apply_2(v___y_1630_, v___x_1632_, lean_box(0));
v___y_1613_ = v___y_1630_;
goto v___jp_1612_;
}
else
{
lean_dec_ref(v___y_1631_);
v___y_1613_ = v___y_1630_;
goto v___jp_1612_;
}
}
v___jp_1634_:
{
switch(v_tmp_1603_)
{
case 3:
{
v___y_1630_ = v___y_1636_;
v___y_1631_ = v___y_1635_;
goto v___jp_1629_;
}
case 4:
{
v___y_1630_ = v___y_1636_;
v___y_1631_ = v___y_1635_;
goto v___jp_1629_;
}
default: 
{
lean_object* v___x_1637_; lean_object* v___x_1638_; 
lean_dec(v___y_1635_);
lean_dec_ref(v_env_1605_);
lean_dec_ref(v_dir_1601_);
v___x_1637_ = lean_box(0);
v___x_1638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1638_, 0, v___x_1637_);
return v___x_1638_;
}
}
}
v___jp_1639_:
{
if (v_a_1642_ == 0)
{
lean_object* v___x_1643_; lean_object* v___x_1644_; 
v___x_1643_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__4));
lean_inc_ref(v___y_1640_);
v___x_1644_ = lean_apply_2(v___y_1640_, v___x_1643_, lean_box(0));
v___y_1635_ = v___y_1641_;
v___y_1636_ = v___y_1640_;
goto v___jp_1634_;
}
else
{
v___y_1635_ = v___y_1641_;
v___y_1636_ = v___y_1640_;
goto v___jp_1634_;
}
}
v___jp_1645_:
{
lean_object* v___x_1650_; lean_object* v___x_1651_; uint8_t v___x_1652_; lean_object* v___x_1653_; 
v___x_1650_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__5));
lean_inc_ref(v_dir_1601_);
v___x_1651_ = l_Lake_joinRelative(v_dir_1601_, v___x_1650_);
v___x_1652_ = 4;
v___x_1653_ = lean_io_prim_handle_mk(v___x_1651_, v___x_1652_);
lean_dec_ref(v___x_1651_);
if (lean_obj_tag(v___x_1653_) == 0)
{
lean_object* v_a_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
v_a_1654_ = lean_ctor_get(v___x_1653_, 0);
lean_inc(v_a_1654_);
lean_dec_ref(v___x_1653_);
v___x_1655_ = l___private_Lake_CLI_Init_0__Lake_gitignoreContents;
v___x_1656_ = lean_io_prim_handle_put_str(v_a_1654_, v___x_1655_);
lean_dec(v_a_1654_);
if (lean_obj_tag(v___x_1656_) == 0)
{
lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; uint8_t v___x_1661_; 
lean_dec_ref(v___x_1656_);
v___x_1657_ = l_Lake_toolchainFileName;
lean_inc_ref(v_dir_1601_);
v___x_1658_ = l_Lake_joinRelative(v_dir_1601_, v___x_1657_);
v___x_1659_ = lean_string_utf8_byte_size(v___y_1646_);
v___x_1660_ = lean_unsigned_to_nat(0u);
v___x_1661_ = lean_nat_dec_eq(v___x_1659_, v___x_1660_);
if (v___x_1661_ == 0)
{
lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; 
lean_dec_ref(v___y_1648_);
v___x_1662_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__2));
v___x_1663_ = lean_string_append(v___y_1646_, v___x_1662_);
v___x_1664_ = l_IO_FS_writeFile(v___x_1658_, v___x_1663_);
lean_dec_ref(v___x_1663_);
lean_dec_ref(v___x_1658_);
if (lean_obj_tag(v___x_1664_) == 0)
{
lean_dec_ref(v___x_1664_);
v___y_1635_ = v___y_1647_;
v___y_1636_ = v___y_1649_;
goto v___jp_1634_;
}
else
{
lean_object* v_a_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1677_; 
lean_dec(v___y_1647_);
lean_dec_ref(v_env_1605_);
lean_dec_ref(v_dir_1601_);
v_a_1665_ = lean_ctor_get(v___x_1664_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1664_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1667_ = v___x_1664_;
v_isShared_1668_ = v_isSharedCheck_1677_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_a_1665_);
lean_dec(v___x_1664_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1677_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1669_; uint8_t v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1675_; 
v___x_1669_ = lean_io_error_to_string(v_a_1665_);
v___x_1670_ = 3;
v___x_1671_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1671_, 0, v___x_1669_);
lean_ctor_set_uint8(v___x_1671_, sizeof(void*)*1, v___x_1670_);
lean_inc_ref(v___y_1649_);
v___x_1672_ = lean_apply_2(v___y_1649_, v___x_1671_, lean_box(0));
v___x_1673_ = lean_box(0);
if (v_isShared_1668_ == 0)
{
lean_ctor_set(v___x_1667_, 0, v___x_1673_);
v___x_1675_ = v___x_1667_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v___x_1673_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
}
else
{
lean_object* v_githash_1678_; lean_object* v___x_1679_; uint8_t v___x_1680_; 
lean_dec_ref(v___y_1646_);
v_githash_1678_ = lean_ctor_get(v___y_1648_, 1);
lean_inc_ref(v_githash_1678_);
lean_dec_ref(v___y_1648_);
v___x_1679_ = lean_string_utf8_byte_size(v_githash_1678_);
lean_dec_ref(v_githash_1678_);
v___x_1680_ = lean_nat_dec_eq(v___x_1679_, v___x_1660_);
if (v___x_1680_ == 0)
{
uint8_t v___x_1681_; lean_object* v___x_1682_; uint8_t v___x_1683_; 
v___x_1681_ = l_System_FilePath_pathExists(v___x_1658_);
lean_dec_ref(v___x_1658_);
v___x_1682_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1683_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1683_ == 0)
{
v___y_1640_ = v___y_1649_;
v___y_1641_ = v___y_1647_;
v_a_1642_ = v___x_1681_;
goto v___jp_1639_;
}
else
{
lean_object* v___x_1684_; uint8_t v___x_1685_; 
v___x_1684_ = lean_box(0);
v___x_1685_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (v___x_1685_ == 0)
{
if (v___x_1683_ == 0)
{
v___y_1640_ = v___y_1649_;
v___y_1641_ = v___y_1647_;
v_a_1642_ = v___x_1681_;
goto v___jp_1639_;
}
else
{
size_t v___x_1686_; size_t v___x_1687_; lean_object* v___x_1688_; 
v___x_1686_ = ((size_t)0ULL);
v___x_1687_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
v___x_1688_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1682_, v___x_1686_, v___x_1687_, v___x_1684_, v___y_1649_);
if (lean_obj_tag(v___x_1688_) == 0)
{
lean_dec_ref(v___x_1688_);
v___y_1640_ = v___y_1649_;
v___y_1641_ = v___y_1647_;
v_a_1642_ = v___x_1681_;
goto v___jp_1639_;
}
else
{
lean_dec(v___y_1647_);
lean_dec_ref(v_env_1605_);
lean_dec_ref(v_dir_1601_);
return v___x_1688_;
}
}
}
else
{
size_t v___x_1689_; size_t v___x_1690_; lean_object* v___x_1691_; 
v___x_1689_ = ((size_t)0ULL);
v___x_1690_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
v___x_1691_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1682_, v___x_1689_, v___x_1690_, v___x_1684_, v___y_1649_);
if (lean_obj_tag(v___x_1691_) == 0)
{
lean_dec_ref(v___x_1691_);
v___y_1640_ = v___y_1649_;
v___y_1641_ = v___y_1647_;
v_a_1642_ = v___x_1681_;
goto v___jp_1639_;
}
else
{
lean_dec(v___y_1647_);
lean_dec_ref(v_env_1605_);
lean_dec_ref(v_dir_1601_);
return v___x_1691_;
}
}
}
}
else
{
lean_dec_ref(v___x_1658_);
v___y_1635_ = v___y_1647_;
v___y_1636_ = v___y_1649_;
goto v___jp_1634_;
}
}
}
else
{
lean_object* v_a_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1704_; 
lean_dec_ref(v___y_1648_);
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1646_);
lean_dec_ref(v_env_1605_);
lean_dec_ref(v_dir_1601_);
v_a_1692_ = lean_ctor_get(v___x_1656_, 0);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1694_ = v___x_1656_;
v_isShared_1695_ = v_isSharedCheck_1704_;
goto v_resetjp_1693_;
}
else
{
lean_inc(v_a_1692_);
lean_dec(v___x_1656_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1704_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
lean_object* v___x_1696_; uint8_t v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1702_; 
v___x_1696_ = lean_io_error_to_string(v_a_1692_);
v___x_1697_ = 3;
v___x_1698_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1698_, 0, v___x_1696_);
lean_ctor_set_uint8(v___x_1698_, sizeof(void*)*1, v___x_1697_);
lean_inc_ref(v___y_1649_);
v___x_1699_ = lean_apply_2(v___y_1649_, v___x_1698_, lean_box(0));
v___x_1700_ = lean_box(0);
if (v_isShared_1695_ == 0)
{
lean_ctor_set(v___x_1694_, 0, v___x_1700_);
v___x_1702_ = v___x_1694_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v___x_1700_);
v___x_1702_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
return v___x_1702_;
}
}
}
}
else
{
lean_object* v_a_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1717_; 
lean_dec_ref(v___y_1648_);
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1646_);
lean_dec_ref(v_env_1605_);
lean_dec_ref(v_dir_1601_);
v_a_1705_ = lean_ctor_get(v___x_1653_, 0);
v_isSharedCheck_1717_ = !lean_is_exclusive(v___x_1653_);
if (v_isSharedCheck_1717_ == 0)
{
v___x_1707_ = v___x_1653_;
v_isShared_1708_ = v_isSharedCheck_1717_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_a_1705_);
lean_dec(v___x_1653_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1717_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1709_; uint8_t v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1715_; 
v___x_1709_ = lean_io_error_to_string(v_a_1705_);
v___x_1710_ = 3;
v___x_1711_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1711_, 0, v___x_1709_);
lean_ctor_set_uint8(v___x_1711_, sizeof(void*)*1, v___x_1710_);
lean_inc_ref(v___y_1649_);
v___x_1712_ = lean_apply_2(v___y_1649_, v___x_1711_, lean_box(0));
v___x_1713_ = lean_box(0);
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 0, v___x_1713_);
v___x_1715_ = v___x_1707_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v___x_1713_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
return v___x_1715_;
}
}
}
}
v___jp_1718_:
{
lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___x_1723_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12));
lean_inc_ref(v___y_1721_);
v___x_1724_ = lean_apply_2(v___y_1721_, v___x_1723_, lean_box(0));
v___y_1646_ = v___y_1719_;
v___y_1647_ = v___y_1720_;
v___y_1648_ = v___y_1722_;
v___y_1649_ = v___y_1721_;
goto v___jp_1645_;
}
v___jp_1725_:
{
if (lean_obj_tag(v___y_1730_) == 0)
{
lean_dec_ref(v___y_1730_);
v___y_1646_ = v___y_1726_;
v___y_1647_ = v___y_1727_;
v___y_1648_ = v___y_1729_;
v___y_1649_ = v___y_1728_;
goto v___jp_1645_;
}
else
{
lean_dec_ref(v___y_1730_);
v___y_1719_ = v___y_1726_;
v___y_1720_ = v___y_1727_;
v___y_1721_ = v___y_1728_;
v___y_1722_ = v___y_1729_;
goto v___jp_1718_;
}
}
v___jp_1731_:
{
lean_object* v___x_1736_; uint8_t v___x_1737_; 
v___x_1736_ = l_Lake_Git_upstreamBranch;
v___x_1737_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13);
if (v___x_1737_ == 0)
{
lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1738_ = lean_unsigned_to_nat(0u);
v___x_1739_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(v_dir_1601_);
v___x_1740_ = l_Lake_GitRepo_checkoutBranch(v___x_1736_, v_dir_1601_, v___x_1739_);
if (lean_obj_tag(v___x_1740_) == 0)
{
lean_object* v_a_1741_; lean_object* v___x_1742_; uint8_t v___x_1743_; 
v_a_1741_ = lean_ctor_get(v___x_1740_, 1);
lean_inc(v_a_1741_);
lean_dec_ref(v___x_1740_);
v___x_1742_ = lean_array_get_size(v_a_1741_);
v___x_1743_ = lean_nat_dec_lt(v___x_1738_, v___x_1742_);
if (v___x_1743_ == 0)
{
lean_dec(v_a_1741_);
v___y_1646_ = v___y_1732_;
v___y_1647_ = v___y_1733_;
v___y_1648_ = v___y_1735_;
v___y_1649_ = v___y_1734_;
goto v___jp_1645_;
}
else
{
lean_object* v___x_1744_; uint8_t v___x_1745_; 
v___x_1744_ = lean_box(0);
v___x_1745_ = lean_nat_dec_le(v___x_1742_, v___x_1742_);
if (v___x_1745_ == 0)
{
if (v___x_1743_ == 0)
{
lean_dec(v_a_1741_);
v___y_1646_ = v___y_1732_;
v___y_1647_ = v___y_1733_;
v___y_1648_ = v___y_1735_;
v___y_1649_ = v___y_1734_;
goto v___jp_1645_;
}
else
{
size_t v___x_1746_; size_t v___x_1747_; lean_object* v___x_1748_; 
v___x_1746_ = ((size_t)0ULL);
v___x_1747_ = lean_usize_of_nat(v___x_1742_);
v___x_1748_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1741_, v___x_1746_, v___x_1747_, v___x_1744_, v___y_1734_);
lean_dec(v_a_1741_);
if (lean_obj_tag(v___x_1748_) == 0)
{
lean_dec_ref(v___x_1748_);
v___y_1646_ = v___y_1732_;
v___y_1647_ = v___y_1733_;
v___y_1648_ = v___y_1735_;
v___y_1649_ = v___y_1734_;
goto v___jp_1645_;
}
else
{
v___y_1726_ = v___y_1732_;
v___y_1727_ = v___y_1733_;
v___y_1728_ = v___y_1734_;
v___y_1729_ = v___y_1735_;
v___y_1730_ = v___x_1748_;
goto v___jp_1725_;
}
}
}
else
{
size_t v___x_1749_; size_t v___x_1750_; lean_object* v___x_1751_; 
v___x_1749_ = ((size_t)0ULL);
v___x_1750_ = lean_usize_of_nat(v___x_1742_);
v___x_1751_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1741_, v___x_1749_, v___x_1750_, v___x_1744_, v___y_1734_);
lean_dec(v_a_1741_);
if (lean_obj_tag(v___x_1751_) == 0)
{
lean_dec_ref(v___x_1751_);
v___y_1646_ = v___y_1732_;
v___y_1647_ = v___y_1733_;
v___y_1648_ = v___y_1735_;
v___y_1649_ = v___y_1734_;
goto v___jp_1645_;
}
else
{
v___y_1726_ = v___y_1732_;
v___y_1727_ = v___y_1733_;
v___y_1728_ = v___y_1734_;
v___y_1729_ = v___y_1735_;
v___y_1730_ = v___x_1751_;
goto v___jp_1725_;
}
}
}
}
else
{
lean_object* v_a_1752_; lean_object* v___x_1753_; uint8_t v___x_1754_; 
v_a_1752_ = lean_ctor_get(v___x_1740_, 1);
lean_inc(v_a_1752_);
lean_dec_ref(v___x_1740_);
v___x_1753_ = lean_array_get_size(v_a_1752_);
v___x_1754_ = lean_nat_dec_lt(v___x_1738_, v___x_1753_);
if (v___x_1754_ == 0)
{
lean_dec(v_a_1752_);
v___y_1719_ = v___y_1732_;
v___y_1720_ = v___y_1733_;
v___y_1721_ = v___y_1734_;
v___y_1722_ = v___y_1735_;
goto v___jp_1718_;
}
else
{
lean_object* v___x_1755_; uint8_t v___x_1756_; 
v___x_1755_ = lean_box(0);
v___x_1756_ = lean_nat_dec_le(v___x_1753_, v___x_1753_);
if (v___x_1756_ == 0)
{
if (v___x_1754_ == 0)
{
lean_dec(v_a_1752_);
v___y_1719_ = v___y_1732_;
v___y_1720_ = v___y_1733_;
v___y_1721_ = v___y_1734_;
v___y_1722_ = v___y_1735_;
goto v___jp_1718_;
}
else
{
size_t v___x_1757_; size_t v___x_1758_; lean_object* v___x_1759_; 
v___x_1757_ = ((size_t)0ULL);
v___x_1758_ = lean_usize_of_nat(v___x_1753_);
v___x_1759_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1752_, v___x_1757_, v___x_1758_, v___x_1755_, v___y_1734_);
lean_dec(v_a_1752_);
if (lean_obj_tag(v___x_1759_) == 0)
{
lean_dec_ref(v___x_1759_);
v___y_1719_ = v___y_1732_;
v___y_1720_ = v___y_1733_;
v___y_1721_ = v___y_1734_;
v___y_1722_ = v___y_1735_;
goto v___jp_1718_;
}
else
{
v___y_1726_ = v___y_1732_;
v___y_1727_ = v___y_1733_;
v___y_1728_ = v___y_1734_;
v___y_1729_ = v___y_1735_;
v___y_1730_ = v___x_1759_;
goto v___jp_1725_;
}
}
}
else
{
size_t v___x_1760_; size_t v___x_1761_; lean_object* v___x_1762_; 
v___x_1760_ = ((size_t)0ULL);
v___x_1761_ = lean_usize_of_nat(v___x_1753_);
v___x_1762_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1752_, v___x_1760_, v___x_1761_, v___x_1755_, v___y_1734_);
lean_dec(v_a_1752_);
if (lean_obj_tag(v___x_1762_) == 0)
{
lean_dec_ref(v___x_1762_);
v___y_1719_ = v___y_1732_;
v___y_1720_ = v___y_1733_;
v___y_1721_ = v___y_1734_;
v___y_1722_ = v___y_1735_;
goto v___jp_1718_;
}
else
{
v___y_1726_ = v___y_1732_;
v___y_1727_ = v___y_1733_;
v___y_1728_ = v___y_1734_;
v___y_1729_ = v___y_1735_;
v___y_1730_ = v___x_1762_;
goto v___jp_1725_;
}
}
}
}
}
else
{
v___y_1646_ = v___y_1732_;
v___y_1647_ = v___y_1733_;
v___y_1648_ = v___y_1735_;
v___y_1649_ = v___y_1734_;
goto v___jp_1645_;
}
}
v___jp_1763_:
{
if (lean_obj_tag(v___y_1768_) == 0)
{
lean_dec_ref(v___y_1768_);
v___y_1732_ = v___y_1764_;
v___y_1733_ = v___y_1765_;
v___y_1734_ = v___y_1766_;
v___y_1735_ = v___y_1767_;
goto v___jp_1731_;
}
else
{
lean_dec_ref(v___y_1768_);
v___y_1719_ = v___y_1764_;
v___y_1720_ = v___y_1765_;
v___y_1721_ = v___y_1766_;
v___y_1722_ = v___y_1767_;
goto v___jp_1718_;
}
}
v___jp_1769_:
{
if (v_a_1774_ == 0)
{
lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; 
v___x_1775_ = lean_unsigned_to_nat(0u);
v___x_1776_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(v_dir_1601_);
v___x_1777_ = l_Lake_GitRepo_quietInit(v_dir_1601_, v___x_1776_);
if (lean_obj_tag(v___x_1777_) == 0)
{
lean_object* v_a_1778_; lean_object* v___x_1779_; uint8_t v___x_1780_; 
v_a_1778_ = lean_ctor_get(v___x_1777_, 1);
lean_inc(v_a_1778_);
lean_dec_ref(v___x_1777_);
v___x_1779_ = lean_array_get_size(v_a_1778_);
v___x_1780_ = lean_nat_dec_lt(v___x_1775_, v___x_1779_);
if (v___x_1780_ == 0)
{
lean_dec(v_a_1778_);
v___y_1732_ = v___y_1770_;
v___y_1733_ = v___y_1771_;
v___y_1734_ = v___y_1772_;
v___y_1735_ = v___y_1773_;
goto v___jp_1731_;
}
else
{
lean_object* v___x_1781_; uint8_t v___x_1782_; 
v___x_1781_ = lean_box(0);
v___x_1782_ = lean_nat_dec_le(v___x_1779_, v___x_1779_);
if (v___x_1782_ == 0)
{
if (v___x_1780_ == 0)
{
lean_dec(v_a_1778_);
v___y_1732_ = v___y_1770_;
v___y_1733_ = v___y_1771_;
v___y_1734_ = v___y_1772_;
v___y_1735_ = v___y_1773_;
goto v___jp_1731_;
}
else
{
size_t v___x_1783_; size_t v___x_1784_; lean_object* v___x_1785_; 
v___x_1783_ = ((size_t)0ULL);
v___x_1784_ = lean_usize_of_nat(v___x_1779_);
v___x_1785_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1778_, v___x_1783_, v___x_1784_, v___x_1781_, v___y_1772_);
lean_dec(v_a_1778_);
if (lean_obj_tag(v___x_1785_) == 0)
{
lean_dec_ref(v___x_1785_);
v___y_1732_ = v___y_1770_;
v___y_1733_ = v___y_1771_;
v___y_1734_ = v___y_1772_;
v___y_1735_ = v___y_1773_;
goto v___jp_1731_;
}
else
{
v___y_1764_ = v___y_1770_;
v___y_1765_ = v___y_1771_;
v___y_1766_ = v___y_1772_;
v___y_1767_ = v___y_1773_;
v___y_1768_ = v___x_1785_;
goto v___jp_1763_;
}
}
}
else
{
size_t v___x_1786_; size_t v___x_1787_; lean_object* v___x_1788_; 
v___x_1786_ = ((size_t)0ULL);
v___x_1787_ = lean_usize_of_nat(v___x_1779_);
v___x_1788_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1778_, v___x_1786_, v___x_1787_, v___x_1781_, v___y_1772_);
lean_dec(v_a_1778_);
if (lean_obj_tag(v___x_1788_) == 0)
{
lean_dec_ref(v___x_1788_);
v___y_1732_ = v___y_1770_;
v___y_1733_ = v___y_1771_;
v___y_1734_ = v___y_1772_;
v___y_1735_ = v___y_1773_;
goto v___jp_1731_;
}
else
{
v___y_1764_ = v___y_1770_;
v___y_1765_ = v___y_1771_;
v___y_1766_ = v___y_1772_;
v___y_1767_ = v___y_1773_;
v___y_1768_ = v___x_1788_;
goto v___jp_1763_;
}
}
}
}
else
{
lean_object* v_a_1789_; lean_object* v___x_1790_; uint8_t v___x_1791_; 
v_a_1789_ = lean_ctor_get(v___x_1777_, 1);
lean_inc(v_a_1789_);
lean_dec_ref(v___x_1777_);
v___x_1790_ = lean_array_get_size(v_a_1789_);
v___x_1791_ = lean_nat_dec_lt(v___x_1775_, v___x_1790_);
if (v___x_1791_ == 0)
{
lean_dec(v_a_1789_);
v___y_1719_ = v___y_1770_;
v___y_1720_ = v___y_1771_;
v___y_1721_ = v___y_1772_;
v___y_1722_ = v___y_1773_;
goto v___jp_1718_;
}
else
{
lean_object* v___x_1792_; uint8_t v___x_1793_; 
v___x_1792_ = lean_box(0);
v___x_1793_ = lean_nat_dec_le(v___x_1790_, v___x_1790_);
if (v___x_1793_ == 0)
{
if (v___x_1791_ == 0)
{
lean_dec(v_a_1789_);
v___y_1719_ = v___y_1770_;
v___y_1720_ = v___y_1771_;
v___y_1721_ = v___y_1772_;
v___y_1722_ = v___y_1773_;
goto v___jp_1718_;
}
else
{
size_t v___x_1794_; size_t v___x_1795_; lean_object* v___x_1796_; 
v___x_1794_ = ((size_t)0ULL);
v___x_1795_ = lean_usize_of_nat(v___x_1790_);
v___x_1796_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1789_, v___x_1794_, v___x_1795_, v___x_1792_, v___y_1772_);
lean_dec(v_a_1789_);
if (lean_obj_tag(v___x_1796_) == 0)
{
lean_dec_ref(v___x_1796_);
v___y_1719_ = v___y_1770_;
v___y_1720_ = v___y_1771_;
v___y_1721_ = v___y_1772_;
v___y_1722_ = v___y_1773_;
goto v___jp_1718_;
}
else
{
v___y_1764_ = v___y_1770_;
v___y_1765_ = v___y_1771_;
v___y_1766_ = v___y_1772_;
v___y_1767_ = v___y_1773_;
v___y_1768_ = v___x_1796_;
goto v___jp_1763_;
}
}
}
else
{
size_t v___x_1797_; size_t v___x_1798_; lean_object* v___x_1799_; 
v___x_1797_ = ((size_t)0ULL);
v___x_1798_ = lean_usize_of_nat(v___x_1790_);
v___x_1799_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1789_, v___x_1797_, v___x_1798_, v___x_1792_, v___y_1772_);
lean_dec(v_a_1789_);
if (lean_obj_tag(v___x_1799_) == 0)
{
lean_dec_ref(v___x_1799_);
v___y_1719_ = v___y_1770_;
v___y_1720_ = v___y_1771_;
v___y_1721_ = v___y_1772_;
v___y_1722_ = v___y_1773_;
goto v___jp_1718_;
}
else
{
v___y_1764_ = v___y_1770_;
v___y_1765_ = v___y_1771_;
v___y_1766_ = v___y_1772_;
v___y_1767_ = v___y_1773_;
v___y_1768_ = v___x_1799_;
goto v___jp_1763_;
}
}
}
}
}
else
{
v___y_1646_ = v___y_1770_;
v___y_1647_ = v___y_1771_;
v___y_1648_ = v___y_1773_;
v___y_1649_ = v___y_1772_;
goto v___jp_1645_;
}
}
v___jp_1800_:
{
uint8_t v___x_1805_; lean_object* v___x_1806_; uint8_t v___x_1807_; 
lean_inc_ref(v_dir_1601_);
v___x_1805_ = l_Lake_GitRepo_insideWorkTree(v_dir_1601_);
v___x_1806_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1807_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1807_ == 0)
{
v___y_1770_ = v___y_1801_;
v___y_1771_ = v___y_1802_;
v___y_1772_ = v___y_1804_;
v___y_1773_ = v___y_1803_;
v_a_1774_ = v___x_1805_;
goto v___jp_1769_;
}
else
{
lean_object* v___x_1808_; uint8_t v___x_1809_; 
v___x_1808_ = lean_box(0);
v___x_1809_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (v___x_1809_ == 0)
{
if (v___x_1807_ == 0)
{
v___y_1770_ = v___y_1801_;
v___y_1771_ = v___y_1802_;
v___y_1772_ = v___y_1804_;
v___y_1773_ = v___y_1803_;
v_a_1774_ = v___x_1805_;
goto v___jp_1769_;
}
else
{
size_t v___x_1810_; size_t v___x_1811_; lean_object* v___x_1812_; 
v___x_1810_ = ((size_t)0ULL);
v___x_1811_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
v___x_1812_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1806_, v___x_1810_, v___x_1811_, v___x_1808_, v___y_1804_);
if (lean_obj_tag(v___x_1812_) == 0)
{
lean_dec_ref(v___x_1812_);
v___y_1770_ = v___y_1801_;
v___y_1771_ = v___y_1802_;
v___y_1772_ = v___y_1804_;
v___y_1773_ = v___y_1803_;
v_a_1774_ = v___x_1805_;
goto v___jp_1769_;
}
else
{
lean_dec_ref(v___y_1803_);
lean_dec(v___y_1802_);
lean_dec_ref(v___y_1801_);
lean_dec_ref(v_env_1605_);
lean_dec_ref(v_dir_1601_);
return v___x_1812_;
}
}
}
else
{
size_t v___x_1813_; size_t v___x_1814_; lean_object* v___x_1815_; 
v___x_1813_ = ((size_t)0ULL);
v___x_1814_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
v___x_1815_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1806_, v___x_1813_, v___x_1814_, v___x_1808_, v___y_1804_);
if (lean_obj_tag(v___x_1815_) == 0)
{
lean_dec_ref(v___x_1815_);
v___y_1770_ = v___y_1801_;
v___y_1771_ = v___y_1802_;
v___y_1772_ = v___y_1804_;
v___y_1773_ = v___y_1803_;
v_a_1774_ = v___x_1805_;
goto v___jp_1769_;
}
else
{
lean_dec_ref(v___y_1803_);
lean_dec(v___y_1802_);
lean_dec_ref(v___y_1801_);
lean_dec_ref(v_env_1605_);
lean_dec_ref(v_dir_1601_);
return v___x_1815_;
}
}
}
}
v___jp_1816_:
{
lean_object* v___x_1823_; 
v___x_1823_ = l_IO_FS_writeFile(v___y_1817_, v___y_1822_);
lean_dec_ref(v___y_1822_);
lean_dec_ref(v___y_1817_);
if (lean_obj_tag(v___x_1823_) == 0)
{
lean_dec_ref(v___x_1823_);
v___y_1801_ = v___y_1819_;
v___y_1802_ = v___y_1820_;
v___y_1803_ = v___y_1821_;
v___y_1804_ = v___y_1818_;
goto v___jp_1800_;
}
else
{
lean_object* v_a_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1836_; 
lean_dec_ref(v___y_1821_);
lean_dec(v___y_1820_);
lean_dec_ref(v___y_1819_);
lean_dec_ref(v_env_1605_);
lean_dec_ref(v_dir_1601_);
v_a_1824_ = lean_ctor_get(v___x_1823_, 0);
v_isSharedCheck_1836_ = !lean_is_exclusive(v___x_1823_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1826_ = v___x_1823_;
v_isShared_1827_ = v_isSharedCheck_1836_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_a_1824_);
lean_dec(v___x_1823_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1836_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1828_; uint8_t v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1834_; 
v___x_1828_ = lean_io_error_to_string(v_a_1824_);
v___x_1829_ = 3;
v___x_1830_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1830_, 0, v___x_1828_);
lean_ctor_set_uint8(v___x_1830_, sizeof(void*)*1, v___x_1829_);
lean_inc_ref(v___y_1818_);
v___x_1831_ = lean_apply_2(v___y_1818_, v___x_1830_, lean_box(0));
v___x_1832_ = lean_box(0);
if (v_isShared_1827_ == 0)
{
lean_ctor_set(v___x_1826_, 0, v___x_1832_);
v___x_1834_ = v___x_1826_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v___x_1832_);
v___x_1834_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
return v___x_1834_;
}
}
}
}
v___jp_1837_:
{
if (v_a_1843_ == 0)
{
uint8_t v___x_1844_; uint8_t v___x_1845_; 
v___x_1844_ = 4;
v___x_1845_ = l_Lake_instDecidableEqInitTemplate(v_tmp_1603_, v___x_1844_);
if (v___x_1845_ == 0)
{
lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1846_ = l___private_Lake_CLI_Init_0__Lake_dotlessName(v_name_1602_);
v___x_1847_ = l___private_Lake_CLI_Init_0__Lake_readmeFileContents(v___x_1846_);
lean_dec_ref(v___x_1846_);
v___y_1817_ = v___y_1838_;
v___y_1818_ = v___y_1839_;
v___y_1819_ = v___y_1840_;
v___y_1820_ = v___y_1841_;
v___y_1821_ = v___y_1842_;
v___y_1822_ = v___x_1847_;
goto v___jp_1816_;
}
else
{
lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___x_1848_ = l___private_Lake_CLI_Init_0__Lake_dotlessName(v_name_1602_);
v___x_1849_ = l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents(v___x_1848_);
lean_dec_ref(v___x_1848_);
v___y_1817_ = v___y_1838_;
v___y_1818_ = v___y_1839_;
v___y_1819_ = v___y_1840_;
v___y_1820_ = v___y_1841_;
v___y_1821_ = v___y_1842_;
v___y_1822_ = v___x_1849_;
goto v___jp_1816_;
}
}
else
{
lean_dec_ref(v___y_1838_);
lean_dec(v_name_1602_);
v___y_1801_ = v___y_1840_;
v___y_1802_ = v___y_1841_;
v___y_1803_ = v___y_1842_;
v___y_1804_ = v___y_1839_;
goto v___jp_1800_;
}
}
v___jp_1850_:
{
lean_object* v___x_1855_; lean_object* v___x_1856_; uint8_t v___x_1857_; lean_object* v___x_1858_; uint8_t v___x_1859_; 
v___x_1855_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__14));
lean_inc_ref(v_dir_1601_);
v___x_1856_ = l_Lake_joinRelative(v_dir_1601_, v___x_1855_);
v___x_1857_ = l_System_FilePath_pathExists(v___x_1856_);
v___x_1858_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1859_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1859_ == 0)
{
v___y_1838_ = v___x_1856_;
v___y_1839_ = v___y_1854_;
v___y_1840_ = v___y_1851_;
v___y_1841_ = v___y_1852_;
v___y_1842_ = v___y_1853_;
v_a_1843_ = v___x_1857_;
goto v___jp_1837_;
}
else
{
lean_object* v___x_1860_; uint8_t v___x_1861_; 
v___x_1860_ = lean_box(0);
v___x_1861_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (v___x_1861_ == 0)
{
if (v___x_1859_ == 0)
{
v___y_1838_ = v___x_1856_;
v___y_1839_ = v___y_1854_;
v___y_1840_ = v___y_1851_;
v___y_1841_ = v___y_1852_;
v___y_1842_ = v___y_1853_;
v_a_1843_ = v___x_1857_;
goto v___jp_1837_;
}
else
{
size_t v___x_1862_; size_t v___x_1863_; lean_object* v___x_1864_; 
v___x_1862_ = ((size_t)0ULL);
v___x_1863_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
v___x_1864_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1858_, v___x_1862_, v___x_1863_, v___x_1860_, v___y_1854_);
if (lean_obj_tag(v___x_1864_) == 0)
{
lean_dec_ref(v___x_1864_);
v___y_1838_ = v___x_1856_;
v___y_1839_ = v___y_1854_;
v___y_1840_ = v___y_1851_;
v___y_1841_ = v___y_1852_;
v___y_1842_ = v___y_1853_;
v_a_1843_ = v___x_1857_;
goto v___jp_1837_;
}
else
{
lean_dec_ref(v___x_1856_);
lean_dec_ref(v___y_1853_);
lean_dec(v___y_1852_);
lean_dec_ref(v___y_1851_);
lean_dec_ref(v_env_1605_);
lean_dec(v_name_1602_);
lean_dec_ref(v_dir_1601_);
return v___x_1864_;
}
}
}
else
{
size_t v___x_1865_; size_t v___x_1866_; lean_object* v___x_1867_; 
v___x_1865_ = ((size_t)0ULL);
v___x_1866_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
v___x_1867_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1858_, v___x_1865_, v___x_1866_, v___x_1860_, v___y_1854_);
if (lean_obj_tag(v___x_1867_) == 0)
{
lean_dec_ref(v___x_1867_);
v___y_1838_ = v___x_1856_;
v___y_1839_ = v___y_1854_;
v___y_1840_ = v___y_1851_;
v___y_1841_ = v___y_1852_;
v___y_1842_ = v___y_1853_;
v_a_1843_ = v___x_1857_;
goto v___jp_1837_;
}
else
{
lean_dec_ref(v___x_1856_);
lean_dec_ref(v___y_1853_);
lean_dec(v___y_1852_);
lean_dec_ref(v___y_1851_);
lean_dec_ref(v_env_1605_);
lean_dec(v_name_1602_);
lean_dec_ref(v_dir_1601_);
return v___x_1867_;
}
}
}
}
v___jp_1868_:
{
if (v_a_1875_ == 0)
{
uint8_t v___x_1876_; uint8_t v___x_1877_; 
v___x_1876_ = 1;
v___x_1877_ = l_Lake_instDecidableEqInitTemplate(v_tmp_1603_, v___x_1876_);
if (v___x_1877_ == 0)
{
lean_object* v___x_1878_; lean_object* v___x_1879_; 
v___x_1878_ = l___private_Lake_CLI_Init_0__Lake_mainFileContents(v___y_1871_);
v___x_1879_ = l_IO_FS_writeFile(v___y_1870_, v___x_1878_);
lean_dec_ref(v___x_1878_);
lean_dec_ref(v___y_1870_);
if (lean_obj_tag(v___x_1879_) == 0)
{
lean_dec_ref(v___x_1879_);
v___y_1851_ = v___y_1872_;
v___y_1852_ = v___y_1873_;
v___y_1853_ = v___y_1874_;
v___y_1854_ = v___y_1869_;
goto v___jp_1850_;
}
else
{
lean_object* v_a_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1892_; 
lean_dec_ref(v___y_1874_);
lean_dec(v___y_1873_);
lean_dec_ref(v___y_1872_);
lean_dec_ref(v_env_1605_);
lean_dec(v_name_1602_);
lean_dec_ref(v_dir_1601_);
v_a_1880_ = lean_ctor_get(v___x_1879_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1879_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1882_ = v___x_1879_;
v_isShared_1883_ = v_isSharedCheck_1892_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_a_1880_);
lean_dec(v___x_1879_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1892_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1884_; uint8_t v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1890_; 
v___x_1884_ = lean_io_error_to_string(v_a_1880_);
v___x_1885_ = 3;
v___x_1886_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1886_, 0, v___x_1884_);
lean_ctor_set_uint8(v___x_1886_, sizeof(void*)*1, v___x_1885_);
lean_inc_ref(v___y_1869_);
v___x_1887_ = lean_apply_2(v___y_1869_, v___x_1886_, lean_box(0));
v___x_1888_ = lean_box(0);
if (v_isShared_1883_ == 0)
{
lean_ctor_set(v___x_1882_, 0, v___x_1888_);
v___x_1890_ = v___x_1882_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v___x_1888_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
return v___x_1890_;
}
}
}
}
else
{
lean_object* v___x_1893_; lean_object* v___x_1894_; 
lean_dec(v___y_1871_);
v___x_1893_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_exeFileContents___closed__0));
v___x_1894_ = l_IO_FS_writeFile(v___y_1870_, v___x_1893_);
lean_dec_ref(v___y_1870_);
if (lean_obj_tag(v___x_1894_) == 0)
{
lean_dec_ref(v___x_1894_);
v___y_1851_ = v___y_1872_;
v___y_1852_ = v___y_1873_;
v___y_1853_ = v___y_1874_;
v___y_1854_ = v___y_1869_;
goto v___jp_1850_;
}
else
{
lean_object* v_a_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1907_; 
lean_dec_ref(v___y_1874_);
lean_dec(v___y_1873_);
lean_dec_ref(v___y_1872_);
lean_dec_ref(v_env_1605_);
lean_dec(v_name_1602_);
lean_dec_ref(v_dir_1601_);
v_a_1895_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_1907_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1907_ == 0)
{
v___x_1897_ = v___x_1894_;
v_isShared_1898_ = v_isSharedCheck_1907_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_a_1895_);
lean_dec(v___x_1894_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1907_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v___x_1899_; uint8_t v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1905_; 
v___x_1899_ = lean_io_error_to_string(v_a_1895_);
v___x_1900_ = 3;
v___x_1901_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1901_, 0, v___x_1899_);
lean_ctor_set_uint8(v___x_1901_, sizeof(void*)*1, v___x_1900_);
lean_inc_ref(v___y_1869_);
v___x_1902_ = lean_apply_2(v___y_1869_, v___x_1901_, lean_box(0));
v___x_1903_ = lean_box(0);
if (v_isShared_1898_ == 0)
{
lean_ctor_set(v___x_1897_, 0, v___x_1903_);
v___x_1905_ = v___x_1897_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v___x_1903_);
v___x_1905_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
return v___x_1905_;
}
}
}
}
}
else
{
lean_dec(v___y_1871_);
lean_dec_ref(v___y_1870_);
v___y_1851_ = v___y_1872_;
v___y_1852_ = v___y_1873_;
v___y_1853_ = v___y_1874_;
v___y_1854_ = v___y_1869_;
goto v___jp_1850_;
}
}
v___jp_1908_:
{
lean_object* v___x_1914_; lean_object* v___x_1915_; uint8_t v___x_1916_; lean_object* v___x_1917_; uint8_t v___x_1918_; 
v___x_1914_ = l___private_Lake_CLI_Init_0__Lake_mainFileName;
lean_inc_ref(v_dir_1601_);
v___x_1915_ = l_Lake_joinRelative(v_dir_1601_, v___x_1914_);
v___x_1916_ = l_System_FilePath_pathExists(v___x_1915_);
v___x_1917_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1918_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1918_ == 0)
{
v___y_1869_ = v___y_1909_;
v___y_1870_ = v___x_1915_;
v___y_1871_ = v___y_1910_;
v___y_1872_ = v___y_1911_;
v___y_1873_ = v___y_1912_;
v___y_1874_ = v___y_1913_;
v_a_1875_ = v___x_1916_;
goto v___jp_1868_;
}
else
{
lean_object* v___x_1919_; uint8_t v___x_1920_; 
v___x_1919_ = lean_box(0);
v___x_1920_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (v___x_1920_ == 0)
{
if (v___x_1918_ == 0)
{
v___y_1869_ = v___y_1909_;
v___y_1870_ = v___x_1915_;
v___y_1871_ = v___y_1910_;
v___y_1872_ = v___y_1911_;
v___y_1873_ = v___y_1912_;
v___y_1874_ = v___y_1913_;
v_a_1875_ = v___x_1916_;
goto v___jp_1868_;
}
else
{
size_t v___x_1921_; size_t v___x_1922_; lean_object* v___x_1923_; 
v___x_1921_ = ((size_t)0ULL);
v___x_1922_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
v___x_1923_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1917_, v___x_1921_, v___x_1922_, v___x_1919_, v___y_1909_);
if (lean_obj_tag(v___x_1923_) == 0)
{
lean_dec_ref(v___x_1923_);
v___y_1869_ = v___y_1909_;
v___y_1870_ = v___x_1915_;
v___y_1871_ = v___y_1910_;
v___y_1872_ = v___y_1911_;
v___y_1873_ = v___y_1912_;
v___y_1874_ = v___y_1913_;
v_a_1875_ = v___x_1916_;
goto v___jp_1868_;
}
else
{
lean_dec_ref(v___x_1915_);
lean_dec_ref(v___y_1913_);
lean_dec(v___y_1912_);
lean_dec_ref(v___y_1911_);
lean_dec(v___y_1910_);
lean_dec_ref(v_env_1605_);
lean_dec(v_name_1602_);
lean_dec_ref(v_dir_1601_);
return v___x_1923_;
}
}
}
else
{
size_t v___x_1924_; size_t v___x_1925_; lean_object* v___x_1926_; 
v___x_1924_ = ((size_t)0ULL);
v___x_1925_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
v___x_1926_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1917_, v___x_1924_, v___x_1925_, v___x_1919_, v___y_1909_);
if (lean_obj_tag(v___x_1926_) == 0)
{
lean_dec_ref(v___x_1926_);
v___y_1869_ = v___y_1909_;
v___y_1870_ = v___x_1915_;
v___y_1871_ = v___y_1910_;
v___y_1872_ = v___y_1911_;
v___y_1873_ = v___y_1912_;
v___y_1874_ = v___y_1913_;
v_a_1875_ = v___x_1916_;
goto v___jp_1868_;
}
else
{
lean_dec_ref(v___x_1915_);
lean_dec_ref(v___y_1913_);
lean_dec(v___y_1912_);
lean_dec_ref(v___y_1911_);
lean_dec(v___y_1910_);
lean_dec_ref(v_env_1605_);
lean_dec(v_name_1602_);
lean_dec_ref(v_dir_1601_);
return v___x_1926_;
}
}
}
}
v___jp_1927_:
{
switch(v_tmp_1603_)
{
case 0:
{
v___y_1909_ = v___y_1932_;
v___y_1910_ = v___y_1928_;
v___y_1911_ = v___y_1929_;
v___y_1912_ = v___y_1930_;
v___y_1913_ = v___y_1931_;
goto v___jp_1908_;
}
case 1:
{
v___y_1909_ = v___y_1932_;
v___y_1910_ = v___y_1928_;
v___y_1911_ = v___y_1929_;
v___y_1912_ = v___y_1930_;
v___y_1913_ = v___y_1931_;
goto v___jp_1908_;
}
default: 
{
lean_dec(v___y_1928_);
v___y_1851_ = v___y_1929_;
v___y_1852_ = v___y_1930_;
v___y_1853_ = v___y_1931_;
v___y_1854_ = v___y_1932_;
goto v___jp_1850_;
}
}
}
v___jp_1933_:
{
lean_object* v___x_1941_; 
v___x_1941_ = l_IO_FS_writeFile(v___y_1935_, v___y_1940_);
lean_dec_ref(v___y_1940_);
lean_dec_ref(v___y_1935_);
if (lean_obj_tag(v___x_1941_) == 0)
{
lean_dec_ref(v___x_1941_);
v___y_1928_ = v___y_1934_;
v___y_1929_ = v___y_1936_;
v___y_1930_ = v___y_1937_;
v___y_1931_ = v___y_1939_;
v___y_1932_ = v___y_1938_;
goto v___jp_1927_;
}
else
{
lean_object* v_a_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1954_; 
lean_dec_ref(v___y_1939_);
lean_dec(v___y_1937_);
lean_dec_ref(v___y_1936_);
lean_dec(v___y_1934_);
lean_dec_ref(v_env_1605_);
lean_dec(v_name_1602_);
lean_dec_ref(v_dir_1601_);
v_a_1942_ = lean_ctor_get(v___x_1941_, 0);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___x_1941_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1944_ = v___x_1941_;
v_isShared_1945_ = v_isSharedCheck_1954_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_a_1942_);
lean_dec(v___x_1941_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1954_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1946_; uint8_t v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1952_; 
v___x_1946_ = lean_io_error_to_string(v_a_1942_);
v___x_1947_ = 3;
v___x_1948_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1948_, 0, v___x_1946_);
lean_ctor_set_uint8(v___x_1948_, sizeof(void*)*1, v___x_1947_);
lean_inc_ref(v___y_1938_);
v___x_1949_ = lean_apply_2(v___y_1938_, v___x_1948_, lean_box(0));
v___x_1950_ = lean_box(0);
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 0, v___x_1950_);
v___x_1952_ = v___x_1944_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v___x_1950_);
v___x_1952_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
return v___x_1952_;
}
}
}
}
v___jp_1955_:
{
uint8_t v___x_1962_; uint8_t v___x_1963_; 
v___x_1962_ = 4;
v___x_1963_ = l_Lake_instDecidableEqInitTemplate(v_tmp_1603_, v___x_1962_);
if (v___x_1963_ == 0)
{
uint8_t v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; 
v___x_1964_ = 1;
lean_inc_n(v___y_1957_, 2);
v___x_1965_ = l_Lean_Name_toString(v___y_1957_, v___x_1964_);
v___x_1966_ = l___private_Lake_CLI_Init_0__Lake_libRootFileContents(v___x_1965_, v___y_1957_);
lean_dec_ref(v___x_1965_);
v___y_1934_ = v___y_1957_;
v___y_1935_ = v___y_1956_;
v___y_1936_ = v___y_1958_;
v___y_1937_ = v___y_1959_;
v___y_1938_ = v___y_1961_;
v___y_1939_ = v___y_1960_;
v___y_1940_ = v___x_1966_;
goto v___jp_1933_;
}
else
{
lean_object* v___x_1967_; 
lean_inc(v___y_1957_);
v___x_1967_ = l___private_Lake_CLI_Init_0__Lake_mathLibRootFileContents(v___y_1957_);
v___y_1934_ = v___y_1957_;
v___y_1935_ = v___y_1956_;
v___y_1936_ = v___y_1958_;
v___y_1937_ = v___y_1959_;
v___y_1938_ = v___y_1961_;
v___y_1939_ = v___y_1960_;
v___y_1940_ = v___x_1967_;
goto v___jp_1933_;
}
}
v___jp_1968_:
{
if (v_a_1976_ == 0)
{
lean_object* v___x_1977_; 
v___x_1977_ = l_IO_FS_createDirAll(v___y_1969_);
if (lean_obj_tag(v___x_1977_) == 0)
{
lean_object* v___x_1978_; lean_object* v___x_1979_; 
lean_dec_ref(v___x_1977_);
v___x_1978_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_basicFileContents___closed__0));
v___x_1979_ = l_IO_FS_writeFile(v___y_1975_, v___x_1978_);
lean_dec_ref(v___y_1975_);
if (lean_obj_tag(v___x_1979_) == 0)
{
lean_dec_ref(v___x_1979_);
v___y_1956_ = v___y_1971_;
v___y_1957_ = v___y_1970_;
v___y_1958_ = v___y_1972_;
v___y_1959_ = v___y_1973_;
v___y_1960_ = v___y_1974_;
v___y_1961_ = v_a_1600_;
goto v___jp_1955_;
}
else
{
lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1992_; 
lean_dec_ref(v___y_1974_);
lean_dec(v___y_1973_);
lean_dec_ref(v___y_1972_);
lean_dec_ref(v___y_1971_);
lean_dec(v___y_1970_);
lean_dec_ref(v_env_1605_);
lean_dec(v_name_1602_);
lean_dec_ref(v_dir_1601_);
v_a_1980_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_1992_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_1992_ == 0)
{
v___x_1982_ = v___x_1979_;
v_isShared_1983_ = v_isSharedCheck_1992_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_dec(v___x_1979_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1992_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1984_; uint8_t v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1990_; 
v___x_1984_ = lean_io_error_to_string(v_a_1980_);
v___x_1985_ = 3;
v___x_1986_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1986_, 0, v___x_1984_);
lean_ctor_set_uint8(v___x_1986_, sizeof(void*)*1, v___x_1985_);
lean_inc_ref(v_a_1600_);
v___x_1987_ = lean_apply_2(v_a_1600_, v___x_1986_, lean_box(0));
v___x_1988_ = lean_box(0);
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 0, v___x_1988_);
v___x_1990_ = v___x_1982_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v___x_1988_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
return v___x_1990_;
}
}
}
}
else
{
lean_object* v_a_1993_; lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2005_; 
lean_dec_ref(v___y_1975_);
lean_dec_ref(v___y_1974_);
lean_dec(v___y_1973_);
lean_dec_ref(v___y_1972_);
lean_dec_ref(v___y_1971_);
lean_dec(v___y_1970_);
lean_dec_ref(v_env_1605_);
lean_dec(v_name_1602_);
lean_dec_ref(v_dir_1601_);
v_a_1993_ = lean_ctor_get(v___x_1977_, 0);
v_isSharedCheck_2005_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_2005_ == 0)
{
v___x_1995_ = v___x_1977_;
v_isShared_1996_ = v_isSharedCheck_2005_;
goto v_resetjp_1994_;
}
else
{
lean_inc(v_a_1993_);
lean_dec(v___x_1977_);
v___x_1995_ = lean_box(0);
v_isShared_1996_ = v_isSharedCheck_2005_;
goto v_resetjp_1994_;
}
v_resetjp_1994_:
{
lean_object* v___x_1997_; uint8_t v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2003_; 
v___x_1997_ = lean_io_error_to_string(v_a_1993_);
v___x_1998_ = 3;
v___x_1999_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1999_, 0, v___x_1997_);
lean_ctor_set_uint8(v___x_1999_, sizeof(void*)*1, v___x_1998_);
lean_inc_ref(v_a_1600_);
v___x_2000_ = lean_apply_2(v_a_1600_, v___x_1999_, lean_box(0));
v___x_2001_ = lean_box(0);
if (v_isShared_1996_ == 0)
{
lean_ctor_set(v___x_1995_, 0, v___x_2001_);
v___x_2003_ = v___x_1995_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v___x_2001_);
v___x_2003_ = v_reuseFailAlloc_2004_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
return v___x_2003_;
}
}
}
}
else
{
lean_dec_ref(v___y_1975_);
lean_dec_ref(v___y_1969_);
v___y_1956_ = v___y_1971_;
v___y_1957_ = v___y_1970_;
v___y_1958_ = v___y_1972_;
v___y_1959_ = v___y_1973_;
v___y_1960_ = v___y_1974_;
v___y_1961_ = v_a_1600_;
goto v___jp_1955_;
}
}
v___jp_2009_:
{
lean_object* v___x_2015_; lean_object* v___x_2016_; 
lean_inc(v___y_2014_);
lean_inc(v___y_2010_);
lean_inc(v_name_1602_);
v___x_2015_ = l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents(v_tmp_1603_, v_lang_1604_, v_name_1602_, v___y_2010_, v___y_2014_);
v___x_2016_ = l_IO_FS_writeFile(v_configFile_2008_, v___x_2015_);
lean_dec_ref(v___x_2015_);
lean_dec_ref(v_configFile_2008_);
if (lean_obj_tag(v___x_2016_) == 0)
{
lean_dec_ref(v___x_2016_);
if (lean_obj_tag(v___y_2012_) == 1)
{
lean_object* v_val_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; uint8_t v___x_2022_; lean_object* v___x_2023_; uint8_t v___x_2024_; 
v_val_2017_ = lean_ctor_get(v___y_2012_, 0);
lean_inc_n(v_val_2017_, 2);
lean_dec_ref(v___y_2012_);
v___x_2018_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0));
v___x_2019_ = l_System_FilePath_withExtension(v_val_2017_, v___x_2018_);
v___x_2020_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__15));
lean_inc_ref(v___x_2019_);
v___x_2021_ = l_Lake_joinRelative(v___x_2019_, v___x_2020_);
v___x_2022_ = l_System_FilePath_pathExists(v___x_2021_);
v___x_2023_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_2024_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_2024_ == 0)
{
v___y_1969_ = v___x_2019_;
v___y_1970_ = v___y_2010_;
v___y_1971_ = v_val_2017_;
v___y_1972_ = v___y_2011_;
v___y_1973_ = v___y_2014_;
v___y_1974_ = v___y_2013_;
v___y_1975_ = v___x_2021_;
v_a_1976_ = v___x_2022_;
goto v___jp_1968_;
}
else
{
lean_object* v___x_2025_; uint8_t v___x_2026_; 
v___x_2025_ = lean_box(0);
v___x_2026_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (v___x_2026_ == 0)
{
if (v___x_2024_ == 0)
{
v___y_1969_ = v___x_2019_;
v___y_1970_ = v___y_2010_;
v___y_1971_ = v_val_2017_;
v___y_1972_ = v___y_2011_;
v___y_1973_ = v___y_2014_;
v___y_1974_ = v___y_2013_;
v___y_1975_ = v___x_2021_;
v_a_1976_ = v___x_2022_;
goto v___jp_1968_;
}
else
{
size_t v___x_2027_; size_t v___x_2028_; lean_object* v___x_2029_; 
v___x_2027_ = ((size_t)0ULL);
v___x_2028_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
v___x_2029_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_2023_, v___x_2027_, v___x_2028_, v___x_2025_, v_a_1600_);
if (lean_obj_tag(v___x_2029_) == 0)
{
lean_dec_ref(v___x_2029_);
v___y_1969_ = v___x_2019_;
v___y_1970_ = v___y_2010_;
v___y_1971_ = v_val_2017_;
v___y_1972_ = v___y_2011_;
v___y_1973_ = v___y_2014_;
v___y_1974_ = v___y_2013_;
v___y_1975_ = v___x_2021_;
v_a_1976_ = v___x_2022_;
goto v___jp_1968_;
}
else
{
lean_dec_ref(v___x_2021_);
lean_dec_ref(v___x_2019_);
lean_dec(v_val_2017_);
lean_dec(v___y_2014_);
lean_dec_ref(v___y_2013_);
lean_dec_ref(v___y_2011_);
lean_dec(v___y_2010_);
lean_dec_ref(v_env_1605_);
lean_dec(v_name_1602_);
lean_dec_ref(v_dir_1601_);
return v___x_2029_;
}
}
}
else
{
size_t v___x_2030_; size_t v___x_2031_; lean_object* v___x_2032_; 
v___x_2030_ = ((size_t)0ULL);
v___x_2031_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
v___x_2032_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_2023_, v___x_2030_, v___x_2031_, v___x_2025_, v_a_1600_);
if (lean_obj_tag(v___x_2032_) == 0)
{
lean_dec_ref(v___x_2032_);
v___y_1969_ = v___x_2019_;
v___y_1970_ = v___y_2010_;
v___y_1971_ = v_val_2017_;
v___y_1972_ = v___y_2011_;
v___y_1973_ = v___y_2014_;
v___y_1974_ = v___y_2013_;
v___y_1975_ = v___x_2021_;
v_a_1976_ = v___x_2022_;
goto v___jp_1968_;
}
else
{
lean_dec_ref(v___x_2021_);
lean_dec_ref(v___x_2019_);
lean_dec(v_val_2017_);
lean_dec(v___y_2014_);
lean_dec_ref(v___y_2013_);
lean_dec_ref(v___y_2011_);
lean_dec(v___y_2010_);
lean_dec_ref(v_env_1605_);
lean_dec(v_name_1602_);
lean_dec_ref(v_dir_1601_);
return v___x_2032_;
}
}
}
}
else
{
lean_dec(v___y_2012_);
v___y_1928_ = v___y_2010_;
v___y_1929_ = v___y_2011_;
v___y_1930_ = v___y_2014_;
v___y_1931_ = v___y_2013_;
v___y_1932_ = v_a_1600_;
goto v___jp_1927_;
}
}
else
{
lean_object* v_a_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2045_; 
lean_dec(v___y_2014_);
lean_dec_ref(v___y_2013_);
lean_dec(v___y_2012_);
lean_dec_ref(v___y_2011_);
lean_dec(v___y_2010_);
lean_dec_ref(v_env_1605_);
lean_dec(v_name_1602_);
lean_dec_ref(v_dir_1601_);
v_a_2033_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2045_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2045_ == 0)
{
v___x_2035_ = v___x_2016_;
v_isShared_2036_ = v_isSharedCheck_2045_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_a_2033_);
lean_dec(v___x_2016_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2045_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v___x_2037_; uint8_t v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2043_; 
v___x_2037_ = lean_io_error_to_string(v_a_2033_);
v___x_2038_ = 3;
v___x_2039_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2039_, 0, v___x_2037_);
lean_ctor_set_uint8(v___x_2039_, sizeof(void*)*1, v___x_2038_);
lean_inc_ref(v_a_1600_);
v___x_2040_ = lean_apply_2(v_a_1600_, v___x_2039_, lean_box(0));
v___x_2041_ = lean_box(0);
if (v_isShared_2036_ == 0)
{
lean_ctor_set(v___x_2035_, 0, v___x_2041_);
v___x_2043_ = v___x_2035_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v___x_2041_);
v___x_2043_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
return v___x_2043_;
}
}
}
}
v___jp_2046_:
{
lean_object* v_lean_2049_; lean_object* v_toolchain_2050_; lean_object* v___x_2051_; 
v_lean_2049_ = lean_ctor_get(v_env_1605_, 1);
v_toolchain_2050_ = lean_ctor_get(v_env_1605_, 18);
lean_inc_ref(v_toolchain_2050_);
v___x_2051_ = l_Lake_ToolchainVer_ofString(v_toolchain_2050_);
if (lean_obj_tag(v___x_2051_) == 0)
{
lean_object* v_ver_2052_; lean_object* v___x_2053_; 
v_ver_2052_ = lean_ctor_get(v___x_2051_, 1);
lean_inc_ref(v_ver_2052_);
lean_dec_ref(v___x_2051_);
v___x_2053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2053_, 0, v_ver_2052_);
lean_inc_ref(v_lean_2049_);
lean_inc_ref(v_toolchain_2050_);
v___y_2010_ = v_fst_2047_;
v___y_2011_ = v_toolchain_2050_;
v___y_2012_ = v_snd_2048_;
v___y_2013_ = v_lean_2049_;
v___y_2014_ = v___x_2053_;
goto v___jp_2009_;
}
else
{
lean_object* v___x_2054_; 
lean_dec_ref(v___x_2051_);
v___x_2054_ = lean_box(0);
lean_inc_ref(v_lean_2049_);
lean_inc_ref(v_toolchain_2050_);
v___y_2010_ = v_fst_2047_;
v___y_2011_ = v_toolchain_2050_;
v___y_2012_ = v_snd_2048_;
v___y_2013_ = v_lean_2049_;
v___y_2014_ = v___x_2054_;
goto v___jp_2009_;
}
}
v___jp_2055_:
{
if (v_a_2058_ == 0)
{
lean_object* v___x_2059_; 
v___x_2059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2059_, 0, v___y_2057_);
v_fst_2047_ = v___y_2056_;
v_snd_2048_ = v___x_2059_;
goto v___jp_2046_;
}
else
{
lean_object* v___x_2060_; 
lean_dec_ref(v___y_2057_);
v___x_2060_ = lean_box(0);
v_fst_2047_ = v___y_2056_;
v_snd_2048_ = v___x_2060_;
goto v___jp_2046_;
}
}
v___jp_2061_:
{
if (v___y_2064_ == 0)
{
lean_object* v___x_2065_; lean_object* v___x_2066_; uint8_t v___x_2067_; lean_object* v___x_2068_; uint8_t v___x_2069_; 
lean_dec_ref(v___y_2063_);
lean_inc(v_name_1602_);
v___x_2065_ = l_Lake_toUpperCamelCase(v_name_1602_);
lean_inc(v___x_2065_);
v___x_2066_ = l_Lean_modToFilePath(v_dir_1601_, v___x_2065_, v___y_2062_);
v___x_2067_ = l_System_FilePath_pathExists(v___x_2066_);
v___x_2068_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_2069_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_2069_ == 0)
{
v___y_2056_ = v___x_2065_;
v___y_2057_ = v___x_2066_;
v_a_2058_ = v___x_2067_;
goto v___jp_2055_;
}
else
{
lean_object* v___x_2070_; uint8_t v___x_2071_; 
v___x_2070_ = lean_box(0);
v___x_2071_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (v___x_2071_ == 0)
{
if (v___x_2069_ == 0)
{
v___y_2056_ = v___x_2065_;
v___y_2057_ = v___x_2066_;
v_a_2058_ = v___x_2067_;
goto v___jp_2055_;
}
else
{
size_t v___x_2072_; size_t v___x_2073_; lean_object* v___x_2074_; 
v___x_2072_ = ((size_t)0ULL);
v___x_2073_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
v___x_2074_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_2068_, v___x_2072_, v___x_2073_, v___x_2070_, v_a_1600_);
if (lean_obj_tag(v___x_2074_) == 0)
{
lean_dec_ref(v___x_2074_);
v___y_2056_ = v___x_2065_;
v___y_2057_ = v___x_2066_;
v_a_2058_ = v___x_2067_;
goto v___jp_2055_;
}
else
{
lean_dec_ref(v___x_2066_);
lean_dec(v___x_2065_);
lean_dec_ref(v_configFile_2008_);
lean_dec_ref(v_env_1605_);
lean_dec(v_name_1602_);
lean_dec_ref(v_dir_1601_);
return v___x_2074_;
}
}
}
else
{
size_t v___x_2075_; size_t v___x_2076_; lean_object* v___x_2077_; 
v___x_2075_ = ((size_t)0ULL);
v___x_2076_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
v___x_2077_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_2068_, v___x_2075_, v___x_2076_, v___x_2070_, v_a_1600_);
if (lean_obj_tag(v___x_2077_) == 0)
{
lean_dec_ref(v___x_2077_);
v___y_2056_ = v___x_2065_;
v___y_2057_ = v___x_2066_;
v_a_2058_ = v___x_2067_;
goto v___jp_2055_;
}
else
{
lean_dec_ref(v___x_2066_);
lean_dec(v___x_2065_);
lean_dec_ref(v_configFile_2008_);
lean_dec_ref(v_env_1605_);
lean_dec(v_name_1602_);
lean_dec_ref(v_dir_1601_);
return v___x_2077_;
}
}
}
}
else
{
lean_object* v___x_2078_; 
v___x_2078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2078_, 0, v___y_2063_);
lean_inc(v_name_1602_);
v_fst_2047_ = v_name_1602_;
v_snd_2048_ = v___x_2078_;
goto v___jp_2046_;
}
}
v___jp_2079_:
{
uint8_t v___x_2083_; uint8_t v___x_2084_; 
v___x_2083_ = 1;
v___x_2084_ = l_Lake_instDecidableEqInitTemplate(v_tmp_1603_, v___x_2083_);
if (v___x_2084_ == 0)
{
v___y_2062_ = v___y_2080_;
v___y_2063_ = v___y_2081_;
v___y_2064_ = v_a_2082_;
goto v___jp_2061_;
}
else
{
v___y_2062_ = v___y_2080_;
v___y_2063_ = v___y_2081_;
v___y_2064_ = v___x_2084_;
goto v___jp_2061_;
}
}
v___jp_2085_:
{
lean_object* v___x_2086_; lean_object* v___x_2087_; uint8_t v___x_2088_; lean_object* v___x_2089_; uint8_t v___x_2090_; 
v___x_2086_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__16));
lean_inc(v_name_1602_);
v___x_2087_ = l_Lean_modToFilePath(v_dir_1601_, v_name_1602_, v___x_2086_);
v___x_2088_ = l_System_FilePath_pathExists(v___x_2087_);
v___x_2089_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_2090_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_2090_ == 0)
{
v___y_2080_ = v___x_2086_;
v___y_2081_ = v___x_2087_;
v_a_2082_ = v___x_2088_;
goto v___jp_2079_;
}
else
{
lean_object* v___x_2091_; uint8_t v___x_2092_; 
v___x_2091_ = lean_box(0);
v___x_2092_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (v___x_2092_ == 0)
{
if (v___x_2090_ == 0)
{
v___y_2080_ = v___x_2086_;
v___y_2081_ = v___x_2087_;
v_a_2082_ = v___x_2088_;
goto v___jp_2079_;
}
else
{
size_t v___x_2093_; size_t v___x_2094_; lean_object* v___x_2095_; 
v___x_2093_ = ((size_t)0ULL);
v___x_2094_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
v___x_2095_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_2089_, v___x_2093_, v___x_2094_, v___x_2091_, v_a_1600_);
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_dec_ref(v___x_2095_);
v___y_2080_ = v___x_2086_;
v___y_2081_ = v___x_2087_;
v_a_2082_ = v___x_2088_;
goto v___jp_2079_;
}
else
{
lean_dec_ref(v___x_2087_);
lean_dec_ref(v_configFile_2008_);
lean_dec_ref(v_env_1605_);
lean_dec(v_name_1602_);
lean_dec_ref(v_dir_1601_);
return v___x_2095_;
}
}
}
else
{
size_t v___x_2096_; size_t v___x_2097_; lean_object* v___x_2098_; 
v___x_2096_ = ((size_t)0ULL);
v___x_2097_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
v___x_2098_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_2089_, v___x_2096_, v___x_2097_, v___x_2091_, v_a_1600_);
if (lean_obj_tag(v___x_2098_) == 0)
{
lean_dec_ref(v___x_2098_);
v___y_2080_ = v___x_2086_;
v___y_2081_ = v___x_2087_;
v_a_2082_ = v___x_2088_;
goto v___jp_2079_;
}
else
{
lean_dec_ref(v___x_2087_);
lean_dec_ref(v_configFile_2008_);
lean_dec_ref(v_env_1605_);
lean_dec(v_name_1602_);
lean_dec_ref(v_dir_1601_);
return v___x_2098_;
}
}
}
}
v___jp_2099_:
{
if (lean_obj_tag(v___y_2100_) == 0)
{
lean_dec_ref(v___y_2100_);
goto v___jp_2085_;
}
else
{
lean_dec_ref(v_configFile_2008_);
lean_dec_ref(v_env_1605_);
lean_dec(v_name_1602_);
lean_dec_ref(v_dir_1601_);
return v___y_2100_;
}
}
v___jp_2102_:
{
if (v___x_2101_ == 0)
{
lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; 
v___x_2103_ = lean_unsigned_to_nat(0u);
v___x_2104_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(v_dir_1601_);
v___x_2105_ = l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow(v_dir_1601_, v_tmp_1603_, v___x_2104_);
if (lean_obj_tag(v___x_2105_) == 0)
{
lean_object* v_a_2106_; lean_object* v___x_2107_; uint8_t v___x_2108_; 
v_a_2106_ = lean_ctor_get(v___x_2105_, 1);
lean_inc(v_a_2106_);
lean_dec_ref(v___x_2105_);
v___x_2107_ = lean_array_get_size(v_a_2106_);
v___x_2108_ = lean_nat_dec_lt(v___x_2103_, v___x_2107_);
if (v___x_2108_ == 0)
{
lean_dec(v_a_2106_);
goto v___jp_2085_;
}
else
{
lean_object* v___x_2109_; uint8_t v___x_2110_; 
v___x_2109_ = lean_box(0);
v___x_2110_ = lean_nat_dec_le(v___x_2107_, v___x_2107_);
if (v___x_2110_ == 0)
{
if (v___x_2108_ == 0)
{
lean_dec(v_a_2106_);
goto v___jp_2085_;
}
else
{
size_t v___x_2111_; size_t v___x_2112_; lean_object* v___x_2113_; 
v___x_2111_ = ((size_t)0ULL);
v___x_2112_ = lean_usize_of_nat(v___x_2107_);
v___x_2113_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_2106_, v___x_2111_, v___x_2112_, v___x_2109_, v_a_1600_);
lean_dec(v_a_2106_);
if (lean_obj_tag(v___x_2113_) == 0)
{
lean_dec_ref(v___x_2113_);
goto v___jp_2085_;
}
else
{
v___y_2100_ = v___x_2113_;
goto v___jp_2099_;
}
}
}
else
{
size_t v___x_2114_; size_t v___x_2115_; lean_object* v___x_2116_; 
v___x_2114_ = ((size_t)0ULL);
v___x_2115_ = lean_usize_of_nat(v___x_2107_);
v___x_2116_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_2106_, v___x_2114_, v___x_2115_, v___x_2109_, v_a_1600_);
lean_dec(v_a_2106_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_dec_ref(v___x_2116_);
goto v___jp_2085_;
}
else
{
v___y_2100_ = v___x_2116_;
goto v___jp_2099_;
}
}
}
}
else
{
lean_object* v_a_2117_; lean_object* v___x_2118_; uint8_t v___x_2119_; 
v_a_2117_ = lean_ctor_get(v___x_2105_, 1);
lean_inc(v_a_2117_);
lean_dec_ref(v___x_2105_);
v___x_2118_ = lean_array_get_size(v_a_2117_);
v___x_2119_ = lean_nat_dec_lt(v___x_2103_, v___x_2118_);
if (v___x_2119_ == 0)
{
lean_object* v___x_2120_; lean_object* v___x_2121_; 
lean_dec(v_a_2117_);
lean_dec_ref(v_configFile_2008_);
lean_dec_ref(v_env_1605_);
lean_dec(v_name_1602_);
lean_dec_ref(v_dir_1601_);
v___x_2120_ = lean_box(0);
v___x_2121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2121_, 0, v___x_2120_);
return v___x_2121_;
}
else
{
lean_object* v___x_2122_; uint8_t v___x_2123_; 
v___x_2122_ = lean_box(0);
v___x_2123_ = lean_nat_dec_le(v___x_2118_, v___x_2118_);
if (v___x_2123_ == 0)
{
if (v___x_2119_ == 0)
{
lean_dec(v_a_2117_);
lean_dec_ref(v_configFile_2008_);
lean_dec_ref(v_env_1605_);
lean_dec(v_name_1602_);
lean_dec_ref(v_dir_1601_);
goto v___jp_1608_;
}
else
{
size_t v___x_2124_; size_t v___x_2125_; lean_object* v___x_2126_; 
v___x_2124_ = ((size_t)0ULL);
v___x_2125_ = lean_usize_of_nat(v___x_2118_);
v___x_2126_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_2117_, v___x_2124_, v___x_2125_, v___x_2122_, v_a_1600_);
lean_dec(v_a_2117_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_dec_ref(v___x_2126_);
lean_dec_ref(v_configFile_2008_);
lean_dec_ref(v_env_1605_);
lean_dec(v_name_1602_);
lean_dec_ref(v_dir_1601_);
goto v___jp_1608_;
}
else
{
v___y_2100_ = v___x_2126_;
goto v___jp_2099_;
}
}
}
else
{
size_t v___x_2127_; size_t v___x_2128_; lean_object* v___x_2129_; 
v___x_2127_ = ((size_t)0ULL);
v___x_2128_ = lean_usize_of_nat(v___x_2118_);
v___x_2129_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_2117_, v___x_2127_, v___x_2128_, v___x_2122_, v_a_1600_);
lean_dec(v_a_2117_);
if (lean_obj_tag(v___x_2129_) == 0)
{
lean_dec_ref(v___x_2129_);
lean_dec_ref(v_configFile_2008_);
lean_dec_ref(v_env_1605_);
lean_dec(v_name_1602_);
lean_dec_ref(v_dir_1601_);
goto v___jp_1608_;
}
else
{
v___y_2100_ = v___x_2129_;
goto v___jp_2099_;
}
}
}
}
}
else
{
lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
lean_dec_ref(v_configFile_2008_);
lean_dec_ref(v_env_1605_);
lean_dec(v_name_1602_);
lean_dec_ref(v_dir_1601_);
v___x_2130_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__18));
lean_inc_ref(v_a_1600_);
v___x_2131_ = lean_apply_2(v_a_1600_, v___x_2130_, lean_box(0));
v___x_2132_ = lean_box(0);
v___x_2133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2133_, 0, v___x_2132_);
return v___x_2133_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__0___boxed(lean_object* v_a_2144_, lean_object* v_dir_2145_, lean_object* v_name_2146_, lean_object* v_tmp_2147_, lean_object* v_lang_2148_, lean_object* v_env_2149_, lean_object* v_offline_2150_, lean_object* v_a_2151_){
_start:
{
uint8_t v_tmp_boxed_2152_; uint8_t v_lang_boxed_2153_; uint8_t v_offline_boxed_2154_; lean_object* v_res_2155_; 
v_tmp_boxed_2152_ = lean_unbox(v_tmp_2147_);
v_lang_boxed_2153_ = lean_unbox(v_lang_2148_);
v_offline_boxed_2154_ = lean_unbox(v_offline_2150_);
v_res_2155_ = l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__0(v_a_2144_, v_dir_2145_, v_name_2146_, v_tmp_boxed_2152_, v_lang_boxed_2153_, v_env_2149_, v_offline_boxed_2154_);
lean_dec_ref(v_a_2144_);
return v_res_2155_;
}
}
LEAN_EXPORT lean_object* l_Lake_init(lean_object* v_name_2157_, uint8_t v_tmp_2158_, uint8_t v_lang_2159_, lean_object* v_env_2160_, lean_object* v_cwd_2161_, uint8_t v_offline_2162_, lean_object* v_a_2163_){
_start:
{
lean_object* v___y_2169_; lean_object* v___y_2187_; lean_object* v___y_2188_; lean_object* v_a_2190_; lean_object* v___x_2225_; uint8_t v___x_2226_; 
v___x_2225_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__4));
v___x_2226_ = lean_string_dec_eq(v_name_2157_, v___x_2225_);
if (v___x_2226_ == 0)
{
v_a_2190_ = v_name_2157_;
goto v___jp_2189_;
}
else
{
lean_object* v___x_2227_; 
lean_dec_ref(v_name_2157_);
lean_inc_ref(v_cwd_2161_);
v___x_2227_ = lean_io_realpath(v_cwd_2161_);
if (lean_obj_tag(v___x_2227_) == 0)
{
lean_object* v_a_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2245_; 
v_a_2228_ = lean_ctor_get(v___x_2227_, 0);
v_isSharedCheck_2245_ = !lean_is_exclusive(v___x_2227_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2230_ = v___x_2227_;
v_isShared_2231_ = v_isSharedCheck_2245_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_a_2228_);
lean_dec(v___x_2227_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2245_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
lean_object* v___x_2232_; 
lean_inc(v_a_2228_);
v___x_2232_ = l_System_FilePath_fileName(v_a_2228_);
if (lean_obj_tag(v___x_2232_) == 0)
{
lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; uint8_t v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2242_; 
lean_dec_ref(v_cwd_2161_);
lean_dec_ref(v_env_2160_);
v___x_2233_ = ((lean_object*)(l_Lake_init___closed__0));
v___x_2234_ = lean_string_append(v___x_2233_, v_a_2228_);
lean_dec(v_a_2228_);
v___x_2235_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__6));
v___x_2236_ = lean_string_append(v___x_2234_, v___x_2235_);
v___x_2237_ = 3;
v___x_2238_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2238_, 0, v___x_2236_);
lean_ctor_set_uint8(v___x_2238_, sizeof(void*)*1, v___x_2237_);
lean_inc_ref(v_a_2163_);
v___x_2239_ = lean_apply_2(v_a_2163_, v___x_2238_, lean_box(0));
v___x_2240_ = lean_box(0);
if (v_isShared_2231_ == 0)
{
lean_ctor_set_tag(v___x_2230_, 1);
lean_ctor_set(v___x_2230_, 0, v___x_2240_);
v___x_2242_ = v___x_2230_;
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
else
{
lean_object* v_val_2244_; 
lean_del_object(v___x_2230_);
lean_dec(v_a_2228_);
v_val_2244_ = lean_ctor_get(v___x_2232_, 0);
lean_inc(v_val_2244_);
lean_dec_ref(v___x_2232_);
v_a_2190_ = v_val_2244_;
goto v___jp_2189_;
}
}
}
else
{
lean_object* v_a_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2258_; 
lean_dec_ref(v_cwd_2161_);
lean_dec_ref(v_env_2160_);
v_a_2246_ = lean_ctor_get(v___x_2227_, 0);
v_isSharedCheck_2258_ = !lean_is_exclusive(v___x_2227_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2248_ = v___x_2227_;
v_isShared_2249_ = v_isSharedCheck_2258_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_a_2246_);
lean_dec(v___x_2227_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2258_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v___x_2250_; uint8_t v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2256_; 
v___x_2250_ = lean_io_error_to_string(v_a_2246_);
v___x_2251_ = 3;
v___x_2252_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2252_, 0, v___x_2250_);
lean_ctor_set_uint8(v___x_2252_, sizeof(void*)*1, v___x_2251_);
lean_inc_ref(v_a_2163_);
v___x_2253_ = lean_apply_2(v_a_2163_, v___x_2252_, lean_box(0));
v___x_2254_ = lean_box(0);
if (v_isShared_2249_ == 0)
{
lean_ctor_set(v___x_2248_, 0, v___x_2254_);
v___x_2256_ = v___x_2248_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v___x_2254_);
v___x_2256_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
return v___x_2256_;
}
}
}
}
v___jp_2165_:
{
lean_object* v___x_2166_; lean_object* v___x_2167_; 
v___x_2166_ = lean_box(0);
v___x_2167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2167_, 0, v___x_2166_);
return v___x_2167_;
}
v___jp_2168_:
{
lean_object* v___x_2170_; 
lean_inc_ref(v_cwd_2161_);
v___x_2170_ = l_IO_FS_createDirAll(v_cwd_2161_);
if (lean_obj_tag(v___x_2170_) == 0)
{
lean_object* v___x_2171_; lean_object* v___x_2172_; 
lean_dec_ref(v___x_2170_);
v___x_2171_ = l_Lake_stringToLegalOrSimpleName(v___y_2169_);
v___x_2172_ = l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__0(v_a_2163_, v_cwd_2161_, v___x_2171_, v_tmp_2158_, v_lang_2159_, v_env_2160_, v_offline_2162_);
return v___x_2172_;
}
else
{
lean_object* v_a_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2185_; 
lean_dec_ref(v___y_2169_);
lean_dec_ref(v_cwd_2161_);
lean_dec_ref(v_env_2160_);
v_a_2173_ = lean_ctor_get(v___x_2170_, 0);
v_isSharedCheck_2185_ = !lean_is_exclusive(v___x_2170_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2175_ = v___x_2170_;
v_isShared_2176_ = v_isSharedCheck_2185_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_a_2173_);
lean_dec(v___x_2170_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2185_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v___x_2177_; uint8_t v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2183_; 
v___x_2177_ = lean_io_error_to_string(v_a_2173_);
v___x_2178_ = 3;
v___x_2179_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2179_, 0, v___x_2177_);
lean_ctor_set_uint8(v___x_2179_, sizeof(void*)*1, v___x_2178_);
lean_inc_ref(v_a_2163_);
v___x_2180_ = lean_apply_2(v_a_2163_, v___x_2179_, lean_box(0));
v___x_2181_ = lean_box(0);
if (v_isShared_2176_ == 0)
{
lean_ctor_set(v___x_2175_, 0, v___x_2181_);
v___x_2183_ = v___x_2175_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v___x_2181_);
v___x_2183_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
return v___x_2183_;
}
}
}
}
v___jp_2186_:
{
if (lean_obj_tag(v___y_2188_) == 0)
{
lean_dec_ref(v___y_2188_);
v___y_2169_ = v___y_2187_;
goto v___jp_2168_;
}
else
{
lean_dec_ref(v___y_2187_);
lean_dec_ref(v_cwd_2161_);
lean_dec_ref(v_env_2160_);
return v___y_2188_;
}
}
v___jp_2189_:
{
lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v_str_2195_; lean_object* v_startInclusive_2196_; lean_object* v_endExclusive_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; 
v___x_2191_ = lean_unsigned_to_nat(0u);
v___x_2192_ = lean_string_utf8_byte_size(v_a_2190_);
v___x_2193_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2193_, 0, v_a_2190_);
lean_ctor_set(v___x_2193_, 1, v___x_2191_);
lean_ctor_set(v___x_2193_, 2, v___x_2192_);
v___x_2194_ = l_String_Slice_trimAscii(v___x_2193_);
v_str_2195_ = lean_ctor_get(v___x_2194_, 0);
lean_inc_ref(v_str_2195_);
v_startInclusive_2196_ = lean_ctor_get(v___x_2194_, 1);
lean_inc(v_startInclusive_2196_);
v_endExclusive_2197_ = lean_ctor_get(v___x_2194_, 2);
lean_inc(v_endExclusive_2197_);
lean_dec_ref(v___x_2194_);
v___x_2198_ = lean_string_utf8_extract(v_str_2195_, v_startInclusive_2196_, v_endExclusive_2197_);
lean_dec(v_endExclusive_2197_);
lean_dec(v_startInclusive_2196_);
lean_dec_ref(v_str_2195_);
v___x_2199_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(v___x_2198_);
v___x_2200_ = l___private_Lake_CLI_Init_0__Lake_validatePkgName(v___x_2198_, v___x_2199_);
if (lean_obj_tag(v___x_2200_) == 0)
{
lean_object* v_a_2201_; lean_object* v___x_2202_; uint8_t v___x_2203_; 
v_a_2201_ = lean_ctor_get(v___x_2200_, 1);
lean_inc(v_a_2201_);
lean_dec_ref(v___x_2200_);
v___x_2202_ = lean_array_get_size(v_a_2201_);
v___x_2203_ = lean_nat_dec_lt(v___x_2191_, v___x_2202_);
if (v___x_2203_ == 0)
{
lean_dec(v_a_2201_);
v___y_2169_ = v___x_2198_;
goto v___jp_2168_;
}
else
{
lean_object* v___x_2204_; uint8_t v___x_2205_; 
v___x_2204_ = lean_box(0);
v___x_2205_ = lean_nat_dec_le(v___x_2202_, v___x_2202_);
if (v___x_2205_ == 0)
{
if (v___x_2203_ == 0)
{
lean_dec(v_a_2201_);
v___y_2169_ = v___x_2198_;
goto v___jp_2168_;
}
else
{
size_t v___x_2206_; size_t v___x_2207_; lean_object* v___x_2208_; 
v___x_2206_ = ((size_t)0ULL);
v___x_2207_ = lean_usize_of_nat(v___x_2202_);
v___x_2208_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_2201_, v___x_2206_, v___x_2207_, v___x_2204_, v_a_2163_);
lean_dec(v_a_2201_);
if (lean_obj_tag(v___x_2208_) == 0)
{
lean_dec_ref(v___x_2208_);
v___y_2169_ = v___x_2198_;
goto v___jp_2168_;
}
else
{
v___y_2187_ = v___x_2198_;
v___y_2188_ = v___x_2208_;
goto v___jp_2186_;
}
}
}
else
{
size_t v___x_2209_; size_t v___x_2210_; lean_object* v___x_2211_; 
v___x_2209_ = ((size_t)0ULL);
v___x_2210_ = lean_usize_of_nat(v___x_2202_);
v___x_2211_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_2201_, v___x_2209_, v___x_2210_, v___x_2204_, v_a_2163_);
lean_dec(v_a_2201_);
if (lean_obj_tag(v___x_2211_) == 0)
{
lean_dec_ref(v___x_2211_);
v___y_2169_ = v___x_2198_;
goto v___jp_2168_;
}
else
{
v___y_2187_ = v___x_2198_;
v___y_2188_ = v___x_2211_;
goto v___jp_2186_;
}
}
}
}
else
{
lean_object* v_a_2212_; lean_object* v___x_2213_; uint8_t v___x_2214_; 
v_a_2212_ = lean_ctor_get(v___x_2200_, 1);
lean_inc(v_a_2212_);
lean_dec_ref(v___x_2200_);
v___x_2213_ = lean_array_get_size(v_a_2212_);
v___x_2214_ = lean_nat_dec_lt(v___x_2191_, v___x_2213_);
if (v___x_2214_ == 0)
{
lean_object* v___x_2215_; lean_object* v___x_2216_; 
lean_dec(v_a_2212_);
lean_dec_ref(v___x_2198_);
lean_dec_ref(v_cwd_2161_);
lean_dec_ref(v_env_2160_);
v___x_2215_ = lean_box(0);
v___x_2216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2216_, 0, v___x_2215_);
return v___x_2216_;
}
else
{
lean_object* v___x_2217_; uint8_t v___x_2218_; 
v___x_2217_ = lean_box(0);
v___x_2218_ = lean_nat_dec_le(v___x_2213_, v___x_2213_);
if (v___x_2218_ == 0)
{
if (v___x_2214_ == 0)
{
lean_dec(v_a_2212_);
lean_dec_ref(v___x_2198_);
lean_dec_ref(v_cwd_2161_);
lean_dec_ref(v_env_2160_);
goto v___jp_2165_;
}
else
{
size_t v___x_2219_; size_t v___x_2220_; lean_object* v___x_2221_; 
v___x_2219_ = ((size_t)0ULL);
v___x_2220_ = lean_usize_of_nat(v___x_2213_);
v___x_2221_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_2212_, v___x_2219_, v___x_2220_, v___x_2217_, v_a_2163_);
lean_dec(v_a_2212_);
if (lean_obj_tag(v___x_2221_) == 0)
{
lean_dec_ref(v___x_2221_);
lean_dec_ref(v___x_2198_);
lean_dec_ref(v_cwd_2161_);
lean_dec_ref(v_env_2160_);
goto v___jp_2165_;
}
else
{
v___y_2187_ = v___x_2198_;
v___y_2188_ = v___x_2221_;
goto v___jp_2186_;
}
}
}
else
{
size_t v___x_2222_; size_t v___x_2223_; lean_object* v___x_2224_; 
v___x_2222_ = ((size_t)0ULL);
v___x_2223_ = lean_usize_of_nat(v___x_2213_);
v___x_2224_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_2212_, v___x_2222_, v___x_2223_, v___x_2217_, v_a_2163_);
lean_dec(v_a_2212_);
if (lean_obj_tag(v___x_2224_) == 0)
{
lean_dec_ref(v___x_2224_);
lean_dec_ref(v___x_2198_);
lean_dec_ref(v_cwd_2161_);
lean_dec_ref(v_env_2160_);
goto v___jp_2165_;
}
else
{
v___y_2187_ = v___x_2198_;
v___y_2188_ = v___x_2224_;
goto v___jp_2186_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_init___boxed(lean_object* v_name_2259_, lean_object* v_tmp_2260_, lean_object* v_lang_2261_, lean_object* v_env_2262_, lean_object* v_cwd_2263_, lean_object* v_offline_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_){
_start:
{
uint8_t v_tmp_boxed_2267_; uint8_t v_lang_boxed_2268_; uint8_t v_offline_boxed_2269_; lean_object* v_res_2270_; 
v_tmp_boxed_2267_ = lean_unbox(v_tmp_2260_);
v_lang_boxed_2268_ = lean_unbox(v_lang_2261_);
v_offline_boxed_2269_ = lean_unbox(v_offline_2264_);
v_res_2270_ = l_Lake_init(v_name_2259_, v_tmp_boxed_2267_, v_lang_boxed_2268_, v_env_2262_, v_cwd_2263_, v_offline_boxed_2269_, v_a_2265_);
lean_dec_ref(v_a_2265_);
return v_res_2270_;
}
}
LEAN_EXPORT lean_object* l_Lake_new(lean_object* v_name_2271_, uint8_t v_tmp_2272_, uint8_t v_lang_2273_, lean_object* v_env_2274_, lean_object* v_cwd_2275_, uint8_t v_offline_2276_, lean_object* v_a_2277_){
_start:
{
lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v_str_2286_; lean_object* v_startInclusive_2287_; lean_object* v_endExclusive_2288_; lean_object* v_name_2289_; lean_object* v___y_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; 
v___x_2282_ = lean_unsigned_to_nat(0u);
v___x_2283_ = lean_string_utf8_byte_size(v_name_2271_);
v___x_2284_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2284_, 0, v_name_2271_);
lean_ctor_set(v___x_2284_, 1, v___x_2282_);
lean_ctor_set(v___x_2284_, 2, v___x_2283_);
v___x_2285_ = l_String_Slice_trimAscii(v___x_2284_);
v_str_2286_ = lean_ctor_get(v___x_2285_, 0);
lean_inc_ref(v_str_2286_);
v_startInclusive_2287_ = lean_ctor_get(v___x_2285_, 1);
lean_inc(v_startInclusive_2287_);
v_endExclusive_2288_ = lean_ctor_get(v___x_2285_, 2);
lean_inc(v_endExclusive_2288_);
lean_dec_ref(v___x_2285_);
v_name_2289_ = lean_string_utf8_extract(v_str_2286_, v_startInclusive_2287_, v_endExclusive_2288_);
lean_dec(v_endExclusive_2288_);
lean_dec(v_startInclusive_2287_);
lean_dec_ref(v_str_2286_);
v___x_2311_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(v_name_2289_);
v___x_2312_ = l___private_Lake_CLI_Init_0__Lake_validatePkgName(v_name_2289_, v___x_2311_);
if (lean_obj_tag(v___x_2312_) == 0)
{
lean_object* v_a_2313_; lean_object* v___x_2314_; uint8_t v___x_2315_; 
v_a_2313_ = lean_ctor_get(v___x_2312_, 1);
lean_inc(v_a_2313_);
lean_dec_ref(v___x_2312_);
v___x_2314_ = lean_array_get_size(v_a_2313_);
v___x_2315_ = lean_nat_dec_lt(v___x_2282_, v___x_2314_);
if (v___x_2315_ == 0)
{
lean_dec(v_a_2313_);
goto v___jp_2290_;
}
else
{
lean_object* v___x_2316_; uint8_t v___x_2317_; 
v___x_2316_ = lean_box(0);
v___x_2317_ = lean_nat_dec_le(v___x_2314_, v___x_2314_);
if (v___x_2317_ == 0)
{
if (v___x_2315_ == 0)
{
lean_dec(v_a_2313_);
goto v___jp_2290_;
}
else
{
size_t v___x_2318_; size_t v___x_2319_; lean_object* v___x_2320_; 
v___x_2318_ = ((size_t)0ULL);
v___x_2319_ = lean_usize_of_nat(v___x_2314_);
v___x_2320_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_2313_, v___x_2318_, v___x_2319_, v___x_2316_, v_a_2277_);
lean_dec(v_a_2313_);
if (lean_obj_tag(v___x_2320_) == 0)
{
lean_dec_ref(v___x_2320_);
goto v___jp_2290_;
}
else
{
v___y_2310_ = v___x_2320_;
goto v___jp_2309_;
}
}
}
else
{
size_t v___x_2321_; size_t v___x_2322_; lean_object* v___x_2323_; 
v___x_2321_ = ((size_t)0ULL);
v___x_2322_ = lean_usize_of_nat(v___x_2314_);
v___x_2323_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_2313_, v___x_2321_, v___x_2322_, v___x_2316_, v_a_2277_);
lean_dec(v_a_2313_);
if (lean_obj_tag(v___x_2323_) == 0)
{
lean_dec_ref(v___x_2323_);
goto v___jp_2290_;
}
else
{
v___y_2310_ = v___x_2323_;
goto v___jp_2309_;
}
}
}
}
else
{
lean_object* v_a_2324_; lean_object* v___x_2325_; uint8_t v___x_2326_; 
v_a_2324_ = lean_ctor_get(v___x_2312_, 1);
lean_inc(v_a_2324_);
lean_dec_ref(v___x_2312_);
v___x_2325_ = lean_array_get_size(v_a_2324_);
v___x_2326_ = lean_nat_dec_lt(v___x_2282_, v___x_2325_);
if (v___x_2326_ == 0)
{
lean_object* v___x_2327_; lean_object* v___x_2328_; 
lean_dec(v_a_2324_);
lean_dec_ref(v_name_2289_);
lean_dec_ref(v_cwd_2275_);
lean_dec_ref(v_env_2274_);
v___x_2327_ = lean_box(0);
v___x_2328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2328_, 0, v___x_2327_);
return v___x_2328_;
}
else
{
lean_object* v___x_2329_; uint8_t v___x_2330_; 
v___x_2329_ = lean_box(0);
v___x_2330_ = lean_nat_dec_le(v___x_2325_, v___x_2325_);
if (v___x_2330_ == 0)
{
if (v___x_2326_ == 0)
{
lean_dec(v_a_2324_);
lean_dec_ref(v_name_2289_);
lean_dec_ref(v_cwd_2275_);
lean_dec_ref(v_env_2274_);
goto v___jp_2279_;
}
else
{
size_t v___x_2331_; size_t v___x_2332_; lean_object* v___x_2333_; 
v___x_2331_ = ((size_t)0ULL);
v___x_2332_ = lean_usize_of_nat(v___x_2325_);
v___x_2333_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_2324_, v___x_2331_, v___x_2332_, v___x_2329_, v_a_2277_);
lean_dec(v_a_2324_);
if (lean_obj_tag(v___x_2333_) == 0)
{
lean_dec_ref(v___x_2333_);
lean_dec_ref(v_name_2289_);
lean_dec_ref(v_cwd_2275_);
lean_dec_ref(v_env_2274_);
goto v___jp_2279_;
}
else
{
v___y_2310_ = v___x_2333_;
goto v___jp_2309_;
}
}
}
else
{
size_t v___x_2334_; size_t v___x_2335_; lean_object* v___x_2336_; 
v___x_2334_ = ((size_t)0ULL);
v___x_2335_ = lean_usize_of_nat(v___x_2325_);
v___x_2336_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_2324_, v___x_2334_, v___x_2335_, v___x_2329_, v_a_2277_);
lean_dec(v_a_2324_);
if (lean_obj_tag(v___x_2336_) == 0)
{
lean_dec_ref(v___x_2336_);
lean_dec_ref(v_name_2289_);
lean_dec_ref(v_cwd_2275_);
lean_dec_ref(v_env_2274_);
goto v___jp_2279_;
}
else
{
v___y_2310_ = v___x_2336_;
goto v___jp_2309_;
}
}
}
}
v___jp_2279_:
{
lean_object* v___x_2280_; lean_object* v___x_2281_; 
v___x_2280_ = lean_box(0);
v___x_2281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2281_, 0, v___x_2280_);
return v___x_2281_;
}
v___jp_2290_:
{
lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; 
v___x_2291_ = l_Lake_stringToLegalOrSimpleName(v_name_2289_);
lean_inc(v___x_2291_);
v___x_2292_ = l___private_Lake_CLI_Init_0__Lake_dotlessName(v___x_2291_);
v___x_2293_ = l_Lake_joinRelative(v_cwd_2275_, v___x_2292_);
lean_inc_ref(v___x_2293_);
v___x_2294_ = l_IO_FS_createDirAll(v___x_2293_);
if (lean_obj_tag(v___x_2294_) == 0)
{
lean_object* v___x_2295_; 
lean_dec_ref(v___x_2294_);
v___x_2295_ = l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__0(v_a_2277_, v___x_2293_, v___x_2291_, v_tmp_2272_, v_lang_2273_, v_env_2274_, v_offline_2276_);
return v___x_2295_;
}
else
{
lean_object* v_a_2296_; lean_object* v___x_2298_; uint8_t v_isShared_2299_; uint8_t v_isSharedCheck_2308_; 
lean_dec_ref(v___x_2293_);
lean_dec(v___x_2291_);
lean_dec_ref(v_env_2274_);
v_a_2296_ = lean_ctor_get(v___x_2294_, 0);
v_isSharedCheck_2308_ = !lean_is_exclusive(v___x_2294_);
if (v_isSharedCheck_2308_ == 0)
{
v___x_2298_ = v___x_2294_;
v_isShared_2299_ = v_isSharedCheck_2308_;
goto v_resetjp_2297_;
}
else
{
lean_inc(v_a_2296_);
lean_dec(v___x_2294_);
v___x_2298_ = lean_box(0);
v_isShared_2299_ = v_isSharedCheck_2308_;
goto v_resetjp_2297_;
}
v_resetjp_2297_:
{
lean_object* v___x_2300_; uint8_t v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2306_; 
v___x_2300_ = lean_io_error_to_string(v_a_2296_);
v___x_2301_ = 3;
v___x_2302_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2302_, 0, v___x_2300_);
lean_ctor_set_uint8(v___x_2302_, sizeof(void*)*1, v___x_2301_);
lean_inc_ref(v_a_2277_);
v___x_2303_ = lean_apply_2(v_a_2277_, v___x_2302_, lean_box(0));
v___x_2304_ = lean_box(0);
if (v_isShared_2299_ == 0)
{
lean_ctor_set(v___x_2298_, 0, v___x_2304_);
v___x_2306_ = v___x_2298_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v___x_2304_);
v___x_2306_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
return v___x_2306_;
}
}
}
}
v___jp_2309_:
{
if (lean_obj_tag(v___y_2310_) == 0)
{
lean_dec_ref(v___y_2310_);
goto v___jp_2290_;
}
else
{
lean_dec_ref(v_name_2289_);
lean_dec_ref(v_cwd_2275_);
lean_dec_ref(v_env_2274_);
return v___y_2310_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_new___boxed(lean_object* v_name_2337_, lean_object* v_tmp_2338_, lean_object* v_lang_2339_, lean_object* v_env_2340_, lean_object* v_cwd_2341_, lean_object* v_offline_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_){
_start:
{
uint8_t v_tmp_boxed_2345_; uint8_t v_lang_boxed_2346_; uint8_t v_offline_boxed_2347_; lean_object* v_res_2348_; 
v_tmp_boxed_2345_ = lean_unbox(v_tmp_2338_);
v_lang_boxed_2346_ = lean_unbox(v_lang_2339_);
v_offline_boxed_2347_ = lean_unbox(v_offline_2342_);
v_res_2348_ = l_Lake_new(v_name_2337_, v_tmp_boxed_2345_, v_lang_boxed_2346_, v_env_2340_, v_cwd_2341_, v_offline_boxed_2347_, v_a_2343_);
lean_dec_ref(v_a_2343_);
return v_res_2348_;
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

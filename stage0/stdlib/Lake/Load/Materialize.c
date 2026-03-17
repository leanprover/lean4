// Lean compiler output
// Module: Lake.Load.Materialize
// Imports: public import Lake.Config.Env public import Lake.Load.Manifest public import Lake.Config.Package import Lake.Util.Git import Lake.Reservoir
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
extern uint8_t l_System_Platform_isWindows;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_IO_FS_removeDirAll(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lake_GitRepo_checkoutDetach(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lake_Git_defaultRemote;
lean_object* l_Lake_GitRepo_resolveRemoteRevision(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_clone(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lake_GitRepo_hasNoDiff(lean_object*);
lean_object* l_Lake_GitRepo_findRemoteRevision(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_getHeadRevision(lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_getRemoteUrl_x3f(lean_object*, lean_object*);
lean_object* lean_io_realpath(lean_object*);
extern lean_object* l_Lake_defaultConfigFile;
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
uint8_t l_System_FilePath_isDir(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
extern lean_object* l_Lake_instInhabitedPackageEntry_default;
extern lean_object* l_System_instInhabitedFilePath_default;
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t l_Lake_VerRange_test(lean_object*, lean_object*);
lean_object* l_Lake_StdVer_toString(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lake_Git_filterUrl_x3f(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_quote(lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_RegistryPkg_gitSrc_x3f(lean_object*);
lean_object* l_Lake_Reservoir_fetchPkgVersions(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lake_Reservoir_fetchPkg_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM(lean_object*, lean_object*);
lean_object* l___private_Lake_Util_Version_0__Lake_runVerParse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_instDecidableEqString___boxed(lean_object*, lean_object*);
uint8_t l_Option_instDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_resolveRevision_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = ": repository '"};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0_value;
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "' has local changes"};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1_value;
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = ": checking out revision '"};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2_value;
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3_value;
static const lean_array_object l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = ": cloning "};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___closed__0 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = ": URL has changed; deleting '"};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__0 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__0_value;
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "' and cloning again"};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__1 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__1_value;
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = ": URL has changed; you might need to delete '"};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__2 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__2_value;
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "' manually"};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__3 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__3_value;
static lean_once_cell_t l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4;
static lean_once_cell_t l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5;
static lean_once_cell_t l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6;
static lean_once_cell_t l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_instInhabitedMaterializedDep_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_instInhabitedMaterializedDep_default___closed__0 = (const lean_object*)&l_Lake_instInhabitedMaterializedDep_default___closed__0_value;
static lean_once_cell_t l_Lake_instInhabitedMaterializedDep_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedMaterializedDep_default___closed__1;
LEAN_EXPORT lean_object* l_Lake_instInhabitedMaterializedDep_default;
LEAN_EXPORT lean_object* l_Lake_instInhabitedMaterializedDep;
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_name(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_name___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_scope(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_scope___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_manifestFile_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_manifestFile_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_configFile(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_configFile___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_none_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_none_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_git_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_git_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ver_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ver_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "/"};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0_value;
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 158, .m_capacity = 158, .m_length = 157, .m_data = ": package not found on Reservoir.\n\n  If the package is on GitHub, you can add a Git source. For example:\n\n    require ...\n      from git \"https://github.com/"};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__1 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__1_value;
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\""};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__2 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__2_value;
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 70, .m_data = "\n\n  or, if using TOML:\n\n    [[require]]\n    git = \"https://github.com/"};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__3 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__3_value;
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "\n    ...\n"};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__4 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__4_value;
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " @ "};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__5 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__5_value;
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "\n    rev = "};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__6 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__6_value;
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "\n    version = "};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__7 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "git#"};
static const lean_object* l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__0 = (const lean_object*)&l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__0_value;
static lean_once_cell_t l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__1;
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Dependency_materialize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = ": Git source not found on Reservoir"};
static const lean_object* l_Lake_Dependency_materialize___closed__0 = (const lean_object*)&l_Lake_Dependency_materialize___closed__0_value;
static const lean_string_object l_Lake_Dependency_materialize___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = ": version `"};
static const lean_object* l_Lake_Dependency_materialize___closed__1 = (const lean_object*)&l_Lake_Dependency_materialize___closed__1_value;
static const lean_string_object l_Lake_Dependency_materialize___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "` not found on Reservoir"};
static const lean_object* l_Lake_Dependency_materialize___closed__2 = (const lean_object*)&l_Lake_Dependency_materialize___closed__2_value;
static const lean_string_object l_Lake_Dependency_materialize___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 96, .m_capacity = 96, .m_length = 95, .m_data = ": could not fetch package versions: this may be a transient error or a bug in Lake or Reservoir"};
static const lean_object* l_Lake_Dependency_materialize___closed__3 = (const lean_object*)&l_Lake_Dependency_materialize___closed__3_value;
static const lean_string_object l_Lake_Dependency_materialize___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = ": using version `"};
static const lean_object* l_Lake_Dependency_materialize___closed__4 = (const lean_object*)&l_Lake_Dependency_materialize___closed__4_value;
static const lean_string_object l_Lake_Dependency_materialize___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "` at revision `"};
static const lean_object* l_Lake_Dependency_materialize___closed__5 = (const lean_object*)&l_Lake_Dependency_materialize___closed__5_value;
static const lean_string_object l_Lake_Dependency_materialize___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lake_Dependency_materialize___closed__6 = (const lean_object*)&l_Lake_Dependency_materialize___closed__6_value;
static const lean_string_object l_Lake_Dependency_materialize___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 93, .m_capacity = 93, .m_length = 92, .m_data = ": could not materialize package: this may be a transient error or a bug in Lake or Reservoir"};
static const lean_object* l_Lake_Dependency_materialize___closed__7 = (const lean_object*)&l_Lake_Dependency_materialize___closed__7_value;
static const lean_closure_object l_Lake_Dependency_materialize___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Util_Version_0__Lake_VerRange_parseM, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Dependency_materialize___closed__8 = (const lean_object*)&l_Lake_Dependency_materialize___closed__8_value;
static const lean_string_object l_Lake_Dependency_materialize___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = ": invalid dependency version range: "};
static const lean_object* l_Lake_Dependency_materialize___closed__9 = (const lean_object*)&l_Lake_Dependency_materialize___closed__9_value;
static const lean_string_object l_Lake_Dependency_materialize___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 93, .m_capacity = 93, .m_length = 92, .m_data = ": ill-formed dependency: dependency is missing a source and is missing a scope for Reservoir"};
static const lean_object* l_Lake_Dependency_materialize___closed__10 = (const lean_object*)&l_Lake_Dependency_materialize___closed__10_value;
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_PackageEntry_materialize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HEAD"};
static const lean_object* l_Lake_PackageEntry_materialize___closed__0 = (const lean_object*)&l_Lake_PackageEntry_materialize___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___redArg(lean_object* v___y_1_, lean_object* v___y_2_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_apply_2(v___y_2_, v___y_1_, lean_box(0));
v___x_5_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5_, 0, v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___redArg___boxed(lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___redArg(v___y_6_, v___y_7_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0(lean_object* v_x_10_, lean_object* v___y_11_, lean_object* v___y_12_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___redArg(v___y_11_, v___y_12_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___boxed(lean_object* v_x_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0(v_x_15_, v___y_16_, v___y_17_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1_spec__1___redArg(lean_object* v___y_20_, lean_object* v___y_21_){
_start:
{
lean_object* v___x_23_; lean_object* v___x_24_; 
v___x_23_ = lean_apply_2(v___y_20_, v___y_21_, lean_box(0));
v___x_24_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_24_, 0, v___x_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1_spec__1___redArg___boxed(lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1_spec__1___redArg(v___y_25_, v___y_26_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(lean_object* v_as_29_, size_t v_i_30_, size_t v_stop_31_, lean_object* v_b_32_, lean_object* v___y_33_){
_start:
{
uint8_t v___x_35_; 
v___x_35_ = lean_usize_dec_eq(v_i_30_, v_stop_31_);
if (v___x_35_ == 0)
{
lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_36_ = lean_array_uget_borrowed(v_as_29_, v_i_30_);
lean_inc(v___x_36_);
lean_inc_ref(v___y_33_);
v___x_37_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1_spec__1___redArg(v___y_33_, v___x_36_);
if (lean_obj_tag(v___x_37_) == 0)
{
lean_object* v_a_38_; size_t v___x_39_; size_t v___x_40_; 
v_a_38_ = lean_ctor_get(v___x_37_, 0);
lean_inc(v_a_38_);
lean_dec_ref(v___x_37_);
v___x_39_ = ((size_t)1ULL);
v___x_40_ = lean_usize_add(v_i_30_, v___x_39_);
v_i_30_ = v___x_40_;
v_b_32_ = v_a_38_;
goto _start;
}
else
{
lean_dec_ref(v___y_33_);
return v___x_37_;
}
}
else
{
lean_object* v___x_42_; 
lean_dec_ref(v___y_33_);
v___x_42_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_42_, 0, v_b_32_);
return v___x_42_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1___boxed(lean_object* v_as_43_, lean_object* v_i_44_, lean_object* v_stop_45_, lean_object* v_b_46_, lean_object* v___y_47_, lean_object* v___y_48_){
_start:
{
size_t v_i_boxed_49_; size_t v_stop_boxed_50_; lean_object* v_res_51_; 
v_i_boxed_49_ = lean_unbox_usize(v_i_44_);
lean_dec(v_i_44_);
v_stop_boxed_50_ = lean_unbox_usize(v_stop_45_);
lean_dec(v_stop_45_);
v_res_51_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_as_43_, v_i_boxed_49_, v_stop_boxed_50_, v_b_46_, v___y_47_);
lean_dec_ref(v_as_43_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg(lean_object* v_name_58_, lean_object* v_repo_59_, lean_object* v_rev_x3f_60_, lean_object* v_a_61_){
_start:
{
uint8_t v_a_64_; lean_object* v___y_77_; lean_object* v___y_78_; uint8_t v_val_79_; lean_object* v___y_94_; lean_object* v_a_95_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_161_ = l_Lake_Git_defaultRemote;
v___x_162_ = lean_unsigned_to_nat(0u);
v___x_163_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
lean_inc_ref(v_repo_59_);
v___x_164_ = l_Lake_GitRepo_findRemoteRevision(v_repo_59_, v_rev_x3f_60_, v___x_161_, v___x_163_);
if (lean_obj_tag(v___x_164_) == 0)
{
lean_object* v_a_165_; lean_object* v_a_166_; lean_object* v___x_194_; uint8_t v___x_195_; 
v_a_165_ = lean_ctor_get(v___x_164_, 0);
lean_inc(v_a_165_);
v_a_166_ = lean_ctor_get(v___x_164_, 1);
lean_inc(v_a_166_);
lean_dec_ref(v___x_164_);
v___x_194_ = lean_array_get_size(v_a_166_);
v___x_195_ = lean_nat_dec_lt(v___x_162_, v___x_194_);
if (v___x_195_ == 0)
{
lean_dec(v_a_166_);
goto v___jp_167_;
}
else
{
lean_object* v___x_196_; uint8_t v___x_197_; 
v___x_196_ = lean_box(0);
v___x_197_ = lean_nat_dec_le(v___x_194_, v___x_194_);
if (v___x_197_ == 0)
{
if (v___x_195_ == 0)
{
lean_dec(v_a_166_);
goto v___jp_167_;
}
else
{
size_t v___x_198_; size_t v___x_199_; lean_object* v___x_200_; 
v___x_198_ = ((size_t)0ULL);
v___x_199_ = lean_usize_of_nat(v___x_194_);
lean_inc_ref(v_a_61_);
v___x_200_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_166_, v___x_198_, v___x_199_, v___x_196_, v_a_61_);
lean_dec(v_a_166_);
if (lean_obj_tag(v___x_200_) == 0)
{
lean_dec_ref(v___x_200_);
goto v___jp_167_;
}
else
{
lean_dec(v_a_165_);
lean_dec_ref(v_a_61_);
lean_dec_ref(v_repo_59_);
lean_dec_ref(v_name_58_);
return v___x_200_;
}
}
}
else
{
size_t v___x_201_; size_t v___x_202_; lean_object* v___x_203_; 
v___x_201_ = ((size_t)0ULL);
v___x_202_ = lean_usize_of_nat(v___x_194_);
lean_inc_ref(v_a_61_);
v___x_203_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_166_, v___x_201_, v___x_202_, v___x_196_, v_a_61_);
lean_dec(v_a_166_);
if (lean_obj_tag(v___x_203_) == 0)
{
lean_dec_ref(v___x_203_);
goto v___jp_167_;
}
else
{
lean_dec(v_a_165_);
lean_dec_ref(v_a_61_);
lean_dec_ref(v_repo_59_);
lean_dec_ref(v_name_58_);
return v___x_203_;
}
}
}
v___jp_167_:
{
lean_object* v___x_168_; 
lean_inc_ref(v_repo_59_);
v___x_168_ = l_Lake_GitRepo_getHeadRevision(v_repo_59_, v___x_163_);
if (lean_obj_tag(v___x_168_) == 0)
{
lean_object* v_a_169_; lean_object* v_a_170_; lean_object* v___x_171_; uint8_t v___x_172_; 
v_a_169_ = lean_ctor_get(v___x_168_, 0);
lean_inc(v_a_169_);
v_a_170_ = lean_ctor_get(v___x_168_, 1);
lean_inc(v_a_170_);
lean_dec_ref(v___x_168_);
v___x_171_ = lean_array_get_size(v_a_170_);
v___x_172_ = lean_nat_dec_lt(v___x_162_, v___x_171_);
if (v___x_172_ == 0)
{
lean_dec(v_a_170_);
v___y_94_ = v_a_165_;
v_a_95_ = v_a_169_;
goto v___jp_93_;
}
else
{
lean_object* v___x_173_; uint8_t v___x_174_; 
v___x_173_ = lean_box(0);
v___x_174_ = lean_nat_dec_le(v___x_171_, v___x_171_);
if (v___x_174_ == 0)
{
if (v___x_172_ == 0)
{
lean_dec(v_a_170_);
v___y_94_ = v_a_165_;
v_a_95_ = v_a_169_;
goto v___jp_93_;
}
else
{
size_t v___x_175_; size_t v___x_176_; lean_object* v___x_177_; 
v___x_175_ = ((size_t)0ULL);
v___x_176_ = lean_usize_of_nat(v___x_171_);
lean_inc_ref(v_a_61_);
v___x_177_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_170_, v___x_175_, v___x_176_, v___x_173_, v_a_61_);
lean_dec(v_a_170_);
if (lean_obj_tag(v___x_177_) == 0)
{
lean_dec_ref(v___x_177_);
v___y_94_ = v_a_165_;
v_a_95_ = v_a_169_;
goto v___jp_93_;
}
else
{
lean_dec(v_a_169_);
lean_dec(v_a_165_);
lean_dec_ref(v_a_61_);
lean_dec_ref(v_repo_59_);
lean_dec_ref(v_name_58_);
return v___x_177_;
}
}
}
else
{
size_t v___x_178_; size_t v___x_179_; lean_object* v___x_180_; 
v___x_178_ = ((size_t)0ULL);
v___x_179_ = lean_usize_of_nat(v___x_171_);
lean_inc_ref(v_a_61_);
v___x_180_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_170_, v___x_178_, v___x_179_, v___x_173_, v_a_61_);
lean_dec(v_a_170_);
if (lean_obj_tag(v___x_180_) == 0)
{
lean_dec_ref(v___x_180_);
v___y_94_ = v_a_165_;
v_a_95_ = v_a_169_;
goto v___jp_93_;
}
else
{
lean_dec(v_a_169_);
lean_dec(v_a_165_);
lean_dec_ref(v_a_61_);
lean_dec_ref(v_repo_59_);
lean_dec_ref(v_name_58_);
return v___x_180_;
}
}
}
}
else
{
lean_object* v_a_181_; lean_object* v___x_182_; uint8_t v___x_183_; 
lean_dec(v_a_165_);
lean_dec_ref(v_repo_59_);
lean_dec_ref(v_name_58_);
v_a_181_ = lean_ctor_get(v___x_168_, 1);
lean_inc(v_a_181_);
lean_dec_ref(v___x_168_);
v___x_182_ = lean_array_get_size(v_a_181_);
v___x_183_ = lean_nat_dec_lt(v___x_162_, v___x_182_);
if (v___x_183_ == 0)
{
lean_object* v___x_184_; lean_object* v___x_185_; 
lean_dec(v_a_181_);
lean_dec_ref(v_a_61_);
v___x_184_ = lean_box(0);
v___x_185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
return v___x_185_;
}
else
{
lean_object* v___x_186_; uint8_t v___x_187_; 
v___x_186_ = lean_box(0);
v___x_187_ = lean_nat_dec_le(v___x_182_, v___x_182_);
if (v___x_187_ == 0)
{
if (v___x_183_ == 0)
{
lean_dec(v_a_181_);
lean_dec_ref(v_a_61_);
goto v___jp_155_;
}
else
{
size_t v___x_188_; size_t v___x_189_; lean_object* v___x_190_; 
v___x_188_ = ((size_t)0ULL);
v___x_189_ = lean_usize_of_nat(v___x_182_);
v___x_190_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_181_, v___x_188_, v___x_189_, v___x_186_, v_a_61_);
lean_dec(v_a_181_);
if (lean_obj_tag(v___x_190_) == 0)
{
lean_dec_ref(v___x_190_);
goto v___jp_155_;
}
else
{
return v___x_190_;
}
}
}
else
{
size_t v___x_191_; size_t v___x_192_; lean_object* v___x_193_; 
v___x_191_ = ((size_t)0ULL);
v___x_192_ = lean_usize_of_nat(v___x_182_);
v___x_193_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_181_, v___x_191_, v___x_192_, v___x_186_, v_a_61_);
lean_dec(v_a_181_);
if (lean_obj_tag(v___x_193_) == 0)
{
lean_dec_ref(v___x_193_);
goto v___jp_155_;
}
else
{
return v___x_193_;
}
}
}
}
}
}
else
{
lean_object* v_a_204_; lean_object* v___x_205_; uint8_t v___x_206_; 
lean_dec_ref(v_repo_59_);
lean_dec_ref(v_name_58_);
v_a_204_ = lean_ctor_get(v___x_164_, 1);
lean_inc(v_a_204_);
lean_dec_ref(v___x_164_);
v___x_205_ = lean_array_get_size(v_a_204_);
v___x_206_ = lean_nat_dec_lt(v___x_162_, v___x_205_);
if (v___x_206_ == 0)
{
lean_object* v___x_207_; lean_object* v___x_208_; 
lean_dec(v_a_204_);
lean_dec_ref(v_a_61_);
v___x_207_ = lean_box(0);
v___x_208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_208_, 0, v___x_207_);
return v___x_208_;
}
else
{
lean_object* v___x_209_; uint8_t v___x_210_; 
v___x_209_ = lean_box(0);
v___x_210_ = lean_nat_dec_le(v___x_205_, v___x_205_);
if (v___x_210_ == 0)
{
if (v___x_206_ == 0)
{
lean_dec(v_a_204_);
lean_dec_ref(v_a_61_);
goto v___jp_158_;
}
else
{
size_t v___x_211_; size_t v___x_212_; lean_object* v___x_213_; 
v___x_211_ = ((size_t)0ULL);
v___x_212_ = lean_usize_of_nat(v___x_205_);
v___x_213_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_204_, v___x_211_, v___x_212_, v___x_209_, v_a_61_);
lean_dec(v_a_204_);
if (lean_obj_tag(v___x_213_) == 0)
{
lean_dec_ref(v___x_213_);
goto v___jp_158_;
}
else
{
return v___x_213_;
}
}
}
else
{
size_t v___x_214_; size_t v___x_215_; lean_object* v___x_216_; 
v___x_214_ = ((size_t)0ULL);
v___x_215_ = lean_usize_of_nat(v___x_205_);
v___x_216_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_204_, v___x_214_, v___x_215_, v___x_209_, v_a_61_);
lean_dec(v_a_204_);
if (lean_obj_tag(v___x_216_) == 0)
{
lean_dec_ref(v___x_216_);
goto v___jp_158_;
}
else
{
return v___x_216_;
}
}
}
}
v___jp_63_:
{
if (v_a_64_ == 0)
{
lean_object* v___x_65_; lean_object* v___x_66_; 
lean_dec_ref(v_a_61_);
lean_dec_ref(v_repo_59_);
lean_dec_ref(v_name_58_);
v___x_65_ = lean_box(0);
v___x_66_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_66_, 0, v___x_65_);
return v___x_66_;
}
else
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; uint8_t v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_67_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0));
v___x_68_ = lean_string_append(v_name_58_, v___x_67_);
v___x_69_ = lean_string_append(v___x_68_, v_repo_59_);
lean_dec_ref(v_repo_59_);
v___x_70_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1));
v___x_71_ = lean_string_append(v___x_69_, v___x_70_);
v___x_72_ = 2;
v___x_73_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_73_, 0, v___x_71_);
lean_ctor_set_uint8(v___x_73_, sizeof(void*)*1, v___x_72_);
v___x_74_ = lean_apply_2(v_a_61_, v___x_73_, lean_box(0));
v___x_75_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_75_, 0, v___x_74_);
return v___x_75_;
}
}
v___jp_76_:
{
lean_object* v___x_80_; uint8_t v___x_81_; 
v___x_80_ = lean_array_get_size(v___y_77_);
v___x_81_ = lean_nat_dec_lt(v___y_78_, v___x_80_);
if (v___x_81_ == 0)
{
lean_dec_ref(v___y_77_);
v_a_64_ = v_val_79_;
goto v___jp_63_;
}
else
{
lean_object* v___x_82_; uint8_t v___x_83_; 
v___x_82_ = lean_box(0);
v___x_83_ = lean_nat_dec_le(v___x_80_, v___x_80_);
if (v___x_83_ == 0)
{
if (v___x_81_ == 0)
{
lean_dec_ref(v___y_77_);
v_a_64_ = v_val_79_;
goto v___jp_63_;
}
else
{
size_t v___x_84_; size_t v___x_85_; lean_object* v___x_86_; 
v___x_84_ = ((size_t)0ULL);
v___x_85_ = lean_usize_of_nat(v___x_80_);
lean_inc_ref(v_a_61_);
v___x_86_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v___y_77_, v___x_84_, v___x_85_, v___x_82_, v_a_61_);
lean_dec_ref(v___y_77_);
if (lean_obj_tag(v___x_86_) == 0)
{
lean_dec_ref(v___x_86_);
v_a_64_ = v_val_79_;
goto v___jp_63_;
}
else
{
lean_dec_ref(v_a_61_);
lean_dec_ref(v_repo_59_);
lean_dec_ref(v_name_58_);
return v___x_86_;
}
}
}
else
{
size_t v___x_87_; size_t v___x_88_; lean_object* v___x_89_; 
v___x_87_ = ((size_t)0ULL);
v___x_88_ = lean_usize_of_nat(v___x_80_);
lean_inc_ref(v_a_61_);
v___x_89_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v___y_77_, v___x_87_, v___x_88_, v___x_82_, v_a_61_);
lean_dec_ref(v___y_77_);
if (lean_obj_tag(v___x_89_) == 0)
{
lean_dec_ref(v___x_89_);
v_a_64_ = v_val_79_;
goto v___jp_63_;
}
else
{
lean_dec_ref(v_a_61_);
lean_dec_ref(v_repo_59_);
lean_dec_ref(v_name_58_);
return v___x_89_;
}
}
}
}
v___jp_90_:
{
lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_91_ = lean_box(0);
v___x_92_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_92_, 0, v___x_91_);
return v___x_92_;
}
v___jp_93_:
{
uint8_t v___x_96_; 
v___x_96_ = lean_string_dec_eq(v_a_95_, v___y_94_);
lean_dec_ref(v_a_95_);
if (v___x_96_ == 0)
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; uint8_t v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_97_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_98_ = lean_string_append(v_name_58_, v___x_97_);
v___x_99_ = lean_string_append(v___x_98_, v___y_94_);
v___x_100_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3));
v___x_101_ = lean_string_append(v___x_99_, v___x_100_);
v___x_102_ = 1;
v___x_103_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_103_, 0, v___x_101_);
lean_ctor_set_uint8(v___x_103_, sizeof(void*)*1, v___x_102_);
lean_inc_ref(v_a_61_);
v___x_104_ = lean_apply_2(v_a_61_, v___x_103_, lean_box(0));
v___x_105_ = lean_unsigned_to_nat(0u);
v___x_106_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
v___x_107_ = l_Lake_GitRepo_checkoutDetach(v___y_94_, v_repo_59_, v___x_106_);
if (lean_obj_tag(v___x_107_) == 0)
{
lean_object* v_a_108_; lean_object* v_a_109_; lean_object* v___x_110_; uint8_t v___x_111_; 
v_a_108_ = lean_ctor_get(v___x_107_, 0);
lean_inc(v_a_108_);
v_a_109_ = lean_ctor_get(v___x_107_, 1);
lean_inc(v_a_109_);
lean_dec_ref(v___x_107_);
v___x_110_ = lean_array_get_size(v_a_109_);
v___x_111_ = lean_nat_dec_lt(v___x_105_, v___x_110_);
if (v___x_111_ == 0)
{
lean_object* v___x_112_; 
lean_dec(v_a_109_);
lean_dec_ref(v_a_61_);
v___x_112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_112_, 0, v_a_108_);
return v___x_112_;
}
else
{
lean_object* v___x_113_; uint8_t v___x_114_; 
v___x_113_ = lean_box(0);
v___x_114_ = lean_nat_dec_le(v___x_110_, v___x_110_);
if (v___x_114_ == 0)
{
if (v___x_111_ == 0)
{
lean_object* v___x_115_; 
lean_dec(v_a_109_);
lean_dec_ref(v_a_61_);
v___x_115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_115_, 0, v_a_108_);
return v___x_115_;
}
else
{
size_t v___x_116_; size_t v___x_117_; lean_object* v___x_118_; 
v___x_116_ = ((size_t)0ULL);
v___x_117_ = lean_usize_of_nat(v___x_110_);
v___x_118_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_109_, v___x_116_, v___x_117_, v___x_113_, v_a_61_);
lean_dec(v_a_109_);
if (lean_obj_tag(v___x_118_) == 0)
{
lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_125_; 
v_isSharedCheck_125_ = !lean_is_exclusive(v___x_118_);
if (v_isSharedCheck_125_ == 0)
{
lean_object* v_unused_126_; 
v_unused_126_ = lean_ctor_get(v___x_118_, 0);
lean_dec(v_unused_126_);
v___x_120_ = v___x_118_;
v_isShared_121_ = v_isSharedCheck_125_;
goto v_resetjp_119_;
}
else
{
lean_dec(v___x_118_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_125_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v___x_123_; 
if (v_isShared_121_ == 0)
{
lean_ctor_set(v___x_120_, 0, v_a_108_);
v___x_123_ = v___x_120_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v_a_108_);
v___x_123_ = v_reuseFailAlloc_124_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
return v___x_123_;
}
}
}
else
{
lean_dec(v_a_108_);
return v___x_118_;
}
}
}
else
{
size_t v___x_127_; size_t v___x_128_; lean_object* v___x_129_; 
v___x_127_ = ((size_t)0ULL);
v___x_128_ = lean_usize_of_nat(v___x_110_);
v___x_129_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_109_, v___x_127_, v___x_128_, v___x_113_, v_a_61_);
lean_dec(v_a_109_);
if (lean_obj_tag(v___x_129_) == 0)
{
lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_136_; 
v_isSharedCheck_136_ = !lean_is_exclusive(v___x_129_);
if (v_isSharedCheck_136_ == 0)
{
lean_object* v_unused_137_; 
v_unused_137_ = lean_ctor_get(v___x_129_, 0);
lean_dec(v_unused_137_);
v___x_131_ = v___x_129_;
v_isShared_132_ = v_isSharedCheck_136_;
goto v_resetjp_130_;
}
else
{
lean_dec(v___x_129_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_136_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
lean_object* v___x_134_; 
if (v_isShared_132_ == 0)
{
lean_ctor_set(v___x_131_, 0, v_a_108_);
v___x_134_ = v___x_131_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v_a_108_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
return v___x_134_;
}
}
}
else
{
lean_dec(v_a_108_);
return v___x_129_;
}
}
}
}
else
{
lean_object* v_a_138_; lean_object* v___x_139_; uint8_t v___x_140_; 
v_a_138_ = lean_ctor_get(v___x_107_, 1);
lean_inc(v_a_138_);
lean_dec_ref(v___x_107_);
v___x_139_ = lean_array_get_size(v_a_138_);
v___x_140_ = lean_nat_dec_lt(v___x_105_, v___x_139_);
if (v___x_140_ == 0)
{
lean_object* v___x_141_; lean_object* v___x_142_; 
lean_dec(v_a_138_);
lean_dec_ref(v_a_61_);
v___x_141_ = lean_box(0);
v___x_142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_142_, 0, v___x_141_);
return v___x_142_;
}
else
{
lean_object* v___x_143_; uint8_t v___x_144_; 
v___x_143_ = lean_box(0);
v___x_144_ = lean_nat_dec_le(v___x_139_, v___x_139_);
if (v___x_144_ == 0)
{
if (v___x_140_ == 0)
{
lean_dec(v_a_138_);
lean_dec_ref(v_a_61_);
goto v___jp_90_;
}
else
{
size_t v___x_145_; size_t v___x_146_; lean_object* v___x_147_; 
v___x_145_ = ((size_t)0ULL);
v___x_146_ = lean_usize_of_nat(v___x_139_);
v___x_147_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_138_, v___x_145_, v___x_146_, v___x_143_, v_a_61_);
lean_dec(v_a_138_);
if (lean_obj_tag(v___x_147_) == 0)
{
lean_dec_ref(v___x_147_);
goto v___jp_90_;
}
else
{
return v___x_147_;
}
}
}
else
{
size_t v___x_148_; size_t v___x_149_; lean_object* v___x_150_; 
v___x_148_ = ((size_t)0ULL);
v___x_149_ = lean_usize_of_nat(v___x_139_);
v___x_150_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_138_, v___x_148_, v___x_149_, v___x_143_, v_a_61_);
lean_dec(v_a_138_);
if (lean_obj_tag(v___x_150_) == 0)
{
lean_dec_ref(v___x_150_);
goto v___jp_90_;
}
else
{
return v___x_150_;
}
}
}
}
}
else
{
uint8_t v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
lean_dec_ref(v___y_94_);
lean_inc_ref(v_repo_59_);
v___x_151_ = l_Lake_GitRepo_hasNoDiff(v_repo_59_);
v___x_152_ = lean_unsigned_to_nat(0u);
v___x_153_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
if (v___x_151_ == 0)
{
v___y_77_ = v___x_153_;
v___y_78_ = v___x_152_;
v_val_79_ = v___x_96_;
goto v___jp_76_;
}
else
{
uint8_t v___x_154_; 
v___x_154_ = 0;
v___y_77_ = v___x_153_;
v___y_78_ = v___x_152_;
v_val_79_ = v___x_154_;
goto v___jp_76_;
}
}
}
v___jp_155_:
{
lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_156_ = lean_box(0);
v___x_157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
return v___x_157_;
}
v___jp_158_:
{
lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_159_ = lean_box(0);
v___x_160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
return v___x_160_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___boxed(lean_object* v_name_217_, lean_object* v_repo_218_, lean_object* v_rev_x3f_219_, lean_object* v_a_220_, lean_object* v_a_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg(v_name_217_, v_repo_218_, v_rev_x3f_219_, v_a_220_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1_spec__1(lean_object* v___y_223_, lean_object* v_x_224_, lean_object* v___y_225_){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1_spec__1___redArg(v___y_223_, v___y_225_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1_spec__1___boxed(lean_object* v___y_228_, lean_object* v_x_229_, lean_object* v___y_230_, lean_object* v___y_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1_spec__1(v___y_228_, v_x_229_, v___y_230_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg(lean_object* v_name_234_, lean_object* v_repo_235_, lean_object* v_url_236_, lean_object* v_rev_x3f_237_, lean_object* v_a_238_){
_start:
{
lean_object* v_a_244_; lean_object* v___y_342_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; uint8_t v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_346_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___closed__0));
lean_inc_ref(v_name_234_);
v___x_347_ = lean_string_append(v_name_234_, v___x_346_);
v___x_348_ = lean_string_append(v___x_347_, v_url_236_);
v___x_349_ = 1;
v___x_350_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_350_, 0, v___x_348_);
lean_ctor_set_uint8(v___x_350_, sizeof(void*)*1, v___x_349_);
lean_inc_ref(v_a_238_);
v___x_351_ = lean_apply_2(v_a_238_, v___x_350_, lean_box(0));
v___x_352_ = lean_unsigned_to_nat(0u);
v___x_353_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
lean_inc_ref(v_repo_235_);
v___x_354_ = l_Lake_GitRepo_clone(v_url_236_, v_repo_235_, v___x_353_);
if (lean_obj_tag(v___x_354_) == 0)
{
lean_object* v_a_355_; lean_object* v___x_356_; uint8_t v___x_357_; 
v_a_355_ = lean_ctor_get(v___x_354_, 1);
lean_inc(v_a_355_);
lean_dec_ref(v___x_354_);
v___x_356_ = lean_array_get_size(v_a_355_);
v___x_357_ = lean_nat_dec_lt(v___x_352_, v___x_356_);
if (v___x_357_ == 0)
{
lean_dec(v_a_355_);
goto v___jp_302_;
}
else
{
lean_object* v___x_358_; uint8_t v___x_359_; 
v___x_358_ = lean_box(0);
v___x_359_ = lean_nat_dec_le(v___x_356_, v___x_356_);
if (v___x_359_ == 0)
{
if (v___x_357_ == 0)
{
lean_dec(v_a_355_);
goto v___jp_302_;
}
else
{
size_t v___x_360_; size_t v___x_361_; lean_object* v___x_362_; 
v___x_360_ = ((size_t)0ULL);
v___x_361_ = lean_usize_of_nat(v___x_356_);
lean_inc_ref(v_a_238_);
v___x_362_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_355_, v___x_360_, v___x_361_, v___x_358_, v_a_238_);
lean_dec(v_a_355_);
if (lean_obj_tag(v___x_362_) == 0)
{
lean_dec_ref(v___x_362_);
goto v___jp_302_;
}
else
{
v___y_342_ = v___x_362_;
goto v___jp_341_;
}
}
}
else
{
size_t v___x_363_; size_t v___x_364_; lean_object* v___x_365_; 
v___x_363_ = ((size_t)0ULL);
v___x_364_ = lean_usize_of_nat(v___x_356_);
lean_inc_ref(v_a_238_);
v___x_365_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_355_, v___x_363_, v___x_364_, v___x_358_, v_a_238_);
lean_dec(v_a_355_);
if (lean_obj_tag(v___x_365_) == 0)
{
lean_dec_ref(v___x_365_);
goto v___jp_302_;
}
else
{
v___y_342_ = v___x_365_;
goto v___jp_341_;
}
}
}
}
else
{
lean_object* v_a_366_; lean_object* v___x_367_; uint8_t v___x_368_; 
v_a_366_ = lean_ctor_get(v___x_354_, 1);
lean_inc(v_a_366_);
lean_dec_ref(v___x_354_);
v___x_367_ = lean_array_get_size(v_a_366_);
v___x_368_ = lean_nat_dec_lt(v___x_352_, v___x_367_);
if (v___x_368_ == 0)
{
lean_object* v___x_369_; lean_object* v___x_370_; 
lean_dec(v_a_366_);
lean_dec_ref(v_a_238_);
lean_dec(v_rev_x3f_237_);
lean_dec_ref(v_repo_235_);
lean_dec_ref(v_name_234_);
v___x_369_ = lean_box(0);
v___x_370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_370_, 0, v___x_369_);
return v___x_370_;
}
else
{
lean_object* v___x_371_; uint8_t v___x_372_; 
v___x_371_ = lean_box(0);
v___x_372_ = lean_nat_dec_le(v___x_367_, v___x_367_);
if (v___x_372_ == 0)
{
if (v___x_368_ == 0)
{
lean_dec(v_a_366_);
lean_dec_ref(v_a_238_);
lean_dec(v_rev_x3f_237_);
lean_dec_ref(v_repo_235_);
lean_dec_ref(v_name_234_);
goto v___jp_343_;
}
else
{
size_t v___x_373_; size_t v___x_374_; lean_object* v___x_375_; 
v___x_373_ = ((size_t)0ULL);
v___x_374_ = lean_usize_of_nat(v___x_367_);
lean_inc_ref(v_a_238_);
v___x_375_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_366_, v___x_373_, v___x_374_, v___x_371_, v_a_238_);
lean_dec(v_a_366_);
if (lean_obj_tag(v___x_375_) == 0)
{
lean_dec_ref(v___x_375_);
lean_dec_ref(v_a_238_);
lean_dec(v_rev_x3f_237_);
lean_dec_ref(v_repo_235_);
lean_dec_ref(v_name_234_);
goto v___jp_343_;
}
else
{
v___y_342_ = v___x_375_;
goto v___jp_341_;
}
}
}
else
{
size_t v___x_376_; size_t v___x_377_; lean_object* v___x_378_; 
v___x_376_ = ((size_t)0ULL);
v___x_377_ = lean_usize_of_nat(v___x_367_);
lean_inc_ref(v_a_238_);
v___x_378_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_366_, v___x_376_, v___x_377_, v___x_371_, v_a_238_);
lean_dec(v_a_366_);
if (lean_obj_tag(v___x_378_) == 0)
{
lean_dec_ref(v___x_378_);
lean_dec_ref(v_a_238_);
lean_dec(v_rev_x3f_237_);
lean_dec_ref(v_repo_235_);
lean_dec_ref(v_name_234_);
goto v___jp_343_;
}
else
{
v___y_342_ = v___x_378_;
goto v___jp_341_;
}
}
}
}
v___jp_240_:
{
lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_241_ = lean_box(0);
v___x_242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_242_, 0, v___x_241_);
return v___x_242_;
}
v___jp_243_:
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; uint8_t v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_245_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_246_ = lean_string_append(v_name_234_, v___x_245_);
v___x_247_ = lean_string_append(v___x_246_, v_a_244_);
v___x_248_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3));
v___x_249_ = lean_string_append(v___x_247_, v___x_248_);
v___x_250_ = 1;
v___x_251_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_251_, 0, v___x_249_);
lean_ctor_set_uint8(v___x_251_, sizeof(void*)*1, v___x_250_);
lean_inc_ref(v_a_238_);
v___x_252_ = lean_apply_2(v_a_238_, v___x_251_, lean_box(0));
v___x_253_ = lean_unsigned_to_nat(0u);
v___x_254_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
v___x_255_ = l_Lake_GitRepo_checkoutDetach(v_a_244_, v_repo_235_, v___x_254_);
if (lean_obj_tag(v___x_255_) == 0)
{
lean_object* v_a_256_; lean_object* v_a_257_; lean_object* v___x_258_; uint8_t v___x_259_; 
v_a_256_ = lean_ctor_get(v___x_255_, 0);
lean_inc(v_a_256_);
v_a_257_ = lean_ctor_get(v___x_255_, 1);
lean_inc(v_a_257_);
lean_dec_ref(v___x_255_);
v___x_258_ = lean_array_get_size(v_a_257_);
v___x_259_ = lean_nat_dec_lt(v___x_253_, v___x_258_);
if (v___x_259_ == 0)
{
lean_object* v___x_260_; 
lean_dec(v_a_257_);
lean_dec_ref(v_a_238_);
v___x_260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_260_, 0, v_a_256_);
return v___x_260_;
}
else
{
lean_object* v___x_261_; uint8_t v___x_262_; 
v___x_261_ = lean_box(0);
v___x_262_ = lean_nat_dec_le(v___x_258_, v___x_258_);
if (v___x_262_ == 0)
{
if (v___x_259_ == 0)
{
lean_object* v___x_263_; 
lean_dec(v_a_257_);
lean_dec_ref(v_a_238_);
v___x_263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_263_, 0, v_a_256_);
return v___x_263_;
}
else
{
size_t v___x_264_; size_t v___x_265_; lean_object* v___x_266_; 
v___x_264_ = ((size_t)0ULL);
v___x_265_ = lean_usize_of_nat(v___x_258_);
v___x_266_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_257_, v___x_264_, v___x_265_, v___x_261_, v_a_238_);
lean_dec(v_a_257_);
if (lean_obj_tag(v___x_266_) == 0)
{
lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_273_; 
v_isSharedCheck_273_ = !lean_is_exclusive(v___x_266_);
if (v_isSharedCheck_273_ == 0)
{
lean_object* v_unused_274_; 
v_unused_274_ = lean_ctor_get(v___x_266_, 0);
lean_dec(v_unused_274_);
v___x_268_ = v___x_266_;
v_isShared_269_ = v_isSharedCheck_273_;
goto v_resetjp_267_;
}
else
{
lean_dec(v___x_266_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_273_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_271_; 
if (v_isShared_269_ == 0)
{
lean_ctor_set(v___x_268_, 0, v_a_256_);
v___x_271_ = v___x_268_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_a_256_);
v___x_271_ = v_reuseFailAlloc_272_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
return v___x_271_;
}
}
}
else
{
lean_dec(v_a_256_);
return v___x_266_;
}
}
}
else
{
size_t v___x_275_; size_t v___x_276_; lean_object* v___x_277_; 
v___x_275_ = ((size_t)0ULL);
v___x_276_ = lean_usize_of_nat(v___x_258_);
v___x_277_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_257_, v___x_275_, v___x_276_, v___x_261_, v_a_238_);
lean_dec(v_a_257_);
if (lean_obj_tag(v___x_277_) == 0)
{
lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_284_; 
v_isSharedCheck_284_ = !lean_is_exclusive(v___x_277_);
if (v_isSharedCheck_284_ == 0)
{
lean_object* v_unused_285_; 
v_unused_285_ = lean_ctor_get(v___x_277_, 0);
lean_dec(v_unused_285_);
v___x_279_ = v___x_277_;
v_isShared_280_ = v_isSharedCheck_284_;
goto v_resetjp_278_;
}
else
{
lean_dec(v___x_277_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_284_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___x_282_; 
if (v_isShared_280_ == 0)
{
lean_ctor_set(v___x_279_, 0, v_a_256_);
v___x_282_ = v___x_279_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v_a_256_);
v___x_282_ = v_reuseFailAlloc_283_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
return v___x_282_;
}
}
}
else
{
lean_dec(v_a_256_);
return v___x_277_;
}
}
}
}
else
{
lean_object* v_a_286_; lean_object* v___x_287_; uint8_t v___x_288_; 
v_a_286_ = lean_ctor_get(v___x_255_, 1);
lean_inc(v_a_286_);
lean_dec_ref(v___x_255_);
v___x_287_ = lean_array_get_size(v_a_286_);
v___x_288_ = lean_nat_dec_lt(v___x_253_, v___x_287_);
if (v___x_288_ == 0)
{
lean_object* v___x_289_; lean_object* v___x_290_; 
lean_dec(v_a_286_);
lean_dec_ref(v_a_238_);
v___x_289_ = lean_box(0);
v___x_290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
return v___x_290_;
}
else
{
lean_object* v___x_291_; uint8_t v___x_292_; 
v___x_291_ = lean_box(0);
v___x_292_ = lean_nat_dec_le(v___x_287_, v___x_287_);
if (v___x_292_ == 0)
{
if (v___x_288_ == 0)
{
lean_dec(v_a_286_);
lean_dec_ref(v_a_238_);
goto v___jp_240_;
}
else
{
size_t v___x_293_; size_t v___x_294_; lean_object* v___x_295_; 
v___x_293_ = ((size_t)0ULL);
v___x_294_ = lean_usize_of_nat(v___x_287_);
v___x_295_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_286_, v___x_293_, v___x_294_, v___x_291_, v_a_238_);
lean_dec(v_a_286_);
if (lean_obj_tag(v___x_295_) == 0)
{
lean_dec_ref(v___x_295_);
goto v___jp_240_;
}
else
{
return v___x_295_;
}
}
}
else
{
size_t v___x_296_; size_t v___x_297_; lean_object* v___x_298_; 
v___x_296_ = ((size_t)0ULL);
v___x_297_ = lean_usize_of_nat(v___x_287_);
v___x_298_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_286_, v___x_296_, v___x_297_, v___x_291_, v_a_238_);
lean_dec(v_a_286_);
if (lean_obj_tag(v___x_298_) == 0)
{
lean_dec_ref(v___x_298_);
goto v___jp_240_;
}
else
{
return v___x_298_;
}
}
}
}
}
v___jp_299_:
{
lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_300_ = lean_box(0);
v___x_301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
return v___x_301_;
}
v___jp_302_:
{
if (lean_obj_tag(v_rev_x3f_237_) == 1)
{
lean_object* v_val_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_338_; 
v_val_303_ = lean_ctor_get(v_rev_x3f_237_, 0);
v_isSharedCheck_338_ = !lean_is_exclusive(v_rev_x3f_237_);
if (v_isSharedCheck_338_ == 0)
{
v___x_305_ = v_rev_x3f_237_;
v_isShared_306_ = v_isSharedCheck_338_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_val_303_);
lean_dec(v_rev_x3f_237_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_338_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_307_ = l_Lake_Git_defaultRemote;
v___x_308_ = lean_unsigned_to_nat(0u);
v___x_309_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
lean_inc_ref(v_repo_235_);
v___x_310_ = l_Lake_GitRepo_resolveRemoteRevision(v_val_303_, v___x_307_, v_repo_235_, v___x_309_);
if (lean_obj_tag(v___x_310_) == 0)
{
lean_object* v_a_311_; lean_object* v_a_312_; lean_object* v___x_313_; uint8_t v___x_314_; 
lean_del_object(v___x_305_);
v_a_311_ = lean_ctor_get(v___x_310_, 0);
lean_inc(v_a_311_);
v_a_312_ = lean_ctor_get(v___x_310_, 1);
lean_inc(v_a_312_);
lean_dec_ref(v___x_310_);
v___x_313_ = lean_array_get_size(v_a_312_);
v___x_314_ = lean_nat_dec_lt(v___x_308_, v___x_313_);
if (v___x_314_ == 0)
{
lean_dec(v_a_312_);
v_a_244_ = v_a_311_;
goto v___jp_243_;
}
else
{
lean_object* v___x_315_; uint8_t v___x_316_; 
v___x_315_ = lean_box(0);
v___x_316_ = lean_nat_dec_le(v___x_313_, v___x_313_);
if (v___x_316_ == 0)
{
if (v___x_314_ == 0)
{
lean_dec(v_a_312_);
v_a_244_ = v_a_311_;
goto v___jp_243_;
}
else
{
size_t v___x_317_; size_t v___x_318_; lean_object* v___x_319_; 
v___x_317_ = ((size_t)0ULL);
v___x_318_ = lean_usize_of_nat(v___x_313_);
lean_inc_ref(v_a_238_);
v___x_319_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_312_, v___x_317_, v___x_318_, v___x_315_, v_a_238_);
lean_dec(v_a_312_);
if (lean_obj_tag(v___x_319_) == 0)
{
lean_dec_ref(v___x_319_);
v_a_244_ = v_a_311_;
goto v___jp_243_;
}
else
{
lean_dec(v_a_311_);
lean_dec_ref(v_a_238_);
lean_dec_ref(v_repo_235_);
lean_dec_ref(v_name_234_);
return v___x_319_;
}
}
}
else
{
size_t v___x_320_; size_t v___x_321_; lean_object* v___x_322_; 
v___x_320_ = ((size_t)0ULL);
v___x_321_ = lean_usize_of_nat(v___x_313_);
lean_inc_ref(v_a_238_);
v___x_322_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_312_, v___x_320_, v___x_321_, v___x_315_, v_a_238_);
lean_dec(v_a_312_);
if (lean_obj_tag(v___x_322_) == 0)
{
lean_dec_ref(v___x_322_);
v_a_244_ = v_a_311_;
goto v___jp_243_;
}
else
{
lean_dec(v_a_311_);
lean_dec_ref(v_a_238_);
lean_dec_ref(v_repo_235_);
lean_dec_ref(v_name_234_);
return v___x_322_;
}
}
}
}
else
{
lean_object* v_a_323_; lean_object* v___x_324_; uint8_t v___x_325_; 
lean_dec_ref(v_repo_235_);
lean_dec_ref(v_name_234_);
v_a_323_ = lean_ctor_get(v___x_310_, 1);
lean_inc(v_a_323_);
lean_dec_ref(v___x_310_);
v___x_324_ = lean_array_get_size(v_a_323_);
v___x_325_ = lean_nat_dec_lt(v___x_308_, v___x_324_);
if (v___x_325_ == 0)
{
lean_object* v___x_326_; lean_object* v___x_328_; 
lean_dec(v_a_323_);
lean_dec_ref(v_a_238_);
v___x_326_ = lean_box(0);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 0, v___x_326_);
v___x_328_ = v___x_305_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v___x_326_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
return v___x_328_;
}
}
else
{
lean_object* v___x_330_; uint8_t v___x_331_; 
lean_del_object(v___x_305_);
v___x_330_ = lean_box(0);
v___x_331_ = lean_nat_dec_le(v___x_324_, v___x_324_);
if (v___x_331_ == 0)
{
if (v___x_325_ == 0)
{
lean_dec(v_a_323_);
lean_dec_ref(v_a_238_);
goto v___jp_299_;
}
else
{
size_t v___x_332_; size_t v___x_333_; lean_object* v___x_334_; 
v___x_332_ = ((size_t)0ULL);
v___x_333_ = lean_usize_of_nat(v___x_324_);
v___x_334_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_323_, v___x_332_, v___x_333_, v___x_330_, v_a_238_);
lean_dec(v_a_323_);
if (lean_obj_tag(v___x_334_) == 0)
{
lean_dec_ref(v___x_334_);
goto v___jp_299_;
}
else
{
return v___x_334_;
}
}
}
else
{
size_t v___x_335_; size_t v___x_336_; lean_object* v___x_337_; 
v___x_335_ = ((size_t)0ULL);
v___x_336_ = lean_usize_of_nat(v___x_324_);
v___x_337_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_323_, v___x_335_, v___x_336_, v___x_330_, v_a_238_);
lean_dec(v_a_323_);
if (lean_obj_tag(v___x_337_) == 0)
{
lean_dec_ref(v___x_337_);
goto v___jp_299_;
}
else
{
return v___x_337_;
}
}
}
}
}
}
else
{
lean_object* v___x_339_; lean_object* v___x_340_; 
lean_dec_ref(v_a_238_);
lean_dec(v_rev_x3f_237_);
lean_dec_ref(v_repo_235_);
lean_dec_ref(v_name_234_);
v___x_339_ = lean_box(0);
v___x_340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
return v___x_340_;
}
}
v___jp_341_:
{
if (lean_obj_tag(v___y_342_) == 0)
{
lean_dec_ref(v___y_342_);
goto v___jp_302_;
}
else
{
lean_dec_ref(v_a_238_);
lean_dec(v_rev_x3f_237_);
lean_dec_ref(v_repo_235_);
lean_dec_ref(v_name_234_);
return v___y_342_;
}
}
v___jp_343_:
{
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = lean_box(0);
v___x_345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
return v___x_345_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___boxed(lean_object* v_name_379_, lean_object* v_repo_380_, lean_object* v_url_381_, lean_object* v_rev_x3f_382_, lean_object* v_a_383_, lean_object* v_a_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg(v_name_379_, v_repo_380_, v_url_381_, v_rev_x3f_382_, v_a_383_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(lean_object* v_a_386_, lean_object* v_name_387_, lean_object* v_repo_388_, lean_object* v_url_389_, lean_object* v_rev_x3f_390_){
_start:
{
lean_object* v_a_396_; lean_object* v___y_494_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; uint8_t v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_498_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___closed__0));
lean_inc_ref(v_name_387_);
v___x_499_ = lean_string_append(v_name_387_, v___x_498_);
v___x_500_ = lean_string_append(v___x_499_, v_url_389_);
v___x_501_ = 1;
v___x_502_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_502_, 0, v___x_500_);
lean_ctor_set_uint8(v___x_502_, sizeof(void*)*1, v___x_501_);
lean_inc_ref(v_a_386_);
v___x_503_ = lean_apply_2(v_a_386_, v___x_502_, lean_box(0));
v___x_504_ = lean_unsigned_to_nat(0u);
v___x_505_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
lean_inc_ref(v_repo_388_);
v___x_506_ = l_Lake_GitRepo_clone(v_url_389_, v_repo_388_, v___x_505_);
if (lean_obj_tag(v___x_506_) == 0)
{
lean_object* v_a_507_; lean_object* v___x_508_; uint8_t v___x_509_; 
v_a_507_ = lean_ctor_get(v___x_506_, 1);
lean_inc(v_a_507_);
lean_dec_ref(v___x_506_);
v___x_508_ = lean_array_get_size(v_a_507_);
v___x_509_ = lean_nat_dec_lt(v___x_504_, v___x_508_);
if (v___x_509_ == 0)
{
lean_dec(v_a_507_);
goto v___jp_454_;
}
else
{
lean_object* v___x_510_; uint8_t v___x_511_; 
v___x_510_ = lean_box(0);
v___x_511_ = lean_nat_dec_le(v___x_508_, v___x_508_);
if (v___x_511_ == 0)
{
if (v___x_509_ == 0)
{
lean_dec(v_a_507_);
goto v___jp_454_;
}
else
{
size_t v___x_512_; size_t v___x_513_; lean_object* v___x_514_; 
v___x_512_ = ((size_t)0ULL);
v___x_513_ = lean_usize_of_nat(v___x_508_);
lean_inc_ref(v_a_386_);
v___x_514_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_507_, v___x_512_, v___x_513_, v___x_510_, v_a_386_);
lean_dec(v_a_507_);
if (lean_obj_tag(v___x_514_) == 0)
{
lean_dec_ref(v___x_514_);
goto v___jp_454_;
}
else
{
v___y_494_ = v___x_514_;
goto v___jp_493_;
}
}
}
else
{
size_t v___x_515_; size_t v___x_516_; lean_object* v___x_517_; 
v___x_515_ = ((size_t)0ULL);
v___x_516_ = lean_usize_of_nat(v___x_508_);
lean_inc_ref(v_a_386_);
v___x_517_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_507_, v___x_515_, v___x_516_, v___x_510_, v_a_386_);
lean_dec(v_a_507_);
if (lean_obj_tag(v___x_517_) == 0)
{
lean_dec_ref(v___x_517_);
goto v___jp_454_;
}
else
{
v___y_494_ = v___x_517_;
goto v___jp_493_;
}
}
}
}
else
{
lean_object* v_a_518_; lean_object* v___x_519_; uint8_t v___x_520_; 
v_a_518_ = lean_ctor_get(v___x_506_, 1);
lean_inc(v_a_518_);
lean_dec_ref(v___x_506_);
v___x_519_ = lean_array_get_size(v_a_518_);
v___x_520_ = lean_nat_dec_lt(v___x_504_, v___x_519_);
if (v___x_520_ == 0)
{
lean_object* v___x_521_; lean_object* v___x_522_; 
lean_dec(v_a_518_);
lean_dec(v_rev_x3f_390_);
lean_dec_ref(v_repo_388_);
lean_dec_ref(v_name_387_);
lean_dec_ref(v_a_386_);
v___x_521_ = lean_box(0);
v___x_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_522_, 0, v___x_521_);
return v___x_522_;
}
else
{
lean_object* v___x_523_; uint8_t v___x_524_; 
v___x_523_ = lean_box(0);
v___x_524_ = lean_nat_dec_le(v___x_519_, v___x_519_);
if (v___x_524_ == 0)
{
if (v___x_520_ == 0)
{
lean_dec(v_a_518_);
lean_dec(v_rev_x3f_390_);
lean_dec_ref(v_repo_388_);
lean_dec_ref(v_name_387_);
lean_dec_ref(v_a_386_);
goto v___jp_495_;
}
else
{
size_t v___x_525_; size_t v___x_526_; lean_object* v___x_527_; 
v___x_525_ = ((size_t)0ULL);
v___x_526_ = lean_usize_of_nat(v___x_519_);
lean_inc_ref(v_a_386_);
v___x_527_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_518_, v___x_525_, v___x_526_, v___x_523_, v_a_386_);
lean_dec(v_a_518_);
if (lean_obj_tag(v___x_527_) == 0)
{
lean_dec_ref(v___x_527_);
lean_dec(v_rev_x3f_390_);
lean_dec_ref(v_repo_388_);
lean_dec_ref(v_name_387_);
lean_dec_ref(v_a_386_);
goto v___jp_495_;
}
else
{
v___y_494_ = v___x_527_;
goto v___jp_493_;
}
}
}
else
{
size_t v___x_528_; size_t v___x_529_; lean_object* v___x_530_; 
v___x_528_ = ((size_t)0ULL);
v___x_529_ = lean_usize_of_nat(v___x_519_);
lean_inc_ref(v_a_386_);
v___x_530_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_518_, v___x_528_, v___x_529_, v___x_523_, v_a_386_);
lean_dec(v_a_518_);
if (lean_obj_tag(v___x_530_) == 0)
{
lean_dec_ref(v___x_530_);
lean_dec(v_rev_x3f_390_);
lean_dec_ref(v_repo_388_);
lean_dec_ref(v_name_387_);
lean_dec_ref(v_a_386_);
goto v___jp_495_;
}
else
{
v___y_494_ = v___x_530_;
goto v___jp_493_;
}
}
}
}
v___jp_392_:
{
lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_393_ = lean_box(0);
v___x_394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_394_, 0, v___x_393_);
return v___x_394_;
}
v___jp_395_:
{
lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; uint8_t v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_397_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_398_ = lean_string_append(v_name_387_, v___x_397_);
v___x_399_ = lean_string_append(v___x_398_, v_a_396_);
v___x_400_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3));
v___x_401_ = lean_string_append(v___x_399_, v___x_400_);
v___x_402_ = 1;
v___x_403_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_403_, 0, v___x_401_);
lean_ctor_set_uint8(v___x_403_, sizeof(void*)*1, v___x_402_);
lean_inc_ref(v_a_386_);
v___x_404_ = lean_apply_2(v_a_386_, v___x_403_, lean_box(0));
v___x_405_ = lean_unsigned_to_nat(0u);
v___x_406_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
v___x_407_ = l_Lake_GitRepo_checkoutDetach(v_a_396_, v_repo_388_, v___x_406_);
if (lean_obj_tag(v___x_407_) == 0)
{
lean_object* v_a_408_; lean_object* v_a_409_; lean_object* v___x_410_; uint8_t v___x_411_; 
v_a_408_ = lean_ctor_get(v___x_407_, 0);
lean_inc(v_a_408_);
v_a_409_ = lean_ctor_get(v___x_407_, 1);
lean_inc(v_a_409_);
lean_dec_ref(v___x_407_);
v___x_410_ = lean_array_get_size(v_a_409_);
v___x_411_ = lean_nat_dec_lt(v___x_405_, v___x_410_);
if (v___x_411_ == 0)
{
lean_object* v___x_412_; 
lean_dec(v_a_409_);
lean_dec_ref(v_a_386_);
v___x_412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_412_, 0, v_a_408_);
return v___x_412_;
}
else
{
lean_object* v___x_413_; uint8_t v___x_414_; 
v___x_413_ = lean_box(0);
v___x_414_ = lean_nat_dec_le(v___x_410_, v___x_410_);
if (v___x_414_ == 0)
{
if (v___x_411_ == 0)
{
lean_object* v___x_415_; 
lean_dec(v_a_409_);
lean_dec_ref(v_a_386_);
v___x_415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_415_, 0, v_a_408_);
return v___x_415_;
}
else
{
size_t v___x_416_; size_t v___x_417_; lean_object* v___x_418_; 
v___x_416_ = ((size_t)0ULL);
v___x_417_ = lean_usize_of_nat(v___x_410_);
v___x_418_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_409_, v___x_416_, v___x_417_, v___x_413_, v_a_386_);
lean_dec(v_a_409_);
if (lean_obj_tag(v___x_418_) == 0)
{
lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_425_; 
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_425_ == 0)
{
lean_object* v_unused_426_; 
v_unused_426_ = lean_ctor_get(v___x_418_, 0);
lean_dec(v_unused_426_);
v___x_420_ = v___x_418_;
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
else
{
lean_dec(v___x_418_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_423_; 
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 0, v_a_408_);
v___x_423_ = v___x_420_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_a_408_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
else
{
lean_dec(v_a_408_);
return v___x_418_;
}
}
}
else
{
size_t v___x_427_; size_t v___x_428_; lean_object* v___x_429_; 
v___x_427_ = ((size_t)0ULL);
v___x_428_ = lean_usize_of_nat(v___x_410_);
v___x_429_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_409_, v___x_427_, v___x_428_, v___x_413_, v_a_386_);
lean_dec(v_a_409_);
if (lean_obj_tag(v___x_429_) == 0)
{
lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_436_; 
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_436_ == 0)
{
lean_object* v_unused_437_; 
v_unused_437_ = lean_ctor_get(v___x_429_, 0);
lean_dec(v_unused_437_);
v___x_431_ = v___x_429_;
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
else
{
lean_dec(v___x_429_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_434_; 
if (v_isShared_432_ == 0)
{
lean_ctor_set(v___x_431_, 0, v_a_408_);
v___x_434_ = v___x_431_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_a_408_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
else
{
lean_dec(v_a_408_);
return v___x_429_;
}
}
}
}
else
{
lean_object* v_a_438_; lean_object* v___x_439_; uint8_t v___x_440_; 
v_a_438_ = lean_ctor_get(v___x_407_, 1);
lean_inc(v_a_438_);
lean_dec_ref(v___x_407_);
v___x_439_ = lean_array_get_size(v_a_438_);
v___x_440_ = lean_nat_dec_lt(v___x_405_, v___x_439_);
if (v___x_440_ == 0)
{
lean_object* v___x_441_; lean_object* v___x_442_; 
lean_dec(v_a_438_);
lean_dec_ref(v_a_386_);
v___x_441_ = lean_box(0);
v___x_442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_442_, 0, v___x_441_);
return v___x_442_;
}
else
{
lean_object* v___x_443_; uint8_t v___x_444_; 
v___x_443_ = lean_box(0);
v___x_444_ = lean_nat_dec_le(v___x_439_, v___x_439_);
if (v___x_444_ == 0)
{
if (v___x_440_ == 0)
{
lean_dec(v_a_438_);
lean_dec_ref(v_a_386_);
goto v___jp_392_;
}
else
{
size_t v___x_445_; size_t v___x_446_; lean_object* v___x_447_; 
v___x_445_ = ((size_t)0ULL);
v___x_446_ = lean_usize_of_nat(v___x_439_);
v___x_447_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_438_, v___x_445_, v___x_446_, v___x_443_, v_a_386_);
lean_dec(v_a_438_);
if (lean_obj_tag(v___x_447_) == 0)
{
lean_dec_ref(v___x_447_);
goto v___jp_392_;
}
else
{
return v___x_447_;
}
}
}
else
{
size_t v___x_448_; size_t v___x_449_; lean_object* v___x_450_; 
v___x_448_ = ((size_t)0ULL);
v___x_449_ = lean_usize_of_nat(v___x_439_);
v___x_450_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_438_, v___x_448_, v___x_449_, v___x_443_, v_a_386_);
lean_dec(v_a_438_);
if (lean_obj_tag(v___x_450_) == 0)
{
lean_dec_ref(v___x_450_);
goto v___jp_392_;
}
else
{
return v___x_450_;
}
}
}
}
}
v___jp_451_:
{
lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_452_ = lean_box(0);
v___x_453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_453_, 0, v___x_452_);
return v___x_453_;
}
v___jp_454_:
{
if (lean_obj_tag(v_rev_x3f_390_) == 1)
{
lean_object* v_val_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_490_; 
v_val_455_ = lean_ctor_get(v_rev_x3f_390_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v_rev_x3f_390_);
if (v_isSharedCheck_490_ == 0)
{
v___x_457_ = v_rev_x3f_390_;
v_isShared_458_ = v_isSharedCheck_490_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_val_455_);
lean_dec(v_rev_x3f_390_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_490_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_459_ = l_Lake_Git_defaultRemote;
v___x_460_ = lean_unsigned_to_nat(0u);
v___x_461_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
lean_inc_ref(v_repo_388_);
v___x_462_ = l_Lake_GitRepo_resolveRemoteRevision(v_val_455_, v___x_459_, v_repo_388_, v___x_461_);
if (lean_obj_tag(v___x_462_) == 0)
{
lean_object* v_a_463_; lean_object* v_a_464_; lean_object* v___x_465_; uint8_t v___x_466_; 
lean_del_object(v___x_457_);
v_a_463_ = lean_ctor_get(v___x_462_, 0);
lean_inc(v_a_463_);
v_a_464_ = lean_ctor_get(v___x_462_, 1);
lean_inc(v_a_464_);
lean_dec_ref(v___x_462_);
v___x_465_ = lean_array_get_size(v_a_464_);
v___x_466_ = lean_nat_dec_lt(v___x_460_, v___x_465_);
if (v___x_466_ == 0)
{
lean_dec(v_a_464_);
v_a_396_ = v_a_463_;
goto v___jp_395_;
}
else
{
lean_object* v___x_467_; uint8_t v___x_468_; 
v___x_467_ = lean_box(0);
v___x_468_ = lean_nat_dec_le(v___x_465_, v___x_465_);
if (v___x_468_ == 0)
{
if (v___x_466_ == 0)
{
lean_dec(v_a_464_);
v_a_396_ = v_a_463_;
goto v___jp_395_;
}
else
{
size_t v___x_469_; size_t v___x_470_; lean_object* v___x_471_; 
v___x_469_ = ((size_t)0ULL);
v___x_470_ = lean_usize_of_nat(v___x_465_);
lean_inc_ref(v_a_386_);
v___x_471_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_464_, v___x_469_, v___x_470_, v___x_467_, v_a_386_);
lean_dec(v_a_464_);
if (lean_obj_tag(v___x_471_) == 0)
{
lean_dec_ref(v___x_471_);
v_a_396_ = v_a_463_;
goto v___jp_395_;
}
else
{
lean_dec(v_a_463_);
lean_dec_ref(v_repo_388_);
lean_dec_ref(v_name_387_);
lean_dec_ref(v_a_386_);
return v___x_471_;
}
}
}
else
{
size_t v___x_472_; size_t v___x_473_; lean_object* v___x_474_; 
v___x_472_ = ((size_t)0ULL);
v___x_473_ = lean_usize_of_nat(v___x_465_);
lean_inc_ref(v_a_386_);
v___x_474_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_464_, v___x_472_, v___x_473_, v___x_467_, v_a_386_);
lean_dec(v_a_464_);
if (lean_obj_tag(v___x_474_) == 0)
{
lean_dec_ref(v___x_474_);
v_a_396_ = v_a_463_;
goto v___jp_395_;
}
else
{
lean_dec(v_a_463_);
lean_dec_ref(v_repo_388_);
lean_dec_ref(v_name_387_);
lean_dec_ref(v_a_386_);
return v___x_474_;
}
}
}
}
else
{
lean_object* v_a_475_; lean_object* v___x_476_; uint8_t v___x_477_; 
lean_dec_ref(v_repo_388_);
lean_dec_ref(v_name_387_);
v_a_475_ = lean_ctor_get(v___x_462_, 1);
lean_inc(v_a_475_);
lean_dec_ref(v___x_462_);
v___x_476_ = lean_array_get_size(v_a_475_);
v___x_477_ = lean_nat_dec_lt(v___x_460_, v___x_476_);
if (v___x_477_ == 0)
{
lean_object* v___x_478_; lean_object* v___x_480_; 
lean_dec(v_a_475_);
lean_dec_ref(v_a_386_);
v___x_478_ = lean_box(0);
if (v_isShared_458_ == 0)
{
lean_ctor_set(v___x_457_, 0, v___x_478_);
v___x_480_ = v___x_457_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v___x_478_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
else
{
lean_object* v___x_482_; uint8_t v___x_483_; 
lean_del_object(v___x_457_);
v___x_482_ = lean_box(0);
v___x_483_ = lean_nat_dec_le(v___x_476_, v___x_476_);
if (v___x_483_ == 0)
{
if (v___x_477_ == 0)
{
lean_dec(v_a_475_);
lean_dec_ref(v_a_386_);
goto v___jp_451_;
}
else
{
size_t v___x_484_; size_t v___x_485_; lean_object* v___x_486_; 
v___x_484_ = ((size_t)0ULL);
v___x_485_ = lean_usize_of_nat(v___x_476_);
v___x_486_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_475_, v___x_484_, v___x_485_, v___x_482_, v_a_386_);
lean_dec(v_a_475_);
if (lean_obj_tag(v___x_486_) == 0)
{
lean_dec_ref(v___x_486_);
goto v___jp_451_;
}
else
{
return v___x_486_;
}
}
}
else
{
size_t v___x_487_; size_t v___x_488_; lean_object* v___x_489_; 
v___x_487_ = ((size_t)0ULL);
v___x_488_ = lean_usize_of_nat(v___x_476_);
v___x_489_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_475_, v___x_487_, v___x_488_, v___x_482_, v_a_386_);
lean_dec(v_a_475_);
if (lean_obj_tag(v___x_489_) == 0)
{
lean_dec_ref(v___x_489_);
goto v___jp_451_;
}
else
{
return v___x_489_;
}
}
}
}
}
}
else
{
lean_object* v___x_491_; lean_object* v___x_492_; 
lean_dec(v_rev_x3f_390_);
lean_dec_ref(v_repo_388_);
lean_dec_ref(v_name_387_);
lean_dec_ref(v_a_386_);
v___x_491_ = lean_box(0);
v___x_492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_492_, 0, v___x_491_);
return v___x_492_;
}
}
v___jp_493_:
{
if (lean_obj_tag(v___y_494_) == 0)
{
lean_dec_ref(v___y_494_);
goto v___jp_454_;
}
else
{
lean_dec(v_rev_x3f_390_);
lean_dec_ref(v_repo_388_);
lean_dec_ref(v_name_387_);
lean_dec_ref(v_a_386_);
return v___y_494_;
}
}
v___jp_495_:
{
lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_496_ = lean_box(0);
v___x_497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_497_, 0, v___x_496_);
return v___x_497_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0___boxed(lean_object* v_a_531_, lean_object* v_name_532_, lean_object* v_repo_533_, lean_object* v_url_534_, lean_object* v_rev_x3f_535_, lean_object* v_a_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(v_a_531_, v_name_532_, v_repo_533_, v_url_534_, v_rev_x3f_535_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(lean_object* v_a_538_, lean_object* v_name_539_, lean_object* v_repo_540_, lean_object* v_rev_x3f_541_){
_start:
{
uint8_t v_a_544_; lean_object* v___y_557_; lean_object* v___y_558_; uint8_t v_val_559_; lean_object* v___y_574_; lean_object* v_a_575_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_641_ = l_Lake_Git_defaultRemote;
v___x_642_ = lean_unsigned_to_nat(0u);
v___x_643_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
lean_inc_ref(v_repo_540_);
v___x_644_ = l_Lake_GitRepo_findRemoteRevision(v_repo_540_, v_rev_x3f_541_, v___x_641_, v___x_643_);
if (lean_obj_tag(v___x_644_) == 0)
{
lean_object* v_a_645_; lean_object* v_a_646_; lean_object* v___x_674_; uint8_t v___x_675_; 
v_a_645_ = lean_ctor_get(v___x_644_, 0);
lean_inc(v_a_645_);
v_a_646_ = lean_ctor_get(v___x_644_, 1);
lean_inc(v_a_646_);
lean_dec_ref(v___x_644_);
v___x_674_ = lean_array_get_size(v_a_646_);
v___x_675_ = lean_nat_dec_lt(v___x_642_, v___x_674_);
if (v___x_675_ == 0)
{
lean_dec(v_a_646_);
goto v___jp_647_;
}
else
{
lean_object* v___x_676_; uint8_t v___x_677_; 
v___x_676_ = lean_box(0);
v___x_677_ = lean_nat_dec_le(v___x_674_, v___x_674_);
if (v___x_677_ == 0)
{
if (v___x_675_ == 0)
{
lean_dec(v_a_646_);
goto v___jp_647_;
}
else
{
size_t v___x_678_; size_t v___x_679_; lean_object* v___x_680_; 
v___x_678_ = ((size_t)0ULL);
v___x_679_ = lean_usize_of_nat(v___x_674_);
lean_inc_ref(v_a_538_);
v___x_680_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_646_, v___x_678_, v___x_679_, v___x_676_, v_a_538_);
lean_dec(v_a_646_);
if (lean_obj_tag(v___x_680_) == 0)
{
lean_dec_ref(v___x_680_);
goto v___jp_647_;
}
else
{
lean_dec(v_a_645_);
lean_dec_ref(v_repo_540_);
lean_dec_ref(v_name_539_);
lean_dec_ref(v_a_538_);
return v___x_680_;
}
}
}
else
{
size_t v___x_681_; size_t v___x_682_; lean_object* v___x_683_; 
v___x_681_ = ((size_t)0ULL);
v___x_682_ = lean_usize_of_nat(v___x_674_);
lean_inc_ref(v_a_538_);
v___x_683_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_646_, v___x_681_, v___x_682_, v___x_676_, v_a_538_);
lean_dec(v_a_646_);
if (lean_obj_tag(v___x_683_) == 0)
{
lean_dec_ref(v___x_683_);
goto v___jp_647_;
}
else
{
lean_dec(v_a_645_);
lean_dec_ref(v_repo_540_);
lean_dec_ref(v_name_539_);
lean_dec_ref(v_a_538_);
return v___x_683_;
}
}
}
v___jp_647_:
{
lean_object* v___x_648_; 
lean_inc_ref(v_repo_540_);
v___x_648_ = l_Lake_GitRepo_getHeadRevision(v_repo_540_, v___x_643_);
if (lean_obj_tag(v___x_648_) == 0)
{
lean_object* v_a_649_; lean_object* v_a_650_; lean_object* v___x_651_; uint8_t v___x_652_; 
v_a_649_ = lean_ctor_get(v___x_648_, 0);
lean_inc(v_a_649_);
v_a_650_ = lean_ctor_get(v___x_648_, 1);
lean_inc(v_a_650_);
lean_dec_ref(v___x_648_);
v___x_651_ = lean_array_get_size(v_a_650_);
v___x_652_ = lean_nat_dec_lt(v___x_642_, v___x_651_);
if (v___x_652_ == 0)
{
lean_dec(v_a_650_);
v___y_574_ = v_a_645_;
v_a_575_ = v_a_649_;
goto v___jp_573_;
}
else
{
lean_object* v___x_653_; uint8_t v___x_654_; 
v___x_653_ = lean_box(0);
v___x_654_ = lean_nat_dec_le(v___x_651_, v___x_651_);
if (v___x_654_ == 0)
{
if (v___x_652_ == 0)
{
lean_dec(v_a_650_);
v___y_574_ = v_a_645_;
v_a_575_ = v_a_649_;
goto v___jp_573_;
}
else
{
size_t v___x_655_; size_t v___x_656_; lean_object* v___x_657_; 
v___x_655_ = ((size_t)0ULL);
v___x_656_ = lean_usize_of_nat(v___x_651_);
lean_inc_ref(v_a_538_);
v___x_657_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_650_, v___x_655_, v___x_656_, v___x_653_, v_a_538_);
lean_dec(v_a_650_);
if (lean_obj_tag(v___x_657_) == 0)
{
lean_dec_ref(v___x_657_);
v___y_574_ = v_a_645_;
v_a_575_ = v_a_649_;
goto v___jp_573_;
}
else
{
lean_dec(v_a_649_);
lean_dec(v_a_645_);
lean_dec_ref(v_repo_540_);
lean_dec_ref(v_name_539_);
lean_dec_ref(v_a_538_);
return v___x_657_;
}
}
}
else
{
size_t v___x_658_; size_t v___x_659_; lean_object* v___x_660_; 
v___x_658_ = ((size_t)0ULL);
v___x_659_ = lean_usize_of_nat(v___x_651_);
lean_inc_ref(v_a_538_);
v___x_660_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_650_, v___x_658_, v___x_659_, v___x_653_, v_a_538_);
lean_dec(v_a_650_);
if (lean_obj_tag(v___x_660_) == 0)
{
lean_dec_ref(v___x_660_);
v___y_574_ = v_a_645_;
v_a_575_ = v_a_649_;
goto v___jp_573_;
}
else
{
lean_dec(v_a_649_);
lean_dec(v_a_645_);
lean_dec_ref(v_repo_540_);
lean_dec_ref(v_name_539_);
lean_dec_ref(v_a_538_);
return v___x_660_;
}
}
}
}
else
{
lean_object* v_a_661_; lean_object* v___x_662_; uint8_t v___x_663_; 
lean_dec(v_a_645_);
lean_dec_ref(v_repo_540_);
lean_dec_ref(v_name_539_);
v_a_661_ = lean_ctor_get(v___x_648_, 1);
lean_inc(v_a_661_);
lean_dec_ref(v___x_648_);
v___x_662_ = lean_array_get_size(v_a_661_);
v___x_663_ = lean_nat_dec_lt(v___x_642_, v___x_662_);
if (v___x_663_ == 0)
{
lean_object* v___x_664_; lean_object* v___x_665_; 
lean_dec(v_a_661_);
lean_dec_ref(v_a_538_);
v___x_664_ = lean_box(0);
v___x_665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_665_, 0, v___x_664_);
return v___x_665_;
}
else
{
lean_object* v___x_666_; uint8_t v___x_667_; 
v___x_666_ = lean_box(0);
v___x_667_ = lean_nat_dec_le(v___x_662_, v___x_662_);
if (v___x_667_ == 0)
{
if (v___x_663_ == 0)
{
lean_dec(v_a_661_);
lean_dec_ref(v_a_538_);
goto v___jp_635_;
}
else
{
size_t v___x_668_; size_t v___x_669_; lean_object* v___x_670_; 
v___x_668_ = ((size_t)0ULL);
v___x_669_ = lean_usize_of_nat(v___x_662_);
v___x_670_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_661_, v___x_668_, v___x_669_, v___x_666_, v_a_538_);
lean_dec(v_a_661_);
if (lean_obj_tag(v___x_670_) == 0)
{
lean_dec_ref(v___x_670_);
goto v___jp_635_;
}
else
{
return v___x_670_;
}
}
}
else
{
size_t v___x_671_; size_t v___x_672_; lean_object* v___x_673_; 
v___x_671_ = ((size_t)0ULL);
v___x_672_ = lean_usize_of_nat(v___x_662_);
v___x_673_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_661_, v___x_671_, v___x_672_, v___x_666_, v_a_538_);
lean_dec(v_a_661_);
if (lean_obj_tag(v___x_673_) == 0)
{
lean_dec_ref(v___x_673_);
goto v___jp_635_;
}
else
{
return v___x_673_;
}
}
}
}
}
}
else
{
lean_object* v_a_684_; lean_object* v___x_685_; uint8_t v___x_686_; 
lean_dec_ref(v_repo_540_);
lean_dec_ref(v_name_539_);
v_a_684_ = lean_ctor_get(v___x_644_, 1);
lean_inc(v_a_684_);
lean_dec_ref(v___x_644_);
v___x_685_ = lean_array_get_size(v_a_684_);
v___x_686_ = lean_nat_dec_lt(v___x_642_, v___x_685_);
if (v___x_686_ == 0)
{
lean_object* v___x_687_; lean_object* v___x_688_; 
lean_dec(v_a_684_);
lean_dec_ref(v_a_538_);
v___x_687_ = lean_box(0);
v___x_688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_688_, 0, v___x_687_);
return v___x_688_;
}
else
{
lean_object* v___x_689_; uint8_t v___x_690_; 
v___x_689_ = lean_box(0);
v___x_690_ = lean_nat_dec_le(v___x_685_, v___x_685_);
if (v___x_690_ == 0)
{
if (v___x_686_ == 0)
{
lean_dec(v_a_684_);
lean_dec_ref(v_a_538_);
goto v___jp_638_;
}
else
{
size_t v___x_691_; size_t v___x_692_; lean_object* v___x_693_; 
v___x_691_ = ((size_t)0ULL);
v___x_692_ = lean_usize_of_nat(v___x_685_);
v___x_693_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_684_, v___x_691_, v___x_692_, v___x_689_, v_a_538_);
lean_dec(v_a_684_);
if (lean_obj_tag(v___x_693_) == 0)
{
lean_dec_ref(v___x_693_);
goto v___jp_638_;
}
else
{
return v___x_693_;
}
}
}
else
{
size_t v___x_694_; size_t v___x_695_; lean_object* v___x_696_; 
v___x_694_ = ((size_t)0ULL);
v___x_695_ = lean_usize_of_nat(v___x_685_);
v___x_696_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_684_, v___x_694_, v___x_695_, v___x_689_, v_a_538_);
lean_dec(v_a_684_);
if (lean_obj_tag(v___x_696_) == 0)
{
lean_dec_ref(v___x_696_);
goto v___jp_638_;
}
else
{
return v___x_696_;
}
}
}
}
v___jp_543_:
{
if (v_a_544_ == 0)
{
lean_object* v___x_545_; lean_object* v___x_546_; 
lean_dec_ref(v_repo_540_);
lean_dec_ref(v_name_539_);
lean_dec_ref(v_a_538_);
v___x_545_ = lean_box(0);
v___x_546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_546_, 0, v___x_545_);
return v___x_546_;
}
else
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; uint8_t v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_547_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0));
v___x_548_ = lean_string_append(v_name_539_, v___x_547_);
v___x_549_ = lean_string_append(v___x_548_, v_repo_540_);
lean_dec_ref(v_repo_540_);
v___x_550_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1));
v___x_551_ = lean_string_append(v___x_549_, v___x_550_);
v___x_552_ = 2;
v___x_553_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_553_, 0, v___x_551_);
lean_ctor_set_uint8(v___x_553_, sizeof(void*)*1, v___x_552_);
v___x_554_ = lean_apply_2(v_a_538_, v___x_553_, lean_box(0));
v___x_555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_555_, 0, v___x_554_);
return v___x_555_;
}
}
v___jp_556_:
{
lean_object* v___x_560_; uint8_t v___x_561_; 
v___x_560_ = lean_array_get_size(v___y_558_);
v___x_561_ = lean_nat_dec_lt(v___y_557_, v___x_560_);
if (v___x_561_ == 0)
{
lean_dec_ref(v___y_558_);
v_a_544_ = v_val_559_;
goto v___jp_543_;
}
else
{
lean_object* v___x_562_; uint8_t v___x_563_; 
v___x_562_ = lean_box(0);
v___x_563_ = lean_nat_dec_le(v___x_560_, v___x_560_);
if (v___x_563_ == 0)
{
if (v___x_561_ == 0)
{
lean_dec_ref(v___y_558_);
v_a_544_ = v_val_559_;
goto v___jp_543_;
}
else
{
size_t v___x_564_; size_t v___x_565_; lean_object* v___x_566_; 
v___x_564_ = ((size_t)0ULL);
v___x_565_ = lean_usize_of_nat(v___x_560_);
lean_inc_ref(v_a_538_);
v___x_566_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v___y_558_, v___x_564_, v___x_565_, v___x_562_, v_a_538_);
lean_dec_ref(v___y_558_);
if (lean_obj_tag(v___x_566_) == 0)
{
lean_dec_ref(v___x_566_);
v_a_544_ = v_val_559_;
goto v___jp_543_;
}
else
{
lean_dec_ref(v_repo_540_);
lean_dec_ref(v_name_539_);
lean_dec_ref(v_a_538_);
return v___x_566_;
}
}
}
else
{
size_t v___x_567_; size_t v___x_568_; lean_object* v___x_569_; 
v___x_567_ = ((size_t)0ULL);
v___x_568_ = lean_usize_of_nat(v___x_560_);
lean_inc_ref(v_a_538_);
v___x_569_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v___y_558_, v___x_567_, v___x_568_, v___x_562_, v_a_538_);
lean_dec_ref(v___y_558_);
if (lean_obj_tag(v___x_569_) == 0)
{
lean_dec_ref(v___x_569_);
v_a_544_ = v_val_559_;
goto v___jp_543_;
}
else
{
lean_dec_ref(v_repo_540_);
lean_dec_ref(v_name_539_);
lean_dec_ref(v_a_538_);
return v___x_569_;
}
}
}
}
v___jp_570_:
{
lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_571_ = lean_box(0);
v___x_572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
return v___x_572_;
}
v___jp_573_:
{
uint8_t v___x_576_; 
v___x_576_ = lean_string_dec_eq(v_a_575_, v___y_574_);
lean_dec_ref(v_a_575_);
if (v___x_576_ == 0)
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; uint8_t v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_577_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_578_ = lean_string_append(v_name_539_, v___x_577_);
v___x_579_ = lean_string_append(v___x_578_, v___y_574_);
v___x_580_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3));
v___x_581_ = lean_string_append(v___x_579_, v___x_580_);
v___x_582_ = 1;
v___x_583_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_583_, 0, v___x_581_);
lean_ctor_set_uint8(v___x_583_, sizeof(void*)*1, v___x_582_);
lean_inc_ref(v_a_538_);
v___x_584_ = lean_apply_2(v_a_538_, v___x_583_, lean_box(0));
v___x_585_ = lean_unsigned_to_nat(0u);
v___x_586_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
v___x_587_ = l_Lake_GitRepo_checkoutDetach(v___y_574_, v_repo_540_, v___x_586_);
if (lean_obj_tag(v___x_587_) == 0)
{
lean_object* v_a_588_; lean_object* v_a_589_; lean_object* v___x_590_; uint8_t v___x_591_; 
v_a_588_ = lean_ctor_get(v___x_587_, 0);
lean_inc(v_a_588_);
v_a_589_ = lean_ctor_get(v___x_587_, 1);
lean_inc(v_a_589_);
lean_dec_ref(v___x_587_);
v___x_590_ = lean_array_get_size(v_a_589_);
v___x_591_ = lean_nat_dec_lt(v___x_585_, v___x_590_);
if (v___x_591_ == 0)
{
lean_object* v___x_592_; 
lean_dec(v_a_589_);
lean_dec_ref(v_a_538_);
v___x_592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_592_, 0, v_a_588_);
return v___x_592_;
}
else
{
lean_object* v___x_593_; uint8_t v___x_594_; 
v___x_593_ = lean_box(0);
v___x_594_ = lean_nat_dec_le(v___x_590_, v___x_590_);
if (v___x_594_ == 0)
{
if (v___x_591_ == 0)
{
lean_object* v___x_595_; 
lean_dec(v_a_589_);
lean_dec_ref(v_a_538_);
v___x_595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_595_, 0, v_a_588_);
return v___x_595_;
}
else
{
size_t v___x_596_; size_t v___x_597_; lean_object* v___x_598_; 
v___x_596_ = ((size_t)0ULL);
v___x_597_ = lean_usize_of_nat(v___x_590_);
v___x_598_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_589_, v___x_596_, v___x_597_, v___x_593_, v_a_538_);
lean_dec(v_a_589_);
if (lean_obj_tag(v___x_598_) == 0)
{
lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_605_; 
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_605_ == 0)
{
lean_object* v_unused_606_; 
v_unused_606_ = lean_ctor_get(v___x_598_, 0);
lean_dec(v_unused_606_);
v___x_600_ = v___x_598_;
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
else
{
lean_dec(v___x_598_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_603_; 
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 0, v_a_588_);
v___x_603_ = v___x_600_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_a_588_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
else
{
lean_dec(v_a_588_);
return v___x_598_;
}
}
}
else
{
size_t v___x_607_; size_t v___x_608_; lean_object* v___x_609_; 
v___x_607_ = ((size_t)0ULL);
v___x_608_ = lean_usize_of_nat(v___x_590_);
v___x_609_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_589_, v___x_607_, v___x_608_, v___x_593_, v_a_538_);
lean_dec(v_a_589_);
if (lean_obj_tag(v___x_609_) == 0)
{
lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_616_; 
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_609_);
if (v_isSharedCheck_616_ == 0)
{
lean_object* v_unused_617_; 
v_unused_617_ = lean_ctor_get(v___x_609_, 0);
lean_dec(v_unused_617_);
v___x_611_ = v___x_609_;
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
else
{
lean_dec(v___x_609_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_614_; 
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 0, v_a_588_);
v___x_614_ = v___x_611_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_a_588_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
}
else
{
lean_dec(v_a_588_);
return v___x_609_;
}
}
}
}
else
{
lean_object* v_a_618_; lean_object* v___x_619_; uint8_t v___x_620_; 
v_a_618_ = lean_ctor_get(v___x_587_, 1);
lean_inc(v_a_618_);
lean_dec_ref(v___x_587_);
v___x_619_ = lean_array_get_size(v_a_618_);
v___x_620_ = lean_nat_dec_lt(v___x_585_, v___x_619_);
if (v___x_620_ == 0)
{
lean_object* v___x_621_; lean_object* v___x_622_; 
lean_dec(v_a_618_);
lean_dec_ref(v_a_538_);
v___x_621_ = lean_box(0);
v___x_622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_622_, 0, v___x_621_);
return v___x_622_;
}
else
{
lean_object* v___x_623_; uint8_t v___x_624_; 
v___x_623_ = lean_box(0);
v___x_624_ = lean_nat_dec_le(v___x_619_, v___x_619_);
if (v___x_624_ == 0)
{
if (v___x_620_ == 0)
{
lean_dec(v_a_618_);
lean_dec_ref(v_a_538_);
goto v___jp_570_;
}
else
{
size_t v___x_625_; size_t v___x_626_; lean_object* v___x_627_; 
v___x_625_ = ((size_t)0ULL);
v___x_626_ = lean_usize_of_nat(v___x_619_);
v___x_627_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_618_, v___x_625_, v___x_626_, v___x_623_, v_a_538_);
lean_dec(v_a_618_);
if (lean_obj_tag(v___x_627_) == 0)
{
lean_dec_ref(v___x_627_);
goto v___jp_570_;
}
else
{
return v___x_627_;
}
}
}
else
{
size_t v___x_628_; size_t v___x_629_; lean_object* v___x_630_; 
v___x_628_ = ((size_t)0ULL);
v___x_629_ = lean_usize_of_nat(v___x_619_);
v___x_630_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_618_, v___x_628_, v___x_629_, v___x_623_, v_a_538_);
lean_dec(v_a_618_);
if (lean_obj_tag(v___x_630_) == 0)
{
lean_dec_ref(v___x_630_);
goto v___jp_570_;
}
else
{
return v___x_630_;
}
}
}
}
}
else
{
uint8_t v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
lean_dec_ref(v___y_574_);
lean_inc_ref(v_repo_540_);
v___x_631_ = l_Lake_GitRepo_hasNoDiff(v_repo_540_);
v___x_632_ = lean_unsigned_to_nat(0u);
v___x_633_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
if (v___x_631_ == 0)
{
v___y_557_ = v___x_632_;
v___y_558_ = v___x_633_;
v_val_559_ = v___x_576_;
goto v___jp_556_;
}
else
{
uint8_t v___x_634_; 
v___x_634_ = 0;
v___y_557_ = v___x_632_;
v___y_558_ = v___x_633_;
v_val_559_ = v___x_634_;
goto v___jp_556_;
}
}
}
v___jp_635_:
{
lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_636_ = lean_box(0);
v___x_637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_637_, 0, v___x_636_);
return v___x_637_;
}
v___jp_638_:
{
lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_639_ = lean_box(0);
v___x_640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_640_, 0, v___x_639_);
return v___x_640_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1___boxed(lean_object* v_a_697_, lean_object* v_name_698_, lean_object* v_repo_699_, lean_object* v_rev_x3f_700_, lean_object* v_a_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(v_a_697_, v_name_698_, v_repo_699_, v_rev_x3f_700_);
return v_res_702_;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4(void){
_start:
{
lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_707_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
v___x_708_ = lean_array_get_size(v___x_707_);
return v___x_708_;
}
}
static uint8_t _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5(void){
_start:
{
lean_object* v___x_709_; lean_object* v___x_710_; uint8_t v___x_711_; 
v___x_709_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4);
v___x_710_ = lean_unsigned_to_nat(0u);
v___x_711_ = lean_nat_dec_lt(v___x_710_, v___x_709_);
return v___x_711_;
}
}
static uint8_t _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6(void){
_start:
{
lean_object* v___x_712_; uint8_t v___x_713_; 
v___x_712_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4);
v___x_713_ = lean_nat_dec_le(v___x_712_, v___x_712_);
return v___x_713_;
}
}
static size_t _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7(void){
_start:
{
lean_object* v___x_714_; size_t v___x_715_; 
v___x_714_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4);
v___x_715_ = lean_usize_of_nat(v___x_714_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo(lean_object* v_name_716_, lean_object* v_repo_717_, lean_object* v_url_718_, lean_object* v_rev_x3f_719_, lean_object* v_a_720_){
_start:
{
uint8_t v_a_723_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; uint8_t v_val_762_; 
v___x_758_ = l_Lake_Git_defaultRemote;
lean_inc_ref(v_repo_717_);
v___x_759_ = l_Lake_GitRepo_getRemoteUrl_x3f(v___x_758_, v_repo_717_);
v___x_760_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
if (lean_obj_tag(v___x_759_) == 1)
{
lean_object* v_val_772_; uint8_t v___x_773_; 
v_val_772_ = lean_ctor_get(v___x_759_, 0);
lean_inc(v_val_772_);
lean_dec_ref(v___x_759_);
v___x_773_ = lean_string_dec_eq(v_val_772_, v_url_718_);
if (v___x_773_ == 0)
{
lean_object* v___x_774_; 
v___x_774_ = lean_io_realpath(v_val_772_);
if (lean_obj_tag(v___x_774_) == 0)
{
lean_object* v_a_775_; lean_object* v___x_776_; 
v_a_775_ = lean_ctor_get(v___x_774_, 0);
lean_inc(v_a_775_);
lean_dec_ref(v___x_774_);
lean_inc_ref(v_url_718_);
v___x_776_ = lean_io_realpath(v_url_718_);
if (lean_obj_tag(v___x_776_) == 0)
{
lean_object* v_a_777_; uint8_t v___x_778_; 
v_a_777_ = lean_ctor_get(v___x_776_, 0);
lean_inc(v_a_777_);
lean_dec_ref(v___x_776_);
v___x_778_ = lean_string_dec_eq(v_a_775_, v_a_777_);
lean_dec(v_a_777_);
lean_dec(v_a_775_);
v_val_762_ = v___x_778_;
goto v___jp_761_;
}
else
{
lean_dec_ref(v___x_776_);
lean_dec(v_a_775_);
v_val_762_ = v___x_773_;
goto v___jp_761_;
}
}
else
{
lean_dec_ref(v___x_774_);
v_val_762_ = v___x_773_;
goto v___jp_761_;
}
}
else
{
lean_dec(v_val_772_);
v_val_762_ = v___x_773_;
goto v___jp_761_;
}
}
else
{
uint8_t v___x_779_; 
lean_dec(v___x_759_);
v___x_779_ = 0;
v_val_762_ = v___x_779_;
goto v___jp_761_;
}
v___jp_722_:
{
if (v_a_723_ == 0)
{
uint8_t v___x_724_; 
v___x_724_ = l_System_Platform_isWindows;
if (v___x_724_ == 0)
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; uint8_t v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_725_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__0));
lean_inc_ref(v_name_716_);
v___x_726_ = lean_string_append(v_name_716_, v___x_725_);
v___x_727_ = lean_string_append(v___x_726_, v_repo_717_);
v___x_728_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__1));
v___x_729_ = lean_string_append(v___x_727_, v___x_728_);
v___x_730_ = 1;
v___x_731_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_731_, 0, v___x_729_);
lean_ctor_set_uint8(v___x_731_, sizeof(void*)*1, v___x_730_);
lean_inc_ref(v_a_720_);
v___x_732_ = lean_apply_2(v_a_720_, v___x_731_, lean_box(0));
v___x_733_ = l_IO_FS_removeDirAll(v_repo_717_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v___x_734_; 
lean_dec_ref(v___x_733_);
v___x_734_ = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(v_a_720_, v_name_716_, v_repo_717_, v_url_718_, v_rev_x3f_719_);
return v___x_734_;
}
else
{
lean_object* v_a_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_747_; 
lean_dec(v_rev_x3f_719_);
lean_dec_ref(v_url_718_);
lean_dec_ref(v_repo_717_);
lean_dec_ref(v_name_716_);
v_a_735_ = lean_ctor_get(v___x_733_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_747_ == 0)
{
v___x_737_ = v___x_733_;
v_isShared_738_ = v_isSharedCheck_747_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_a_735_);
lean_dec(v___x_733_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_747_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_739_; uint8_t v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_745_; 
v___x_739_ = lean_io_error_to_string(v_a_735_);
v___x_740_ = 3;
v___x_741_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_741_, 0, v___x_739_);
lean_ctor_set_uint8(v___x_741_, sizeof(void*)*1, v___x_740_);
v___x_742_ = lean_apply_2(v_a_720_, v___x_741_, lean_box(0));
v___x_743_ = lean_box(0);
if (v_isShared_738_ == 0)
{
lean_ctor_set(v___x_737_, 0, v___x_743_);
v___x_745_ = v___x_737_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v___x_743_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
}
else
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; uint8_t v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
lean_dec_ref(v_url_718_);
v___x_748_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__2));
lean_inc_ref(v_name_716_);
v___x_749_ = lean_string_append(v_name_716_, v___x_748_);
v___x_750_ = lean_string_append(v___x_749_, v_repo_717_);
v___x_751_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__3));
v___x_752_ = lean_string_append(v___x_750_, v___x_751_);
v___x_753_ = 1;
v___x_754_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_754_, 0, v___x_752_);
lean_ctor_set_uint8(v___x_754_, sizeof(void*)*1, v___x_753_);
lean_inc_ref(v_a_720_);
v___x_755_ = lean_apply_2(v_a_720_, v___x_754_, lean_box(0));
v___x_756_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(v_a_720_, v_name_716_, v_repo_717_, v_rev_x3f_719_);
return v___x_756_;
}
}
else
{
lean_object* v___x_757_; 
lean_dec_ref(v_url_718_);
v___x_757_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(v_a_720_, v_name_716_, v_repo_717_, v_rev_x3f_719_);
return v___x_757_;
}
}
v___jp_761_:
{
uint8_t v___x_763_; 
v___x_763_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_763_ == 0)
{
v_a_723_ = v_val_762_;
goto v___jp_722_;
}
else
{
lean_object* v___x_764_; uint8_t v___x_765_; 
v___x_764_ = lean_box(0);
v___x_765_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_765_ == 0)
{
if (v___x_763_ == 0)
{
v_a_723_ = v_val_762_;
goto v___jp_722_;
}
else
{
size_t v___x_766_; size_t v___x_767_; lean_object* v___x_768_; 
v___x_766_ = ((size_t)0ULL);
v___x_767_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
lean_inc_ref(v_a_720_);
v___x_768_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v___x_760_, v___x_766_, v___x_767_, v___x_764_, v_a_720_);
if (lean_obj_tag(v___x_768_) == 0)
{
lean_dec_ref(v___x_768_);
v_a_723_ = v_val_762_;
goto v___jp_722_;
}
else
{
lean_dec_ref(v_a_720_);
lean_dec(v_rev_x3f_719_);
lean_dec_ref(v_url_718_);
lean_dec_ref(v_repo_717_);
lean_dec_ref(v_name_716_);
return v___x_768_;
}
}
}
else
{
size_t v___x_769_; size_t v___x_770_; lean_object* v___x_771_; 
v___x_769_ = ((size_t)0ULL);
v___x_770_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
lean_inc_ref(v_a_720_);
v___x_771_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v___x_760_, v___x_769_, v___x_770_, v___x_764_, v_a_720_);
if (lean_obj_tag(v___x_771_) == 0)
{
lean_dec_ref(v___x_771_);
v_a_723_ = v_val_762_;
goto v___jp_722_;
}
else
{
lean_dec_ref(v_a_720_);
lean_dec(v_rev_x3f_719_);
lean_dec_ref(v_url_718_);
lean_dec_ref(v_repo_717_);
lean_dec_ref(v_name_716_);
return v___x_771_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___boxed(lean_object* v_name_780_, lean_object* v_repo_781_, lean_object* v_url_782_, lean_object* v_rev_x3f_783_, lean_object* v_a_784_, lean_object* v_a_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo(v_name_780_, v_repo_781_, v_url_782_, v_rev_x3f_783_, v_a_784_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(lean_object* v_a_787_, lean_object* v_name_788_, lean_object* v_repo_789_, lean_object* v_url_790_, lean_object* v_rev_x3f_791_){
_start:
{
uint8_t v_a_794_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; uint8_t v_val_833_; 
v___x_829_ = l_Lake_Git_defaultRemote;
lean_inc_ref(v_repo_789_);
v___x_830_ = l_Lake_GitRepo_getRemoteUrl_x3f(v___x_829_, v_repo_789_);
v___x_831_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
if (lean_obj_tag(v___x_830_) == 1)
{
lean_object* v_val_843_; uint8_t v___x_844_; 
v_val_843_ = lean_ctor_get(v___x_830_, 0);
lean_inc(v_val_843_);
lean_dec_ref(v___x_830_);
v___x_844_ = lean_string_dec_eq(v_val_843_, v_url_790_);
if (v___x_844_ == 0)
{
lean_object* v___x_845_; 
v___x_845_ = lean_io_realpath(v_val_843_);
if (lean_obj_tag(v___x_845_) == 0)
{
lean_object* v_a_846_; lean_object* v___x_847_; 
v_a_846_ = lean_ctor_get(v___x_845_, 0);
lean_inc(v_a_846_);
lean_dec_ref(v___x_845_);
lean_inc_ref(v_url_790_);
v___x_847_ = lean_io_realpath(v_url_790_);
if (lean_obj_tag(v___x_847_) == 0)
{
lean_object* v_a_848_; uint8_t v___x_849_; 
v_a_848_ = lean_ctor_get(v___x_847_, 0);
lean_inc(v_a_848_);
lean_dec_ref(v___x_847_);
v___x_849_ = lean_string_dec_eq(v_a_846_, v_a_848_);
lean_dec(v_a_848_);
lean_dec(v_a_846_);
v_val_833_ = v___x_849_;
goto v___jp_832_;
}
else
{
lean_dec_ref(v___x_847_);
lean_dec(v_a_846_);
v_val_833_ = v___x_844_;
goto v___jp_832_;
}
}
else
{
lean_dec_ref(v___x_845_);
v_val_833_ = v___x_844_;
goto v___jp_832_;
}
}
else
{
lean_dec(v_val_843_);
v_val_833_ = v___x_844_;
goto v___jp_832_;
}
}
else
{
uint8_t v___x_850_; 
lean_dec(v___x_830_);
v___x_850_ = 0;
v_val_833_ = v___x_850_;
goto v___jp_832_;
}
v___jp_793_:
{
if (v_a_794_ == 0)
{
uint8_t v___x_795_; 
v___x_795_ = l_System_Platform_isWindows;
if (v___x_795_ == 0)
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; uint8_t v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_796_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__0));
lean_inc_ref(v_name_788_);
v___x_797_ = lean_string_append(v_name_788_, v___x_796_);
v___x_798_ = lean_string_append(v___x_797_, v_repo_789_);
v___x_799_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__1));
v___x_800_ = lean_string_append(v___x_798_, v___x_799_);
v___x_801_ = 1;
v___x_802_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_802_, 0, v___x_800_);
lean_ctor_set_uint8(v___x_802_, sizeof(void*)*1, v___x_801_);
lean_inc_ref(v_a_787_);
v___x_803_ = lean_apply_2(v_a_787_, v___x_802_, lean_box(0));
v___x_804_ = l_IO_FS_removeDirAll(v_repo_789_);
if (lean_obj_tag(v___x_804_) == 0)
{
lean_object* v___x_805_; 
lean_dec_ref(v___x_804_);
v___x_805_ = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(v_a_787_, v_name_788_, v_repo_789_, v_url_790_, v_rev_x3f_791_);
return v___x_805_;
}
else
{
lean_object* v_a_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_818_; 
lean_dec(v_rev_x3f_791_);
lean_dec_ref(v_url_790_);
lean_dec_ref(v_repo_789_);
lean_dec_ref(v_name_788_);
v_a_806_ = lean_ctor_get(v___x_804_, 0);
v_isSharedCheck_818_ = !lean_is_exclusive(v___x_804_);
if (v_isSharedCheck_818_ == 0)
{
v___x_808_ = v___x_804_;
v_isShared_809_ = v_isSharedCheck_818_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_a_806_);
lean_dec(v___x_804_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_818_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_810_; uint8_t v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_816_; 
v___x_810_ = lean_io_error_to_string(v_a_806_);
v___x_811_ = 3;
v___x_812_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_812_, 0, v___x_810_);
lean_ctor_set_uint8(v___x_812_, sizeof(void*)*1, v___x_811_);
v___x_813_ = lean_apply_2(v_a_787_, v___x_812_, lean_box(0));
v___x_814_ = lean_box(0);
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 0, v___x_814_);
v___x_816_ = v___x_808_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v___x_814_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
}
}
else
{
lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; uint8_t v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
lean_dec_ref(v_url_790_);
v___x_819_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__2));
lean_inc_ref(v_name_788_);
v___x_820_ = lean_string_append(v_name_788_, v___x_819_);
v___x_821_ = lean_string_append(v___x_820_, v_repo_789_);
v___x_822_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__3));
v___x_823_ = lean_string_append(v___x_821_, v___x_822_);
v___x_824_ = 1;
v___x_825_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_825_, 0, v___x_823_);
lean_ctor_set_uint8(v___x_825_, sizeof(void*)*1, v___x_824_);
lean_inc_ref(v_a_787_);
v___x_826_ = lean_apply_2(v_a_787_, v___x_825_, lean_box(0));
v___x_827_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(v_a_787_, v_name_788_, v_repo_789_, v_rev_x3f_791_);
return v___x_827_;
}
}
else
{
lean_object* v___x_828_; 
lean_dec_ref(v_url_790_);
v___x_828_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(v_a_787_, v_name_788_, v_repo_789_, v_rev_x3f_791_);
return v___x_828_;
}
}
v___jp_832_:
{
uint8_t v___x_834_; 
v___x_834_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_834_ == 0)
{
v_a_794_ = v_val_833_;
goto v___jp_793_;
}
else
{
lean_object* v___x_835_; uint8_t v___x_836_; 
v___x_835_ = lean_box(0);
v___x_836_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_836_ == 0)
{
if (v___x_834_ == 0)
{
v_a_794_ = v_val_833_;
goto v___jp_793_;
}
else
{
size_t v___x_837_; size_t v___x_838_; lean_object* v___x_839_; 
v___x_837_ = ((size_t)0ULL);
v___x_838_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
lean_inc_ref(v_a_787_);
v___x_839_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v___x_831_, v___x_837_, v___x_838_, v___x_835_, v_a_787_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_dec_ref(v___x_839_);
v_a_794_ = v_val_833_;
goto v___jp_793_;
}
else
{
lean_dec(v_rev_x3f_791_);
lean_dec_ref(v_url_790_);
lean_dec_ref(v_repo_789_);
lean_dec_ref(v_name_788_);
lean_dec_ref(v_a_787_);
return v___x_839_;
}
}
}
else
{
size_t v___x_840_; size_t v___x_841_; lean_object* v___x_842_; 
v___x_840_ = ((size_t)0ULL);
v___x_841_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
lean_inc_ref(v_a_787_);
v___x_842_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v___x_831_, v___x_840_, v___x_841_, v___x_835_, v_a_787_);
if (lean_obj_tag(v___x_842_) == 0)
{
lean_dec_ref(v___x_842_);
v_a_794_ = v_val_833_;
goto v___jp_793_;
}
else
{
lean_dec(v_rev_x3f_791_);
lean_dec_ref(v_url_790_);
lean_dec_ref(v_repo_789_);
lean_dec_ref(v_name_788_);
lean_dec_ref(v_a_787_);
return v___x_842_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0___boxed(lean_object* v_a_851_, lean_object* v_name_852_, lean_object* v_repo_853_, lean_object* v_url_854_, lean_object* v_rev_x3f_855_, lean_object* v_a_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_851_, v_name_852_, v_repo_853_, v_url_854_, v_rev_x3f_855_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo(lean_object* v_name_858_, lean_object* v_repo_859_, lean_object* v_url_860_, lean_object* v_rev_x3f_861_, lean_object* v_a_862_){
_start:
{
uint8_t v___x_864_; lean_object* v___x_868_; uint8_t v___x_869_; 
v___x_864_ = l_System_FilePath_isDir(v_repo_859_);
v___x_868_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
v___x_869_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_869_ == 0)
{
goto v___jp_865_;
}
else
{
lean_object* v___x_870_; uint8_t v___x_871_; 
v___x_870_ = lean_box(0);
v___x_871_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_871_ == 0)
{
if (v___x_869_ == 0)
{
goto v___jp_865_;
}
else
{
size_t v___x_872_; size_t v___x_873_; lean_object* v___x_874_; 
v___x_872_ = ((size_t)0ULL);
v___x_873_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
lean_inc_ref(v_a_862_);
v___x_874_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v___x_868_, v___x_872_, v___x_873_, v___x_870_, v_a_862_);
if (lean_obj_tag(v___x_874_) == 0)
{
lean_dec_ref(v___x_874_);
goto v___jp_865_;
}
else
{
lean_dec_ref(v_a_862_);
lean_dec(v_rev_x3f_861_);
lean_dec_ref(v_url_860_);
lean_dec_ref(v_repo_859_);
lean_dec_ref(v_name_858_);
return v___x_874_;
}
}
}
else
{
size_t v___x_875_; size_t v___x_876_; lean_object* v___x_877_; 
v___x_875_ = ((size_t)0ULL);
v___x_876_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
lean_inc_ref(v_a_862_);
v___x_877_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v___x_868_, v___x_875_, v___x_876_, v___x_870_, v_a_862_);
if (lean_obj_tag(v___x_877_) == 0)
{
lean_dec_ref(v___x_877_);
goto v___jp_865_;
}
else
{
lean_dec_ref(v_a_862_);
lean_dec(v_rev_x3f_861_);
lean_dec_ref(v_url_860_);
lean_dec_ref(v_repo_859_);
lean_dec_ref(v_name_858_);
return v___x_877_;
}
}
}
v___jp_865_:
{
if (v___x_864_ == 0)
{
lean_object* v___x_866_; 
v___x_866_ = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(v_a_862_, v_name_858_, v_repo_859_, v_url_860_, v_rev_x3f_861_);
return v___x_866_;
}
else
{
lean_object* v___x_867_; 
v___x_867_ = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_862_, v_name_858_, v_repo_859_, v_url_860_, v_rev_x3f_861_);
return v___x_867_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___boxed(lean_object* v_name_878_, lean_object* v_repo_879_, lean_object* v_url_880_, lean_object* v_rev_x3f_881_, lean_object* v_a_882_, lean_object* v_a_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo(v_name_878_, v_repo_879_, v_url_880_, v_rev_x3f_881_, v_a_882_);
return v_res_884_;
}
}
static lean_object* _init_l_Lake_instInhabitedMaterializedDep_default___closed__1(void){
_start:
{
lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_886_ = l_Lake_instInhabitedPackageEntry_default;
v___x_887_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___x_888_ = l_System_instInhabitedFilePath_default;
v___x_889_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_889_, 0, v___x_888_);
lean_ctor_set(v___x_889_, 1, v___x_887_);
lean_ctor_set(v___x_889_, 2, v___x_886_);
return v___x_889_;
}
}
static lean_object* _init_l_Lake_instInhabitedMaterializedDep_default(void){
_start:
{
lean_object* v___x_890_; 
v___x_890_ = lean_obj_once(&l_Lake_instInhabitedMaterializedDep_default___closed__1, &l_Lake_instInhabitedMaterializedDep_default___closed__1_once, _init_l_Lake_instInhabitedMaterializedDep_default___closed__1);
return v___x_890_;
}
}
static lean_object* _init_l_Lake_instInhabitedMaterializedDep(void){
_start:
{
lean_object* v___x_891_; 
v___x_891_ = l_Lake_instInhabitedMaterializedDep_default;
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_name(lean_object* v_self_892_){
_start:
{
lean_object* v_manifestEntry_893_; lean_object* v_name_894_; 
v_manifestEntry_893_ = lean_ctor_get(v_self_892_, 2);
v_name_894_ = lean_ctor_get(v_manifestEntry_893_, 0);
lean_inc(v_name_894_);
return v_name_894_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_name___boxed(lean_object* v_self_895_){
_start:
{
lean_object* v_res_896_; 
v_res_896_ = l_Lake_MaterializedDep_name(v_self_895_);
lean_dec_ref(v_self_895_);
return v_res_896_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_scope(lean_object* v_self_897_){
_start:
{
lean_object* v_manifestEntry_898_; lean_object* v_scope_899_; 
v_manifestEntry_898_ = lean_ctor_get(v_self_897_, 2);
v_scope_899_ = lean_ctor_get(v_manifestEntry_898_, 1);
lean_inc_ref(v_scope_899_);
return v_scope_899_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_scope___boxed(lean_object* v_self_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_Lake_MaterializedDep_scope(v_self_900_);
lean_dec_ref(v_self_900_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_manifestFile_x3f(lean_object* v_self_902_){
_start:
{
lean_object* v_manifestEntry_903_; lean_object* v_manifestFile_x3f_904_; 
v_manifestEntry_903_ = lean_ctor_get(v_self_902_, 2);
v_manifestFile_x3f_904_ = lean_ctor_get(v_manifestEntry_903_, 3);
lean_inc(v_manifestFile_x3f_904_);
return v_manifestFile_x3f_904_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_manifestFile_x3f___boxed(lean_object* v_self_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_Lake_MaterializedDep_manifestFile_x3f(v_self_905_);
lean_dec_ref(v_self_905_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_configFile(lean_object* v_self_907_){
_start:
{
lean_object* v_manifestEntry_908_; lean_object* v_configFile_909_; 
v_manifestEntry_908_ = lean_ctor_get(v_self_907_, 2);
v_configFile_909_ = lean_ctor_get(v_manifestEntry_908_, 2);
lean_inc_ref(v_configFile_909_);
return v_configFile_909_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_configFile___boxed(lean_object* v_self_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_Lake_MaterializedDep_configFile(v_self_910_);
lean_dec_ref(v_self_910_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorIdx(lean_object* v_x_912_){
_start:
{
switch(lean_obj_tag(v_x_912_))
{
case 0:
{
lean_object* v___x_913_; 
v___x_913_ = lean_unsigned_to_nat(0u);
return v___x_913_;
}
case 1:
{
lean_object* v___x_914_; 
v___x_914_ = lean_unsigned_to_nat(1u);
return v___x_914_;
}
default: 
{
lean_object* v___x_915_; 
v___x_915_ = lean_unsigned_to_nat(2u);
return v___x_915_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorIdx___boxed(lean_object* v_x_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorIdx(v_x_916_);
lean_dec(v_x_916_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(lean_object* v_t_918_, lean_object* v_k_919_){
_start:
{
if (lean_obj_tag(v_t_918_) == 0)
{
return v_k_919_;
}
else
{
lean_object* v_rev_920_; lean_object* v___x_921_; 
v_rev_920_ = lean_ctor_get(v_t_918_, 0);
lean_inc_ref(v_rev_920_);
lean_dec(v_t_918_);
v___x_921_ = lean_apply_1(v_k_919_, v_rev_920_);
return v___x_921_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim(lean_object* v_motive_922_, lean_object* v_ctorIdx_923_, lean_object* v_t_924_, lean_object* v_h_925_, lean_object* v_k_926_){
_start:
{
lean_object* v___x_927_; 
v___x_927_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(v_t_924_, v_k_926_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___boxed(lean_object* v_motive_928_, lean_object* v_ctorIdx_929_, lean_object* v_t_930_, lean_object* v_h_931_, lean_object* v_k_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim(v_motive_928_, v_ctorIdx_929_, v_t_930_, v_h_931_, v_k_932_);
lean_dec(v_ctorIdx_929_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_none_elim___redArg(lean_object* v_t_934_, lean_object* v_none_935_){
_start:
{
lean_object* v___x_936_; 
v___x_936_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(v_t_934_, v_none_935_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_none_elim(lean_object* v_motive_937_, lean_object* v_t_938_, lean_object* v_h_939_, lean_object* v_none_940_){
_start:
{
lean_object* v___x_941_; 
v___x_941_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(v_t_938_, v_none_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_git_elim___redArg(lean_object* v_t_942_, lean_object* v_git_943_){
_start:
{
lean_object* v___x_944_; 
v___x_944_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(v_t_942_, v_git_943_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_git_elim(lean_object* v_motive_945_, lean_object* v_t_946_, lean_object* v_h_947_, lean_object* v_git_948_){
_start:
{
lean_object* v___x_949_; 
v___x_949_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(v_t_946_, v_git_948_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ver_elim___redArg(lean_object* v_t_950_, lean_object* v_ver_951_){
_start:
{
lean_object* v___x_952_; 
v___x_952_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(v_t_950_, v_ver_951_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ver_elim(lean_object* v_motive_953_, lean_object* v_t_954_, lean_object* v_h_955_, lean_object* v_ver_956_){
_start:
{
lean_object* v___x_957_; 
v___x_957_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(v_t_954_, v_ver_956_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed(lean_object* v_scope_966_, lean_object* v_name_967_, lean_object* v_ver_968_){
_start:
{
lean_object* v_fst_970_; lean_object* v_snd_971_; 
switch(lean_obj_tag(v_ver_968_))
{
case 0:
{
lean_object* v___x_992_; 
v___x_992_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v_fst_970_ = v___x_992_;
v_snd_971_ = v___x_992_;
goto v___jp_969_;
}
case 1:
{
lean_object* v_rev_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1008_; 
v_rev_993_ = lean_ctor_get(v_ver_968_, 0);
v_isSharedCheck_1008_ = !lean_is_exclusive(v_ver_968_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_995_ = v_ver_968_;
v_isShared_996_ = v_isSharedCheck_1008_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_rev_993_);
lean_dec(v_ver_968_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1008_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_1000_; 
v___x_997_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__5));
v___x_998_ = l_String_quote(v_rev_993_);
if (v_isShared_996_ == 0)
{
lean_ctor_set_tag(v___x_995_, 3);
lean_ctor_set(v___x_995_, 0, v___x_998_);
v___x_1000_ = v___x_995_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v___x_998_);
v___x_1000_ = v_reuseFailAlloc_1007_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1001_ = l_Std_Format_defWidth;
v___x_1002_ = lean_unsigned_to_nat(0u);
v___x_1003_ = l_Std_Format_pretty(v___x_1000_, v___x_1001_, v___x_1002_, v___x_1002_);
v___x_1004_ = lean_string_append(v___x_997_, v___x_1003_);
v___x_1005_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__6));
v___x_1006_ = lean_string_append(v___x_1005_, v___x_1003_);
lean_dec_ref(v___x_1003_);
v_fst_970_ = v___x_1004_;
v_snd_971_ = v___x_1006_;
goto v___jp_969_;
}
}
}
default: 
{
lean_object* v_ver_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1025_; 
v_ver_1009_ = lean_ctor_get(v_ver_968_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v_ver_968_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1011_ = v_ver_968_;
v_isShared_1012_ = v_isSharedCheck_1025_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_ver_1009_);
lean_dec(v_ver_968_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1025_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v_toString_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1017_; 
v_toString_1013_ = lean_ctor_get(v_ver_1009_, 0);
lean_inc_ref(v_toString_1013_);
lean_dec_ref(v_ver_1009_);
v___x_1014_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__5));
v___x_1015_ = l_String_quote(v_toString_1013_);
if (v_isShared_1012_ == 0)
{
lean_ctor_set_tag(v___x_1011_, 3);
lean_ctor_set(v___x_1011_, 0, v___x_1015_);
v___x_1017_ = v___x_1011_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v___x_1015_);
v___x_1017_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1018_ = l_Std_Format_defWidth;
v___x_1019_ = lean_unsigned_to_nat(0u);
v___x_1020_ = l_Std_Format_pretty(v___x_1017_, v___x_1018_, v___x_1019_, v___x_1019_);
v___x_1021_ = lean_string_append(v___x_1014_, v___x_1020_);
v___x_1022_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__7));
v___x_1023_ = lean_string_append(v___x_1022_, v___x_1020_);
lean_dec_ref(v___x_1020_);
v_fst_970_ = v___x_1021_;
v_snd_971_ = v___x_1023_;
goto v___jp_969_;
}
}
}
}
v___jp_969_:
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_972_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
lean_inc_ref(v_scope_966_);
v___x_973_ = lean_string_append(v_scope_966_, v___x_972_);
v___x_974_ = lean_string_append(v___x_973_, v_name_967_);
v___x_975_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__1));
v___x_976_ = lean_string_append(v___x_974_, v___x_975_);
v___x_977_ = lean_string_append(v___x_976_, v_scope_966_);
v___x_978_ = lean_string_append(v___x_977_, v___x_972_);
v___x_979_ = lean_string_append(v___x_978_, v_name_967_);
v___x_980_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__2));
v___x_981_ = lean_string_append(v___x_979_, v___x_980_);
v___x_982_ = lean_string_append(v___x_981_, v_fst_970_);
lean_dec_ref(v_fst_970_);
v___x_983_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__3));
v___x_984_ = lean_string_append(v___x_982_, v___x_983_);
v___x_985_ = lean_string_append(v___x_984_, v_scope_966_);
lean_dec_ref(v_scope_966_);
v___x_986_ = lean_string_append(v___x_985_, v___x_972_);
v___x_987_ = lean_string_append(v___x_986_, v_name_967_);
v___x_988_ = lean_string_append(v___x_987_, v___x_980_);
v___x_989_ = lean_string_append(v___x_988_, v_snd_971_);
lean_dec_ref(v_snd_971_);
v___x_990_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__4));
v___x_991_ = lean_string_append(v___x_989_, v___x_990_);
return v___x_991_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___boxed(lean_object* v_scope_1026_, lean_object* v_name_1027_, lean_object* v_ver_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed(v_scope_1026_, v_name_1027_, v_ver_1028_);
lean_dec_ref(v_name_1027_);
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep(lean_object* v_dep_1030_, uint8_t v_inherited_1031_, lean_object* v_relPkgDir_1032_, lean_object* v_remoteUrl_1033_, lean_object* v_src_1034_){
_start:
{
lean_object* v_name_1035_; lean_object* v_scope_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; 
v_name_1035_ = lean_ctor_get(v_dep_1030_, 0);
v_scope_1036_ = lean_ctor_get(v_dep_1030_, 1);
v___x_1037_ = l_Lake_defaultConfigFile;
v___x_1038_ = lean_box(0);
lean_inc_ref(v_scope_1036_);
lean_inc(v_name_1035_);
v___x_1039_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1039_, 0, v_name_1035_);
lean_ctor_set(v___x_1039_, 1, v_scope_1036_);
lean_ctor_set(v___x_1039_, 2, v___x_1037_);
lean_ctor_set(v___x_1039_, 3, v___x_1038_);
lean_ctor_set(v___x_1039_, 4, v_src_1034_);
lean_ctor_set_uint8(v___x_1039_, sizeof(void*)*5, v_inherited_1031_);
v___x_1040_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1040_, 0, v_relPkgDir_1032_);
lean_ctor_set(v___x_1040_, 1, v_remoteUrl_1033_);
lean_ctor_set(v___x_1040_, 2, v___x_1039_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___boxed(lean_object* v_dep_1041_, lean_object* v_inherited_1042_, lean_object* v_relPkgDir_1043_, lean_object* v_remoteUrl_1044_, lean_object* v_src_1045_){
_start:
{
uint8_t v_inherited_boxed_1046_; lean_object* v_res_1047_; 
v_inherited_boxed_1046_ = lean_unbox(v_inherited_1042_);
v_res_1047_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep(v_dep_1041_, v_inherited_boxed_1046_, v_relPkgDir_1043_, v_remoteUrl_1044_, v_src_1045_);
lean_dec_ref(v_dep_1041_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(lean_object* v_a_1048_, lean_object* v_name_1049_, lean_object* v_repo_1050_, lean_object* v_url_1051_, lean_object* v_rev_x3f_1052_){
_start:
{
uint8_t v___x_1054_; lean_object* v___x_1058_; uint8_t v___x_1059_; 
v___x_1054_ = l_System_FilePath_isDir(v_repo_1050_);
v___x_1058_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
v___x_1059_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_1059_ == 0)
{
goto v___jp_1055_;
}
else
{
lean_object* v___x_1060_; uint8_t v___x_1061_; 
v___x_1060_ = lean_box(0);
v___x_1061_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_1061_ == 0)
{
if (v___x_1059_ == 0)
{
goto v___jp_1055_;
}
else
{
size_t v___x_1062_; size_t v___x_1063_; lean_object* v___x_1064_; 
v___x_1062_ = ((size_t)0ULL);
v___x_1063_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
lean_inc_ref(v_a_1048_);
v___x_1064_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v___x_1058_, v___x_1062_, v___x_1063_, v___x_1060_, v_a_1048_);
if (lean_obj_tag(v___x_1064_) == 0)
{
lean_dec_ref(v___x_1064_);
goto v___jp_1055_;
}
else
{
lean_dec(v_rev_x3f_1052_);
lean_dec_ref(v_url_1051_);
lean_dec_ref(v_repo_1050_);
lean_dec_ref(v_name_1049_);
lean_dec_ref(v_a_1048_);
return v___x_1064_;
}
}
}
else
{
size_t v___x_1065_; size_t v___x_1066_; lean_object* v___x_1067_; 
v___x_1065_ = ((size_t)0ULL);
v___x_1066_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
lean_inc_ref(v_a_1048_);
v___x_1067_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v___x_1058_, v___x_1065_, v___x_1066_, v___x_1060_, v_a_1048_);
if (lean_obj_tag(v___x_1067_) == 0)
{
lean_dec_ref(v___x_1067_);
goto v___jp_1055_;
}
else
{
lean_dec(v_rev_x3f_1052_);
lean_dec_ref(v_url_1051_);
lean_dec_ref(v_repo_1050_);
lean_dec_ref(v_name_1049_);
lean_dec_ref(v_a_1048_);
return v___x_1067_;
}
}
}
v___jp_1055_:
{
if (v___x_1054_ == 0)
{
lean_object* v___x_1056_; 
v___x_1056_ = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(v_a_1048_, v_name_1049_, v_repo_1050_, v_url_1051_, v_rev_x3f_1052_);
return v___x_1056_;
}
else
{
lean_object* v___x_1057_; 
v___x_1057_ = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1048_, v_name_1049_, v_repo_1050_, v_url_1051_, v_rev_x3f_1052_);
return v___x_1057_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0___boxed(lean_object* v_a_1068_, lean_object* v_name_1069_, lean_object* v_repo_1070_, lean_object* v_url_1071_, lean_object* v_rev_x3f_1072_, lean_object* v_a_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(v_a_1068_, v_name_1069_, v_repo_1070_, v_url_1071_, v_rev_x3f_1072_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit(lean_object* v_dep_1075_, uint8_t v_inherited_1076_, lean_object* v_lakeEnv_1077_, lean_object* v_wsDir_1078_, lean_object* v_name_1079_, lean_object* v_relPkgDir_1080_, lean_object* v_gitUrl_1081_, lean_object* v_remoteUrl_1082_, lean_object* v_inputRev_x3f_1083_, lean_object* v_subDir_x3f_1084_, lean_object* v_a_1085_){
_start:
{
lean_object* v_pkgUrlMap_1090_; lean_object* v_name_1091_; lean_object* v_scope_1092_; lean_object* v___y_1094_; lean_object* v___y_1095_; lean_object* v___y_1096_; lean_object* v___y_1104_; lean_object* v_a_1105_; lean_object* v_repo_1108_; lean_object* v___y_1110_; lean_object* v___x_1187_; 
v_pkgUrlMap_1090_ = lean_ctor_get(v_lakeEnv_1077_, 5);
v_name_1091_ = lean_ctor_get(v_dep_1075_, 0);
v_scope_1092_ = lean_ctor_get(v_dep_1075_, 1);
lean_inc_ref(v_relPkgDir_1080_);
v_repo_1108_ = l_Lake_joinRelative(v_wsDir_1078_, v_relPkgDir_1080_);
v___x_1187_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgUrlMap_1090_, v_name_1091_);
if (lean_obj_tag(v___x_1187_) == 0)
{
v___y_1110_ = v_gitUrl_1081_;
goto v___jp_1109_;
}
else
{
lean_object* v_val_1188_; 
lean_dec_ref(v_gitUrl_1081_);
v_val_1188_ = lean_ctor_get(v___x_1187_, 0);
lean_inc(v_val_1188_);
lean_dec_ref(v___x_1187_);
v___y_1110_ = v_val_1188_;
goto v___jp_1109_;
}
v___jp_1087_:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1088_ = lean_box(0);
v___x_1089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1088_);
return v___x_1089_;
}
v___jp_1093_:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1097_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1097_, 0, v___y_1094_);
lean_ctor_set(v___x_1097_, 1, v___y_1095_);
lean_ctor_set(v___x_1097_, 2, v_inputRev_x3f_1083_);
lean_ctor_set(v___x_1097_, 3, v_subDir_x3f_1084_);
v___x_1098_ = l_Lake_defaultConfigFile;
v___x_1099_ = lean_box(0);
lean_inc_ref(v_scope_1092_);
lean_inc(v_name_1091_);
v___x_1100_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1100_, 0, v_name_1091_);
lean_ctor_set(v___x_1100_, 1, v_scope_1092_);
lean_ctor_set(v___x_1100_, 2, v___x_1098_);
lean_ctor_set(v___x_1100_, 3, v___x_1099_);
lean_ctor_set(v___x_1100_, 4, v___x_1097_);
lean_ctor_set_uint8(v___x_1100_, sizeof(void*)*5, v_inherited_1076_);
v___x_1101_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1101_, 0, v___y_1096_);
lean_ctor_set(v___x_1101_, 1, v_remoteUrl_1082_);
lean_ctor_set(v___x_1101_, 2, v___x_1100_);
v___x_1102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1101_);
return v___x_1102_;
}
v___jp_1103_:
{
if (lean_obj_tag(v_subDir_x3f_1084_) == 1)
{
lean_object* v_val_1106_; lean_object* v___x_1107_; 
v_val_1106_ = lean_ctor_get(v_subDir_x3f_1084_, 0);
lean_inc(v_val_1106_);
v___x_1107_ = l_Lake_joinRelative(v_relPkgDir_1080_, v_val_1106_);
v___y_1094_ = v___y_1104_;
v___y_1095_ = v_a_1105_;
v___y_1096_ = v___x_1107_;
goto v___jp_1093_;
}
else
{
v___y_1094_ = v___y_1104_;
v___y_1095_ = v_a_1105_;
v___y_1096_ = v_relPkgDir_1080_;
goto v___jp_1093_;
}
}
v___jp_1109_:
{
lean_object* v___x_1111_; 
lean_inc(v_inputRev_x3f_1083_);
lean_inc_ref(v___y_1110_);
lean_inc_ref(v_repo_1108_);
lean_inc_ref(v_a_1085_);
v___x_1111_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(v_a_1085_, v_name_1079_, v_repo_1108_, v___y_1110_, v_inputRev_x3f_1083_);
if (lean_obj_tag(v___x_1111_) == 0)
{
lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1177_; 
v_isSharedCheck_1177_ = !lean_is_exclusive(v___x_1111_);
if (v_isSharedCheck_1177_ == 0)
{
lean_object* v_unused_1178_; 
v_unused_1178_ = lean_ctor_get(v___x_1111_, 0);
lean_dec(v_unused_1178_);
v___x_1113_ = v___x_1111_;
v_isShared_1114_ = v_isSharedCheck_1177_;
goto v_resetjp_1112_;
}
else
{
lean_dec(v___x_1111_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1177_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1115_ = lean_unsigned_to_nat(0u);
v___x_1116_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
v___x_1117_ = l_Lake_GitRepo_getHeadRevision(v_repo_1108_, v___x_1116_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v_a_1118_; lean_object* v_a_1119_; lean_object* v___x_1120_; uint8_t v___x_1121_; 
lean_del_object(v___x_1113_);
v_a_1118_ = lean_ctor_get(v___x_1117_, 0);
lean_inc(v_a_1118_);
v_a_1119_ = lean_ctor_get(v___x_1117_, 1);
lean_inc(v_a_1119_);
lean_dec_ref(v___x_1117_);
v___x_1120_ = lean_array_get_size(v_a_1119_);
v___x_1121_ = lean_nat_dec_lt(v___x_1115_, v___x_1120_);
if (v___x_1121_ == 0)
{
lean_dec(v_a_1119_);
lean_dec_ref(v_a_1085_);
v___y_1104_ = v___y_1110_;
v_a_1105_ = v_a_1118_;
goto v___jp_1103_;
}
else
{
lean_object* v___x_1122_; uint8_t v___x_1123_; 
v___x_1122_ = lean_box(0);
v___x_1123_ = lean_nat_dec_le(v___x_1120_, v___x_1120_);
if (v___x_1123_ == 0)
{
if (v___x_1121_ == 0)
{
lean_dec(v_a_1119_);
lean_dec_ref(v_a_1085_);
v___y_1104_ = v___y_1110_;
v_a_1105_ = v_a_1118_;
goto v___jp_1103_;
}
else
{
size_t v___x_1124_; size_t v___x_1125_; lean_object* v___x_1126_; 
v___x_1124_ = ((size_t)0ULL);
v___x_1125_ = lean_usize_of_nat(v___x_1120_);
v___x_1126_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_1119_, v___x_1124_, v___x_1125_, v___x_1122_, v_a_1085_);
lean_dec(v_a_1119_);
if (lean_obj_tag(v___x_1126_) == 0)
{
lean_dec_ref(v___x_1126_);
v___y_1104_ = v___y_1110_;
v_a_1105_ = v_a_1118_;
goto v___jp_1103_;
}
else
{
lean_object* v_a_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1134_; 
lean_dec(v_a_1118_);
lean_dec_ref(v___y_1110_);
lean_dec(v_subDir_x3f_1084_);
lean_dec(v_inputRev_x3f_1083_);
lean_dec_ref(v_remoteUrl_1082_);
lean_dec_ref(v_relPkgDir_1080_);
v_a_1127_ = lean_ctor_get(v___x_1126_, 0);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1129_ = v___x_1126_;
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_a_1127_);
lean_dec(v___x_1126_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1132_; 
if (v_isShared_1130_ == 0)
{
v___x_1132_ = v___x_1129_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_a_1127_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
}
}
else
{
size_t v___x_1135_; size_t v___x_1136_; lean_object* v___x_1137_; 
v___x_1135_ = ((size_t)0ULL);
v___x_1136_ = lean_usize_of_nat(v___x_1120_);
v___x_1137_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_1119_, v___x_1135_, v___x_1136_, v___x_1122_, v_a_1085_);
lean_dec(v_a_1119_);
if (lean_obj_tag(v___x_1137_) == 0)
{
lean_dec_ref(v___x_1137_);
v___y_1104_ = v___y_1110_;
v_a_1105_ = v_a_1118_;
goto v___jp_1103_;
}
else
{
lean_object* v_a_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1145_; 
lean_dec(v_a_1118_);
lean_dec_ref(v___y_1110_);
lean_dec(v_subDir_x3f_1084_);
lean_dec(v_inputRev_x3f_1083_);
lean_dec_ref(v_remoteUrl_1082_);
lean_dec_ref(v_relPkgDir_1080_);
v_a_1138_ = lean_ctor_get(v___x_1137_, 0);
v_isSharedCheck_1145_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1140_ = v___x_1137_;
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_a_1138_);
lean_dec(v___x_1137_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v___x_1143_; 
if (v_isShared_1141_ == 0)
{
v___x_1143_ = v___x_1140_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v_a_1138_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
}
}
}
}
else
{
lean_object* v_a_1146_; lean_object* v___x_1147_; uint8_t v___x_1148_; 
lean_dec_ref(v___y_1110_);
lean_dec(v_subDir_x3f_1084_);
lean_dec(v_inputRev_x3f_1083_);
lean_dec_ref(v_remoteUrl_1082_);
lean_dec_ref(v_relPkgDir_1080_);
v_a_1146_ = lean_ctor_get(v___x_1117_, 1);
lean_inc(v_a_1146_);
lean_dec_ref(v___x_1117_);
v___x_1147_ = lean_array_get_size(v_a_1146_);
v___x_1148_ = lean_nat_dec_lt(v___x_1115_, v___x_1147_);
if (v___x_1148_ == 0)
{
lean_object* v___x_1149_; lean_object* v___x_1151_; 
lean_dec(v_a_1146_);
lean_dec_ref(v_a_1085_);
v___x_1149_ = lean_box(0);
if (v_isShared_1114_ == 0)
{
lean_ctor_set_tag(v___x_1113_, 1);
lean_ctor_set(v___x_1113_, 0, v___x_1149_);
v___x_1151_ = v___x_1113_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v___x_1149_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
else
{
lean_object* v___x_1153_; uint8_t v___x_1154_; 
lean_del_object(v___x_1113_);
v___x_1153_ = lean_box(0);
v___x_1154_ = lean_nat_dec_le(v___x_1147_, v___x_1147_);
if (v___x_1154_ == 0)
{
if (v___x_1148_ == 0)
{
lean_dec(v_a_1146_);
lean_dec_ref(v_a_1085_);
goto v___jp_1087_;
}
else
{
size_t v___x_1155_; size_t v___x_1156_; lean_object* v___x_1157_; 
v___x_1155_ = ((size_t)0ULL);
v___x_1156_ = lean_usize_of_nat(v___x_1147_);
v___x_1157_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_1146_, v___x_1155_, v___x_1156_, v___x_1153_, v_a_1085_);
lean_dec(v_a_1146_);
if (lean_obj_tag(v___x_1157_) == 0)
{
lean_dec_ref(v___x_1157_);
goto v___jp_1087_;
}
else
{
lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1165_; 
v_a_1158_ = lean_ctor_get(v___x_1157_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1160_ = v___x_1157_;
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_dec(v___x_1157_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1163_; 
if (v_isShared_1161_ == 0)
{
v___x_1163_ = v___x_1160_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_a_1158_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
}
}
else
{
size_t v___x_1166_; size_t v___x_1167_; lean_object* v___x_1168_; 
v___x_1166_ = ((size_t)0ULL);
v___x_1167_ = lean_usize_of_nat(v___x_1147_);
v___x_1168_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_1146_, v___x_1166_, v___x_1167_, v___x_1153_, v_a_1085_);
lean_dec(v_a_1146_);
if (lean_obj_tag(v___x_1168_) == 0)
{
lean_dec_ref(v___x_1168_);
goto v___jp_1087_;
}
else
{
lean_object* v_a_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1176_; 
v_a_1169_ = lean_ctor_get(v___x_1168_, 0);
v_isSharedCheck_1176_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1171_ = v___x_1168_;
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_a_1169_);
lean_dec(v___x_1168_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v___x_1174_; 
if (v_isShared_1172_ == 0)
{
v___x_1174_ = v___x_1171_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v_a_1169_);
v___x_1174_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
return v___x_1174_;
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1186_; 
lean_dec_ref(v___y_1110_);
lean_dec_ref(v_repo_1108_);
lean_dec_ref(v_a_1085_);
lean_dec(v_subDir_x3f_1084_);
lean_dec(v_inputRev_x3f_1083_);
lean_dec_ref(v_remoteUrl_1082_);
lean_dec_ref(v_relPkgDir_1080_);
v_a_1179_ = lean_ctor_get(v___x_1111_, 0);
v_isSharedCheck_1186_ = !lean_is_exclusive(v___x_1111_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1181_ = v___x_1111_;
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_a_1179_);
lean_dec(v___x_1111_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1184_; 
if (v_isShared_1182_ == 0)
{
v___x_1184_ = v___x_1181_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_a_1179_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___boxed(lean_object* v_dep_1189_, lean_object* v_inherited_1190_, lean_object* v_lakeEnv_1191_, lean_object* v_wsDir_1192_, lean_object* v_name_1193_, lean_object* v_relPkgDir_1194_, lean_object* v_gitUrl_1195_, lean_object* v_remoteUrl_1196_, lean_object* v_inputRev_x3f_1197_, lean_object* v_subDir_x3f_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_){
_start:
{
uint8_t v_inherited_boxed_1201_; lean_object* v_res_1202_; 
v_inherited_boxed_1201_ = lean_unbox(v_inherited_1190_);
v_res_1202_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit(v_dep_1189_, v_inherited_boxed_1201_, v_lakeEnv_1191_, v_wsDir_1192_, v_name_1193_, v_relPkgDir_1194_, v_gitUrl_1195_, v_remoteUrl_1196_, v_inputRev_x3f_1197_, v_subDir_x3f_1198_, v_a_1199_);
lean_dec_ref(v_lakeEnv_1191_);
lean_dec_ref(v_dep_1189_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(lean_object* v_a_1203_, lean_object* v_dep_1204_, uint8_t v_inherited_1205_, lean_object* v_lakeEnv_1206_, lean_object* v_wsDir_1207_, lean_object* v_name_1208_, lean_object* v_relPkgDir_1209_, lean_object* v_gitUrl_1210_, lean_object* v_remoteUrl_1211_, lean_object* v_inputRev_x3f_1212_, lean_object* v_subDir_x3f_1213_){
_start:
{
lean_object* v_pkgUrlMap_1218_; lean_object* v_name_1219_; lean_object* v_scope_1220_; lean_object* v___y_1222_; lean_object* v___y_1223_; lean_object* v___y_1224_; lean_object* v___y_1232_; lean_object* v_a_1233_; lean_object* v_repo_1236_; lean_object* v___y_1238_; lean_object* v___x_1315_; 
v_pkgUrlMap_1218_ = lean_ctor_get(v_lakeEnv_1206_, 5);
v_name_1219_ = lean_ctor_get(v_dep_1204_, 0);
v_scope_1220_ = lean_ctor_get(v_dep_1204_, 1);
lean_inc_ref(v_relPkgDir_1209_);
v_repo_1236_ = l_Lake_joinRelative(v_wsDir_1207_, v_relPkgDir_1209_);
v___x_1315_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgUrlMap_1218_, v_name_1219_);
if (lean_obj_tag(v___x_1315_) == 0)
{
v___y_1238_ = v_gitUrl_1210_;
goto v___jp_1237_;
}
else
{
lean_object* v_val_1316_; 
lean_dec_ref(v_gitUrl_1210_);
v_val_1316_ = lean_ctor_get(v___x_1315_, 0);
lean_inc(v_val_1316_);
lean_dec_ref(v___x_1315_);
v___y_1238_ = v_val_1316_;
goto v___jp_1237_;
}
v___jp_1215_:
{
lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1216_ = lean_box(0);
v___x_1217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1216_);
return v___x_1217_;
}
v___jp_1221_:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1225_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1225_, 0, v___y_1223_);
lean_ctor_set(v___x_1225_, 1, v___y_1222_);
lean_ctor_set(v___x_1225_, 2, v_inputRev_x3f_1212_);
lean_ctor_set(v___x_1225_, 3, v_subDir_x3f_1213_);
v___x_1226_ = l_Lake_defaultConfigFile;
v___x_1227_ = lean_box(0);
lean_inc_ref(v_scope_1220_);
lean_inc(v_name_1219_);
v___x_1228_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1228_, 0, v_name_1219_);
lean_ctor_set(v___x_1228_, 1, v_scope_1220_);
lean_ctor_set(v___x_1228_, 2, v___x_1226_);
lean_ctor_set(v___x_1228_, 3, v___x_1227_);
lean_ctor_set(v___x_1228_, 4, v___x_1225_);
lean_ctor_set_uint8(v___x_1228_, sizeof(void*)*5, v_inherited_1205_);
v___x_1229_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1229_, 0, v___y_1224_);
lean_ctor_set(v___x_1229_, 1, v_remoteUrl_1211_);
lean_ctor_set(v___x_1229_, 2, v___x_1228_);
v___x_1230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1230_, 0, v___x_1229_);
return v___x_1230_;
}
v___jp_1231_:
{
if (lean_obj_tag(v_subDir_x3f_1213_) == 1)
{
lean_object* v_val_1234_; lean_object* v___x_1235_; 
v_val_1234_ = lean_ctor_get(v_subDir_x3f_1213_, 0);
lean_inc(v_val_1234_);
v___x_1235_ = l_Lake_joinRelative(v_relPkgDir_1209_, v_val_1234_);
v___y_1222_ = v_a_1233_;
v___y_1223_ = v___y_1232_;
v___y_1224_ = v___x_1235_;
goto v___jp_1221_;
}
else
{
v___y_1222_ = v_a_1233_;
v___y_1223_ = v___y_1232_;
v___y_1224_ = v_relPkgDir_1209_;
goto v___jp_1221_;
}
}
v___jp_1237_:
{
lean_object* v___x_1239_; 
lean_inc(v_inputRev_x3f_1212_);
lean_inc_ref(v___y_1238_);
lean_inc_ref(v_repo_1236_);
lean_inc_ref(v_a_1203_);
v___x_1239_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(v_a_1203_, v_name_1208_, v_repo_1236_, v___y_1238_, v_inputRev_x3f_1212_);
if (lean_obj_tag(v___x_1239_) == 0)
{
lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1305_; 
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1305_ == 0)
{
lean_object* v_unused_1306_; 
v_unused_1306_ = lean_ctor_get(v___x_1239_, 0);
lean_dec(v_unused_1306_);
v___x_1241_ = v___x_1239_;
v_isShared_1242_ = v_isSharedCheck_1305_;
goto v_resetjp_1240_;
}
else
{
lean_dec(v___x_1239_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1305_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1243_ = lean_unsigned_to_nat(0u);
v___x_1244_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
v___x_1245_ = l_Lake_GitRepo_getHeadRevision(v_repo_1236_, v___x_1244_);
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_object* v_a_1246_; lean_object* v_a_1247_; lean_object* v___x_1248_; uint8_t v___x_1249_; 
lean_del_object(v___x_1241_);
v_a_1246_ = lean_ctor_get(v___x_1245_, 0);
lean_inc(v_a_1246_);
v_a_1247_ = lean_ctor_get(v___x_1245_, 1);
lean_inc(v_a_1247_);
lean_dec_ref(v___x_1245_);
v___x_1248_ = lean_array_get_size(v_a_1247_);
v___x_1249_ = lean_nat_dec_lt(v___x_1243_, v___x_1248_);
if (v___x_1249_ == 0)
{
lean_dec(v_a_1247_);
lean_dec_ref(v_a_1203_);
v___y_1232_ = v___y_1238_;
v_a_1233_ = v_a_1246_;
goto v___jp_1231_;
}
else
{
lean_object* v___x_1250_; uint8_t v___x_1251_; 
v___x_1250_ = lean_box(0);
v___x_1251_ = lean_nat_dec_le(v___x_1248_, v___x_1248_);
if (v___x_1251_ == 0)
{
if (v___x_1249_ == 0)
{
lean_dec(v_a_1247_);
lean_dec_ref(v_a_1203_);
v___y_1232_ = v___y_1238_;
v_a_1233_ = v_a_1246_;
goto v___jp_1231_;
}
else
{
size_t v___x_1252_; size_t v___x_1253_; lean_object* v___x_1254_; 
v___x_1252_ = ((size_t)0ULL);
v___x_1253_ = lean_usize_of_nat(v___x_1248_);
v___x_1254_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_1247_, v___x_1252_, v___x_1253_, v___x_1250_, v_a_1203_);
lean_dec(v_a_1247_);
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_dec_ref(v___x_1254_);
v___y_1232_ = v___y_1238_;
v_a_1233_ = v_a_1246_;
goto v___jp_1231_;
}
else
{
lean_object* v_a_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1262_; 
lean_dec(v_a_1246_);
lean_dec_ref(v___y_1238_);
lean_dec(v_subDir_x3f_1213_);
lean_dec(v_inputRev_x3f_1212_);
lean_dec_ref(v_remoteUrl_1211_);
lean_dec_ref(v_relPkgDir_1209_);
v_a_1255_ = lean_ctor_get(v___x_1254_, 0);
v_isSharedCheck_1262_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1262_ == 0)
{
v___x_1257_ = v___x_1254_;
v_isShared_1258_ = v_isSharedCheck_1262_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_a_1255_);
lean_dec(v___x_1254_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1262_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___x_1260_; 
if (v_isShared_1258_ == 0)
{
v___x_1260_ = v___x_1257_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v_a_1255_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
return v___x_1260_;
}
}
}
}
}
else
{
size_t v___x_1263_; size_t v___x_1264_; lean_object* v___x_1265_; 
v___x_1263_ = ((size_t)0ULL);
v___x_1264_ = lean_usize_of_nat(v___x_1248_);
v___x_1265_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_1247_, v___x_1263_, v___x_1264_, v___x_1250_, v_a_1203_);
lean_dec(v_a_1247_);
if (lean_obj_tag(v___x_1265_) == 0)
{
lean_dec_ref(v___x_1265_);
v___y_1232_ = v___y_1238_;
v_a_1233_ = v_a_1246_;
goto v___jp_1231_;
}
else
{
lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1273_; 
lean_dec(v_a_1246_);
lean_dec_ref(v___y_1238_);
lean_dec(v_subDir_x3f_1213_);
lean_dec(v_inputRev_x3f_1212_);
lean_dec_ref(v_remoteUrl_1211_);
lean_dec_ref(v_relPkgDir_1209_);
v_a_1266_ = lean_ctor_get(v___x_1265_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1268_ = v___x_1265_;
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___x_1265_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1271_; 
if (v_isShared_1269_ == 0)
{
v___x_1271_ = v___x_1268_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_a_1266_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
}
}
}
else
{
lean_object* v_a_1274_; lean_object* v___x_1275_; uint8_t v___x_1276_; 
lean_dec_ref(v___y_1238_);
lean_dec(v_subDir_x3f_1213_);
lean_dec(v_inputRev_x3f_1212_);
lean_dec_ref(v_remoteUrl_1211_);
lean_dec_ref(v_relPkgDir_1209_);
v_a_1274_ = lean_ctor_get(v___x_1245_, 1);
lean_inc(v_a_1274_);
lean_dec_ref(v___x_1245_);
v___x_1275_ = lean_array_get_size(v_a_1274_);
v___x_1276_ = lean_nat_dec_lt(v___x_1243_, v___x_1275_);
if (v___x_1276_ == 0)
{
lean_object* v___x_1277_; lean_object* v___x_1279_; 
lean_dec(v_a_1274_);
lean_dec_ref(v_a_1203_);
v___x_1277_ = lean_box(0);
if (v_isShared_1242_ == 0)
{
lean_ctor_set_tag(v___x_1241_, 1);
lean_ctor_set(v___x_1241_, 0, v___x_1277_);
v___x_1279_ = v___x_1241_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v___x_1277_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
return v___x_1279_;
}
}
else
{
lean_object* v___x_1281_; uint8_t v___x_1282_; 
lean_del_object(v___x_1241_);
v___x_1281_ = lean_box(0);
v___x_1282_ = lean_nat_dec_le(v___x_1275_, v___x_1275_);
if (v___x_1282_ == 0)
{
if (v___x_1276_ == 0)
{
lean_dec(v_a_1274_);
lean_dec_ref(v_a_1203_);
goto v___jp_1215_;
}
else
{
size_t v___x_1283_; size_t v___x_1284_; lean_object* v___x_1285_; 
v___x_1283_ = ((size_t)0ULL);
v___x_1284_ = lean_usize_of_nat(v___x_1275_);
v___x_1285_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_1274_, v___x_1283_, v___x_1284_, v___x_1281_, v_a_1203_);
lean_dec(v_a_1274_);
if (lean_obj_tag(v___x_1285_) == 0)
{
lean_dec_ref(v___x_1285_);
goto v___jp_1215_;
}
else
{
lean_object* v_a_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1293_; 
v_a_1286_ = lean_ctor_get(v___x_1285_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1288_ = v___x_1285_;
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_a_1286_);
lean_dec(v___x_1285_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1291_; 
if (v_isShared_1289_ == 0)
{
v___x_1291_ = v___x_1288_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_a_1286_);
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
else
{
size_t v___x_1294_; size_t v___x_1295_; lean_object* v___x_1296_; 
v___x_1294_ = ((size_t)0ULL);
v___x_1295_ = lean_usize_of_nat(v___x_1275_);
v___x_1296_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_1274_, v___x_1294_, v___x_1295_, v___x_1281_, v_a_1203_);
lean_dec(v_a_1274_);
if (lean_obj_tag(v___x_1296_) == 0)
{
lean_dec_ref(v___x_1296_);
goto v___jp_1215_;
}
else
{
lean_object* v_a_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1304_; 
v_a_1297_ = lean_ctor_get(v___x_1296_, 0);
v_isSharedCheck_1304_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1299_ = v___x_1296_;
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_a_1297_);
lean_dec(v___x_1296_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___x_1302_; 
if (v_isShared_1300_ == 0)
{
v___x_1302_ = v___x_1299_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v_a_1297_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
return v___x_1302_;
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1314_; 
lean_dec_ref(v___y_1238_);
lean_dec_ref(v_repo_1236_);
lean_dec(v_subDir_x3f_1213_);
lean_dec(v_inputRev_x3f_1212_);
lean_dec_ref(v_remoteUrl_1211_);
lean_dec_ref(v_relPkgDir_1209_);
lean_dec_ref(v_a_1203_);
v_a_1307_ = lean_ctor_get(v___x_1239_, 0);
v_isSharedCheck_1314_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1309_ = v___x_1239_;
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_a_1307_);
lean_dec(v___x_1239_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1312_; 
if (v_isShared_1310_ == 0)
{
v___x_1312_ = v___x_1309_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_a_1307_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
return v___x_1312_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0___boxed(lean_object* v_a_1317_, lean_object* v_dep_1318_, lean_object* v_inherited_1319_, lean_object* v_lakeEnv_1320_, lean_object* v_wsDir_1321_, lean_object* v_name_1322_, lean_object* v_relPkgDir_1323_, lean_object* v_gitUrl_1324_, lean_object* v_remoteUrl_1325_, lean_object* v_inputRev_x3f_1326_, lean_object* v_subDir_x3f_1327_, lean_object* v_a_1328_){
_start:
{
uint8_t v_inherited_boxed_1329_; lean_object* v_res_1330_; 
v_inherited_boxed_1329_ = lean_unbox(v_inherited_1319_);
v_res_1330_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(v_a_1317_, v_dep_1318_, v_inherited_boxed_1329_, v_lakeEnv_1320_, v_wsDir_1321_, v_name_1322_, v_relPkgDir_1323_, v_gitUrl_1324_, v_remoteUrl_1325_, v_inputRev_x3f_1326_, v_subDir_x3f_1327_);
lean_dec_ref(v_lakeEnv_1320_);
lean_dec_ref(v_dep_1318_);
return v_res_1330_;
}
}
static lean_object* _init_l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1332_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__0));
v___x_1333_ = lean_string_utf8_byte_size(v___x_1332_);
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg(lean_object* v_s_1334_){
_start:
{
lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; uint8_t v___x_1338_; 
v___x_1335_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__0));
v___x_1336_ = lean_string_utf8_byte_size(v_s_1334_);
v___x_1337_ = lean_obj_once(&l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__1, &l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__1_once, _init_l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__1);
v___x_1338_ = lean_nat_dec_le(v___x_1337_, v___x_1336_);
if (v___x_1338_ == 0)
{
lean_object* v___x_1339_; 
lean_dec_ref(v_s_1334_);
v___x_1339_ = lean_box(0);
return v___x_1339_;
}
else
{
lean_object* v___x_1340_; uint8_t v___x_1341_; 
v___x_1340_ = lean_unsigned_to_nat(0u);
v___x_1341_ = lean_string_memcmp(v_s_1334_, v___x_1335_, v___x_1340_, v___x_1340_, v___x_1337_);
if (v___x_1341_ == 0)
{
lean_object* v___x_1342_; 
lean_dec_ref(v_s_1334_);
v___x_1342_ = lean_box(0);
return v___x_1342_;
}
else
{
lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
lean_inc_ref(v_s_1334_);
v___x_1343_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1343_, 0, v_s_1334_);
lean_ctor_set(v___x_1343_, 1, v___x_1340_);
lean_ctor_set(v___x_1343_, 2, v___x_1336_);
v___x_1344_ = l_String_Slice_pos_x21(v___x_1343_, v___x_1337_);
lean_dec_ref(v___x_1343_);
v___x_1345_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1345_, 0, v_s_1334_);
lean_ctor_set(v___x_1345_, 1, v___x_1344_);
lean_ctor_set(v___x_1345_, 2, v___x_1336_);
v___x_1346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1345_);
return v___x_1346_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2(lean_object* v_s_1347_, lean_object* v_pat_1348_){
_start:
{
lean_object* v___x_1349_; 
v___x_1349_ = l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg(v_s_1347_);
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___boxed(lean_object* v_s_1350_, lean_object* v_pat_1351_){
_start:
{
lean_object* v_res_1352_; 
v_res_1352_ = l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2(v_s_1350_, v_pat_1351_);
lean_dec_ref(v_pat_1351_);
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(lean_object* v_ver_1356_, lean_object* v_as_1357_, size_t v_sz_1358_, size_t v_i_1359_, lean_object* v_b_1360_){
_start:
{
uint8_t v___x_1361_; 
v___x_1361_ = lean_usize_dec_lt(v_i_1359_, v_sz_1358_);
if (v___x_1361_ == 0)
{
return v_b_1360_;
}
else
{
lean_object* v_a_1362_; lean_object* v_version_1363_; lean_object* v___x_1364_; uint8_t v___x_1365_; 
lean_dec_ref(v_b_1360_);
v_a_1362_ = lean_array_uget_borrowed(v_as_1357_, v_i_1359_);
v_version_1363_ = lean_ctor_get(v_a_1362_, 0);
v___x_1364_ = lean_box(0);
v___x_1365_ = l_Lake_VerRange_test(v_ver_1356_, v_version_1363_);
if (v___x_1365_ == 0)
{
lean_object* v___x_1366_; size_t v___x_1367_; size_t v___x_1368_; 
v___x_1366_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___closed__0));
v___x_1367_ = ((size_t)1ULL);
v___x_1368_ = lean_usize_add(v_i_1359_, v___x_1367_);
v_i_1359_ = v___x_1368_;
v_b_1360_ = v___x_1366_;
goto _start;
}
else
{
lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; 
lean_inc(v_a_1362_);
v___x_1370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1370_, 0, v_a_1362_);
v___x_1371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1371_, 0, v___x_1370_);
v___x_1372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1372_, 0, v___x_1371_);
lean_ctor_set(v___x_1372_, 1, v___x_1364_);
return v___x_1372_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___boxed(lean_object* v_ver_1373_, lean_object* v_as_1374_, lean_object* v_sz_1375_, lean_object* v_i_1376_, lean_object* v_b_1377_){
_start:
{
size_t v_sz_boxed_1378_; size_t v_i_boxed_1379_; lean_object* v_res_1380_; 
v_sz_boxed_1378_ = lean_unbox_usize(v_sz_1375_);
lean_dec(v_sz_1375_);
v_i_boxed_1379_ = lean_unbox_usize(v_i_1376_);
lean_dec(v_i_1376_);
v_res_1380_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(v_ver_1373_, v_as_1374_, v_sz_boxed_1378_, v_i_boxed_1379_, v_b_1377_);
lean_dec_ref(v_as_1374_);
lean_dec_ref(v_ver_1373_);
return v_res_1380_;
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize(lean_object* v_dep_1392_, uint8_t v_inherited_1393_, lean_object* v_lakeEnv_1394_, lean_object* v_wsDir_1395_, lean_object* v_relPkgsDir_1396_, lean_object* v_relParentDir_1397_, lean_object* v_a_1398_){
_start:
{
lean_object* v___y_1404_; lean_object* v___y_1405_; lean_object* v___y_1415_; lean_object* v___y_1416_; lean_object* v___y_1417_; lean_object* v___y_1418_; lean_object* v___y_1419_; lean_object* v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1425_; lean_object* v___y_1426_; lean_object* v___y_1427_; lean_object* v___y_1428_; lean_object* v___y_1429_; lean_object* v_rev_x3f_1430_; lean_object* v___y_1431_; lean_object* v_name_1434_; lean_object* v_scope_1435_; lean_object* v_version_x3f_1436_; lean_object* v_src_x3f_1437_; lean_object* v___y_1439_; lean_object* v___y_1440_; lean_object* v___y_1456_; lean_object* v___y_1457_; lean_object* v___y_1458_; lean_object* v___y_1459_; lean_object* v___y_1460_; lean_object* v___y_1461_; lean_object* v___y_1462_; lean_object* v_a_1463_; 
v_name_1434_ = lean_ctor_get(v_dep_1392_, 0);
v_scope_1435_ = lean_ctor_get(v_dep_1392_, 1);
v_version_x3f_1436_ = lean_ctor_get(v_dep_1392_, 2);
v_src_x3f_1437_ = lean_ctor_get(v_dep_1392_, 3);
lean_inc(v_src_x3f_1437_);
if (lean_obj_tag(v_src_x3f_1437_) == 1)
{
lean_object* v_val_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1539_; 
v_val_1506_ = lean_ctor_get(v_src_x3f_1437_, 0);
v_isSharedCheck_1539_ = !lean_is_exclusive(v_src_x3f_1437_);
if (v_isSharedCheck_1539_ == 0)
{
v___x_1508_ = v_src_x3f_1437_;
v_isShared_1509_ = v_isSharedCheck_1539_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_val_1506_);
lean_dec(v_src_x3f_1437_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1539_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
if (lean_obj_tag(v_val_1506_) == 0)
{
lean_object* v_dir_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1526_; 
lean_inc_ref(v_scope_1435_);
lean_inc(v_name_1434_);
lean_dec_ref(v_a_1398_);
lean_dec_ref(v_relPkgsDir_1396_);
lean_dec_ref(v_wsDir_1395_);
lean_dec_ref(v_lakeEnv_1394_);
lean_dec_ref(v_dep_1392_);
v_dir_1510_ = lean_ctor_get(v_val_1506_, 0);
v_isSharedCheck_1526_ = !lean_is_exclusive(v_val_1506_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1512_ = v_val_1506_;
v_isShared_1513_ = v_isSharedCheck_1526_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_dir_1510_);
lean_dec(v_val_1506_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1526_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v_relPkgDir_1514_; lean_object* v___x_1515_; lean_object* v___x_1517_; 
v_relPkgDir_1514_ = l_Lake_joinRelative(v_relParentDir_1397_, v_dir_1510_);
v___x_1515_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
lean_inc_ref(v_relPkgDir_1514_);
if (v_isShared_1513_ == 0)
{
lean_ctor_set(v___x_1512_, 0, v_relPkgDir_1514_);
v___x_1517_ = v___x_1512_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_relPkgDir_1514_);
v___x_1517_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1523_; 
v___x_1518_ = l_Lake_defaultConfigFile;
v___x_1519_ = lean_box(0);
v___x_1520_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1520_, 0, v_name_1434_);
lean_ctor_set(v___x_1520_, 1, v_scope_1435_);
lean_ctor_set(v___x_1520_, 2, v___x_1518_);
lean_ctor_set(v___x_1520_, 3, v___x_1519_);
lean_ctor_set(v___x_1520_, 4, v___x_1517_);
lean_ctor_set_uint8(v___x_1520_, sizeof(void*)*5, v_inherited_1393_);
v___x_1521_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1521_, 0, v_relPkgDir_1514_);
lean_ctor_set(v___x_1521_, 1, v___x_1515_);
lean_ctor_set(v___x_1521_, 2, v___x_1520_);
if (v_isShared_1509_ == 0)
{
lean_ctor_set_tag(v___x_1508_, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1521_);
v___x_1523_ = v___x_1508_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v___x_1521_);
v___x_1523_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
return v___x_1523_;
}
}
}
}
else
{
lean_object* v_url_1527_; lean_object* v_rev_1528_; lean_object* v_subDir_1529_; uint8_t v___x_1530_; lean_object* v_sname_1531_; lean_object* v___y_1533_; lean_object* v___x_1536_; 
lean_del_object(v___x_1508_);
lean_dec_ref(v_relParentDir_1397_);
v_url_1527_ = lean_ctor_get(v_val_1506_, 0);
lean_inc_ref(v_url_1527_);
v_rev_1528_ = lean_ctor_get(v_val_1506_, 1);
lean_inc(v_rev_1528_);
v_subDir_1529_ = lean_ctor_get(v_val_1506_, 2);
lean_inc(v_subDir_1529_);
lean_dec_ref(v_val_1506_);
v___x_1530_ = 0;
lean_inc(v_name_1434_);
v_sname_1531_ = l_Lean_Name_toString(v_name_1434_, v___x_1530_);
lean_inc_ref(v_url_1527_);
v___x_1536_ = l_Lake_Git_filterUrl_x3f(v_url_1527_);
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_object* v___x_1537_; 
v___x_1537_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___y_1533_ = v___x_1537_;
goto v___jp_1532_;
}
else
{
lean_object* v_val_1538_; 
v_val_1538_ = lean_ctor_get(v___x_1536_, 0);
lean_inc(v_val_1538_);
lean_dec_ref(v___x_1536_);
v___y_1533_ = v_val_1538_;
goto v___jp_1532_;
}
v___jp_1532_:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; 
lean_inc_ref(v_sname_1531_);
v___x_1534_ = l_Lake_joinRelative(v_relPkgsDir_1396_, v_sname_1531_);
v___x_1535_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(v_a_1398_, v_dep_1392_, v_inherited_1393_, v_lakeEnv_1394_, v_wsDir_1395_, v_sname_1531_, v___x_1534_, v_url_1527_, v___y_1533_, v_rev_1528_, v_subDir_1529_);
lean_dec_ref(v_lakeEnv_1394_);
lean_dec_ref(v_dep_1392_);
return v___x_1535_;
}
}
}
}
else
{
lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___y_1543_; lean_object* v___y_1544_; lean_object* v___y_1545_; lean_object* v___y_1546_; lean_object* v___y_1547_; lean_object* v___y_1548_; lean_object* v___y_1549_; lean_object* v_fst_1550_; lean_object* v_snd_1551_; lean_object* v___y_1579_; lean_object* v___y_1580_; lean_object* v_a_1581_; lean_object* v___y_1714_; lean_object* v___y_1715_; lean_object* v_fst_1716_; lean_object* v_snd_1717_; uint8_t v___x_1744_; lean_object* v_a_1746_; 
lean_dec(v_src_x3f_1437_);
lean_dec_ref(v_relParentDir_1397_);
v___x_1540_ = lean_string_utf8_byte_size(v_scope_1435_);
v___x_1541_ = lean_unsigned_to_nat(0u);
v___x_1744_ = lean_nat_dec_eq(v___x_1540_, v___x_1541_);
if (v___x_1744_ == 0)
{
if (lean_obj_tag(v_version_x3f_1436_) == 1)
{
lean_object* v_val_1756_; lean_object* v___x_1757_; 
v_val_1756_ = lean_ctor_get(v_version_x3f_1436_, 0);
lean_inc(v_val_1756_);
v___x_1757_ = l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg(v_val_1756_);
if (lean_obj_tag(v___x_1757_) == 1)
{
lean_object* v_val_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1766_; 
v_val_1758_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1766_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1766_ == 0)
{
v___x_1760_ = v___x_1757_;
v_isShared_1761_ = v_isSharedCheck_1766_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_val_1758_);
lean_dec(v___x_1757_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1766_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v___x_1762_; lean_object* v___x_1764_; 
v___x_1762_ = l_String_Slice_toString(v_val_1758_);
lean_dec(v_val_1758_);
if (v_isShared_1761_ == 0)
{
lean_ctor_set(v___x_1760_, 0, v___x_1762_);
v___x_1764_ = v___x_1760_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v___x_1762_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
v_a_1746_ = v___x_1764_;
goto v___jp_1745_;
}
}
}
else
{
lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
lean_dec(v___x_1757_);
v___x_1767_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__8));
v___x_1768_ = lean_string_utf8_byte_size(v_val_1756_);
lean_inc(v_val_1756_);
v___x_1769_ = l___private_Lake_Util_Version_0__Lake_runVerParse(lean_box(0), v_val_1756_, v___x_1767_, v___x_1541_, v___x_1768_);
if (lean_obj_tag(v___x_1769_) == 0)
{
lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1786_; 
lean_inc(v_name_1434_);
lean_dec_ref(v_relPkgsDir_1396_);
lean_dec_ref(v_wsDir_1395_);
lean_dec_ref(v_lakeEnv_1394_);
lean_dec_ref(v_dep_1392_);
v_a_1770_ = lean_ctor_get(v___x_1769_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1769_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1772_ = v___x_1769_;
v_isShared_1773_ = v_isSharedCheck_1786_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_a_1770_);
lean_dec(v___x_1769_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1786_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
uint8_t v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; uint8_t v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1784_; 
v___x_1774_ = 1;
v___x_1775_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1434_, v___x_1774_);
v___x_1776_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__9));
v___x_1777_ = lean_string_append(v___x_1775_, v___x_1776_);
v___x_1778_ = lean_string_append(v___x_1777_, v_a_1770_);
lean_dec(v_a_1770_);
v___x_1779_ = 3;
v___x_1780_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1780_, 0, v___x_1778_);
lean_ctor_set_uint8(v___x_1780_, sizeof(void*)*1, v___x_1779_);
v___x_1781_ = lean_apply_2(v_a_1398_, v___x_1780_, lean_box(0));
v___x_1782_ = lean_box(0);
if (v_isShared_1773_ == 0)
{
lean_ctor_set_tag(v___x_1772_, 1);
lean_ctor_set(v___x_1772_, 0, v___x_1782_);
v___x_1784_ = v___x_1772_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v___x_1782_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
else
{
lean_object* v_a_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1794_; 
v_a_1787_ = lean_ctor_get(v___x_1769_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1769_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1789_ = v___x_1769_;
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_a_1787_);
lean_dec(v___x_1769_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1792_; 
if (v_isShared_1790_ == 0)
{
lean_ctor_set_tag(v___x_1789_, 2);
v___x_1792_ = v___x_1789_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_a_1787_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
v_a_1746_ = v___x_1792_;
goto v___jp_1745_;
}
}
}
}
}
else
{
lean_object* v___x_1795_; 
v___x_1795_ = lean_box(0);
v_a_1746_ = v___x_1795_;
goto v___jp_1745_;
}
}
else
{
lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; uint8_t v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; 
lean_inc(v_name_1434_);
lean_dec_ref(v_relPkgsDir_1396_);
lean_dec_ref(v_wsDir_1395_);
lean_dec_ref(v_lakeEnv_1394_);
lean_dec_ref(v_dep_1392_);
v___x_1796_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1434_, v___x_1744_);
v___x_1797_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__10));
v___x_1798_ = lean_string_append(v___x_1796_, v___x_1797_);
v___x_1799_ = 3;
v___x_1800_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1800_, 0, v___x_1798_);
lean_ctor_set_uint8(v___x_1800_, sizeof(void*)*1, v___x_1799_);
v___x_1801_ = lean_apply_2(v_a_1398_, v___x_1800_, lean_box(0));
v___x_1802_ = lean_box(0);
v___x_1803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1803_, 0, v___x_1802_);
return v___x_1803_;
}
v___jp_1542_:
{
lean_object* v___x_1552_; uint8_t v___x_1553_; 
v___x_1552_ = lean_array_get_size(v_snd_1551_);
v___x_1553_ = lean_nat_dec_lt(v___x_1541_, v___x_1552_);
if (v___x_1553_ == 0)
{
lean_dec_ref(v_snd_1551_);
v___y_1456_ = v___y_1543_;
v___y_1457_ = v___y_1544_;
v___y_1458_ = v___y_1545_;
v___y_1459_ = v___y_1547_;
v___y_1460_ = v___y_1546_;
v___y_1461_ = v___y_1548_;
v___y_1462_ = v___y_1549_;
v_a_1463_ = v_fst_1550_;
goto v___jp_1455_;
}
else
{
lean_object* v___x_1554_; uint8_t v___x_1555_; 
v___x_1554_ = lean_box(0);
v___x_1555_ = lean_nat_dec_le(v___x_1552_, v___x_1552_);
if (v___x_1555_ == 0)
{
if (v___x_1553_ == 0)
{
lean_dec_ref(v_snd_1551_);
v___y_1456_ = v___y_1543_;
v___y_1457_ = v___y_1544_;
v___y_1458_ = v___y_1545_;
v___y_1459_ = v___y_1547_;
v___y_1460_ = v___y_1546_;
v___y_1461_ = v___y_1548_;
v___y_1462_ = v___y_1549_;
v_a_1463_ = v_fst_1550_;
goto v___jp_1455_;
}
else
{
size_t v___x_1556_; size_t v___x_1557_; lean_object* v___x_1558_; 
v___x_1556_ = ((size_t)0ULL);
v___x_1557_ = lean_usize_of_nat(v___x_1552_);
lean_inc_ref(v_a_1398_);
v___x_1558_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_snd_1551_, v___x_1556_, v___x_1557_, v___x_1554_, v_a_1398_);
lean_dec_ref(v_snd_1551_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_dec_ref(v___x_1558_);
v___y_1456_ = v___y_1543_;
v___y_1457_ = v___y_1544_;
v___y_1458_ = v___y_1545_;
v___y_1459_ = v___y_1547_;
v___y_1460_ = v___y_1546_;
v___y_1461_ = v___y_1548_;
v___y_1462_ = v___y_1549_;
v_a_1463_ = v_fst_1550_;
goto v___jp_1455_;
}
else
{
lean_object* v_a_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1566_; 
lean_dec_ref(v_fst_1550_);
lean_dec_ref(v___y_1549_);
lean_dec_ref(v___y_1548_);
lean_dec(v___y_1547_);
lean_dec_ref(v___y_1546_);
lean_dec_ref(v___y_1545_);
lean_dec_ref(v___y_1544_);
lean_dec(v___y_1543_);
lean_dec_ref(v_a_1398_);
lean_dec_ref(v_wsDir_1395_);
lean_dec_ref(v_lakeEnv_1394_);
lean_dec_ref(v_dep_1392_);
v_a_1559_ = lean_ctor_get(v___x_1558_, 0);
v_isSharedCheck_1566_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1566_ == 0)
{
v___x_1561_ = v___x_1558_;
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_a_1559_);
lean_dec(v___x_1558_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1564_; 
if (v_isShared_1562_ == 0)
{
v___x_1564_ = v___x_1561_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v_a_1559_);
v___x_1564_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
return v___x_1564_;
}
}
}
}
}
else
{
size_t v___x_1567_; size_t v___x_1568_; lean_object* v___x_1569_; 
v___x_1567_ = ((size_t)0ULL);
v___x_1568_ = lean_usize_of_nat(v___x_1552_);
lean_inc_ref(v_a_1398_);
v___x_1569_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_snd_1551_, v___x_1567_, v___x_1568_, v___x_1554_, v_a_1398_);
lean_dec_ref(v_snd_1551_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_dec_ref(v___x_1569_);
v___y_1456_ = v___y_1543_;
v___y_1457_ = v___y_1544_;
v___y_1458_ = v___y_1545_;
v___y_1459_ = v___y_1547_;
v___y_1460_ = v___y_1546_;
v___y_1461_ = v___y_1548_;
v___y_1462_ = v___y_1549_;
v_a_1463_ = v_fst_1550_;
goto v___jp_1455_;
}
else
{
lean_object* v_a_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1577_; 
lean_dec_ref(v_fst_1550_);
lean_dec_ref(v___y_1549_);
lean_dec_ref(v___y_1548_);
lean_dec(v___y_1547_);
lean_dec_ref(v___y_1546_);
lean_dec_ref(v___y_1545_);
lean_dec_ref(v___y_1544_);
lean_dec(v___y_1543_);
lean_dec_ref(v_a_1398_);
lean_dec_ref(v_wsDir_1395_);
lean_dec_ref(v_lakeEnv_1394_);
lean_dec_ref(v_dep_1392_);
v_a_1570_ = lean_ctor_get(v___x_1569_, 0);
v_isSharedCheck_1577_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1577_ == 0)
{
v___x_1572_ = v___x_1569_;
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_a_1570_);
lean_dec(v___x_1569_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v___x_1575_; 
if (v_isShared_1573_ == 0)
{
v___x_1575_ = v___x_1572_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v_a_1570_);
v___x_1575_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
return v___x_1575_;
}
}
}
}
}
}
v___jp_1578_:
{
if (lean_obj_tag(v_a_1581_) == 0)
{
lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; uint8_t v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; 
lean_inc_ref(v_scope_1435_);
lean_dec_ref(v_a_1581_);
lean_dec(v___y_1579_);
lean_dec_ref(v_relPkgsDir_1396_);
lean_dec_ref(v_wsDir_1395_);
lean_dec_ref(v_lakeEnv_1394_);
lean_dec_ref(v_dep_1392_);
v___x_1582_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
v___x_1583_ = lean_string_append(v_scope_1435_, v___x_1582_);
v___x_1584_ = lean_string_append(v___x_1583_, v___y_1580_);
lean_dec_ref(v___y_1580_);
v___x_1585_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__7));
v___x_1586_ = lean_string_append(v___x_1584_, v___x_1585_);
v___x_1587_ = 3;
v___x_1588_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1588_, 0, v___x_1586_);
lean_ctor_set_uint8(v___x_1588_, sizeof(void*)*1, v___x_1587_);
v___x_1589_ = lean_apply_2(v_a_1398_, v___x_1588_, lean_box(0));
v___x_1590_ = lean_box(0);
v___x_1591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1591_, 0, v___x_1590_);
return v___x_1591_;
}
else
{
lean_object* v_a_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1712_; 
v_a_1592_ = lean_ctor_get(v_a_1581_, 0);
v_isSharedCheck_1712_ = !lean_is_exclusive(v_a_1581_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1594_ = v_a_1581_;
v_isShared_1595_ = v_isSharedCheck_1712_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_a_1592_);
lean_dec(v_a_1581_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1712_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
if (lean_obj_tag(v_a_1592_) == 0)
{
lean_object* v___x_1596_; uint8_t v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; 
lean_inc_ref(v_scope_1435_);
lean_del_object(v___x_1594_);
lean_dec_ref(v_relPkgsDir_1396_);
lean_dec_ref(v_wsDir_1395_);
lean_dec_ref(v_lakeEnv_1394_);
lean_dec_ref(v_dep_1392_);
v___x_1596_ = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed(v_scope_1435_, v___y_1580_, v___y_1579_);
lean_dec_ref(v___y_1580_);
v___x_1597_ = 3;
v___x_1598_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1598_, 0, v___x_1596_);
lean_ctor_set_uint8(v___x_1598_, sizeof(void*)*1, v___x_1597_);
v___x_1599_ = lean_apply_2(v_a_1398_, v___x_1598_, lean_box(0));
v___x_1600_ = lean_box(0);
v___x_1601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1601_, 0, v___x_1600_);
return v___x_1601_;
}
else
{
lean_object* v_val_1602_; lean_object* v___x_1603_; 
v_val_1602_ = lean_ctor_get(v_a_1592_, 0);
lean_inc(v_val_1602_);
lean_dec_ref(v_a_1592_);
v___x_1603_ = l_Lake_RegistryPkg_gitSrc_x3f(v_val_1602_);
if (lean_obj_tag(v___x_1603_) == 1)
{
lean_object* v_val_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1711_; 
v_val_1604_ = lean_ctor_get(v___x_1603_, 0);
v_isSharedCheck_1711_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1606_ = v___x_1603_;
v_isShared_1607_ = v_isSharedCheck_1711_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_val_1604_);
lean_dec(v___x_1603_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1711_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
if (lean_obj_tag(v_val_1604_) == 0)
{
lean_object* v_url_1608_; lean_object* v_githubUrl_x3f_1609_; lean_object* v_defaultBranch_x3f_1610_; lean_object* v_subDir_x3f_1611_; lean_object* v_name_1612_; lean_object* v_fullName_1613_; lean_object* v___x_1614_; 
v_url_1608_ = lean_ctor_get(v_val_1604_, 1);
lean_inc_ref(v_url_1608_);
v_githubUrl_x3f_1609_ = lean_ctor_get(v_val_1604_, 2);
lean_inc(v_githubUrl_x3f_1609_);
v_defaultBranch_x3f_1610_ = lean_ctor_get(v_val_1604_, 3);
lean_inc(v_defaultBranch_x3f_1610_);
v_subDir_x3f_1611_ = lean_ctor_get(v_val_1604_, 4);
lean_inc(v_subDir_x3f_1611_);
lean_dec_ref(v_val_1604_);
v_name_1612_ = lean_ctor_get(v_val_1602_, 0);
lean_inc_ref(v_name_1612_);
v_fullName_1613_ = lean_ctor_get(v_val_1602_, 1);
lean_inc_ref(v_fullName_1613_);
lean_dec(v_val_1602_);
v___x_1614_ = l_Lake_joinRelative(v_relPkgsDir_1396_, v_name_1612_);
switch(lean_obj_tag(v___y_1579_))
{
case 0:
{
lean_object* v___x_1615_; 
lean_del_object(v___x_1594_);
lean_dec_ref(v___y_1580_);
v___x_1615_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
if (lean_obj_tag(v_defaultBranch_x3f_1610_) == 0)
{
uint8_t v___x_1616_; 
lean_dec_ref(v___x_1614_);
lean_dec_ref(v_fullName_1613_);
lean_dec(v_subDir_x3f_1611_);
lean_dec(v_githubUrl_x3f_1609_);
lean_dec_ref(v_url_1608_);
lean_dec_ref(v_wsDir_1395_);
lean_dec_ref(v_lakeEnv_1394_);
lean_dec_ref(v_dep_1392_);
v___x_1616_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_1616_ == 0)
{
lean_object* v___x_1617_; lean_object* v___x_1619_; 
lean_dec_ref(v_a_1398_);
v___x_1617_ = lean_box(0);
if (v_isShared_1607_ == 0)
{
lean_ctor_set(v___x_1606_, 0, v___x_1617_);
v___x_1619_ = v___x_1606_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v___x_1617_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
else
{
lean_object* v___x_1621_; uint8_t v___x_1622_; 
lean_del_object(v___x_1606_);
v___x_1621_ = lean_box(0);
v___x_1622_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_1622_ == 0)
{
if (v___x_1616_ == 0)
{
lean_dec_ref(v_a_1398_);
goto v___jp_1400_;
}
else
{
size_t v___x_1623_; size_t v___x_1624_; lean_object* v___x_1625_; 
v___x_1623_ = ((size_t)0ULL);
v___x_1624_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_1625_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v___x_1615_, v___x_1623_, v___x_1624_, v___x_1621_, v_a_1398_);
if (lean_obj_tag(v___x_1625_) == 0)
{
lean_dec_ref(v___x_1625_);
goto v___jp_1400_;
}
else
{
lean_object* v_a_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1633_; 
v_a_1626_ = lean_ctor_get(v___x_1625_, 0);
v_isSharedCheck_1633_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1633_ == 0)
{
v___x_1628_ = v___x_1625_;
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_a_1626_);
lean_dec(v___x_1625_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v___x_1631_; 
if (v_isShared_1629_ == 0)
{
v___x_1631_ = v___x_1628_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v_a_1626_);
v___x_1631_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
return v___x_1631_;
}
}
}
}
}
else
{
size_t v___x_1634_; size_t v___x_1635_; lean_object* v___x_1636_; 
v___x_1634_ = ((size_t)0ULL);
v___x_1635_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_1636_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v___x_1615_, v___x_1634_, v___x_1635_, v___x_1621_, v_a_1398_);
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_dec_ref(v___x_1636_);
goto v___jp_1400_;
}
else
{
lean_object* v_a_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1644_; 
v_a_1637_ = lean_ctor_get(v___x_1636_, 0);
v_isSharedCheck_1644_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1639_ = v___x_1636_;
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_a_1637_);
lean_dec(v___x_1636_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v___x_1642_; 
if (v_isShared_1640_ == 0)
{
v___x_1642_ = v___x_1639_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_a_1637_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
}
}
}
}
else
{
lean_object* v_val_1645_; uint8_t v___x_1646_; 
lean_del_object(v___x_1606_);
v_val_1645_ = lean_ctor_get(v_defaultBranch_x3f_1610_, 0);
lean_inc(v_val_1645_);
lean_dec_ref(v_defaultBranch_x3f_1610_);
v___x_1646_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_1646_ == 0)
{
v___y_1425_ = v_subDir_x3f_1611_;
v___y_1426_ = v_fullName_1613_;
v___y_1427_ = v_url_1608_;
v___y_1428_ = v_githubUrl_x3f_1609_;
v___y_1429_ = v___x_1614_;
v_rev_x3f_1430_ = v_val_1645_;
v___y_1431_ = v_a_1398_;
goto v___jp_1424_;
}
else
{
lean_object* v___x_1647_; uint8_t v___x_1648_; 
v___x_1647_ = lean_box(0);
v___x_1648_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_1648_ == 0)
{
if (v___x_1646_ == 0)
{
v___y_1425_ = v_subDir_x3f_1611_;
v___y_1426_ = v_fullName_1613_;
v___y_1427_ = v_url_1608_;
v___y_1428_ = v_githubUrl_x3f_1609_;
v___y_1429_ = v___x_1614_;
v_rev_x3f_1430_ = v_val_1645_;
v___y_1431_ = v_a_1398_;
goto v___jp_1424_;
}
else
{
size_t v___x_1649_; size_t v___x_1650_; lean_object* v___x_1651_; 
v___x_1649_ = ((size_t)0ULL);
v___x_1650_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
lean_inc_ref(v_a_1398_);
v___x_1651_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v___x_1615_, v___x_1649_, v___x_1650_, v___x_1647_, v_a_1398_);
if (lean_obj_tag(v___x_1651_) == 0)
{
lean_dec_ref(v___x_1651_);
v___y_1425_ = v_subDir_x3f_1611_;
v___y_1426_ = v_fullName_1613_;
v___y_1427_ = v_url_1608_;
v___y_1428_ = v_githubUrl_x3f_1609_;
v___y_1429_ = v___x_1614_;
v_rev_x3f_1430_ = v_val_1645_;
v___y_1431_ = v_a_1398_;
goto v___jp_1424_;
}
else
{
lean_object* v_a_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1659_; 
lean_dec(v_val_1645_);
lean_dec_ref(v___x_1614_);
lean_dec_ref(v_fullName_1613_);
lean_dec(v_subDir_x3f_1611_);
lean_dec(v_githubUrl_x3f_1609_);
lean_dec_ref(v_url_1608_);
lean_dec_ref(v_a_1398_);
lean_dec_ref(v_wsDir_1395_);
lean_dec_ref(v_lakeEnv_1394_);
lean_dec_ref(v_dep_1392_);
v_a_1652_ = lean_ctor_get(v___x_1651_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1651_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1654_ = v___x_1651_;
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_a_1652_);
lean_dec(v___x_1651_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___x_1657_; 
if (v_isShared_1655_ == 0)
{
v___x_1657_ = v___x_1654_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_a_1652_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
}
}
}
else
{
size_t v___x_1660_; size_t v___x_1661_; lean_object* v___x_1662_; 
v___x_1660_ = ((size_t)0ULL);
v___x_1661_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
lean_inc_ref(v_a_1398_);
v___x_1662_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v___x_1615_, v___x_1660_, v___x_1661_, v___x_1647_, v_a_1398_);
if (lean_obj_tag(v___x_1662_) == 0)
{
lean_dec_ref(v___x_1662_);
v___y_1425_ = v_subDir_x3f_1611_;
v___y_1426_ = v_fullName_1613_;
v___y_1427_ = v_url_1608_;
v___y_1428_ = v_githubUrl_x3f_1609_;
v___y_1429_ = v___x_1614_;
v_rev_x3f_1430_ = v_val_1645_;
v___y_1431_ = v_a_1398_;
goto v___jp_1424_;
}
else
{
lean_object* v_a_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1670_; 
lean_dec(v_val_1645_);
lean_dec_ref(v___x_1614_);
lean_dec_ref(v_fullName_1613_);
lean_dec(v_subDir_x3f_1611_);
lean_dec(v_githubUrl_x3f_1609_);
lean_dec_ref(v_url_1608_);
lean_dec_ref(v_a_1398_);
lean_dec_ref(v_wsDir_1395_);
lean_dec_ref(v_lakeEnv_1394_);
lean_dec_ref(v_dep_1392_);
v_a_1663_ = lean_ctor_get(v___x_1662_, 0);
v_isSharedCheck_1670_ = !lean_is_exclusive(v___x_1662_);
if (v_isSharedCheck_1670_ == 0)
{
v___x_1665_ = v___x_1662_;
v_isShared_1666_ = v_isSharedCheck_1670_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_a_1663_);
lean_dec(v___x_1662_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1670_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v___x_1668_; 
if (v_isShared_1666_ == 0)
{
v___x_1668_ = v___x_1665_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v_a_1663_);
v___x_1668_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
return v___x_1668_;
}
}
}
}
}
}
}
case 1:
{
lean_object* v_rev_1671_; lean_object* v___x_1672_; uint8_t v___x_1673_; 
lean_dec(v_defaultBranch_x3f_1610_);
lean_del_object(v___x_1606_);
lean_del_object(v___x_1594_);
lean_dec_ref(v___y_1580_);
v_rev_1671_ = lean_ctor_get(v___y_1579_, 0);
lean_inc_ref(v_rev_1671_);
lean_dec_ref(v___y_1579_);
v___x_1672_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
v___x_1673_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_1673_ == 0)
{
v___y_1425_ = v_subDir_x3f_1611_;
v___y_1426_ = v_fullName_1613_;
v___y_1427_ = v_url_1608_;
v___y_1428_ = v_githubUrl_x3f_1609_;
v___y_1429_ = v___x_1614_;
v_rev_x3f_1430_ = v_rev_1671_;
v___y_1431_ = v_a_1398_;
goto v___jp_1424_;
}
else
{
lean_object* v___x_1674_; uint8_t v___x_1675_; 
v___x_1674_ = lean_box(0);
v___x_1675_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_1675_ == 0)
{
if (v___x_1673_ == 0)
{
v___y_1425_ = v_subDir_x3f_1611_;
v___y_1426_ = v_fullName_1613_;
v___y_1427_ = v_url_1608_;
v___y_1428_ = v_githubUrl_x3f_1609_;
v___y_1429_ = v___x_1614_;
v_rev_x3f_1430_ = v_rev_1671_;
v___y_1431_ = v_a_1398_;
goto v___jp_1424_;
}
else
{
size_t v___x_1676_; size_t v___x_1677_; lean_object* v___x_1678_; 
v___x_1676_ = ((size_t)0ULL);
v___x_1677_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
lean_inc_ref(v_a_1398_);
v___x_1678_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v___x_1672_, v___x_1676_, v___x_1677_, v___x_1674_, v_a_1398_);
if (lean_obj_tag(v___x_1678_) == 0)
{
lean_dec_ref(v___x_1678_);
v___y_1425_ = v_subDir_x3f_1611_;
v___y_1426_ = v_fullName_1613_;
v___y_1427_ = v_url_1608_;
v___y_1428_ = v_githubUrl_x3f_1609_;
v___y_1429_ = v___x_1614_;
v_rev_x3f_1430_ = v_rev_1671_;
v___y_1431_ = v_a_1398_;
goto v___jp_1424_;
}
else
{
lean_object* v_a_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1686_; 
lean_dec_ref(v_rev_1671_);
lean_dec_ref(v___x_1614_);
lean_dec_ref(v_fullName_1613_);
lean_dec(v_subDir_x3f_1611_);
lean_dec(v_githubUrl_x3f_1609_);
lean_dec_ref(v_url_1608_);
lean_dec_ref(v_a_1398_);
lean_dec_ref(v_wsDir_1395_);
lean_dec_ref(v_lakeEnv_1394_);
lean_dec_ref(v_dep_1392_);
v_a_1679_ = lean_ctor_get(v___x_1678_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v___x_1678_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1681_ = v___x_1678_;
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_a_1679_);
lean_dec(v___x_1678_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1684_; 
if (v_isShared_1682_ == 0)
{
v___x_1684_ = v___x_1681_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v_a_1679_);
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
}
else
{
size_t v___x_1687_; size_t v___x_1688_; lean_object* v___x_1689_; 
v___x_1687_ = ((size_t)0ULL);
v___x_1688_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
lean_inc_ref(v_a_1398_);
v___x_1689_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v___x_1672_, v___x_1687_, v___x_1688_, v___x_1674_, v_a_1398_);
if (lean_obj_tag(v___x_1689_) == 0)
{
lean_dec_ref(v___x_1689_);
v___y_1425_ = v_subDir_x3f_1611_;
v___y_1426_ = v_fullName_1613_;
v___y_1427_ = v_url_1608_;
v___y_1428_ = v_githubUrl_x3f_1609_;
v___y_1429_ = v___x_1614_;
v_rev_x3f_1430_ = v_rev_1671_;
v___y_1431_ = v_a_1398_;
goto v___jp_1424_;
}
else
{
lean_object* v_a_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1697_; 
lean_dec_ref(v_rev_1671_);
lean_dec_ref(v___x_1614_);
lean_dec_ref(v_fullName_1613_);
lean_dec(v_subDir_x3f_1611_);
lean_dec(v_githubUrl_x3f_1609_);
lean_dec_ref(v_url_1608_);
lean_dec_ref(v_a_1398_);
lean_dec_ref(v_wsDir_1395_);
lean_dec_ref(v_lakeEnv_1394_);
lean_dec_ref(v_dep_1392_);
v_a_1690_ = lean_ctor_get(v___x_1689_, 0);
v_isSharedCheck_1697_ = !lean_is_exclusive(v___x_1689_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1692_ = v___x_1689_;
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_a_1690_);
lean_dec(v___x_1689_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v___x_1695_; 
if (v_isShared_1693_ == 0)
{
v___x_1695_ = v___x_1692_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_a_1690_);
v___x_1695_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
return v___x_1695_;
}
}
}
}
}
}
default: 
{
lean_object* v_ver_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; 
lean_dec(v_defaultBranch_x3f_1610_);
lean_del_object(v___x_1606_);
v_ver_1698_ = lean_ctor_get(v___y_1579_, 0);
lean_inc_ref(v_ver_1698_);
lean_dec_ref(v___y_1579_);
v___x_1699_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
lean_inc_ref(v___y_1580_);
lean_inc_ref(v_scope_1435_);
lean_inc_ref(v_lakeEnv_1394_);
v___x_1700_ = l_Lake_Reservoir_fetchPkgVersions(v_lakeEnv_1394_, v_scope_1435_, v___y_1580_, v___x_1699_);
if (lean_obj_tag(v___x_1700_) == 0)
{
lean_object* v_a_1701_; lean_object* v_a_1702_; lean_object* v___x_1704_; 
v_a_1701_ = lean_ctor_get(v___x_1700_, 0);
lean_inc(v_a_1701_);
v_a_1702_ = lean_ctor_get(v___x_1700_, 1);
lean_inc(v_a_1702_);
lean_dec_ref(v___x_1700_);
if (v_isShared_1595_ == 0)
{
lean_ctor_set(v___x_1594_, 0, v_a_1701_);
v___x_1704_ = v___x_1594_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v_a_1701_);
v___x_1704_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
v___y_1543_ = v_subDir_x3f_1611_;
v___y_1544_ = v_fullName_1613_;
v___y_1545_ = v_url_1608_;
v___y_1546_ = v_ver_1698_;
v___y_1547_ = v_githubUrl_x3f_1609_;
v___y_1548_ = v___x_1614_;
v___y_1549_ = v___y_1580_;
v_fst_1550_ = v___x_1704_;
v_snd_1551_ = v_a_1702_;
goto v___jp_1542_;
}
}
else
{
lean_object* v_a_1706_; lean_object* v_a_1707_; lean_object* v___x_1709_; 
v_a_1706_ = lean_ctor_get(v___x_1700_, 0);
lean_inc(v_a_1706_);
v_a_1707_ = lean_ctor_get(v___x_1700_, 1);
lean_inc(v_a_1707_);
lean_dec_ref(v___x_1700_);
if (v_isShared_1595_ == 0)
{
lean_ctor_set_tag(v___x_1594_, 0);
lean_ctor_set(v___x_1594_, 0, v_a_1706_);
v___x_1709_ = v___x_1594_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v_a_1706_);
v___x_1709_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
v___y_1543_ = v_subDir_x3f_1611_;
v___y_1544_ = v_fullName_1613_;
v___y_1545_ = v_url_1608_;
v___y_1546_ = v_ver_1698_;
v___y_1547_ = v_githubUrl_x3f_1609_;
v___y_1548_ = v___x_1614_;
v___y_1549_ = v___y_1580_;
v_fst_1550_ = v___x_1709_;
v_snd_1551_ = v_a_1707_;
goto v___jp_1542_;
}
}
}
}
}
else
{
lean_del_object(v___x_1606_);
lean_dec(v_val_1604_);
lean_del_object(v___x_1594_);
lean_dec_ref(v___y_1580_);
lean_dec(v___y_1579_);
lean_dec_ref(v_relPkgsDir_1396_);
lean_dec_ref(v_wsDir_1395_);
lean_dec_ref(v_lakeEnv_1394_);
lean_dec_ref(v_dep_1392_);
v___y_1404_ = v_val_1602_;
v___y_1405_ = v_a_1398_;
goto v___jp_1403_;
}
}
}
else
{
lean_dec(v___x_1603_);
lean_del_object(v___x_1594_);
lean_dec_ref(v___y_1580_);
lean_dec(v___y_1579_);
lean_dec_ref(v_relPkgsDir_1396_);
lean_dec_ref(v_wsDir_1395_);
lean_dec_ref(v_lakeEnv_1394_);
lean_dec_ref(v_dep_1392_);
v___y_1404_ = v_val_1602_;
v___y_1405_ = v_a_1398_;
goto v___jp_1403_;
}
}
}
}
}
v___jp_1713_:
{
lean_object* v___x_1718_; uint8_t v___x_1719_; 
v___x_1718_ = lean_array_get_size(v_snd_1717_);
v___x_1719_ = lean_nat_dec_lt(v___x_1541_, v___x_1718_);
if (v___x_1719_ == 0)
{
lean_dec_ref(v_snd_1717_);
v___y_1579_ = v___y_1714_;
v___y_1580_ = v___y_1715_;
v_a_1581_ = v_fst_1716_;
goto v___jp_1578_;
}
else
{
lean_object* v___x_1720_; uint8_t v___x_1721_; 
v___x_1720_ = lean_box(0);
v___x_1721_ = lean_nat_dec_le(v___x_1718_, v___x_1718_);
if (v___x_1721_ == 0)
{
if (v___x_1719_ == 0)
{
lean_dec_ref(v_snd_1717_);
v___y_1579_ = v___y_1714_;
v___y_1580_ = v___y_1715_;
v_a_1581_ = v_fst_1716_;
goto v___jp_1578_;
}
else
{
size_t v___x_1722_; size_t v___x_1723_; lean_object* v___x_1724_; 
v___x_1722_ = ((size_t)0ULL);
v___x_1723_ = lean_usize_of_nat(v___x_1718_);
lean_inc_ref(v_a_1398_);
v___x_1724_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_snd_1717_, v___x_1722_, v___x_1723_, v___x_1720_, v_a_1398_);
lean_dec_ref(v_snd_1717_);
if (lean_obj_tag(v___x_1724_) == 0)
{
lean_dec_ref(v___x_1724_);
v___y_1579_ = v___y_1714_;
v___y_1580_ = v___y_1715_;
v_a_1581_ = v_fst_1716_;
goto v___jp_1578_;
}
else
{
lean_object* v_a_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1732_; 
lean_dec_ref(v_fst_1716_);
lean_dec_ref(v___y_1715_);
lean_dec(v___y_1714_);
lean_dec_ref(v_a_1398_);
lean_dec_ref(v_relPkgsDir_1396_);
lean_dec_ref(v_wsDir_1395_);
lean_dec_ref(v_lakeEnv_1394_);
lean_dec_ref(v_dep_1392_);
v_a_1725_ = lean_ctor_get(v___x_1724_, 0);
v_isSharedCheck_1732_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1732_ == 0)
{
v___x_1727_ = v___x_1724_;
v_isShared_1728_ = v_isSharedCheck_1732_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_a_1725_);
lean_dec(v___x_1724_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1732_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1730_; 
if (v_isShared_1728_ == 0)
{
v___x_1730_ = v___x_1727_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v_a_1725_);
v___x_1730_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
return v___x_1730_;
}
}
}
}
}
else
{
size_t v___x_1733_; size_t v___x_1734_; lean_object* v___x_1735_; 
v___x_1733_ = ((size_t)0ULL);
v___x_1734_ = lean_usize_of_nat(v___x_1718_);
lean_inc_ref(v_a_1398_);
v___x_1735_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_snd_1717_, v___x_1733_, v___x_1734_, v___x_1720_, v_a_1398_);
lean_dec_ref(v_snd_1717_);
if (lean_obj_tag(v___x_1735_) == 0)
{
lean_dec_ref(v___x_1735_);
v___y_1579_ = v___y_1714_;
v___y_1580_ = v___y_1715_;
v_a_1581_ = v_fst_1716_;
goto v___jp_1578_;
}
else
{
lean_object* v_a_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1743_; 
lean_dec_ref(v_fst_1716_);
lean_dec_ref(v___y_1715_);
lean_dec(v___y_1714_);
lean_dec_ref(v_a_1398_);
lean_dec_ref(v_relPkgsDir_1396_);
lean_dec_ref(v_wsDir_1395_);
lean_dec_ref(v_lakeEnv_1394_);
lean_dec_ref(v_dep_1392_);
v_a_1736_ = lean_ctor_get(v___x_1735_, 0);
v_isSharedCheck_1743_ = !lean_is_exclusive(v___x_1735_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1738_ = v___x_1735_;
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_a_1736_);
lean_dec(v___x_1735_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
lean_object* v___x_1741_; 
if (v_isShared_1739_ == 0)
{
v___x_1741_ = v___x_1738_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_a_1736_);
v___x_1741_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
return v___x_1741_;
}
}
}
}
}
}
v___jp_1745_:
{
lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; 
lean_inc(v_name_1434_);
v___x_1747_ = l_Lean_Name_toString(v_name_1434_, v___x_1744_);
v___x_1748_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
lean_inc_ref(v___x_1747_);
lean_inc_ref(v_scope_1435_);
lean_inc_ref(v_lakeEnv_1394_);
v___x_1749_ = l_Lake_Reservoir_fetchPkg_x3f(v_lakeEnv_1394_, v_scope_1435_, v___x_1747_, v___x_1748_);
if (lean_obj_tag(v___x_1749_) == 0)
{
lean_object* v_a_1750_; lean_object* v_a_1751_; lean_object* v___x_1752_; 
v_a_1750_ = lean_ctor_get(v___x_1749_, 0);
lean_inc(v_a_1750_);
v_a_1751_ = lean_ctor_get(v___x_1749_, 1);
lean_inc(v_a_1751_);
lean_dec_ref(v___x_1749_);
v___x_1752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1752_, 0, v_a_1750_);
v___y_1714_ = v_a_1746_;
v___y_1715_ = v___x_1747_;
v_fst_1716_ = v___x_1752_;
v_snd_1717_ = v_a_1751_;
goto v___jp_1713_;
}
else
{
lean_object* v_a_1753_; lean_object* v_a_1754_; lean_object* v___x_1755_; 
v_a_1753_ = lean_ctor_get(v___x_1749_, 0);
lean_inc(v_a_1753_);
v_a_1754_ = lean_ctor_get(v___x_1749_, 1);
lean_inc(v_a_1754_);
lean_dec_ref(v___x_1749_);
v___x_1755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1755_, 0, v_a_1753_);
v___y_1714_ = v_a_1746_;
v___y_1715_ = v___x_1747_;
v_fst_1716_ = v___x_1755_;
v_snd_1717_ = v_a_1754_;
goto v___jp_1713_;
}
}
}
v___jp_1400_:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___x_1401_ = lean_box(0);
v___x_1402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1402_, 0, v___x_1401_);
return v___x_1402_;
}
v___jp_1403_:
{
lean_object* v_fullName_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; uint8_t v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; 
v_fullName_1406_ = lean_ctor_get(v___y_1404_, 1);
lean_inc_ref(v_fullName_1406_);
lean_dec_ref(v___y_1404_);
v___x_1407_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__0));
v___x_1408_ = lean_string_append(v_fullName_1406_, v___x_1407_);
v___x_1409_ = 3;
v___x_1410_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1410_, 0, v___x_1408_);
lean_ctor_set_uint8(v___x_1410_, sizeof(void*)*1, v___x_1409_);
v___x_1411_ = lean_apply_2(v___y_1405_, v___x_1410_, lean_box(0));
v___x_1412_ = lean_box(0);
v___x_1413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1413_, 0, v___x_1412_);
return v___x_1413_;
}
v___jp_1414_:
{
lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1422_, 0, v___y_1417_);
v___x_1423_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit(v_dep_1392_, v_inherited_1393_, v_lakeEnv_1394_, v_wsDir_1395_, v___y_1416_, v___y_1420_, v___y_1418_, v___y_1421_, v___x_1422_, v___y_1415_, v___y_1419_);
lean_dec_ref(v_lakeEnv_1394_);
lean_dec_ref(v_dep_1392_);
return v___x_1423_;
}
v___jp_1424_:
{
if (lean_obj_tag(v___y_1428_) == 0)
{
lean_object* v___x_1432_; 
v___x_1432_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___y_1415_ = v___y_1425_;
v___y_1416_ = v___y_1426_;
v___y_1417_ = v_rev_x3f_1430_;
v___y_1418_ = v___y_1427_;
v___y_1419_ = v___y_1431_;
v___y_1420_ = v___y_1429_;
v___y_1421_ = v___x_1432_;
goto v___jp_1414_;
}
else
{
lean_object* v_val_1433_; 
v_val_1433_ = lean_ctor_get(v___y_1428_, 0);
lean_inc(v_val_1433_);
lean_dec_ref(v___y_1428_);
v___y_1415_ = v___y_1425_;
v___y_1416_ = v___y_1426_;
v___y_1417_ = v_rev_x3f_1430_;
v___y_1418_ = v___y_1427_;
v___y_1419_ = v___y_1431_;
v___y_1420_ = v___y_1429_;
v___y_1421_ = v_val_1433_;
goto v___jp_1414_;
}
}
v___jp_1438_:
{
lean_object* v_toString_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; uint8_t v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; 
v_toString_1441_ = lean_ctor_get(v___y_1439_, 0);
lean_inc_ref(v_toString_1441_);
lean_dec_ref(v___y_1439_);
v___x_1442_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
v___x_1443_ = lean_string_append(v_scope_1435_, v___x_1442_);
v___x_1444_ = lean_string_append(v___x_1443_, v___y_1440_);
lean_dec_ref(v___y_1440_);
v___x_1445_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__1));
v___x_1446_ = lean_string_append(v___x_1444_, v___x_1445_);
v___x_1447_ = lean_string_append(v___x_1446_, v_toString_1441_);
lean_dec_ref(v_toString_1441_);
v___x_1448_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__2));
v___x_1449_ = lean_string_append(v___x_1447_, v___x_1448_);
v___x_1450_ = 3;
v___x_1451_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1451_, 0, v___x_1449_);
lean_ctor_set_uint8(v___x_1451_, sizeof(void*)*1, v___x_1450_);
v___x_1452_ = lean_apply_2(v_a_1398_, v___x_1451_, lean_box(0));
v___x_1453_ = lean_box(0);
v___x_1454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1454_, 0, v___x_1453_);
return v___x_1454_;
}
v___jp_1455_:
{
if (lean_obj_tag(v_a_1463_) == 0)
{
lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1479_; 
lean_inc_ref(v_scope_1435_);
lean_dec_ref(v___y_1461_);
lean_dec_ref(v___y_1460_);
lean_dec(v___y_1459_);
lean_dec_ref(v___y_1458_);
lean_dec_ref(v___y_1457_);
lean_dec(v___y_1456_);
lean_dec_ref(v_wsDir_1395_);
lean_dec_ref(v_lakeEnv_1394_);
lean_dec_ref(v_dep_1392_);
v_isSharedCheck_1479_ = !lean_is_exclusive(v_a_1463_);
if (v_isSharedCheck_1479_ == 0)
{
lean_object* v_unused_1480_; 
v_unused_1480_ = lean_ctor_get(v_a_1463_, 0);
lean_dec(v_unused_1480_);
v___x_1465_ = v_a_1463_;
v_isShared_1466_ = v_isSharedCheck_1479_;
goto v_resetjp_1464_;
}
else
{
lean_dec(v_a_1463_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1479_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; uint8_t v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1477_; 
v___x_1467_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
v___x_1468_ = lean_string_append(v_scope_1435_, v___x_1467_);
v___x_1469_ = lean_string_append(v___x_1468_, v___y_1462_);
lean_dec_ref(v___y_1462_);
v___x_1470_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__3));
v___x_1471_ = lean_string_append(v___x_1469_, v___x_1470_);
v___x_1472_ = 3;
v___x_1473_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1473_, 0, v___x_1471_);
lean_ctor_set_uint8(v___x_1473_, sizeof(void*)*1, v___x_1472_);
v___x_1474_ = lean_apply_2(v_a_1398_, v___x_1473_, lean_box(0));
v___x_1475_ = lean_box(0);
if (v_isShared_1466_ == 0)
{
lean_ctor_set_tag(v___x_1465_, 1);
lean_ctor_set(v___x_1465_, 0, v___x_1475_);
v___x_1477_ = v___x_1465_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v___x_1475_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
return v___x_1477_;
}
}
}
else
{
lean_object* v_a_1481_; lean_object* v___x_1482_; size_t v_sz_1483_; size_t v___x_1484_; lean_object* v___x_1485_; lean_object* v_fst_1486_; 
v_a_1481_ = lean_ctor_get(v_a_1463_, 0);
lean_inc(v_a_1481_);
lean_dec_ref(v_a_1463_);
v___x_1482_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___closed__0));
v_sz_1483_ = lean_array_size(v_a_1481_);
v___x_1484_ = ((size_t)0ULL);
v___x_1485_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(v___y_1460_, v_a_1481_, v_sz_1483_, v___x_1484_, v___x_1482_);
lean_dec(v_a_1481_);
v_fst_1486_ = lean_ctor_get(v___x_1485_, 0);
lean_inc(v_fst_1486_);
lean_dec_ref(v___x_1485_);
if (lean_obj_tag(v_fst_1486_) == 0)
{
lean_inc_ref(v_scope_1435_);
lean_dec_ref(v___y_1461_);
lean_dec(v___y_1459_);
lean_dec_ref(v___y_1458_);
lean_dec_ref(v___y_1457_);
lean_dec(v___y_1456_);
lean_dec_ref(v_wsDir_1395_);
lean_dec_ref(v_lakeEnv_1394_);
lean_dec_ref(v_dep_1392_);
v___y_1439_ = v___y_1460_;
v___y_1440_ = v___y_1462_;
goto v___jp_1438_;
}
else
{
lean_object* v_val_1487_; 
v_val_1487_ = lean_ctor_get(v_fst_1486_, 0);
lean_inc(v_val_1487_);
lean_dec_ref(v_fst_1486_);
if (lean_obj_tag(v_val_1487_) == 1)
{
lean_object* v_val_1488_; lean_object* v_version_1489_; lean_object* v_revision_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; uint8_t v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; 
lean_dec_ref(v___y_1460_);
v_val_1488_ = lean_ctor_get(v_val_1487_, 0);
lean_inc(v_val_1488_);
lean_dec_ref(v_val_1487_);
v_version_1489_ = lean_ctor_get(v_val_1488_, 0);
lean_inc_ref(v_version_1489_);
v_revision_1490_ = lean_ctor_get(v_val_1488_, 1);
lean_inc_ref(v_revision_1490_);
lean_dec(v_val_1488_);
v___x_1491_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
lean_inc_ref(v_scope_1435_);
v___x_1492_ = lean_string_append(v_scope_1435_, v___x_1491_);
v___x_1493_ = lean_string_append(v___x_1492_, v___y_1462_);
lean_dec_ref(v___y_1462_);
v___x_1494_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__4));
v___x_1495_ = lean_string_append(v___x_1493_, v___x_1494_);
v___x_1496_ = l_Lake_StdVer_toString(v_version_1489_);
v___x_1497_ = lean_string_append(v___x_1495_, v___x_1496_);
lean_dec_ref(v___x_1496_);
v___x_1498_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__5));
v___x_1499_ = lean_string_append(v___x_1497_, v___x_1498_);
v___x_1500_ = lean_string_append(v___x_1499_, v_revision_1490_);
v___x_1501_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__6));
v___x_1502_ = lean_string_append(v___x_1500_, v___x_1501_);
v___x_1503_ = 1;
v___x_1504_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1504_, 0, v___x_1502_);
lean_ctor_set_uint8(v___x_1504_, sizeof(void*)*1, v___x_1503_);
lean_inc_ref(v_a_1398_);
v___x_1505_ = lean_apply_2(v_a_1398_, v___x_1504_, lean_box(0));
v___y_1425_ = v___y_1456_;
v___y_1426_ = v___y_1457_;
v___y_1427_ = v___y_1458_;
v___y_1428_ = v___y_1459_;
v___y_1429_ = v___y_1461_;
v_rev_x3f_1430_ = v_revision_1490_;
v___y_1431_ = v_a_1398_;
goto v___jp_1424_;
}
else
{
lean_inc_ref(v_scope_1435_);
lean_dec(v_val_1487_);
lean_dec_ref(v___y_1461_);
lean_dec(v___y_1459_);
lean_dec_ref(v___y_1458_);
lean_dec_ref(v___y_1457_);
lean_dec(v___y_1456_);
lean_dec_ref(v_wsDir_1395_);
lean_dec_ref(v_lakeEnv_1394_);
lean_dec_ref(v_dep_1392_);
v___y_1439_ = v___y_1460_;
v___y_1440_ = v___y_1462_;
goto v___jp_1438_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize___boxed(lean_object* v_dep_1804_, lean_object* v_inherited_1805_, lean_object* v_lakeEnv_1806_, lean_object* v_wsDir_1807_, lean_object* v_relPkgsDir_1808_, lean_object* v_relParentDir_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_){
_start:
{
uint8_t v_inherited_boxed_1812_; lean_object* v_res_1813_; 
v_inherited_boxed_1812_ = lean_unbox(v_inherited_1805_);
v_res_1813_ = l_Lake_Dependency_materialize(v_dep_1804_, v_inherited_boxed_1812_, v_lakeEnv_1806_, v_wsDir_1807_, v_relPkgsDir_1808_, v_relParentDir_1809_, v_a_1810_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep(lean_object* v_manifestEntry_1814_, lean_object* v_relPkgDir_1815_, lean_object* v_remoteUrl_1816_){
_start:
{
lean_object* v___x_1817_; 
v___x_1817_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1817_, 0, v_relPkgDir_1815_);
lean_ctor_set(v___x_1817_, 1, v_remoteUrl_1816_);
lean_ctor_set(v___x_1817_, 2, v_manifestEntry_1814_);
return v___x_1817_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize(lean_object* v_manifestEntry_1819_, lean_object* v_lakeEnv_1820_, lean_object* v_wsDir_1821_, lean_object* v_relPkgsDir_1822_, lean_object* v_a_1823_){
_start:
{
lean_object* v___y_1826_; lean_object* v___y_1827_; lean_object* v_src_1830_; 
v_src_1830_ = lean_ctor_get(v_manifestEntry_1819_, 4);
lean_inc_ref(v_src_1830_);
if (lean_obj_tag(v_src_1830_) == 0)
{
lean_object* v_dir_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1840_; 
lean_dec_ref(v_a_1823_);
lean_dec_ref(v_relPkgsDir_1822_);
lean_dec_ref(v_wsDir_1821_);
v_dir_1831_ = lean_ctor_get(v_src_1830_, 0);
v_isSharedCheck_1840_ = !lean_is_exclusive(v_src_1830_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1833_ = v_src_1830_;
v_isShared_1834_ = v_isSharedCheck_1840_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_dir_1831_);
lean_dec(v_src_1830_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1840_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1838_; 
v___x_1835_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___x_1836_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1836_, 0, v_dir_1831_);
lean_ctor_set(v___x_1836_, 1, v___x_1835_);
lean_ctor_set(v___x_1836_, 2, v_manifestEntry_1819_);
if (v_isShared_1834_ == 0)
{
lean_ctor_set(v___x_1833_, 0, v___x_1836_);
v___x_1838_ = v___x_1833_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v___x_1836_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
return v___x_1838_;
}
}
}
else
{
lean_object* v_name_1841_; lean_object* v_url_1842_; lean_object* v_rev_1843_; lean_object* v_subDir_x3f_1844_; lean_object* v___y_1846_; uint8_t v___x_1850_; lean_object* v_sname_1851_; lean_object* v_relGitDir_1852_; lean_object* v_gitDir_1856_; lean_object* v___y_1858_; lean_object* v___y_1859_; lean_object* v___y_1870_; uint8_t v_a_1882_; lean_object* v___y_1892_; lean_object* v___y_1893_; uint8_t v_val_1894_; uint8_t v___y_1922_; lean_object* v_a_1923_; uint8_t v___x_1933_; lean_object* v___x_1966_; uint8_t v___x_1967_; 
v_name_1841_ = lean_ctor_get(v_manifestEntry_1819_, 0);
v_url_1842_ = lean_ctor_get(v_src_1830_, 0);
lean_inc_ref(v_url_1842_);
v_rev_1843_ = lean_ctor_get(v_src_1830_, 1);
lean_inc_ref(v_rev_1843_);
v_subDir_x3f_1844_ = lean_ctor_get(v_src_1830_, 3);
lean_inc(v_subDir_x3f_1844_);
lean_dec_ref(v_src_1830_);
v___x_1850_ = 0;
lean_inc(v_name_1841_);
v_sname_1851_ = l_Lean_Name_toString(v_name_1841_, v___x_1850_);
lean_inc_ref(v_sname_1851_);
v_relGitDir_1852_ = l_Lake_joinRelative(v_relPkgsDir_1822_, v_sname_1851_);
lean_inc_ref(v_relGitDir_1852_);
v_gitDir_1856_ = l_Lake_joinRelative(v_wsDir_1821_, v_relGitDir_1852_);
v___x_1933_ = l_System_FilePath_isDir(v_gitDir_1856_);
v___x_1966_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
v___x_1967_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_1967_ == 0)
{
goto v___jp_1934_;
}
else
{
lean_object* v___x_1968_; uint8_t v___x_1969_; 
v___x_1968_ = lean_box(0);
v___x_1969_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_1969_ == 0)
{
if (v___x_1967_ == 0)
{
goto v___jp_1934_;
}
else
{
size_t v___x_1970_; size_t v___x_1971_; lean_object* v___x_1972_; 
v___x_1970_ = ((size_t)0ULL);
v___x_1971_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
lean_inc_ref(v_a_1823_);
v___x_1972_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v___x_1966_, v___x_1970_, v___x_1971_, v___x_1968_, v_a_1823_);
if (lean_obj_tag(v___x_1972_) == 0)
{
lean_dec_ref(v___x_1972_);
goto v___jp_1934_;
}
else
{
lean_object* v_a_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1980_; 
lean_dec_ref(v_gitDir_1856_);
lean_dec_ref(v_relGitDir_1852_);
lean_dec_ref(v_sname_1851_);
lean_dec(v_subDir_x3f_1844_);
lean_dec_ref(v_rev_1843_);
lean_dec_ref(v_url_1842_);
lean_dec_ref(v_a_1823_);
lean_dec_ref(v_manifestEntry_1819_);
v_a_1973_ = lean_ctor_get(v___x_1972_, 0);
v_isSharedCheck_1980_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1975_ = v___x_1972_;
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_a_1973_);
lean_dec(v___x_1972_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___x_1978_; 
if (v_isShared_1976_ == 0)
{
v___x_1978_ = v___x_1975_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v_a_1973_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
return v___x_1978_;
}
}
}
}
}
else
{
size_t v___x_1981_; size_t v___x_1982_; lean_object* v___x_1983_; 
v___x_1981_ = ((size_t)0ULL);
v___x_1982_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
lean_inc_ref(v_a_1823_);
v___x_1983_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v___x_1966_, v___x_1981_, v___x_1982_, v___x_1968_, v_a_1823_);
if (lean_obj_tag(v___x_1983_) == 0)
{
lean_dec_ref(v___x_1983_);
goto v___jp_1934_;
}
else
{
lean_object* v_a_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1991_; 
lean_dec_ref(v_gitDir_1856_);
lean_dec_ref(v_relGitDir_1852_);
lean_dec_ref(v_sname_1851_);
lean_dec(v_subDir_x3f_1844_);
lean_dec_ref(v_rev_1843_);
lean_dec_ref(v_url_1842_);
lean_dec_ref(v_a_1823_);
lean_dec_ref(v_manifestEntry_1819_);
v_a_1984_ = lean_ctor_get(v___x_1983_, 0);
v_isSharedCheck_1991_ = !lean_is_exclusive(v___x_1983_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1986_ = v___x_1983_;
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_a_1984_);
lean_dec(v___x_1983_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v___x_1989_; 
if (v_isShared_1987_ == 0)
{
v___x_1989_ = v___x_1986_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_a_1984_);
v___x_1989_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
return v___x_1989_;
}
}
}
}
}
v___jp_1845_:
{
lean_object* v___x_1847_; 
v___x_1847_ = l_Lake_Git_filterUrl_x3f(v_url_1842_);
if (lean_obj_tag(v___x_1847_) == 0)
{
lean_object* v___x_1848_; 
v___x_1848_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___y_1826_ = v___y_1846_;
v___y_1827_ = v___x_1848_;
goto v___jp_1825_;
}
else
{
lean_object* v_val_1849_; 
v_val_1849_ = lean_ctor_get(v___x_1847_, 0);
lean_inc(v_val_1849_);
lean_dec_ref(v___x_1847_);
v___y_1826_ = v___y_1846_;
v___y_1827_ = v_val_1849_;
goto v___jp_1825_;
}
}
v___jp_1853_:
{
if (lean_obj_tag(v_subDir_x3f_1844_) == 0)
{
v___y_1846_ = v_relGitDir_1852_;
goto v___jp_1845_;
}
else
{
lean_object* v_val_1854_; lean_object* v___x_1855_; 
v_val_1854_ = lean_ctor_get(v_subDir_x3f_1844_, 0);
lean_inc(v_val_1854_);
lean_dec_ref(v_subDir_x3f_1844_);
v___x_1855_ = l_Lake_joinRelative(v_relGitDir_1852_, v_val_1854_);
v___y_1846_ = v___x_1855_;
goto v___jp_1845_;
}
}
v___jp_1857_:
{
lean_object* v___x_1860_; 
v___x_1860_ = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1823_, v_sname_1851_, v_gitDir_1856_, v___y_1859_, v___y_1858_);
if (lean_obj_tag(v___x_1860_) == 0)
{
lean_dec_ref(v___x_1860_);
goto v___jp_1853_;
}
else
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1868_; 
lean_dec_ref(v_relGitDir_1852_);
lean_dec(v_subDir_x3f_1844_);
lean_dec_ref(v_url_1842_);
lean_dec_ref(v_manifestEntry_1819_);
v_a_1861_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1863_ = v___x_1860_;
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1860_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1866_; 
if (v_isShared_1864_ == 0)
{
v___x_1866_ = v___x_1863_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_a_1861_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
}
}
v___jp_1869_:
{
lean_object* v___x_1871_; lean_object* v___x_1872_; 
v___x_1871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1871_, 0, v_rev_1843_);
v___x_1872_ = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(v_a_1823_, v_sname_1851_, v_gitDir_1856_, v___y_1870_, v___x_1871_);
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_dec_ref(v___x_1872_);
goto v___jp_1853_;
}
else
{
lean_object* v_a_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1880_; 
lean_dec_ref(v_relGitDir_1852_);
lean_dec(v_subDir_x3f_1844_);
lean_dec_ref(v_url_1842_);
lean_dec_ref(v_manifestEntry_1819_);
v_a_1873_ = lean_ctor_get(v___x_1872_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1875_ = v___x_1872_;
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_a_1873_);
lean_dec(v___x_1872_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1878_; 
if (v_isShared_1876_ == 0)
{
v___x_1878_ = v___x_1875_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_a_1873_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
}
}
v___jp_1881_:
{
if (v_a_1882_ == 0)
{
lean_dec_ref(v_gitDir_1856_);
lean_dec_ref(v_sname_1851_);
lean_dec_ref(v_a_1823_);
goto v___jp_1853_;
}
else
{
lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; uint8_t v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; 
v___x_1883_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0));
v___x_1884_ = lean_string_append(v_sname_1851_, v___x_1883_);
v___x_1885_ = lean_string_append(v___x_1884_, v_gitDir_1856_);
lean_dec_ref(v_gitDir_1856_);
v___x_1886_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1));
v___x_1887_ = lean_string_append(v___x_1885_, v___x_1886_);
v___x_1888_ = 2;
v___x_1889_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1889_, 0, v___x_1887_);
lean_ctor_set_uint8(v___x_1889_, sizeof(void*)*1, v___x_1888_);
v___x_1890_ = lean_apply_2(v_a_1823_, v___x_1889_, lean_box(0));
goto v___jp_1853_;
}
}
v___jp_1891_:
{
lean_object* v___x_1895_; uint8_t v___x_1896_; 
v___x_1895_ = lean_array_get_size(v___y_1892_);
v___x_1896_ = lean_nat_dec_lt(v___y_1893_, v___x_1895_);
if (v___x_1896_ == 0)
{
lean_dec_ref(v___y_1892_);
v_a_1882_ = v_val_1894_;
goto v___jp_1881_;
}
else
{
lean_object* v___x_1897_; uint8_t v___x_1898_; 
v___x_1897_ = lean_box(0);
v___x_1898_ = lean_nat_dec_le(v___x_1895_, v___x_1895_);
if (v___x_1898_ == 0)
{
if (v___x_1896_ == 0)
{
lean_dec_ref(v___y_1892_);
v_a_1882_ = v_val_1894_;
goto v___jp_1881_;
}
else
{
size_t v___x_1899_; size_t v___x_1900_; lean_object* v___x_1901_; 
v___x_1899_ = ((size_t)0ULL);
v___x_1900_ = lean_usize_of_nat(v___x_1895_);
lean_inc_ref(v_a_1823_);
v___x_1901_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v___y_1892_, v___x_1899_, v___x_1900_, v___x_1897_, v_a_1823_);
lean_dec_ref(v___y_1892_);
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_dec_ref(v___x_1901_);
v_a_1882_ = v_val_1894_;
goto v___jp_1881_;
}
else
{
lean_object* v_a_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1909_; 
lean_dec_ref(v_gitDir_1856_);
lean_dec_ref(v_relGitDir_1852_);
lean_dec_ref(v_sname_1851_);
lean_dec(v_subDir_x3f_1844_);
lean_dec_ref(v_url_1842_);
lean_dec_ref(v_a_1823_);
lean_dec_ref(v_manifestEntry_1819_);
v_a_1902_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_1909_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1904_ = v___x_1901_;
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_a_1902_);
lean_dec(v___x_1901_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___x_1907_; 
if (v_isShared_1905_ == 0)
{
v___x_1907_ = v___x_1904_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_a_1902_);
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
}
else
{
size_t v___x_1910_; size_t v___x_1911_; lean_object* v___x_1912_; 
v___x_1910_ = ((size_t)0ULL);
v___x_1911_ = lean_usize_of_nat(v___x_1895_);
lean_inc_ref(v_a_1823_);
v___x_1912_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v___y_1892_, v___x_1910_, v___x_1911_, v___x_1897_, v_a_1823_);
lean_dec_ref(v___y_1892_);
if (lean_obj_tag(v___x_1912_) == 0)
{
lean_dec_ref(v___x_1912_);
v_a_1882_ = v_val_1894_;
goto v___jp_1881_;
}
else
{
lean_object* v_a_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1920_; 
lean_dec_ref(v_gitDir_1856_);
lean_dec_ref(v_relGitDir_1852_);
lean_dec_ref(v_sname_1851_);
lean_dec(v_subDir_x3f_1844_);
lean_dec_ref(v_url_1842_);
lean_dec_ref(v_a_1823_);
lean_dec_ref(v_manifestEntry_1819_);
v_a_1913_ = lean_ctor_get(v___x_1912_, 0);
v_isSharedCheck_1920_ = !lean_is_exclusive(v___x_1912_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1915_ = v___x_1912_;
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_a_1913_);
lean_dec(v___x_1912_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v___x_1918_; 
if (v_isShared_1916_ == 0)
{
v___x_1918_ = v___x_1915_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_a_1913_);
v___x_1918_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
return v___x_1918_;
}
}
}
}
}
}
v___jp_1921_:
{
lean_object* v___x_1924_; lean_object* v___x_1925_; uint8_t v___x_1926_; 
v___x_1924_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
v___x_1925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1925_, 0, v_rev_1843_);
lean_inc_ref(v___x_1925_);
v___x_1926_ = l_Option_instDecidableEq___redArg(v___x_1924_, v_a_1923_, v___x_1925_);
if (v___x_1926_ == 0)
{
lean_object* v_pkgUrlMap_1927_; lean_object* v___x_1928_; 
v_pkgUrlMap_1927_ = lean_ctor_get(v_lakeEnv_1820_, 5);
v___x_1928_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgUrlMap_1927_, v_name_1841_);
if (lean_obj_tag(v___x_1928_) == 0)
{
lean_inc_ref(v_url_1842_);
v___y_1858_ = v___x_1925_;
v___y_1859_ = v_url_1842_;
goto v___jp_1857_;
}
else
{
lean_object* v_val_1929_; 
v_val_1929_ = lean_ctor_get(v___x_1928_, 0);
lean_inc(v_val_1929_);
lean_dec_ref(v___x_1928_);
v___y_1858_ = v___x_1925_;
v___y_1859_ = v_val_1929_;
goto v___jp_1857_;
}
}
else
{
uint8_t v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
lean_dec_ref(v___x_1925_);
lean_inc_ref(v_gitDir_1856_);
v___x_1930_ = l_Lake_GitRepo_hasNoDiff(v_gitDir_1856_);
v___x_1931_ = lean_unsigned_to_nat(0u);
v___x_1932_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
if (v___x_1930_ == 0)
{
v___y_1892_ = v___x_1932_;
v___y_1893_ = v___x_1931_;
v_val_1894_ = v___y_1922_;
goto v___jp_1891_;
}
else
{
v___y_1892_ = v___x_1932_;
v___y_1893_ = v___x_1931_;
v_val_1894_ = v___x_1850_;
goto v___jp_1891_;
}
}
}
v___jp_1934_:
{
if (v___x_1933_ == 0)
{
lean_object* v_pkgUrlMap_1935_; lean_object* v___x_1936_; 
v_pkgUrlMap_1935_ = lean_ctor_get(v_lakeEnv_1820_, 5);
v___x_1936_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgUrlMap_1935_, v_name_1841_);
if (lean_obj_tag(v___x_1936_) == 0)
{
lean_inc_ref(v_url_1842_);
v___y_1870_ = v_url_1842_;
goto v___jp_1869_;
}
else
{
lean_object* v_val_1937_; 
v_val_1937_ = lean_ctor_get(v___x_1936_, 0);
lean_inc(v_val_1937_);
lean_dec_ref(v___x_1936_);
v___y_1870_ = v_val_1937_;
goto v___jp_1869_;
}
}
else
{
lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; uint8_t v___x_1941_; 
v___x_1938_ = ((lean_object*)(l_Lake_PackageEntry_materialize___closed__0));
lean_inc_ref(v_gitDir_1856_);
v___x_1939_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_1938_, v_gitDir_1856_);
v___x_1940_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
v___x_1941_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_1941_ == 0)
{
v___y_1922_ = v___x_1933_;
v_a_1923_ = v___x_1939_;
goto v___jp_1921_;
}
else
{
lean_object* v___x_1942_; uint8_t v___x_1943_; 
v___x_1942_ = lean_box(0);
v___x_1943_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_1943_ == 0)
{
if (v___x_1941_ == 0)
{
v___y_1922_ = v___x_1933_;
v_a_1923_ = v___x_1939_;
goto v___jp_1921_;
}
else
{
size_t v___x_1944_; size_t v___x_1945_; lean_object* v___x_1946_; 
v___x_1944_ = ((size_t)0ULL);
v___x_1945_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
lean_inc_ref(v_a_1823_);
v___x_1946_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v___x_1940_, v___x_1944_, v___x_1945_, v___x_1942_, v_a_1823_);
if (lean_obj_tag(v___x_1946_) == 0)
{
lean_dec_ref(v___x_1946_);
v___y_1922_ = v___x_1933_;
v_a_1923_ = v___x_1939_;
goto v___jp_1921_;
}
else
{
lean_object* v_a_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1954_; 
lean_dec(v___x_1939_);
lean_dec_ref(v_gitDir_1856_);
lean_dec_ref(v_relGitDir_1852_);
lean_dec_ref(v_sname_1851_);
lean_dec(v_subDir_x3f_1844_);
lean_dec_ref(v_rev_1843_);
lean_dec_ref(v_url_1842_);
lean_dec_ref(v_a_1823_);
lean_dec_ref(v_manifestEntry_1819_);
v_a_1947_ = lean_ctor_get(v___x_1946_, 0);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___x_1946_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1949_ = v___x_1946_;
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_a_1947_);
lean_dec(v___x_1946_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___x_1952_; 
if (v_isShared_1950_ == 0)
{
v___x_1952_ = v___x_1949_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_a_1947_);
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
}
else
{
size_t v___x_1955_; size_t v___x_1956_; lean_object* v___x_1957_; 
v___x_1955_ = ((size_t)0ULL);
v___x_1956_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
lean_inc_ref(v_a_1823_);
v___x_1957_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v___x_1940_, v___x_1955_, v___x_1956_, v___x_1942_, v_a_1823_);
if (lean_obj_tag(v___x_1957_) == 0)
{
lean_dec_ref(v___x_1957_);
v___y_1922_ = v___x_1933_;
v_a_1923_ = v___x_1939_;
goto v___jp_1921_;
}
else
{
lean_object* v_a_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1965_; 
lean_dec(v___x_1939_);
lean_dec_ref(v_gitDir_1856_);
lean_dec_ref(v_relGitDir_1852_);
lean_dec_ref(v_sname_1851_);
lean_dec(v_subDir_x3f_1844_);
lean_dec_ref(v_rev_1843_);
lean_dec_ref(v_url_1842_);
lean_dec_ref(v_a_1823_);
lean_dec_ref(v_manifestEntry_1819_);
v_a_1958_ = lean_ctor_get(v___x_1957_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1957_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1960_ = v___x_1957_;
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_a_1958_);
lean_dec(v___x_1957_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v___x_1963_; 
if (v_isShared_1961_ == 0)
{
v___x_1963_ = v___x_1960_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_a_1958_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
return v___x_1963_;
}
}
}
}
}
}
}
}
v___jp_1825_:
{
lean_object* v___x_1828_; lean_object* v___x_1829_; 
v___x_1828_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1828_, 0, v___y_1826_);
lean_ctor_set(v___x_1828_, 1, v___y_1827_);
lean_ctor_set(v___x_1828_, 2, v_manifestEntry_1819_);
v___x_1829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1828_);
return v___x_1829_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize___boxed(lean_object* v_manifestEntry_1992_, lean_object* v_lakeEnv_1993_, lean_object* v_wsDir_1994_, lean_object* v_relPkgsDir_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_){
_start:
{
lean_object* v_res_1998_; 
v_res_1998_ = l_Lake_PackageEntry_materialize(v_manifestEntry_1992_, v_lakeEnv_1993_, v_wsDir_1994_, v_relPkgsDir_1995_, v_a_1996_);
lean_dec_ref(v_lakeEnv_1993_);
return v_res_1998_;
}
}
lean_object* runtime_initialize_Lake_Config_Env(uint8_t builtin);
lean_object* runtime_initialize_Lake_Load_Manifest(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Package(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Git(uint8_t builtin);
lean_object* runtime_initialize_Lake_Reservoir(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Load_Materialize(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lake_Config_Env(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Load_Manifest(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Git(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Reservoir(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instInhabitedMaterializedDep_default = _init_l_Lake_instInhabitedMaterializedDep_default();
lean_mark_persistent(l_Lake_instInhabitedMaterializedDep_default);
l_Lake_instInhabitedMaterializedDep = _init_l_Lake_instInhabitedMaterializedDep();
lean_mark_persistent(l_Lake_instInhabitedMaterializedDep);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Load_Materialize(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Config_Env(uint8_t builtin);
lean_object* initialize_Lake_Load_Manifest(uint8_t builtin);
lean_object* initialize_Lake_Config_Package(uint8_t builtin);
lean_object* initialize_Lake_Util_Git(uint8_t builtin);
lean_object* initialize_Lake_Reservoir(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Load_Materialize(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Config_Env(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Manifest(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Git(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Reservoir(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Load_Materialize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Load_Materialize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Load_Materialize(builtin);
}
#ifdef __cplusplus
}
#endif

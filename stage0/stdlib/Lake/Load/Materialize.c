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
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4_value;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_checkoutDetach(lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_GitRepo_hasNoDiff(lean_object*);
extern lean_object* l_Lake_Git_defaultRemote;
lean_object* l_Lake_GitRepo_findRemoteRevision(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_getHeadRevision(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = ": cloning "};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___closed__0 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___closed__0_value;
lean_object* l_Lake_GitRepo_resolveRemoteRevision(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_clone(lean_object*, lean_object*, lean_object*);
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
extern uint8_t l_System_Platform_isWindows;
lean_object* l_IO_FS_removeDirAll(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lake_GitRepo_getRemoteUrl_x3f(lean_object*, lean_object*);
lean_object* lean_io_realpath(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_System_FilePath_isDir(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_instInhabitedMaterializedDep_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_instInhabitedMaterializedDep_default___closed__0 = (const lean_object*)&l_Lake_instInhabitedMaterializedDep_default___closed__0_value;
extern lean_object* l_Lake_instInhabitedPackageEntry_default;
extern lean_object* l_System_instInhabitedFilePath_default;
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
lean_object* l_String_quote(lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_defaultConfigFile;
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "git#"};
static const lean_object* l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__0 = (const lean_object*)&l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__0_value;
lean_object* lean_string_utf8_byte_size(lean_object*);
static lean_once_cell_t l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__1;
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___closed__0_value;
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t l_Lake_VerRange_test(lean_object*, lean_object*);
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
lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM(lean_object*, lean_object*);
static const lean_closure_object l_Lake_Dependency_materialize___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Util_Version_0__Lake_VerRange_parseM, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Dependency_materialize___closed__8 = (const lean_object*)&l_Lake_Dependency_materialize___closed__8_value;
static const lean_string_object l_Lake_Dependency_materialize___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = ": invalid dependency version range: "};
static const lean_object* l_Lake_Dependency_materialize___closed__9 = (const lean_object*)&l_Lake_Dependency_materialize___closed__9_value;
static const lean_string_object l_Lake_Dependency_materialize___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 93, .m_capacity = 93, .m_length = 92, .m_data = ": ill-formed dependency: dependency is missing a source and is missing a scope for Reservoir"};
static const lean_object* l_Lake_Dependency_materialize___closed__10 = (const lean_object*)&l_Lake_Dependency_materialize___closed__10_value;
size_t lean_array_size(lean_object*);
lean_object* l_Lake_StdVer_toString(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lake_Git_filterUrl_x3f(lean_object*);
lean_object* l_Lake_RegistryPkg_gitSrc_x3f(lean_object*);
lean_object* l_Lake_Reservoir_fetchPkgVersions(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lake_Reservoir_fetchPkg_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* l___private_Lake_Util_Version_0__Lake_runVerParse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_PackageEntry_materialize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HEAD"};
static const lean_object* l_Lake_PackageEntry_materialize___closed__0 = (const lean_object*)&l_Lake_PackageEntry_materialize___closed__0_value;
lean_object* l_instDecidableEqString___boxed(lean_object*, lean_object*);
uint8_t l_Option_instDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_resolveRevision_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_2(x_2, x_1, lean_box(0));
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_2(x_1, x_2, lean_box(0));
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1_spec__1___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_array_uget_borrowed(x_1, x_2);
lean_inc(x_8);
lean_inc_ref(x_5);
x_9 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1_spec__1___redArg(x_5, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; size_t x_11; size_t x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_2 = x_12;
x_4 = x_10;
goto _start;
}
else
{
lean_dec_ref(x_5);
return x_9;
}
}
else
{
lean_object* x_14; 
lean_dec_ref(x_5);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_4);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_1, x_7, x_8, x_4, x_5);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_6; lean_object* x_7; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_35; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_102; lean_object* x_106; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_110 = l_Lake_Git_defaultRemote;
x_111 = lean_unsigned_to_nat(0u);
x_112 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
lean_inc_ref(x_2);
x_113 = l_Lake_GitRepo_findRemoteRevision(x_2, x_3, x_110, x_112);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_144; uint8_t x_145; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec_ref(x_113);
x_144 = lean_array_get_size(x_115);
x_145 = lean_nat_dec_lt(x_111, x_144);
if (x_145 == 0)
{
lean_dec(x_115);
x_116 = lean_box(0);
goto block_143;
}
else
{
lean_object* x_146; uint8_t x_147; 
x_146 = lean_box(0);
x_147 = lean_nat_dec_le(x_144, x_144);
if (x_147 == 0)
{
if (x_145 == 0)
{
lean_dec(x_115);
x_116 = lean_box(0);
goto block_143;
}
else
{
size_t x_148; size_t x_149; lean_object* x_150; 
x_148 = 0;
x_149 = lean_usize_of_nat(x_144);
lean_inc_ref(x_4);
x_150 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_115, x_148, x_149, x_146, x_4);
lean_dec(x_115);
if (lean_obj_tag(x_150) == 0)
{
lean_dec_ref(x_150);
x_116 = lean_box(0);
goto block_143;
}
else
{
lean_dec(x_114);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_150;
}
}
}
else
{
size_t x_151; size_t x_152; lean_object* x_153; 
x_151 = 0;
x_152 = lean_usize_of_nat(x_144);
lean_inc_ref(x_4);
x_153 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_115, x_151, x_152, x_146, x_4);
lean_dec(x_115);
if (lean_obj_tag(x_153) == 0)
{
lean_dec_ref(x_153);
x_116 = lean_box(0);
goto block_143;
}
else
{
lean_dec(x_114);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_153;
}
}
}
block_143:
{
lean_object* x_117; 
lean_inc_ref(x_2);
x_117 = l_Lake_GitRepo_getHeadRevision(x_2, x_112);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec_ref(x_117);
x_120 = lean_array_get_size(x_119);
x_121 = lean_nat_dec_lt(x_111, x_120);
if (x_121 == 0)
{
lean_dec(x_119);
x_39 = x_114;
x_40 = x_118;
x_41 = lean_box(0);
goto block_101;
}
else
{
lean_object* x_122; uint8_t x_123; 
x_122 = lean_box(0);
x_123 = lean_nat_dec_le(x_120, x_120);
if (x_123 == 0)
{
if (x_121 == 0)
{
lean_dec(x_119);
x_39 = x_114;
x_40 = x_118;
x_41 = lean_box(0);
goto block_101;
}
else
{
size_t x_124; size_t x_125; lean_object* x_126; 
x_124 = 0;
x_125 = lean_usize_of_nat(x_120);
lean_inc_ref(x_4);
x_126 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_119, x_124, x_125, x_122, x_4);
lean_dec(x_119);
if (lean_obj_tag(x_126) == 0)
{
lean_dec_ref(x_126);
x_39 = x_114;
x_40 = x_118;
x_41 = lean_box(0);
goto block_101;
}
else
{
lean_dec(x_118);
lean_dec(x_114);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_126;
}
}
}
else
{
size_t x_127; size_t x_128; lean_object* x_129; 
x_127 = 0;
x_128 = lean_usize_of_nat(x_120);
lean_inc_ref(x_4);
x_129 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_119, x_127, x_128, x_122, x_4);
lean_dec(x_119);
if (lean_obj_tag(x_129) == 0)
{
lean_dec_ref(x_129);
x_39 = x_114;
x_40 = x_118;
x_41 = lean_box(0);
goto block_101;
}
else
{
lean_dec(x_118);
lean_dec(x_114);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_129;
}
}
}
}
else
{
lean_object* x_130; lean_object* x_131; uint8_t x_132; 
lean_dec(x_114);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_130 = lean_ctor_get(x_117, 1);
lean_inc(x_130);
lean_dec_ref(x_117);
x_131 = lean_array_get_size(x_130);
x_132 = lean_nat_dec_lt(x_111, x_131);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; 
lean_dec(x_130);
lean_dec_ref(x_4);
x_133 = lean_box(0);
x_134 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_134, 0, x_133);
return x_134;
}
else
{
lean_object* x_135; uint8_t x_136; 
x_135 = lean_box(0);
x_136 = lean_nat_dec_le(x_131, x_131);
if (x_136 == 0)
{
if (x_132 == 0)
{
lean_dec(x_130);
lean_dec_ref(x_4);
x_102 = lean_box(0);
goto block_105;
}
else
{
size_t x_137; size_t x_138; lean_object* x_139; 
x_137 = 0;
x_138 = lean_usize_of_nat(x_131);
x_139 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_130, x_137, x_138, x_135, x_4);
lean_dec(x_130);
if (lean_obj_tag(x_139) == 0)
{
lean_dec_ref(x_139);
x_102 = lean_box(0);
goto block_105;
}
else
{
return x_139;
}
}
}
else
{
size_t x_140; size_t x_141; lean_object* x_142; 
x_140 = 0;
x_141 = lean_usize_of_nat(x_131);
x_142 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_130, x_140, x_141, x_135, x_4);
lean_dec(x_130);
if (lean_obj_tag(x_142) == 0)
{
lean_dec_ref(x_142);
x_102 = lean_box(0);
goto block_105;
}
else
{
return x_142;
}
}
}
}
}
}
else
{
lean_object* x_154; lean_object* x_155; uint8_t x_156; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_154 = lean_ctor_get(x_113, 1);
lean_inc(x_154);
lean_dec_ref(x_113);
x_155 = lean_array_get_size(x_154);
x_156 = lean_nat_dec_lt(x_111, x_155);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; 
lean_dec(x_154);
lean_dec_ref(x_4);
x_157 = lean_box(0);
x_158 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_158, 0, x_157);
return x_158;
}
else
{
lean_object* x_159; uint8_t x_160; 
x_159 = lean_box(0);
x_160 = lean_nat_dec_le(x_155, x_155);
if (x_160 == 0)
{
if (x_156 == 0)
{
lean_dec(x_154);
lean_dec_ref(x_4);
x_106 = lean_box(0);
goto block_109;
}
else
{
size_t x_161; size_t x_162; lean_object* x_163; 
x_161 = 0;
x_162 = lean_usize_of_nat(x_155);
x_163 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_154, x_161, x_162, x_159, x_4);
lean_dec(x_154);
if (lean_obj_tag(x_163) == 0)
{
lean_dec_ref(x_163);
x_106 = lean_box(0);
goto block_109;
}
else
{
return x_163;
}
}
}
else
{
size_t x_164; size_t x_165; lean_object* x_166; 
x_164 = 0;
x_165 = lean_usize_of_nat(x_155);
x_166 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_154, x_164, x_165, x_159, x_4);
lean_dec(x_154);
if (lean_obj_tag(x_166) == 0)
{
lean_dec_ref(x_166);
x_106 = lean_box(0);
goto block_109;
}
else
{
return x_166;
}
}
}
}
block_19:
{
if (x_6 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0));
x_11 = lean_string_append(x_1, x_10);
x_12 = lean_string_append(x_11, x_2);
lean_dec_ref(x_2);
x_13 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1));
x_14 = lean_string_append(x_12, x_13);
x_15 = 2;
x_16 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_15);
x_17 = lean_apply_2(x_4, x_16, lean_box(0));
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
block_34:
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_array_get_size(x_21);
x_25 = lean_nat_dec_lt(x_20, x_24);
if (x_25 == 0)
{
lean_dec_ref(x_21);
x_6 = x_22;
x_7 = lean_box(0);
goto block_19;
}
else
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_box(0);
x_27 = lean_nat_dec_le(x_24, x_24);
if (x_27 == 0)
{
if (x_25 == 0)
{
lean_dec_ref(x_21);
x_6 = x_22;
x_7 = lean_box(0);
goto block_19;
}
else
{
size_t x_28; size_t x_29; lean_object* x_30; 
x_28 = 0;
x_29 = lean_usize_of_nat(x_24);
lean_inc_ref(x_4);
x_30 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_21, x_28, x_29, x_26, x_4);
lean_dec_ref(x_21);
if (lean_obj_tag(x_30) == 0)
{
lean_dec_ref(x_30);
x_6 = x_22;
x_7 = lean_box(0);
goto block_19;
}
else
{
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_30;
}
}
}
else
{
size_t x_31; size_t x_32; lean_object* x_33; 
x_31 = 0;
x_32 = lean_usize_of_nat(x_24);
lean_inc_ref(x_4);
x_33 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_21, x_31, x_32, x_26, x_4);
lean_dec_ref(x_21);
if (lean_obj_tag(x_33) == 0)
{
lean_dec_ref(x_33);
x_6 = x_22;
x_7 = lean_box(0);
goto block_19;
}
else
{
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_33;
}
}
}
}
block_38:
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
block_101:
{
uint8_t x_42; 
x_42 = lean_string_dec_eq(x_40, x_39);
lean_dec_ref(x_40);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_43 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
x_44 = lean_string_append(x_1, x_43);
x_45 = lean_string_append(x_44, x_39);
x_46 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3));
x_47 = lean_string_append(x_45, x_46);
x_48 = 1;
x_49 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set_uint8(x_49, sizeof(void*)*1, x_48);
lean_inc_ref(x_4);
x_50 = lean_apply_2(x_4, x_49, lean_box(0));
x_51 = lean_unsigned_to_nat(0u);
x_52 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
x_53 = l_Lake_GitRepo_checkoutDetach(x_39, x_2, x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec_ref(x_53);
x_56 = lean_array_get_size(x_55);
x_57 = lean_nat_dec_lt(x_51, x_56);
if (x_57 == 0)
{
lean_object* x_58; 
lean_dec(x_55);
lean_dec_ref(x_4);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_54);
return x_58;
}
else
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_box(0);
x_60 = lean_nat_dec_le(x_56, x_56);
if (x_60 == 0)
{
if (x_57 == 0)
{
lean_object* x_61; 
lean_dec(x_55);
lean_dec_ref(x_4);
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_54);
return x_61;
}
else
{
size_t x_62; size_t x_63; lean_object* x_64; 
x_62 = 0;
x_63 = lean_usize_of_nat(x_56);
x_64 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_55, x_62, x_63, x_59, x_4);
lean_dec(x_55);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; uint8_t x_66; uint8_t x_71; 
x_71 = !lean_is_exclusive(x_64);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_64, 0);
lean_dec(x_72);
x_65 = x_64;
x_66 = x_71;
goto block_70;
}
else
{
lean_dec(x_64);
x_65 = lean_box(0);
x_66 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_67; 
if (x_66 == 0)
{
lean_ctor_set(x_65, 0, x_54);
x_67 = x_65;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_69, 0, x_54);
x_67 = x_69;
goto block_68;
}
block_68:
{
return x_67;
}
}
}
else
{
lean_dec(x_54);
return x_64;
}
}
}
else
{
size_t x_73; size_t x_74; lean_object* x_75; 
x_73 = 0;
x_74 = lean_usize_of_nat(x_56);
x_75 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_55, x_73, x_74, x_59, x_4);
lean_dec(x_55);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; uint8_t x_77; uint8_t x_82; 
x_82 = !lean_is_exclusive(x_75);
if (x_82 == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_75, 0);
lean_dec(x_83);
x_76 = x_75;
x_77 = x_82;
goto block_81;
}
else
{
lean_dec(x_75);
x_76 = lean_box(0);
x_77 = x_82;
goto block_81;
}
block_81:
{
lean_object* x_78; 
if (x_77 == 0)
{
lean_ctor_set(x_76, 0, x_54);
x_78 = x_76;
goto block_79;
}
else
{
lean_object* x_80; 
x_80 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_80, 0, x_54);
x_78 = x_80;
goto block_79;
}
block_79:
{
return x_78;
}
}
}
else
{
lean_dec(x_54);
return x_75;
}
}
}
}
else
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_84 = lean_ctor_get(x_53, 1);
lean_inc(x_84);
lean_dec_ref(x_53);
x_85 = lean_array_get_size(x_84);
x_86 = lean_nat_dec_lt(x_51, x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_84);
lean_dec_ref(x_4);
x_87 = lean_box(0);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
return x_88;
}
else
{
lean_object* x_89; uint8_t x_90; 
x_89 = lean_box(0);
x_90 = lean_nat_dec_le(x_85, x_85);
if (x_90 == 0)
{
if (x_86 == 0)
{
lean_dec(x_84);
lean_dec_ref(x_4);
x_35 = lean_box(0);
goto block_38;
}
else
{
size_t x_91; size_t x_92; lean_object* x_93; 
x_91 = 0;
x_92 = lean_usize_of_nat(x_85);
x_93 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_84, x_91, x_92, x_89, x_4);
lean_dec(x_84);
if (lean_obj_tag(x_93) == 0)
{
lean_dec_ref(x_93);
x_35 = lean_box(0);
goto block_38;
}
else
{
return x_93;
}
}
}
else
{
size_t x_94; size_t x_95; lean_object* x_96; 
x_94 = 0;
x_95 = lean_usize_of_nat(x_85);
x_96 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_84, x_94, x_95, x_89, x_4);
lean_dec(x_84);
if (lean_obj_tag(x_96) == 0)
{
lean_dec_ref(x_96);
x_35 = lean_box(0);
goto block_38;
}
else
{
return x_96;
}
}
}
}
}
else
{
uint8_t x_97; lean_object* x_98; lean_object* x_99; 
lean_dec_ref(x_39);
lean_inc_ref(x_2);
x_97 = l_Lake_GitRepo_hasNoDiff(x_2);
x_98 = lean_unsigned_to_nat(0u);
x_99 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
if (x_97 == 0)
{
x_20 = x_98;
x_21 = x_99;
x_22 = x_42;
x_23 = lean_box(0);
goto block_34;
}
else
{
uint8_t x_100; 
x_100 = 0;
x_20 = x_98;
x_21 = x_99;
x_22 = x_100;
x_23 = lean_box(0);
goto block_34;
}
}
}
block_105:
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_box(0);
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_103);
return x_104;
}
block_109:
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_box(0);
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_107);
return x_108;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1_spec__1___redArg(x_1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1_spec__1(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_11; lean_object* x_12; lean_object* x_68; lean_object* x_72; lean_object* x_112; lean_object* x_114; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_118 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___closed__0));
lean_inc_ref(x_1);
x_119 = lean_string_append(x_1, x_118);
x_120 = lean_string_append(x_119, x_3);
x_121 = 1;
x_122 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set_uint8(x_122, sizeof(void*)*1, x_121);
lean_inc_ref(x_5);
x_123 = lean_apply_2(x_5, x_122, lean_box(0));
x_124 = lean_unsigned_to_nat(0u);
x_125 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
lean_inc_ref(x_2);
x_126 = l_Lake_GitRepo_clone(x_3, x_2, x_125);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_127 = lean_ctor_get(x_126, 1);
lean_inc(x_127);
lean_dec_ref(x_126);
x_128 = lean_array_get_size(x_127);
x_129 = lean_nat_dec_lt(x_124, x_128);
if (x_129 == 0)
{
lean_dec(x_127);
x_72 = lean_box(0);
goto block_111;
}
else
{
lean_object* x_130; uint8_t x_131; 
x_130 = lean_box(0);
x_131 = lean_nat_dec_le(x_128, x_128);
if (x_131 == 0)
{
if (x_129 == 0)
{
lean_dec(x_127);
x_72 = lean_box(0);
goto block_111;
}
else
{
size_t x_132; size_t x_133; lean_object* x_134; 
x_132 = 0;
x_133 = lean_usize_of_nat(x_128);
lean_inc_ref(x_5);
x_134 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_127, x_132, x_133, x_130, x_5);
lean_dec(x_127);
if (lean_obj_tag(x_134) == 0)
{
lean_dec_ref(x_134);
x_72 = lean_box(0);
goto block_111;
}
else
{
x_112 = x_134;
goto block_113;
}
}
}
else
{
size_t x_135; size_t x_136; lean_object* x_137; 
x_135 = 0;
x_136 = lean_usize_of_nat(x_128);
lean_inc_ref(x_5);
x_137 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_127, x_135, x_136, x_130, x_5);
lean_dec(x_127);
if (lean_obj_tag(x_137) == 0)
{
lean_dec_ref(x_137);
x_72 = lean_box(0);
goto block_111;
}
else
{
x_112 = x_137;
goto block_113;
}
}
}
}
else
{
lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_138 = lean_ctor_get(x_126, 1);
lean_inc(x_138);
lean_dec_ref(x_126);
x_139 = lean_array_get_size(x_138);
x_140 = lean_nat_dec_lt(x_124, x_139);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; 
lean_dec(x_138);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_141 = lean_box(0);
x_142 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_142, 0, x_141);
return x_142;
}
else
{
lean_object* x_143; uint8_t x_144; 
x_143 = lean_box(0);
x_144 = lean_nat_dec_le(x_139, x_139);
if (x_144 == 0)
{
if (x_140 == 0)
{
lean_dec(x_138);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_114 = lean_box(0);
goto block_117;
}
else
{
size_t x_145; size_t x_146; lean_object* x_147; 
x_145 = 0;
x_146 = lean_usize_of_nat(x_139);
lean_inc_ref(x_5);
x_147 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_138, x_145, x_146, x_143, x_5);
lean_dec(x_138);
if (lean_obj_tag(x_147) == 0)
{
lean_dec_ref(x_147);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_114 = lean_box(0);
goto block_117;
}
else
{
x_112 = x_147;
goto block_113;
}
}
}
else
{
size_t x_148; size_t x_149; lean_object* x_150; 
x_148 = 0;
x_149 = lean_usize_of_nat(x_139);
lean_inc_ref(x_5);
x_150 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_138, x_148, x_149, x_143, x_5);
lean_dec(x_138);
if (lean_obj_tag(x_150) == 0)
{
lean_dec_ref(x_150);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_114 = lean_box(0);
goto block_117;
}
else
{
x_112 = x_150;
goto block_113;
}
}
}
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
block_67:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_13 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
x_14 = lean_string_append(x_1, x_13);
x_15 = lean_string_append(x_14, x_11);
x_16 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3));
x_17 = lean_string_append(x_15, x_16);
x_18 = 1;
x_19 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_18);
lean_inc_ref(x_5);
x_20 = lean_apply_2(x_5, x_19, lean_box(0));
x_21 = lean_unsigned_to_nat(0u);
x_22 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
x_23 = l_Lake_GitRepo_checkoutDetach(x_11, x_2, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec_ref(x_23);
x_26 = lean_array_get_size(x_25);
x_27 = lean_nat_dec_lt(x_21, x_26);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_25);
lean_dec_ref(x_5);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_24);
return x_28;
}
else
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_box(0);
x_30 = lean_nat_dec_le(x_26, x_26);
if (x_30 == 0)
{
if (x_27 == 0)
{
lean_object* x_31; 
lean_dec(x_25);
lean_dec_ref(x_5);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_24);
return x_31;
}
else
{
size_t x_32; size_t x_33; lean_object* x_34; 
x_32 = 0;
x_33 = lean_usize_of_nat(x_26);
x_34 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_25, x_32, x_33, x_29, x_5);
lean_dec(x_25);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; uint8_t x_36; uint8_t x_41; 
x_41 = !lean_is_exclusive(x_34);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_34, 0);
lean_dec(x_42);
x_35 = x_34;
x_36 = x_41;
goto block_40;
}
else
{
lean_dec(x_34);
x_35 = lean_box(0);
x_36 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_37; 
if (x_36 == 0)
{
lean_ctor_set(x_35, 0, x_24);
x_37 = x_35;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_24);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
}
else
{
lean_dec(x_24);
return x_34;
}
}
}
else
{
size_t x_43; size_t x_44; lean_object* x_45; 
x_43 = 0;
x_44 = lean_usize_of_nat(x_26);
x_45 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_25, x_43, x_44, x_29, x_5);
lean_dec(x_25);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; uint8_t x_47; uint8_t x_52; 
x_52 = !lean_is_exclusive(x_45);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_45, 0);
lean_dec(x_53);
x_46 = x_45;
x_47 = x_52;
goto block_51;
}
else
{
lean_dec(x_45);
x_46 = lean_box(0);
x_47 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_48; 
if (x_47 == 0)
{
lean_ctor_set(x_46, 0, x_24);
x_48 = x_46;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_24);
x_48 = x_50;
goto block_49;
}
block_49:
{
return x_48;
}
}
}
else
{
lean_dec(x_24);
return x_45;
}
}
}
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_54 = lean_ctor_get(x_23, 1);
lean_inc(x_54);
lean_dec_ref(x_23);
x_55 = lean_array_get_size(x_54);
x_56 = lean_nat_dec_lt(x_21, x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_54);
lean_dec_ref(x_5);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
else
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_box(0);
x_60 = lean_nat_dec_le(x_55, x_55);
if (x_60 == 0)
{
if (x_56 == 0)
{
lean_dec(x_54);
lean_dec_ref(x_5);
x_7 = lean_box(0);
goto block_10;
}
else
{
size_t x_61; size_t x_62; lean_object* x_63; 
x_61 = 0;
x_62 = lean_usize_of_nat(x_55);
x_63 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_54, x_61, x_62, x_59, x_5);
lean_dec(x_54);
if (lean_obj_tag(x_63) == 0)
{
lean_dec_ref(x_63);
x_7 = lean_box(0);
goto block_10;
}
else
{
return x_63;
}
}
}
else
{
size_t x_64; size_t x_65; lean_object* x_66; 
x_64 = 0;
x_65 = lean_usize_of_nat(x_55);
x_66 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_54, x_64, x_65, x_59, x_5);
lean_dec(x_54);
if (lean_obj_tag(x_66) == 0)
{
lean_dec_ref(x_66);
x_7 = lean_box(0);
goto block_10;
}
else
{
return x_66;
}
}
}
}
}
block_71:
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
block_111:
{
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_108; 
x_73 = lean_ctor_get(x_4, 0);
x_108 = !lean_is_exclusive(x_4);
if (x_108 == 0)
{
x_74 = x_4;
x_75 = x_108;
goto block_107;
}
else
{
lean_inc(x_73);
lean_dec(x_4);
x_74 = lean_box(0);
x_75 = x_108;
goto block_107;
}
block_107:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = l_Lake_Git_defaultRemote;
x_77 = lean_unsigned_to_nat(0u);
x_78 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
lean_inc_ref(x_2);
x_79 = l_Lake_GitRepo_resolveRemoteRevision(x_73, x_76, x_2, x_78);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
lean_del_object(x_74);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec_ref(x_79);
x_82 = lean_array_get_size(x_81);
x_83 = lean_nat_dec_lt(x_77, x_82);
if (x_83 == 0)
{
lean_dec(x_81);
x_11 = x_80;
x_12 = lean_box(0);
goto block_67;
}
else
{
lean_object* x_84; uint8_t x_85; 
x_84 = lean_box(0);
x_85 = lean_nat_dec_le(x_82, x_82);
if (x_85 == 0)
{
if (x_83 == 0)
{
lean_dec(x_81);
x_11 = x_80;
x_12 = lean_box(0);
goto block_67;
}
else
{
size_t x_86; size_t x_87; lean_object* x_88; 
x_86 = 0;
x_87 = lean_usize_of_nat(x_82);
lean_inc_ref(x_5);
x_88 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_81, x_86, x_87, x_84, x_5);
lean_dec(x_81);
if (lean_obj_tag(x_88) == 0)
{
lean_dec_ref(x_88);
x_11 = x_80;
x_12 = lean_box(0);
goto block_67;
}
else
{
lean_dec(x_80);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_88;
}
}
}
else
{
size_t x_89; size_t x_90; lean_object* x_91; 
x_89 = 0;
x_90 = lean_usize_of_nat(x_82);
lean_inc_ref(x_5);
x_91 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_81, x_89, x_90, x_84, x_5);
lean_dec(x_81);
if (lean_obj_tag(x_91) == 0)
{
lean_dec_ref(x_91);
x_11 = x_80;
x_12 = lean_box(0);
goto block_67;
}
else
{
lean_dec(x_80);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_91;
}
}
}
}
else
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_92 = lean_ctor_get(x_79, 1);
lean_inc(x_92);
lean_dec_ref(x_79);
x_93 = lean_array_get_size(x_92);
x_94 = lean_nat_dec_lt(x_77, x_93);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; 
lean_dec(x_92);
lean_dec_ref(x_5);
x_95 = lean_box(0);
if (x_75 == 0)
{
lean_ctor_set(x_74, 0, x_95);
x_96 = x_74;
goto block_97;
}
else
{
lean_object* x_98; 
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_95);
x_96 = x_98;
goto block_97;
}
block_97:
{
return x_96;
}
}
else
{
lean_object* x_99; uint8_t x_100; 
lean_del_object(x_74);
x_99 = lean_box(0);
x_100 = lean_nat_dec_le(x_93, x_93);
if (x_100 == 0)
{
if (x_94 == 0)
{
lean_dec(x_92);
lean_dec_ref(x_5);
x_68 = lean_box(0);
goto block_71;
}
else
{
size_t x_101; size_t x_102; lean_object* x_103; 
x_101 = 0;
x_102 = lean_usize_of_nat(x_93);
x_103 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_92, x_101, x_102, x_99, x_5);
lean_dec(x_92);
if (lean_obj_tag(x_103) == 0)
{
lean_dec_ref(x_103);
x_68 = lean_box(0);
goto block_71;
}
else
{
return x_103;
}
}
}
else
{
size_t x_104; size_t x_105; lean_object* x_106; 
x_104 = 0;
x_105 = lean_usize_of_nat(x_93);
x_106 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_92, x_104, x_105, x_99, x_5);
lean_dec(x_92);
if (lean_obj_tag(x_106) == 0)
{
lean_dec_ref(x_106);
x_68 = lean_box(0);
goto block_71;
}
else
{
return x_106;
}
}
}
}
}
}
else
{
lean_object* x_109; lean_object* x_110; 
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_109 = lean_box(0);
x_110 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_110, 0, x_109);
return x_110;
}
}
block_113:
{
if (lean_obj_tag(x_112) == 0)
{
lean_dec_ref(x_112);
x_72 = lean_box(0);
goto block_111;
}
else
{
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_112;
}
}
block_117:
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_box(0);
x_116 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_116, 0, x_115);
return x_116;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_11; lean_object* x_12; lean_object* x_68; lean_object* x_72; lean_object* x_112; lean_object* x_114; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_118 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___closed__0));
lean_inc_ref(x_2);
x_119 = lean_string_append(x_2, x_118);
x_120 = lean_string_append(x_119, x_4);
x_121 = 1;
x_122 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set_uint8(x_122, sizeof(void*)*1, x_121);
lean_inc_ref(x_1);
x_123 = lean_apply_2(x_1, x_122, lean_box(0));
x_124 = lean_unsigned_to_nat(0u);
x_125 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
lean_inc_ref(x_3);
x_126 = l_Lake_GitRepo_clone(x_4, x_3, x_125);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_127 = lean_ctor_get(x_126, 1);
lean_inc(x_127);
lean_dec_ref(x_126);
x_128 = lean_array_get_size(x_127);
x_129 = lean_nat_dec_lt(x_124, x_128);
if (x_129 == 0)
{
lean_dec(x_127);
x_72 = lean_box(0);
goto block_111;
}
else
{
lean_object* x_130; uint8_t x_131; 
x_130 = lean_box(0);
x_131 = lean_nat_dec_le(x_128, x_128);
if (x_131 == 0)
{
if (x_129 == 0)
{
lean_dec(x_127);
x_72 = lean_box(0);
goto block_111;
}
else
{
size_t x_132; size_t x_133; lean_object* x_134; 
x_132 = 0;
x_133 = lean_usize_of_nat(x_128);
lean_inc_ref(x_1);
x_134 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_127, x_132, x_133, x_130, x_1);
lean_dec(x_127);
if (lean_obj_tag(x_134) == 0)
{
lean_dec_ref(x_134);
x_72 = lean_box(0);
goto block_111;
}
else
{
x_112 = x_134;
goto block_113;
}
}
}
else
{
size_t x_135; size_t x_136; lean_object* x_137; 
x_135 = 0;
x_136 = lean_usize_of_nat(x_128);
lean_inc_ref(x_1);
x_137 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_127, x_135, x_136, x_130, x_1);
lean_dec(x_127);
if (lean_obj_tag(x_137) == 0)
{
lean_dec_ref(x_137);
x_72 = lean_box(0);
goto block_111;
}
else
{
x_112 = x_137;
goto block_113;
}
}
}
}
else
{
lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_138 = lean_ctor_get(x_126, 1);
lean_inc(x_138);
lean_dec_ref(x_126);
x_139 = lean_array_get_size(x_138);
x_140 = lean_nat_dec_lt(x_124, x_139);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; 
lean_dec(x_138);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_141 = lean_box(0);
x_142 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_142, 0, x_141);
return x_142;
}
else
{
lean_object* x_143; uint8_t x_144; 
x_143 = lean_box(0);
x_144 = lean_nat_dec_le(x_139, x_139);
if (x_144 == 0)
{
if (x_140 == 0)
{
lean_dec(x_138);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_114 = lean_box(0);
goto block_117;
}
else
{
size_t x_145; size_t x_146; lean_object* x_147; 
x_145 = 0;
x_146 = lean_usize_of_nat(x_139);
lean_inc_ref(x_1);
x_147 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_138, x_145, x_146, x_143, x_1);
lean_dec(x_138);
if (lean_obj_tag(x_147) == 0)
{
lean_dec_ref(x_147);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_114 = lean_box(0);
goto block_117;
}
else
{
x_112 = x_147;
goto block_113;
}
}
}
else
{
size_t x_148; size_t x_149; lean_object* x_150; 
x_148 = 0;
x_149 = lean_usize_of_nat(x_139);
lean_inc_ref(x_1);
x_150 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_138, x_148, x_149, x_143, x_1);
lean_dec(x_138);
if (lean_obj_tag(x_150) == 0)
{
lean_dec_ref(x_150);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_114 = lean_box(0);
goto block_117;
}
else
{
x_112 = x_150;
goto block_113;
}
}
}
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
block_67:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_13 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
x_14 = lean_string_append(x_2, x_13);
x_15 = lean_string_append(x_14, x_11);
x_16 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3));
x_17 = lean_string_append(x_15, x_16);
x_18 = 1;
x_19 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_18);
lean_inc_ref(x_1);
x_20 = lean_apply_2(x_1, x_19, lean_box(0));
x_21 = lean_unsigned_to_nat(0u);
x_22 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
x_23 = l_Lake_GitRepo_checkoutDetach(x_11, x_3, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec_ref(x_23);
x_26 = lean_array_get_size(x_25);
x_27 = lean_nat_dec_lt(x_21, x_26);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_25);
lean_dec_ref(x_1);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_24);
return x_28;
}
else
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_box(0);
x_30 = lean_nat_dec_le(x_26, x_26);
if (x_30 == 0)
{
if (x_27 == 0)
{
lean_object* x_31; 
lean_dec(x_25);
lean_dec_ref(x_1);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_24);
return x_31;
}
else
{
size_t x_32; size_t x_33; lean_object* x_34; 
x_32 = 0;
x_33 = lean_usize_of_nat(x_26);
x_34 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_25, x_32, x_33, x_29, x_1);
lean_dec(x_25);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; uint8_t x_36; uint8_t x_41; 
x_41 = !lean_is_exclusive(x_34);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_34, 0);
lean_dec(x_42);
x_35 = x_34;
x_36 = x_41;
goto block_40;
}
else
{
lean_dec(x_34);
x_35 = lean_box(0);
x_36 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_37; 
if (x_36 == 0)
{
lean_ctor_set(x_35, 0, x_24);
x_37 = x_35;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_24);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
}
else
{
lean_dec(x_24);
return x_34;
}
}
}
else
{
size_t x_43; size_t x_44; lean_object* x_45; 
x_43 = 0;
x_44 = lean_usize_of_nat(x_26);
x_45 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_25, x_43, x_44, x_29, x_1);
lean_dec(x_25);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; uint8_t x_47; uint8_t x_52; 
x_52 = !lean_is_exclusive(x_45);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_45, 0);
lean_dec(x_53);
x_46 = x_45;
x_47 = x_52;
goto block_51;
}
else
{
lean_dec(x_45);
x_46 = lean_box(0);
x_47 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_48; 
if (x_47 == 0)
{
lean_ctor_set(x_46, 0, x_24);
x_48 = x_46;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_24);
x_48 = x_50;
goto block_49;
}
block_49:
{
return x_48;
}
}
}
else
{
lean_dec(x_24);
return x_45;
}
}
}
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_54 = lean_ctor_get(x_23, 1);
lean_inc(x_54);
lean_dec_ref(x_23);
x_55 = lean_array_get_size(x_54);
x_56 = lean_nat_dec_lt(x_21, x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_54);
lean_dec_ref(x_1);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
else
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_box(0);
x_60 = lean_nat_dec_le(x_55, x_55);
if (x_60 == 0)
{
if (x_56 == 0)
{
lean_dec(x_54);
lean_dec_ref(x_1);
x_7 = lean_box(0);
goto block_10;
}
else
{
size_t x_61; size_t x_62; lean_object* x_63; 
x_61 = 0;
x_62 = lean_usize_of_nat(x_55);
x_63 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_54, x_61, x_62, x_59, x_1);
lean_dec(x_54);
if (lean_obj_tag(x_63) == 0)
{
lean_dec_ref(x_63);
x_7 = lean_box(0);
goto block_10;
}
else
{
return x_63;
}
}
}
else
{
size_t x_64; size_t x_65; lean_object* x_66; 
x_64 = 0;
x_65 = lean_usize_of_nat(x_55);
x_66 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_54, x_64, x_65, x_59, x_1);
lean_dec(x_54);
if (lean_obj_tag(x_66) == 0)
{
lean_dec_ref(x_66);
x_7 = lean_box(0);
goto block_10;
}
else
{
return x_66;
}
}
}
}
}
block_71:
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
block_111:
{
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_108; 
x_73 = lean_ctor_get(x_5, 0);
x_108 = !lean_is_exclusive(x_5);
if (x_108 == 0)
{
x_74 = x_5;
x_75 = x_108;
goto block_107;
}
else
{
lean_inc(x_73);
lean_dec(x_5);
x_74 = lean_box(0);
x_75 = x_108;
goto block_107;
}
block_107:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = l_Lake_Git_defaultRemote;
x_77 = lean_unsigned_to_nat(0u);
x_78 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
lean_inc_ref(x_3);
x_79 = l_Lake_GitRepo_resolveRemoteRevision(x_73, x_76, x_3, x_78);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
lean_del_object(x_74);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec_ref(x_79);
x_82 = lean_array_get_size(x_81);
x_83 = lean_nat_dec_lt(x_77, x_82);
if (x_83 == 0)
{
lean_dec(x_81);
x_11 = x_80;
x_12 = lean_box(0);
goto block_67;
}
else
{
lean_object* x_84; uint8_t x_85; 
x_84 = lean_box(0);
x_85 = lean_nat_dec_le(x_82, x_82);
if (x_85 == 0)
{
if (x_83 == 0)
{
lean_dec(x_81);
x_11 = x_80;
x_12 = lean_box(0);
goto block_67;
}
else
{
size_t x_86; size_t x_87; lean_object* x_88; 
x_86 = 0;
x_87 = lean_usize_of_nat(x_82);
lean_inc_ref(x_1);
x_88 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_81, x_86, x_87, x_84, x_1);
lean_dec(x_81);
if (lean_obj_tag(x_88) == 0)
{
lean_dec_ref(x_88);
x_11 = x_80;
x_12 = lean_box(0);
goto block_67;
}
else
{
lean_dec(x_80);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_88;
}
}
}
else
{
size_t x_89; size_t x_90; lean_object* x_91; 
x_89 = 0;
x_90 = lean_usize_of_nat(x_82);
lean_inc_ref(x_1);
x_91 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_81, x_89, x_90, x_84, x_1);
lean_dec(x_81);
if (lean_obj_tag(x_91) == 0)
{
lean_dec_ref(x_91);
x_11 = x_80;
x_12 = lean_box(0);
goto block_67;
}
else
{
lean_dec(x_80);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_91;
}
}
}
}
else
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_92 = lean_ctor_get(x_79, 1);
lean_inc(x_92);
lean_dec_ref(x_79);
x_93 = lean_array_get_size(x_92);
x_94 = lean_nat_dec_lt(x_77, x_93);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; 
lean_dec(x_92);
lean_dec_ref(x_1);
x_95 = lean_box(0);
if (x_75 == 0)
{
lean_ctor_set(x_74, 0, x_95);
x_96 = x_74;
goto block_97;
}
else
{
lean_object* x_98; 
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_95);
x_96 = x_98;
goto block_97;
}
block_97:
{
return x_96;
}
}
else
{
lean_object* x_99; uint8_t x_100; 
lean_del_object(x_74);
x_99 = lean_box(0);
x_100 = lean_nat_dec_le(x_93, x_93);
if (x_100 == 0)
{
if (x_94 == 0)
{
lean_dec(x_92);
lean_dec_ref(x_1);
x_68 = lean_box(0);
goto block_71;
}
else
{
size_t x_101; size_t x_102; lean_object* x_103; 
x_101 = 0;
x_102 = lean_usize_of_nat(x_93);
x_103 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_92, x_101, x_102, x_99, x_1);
lean_dec(x_92);
if (lean_obj_tag(x_103) == 0)
{
lean_dec_ref(x_103);
x_68 = lean_box(0);
goto block_71;
}
else
{
return x_103;
}
}
}
else
{
size_t x_104; size_t x_105; lean_object* x_106; 
x_104 = 0;
x_105 = lean_usize_of_nat(x_93);
x_106 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_92, x_104, x_105, x_99, x_1);
lean_dec(x_92);
if (lean_obj_tag(x_106) == 0)
{
lean_dec_ref(x_106);
x_68 = lean_box(0);
goto block_71;
}
else
{
return x_106;
}
}
}
}
}
}
else
{
lean_object* x_109; lean_object* x_110; 
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_109 = lean_box(0);
x_110 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_110, 0, x_109);
return x_110;
}
}
block_113:
{
if (lean_obj_tag(x_112) == 0)
{
lean_dec_ref(x_112);
x_72 = lean_box(0);
goto block_111;
}
else
{
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_112;
}
}
block_117:
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_box(0);
x_116 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_116, 0, x_115);
return x_116;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_6; lean_object* x_7; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_35; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_102; lean_object* x_106; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_110 = l_Lake_Git_defaultRemote;
x_111 = lean_unsigned_to_nat(0u);
x_112 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
lean_inc_ref(x_3);
x_113 = l_Lake_GitRepo_findRemoteRevision(x_3, x_4, x_110, x_112);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_144; uint8_t x_145; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec_ref(x_113);
x_144 = lean_array_get_size(x_115);
x_145 = lean_nat_dec_lt(x_111, x_144);
if (x_145 == 0)
{
lean_dec(x_115);
x_116 = lean_box(0);
goto block_143;
}
else
{
lean_object* x_146; uint8_t x_147; 
x_146 = lean_box(0);
x_147 = lean_nat_dec_le(x_144, x_144);
if (x_147 == 0)
{
if (x_145 == 0)
{
lean_dec(x_115);
x_116 = lean_box(0);
goto block_143;
}
else
{
size_t x_148; size_t x_149; lean_object* x_150; 
x_148 = 0;
x_149 = lean_usize_of_nat(x_144);
lean_inc_ref(x_1);
x_150 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_115, x_148, x_149, x_146, x_1);
lean_dec(x_115);
if (lean_obj_tag(x_150) == 0)
{
lean_dec_ref(x_150);
x_116 = lean_box(0);
goto block_143;
}
else
{
lean_dec(x_114);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_150;
}
}
}
else
{
size_t x_151; size_t x_152; lean_object* x_153; 
x_151 = 0;
x_152 = lean_usize_of_nat(x_144);
lean_inc_ref(x_1);
x_153 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_115, x_151, x_152, x_146, x_1);
lean_dec(x_115);
if (lean_obj_tag(x_153) == 0)
{
lean_dec_ref(x_153);
x_116 = lean_box(0);
goto block_143;
}
else
{
lean_dec(x_114);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_153;
}
}
}
block_143:
{
lean_object* x_117; 
lean_inc_ref(x_3);
x_117 = l_Lake_GitRepo_getHeadRevision(x_3, x_112);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec_ref(x_117);
x_120 = lean_array_get_size(x_119);
x_121 = lean_nat_dec_lt(x_111, x_120);
if (x_121 == 0)
{
lean_dec(x_119);
x_39 = x_114;
x_40 = x_118;
x_41 = lean_box(0);
goto block_101;
}
else
{
lean_object* x_122; uint8_t x_123; 
x_122 = lean_box(0);
x_123 = lean_nat_dec_le(x_120, x_120);
if (x_123 == 0)
{
if (x_121 == 0)
{
lean_dec(x_119);
x_39 = x_114;
x_40 = x_118;
x_41 = lean_box(0);
goto block_101;
}
else
{
size_t x_124; size_t x_125; lean_object* x_126; 
x_124 = 0;
x_125 = lean_usize_of_nat(x_120);
lean_inc_ref(x_1);
x_126 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_119, x_124, x_125, x_122, x_1);
lean_dec(x_119);
if (lean_obj_tag(x_126) == 0)
{
lean_dec_ref(x_126);
x_39 = x_114;
x_40 = x_118;
x_41 = lean_box(0);
goto block_101;
}
else
{
lean_dec(x_118);
lean_dec(x_114);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_126;
}
}
}
else
{
size_t x_127; size_t x_128; lean_object* x_129; 
x_127 = 0;
x_128 = lean_usize_of_nat(x_120);
lean_inc_ref(x_1);
x_129 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_119, x_127, x_128, x_122, x_1);
lean_dec(x_119);
if (lean_obj_tag(x_129) == 0)
{
lean_dec_ref(x_129);
x_39 = x_114;
x_40 = x_118;
x_41 = lean_box(0);
goto block_101;
}
else
{
lean_dec(x_118);
lean_dec(x_114);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_129;
}
}
}
}
else
{
lean_object* x_130; lean_object* x_131; uint8_t x_132; 
lean_dec(x_114);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_130 = lean_ctor_get(x_117, 1);
lean_inc(x_130);
lean_dec_ref(x_117);
x_131 = lean_array_get_size(x_130);
x_132 = lean_nat_dec_lt(x_111, x_131);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; 
lean_dec(x_130);
lean_dec_ref(x_1);
x_133 = lean_box(0);
x_134 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_134, 0, x_133);
return x_134;
}
else
{
lean_object* x_135; uint8_t x_136; 
x_135 = lean_box(0);
x_136 = lean_nat_dec_le(x_131, x_131);
if (x_136 == 0)
{
if (x_132 == 0)
{
lean_dec(x_130);
lean_dec_ref(x_1);
x_102 = lean_box(0);
goto block_105;
}
else
{
size_t x_137; size_t x_138; lean_object* x_139; 
x_137 = 0;
x_138 = lean_usize_of_nat(x_131);
x_139 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_130, x_137, x_138, x_135, x_1);
lean_dec(x_130);
if (lean_obj_tag(x_139) == 0)
{
lean_dec_ref(x_139);
x_102 = lean_box(0);
goto block_105;
}
else
{
return x_139;
}
}
}
else
{
size_t x_140; size_t x_141; lean_object* x_142; 
x_140 = 0;
x_141 = lean_usize_of_nat(x_131);
x_142 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_130, x_140, x_141, x_135, x_1);
lean_dec(x_130);
if (lean_obj_tag(x_142) == 0)
{
lean_dec_ref(x_142);
x_102 = lean_box(0);
goto block_105;
}
else
{
return x_142;
}
}
}
}
}
}
else
{
lean_object* x_154; lean_object* x_155; uint8_t x_156; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_154 = lean_ctor_get(x_113, 1);
lean_inc(x_154);
lean_dec_ref(x_113);
x_155 = lean_array_get_size(x_154);
x_156 = lean_nat_dec_lt(x_111, x_155);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; 
lean_dec(x_154);
lean_dec_ref(x_1);
x_157 = lean_box(0);
x_158 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_158, 0, x_157);
return x_158;
}
else
{
lean_object* x_159; uint8_t x_160; 
x_159 = lean_box(0);
x_160 = lean_nat_dec_le(x_155, x_155);
if (x_160 == 0)
{
if (x_156 == 0)
{
lean_dec(x_154);
lean_dec_ref(x_1);
x_106 = lean_box(0);
goto block_109;
}
else
{
size_t x_161; size_t x_162; lean_object* x_163; 
x_161 = 0;
x_162 = lean_usize_of_nat(x_155);
x_163 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_154, x_161, x_162, x_159, x_1);
lean_dec(x_154);
if (lean_obj_tag(x_163) == 0)
{
lean_dec_ref(x_163);
x_106 = lean_box(0);
goto block_109;
}
else
{
return x_163;
}
}
}
else
{
size_t x_164; size_t x_165; lean_object* x_166; 
x_164 = 0;
x_165 = lean_usize_of_nat(x_155);
x_166 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_154, x_164, x_165, x_159, x_1);
lean_dec(x_154);
if (lean_obj_tag(x_166) == 0)
{
lean_dec_ref(x_166);
x_106 = lean_box(0);
goto block_109;
}
else
{
return x_166;
}
}
}
}
block_19:
{
if (x_6 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0));
x_11 = lean_string_append(x_2, x_10);
x_12 = lean_string_append(x_11, x_3);
lean_dec_ref(x_3);
x_13 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1));
x_14 = lean_string_append(x_12, x_13);
x_15 = 2;
x_16 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_15);
x_17 = lean_apply_2(x_1, x_16, lean_box(0));
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
block_34:
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_array_get_size(x_21);
x_25 = lean_nat_dec_lt(x_20, x_24);
if (x_25 == 0)
{
lean_dec_ref(x_21);
x_6 = x_22;
x_7 = lean_box(0);
goto block_19;
}
else
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_box(0);
x_27 = lean_nat_dec_le(x_24, x_24);
if (x_27 == 0)
{
if (x_25 == 0)
{
lean_dec_ref(x_21);
x_6 = x_22;
x_7 = lean_box(0);
goto block_19;
}
else
{
size_t x_28; size_t x_29; lean_object* x_30; 
x_28 = 0;
x_29 = lean_usize_of_nat(x_24);
lean_inc_ref(x_1);
x_30 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_21, x_28, x_29, x_26, x_1);
lean_dec_ref(x_21);
if (lean_obj_tag(x_30) == 0)
{
lean_dec_ref(x_30);
x_6 = x_22;
x_7 = lean_box(0);
goto block_19;
}
else
{
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_30;
}
}
}
else
{
size_t x_31; size_t x_32; lean_object* x_33; 
x_31 = 0;
x_32 = lean_usize_of_nat(x_24);
lean_inc_ref(x_1);
x_33 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_21, x_31, x_32, x_26, x_1);
lean_dec_ref(x_21);
if (lean_obj_tag(x_33) == 0)
{
lean_dec_ref(x_33);
x_6 = x_22;
x_7 = lean_box(0);
goto block_19;
}
else
{
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_33;
}
}
}
}
block_38:
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
block_101:
{
uint8_t x_42; 
x_42 = lean_string_dec_eq(x_40, x_39);
lean_dec_ref(x_40);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_43 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
x_44 = lean_string_append(x_2, x_43);
x_45 = lean_string_append(x_44, x_39);
x_46 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3));
x_47 = lean_string_append(x_45, x_46);
x_48 = 1;
x_49 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set_uint8(x_49, sizeof(void*)*1, x_48);
lean_inc_ref(x_1);
x_50 = lean_apply_2(x_1, x_49, lean_box(0));
x_51 = lean_unsigned_to_nat(0u);
x_52 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
x_53 = l_Lake_GitRepo_checkoutDetach(x_39, x_3, x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec_ref(x_53);
x_56 = lean_array_get_size(x_55);
x_57 = lean_nat_dec_lt(x_51, x_56);
if (x_57 == 0)
{
lean_object* x_58; 
lean_dec(x_55);
lean_dec_ref(x_1);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_54);
return x_58;
}
else
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_box(0);
x_60 = lean_nat_dec_le(x_56, x_56);
if (x_60 == 0)
{
if (x_57 == 0)
{
lean_object* x_61; 
lean_dec(x_55);
lean_dec_ref(x_1);
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_54);
return x_61;
}
else
{
size_t x_62; size_t x_63; lean_object* x_64; 
x_62 = 0;
x_63 = lean_usize_of_nat(x_56);
x_64 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_55, x_62, x_63, x_59, x_1);
lean_dec(x_55);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; uint8_t x_66; uint8_t x_71; 
x_71 = !lean_is_exclusive(x_64);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_64, 0);
lean_dec(x_72);
x_65 = x_64;
x_66 = x_71;
goto block_70;
}
else
{
lean_dec(x_64);
x_65 = lean_box(0);
x_66 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_67; 
if (x_66 == 0)
{
lean_ctor_set(x_65, 0, x_54);
x_67 = x_65;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_69, 0, x_54);
x_67 = x_69;
goto block_68;
}
block_68:
{
return x_67;
}
}
}
else
{
lean_dec(x_54);
return x_64;
}
}
}
else
{
size_t x_73; size_t x_74; lean_object* x_75; 
x_73 = 0;
x_74 = lean_usize_of_nat(x_56);
x_75 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_55, x_73, x_74, x_59, x_1);
lean_dec(x_55);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; uint8_t x_77; uint8_t x_82; 
x_82 = !lean_is_exclusive(x_75);
if (x_82 == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_75, 0);
lean_dec(x_83);
x_76 = x_75;
x_77 = x_82;
goto block_81;
}
else
{
lean_dec(x_75);
x_76 = lean_box(0);
x_77 = x_82;
goto block_81;
}
block_81:
{
lean_object* x_78; 
if (x_77 == 0)
{
lean_ctor_set(x_76, 0, x_54);
x_78 = x_76;
goto block_79;
}
else
{
lean_object* x_80; 
x_80 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_80, 0, x_54);
x_78 = x_80;
goto block_79;
}
block_79:
{
return x_78;
}
}
}
else
{
lean_dec(x_54);
return x_75;
}
}
}
}
else
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_84 = lean_ctor_get(x_53, 1);
lean_inc(x_84);
lean_dec_ref(x_53);
x_85 = lean_array_get_size(x_84);
x_86 = lean_nat_dec_lt(x_51, x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_84);
lean_dec_ref(x_1);
x_87 = lean_box(0);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
return x_88;
}
else
{
lean_object* x_89; uint8_t x_90; 
x_89 = lean_box(0);
x_90 = lean_nat_dec_le(x_85, x_85);
if (x_90 == 0)
{
if (x_86 == 0)
{
lean_dec(x_84);
lean_dec_ref(x_1);
x_35 = lean_box(0);
goto block_38;
}
else
{
size_t x_91; size_t x_92; lean_object* x_93; 
x_91 = 0;
x_92 = lean_usize_of_nat(x_85);
x_93 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_84, x_91, x_92, x_89, x_1);
lean_dec(x_84);
if (lean_obj_tag(x_93) == 0)
{
lean_dec_ref(x_93);
x_35 = lean_box(0);
goto block_38;
}
else
{
return x_93;
}
}
}
else
{
size_t x_94; size_t x_95; lean_object* x_96; 
x_94 = 0;
x_95 = lean_usize_of_nat(x_85);
x_96 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_84, x_94, x_95, x_89, x_1);
lean_dec(x_84);
if (lean_obj_tag(x_96) == 0)
{
lean_dec_ref(x_96);
x_35 = lean_box(0);
goto block_38;
}
else
{
return x_96;
}
}
}
}
}
else
{
uint8_t x_97; lean_object* x_98; lean_object* x_99; 
lean_dec_ref(x_39);
lean_inc_ref(x_3);
x_97 = l_Lake_GitRepo_hasNoDiff(x_3);
x_98 = lean_unsigned_to_nat(0u);
x_99 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
if (x_97 == 0)
{
x_20 = x_98;
x_21 = x_99;
x_22 = x_42;
x_23 = lean_box(0);
goto block_34;
}
else
{
uint8_t x_100; 
x_100 = 0;
x_20 = x_98;
x_21 = x_99;
x_22 = x_100;
x_23 = lean_box(0);
goto block_34;
}
}
}
block_105:
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_box(0);
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_103);
return x_104;
}
block_109:
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_box(0);
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_107);
return x_108;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(x_1, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
x_2 = lean_array_get_size(x_1);
return x_2;
}
}
static uint8_t _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_lt(x_2, x_1);
return x_3;
}
}
static uint8_t _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6(void) {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4);
x_2 = lean_nat_dec_le(x_1, x_1);
return x_2;
}
}
static size_t _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7(void) {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4);
x_2 = lean_usize_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; lean_object* x_8; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; 
x_44 = l_Lake_Git_defaultRemote;
lean_inc_ref(x_2);
x_45 = l_Lake_GitRepo_getRemoteUrl_x3f(x_44, x_2);
x_46 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
if (lean_obj_tag(x_45) == 1)
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_45, 0);
lean_inc(x_59);
lean_dec_ref(x_45);
x_60 = lean_string_dec_eq(x_59, x_3);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_io_realpath(x_59);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_dec_ref(x_61);
lean_inc_ref(x_3);
x_63 = lean_io_realpath(x_3);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; uint8_t x_65; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec_ref(x_63);
x_65 = lean_string_dec_eq(x_62, x_64);
lean_dec(x_64);
lean_dec(x_62);
x_47 = x_65;
x_48 = lean_box(0);
goto block_58;
}
else
{
lean_dec_ref(x_63);
lean_dec(x_62);
x_47 = x_60;
x_48 = lean_box(0);
goto block_58;
}
}
else
{
lean_dec_ref(x_61);
x_47 = x_60;
x_48 = lean_box(0);
goto block_58;
}
}
else
{
lean_dec(x_59);
x_47 = x_60;
x_48 = lean_box(0);
goto block_58;
}
}
else
{
uint8_t x_66; 
lean_dec(x_45);
x_66 = 0;
x_47 = x_66;
x_48 = lean_box(0);
goto block_58;
}
block_43:
{
if (x_7 == 0)
{
uint8_t x_9; 
x_9 = l_System_Platform_isWindows;
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__0));
lean_inc_ref(x_1);
x_11 = lean_string_append(x_1, x_10);
x_12 = lean_string_append(x_11, x_2);
x_13 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__1));
x_14 = lean_string_append(x_12, x_13);
x_15 = 1;
x_16 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_15);
lean_inc_ref(x_5);
x_17 = lean_apply_2(x_5, x_16, lean_box(0));
x_18 = l_IO_FS_removeDirAll(x_2);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
lean_dec_ref(x_18);
x_19 = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(x_5, x_1, x_2, x_3, x_4);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_32; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_20 = lean_ctor_get(x_18, 0);
x_32 = !lean_is_exclusive(x_18);
if (x_32 == 0)
{
x_21 = x_18;
x_22 = x_32;
goto block_31;
}
else
{
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_box(0);
x_22 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_io_error_to_string(x_20);
x_24 = 3;
x_25 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_24);
x_26 = lean_apply_2(x_5, x_25, lean_box(0));
x_27 = lean_box(0);
if (x_22 == 0)
{
lean_ctor_set(x_21, 0, x_27);
x_28 = x_21;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_27);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec_ref(x_3);
x_33 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__2));
lean_inc_ref(x_1);
x_34 = lean_string_append(x_1, x_33);
x_35 = lean_string_append(x_34, x_2);
x_36 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__3));
x_37 = lean_string_append(x_35, x_36);
x_38 = 1;
x_39 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set_uint8(x_39, sizeof(void*)*1, x_38);
lean_inc_ref(x_5);
x_40 = lean_apply_2(x_5, x_39, lean_box(0));
x_41 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(x_5, x_1, x_2, x_4);
return x_41;
}
}
else
{
lean_object* x_42; 
lean_dec_ref(x_3);
x_42 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(x_5, x_1, x_2, x_4);
return x_42;
}
}
block_58:
{
uint8_t x_49; 
x_49 = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (x_49 == 0)
{
x_7 = x_47;
x_8 = lean_box(0);
goto block_43;
}
else
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_box(0);
x_51 = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (x_51 == 0)
{
if (x_49 == 0)
{
x_7 = x_47;
x_8 = lean_box(0);
goto block_43;
}
else
{
size_t x_52; size_t x_53; lean_object* x_54; 
x_52 = 0;
x_53 = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
lean_inc_ref(x_5);
x_54 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_46, x_52, x_53, x_50, x_5);
if (lean_obj_tag(x_54) == 0)
{
lean_dec_ref(x_54);
x_7 = x_47;
x_8 = lean_box(0);
goto block_43;
}
else
{
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_54;
}
}
}
else
{
size_t x_55; size_t x_56; lean_object* x_57; 
x_55 = 0;
x_56 = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
lean_inc_ref(x_5);
x_57 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_46, x_55, x_56, x_50, x_5);
if (lean_obj_tag(x_57) == 0)
{
lean_dec_ref(x_57);
x_7 = x_47;
x_8 = lean_box(0);
goto block_43;
}
else
{
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_57;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; lean_object* x_8; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; 
x_44 = l_Lake_Git_defaultRemote;
lean_inc_ref(x_3);
x_45 = l_Lake_GitRepo_getRemoteUrl_x3f(x_44, x_3);
x_46 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
if (lean_obj_tag(x_45) == 1)
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_45, 0);
lean_inc(x_59);
lean_dec_ref(x_45);
x_60 = lean_string_dec_eq(x_59, x_4);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_io_realpath(x_59);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_dec_ref(x_61);
lean_inc_ref(x_4);
x_63 = lean_io_realpath(x_4);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; uint8_t x_65; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec_ref(x_63);
x_65 = lean_string_dec_eq(x_62, x_64);
lean_dec(x_64);
lean_dec(x_62);
x_47 = x_65;
x_48 = lean_box(0);
goto block_58;
}
else
{
lean_dec_ref(x_63);
lean_dec(x_62);
x_47 = x_60;
x_48 = lean_box(0);
goto block_58;
}
}
else
{
lean_dec_ref(x_61);
x_47 = x_60;
x_48 = lean_box(0);
goto block_58;
}
}
else
{
lean_dec(x_59);
x_47 = x_60;
x_48 = lean_box(0);
goto block_58;
}
}
else
{
uint8_t x_66; 
lean_dec(x_45);
x_66 = 0;
x_47 = x_66;
x_48 = lean_box(0);
goto block_58;
}
block_43:
{
if (x_7 == 0)
{
uint8_t x_9; 
x_9 = l_System_Platform_isWindows;
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__0));
lean_inc_ref(x_2);
x_11 = lean_string_append(x_2, x_10);
x_12 = lean_string_append(x_11, x_3);
x_13 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__1));
x_14 = lean_string_append(x_12, x_13);
x_15 = 1;
x_16 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_15);
lean_inc_ref(x_1);
x_17 = lean_apply_2(x_1, x_16, lean_box(0));
x_18 = l_IO_FS_removeDirAll(x_3);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
lean_dec_ref(x_18);
x_19 = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(x_1, x_2, x_3, x_4, x_5);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_32; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_20 = lean_ctor_get(x_18, 0);
x_32 = !lean_is_exclusive(x_18);
if (x_32 == 0)
{
x_21 = x_18;
x_22 = x_32;
goto block_31;
}
else
{
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_box(0);
x_22 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_io_error_to_string(x_20);
x_24 = 3;
x_25 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_24);
x_26 = lean_apply_2(x_1, x_25, lean_box(0));
x_27 = lean_box(0);
if (x_22 == 0)
{
lean_ctor_set(x_21, 0, x_27);
x_28 = x_21;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_27);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec_ref(x_4);
x_33 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__2));
lean_inc_ref(x_2);
x_34 = lean_string_append(x_2, x_33);
x_35 = lean_string_append(x_34, x_3);
x_36 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__3));
x_37 = lean_string_append(x_35, x_36);
x_38 = 1;
x_39 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set_uint8(x_39, sizeof(void*)*1, x_38);
lean_inc_ref(x_1);
x_40 = lean_apply_2(x_1, x_39, lean_box(0));
x_41 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(x_1, x_2, x_3, x_5);
return x_41;
}
}
else
{
lean_object* x_42; 
lean_dec_ref(x_4);
x_42 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(x_1, x_2, x_3, x_5);
return x_42;
}
}
block_58:
{
uint8_t x_49; 
x_49 = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (x_49 == 0)
{
x_7 = x_47;
x_8 = lean_box(0);
goto block_43;
}
else
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_box(0);
x_51 = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (x_51 == 0)
{
if (x_49 == 0)
{
x_7 = x_47;
x_8 = lean_box(0);
goto block_43;
}
else
{
size_t x_52; size_t x_53; lean_object* x_54; 
x_52 = 0;
x_53 = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
lean_inc_ref(x_1);
x_54 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_46, x_52, x_53, x_50, x_1);
if (lean_obj_tag(x_54) == 0)
{
lean_dec_ref(x_54);
x_7 = x_47;
x_8 = lean_box(0);
goto block_43;
}
else
{
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_54;
}
}
}
else
{
size_t x_55; size_t x_56; lean_object* x_57; 
x_55 = 0;
x_56 = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
lean_inc_ref(x_1);
x_57 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_46, x_55, x_56, x_50, x_1);
if (lean_obj_tag(x_57) == 0)
{
lean_dec_ref(x_57);
x_7 = x_47;
x_8 = lean_box(0);
goto block_43;
}
else
{
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_57;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; lean_object* x_8; lean_object* x_12; uint8_t x_13; 
x_7 = l_System_FilePath_isDir(x_2);
x_12 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
x_13 = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (x_13 == 0)
{
x_8 = lean_box(0);
goto block_11;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_box(0);
x_15 = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (x_15 == 0)
{
if (x_13 == 0)
{
x_8 = lean_box(0);
goto block_11;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = 0;
x_17 = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
lean_inc_ref(x_5);
x_18 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_12, x_16, x_17, x_14, x_5);
if (lean_obj_tag(x_18) == 0)
{
lean_dec_ref(x_18);
x_8 = lean_box(0);
goto block_11;
}
else
{
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_18;
}
}
}
else
{
size_t x_19; size_t x_20; lean_object* x_21; 
x_19 = 0;
x_20 = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
lean_inc_ref(x_5);
x_21 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_12, x_19, x_20, x_14, x_5);
if (lean_obj_tag(x_21) == 0)
{
lean_dec_ref(x_21);
x_8 = lean_box(0);
goto block_11;
}
else
{
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_21;
}
}
}
block_11:
{
if (x_7 == 0)
{
lean_object* x_9; 
x_9 = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(x_5, x_1, x_2, x_3, x_4);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(x_5, x_1, x_2, x_3, x_4);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Lake_instInhabitedMaterializedDep_default___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_instInhabitedPackageEntry_default;
x_2 = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
x_3 = l_System_instInhabitedFilePath_default;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_instInhabitedMaterializedDep_default(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lake_instInhabitedMaterializedDep_default___closed__1, &l_Lake_instInhabitedMaterializedDep_default___closed__1_once, _init_l_Lake_instInhabitedMaterializedDep_default___closed__1);
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedMaterializedDep(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instInhabitedMaterializedDep_default;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_name(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_name___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_MaterializedDep_name(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_scope(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_scope___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_MaterializedDep_scope(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_manifestFile_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = lean_ctor_get(x_2, 3);
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_manifestFile_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_MaterializedDep_manifestFile_x3f(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_configFile(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_configFile___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_MaterializedDep_configFile(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorIdx(lean_object* x_1) {
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
default: 
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorIdx(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
lean_dec(x_1);
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_none_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_none_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_git_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_git_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ver_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ver_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_27; 
x_27 = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
x_4 = x_27;
x_5 = x_27;
goto block_26;
}
case 1:
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_43; 
x_28 = lean_ctor_get(x_3, 0);
x_43 = !lean_is_exclusive(x_3);
if (x_43 == 0)
{
x_29 = x_3;
x_30 = x_43;
goto block_42;
}
else
{
lean_inc(x_28);
lean_dec(x_3);
x_29 = lean_box(0);
x_30 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__5));
x_32 = l_String_quote(x_28);
if (x_30 == 0)
{
lean_ctor_set_tag(x_29, 3);
lean_ctor_set(x_29, 0, x_32);
x_33 = x_29;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_41, 0, x_32);
x_33 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = l_Std_Format_defWidth;
x_35 = lean_unsigned_to_nat(0u);
x_36 = l_Std_Format_pretty(x_33, x_34, x_35, x_35);
x_37 = lean_string_append(x_31, x_36);
x_38 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__6));
x_39 = lean_string_append(x_38, x_36);
lean_dec_ref(x_36);
x_4 = x_37;
x_5 = x_39;
goto block_26;
}
}
}
default: 
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_60; 
x_44 = lean_ctor_get(x_3, 0);
x_60 = !lean_is_exclusive(x_3);
if (x_60 == 0)
{
x_45 = x_3;
x_46 = x_60;
goto block_59;
}
else
{
lean_inc(x_44);
lean_dec(x_3);
x_45 = lean_box(0);
x_46 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_44, 0);
lean_inc_ref(x_47);
lean_dec_ref(x_44);
x_48 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__5));
x_49 = l_String_quote(x_47);
if (x_46 == 0)
{
lean_ctor_set_tag(x_45, 3);
lean_ctor_set(x_45, 0, x_49);
x_50 = x_45;
goto block_57;
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_58, 0, x_49);
x_50 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_51 = l_Std_Format_defWidth;
x_52 = lean_unsigned_to_nat(0u);
x_53 = l_Std_Format_pretty(x_50, x_51, x_52, x_52);
x_54 = lean_string_append(x_48, x_53);
x_55 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__7));
x_56 = lean_string_append(x_55, x_53);
lean_dec_ref(x_53);
x_4 = x_54;
x_5 = x_56;
goto block_26;
}
}
}
}
block_26:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_6 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
lean_inc_ref(x_1);
x_7 = lean_string_append(x_1, x_6);
x_8 = lean_string_append(x_7, x_2);
x_9 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__1));
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_string_append(x_10, x_1);
x_12 = lean_string_append(x_11, x_6);
x_13 = lean_string_append(x_12, x_2);
x_14 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__2));
x_15 = lean_string_append(x_13, x_14);
x_16 = lean_string_append(x_15, x_4);
lean_dec_ref(x_4);
x_17 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__3));
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_string_append(x_18, x_1);
lean_dec_ref(x_1);
x_20 = lean_string_append(x_19, x_6);
x_21 = lean_string_append(x_20, x_2);
x_22 = lean_string_append(x_21, x_14);
x_23 = lean_string_append(x_22, x_5);
lean_dec_ref(x_5);
x_24 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__4));
x_25 = lean_string_append(x_23, x_24);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = l_Lake_defaultConfigFile;
x_9 = lean_box(0);
lean_inc_ref(x_7);
lean_inc(x_6);
x_10 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_7);
lean_ctor_set(x_10, 2, x_8);
lean_ctor_set(x_10, 3, x_9);
lean_ctor_set(x_10, 4, x_5);
lean_ctor_set_uint8(x_10, sizeof(void*)*5, x_2);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_4);
lean_ctor_set(x_11, 2, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
x_7 = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep(x_1, x_6, x_3, x_4, x_5);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; lean_object* x_8; lean_object* x_12; uint8_t x_13; 
x_7 = l_System_FilePath_isDir(x_3);
x_12 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
x_13 = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (x_13 == 0)
{
x_8 = lean_box(0);
goto block_11;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_box(0);
x_15 = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (x_15 == 0)
{
if (x_13 == 0)
{
x_8 = lean_box(0);
goto block_11;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = 0;
x_17 = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
lean_inc_ref(x_1);
x_18 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_12, x_16, x_17, x_14, x_1);
if (lean_obj_tag(x_18) == 0)
{
lean_dec_ref(x_18);
x_8 = lean_box(0);
goto block_11;
}
else
{
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_18;
}
}
}
else
{
size_t x_19; size_t x_20; lean_object* x_21; 
x_19 = 0;
x_20 = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
lean_inc_ref(x_1);
x_21 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_12, x_19, x_20, x_14, x_1);
if (lean_obj_tag(x_21) == 0)
{
lean_dec_ref(x_21);
x_8 = lean_box(0);
goto block_11;
}
else
{
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_21;
}
}
}
block_11:
{
if (x_7 == 0)
{
lean_object* x_9; 
x_9 = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(x_1, x_2, x_3, x_4, x_5);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(x_1, x_2, x_3, x_4, x_5);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_37; lean_object* x_38; lean_object* x_116; 
x_17 = lean_ctor_get(x_3, 5);
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_6);
x_37 = l_Lake_joinRelative(x_4, x_6);
x_116 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_17, x_18);
if (lean_obj_tag(x_116) == 0)
{
x_38 = x_7;
goto block_115;
}
else
{
lean_object* x_117; 
lean_dec_ref(x_7);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
lean_dec_ref(x_116);
x_38 = x_117;
goto block_115;
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
block_30:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_20);
lean_ctor_set(x_24, 2, x_9);
lean_ctor_set(x_24, 3, x_10);
x_25 = l_Lake_defaultConfigFile;
x_26 = lean_box(0);
lean_inc_ref(x_19);
lean_inc(x_18);
x_27 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_27, 0, x_18);
lean_ctor_set(x_27, 1, x_19);
lean_ctor_set(x_27, 2, x_25);
lean_ctor_set(x_27, 3, x_26);
lean_ctor_set(x_27, 4, x_24);
lean_ctor_set_uint8(x_27, sizeof(void*)*5, x_2);
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_8);
lean_ctor_set(x_28, 2, x_27);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
block_36:
{
if (lean_obj_tag(x_10) == 1)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_10, 0);
lean_inc(x_34);
x_35 = l_Lake_joinRelative(x_6, x_34);
x_20 = x_32;
x_21 = lean_box(0);
x_22 = x_31;
x_23 = x_35;
goto block_30;
}
else
{
x_20 = x_32;
x_21 = lean_box(0);
x_22 = x_31;
x_23 = x_6;
goto block_30;
}
}
block_115:
{
lean_object* x_39; 
lean_inc(x_9);
lean_inc_ref(x_38);
lean_inc_ref(x_37);
lean_inc_ref(x_11);
x_39 = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(x_11, x_5, x_37, x_38, x_9);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; uint8_t x_41; uint8_t x_105; 
x_105 = !lean_is_exclusive(x_39);
if (x_105 == 0)
{
lean_object* x_106; 
x_106 = lean_ctor_get(x_39, 0);
lean_dec(x_106);
x_40 = x_39;
x_41 = x_105;
goto block_104;
}
else
{
lean_dec(x_39);
x_40 = lean_box(0);
x_41 = x_105;
goto block_104;
}
block_104:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_unsigned_to_nat(0u);
x_43 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
x_44 = l_Lake_GitRepo_getHeadRevision(x_37, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
lean_del_object(x_40);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec_ref(x_44);
x_47 = lean_array_get_size(x_46);
x_48 = lean_nat_dec_lt(x_42, x_47);
if (x_48 == 0)
{
lean_dec(x_46);
lean_dec_ref(x_11);
x_31 = x_38;
x_32 = x_45;
x_33 = lean_box(0);
goto block_36;
}
else
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_box(0);
x_50 = lean_nat_dec_le(x_47, x_47);
if (x_50 == 0)
{
if (x_48 == 0)
{
lean_dec(x_46);
lean_dec_ref(x_11);
x_31 = x_38;
x_32 = x_45;
x_33 = lean_box(0);
goto block_36;
}
else
{
size_t x_51; size_t x_52; lean_object* x_53; 
x_51 = 0;
x_52 = lean_usize_of_nat(x_47);
x_53 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_46, x_51, x_52, x_49, x_11);
lean_dec(x_46);
if (lean_obj_tag(x_53) == 0)
{
lean_dec_ref(x_53);
x_31 = x_38;
x_32 = x_45;
x_33 = lean_box(0);
goto block_36;
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_61; 
lean_dec(x_45);
lean_dec_ref(x_38);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
x_54 = lean_ctor_get(x_53, 0);
x_61 = !lean_is_exclusive(x_53);
if (x_61 == 0)
{
x_55 = x_53;
x_56 = x_61;
goto block_60;
}
else
{
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_box(0);
x_56 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_57; 
if (x_56 == 0)
{
x_57 = x_55;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_54);
x_57 = x_59;
goto block_58;
}
block_58:
{
return x_57;
}
}
}
}
}
else
{
size_t x_62; size_t x_63; lean_object* x_64; 
x_62 = 0;
x_63 = lean_usize_of_nat(x_47);
x_64 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_46, x_62, x_63, x_49, x_11);
lean_dec(x_46);
if (lean_obj_tag(x_64) == 0)
{
lean_dec_ref(x_64);
x_31 = x_38;
x_32 = x_45;
x_33 = lean_box(0);
goto block_36;
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; uint8_t x_72; 
lean_dec(x_45);
lean_dec_ref(x_38);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
x_65 = lean_ctor_get(x_64, 0);
x_72 = !lean_is_exclusive(x_64);
if (x_72 == 0)
{
x_66 = x_64;
x_67 = x_72;
goto block_71;
}
else
{
lean_inc(x_65);
lean_dec(x_64);
x_66 = lean_box(0);
x_67 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_68; 
if (x_67 == 0)
{
x_68 = x_66;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_65);
x_68 = x_70;
goto block_69;
}
block_69:
{
return x_68;
}
}
}
}
}
}
else
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; 
lean_dec_ref(x_38);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
x_73 = lean_ctor_get(x_44, 1);
lean_inc(x_73);
lean_dec_ref(x_44);
x_74 = lean_array_get_size(x_73);
x_75 = lean_nat_dec_lt(x_42, x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_73);
lean_dec_ref(x_11);
x_76 = lean_box(0);
if (x_41 == 0)
{
lean_ctor_set_tag(x_40, 1);
lean_ctor_set(x_40, 0, x_76);
x_77 = x_40;
goto block_78;
}
else
{
lean_object* x_79; 
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_76);
x_77 = x_79;
goto block_78;
}
block_78:
{
return x_77;
}
}
else
{
lean_object* x_80; uint8_t x_81; 
lean_del_object(x_40);
x_80 = lean_box(0);
x_81 = lean_nat_dec_le(x_74, x_74);
if (x_81 == 0)
{
if (x_75 == 0)
{
lean_dec(x_73);
lean_dec_ref(x_11);
x_13 = lean_box(0);
goto block_16;
}
else
{
size_t x_82; size_t x_83; lean_object* x_84; 
x_82 = 0;
x_83 = lean_usize_of_nat(x_74);
x_84 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_73, x_82, x_83, x_80, x_11);
lean_dec(x_73);
if (lean_obj_tag(x_84) == 0)
{
lean_dec_ref(x_84);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; uint8_t x_92; 
x_85 = lean_ctor_get(x_84, 0);
x_92 = !lean_is_exclusive(x_84);
if (x_92 == 0)
{
x_86 = x_84;
x_87 = x_92;
goto block_91;
}
else
{
lean_inc(x_85);
lean_dec(x_84);
x_86 = lean_box(0);
x_87 = x_92;
goto block_91;
}
block_91:
{
lean_object* x_88; 
if (x_87 == 0)
{
x_88 = x_86;
goto block_89;
}
else
{
lean_object* x_90; 
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_85);
x_88 = x_90;
goto block_89;
}
block_89:
{
return x_88;
}
}
}
}
}
else
{
size_t x_93; size_t x_94; lean_object* x_95; 
x_93 = 0;
x_94 = lean_usize_of_nat(x_74);
x_95 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_73, x_93, x_94, x_80, x_11);
lean_dec(x_73);
if (lean_obj_tag(x_95) == 0)
{
lean_dec_ref(x_95);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_96; lean_object* x_97; uint8_t x_98; uint8_t x_103; 
x_96 = lean_ctor_get(x_95, 0);
x_103 = !lean_is_exclusive(x_95);
if (x_103 == 0)
{
x_97 = x_95;
x_98 = x_103;
goto block_102;
}
else
{
lean_inc(x_96);
lean_dec(x_95);
x_97 = lean_box(0);
x_98 = x_103;
goto block_102;
}
block_102:
{
lean_object* x_99; 
if (x_98 == 0)
{
x_99 = x_97;
goto block_100;
}
else
{
lean_object* x_101; 
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_96);
x_99 = x_101;
goto block_100;
}
block_100:
{
return x_99;
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
lean_object* x_107; lean_object* x_108; uint8_t x_109; uint8_t x_114; 
lean_dec_ref(x_38);
lean_dec_ref(x_37);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
x_107 = lean_ctor_get(x_39, 0);
x_114 = !lean_is_exclusive(x_39);
if (x_114 == 0)
{
x_108 = x_39;
x_109 = x_114;
goto block_113;
}
else
{
lean_inc(x_107);
lean_dec(x_39);
x_108 = lean_box(0);
x_109 = x_114;
goto block_113;
}
block_113:
{
lean_object* x_110; 
if (x_109 == 0)
{
x_110 = x_108;
goto block_111;
}
else
{
lean_object* x_112; 
x_112 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_112, 0, x_107);
x_110 = x_112;
goto block_111;
}
block_111:
{
return x_110;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
x_14 = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_37; lean_object* x_38; lean_object* x_116; 
x_17 = lean_ctor_get(x_4, 5);
x_18 = lean_ctor_get(x_2, 0);
x_19 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_7);
x_37 = l_Lake_joinRelative(x_5, x_7);
x_116 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_17, x_18);
if (lean_obj_tag(x_116) == 0)
{
x_38 = x_8;
goto block_115;
}
else
{
lean_object* x_117; 
lean_dec_ref(x_8);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
lean_dec_ref(x_116);
x_38 = x_117;
goto block_115;
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
block_30:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_10);
lean_ctor_set(x_24, 3, x_11);
x_25 = l_Lake_defaultConfigFile;
x_26 = lean_box(0);
lean_inc_ref(x_19);
lean_inc(x_18);
x_27 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_27, 0, x_18);
lean_ctor_set(x_27, 1, x_19);
lean_ctor_set(x_27, 2, x_25);
lean_ctor_set(x_27, 3, x_26);
lean_ctor_set(x_27, 4, x_24);
lean_ctor_set_uint8(x_27, sizeof(void*)*5, x_3);
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_9);
lean_ctor_set(x_28, 2, x_27);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
block_36:
{
if (lean_obj_tag(x_11) == 1)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_11, 0);
lean_inc(x_34);
x_35 = l_Lake_joinRelative(x_7, x_34);
x_20 = x_31;
x_21 = x_32;
x_22 = lean_box(0);
x_23 = x_35;
goto block_30;
}
else
{
x_20 = x_31;
x_21 = x_32;
x_22 = lean_box(0);
x_23 = x_7;
goto block_30;
}
}
block_115:
{
lean_object* x_39; 
lean_inc(x_10);
lean_inc_ref(x_38);
lean_inc_ref(x_37);
lean_inc_ref(x_1);
x_39 = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(x_1, x_6, x_37, x_38, x_10);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; uint8_t x_41; uint8_t x_105; 
x_105 = !lean_is_exclusive(x_39);
if (x_105 == 0)
{
lean_object* x_106; 
x_106 = lean_ctor_get(x_39, 0);
lean_dec(x_106);
x_40 = x_39;
x_41 = x_105;
goto block_104;
}
else
{
lean_dec(x_39);
x_40 = lean_box(0);
x_41 = x_105;
goto block_104;
}
block_104:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_unsigned_to_nat(0u);
x_43 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
x_44 = l_Lake_GitRepo_getHeadRevision(x_37, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
lean_del_object(x_40);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec_ref(x_44);
x_47 = lean_array_get_size(x_46);
x_48 = lean_nat_dec_lt(x_42, x_47);
if (x_48 == 0)
{
lean_dec(x_46);
lean_dec_ref(x_1);
x_31 = x_38;
x_32 = x_45;
x_33 = lean_box(0);
goto block_36;
}
else
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_box(0);
x_50 = lean_nat_dec_le(x_47, x_47);
if (x_50 == 0)
{
if (x_48 == 0)
{
lean_dec(x_46);
lean_dec_ref(x_1);
x_31 = x_38;
x_32 = x_45;
x_33 = lean_box(0);
goto block_36;
}
else
{
size_t x_51; size_t x_52; lean_object* x_53; 
x_51 = 0;
x_52 = lean_usize_of_nat(x_47);
x_53 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_46, x_51, x_52, x_49, x_1);
lean_dec(x_46);
if (lean_obj_tag(x_53) == 0)
{
lean_dec_ref(x_53);
x_31 = x_38;
x_32 = x_45;
x_33 = lean_box(0);
goto block_36;
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_61; 
lean_dec(x_45);
lean_dec_ref(x_38);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
x_54 = lean_ctor_get(x_53, 0);
x_61 = !lean_is_exclusive(x_53);
if (x_61 == 0)
{
x_55 = x_53;
x_56 = x_61;
goto block_60;
}
else
{
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_box(0);
x_56 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_57; 
if (x_56 == 0)
{
x_57 = x_55;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_54);
x_57 = x_59;
goto block_58;
}
block_58:
{
return x_57;
}
}
}
}
}
else
{
size_t x_62; size_t x_63; lean_object* x_64; 
x_62 = 0;
x_63 = lean_usize_of_nat(x_47);
x_64 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_46, x_62, x_63, x_49, x_1);
lean_dec(x_46);
if (lean_obj_tag(x_64) == 0)
{
lean_dec_ref(x_64);
x_31 = x_38;
x_32 = x_45;
x_33 = lean_box(0);
goto block_36;
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; uint8_t x_72; 
lean_dec(x_45);
lean_dec_ref(x_38);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
x_65 = lean_ctor_get(x_64, 0);
x_72 = !lean_is_exclusive(x_64);
if (x_72 == 0)
{
x_66 = x_64;
x_67 = x_72;
goto block_71;
}
else
{
lean_inc(x_65);
lean_dec(x_64);
x_66 = lean_box(0);
x_67 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_68; 
if (x_67 == 0)
{
x_68 = x_66;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_65);
x_68 = x_70;
goto block_69;
}
block_69:
{
return x_68;
}
}
}
}
}
}
else
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; 
lean_dec_ref(x_38);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
x_73 = lean_ctor_get(x_44, 1);
lean_inc(x_73);
lean_dec_ref(x_44);
x_74 = lean_array_get_size(x_73);
x_75 = lean_nat_dec_lt(x_42, x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_73);
lean_dec_ref(x_1);
x_76 = lean_box(0);
if (x_41 == 0)
{
lean_ctor_set_tag(x_40, 1);
lean_ctor_set(x_40, 0, x_76);
x_77 = x_40;
goto block_78;
}
else
{
lean_object* x_79; 
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_76);
x_77 = x_79;
goto block_78;
}
block_78:
{
return x_77;
}
}
else
{
lean_object* x_80; uint8_t x_81; 
lean_del_object(x_40);
x_80 = lean_box(0);
x_81 = lean_nat_dec_le(x_74, x_74);
if (x_81 == 0)
{
if (x_75 == 0)
{
lean_dec(x_73);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
size_t x_82; size_t x_83; lean_object* x_84; 
x_82 = 0;
x_83 = lean_usize_of_nat(x_74);
x_84 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_73, x_82, x_83, x_80, x_1);
lean_dec(x_73);
if (lean_obj_tag(x_84) == 0)
{
lean_dec_ref(x_84);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; uint8_t x_92; 
x_85 = lean_ctor_get(x_84, 0);
x_92 = !lean_is_exclusive(x_84);
if (x_92 == 0)
{
x_86 = x_84;
x_87 = x_92;
goto block_91;
}
else
{
lean_inc(x_85);
lean_dec(x_84);
x_86 = lean_box(0);
x_87 = x_92;
goto block_91;
}
block_91:
{
lean_object* x_88; 
if (x_87 == 0)
{
x_88 = x_86;
goto block_89;
}
else
{
lean_object* x_90; 
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_85);
x_88 = x_90;
goto block_89;
}
block_89:
{
return x_88;
}
}
}
}
}
else
{
size_t x_93; size_t x_94; lean_object* x_95; 
x_93 = 0;
x_94 = lean_usize_of_nat(x_74);
x_95 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_73, x_93, x_94, x_80, x_1);
lean_dec(x_73);
if (lean_obj_tag(x_95) == 0)
{
lean_dec_ref(x_95);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_96; lean_object* x_97; uint8_t x_98; uint8_t x_103; 
x_96 = lean_ctor_get(x_95, 0);
x_103 = !lean_is_exclusive(x_95);
if (x_103 == 0)
{
x_97 = x_95;
x_98 = x_103;
goto block_102;
}
else
{
lean_inc(x_96);
lean_dec(x_95);
x_97 = lean_box(0);
x_98 = x_103;
goto block_102;
}
block_102:
{
lean_object* x_99; 
if (x_98 == 0)
{
x_99 = x_97;
goto block_100;
}
else
{
lean_object* x_101; 
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_96);
x_99 = x_101;
goto block_100;
}
block_100:
{
return x_99;
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
lean_object* x_107; lean_object* x_108; uint8_t x_109; uint8_t x_114; 
lean_dec_ref(x_38);
lean_dec_ref(x_37);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_107 = lean_ctor_get(x_39, 0);
x_114 = !lean_is_exclusive(x_39);
if (x_114 == 0)
{
x_108 = x_39;
x_109 = x_114;
goto block_113;
}
else
{
lean_inc(x_107);
lean_dec(x_39);
x_108 = lean_box(0);
x_109 = x_114;
goto block_113;
}
block_113:
{
lean_object* x_110; 
if (x_109 == 0)
{
x_110 = x_108;
goto block_111;
}
else
{
lean_object* x_112; 
x_112 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_112, 0, x_107);
x_110 = x_112;
goto block_111;
}
block_111:
{
return x_110;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
x_14 = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
return x_14;
}
}
static lean_object* _init_l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__0));
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = ((lean_object*)(l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__0));
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = lean_obj_once(&l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__1, &l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__1_once, _init_l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__1);
x_5 = lean_nat_dec_le(x_4, x_3);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec_ref(x_1);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_string_memcmp(x_1, x_2, x_7, x_7, x_4);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec_ref(x_1);
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc_ref(x_1);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_7);
lean_ctor_set(x_10, 2, x_3);
x_11 = l_String_Slice_pos_x21(x_10, x_4);
lean_dec_ref(x_10);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 2, x_3);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_4, x_3);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_dec_ref(x_5);
x_7 = lean_array_uget_borrowed(x_2, x_4);
x_8 = lean_ctor_get(x_7, 0);
x_9 = lean_box(0);
x_10 = l_Lake_VerRange_test(x_1, x_8);
if (x_10 == 0)
{
lean_object* x_11; size_t x_12; size_t x_13; 
x_11 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___closed__0));
x_12 = 1;
x_13 = lean_usize_add(x_4, x_12);
x_4 = x_13;
x_5 = x_11;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_inc(x_7);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_7);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_9);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_47 = lean_ctor_get(x_1, 0);
x_48 = lean_ctor_get(x_1, 1);
x_49 = lean_ctor_get(x_1, 2);
x_50 = lean_ctor_get(x_1, 3);
lean_inc(x_50);
if (lean_obj_tag(x_50) == 1)
{
lean_object* x_121; lean_object* x_122; uint8_t x_123; uint8_t x_154; 
x_121 = lean_ctor_get(x_50, 0);
x_154 = !lean_is_exclusive(x_50);
if (x_154 == 0)
{
x_122 = x_50;
x_123 = x_154;
goto block_153;
}
else
{
lean_inc(x_121);
lean_dec(x_50);
x_122 = lean_box(0);
x_123 = x_154;
goto block_153;
}
block_153:
{
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_124; lean_object* x_125; uint8_t x_126; uint8_t x_140; 
lean_inc_ref(x_48);
lean_inc(x_47);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_124 = lean_ctor_get(x_121, 0);
x_140 = !lean_is_exclusive(x_121);
if (x_140 == 0)
{
x_125 = x_121;
x_126 = x_140;
goto block_139;
}
else
{
lean_inc(x_124);
lean_dec(x_121);
x_125 = lean_box(0);
x_126 = x_140;
goto block_139;
}
block_139:
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = l_Lake_joinRelative(x_6, x_124);
x_128 = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
lean_inc_ref(x_127);
if (x_126 == 0)
{
lean_ctor_set(x_125, 0, x_127);
x_129 = x_125;
goto block_137;
}
else
{
lean_object* x_138; 
x_138 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_138, 0, x_127);
x_129 = x_138;
goto block_137;
}
block_137:
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_130 = l_Lake_defaultConfigFile;
x_131 = lean_box(0);
x_132 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_132, 0, x_47);
lean_ctor_set(x_132, 1, x_48);
lean_ctor_set(x_132, 2, x_130);
lean_ctor_set(x_132, 3, x_131);
lean_ctor_set(x_132, 4, x_129);
lean_ctor_set_uint8(x_132, sizeof(void*)*5, x_2);
x_133 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_133, 0, x_127);
lean_ctor_set(x_133, 1, x_128);
lean_ctor_set(x_133, 2, x_132);
if (x_123 == 0)
{
lean_ctor_set_tag(x_122, 0);
lean_ctor_set(x_122, 0, x_133);
x_134 = x_122;
goto block_135;
}
else
{
lean_object* x_136; 
x_136 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_136, 0, x_133);
x_134 = x_136;
goto block_135;
}
block_135:
{
return x_134;
}
}
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; lean_object* x_145; lean_object* x_146; lean_object* x_150; 
lean_del_object(x_122);
lean_dec_ref(x_6);
x_141 = lean_ctor_get(x_121, 0);
lean_inc_ref(x_141);
x_142 = lean_ctor_get(x_121, 1);
lean_inc(x_142);
x_143 = lean_ctor_get(x_121, 2);
lean_inc(x_143);
lean_dec_ref(x_121);
x_144 = 0;
lean_inc(x_47);
x_145 = l_Lean_Name_toString(x_47, x_144);
lean_inc_ref(x_141);
x_150 = l_Lake_Git_filterUrl_x3f(x_141);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; 
x_151 = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
x_146 = x_151;
goto block_149;
}
else
{
lean_object* x_152; 
x_152 = lean_ctor_get(x_150, 0);
lean_inc(x_152);
lean_dec_ref(x_150);
x_146 = x_152;
goto block_149;
}
block_149:
{
lean_object* x_147; lean_object* x_148; 
lean_inc_ref(x_145);
x_147 = l_Lake_joinRelative(x_5, x_145);
x_148 = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(x_7, x_1, x_2, x_3, x_4, x_145, x_147, x_141, x_146, x_142, x_143);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_148;
}
}
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; uint8_t x_362; lean_object* x_363; lean_object* x_364; 
lean_dec(x_50);
lean_dec_ref(x_6);
x_155 = lean_string_utf8_byte_size(x_48);
x_156 = lean_unsigned_to_nat(0u);
x_362 = lean_nat_dec_eq(x_155, x_156);
if (x_362 == 0)
{
if (lean_obj_tag(x_49) == 1)
{
lean_object* x_375; lean_object* x_376; 
x_375 = lean_ctor_get(x_49, 0);
lean_inc(x_375);
x_376 = l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg(x_375);
if (lean_obj_tag(x_376) == 1)
{
lean_object* x_377; lean_object* x_378; uint8_t x_379; uint8_t x_385; 
x_377 = lean_ctor_get(x_376, 0);
x_385 = !lean_is_exclusive(x_376);
if (x_385 == 0)
{
x_378 = x_376;
x_379 = x_385;
goto block_384;
}
else
{
lean_inc(x_377);
lean_dec(x_376);
x_378 = lean_box(0);
x_379 = x_385;
goto block_384;
}
block_384:
{
lean_object* x_380; lean_object* x_381; 
x_380 = l_String_Slice_toString(x_377);
lean_dec(x_377);
if (x_379 == 0)
{
lean_ctor_set(x_378, 0, x_380);
x_381 = x_378;
goto block_382;
}
else
{
lean_object* x_383; 
x_383 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_383, 0, x_380);
x_381 = x_383;
goto block_382;
}
block_382:
{
x_363 = x_381;
x_364 = lean_box(0);
goto block_374;
}
}
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; 
lean_dec(x_376);
x_386 = ((lean_object*)(l_Lake_Dependency_materialize___closed__8));
x_387 = lean_string_utf8_byte_size(x_375);
lean_inc(x_375);
x_388 = l___private_Lake_Util_Version_0__Lake_runVerParse(lean_box(0), x_375, x_386, x_156, x_387);
if (lean_obj_tag(x_388) == 0)
{
lean_object* x_389; lean_object* x_390; uint8_t x_391; uint8_t x_405; 
lean_inc(x_47);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_389 = lean_ctor_get(x_388, 0);
x_405 = !lean_is_exclusive(x_388);
if (x_405 == 0)
{
x_390 = x_388;
x_391 = x_405;
goto block_404;
}
else
{
lean_inc(x_389);
lean_dec(x_388);
x_390 = lean_box(0);
x_391 = x_405;
goto block_404;
}
block_404:
{
uint8_t x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; uint8_t x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; 
x_392 = 1;
x_393 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_47, x_392);
x_394 = ((lean_object*)(l_Lake_Dependency_materialize___closed__9));
x_395 = lean_string_append(x_393, x_394);
x_396 = lean_string_append(x_395, x_389);
lean_dec(x_389);
x_397 = 3;
x_398 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_398, 0, x_396);
lean_ctor_set_uint8(x_398, sizeof(void*)*1, x_397);
x_399 = lean_apply_2(x_7, x_398, lean_box(0));
x_400 = lean_box(0);
if (x_391 == 0)
{
lean_ctor_set_tag(x_390, 1);
lean_ctor_set(x_390, 0, x_400);
x_401 = x_390;
goto block_402;
}
else
{
lean_object* x_403; 
x_403 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_403, 0, x_400);
x_401 = x_403;
goto block_402;
}
block_402:
{
return x_401;
}
}
}
else
{
lean_object* x_406; lean_object* x_407; uint8_t x_408; uint8_t x_413; 
x_406 = lean_ctor_get(x_388, 0);
x_413 = !lean_is_exclusive(x_388);
if (x_413 == 0)
{
x_407 = x_388;
x_408 = x_413;
goto block_412;
}
else
{
lean_inc(x_406);
lean_dec(x_388);
x_407 = lean_box(0);
x_408 = x_413;
goto block_412;
}
block_412:
{
lean_object* x_409; 
if (x_408 == 0)
{
lean_ctor_set_tag(x_407, 2);
x_409 = x_407;
goto block_410;
}
else
{
lean_object* x_411; 
x_411 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_411, 0, x_406);
x_409 = x_411;
goto block_410;
}
block_410:
{
x_363 = x_409;
x_364 = lean_box(0);
goto block_374;
}
}
}
}
}
else
{
lean_object* x_414; 
x_414 = lean_box(0);
x_363 = x_414;
x_364 = lean_box(0);
goto block_374;
}
}
else
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; uint8_t x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; 
lean_inc(x_47);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_415 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_47, x_362);
x_416 = ((lean_object*)(l_Lake_Dependency_materialize___closed__10));
x_417 = lean_string_append(x_415, x_416);
x_418 = 3;
x_419 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_419, 0, x_417);
lean_ctor_set_uint8(x_419, sizeof(void*)*1, x_418);
x_420 = lean_apply_2(x_7, x_419, lean_box(0));
x_421 = lean_box(0);
x_422 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_422, 0, x_421);
return x_422;
}
block_193:
{
lean_object* x_167; uint8_t x_168; 
x_167 = lean_array_get_size(x_165);
x_168 = lean_nat_dec_lt(x_156, x_167);
if (x_168 == 0)
{
lean_dec_ref(x_165);
x_69 = x_157;
x_70 = x_158;
x_71 = x_159;
x_72 = x_160;
x_73 = x_161;
x_74 = x_162;
x_75 = x_163;
x_76 = x_164;
x_77 = lean_box(0);
goto block_120;
}
else
{
lean_object* x_169; uint8_t x_170; 
x_169 = lean_box(0);
x_170 = lean_nat_dec_le(x_167, x_167);
if (x_170 == 0)
{
if (x_168 == 0)
{
lean_dec_ref(x_165);
x_69 = x_157;
x_70 = x_158;
x_71 = x_159;
x_72 = x_160;
x_73 = x_161;
x_74 = x_162;
x_75 = x_163;
x_76 = x_164;
x_77 = lean_box(0);
goto block_120;
}
else
{
size_t x_171; size_t x_172; lean_object* x_173; 
x_171 = 0;
x_172 = lean_usize_of_nat(x_167);
lean_inc_ref(x_7);
x_173 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_165, x_171, x_172, x_169, x_7);
lean_dec_ref(x_165);
if (lean_obj_tag(x_173) == 0)
{
lean_dec_ref(x_173);
x_69 = x_157;
x_70 = x_158;
x_71 = x_159;
x_72 = x_160;
x_73 = x_161;
x_74 = x_162;
x_75 = x_163;
x_76 = x_164;
x_77 = lean_box(0);
goto block_120;
}
else
{
lean_object* x_174; lean_object* x_175; uint8_t x_176; uint8_t x_181; 
lean_dec_ref(x_164);
lean_dec(x_163);
lean_dec_ref(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec_ref(x_158);
lean_dec_ref(x_157);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_174 = lean_ctor_get(x_173, 0);
x_181 = !lean_is_exclusive(x_173);
if (x_181 == 0)
{
x_175 = x_173;
x_176 = x_181;
goto block_180;
}
else
{
lean_inc(x_174);
lean_dec(x_173);
x_175 = lean_box(0);
x_176 = x_181;
goto block_180;
}
block_180:
{
lean_object* x_177; 
if (x_176 == 0)
{
x_177 = x_175;
goto block_178;
}
else
{
lean_object* x_179; 
x_179 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_179, 0, x_174);
x_177 = x_179;
goto block_178;
}
block_178:
{
return x_177;
}
}
}
}
}
else
{
size_t x_182; size_t x_183; lean_object* x_184; 
x_182 = 0;
x_183 = lean_usize_of_nat(x_167);
lean_inc_ref(x_7);
x_184 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_165, x_182, x_183, x_169, x_7);
lean_dec_ref(x_165);
if (lean_obj_tag(x_184) == 0)
{
lean_dec_ref(x_184);
x_69 = x_157;
x_70 = x_158;
x_71 = x_159;
x_72 = x_160;
x_73 = x_161;
x_74 = x_162;
x_75 = x_163;
x_76 = x_164;
x_77 = lean_box(0);
goto block_120;
}
else
{
lean_object* x_185; lean_object* x_186; uint8_t x_187; uint8_t x_192; 
lean_dec_ref(x_164);
lean_dec(x_163);
lean_dec_ref(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec_ref(x_158);
lean_dec_ref(x_157);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_185 = lean_ctor_get(x_184, 0);
x_192 = !lean_is_exclusive(x_184);
if (x_192 == 0)
{
x_186 = x_184;
x_187 = x_192;
goto block_191;
}
else
{
lean_inc(x_185);
lean_dec(x_184);
x_186 = lean_box(0);
x_187 = x_192;
goto block_191;
}
block_191:
{
lean_object* x_188; 
if (x_187 == 0)
{
x_188 = x_186;
goto block_189;
}
else
{
lean_object* x_190; 
x_190 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_190, 0, x_185);
x_188 = x_190;
goto block_189;
}
block_189:
{
return x_188;
}
}
}
}
}
}
block_329:
{
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; uint8_t x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_inc_ref(x_48);
lean_dec_ref(x_196);
lean_dec(x_195);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_198 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
x_199 = lean_string_append(x_48, x_198);
x_200 = lean_string_append(x_199, x_194);
lean_dec_ref(x_194);
x_201 = ((lean_object*)(l_Lake_Dependency_materialize___closed__7));
x_202 = lean_string_append(x_200, x_201);
x_203 = 3;
x_204 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set_uint8(x_204, sizeof(void*)*1, x_203);
x_205 = lean_apply_2(x_7, x_204, lean_box(0));
x_206 = lean_box(0);
x_207 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_207, 0, x_206);
return x_207;
}
else
{
lean_object* x_208; lean_object* x_209; uint8_t x_210; uint8_t x_328; 
x_208 = lean_ctor_get(x_196, 0);
x_328 = !lean_is_exclusive(x_196);
if (x_328 == 0)
{
x_209 = x_196;
x_210 = x_328;
goto block_327;
}
else
{
lean_inc(x_208);
lean_dec(x_196);
x_209 = lean_box(0);
x_210 = x_328;
goto block_327;
}
block_327:
{
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_211; uint8_t x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_inc_ref(x_48);
lean_del_object(x_209);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_211 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed(x_48, x_194, x_195);
lean_dec_ref(x_194);
x_212 = 3;
x_213 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_213, 0, x_211);
lean_ctor_set_uint8(x_213, sizeof(void*)*1, x_212);
x_214 = lean_apply_2(x_7, x_213, lean_box(0));
x_215 = lean_box(0);
x_216 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_216, 0, x_215);
return x_216;
}
else
{
lean_object* x_217; lean_object* x_218; 
x_217 = lean_ctor_get(x_208, 0);
lean_inc(x_217);
lean_dec_ref(x_208);
x_218 = l_Lake_RegistryPkg_gitSrc_x3f(x_217);
if (lean_obj_tag(x_218) == 1)
{
lean_object* x_219; lean_object* x_220; uint8_t x_221; uint8_t x_326; 
x_219 = lean_ctor_get(x_218, 0);
x_326 = !lean_is_exclusive(x_218);
if (x_326 == 0)
{
x_220 = x_218;
x_221 = x_326;
goto block_325;
}
else
{
lean_inc(x_219);
lean_dec(x_218);
x_220 = lean_box(0);
x_221 = x_326;
goto block_325;
}
block_325:
{
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_222 = lean_ctor_get(x_219, 1);
lean_inc_ref(x_222);
x_223 = lean_ctor_get(x_219, 2);
lean_inc(x_223);
x_224 = lean_ctor_get(x_219, 3);
lean_inc(x_224);
x_225 = lean_ctor_get(x_219, 4);
lean_inc(x_225);
lean_dec_ref(x_219);
x_226 = lean_ctor_get(x_217, 0);
lean_inc_ref(x_226);
x_227 = lean_ctor_get(x_217, 1);
lean_inc_ref(x_227);
lean_dec(x_217);
x_228 = l_Lake_joinRelative(x_5, x_226);
switch (lean_obj_tag(x_195)) {
case 0:
{
lean_object* x_229; 
lean_del_object(x_209);
lean_dec_ref(x_194);
x_229 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
if (lean_obj_tag(x_224) == 0)
{
uint8_t x_230; 
lean_dec_ref(x_228);
lean_dec_ref(x_227);
lean_dec(x_225);
lean_dec(x_223);
lean_dec_ref(x_222);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_230 = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (x_230 == 0)
{
lean_object* x_231; lean_object* x_232; 
lean_dec_ref(x_7);
x_231 = lean_box(0);
if (x_221 == 0)
{
lean_ctor_set(x_220, 0, x_231);
x_232 = x_220;
goto block_233;
}
else
{
lean_object* x_234; 
x_234 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_234, 0, x_231);
x_232 = x_234;
goto block_233;
}
block_233:
{
return x_232;
}
}
else
{
lean_object* x_235; uint8_t x_236; 
lean_del_object(x_220);
x_235 = lean_box(0);
x_236 = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (x_236 == 0)
{
if (x_230 == 0)
{
lean_dec_ref(x_7);
x_9 = lean_box(0);
goto block_12;
}
else
{
size_t x_237; size_t x_238; lean_object* x_239; 
x_237 = 0;
x_238 = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
x_239 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_229, x_237, x_238, x_235, x_7);
if (lean_obj_tag(x_239) == 0)
{
lean_dec_ref(x_239);
x_9 = lean_box(0);
goto block_12;
}
else
{
lean_object* x_240; lean_object* x_241; uint8_t x_242; uint8_t x_247; 
x_240 = lean_ctor_get(x_239, 0);
x_247 = !lean_is_exclusive(x_239);
if (x_247 == 0)
{
x_241 = x_239;
x_242 = x_247;
goto block_246;
}
else
{
lean_inc(x_240);
lean_dec(x_239);
x_241 = lean_box(0);
x_242 = x_247;
goto block_246;
}
block_246:
{
lean_object* x_243; 
if (x_242 == 0)
{
x_243 = x_241;
goto block_244;
}
else
{
lean_object* x_245; 
x_245 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_245, 0, x_240);
x_243 = x_245;
goto block_244;
}
block_244:
{
return x_243;
}
}
}
}
}
else
{
size_t x_248; size_t x_249; lean_object* x_250; 
x_248 = 0;
x_249 = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
x_250 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_229, x_248, x_249, x_235, x_7);
if (lean_obj_tag(x_250) == 0)
{
lean_dec_ref(x_250);
x_9 = lean_box(0);
goto block_12;
}
else
{
lean_object* x_251; lean_object* x_252; uint8_t x_253; uint8_t x_258; 
x_251 = lean_ctor_get(x_250, 0);
x_258 = !lean_is_exclusive(x_250);
if (x_258 == 0)
{
x_252 = x_250;
x_253 = x_258;
goto block_257;
}
else
{
lean_inc(x_251);
lean_dec(x_250);
x_252 = lean_box(0);
x_253 = x_258;
goto block_257;
}
block_257:
{
lean_object* x_254; 
if (x_253 == 0)
{
x_254 = x_252;
goto block_255;
}
else
{
lean_object* x_256; 
x_256 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_256, 0, x_251);
x_254 = x_256;
goto block_255;
}
block_255:
{
return x_254;
}
}
}
}
}
}
else
{
lean_object* x_259; uint8_t x_260; 
lean_del_object(x_220);
x_259 = lean_ctor_get(x_224, 0);
lean_inc(x_259);
lean_dec_ref(x_224);
x_260 = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (x_260 == 0)
{
x_36 = x_227;
x_37 = x_223;
x_38 = x_222;
x_39 = x_228;
x_40 = x_225;
x_41 = x_259;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
else
{
lean_object* x_261; uint8_t x_262; 
x_261 = lean_box(0);
x_262 = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (x_262 == 0)
{
if (x_260 == 0)
{
x_36 = x_227;
x_37 = x_223;
x_38 = x_222;
x_39 = x_228;
x_40 = x_225;
x_41 = x_259;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
else
{
size_t x_263; size_t x_264; lean_object* x_265; 
x_263 = 0;
x_264 = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
lean_inc_ref(x_7);
x_265 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_229, x_263, x_264, x_261, x_7);
if (lean_obj_tag(x_265) == 0)
{
lean_dec_ref(x_265);
x_36 = x_227;
x_37 = x_223;
x_38 = x_222;
x_39 = x_228;
x_40 = x_225;
x_41 = x_259;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
else
{
lean_object* x_266; lean_object* x_267; uint8_t x_268; uint8_t x_273; 
lean_dec(x_259);
lean_dec_ref(x_228);
lean_dec_ref(x_227);
lean_dec(x_225);
lean_dec(x_223);
lean_dec_ref(x_222);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_266 = lean_ctor_get(x_265, 0);
x_273 = !lean_is_exclusive(x_265);
if (x_273 == 0)
{
x_267 = x_265;
x_268 = x_273;
goto block_272;
}
else
{
lean_inc(x_266);
lean_dec(x_265);
x_267 = lean_box(0);
x_268 = x_273;
goto block_272;
}
block_272:
{
lean_object* x_269; 
if (x_268 == 0)
{
x_269 = x_267;
goto block_270;
}
else
{
lean_object* x_271; 
x_271 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_271, 0, x_266);
x_269 = x_271;
goto block_270;
}
block_270:
{
return x_269;
}
}
}
}
}
else
{
size_t x_274; size_t x_275; lean_object* x_276; 
x_274 = 0;
x_275 = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
lean_inc_ref(x_7);
x_276 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_229, x_274, x_275, x_261, x_7);
if (lean_obj_tag(x_276) == 0)
{
lean_dec_ref(x_276);
x_36 = x_227;
x_37 = x_223;
x_38 = x_222;
x_39 = x_228;
x_40 = x_225;
x_41 = x_259;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
else
{
lean_object* x_277; lean_object* x_278; uint8_t x_279; uint8_t x_284; 
lean_dec(x_259);
lean_dec_ref(x_228);
lean_dec_ref(x_227);
lean_dec(x_225);
lean_dec(x_223);
lean_dec_ref(x_222);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_277 = lean_ctor_get(x_276, 0);
x_284 = !lean_is_exclusive(x_276);
if (x_284 == 0)
{
x_278 = x_276;
x_279 = x_284;
goto block_283;
}
else
{
lean_inc(x_277);
lean_dec(x_276);
x_278 = lean_box(0);
x_279 = x_284;
goto block_283;
}
block_283:
{
lean_object* x_280; 
if (x_279 == 0)
{
x_280 = x_278;
goto block_281;
}
else
{
lean_object* x_282; 
x_282 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_282, 0, x_277);
x_280 = x_282;
goto block_281;
}
block_281:
{
return x_280;
}
}
}
}
}
}
}
case 1:
{
lean_object* x_285; lean_object* x_286; uint8_t x_287; 
lean_dec(x_224);
lean_del_object(x_220);
lean_del_object(x_209);
lean_dec_ref(x_194);
x_285 = lean_ctor_get(x_195, 0);
lean_inc_ref(x_285);
lean_dec_ref(x_195);
x_286 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
x_287 = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (x_287 == 0)
{
x_36 = x_227;
x_37 = x_223;
x_38 = x_222;
x_39 = x_228;
x_40 = x_225;
x_41 = x_285;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
else
{
lean_object* x_288; uint8_t x_289; 
x_288 = lean_box(0);
x_289 = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (x_289 == 0)
{
if (x_287 == 0)
{
x_36 = x_227;
x_37 = x_223;
x_38 = x_222;
x_39 = x_228;
x_40 = x_225;
x_41 = x_285;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
else
{
size_t x_290; size_t x_291; lean_object* x_292; 
x_290 = 0;
x_291 = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
lean_inc_ref(x_7);
x_292 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_286, x_290, x_291, x_288, x_7);
if (lean_obj_tag(x_292) == 0)
{
lean_dec_ref(x_292);
x_36 = x_227;
x_37 = x_223;
x_38 = x_222;
x_39 = x_228;
x_40 = x_225;
x_41 = x_285;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
else
{
lean_object* x_293; lean_object* x_294; uint8_t x_295; uint8_t x_300; 
lean_dec_ref(x_285);
lean_dec_ref(x_228);
lean_dec_ref(x_227);
lean_dec(x_225);
lean_dec(x_223);
lean_dec_ref(x_222);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_293 = lean_ctor_get(x_292, 0);
x_300 = !lean_is_exclusive(x_292);
if (x_300 == 0)
{
x_294 = x_292;
x_295 = x_300;
goto block_299;
}
else
{
lean_inc(x_293);
lean_dec(x_292);
x_294 = lean_box(0);
x_295 = x_300;
goto block_299;
}
block_299:
{
lean_object* x_296; 
if (x_295 == 0)
{
x_296 = x_294;
goto block_297;
}
else
{
lean_object* x_298; 
x_298 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_298, 0, x_293);
x_296 = x_298;
goto block_297;
}
block_297:
{
return x_296;
}
}
}
}
}
else
{
size_t x_301; size_t x_302; lean_object* x_303; 
x_301 = 0;
x_302 = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
lean_inc_ref(x_7);
x_303 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_286, x_301, x_302, x_288, x_7);
if (lean_obj_tag(x_303) == 0)
{
lean_dec_ref(x_303);
x_36 = x_227;
x_37 = x_223;
x_38 = x_222;
x_39 = x_228;
x_40 = x_225;
x_41 = x_285;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
else
{
lean_object* x_304; lean_object* x_305; uint8_t x_306; uint8_t x_311; 
lean_dec_ref(x_285);
lean_dec_ref(x_228);
lean_dec_ref(x_227);
lean_dec(x_225);
lean_dec(x_223);
lean_dec_ref(x_222);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_304 = lean_ctor_get(x_303, 0);
x_311 = !lean_is_exclusive(x_303);
if (x_311 == 0)
{
x_305 = x_303;
x_306 = x_311;
goto block_310;
}
else
{
lean_inc(x_304);
lean_dec(x_303);
x_305 = lean_box(0);
x_306 = x_311;
goto block_310;
}
block_310:
{
lean_object* x_307; 
if (x_306 == 0)
{
x_307 = x_305;
goto block_308;
}
else
{
lean_object* x_309; 
x_309 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_309, 0, x_304);
x_307 = x_309;
goto block_308;
}
block_308:
{
return x_307;
}
}
}
}
}
}
default: 
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; 
lean_dec(x_224);
lean_del_object(x_220);
x_312 = lean_ctor_get(x_195, 0);
lean_inc_ref(x_312);
lean_dec_ref(x_195);
x_313 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
lean_inc_ref(x_194);
lean_inc_ref(x_48);
lean_inc_ref(x_3);
x_314 = l_Lake_Reservoir_fetchPkgVersions(x_3, x_48, x_194, x_313);
if (lean_obj_tag(x_314) == 0)
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_314, 1);
lean_inc(x_316);
lean_dec_ref(x_314);
if (x_210 == 0)
{
lean_ctor_set(x_209, 0, x_315);
x_317 = x_209;
goto block_318;
}
else
{
lean_object* x_319; 
x_319 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_319, 0, x_315);
x_317 = x_319;
goto block_318;
}
block_318:
{
x_157 = x_194;
x_158 = x_312;
x_159 = x_227;
x_160 = x_223;
x_161 = x_222;
x_162 = x_228;
x_163 = x_225;
x_164 = x_317;
x_165 = x_316;
x_166 = lean_box(0);
goto block_193;
}
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_320 = lean_ctor_get(x_314, 0);
lean_inc(x_320);
x_321 = lean_ctor_get(x_314, 1);
lean_inc(x_321);
lean_dec_ref(x_314);
if (x_210 == 0)
{
lean_ctor_set_tag(x_209, 0);
lean_ctor_set(x_209, 0, x_320);
x_322 = x_209;
goto block_323;
}
else
{
lean_object* x_324; 
x_324 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_324, 0, x_320);
x_322 = x_324;
goto block_323;
}
block_323:
{
x_157 = x_194;
x_158 = x_312;
x_159 = x_227;
x_160 = x_223;
x_161 = x_222;
x_162 = x_228;
x_163 = x_225;
x_164 = x_322;
x_165 = x_321;
x_166 = lean_box(0);
goto block_193;
}
}
}
}
}
else
{
lean_del_object(x_220);
lean_dec(x_219);
lean_del_object(x_209);
lean_dec(x_195);
lean_dec_ref(x_194);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_13 = x_217;
x_14 = x_7;
x_15 = lean_box(0);
goto block_24;
}
}
}
else
{
lean_dec(x_218);
lean_del_object(x_209);
lean_dec(x_195);
lean_dec_ref(x_194);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_13 = x_217;
x_14 = x_7;
x_15 = lean_box(0);
goto block_24;
}
}
}
}
}
block_361:
{
lean_object* x_335; uint8_t x_336; 
x_335 = lean_array_get_size(x_333);
x_336 = lean_nat_dec_lt(x_156, x_335);
if (x_336 == 0)
{
lean_dec_ref(x_333);
x_194 = x_330;
x_195 = x_331;
x_196 = x_332;
x_197 = lean_box(0);
goto block_329;
}
else
{
lean_object* x_337; uint8_t x_338; 
x_337 = lean_box(0);
x_338 = lean_nat_dec_le(x_335, x_335);
if (x_338 == 0)
{
if (x_336 == 0)
{
lean_dec_ref(x_333);
x_194 = x_330;
x_195 = x_331;
x_196 = x_332;
x_197 = lean_box(0);
goto block_329;
}
else
{
size_t x_339; size_t x_340; lean_object* x_341; 
x_339 = 0;
x_340 = lean_usize_of_nat(x_335);
lean_inc_ref(x_7);
x_341 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_333, x_339, x_340, x_337, x_7);
lean_dec_ref(x_333);
if (lean_obj_tag(x_341) == 0)
{
lean_dec_ref(x_341);
x_194 = x_330;
x_195 = x_331;
x_196 = x_332;
x_197 = lean_box(0);
goto block_329;
}
else
{
lean_object* x_342; lean_object* x_343; uint8_t x_344; uint8_t x_349; 
lean_dec_ref(x_332);
lean_dec(x_331);
lean_dec_ref(x_330);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_342 = lean_ctor_get(x_341, 0);
x_349 = !lean_is_exclusive(x_341);
if (x_349 == 0)
{
x_343 = x_341;
x_344 = x_349;
goto block_348;
}
else
{
lean_inc(x_342);
lean_dec(x_341);
x_343 = lean_box(0);
x_344 = x_349;
goto block_348;
}
block_348:
{
lean_object* x_345; 
if (x_344 == 0)
{
x_345 = x_343;
goto block_346;
}
else
{
lean_object* x_347; 
x_347 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_347, 0, x_342);
x_345 = x_347;
goto block_346;
}
block_346:
{
return x_345;
}
}
}
}
}
else
{
size_t x_350; size_t x_351; lean_object* x_352; 
x_350 = 0;
x_351 = lean_usize_of_nat(x_335);
lean_inc_ref(x_7);
x_352 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_333, x_350, x_351, x_337, x_7);
lean_dec_ref(x_333);
if (lean_obj_tag(x_352) == 0)
{
lean_dec_ref(x_352);
x_194 = x_330;
x_195 = x_331;
x_196 = x_332;
x_197 = lean_box(0);
goto block_329;
}
else
{
lean_object* x_353; lean_object* x_354; uint8_t x_355; uint8_t x_360; 
lean_dec_ref(x_332);
lean_dec(x_331);
lean_dec_ref(x_330);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_353 = lean_ctor_get(x_352, 0);
x_360 = !lean_is_exclusive(x_352);
if (x_360 == 0)
{
x_354 = x_352;
x_355 = x_360;
goto block_359;
}
else
{
lean_inc(x_353);
lean_dec(x_352);
x_354 = lean_box(0);
x_355 = x_360;
goto block_359;
}
block_359:
{
lean_object* x_356; 
if (x_355 == 0)
{
x_356 = x_354;
goto block_357;
}
else
{
lean_object* x_358; 
x_358 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_358, 0, x_353);
x_356 = x_358;
goto block_357;
}
block_357:
{
return x_356;
}
}
}
}
}
}
block_374:
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; 
lean_inc(x_47);
x_365 = l_Lean_Name_toString(x_47, x_362);
x_366 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
lean_inc_ref(x_365);
lean_inc_ref(x_48);
lean_inc_ref(x_3);
x_367 = l_Lake_Reservoir_fetchPkg_x3f(x_3, x_48, x_365, x_366);
if (lean_obj_tag(x_367) == 0)
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_368 = lean_ctor_get(x_367, 0);
lean_inc(x_368);
x_369 = lean_ctor_get(x_367, 1);
lean_inc(x_369);
lean_dec_ref(x_367);
x_370 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_370, 0, x_368);
x_330 = x_365;
x_331 = x_363;
x_332 = x_370;
x_333 = x_369;
x_334 = lean_box(0);
goto block_361;
}
else
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; 
x_371 = lean_ctor_get(x_367, 0);
lean_inc(x_371);
x_372 = lean_ctor_get(x_367, 1);
lean_inc(x_372);
lean_dec_ref(x_367);
x_373 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_373, 0, x_371);
x_330 = x_365;
x_331 = x_363;
x_332 = x_373;
x_333 = x_372;
x_334 = lean_box(0);
goto block_361;
}
}
}
block_12:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
block_24:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc_ref(x_16);
lean_dec_ref(x_13);
x_17 = ((lean_object*)(l_Lake_Dependency_materialize___closed__0));
x_18 = lean_string_append(x_16, x_17);
x_19 = 3;
x_20 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*1, x_19);
x_21 = lean_apply_2(x_14, x_20, lean_box(0));
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
block_35:
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_29);
x_34 = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit(x_1, x_2, x_3, x_4, x_27, x_30, x_28, x_32, x_33, x_31, x_26);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_34;
}
block_46:
{
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_44; 
x_44 = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
x_25 = lean_box(0);
x_26 = x_42;
x_27 = x_36;
x_28 = x_38;
x_29 = x_41;
x_30 = x_39;
x_31 = x_40;
x_32 = x_44;
goto block_35;
}
else
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_37, 0);
lean_inc(x_45);
lean_dec_ref(x_37);
x_25 = lean_box(0);
x_26 = x_42;
x_27 = x_36;
x_28 = x_38;
x_29 = x_41;
x_30 = x_39;
x_31 = x_40;
x_32 = x_45;
goto block_35;
}
}
block_68:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_54 = lean_ctor_get(x_52, 0);
lean_inc_ref(x_54);
lean_dec_ref(x_52);
x_55 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
x_56 = lean_string_append(x_48, x_55);
x_57 = lean_string_append(x_56, x_51);
lean_dec_ref(x_51);
x_58 = ((lean_object*)(l_Lake_Dependency_materialize___closed__1));
x_59 = lean_string_append(x_57, x_58);
x_60 = lean_string_append(x_59, x_54);
lean_dec_ref(x_54);
x_61 = ((lean_object*)(l_Lake_Dependency_materialize___closed__2));
x_62 = lean_string_append(x_60, x_61);
x_63 = 3;
x_64 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set_uint8(x_64, sizeof(void*)*1, x_63);
x_65 = lean_apply_2(x_7, x_64, lean_box(0));
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
block_120:
{
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_78; uint8_t x_79; uint8_t x_93; 
lean_inc_ref(x_48);
lean_dec(x_75);
lean_dec_ref(x_74);
lean_dec_ref(x_73);
lean_dec(x_72);
lean_dec_ref(x_71);
lean_dec_ref(x_70);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_93 = !lean_is_exclusive(x_76);
if (x_93 == 0)
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_76, 0);
lean_dec(x_94);
x_78 = x_76;
x_79 = x_93;
goto block_92;
}
else
{
lean_dec(x_76);
x_78 = lean_box(0);
x_79 = x_93;
goto block_92;
}
block_92:
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_80 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
x_81 = lean_string_append(x_48, x_80);
x_82 = lean_string_append(x_81, x_69);
lean_dec_ref(x_69);
x_83 = ((lean_object*)(l_Lake_Dependency_materialize___closed__3));
x_84 = lean_string_append(x_82, x_83);
x_85 = 3;
x_86 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set_uint8(x_86, sizeof(void*)*1, x_85);
x_87 = lean_apply_2(x_7, x_86, lean_box(0));
x_88 = lean_box(0);
if (x_79 == 0)
{
lean_ctor_set_tag(x_78, 1);
lean_ctor_set(x_78, 0, x_88);
x_89 = x_78;
goto block_90;
}
else
{
lean_object* x_91; 
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_88);
x_89 = x_91;
goto block_90;
}
block_90:
{
return x_89;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; size_t x_97; size_t x_98; lean_object* x_99; lean_object* x_100; 
x_95 = lean_ctor_get(x_76, 0);
lean_inc(x_95);
lean_dec_ref(x_76);
x_96 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___closed__0));
x_97 = lean_array_size(x_95);
x_98 = 0;
x_99 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(x_70, x_95, x_97, x_98, x_96);
lean_dec(x_95);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
lean_dec_ref(x_99);
if (lean_obj_tag(x_100) == 0)
{
lean_inc_ref(x_48);
lean_dec(x_75);
lean_dec_ref(x_74);
lean_dec_ref(x_73);
lean_dec(x_72);
lean_dec_ref(x_71);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_51 = x_69;
x_52 = x_70;
x_53 = lean_box(0);
goto block_68;
}
else
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
lean_dec_ref(x_100);
if (lean_obj_tag(x_101) == 1)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; 
lean_dec_ref(x_70);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
lean_dec_ref(x_101);
x_103 = lean_ctor_get(x_102, 0);
lean_inc_ref(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc_ref(x_104);
lean_dec(x_102);
x_105 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
lean_inc_ref(x_48);
x_106 = lean_string_append(x_48, x_105);
x_107 = lean_string_append(x_106, x_69);
lean_dec_ref(x_69);
x_108 = ((lean_object*)(l_Lake_Dependency_materialize___closed__4));
x_109 = lean_string_append(x_107, x_108);
x_110 = l_Lake_StdVer_toString(x_103);
x_111 = lean_string_append(x_109, x_110);
lean_dec_ref(x_110);
x_112 = ((lean_object*)(l_Lake_Dependency_materialize___closed__5));
x_113 = lean_string_append(x_111, x_112);
x_114 = lean_string_append(x_113, x_104);
x_115 = ((lean_object*)(l_Lake_Dependency_materialize___closed__6));
x_116 = lean_string_append(x_114, x_115);
x_117 = 1;
x_118 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set_uint8(x_118, sizeof(void*)*1, x_117);
lean_inc_ref(x_7);
x_119 = lean_apply_2(x_7, x_118, lean_box(0));
x_36 = x_71;
x_37 = x_72;
x_38 = x_73;
x_39 = x_74;
x_40 = x_75;
x_41 = x_104;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
else
{
lean_inc_ref(x_48);
lean_dec(x_101);
lean_dec(x_75);
lean_dec_ref(x_74);
lean_dec_ref(x_73);
lean_dec(x_72);
lean_dec_ref(x_71);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_51 = x_69;
x_52 = x_70;
x_53 = lean_box(0);
goto block_68;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l_Lake_Dependency_materialize(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_13; 
x_13 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_23; 
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_14 = lean_ctor_get(x_13, 0);
x_23 = !lean_is_exclusive(x_13);
if (x_23 == 0)
{
x_15 = x_13;
x_16 = x_23;
goto block_22;
}
else
{
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_18, 2, x_1);
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_18);
x_19 = x_15;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_55; lean_object* x_56; uint8_t x_68; lean_object* x_69; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; uint8_t x_110; lean_object* x_111; lean_object* x_112; uint8_t x_123; lean_object* x_124; lean_object* x_157; uint8_t x_158; 
x_24 = lean_ctor_get(x_1, 0);
x_25 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_25);
x_26 = lean_ctor_get(x_13, 1);
lean_inc_ref(x_26);
x_27 = lean_ctor_get(x_13, 3);
lean_inc(x_27);
lean_dec_ref(x_13);
x_34 = 0;
lean_inc(x_24);
x_35 = l_Lean_Name_toString(x_24, x_34);
lean_inc_ref(x_35);
x_36 = l_Lake_joinRelative(x_4, x_35);
lean_inc_ref(x_36);
x_41 = l_Lake_joinRelative(x_3, x_36);
x_123 = l_System_FilePath_isDir(x_41);
x_157 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
x_158 = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (x_158 == 0)
{
x_124 = lean_box(0);
goto block_156;
}
else
{
lean_object* x_159; uint8_t x_160; 
x_159 = lean_box(0);
x_160 = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (x_160 == 0)
{
if (x_158 == 0)
{
x_124 = lean_box(0);
goto block_156;
}
else
{
size_t x_161; size_t x_162; lean_object* x_163; 
x_161 = 0;
x_162 = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
lean_inc_ref(x_5);
x_163 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_157, x_161, x_162, x_159, x_5);
if (lean_obj_tag(x_163) == 0)
{
lean_dec_ref(x_163);
x_124 = lean_box(0);
goto block_156;
}
else
{
lean_object* x_164; lean_object* x_165; uint8_t x_166; uint8_t x_171; 
lean_dec_ref(x_41);
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_164 = lean_ctor_get(x_163, 0);
x_171 = !lean_is_exclusive(x_163);
if (x_171 == 0)
{
x_165 = x_163;
x_166 = x_171;
goto block_170;
}
else
{
lean_inc(x_164);
lean_dec(x_163);
x_165 = lean_box(0);
x_166 = x_171;
goto block_170;
}
block_170:
{
lean_object* x_167; 
if (x_166 == 0)
{
x_167 = x_165;
goto block_168;
}
else
{
lean_object* x_169; 
x_169 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_169, 0, x_164);
x_167 = x_169;
goto block_168;
}
block_168:
{
return x_167;
}
}
}
}
}
else
{
size_t x_172; size_t x_173; lean_object* x_174; 
x_172 = 0;
x_173 = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
lean_inc_ref(x_5);
x_174 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_157, x_172, x_173, x_159, x_5);
if (lean_obj_tag(x_174) == 0)
{
lean_dec_ref(x_174);
x_124 = lean_box(0);
goto block_156;
}
else
{
lean_object* x_175; lean_object* x_176; uint8_t x_177; uint8_t x_182; 
lean_dec_ref(x_41);
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_175 = lean_ctor_get(x_174, 0);
x_182 = !lean_is_exclusive(x_174);
if (x_182 == 0)
{
x_176 = x_174;
x_177 = x_182;
goto block_181;
}
else
{
lean_inc(x_175);
lean_dec(x_174);
x_176 = lean_box(0);
x_177 = x_182;
goto block_181;
}
block_181:
{
lean_object* x_178; 
if (x_177 == 0)
{
x_178 = x_176;
goto block_179;
}
else
{
lean_object* x_180; 
x_180 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_180, 0, x_175);
x_178 = x_180;
goto block_179;
}
block_179:
{
return x_178;
}
}
}
}
}
block_33:
{
lean_object* x_30; 
x_30 = l_Lake_Git_filterUrl_x3f(x_25);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
x_7 = x_29;
x_8 = lean_box(0);
x_9 = x_31;
goto block_12;
}
else
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec_ref(x_30);
x_7 = x_29;
x_8 = lean_box(0);
x_9 = x_32;
goto block_12;
}
}
block_40:
{
if (lean_obj_tag(x_27) == 0)
{
x_28 = lean_box(0);
x_29 = x_36;
goto block_33;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_27, 0);
lean_inc(x_38);
lean_dec_ref(x_27);
x_39 = l_Lake_joinRelative(x_36, x_38);
x_28 = lean_box(0);
x_29 = x_39;
goto block_33;
}
}
block_54:
{
lean_object* x_45; 
x_45 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(x_5, x_35, x_41, x_44, x_43);
if (lean_obj_tag(x_45) == 0)
{
lean_dec_ref(x_45);
x_37 = lean_box(0);
goto block_40;
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_53; 
lean_dec_ref(x_36);
lean_dec(x_27);
lean_dec_ref(x_25);
lean_dec_ref(x_1);
x_46 = lean_ctor_get(x_45, 0);
x_53 = !lean_is_exclusive(x_45);
if (x_53 == 0)
{
x_47 = x_45;
x_48 = x_53;
goto block_52;
}
else
{
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_box(0);
x_48 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_49; 
if (x_48 == 0)
{
x_49 = x_47;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_46);
x_49 = x_51;
goto block_50;
}
block_50:
{
return x_49;
}
}
}
}
block_67:
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_26);
x_58 = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(x_5, x_35, x_41, x_56, x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_dec_ref(x_58);
x_37 = lean_box(0);
goto block_40;
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; uint8_t x_66; 
lean_dec_ref(x_36);
lean_dec(x_27);
lean_dec_ref(x_25);
lean_dec_ref(x_1);
x_59 = lean_ctor_get(x_58, 0);
x_66 = !lean_is_exclusive(x_58);
if (x_66 == 0)
{
x_60 = x_58;
x_61 = x_66;
goto block_65;
}
else
{
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_box(0);
x_61 = x_66;
goto block_65;
}
block_65:
{
lean_object* x_62; 
if (x_61 == 0)
{
x_62 = x_60;
goto block_63;
}
else
{
lean_object* x_64; 
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_59);
x_62 = x_64;
goto block_63;
}
block_63:
{
return x_62;
}
}
}
}
block_78:
{
if (x_68 == 0)
{
lean_dec_ref(x_41);
lean_dec_ref(x_35);
lean_dec_ref(x_5);
x_37 = lean_box(0);
goto block_40;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; 
x_70 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0));
x_71 = lean_string_append(x_35, x_70);
x_72 = lean_string_append(x_71, x_41);
lean_dec_ref(x_41);
x_73 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1));
x_74 = lean_string_append(x_72, x_73);
x_75 = 2;
x_76 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set_uint8(x_76, sizeof(void*)*1, x_75);
x_77 = lean_apply_2(x_5, x_76, lean_box(0));
x_37 = lean_box(0);
goto block_40;
}
}
block_109:
{
lean_object* x_83; uint8_t x_84; 
x_83 = lean_array_get_size(x_80);
x_84 = lean_nat_dec_lt(x_79, x_83);
if (x_84 == 0)
{
lean_dec_ref(x_80);
x_68 = x_81;
x_69 = lean_box(0);
goto block_78;
}
else
{
lean_object* x_85; uint8_t x_86; 
x_85 = lean_box(0);
x_86 = lean_nat_dec_le(x_83, x_83);
if (x_86 == 0)
{
if (x_84 == 0)
{
lean_dec_ref(x_80);
x_68 = x_81;
x_69 = lean_box(0);
goto block_78;
}
else
{
size_t x_87; size_t x_88; lean_object* x_89; 
x_87 = 0;
x_88 = lean_usize_of_nat(x_83);
lean_inc_ref(x_5);
x_89 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_80, x_87, x_88, x_85, x_5);
lean_dec_ref(x_80);
if (lean_obj_tag(x_89) == 0)
{
lean_dec_ref(x_89);
x_68 = x_81;
x_69 = lean_box(0);
goto block_78;
}
else
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; uint8_t x_97; 
lean_dec_ref(x_41);
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec(x_27);
lean_dec_ref(x_25);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_90 = lean_ctor_get(x_89, 0);
x_97 = !lean_is_exclusive(x_89);
if (x_97 == 0)
{
x_91 = x_89;
x_92 = x_97;
goto block_96;
}
else
{
lean_inc(x_90);
lean_dec(x_89);
x_91 = lean_box(0);
x_92 = x_97;
goto block_96;
}
block_96:
{
lean_object* x_93; 
if (x_92 == 0)
{
x_93 = x_91;
goto block_94;
}
else
{
lean_object* x_95; 
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_90);
x_93 = x_95;
goto block_94;
}
block_94:
{
return x_93;
}
}
}
}
}
else
{
size_t x_98; size_t x_99; lean_object* x_100; 
x_98 = 0;
x_99 = lean_usize_of_nat(x_83);
lean_inc_ref(x_5);
x_100 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_80, x_98, x_99, x_85, x_5);
lean_dec_ref(x_80);
if (lean_obj_tag(x_100) == 0)
{
lean_dec_ref(x_100);
x_68 = x_81;
x_69 = lean_box(0);
goto block_78;
}
else
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; uint8_t x_108; 
lean_dec_ref(x_41);
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec(x_27);
lean_dec_ref(x_25);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_101 = lean_ctor_get(x_100, 0);
x_108 = !lean_is_exclusive(x_100);
if (x_108 == 0)
{
x_102 = x_100;
x_103 = x_108;
goto block_107;
}
else
{
lean_inc(x_101);
lean_dec(x_100);
x_102 = lean_box(0);
x_103 = x_108;
goto block_107;
}
block_107:
{
lean_object* x_104; 
if (x_103 == 0)
{
x_104 = x_102;
goto block_105;
}
else
{
lean_object* x_106; 
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_101);
x_104 = x_106;
goto block_105;
}
block_105:
{
return x_104;
}
}
}
}
}
}
block_122:
{
lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_113 = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_26);
lean_inc_ref(x_114);
x_115 = l_Option_instDecidableEq___redArg(x_113, x_111, x_114);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_2, 5);
x_117 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_116, x_24);
if (lean_obj_tag(x_117) == 0)
{
lean_inc_ref(x_25);
x_42 = lean_box(0);
x_43 = x_114;
x_44 = x_25;
goto block_54;
}
else
{
lean_object* x_118; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
lean_dec_ref(x_117);
x_42 = lean_box(0);
x_43 = x_114;
x_44 = x_118;
goto block_54;
}
}
else
{
uint8_t x_119; lean_object* x_120; lean_object* x_121; 
lean_dec_ref(x_114);
lean_inc_ref(x_41);
x_119 = l_Lake_GitRepo_hasNoDiff(x_41);
x_120 = lean_unsigned_to_nat(0u);
x_121 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
if (x_119 == 0)
{
x_79 = x_120;
x_80 = x_121;
x_81 = x_110;
x_82 = lean_box(0);
goto block_109;
}
else
{
x_79 = x_120;
x_80 = x_121;
x_81 = x_34;
x_82 = lean_box(0);
goto block_109;
}
}
}
block_156:
{
if (x_123 == 0)
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_2, 5);
x_126 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_125, x_24);
if (lean_obj_tag(x_126) == 0)
{
lean_inc_ref(x_25);
x_55 = lean_box(0);
x_56 = x_25;
goto block_67;
}
else
{
lean_object* x_127; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
lean_dec_ref(x_126);
x_55 = lean_box(0);
x_56 = x_127;
goto block_67;
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; 
x_128 = ((lean_object*)(l_Lake_PackageEntry_materialize___closed__0));
lean_inc_ref(x_41);
x_129 = l_Lake_GitRepo_resolveRevision_x3f(x_128, x_41);
x_130 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
x_131 = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (x_131 == 0)
{
x_110 = x_123;
x_111 = x_129;
x_112 = lean_box(0);
goto block_122;
}
else
{
lean_object* x_132; uint8_t x_133; 
x_132 = lean_box(0);
x_133 = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (x_133 == 0)
{
if (x_131 == 0)
{
x_110 = x_123;
x_111 = x_129;
x_112 = lean_box(0);
goto block_122;
}
else
{
size_t x_134; size_t x_135; lean_object* x_136; 
x_134 = 0;
x_135 = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
lean_inc_ref(x_5);
x_136 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_130, x_134, x_135, x_132, x_5);
if (lean_obj_tag(x_136) == 0)
{
lean_dec_ref(x_136);
x_110 = x_123;
x_111 = x_129;
x_112 = lean_box(0);
goto block_122;
}
else
{
lean_object* x_137; lean_object* x_138; uint8_t x_139; uint8_t x_144; 
lean_dec(x_129);
lean_dec_ref(x_41);
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_137 = lean_ctor_get(x_136, 0);
x_144 = !lean_is_exclusive(x_136);
if (x_144 == 0)
{
x_138 = x_136;
x_139 = x_144;
goto block_143;
}
else
{
lean_inc(x_137);
lean_dec(x_136);
x_138 = lean_box(0);
x_139 = x_144;
goto block_143;
}
block_143:
{
lean_object* x_140; 
if (x_139 == 0)
{
x_140 = x_138;
goto block_141;
}
else
{
lean_object* x_142; 
x_142 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_142, 0, x_137);
x_140 = x_142;
goto block_141;
}
block_141:
{
return x_140;
}
}
}
}
}
else
{
size_t x_145; size_t x_146; lean_object* x_147; 
x_145 = 0;
x_146 = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
lean_inc_ref(x_5);
x_147 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_130, x_145, x_146, x_132, x_5);
if (lean_obj_tag(x_147) == 0)
{
lean_dec_ref(x_147);
x_110 = x_123;
x_111 = x_129;
x_112 = lean_box(0);
goto block_122;
}
else
{
lean_object* x_148; lean_object* x_149; uint8_t x_150; uint8_t x_155; 
lean_dec(x_129);
lean_dec_ref(x_41);
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_148 = lean_ctor_get(x_147, 0);
x_155 = !lean_is_exclusive(x_147);
if (x_155 == 0)
{
x_149 = x_147;
x_150 = x_155;
goto block_154;
}
else
{
lean_inc(x_148);
lean_dec(x_147);
x_149 = lean_box(0);
x_150 = x_155;
goto block_154;
}
block_154:
{
lean_object* x_151; 
if (x_150 == 0)
{
x_151 = x_149;
goto block_152;
}
else
{
lean_object* x_153; 
x_153 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_153, 0, x_148);
x_151 = x_153;
goto block_152;
}
block_152:
{
return x_151;
}
}
}
}
}
}
}
}
block_12:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set(x_10, 2, x_1);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_PackageEntry_materialize(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
return x_7;
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
res = runtime_initialize_Lake_Config_Env(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Load_Manifest(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Package(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Git(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Reservoir(builtin)
;
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
res = initialize_Lake_Config_Env(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Manifest(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Package(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Git(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Reservoir(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Load_Materialize(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Load_Materialize(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Load_Materialize(builtin);
}
#ifdef __cplusplus
}
#endif

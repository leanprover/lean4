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
extern lean_object* l_Lake_defaultManifestFile;
lean_object* l_Lake_Manifest_load(lean_object*);
uint8_t l_System_FilePath_isDir(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
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
extern lean_object* l_Lake_instInhabitedPackageEntry_default;
extern lean_object* l_System_instInhabitedFilePath_default;
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_instDecidableEqString___boxed(lean_object*, lean_object*);
uint8_t l_Option_instDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_resolveRevision_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lake_instInhabitedMaterializedDep_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "(`Inhabited.default` for `IO.Error`)"};
static const lean_object* l_Lake_instInhabitedMaterializedDep_default___closed__1 = (const lean_object*)&l_Lake_instInhabitedMaterializedDep_default___closed__1_value;
static const lean_ctor_object l_Lake_instInhabitedMaterializedDep_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_Lake_instInhabitedMaterializedDep_default___closed__1_value)}};
static const lean_object* l_Lake_instInhabitedMaterializedDep_default___closed__2 = (const lean_object*)&l_Lake_instInhabitedMaterializedDep_default___closed__2_value;
static const lean_ctor_object l_Lake_instInhabitedMaterializedDep_default___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_instInhabitedMaterializedDep_default___closed__2_value)}};
static const lean_object* l_Lake_instInhabitedMaterializedDep_default___closed__3 = (const lean_object*)&l_Lake_instInhabitedMaterializedDep_default___closed__3_value;
static lean_once_cell_t l_Lake_instInhabitedMaterializedDep_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedMaterializedDep_default___closed__4;
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
LEAN_EXPORT uint8_t l_Lake_MaterializedDep_fixedToolchain(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_fixedToolchain___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0_value;
static lean_once_cell_t l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1;
static lean_once_cell_t l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__2;
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__0;
static lean_once_cell_t l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_PackageEntry_materialize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HEAD"};
static const lean_object* l_Lake_PackageEntry_materialize___closed__0 = (const lean_object*)&l_Lake_PackageEntry_materialize___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(lean_object* v_as_1_, size_t v_i_2_, size_t v_stop_3_, lean_object* v_b_4_, lean_object* v___y_5_){
_start:
{
uint8_t v___x_7_; 
v___x_7_ = lean_usize_dec_eq(v_i_2_, v_stop_3_);
if (v___x_7_ == 0)
{
lean_object* v___x_8_; lean_object* v___x_9_; size_t v___x_10_; size_t v___x_11_; 
v___x_8_ = lean_array_uget_borrowed(v_as_1_, v_i_2_);
lean_inc_ref(v___y_5_);
lean_inc(v___x_8_);
v___x_9_ = lean_apply_2(v___y_5_, v___x_8_, lean_box(0));
v___x_10_ = ((size_t)1ULL);
v___x_11_ = lean_usize_add(v_i_2_, v___x_10_);
v_i_2_ = v___x_11_;
v_b_4_ = v___x_9_;
goto _start;
}
else
{
lean_object* v___x_13_; 
v___x_13_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_13_, 0, v_b_4_);
return v___x_13_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0___boxed(lean_object* v_as_14_, lean_object* v_i_15_, lean_object* v_stop_16_, lean_object* v_b_17_, lean_object* v___y_18_, lean_object* v___y_19_){
_start:
{
size_t v_i_boxed_20_; size_t v_stop_boxed_21_; lean_object* v_res_22_; 
v_i_boxed_20_ = lean_unbox_usize(v_i_15_);
lean_dec(v_i_15_);
v_stop_boxed_21_ = lean_unbox_usize(v_stop_16_);
lean_dec(v_stop_16_);
v_res_22_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_as_14_, v_i_boxed_20_, v_stop_boxed_21_, v_b_17_, v___y_18_);
lean_dec_ref(v___y_18_);
lean_dec_ref(v_as_14_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg(lean_object* v_name_29_, lean_object* v_repo_30_, lean_object* v_rev_x3f_31_, lean_object* v_a_32_){
_start:
{
uint8_t v_a_35_; lean_object* v___y_48_; lean_object* v___y_49_; uint8_t v_val_50_; lean_object* v___y_65_; lean_object* v_a_66_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_132_ = l_Lake_Git_defaultRemote;
v___x_133_ = lean_unsigned_to_nat(0u);
v___x_134_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
lean_inc_ref(v_repo_30_);
v___x_135_ = l_Lake_GitRepo_findRemoteRevision(v_repo_30_, v_rev_x3f_31_, v___x_132_, v___x_134_);
if (lean_obj_tag(v___x_135_) == 0)
{
lean_object* v_a_136_; lean_object* v_a_137_; lean_object* v___x_165_; uint8_t v___x_166_; 
v_a_136_ = lean_ctor_get(v___x_135_, 0);
lean_inc(v_a_136_);
v_a_137_ = lean_ctor_get(v___x_135_, 1);
lean_inc(v_a_137_);
lean_dec_ref(v___x_135_);
v___x_165_ = lean_array_get_size(v_a_137_);
v___x_166_ = lean_nat_dec_lt(v___x_133_, v___x_165_);
if (v___x_166_ == 0)
{
lean_dec(v_a_137_);
goto v___jp_138_;
}
else
{
lean_object* v___x_167_; uint8_t v___x_168_; 
v___x_167_ = lean_box(0);
v___x_168_ = lean_nat_dec_le(v___x_165_, v___x_165_);
if (v___x_168_ == 0)
{
if (v___x_166_ == 0)
{
lean_dec(v_a_137_);
goto v___jp_138_;
}
else
{
size_t v___x_169_; size_t v___x_170_; lean_object* v___x_171_; 
v___x_169_ = ((size_t)0ULL);
v___x_170_ = lean_usize_of_nat(v___x_165_);
v___x_171_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_137_, v___x_169_, v___x_170_, v___x_167_, v_a_32_);
lean_dec(v_a_137_);
if (lean_obj_tag(v___x_171_) == 0)
{
lean_dec_ref(v___x_171_);
goto v___jp_138_;
}
else
{
lean_dec(v_a_136_);
lean_dec_ref(v_repo_30_);
lean_dec_ref(v_name_29_);
return v___x_171_;
}
}
}
else
{
size_t v___x_172_; size_t v___x_173_; lean_object* v___x_174_; 
v___x_172_ = ((size_t)0ULL);
v___x_173_ = lean_usize_of_nat(v___x_165_);
v___x_174_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_137_, v___x_172_, v___x_173_, v___x_167_, v_a_32_);
lean_dec(v_a_137_);
if (lean_obj_tag(v___x_174_) == 0)
{
lean_dec_ref(v___x_174_);
goto v___jp_138_;
}
else
{
lean_dec(v_a_136_);
lean_dec_ref(v_repo_30_);
lean_dec_ref(v_name_29_);
return v___x_174_;
}
}
}
v___jp_138_:
{
lean_object* v___x_139_; 
lean_inc_ref(v_repo_30_);
v___x_139_ = l_Lake_GitRepo_getHeadRevision(v_repo_30_, v___x_134_);
if (lean_obj_tag(v___x_139_) == 0)
{
lean_object* v_a_140_; lean_object* v_a_141_; lean_object* v___x_142_; uint8_t v___x_143_; 
v_a_140_ = lean_ctor_get(v___x_139_, 0);
lean_inc(v_a_140_);
v_a_141_ = lean_ctor_get(v___x_139_, 1);
lean_inc(v_a_141_);
lean_dec_ref(v___x_139_);
v___x_142_ = lean_array_get_size(v_a_141_);
v___x_143_ = lean_nat_dec_lt(v___x_133_, v___x_142_);
if (v___x_143_ == 0)
{
lean_dec(v_a_141_);
v___y_65_ = v_a_136_;
v_a_66_ = v_a_140_;
goto v___jp_64_;
}
else
{
lean_object* v___x_144_; uint8_t v___x_145_; 
v___x_144_ = lean_box(0);
v___x_145_ = lean_nat_dec_le(v___x_142_, v___x_142_);
if (v___x_145_ == 0)
{
if (v___x_143_ == 0)
{
lean_dec(v_a_141_);
v___y_65_ = v_a_136_;
v_a_66_ = v_a_140_;
goto v___jp_64_;
}
else
{
size_t v___x_146_; size_t v___x_147_; lean_object* v___x_148_; 
v___x_146_ = ((size_t)0ULL);
v___x_147_ = lean_usize_of_nat(v___x_142_);
v___x_148_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_141_, v___x_146_, v___x_147_, v___x_144_, v_a_32_);
lean_dec(v_a_141_);
if (lean_obj_tag(v___x_148_) == 0)
{
lean_dec_ref(v___x_148_);
v___y_65_ = v_a_136_;
v_a_66_ = v_a_140_;
goto v___jp_64_;
}
else
{
lean_dec(v_a_140_);
lean_dec(v_a_136_);
lean_dec_ref(v_repo_30_);
lean_dec_ref(v_name_29_);
return v___x_148_;
}
}
}
else
{
size_t v___x_149_; size_t v___x_150_; lean_object* v___x_151_; 
v___x_149_ = ((size_t)0ULL);
v___x_150_ = lean_usize_of_nat(v___x_142_);
v___x_151_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_141_, v___x_149_, v___x_150_, v___x_144_, v_a_32_);
lean_dec(v_a_141_);
if (lean_obj_tag(v___x_151_) == 0)
{
lean_dec_ref(v___x_151_);
v___y_65_ = v_a_136_;
v_a_66_ = v_a_140_;
goto v___jp_64_;
}
else
{
lean_dec(v_a_140_);
lean_dec(v_a_136_);
lean_dec_ref(v_repo_30_);
lean_dec_ref(v_name_29_);
return v___x_151_;
}
}
}
}
else
{
lean_object* v_a_152_; lean_object* v___x_153_; uint8_t v___x_154_; 
lean_dec(v_a_136_);
lean_dec_ref(v_repo_30_);
lean_dec_ref(v_name_29_);
v_a_152_ = lean_ctor_get(v___x_139_, 1);
lean_inc(v_a_152_);
lean_dec_ref(v___x_139_);
v___x_153_ = lean_array_get_size(v_a_152_);
v___x_154_ = lean_nat_dec_lt(v___x_133_, v___x_153_);
if (v___x_154_ == 0)
{
lean_object* v___x_155_; lean_object* v___x_156_; 
lean_dec(v_a_152_);
v___x_155_ = lean_box(0);
v___x_156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_156_, 0, v___x_155_);
return v___x_156_;
}
else
{
lean_object* v___x_157_; uint8_t v___x_158_; 
v___x_157_ = lean_box(0);
v___x_158_ = lean_nat_dec_le(v___x_153_, v___x_153_);
if (v___x_158_ == 0)
{
if (v___x_154_ == 0)
{
lean_dec(v_a_152_);
goto v___jp_126_;
}
else
{
size_t v___x_159_; size_t v___x_160_; lean_object* v___x_161_; 
v___x_159_ = ((size_t)0ULL);
v___x_160_ = lean_usize_of_nat(v___x_153_);
v___x_161_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_152_, v___x_159_, v___x_160_, v___x_157_, v_a_32_);
lean_dec(v_a_152_);
if (lean_obj_tag(v___x_161_) == 0)
{
lean_dec_ref(v___x_161_);
goto v___jp_126_;
}
else
{
return v___x_161_;
}
}
}
else
{
size_t v___x_162_; size_t v___x_163_; lean_object* v___x_164_; 
v___x_162_ = ((size_t)0ULL);
v___x_163_ = lean_usize_of_nat(v___x_153_);
v___x_164_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_152_, v___x_162_, v___x_163_, v___x_157_, v_a_32_);
lean_dec(v_a_152_);
if (lean_obj_tag(v___x_164_) == 0)
{
lean_dec_ref(v___x_164_);
goto v___jp_126_;
}
else
{
return v___x_164_;
}
}
}
}
}
}
else
{
lean_object* v_a_175_; lean_object* v___x_176_; uint8_t v___x_177_; 
lean_dec_ref(v_repo_30_);
lean_dec_ref(v_name_29_);
v_a_175_ = lean_ctor_get(v___x_135_, 1);
lean_inc(v_a_175_);
lean_dec_ref(v___x_135_);
v___x_176_ = lean_array_get_size(v_a_175_);
v___x_177_ = lean_nat_dec_lt(v___x_133_, v___x_176_);
if (v___x_177_ == 0)
{
lean_object* v___x_178_; lean_object* v___x_179_; 
lean_dec(v_a_175_);
v___x_178_ = lean_box(0);
v___x_179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_179_, 0, v___x_178_);
return v___x_179_;
}
else
{
lean_object* v___x_180_; uint8_t v___x_181_; 
v___x_180_ = lean_box(0);
v___x_181_ = lean_nat_dec_le(v___x_176_, v___x_176_);
if (v___x_181_ == 0)
{
if (v___x_177_ == 0)
{
lean_dec(v_a_175_);
goto v___jp_129_;
}
else
{
size_t v___x_182_; size_t v___x_183_; lean_object* v___x_184_; 
v___x_182_ = ((size_t)0ULL);
v___x_183_ = lean_usize_of_nat(v___x_176_);
v___x_184_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_175_, v___x_182_, v___x_183_, v___x_180_, v_a_32_);
lean_dec(v_a_175_);
if (lean_obj_tag(v___x_184_) == 0)
{
lean_dec_ref(v___x_184_);
goto v___jp_129_;
}
else
{
return v___x_184_;
}
}
}
else
{
size_t v___x_185_; size_t v___x_186_; lean_object* v___x_187_; 
v___x_185_ = ((size_t)0ULL);
v___x_186_ = lean_usize_of_nat(v___x_176_);
v___x_187_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_175_, v___x_185_, v___x_186_, v___x_180_, v_a_32_);
lean_dec(v_a_175_);
if (lean_obj_tag(v___x_187_) == 0)
{
lean_dec_ref(v___x_187_);
goto v___jp_129_;
}
else
{
return v___x_187_;
}
}
}
}
v___jp_34_:
{
if (v_a_35_ == 0)
{
lean_object* v___x_36_; lean_object* v___x_37_; 
lean_dec_ref(v_repo_30_);
lean_dec_ref(v_name_29_);
v___x_36_ = lean_box(0);
v___x_37_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_37_, 0, v___x_36_);
return v___x_37_;
}
else
{
lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; uint8_t v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_38_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0));
v___x_39_ = lean_string_append(v_name_29_, v___x_38_);
v___x_40_ = lean_string_append(v___x_39_, v_repo_30_);
lean_dec_ref(v_repo_30_);
v___x_41_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1));
v___x_42_ = lean_string_append(v___x_40_, v___x_41_);
v___x_43_ = 2;
v___x_44_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_44_, 0, v___x_42_);
lean_ctor_set_uint8(v___x_44_, sizeof(void*)*1, v___x_43_);
lean_inc_ref(v_a_32_);
v___x_45_ = lean_apply_2(v_a_32_, v___x_44_, lean_box(0));
v___x_46_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_46_, 0, v___x_45_);
return v___x_46_;
}
}
v___jp_47_:
{
lean_object* v___x_51_; uint8_t v___x_52_; 
v___x_51_ = lean_array_get_size(v___y_48_);
v___x_52_ = lean_nat_dec_lt(v___y_49_, v___x_51_);
if (v___x_52_ == 0)
{
lean_dec_ref(v___y_48_);
v_a_35_ = v_val_50_;
goto v___jp_34_;
}
else
{
lean_object* v___x_53_; uint8_t v___x_54_; 
v___x_53_ = lean_box(0);
v___x_54_ = lean_nat_dec_le(v___x_51_, v___x_51_);
if (v___x_54_ == 0)
{
if (v___x_52_ == 0)
{
lean_dec_ref(v___y_48_);
v_a_35_ = v_val_50_;
goto v___jp_34_;
}
else
{
size_t v___x_55_; size_t v___x_56_; lean_object* v___x_57_; 
v___x_55_ = ((size_t)0ULL);
v___x_56_ = lean_usize_of_nat(v___x_51_);
v___x_57_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_48_, v___x_55_, v___x_56_, v___x_53_, v_a_32_);
lean_dec_ref(v___y_48_);
if (lean_obj_tag(v___x_57_) == 0)
{
lean_dec_ref(v___x_57_);
v_a_35_ = v_val_50_;
goto v___jp_34_;
}
else
{
lean_dec_ref(v_repo_30_);
lean_dec_ref(v_name_29_);
return v___x_57_;
}
}
}
else
{
size_t v___x_58_; size_t v___x_59_; lean_object* v___x_60_; 
v___x_58_ = ((size_t)0ULL);
v___x_59_ = lean_usize_of_nat(v___x_51_);
v___x_60_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_48_, v___x_58_, v___x_59_, v___x_53_, v_a_32_);
lean_dec_ref(v___y_48_);
if (lean_obj_tag(v___x_60_) == 0)
{
lean_dec_ref(v___x_60_);
v_a_35_ = v_val_50_;
goto v___jp_34_;
}
else
{
lean_dec_ref(v_repo_30_);
lean_dec_ref(v_name_29_);
return v___x_60_;
}
}
}
}
v___jp_61_:
{
lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_62_ = lean_box(0);
v___x_63_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_63_, 0, v___x_62_);
return v___x_63_;
}
v___jp_64_:
{
uint8_t v___x_67_; 
v___x_67_ = lean_string_dec_eq(v_a_66_, v___y_65_);
lean_dec_ref(v_a_66_);
if (v___x_67_ == 0)
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; uint8_t v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_68_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_69_ = lean_string_append(v_name_29_, v___x_68_);
v___x_70_ = lean_string_append(v___x_69_, v___y_65_);
v___x_71_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3));
v___x_72_ = lean_string_append(v___x_70_, v___x_71_);
v___x_73_ = 1;
v___x_74_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_74_, 0, v___x_72_);
lean_ctor_set_uint8(v___x_74_, sizeof(void*)*1, v___x_73_);
lean_inc_ref(v_a_32_);
v___x_75_ = lean_apply_2(v_a_32_, v___x_74_, lean_box(0));
v___x_76_ = lean_unsigned_to_nat(0u);
v___x_77_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
v___x_78_ = l_Lake_GitRepo_checkoutDetach(v___y_65_, v_repo_30_, v___x_77_);
if (lean_obj_tag(v___x_78_) == 0)
{
lean_object* v_a_79_; lean_object* v_a_80_; lean_object* v___x_81_; uint8_t v___x_82_; 
v_a_79_ = lean_ctor_get(v___x_78_, 0);
lean_inc(v_a_79_);
v_a_80_ = lean_ctor_get(v___x_78_, 1);
lean_inc(v_a_80_);
lean_dec_ref(v___x_78_);
v___x_81_ = lean_array_get_size(v_a_80_);
v___x_82_ = lean_nat_dec_lt(v___x_76_, v___x_81_);
if (v___x_82_ == 0)
{
lean_object* v___x_83_; 
lean_dec(v_a_80_);
v___x_83_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_83_, 0, v_a_79_);
return v___x_83_;
}
else
{
lean_object* v___x_84_; uint8_t v___x_85_; 
v___x_84_ = lean_box(0);
v___x_85_ = lean_nat_dec_le(v___x_81_, v___x_81_);
if (v___x_85_ == 0)
{
if (v___x_82_ == 0)
{
lean_object* v___x_86_; 
lean_dec(v_a_80_);
v___x_86_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_86_, 0, v_a_79_);
return v___x_86_;
}
else
{
size_t v___x_87_; size_t v___x_88_; lean_object* v___x_89_; 
v___x_87_ = ((size_t)0ULL);
v___x_88_ = lean_usize_of_nat(v___x_81_);
v___x_89_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_80_, v___x_87_, v___x_88_, v___x_84_, v_a_32_);
lean_dec(v_a_80_);
if (lean_obj_tag(v___x_89_) == 0)
{
lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_96_; 
v_isSharedCheck_96_ = !lean_is_exclusive(v___x_89_);
if (v_isSharedCheck_96_ == 0)
{
lean_object* v_unused_97_; 
v_unused_97_ = lean_ctor_get(v___x_89_, 0);
lean_dec(v_unused_97_);
v___x_91_ = v___x_89_;
v_isShared_92_ = v_isSharedCheck_96_;
goto v_resetjp_90_;
}
else
{
lean_dec(v___x_89_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_96_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v___x_94_; 
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 0, v_a_79_);
v___x_94_ = v___x_91_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v_a_79_);
v___x_94_ = v_reuseFailAlloc_95_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
return v___x_94_;
}
}
}
else
{
lean_dec(v_a_79_);
return v___x_89_;
}
}
}
else
{
size_t v___x_98_; size_t v___x_99_; lean_object* v___x_100_; 
v___x_98_ = ((size_t)0ULL);
v___x_99_ = lean_usize_of_nat(v___x_81_);
v___x_100_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_80_, v___x_98_, v___x_99_, v___x_84_, v_a_32_);
lean_dec(v_a_80_);
if (lean_obj_tag(v___x_100_) == 0)
{
lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_107_; 
v_isSharedCheck_107_ = !lean_is_exclusive(v___x_100_);
if (v_isSharedCheck_107_ == 0)
{
lean_object* v_unused_108_; 
v_unused_108_ = lean_ctor_get(v___x_100_, 0);
lean_dec(v_unused_108_);
v___x_102_ = v___x_100_;
v_isShared_103_ = v_isSharedCheck_107_;
goto v_resetjp_101_;
}
else
{
lean_dec(v___x_100_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_107_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v___x_105_; 
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 0, v_a_79_);
v___x_105_ = v___x_102_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v_a_79_);
v___x_105_ = v_reuseFailAlloc_106_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
return v___x_105_;
}
}
}
else
{
lean_dec(v_a_79_);
return v___x_100_;
}
}
}
}
else
{
lean_object* v_a_109_; lean_object* v___x_110_; uint8_t v___x_111_; 
v_a_109_ = lean_ctor_get(v___x_78_, 1);
lean_inc(v_a_109_);
lean_dec_ref(v___x_78_);
v___x_110_ = lean_array_get_size(v_a_109_);
v___x_111_ = lean_nat_dec_lt(v___x_76_, v___x_110_);
if (v___x_111_ == 0)
{
lean_object* v___x_112_; lean_object* v___x_113_; 
lean_dec(v_a_109_);
v___x_112_ = lean_box(0);
v___x_113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_113_, 0, v___x_112_);
return v___x_113_;
}
else
{
lean_object* v___x_114_; uint8_t v___x_115_; 
v___x_114_ = lean_box(0);
v___x_115_ = lean_nat_dec_le(v___x_110_, v___x_110_);
if (v___x_115_ == 0)
{
if (v___x_111_ == 0)
{
lean_dec(v_a_109_);
goto v___jp_61_;
}
else
{
size_t v___x_116_; size_t v___x_117_; lean_object* v___x_118_; 
v___x_116_ = ((size_t)0ULL);
v___x_117_ = lean_usize_of_nat(v___x_110_);
v___x_118_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_109_, v___x_116_, v___x_117_, v___x_114_, v_a_32_);
lean_dec(v_a_109_);
if (lean_obj_tag(v___x_118_) == 0)
{
lean_dec_ref(v___x_118_);
goto v___jp_61_;
}
else
{
return v___x_118_;
}
}
}
else
{
size_t v___x_119_; size_t v___x_120_; lean_object* v___x_121_; 
v___x_119_ = ((size_t)0ULL);
v___x_120_ = lean_usize_of_nat(v___x_110_);
v___x_121_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_109_, v___x_119_, v___x_120_, v___x_114_, v_a_32_);
lean_dec(v_a_109_);
if (lean_obj_tag(v___x_121_) == 0)
{
lean_dec_ref(v___x_121_);
goto v___jp_61_;
}
else
{
return v___x_121_;
}
}
}
}
}
else
{
uint8_t v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
lean_dec_ref(v___y_65_);
lean_inc_ref(v_repo_30_);
v___x_122_ = l_Lake_GitRepo_hasNoDiff(v_repo_30_);
v___x_123_ = lean_unsigned_to_nat(0u);
v___x_124_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
if (v___x_122_ == 0)
{
v___y_48_ = v___x_124_;
v___y_49_ = v___x_123_;
v_val_50_ = v___x_67_;
goto v___jp_47_;
}
else
{
uint8_t v___x_125_; 
v___x_125_ = 0;
v___y_48_ = v___x_124_;
v___y_49_ = v___x_123_;
v_val_50_ = v___x_125_;
goto v___jp_47_;
}
}
}
v___jp_126_:
{
lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_127_ = lean_box(0);
v___x_128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
return v___x_128_;
}
v___jp_129_:
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = lean_box(0);
v___x_131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_131_, 0, v___x_130_);
return v___x_131_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___boxed(lean_object* v_name_188_, lean_object* v_repo_189_, lean_object* v_rev_x3f_190_, lean_object* v_a_191_, lean_object* v_a_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg(v_name_188_, v_repo_189_, v_rev_x3f_190_, v_a_191_);
lean_dec_ref(v_a_191_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg(lean_object* v_name_195_, lean_object* v_repo_196_, lean_object* v_url_197_, lean_object* v_rev_x3f_198_, lean_object* v_a_199_){
_start:
{
lean_object* v_a_205_; lean_object* v___y_303_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; uint8_t v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_307_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___closed__0));
lean_inc_ref(v_name_195_);
v___x_308_ = lean_string_append(v_name_195_, v___x_307_);
v___x_309_ = lean_string_append(v___x_308_, v_url_197_);
v___x_310_ = 1;
v___x_311_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_311_, 0, v___x_309_);
lean_ctor_set_uint8(v___x_311_, sizeof(void*)*1, v___x_310_);
lean_inc_ref(v_a_199_);
v___x_312_ = lean_apply_2(v_a_199_, v___x_311_, lean_box(0));
v___x_313_ = lean_unsigned_to_nat(0u);
v___x_314_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
lean_inc_ref(v_repo_196_);
v___x_315_ = l_Lake_GitRepo_clone(v_url_197_, v_repo_196_, v___x_314_);
if (lean_obj_tag(v___x_315_) == 0)
{
lean_object* v_a_316_; lean_object* v___x_317_; uint8_t v___x_318_; 
v_a_316_ = lean_ctor_get(v___x_315_, 1);
lean_inc(v_a_316_);
lean_dec_ref(v___x_315_);
v___x_317_ = lean_array_get_size(v_a_316_);
v___x_318_ = lean_nat_dec_lt(v___x_313_, v___x_317_);
if (v___x_318_ == 0)
{
lean_dec(v_a_316_);
goto v___jp_263_;
}
else
{
lean_object* v___x_319_; uint8_t v___x_320_; 
v___x_319_ = lean_box(0);
v___x_320_ = lean_nat_dec_le(v___x_317_, v___x_317_);
if (v___x_320_ == 0)
{
if (v___x_318_ == 0)
{
lean_dec(v_a_316_);
goto v___jp_263_;
}
else
{
size_t v___x_321_; size_t v___x_322_; lean_object* v___x_323_; 
v___x_321_ = ((size_t)0ULL);
v___x_322_ = lean_usize_of_nat(v___x_317_);
v___x_323_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_316_, v___x_321_, v___x_322_, v___x_319_, v_a_199_);
lean_dec(v_a_316_);
if (lean_obj_tag(v___x_323_) == 0)
{
lean_dec_ref(v___x_323_);
goto v___jp_263_;
}
else
{
v___y_303_ = v___x_323_;
goto v___jp_302_;
}
}
}
else
{
size_t v___x_324_; size_t v___x_325_; lean_object* v___x_326_; 
v___x_324_ = ((size_t)0ULL);
v___x_325_ = lean_usize_of_nat(v___x_317_);
v___x_326_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_316_, v___x_324_, v___x_325_, v___x_319_, v_a_199_);
lean_dec(v_a_316_);
if (lean_obj_tag(v___x_326_) == 0)
{
lean_dec_ref(v___x_326_);
goto v___jp_263_;
}
else
{
v___y_303_ = v___x_326_;
goto v___jp_302_;
}
}
}
}
else
{
lean_object* v_a_327_; lean_object* v___x_328_; uint8_t v___x_329_; 
v_a_327_ = lean_ctor_get(v___x_315_, 1);
lean_inc(v_a_327_);
lean_dec_ref(v___x_315_);
v___x_328_ = lean_array_get_size(v_a_327_);
v___x_329_ = lean_nat_dec_lt(v___x_313_, v___x_328_);
if (v___x_329_ == 0)
{
lean_object* v___x_330_; lean_object* v___x_331_; 
lean_dec(v_a_327_);
lean_dec(v_rev_x3f_198_);
lean_dec_ref(v_repo_196_);
lean_dec_ref(v_name_195_);
v___x_330_ = lean_box(0);
v___x_331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_331_, 0, v___x_330_);
return v___x_331_;
}
else
{
lean_object* v___x_332_; uint8_t v___x_333_; 
v___x_332_ = lean_box(0);
v___x_333_ = lean_nat_dec_le(v___x_328_, v___x_328_);
if (v___x_333_ == 0)
{
if (v___x_329_ == 0)
{
lean_dec(v_a_327_);
lean_dec(v_rev_x3f_198_);
lean_dec_ref(v_repo_196_);
lean_dec_ref(v_name_195_);
goto v___jp_304_;
}
else
{
size_t v___x_334_; size_t v___x_335_; lean_object* v___x_336_; 
v___x_334_ = ((size_t)0ULL);
v___x_335_ = lean_usize_of_nat(v___x_328_);
v___x_336_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_327_, v___x_334_, v___x_335_, v___x_332_, v_a_199_);
lean_dec(v_a_327_);
if (lean_obj_tag(v___x_336_) == 0)
{
lean_dec_ref(v___x_336_);
lean_dec(v_rev_x3f_198_);
lean_dec_ref(v_repo_196_);
lean_dec_ref(v_name_195_);
goto v___jp_304_;
}
else
{
v___y_303_ = v___x_336_;
goto v___jp_302_;
}
}
}
else
{
size_t v___x_337_; size_t v___x_338_; lean_object* v___x_339_; 
v___x_337_ = ((size_t)0ULL);
v___x_338_ = lean_usize_of_nat(v___x_328_);
v___x_339_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_327_, v___x_337_, v___x_338_, v___x_332_, v_a_199_);
lean_dec(v_a_327_);
if (lean_obj_tag(v___x_339_) == 0)
{
lean_dec_ref(v___x_339_);
lean_dec(v_rev_x3f_198_);
lean_dec_ref(v_repo_196_);
lean_dec_ref(v_name_195_);
goto v___jp_304_;
}
else
{
v___y_303_ = v___x_339_;
goto v___jp_302_;
}
}
}
}
v___jp_201_:
{
lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_202_ = lean_box(0);
v___x_203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_203_, 0, v___x_202_);
return v___x_203_;
}
v___jp_204_:
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; uint8_t v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_206_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_207_ = lean_string_append(v_name_195_, v___x_206_);
v___x_208_ = lean_string_append(v___x_207_, v_a_205_);
v___x_209_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3));
v___x_210_ = lean_string_append(v___x_208_, v___x_209_);
v___x_211_ = 1;
v___x_212_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_212_, 0, v___x_210_);
lean_ctor_set_uint8(v___x_212_, sizeof(void*)*1, v___x_211_);
lean_inc_ref(v_a_199_);
v___x_213_ = lean_apply_2(v_a_199_, v___x_212_, lean_box(0));
v___x_214_ = lean_unsigned_to_nat(0u);
v___x_215_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
v___x_216_ = l_Lake_GitRepo_checkoutDetach(v_a_205_, v_repo_196_, v___x_215_);
if (lean_obj_tag(v___x_216_) == 0)
{
lean_object* v_a_217_; lean_object* v_a_218_; lean_object* v___x_219_; uint8_t v___x_220_; 
v_a_217_ = lean_ctor_get(v___x_216_, 0);
lean_inc(v_a_217_);
v_a_218_ = lean_ctor_get(v___x_216_, 1);
lean_inc(v_a_218_);
lean_dec_ref(v___x_216_);
v___x_219_ = lean_array_get_size(v_a_218_);
v___x_220_ = lean_nat_dec_lt(v___x_214_, v___x_219_);
if (v___x_220_ == 0)
{
lean_object* v___x_221_; 
lean_dec(v_a_218_);
v___x_221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_221_, 0, v_a_217_);
return v___x_221_;
}
else
{
lean_object* v___x_222_; uint8_t v___x_223_; 
v___x_222_ = lean_box(0);
v___x_223_ = lean_nat_dec_le(v___x_219_, v___x_219_);
if (v___x_223_ == 0)
{
if (v___x_220_ == 0)
{
lean_object* v___x_224_; 
lean_dec(v_a_218_);
v___x_224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_224_, 0, v_a_217_);
return v___x_224_;
}
else
{
size_t v___x_225_; size_t v___x_226_; lean_object* v___x_227_; 
v___x_225_ = ((size_t)0ULL);
v___x_226_ = lean_usize_of_nat(v___x_219_);
v___x_227_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_218_, v___x_225_, v___x_226_, v___x_222_, v_a_199_);
lean_dec(v_a_218_);
if (lean_obj_tag(v___x_227_) == 0)
{
lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_234_; 
v_isSharedCheck_234_ = !lean_is_exclusive(v___x_227_);
if (v_isSharedCheck_234_ == 0)
{
lean_object* v_unused_235_; 
v_unused_235_ = lean_ctor_get(v___x_227_, 0);
lean_dec(v_unused_235_);
v___x_229_ = v___x_227_;
v_isShared_230_ = v_isSharedCheck_234_;
goto v_resetjp_228_;
}
else
{
lean_dec(v___x_227_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_234_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v___x_232_; 
if (v_isShared_230_ == 0)
{
lean_ctor_set(v___x_229_, 0, v_a_217_);
v___x_232_ = v___x_229_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v_a_217_);
v___x_232_ = v_reuseFailAlloc_233_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
return v___x_232_;
}
}
}
else
{
lean_dec(v_a_217_);
return v___x_227_;
}
}
}
else
{
size_t v___x_236_; size_t v___x_237_; lean_object* v___x_238_; 
v___x_236_ = ((size_t)0ULL);
v___x_237_ = lean_usize_of_nat(v___x_219_);
v___x_238_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_218_, v___x_236_, v___x_237_, v___x_222_, v_a_199_);
lean_dec(v_a_218_);
if (lean_obj_tag(v___x_238_) == 0)
{
lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_245_; 
v_isSharedCheck_245_ = !lean_is_exclusive(v___x_238_);
if (v_isSharedCheck_245_ == 0)
{
lean_object* v_unused_246_; 
v_unused_246_ = lean_ctor_get(v___x_238_, 0);
lean_dec(v_unused_246_);
v___x_240_ = v___x_238_;
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
else
{
lean_dec(v___x_238_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_243_; 
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 0, v_a_217_);
v___x_243_ = v___x_240_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_a_217_);
v___x_243_ = v_reuseFailAlloc_244_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
return v___x_243_;
}
}
}
else
{
lean_dec(v_a_217_);
return v___x_238_;
}
}
}
}
else
{
lean_object* v_a_247_; lean_object* v___x_248_; uint8_t v___x_249_; 
v_a_247_ = lean_ctor_get(v___x_216_, 1);
lean_inc(v_a_247_);
lean_dec_ref(v___x_216_);
v___x_248_ = lean_array_get_size(v_a_247_);
v___x_249_ = lean_nat_dec_lt(v___x_214_, v___x_248_);
if (v___x_249_ == 0)
{
lean_object* v___x_250_; lean_object* v___x_251_; 
lean_dec(v_a_247_);
v___x_250_ = lean_box(0);
v___x_251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
return v___x_251_;
}
else
{
lean_object* v___x_252_; uint8_t v___x_253_; 
v___x_252_ = lean_box(0);
v___x_253_ = lean_nat_dec_le(v___x_248_, v___x_248_);
if (v___x_253_ == 0)
{
if (v___x_249_ == 0)
{
lean_dec(v_a_247_);
goto v___jp_201_;
}
else
{
size_t v___x_254_; size_t v___x_255_; lean_object* v___x_256_; 
v___x_254_ = ((size_t)0ULL);
v___x_255_ = lean_usize_of_nat(v___x_248_);
v___x_256_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_247_, v___x_254_, v___x_255_, v___x_252_, v_a_199_);
lean_dec(v_a_247_);
if (lean_obj_tag(v___x_256_) == 0)
{
lean_dec_ref(v___x_256_);
goto v___jp_201_;
}
else
{
return v___x_256_;
}
}
}
else
{
size_t v___x_257_; size_t v___x_258_; lean_object* v___x_259_; 
v___x_257_ = ((size_t)0ULL);
v___x_258_ = lean_usize_of_nat(v___x_248_);
v___x_259_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_247_, v___x_257_, v___x_258_, v___x_252_, v_a_199_);
lean_dec(v_a_247_);
if (lean_obj_tag(v___x_259_) == 0)
{
lean_dec_ref(v___x_259_);
goto v___jp_201_;
}
else
{
return v___x_259_;
}
}
}
}
}
v___jp_260_:
{
lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_261_ = lean_box(0);
v___x_262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_262_, 0, v___x_261_);
return v___x_262_;
}
v___jp_263_:
{
if (lean_obj_tag(v_rev_x3f_198_) == 1)
{
lean_object* v_val_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_299_; 
v_val_264_ = lean_ctor_get(v_rev_x3f_198_, 0);
v_isSharedCheck_299_ = !lean_is_exclusive(v_rev_x3f_198_);
if (v_isSharedCheck_299_ == 0)
{
v___x_266_ = v_rev_x3f_198_;
v_isShared_267_ = v_isSharedCheck_299_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_val_264_);
lean_dec(v_rev_x3f_198_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_299_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_268_ = l_Lake_Git_defaultRemote;
v___x_269_ = lean_unsigned_to_nat(0u);
v___x_270_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
lean_inc_ref(v_repo_196_);
v___x_271_ = l_Lake_GitRepo_resolveRemoteRevision(v_val_264_, v___x_268_, v_repo_196_, v___x_270_);
if (lean_obj_tag(v___x_271_) == 0)
{
lean_object* v_a_272_; lean_object* v_a_273_; lean_object* v___x_274_; uint8_t v___x_275_; 
lean_del_object(v___x_266_);
v_a_272_ = lean_ctor_get(v___x_271_, 0);
lean_inc(v_a_272_);
v_a_273_ = lean_ctor_get(v___x_271_, 1);
lean_inc(v_a_273_);
lean_dec_ref(v___x_271_);
v___x_274_ = lean_array_get_size(v_a_273_);
v___x_275_ = lean_nat_dec_lt(v___x_269_, v___x_274_);
if (v___x_275_ == 0)
{
lean_dec(v_a_273_);
v_a_205_ = v_a_272_;
goto v___jp_204_;
}
else
{
lean_object* v___x_276_; uint8_t v___x_277_; 
v___x_276_ = lean_box(0);
v___x_277_ = lean_nat_dec_le(v___x_274_, v___x_274_);
if (v___x_277_ == 0)
{
if (v___x_275_ == 0)
{
lean_dec(v_a_273_);
v_a_205_ = v_a_272_;
goto v___jp_204_;
}
else
{
size_t v___x_278_; size_t v___x_279_; lean_object* v___x_280_; 
v___x_278_ = ((size_t)0ULL);
v___x_279_ = lean_usize_of_nat(v___x_274_);
v___x_280_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_273_, v___x_278_, v___x_279_, v___x_276_, v_a_199_);
lean_dec(v_a_273_);
if (lean_obj_tag(v___x_280_) == 0)
{
lean_dec_ref(v___x_280_);
v_a_205_ = v_a_272_;
goto v___jp_204_;
}
else
{
lean_dec(v_a_272_);
lean_dec_ref(v_repo_196_);
lean_dec_ref(v_name_195_);
return v___x_280_;
}
}
}
else
{
size_t v___x_281_; size_t v___x_282_; lean_object* v___x_283_; 
v___x_281_ = ((size_t)0ULL);
v___x_282_ = lean_usize_of_nat(v___x_274_);
v___x_283_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_273_, v___x_281_, v___x_282_, v___x_276_, v_a_199_);
lean_dec(v_a_273_);
if (lean_obj_tag(v___x_283_) == 0)
{
lean_dec_ref(v___x_283_);
v_a_205_ = v_a_272_;
goto v___jp_204_;
}
else
{
lean_dec(v_a_272_);
lean_dec_ref(v_repo_196_);
lean_dec_ref(v_name_195_);
return v___x_283_;
}
}
}
}
else
{
lean_object* v_a_284_; lean_object* v___x_285_; uint8_t v___x_286_; 
lean_dec_ref(v_repo_196_);
lean_dec_ref(v_name_195_);
v_a_284_ = lean_ctor_get(v___x_271_, 1);
lean_inc(v_a_284_);
lean_dec_ref(v___x_271_);
v___x_285_ = lean_array_get_size(v_a_284_);
v___x_286_ = lean_nat_dec_lt(v___x_269_, v___x_285_);
if (v___x_286_ == 0)
{
lean_object* v___x_287_; lean_object* v___x_289_; 
lean_dec(v_a_284_);
v___x_287_ = lean_box(0);
if (v_isShared_267_ == 0)
{
lean_ctor_set(v___x_266_, 0, v___x_287_);
v___x_289_ = v___x_266_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v___x_287_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
return v___x_289_;
}
}
else
{
lean_object* v___x_291_; uint8_t v___x_292_; 
lean_del_object(v___x_266_);
v___x_291_ = lean_box(0);
v___x_292_ = lean_nat_dec_le(v___x_285_, v___x_285_);
if (v___x_292_ == 0)
{
if (v___x_286_ == 0)
{
lean_dec(v_a_284_);
goto v___jp_260_;
}
else
{
size_t v___x_293_; size_t v___x_294_; lean_object* v___x_295_; 
v___x_293_ = ((size_t)0ULL);
v___x_294_ = lean_usize_of_nat(v___x_285_);
v___x_295_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_284_, v___x_293_, v___x_294_, v___x_291_, v_a_199_);
lean_dec(v_a_284_);
if (lean_obj_tag(v___x_295_) == 0)
{
lean_dec_ref(v___x_295_);
goto v___jp_260_;
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
v___x_297_ = lean_usize_of_nat(v___x_285_);
v___x_298_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_284_, v___x_296_, v___x_297_, v___x_291_, v_a_199_);
lean_dec(v_a_284_);
if (lean_obj_tag(v___x_298_) == 0)
{
lean_dec_ref(v___x_298_);
goto v___jp_260_;
}
else
{
return v___x_298_;
}
}
}
}
}
}
else
{
lean_object* v___x_300_; lean_object* v___x_301_; 
lean_dec(v_rev_x3f_198_);
lean_dec_ref(v_repo_196_);
lean_dec_ref(v_name_195_);
v___x_300_ = lean_box(0);
v___x_301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
return v___x_301_;
}
}
v___jp_302_:
{
if (lean_obj_tag(v___y_303_) == 0)
{
lean_dec_ref(v___y_303_);
goto v___jp_263_;
}
else
{
lean_dec(v_rev_x3f_198_);
lean_dec_ref(v_repo_196_);
lean_dec_ref(v_name_195_);
return v___y_303_;
}
}
v___jp_304_:
{
lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_305_ = lean_box(0);
v___x_306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
return v___x_306_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___boxed(lean_object* v_name_340_, lean_object* v_repo_341_, lean_object* v_url_342_, lean_object* v_rev_x3f_343_, lean_object* v_a_344_, lean_object* v_a_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg(v_name_340_, v_repo_341_, v_url_342_, v_rev_x3f_343_, v_a_344_);
lean_dec_ref(v_a_344_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(lean_object* v_a_347_, lean_object* v_name_348_, lean_object* v_repo_349_, lean_object* v_url_350_, lean_object* v_rev_x3f_351_){
_start:
{
lean_object* v_a_357_; lean_object* v___y_455_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; uint8_t v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_459_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___closed__0));
lean_inc_ref(v_name_348_);
v___x_460_ = lean_string_append(v_name_348_, v___x_459_);
v___x_461_ = lean_string_append(v___x_460_, v_url_350_);
v___x_462_ = 1;
v___x_463_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_463_, 0, v___x_461_);
lean_ctor_set_uint8(v___x_463_, sizeof(void*)*1, v___x_462_);
lean_inc_ref(v_a_347_);
v___x_464_ = lean_apply_2(v_a_347_, v___x_463_, lean_box(0));
v___x_465_ = lean_unsigned_to_nat(0u);
v___x_466_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
lean_inc_ref(v_repo_349_);
v___x_467_ = l_Lake_GitRepo_clone(v_url_350_, v_repo_349_, v___x_466_);
if (lean_obj_tag(v___x_467_) == 0)
{
lean_object* v_a_468_; lean_object* v___x_469_; uint8_t v___x_470_; 
v_a_468_ = lean_ctor_get(v___x_467_, 1);
lean_inc(v_a_468_);
lean_dec_ref(v___x_467_);
v___x_469_ = lean_array_get_size(v_a_468_);
v___x_470_ = lean_nat_dec_lt(v___x_465_, v___x_469_);
if (v___x_470_ == 0)
{
lean_dec(v_a_468_);
goto v___jp_415_;
}
else
{
lean_object* v___x_471_; uint8_t v___x_472_; 
v___x_471_ = lean_box(0);
v___x_472_ = lean_nat_dec_le(v___x_469_, v___x_469_);
if (v___x_472_ == 0)
{
if (v___x_470_ == 0)
{
lean_dec(v_a_468_);
goto v___jp_415_;
}
else
{
size_t v___x_473_; size_t v___x_474_; lean_object* v___x_475_; 
v___x_473_ = ((size_t)0ULL);
v___x_474_ = lean_usize_of_nat(v___x_469_);
v___x_475_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_468_, v___x_473_, v___x_474_, v___x_471_, v_a_347_);
lean_dec(v_a_468_);
if (lean_obj_tag(v___x_475_) == 0)
{
lean_dec_ref(v___x_475_);
goto v___jp_415_;
}
else
{
v___y_455_ = v___x_475_;
goto v___jp_454_;
}
}
}
else
{
size_t v___x_476_; size_t v___x_477_; lean_object* v___x_478_; 
v___x_476_ = ((size_t)0ULL);
v___x_477_ = lean_usize_of_nat(v___x_469_);
v___x_478_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_468_, v___x_476_, v___x_477_, v___x_471_, v_a_347_);
lean_dec(v_a_468_);
if (lean_obj_tag(v___x_478_) == 0)
{
lean_dec_ref(v___x_478_);
goto v___jp_415_;
}
else
{
v___y_455_ = v___x_478_;
goto v___jp_454_;
}
}
}
}
else
{
lean_object* v_a_479_; lean_object* v___x_480_; uint8_t v___x_481_; 
v_a_479_ = lean_ctor_get(v___x_467_, 1);
lean_inc(v_a_479_);
lean_dec_ref(v___x_467_);
v___x_480_ = lean_array_get_size(v_a_479_);
v___x_481_ = lean_nat_dec_lt(v___x_465_, v___x_480_);
if (v___x_481_ == 0)
{
lean_object* v___x_482_; lean_object* v___x_483_; 
lean_dec(v_a_479_);
lean_dec(v_rev_x3f_351_);
lean_dec_ref(v_repo_349_);
lean_dec_ref(v_name_348_);
v___x_482_ = lean_box(0);
v___x_483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
return v___x_483_;
}
else
{
lean_object* v___x_484_; uint8_t v___x_485_; 
v___x_484_ = lean_box(0);
v___x_485_ = lean_nat_dec_le(v___x_480_, v___x_480_);
if (v___x_485_ == 0)
{
if (v___x_481_ == 0)
{
lean_dec(v_a_479_);
lean_dec(v_rev_x3f_351_);
lean_dec_ref(v_repo_349_);
lean_dec_ref(v_name_348_);
goto v___jp_456_;
}
else
{
size_t v___x_486_; size_t v___x_487_; lean_object* v___x_488_; 
v___x_486_ = ((size_t)0ULL);
v___x_487_ = lean_usize_of_nat(v___x_480_);
v___x_488_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_479_, v___x_486_, v___x_487_, v___x_484_, v_a_347_);
lean_dec(v_a_479_);
if (lean_obj_tag(v___x_488_) == 0)
{
lean_dec_ref(v___x_488_);
lean_dec(v_rev_x3f_351_);
lean_dec_ref(v_repo_349_);
lean_dec_ref(v_name_348_);
goto v___jp_456_;
}
else
{
v___y_455_ = v___x_488_;
goto v___jp_454_;
}
}
}
else
{
size_t v___x_489_; size_t v___x_490_; lean_object* v___x_491_; 
v___x_489_ = ((size_t)0ULL);
v___x_490_ = lean_usize_of_nat(v___x_480_);
v___x_491_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_479_, v___x_489_, v___x_490_, v___x_484_, v_a_347_);
lean_dec(v_a_479_);
if (lean_obj_tag(v___x_491_) == 0)
{
lean_dec_ref(v___x_491_);
lean_dec(v_rev_x3f_351_);
lean_dec_ref(v_repo_349_);
lean_dec_ref(v_name_348_);
goto v___jp_456_;
}
else
{
v___y_455_ = v___x_491_;
goto v___jp_454_;
}
}
}
}
v___jp_353_:
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = lean_box(0);
v___x_355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_355_, 0, v___x_354_);
return v___x_355_;
}
v___jp_356_:
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; uint8_t v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_358_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_359_ = lean_string_append(v_name_348_, v___x_358_);
v___x_360_ = lean_string_append(v___x_359_, v_a_357_);
v___x_361_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3));
v___x_362_ = lean_string_append(v___x_360_, v___x_361_);
v___x_363_ = 1;
v___x_364_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_364_, 0, v___x_362_);
lean_ctor_set_uint8(v___x_364_, sizeof(void*)*1, v___x_363_);
lean_inc_ref(v_a_347_);
v___x_365_ = lean_apply_2(v_a_347_, v___x_364_, lean_box(0));
v___x_366_ = lean_unsigned_to_nat(0u);
v___x_367_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
v___x_368_ = l_Lake_GitRepo_checkoutDetach(v_a_357_, v_repo_349_, v___x_367_);
if (lean_obj_tag(v___x_368_) == 0)
{
lean_object* v_a_369_; lean_object* v_a_370_; lean_object* v___x_371_; uint8_t v___x_372_; 
v_a_369_ = lean_ctor_get(v___x_368_, 0);
lean_inc(v_a_369_);
v_a_370_ = lean_ctor_get(v___x_368_, 1);
lean_inc(v_a_370_);
lean_dec_ref(v___x_368_);
v___x_371_ = lean_array_get_size(v_a_370_);
v___x_372_ = lean_nat_dec_lt(v___x_366_, v___x_371_);
if (v___x_372_ == 0)
{
lean_object* v___x_373_; 
lean_dec(v_a_370_);
v___x_373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_373_, 0, v_a_369_);
return v___x_373_;
}
else
{
lean_object* v___x_374_; uint8_t v___x_375_; 
v___x_374_ = lean_box(0);
v___x_375_ = lean_nat_dec_le(v___x_371_, v___x_371_);
if (v___x_375_ == 0)
{
if (v___x_372_ == 0)
{
lean_object* v___x_376_; 
lean_dec(v_a_370_);
v___x_376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_376_, 0, v_a_369_);
return v___x_376_;
}
else
{
size_t v___x_377_; size_t v___x_378_; lean_object* v___x_379_; 
v___x_377_ = ((size_t)0ULL);
v___x_378_ = lean_usize_of_nat(v___x_371_);
v___x_379_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_370_, v___x_377_, v___x_378_, v___x_374_, v_a_347_);
lean_dec(v_a_370_);
if (lean_obj_tag(v___x_379_) == 0)
{
lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_386_; 
v_isSharedCheck_386_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_386_ == 0)
{
lean_object* v_unused_387_; 
v_unused_387_ = lean_ctor_get(v___x_379_, 0);
lean_dec(v_unused_387_);
v___x_381_ = v___x_379_;
v_isShared_382_ = v_isSharedCheck_386_;
goto v_resetjp_380_;
}
else
{
lean_dec(v___x_379_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_386_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v___x_384_; 
if (v_isShared_382_ == 0)
{
lean_ctor_set(v___x_381_, 0, v_a_369_);
v___x_384_ = v___x_381_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v_a_369_);
v___x_384_ = v_reuseFailAlloc_385_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
return v___x_384_;
}
}
}
else
{
lean_dec(v_a_369_);
return v___x_379_;
}
}
}
else
{
size_t v___x_388_; size_t v___x_389_; lean_object* v___x_390_; 
v___x_388_ = ((size_t)0ULL);
v___x_389_ = lean_usize_of_nat(v___x_371_);
v___x_390_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_370_, v___x_388_, v___x_389_, v___x_374_, v_a_347_);
lean_dec(v_a_370_);
if (lean_obj_tag(v___x_390_) == 0)
{
lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_397_; 
v_isSharedCheck_397_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_397_ == 0)
{
lean_object* v_unused_398_; 
v_unused_398_ = lean_ctor_get(v___x_390_, 0);
lean_dec(v_unused_398_);
v___x_392_ = v___x_390_;
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
else
{
lean_dec(v___x_390_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___x_395_; 
if (v_isShared_393_ == 0)
{
lean_ctor_set(v___x_392_, 0, v_a_369_);
v___x_395_ = v___x_392_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_a_369_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
}
else
{
lean_dec(v_a_369_);
return v___x_390_;
}
}
}
}
else
{
lean_object* v_a_399_; lean_object* v___x_400_; uint8_t v___x_401_; 
v_a_399_ = lean_ctor_get(v___x_368_, 1);
lean_inc(v_a_399_);
lean_dec_ref(v___x_368_);
v___x_400_ = lean_array_get_size(v_a_399_);
v___x_401_ = lean_nat_dec_lt(v___x_366_, v___x_400_);
if (v___x_401_ == 0)
{
lean_object* v___x_402_; lean_object* v___x_403_; 
lean_dec(v_a_399_);
v___x_402_ = lean_box(0);
v___x_403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_403_, 0, v___x_402_);
return v___x_403_;
}
else
{
lean_object* v___x_404_; uint8_t v___x_405_; 
v___x_404_ = lean_box(0);
v___x_405_ = lean_nat_dec_le(v___x_400_, v___x_400_);
if (v___x_405_ == 0)
{
if (v___x_401_ == 0)
{
lean_dec(v_a_399_);
goto v___jp_353_;
}
else
{
size_t v___x_406_; size_t v___x_407_; lean_object* v___x_408_; 
v___x_406_ = ((size_t)0ULL);
v___x_407_ = lean_usize_of_nat(v___x_400_);
v___x_408_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_399_, v___x_406_, v___x_407_, v___x_404_, v_a_347_);
lean_dec(v_a_399_);
if (lean_obj_tag(v___x_408_) == 0)
{
lean_dec_ref(v___x_408_);
goto v___jp_353_;
}
else
{
return v___x_408_;
}
}
}
else
{
size_t v___x_409_; size_t v___x_410_; lean_object* v___x_411_; 
v___x_409_ = ((size_t)0ULL);
v___x_410_ = lean_usize_of_nat(v___x_400_);
v___x_411_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_399_, v___x_409_, v___x_410_, v___x_404_, v_a_347_);
lean_dec(v_a_399_);
if (lean_obj_tag(v___x_411_) == 0)
{
lean_dec_ref(v___x_411_);
goto v___jp_353_;
}
else
{
return v___x_411_;
}
}
}
}
}
v___jp_412_:
{
lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_413_ = lean_box(0);
v___x_414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_414_, 0, v___x_413_);
return v___x_414_;
}
v___jp_415_:
{
if (lean_obj_tag(v_rev_x3f_351_) == 1)
{
lean_object* v_val_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_451_; 
v_val_416_ = lean_ctor_get(v_rev_x3f_351_, 0);
v_isSharedCheck_451_ = !lean_is_exclusive(v_rev_x3f_351_);
if (v_isSharedCheck_451_ == 0)
{
v___x_418_ = v_rev_x3f_351_;
v_isShared_419_ = v_isSharedCheck_451_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_val_416_);
lean_dec(v_rev_x3f_351_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_451_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_420_ = l_Lake_Git_defaultRemote;
v___x_421_ = lean_unsigned_to_nat(0u);
v___x_422_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
lean_inc_ref(v_repo_349_);
v___x_423_ = l_Lake_GitRepo_resolveRemoteRevision(v_val_416_, v___x_420_, v_repo_349_, v___x_422_);
if (lean_obj_tag(v___x_423_) == 0)
{
lean_object* v_a_424_; lean_object* v_a_425_; lean_object* v___x_426_; uint8_t v___x_427_; 
lean_del_object(v___x_418_);
v_a_424_ = lean_ctor_get(v___x_423_, 0);
lean_inc(v_a_424_);
v_a_425_ = lean_ctor_get(v___x_423_, 1);
lean_inc(v_a_425_);
lean_dec_ref(v___x_423_);
v___x_426_ = lean_array_get_size(v_a_425_);
v___x_427_ = lean_nat_dec_lt(v___x_421_, v___x_426_);
if (v___x_427_ == 0)
{
lean_dec(v_a_425_);
v_a_357_ = v_a_424_;
goto v___jp_356_;
}
else
{
lean_object* v___x_428_; uint8_t v___x_429_; 
v___x_428_ = lean_box(0);
v___x_429_ = lean_nat_dec_le(v___x_426_, v___x_426_);
if (v___x_429_ == 0)
{
if (v___x_427_ == 0)
{
lean_dec(v_a_425_);
v_a_357_ = v_a_424_;
goto v___jp_356_;
}
else
{
size_t v___x_430_; size_t v___x_431_; lean_object* v___x_432_; 
v___x_430_ = ((size_t)0ULL);
v___x_431_ = lean_usize_of_nat(v___x_426_);
v___x_432_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_425_, v___x_430_, v___x_431_, v___x_428_, v_a_347_);
lean_dec(v_a_425_);
if (lean_obj_tag(v___x_432_) == 0)
{
lean_dec_ref(v___x_432_);
v_a_357_ = v_a_424_;
goto v___jp_356_;
}
else
{
lean_dec(v_a_424_);
lean_dec_ref(v_repo_349_);
lean_dec_ref(v_name_348_);
return v___x_432_;
}
}
}
else
{
size_t v___x_433_; size_t v___x_434_; lean_object* v___x_435_; 
v___x_433_ = ((size_t)0ULL);
v___x_434_ = lean_usize_of_nat(v___x_426_);
v___x_435_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_425_, v___x_433_, v___x_434_, v___x_428_, v_a_347_);
lean_dec(v_a_425_);
if (lean_obj_tag(v___x_435_) == 0)
{
lean_dec_ref(v___x_435_);
v_a_357_ = v_a_424_;
goto v___jp_356_;
}
else
{
lean_dec(v_a_424_);
lean_dec_ref(v_repo_349_);
lean_dec_ref(v_name_348_);
return v___x_435_;
}
}
}
}
else
{
lean_object* v_a_436_; lean_object* v___x_437_; uint8_t v___x_438_; 
lean_dec_ref(v_repo_349_);
lean_dec_ref(v_name_348_);
v_a_436_ = lean_ctor_get(v___x_423_, 1);
lean_inc(v_a_436_);
lean_dec_ref(v___x_423_);
v___x_437_ = lean_array_get_size(v_a_436_);
v___x_438_ = lean_nat_dec_lt(v___x_421_, v___x_437_);
if (v___x_438_ == 0)
{
lean_object* v___x_439_; lean_object* v___x_441_; 
lean_dec(v_a_436_);
v___x_439_ = lean_box(0);
if (v_isShared_419_ == 0)
{
lean_ctor_set(v___x_418_, 0, v___x_439_);
v___x_441_ = v___x_418_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v___x_439_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
}
}
else
{
lean_object* v___x_443_; uint8_t v___x_444_; 
lean_del_object(v___x_418_);
v___x_443_ = lean_box(0);
v___x_444_ = lean_nat_dec_le(v___x_437_, v___x_437_);
if (v___x_444_ == 0)
{
if (v___x_438_ == 0)
{
lean_dec(v_a_436_);
goto v___jp_412_;
}
else
{
size_t v___x_445_; size_t v___x_446_; lean_object* v___x_447_; 
v___x_445_ = ((size_t)0ULL);
v___x_446_ = lean_usize_of_nat(v___x_437_);
v___x_447_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_436_, v___x_445_, v___x_446_, v___x_443_, v_a_347_);
lean_dec(v_a_436_);
if (lean_obj_tag(v___x_447_) == 0)
{
lean_dec_ref(v___x_447_);
goto v___jp_412_;
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
v___x_449_ = lean_usize_of_nat(v___x_437_);
v___x_450_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_436_, v___x_448_, v___x_449_, v___x_443_, v_a_347_);
lean_dec(v_a_436_);
if (lean_obj_tag(v___x_450_) == 0)
{
lean_dec_ref(v___x_450_);
goto v___jp_412_;
}
else
{
return v___x_450_;
}
}
}
}
}
}
else
{
lean_object* v___x_452_; lean_object* v___x_453_; 
lean_dec(v_rev_x3f_351_);
lean_dec_ref(v_repo_349_);
lean_dec_ref(v_name_348_);
v___x_452_ = lean_box(0);
v___x_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_453_, 0, v___x_452_);
return v___x_453_;
}
}
v___jp_454_:
{
if (lean_obj_tag(v___y_455_) == 0)
{
lean_dec_ref(v___y_455_);
goto v___jp_415_;
}
else
{
lean_dec(v_rev_x3f_351_);
lean_dec_ref(v_repo_349_);
lean_dec_ref(v_name_348_);
return v___y_455_;
}
}
v___jp_456_:
{
lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_457_ = lean_box(0);
v___x_458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_458_, 0, v___x_457_);
return v___x_458_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0___boxed(lean_object* v_a_492_, lean_object* v_name_493_, lean_object* v_repo_494_, lean_object* v_url_495_, lean_object* v_rev_x3f_496_, lean_object* v_a_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(v_a_492_, v_name_493_, v_repo_494_, v_url_495_, v_rev_x3f_496_);
lean_dec_ref(v_a_492_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(lean_object* v_a_499_, lean_object* v_name_500_, lean_object* v_repo_501_, lean_object* v_rev_x3f_502_){
_start:
{
uint8_t v_a_505_; lean_object* v___y_518_; lean_object* v___y_519_; uint8_t v_val_520_; lean_object* v___y_535_; lean_object* v_a_536_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_602_ = l_Lake_Git_defaultRemote;
v___x_603_ = lean_unsigned_to_nat(0u);
v___x_604_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
lean_inc_ref(v_repo_501_);
v___x_605_ = l_Lake_GitRepo_findRemoteRevision(v_repo_501_, v_rev_x3f_502_, v___x_602_, v___x_604_);
if (lean_obj_tag(v___x_605_) == 0)
{
lean_object* v_a_606_; lean_object* v_a_607_; lean_object* v___x_635_; uint8_t v___x_636_; 
v_a_606_ = lean_ctor_get(v___x_605_, 0);
lean_inc(v_a_606_);
v_a_607_ = lean_ctor_get(v___x_605_, 1);
lean_inc(v_a_607_);
lean_dec_ref(v___x_605_);
v___x_635_ = lean_array_get_size(v_a_607_);
v___x_636_ = lean_nat_dec_lt(v___x_603_, v___x_635_);
if (v___x_636_ == 0)
{
lean_dec(v_a_607_);
goto v___jp_608_;
}
else
{
lean_object* v___x_637_; uint8_t v___x_638_; 
v___x_637_ = lean_box(0);
v___x_638_ = lean_nat_dec_le(v___x_635_, v___x_635_);
if (v___x_638_ == 0)
{
if (v___x_636_ == 0)
{
lean_dec(v_a_607_);
goto v___jp_608_;
}
else
{
size_t v___x_639_; size_t v___x_640_; lean_object* v___x_641_; 
v___x_639_ = ((size_t)0ULL);
v___x_640_ = lean_usize_of_nat(v___x_635_);
v___x_641_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_607_, v___x_639_, v___x_640_, v___x_637_, v_a_499_);
lean_dec(v_a_607_);
if (lean_obj_tag(v___x_641_) == 0)
{
lean_dec_ref(v___x_641_);
goto v___jp_608_;
}
else
{
lean_dec(v_a_606_);
lean_dec_ref(v_repo_501_);
lean_dec_ref(v_name_500_);
return v___x_641_;
}
}
}
else
{
size_t v___x_642_; size_t v___x_643_; lean_object* v___x_644_; 
v___x_642_ = ((size_t)0ULL);
v___x_643_ = lean_usize_of_nat(v___x_635_);
v___x_644_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_607_, v___x_642_, v___x_643_, v___x_637_, v_a_499_);
lean_dec(v_a_607_);
if (lean_obj_tag(v___x_644_) == 0)
{
lean_dec_ref(v___x_644_);
goto v___jp_608_;
}
else
{
lean_dec(v_a_606_);
lean_dec_ref(v_repo_501_);
lean_dec_ref(v_name_500_);
return v___x_644_;
}
}
}
v___jp_608_:
{
lean_object* v___x_609_; 
lean_inc_ref(v_repo_501_);
v___x_609_ = l_Lake_GitRepo_getHeadRevision(v_repo_501_, v___x_604_);
if (lean_obj_tag(v___x_609_) == 0)
{
lean_object* v_a_610_; lean_object* v_a_611_; lean_object* v___x_612_; uint8_t v___x_613_; 
v_a_610_ = lean_ctor_get(v___x_609_, 0);
lean_inc(v_a_610_);
v_a_611_ = lean_ctor_get(v___x_609_, 1);
lean_inc(v_a_611_);
lean_dec_ref(v___x_609_);
v___x_612_ = lean_array_get_size(v_a_611_);
v___x_613_ = lean_nat_dec_lt(v___x_603_, v___x_612_);
if (v___x_613_ == 0)
{
lean_dec(v_a_611_);
v___y_535_ = v_a_606_;
v_a_536_ = v_a_610_;
goto v___jp_534_;
}
else
{
lean_object* v___x_614_; uint8_t v___x_615_; 
v___x_614_ = lean_box(0);
v___x_615_ = lean_nat_dec_le(v___x_612_, v___x_612_);
if (v___x_615_ == 0)
{
if (v___x_613_ == 0)
{
lean_dec(v_a_611_);
v___y_535_ = v_a_606_;
v_a_536_ = v_a_610_;
goto v___jp_534_;
}
else
{
size_t v___x_616_; size_t v___x_617_; lean_object* v___x_618_; 
v___x_616_ = ((size_t)0ULL);
v___x_617_ = lean_usize_of_nat(v___x_612_);
v___x_618_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_611_, v___x_616_, v___x_617_, v___x_614_, v_a_499_);
lean_dec(v_a_611_);
if (lean_obj_tag(v___x_618_) == 0)
{
lean_dec_ref(v___x_618_);
v___y_535_ = v_a_606_;
v_a_536_ = v_a_610_;
goto v___jp_534_;
}
else
{
lean_dec(v_a_610_);
lean_dec(v_a_606_);
lean_dec_ref(v_repo_501_);
lean_dec_ref(v_name_500_);
return v___x_618_;
}
}
}
else
{
size_t v___x_619_; size_t v___x_620_; lean_object* v___x_621_; 
v___x_619_ = ((size_t)0ULL);
v___x_620_ = lean_usize_of_nat(v___x_612_);
v___x_621_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_611_, v___x_619_, v___x_620_, v___x_614_, v_a_499_);
lean_dec(v_a_611_);
if (lean_obj_tag(v___x_621_) == 0)
{
lean_dec_ref(v___x_621_);
v___y_535_ = v_a_606_;
v_a_536_ = v_a_610_;
goto v___jp_534_;
}
else
{
lean_dec(v_a_610_);
lean_dec(v_a_606_);
lean_dec_ref(v_repo_501_);
lean_dec_ref(v_name_500_);
return v___x_621_;
}
}
}
}
else
{
lean_object* v_a_622_; lean_object* v___x_623_; uint8_t v___x_624_; 
lean_dec(v_a_606_);
lean_dec_ref(v_repo_501_);
lean_dec_ref(v_name_500_);
v_a_622_ = lean_ctor_get(v___x_609_, 1);
lean_inc(v_a_622_);
lean_dec_ref(v___x_609_);
v___x_623_ = lean_array_get_size(v_a_622_);
v___x_624_ = lean_nat_dec_lt(v___x_603_, v___x_623_);
if (v___x_624_ == 0)
{
lean_object* v___x_625_; lean_object* v___x_626_; 
lean_dec(v_a_622_);
v___x_625_ = lean_box(0);
v___x_626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_626_, 0, v___x_625_);
return v___x_626_;
}
else
{
lean_object* v___x_627_; uint8_t v___x_628_; 
v___x_627_ = lean_box(0);
v___x_628_ = lean_nat_dec_le(v___x_623_, v___x_623_);
if (v___x_628_ == 0)
{
if (v___x_624_ == 0)
{
lean_dec(v_a_622_);
goto v___jp_596_;
}
else
{
size_t v___x_629_; size_t v___x_630_; lean_object* v___x_631_; 
v___x_629_ = ((size_t)0ULL);
v___x_630_ = lean_usize_of_nat(v___x_623_);
v___x_631_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_622_, v___x_629_, v___x_630_, v___x_627_, v_a_499_);
lean_dec(v_a_622_);
if (lean_obj_tag(v___x_631_) == 0)
{
lean_dec_ref(v___x_631_);
goto v___jp_596_;
}
else
{
return v___x_631_;
}
}
}
else
{
size_t v___x_632_; size_t v___x_633_; lean_object* v___x_634_; 
v___x_632_ = ((size_t)0ULL);
v___x_633_ = lean_usize_of_nat(v___x_623_);
v___x_634_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_622_, v___x_632_, v___x_633_, v___x_627_, v_a_499_);
lean_dec(v_a_622_);
if (lean_obj_tag(v___x_634_) == 0)
{
lean_dec_ref(v___x_634_);
goto v___jp_596_;
}
else
{
return v___x_634_;
}
}
}
}
}
}
else
{
lean_object* v_a_645_; lean_object* v___x_646_; uint8_t v___x_647_; 
lean_dec_ref(v_repo_501_);
lean_dec_ref(v_name_500_);
v_a_645_ = lean_ctor_get(v___x_605_, 1);
lean_inc(v_a_645_);
lean_dec_ref(v___x_605_);
v___x_646_ = lean_array_get_size(v_a_645_);
v___x_647_ = lean_nat_dec_lt(v___x_603_, v___x_646_);
if (v___x_647_ == 0)
{
lean_object* v___x_648_; lean_object* v___x_649_; 
lean_dec(v_a_645_);
v___x_648_ = lean_box(0);
v___x_649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_649_, 0, v___x_648_);
return v___x_649_;
}
else
{
lean_object* v___x_650_; uint8_t v___x_651_; 
v___x_650_ = lean_box(0);
v___x_651_ = lean_nat_dec_le(v___x_646_, v___x_646_);
if (v___x_651_ == 0)
{
if (v___x_647_ == 0)
{
lean_dec(v_a_645_);
goto v___jp_599_;
}
else
{
size_t v___x_652_; size_t v___x_653_; lean_object* v___x_654_; 
v___x_652_ = ((size_t)0ULL);
v___x_653_ = lean_usize_of_nat(v___x_646_);
v___x_654_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_645_, v___x_652_, v___x_653_, v___x_650_, v_a_499_);
lean_dec(v_a_645_);
if (lean_obj_tag(v___x_654_) == 0)
{
lean_dec_ref(v___x_654_);
goto v___jp_599_;
}
else
{
return v___x_654_;
}
}
}
else
{
size_t v___x_655_; size_t v___x_656_; lean_object* v___x_657_; 
v___x_655_ = ((size_t)0ULL);
v___x_656_ = lean_usize_of_nat(v___x_646_);
v___x_657_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_645_, v___x_655_, v___x_656_, v___x_650_, v_a_499_);
lean_dec(v_a_645_);
if (lean_obj_tag(v___x_657_) == 0)
{
lean_dec_ref(v___x_657_);
goto v___jp_599_;
}
else
{
return v___x_657_;
}
}
}
}
v___jp_504_:
{
if (v_a_505_ == 0)
{
lean_object* v___x_506_; lean_object* v___x_507_; 
lean_dec_ref(v_repo_501_);
lean_dec_ref(v_name_500_);
v___x_506_ = lean_box(0);
v___x_507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_507_, 0, v___x_506_);
return v___x_507_;
}
else
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; uint8_t v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_508_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0));
v___x_509_ = lean_string_append(v_name_500_, v___x_508_);
v___x_510_ = lean_string_append(v___x_509_, v_repo_501_);
lean_dec_ref(v_repo_501_);
v___x_511_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1));
v___x_512_ = lean_string_append(v___x_510_, v___x_511_);
v___x_513_ = 2;
v___x_514_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_514_, 0, v___x_512_);
lean_ctor_set_uint8(v___x_514_, sizeof(void*)*1, v___x_513_);
lean_inc_ref(v_a_499_);
v___x_515_ = lean_apply_2(v_a_499_, v___x_514_, lean_box(0));
v___x_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_516_, 0, v___x_515_);
return v___x_516_;
}
}
v___jp_517_:
{
lean_object* v___x_521_; uint8_t v___x_522_; 
v___x_521_ = lean_array_get_size(v___y_518_);
v___x_522_ = lean_nat_dec_lt(v___y_519_, v___x_521_);
if (v___x_522_ == 0)
{
lean_dec_ref(v___y_518_);
v_a_505_ = v_val_520_;
goto v___jp_504_;
}
else
{
lean_object* v___x_523_; uint8_t v___x_524_; 
v___x_523_ = lean_box(0);
v___x_524_ = lean_nat_dec_le(v___x_521_, v___x_521_);
if (v___x_524_ == 0)
{
if (v___x_522_ == 0)
{
lean_dec_ref(v___y_518_);
v_a_505_ = v_val_520_;
goto v___jp_504_;
}
else
{
size_t v___x_525_; size_t v___x_526_; lean_object* v___x_527_; 
v___x_525_ = ((size_t)0ULL);
v___x_526_ = lean_usize_of_nat(v___x_521_);
v___x_527_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_518_, v___x_525_, v___x_526_, v___x_523_, v_a_499_);
lean_dec_ref(v___y_518_);
if (lean_obj_tag(v___x_527_) == 0)
{
lean_dec_ref(v___x_527_);
v_a_505_ = v_val_520_;
goto v___jp_504_;
}
else
{
lean_dec_ref(v_repo_501_);
lean_dec_ref(v_name_500_);
return v___x_527_;
}
}
}
else
{
size_t v___x_528_; size_t v___x_529_; lean_object* v___x_530_; 
v___x_528_ = ((size_t)0ULL);
v___x_529_ = lean_usize_of_nat(v___x_521_);
v___x_530_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_518_, v___x_528_, v___x_529_, v___x_523_, v_a_499_);
lean_dec_ref(v___y_518_);
if (lean_obj_tag(v___x_530_) == 0)
{
lean_dec_ref(v___x_530_);
v_a_505_ = v_val_520_;
goto v___jp_504_;
}
else
{
lean_dec_ref(v_repo_501_);
lean_dec_ref(v_name_500_);
return v___x_530_;
}
}
}
}
v___jp_531_:
{
lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_532_ = lean_box(0);
v___x_533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_533_, 0, v___x_532_);
return v___x_533_;
}
v___jp_534_:
{
uint8_t v___x_537_; 
v___x_537_ = lean_string_dec_eq(v_a_536_, v___y_535_);
lean_dec_ref(v_a_536_);
if (v___x_537_ == 0)
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; uint8_t v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_538_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_539_ = lean_string_append(v_name_500_, v___x_538_);
v___x_540_ = lean_string_append(v___x_539_, v___y_535_);
v___x_541_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3));
v___x_542_ = lean_string_append(v___x_540_, v___x_541_);
v___x_543_ = 1;
v___x_544_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_544_, 0, v___x_542_);
lean_ctor_set_uint8(v___x_544_, sizeof(void*)*1, v___x_543_);
lean_inc_ref(v_a_499_);
v___x_545_ = lean_apply_2(v_a_499_, v___x_544_, lean_box(0));
v___x_546_ = lean_unsigned_to_nat(0u);
v___x_547_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
v___x_548_ = l_Lake_GitRepo_checkoutDetach(v___y_535_, v_repo_501_, v___x_547_);
if (lean_obj_tag(v___x_548_) == 0)
{
lean_object* v_a_549_; lean_object* v_a_550_; lean_object* v___x_551_; uint8_t v___x_552_; 
v_a_549_ = lean_ctor_get(v___x_548_, 0);
lean_inc(v_a_549_);
v_a_550_ = lean_ctor_get(v___x_548_, 1);
lean_inc(v_a_550_);
lean_dec_ref(v___x_548_);
v___x_551_ = lean_array_get_size(v_a_550_);
v___x_552_ = lean_nat_dec_lt(v___x_546_, v___x_551_);
if (v___x_552_ == 0)
{
lean_object* v___x_553_; 
lean_dec(v_a_550_);
v___x_553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_553_, 0, v_a_549_);
return v___x_553_;
}
else
{
lean_object* v___x_554_; uint8_t v___x_555_; 
v___x_554_ = lean_box(0);
v___x_555_ = lean_nat_dec_le(v___x_551_, v___x_551_);
if (v___x_555_ == 0)
{
if (v___x_552_ == 0)
{
lean_object* v___x_556_; 
lean_dec(v_a_550_);
v___x_556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_556_, 0, v_a_549_);
return v___x_556_;
}
else
{
size_t v___x_557_; size_t v___x_558_; lean_object* v___x_559_; 
v___x_557_ = ((size_t)0ULL);
v___x_558_ = lean_usize_of_nat(v___x_551_);
v___x_559_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_550_, v___x_557_, v___x_558_, v___x_554_, v_a_499_);
lean_dec(v_a_550_);
if (lean_obj_tag(v___x_559_) == 0)
{
lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_566_; 
v_isSharedCheck_566_ = !lean_is_exclusive(v___x_559_);
if (v_isSharedCheck_566_ == 0)
{
lean_object* v_unused_567_; 
v_unused_567_ = lean_ctor_get(v___x_559_, 0);
lean_dec(v_unused_567_);
v___x_561_ = v___x_559_;
v_isShared_562_ = v_isSharedCheck_566_;
goto v_resetjp_560_;
}
else
{
lean_dec(v___x_559_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_566_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___x_564_; 
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 0, v_a_549_);
v___x_564_ = v___x_561_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v_a_549_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
return v___x_564_;
}
}
}
else
{
lean_dec(v_a_549_);
return v___x_559_;
}
}
}
else
{
size_t v___x_568_; size_t v___x_569_; lean_object* v___x_570_; 
v___x_568_ = ((size_t)0ULL);
v___x_569_ = lean_usize_of_nat(v___x_551_);
v___x_570_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_550_, v___x_568_, v___x_569_, v___x_554_, v_a_499_);
lean_dec(v_a_550_);
if (lean_obj_tag(v___x_570_) == 0)
{
lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_577_; 
v_isSharedCheck_577_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_577_ == 0)
{
lean_object* v_unused_578_; 
v_unused_578_ = lean_ctor_get(v___x_570_, 0);
lean_dec(v_unused_578_);
v___x_572_ = v___x_570_;
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
else
{
lean_dec(v___x_570_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_575_; 
if (v_isShared_573_ == 0)
{
lean_ctor_set(v___x_572_, 0, v_a_549_);
v___x_575_ = v___x_572_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v_a_549_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
}
else
{
lean_dec(v_a_549_);
return v___x_570_;
}
}
}
}
else
{
lean_object* v_a_579_; lean_object* v___x_580_; uint8_t v___x_581_; 
v_a_579_ = lean_ctor_get(v___x_548_, 1);
lean_inc(v_a_579_);
lean_dec_ref(v___x_548_);
v___x_580_ = lean_array_get_size(v_a_579_);
v___x_581_ = lean_nat_dec_lt(v___x_546_, v___x_580_);
if (v___x_581_ == 0)
{
lean_object* v___x_582_; lean_object* v___x_583_; 
lean_dec(v_a_579_);
v___x_582_ = lean_box(0);
v___x_583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_583_, 0, v___x_582_);
return v___x_583_;
}
else
{
lean_object* v___x_584_; uint8_t v___x_585_; 
v___x_584_ = lean_box(0);
v___x_585_ = lean_nat_dec_le(v___x_580_, v___x_580_);
if (v___x_585_ == 0)
{
if (v___x_581_ == 0)
{
lean_dec(v_a_579_);
goto v___jp_531_;
}
else
{
size_t v___x_586_; size_t v___x_587_; lean_object* v___x_588_; 
v___x_586_ = ((size_t)0ULL);
v___x_587_ = lean_usize_of_nat(v___x_580_);
v___x_588_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_579_, v___x_586_, v___x_587_, v___x_584_, v_a_499_);
lean_dec(v_a_579_);
if (lean_obj_tag(v___x_588_) == 0)
{
lean_dec_ref(v___x_588_);
goto v___jp_531_;
}
else
{
return v___x_588_;
}
}
}
else
{
size_t v___x_589_; size_t v___x_590_; lean_object* v___x_591_; 
v___x_589_ = ((size_t)0ULL);
v___x_590_ = lean_usize_of_nat(v___x_580_);
v___x_591_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_579_, v___x_589_, v___x_590_, v___x_584_, v_a_499_);
lean_dec(v_a_579_);
if (lean_obj_tag(v___x_591_) == 0)
{
lean_dec_ref(v___x_591_);
goto v___jp_531_;
}
else
{
return v___x_591_;
}
}
}
}
}
else
{
uint8_t v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
lean_dec_ref(v___y_535_);
lean_inc_ref(v_repo_501_);
v___x_592_ = l_Lake_GitRepo_hasNoDiff(v_repo_501_);
v___x_593_ = lean_unsigned_to_nat(0u);
v___x_594_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
if (v___x_592_ == 0)
{
v___y_518_ = v___x_594_;
v___y_519_ = v___x_593_;
v_val_520_ = v___x_537_;
goto v___jp_517_;
}
else
{
uint8_t v___x_595_; 
v___x_595_ = 0;
v___y_518_ = v___x_594_;
v___y_519_ = v___x_593_;
v_val_520_ = v___x_595_;
goto v___jp_517_;
}
}
}
v___jp_596_:
{
lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_597_ = lean_box(0);
v___x_598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_598_, 0, v___x_597_);
return v___x_598_;
}
v___jp_599_:
{
lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_600_ = lean_box(0);
v___x_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
return v___x_601_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1___boxed(lean_object* v_a_658_, lean_object* v_name_659_, lean_object* v_repo_660_, lean_object* v_rev_x3f_661_, lean_object* v_a_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(v_a_658_, v_name_659_, v_repo_660_, v_rev_x3f_661_);
lean_dec_ref(v_a_658_);
return v_res_663_;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4(void){
_start:
{
lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_668_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
v___x_669_ = lean_array_get_size(v___x_668_);
return v___x_669_;
}
}
static uint8_t _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5(void){
_start:
{
lean_object* v___x_670_; lean_object* v___x_671_; uint8_t v___x_672_; 
v___x_670_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4);
v___x_671_ = lean_unsigned_to_nat(0u);
v___x_672_ = lean_nat_dec_lt(v___x_671_, v___x_670_);
return v___x_672_;
}
}
static uint8_t _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6(void){
_start:
{
lean_object* v___x_673_; uint8_t v___x_674_; 
v___x_673_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4);
v___x_674_ = lean_nat_dec_le(v___x_673_, v___x_673_);
return v___x_674_;
}
}
static size_t _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7(void){
_start:
{
lean_object* v___x_675_; size_t v___x_676_; 
v___x_675_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4);
v___x_676_ = lean_usize_of_nat(v___x_675_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo(lean_object* v_name_677_, lean_object* v_repo_678_, lean_object* v_url_679_, lean_object* v_rev_x3f_680_, lean_object* v_a_681_){
_start:
{
uint8_t v_a_684_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; uint8_t v_val_723_; 
v___x_719_ = l_Lake_Git_defaultRemote;
lean_inc_ref(v_repo_678_);
v___x_720_ = l_Lake_GitRepo_getRemoteUrl_x3f(v___x_719_, v_repo_678_);
v___x_721_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
if (lean_obj_tag(v___x_720_) == 1)
{
lean_object* v_val_733_; uint8_t v___x_734_; 
v_val_733_ = lean_ctor_get(v___x_720_, 0);
lean_inc(v_val_733_);
lean_dec_ref(v___x_720_);
v___x_734_ = lean_string_dec_eq(v_val_733_, v_url_679_);
if (v___x_734_ == 0)
{
lean_object* v___x_735_; 
v___x_735_ = lean_io_realpath(v_val_733_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_object* v_a_736_; lean_object* v___x_737_; 
v_a_736_ = lean_ctor_get(v___x_735_, 0);
lean_inc(v_a_736_);
lean_dec_ref(v___x_735_);
lean_inc_ref(v_url_679_);
v___x_737_ = lean_io_realpath(v_url_679_);
if (lean_obj_tag(v___x_737_) == 0)
{
lean_object* v_a_738_; uint8_t v___x_739_; 
v_a_738_ = lean_ctor_get(v___x_737_, 0);
lean_inc(v_a_738_);
lean_dec_ref(v___x_737_);
v___x_739_ = lean_string_dec_eq(v_a_736_, v_a_738_);
lean_dec(v_a_738_);
lean_dec(v_a_736_);
v_val_723_ = v___x_739_;
goto v___jp_722_;
}
else
{
lean_dec_ref(v___x_737_);
lean_dec(v_a_736_);
v_val_723_ = v___x_734_;
goto v___jp_722_;
}
}
else
{
lean_dec_ref(v___x_735_);
v_val_723_ = v___x_734_;
goto v___jp_722_;
}
}
else
{
lean_dec(v_val_733_);
v_val_723_ = v___x_734_;
goto v___jp_722_;
}
}
else
{
uint8_t v___x_740_; 
lean_dec(v___x_720_);
v___x_740_ = 0;
v_val_723_ = v___x_740_;
goto v___jp_722_;
}
v___jp_683_:
{
if (v_a_684_ == 0)
{
uint8_t v___x_685_; 
v___x_685_ = l_System_Platform_isWindows;
if (v___x_685_ == 0)
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; uint8_t v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_686_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__0));
lean_inc_ref(v_name_677_);
v___x_687_ = lean_string_append(v_name_677_, v___x_686_);
v___x_688_ = lean_string_append(v___x_687_, v_repo_678_);
v___x_689_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__1));
v___x_690_ = lean_string_append(v___x_688_, v___x_689_);
v___x_691_ = 1;
v___x_692_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_692_, 0, v___x_690_);
lean_ctor_set_uint8(v___x_692_, sizeof(void*)*1, v___x_691_);
lean_inc_ref(v_a_681_);
v___x_693_ = lean_apply_2(v_a_681_, v___x_692_, lean_box(0));
v___x_694_ = l_IO_FS_removeDirAll(v_repo_678_);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_object* v___x_695_; 
lean_dec_ref(v___x_694_);
v___x_695_ = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(v_a_681_, v_name_677_, v_repo_678_, v_url_679_, v_rev_x3f_680_);
return v___x_695_;
}
else
{
lean_object* v_a_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_708_; 
lean_dec(v_rev_x3f_680_);
lean_dec_ref(v_url_679_);
lean_dec_ref(v_repo_678_);
lean_dec_ref(v_name_677_);
v_a_696_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_708_ == 0)
{
v___x_698_ = v___x_694_;
v_isShared_699_ = v_isSharedCheck_708_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_a_696_);
lean_dec(v___x_694_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_708_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_700_; uint8_t v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_706_; 
v___x_700_ = lean_io_error_to_string(v_a_696_);
v___x_701_ = 3;
v___x_702_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_702_, 0, v___x_700_);
lean_ctor_set_uint8(v___x_702_, sizeof(void*)*1, v___x_701_);
lean_inc_ref(v_a_681_);
v___x_703_ = lean_apply_2(v_a_681_, v___x_702_, lean_box(0));
v___x_704_ = lean_box(0);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 0, v___x_704_);
v___x_706_ = v___x_698_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v___x_704_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
}
else
{
lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; uint8_t v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
lean_dec_ref(v_url_679_);
v___x_709_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__2));
lean_inc_ref(v_name_677_);
v___x_710_ = lean_string_append(v_name_677_, v___x_709_);
v___x_711_ = lean_string_append(v___x_710_, v_repo_678_);
v___x_712_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__3));
v___x_713_ = lean_string_append(v___x_711_, v___x_712_);
v___x_714_ = 1;
v___x_715_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_715_, 0, v___x_713_);
lean_ctor_set_uint8(v___x_715_, sizeof(void*)*1, v___x_714_);
lean_inc_ref(v_a_681_);
v___x_716_ = lean_apply_2(v_a_681_, v___x_715_, lean_box(0));
v___x_717_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(v_a_681_, v_name_677_, v_repo_678_, v_rev_x3f_680_);
return v___x_717_;
}
}
else
{
lean_object* v___x_718_; 
lean_dec_ref(v_url_679_);
v___x_718_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(v_a_681_, v_name_677_, v_repo_678_, v_rev_x3f_680_);
return v___x_718_;
}
}
v___jp_722_:
{
uint8_t v___x_724_; 
v___x_724_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_724_ == 0)
{
v_a_684_ = v_val_723_;
goto v___jp_683_;
}
else
{
lean_object* v___x_725_; uint8_t v___x_726_; 
v___x_725_ = lean_box(0);
v___x_726_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_726_ == 0)
{
if (v___x_724_ == 0)
{
v_a_684_ = v_val_723_;
goto v___jp_683_;
}
else
{
size_t v___x_727_; size_t v___x_728_; lean_object* v___x_729_; 
v___x_727_ = ((size_t)0ULL);
v___x_728_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_729_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_721_, v___x_727_, v___x_728_, v___x_725_, v_a_681_);
if (lean_obj_tag(v___x_729_) == 0)
{
lean_dec_ref(v___x_729_);
v_a_684_ = v_val_723_;
goto v___jp_683_;
}
else
{
lean_dec(v_rev_x3f_680_);
lean_dec_ref(v_url_679_);
lean_dec_ref(v_repo_678_);
lean_dec_ref(v_name_677_);
return v___x_729_;
}
}
}
else
{
size_t v___x_730_; size_t v___x_731_; lean_object* v___x_732_; 
v___x_730_ = ((size_t)0ULL);
v___x_731_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_732_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_721_, v___x_730_, v___x_731_, v___x_725_, v_a_681_);
if (lean_obj_tag(v___x_732_) == 0)
{
lean_dec_ref(v___x_732_);
v_a_684_ = v_val_723_;
goto v___jp_683_;
}
else
{
lean_dec(v_rev_x3f_680_);
lean_dec_ref(v_url_679_);
lean_dec_ref(v_repo_678_);
lean_dec_ref(v_name_677_);
return v___x_732_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___boxed(lean_object* v_name_741_, lean_object* v_repo_742_, lean_object* v_url_743_, lean_object* v_rev_x3f_744_, lean_object* v_a_745_, lean_object* v_a_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo(v_name_741_, v_repo_742_, v_url_743_, v_rev_x3f_744_, v_a_745_);
lean_dec_ref(v_a_745_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(lean_object* v_a_748_, lean_object* v_name_749_, lean_object* v_repo_750_, lean_object* v_url_751_, lean_object* v_rev_x3f_752_){
_start:
{
uint8_t v_a_755_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; uint8_t v_val_794_; 
v___x_790_ = l_Lake_Git_defaultRemote;
lean_inc_ref(v_repo_750_);
v___x_791_ = l_Lake_GitRepo_getRemoteUrl_x3f(v___x_790_, v_repo_750_);
v___x_792_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
if (lean_obj_tag(v___x_791_) == 1)
{
lean_object* v_val_804_; uint8_t v___x_805_; 
v_val_804_ = lean_ctor_get(v___x_791_, 0);
lean_inc(v_val_804_);
lean_dec_ref(v___x_791_);
v___x_805_ = lean_string_dec_eq(v_val_804_, v_url_751_);
if (v___x_805_ == 0)
{
lean_object* v___x_806_; 
v___x_806_ = lean_io_realpath(v_val_804_);
if (lean_obj_tag(v___x_806_) == 0)
{
lean_object* v_a_807_; lean_object* v___x_808_; 
v_a_807_ = lean_ctor_get(v___x_806_, 0);
lean_inc(v_a_807_);
lean_dec_ref(v___x_806_);
lean_inc_ref(v_url_751_);
v___x_808_ = lean_io_realpath(v_url_751_);
if (lean_obj_tag(v___x_808_) == 0)
{
lean_object* v_a_809_; uint8_t v___x_810_; 
v_a_809_ = lean_ctor_get(v___x_808_, 0);
lean_inc(v_a_809_);
lean_dec_ref(v___x_808_);
v___x_810_ = lean_string_dec_eq(v_a_807_, v_a_809_);
lean_dec(v_a_809_);
lean_dec(v_a_807_);
v_val_794_ = v___x_810_;
goto v___jp_793_;
}
else
{
lean_dec_ref(v___x_808_);
lean_dec(v_a_807_);
v_val_794_ = v___x_805_;
goto v___jp_793_;
}
}
else
{
lean_dec_ref(v___x_806_);
v_val_794_ = v___x_805_;
goto v___jp_793_;
}
}
else
{
lean_dec(v_val_804_);
v_val_794_ = v___x_805_;
goto v___jp_793_;
}
}
else
{
uint8_t v___x_811_; 
lean_dec(v___x_791_);
v___x_811_ = 0;
v_val_794_ = v___x_811_;
goto v___jp_793_;
}
v___jp_754_:
{
if (v_a_755_ == 0)
{
uint8_t v___x_756_; 
v___x_756_ = l_System_Platform_isWindows;
if (v___x_756_ == 0)
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; uint8_t v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_757_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__0));
lean_inc_ref(v_name_749_);
v___x_758_ = lean_string_append(v_name_749_, v___x_757_);
v___x_759_ = lean_string_append(v___x_758_, v_repo_750_);
v___x_760_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__1));
v___x_761_ = lean_string_append(v___x_759_, v___x_760_);
v___x_762_ = 1;
v___x_763_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_763_, 0, v___x_761_);
lean_ctor_set_uint8(v___x_763_, sizeof(void*)*1, v___x_762_);
lean_inc_ref(v_a_748_);
v___x_764_ = lean_apply_2(v_a_748_, v___x_763_, lean_box(0));
v___x_765_ = l_IO_FS_removeDirAll(v_repo_750_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_object* v___x_766_; 
lean_dec_ref(v___x_765_);
v___x_766_ = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(v_a_748_, v_name_749_, v_repo_750_, v_url_751_, v_rev_x3f_752_);
return v___x_766_;
}
else
{
lean_object* v_a_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_779_; 
lean_dec(v_rev_x3f_752_);
lean_dec_ref(v_url_751_);
lean_dec_ref(v_repo_750_);
lean_dec_ref(v_name_749_);
v_a_767_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_779_ == 0)
{
v___x_769_ = v___x_765_;
v_isShared_770_ = v_isSharedCheck_779_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_a_767_);
lean_dec(v___x_765_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_779_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_771_; uint8_t v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_777_; 
v___x_771_ = lean_io_error_to_string(v_a_767_);
v___x_772_ = 3;
v___x_773_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_773_, 0, v___x_771_);
lean_ctor_set_uint8(v___x_773_, sizeof(void*)*1, v___x_772_);
lean_inc_ref(v_a_748_);
v___x_774_ = lean_apply_2(v_a_748_, v___x_773_, lean_box(0));
v___x_775_ = lean_box(0);
if (v_isShared_770_ == 0)
{
lean_ctor_set(v___x_769_, 0, v___x_775_);
v___x_777_ = v___x_769_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v___x_775_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
}
}
else
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; uint8_t v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
lean_dec_ref(v_url_751_);
v___x_780_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__2));
lean_inc_ref(v_name_749_);
v___x_781_ = lean_string_append(v_name_749_, v___x_780_);
v___x_782_ = lean_string_append(v___x_781_, v_repo_750_);
v___x_783_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__3));
v___x_784_ = lean_string_append(v___x_782_, v___x_783_);
v___x_785_ = 1;
v___x_786_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_786_, 0, v___x_784_);
lean_ctor_set_uint8(v___x_786_, sizeof(void*)*1, v___x_785_);
lean_inc_ref(v_a_748_);
v___x_787_ = lean_apply_2(v_a_748_, v___x_786_, lean_box(0));
v___x_788_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(v_a_748_, v_name_749_, v_repo_750_, v_rev_x3f_752_);
return v___x_788_;
}
}
else
{
lean_object* v___x_789_; 
lean_dec_ref(v_url_751_);
v___x_789_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(v_a_748_, v_name_749_, v_repo_750_, v_rev_x3f_752_);
return v___x_789_;
}
}
v___jp_793_:
{
uint8_t v___x_795_; 
v___x_795_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_795_ == 0)
{
v_a_755_ = v_val_794_;
goto v___jp_754_;
}
else
{
lean_object* v___x_796_; uint8_t v___x_797_; 
v___x_796_ = lean_box(0);
v___x_797_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_797_ == 0)
{
if (v___x_795_ == 0)
{
v_a_755_ = v_val_794_;
goto v___jp_754_;
}
else
{
size_t v___x_798_; size_t v___x_799_; lean_object* v___x_800_; 
v___x_798_ = ((size_t)0ULL);
v___x_799_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_800_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_792_, v___x_798_, v___x_799_, v___x_796_, v_a_748_);
if (lean_obj_tag(v___x_800_) == 0)
{
lean_dec_ref(v___x_800_);
v_a_755_ = v_val_794_;
goto v___jp_754_;
}
else
{
lean_dec(v_rev_x3f_752_);
lean_dec_ref(v_url_751_);
lean_dec_ref(v_repo_750_);
lean_dec_ref(v_name_749_);
return v___x_800_;
}
}
}
else
{
size_t v___x_801_; size_t v___x_802_; lean_object* v___x_803_; 
v___x_801_ = ((size_t)0ULL);
v___x_802_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_803_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_792_, v___x_801_, v___x_802_, v___x_796_, v_a_748_);
if (lean_obj_tag(v___x_803_) == 0)
{
lean_dec_ref(v___x_803_);
v_a_755_ = v_val_794_;
goto v___jp_754_;
}
else
{
lean_dec(v_rev_x3f_752_);
lean_dec_ref(v_url_751_);
lean_dec_ref(v_repo_750_);
lean_dec_ref(v_name_749_);
return v___x_803_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0___boxed(lean_object* v_a_812_, lean_object* v_name_813_, lean_object* v_repo_814_, lean_object* v_url_815_, lean_object* v_rev_x3f_816_, lean_object* v_a_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_812_, v_name_813_, v_repo_814_, v_url_815_, v_rev_x3f_816_);
lean_dec_ref(v_a_812_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo(lean_object* v_name_819_, lean_object* v_repo_820_, lean_object* v_url_821_, lean_object* v_rev_x3f_822_, lean_object* v_a_823_){
_start:
{
uint8_t v___x_825_; lean_object* v___x_829_; uint8_t v___x_830_; 
v___x_825_ = l_System_FilePath_isDir(v_repo_820_);
v___x_829_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
v___x_830_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_830_ == 0)
{
goto v___jp_826_;
}
else
{
lean_object* v___x_831_; uint8_t v___x_832_; 
v___x_831_ = lean_box(0);
v___x_832_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_832_ == 0)
{
if (v___x_830_ == 0)
{
goto v___jp_826_;
}
else
{
size_t v___x_833_; size_t v___x_834_; lean_object* v___x_835_; 
v___x_833_ = ((size_t)0ULL);
v___x_834_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_835_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_829_, v___x_833_, v___x_834_, v___x_831_, v_a_823_);
if (lean_obj_tag(v___x_835_) == 0)
{
lean_dec_ref(v___x_835_);
goto v___jp_826_;
}
else
{
lean_dec(v_rev_x3f_822_);
lean_dec_ref(v_url_821_);
lean_dec_ref(v_repo_820_);
lean_dec_ref(v_name_819_);
return v___x_835_;
}
}
}
else
{
size_t v___x_836_; size_t v___x_837_; lean_object* v___x_838_; 
v___x_836_ = ((size_t)0ULL);
v___x_837_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_838_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_829_, v___x_836_, v___x_837_, v___x_831_, v_a_823_);
if (lean_obj_tag(v___x_838_) == 0)
{
lean_dec_ref(v___x_838_);
goto v___jp_826_;
}
else
{
lean_dec(v_rev_x3f_822_);
lean_dec_ref(v_url_821_);
lean_dec_ref(v_repo_820_);
lean_dec_ref(v_name_819_);
return v___x_838_;
}
}
}
v___jp_826_:
{
if (v___x_825_ == 0)
{
lean_object* v___x_827_; 
v___x_827_ = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(v_a_823_, v_name_819_, v_repo_820_, v_url_821_, v_rev_x3f_822_);
return v___x_827_;
}
else
{
lean_object* v___x_828_; 
v___x_828_ = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_823_, v_name_819_, v_repo_820_, v_url_821_, v_rev_x3f_822_);
return v___x_828_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___boxed(lean_object* v_name_839_, lean_object* v_repo_840_, lean_object* v_url_841_, lean_object* v_rev_x3f_842_, lean_object* v_a_843_, lean_object* v_a_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo(v_name_839_, v_repo_840_, v_url_841_, v_rev_x3f_842_, v_a_843_);
lean_dec_ref(v_a_843_);
return v_res_845_;
}
}
static lean_object* _init_l_Lake_instInhabitedMaterializedDep_default___closed__4(void){
_start:
{
lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_852_ = l_Lake_instInhabitedPackageEntry_default;
v___x_853_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__3));
v___x_854_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___x_855_ = l_System_instInhabitedFilePath_default;
v___x_856_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_856_, 0, v___x_855_);
lean_ctor_set(v___x_856_, 1, v___x_854_);
lean_ctor_set(v___x_856_, 2, v___x_853_);
lean_ctor_set(v___x_856_, 3, v___x_852_);
return v___x_856_;
}
}
static lean_object* _init_l_Lake_instInhabitedMaterializedDep_default(void){
_start:
{
lean_object* v___x_857_; 
v___x_857_ = lean_obj_once(&l_Lake_instInhabitedMaterializedDep_default___closed__4, &l_Lake_instInhabitedMaterializedDep_default___closed__4_once, _init_l_Lake_instInhabitedMaterializedDep_default___closed__4);
return v___x_857_;
}
}
static lean_object* _init_l_Lake_instInhabitedMaterializedDep(void){
_start:
{
lean_object* v___x_858_; 
v___x_858_ = l_Lake_instInhabitedMaterializedDep_default;
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_name(lean_object* v_self_859_){
_start:
{
lean_object* v_manifestEntry_860_; lean_object* v_name_861_; 
v_manifestEntry_860_ = lean_ctor_get(v_self_859_, 3);
v_name_861_ = lean_ctor_get(v_manifestEntry_860_, 0);
lean_inc(v_name_861_);
return v_name_861_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_name___boxed(lean_object* v_self_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l_Lake_MaterializedDep_name(v_self_862_);
lean_dec_ref(v_self_862_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_scope(lean_object* v_self_864_){
_start:
{
lean_object* v_manifestEntry_865_; lean_object* v_scope_866_; 
v_manifestEntry_865_ = lean_ctor_get(v_self_864_, 3);
v_scope_866_ = lean_ctor_get(v_manifestEntry_865_, 1);
lean_inc_ref(v_scope_866_);
return v_scope_866_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_scope___boxed(lean_object* v_self_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l_Lake_MaterializedDep_scope(v_self_867_);
lean_dec_ref(v_self_867_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_manifestFile_x3f(lean_object* v_self_869_){
_start:
{
lean_object* v_manifestEntry_870_; lean_object* v_manifestFile_x3f_871_; 
v_manifestEntry_870_ = lean_ctor_get(v_self_869_, 3);
v_manifestFile_x3f_871_ = lean_ctor_get(v_manifestEntry_870_, 3);
lean_inc(v_manifestFile_x3f_871_);
return v_manifestFile_x3f_871_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_manifestFile_x3f___boxed(lean_object* v_self_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l_Lake_MaterializedDep_manifestFile_x3f(v_self_872_);
lean_dec_ref(v_self_872_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_configFile(lean_object* v_self_874_){
_start:
{
lean_object* v_manifestEntry_875_; lean_object* v_configFile_876_; 
v_manifestEntry_875_ = lean_ctor_get(v_self_874_, 3);
v_configFile_876_ = lean_ctor_get(v_manifestEntry_875_, 2);
lean_inc_ref(v_configFile_876_);
return v_configFile_876_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_configFile___boxed(lean_object* v_self_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l_Lake_MaterializedDep_configFile(v_self_877_);
lean_dec_ref(v_self_877_);
return v_res_878_;
}
}
LEAN_EXPORT uint8_t l_Lake_MaterializedDep_fixedToolchain(lean_object* v_self_879_){
_start:
{
lean_object* v_manifest_x3f_880_; 
v_manifest_x3f_880_ = lean_ctor_get(v_self_879_, 2);
if (lean_obj_tag(v_manifest_x3f_880_) == 1)
{
lean_object* v_a_881_; uint8_t v_fixedToolchain_882_; 
v_a_881_ = lean_ctor_get(v_manifest_x3f_880_, 0);
v_fixedToolchain_882_ = lean_ctor_get_uint8(v_a_881_, sizeof(void*)*4);
return v_fixedToolchain_882_;
}
else
{
uint8_t v___x_883_; 
v___x_883_ = 0;
return v___x_883_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_fixedToolchain___boxed(lean_object* v_self_884_){
_start:
{
uint8_t v_res_885_; lean_object* v_r_886_; 
v_res_885_ = l_Lake_MaterializedDep_fixedToolchain(v_self_884_);
lean_dec_ref(v_self_884_);
v_r_886_ = lean_box(v_res_885_);
return v_r_886_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorIdx(lean_object* v_x_887_){
_start:
{
switch(lean_obj_tag(v_x_887_))
{
case 0:
{
lean_object* v___x_888_; 
v___x_888_ = lean_unsigned_to_nat(0u);
return v___x_888_;
}
case 1:
{
lean_object* v___x_889_; 
v___x_889_ = lean_unsigned_to_nat(1u);
return v___x_889_;
}
default: 
{
lean_object* v___x_890_; 
v___x_890_ = lean_unsigned_to_nat(2u);
return v___x_890_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorIdx___boxed(lean_object* v_x_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorIdx(v_x_891_);
lean_dec(v_x_891_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(lean_object* v_t_893_, lean_object* v_k_894_){
_start:
{
if (lean_obj_tag(v_t_893_) == 0)
{
return v_k_894_;
}
else
{
lean_object* v_rev_895_; lean_object* v___x_896_; 
v_rev_895_ = lean_ctor_get(v_t_893_, 0);
lean_inc_ref(v_rev_895_);
lean_dec(v_t_893_);
v___x_896_ = lean_apply_1(v_k_894_, v_rev_895_);
return v___x_896_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim(lean_object* v_motive_897_, lean_object* v_ctorIdx_898_, lean_object* v_t_899_, lean_object* v_h_900_, lean_object* v_k_901_){
_start:
{
lean_object* v___x_902_; 
v___x_902_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(v_t_899_, v_k_901_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___boxed(lean_object* v_motive_903_, lean_object* v_ctorIdx_904_, lean_object* v_t_905_, lean_object* v_h_906_, lean_object* v_k_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim(v_motive_903_, v_ctorIdx_904_, v_t_905_, v_h_906_, v_k_907_);
lean_dec(v_ctorIdx_904_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_none_elim___redArg(lean_object* v_t_909_, lean_object* v_none_910_){
_start:
{
lean_object* v___x_911_; 
v___x_911_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(v_t_909_, v_none_910_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_none_elim(lean_object* v_motive_912_, lean_object* v_t_913_, lean_object* v_h_914_, lean_object* v_none_915_){
_start:
{
lean_object* v___x_916_; 
v___x_916_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(v_t_913_, v_none_915_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_git_elim___redArg(lean_object* v_t_917_, lean_object* v_git_918_){
_start:
{
lean_object* v___x_919_; 
v___x_919_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(v_t_917_, v_git_918_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_git_elim(lean_object* v_motive_920_, lean_object* v_t_921_, lean_object* v_h_922_, lean_object* v_git_923_){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(v_t_921_, v_git_923_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ver_elim___redArg(lean_object* v_t_925_, lean_object* v_ver_926_){
_start:
{
lean_object* v___x_927_; 
v___x_927_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(v_t_925_, v_ver_926_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ver_elim(lean_object* v_motive_928_, lean_object* v_t_929_, lean_object* v_h_930_, lean_object* v_ver_931_){
_start:
{
lean_object* v___x_932_; 
v___x_932_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(v_t_929_, v_ver_931_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed(lean_object* v_scope_941_, lean_object* v_name_942_, lean_object* v_ver_943_){
_start:
{
lean_object* v_fst_945_; lean_object* v_snd_946_; 
switch(lean_obj_tag(v_ver_943_))
{
case 0:
{
lean_object* v___x_967_; 
v___x_967_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v_fst_945_ = v___x_967_;
v_snd_946_ = v___x_967_;
goto v___jp_944_;
}
case 1:
{
lean_object* v_rev_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_983_; 
v_rev_968_ = lean_ctor_get(v_ver_943_, 0);
v_isSharedCheck_983_ = !lean_is_exclusive(v_ver_943_);
if (v_isSharedCheck_983_ == 0)
{
v___x_970_ = v_ver_943_;
v_isShared_971_ = v_isSharedCheck_983_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_rev_968_);
lean_dec(v_ver_943_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_983_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_975_; 
v___x_972_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__5));
v___x_973_ = l_String_quote(v_rev_968_);
if (v_isShared_971_ == 0)
{
lean_ctor_set_tag(v___x_970_, 3);
lean_ctor_set(v___x_970_, 0, v___x_973_);
v___x_975_ = v___x_970_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v___x_973_);
v___x_975_ = v_reuseFailAlloc_982_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_976_ = l_Std_Format_defWidth;
v___x_977_ = lean_unsigned_to_nat(0u);
v___x_978_ = l_Std_Format_pretty(v___x_975_, v___x_976_, v___x_977_, v___x_977_);
v___x_979_ = lean_string_append(v___x_972_, v___x_978_);
v___x_980_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__6));
v___x_981_ = lean_string_append(v___x_980_, v___x_978_);
lean_dec_ref(v___x_978_);
v_fst_945_ = v___x_979_;
v_snd_946_ = v___x_981_;
goto v___jp_944_;
}
}
}
default: 
{
lean_object* v_ver_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_1000_; 
v_ver_984_ = lean_ctor_get(v_ver_943_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v_ver_943_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_986_ = v_ver_943_;
v_isShared_987_ = v_isSharedCheck_1000_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_ver_984_);
lean_dec(v_ver_943_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_1000_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v_toString_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_992_; 
v_toString_988_ = lean_ctor_get(v_ver_984_, 0);
lean_inc_ref(v_toString_988_);
lean_dec_ref(v_ver_984_);
v___x_989_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__5));
v___x_990_ = l_String_quote(v_toString_988_);
if (v_isShared_987_ == 0)
{
lean_ctor_set_tag(v___x_986_, 3);
lean_ctor_set(v___x_986_, 0, v___x_990_);
v___x_992_ = v___x_986_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v___x_990_);
v___x_992_ = v_reuseFailAlloc_999_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_993_ = l_Std_Format_defWidth;
v___x_994_ = lean_unsigned_to_nat(0u);
v___x_995_ = l_Std_Format_pretty(v___x_992_, v___x_993_, v___x_994_, v___x_994_);
v___x_996_ = lean_string_append(v___x_989_, v___x_995_);
v___x_997_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__7));
v___x_998_ = lean_string_append(v___x_997_, v___x_995_);
lean_dec_ref(v___x_995_);
v_fst_945_ = v___x_996_;
v_snd_946_ = v___x_998_;
goto v___jp_944_;
}
}
}
}
v___jp_944_:
{
lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_947_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
lean_inc_ref(v_scope_941_);
v___x_948_ = lean_string_append(v_scope_941_, v___x_947_);
v___x_949_ = lean_string_append(v___x_948_, v_name_942_);
v___x_950_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__1));
v___x_951_ = lean_string_append(v___x_949_, v___x_950_);
v___x_952_ = lean_string_append(v___x_951_, v_scope_941_);
v___x_953_ = lean_string_append(v___x_952_, v___x_947_);
v___x_954_ = lean_string_append(v___x_953_, v_name_942_);
v___x_955_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__2));
v___x_956_ = lean_string_append(v___x_954_, v___x_955_);
v___x_957_ = lean_string_append(v___x_956_, v_fst_945_);
lean_dec_ref(v_fst_945_);
v___x_958_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__3));
v___x_959_ = lean_string_append(v___x_957_, v___x_958_);
v___x_960_ = lean_string_append(v___x_959_, v_scope_941_);
lean_dec_ref(v_scope_941_);
v___x_961_ = lean_string_append(v___x_960_, v___x_947_);
v___x_962_ = lean_string_append(v___x_961_, v_name_942_);
v___x_963_ = lean_string_append(v___x_962_, v___x_955_);
v___x_964_ = lean_string_append(v___x_963_, v_snd_946_);
lean_dec_ref(v_snd_946_);
v___x_965_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__4));
v___x_966_ = lean_string_append(v___x_964_, v___x_965_);
return v___x_966_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___boxed(lean_object* v_scope_1001_, lean_object* v_name_1002_, lean_object* v_ver_1003_){
_start:
{
lean_object* v_res_1004_; 
v_res_1004_ = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed(v_scope_1001_, v_name_1002_, v_ver_1003_);
lean_dec_ref(v_name_1002_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___lam__0(lean_object* v_x_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_){
_start:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; 
lean_inc_ref(v___y_1007_);
v___x_1009_ = lean_apply_2(v___y_1007_, v___y_1006_, lean_box(0));
v___x_1010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1009_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___lam__0___boxed(lean_object* v_x_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___lam__0(v_x_1011_, v___y_1012_, v___y_1013_);
lean_dec_ref(v___y_1013_);
return v_res_1015_;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1(void){
_start:
{
lean_object* v___x_1017_; 
v___x_1017_ = l_instMonadEIO(lean_box(0));
return v___x_1017_;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__2(void){
_start:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1018_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1, &l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1_once, _init_l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1);
v___x_1019_ = l_ReaderT_instMonad___redArg(v___x_1018_);
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep(lean_object* v_dep_1020_, uint8_t v_inherited_1021_, lean_object* v_pkgDir_1022_, lean_object* v_relPkgDir_1023_, lean_object* v_remoteUrl_1024_, lean_object* v_src_1025_, lean_object* v_a_1026_){
_start:
{
lean_object* v_a_1029_; lean_object* v___f_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v_val_1043_; lean_object* v___x_1071_; 
v___f_1037_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0));
v___x_1038_ = l_Lake_defaultManifestFile;
v___x_1039_ = l_Lake_joinRelative(v_pkgDir_1022_, v___x_1038_);
v___x_1040_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__2, &l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__2_once, _init_l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__2);
v___x_1041_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
v___x_1071_ = l_Lake_Manifest_load(v___x_1039_);
if (lean_obj_tag(v___x_1071_) == 0)
{
lean_object* v_a_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1079_; 
v_a_1072_ = lean_ctor_get(v___x_1071_, 0);
v_isSharedCheck_1079_ = !lean_is_exclusive(v___x_1071_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1074_ = v___x_1071_;
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_a_1072_);
lean_dec(v___x_1071_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1077_; 
if (v_isShared_1075_ == 0)
{
lean_ctor_set_tag(v___x_1074_, 1);
v___x_1077_ = v___x_1074_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_a_1072_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
v_val_1043_ = v___x_1077_;
goto v___jp_1042_;
}
}
}
else
{
lean_object* v_a_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1087_; 
v_a_1080_ = lean_ctor_get(v___x_1071_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1071_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1082_ = v___x_1071_;
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_a_1080_);
lean_dec(v___x_1071_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1085_; 
if (v_isShared_1083_ == 0)
{
lean_ctor_set_tag(v___x_1082_, 0);
v___x_1085_ = v___x_1082_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_a_1080_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
v_val_1043_ = v___x_1085_;
goto v___jp_1042_;
}
}
}
v___jp_1028_:
{
lean_object* v_name_1030_; lean_object* v_scope_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; 
v_name_1030_ = lean_ctor_get(v_dep_1020_, 0);
v_scope_1031_ = lean_ctor_get(v_dep_1020_, 1);
v___x_1032_ = l_Lake_defaultConfigFile;
v___x_1033_ = lean_box(0);
lean_inc_ref(v_scope_1031_);
lean_inc(v_name_1030_);
v___x_1034_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1034_, 0, v_name_1030_);
lean_ctor_set(v___x_1034_, 1, v_scope_1031_);
lean_ctor_set(v___x_1034_, 2, v___x_1032_);
lean_ctor_set(v___x_1034_, 3, v___x_1033_);
lean_ctor_set(v___x_1034_, 4, v_src_1025_);
lean_ctor_set_uint8(v___x_1034_, sizeof(void*)*5, v_inherited_1021_);
v___x_1035_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1035_, 0, v_relPkgDir_1023_);
lean_ctor_set(v___x_1035_, 1, v_remoteUrl_1024_);
lean_ctor_set(v___x_1035_, 2, v_a_1029_);
lean_ctor_set(v___x_1035_, 3, v___x_1034_);
v___x_1036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1035_);
return v___x_1036_;
}
v___jp_1042_:
{
uint8_t v___x_1044_; 
v___x_1044_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_1044_ == 0)
{
v_a_1029_ = v_val_1043_;
goto v___jp_1028_;
}
else
{
lean_object* v___x_1045_; uint8_t v___x_1046_; 
v___x_1045_ = lean_box(0);
v___x_1046_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_1046_ == 0)
{
if (v___x_1044_ == 0)
{
v_a_1029_ = v_val_1043_;
goto v___jp_1028_;
}
else
{
size_t v___x_1047_; size_t v___x_1048_; lean_object* v___x_808__overap_1049_; lean_object* v___x_1050_; 
v___x_1047_ = ((size_t)0ULL);
v___x_1048_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_808__overap_1049_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1040_, v___f_1037_, v___x_1041_, v___x_1047_, v___x_1048_, v___x_1045_);
lean_inc_ref(v_a_1026_);
v___x_1050_ = lean_apply_2(v___x_808__overap_1049_, v_a_1026_, lean_box(0));
if (lean_obj_tag(v___x_1050_) == 0)
{
lean_dec_ref(v___x_1050_);
v_a_1029_ = v_val_1043_;
goto v___jp_1028_;
}
else
{
lean_object* v_a_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1058_; 
lean_dec_ref(v_val_1043_);
lean_dec_ref(v_src_1025_);
lean_dec_ref(v_remoteUrl_1024_);
lean_dec_ref(v_relPkgDir_1023_);
v_a_1051_ = lean_ctor_get(v___x_1050_, 0);
v_isSharedCheck_1058_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1053_ = v___x_1050_;
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_a_1051_);
lean_dec(v___x_1050_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1056_; 
if (v_isShared_1054_ == 0)
{
v___x_1056_ = v___x_1053_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v_a_1051_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
}
}
}
else
{
size_t v___x_1059_; size_t v___x_1060_; lean_object* v___x_818__overap_1061_; lean_object* v___x_1062_; 
v___x_1059_ = ((size_t)0ULL);
v___x_1060_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_818__overap_1061_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1040_, v___f_1037_, v___x_1041_, v___x_1059_, v___x_1060_, v___x_1045_);
lean_inc_ref(v_a_1026_);
v___x_1062_ = lean_apply_2(v___x_818__overap_1061_, v_a_1026_, lean_box(0));
if (lean_obj_tag(v___x_1062_) == 0)
{
lean_dec_ref(v___x_1062_);
v_a_1029_ = v_val_1043_;
goto v___jp_1028_;
}
else
{
lean_object* v_a_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1070_; 
lean_dec_ref(v_val_1043_);
lean_dec_ref(v_src_1025_);
lean_dec_ref(v_remoteUrl_1024_);
lean_dec_ref(v_relPkgDir_1023_);
v_a_1063_ = lean_ctor_get(v___x_1062_, 0);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1065_ = v___x_1062_;
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_a_1063_);
lean_dec(v___x_1062_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1068_; 
if (v_isShared_1066_ == 0)
{
v___x_1068_ = v___x_1065_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_a_1063_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___boxed(lean_object* v_dep_1088_, lean_object* v_inherited_1089_, lean_object* v_pkgDir_1090_, lean_object* v_relPkgDir_1091_, lean_object* v_remoteUrl_1092_, lean_object* v_src_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_){
_start:
{
uint8_t v_inherited_boxed_1096_; lean_object* v_res_1097_; 
v_inherited_boxed_1096_ = lean_unbox(v_inherited_1089_);
v_res_1097_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep(v_dep_1088_, v_inherited_boxed_1096_, v_pkgDir_1090_, v_relPkgDir_1091_, v_remoteUrl_1092_, v_src_1093_, v_a_1094_);
lean_dec_ref(v_a_1094_);
lean_dec_ref(v_dep_1088_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(lean_object* v_a_1098_, lean_object* v_name_1099_, lean_object* v_repo_1100_, lean_object* v_url_1101_, lean_object* v_rev_x3f_1102_){
_start:
{
uint8_t v___x_1104_; lean_object* v___x_1108_; uint8_t v___x_1109_; 
v___x_1104_ = l_System_FilePath_isDir(v_repo_1100_);
v___x_1108_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
v___x_1109_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_1109_ == 0)
{
goto v___jp_1105_;
}
else
{
lean_object* v___x_1110_; uint8_t v___x_1111_; 
v___x_1110_ = lean_box(0);
v___x_1111_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_1111_ == 0)
{
if (v___x_1109_ == 0)
{
goto v___jp_1105_;
}
else
{
size_t v___x_1112_; size_t v___x_1113_; lean_object* v___x_1114_; 
v___x_1112_ = ((size_t)0ULL);
v___x_1113_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_1114_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_1108_, v___x_1112_, v___x_1113_, v___x_1110_, v_a_1098_);
if (lean_obj_tag(v___x_1114_) == 0)
{
lean_dec_ref(v___x_1114_);
goto v___jp_1105_;
}
else
{
lean_dec(v_rev_x3f_1102_);
lean_dec_ref(v_url_1101_);
lean_dec_ref(v_repo_1100_);
lean_dec_ref(v_name_1099_);
return v___x_1114_;
}
}
}
else
{
size_t v___x_1115_; size_t v___x_1116_; lean_object* v___x_1117_; 
v___x_1115_ = ((size_t)0ULL);
v___x_1116_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_1117_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_1108_, v___x_1115_, v___x_1116_, v___x_1110_, v_a_1098_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_dec_ref(v___x_1117_);
goto v___jp_1105_;
}
else
{
lean_dec(v_rev_x3f_1102_);
lean_dec_ref(v_url_1101_);
lean_dec_ref(v_repo_1100_);
lean_dec_ref(v_name_1099_);
return v___x_1117_;
}
}
}
v___jp_1105_:
{
if (v___x_1104_ == 0)
{
lean_object* v___x_1106_; 
v___x_1106_ = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(v_a_1098_, v_name_1099_, v_repo_1100_, v_url_1101_, v_rev_x3f_1102_);
return v___x_1106_;
}
else
{
lean_object* v___x_1107_; 
v___x_1107_ = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1098_, v_name_1099_, v_repo_1100_, v_url_1101_, v_rev_x3f_1102_);
return v___x_1107_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0___boxed(lean_object* v_a_1118_, lean_object* v_name_1119_, lean_object* v_repo_1120_, lean_object* v_url_1121_, lean_object* v_rev_x3f_1122_, lean_object* v_a_1123_){
_start:
{
lean_object* v_res_1124_; 
v_res_1124_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(v_a_1118_, v_name_1119_, v_repo_1120_, v_url_1121_, v_rev_x3f_1122_);
lean_dec_ref(v_a_1118_);
return v_res_1124_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit(lean_object* v_dep_1125_, uint8_t v_inherited_1126_, lean_object* v_lakeEnv_1127_, lean_object* v_wsDir_1128_, lean_object* v_name_1129_, lean_object* v_relPkgDir_1130_, lean_object* v_gitUrl_1131_, lean_object* v_remoteUrl_1132_, lean_object* v_inputRev_x3f_1133_, lean_object* v_subDir_x3f_1134_, lean_object* v_a_1135_){
_start:
{
lean_object* v_pkgUrlMap_1140_; lean_object* v_name_1141_; lean_object* v_scope_1142_; lean_object* v___y_1144_; lean_object* v___y_1145_; lean_object* v_a_1146_; lean_object* v___y_1153_; lean_object* v___y_1154_; lean_object* v___y_1155_; lean_object* v___y_1156_; lean_object* v_val_1157_; lean_object* v_pkgDir_1184_; lean_object* v___y_1186_; lean_object* v___y_1187_; lean_object* v___y_1188_; lean_object* v___y_1212_; lean_object* v_a_1213_; lean_object* v___y_1217_; lean_object* v___x_1294_; 
v_pkgUrlMap_1140_ = lean_ctor_get(v_lakeEnv_1127_, 5);
v_name_1141_ = lean_ctor_get(v_dep_1125_, 0);
v_scope_1142_ = lean_ctor_get(v_dep_1125_, 1);
lean_inc_ref(v_relPkgDir_1130_);
v_pkgDir_1184_ = l_Lake_joinRelative(v_wsDir_1128_, v_relPkgDir_1130_);
v___x_1294_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgUrlMap_1140_, v_name_1141_);
if (lean_obj_tag(v___x_1294_) == 0)
{
v___y_1217_ = v_gitUrl_1131_;
goto v___jp_1216_;
}
else
{
lean_object* v_val_1295_; 
lean_dec_ref(v_gitUrl_1131_);
v_val_1295_ = lean_ctor_get(v___x_1294_, 0);
lean_inc(v_val_1295_);
lean_dec_ref(v___x_1294_);
v___y_1217_ = v_val_1295_;
goto v___jp_1216_;
}
v___jp_1137_:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1138_ = lean_box(0);
v___x_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1138_);
return v___x_1139_;
}
v___jp_1143_:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1147_ = l_Lake_defaultConfigFile;
v___x_1148_ = lean_box(0);
lean_inc_ref(v_scope_1142_);
lean_inc(v_name_1141_);
v___x_1149_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1149_, 0, v_name_1141_);
lean_ctor_set(v___x_1149_, 1, v_scope_1142_);
lean_ctor_set(v___x_1149_, 2, v___x_1147_);
lean_ctor_set(v___x_1149_, 3, v___x_1148_);
lean_ctor_set(v___x_1149_, 4, v___y_1145_);
lean_ctor_set_uint8(v___x_1149_, sizeof(void*)*5, v_inherited_1126_);
v___x_1150_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1150_, 0, v___y_1144_);
lean_ctor_set(v___x_1150_, 1, v_remoteUrl_1132_);
lean_ctor_set(v___x_1150_, 2, v_a_1146_);
lean_ctor_set(v___x_1150_, 3, v___x_1149_);
v___x_1151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1150_);
return v___x_1151_;
}
v___jp_1152_:
{
lean_object* v___x_1158_; uint8_t v___x_1159_; 
v___x_1158_ = lean_array_get_size(v___y_1155_);
v___x_1159_ = lean_nat_dec_lt(v___y_1156_, v___x_1158_);
if (v___x_1159_ == 0)
{
lean_dec_ref(v___y_1155_);
v___y_1144_ = v___y_1153_;
v___y_1145_ = v___y_1154_;
v_a_1146_ = v_val_1157_;
goto v___jp_1143_;
}
else
{
lean_object* v___x_1160_; uint8_t v___x_1161_; 
v___x_1160_ = lean_box(0);
v___x_1161_ = lean_nat_dec_le(v___x_1158_, v___x_1158_);
if (v___x_1161_ == 0)
{
if (v___x_1159_ == 0)
{
lean_dec_ref(v___y_1155_);
v___y_1144_ = v___y_1153_;
v___y_1145_ = v___y_1154_;
v_a_1146_ = v_val_1157_;
goto v___jp_1143_;
}
else
{
size_t v___x_1162_; size_t v___x_1163_; lean_object* v___x_1164_; 
v___x_1162_ = ((size_t)0ULL);
v___x_1163_ = lean_usize_of_nat(v___x_1158_);
v___x_1164_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_1155_, v___x_1162_, v___x_1163_, v___x_1160_, v_a_1135_);
lean_dec_ref(v___y_1155_);
if (lean_obj_tag(v___x_1164_) == 0)
{
lean_dec_ref(v___x_1164_);
v___y_1144_ = v___y_1153_;
v___y_1145_ = v___y_1154_;
v_a_1146_ = v_val_1157_;
goto v___jp_1143_;
}
else
{
lean_object* v_a_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1172_; 
lean_dec_ref(v_val_1157_);
lean_dec_ref(v___y_1154_);
lean_dec_ref(v___y_1153_);
lean_dec_ref(v_remoteUrl_1132_);
v_a_1165_ = lean_ctor_get(v___x_1164_, 0);
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1167_ = v___x_1164_;
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_a_1165_);
lean_dec(v___x_1164_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1170_; 
if (v_isShared_1168_ == 0)
{
v___x_1170_ = v___x_1167_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v_a_1165_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
}
}
else
{
size_t v___x_1173_; size_t v___x_1174_; lean_object* v___x_1175_; 
v___x_1173_ = ((size_t)0ULL);
v___x_1174_ = lean_usize_of_nat(v___x_1158_);
v___x_1175_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_1155_, v___x_1173_, v___x_1174_, v___x_1160_, v_a_1135_);
lean_dec_ref(v___y_1155_);
if (lean_obj_tag(v___x_1175_) == 0)
{
lean_dec_ref(v___x_1175_);
v___y_1144_ = v___y_1153_;
v___y_1145_ = v___y_1154_;
v_a_1146_ = v_val_1157_;
goto v___jp_1143_;
}
else
{
lean_object* v_a_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1183_; 
lean_dec_ref(v_val_1157_);
lean_dec_ref(v___y_1154_);
lean_dec_ref(v___y_1153_);
lean_dec_ref(v_remoteUrl_1132_);
v_a_1176_ = lean_ctor_get(v___x_1175_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1178_ = v___x_1175_;
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_a_1176_);
lean_dec(v___x_1175_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1181_; 
if (v_isShared_1179_ == 0)
{
v___x_1181_ = v___x_1178_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_a_1176_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
}
}
}
}
v___jp_1185_:
{
lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1189_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1189_, 0, v___y_1186_);
lean_ctor_set(v___x_1189_, 1, v___y_1187_);
lean_ctor_set(v___x_1189_, 2, v_inputRev_x3f_1133_);
lean_ctor_set(v___x_1189_, 3, v_subDir_x3f_1134_);
v___x_1190_ = l_Lake_defaultManifestFile;
v___x_1191_ = l_Lake_joinRelative(v_pkgDir_1184_, v___x_1190_);
v___x_1192_ = lean_unsigned_to_nat(0u);
v___x_1193_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
v___x_1194_ = l_Lake_Manifest_load(v___x_1191_);
if (lean_obj_tag(v___x_1194_) == 0)
{
lean_object* v_a_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1202_; 
v_a_1195_ = lean_ctor_get(v___x_1194_, 0);
v_isSharedCheck_1202_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1197_ = v___x_1194_;
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_a_1195_);
lean_dec(v___x_1194_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v___x_1200_; 
if (v_isShared_1198_ == 0)
{
lean_ctor_set_tag(v___x_1197_, 1);
v___x_1200_ = v___x_1197_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v_a_1195_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
v___y_1153_ = v___y_1188_;
v___y_1154_ = v___x_1189_;
v___y_1155_ = v___x_1193_;
v___y_1156_ = v___x_1192_;
v_val_1157_ = v___x_1200_;
goto v___jp_1152_;
}
}
}
else
{
lean_object* v_a_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1210_; 
v_a_1203_ = lean_ctor_get(v___x_1194_, 0);
v_isSharedCheck_1210_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1205_ = v___x_1194_;
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_a_1203_);
lean_dec(v___x_1194_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1208_; 
if (v_isShared_1206_ == 0)
{
lean_ctor_set_tag(v___x_1205_, 0);
v___x_1208_ = v___x_1205_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_a_1203_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
v___y_1153_ = v___y_1188_;
v___y_1154_ = v___x_1189_;
v___y_1155_ = v___x_1193_;
v___y_1156_ = v___x_1192_;
v_val_1157_ = v___x_1208_;
goto v___jp_1152_;
}
}
}
}
v___jp_1211_:
{
if (lean_obj_tag(v_subDir_x3f_1134_) == 1)
{
lean_object* v_val_1214_; lean_object* v___x_1215_; 
v_val_1214_ = lean_ctor_get(v_subDir_x3f_1134_, 0);
lean_inc(v_val_1214_);
v___x_1215_ = l_Lake_joinRelative(v_relPkgDir_1130_, v_val_1214_);
v___y_1186_ = v___y_1212_;
v___y_1187_ = v_a_1213_;
v___y_1188_ = v___x_1215_;
goto v___jp_1185_;
}
else
{
v___y_1186_ = v___y_1212_;
v___y_1187_ = v_a_1213_;
v___y_1188_ = v_relPkgDir_1130_;
goto v___jp_1185_;
}
}
v___jp_1216_:
{
lean_object* v___x_1218_; 
lean_inc(v_inputRev_x3f_1133_);
lean_inc_ref(v___y_1217_);
lean_inc_ref(v_pkgDir_1184_);
v___x_1218_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(v_a_1135_, v_name_1129_, v_pkgDir_1184_, v___y_1217_, v_inputRev_x3f_1133_);
if (lean_obj_tag(v___x_1218_) == 0)
{
lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1284_; 
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1284_ == 0)
{
lean_object* v_unused_1285_; 
v_unused_1285_ = lean_ctor_get(v___x_1218_, 0);
lean_dec(v_unused_1285_);
v___x_1220_ = v___x_1218_;
v_isShared_1221_ = v_isSharedCheck_1284_;
goto v_resetjp_1219_;
}
else
{
lean_dec(v___x_1218_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1284_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1222_ = lean_unsigned_to_nat(0u);
v___x_1223_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
lean_inc_ref(v_pkgDir_1184_);
v___x_1224_ = l_Lake_GitRepo_getHeadRevision(v_pkgDir_1184_, v___x_1223_);
if (lean_obj_tag(v___x_1224_) == 0)
{
lean_object* v_a_1225_; lean_object* v_a_1226_; lean_object* v___x_1227_; uint8_t v___x_1228_; 
lean_del_object(v___x_1220_);
v_a_1225_ = lean_ctor_get(v___x_1224_, 0);
lean_inc(v_a_1225_);
v_a_1226_ = lean_ctor_get(v___x_1224_, 1);
lean_inc(v_a_1226_);
lean_dec_ref(v___x_1224_);
v___x_1227_ = lean_array_get_size(v_a_1226_);
v___x_1228_ = lean_nat_dec_lt(v___x_1222_, v___x_1227_);
if (v___x_1228_ == 0)
{
lean_dec(v_a_1226_);
v___y_1212_ = v___y_1217_;
v_a_1213_ = v_a_1225_;
goto v___jp_1211_;
}
else
{
lean_object* v___x_1229_; uint8_t v___x_1230_; 
v___x_1229_ = lean_box(0);
v___x_1230_ = lean_nat_dec_le(v___x_1227_, v___x_1227_);
if (v___x_1230_ == 0)
{
if (v___x_1228_ == 0)
{
lean_dec(v_a_1226_);
v___y_1212_ = v___y_1217_;
v_a_1213_ = v_a_1225_;
goto v___jp_1211_;
}
else
{
size_t v___x_1231_; size_t v___x_1232_; lean_object* v___x_1233_; 
v___x_1231_ = ((size_t)0ULL);
v___x_1232_ = lean_usize_of_nat(v___x_1227_);
v___x_1233_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_1226_, v___x_1231_, v___x_1232_, v___x_1229_, v_a_1135_);
lean_dec(v_a_1226_);
if (lean_obj_tag(v___x_1233_) == 0)
{
lean_dec_ref(v___x_1233_);
v___y_1212_ = v___y_1217_;
v_a_1213_ = v_a_1225_;
goto v___jp_1211_;
}
else
{
lean_object* v_a_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1241_; 
lean_dec(v_a_1225_);
lean_dec_ref(v___y_1217_);
lean_dec_ref(v_pkgDir_1184_);
lean_dec(v_subDir_x3f_1134_);
lean_dec(v_inputRev_x3f_1133_);
lean_dec_ref(v_remoteUrl_1132_);
lean_dec_ref(v_relPkgDir_1130_);
v_a_1234_ = lean_ctor_get(v___x_1233_, 0);
v_isSharedCheck_1241_ = !lean_is_exclusive(v___x_1233_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1236_ = v___x_1233_;
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_a_1234_);
lean_dec(v___x_1233_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v___x_1239_; 
if (v_isShared_1237_ == 0)
{
v___x_1239_ = v___x_1236_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_a_1234_);
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
size_t v___x_1242_; size_t v___x_1243_; lean_object* v___x_1244_; 
v___x_1242_ = ((size_t)0ULL);
v___x_1243_ = lean_usize_of_nat(v___x_1227_);
v___x_1244_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_1226_, v___x_1242_, v___x_1243_, v___x_1229_, v_a_1135_);
lean_dec(v_a_1226_);
if (lean_obj_tag(v___x_1244_) == 0)
{
lean_dec_ref(v___x_1244_);
v___y_1212_ = v___y_1217_;
v_a_1213_ = v_a_1225_;
goto v___jp_1211_;
}
else
{
lean_object* v_a_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1252_; 
lean_dec(v_a_1225_);
lean_dec_ref(v___y_1217_);
lean_dec_ref(v_pkgDir_1184_);
lean_dec(v_subDir_x3f_1134_);
lean_dec(v_inputRev_x3f_1133_);
lean_dec_ref(v_remoteUrl_1132_);
lean_dec_ref(v_relPkgDir_1130_);
v_a_1245_ = lean_ctor_get(v___x_1244_, 0);
v_isSharedCheck_1252_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1247_ = v___x_1244_;
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_a_1245_);
lean_dec(v___x_1244_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1250_; 
if (v_isShared_1248_ == 0)
{
v___x_1250_ = v___x_1247_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_a_1245_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
}
}
}
}
else
{
lean_object* v_a_1253_; lean_object* v___x_1254_; uint8_t v___x_1255_; 
lean_dec_ref(v___y_1217_);
lean_dec_ref(v_pkgDir_1184_);
lean_dec(v_subDir_x3f_1134_);
lean_dec(v_inputRev_x3f_1133_);
lean_dec_ref(v_remoteUrl_1132_);
lean_dec_ref(v_relPkgDir_1130_);
v_a_1253_ = lean_ctor_get(v___x_1224_, 1);
lean_inc(v_a_1253_);
lean_dec_ref(v___x_1224_);
v___x_1254_ = lean_array_get_size(v_a_1253_);
v___x_1255_ = lean_nat_dec_lt(v___x_1222_, v___x_1254_);
if (v___x_1255_ == 0)
{
lean_object* v___x_1256_; lean_object* v___x_1258_; 
lean_dec(v_a_1253_);
v___x_1256_ = lean_box(0);
if (v_isShared_1221_ == 0)
{
lean_ctor_set_tag(v___x_1220_, 1);
lean_ctor_set(v___x_1220_, 0, v___x_1256_);
v___x_1258_ = v___x_1220_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v___x_1256_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
return v___x_1258_;
}
}
else
{
lean_object* v___x_1260_; uint8_t v___x_1261_; 
lean_del_object(v___x_1220_);
v___x_1260_ = lean_box(0);
v___x_1261_ = lean_nat_dec_le(v___x_1254_, v___x_1254_);
if (v___x_1261_ == 0)
{
if (v___x_1255_ == 0)
{
lean_dec(v_a_1253_);
goto v___jp_1137_;
}
else
{
size_t v___x_1262_; size_t v___x_1263_; lean_object* v___x_1264_; 
v___x_1262_ = ((size_t)0ULL);
v___x_1263_ = lean_usize_of_nat(v___x_1254_);
v___x_1264_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_1253_, v___x_1262_, v___x_1263_, v___x_1260_, v_a_1135_);
lean_dec(v_a_1253_);
if (lean_obj_tag(v___x_1264_) == 0)
{
lean_dec_ref(v___x_1264_);
goto v___jp_1137_;
}
else
{
lean_object* v_a_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1272_; 
v_a_1265_ = lean_ctor_get(v___x_1264_, 0);
v_isSharedCheck_1272_ = !lean_is_exclusive(v___x_1264_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1267_ = v___x_1264_;
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_a_1265_);
lean_dec(v___x_1264_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1270_; 
if (v_isShared_1268_ == 0)
{
v___x_1270_ = v___x_1267_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_a_1265_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
return v___x_1270_;
}
}
}
}
}
else
{
size_t v___x_1273_; size_t v___x_1274_; lean_object* v___x_1275_; 
v___x_1273_ = ((size_t)0ULL);
v___x_1274_ = lean_usize_of_nat(v___x_1254_);
v___x_1275_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_1253_, v___x_1273_, v___x_1274_, v___x_1260_, v_a_1135_);
lean_dec(v_a_1253_);
if (lean_obj_tag(v___x_1275_) == 0)
{
lean_dec_ref(v___x_1275_);
goto v___jp_1137_;
}
else
{
lean_object* v_a_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1283_; 
v_a_1276_ = lean_ctor_get(v___x_1275_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1278_ = v___x_1275_;
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_a_1276_);
lean_dec(v___x_1275_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1281_; 
if (v_isShared_1279_ == 0)
{
v___x_1281_ = v___x_1278_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v_a_1276_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
return v___x_1281_;
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
lean_object* v_a_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1293_; 
lean_dec_ref(v___y_1217_);
lean_dec_ref(v_pkgDir_1184_);
lean_dec(v_subDir_x3f_1134_);
lean_dec(v_inputRev_x3f_1133_);
lean_dec_ref(v_remoteUrl_1132_);
lean_dec_ref(v_relPkgDir_1130_);
v_a_1286_ = lean_ctor_get(v___x_1218_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1288_ = v___x_1218_;
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_a_1286_);
lean_dec(v___x_1218_);
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
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___boxed(lean_object* v_dep_1296_, lean_object* v_inherited_1297_, lean_object* v_lakeEnv_1298_, lean_object* v_wsDir_1299_, lean_object* v_name_1300_, lean_object* v_relPkgDir_1301_, lean_object* v_gitUrl_1302_, lean_object* v_remoteUrl_1303_, lean_object* v_inputRev_x3f_1304_, lean_object* v_subDir_x3f_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_){
_start:
{
uint8_t v_inherited_boxed_1308_; lean_object* v_res_1309_; 
v_inherited_boxed_1308_ = lean_unbox(v_inherited_1297_);
v_res_1309_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit(v_dep_1296_, v_inherited_boxed_1308_, v_lakeEnv_1298_, v_wsDir_1299_, v_name_1300_, v_relPkgDir_1301_, v_gitUrl_1302_, v_remoteUrl_1303_, v_inputRev_x3f_1304_, v_subDir_x3f_1305_, v_a_1306_);
lean_dec_ref(v_a_1306_);
lean_dec_ref(v_lakeEnv_1298_);
lean_dec_ref(v_dep_1296_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(lean_object* v_a_1310_, lean_object* v_dep_1311_, uint8_t v_inherited_1312_, lean_object* v_lakeEnv_1313_, lean_object* v_wsDir_1314_, lean_object* v_name_1315_, lean_object* v_relPkgDir_1316_, lean_object* v_gitUrl_1317_, lean_object* v_remoteUrl_1318_, lean_object* v_inputRev_x3f_1319_, lean_object* v_subDir_x3f_1320_){
_start:
{
lean_object* v_pkgUrlMap_1325_; lean_object* v_name_1326_; lean_object* v_scope_1327_; lean_object* v___y_1329_; lean_object* v___y_1330_; lean_object* v_a_1331_; lean_object* v___y_1338_; lean_object* v___y_1339_; lean_object* v___y_1340_; lean_object* v___y_1341_; lean_object* v_val_1342_; lean_object* v_pkgDir_1369_; lean_object* v___y_1371_; lean_object* v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1397_; lean_object* v_a_1398_; lean_object* v___y_1402_; lean_object* v___x_1479_; 
v_pkgUrlMap_1325_ = lean_ctor_get(v_lakeEnv_1313_, 5);
v_name_1326_ = lean_ctor_get(v_dep_1311_, 0);
v_scope_1327_ = lean_ctor_get(v_dep_1311_, 1);
lean_inc_ref(v_relPkgDir_1316_);
v_pkgDir_1369_ = l_Lake_joinRelative(v_wsDir_1314_, v_relPkgDir_1316_);
v___x_1479_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgUrlMap_1325_, v_name_1326_);
if (lean_obj_tag(v___x_1479_) == 0)
{
v___y_1402_ = v_gitUrl_1317_;
goto v___jp_1401_;
}
else
{
lean_object* v_val_1480_; 
lean_dec_ref(v_gitUrl_1317_);
v_val_1480_ = lean_ctor_get(v___x_1479_, 0);
lean_inc(v_val_1480_);
lean_dec_ref(v___x_1479_);
v___y_1402_ = v_val_1480_;
goto v___jp_1401_;
}
v___jp_1322_:
{
lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1323_ = lean_box(0);
v___x_1324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1323_);
return v___x_1324_;
}
v___jp_1328_:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; 
v___x_1332_ = l_Lake_defaultConfigFile;
v___x_1333_ = lean_box(0);
lean_inc_ref(v_scope_1327_);
lean_inc(v_name_1326_);
v___x_1334_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1334_, 0, v_name_1326_);
lean_ctor_set(v___x_1334_, 1, v_scope_1327_);
lean_ctor_set(v___x_1334_, 2, v___x_1332_);
lean_ctor_set(v___x_1334_, 3, v___x_1333_);
lean_ctor_set(v___x_1334_, 4, v___y_1330_);
lean_ctor_set_uint8(v___x_1334_, sizeof(void*)*5, v_inherited_1312_);
v___x_1335_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1335_, 0, v___y_1329_);
lean_ctor_set(v___x_1335_, 1, v_remoteUrl_1318_);
lean_ctor_set(v___x_1335_, 2, v_a_1331_);
lean_ctor_set(v___x_1335_, 3, v___x_1334_);
v___x_1336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1336_, 0, v___x_1335_);
return v___x_1336_;
}
v___jp_1337_:
{
lean_object* v___x_1343_; uint8_t v___x_1344_; 
v___x_1343_ = lean_array_get_size(v___y_1338_);
v___x_1344_ = lean_nat_dec_lt(v___y_1339_, v___x_1343_);
if (v___x_1344_ == 0)
{
lean_dec_ref(v___y_1338_);
v___y_1329_ = v___y_1340_;
v___y_1330_ = v___y_1341_;
v_a_1331_ = v_val_1342_;
goto v___jp_1328_;
}
else
{
lean_object* v___x_1345_; uint8_t v___x_1346_; 
v___x_1345_ = lean_box(0);
v___x_1346_ = lean_nat_dec_le(v___x_1343_, v___x_1343_);
if (v___x_1346_ == 0)
{
if (v___x_1344_ == 0)
{
lean_dec_ref(v___y_1338_);
v___y_1329_ = v___y_1340_;
v___y_1330_ = v___y_1341_;
v_a_1331_ = v_val_1342_;
goto v___jp_1328_;
}
else
{
size_t v___x_1347_; size_t v___x_1348_; lean_object* v___x_1349_; 
v___x_1347_ = ((size_t)0ULL);
v___x_1348_ = lean_usize_of_nat(v___x_1343_);
v___x_1349_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_1338_, v___x_1347_, v___x_1348_, v___x_1345_, v_a_1310_);
lean_dec_ref(v___y_1338_);
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_dec_ref(v___x_1349_);
v___y_1329_ = v___y_1340_;
v___y_1330_ = v___y_1341_;
v_a_1331_ = v_val_1342_;
goto v___jp_1328_;
}
else
{
lean_object* v_a_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1357_; 
lean_dec_ref(v_val_1342_);
lean_dec_ref(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec_ref(v_remoteUrl_1318_);
v_a_1350_ = lean_ctor_get(v___x_1349_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1352_ = v___x_1349_;
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_a_1350_);
lean_dec(v___x_1349_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1355_; 
if (v_isShared_1353_ == 0)
{
v___x_1355_ = v___x_1352_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_a_1350_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
return v___x_1355_;
}
}
}
}
}
else
{
size_t v___x_1358_; size_t v___x_1359_; lean_object* v___x_1360_; 
v___x_1358_ = ((size_t)0ULL);
v___x_1359_ = lean_usize_of_nat(v___x_1343_);
v___x_1360_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_1338_, v___x_1358_, v___x_1359_, v___x_1345_, v_a_1310_);
lean_dec_ref(v___y_1338_);
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_dec_ref(v___x_1360_);
v___y_1329_ = v___y_1340_;
v___y_1330_ = v___y_1341_;
v_a_1331_ = v_val_1342_;
goto v___jp_1328_;
}
else
{
lean_object* v_a_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1368_; 
lean_dec_ref(v_val_1342_);
lean_dec_ref(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec_ref(v_remoteUrl_1318_);
v_a_1361_ = lean_ctor_get(v___x_1360_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1363_ = v___x_1360_;
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_a_1361_);
lean_dec(v___x_1360_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1366_; 
if (v_isShared_1364_ == 0)
{
v___x_1366_ = v___x_1363_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_a_1361_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
}
}
}
}
v___jp_1370_:
{
lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1374_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1374_, 0, v___y_1371_);
lean_ctor_set(v___x_1374_, 1, v___y_1372_);
lean_ctor_set(v___x_1374_, 2, v_inputRev_x3f_1319_);
lean_ctor_set(v___x_1374_, 3, v_subDir_x3f_1320_);
v___x_1375_ = l_Lake_defaultManifestFile;
v___x_1376_ = l_Lake_joinRelative(v_pkgDir_1369_, v___x_1375_);
v___x_1377_ = lean_unsigned_to_nat(0u);
v___x_1378_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
v___x_1379_ = l_Lake_Manifest_load(v___x_1376_);
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_object* v_a_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1387_; 
v_a_1380_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1387_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1382_ = v___x_1379_;
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_a_1380_);
lean_dec(v___x_1379_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1385_; 
if (v_isShared_1383_ == 0)
{
lean_ctor_set_tag(v___x_1382_, 1);
v___x_1385_ = v___x_1382_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_a_1380_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
v___y_1338_ = v___x_1378_;
v___y_1339_ = v___x_1377_;
v___y_1340_ = v___y_1373_;
v___y_1341_ = v___x_1374_;
v_val_1342_ = v___x_1385_;
goto v___jp_1337_;
}
}
}
else
{
lean_object* v_a_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1395_; 
v_a_1388_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1395_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1390_ = v___x_1379_;
v_isShared_1391_ = v_isSharedCheck_1395_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_a_1388_);
lean_dec(v___x_1379_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1395_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v___x_1393_; 
if (v_isShared_1391_ == 0)
{
lean_ctor_set_tag(v___x_1390_, 0);
v___x_1393_ = v___x_1390_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v_a_1388_);
v___x_1393_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
v___y_1338_ = v___x_1378_;
v___y_1339_ = v___x_1377_;
v___y_1340_ = v___y_1373_;
v___y_1341_ = v___x_1374_;
v_val_1342_ = v___x_1393_;
goto v___jp_1337_;
}
}
}
}
v___jp_1396_:
{
if (lean_obj_tag(v_subDir_x3f_1320_) == 1)
{
lean_object* v_val_1399_; lean_object* v___x_1400_; 
v_val_1399_ = lean_ctor_get(v_subDir_x3f_1320_, 0);
lean_inc(v_val_1399_);
v___x_1400_ = l_Lake_joinRelative(v_relPkgDir_1316_, v_val_1399_);
v___y_1371_ = v___y_1397_;
v___y_1372_ = v_a_1398_;
v___y_1373_ = v___x_1400_;
goto v___jp_1370_;
}
else
{
v___y_1371_ = v___y_1397_;
v___y_1372_ = v_a_1398_;
v___y_1373_ = v_relPkgDir_1316_;
goto v___jp_1370_;
}
}
v___jp_1401_:
{
lean_object* v___x_1403_; 
lean_inc(v_inputRev_x3f_1319_);
lean_inc_ref(v___y_1402_);
lean_inc_ref(v_pkgDir_1369_);
v___x_1403_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(v_a_1310_, v_name_1315_, v_pkgDir_1369_, v___y_1402_, v_inputRev_x3f_1319_);
if (lean_obj_tag(v___x_1403_) == 0)
{
lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1469_; 
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1403_);
if (v_isSharedCheck_1469_ == 0)
{
lean_object* v_unused_1470_; 
v_unused_1470_ = lean_ctor_get(v___x_1403_, 0);
lean_dec(v_unused_1470_);
v___x_1405_ = v___x_1403_;
v_isShared_1406_ = v_isSharedCheck_1469_;
goto v_resetjp_1404_;
}
else
{
lean_dec(v___x_1403_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1469_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; 
v___x_1407_ = lean_unsigned_to_nat(0u);
v___x_1408_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
lean_inc_ref(v_pkgDir_1369_);
v___x_1409_ = l_Lake_GitRepo_getHeadRevision(v_pkgDir_1369_, v___x_1408_);
if (lean_obj_tag(v___x_1409_) == 0)
{
lean_object* v_a_1410_; lean_object* v_a_1411_; lean_object* v___x_1412_; uint8_t v___x_1413_; 
lean_del_object(v___x_1405_);
v_a_1410_ = lean_ctor_get(v___x_1409_, 0);
lean_inc(v_a_1410_);
v_a_1411_ = lean_ctor_get(v___x_1409_, 1);
lean_inc(v_a_1411_);
lean_dec_ref(v___x_1409_);
v___x_1412_ = lean_array_get_size(v_a_1411_);
v___x_1413_ = lean_nat_dec_lt(v___x_1407_, v___x_1412_);
if (v___x_1413_ == 0)
{
lean_dec(v_a_1411_);
v___y_1397_ = v___y_1402_;
v_a_1398_ = v_a_1410_;
goto v___jp_1396_;
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
v___y_1397_ = v___y_1402_;
v_a_1398_ = v_a_1410_;
goto v___jp_1396_;
}
else
{
size_t v___x_1416_; size_t v___x_1417_; lean_object* v___x_1418_; 
v___x_1416_ = ((size_t)0ULL);
v___x_1417_ = lean_usize_of_nat(v___x_1412_);
v___x_1418_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_1411_, v___x_1416_, v___x_1417_, v___x_1414_, v_a_1310_);
lean_dec(v_a_1411_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_dec_ref(v___x_1418_);
v___y_1397_ = v___y_1402_;
v_a_1398_ = v_a_1410_;
goto v___jp_1396_;
}
else
{
lean_object* v_a_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1426_; 
lean_dec(v_a_1410_);
lean_dec_ref(v___y_1402_);
lean_dec_ref(v_pkgDir_1369_);
lean_dec(v_subDir_x3f_1320_);
lean_dec(v_inputRev_x3f_1319_);
lean_dec_ref(v_remoteUrl_1318_);
lean_dec_ref(v_relPkgDir_1316_);
v_a_1419_ = lean_ctor_get(v___x_1418_, 0);
v_isSharedCheck_1426_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1421_ = v___x_1418_;
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_a_1419_);
lean_dec(v___x_1418_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1424_; 
if (v_isShared_1422_ == 0)
{
v___x_1424_ = v___x_1421_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v_a_1419_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
}
}
}
else
{
size_t v___x_1427_; size_t v___x_1428_; lean_object* v___x_1429_; 
v___x_1427_ = ((size_t)0ULL);
v___x_1428_ = lean_usize_of_nat(v___x_1412_);
v___x_1429_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_1411_, v___x_1427_, v___x_1428_, v___x_1414_, v_a_1310_);
lean_dec(v_a_1411_);
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_dec_ref(v___x_1429_);
v___y_1397_ = v___y_1402_;
v_a_1398_ = v_a_1410_;
goto v___jp_1396_;
}
else
{
lean_object* v_a_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1437_; 
lean_dec(v_a_1410_);
lean_dec_ref(v___y_1402_);
lean_dec_ref(v_pkgDir_1369_);
lean_dec(v_subDir_x3f_1320_);
lean_dec(v_inputRev_x3f_1319_);
lean_dec_ref(v_remoteUrl_1318_);
lean_dec_ref(v_relPkgDir_1316_);
v_a_1430_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1432_ = v___x_1429_;
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_a_1430_);
lean_dec(v___x_1429_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1435_; 
if (v_isShared_1433_ == 0)
{
v___x_1435_ = v___x_1432_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_a_1430_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
}
}
}
}
else
{
lean_object* v_a_1438_; lean_object* v___x_1439_; uint8_t v___x_1440_; 
lean_dec_ref(v___y_1402_);
lean_dec_ref(v_pkgDir_1369_);
lean_dec(v_subDir_x3f_1320_);
lean_dec(v_inputRev_x3f_1319_);
lean_dec_ref(v_remoteUrl_1318_);
lean_dec_ref(v_relPkgDir_1316_);
v_a_1438_ = lean_ctor_get(v___x_1409_, 1);
lean_inc(v_a_1438_);
lean_dec_ref(v___x_1409_);
v___x_1439_ = lean_array_get_size(v_a_1438_);
v___x_1440_ = lean_nat_dec_lt(v___x_1407_, v___x_1439_);
if (v___x_1440_ == 0)
{
lean_object* v___x_1441_; lean_object* v___x_1443_; 
lean_dec(v_a_1438_);
v___x_1441_ = lean_box(0);
if (v_isShared_1406_ == 0)
{
lean_ctor_set_tag(v___x_1405_, 1);
lean_ctor_set(v___x_1405_, 0, v___x_1441_);
v___x_1443_ = v___x_1405_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v___x_1441_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
else
{
lean_object* v___x_1445_; uint8_t v___x_1446_; 
lean_del_object(v___x_1405_);
v___x_1445_ = lean_box(0);
v___x_1446_ = lean_nat_dec_le(v___x_1439_, v___x_1439_);
if (v___x_1446_ == 0)
{
if (v___x_1440_ == 0)
{
lean_dec(v_a_1438_);
goto v___jp_1322_;
}
else
{
size_t v___x_1447_; size_t v___x_1448_; lean_object* v___x_1449_; 
v___x_1447_ = ((size_t)0ULL);
v___x_1448_ = lean_usize_of_nat(v___x_1439_);
v___x_1449_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_1438_, v___x_1447_, v___x_1448_, v___x_1445_, v_a_1310_);
lean_dec(v_a_1438_);
if (lean_obj_tag(v___x_1449_) == 0)
{
lean_dec_ref(v___x_1449_);
goto v___jp_1322_;
}
else
{
lean_object* v_a_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1457_; 
v_a_1450_ = lean_ctor_get(v___x_1449_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1449_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1452_ = v___x_1449_;
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_a_1450_);
lean_dec(v___x_1449_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1455_; 
if (v_isShared_1453_ == 0)
{
v___x_1455_ = v___x_1452_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_a_1450_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
}
}
}
else
{
size_t v___x_1458_; size_t v___x_1459_; lean_object* v___x_1460_; 
v___x_1458_ = ((size_t)0ULL);
v___x_1459_ = lean_usize_of_nat(v___x_1439_);
v___x_1460_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_1438_, v___x_1458_, v___x_1459_, v___x_1445_, v_a_1310_);
lean_dec(v_a_1438_);
if (lean_obj_tag(v___x_1460_) == 0)
{
lean_dec_ref(v___x_1460_);
goto v___jp_1322_;
}
else
{
lean_object* v_a_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1468_; 
v_a_1461_ = lean_ctor_get(v___x_1460_, 0);
v_isSharedCheck_1468_ = !lean_is_exclusive(v___x_1460_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1463_ = v___x_1460_;
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_a_1461_);
lean_dec(v___x_1460_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1466_; 
if (v_isShared_1464_ == 0)
{
v___x_1466_ = v___x_1463_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_a_1461_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
return v___x_1466_;
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
lean_object* v_a_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1478_; 
lean_dec_ref(v___y_1402_);
lean_dec_ref(v_pkgDir_1369_);
lean_dec(v_subDir_x3f_1320_);
lean_dec(v_inputRev_x3f_1319_);
lean_dec_ref(v_remoteUrl_1318_);
lean_dec_ref(v_relPkgDir_1316_);
v_a_1471_ = lean_ctor_get(v___x_1403_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v___x_1403_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1473_ = v___x_1403_;
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_a_1471_);
lean_dec(v___x_1403_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1476_; 
if (v_isShared_1474_ == 0)
{
v___x_1476_ = v___x_1473_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_a_1471_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0___boxed(lean_object* v_a_1481_, lean_object* v_dep_1482_, lean_object* v_inherited_1483_, lean_object* v_lakeEnv_1484_, lean_object* v_wsDir_1485_, lean_object* v_name_1486_, lean_object* v_relPkgDir_1487_, lean_object* v_gitUrl_1488_, lean_object* v_remoteUrl_1489_, lean_object* v_inputRev_x3f_1490_, lean_object* v_subDir_x3f_1491_, lean_object* v_a_1492_){
_start:
{
uint8_t v_inherited_boxed_1493_; lean_object* v_res_1494_; 
v_inherited_boxed_1493_ = lean_unbox(v_inherited_1483_);
v_res_1494_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(v_a_1481_, v_dep_1482_, v_inherited_boxed_1493_, v_lakeEnv_1484_, v_wsDir_1485_, v_name_1486_, v_relPkgDir_1487_, v_gitUrl_1488_, v_remoteUrl_1489_, v_inputRev_x3f_1490_, v_subDir_x3f_1491_);
lean_dec_ref(v_lakeEnv_1484_);
lean_dec_ref(v_dep_1482_);
lean_dec_ref(v_a_1481_);
return v_res_1494_;
}
}
static lean_object* _init_l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___x_1496_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__0));
v___x_1497_ = lean_string_utf8_byte_size(v___x_1496_);
return v___x_1497_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg(lean_object* v_s_1498_){
_start:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; uint8_t v___x_1502_; 
v___x_1499_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__0));
v___x_1500_ = lean_string_utf8_byte_size(v_s_1498_);
v___x_1501_ = lean_obj_once(&l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__1, &l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__1_once, _init_l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__1);
v___x_1502_ = lean_nat_dec_le(v___x_1501_, v___x_1500_);
if (v___x_1502_ == 0)
{
lean_object* v___x_1503_; 
lean_dec_ref(v_s_1498_);
v___x_1503_ = lean_box(0);
return v___x_1503_;
}
else
{
lean_object* v___x_1504_; uint8_t v___x_1505_; 
v___x_1504_ = lean_unsigned_to_nat(0u);
v___x_1505_ = lean_string_memcmp(v_s_1498_, v___x_1499_, v___x_1504_, v___x_1504_, v___x_1501_);
if (v___x_1505_ == 0)
{
lean_object* v___x_1506_; 
lean_dec_ref(v_s_1498_);
v___x_1506_ = lean_box(0);
return v___x_1506_;
}
else
{
lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; 
lean_inc_ref(v_s_1498_);
v___x_1507_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1507_, 0, v_s_1498_);
lean_ctor_set(v___x_1507_, 1, v___x_1504_);
lean_ctor_set(v___x_1507_, 2, v___x_1500_);
v___x_1508_ = l_String_Slice_pos_x21(v___x_1507_, v___x_1501_);
lean_dec_ref(v___x_1507_);
v___x_1509_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1509_, 0, v_s_1498_);
lean_ctor_set(v___x_1509_, 1, v___x_1508_);
lean_ctor_set(v___x_1509_, 2, v___x_1500_);
v___x_1510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1509_);
return v___x_1510_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2(lean_object* v_s_1511_, lean_object* v_pat_1512_){
_start:
{
lean_object* v___x_1513_; 
v___x_1513_ = l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg(v_s_1511_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___boxed(lean_object* v_s_1514_, lean_object* v_pat_1515_){
_start:
{
lean_object* v_res_1516_; 
v_res_1516_ = l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2(v_s_1514_, v_pat_1515_);
lean_dec_ref(v_pat_1515_);
return v_res_1516_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(lean_object* v_ver_1520_, lean_object* v_as_1521_, size_t v_sz_1522_, size_t v_i_1523_, lean_object* v_b_1524_){
_start:
{
uint8_t v___x_1525_; 
v___x_1525_ = lean_usize_dec_lt(v_i_1523_, v_sz_1522_);
if (v___x_1525_ == 0)
{
return v_b_1524_;
}
else
{
lean_object* v_a_1526_; lean_object* v_version_1527_; lean_object* v___x_1528_; uint8_t v___x_1529_; 
lean_dec_ref(v_b_1524_);
v_a_1526_ = lean_array_uget_borrowed(v_as_1521_, v_i_1523_);
v_version_1527_ = lean_ctor_get(v_a_1526_, 0);
v___x_1528_ = lean_box(0);
v___x_1529_ = l_Lake_VerRange_test(v_ver_1520_, v_version_1527_);
if (v___x_1529_ == 0)
{
lean_object* v___x_1530_; size_t v___x_1531_; size_t v___x_1532_; 
v___x_1530_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___closed__0));
v___x_1531_ = ((size_t)1ULL);
v___x_1532_ = lean_usize_add(v_i_1523_, v___x_1531_);
v_i_1523_ = v___x_1532_;
v_b_1524_ = v___x_1530_;
goto _start;
}
else
{
lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; 
lean_inc(v_a_1526_);
v___x_1534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1534_, 0, v_a_1526_);
v___x_1535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1535_, 0, v___x_1534_);
v___x_1536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1536_, 0, v___x_1535_);
lean_ctor_set(v___x_1536_, 1, v___x_1528_);
return v___x_1536_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___boxed(lean_object* v_ver_1537_, lean_object* v_as_1538_, lean_object* v_sz_1539_, lean_object* v_i_1540_, lean_object* v_b_1541_){
_start:
{
size_t v_sz_boxed_1542_; size_t v_i_boxed_1543_; lean_object* v_res_1544_; 
v_sz_boxed_1542_ = lean_unbox_usize(v_sz_1539_);
lean_dec(v_sz_1539_);
v_i_boxed_1543_ = lean_unbox_usize(v_i_1540_);
lean_dec(v_i_1540_);
v_res_1544_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(v_ver_1537_, v_as_1538_, v_sz_boxed_1542_, v_i_boxed_1543_, v_b_1541_);
lean_dec_ref(v_as_1538_);
lean_dec_ref(v_ver_1537_);
return v_res_1544_;
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize(lean_object* v_dep_1556_, uint8_t v_inherited_1557_, lean_object* v_lakeEnv_1558_, lean_object* v_wsDir_1559_, lean_object* v_relPkgsDir_1560_, lean_object* v_relParentDir_1561_, lean_object* v_a_1562_){
_start:
{
lean_object* v___y_1568_; lean_object* v___y_1569_; lean_object* v___y_1579_; lean_object* v___y_1580_; lean_object* v___y_1581_; lean_object* v___y_1582_; lean_object* v___y_1583_; lean_object* v___y_1584_; lean_object* v___y_1585_; lean_object* v___y_1589_; lean_object* v___y_1590_; lean_object* v___y_1591_; lean_object* v___y_1592_; lean_object* v___y_1593_; lean_object* v_rev_x3f_1594_; lean_object* v___y_1595_; lean_object* v_name_1598_; lean_object* v_scope_1599_; lean_object* v_version_x3f_1600_; lean_object* v_src_x3f_1601_; lean_object* v___y_1603_; lean_object* v___y_1604_; lean_object* v___y_1620_; lean_object* v___y_1621_; lean_object* v___y_1622_; lean_object* v___y_1623_; lean_object* v___y_1624_; lean_object* v___y_1625_; lean_object* v___y_1626_; lean_object* v_a_1627_; 
v_name_1598_ = lean_ctor_get(v_dep_1556_, 0);
v_scope_1599_ = lean_ctor_get(v_dep_1556_, 1);
v_version_x3f_1600_ = lean_ctor_get(v_dep_1556_, 2);
v_src_x3f_1601_ = lean_ctor_get(v_dep_1556_, 3);
lean_inc(v_src_x3f_1601_);
if (lean_obj_tag(v_src_x3f_1601_) == 1)
{
lean_object* v_val_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1753_; 
v_val_1670_ = lean_ctor_get(v_src_x3f_1601_, 0);
v_isSharedCheck_1753_ = !lean_is_exclusive(v_src_x3f_1601_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1672_ = v_src_x3f_1601_;
v_isShared_1673_ = v_isSharedCheck_1753_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_val_1670_);
lean_dec(v_src_x3f_1601_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1753_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
if (lean_obj_tag(v_val_1670_) == 0)
{
lean_object* v_dir_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1740_; 
lean_inc_ref(v_scope_1599_);
lean_inc(v_name_1598_);
lean_dec_ref(v_relPkgsDir_1560_);
lean_dec_ref(v_lakeEnv_1558_);
lean_dec_ref(v_dep_1556_);
v_dir_1674_ = lean_ctor_get(v_val_1670_, 0);
v_isSharedCheck_1740_ = !lean_is_exclusive(v_val_1670_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1676_ = v_val_1670_;
v_isShared_1677_ = v_isSharedCheck_1740_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_dir_1674_);
lean_dec(v_val_1670_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1740_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v_relPkgDir_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1682_; 
v_relPkgDir_1678_ = l_Lake_joinRelative(v_relParentDir_1561_, v_dir_1674_);
lean_inc_ref(v_relPkgDir_1678_);
v___x_1679_ = l_Lake_joinRelative(v_wsDir_1559_, v_relPkgDir_1678_);
v___x_1680_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
lean_inc_ref(v_relPkgDir_1678_);
if (v_isShared_1677_ == 0)
{
lean_ctor_set(v___x_1676_, 0, v_relPkgDir_1678_);
v___x_1682_ = v___x_1676_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_relPkgDir_1678_);
v___x_1682_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
lean_object* v_a_1684_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v_val_1696_; lean_object* v___x_1722_; 
v___x_1692_ = l_Lake_defaultManifestFile;
v___x_1693_ = l_Lake_joinRelative(v___x_1679_, v___x_1692_);
v___x_1694_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
v___x_1722_ = l_Lake_Manifest_load(v___x_1693_);
if (lean_obj_tag(v___x_1722_) == 0)
{
lean_object* v_a_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1730_; 
v_a_1723_ = lean_ctor_get(v___x_1722_, 0);
v_isSharedCheck_1730_ = !lean_is_exclusive(v___x_1722_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1725_ = v___x_1722_;
v_isShared_1726_ = v_isSharedCheck_1730_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_a_1723_);
lean_dec(v___x_1722_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1730_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v___x_1728_; 
if (v_isShared_1726_ == 0)
{
lean_ctor_set_tag(v___x_1725_, 1);
v___x_1728_ = v___x_1725_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v_a_1723_);
v___x_1728_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
v_val_1696_ = v___x_1728_;
goto v___jp_1695_;
}
}
}
else
{
lean_object* v_a_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1738_; 
v_a_1731_ = lean_ctor_get(v___x_1722_, 0);
v_isSharedCheck_1738_ = !lean_is_exclusive(v___x_1722_);
if (v_isSharedCheck_1738_ == 0)
{
v___x_1733_ = v___x_1722_;
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_a_1731_);
lean_dec(v___x_1722_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v___x_1736_; 
if (v_isShared_1734_ == 0)
{
lean_ctor_set_tag(v___x_1733_, 0);
v___x_1736_ = v___x_1733_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v_a_1731_);
v___x_1736_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
v_val_1696_ = v___x_1736_;
goto v___jp_1695_;
}
}
}
v___jp_1683_:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1690_; 
v___x_1685_ = l_Lake_defaultConfigFile;
v___x_1686_ = lean_box(0);
v___x_1687_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1687_, 0, v_name_1598_);
lean_ctor_set(v___x_1687_, 1, v_scope_1599_);
lean_ctor_set(v___x_1687_, 2, v___x_1685_);
lean_ctor_set(v___x_1687_, 3, v___x_1686_);
lean_ctor_set(v___x_1687_, 4, v___x_1682_);
lean_ctor_set_uint8(v___x_1687_, sizeof(void*)*5, v_inherited_1557_);
v___x_1688_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1688_, 0, v_relPkgDir_1678_);
lean_ctor_set(v___x_1688_, 1, v___x_1680_);
lean_ctor_set(v___x_1688_, 2, v_a_1684_);
lean_ctor_set(v___x_1688_, 3, v___x_1687_);
if (v_isShared_1673_ == 0)
{
lean_ctor_set_tag(v___x_1672_, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1688_);
v___x_1690_ = v___x_1672_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v___x_1688_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
v___jp_1695_:
{
uint8_t v___x_1697_; 
v___x_1697_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_1697_ == 0)
{
v_a_1684_ = v_val_1696_;
goto v___jp_1683_;
}
else
{
lean_object* v___x_1698_; uint8_t v___x_1699_; 
v___x_1698_ = lean_box(0);
v___x_1699_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_1699_ == 0)
{
if (v___x_1697_ == 0)
{
v_a_1684_ = v_val_1696_;
goto v___jp_1683_;
}
else
{
size_t v___x_1700_; size_t v___x_1701_; lean_object* v___x_1702_; 
v___x_1700_ = ((size_t)0ULL);
v___x_1701_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_1702_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_1694_, v___x_1700_, v___x_1701_, v___x_1698_, v_a_1562_);
if (lean_obj_tag(v___x_1702_) == 0)
{
lean_dec_ref(v___x_1702_);
v_a_1684_ = v_val_1696_;
goto v___jp_1683_;
}
else
{
lean_object* v_a_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1710_; 
lean_dec_ref(v_val_1696_);
lean_dec_ref(v___x_1682_);
lean_dec_ref(v_relPkgDir_1678_);
lean_del_object(v___x_1672_);
lean_dec_ref(v_scope_1599_);
lean_dec(v_name_1598_);
v_a_1703_ = lean_ctor_get(v___x_1702_, 0);
v_isSharedCheck_1710_ = !lean_is_exclusive(v___x_1702_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1705_ = v___x_1702_;
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_a_1703_);
lean_dec(v___x_1702_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___x_1708_; 
if (v_isShared_1706_ == 0)
{
v___x_1708_ = v___x_1705_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v_a_1703_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
}
}
}
else
{
size_t v___x_1711_; size_t v___x_1712_; lean_object* v___x_1713_; 
v___x_1711_ = ((size_t)0ULL);
v___x_1712_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_1713_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_1694_, v___x_1711_, v___x_1712_, v___x_1698_, v_a_1562_);
if (lean_obj_tag(v___x_1713_) == 0)
{
lean_dec_ref(v___x_1713_);
v_a_1684_ = v_val_1696_;
goto v___jp_1683_;
}
else
{
lean_object* v_a_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1721_; 
lean_dec_ref(v_val_1696_);
lean_dec_ref(v___x_1682_);
lean_dec_ref(v_relPkgDir_1678_);
lean_del_object(v___x_1672_);
lean_dec_ref(v_scope_1599_);
lean_dec(v_name_1598_);
v_a_1714_ = lean_ctor_get(v___x_1713_, 0);
v_isSharedCheck_1721_ = !lean_is_exclusive(v___x_1713_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1716_ = v___x_1713_;
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_a_1714_);
lean_dec(v___x_1713_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1719_; 
if (v_isShared_1717_ == 0)
{
v___x_1719_ = v___x_1716_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_a_1714_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
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
lean_object* v_url_1741_; lean_object* v_rev_1742_; lean_object* v_subDir_1743_; uint8_t v___x_1744_; lean_object* v_sname_1745_; lean_object* v___y_1747_; lean_object* v___x_1750_; 
lean_del_object(v___x_1672_);
lean_dec_ref(v_relParentDir_1561_);
v_url_1741_ = lean_ctor_get(v_val_1670_, 0);
lean_inc_ref(v_url_1741_);
v_rev_1742_ = lean_ctor_get(v_val_1670_, 1);
lean_inc(v_rev_1742_);
v_subDir_1743_ = lean_ctor_get(v_val_1670_, 2);
lean_inc(v_subDir_1743_);
lean_dec_ref(v_val_1670_);
v___x_1744_ = 0;
lean_inc(v_name_1598_);
v_sname_1745_ = l_Lean_Name_toString(v_name_1598_, v___x_1744_);
lean_inc_ref(v_url_1741_);
v___x_1750_ = l_Lake_Git_filterUrl_x3f(v_url_1741_);
if (lean_obj_tag(v___x_1750_) == 0)
{
lean_object* v___x_1751_; 
v___x_1751_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___y_1747_ = v___x_1751_;
goto v___jp_1746_;
}
else
{
lean_object* v_val_1752_; 
v_val_1752_ = lean_ctor_get(v___x_1750_, 0);
lean_inc(v_val_1752_);
lean_dec_ref(v___x_1750_);
v___y_1747_ = v_val_1752_;
goto v___jp_1746_;
}
v___jp_1746_:
{
lean_object* v___x_1748_; lean_object* v___x_1749_; 
lean_inc_ref(v_sname_1745_);
v___x_1748_ = l_Lake_joinRelative(v_relPkgsDir_1560_, v_sname_1745_);
v___x_1749_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(v_a_1562_, v_dep_1556_, v_inherited_1557_, v_lakeEnv_1558_, v_wsDir_1559_, v_sname_1745_, v___x_1748_, v_url_1741_, v___y_1747_, v_rev_1742_, v_subDir_1743_);
lean_dec_ref(v_lakeEnv_1558_);
lean_dec_ref(v_dep_1556_);
return v___x_1749_;
}
}
}
}
else
{
lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___y_1757_; lean_object* v___y_1758_; lean_object* v___y_1759_; lean_object* v___y_1760_; lean_object* v___y_1761_; lean_object* v___y_1762_; lean_object* v___y_1763_; lean_object* v_fst_1764_; lean_object* v_snd_1765_; lean_object* v___y_1793_; lean_object* v___y_1794_; lean_object* v_a_1795_; lean_object* v___y_1928_; lean_object* v___y_1929_; lean_object* v_fst_1930_; lean_object* v_snd_1931_; uint8_t v___x_1958_; lean_object* v_a_1960_; 
lean_dec(v_src_x3f_1601_);
lean_dec_ref(v_relParentDir_1561_);
v___x_1754_ = lean_string_utf8_byte_size(v_scope_1599_);
v___x_1755_ = lean_unsigned_to_nat(0u);
v___x_1958_ = lean_nat_dec_eq(v___x_1754_, v___x_1755_);
if (v___x_1958_ == 0)
{
if (lean_obj_tag(v_version_x3f_1600_) == 1)
{
lean_object* v_val_1970_; lean_object* v___x_1971_; 
v_val_1970_ = lean_ctor_get(v_version_x3f_1600_, 0);
lean_inc(v_val_1970_);
v___x_1971_ = l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg(v_val_1970_);
if (lean_obj_tag(v___x_1971_) == 1)
{
lean_object* v_val_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1980_; 
v_val_1972_ = lean_ctor_get(v___x_1971_, 0);
v_isSharedCheck_1980_ = !lean_is_exclusive(v___x_1971_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1974_ = v___x_1971_;
v_isShared_1975_ = v_isSharedCheck_1980_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_val_1972_);
lean_dec(v___x_1971_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_1980_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v___x_1976_; lean_object* v___x_1978_; 
v___x_1976_ = l_String_Slice_toString(v_val_1972_);
lean_dec(v_val_1972_);
if (v_isShared_1975_ == 0)
{
lean_ctor_set(v___x_1974_, 0, v___x_1976_);
v___x_1978_ = v___x_1974_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v___x_1976_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
v_a_1960_ = v___x_1978_;
goto v___jp_1959_;
}
}
}
else
{
lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; 
lean_dec(v___x_1971_);
v___x_1981_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__8));
v___x_1982_ = lean_string_utf8_byte_size(v_val_1970_);
lean_inc(v_val_1970_);
v___x_1983_ = l___private_Lake_Util_Version_0__Lake_runVerParse(lean_box(0), v_val_1970_, v___x_1981_, v___x_1755_, v___x_1982_);
if (lean_obj_tag(v___x_1983_) == 0)
{
lean_object* v_a_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_2000_; 
lean_inc(v_name_1598_);
lean_dec_ref(v_relPkgsDir_1560_);
lean_dec_ref(v_wsDir_1559_);
lean_dec_ref(v_lakeEnv_1558_);
lean_dec_ref(v_dep_1556_);
v_a_1984_ = lean_ctor_get(v___x_1983_, 0);
v_isSharedCheck_2000_ = !lean_is_exclusive(v___x_1983_);
if (v_isSharedCheck_2000_ == 0)
{
v___x_1986_ = v___x_1983_;
v_isShared_1987_ = v_isSharedCheck_2000_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_a_1984_);
lean_dec(v___x_1983_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_2000_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
uint8_t v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; uint8_t v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1998_; 
v___x_1988_ = 1;
v___x_1989_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1598_, v___x_1988_);
v___x_1990_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__9));
v___x_1991_ = lean_string_append(v___x_1989_, v___x_1990_);
v___x_1992_ = lean_string_append(v___x_1991_, v_a_1984_);
lean_dec(v_a_1984_);
v___x_1993_ = 3;
v___x_1994_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1994_, 0, v___x_1992_);
lean_ctor_set_uint8(v___x_1994_, sizeof(void*)*1, v___x_1993_);
lean_inc_ref(v_a_1562_);
v___x_1995_ = lean_apply_2(v_a_1562_, v___x_1994_, lean_box(0));
v___x_1996_ = lean_box(0);
if (v_isShared_1987_ == 0)
{
lean_ctor_set_tag(v___x_1986_, 1);
lean_ctor_set(v___x_1986_, 0, v___x_1996_);
v___x_1998_ = v___x_1986_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v___x_1996_);
v___x_1998_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
return v___x_1998_;
}
}
}
else
{
lean_object* v_a_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2008_; 
v_a_2001_ = lean_ctor_get(v___x_1983_, 0);
v_isSharedCheck_2008_ = !lean_is_exclusive(v___x_1983_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_2003_ = v___x_1983_;
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_a_2001_);
lean_dec(v___x_1983_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2006_; 
if (v_isShared_2004_ == 0)
{
lean_ctor_set_tag(v___x_2003_, 2);
v___x_2006_ = v___x_2003_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v_a_2001_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
v_a_1960_ = v___x_2006_;
goto v___jp_1959_;
}
}
}
}
}
else
{
lean_object* v___x_2009_; 
v___x_2009_ = lean_box(0);
v_a_1960_ = v___x_2009_;
goto v___jp_1959_;
}
}
else
{
lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; uint8_t v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; 
lean_inc(v_name_1598_);
lean_dec_ref(v_relPkgsDir_1560_);
lean_dec_ref(v_wsDir_1559_);
lean_dec_ref(v_lakeEnv_1558_);
lean_dec_ref(v_dep_1556_);
v___x_2010_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1598_, v___x_1958_);
v___x_2011_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__10));
v___x_2012_ = lean_string_append(v___x_2010_, v___x_2011_);
v___x_2013_ = 3;
v___x_2014_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2014_, 0, v___x_2012_);
lean_ctor_set_uint8(v___x_2014_, sizeof(void*)*1, v___x_2013_);
lean_inc_ref(v_a_1562_);
v___x_2015_ = lean_apply_2(v_a_1562_, v___x_2014_, lean_box(0));
v___x_2016_ = lean_box(0);
v___x_2017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2017_, 0, v___x_2016_);
return v___x_2017_;
}
v___jp_1756_:
{
lean_object* v___x_1766_; uint8_t v___x_1767_; 
v___x_1766_ = lean_array_get_size(v_snd_1765_);
v___x_1767_ = lean_nat_dec_lt(v___x_1755_, v___x_1766_);
if (v___x_1767_ == 0)
{
lean_dec_ref(v_snd_1765_);
v___y_1620_ = v___y_1757_;
v___y_1621_ = v___y_1758_;
v___y_1622_ = v___y_1759_;
v___y_1623_ = v___y_1761_;
v___y_1624_ = v___y_1760_;
v___y_1625_ = v___y_1762_;
v___y_1626_ = v___y_1763_;
v_a_1627_ = v_fst_1764_;
goto v___jp_1619_;
}
else
{
lean_object* v___x_1768_; uint8_t v___x_1769_; 
v___x_1768_ = lean_box(0);
v___x_1769_ = lean_nat_dec_le(v___x_1766_, v___x_1766_);
if (v___x_1769_ == 0)
{
if (v___x_1767_ == 0)
{
lean_dec_ref(v_snd_1765_);
v___y_1620_ = v___y_1757_;
v___y_1621_ = v___y_1758_;
v___y_1622_ = v___y_1759_;
v___y_1623_ = v___y_1761_;
v___y_1624_ = v___y_1760_;
v___y_1625_ = v___y_1762_;
v___y_1626_ = v___y_1763_;
v_a_1627_ = v_fst_1764_;
goto v___jp_1619_;
}
else
{
size_t v___x_1770_; size_t v___x_1771_; lean_object* v___x_1772_; 
v___x_1770_ = ((size_t)0ULL);
v___x_1771_ = lean_usize_of_nat(v___x_1766_);
v___x_1772_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_snd_1765_, v___x_1770_, v___x_1771_, v___x_1768_, v_a_1562_);
lean_dec_ref(v_snd_1765_);
if (lean_obj_tag(v___x_1772_) == 0)
{
lean_dec_ref(v___x_1772_);
v___y_1620_ = v___y_1757_;
v___y_1621_ = v___y_1758_;
v___y_1622_ = v___y_1759_;
v___y_1623_ = v___y_1761_;
v___y_1624_ = v___y_1760_;
v___y_1625_ = v___y_1762_;
v___y_1626_ = v___y_1763_;
v_a_1627_ = v_fst_1764_;
goto v___jp_1619_;
}
else
{
lean_object* v_a_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1780_; 
lean_dec_ref(v_fst_1764_);
lean_dec_ref(v___y_1763_);
lean_dec(v___y_1762_);
lean_dec(v___y_1761_);
lean_dec_ref(v___y_1760_);
lean_dec_ref(v___y_1759_);
lean_dec_ref(v___y_1758_);
lean_dec_ref(v___y_1757_);
lean_dec_ref(v_wsDir_1559_);
lean_dec_ref(v_lakeEnv_1558_);
lean_dec_ref(v_dep_1556_);
v_a_1773_ = lean_ctor_get(v___x_1772_, 0);
v_isSharedCheck_1780_ = !lean_is_exclusive(v___x_1772_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1775_ = v___x_1772_;
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_a_1773_);
lean_dec(v___x_1772_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1778_; 
if (v_isShared_1776_ == 0)
{
v___x_1778_ = v___x_1775_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_a_1773_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
return v___x_1778_;
}
}
}
}
}
else
{
size_t v___x_1781_; size_t v___x_1782_; lean_object* v___x_1783_; 
v___x_1781_ = ((size_t)0ULL);
v___x_1782_ = lean_usize_of_nat(v___x_1766_);
v___x_1783_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_snd_1765_, v___x_1781_, v___x_1782_, v___x_1768_, v_a_1562_);
lean_dec_ref(v_snd_1765_);
if (lean_obj_tag(v___x_1783_) == 0)
{
lean_dec_ref(v___x_1783_);
v___y_1620_ = v___y_1757_;
v___y_1621_ = v___y_1758_;
v___y_1622_ = v___y_1759_;
v___y_1623_ = v___y_1761_;
v___y_1624_ = v___y_1760_;
v___y_1625_ = v___y_1762_;
v___y_1626_ = v___y_1763_;
v_a_1627_ = v_fst_1764_;
goto v___jp_1619_;
}
else
{
lean_object* v_a_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1791_; 
lean_dec_ref(v_fst_1764_);
lean_dec_ref(v___y_1763_);
lean_dec(v___y_1762_);
lean_dec(v___y_1761_);
lean_dec_ref(v___y_1760_);
lean_dec_ref(v___y_1759_);
lean_dec_ref(v___y_1758_);
lean_dec_ref(v___y_1757_);
lean_dec_ref(v_wsDir_1559_);
lean_dec_ref(v_lakeEnv_1558_);
lean_dec_ref(v_dep_1556_);
v_a_1784_ = lean_ctor_get(v___x_1783_, 0);
v_isSharedCheck_1791_ = !lean_is_exclusive(v___x_1783_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1786_ = v___x_1783_;
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_a_1784_);
lean_dec(v___x_1783_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
lean_object* v___x_1789_; 
if (v_isShared_1787_ == 0)
{
v___x_1789_ = v___x_1786_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_a_1784_);
v___x_1789_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
return v___x_1789_;
}
}
}
}
}
}
v___jp_1792_:
{
if (lean_obj_tag(v_a_1795_) == 0)
{
lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; uint8_t v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
lean_inc_ref(v_scope_1599_);
lean_dec_ref(v_a_1795_);
lean_dec(v___y_1794_);
lean_dec_ref(v_relPkgsDir_1560_);
lean_dec_ref(v_wsDir_1559_);
lean_dec_ref(v_lakeEnv_1558_);
lean_dec_ref(v_dep_1556_);
v___x_1796_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
v___x_1797_ = lean_string_append(v_scope_1599_, v___x_1796_);
v___x_1798_ = lean_string_append(v___x_1797_, v___y_1793_);
lean_dec_ref(v___y_1793_);
v___x_1799_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__7));
v___x_1800_ = lean_string_append(v___x_1798_, v___x_1799_);
v___x_1801_ = 3;
v___x_1802_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1802_, 0, v___x_1800_);
lean_ctor_set_uint8(v___x_1802_, sizeof(void*)*1, v___x_1801_);
lean_inc_ref(v_a_1562_);
v___x_1803_ = lean_apply_2(v_a_1562_, v___x_1802_, lean_box(0));
v___x_1804_ = lean_box(0);
v___x_1805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1805_, 0, v___x_1804_);
return v___x_1805_;
}
else
{
lean_object* v_a_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1926_; 
v_a_1806_ = lean_ctor_get(v_a_1795_, 0);
v_isSharedCheck_1926_ = !lean_is_exclusive(v_a_1795_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1808_ = v_a_1795_;
v_isShared_1809_ = v_isSharedCheck_1926_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_a_1806_);
lean_dec(v_a_1795_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1926_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
if (lean_obj_tag(v_a_1806_) == 0)
{
lean_object* v___x_1810_; uint8_t v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; 
lean_inc_ref(v_scope_1599_);
lean_del_object(v___x_1808_);
lean_dec_ref(v_relPkgsDir_1560_);
lean_dec_ref(v_wsDir_1559_);
lean_dec_ref(v_lakeEnv_1558_);
lean_dec_ref(v_dep_1556_);
v___x_1810_ = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed(v_scope_1599_, v___y_1793_, v___y_1794_);
lean_dec_ref(v___y_1793_);
v___x_1811_ = 3;
v___x_1812_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1812_, 0, v___x_1810_);
lean_ctor_set_uint8(v___x_1812_, sizeof(void*)*1, v___x_1811_);
lean_inc_ref(v_a_1562_);
v___x_1813_ = lean_apply_2(v_a_1562_, v___x_1812_, lean_box(0));
v___x_1814_ = lean_box(0);
v___x_1815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1815_, 0, v___x_1814_);
return v___x_1815_;
}
else
{
lean_object* v_val_1816_; lean_object* v___x_1817_; 
v_val_1816_ = lean_ctor_get(v_a_1806_, 0);
lean_inc(v_val_1816_);
lean_dec_ref(v_a_1806_);
v___x_1817_ = l_Lake_RegistryPkg_gitSrc_x3f(v_val_1816_);
if (lean_obj_tag(v___x_1817_) == 1)
{
lean_object* v_val_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1925_; 
v_val_1818_ = lean_ctor_get(v___x_1817_, 0);
v_isSharedCheck_1925_ = !lean_is_exclusive(v___x_1817_);
if (v_isSharedCheck_1925_ == 0)
{
v___x_1820_ = v___x_1817_;
v_isShared_1821_ = v_isSharedCheck_1925_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_val_1818_);
lean_dec(v___x_1817_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1925_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
if (lean_obj_tag(v_val_1818_) == 0)
{
lean_object* v_url_1822_; lean_object* v_githubUrl_x3f_1823_; lean_object* v_defaultBranch_x3f_1824_; lean_object* v_subDir_x3f_1825_; lean_object* v_name_1826_; lean_object* v_fullName_1827_; lean_object* v___x_1828_; 
v_url_1822_ = lean_ctor_get(v_val_1818_, 1);
lean_inc_ref(v_url_1822_);
v_githubUrl_x3f_1823_ = lean_ctor_get(v_val_1818_, 2);
lean_inc(v_githubUrl_x3f_1823_);
v_defaultBranch_x3f_1824_ = lean_ctor_get(v_val_1818_, 3);
lean_inc(v_defaultBranch_x3f_1824_);
v_subDir_x3f_1825_ = lean_ctor_get(v_val_1818_, 4);
lean_inc(v_subDir_x3f_1825_);
lean_dec_ref(v_val_1818_);
v_name_1826_ = lean_ctor_get(v_val_1816_, 0);
lean_inc_ref(v_name_1826_);
v_fullName_1827_ = lean_ctor_get(v_val_1816_, 1);
lean_inc_ref(v_fullName_1827_);
lean_dec(v_val_1816_);
v___x_1828_ = l_Lake_joinRelative(v_relPkgsDir_1560_, v_name_1826_);
switch(lean_obj_tag(v___y_1794_))
{
case 0:
{
lean_object* v___x_1829_; 
lean_del_object(v___x_1808_);
lean_dec_ref(v___y_1793_);
v___x_1829_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
if (lean_obj_tag(v_defaultBranch_x3f_1824_) == 0)
{
uint8_t v___x_1830_; 
lean_dec_ref(v___x_1828_);
lean_dec_ref(v_fullName_1827_);
lean_dec(v_subDir_x3f_1825_);
lean_dec(v_githubUrl_x3f_1823_);
lean_dec_ref(v_url_1822_);
lean_dec_ref(v_wsDir_1559_);
lean_dec_ref(v_lakeEnv_1558_);
lean_dec_ref(v_dep_1556_);
v___x_1830_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_1830_ == 0)
{
lean_object* v___x_1831_; lean_object* v___x_1833_; 
v___x_1831_ = lean_box(0);
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 0, v___x_1831_);
v___x_1833_ = v___x_1820_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v___x_1831_);
v___x_1833_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
return v___x_1833_;
}
}
else
{
lean_object* v___x_1835_; uint8_t v___x_1836_; 
lean_del_object(v___x_1820_);
v___x_1835_ = lean_box(0);
v___x_1836_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_1836_ == 0)
{
if (v___x_1830_ == 0)
{
goto v___jp_1564_;
}
else
{
size_t v___x_1837_; size_t v___x_1838_; lean_object* v___x_1839_; 
v___x_1837_ = ((size_t)0ULL);
v___x_1838_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_1839_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_1829_, v___x_1837_, v___x_1838_, v___x_1835_, v_a_1562_);
if (lean_obj_tag(v___x_1839_) == 0)
{
lean_dec_ref(v___x_1839_);
goto v___jp_1564_;
}
else
{
lean_object* v_a_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1847_; 
v_a_1840_ = lean_ctor_get(v___x_1839_, 0);
v_isSharedCheck_1847_ = !lean_is_exclusive(v___x_1839_);
if (v_isSharedCheck_1847_ == 0)
{
v___x_1842_ = v___x_1839_;
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_a_1840_);
lean_dec(v___x_1839_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v___x_1845_; 
if (v_isShared_1843_ == 0)
{
v___x_1845_ = v___x_1842_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v_a_1840_);
v___x_1845_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
return v___x_1845_;
}
}
}
}
}
else
{
size_t v___x_1848_; size_t v___x_1849_; lean_object* v___x_1850_; 
v___x_1848_ = ((size_t)0ULL);
v___x_1849_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_1850_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_1829_, v___x_1848_, v___x_1849_, v___x_1835_, v_a_1562_);
if (lean_obj_tag(v___x_1850_) == 0)
{
lean_dec_ref(v___x_1850_);
goto v___jp_1564_;
}
else
{
lean_object* v_a_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1858_; 
v_a_1851_ = lean_ctor_get(v___x_1850_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1853_ = v___x_1850_;
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_a_1851_);
lean_dec(v___x_1850_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1856_; 
if (v_isShared_1854_ == 0)
{
v___x_1856_ = v___x_1853_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_a_1851_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
return v___x_1856_;
}
}
}
}
}
}
else
{
lean_object* v_val_1859_; uint8_t v___x_1860_; 
lean_del_object(v___x_1820_);
v_val_1859_ = lean_ctor_get(v_defaultBranch_x3f_1824_, 0);
lean_inc(v_val_1859_);
lean_dec_ref(v_defaultBranch_x3f_1824_);
v___x_1860_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_1860_ == 0)
{
v___y_1589_ = v___x_1828_;
v___y_1590_ = v_fullName_1827_;
v___y_1591_ = v_githubUrl_x3f_1823_;
v___y_1592_ = v_subDir_x3f_1825_;
v___y_1593_ = v_url_1822_;
v_rev_x3f_1594_ = v_val_1859_;
v___y_1595_ = v_a_1562_;
goto v___jp_1588_;
}
else
{
lean_object* v___x_1861_; uint8_t v___x_1862_; 
v___x_1861_ = lean_box(0);
v___x_1862_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_1862_ == 0)
{
if (v___x_1860_ == 0)
{
v___y_1589_ = v___x_1828_;
v___y_1590_ = v_fullName_1827_;
v___y_1591_ = v_githubUrl_x3f_1823_;
v___y_1592_ = v_subDir_x3f_1825_;
v___y_1593_ = v_url_1822_;
v_rev_x3f_1594_ = v_val_1859_;
v___y_1595_ = v_a_1562_;
goto v___jp_1588_;
}
else
{
size_t v___x_1863_; size_t v___x_1864_; lean_object* v___x_1865_; 
v___x_1863_ = ((size_t)0ULL);
v___x_1864_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_1865_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_1829_, v___x_1863_, v___x_1864_, v___x_1861_, v_a_1562_);
if (lean_obj_tag(v___x_1865_) == 0)
{
lean_dec_ref(v___x_1865_);
v___y_1589_ = v___x_1828_;
v___y_1590_ = v_fullName_1827_;
v___y_1591_ = v_githubUrl_x3f_1823_;
v___y_1592_ = v_subDir_x3f_1825_;
v___y_1593_ = v_url_1822_;
v_rev_x3f_1594_ = v_val_1859_;
v___y_1595_ = v_a_1562_;
goto v___jp_1588_;
}
else
{
lean_object* v_a_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1873_; 
lean_dec(v_val_1859_);
lean_dec_ref(v___x_1828_);
lean_dec_ref(v_fullName_1827_);
lean_dec(v_subDir_x3f_1825_);
lean_dec(v_githubUrl_x3f_1823_);
lean_dec_ref(v_url_1822_);
lean_dec_ref(v_wsDir_1559_);
lean_dec_ref(v_lakeEnv_1558_);
lean_dec_ref(v_dep_1556_);
v_a_1866_ = lean_ctor_get(v___x_1865_, 0);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1865_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1868_ = v___x_1865_;
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_a_1866_);
lean_dec(v___x_1865_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v___x_1871_; 
if (v_isShared_1869_ == 0)
{
v___x_1871_ = v___x_1868_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_a_1866_);
v___x_1871_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
return v___x_1871_;
}
}
}
}
}
else
{
size_t v___x_1874_; size_t v___x_1875_; lean_object* v___x_1876_; 
v___x_1874_ = ((size_t)0ULL);
v___x_1875_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_1876_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_1829_, v___x_1874_, v___x_1875_, v___x_1861_, v_a_1562_);
if (lean_obj_tag(v___x_1876_) == 0)
{
lean_dec_ref(v___x_1876_);
v___y_1589_ = v___x_1828_;
v___y_1590_ = v_fullName_1827_;
v___y_1591_ = v_githubUrl_x3f_1823_;
v___y_1592_ = v_subDir_x3f_1825_;
v___y_1593_ = v_url_1822_;
v_rev_x3f_1594_ = v_val_1859_;
v___y_1595_ = v_a_1562_;
goto v___jp_1588_;
}
else
{
lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1884_; 
lean_dec(v_val_1859_);
lean_dec_ref(v___x_1828_);
lean_dec_ref(v_fullName_1827_);
lean_dec(v_subDir_x3f_1825_);
lean_dec(v_githubUrl_x3f_1823_);
lean_dec_ref(v_url_1822_);
lean_dec_ref(v_wsDir_1559_);
lean_dec_ref(v_lakeEnv_1558_);
lean_dec_ref(v_dep_1556_);
v_a_1877_ = lean_ctor_get(v___x_1876_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1879_ = v___x_1876_;
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_dec(v___x_1876_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1882_; 
if (v_isShared_1880_ == 0)
{
v___x_1882_ = v___x_1879_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_a_1877_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
}
}
}
}
}
case 1:
{
lean_object* v_rev_1885_; lean_object* v___x_1886_; uint8_t v___x_1887_; 
lean_dec(v_defaultBranch_x3f_1824_);
lean_del_object(v___x_1820_);
lean_del_object(v___x_1808_);
lean_dec_ref(v___y_1793_);
v_rev_1885_ = lean_ctor_get(v___y_1794_, 0);
lean_inc_ref(v_rev_1885_);
lean_dec_ref(v___y_1794_);
v___x_1886_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
v___x_1887_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_1887_ == 0)
{
v___y_1589_ = v___x_1828_;
v___y_1590_ = v_fullName_1827_;
v___y_1591_ = v_githubUrl_x3f_1823_;
v___y_1592_ = v_subDir_x3f_1825_;
v___y_1593_ = v_url_1822_;
v_rev_x3f_1594_ = v_rev_1885_;
v___y_1595_ = v_a_1562_;
goto v___jp_1588_;
}
else
{
lean_object* v___x_1888_; uint8_t v___x_1889_; 
v___x_1888_ = lean_box(0);
v___x_1889_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_1889_ == 0)
{
if (v___x_1887_ == 0)
{
v___y_1589_ = v___x_1828_;
v___y_1590_ = v_fullName_1827_;
v___y_1591_ = v_githubUrl_x3f_1823_;
v___y_1592_ = v_subDir_x3f_1825_;
v___y_1593_ = v_url_1822_;
v_rev_x3f_1594_ = v_rev_1885_;
v___y_1595_ = v_a_1562_;
goto v___jp_1588_;
}
else
{
size_t v___x_1890_; size_t v___x_1891_; lean_object* v___x_1892_; 
v___x_1890_ = ((size_t)0ULL);
v___x_1891_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_1892_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_1886_, v___x_1890_, v___x_1891_, v___x_1888_, v_a_1562_);
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_dec_ref(v___x_1892_);
v___y_1589_ = v___x_1828_;
v___y_1590_ = v_fullName_1827_;
v___y_1591_ = v_githubUrl_x3f_1823_;
v___y_1592_ = v_subDir_x3f_1825_;
v___y_1593_ = v_url_1822_;
v_rev_x3f_1594_ = v_rev_1885_;
v___y_1595_ = v_a_1562_;
goto v___jp_1588_;
}
else
{
lean_object* v_a_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1900_; 
lean_dec_ref(v_rev_1885_);
lean_dec_ref(v___x_1828_);
lean_dec_ref(v_fullName_1827_);
lean_dec(v_subDir_x3f_1825_);
lean_dec(v_githubUrl_x3f_1823_);
lean_dec_ref(v_url_1822_);
lean_dec_ref(v_wsDir_1559_);
lean_dec_ref(v_lakeEnv_1558_);
lean_dec_ref(v_dep_1556_);
v_a_1893_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1900_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1895_ = v___x_1892_;
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_a_1893_);
lean_dec(v___x_1892_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___x_1898_; 
if (v_isShared_1896_ == 0)
{
v___x_1898_ = v___x_1895_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_a_1893_);
v___x_1898_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
return v___x_1898_;
}
}
}
}
}
else
{
size_t v___x_1901_; size_t v___x_1902_; lean_object* v___x_1903_; 
v___x_1901_ = ((size_t)0ULL);
v___x_1902_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_1903_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_1886_, v___x_1901_, v___x_1902_, v___x_1888_, v_a_1562_);
if (lean_obj_tag(v___x_1903_) == 0)
{
lean_dec_ref(v___x_1903_);
v___y_1589_ = v___x_1828_;
v___y_1590_ = v_fullName_1827_;
v___y_1591_ = v_githubUrl_x3f_1823_;
v___y_1592_ = v_subDir_x3f_1825_;
v___y_1593_ = v_url_1822_;
v_rev_x3f_1594_ = v_rev_1885_;
v___y_1595_ = v_a_1562_;
goto v___jp_1588_;
}
else
{
lean_object* v_a_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1911_; 
lean_dec_ref(v_rev_1885_);
lean_dec_ref(v___x_1828_);
lean_dec_ref(v_fullName_1827_);
lean_dec(v_subDir_x3f_1825_);
lean_dec(v_githubUrl_x3f_1823_);
lean_dec_ref(v_url_1822_);
lean_dec_ref(v_wsDir_1559_);
lean_dec_ref(v_lakeEnv_1558_);
lean_dec_ref(v_dep_1556_);
v_a_1904_ = lean_ctor_get(v___x_1903_, 0);
v_isSharedCheck_1911_ = !lean_is_exclusive(v___x_1903_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1906_ = v___x_1903_;
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_a_1904_);
lean_dec(v___x_1903_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v___x_1909_; 
if (v_isShared_1907_ == 0)
{
v___x_1909_ = v___x_1906_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v_a_1904_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
}
}
}
}
default: 
{
lean_object* v_ver_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; 
lean_dec(v_defaultBranch_x3f_1824_);
lean_del_object(v___x_1820_);
v_ver_1912_ = lean_ctor_get(v___y_1794_, 0);
lean_inc_ref(v_ver_1912_);
lean_dec_ref(v___y_1794_);
v___x_1913_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
lean_inc_ref(v___y_1793_);
lean_inc_ref(v_scope_1599_);
lean_inc_ref(v_lakeEnv_1558_);
v___x_1914_ = l_Lake_Reservoir_fetchPkgVersions(v_lakeEnv_1558_, v_scope_1599_, v___y_1793_, v___x_1913_);
if (lean_obj_tag(v___x_1914_) == 0)
{
lean_object* v_a_1915_; lean_object* v_a_1916_; lean_object* v___x_1918_; 
v_a_1915_ = lean_ctor_get(v___x_1914_, 0);
lean_inc(v_a_1915_);
v_a_1916_ = lean_ctor_get(v___x_1914_, 1);
lean_inc(v_a_1916_);
lean_dec_ref(v___x_1914_);
if (v_isShared_1809_ == 0)
{
lean_ctor_set(v___x_1808_, 0, v_a_1915_);
v___x_1918_ = v___x_1808_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_a_1915_);
v___x_1918_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
v___y_1757_ = v___x_1828_;
v___y_1758_ = v_fullName_1827_;
v___y_1759_ = v_ver_1912_;
v___y_1760_ = v___y_1793_;
v___y_1761_ = v_githubUrl_x3f_1823_;
v___y_1762_ = v_subDir_x3f_1825_;
v___y_1763_ = v_url_1822_;
v_fst_1764_ = v___x_1918_;
v_snd_1765_ = v_a_1916_;
goto v___jp_1756_;
}
}
else
{
lean_object* v_a_1920_; lean_object* v_a_1921_; lean_object* v___x_1923_; 
v_a_1920_ = lean_ctor_get(v___x_1914_, 0);
lean_inc(v_a_1920_);
v_a_1921_ = lean_ctor_get(v___x_1914_, 1);
lean_inc(v_a_1921_);
lean_dec_ref(v___x_1914_);
if (v_isShared_1809_ == 0)
{
lean_ctor_set_tag(v___x_1808_, 0);
lean_ctor_set(v___x_1808_, 0, v_a_1920_);
v___x_1923_ = v___x_1808_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v_a_1920_);
v___x_1923_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
v___y_1757_ = v___x_1828_;
v___y_1758_ = v_fullName_1827_;
v___y_1759_ = v_ver_1912_;
v___y_1760_ = v___y_1793_;
v___y_1761_ = v_githubUrl_x3f_1823_;
v___y_1762_ = v_subDir_x3f_1825_;
v___y_1763_ = v_url_1822_;
v_fst_1764_ = v___x_1923_;
v_snd_1765_ = v_a_1921_;
goto v___jp_1756_;
}
}
}
}
}
else
{
lean_del_object(v___x_1820_);
lean_dec(v_val_1818_);
lean_del_object(v___x_1808_);
lean_dec(v___y_1794_);
lean_dec_ref(v___y_1793_);
lean_dec_ref(v_relPkgsDir_1560_);
lean_dec_ref(v_wsDir_1559_);
lean_dec_ref(v_lakeEnv_1558_);
lean_dec_ref(v_dep_1556_);
v___y_1568_ = v_val_1816_;
v___y_1569_ = v_a_1562_;
goto v___jp_1567_;
}
}
}
else
{
lean_dec(v___x_1817_);
lean_del_object(v___x_1808_);
lean_dec(v___y_1794_);
lean_dec_ref(v___y_1793_);
lean_dec_ref(v_relPkgsDir_1560_);
lean_dec_ref(v_wsDir_1559_);
lean_dec_ref(v_lakeEnv_1558_);
lean_dec_ref(v_dep_1556_);
v___y_1568_ = v_val_1816_;
v___y_1569_ = v_a_1562_;
goto v___jp_1567_;
}
}
}
}
}
v___jp_1927_:
{
lean_object* v___x_1932_; uint8_t v___x_1933_; 
v___x_1932_ = lean_array_get_size(v_snd_1931_);
v___x_1933_ = lean_nat_dec_lt(v___x_1755_, v___x_1932_);
if (v___x_1933_ == 0)
{
lean_dec_ref(v_snd_1931_);
v___y_1793_ = v___y_1928_;
v___y_1794_ = v___y_1929_;
v_a_1795_ = v_fst_1930_;
goto v___jp_1792_;
}
else
{
lean_object* v___x_1934_; uint8_t v___x_1935_; 
v___x_1934_ = lean_box(0);
v___x_1935_ = lean_nat_dec_le(v___x_1932_, v___x_1932_);
if (v___x_1935_ == 0)
{
if (v___x_1933_ == 0)
{
lean_dec_ref(v_snd_1931_);
v___y_1793_ = v___y_1928_;
v___y_1794_ = v___y_1929_;
v_a_1795_ = v_fst_1930_;
goto v___jp_1792_;
}
else
{
size_t v___x_1936_; size_t v___x_1937_; lean_object* v___x_1938_; 
v___x_1936_ = ((size_t)0ULL);
v___x_1937_ = lean_usize_of_nat(v___x_1932_);
v___x_1938_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_snd_1931_, v___x_1936_, v___x_1937_, v___x_1934_, v_a_1562_);
lean_dec_ref(v_snd_1931_);
if (lean_obj_tag(v___x_1938_) == 0)
{
lean_dec_ref(v___x_1938_);
v___y_1793_ = v___y_1928_;
v___y_1794_ = v___y_1929_;
v_a_1795_ = v_fst_1930_;
goto v___jp_1792_;
}
else
{
lean_object* v_a_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1946_; 
lean_dec_ref(v_fst_1930_);
lean_dec(v___y_1929_);
lean_dec_ref(v___y_1928_);
lean_dec_ref(v_relPkgsDir_1560_);
lean_dec_ref(v_wsDir_1559_);
lean_dec_ref(v_lakeEnv_1558_);
lean_dec_ref(v_dep_1556_);
v_a_1939_ = lean_ctor_get(v___x_1938_, 0);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1938_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1941_ = v___x_1938_;
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_a_1939_);
lean_dec(v___x_1938_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___x_1944_; 
if (v_isShared_1942_ == 0)
{
v___x_1944_ = v___x_1941_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_a_1939_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
return v___x_1944_;
}
}
}
}
}
else
{
size_t v___x_1947_; size_t v___x_1948_; lean_object* v___x_1949_; 
v___x_1947_ = ((size_t)0ULL);
v___x_1948_ = lean_usize_of_nat(v___x_1932_);
v___x_1949_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_snd_1931_, v___x_1947_, v___x_1948_, v___x_1934_, v_a_1562_);
lean_dec_ref(v_snd_1931_);
if (lean_obj_tag(v___x_1949_) == 0)
{
lean_dec_ref(v___x_1949_);
v___y_1793_ = v___y_1928_;
v___y_1794_ = v___y_1929_;
v_a_1795_ = v_fst_1930_;
goto v___jp_1792_;
}
else
{
lean_object* v_a_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1957_; 
lean_dec_ref(v_fst_1930_);
lean_dec(v___y_1929_);
lean_dec_ref(v___y_1928_);
lean_dec_ref(v_relPkgsDir_1560_);
lean_dec_ref(v_wsDir_1559_);
lean_dec_ref(v_lakeEnv_1558_);
lean_dec_ref(v_dep_1556_);
v_a_1950_ = lean_ctor_get(v___x_1949_, 0);
v_isSharedCheck_1957_ = !lean_is_exclusive(v___x_1949_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1952_ = v___x_1949_;
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_a_1950_);
lean_dec(v___x_1949_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1955_; 
if (v_isShared_1953_ == 0)
{
v___x_1955_ = v___x_1952_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v_a_1950_);
v___x_1955_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
return v___x_1955_;
}
}
}
}
}
}
v___jp_1959_:
{
lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; 
lean_inc(v_name_1598_);
v___x_1961_ = l_Lean_Name_toString(v_name_1598_, v___x_1958_);
v___x_1962_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
lean_inc_ref(v___x_1961_);
lean_inc_ref(v_scope_1599_);
lean_inc_ref(v_lakeEnv_1558_);
v___x_1963_ = l_Lake_Reservoir_fetchPkg_x3f(v_lakeEnv_1558_, v_scope_1599_, v___x_1961_, v___x_1962_);
if (lean_obj_tag(v___x_1963_) == 0)
{
lean_object* v_a_1964_; lean_object* v_a_1965_; lean_object* v___x_1966_; 
v_a_1964_ = lean_ctor_get(v___x_1963_, 0);
lean_inc(v_a_1964_);
v_a_1965_ = lean_ctor_get(v___x_1963_, 1);
lean_inc(v_a_1965_);
lean_dec_ref(v___x_1963_);
v___x_1966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1966_, 0, v_a_1964_);
v___y_1928_ = v___x_1961_;
v___y_1929_ = v_a_1960_;
v_fst_1930_ = v___x_1966_;
v_snd_1931_ = v_a_1965_;
goto v___jp_1927_;
}
else
{
lean_object* v_a_1967_; lean_object* v_a_1968_; lean_object* v___x_1969_; 
v_a_1967_ = lean_ctor_get(v___x_1963_, 0);
lean_inc(v_a_1967_);
v_a_1968_ = lean_ctor_get(v___x_1963_, 1);
lean_inc(v_a_1968_);
lean_dec_ref(v___x_1963_);
v___x_1969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1969_, 0, v_a_1967_);
v___y_1928_ = v___x_1961_;
v___y_1929_ = v_a_1960_;
v_fst_1930_ = v___x_1969_;
v_snd_1931_ = v_a_1968_;
goto v___jp_1927_;
}
}
}
v___jp_1564_:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; 
v___x_1565_ = lean_box(0);
v___x_1566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1565_);
return v___x_1566_;
}
v___jp_1567_:
{
lean_object* v_fullName_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; uint8_t v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; 
v_fullName_1570_ = lean_ctor_get(v___y_1568_, 1);
lean_inc_ref(v_fullName_1570_);
lean_dec_ref(v___y_1568_);
v___x_1571_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__0));
v___x_1572_ = lean_string_append(v_fullName_1570_, v___x_1571_);
v___x_1573_ = 3;
v___x_1574_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1574_, 0, v___x_1572_);
lean_ctor_set_uint8(v___x_1574_, sizeof(void*)*1, v___x_1573_);
lean_inc_ref(v___y_1569_);
v___x_1575_ = lean_apply_2(v___y_1569_, v___x_1574_, lean_box(0));
v___x_1576_ = lean_box(0);
v___x_1577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1577_, 0, v___x_1576_);
return v___x_1577_;
}
v___jp_1578_:
{
lean_object* v___x_1586_; lean_object* v___x_1587_; 
v___x_1586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1586_, 0, v___y_1582_);
v___x_1587_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit(v_dep_1556_, v_inherited_1557_, v_lakeEnv_1558_, v_wsDir_1559_, v___y_1581_, v___y_1580_, v___y_1584_, v___y_1585_, v___x_1586_, v___y_1583_, v___y_1579_);
lean_dec_ref(v_lakeEnv_1558_);
lean_dec_ref(v_dep_1556_);
return v___x_1587_;
}
v___jp_1588_:
{
if (lean_obj_tag(v___y_1591_) == 0)
{
lean_object* v___x_1596_; 
v___x_1596_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___y_1579_ = v___y_1595_;
v___y_1580_ = v___y_1589_;
v___y_1581_ = v___y_1590_;
v___y_1582_ = v_rev_x3f_1594_;
v___y_1583_ = v___y_1592_;
v___y_1584_ = v___y_1593_;
v___y_1585_ = v___x_1596_;
goto v___jp_1578_;
}
else
{
lean_object* v_val_1597_; 
v_val_1597_ = lean_ctor_get(v___y_1591_, 0);
lean_inc(v_val_1597_);
lean_dec_ref(v___y_1591_);
v___y_1579_ = v___y_1595_;
v___y_1580_ = v___y_1589_;
v___y_1581_ = v___y_1590_;
v___y_1582_ = v_rev_x3f_1594_;
v___y_1583_ = v___y_1592_;
v___y_1584_ = v___y_1593_;
v___y_1585_ = v_val_1597_;
goto v___jp_1578_;
}
}
v___jp_1602_:
{
lean_object* v_toString_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; uint8_t v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; 
v_toString_1605_ = lean_ctor_get(v___y_1603_, 0);
lean_inc_ref(v_toString_1605_);
lean_dec_ref(v___y_1603_);
v___x_1606_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
v___x_1607_ = lean_string_append(v_scope_1599_, v___x_1606_);
v___x_1608_ = lean_string_append(v___x_1607_, v___y_1604_);
lean_dec_ref(v___y_1604_);
v___x_1609_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__1));
v___x_1610_ = lean_string_append(v___x_1608_, v___x_1609_);
v___x_1611_ = lean_string_append(v___x_1610_, v_toString_1605_);
lean_dec_ref(v_toString_1605_);
v___x_1612_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__2));
v___x_1613_ = lean_string_append(v___x_1611_, v___x_1612_);
v___x_1614_ = 3;
v___x_1615_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1615_, 0, v___x_1613_);
lean_ctor_set_uint8(v___x_1615_, sizeof(void*)*1, v___x_1614_);
lean_inc_ref(v_a_1562_);
v___x_1616_ = lean_apply_2(v_a_1562_, v___x_1615_, lean_box(0));
v___x_1617_ = lean_box(0);
v___x_1618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1618_, 0, v___x_1617_);
return v___x_1618_;
}
v___jp_1619_:
{
if (lean_obj_tag(v_a_1627_) == 0)
{
lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1643_; 
lean_inc_ref(v_scope_1599_);
lean_dec_ref(v___y_1626_);
lean_dec(v___y_1625_);
lean_dec(v___y_1623_);
lean_dec_ref(v___y_1622_);
lean_dec_ref(v___y_1621_);
lean_dec_ref(v___y_1620_);
lean_dec_ref(v_wsDir_1559_);
lean_dec_ref(v_lakeEnv_1558_);
lean_dec_ref(v_dep_1556_);
v_isSharedCheck_1643_ = !lean_is_exclusive(v_a_1627_);
if (v_isSharedCheck_1643_ == 0)
{
lean_object* v_unused_1644_; 
v_unused_1644_ = lean_ctor_get(v_a_1627_, 0);
lean_dec(v_unused_1644_);
v___x_1629_ = v_a_1627_;
v_isShared_1630_ = v_isSharedCheck_1643_;
goto v_resetjp_1628_;
}
else
{
lean_dec(v_a_1627_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1643_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; uint8_t v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1641_; 
v___x_1631_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
v___x_1632_ = lean_string_append(v_scope_1599_, v___x_1631_);
v___x_1633_ = lean_string_append(v___x_1632_, v___y_1624_);
lean_dec_ref(v___y_1624_);
v___x_1634_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__3));
v___x_1635_ = lean_string_append(v___x_1633_, v___x_1634_);
v___x_1636_ = 3;
v___x_1637_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1637_, 0, v___x_1635_);
lean_ctor_set_uint8(v___x_1637_, sizeof(void*)*1, v___x_1636_);
lean_inc_ref(v_a_1562_);
v___x_1638_ = lean_apply_2(v_a_1562_, v___x_1637_, lean_box(0));
v___x_1639_ = lean_box(0);
if (v_isShared_1630_ == 0)
{
lean_ctor_set_tag(v___x_1629_, 1);
lean_ctor_set(v___x_1629_, 0, v___x_1639_);
v___x_1641_ = v___x_1629_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v___x_1639_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
}
else
{
lean_object* v_a_1645_; lean_object* v___x_1646_; size_t v_sz_1647_; size_t v___x_1648_; lean_object* v___x_1649_; lean_object* v_fst_1650_; 
v_a_1645_ = lean_ctor_get(v_a_1627_, 0);
lean_inc(v_a_1645_);
lean_dec_ref(v_a_1627_);
v___x_1646_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___closed__0));
v_sz_1647_ = lean_array_size(v_a_1645_);
v___x_1648_ = ((size_t)0ULL);
v___x_1649_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(v___y_1622_, v_a_1645_, v_sz_1647_, v___x_1648_, v___x_1646_);
lean_dec(v_a_1645_);
v_fst_1650_ = lean_ctor_get(v___x_1649_, 0);
lean_inc(v_fst_1650_);
lean_dec_ref(v___x_1649_);
if (lean_obj_tag(v_fst_1650_) == 0)
{
lean_inc_ref(v_scope_1599_);
lean_dec_ref(v___y_1626_);
lean_dec(v___y_1625_);
lean_dec(v___y_1623_);
lean_dec_ref(v___y_1621_);
lean_dec_ref(v___y_1620_);
lean_dec_ref(v_wsDir_1559_);
lean_dec_ref(v_lakeEnv_1558_);
lean_dec_ref(v_dep_1556_);
v___y_1603_ = v___y_1622_;
v___y_1604_ = v___y_1624_;
goto v___jp_1602_;
}
else
{
lean_object* v_val_1651_; 
v_val_1651_ = lean_ctor_get(v_fst_1650_, 0);
lean_inc(v_val_1651_);
lean_dec_ref(v_fst_1650_);
if (lean_obj_tag(v_val_1651_) == 1)
{
lean_object* v_val_1652_; lean_object* v_version_1653_; lean_object* v_revision_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; uint8_t v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; 
lean_dec_ref(v___y_1622_);
v_val_1652_ = lean_ctor_get(v_val_1651_, 0);
lean_inc(v_val_1652_);
lean_dec_ref(v_val_1651_);
v_version_1653_ = lean_ctor_get(v_val_1652_, 0);
lean_inc_ref(v_version_1653_);
v_revision_1654_ = lean_ctor_get(v_val_1652_, 1);
lean_inc_ref(v_revision_1654_);
lean_dec(v_val_1652_);
v___x_1655_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
lean_inc_ref(v_scope_1599_);
v___x_1656_ = lean_string_append(v_scope_1599_, v___x_1655_);
v___x_1657_ = lean_string_append(v___x_1656_, v___y_1624_);
lean_dec_ref(v___y_1624_);
v___x_1658_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__4));
v___x_1659_ = lean_string_append(v___x_1657_, v___x_1658_);
v___x_1660_ = l_Lake_StdVer_toString(v_version_1653_);
v___x_1661_ = lean_string_append(v___x_1659_, v___x_1660_);
lean_dec_ref(v___x_1660_);
v___x_1662_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__5));
v___x_1663_ = lean_string_append(v___x_1661_, v___x_1662_);
v___x_1664_ = lean_string_append(v___x_1663_, v_revision_1654_);
v___x_1665_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__6));
v___x_1666_ = lean_string_append(v___x_1664_, v___x_1665_);
v___x_1667_ = 1;
v___x_1668_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1668_, 0, v___x_1666_);
lean_ctor_set_uint8(v___x_1668_, sizeof(void*)*1, v___x_1667_);
lean_inc_ref(v_a_1562_);
v___x_1669_ = lean_apply_2(v_a_1562_, v___x_1668_, lean_box(0));
v___y_1589_ = v___y_1620_;
v___y_1590_ = v___y_1621_;
v___y_1591_ = v___y_1623_;
v___y_1592_ = v___y_1625_;
v___y_1593_ = v___y_1626_;
v_rev_x3f_1594_ = v_revision_1654_;
v___y_1595_ = v_a_1562_;
goto v___jp_1588_;
}
else
{
lean_inc_ref(v_scope_1599_);
lean_dec(v_val_1651_);
lean_dec_ref(v___y_1626_);
lean_dec(v___y_1625_);
lean_dec(v___y_1623_);
lean_dec_ref(v___y_1621_);
lean_dec_ref(v___y_1620_);
lean_dec_ref(v_wsDir_1559_);
lean_dec_ref(v_lakeEnv_1558_);
lean_dec_ref(v_dep_1556_);
v___y_1603_ = v___y_1622_;
v___y_1604_ = v___y_1624_;
goto v___jp_1602_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize___boxed(lean_object* v_dep_2018_, lean_object* v_inherited_2019_, lean_object* v_lakeEnv_2020_, lean_object* v_wsDir_2021_, lean_object* v_relPkgsDir_2022_, lean_object* v_relParentDir_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_){
_start:
{
uint8_t v_inherited_boxed_2026_; lean_object* v_res_2027_; 
v_inherited_boxed_2026_ = lean_unbox(v_inherited_2019_);
v_res_2027_ = l_Lake_Dependency_materialize(v_dep_2018_, v_inherited_boxed_2026_, v_lakeEnv_2020_, v_wsDir_2021_, v_relPkgsDir_2022_, v_relParentDir_2023_, v_a_2024_);
lean_dec_ref(v_a_2024_);
return v_res_2027_;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__0(void){
_start:
{
uint32_t v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; 
v___x_2028_ = 0;
v___x_2029_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___x_2030_ = lean_alloc_ctor(11, 2, 4);
lean_ctor_set(v___x_2030_, 0, v___x_2029_);
lean_ctor_set(v___x_2030_, 1, v___x_2029_);
lean_ctor_set_uint32(v___x_2030_, sizeof(void*)*2, v___x_2028_);
return v___x_2030_;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1(void){
_start:
{
lean_object* v___x_2031_; lean_object* v___x_2032_; 
v___x_2031_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__0, &l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__0_once, _init_l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__0);
v___x_2032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2032_, 0, v___x_2031_);
return v___x_2032_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep(lean_object* v_manifestEntry_2033_, lean_object* v_pkgDir_2034_, lean_object* v_relPkgDir_2035_, lean_object* v_remoteUrl_2036_, lean_object* v_a_2037_){
_start:
{
lean_object* v_a_2040_; lean_object* v_manifestFile_x3f_2043_; 
v_manifestFile_x3f_2043_ = lean_ctor_get(v_manifestEntry_2033_, 3);
if (lean_obj_tag(v_manifestFile_x3f_2043_) == 1)
{
lean_object* v_val_2044_; lean_object* v___f_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v_a_2050_; lean_object* v_a_2051_; lean_object* v___x_2080_; lean_object* v___x_2081_; 
v_val_2044_ = lean_ctor_get(v_manifestFile_x3f_2043_, 0);
v___f_2045_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0));
lean_inc(v_val_2044_);
v___x_2046_ = l_Lake_joinRelative(v_pkgDir_2034_, v_val_2044_);
v___x_2047_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__2, &l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__2_once, _init_l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__2);
v___x_2048_ = lean_unsigned_to_nat(0u);
v___x_2080_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
v___x_2081_ = l_Lake_Manifest_load(v___x_2046_);
if (lean_obj_tag(v___x_2081_) == 0)
{
lean_object* v_a_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2089_; 
v_a_2082_ = lean_ctor_get(v___x_2081_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_2081_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2084_ = v___x_2081_;
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_a_2082_);
lean_dec(v___x_2081_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2087_; 
if (v_isShared_2085_ == 0)
{
lean_ctor_set_tag(v___x_2084_, 1);
v___x_2087_ = v___x_2084_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_a_2082_);
v___x_2087_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
v_a_2050_ = v___x_2087_;
v_a_2051_ = v___x_2080_;
goto v___jp_2049_;
}
}
}
else
{
lean_object* v_a_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2097_; 
v_a_2090_ = lean_ctor_get(v___x_2081_, 0);
v_isSharedCheck_2097_ = !lean_is_exclusive(v___x_2081_);
if (v_isSharedCheck_2097_ == 0)
{
v___x_2092_ = v___x_2081_;
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_a_2090_);
lean_dec(v___x_2081_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2095_; 
if (v_isShared_2093_ == 0)
{
lean_ctor_set_tag(v___x_2092_, 0);
v___x_2095_ = v___x_2092_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v_a_2090_);
v___x_2095_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
v_a_2050_ = v___x_2095_;
v_a_2051_ = v___x_2080_;
goto v___jp_2049_;
}
}
}
v___jp_2049_:
{
lean_object* v___x_2052_; uint8_t v___x_2053_; 
v___x_2052_ = lean_array_get_size(v_a_2051_);
v___x_2053_ = lean_nat_dec_lt(v___x_2048_, v___x_2052_);
if (v___x_2053_ == 0)
{
lean_dec_ref(v_a_2051_);
v_a_2040_ = v_a_2050_;
goto v___jp_2039_;
}
else
{
lean_object* v___x_2054_; uint8_t v___x_2055_; 
v___x_2054_ = lean_box(0);
v___x_2055_ = lean_nat_dec_le(v___x_2052_, v___x_2052_);
if (v___x_2055_ == 0)
{
if (v___x_2053_ == 0)
{
lean_dec_ref(v_a_2051_);
v_a_2040_ = v_a_2050_;
goto v___jp_2039_;
}
else
{
size_t v___x_2056_; size_t v___x_2057_; lean_object* v___x_944__overap_2058_; lean_object* v___x_2059_; 
v___x_2056_ = ((size_t)0ULL);
v___x_2057_ = lean_usize_of_nat(v___x_2052_);
v___x_944__overap_2058_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2047_, v___f_2045_, v_a_2051_, v___x_2056_, v___x_2057_, v___x_2054_);
lean_inc_ref(v_a_2037_);
v___x_2059_ = lean_apply_2(v___x_944__overap_2058_, v_a_2037_, lean_box(0));
if (lean_obj_tag(v___x_2059_) == 0)
{
lean_dec_ref(v___x_2059_);
v_a_2040_ = v_a_2050_;
goto v___jp_2039_;
}
else
{
lean_object* v_a_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2067_; 
lean_dec_ref(v_a_2050_);
lean_dec_ref(v_remoteUrl_2036_);
lean_dec_ref(v_relPkgDir_2035_);
lean_dec_ref(v_manifestEntry_2033_);
v_a_2060_ = lean_ctor_get(v___x_2059_, 0);
v_isSharedCheck_2067_ = !lean_is_exclusive(v___x_2059_);
if (v_isSharedCheck_2067_ == 0)
{
v___x_2062_ = v___x_2059_;
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_a_2060_);
lean_dec(v___x_2059_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v___x_2065_; 
if (v_isShared_2063_ == 0)
{
v___x_2065_ = v___x_2062_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v_a_2060_);
v___x_2065_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
return v___x_2065_;
}
}
}
}
}
else
{
size_t v___x_2068_; size_t v___x_2069_; lean_object* v___x_954__overap_2070_; lean_object* v___x_2071_; 
v___x_2068_ = ((size_t)0ULL);
v___x_2069_ = lean_usize_of_nat(v___x_2052_);
v___x_954__overap_2070_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2047_, v___f_2045_, v_a_2051_, v___x_2068_, v___x_2069_, v___x_2054_);
lean_inc_ref(v_a_2037_);
v___x_2071_ = lean_apply_2(v___x_954__overap_2070_, v_a_2037_, lean_box(0));
if (lean_obj_tag(v___x_2071_) == 0)
{
lean_dec_ref(v___x_2071_);
v_a_2040_ = v_a_2050_;
goto v___jp_2039_;
}
else
{
lean_object* v_a_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2079_; 
lean_dec_ref(v_a_2050_);
lean_dec_ref(v_remoteUrl_2036_);
lean_dec_ref(v_relPkgDir_2035_);
lean_dec_ref(v_manifestEntry_2033_);
v_a_2072_ = lean_ctor_get(v___x_2071_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2074_ = v___x_2071_;
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_a_2072_);
lean_dec(v___x_2071_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v___x_2077_; 
if (v_isShared_2075_ == 0)
{
v___x_2077_ = v___x_2074_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_a_2072_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2098_; 
lean_dec_ref(v_pkgDir_2034_);
v___x_2098_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1, &l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1_once, _init_l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1);
v_a_2040_ = v___x_2098_;
goto v___jp_2039_;
}
v___jp_2039_:
{
lean_object* v___x_2041_; lean_object* v___x_2042_; 
v___x_2041_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2041_, 0, v_relPkgDir_2035_);
lean_ctor_set(v___x_2041_, 1, v_remoteUrl_2036_);
lean_ctor_set(v___x_2041_, 2, v_a_2040_);
lean_ctor_set(v___x_2041_, 3, v_manifestEntry_2033_);
v___x_2042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2042_, 0, v___x_2041_);
return v___x_2042_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___boxed(lean_object* v_manifestEntry_2099_, lean_object* v_pkgDir_2100_, lean_object* v_relPkgDir_2101_, lean_object* v_remoteUrl_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_){
_start:
{
lean_object* v_res_2105_; 
v_res_2105_ = l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep(v_manifestEntry_2099_, v_pkgDir_2100_, v_relPkgDir_2101_, v_remoteUrl_2102_, v_a_2103_);
lean_dec_ref(v_a_2103_);
return v_res_2105_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize(lean_object* v_manifestEntry_2107_, lean_object* v_lakeEnv_2108_, lean_object* v_wsDir_2109_, lean_object* v_relPkgsDir_2110_, lean_object* v_a_2111_){
_start:
{
lean_object* v___y_2114_; lean_object* v___y_2115_; lean_object* v_a_2116_; lean_object* v___y_2120_; lean_object* v___y_2121_; lean_object* v___y_2122_; lean_object* v___y_2123_; lean_object* v_a_2124_; lean_object* v_a_2125_; lean_object* v_src_2152_; 
v_src_2152_ = lean_ctor_get(v_manifestEntry_2107_, 4);
lean_inc_ref(v_src_2152_);
if (lean_obj_tag(v_src_2152_) == 0)
{
lean_object* v_manifestFile_x3f_2153_; lean_object* v_dir_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2217_; 
lean_dec_ref(v_relPkgsDir_2110_);
v_manifestFile_x3f_2153_ = lean_ctor_get(v_manifestEntry_2107_, 3);
v_dir_2154_ = lean_ctor_get(v_src_2152_, 0);
v_isSharedCheck_2217_ = !lean_is_exclusive(v_src_2152_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_2156_ = v_src_2152_;
v_isShared_2157_ = v_isSharedCheck_2217_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_dir_2154_);
lean_dec(v_src_2152_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2217_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2158_; lean_object* v_a_2160_; 
v___x_2158_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
if (lean_obj_tag(v_manifestFile_x3f_2153_) == 1)
{
lean_object* v_val_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v_a_2170_; lean_object* v_a_2171_; lean_object* v___x_2198_; lean_object* v___x_2199_; 
v_val_2165_ = lean_ctor_get(v_manifestFile_x3f_2153_, 0);
lean_inc_ref(v_dir_2154_);
v___x_2166_ = l_Lake_joinRelative(v_wsDir_2109_, v_dir_2154_);
lean_inc(v_val_2165_);
v___x_2167_ = l_Lake_joinRelative(v___x_2166_, v_val_2165_);
v___x_2168_ = lean_unsigned_to_nat(0u);
v___x_2198_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
v___x_2199_ = l_Lake_Manifest_load(v___x_2167_);
if (lean_obj_tag(v___x_2199_) == 0)
{
lean_object* v_a_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2207_; 
v_a_2200_ = lean_ctor_get(v___x_2199_, 0);
v_isSharedCheck_2207_ = !lean_is_exclusive(v___x_2199_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2202_ = v___x_2199_;
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_a_2200_);
lean_dec(v___x_2199_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v___x_2205_; 
if (v_isShared_2203_ == 0)
{
lean_ctor_set_tag(v___x_2202_, 1);
v___x_2205_ = v___x_2202_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v_a_2200_);
v___x_2205_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
v_a_2170_ = v___x_2205_;
v_a_2171_ = v___x_2198_;
goto v___jp_2169_;
}
}
}
else
{
lean_object* v_a_2208_; lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2215_; 
v_a_2208_ = lean_ctor_get(v___x_2199_, 0);
v_isSharedCheck_2215_ = !lean_is_exclusive(v___x_2199_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2210_ = v___x_2199_;
v_isShared_2211_ = v_isSharedCheck_2215_;
goto v_resetjp_2209_;
}
else
{
lean_inc(v_a_2208_);
lean_dec(v___x_2199_);
v___x_2210_ = lean_box(0);
v_isShared_2211_ = v_isSharedCheck_2215_;
goto v_resetjp_2209_;
}
v_resetjp_2209_:
{
lean_object* v___x_2213_; 
if (v_isShared_2211_ == 0)
{
lean_ctor_set_tag(v___x_2210_, 0);
v___x_2213_ = v___x_2210_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v_a_2208_);
v___x_2213_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
v_a_2170_ = v___x_2213_;
v_a_2171_ = v___x_2198_;
goto v___jp_2169_;
}
}
}
v___jp_2169_:
{
lean_object* v___x_2172_; uint8_t v___x_2173_; 
v___x_2172_ = lean_array_get_size(v_a_2171_);
v___x_2173_ = lean_nat_dec_lt(v___x_2168_, v___x_2172_);
if (v___x_2173_ == 0)
{
lean_dec_ref(v_a_2171_);
v_a_2160_ = v_a_2170_;
goto v___jp_2159_;
}
else
{
lean_object* v___x_2174_; uint8_t v___x_2175_; 
v___x_2174_ = lean_box(0);
v___x_2175_ = lean_nat_dec_le(v___x_2172_, v___x_2172_);
if (v___x_2175_ == 0)
{
if (v___x_2173_ == 0)
{
lean_dec_ref(v_a_2171_);
v_a_2160_ = v_a_2170_;
goto v___jp_2159_;
}
else
{
size_t v___x_2176_; size_t v___x_2177_; lean_object* v___x_2178_; 
v___x_2176_ = ((size_t)0ULL);
v___x_2177_ = lean_usize_of_nat(v___x_2172_);
v___x_2178_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_2171_, v___x_2176_, v___x_2177_, v___x_2174_, v_a_2111_);
lean_dec_ref(v_a_2171_);
if (lean_obj_tag(v___x_2178_) == 0)
{
lean_dec_ref(v___x_2178_);
v_a_2160_ = v_a_2170_;
goto v___jp_2159_;
}
else
{
lean_object* v_a_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2186_; 
lean_dec_ref(v_a_2170_);
lean_del_object(v___x_2156_);
lean_dec_ref(v_dir_2154_);
lean_dec_ref(v_manifestEntry_2107_);
v_a_2179_ = lean_ctor_get(v___x_2178_, 0);
v_isSharedCheck_2186_ = !lean_is_exclusive(v___x_2178_);
if (v_isSharedCheck_2186_ == 0)
{
v___x_2181_ = v___x_2178_;
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_a_2179_);
lean_dec(v___x_2178_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v___x_2184_; 
if (v_isShared_2182_ == 0)
{
v___x_2184_ = v___x_2181_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v_a_2179_);
v___x_2184_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
return v___x_2184_;
}
}
}
}
}
else
{
size_t v___x_2187_; size_t v___x_2188_; lean_object* v___x_2189_; 
v___x_2187_ = ((size_t)0ULL);
v___x_2188_ = lean_usize_of_nat(v___x_2172_);
v___x_2189_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_2171_, v___x_2187_, v___x_2188_, v___x_2174_, v_a_2111_);
lean_dec_ref(v_a_2171_);
if (lean_obj_tag(v___x_2189_) == 0)
{
lean_dec_ref(v___x_2189_);
v_a_2160_ = v_a_2170_;
goto v___jp_2159_;
}
else
{
lean_object* v_a_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2197_; 
lean_dec_ref(v_a_2170_);
lean_del_object(v___x_2156_);
lean_dec_ref(v_dir_2154_);
lean_dec_ref(v_manifestEntry_2107_);
v_a_2190_ = lean_ctor_get(v___x_2189_, 0);
v_isSharedCheck_2197_ = !lean_is_exclusive(v___x_2189_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2192_ = v___x_2189_;
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_a_2190_);
lean_dec(v___x_2189_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2195_; 
if (v_isShared_2193_ == 0)
{
v___x_2195_ = v___x_2192_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_a_2190_);
v___x_2195_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
return v___x_2195_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2216_; 
lean_dec_ref(v_wsDir_2109_);
v___x_2216_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1, &l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1_once, _init_l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1);
v_a_2160_ = v___x_2216_;
goto v___jp_2159_;
}
v___jp_2159_:
{
lean_object* v___x_2161_; lean_object* v___x_2163_; 
v___x_2161_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2161_, 0, v_dir_2154_);
lean_ctor_set(v___x_2161_, 1, v___x_2158_);
lean_ctor_set(v___x_2161_, 2, v_a_2160_);
lean_ctor_set(v___x_2161_, 3, v_manifestEntry_2107_);
if (v_isShared_2157_ == 0)
{
lean_ctor_set(v___x_2156_, 0, v___x_2161_);
v___x_2163_ = v___x_2156_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v___x_2161_);
v___x_2163_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
return v___x_2163_;
}
}
}
}
else
{
lean_object* v_name_2218_; lean_object* v_manifestFile_x3f_2219_; lean_object* v_url_2220_; lean_object* v_rev_2221_; lean_object* v_subDir_x3f_2222_; uint8_t v___x_2223_; lean_object* v_sname_2224_; lean_object* v_relGitDir_2225_; lean_object* v_gitDir_2226_; lean_object* v___y_2228_; lean_object* v___y_2229_; lean_object* v___y_2230_; lean_object* v___y_2254_; lean_object* v___y_2255_; lean_object* v___y_2260_; lean_object* v___y_2264_; lean_object* v___y_2265_; lean_object* v___y_2276_; uint8_t v_a_2288_; lean_object* v___y_2298_; lean_object* v___y_2299_; uint8_t v_val_2300_; uint8_t v___y_2328_; lean_object* v_a_2329_; uint8_t v___x_2339_; lean_object* v___x_2372_; uint8_t v___x_2373_; 
v_name_2218_ = lean_ctor_get(v_manifestEntry_2107_, 0);
v_manifestFile_x3f_2219_ = lean_ctor_get(v_manifestEntry_2107_, 3);
v_url_2220_ = lean_ctor_get(v_src_2152_, 0);
lean_inc_ref(v_url_2220_);
v_rev_2221_ = lean_ctor_get(v_src_2152_, 1);
lean_inc_ref(v_rev_2221_);
v_subDir_x3f_2222_ = lean_ctor_get(v_src_2152_, 3);
lean_inc(v_subDir_x3f_2222_);
lean_dec_ref(v_src_2152_);
v___x_2223_ = 0;
lean_inc(v_name_2218_);
v_sname_2224_ = l_Lean_Name_toString(v_name_2218_, v___x_2223_);
lean_inc_ref(v_sname_2224_);
v_relGitDir_2225_ = l_Lake_joinRelative(v_relPkgsDir_2110_, v_sname_2224_);
lean_inc_ref(v_relGitDir_2225_);
v_gitDir_2226_ = l_Lake_joinRelative(v_wsDir_2109_, v_relGitDir_2225_);
v___x_2339_ = l_System_FilePath_isDir(v_gitDir_2226_);
v___x_2372_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
v___x_2373_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_2373_ == 0)
{
goto v___jp_2340_;
}
else
{
lean_object* v___x_2374_; uint8_t v___x_2375_; 
v___x_2374_ = lean_box(0);
v___x_2375_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_2375_ == 0)
{
if (v___x_2373_ == 0)
{
goto v___jp_2340_;
}
else
{
size_t v___x_2376_; size_t v___x_2377_; lean_object* v___x_2378_; 
v___x_2376_ = ((size_t)0ULL);
v___x_2377_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_2378_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_2372_, v___x_2376_, v___x_2377_, v___x_2374_, v_a_2111_);
if (lean_obj_tag(v___x_2378_) == 0)
{
lean_dec_ref(v___x_2378_);
goto v___jp_2340_;
}
else
{
lean_object* v_a_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2386_; 
lean_dec_ref(v_gitDir_2226_);
lean_dec_ref(v_relGitDir_2225_);
lean_dec_ref(v_sname_2224_);
lean_dec(v_subDir_x3f_2222_);
lean_dec_ref(v_rev_2221_);
lean_dec_ref(v_url_2220_);
lean_dec_ref(v_manifestEntry_2107_);
v_a_2379_ = lean_ctor_get(v___x_2378_, 0);
v_isSharedCheck_2386_ = !lean_is_exclusive(v___x_2378_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2381_ = v___x_2378_;
v_isShared_2382_ = v_isSharedCheck_2386_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_a_2379_);
lean_dec(v___x_2378_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2386_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
lean_object* v___x_2384_; 
if (v_isShared_2382_ == 0)
{
v___x_2384_ = v___x_2381_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v_a_2379_);
v___x_2384_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
return v___x_2384_;
}
}
}
}
}
else
{
size_t v___x_2387_; size_t v___x_2388_; lean_object* v___x_2389_; 
v___x_2387_ = ((size_t)0ULL);
v___x_2388_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_2389_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_2372_, v___x_2387_, v___x_2388_, v___x_2374_, v_a_2111_);
if (lean_obj_tag(v___x_2389_) == 0)
{
lean_dec_ref(v___x_2389_);
goto v___jp_2340_;
}
else
{
lean_object* v_a_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2397_; 
lean_dec_ref(v_gitDir_2226_);
lean_dec_ref(v_relGitDir_2225_);
lean_dec_ref(v_sname_2224_);
lean_dec(v_subDir_x3f_2222_);
lean_dec_ref(v_rev_2221_);
lean_dec_ref(v_url_2220_);
lean_dec_ref(v_manifestEntry_2107_);
v_a_2390_ = lean_ctor_get(v___x_2389_, 0);
v_isSharedCheck_2397_ = !lean_is_exclusive(v___x_2389_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2392_ = v___x_2389_;
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
else
{
lean_inc(v_a_2390_);
lean_dec(v___x_2389_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
lean_object* v___x_2395_; 
if (v_isShared_2393_ == 0)
{
v___x_2395_ = v___x_2392_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v_a_2390_);
v___x_2395_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
return v___x_2395_;
}
}
}
}
}
v___jp_2227_:
{
if (lean_obj_tag(v_manifestFile_x3f_2219_) == 1)
{
lean_object* v_val_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; 
v_val_2231_ = lean_ctor_get(v_manifestFile_x3f_2219_, 0);
lean_inc(v_val_2231_);
v___x_2232_ = l_Lake_joinRelative(v_gitDir_2226_, v_val_2231_);
v___x_2233_ = lean_unsigned_to_nat(0u);
v___x_2234_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
v___x_2235_ = l_Lake_Manifest_load(v___x_2232_);
if (lean_obj_tag(v___x_2235_) == 0)
{
lean_object* v_a_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2243_; 
v_a_2236_ = lean_ctor_get(v___x_2235_, 0);
v_isSharedCheck_2243_ = !lean_is_exclusive(v___x_2235_);
if (v_isSharedCheck_2243_ == 0)
{
v___x_2238_ = v___x_2235_;
v_isShared_2239_ = v_isSharedCheck_2243_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_a_2236_);
lean_dec(v___x_2235_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2243_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
lean_object* v___x_2241_; 
if (v_isShared_2239_ == 0)
{
lean_ctor_set_tag(v___x_2238_, 1);
v___x_2241_ = v___x_2238_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v_a_2236_);
v___x_2241_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
v___y_2120_ = v___y_2228_;
v___y_2121_ = v___y_2230_;
v___y_2122_ = v___x_2233_;
v___y_2123_ = v___y_2229_;
v_a_2124_ = v___x_2241_;
v_a_2125_ = v___x_2234_;
goto v___jp_2119_;
}
}
}
else
{
lean_object* v_a_2244_; lean_object* v___x_2246_; uint8_t v_isShared_2247_; uint8_t v_isSharedCheck_2251_; 
v_a_2244_ = lean_ctor_get(v___x_2235_, 0);
v_isSharedCheck_2251_ = !lean_is_exclusive(v___x_2235_);
if (v_isSharedCheck_2251_ == 0)
{
v___x_2246_ = v___x_2235_;
v_isShared_2247_ = v_isSharedCheck_2251_;
goto v_resetjp_2245_;
}
else
{
lean_inc(v_a_2244_);
lean_dec(v___x_2235_);
v___x_2246_ = lean_box(0);
v_isShared_2247_ = v_isSharedCheck_2251_;
goto v_resetjp_2245_;
}
v_resetjp_2245_:
{
lean_object* v___x_2249_; 
if (v_isShared_2247_ == 0)
{
lean_ctor_set_tag(v___x_2246_, 0);
v___x_2249_ = v___x_2246_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v_a_2244_);
v___x_2249_ = v_reuseFailAlloc_2250_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
v___y_2120_ = v___y_2228_;
v___y_2121_ = v___y_2230_;
v___y_2122_ = v___x_2233_;
v___y_2123_ = v___y_2229_;
v_a_2124_ = v___x_2249_;
v_a_2125_ = v___x_2234_;
goto v___jp_2119_;
}
}
}
}
else
{
lean_object* v___x_2252_; 
lean_dec_ref(v_gitDir_2226_);
v___x_2252_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1, &l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1_once, _init_l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1);
v___y_2114_ = v___y_2228_;
v___y_2115_ = v___y_2230_;
v_a_2116_ = v___x_2252_;
goto v___jp_2113_;
}
}
v___jp_2253_:
{
lean_object* v___x_2256_; 
v___x_2256_ = l_Lake_Git_filterUrl_x3f(v_url_2220_);
if (lean_obj_tag(v___x_2256_) == 0)
{
lean_object* v___x_2257_; 
v___x_2257_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___y_2228_ = v___y_2255_;
v___y_2229_ = v___y_2254_;
v___y_2230_ = v___x_2257_;
goto v___jp_2227_;
}
else
{
lean_object* v_val_2258_; 
v_val_2258_ = lean_ctor_get(v___x_2256_, 0);
lean_inc(v_val_2258_);
lean_dec_ref(v___x_2256_);
v___y_2228_ = v___y_2255_;
v___y_2229_ = v___y_2254_;
v___y_2230_ = v_val_2258_;
goto v___jp_2227_;
}
}
v___jp_2259_:
{
if (lean_obj_tag(v_subDir_x3f_2222_) == 0)
{
v___y_2254_ = v___y_2260_;
v___y_2255_ = v_relGitDir_2225_;
goto v___jp_2253_;
}
else
{
lean_object* v_val_2261_; lean_object* v___x_2262_; 
v_val_2261_ = lean_ctor_get(v_subDir_x3f_2222_, 0);
lean_inc(v_val_2261_);
lean_dec_ref(v_subDir_x3f_2222_);
v___x_2262_ = l_Lake_joinRelative(v_relGitDir_2225_, v_val_2261_);
v___y_2254_ = v___y_2260_;
v___y_2255_ = v___x_2262_;
goto v___jp_2253_;
}
}
v___jp_2263_:
{
lean_object* v___x_2266_; 
lean_inc_ref(v_gitDir_2226_);
v___x_2266_ = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_2111_, v_sname_2224_, v_gitDir_2226_, v___y_2265_, v___y_2264_);
if (lean_obj_tag(v___x_2266_) == 0)
{
lean_dec_ref(v___x_2266_);
v___y_2260_ = v_a_2111_;
goto v___jp_2259_;
}
else
{
lean_object* v_a_2267_; lean_object* v___x_2269_; uint8_t v_isShared_2270_; uint8_t v_isSharedCheck_2274_; 
lean_dec_ref(v_gitDir_2226_);
lean_dec_ref(v_relGitDir_2225_);
lean_dec(v_subDir_x3f_2222_);
lean_dec_ref(v_url_2220_);
lean_dec_ref(v_manifestEntry_2107_);
v_a_2267_ = lean_ctor_get(v___x_2266_, 0);
v_isSharedCheck_2274_ = !lean_is_exclusive(v___x_2266_);
if (v_isSharedCheck_2274_ == 0)
{
v___x_2269_ = v___x_2266_;
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
else
{
lean_inc(v_a_2267_);
lean_dec(v___x_2266_);
v___x_2269_ = lean_box(0);
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
v_resetjp_2268_:
{
lean_object* v___x_2272_; 
if (v_isShared_2270_ == 0)
{
v___x_2272_ = v___x_2269_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v_a_2267_);
v___x_2272_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
return v___x_2272_;
}
}
}
}
v___jp_2275_:
{
lean_object* v___x_2277_; lean_object* v___x_2278_; 
v___x_2277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2277_, 0, v_rev_2221_);
lean_inc_ref(v_gitDir_2226_);
v___x_2278_ = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(v_a_2111_, v_sname_2224_, v_gitDir_2226_, v___y_2276_, v___x_2277_);
if (lean_obj_tag(v___x_2278_) == 0)
{
lean_dec_ref(v___x_2278_);
v___y_2260_ = v_a_2111_;
goto v___jp_2259_;
}
else
{
lean_object* v_a_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2286_; 
lean_dec_ref(v_gitDir_2226_);
lean_dec_ref(v_relGitDir_2225_);
lean_dec(v_subDir_x3f_2222_);
lean_dec_ref(v_url_2220_);
lean_dec_ref(v_manifestEntry_2107_);
v_a_2279_ = lean_ctor_get(v___x_2278_, 0);
v_isSharedCheck_2286_ = !lean_is_exclusive(v___x_2278_);
if (v_isSharedCheck_2286_ == 0)
{
v___x_2281_ = v___x_2278_;
v_isShared_2282_ = v_isSharedCheck_2286_;
goto v_resetjp_2280_;
}
else
{
lean_inc(v_a_2279_);
lean_dec(v___x_2278_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2286_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
lean_object* v___x_2284_; 
if (v_isShared_2282_ == 0)
{
v___x_2284_ = v___x_2281_;
goto v_reusejp_2283_;
}
else
{
lean_object* v_reuseFailAlloc_2285_; 
v_reuseFailAlloc_2285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2285_, 0, v_a_2279_);
v___x_2284_ = v_reuseFailAlloc_2285_;
goto v_reusejp_2283_;
}
v_reusejp_2283_:
{
return v___x_2284_;
}
}
}
}
v___jp_2287_:
{
if (v_a_2288_ == 0)
{
lean_dec_ref(v_sname_2224_);
v___y_2260_ = v_a_2111_;
goto v___jp_2259_;
}
else
{
lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; uint8_t v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; 
v___x_2289_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0));
v___x_2290_ = lean_string_append(v_sname_2224_, v___x_2289_);
v___x_2291_ = lean_string_append(v___x_2290_, v_gitDir_2226_);
v___x_2292_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1));
v___x_2293_ = lean_string_append(v___x_2291_, v___x_2292_);
v___x_2294_ = 2;
v___x_2295_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2295_, 0, v___x_2293_);
lean_ctor_set_uint8(v___x_2295_, sizeof(void*)*1, v___x_2294_);
lean_inc_ref(v_a_2111_);
v___x_2296_ = lean_apply_2(v_a_2111_, v___x_2295_, lean_box(0));
v___y_2260_ = v_a_2111_;
goto v___jp_2259_;
}
}
v___jp_2297_:
{
lean_object* v___x_2301_; uint8_t v___x_2302_; 
v___x_2301_ = lean_array_get_size(v___y_2299_);
v___x_2302_ = lean_nat_dec_lt(v___y_2298_, v___x_2301_);
if (v___x_2302_ == 0)
{
lean_dec_ref(v___y_2299_);
v_a_2288_ = v_val_2300_;
goto v___jp_2287_;
}
else
{
lean_object* v___x_2303_; uint8_t v___x_2304_; 
v___x_2303_ = lean_box(0);
v___x_2304_ = lean_nat_dec_le(v___x_2301_, v___x_2301_);
if (v___x_2304_ == 0)
{
if (v___x_2302_ == 0)
{
lean_dec_ref(v___y_2299_);
v_a_2288_ = v_val_2300_;
goto v___jp_2287_;
}
else
{
size_t v___x_2305_; size_t v___x_2306_; lean_object* v___x_2307_; 
v___x_2305_ = ((size_t)0ULL);
v___x_2306_ = lean_usize_of_nat(v___x_2301_);
v___x_2307_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_2299_, v___x_2305_, v___x_2306_, v___x_2303_, v_a_2111_);
lean_dec_ref(v___y_2299_);
if (lean_obj_tag(v___x_2307_) == 0)
{
lean_dec_ref(v___x_2307_);
v_a_2288_ = v_val_2300_;
goto v___jp_2287_;
}
else
{
lean_object* v_a_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2315_; 
lean_dec_ref(v_gitDir_2226_);
lean_dec_ref(v_relGitDir_2225_);
lean_dec_ref(v_sname_2224_);
lean_dec(v_subDir_x3f_2222_);
lean_dec_ref(v_url_2220_);
lean_dec_ref(v_manifestEntry_2107_);
v_a_2308_ = lean_ctor_get(v___x_2307_, 0);
v_isSharedCheck_2315_ = !lean_is_exclusive(v___x_2307_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2310_ = v___x_2307_;
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_a_2308_);
lean_dec(v___x_2307_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
lean_object* v___x_2313_; 
if (v_isShared_2311_ == 0)
{
v___x_2313_ = v___x_2310_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v_a_2308_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
return v___x_2313_;
}
}
}
}
}
else
{
size_t v___x_2316_; size_t v___x_2317_; lean_object* v___x_2318_; 
v___x_2316_ = ((size_t)0ULL);
v___x_2317_ = lean_usize_of_nat(v___x_2301_);
v___x_2318_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_2299_, v___x_2316_, v___x_2317_, v___x_2303_, v_a_2111_);
lean_dec_ref(v___y_2299_);
if (lean_obj_tag(v___x_2318_) == 0)
{
lean_dec_ref(v___x_2318_);
v_a_2288_ = v_val_2300_;
goto v___jp_2287_;
}
else
{
lean_object* v_a_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2326_; 
lean_dec_ref(v_gitDir_2226_);
lean_dec_ref(v_relGitDir_2225_);
lean_dec_ref(v_sname_2224_);
lean_dec(v_subDir_x3f_2222_);
lean_dec_ref(v_url_2220_);
lean_dec_ref(v_manifestEntry_2107_);
v_a_2319_ = lean_ctor_get(v___x_2318_, 0);
v_isSharedCheck_2326_ = !lean_is_exclusive(v___x_2318_);
if (v_isSharedCheck_2326_ == 0)
{
v___x_2321_ = v___x_2318_;
v_isShared_2322_ = v_isSharedCheck_2326_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_a_2319_);
lean_dec(v___x_2318_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2326_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v___x_2324_; 
if (v_isShared_2322_ == 0)
{
v___x_2324_ = v___x_2321_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_a_2319_);
v___x_2324_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
return v___x_2324_;
}
}
}
}
}
}
v___jp_2327_:
{
lean_object* v___x_2330_; lean_object* v___x_2331_; uint8_t v___x_2332_; 
v___x_2330_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
v___x_2331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2331_, 0, v_rev_2221_);
lean_inc_ref(v___x_2331_);
v___x_2332_ = l_Option_instDecidableEq___redArg(v___x_2330_, v_a_2329_, v___x_2331_);
if (v___x_2332_ == 0)
{
lean_object* v_pkgUrlMap_2333_; lean_object* v___x_2334_; 
v_pkgUrlMap_2333_ = lean_ctor_get(v_lakeEnv_2108_, 5);
v___x_2334_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgUrlMap_2333_, v_name_2218_);
if (lean_obj_tag(v___x_2334_) == 0)
{
lean_inc_ref(v_url_2220_);
v___y_2264_ = v___x_2331_;
v___y_2265_ = v_url_2220_;
goto v___jp_2263_;
}
else
{
lean_object* v_val_2335_; 
v_val_2335_ = lean_ctor_get(v___x_2334_, 0);
lean_inc(v_val_2335_);
lean_dec_ref(v___x_2334_);
v___y_2264_ = v___x_2331_;
v___y_2265_ = v_val_2335_;
goto v___jp_2263_;
}
}
else
{
uint8_t v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; 
lean_dec_ref(v___x_2331_);
lean_inc_ref(v_gitDir_2226_);
v___x_2336_ = l_Lake_GitRepo_hasNoDiff(v_gitDir_2226_);
v___x_2337_ = lean_unsigned_to_nat(0u);
v___x_2338_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
if (v___x_2336_ == 0)
{
v___y_2298_ = v___x_2337_;
v___y_2299_ = v___x_2338_;
v_val_2300_ = v___y_2328_;
goto v___jp_2297_;
}
else
{
v___y_2298_ = v___x_2337_;
v___y_2299_ = v___x_2338_;
v_val_2300_ = v___x_2223_;
goto v___jp_2297_;
}
}
}
v___jp_2340_:
{
if (v___x_2339_ == 0)
{
lean_object* v_pkgUrlMap_2341_; lean_object* v___x_2342_; 
v_pkgUrlMap_2341_ = lean_ctor_get(v_lakeEnv_2108_, 5);
v___x_2342_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgUrlMap_2341_, v_name_2218_);
if (lean_obj_tag(v___x_2342_) == 0)
{
lean_inc_ref(v_url_2220_);
v___y_2276_ = v_url_2220_;
goto v___jp_2275_;
}
else
{
lean_object* v_val_2343_; 
v_val_2343_ = lean_ctor_get(v___x_2342_, 0);
lean_inc(v_val_2343_);
lean_dec_ref(v___x_2342_);
v___y_2276_ = v_val_2343_;
goto v___jp_2275_;
}
}
else
{
lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; uint8_t v___x_2347_; 
v___x_2344_ = ((lean_object*)(l_Lake_PackageEntry_materialize___closed__0));
lean_inc_ref(v_gitDir_2226_);
v___x_2345_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_2344_, v_gitDir_2226_);
v___x_2346_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
v___x_2347_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_2347_ == 0)
{
v___y_2328_ = v___x_2339_;
v_a_2329_ = v___x_2345_;
goto v___jp_2327_;
}
else
{
lean_object* v___x_2348_; uint8_t v___x_2349_; 
v___x_2348_ = lean_box(0);
v___x_2349_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_2349_ == 0)
{
if (v___x_2347_ == 0)
{
v___y_2328_ = v___x_2339_;
v_a_2329_ = v___x_2345_;
goto v___jp_2327_;
}
else
{
size_t v___x_2350_; size_t v___x_2351_; lean_object* v___x_2352_; 
v___x_2350_ = ((size_t)0ULL);
v___x_2351_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_2352_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_2346_, v___x_2350_, v___x_2351_, v___x_2348_, v_a_2111_);
if (lean_obj_tag(v___x_2352_) == 0)
{
lean_dec_ref(v___x_2352_);
v___y_2328_ = v___x_2339_;
v_a_2329_ = v___x_2345_;
goto v___jp_2327_;
}
else
{
lean_object* v_a_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2360_; 
lean_dec(v___x_2345_);
lean_dec_ref(v_gitDir_2226_);
lean_dec_ref(v_relGitDir_2225_);
lean_dec_ref(v_sname_2224_);
lean_dec(v_subDir_x3f_2222_);
lean_dec_ref(v_rev_2221_);
lean_dec_ref(v_url_2220_);
lean_dec_ref(v_manifestEntry_2107_);
v_a_2353_ = lean_ctor_get(v___x_2352_, 0);
v_isSharedCheck_2360_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2360_ == 0)
{
v___x_2355_ = v___x_2352_;
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_a_2353_);
lean_dec(v___x_2352_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v___x_2358_; 
if (v_isShared_2356_ == 0)
{
v___x_2358_ = v___x_2355_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v_a_2353_);
v___x_2358_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
return v___x_2358_;
}
}
}
}
}
else
{
size_t v___x_2361_; size_t v___x_2362_; lean_object* v___x_2363_; 
v___x_2361_ = ((size_t)0ULL);
v___x_2362_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_2363_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_2346_, v___x_2361_, v___x_2362_, v___x_2348_, v_a_2111_);
if (lean_obj_tag(v___x_2363_) == 0)
{
lean_dec_ref(v___x_2363_);
v___y_2328_ = v___x_2339_;
v_a_2329_ = v___x_2345_;
goto v___jp_2327_;
}
else
{
lean_object* v_a_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2371_; 
lean_dec(v___x_2345_);
lean_dec_ref(v_gitDir_2226_);
lean_dec_ref(v_relGitDir_2225_);
lean_dec_ref(v_sname_2224_);
lean_dec(v_subDir_x3f_2222_);
lean_dec_ref(v_rev_2221_);
lean_dec_ref(v_url_2220_);
lean_dec_ref(v_manifestEntry_2107_);
v_a_2364_ = lean_ctor_get(v___x_2363_, 0);
v_isSharedCheck_2371_ = !lean_is_exclusive(v___x_2363_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2366_ = v___x_2363_;
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_a_2364_);
lean_dec(v___x_2363_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v___x_2369_; 
if (v_isShared_2367_ == 0)
{
v___x_2369_ = v___x_2366_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v_a_2364_);
v___x_2369_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
return v___x_2369_;
}
}
}
}
}
}
}
}
v___jp_2113_:
{
lean_object* v___x_2117_; lean_object* v___x_2118_; 
v___x_2117_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2117_, 0, v___y_2114_);
lean_ctor_set(v___x_2117_, 1, v___y_2115_);
lean_ctor_set(v___x_2117_, 2, v_a_2116_);
lean_ctor_set(v___x_2117_, 3, v_manifestEntry_2107_);
v___x_2118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2117_);
return v___x_2118_;
}
v___jp_2119_:
{
lean_object* v___x_2126_; uint8_t v___x_2127_; 
v___x_2126_ = lean_array_get_size(v_a_2125_);
v___x_2127_ = lean_nat_dec_lt(v___y_2122_, v___x_2126_);
if (v___x_2127_ == 0)
{
lean_dec_ref(v_a_2125_);
v___y_2114_ = v___y_2120_;
v___y_2115_ = v___y_2121_;
v_a_2116_ = v_a_2124_;
goto v___jp_2113_;
}
else
{
lean_object* v___x_2128_; uint8_t v___x_2129_; 
v___x_2128_ = lean_box(0);
v___x_2129_ = lean_nat_dec_le(v___x_2126_, v___x_2126_);
if (v___x_2129_ == 0)
{
if (v___x_2127_ == 0)
{
lean_dec_ref(v_a_2125_);
v___y_2114_ = v___y_2120_;
v___y_2115_ = v___y_2121_;
v_a_2116_ = v_a_2124_;
goto v___jp_2113_;
}
else
{
size_t v___x_2130_; size_t v___x_2131_; lean_object* v___x_2132_; 
v___x_2130_ = ((size_t)0ULL);
v___x_2131_ = lean_usize_of_nat(v___x_2126_);
v___x_2132_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_2125_, v___x_2130_, v___x_2131_, v___x_2128_, v___y_2123_);
lean_dec_ref(v_a_2125_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_dec_ref(v___x_2132_);
v___y_2114_ = v___y_2120_;
v___y_2115_ = v___y_2121_;
v_a_2116_ = v_a_2124_;
goto v___jp_2113_;
}
else
{
lean_object* v_a_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2140_; 
lean_dec_ref(v_a_2124_);
lean_dec_ref(v___y_2121_);
lean_dec_ref(v___y_2120_);
lean_dec_ref(v_manifestEntry_2107_);
v_a_2133_ = lean_ctor_get(v___x_2132_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2132_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2135_ = v___x_2132_;
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_a_2133_);
lean_dec(v___x_2132_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2138_; 
if (v_isShared_2136_ == 0)
{
v___x_2138_ = v___x_2135_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_a_2133_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
return v___x_2138_;
}
}
}
}
}
else
{
size_t v___x_2141_; size_t v___x_2142_; lean_object* v___x_2143_; 
v___x_2141_ = ((size_t)0ULL);
v___x_2142_ = lean_usize_of_nat(v___x_2126_);
v___x_2143_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_2125_, v___x_2141_, v___x_2142_, v___x_2128_, v___y_2123_);
lean_dec_ref(v_a_2125_);
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_dec_ref(v___x_2143_);
v___y_2114_ = v___y_2120_;
v___y_2115_ = v___y_2121_;
v_a_2116_ = v_a_2124_;
goto v___jp_2113_;
}
else
{
lean_object* v_a_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2151_; 
lean_dec_ref(v_a_2124_);
lean_dec_ref(v___y_2121_);
lean_dec_ref(v___y_2120_);
lean_dec_ref(v_manifestEntry_2107_);
v_a_2144_ = lean_ctor_get(v___x_2143_, 0);
v_isSharedCheck_2151_ = !lean_is_exclusive(v___x_2143_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2146_ = v___x_2143_;
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_a_2144_);
lean_dec(v___x_2143_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v___x_2149_; 
if (v_isShared_2147_ == 0)
{
v___x_2149_ = v___x_2146_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v_a_2144_);
v___x_2149_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
return v___x_2149_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize___boxed(lean_object* v_manifestEntry_2398_, lean_object* v_lakeEnv_2399_, lean_object* v_wsDir_2400_, lean_object* v_relPkgsDir_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_){
_start:
{
lean_object* v_res_2404_; 
v_res_2404_ = l_Lake_PackageEntry_materialize(v_manifestEntry_2398_, v_lakeEnv_2399_, v_wsDir_2400_, v_relPkgsDir_2401_, v_a_2402_);
lean_dec_ref(v_a_2402_);
lean_dec_ref(v_lakeEnv_2399_);
return v_res_2404_;
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

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
lean_object* l_instMonadEST(lean_object*, lean_object*);
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
static lean_object* _init_l_Lake_instInhabitedMaterializedDep_default___closed__4(void){
_start:
{
lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_891_ = l_Lake_instInhabitedPackageEntry_default;
v___x_892_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__3));
v___x_893_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___x_894_ = l_System_instInhabitedFilePath_default;
v___x_895_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_895_, 0, v___x_894_);
lean_ctor_set(v___x_895_, 1, v___x_893_);
lean_ctor_set(v___x_895_, 2, v___x_892_);
lean_ctor_set(v___x_895_, 3, v___x_891_);
return v___x_895_;
}
}
static lean_object* _init_l_Lake_instInhabitedMaterializedDep_default(void){
_start:
{
lean_object* v___x_896_; 
v___x_896_ = lean_obj_once(&l_Lake_instInhabitedMaterializedDep_default___closed__4, &l_Lake_instInhabitedMaterializedDep_default___closed__4_once, _init_l_Lake_instInhabitedMaterializedDep_default___closed__4);
return v___x_896_;
}
}
static lean_object* _init_l_Lake_instInhabitedMaterializedDep(void){
_start:
{
lean_object* v___x_897_; 
v___x_897_ = l_Lake_instInhabitedMaterializedDep_default;
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_name(lean_object* v_self_898_){
_start:
{
lean_object* v_manifestEntry_899_; lean_object* v_name_900_; 
v_manifestEntry_899_ = lean_ctor_get(v_self_898_, 3);
v_name_900_ = lean_ctor_get(v_manifestEntry_899_, 0);
lean_inc(v_name_900_);
return v_name_900_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_name___boxed(lean_object* v_self_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_Lake_MaterializedDep_name(v_self_901_);
lean_dec_ref(v_self_901_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_scope(lean_object* v_self_903_){
_start:
{
lean_object* v_manifestEntry_904_; lean_object* v_scope_905_; 
v_manifestEntry_904_ = lean_ctor_get(v_self_903_, 3);
v_scope_905_ = lean_ctor_get(v_manifestEntry_904_, 1);
lean_inc_ref(v_scope_905_);
return v_scope_905_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_scope___boxed(lean_object* v_self_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l_Lake_MaterializedDep_scope(v_self_906_);
lean_dec_ref(v_self_906_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_manifestFile_x3f(lean_object* v_self_908_){
_start:
{
lean_object* v_manifestEntry_909_; lean_object* v_manifestFile_x3f_910_; 
v_manifestEntry_909_ = lean_ctor_get(v_self_908_, 3);
v_manifestFile_x3f_910_ = lean_ctor_get(v_manifestEntry_909_, 3);
lean_inc(v_manifestFile_x3f_910_);
return v_manifestFile_x3f_910_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_manifestFile_x3f___boxed(lean_object* v_self_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l_Lake_MaterializedDep_manifestFile_x3f(v_self_911_);
lean_dec_ref(v_self_911_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_configFile(lean_object* v_self_913_){
_start:
{
lean_object* v_manifestEntry_914_; lean_object* v_configFile_915_; 
v_manifestEntry_914_ = lean_ctor_get(v_self_913_, 3);
v_configFile_915_ = lean_ctor_get(v_manifestEntry_914_, 2);
lean_inc_ref(v_configFile_915_);
return v_configFile_915_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_configFile___boxed(lean_object* v_self_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l_Lake_MaterializedDep_configFile(v_self_916_);
lean_dec_ref(v_self_916_);
return v_res_917_;
}
}
LEAN_EXPORT uint8_t l_Lake_MaterializedDep_fixedToolchain(lean_object* v_self_918_){
_start:
{
lean_object* v_manifest_x3f_919_; 
v_manifest_x3f_919_ = lean_ctor_get(v_self_918_, 2);
if (lean_obj_tag(v_manifest_x3f_919_) == 1)
{
lean_object* v_a_920_; uint8_t v_fixedToolchain_921_; 
v_a_920_ = lean_ctor_get(v_manifest_x3f_919_, 0);
v_fixedToolchain_921_ = lean_ctor_get_uint8(v_a_920_, sizeof(void*)*4);
return v_fixedToolchain_921_;
}
else
{
uint8_t v___x_922_; 
v___x_922_ = 0;
return v___x_922_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_fixedToolchain___boxed(lean_object* v_self_923_){
_start:
{
uint8_t v_res_924_; lean_object* v_r_925_; 
v_res_924_ = l_Lake_MaterializedDep_fixedToolchain(v_self_923_);
lean_dec_ref(v_self_923_);
v_r_925_ = lean_box(v_res_924_);
return v_r_925_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorIdx(lean_object* v_x_926_){
_start:
{
switch(lean_obj_tag(v_x_926_))
{
case 0:
{
lean_object* v___x_927_; 
v___x_927_ = lean_unsigned_to_nat(0u);
return v___x_927_;
}
case 1:
{
lean_object* v___x_928_; 
v___x_928_ = lean_unsigned_to_nat(1u);
return v___x_928_;
}
default: 
{
lean_object* v___x_929_; 
v___x_929_ = lean_unsigned_to_nat(2u);
return v___x_929_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorIdx___boxed(lean_object* v_x_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorIdx(v_x_930_);
lean_dec(v_x_930_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(lean_object* v_t_932_, lean_object* v_k_933_){
_start:
{
if (lean_obj_tag(v_t_932_) == 0)
{
return v_k_933_;
}
else
{
lean_object* v_rev_934_; lean_object* v___x_935_; 
v_rev_934_ = lean_ctor_get(v_t_932_, 0);
lean_inc_ref(v_rev_934_);
lean_dec(v_t_932_);
v___x_935_ = lean_apply_1(v_k_933_, v_rev_934_);
return v___x_935_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim(lean_object* v_motive_936_, lean_object* v_ctorIdx_937_, lean_object* v_t_938_, lean_object* v_h_939_, lean_object* v_k_940_){
_start:
{
lean_object* v___x_941_; 
v___x_941_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(v_t_938_, v_k_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___boxed(lean_object* v_motive_942_, lean_object* v_ctorIdx_943_, lean_object* v_t_944_, lean_object* v_h_945_, lean_object* v_k_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim(v_motive_942_, v_ctorIdx_943_, v_t_944_, v_h_945_, v_k_946_);
lean_dec(v_ctorIdx_943_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_none_elim___redArg(lean_object* v_t_948_, lean_object* v_none_949_){
_start:
{
lean_object* v___x_950_; 
v___x_950_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(v_t_948_, v_none_949_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_none_elim(lean_object* v_motive_951_, lean_object* v_t_952_, lean_object* v_h_953_, lean_object* v_none_954_){
_start:
{
lean_object* v___x_955_; 
v___x_955_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(v_t_952_, v_none_954_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_git_elim___redArg(lean_object* v_t_956_, lean_object* v_git_957_){
_start:
{
lean_object* v___x_958_; 
v___x_958_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(v_t_956_, v_git_957_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_git_elim(lean_object* v_motive_959_, lean_object* v_t_960_, lean_object* v_h_961_, lean_object* v_git_962_){
_start:
{
lean_object* v___x_963_; 
v___x_963_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(v_t_960_, v_git_962_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ver_elim___redArg(lean_object* v_t_964_, lean_object* v_ver_965_){
_start:
{
lean_object* v___x_966_; 
v___x_966_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(v_t_964_, v_ver_965_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ver_elim(lean_object* v_motive_967_, lean_object* v_t_968_, lean_object* v_h_969_, lean_object* v_ver_970_){
_start:
{
lean_object* v___x_971_; 
v___x_971_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(v_t_968_, v_ver_970_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed(lean_object* v_scope_980_, lean_object* v_name_981_, lean_object* v_ver_982_){
_start:
{
lean_object* v_fst_984_; lean_object* v_snd_985_; 
switch(lean_obj_tag(v_ver_982_))
{
case 0:
{
lean_object* v___x_1006_; 
v___x_1006_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v_fst_984_ = v___x_1006_;
v_snd_985_ = v___x_1006_;
goto v___jp_983_;
}
case 1:
{
lean_object* v_rev_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1022_; 
v_rev_1007_ = lean_ctor_get(v_ver_982_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v_ver_982_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1009_ = v_ver_982_;
v_isShared_1010_ = v_isSharedCheck_1022_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_rev_1007_);
lean_dec(v_ver_982_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1022_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1014_; 
v___x_1011_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__5));
v___x_1012_ = l_String_quote(v_rev_1007_);
if (v_isShared_1010_ == 0)
{
lean_ctor_set_tag(v___x_1009_, 3);
lean_ctor_set(v___x_1009_, 0, v___x_1012_);
v___x_1014_ = v___x_1009_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v___x_1012_);
v___x_1014_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1015_ = l_Std_Format_defWidth;
v___x_1016_ = lean_unsigned_to_nat(0u);
v___x_1017_ = l_Std_Format_pretty(v___x_1014_, v___x_1015_, v___x_1016_, v___x_1016_);
v___x_1018_ = lean_string_append(v___x_1011_, v___x_1017_);
v___x_1019_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__6));
v___x_1020_ = lean_string_append(v___x_1019_, v___x_1017_);
lean_dec_ref(v___x_1017_);
v_fst_984_ = v___x_1018_;
v_snd_985_ = v___x_1020_;
goto v___jp_983_;
}
}
}
default: 
{
lean_object* v_ver_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1039_; 
v_ver_1023_ = lean_ctor_get(v_ver_982_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v_ver_982_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1025_ = v_ver_982_;
v_isShared_1026_ = v_isSharedCheck_1039_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_ver_1023_);
lean_dec(v_ver_982_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1039_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v_toString_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1031_; 
v_toString_1027_ = lean_ctor_get(v_ver_1023_, 0);
lean_inc_ref(v_toString_1027_);
lean_dec_ref(v_ver_1023_);
v___x_1028_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__5));
v___x_1029_ = l_String_quote(v_toString_1027_);
if (v_isShared_1026_ == 0)
{
lean_ctor_set_tag(v___x_1025_, 3);
lean_ctor_set(v___x_1025_, 0, v___x_1029_);
v___x_1031_ = v___x_1025_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v___x_1029_);
v___x_1031_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1032_ = l_Std_Format_defWidth;
v___x_1033_ = lean_unsigned_to_nat(0u);
v___x_1034_ = l_Std_Format_pretty(v___x_1031_, v___x_1032_, v___x_1033_, v___x_1033_);
v___x_1035_ = lean_string_append(v___x_1028_, v___x_1034_);
v___x_1036_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__7));
v___x_1037_ = lean_string_append(v___x_1036_, v___x_1034_);
lean_dec_ref(v___x_1034_);
v_fst_984_ = v___x_1035_;
v_snd_985_ = v___x_1037_;
goto v___jp_983_;
}
}
}
}
v___jp_983_:
{
lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_986_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
lean_inc_ref(v_scope_980_);
v___x_987_ = lean_string_append(v_scope_980_, v___x_986_);
v___x_988_ = lean_string_append(v___x_987_, v_name_981_);
v___x_989_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__1));
v___x_990_ = lean_string_append(v___x_988_, v___x_989_);
v___x_991_ = lean_string_append(v___x_990_, v_scope_980_);
v___x_992_ = lean_string_append(v___x_991_, v___x_986_);
v___x_993_ = lean_string_append(v___x_992_, v_name_981_);
v___x_994_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__2));
v___x_995_ = lean_string_append(v___x_993_, v___x_994_);
v___x_996_ = lean_string_append(v___x_995_, v_fst_984_);
lean_dec_ref(v_fst_984_);
v___x_997_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__3));
v___x_998_ = lean_string_append(v___x_996_, v___x_997_);
v___x_999_ = lean_string_append(v___x_998_, v_scope_980_);
lean_dec_ref(v_scope_980_);
v___x_1000_ = lean_string_append(v___x_999_, v___x_986_);
v___x_1001_ = lean_string_append(v___x_1000_, v_name_981_);
v___x_1002_ = lean_string_append(v___x_1001_, v___x_994_);
v___x_1003_ = lean_string_append(v___x_1002_, v_snd_985_);
lean_dec_ref(v_snd_985_);
v___x_1004_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__4));
v___x_1005_ = lean_string_append(v___x_1003_, v___x_1004_);
return v___x_1005_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___boxed(lean_object* v_scope_1040_, lean_object* v_name_1041_, lean_object* v_ver_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed(v_scope_1040_, v_name_1041_, v_ver_1042_);
lean_dec_ref(v_name_1041_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___lam__0(lean_object* v_x_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_){
_start:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1048_ = lean_apply_2(v___y_1046_, v___y_1045_, lean_box(0));
v___x_1049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1048_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___lam__0___boxed(lean_object* v_x_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_){
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___lam__0(v_x_1050_, v___y_1051_, v___y_1052_);
return v_res_1054_;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1(void){
_start:
{
lean_object* v___x_1056_; 
v___x_1056_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_1056_;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__2(void){
_start:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1057_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1, &l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1_once, _init_l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1);
v___x_1058_ = l_ReaderT_instMonad___redArg(v___x_1057_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep(lean_object* v_dep_1059_, uint8_t v_inherited_1060_, lean_object* v_pkgDir_1061_, lean_object* v_relPkgDir_1062_, lean_object* v_remoteUrl_1063_, lean_object* v_src_1064_, lean_object* v_a_1065_){
_start:
{
lean_object* v_a_1068_; lean_object* v___f_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v_val_1082_; lean_object* v___x_1110_; 
v___f_1076_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0));
v___x_1077_ = l_Lake_defaultManifestFile;
v___x_1078_ = l_Lake_joinRelative(v_pkgDir_1061_, v___x_1077_);
v___x_1079_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__2, &l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__2_once, _init_l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__2);
v___x_1080_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
v___x_1110_ = l_Lake_Manifest_load(v___x_1078_);
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1118_; 
v_a_1111_ = lean_ctor_get(v___x_1110_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1113_ = v___x_1110_;
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_a_1111_);
lean_dec(v___x_1110_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1116_; 
if (v_isShared_1114_ == 0)
{
lean_ctor_set_tag(v___x_1113_, 1);
v___x_1116_ = v___x_1113_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_a_1111_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
v_val_1082_ = v___x_1116_;
goto v___jp_1081_;
}
}
}
else
{
lean_object* v_a_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1126_; 
v_a_1119_ = lean_ctor_get(v___x_1110_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1121_ = v___x_1110_;
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_a_1119_);
lean_dec(v___x_1110_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1124_; 
if (v_isShared_1122_ == 0)
{
lean_ctor_set_tag(v___x_1121_, 0);
v___x_1124_ = v___x_1121_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_a_1119_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
v_val_1082_ = v___x_1124_;
goto v___jp_1081_;
}
}
}
v___jp_1067_:
{
lean_object* v_name_1069_; lean_object* v_scope_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
v_name_1069_ = lean_ctor_get(v_dep_1059_, 0);
v_scope_1070_ = lean_ctor_get(v_dep_1059_, 1);
v___x_1071_ = l_Lake_defaultConfigFile;
v___x_1072_ = lean_box(0);
lean_inc_ref(v_scope_1070_);
lean_inc(v_name_1069_);
v___x_1073_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1073_, 0, v_name_1069_);
lean_ctor_set(v___x_1073_, 1, v_scope_1070_);
lean_ctor_set(v___x_1073_, 2, v___x_1071_);
lean_ctor_set(v___x_1073_, 3, v___x_1072_);
lean_ctor_set(v___x_1073_, 4, v_src_1064_);
lean_ctor_set_uint8(v___x_1073_, sizeof(void*)*5, v_inherited_1060_);
v___x_1074_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1074_, 0, v_relPkgDir_1062_);
lean_ctor_set(v___x_1074_, 1, v_remoteUrl_1063_);
lean_ctor_set(v___x_1074_, 2, v_a_1068_);
lean_ctor_set(v___x_1074_, 3, v___x_1073_);
v___x_1075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1074_);
return v___x_1075_;
}
v___jp_1081_:
{
uint8_t v___x_1083_; 
v___x_1083_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_1083_ == 0)
{
lean_dec_ref(v_a_1065_);
v_a_1068_ = v_val_1082_;
goto v___jp_1067_;
}
else
{
lean_object* v___x_1084_; uint8_t v___x_1085_; 
v___x_1084_ = lean_box(0);
v___x_1085_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_1085_ == 0)
{
if (v___x_1083_ == 0)
{
lean_dec_ref(v_a_1065_);
v_a_1068_ = v_val_1082_;
goto v___jp_1067_;
}
else
{
size_t v___x_1086_; size_t v___x_1087_; lean_object* v___x_1069__overap_1088_; lean_object* v___x_1089_; 
v___x_1086_ = ((size_t)0ULL);
v___x_1087_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_1069__overap_1088_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1079_, v___f_1076_, v___x_1080_, v___x_1086_, v___x_1087_, v___x_1084_);
v___x_1089_ = lean_apply_2(v___x_1069__overap_1088_, v_a_1065_, lean_box(0));
if (lean_obj_tag(v___x_1089_) == 0)
{
lean_dec_ref(v___x_1089_);
v_a_1068_ = v_val_1082_;
goto v___jp_1067_;
}
else
{
lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1097_; 
lean_dec_ref(v_val_1082_);
lean_dec_ref(v_src_1064_);
lean_dec_ref(v_remoteUrl_1063_);
lean_dec_ref(v_relPkgDir_1062_);
v_a_1090_ = lean_ctor_get(v___x_1089_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1092_ = v___x_1089_;
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v___x_1089_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1095_; 
if (v_isShared_1093_ == 0)
{
v___x_1095_ = v___x_1092_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_a_1090_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
}
}
}
else
{
size_t v___x_1098_; size_t v___x_1099_; lean_object* v___x_1079__overap_1100_; lean_object* v___x_1101_; 
v___x_1098_ = ((size_t)0ULL);
v___x_1099_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_1079__overap_1100_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1079_, v___f_1076_, v___x_1080_, v___x_1098_, v___x_1099_, v___x_1084_);
v___x_1101_ = lean_apply_2(v___x_1079__overap_1100_, v_a_1065_, lean_box(0));
if (lean_obj_tag(v___x_1101_) == 0)
{
lean_dec_ref(v___x_1101_);
v_a_1068_ = v_val_1082_;
goto v___jp_1067_;
}
else
{
lean_object* v_a_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1109_; 
lean_dec_ref(v_val_1082_);
lean_dec_ref(v_src_1064_);
lean_dec_ref(v_remoteUrl_1063_);
lean_dec_ref(v_relPkgDir_1062_);
v_a_1102_ = lean_ctor_get(v___x_1101_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1104_ = v___x_1101_;
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_a_1102_);
lean_dec(v___x_1101_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1107_; 
if (v_isShared_1105_ == 0)
{
v___x_1107_ = v___x_1104_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_a_1102_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
return v___x_1107_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___boxed(lean_object* v_dep_1127_, lean_object* v_inherited_1128_, lean_object* v_pkgDir_1129_, lean_object* v_relPkgDir_1130_, lean_object* v_remoteUrl_1131_, lean_object* v_src_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_){
_start:
{
uint8_t v_inherited_boxed_1135_; lean_object* v_res_1136_; 
v_inherited_boxed_1135_ = lean_unbox(v_inherited_1128_);
v_res_1136_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep(v_dep_1127_, v_inherited_boxed_1135_, v_pkgDir_1129_, v_relPkgDir_1130_, v_remoteUrl_1131_, v_src_1132_, v_a_1133_);
lean_dec_ref(v_dep_1127_);
return v_res_1136_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(lean_object* v_a_1137_, lean_object* v_name_1138_, lean_object* v_repo_1139_, lean_object* v_url_1140_, lean_object* v_rev_x3f_1141_){
_start:
{
uint8_t v___x_1143_; lean_object* v___x_1147_; uint8_t v___x_1148_; 
v___x_1143_ = l_System_FilePath_isDir(v_repo_1139_);
v___x_1147_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
v___x_1148_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_1148_ == 0)
{
goto v___jp_1144_;
}
else
{
lean_object* v___x_1149_; uint8_t v___x_1150_; 
v___x_1149_ = lean_box(0);
v___x_1150_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_1150_ == 0)
{
if (v___x_1148_ == 0)
{
goto v___jp_1144_;
}
else
{
size_t v___x_1151_; size_t v___x_1152_; lean_object* v___x_1153_; 
v___x_1151_ = ((size_t)0ULL);
v___x_1152_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
lean_inc_ref(v_a_1137_);
v___x_1153_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v___x_1147_, v___x_1151_, v___x_1152_, v___x_1149_, v_a_1137_);
if (lean_obj_tag(v___x_1153_) == 0)
{
lean_dec_ref(v___x_1153_);
goto v___jp_1144_;
}
else
{
lean_dec(v_rev_x3f_1141_);
lean_dec_ref(v_url_1140_);
lean_dec_ref(v_repo_1139_);
lean_dec_ref(v_name_1138_);
lean_dec_ref(v_a_1137_);
return v___x_1153_;
}
}
}
else
{
size_t v___x_1154_; size_t v___x_1155_; lean_object* v___x_1156_; 
v___x_1154_ = ((size_t)0ULL);
v___x_1155_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
lean_inc_ref(v_a_1137_);
v___x_1156_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v___x_1147_, v___x_1154_, v___x_1155_, v___x_1149_, v_a_1137_);
if (lean_obj_tag(v___x_1156_) == 0)
{
lean_dec_ref(v___x_1156_);
goto v___jp_1144_;
}
else
{
lean_dec(v_rev_x3f_1141_);
lean_dec_ref(v_url_1140_);
lean_dec_ref(v_repo_1139_);
lean_dec_ref(v_name_1138_);
lean_dec_ref(v_a_1137_);
return v___x_1156_;
}
}
}
v___jp_1144_:
{
if (v___x_1143_ == 0)
{
lean_object* v___x_1145_; 
v___x_1145_ = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(v_a_1137_, v_name_1138_, v_repo_1139_, v_url_1140_, v_rev_x3f_1141_);
return v___x_1145_;
}
else
{
lean_object* v___x_1146_; 
v___x_1146_ = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1137_, v_name_1138_, v_repo_1139_, v_url_1140_, v_rev_x3f_1141_);
return v___x_1146_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0___boxed(lean_object* v_a_1157_, lean_object* v_name_1158_, lean_object* v_repo_1159_, lean_object* v_url_1160_, lean_object* v_rev_x3f_1161_, lean_object* v_a_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(v_a_1157_, v_name_1158_, v_repo_1159_, v_url_1160_, v_rev_x3f_1161_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit(lean_object* v_dep_1164_, uint8_t v_inherited_1165_, lean_object* v_lakeEnv_1166_, lean_object* v_wsDir_1167_, lean_object* v_name_1168_, lean_object* v_relPkgDir_1169_, lean_object* v_gitUrl_1170_, lean_object* v_remoteUrl_1171_, lean_object* v_inputRev_x3f_1172_, lean_object* v_subDir_x3f_1173_, lean_object* v_a_1174_){
_start:
{
lean_object* v_pkgUrlMap_1179_; lean_object* v_name_1180_; lean_object* v_scope_1181_; lean_object* v___y_1183_; lean_object* v___y_1184_; lean_object* v_a_1185_; lean_object* v___y_1192_; lean_object* v___y_1193_; lean_object* v___y_1194_; lean_object* v___y_1195_; lean_object* v_val_1196_; lean_object* v_pkgDir_1223_; lean_object* v___y_1225_; lean_object* v___y_1226_; lean_object* v___y_1227_; lean_object* v___y_1251_; lean_object* v_a_1252_; lean_object* v___y_1256_; lean_object* v___x_1333_; 
v_pkgUrlMap_1179_ = lean_ctor_get(v_lakeEnv_1166_, 5);
v_name_1180_ = lean_ctor_get(v_dep_1164_, 0);
v_scope_1181_ = lean_ctor_get(v_dep_1164_, 1);
lean_inc_ref(v_relPkgDir_1169_);
v_pkgDir_1223_ = l_Lake_joinRelative(v_wsDir_1167_, v_relPkgDir_1169_);
v___x_1333_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgUrlMap_1179_, v_name_1180_);
if (lean_obj_tag(v___x_1333_) == 0)
{
v___y_1256_ = v_gitUrl_1170_;
goto v___jp_1255_;
}
else
{
lean_object* v_val_1334_; 
lean_dec_ref(v_gitUrl_1170_);
v_val_1334_ = lean_ctor_get(v___x_1333_, 0);
lean_inc(v_val_1334_);
lean_dec_ref(v___x_1333_);
v___y_1256_ = v_val_1334_;
goto v___jp_1255_;
}
v___jp_1176_:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1177_ = lean_box(0);
v___x_1178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1177_);
return v___x_1178_;
}
v___jp_1182_:
{
lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1186_ = l_Lake_defaultConfigFile;
v___x_1187_ = lean_box(0);
lean_inc_ref(v_scope_1181_);
lean_inc(v_name_1180_);
v___x_1188_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1188_, 0, v_name_1180_);
lean_ctor_set(v___x_1188_, 1, v_scope_1181_);
lean_ctor_set(v___x_1188_, 2, v___x_1186_);
lean_ctor_set(v___x_1188_, 3, v___x_1187_);
lean_ctor_set(v___x_1188_, 4, v___y_1184_);
lean_ctor_set_uint8(v___x_1188_, sizeof(void*)*5, v_inherited_1165_);
v___x_1189_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1189_, 0, v___y_1183_);
lean_ctor_set(v___x_1189_, 1, v_remoteUrl_1171_);
lean_ctor_set(v___x_1189_, 2, v_a_1185_);
lean_ctor_set(v___x_1189_, 3, v___x_1188_);
v___x_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1189_);
return v___x_1190_;
}
v___jp_1191_:
{
lean_object* v___x_1197_; uint8_t v___x_1198_; 
v___x_1197_ = lean_array_get_size(v___y_1193_);
v___x_1198_ = lean_nat_dec_lt(v___y_1194_, v___x_1197_);
if (v___x_1198_ == 0)
{
lean_dec_ref(v___y_1193_);
lean_dec_ref(v_a_1174_);
v___y_1183_ = v___y_1192_;
v___y_1184_ = v___y_1195_;
v_a_1185_ = v_val_1196_;
goto v___jp_1182_;
}
else
{
lean_object* v___x_1199_; uint8_t v___x_1200_; 
v___x_1199_ = lean_box(0);
v___x_1200_ = lean_nat_dec_le(v___x_1197_, v___x_1197_);
if (v___x_1200_ == 0)
{
if (v___x_1198_ == 0)
{
lean_dec_ref(v___y_1193_);
lean_dec_ref(v_a_1174_);
v___y_1183_ = v___y_1192_;
v___y_1184_ = v___y_1195_;
v_a_1185_ = v_val_1196_;
goto v___jp_1182_;
}
else
{
size_t v___x_1201_; size_t v___x_1202_; lean_object* v___x_1203_; 
v___x_1201_ = ((size_t)0ULL);
v___x_1202_ = lean_usize_of_nat(v___x_1197_);
v___x_1203_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v___y_1193_, v___x_1201_, v___x_1202_, v___x_1199_, v_a_1174_);
lean_dec_ref(v___y_1193_);
if (lean_obj_tag(v___x_1203_) == 0)
{
lean_dec_ref(v___x_1203_);
v___y_1183_ = v___y_1192_;
v___y_1184_ = v___y_1195_;
v_a_1185_ = v_val_1196_;
goto v___jp_1182_;
}
else
{
lean_object* v_a_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1211_; 
lean_dec_ref(v_val_1196_);
lean_dec_ref(v___y_1195_);
lean_dec_ref(v___y_1192_);
lean_dec_ref(v_remoteUrl_1171_);
v_a_1204_ = lean_ctor_get(v___x_1203_, 0);
v_isSharedCheck_1211_ = !lean_is_exclusive(v___x_1203_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1206_ = v___x_1203_;
v_isShared_1207_ = v_isSharedCheck_1211_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_a_1204_);
lean_dec(v___x_1203_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1211_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v___x_1209_; 
if (v_isShared_1207_ == 0)
{
v___x_1209_ = v___x_1206_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v_a_1204_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
}
}
}
else
{
size_t v___x_1212_; size_t v___x_1213_; lean_object* v___x_1214_; 
v___x_1212_ = ((size_t)0ULL);
v___x_1213_ = lean_usize_of_nat(v___x_1197_);
v___x_1214_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v___y_1193_, v___x_1212_, v___x_1213_, v___x_1199_, v_a_1174_);
lean_dec_ref(v___y_1193_);
if (lean_obj_tag(v___x_1214_) == 0)
{
lean_dec_ref(v___x_1214_);
v___y_1183_ = v___y_1192_;
v___y_1184_ = v___y_1195_;
v_a_1185_ = v_val_1196_;
goto v___jp_1182_;
}
else
{
lean_object* v_a_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1222_; 
lean_dec_ref(v_val_1196_);
lean_dec_ref(v___y_1195_);
lean_dec_ref(v___y_1192_);
lean_dec_ref(v_remoteUrl_1171_);
v_a_1215_ = lean_ctor_get(v___x_1214_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1217_ = v___x_1214_;
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_a_1215_);
lean_dec(v___x_1214_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1220_; 
if (v_isShared_1218_ == 0)
{
v___x_1220_ = v___x_1217_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_a_1215_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
return v___x_1220_;
}
}
}
}
}
}
v___jp_1224_:
{
lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1228_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1228_, 0, v___y_1225_);
lean_ctor_set(v___x_1228_, 1, v___y_1226_);
lean_ctor_set(v___x_1228_, 2, v_inputRev_x3f_1172_);
lean_ctor_set(v___x_1228_, 3, v_subDir_x3f_1173_);
v___x_1229_ = l_Lake_defaultManifestFile;
v___x_1230_ = l_Lake_joinRelative(v_pkgDir_1223_, v___x_1229_);
v___x_1231_ = lean_unsigned_to_nat(0u);
v___x_1232_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
v___x_1233_ = l_Lake_Manifest_load(v___x_1230_);
if (lean_obj_tag(v___x_1233_) == 0)
{
lean_object* v_a_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1241_; 
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
lean_ctor_set_tag(v___x_1236_, 1);
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
v___y_1192_ = v___y_1227_;
v___y_1193_ = v___x_1232_;
v___y_1194_ = v___x_1231_;
v___y_1195_ = v___x_1228_;
v_val_1196_ = v___x_1239_;
goto v___jp_1191_;
}
}
}
else
{
lean_object* v_a_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1249_; 
v_a_1242_ = lean_ctor_get(v___x_1233_, 0);
v_isSharedCheck_1249_ = !lean_is_exclusive(v___x_1233_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1244_ = v___x_1233_;
v_isShared_1245_ = v_isSharedCheck_1249_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_a_1242_);
lean_dec(v___x_1233_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1249_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1247_; 
if (v_isShared_1245_ == 0)
{
lean_ctor_set_tag(v___x_1244_, 0);
v___x_1247_ = v___x_1244_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_a_1242_);
v___x_1247_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
v___y_1192_ = v___y_1227_;
v___y_1193_ = v___x_1232_;
v___y_1194_ = v___x_1231_;
v___y_1195_ = v___x_1228_;
v_val_1196_ = v___x_1247_;
goto v___jp_1191_;
}
}
}
}
v___jp_1250_:
{
if (lean_obj_tag(v_subDir_x3f_1173_) == 1)
{
lean_object* v_val_1253_; lean_object* v___x_1254_; 
v_val_1253_ = lean_ctor_get(v_subDir_x3f_1173_, 0);
lean_inc(v_val_1253_);
v___x_1254_ = l_Lake_joinRelative(v_relPkgDir_1169_, v_val_1253_);
v___y_1225_ = v___y_1251_;
v___y_1226_ = v_a_1252_;
v___y_1227_ = v___x_1254_;
goto v___jp_1224_;
}
else
{
v___y_1225_ = v___y_1251_;
v___y_1226_ = v_a_1252_;
v___y_1227_ = v_relPkgDir_1169_;
goto v___jp_1224_;
}
}
v___jp_1255_:
{
lean_object* v___x_1257_; 
lean_inc(v_inputRev_x3f_1172_);
lean_inc_ref(v___y_1256_);
lean_inc_ref(v_pkgDir_1223_);
lean_inc_ref(v_a_1174_);
v___x_1257_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(v_a_1174_, v_name_1168_, v_pkgDir_1223_, v___y_1256_, v_inputRev_x3f_1172_);
if (lean_obj_tag(v___x_1257_) == 0)
{
lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1323_; 
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1323_ == 0)
{
lean_object* v_unused_1324_; 
v_unused_1324_ = lean_ctor_get(v___x_1257_, 0);
lean_dec(v_unused_1324_);
v___x_1259_ = v___x_1257_;
v_isShared_1260_ = v_isSharedCheck_1323_;
goto v_resetjp_1258_;
}
else
{
lean_dec(v___x_1257_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1323_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1261_ = lean_unsigned_to_nat(0u);
v___x_1262_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
lean_inc_ref(v_pkgDir_1223_);
v___x_1263_ = l_Lake_GitRepo_getHeadRevision(v_pkgDir_1223_, v___x_1262_);
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_object* v_a_1264_; lean_object* v_a_1265_; lean_object* v___x_1266_; uint8_t v___x_1267_; 
lean_del_object(v___x_1259_);
v_a_1264_ = lean_ctor_get(v___x_1263_, 0);
lean_inc(v_a_1264_);
v_a_1265_ = lean_ctor_get(v___x_1263_, 1);
lean_inc(v_a_1265_);
lean_dec_ref(v___x_1263_);
v___x_1266_ = lean_array_get_size(v_a_1265_);
v___x_1267_ = lean_nat_dec_lt(v___x_1261_, v___x_1266_);
if (v___x_1267_ == 0)
{
lean_dec(v_a_1265_);
v___y_1251_ = v___y_1256_;
v_a_1252_ = v_a_1264_;
goto v___jp_1250_;
}
else
{
lean_object* v___x_1268_; uint8_t v___x_1269_; 
v___x_1268_ = lean_box(0);
v___x_1269_ = lean_nat_dec_le(v___x_1266_, v___x_1266_);
if (v___x_1269_ == 0)
{
if (v___x_1267_ == 0)
{
lean_dec(v_a_1265_);
v___y_1251_ = v___y_1256_;
v_a_1252_ = v_a_1264_;
goto v___jp_1250_;
}
else
{
size_t v___x_1270_; size_t v___x_1271_; lean_object* v___x_1272_; 
v___x_1270_ = ((size_t)0ULL);
v___x_1271_ = lean_usize_of_nat(v___x_1266_);
lean_inc_ref(v_a_1174_);
v___x_1272_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_1265_, v___x_1270_, v___x_1271_, v___x_1268_, v_a_1174_);
lean_dec(v_a_1265_);
if (lean_obj_tag(v___x_1272_) == 0)
{
lean_dec_ref(v___x_1272_);
v___y_1251_ = v___y_1256_;
v_a_1252_ = v_a_1264_;
goto v___jp_1250_;
}
else
{
lean_object* v_a_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1280_; 
lean_dec(v_a_1264_);
lean_dec_ref(v___y_1256_);
lean_dec_ref(v_pkgDir_1223_);
lean_dec_ref(v_a_1174_);
lean_dec(v_subDir_x3f_1173_);
lean_dec(v_inputRev_x3f_1172_);
lean_dec_ref(v_remoteUrl_1171_);
lean_dec_ref(v_relPkgDir_1169_);
v_a_1273_ = lean_ctor_get(v___x_1272_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1275_ = v___x_1272_;
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_a_1273_);
lean_dec(v___x_1272_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1278_; 
if (v_isShared_1276_ == 0)
{
v___x_1278_ = v___x_1275_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_a_1273_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
}
}
}
else
{
size_t v___x_1281_; size_t v___x_1282_; lean_object* v___x_1283_; 
v___x_1281_ = ((size_t)0ULL);
v___x_1282_ = lean_usize_of_nat(v___x_1266_);
lean_inc_ref(v_a_1174_);
v___x_1283_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_1265_, v___x_1281_, v___x_1282_, v___x_1268_, v_a_1174_);
lean_dec(v_a_1265_);
if (lean_obj_tag(v___x_1283_) == 0)
{
lean_dec_ref(v___x_1283_);
v___y_1251_ = v___y_1256_;
v_a_1252_ = v_a_1264_;
goto v___jp_1250_;
}
else
{
lean_object* v_a_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1291_; 
lean_dec(v_a_1264_);
lean_dec_ref(v___y_1256_);
lean_dec_ref(v_pkgDir_1223_);
lean_dec_ref(v_a_1174_);
lean_dec(v_subDir_x3f_1173_);
lean_dec(v_inputRev_x3f_1172_);
lean_dec_ref(v_remoteUrl_1171_);
lean_dec_ref(v_relPkgDir_1169_);
v_a_1284_ = lean_ctor_get(v___x_1283_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1286_ = v___x_1283_;
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_a_1284_);
lean_dec(v___x_1283_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1289_; 
if (v_isShared_1287_ == 0)
{
v___x_1289_ = v___x_1286_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_a_1284_);
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
}
}
else
{
lean_object* v_a_1292_; lean_object* v___x_1293_; uint8_t v___x_1294_; 
lean_dec_ref(v___y_1256_);
lean_dec_ref(v_pkgDir_1223_);
lean_dec(v_subDir_x3f_1173_);
lean_dec(v_inputRev_x3f_1172_);
lean_dec_ref(v_remoteUrl_1171_);
lean_dec_ref(v_relPkgDir_1169_);
v_a_1292_ = lean_ctor_get(v___x_1263_, 1);
lean_inc(v_a_1292_);
lean_dec_ref(v___x_1263_);
v___x_1293_ = lean_array_get_size(v_a_1292_);
v___x_1294_ = lean_nat_dec_lt(v___x_1261_, v___x_1293_);
if (v___x_1294_ == 0)
{
lean_object* v___x_1295_; lean_object* v___x_1297_; 
lean_dec(v_a_1292_);
lean_dec_ref(v_a_1174_);
v___x_1295_ = lean_box(0);
if (v_isShared_1260_ == 0)
{
lean_ctor_set_tag(v___x_1259_, 1);
lean_ctor_set(v___x_1259_, 0, v___x_1295_);
v___x_1297_ = v___x_1259_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v___x_1295_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
else
{
lean_object* v___x_1299_; uint8_t v___x_1300_; 
lean_del_object(v___x_1259_);
v___x_1299_ = lean_box(0);
v___x_1300_ = lean_nat_dec_le(v___x_1293_, v___x_1293_);
if (v___x_1300_ == 0)
{
if (v___x_1294_ == 0)
{
lean_dec(v_a_1292_);
lean_dec_ref(v_a_1174_);
goto v___jp_1176_;
}
else
{
size_t v___x_1301_; size_t v___x_1302_; lean_object* v___x_1303_; 
v___x_1301_ = ((size_t)0ULL);
v___x_1302_ = lean_usize_of_nat(v___x_1293_);
v___x_1303_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_1292_, v___x_1301_, v___x_1302_, v___x_1299_, v_a_1174_);
lean_dec(v_a_1292_);
if (lean_obj_tag(v___x_1303_) == 0)
{
lean_dec_ref(v___x_1303_);
goto v___jp_1176_;
}
else
{
lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1311_; 
v_a_1304_ = lean_ctor_get(v___x_1303_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1303_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1306_ = v___x_1303_;
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_dec(v___x_1303_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1309_; 
if (v_isShared_1307_ == 0)
{
v___x_1309_ = v___x_1306_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_a_1304_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
}
}
else
{
size_t v___x_1312_; size_t v___x_1313_; lean_object* v___x_1314_; 
v___x_1312_ = ((size_t)0ULL);
v___x_1313_ = lean_usize_of_nat(v___x_1293_);
v___x_1314_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_1292_, v___x_1312_, v___x_1313_, v___x_1299_, v_a_1174_);
lean_dec(v_a_1292_);
if (lean_obj_tag(v___x_1314_) == 0)
{
lean_dec_ref(v___x_1314_);
goto v___jp_1176_;
}
else
{
lean_object* v_a_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1322_; 
v_a_1315_ = lean_ctor_get(v___x_1314_, 0);
v_isSharedCheck_1322_ = !lean_is_exclusive(v___x_1314_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1317_ = v___x_1314_;
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_a_1315_);
lean_dec(v___x_1314_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___x_1320_; 
if (v_isShared_1318_ == 0)
{
v___x_1320_ = v___x_1317_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_a_1315_);
v___x_1320_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
return v___x_1320_;
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
lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1332_; 
lean_dec_ref(v___y_1256_);
lean_dec_ref(v_pkgDir_1223_);
lean_dec_ref(v_a_1174_);
lean_dec(v_subDir_x3f_1173_);
lean_dec(v_inputRev_x3f_1172_);
lean_dec_ref(v_remoteUrl_1171_);
lean_dec_ref(v_relPkgDir_1169_);
v_a_1325_ = lean_ctor_get(v___x_1257_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1327_ = v___x_1257_;
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_a_1325_);
lean_dec(v___x_1257_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1330_; 
if (v_isShared_1328_ == 0)
{
v___x_1330_ = v___x_1327_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_a_1325_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___boxed(lean_object* v_dep_1335_, lean_object* v_inherited_1336_, lean_object* v_lakeEnv_1337_, lean_object* v_wsDir_1338_, lean_object* v_name_1339_, lean_object* v_relPkgDir_1340_, lean_object* v_gitUrl_1341_, lean_object* v_remoteUrl_1342_, lean_object* v_inputRev_x3f_1343_, lean_object* v_subDir_x3f_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_){
_start:
{
uint8_t v_inherited_boxed_1347_; lean_object* v_res_1348_; 
v_inherited_boxed_1347_ = lean_unbox(v_inherited_1336_);
v_res_1348_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit(v_dep_1335_, v_inherited_boxed_1347_, v_lakeEnv_1337_, v_wsDir_1338_, v_name_1339_, v_relPkgDir_1340_, v_gitUrl_1341_, v_remoteUrl_1342_, v_inputRev_x3f_1343_, v_subDir_x3f_1344_, v_a_1345_);
lean_dec_ref(v_lakeEnv_1337_);
lean_dec_ref(v_dep_1335_);
return v_res_1348_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(lean_object* v_a_1349_, lean_object* v_dep_1350_, uint8_t v_inherited_1351_, lean_object* v_lakeEnv_1352_, lean_object* v_wsDir_1353_, lean_object* v_name_1354_, lean_object* v_relPkgDir_1355_, lean_object* v_gitUrl_1356_, lean_object* v_remoteUrl_1357_, lean_object* v_inputRev_x3f_1358_, lean_object* v_subDir_x3f_1359_){
_start:
{
lean_object* v_pkgUrlMap_1364_; lean_object* v_name_1365_; lean_object* v_scope_1366_; lean_object* v___y_1368_; lean_object* v___y_1369_; lean_object* v_a_1370_; lean_object* v___y_1377_; lean_object* v___y_1378_; lean_object* v___y_1379_; lean_object* v___y_1380_; lean_object* v_val_1381_; lean_object* v_pkgDir_1408_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___y_1436_; lean_object* v_a_1437_; lean_object* v___y_1441_; lean_object* v___x_1518_; 
v_pkgUrlMap_1364_ = lean_ctor_get(v_lakeEnv_1352_, 5);
v_name_1365_ = lean_ctor_get(v_dep_1350_, 0);
v_scope_1366_ = lean_ctor_get(v_dep_1350_, 1);
lean_inc_ref(v_relPkgDir_1355_);
v_pkgDir_1408_ = l_Lake_joinRelative(v_wsDir_1353_, v_relPkgDir_1355_);
v___x_1518_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgUrlMap_1364_, v_name_1365_);
if (lean_obj_tag(v___x_1518_) == 0)
{
v___y_1441_ = v_gitUrl_1356_;
goto v___jp_1440_;
}
else
{
lean_object* v_val_1519_; 
lean_dec_ref(v_gitUrl_1356_);
v_val_1519_ = lean_ctor_get(v___x_1518_, 0);
lean_inc(v_val_1519_);
lean_dec_ref(v___x_1518_);
v___y_1441_ = v_val_1519_;
goto v___jp_1440_;
}
v___jp_1361_:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1362_ = lean_box(0);
v___x_1363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1362_);
return v___x_1363_;
}
v___jp_1367_:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___x_1371_ = l_Lake_defaultConfigFile;
v___x_1372_ = lean_box(0);
lean_inc_ref(v_scope_1366_);
lean_inc(v_name_1365_);
v___x_1373_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1373_, 0, v_name_1365_);
lean_ctor_set(v___x_1373_, 1, v_scope_1366_);
lean_ctor_set(v___x_1373_, 2, v___x_1371_);
lean_ctor_set(v___x_1373_, 3, v___x_1372_);
lean_ctor_set(v___x_1373_, 4, v___y_1368_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*5, v_inherited_1351_);
v___x_1374_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1374_, 0, v___y_1369_);
lean_ctor_set(v___x_1374_, 1, v_remoteUrl_1357_);
lean_ctor_set(v___x_1374_, 2, v_a_1370_);
lean_ctor_set(v___x_1374_, 3, v___x_1373_);
v___x_1375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1374_);
return v___x_1375_;
}
v___jp_1376_:
{
lean_object* v___x_1382_; uint8_t v___x_1383_; 
v___x_1382_ = lean_array_get_size(v___y_1379_);
v___x_1383_ = lean_nat_dec_lt(v___y_1378_, v___x_1382_);
if (v___x_1383_ == 0)
{
lean_dec_ref(v___y_1379_);
lean_dec_ref(v_a_1349_);
v___y_1368_ = v___y_1377_;
v___y_1369_ = v___y_1380_;
v_a_1370_ = v_val_1381_;
goto v___jp_1367_;
}
else
{
lean_object* v___x_1384_; uint8_t v___x_1385_; 
v___x_1384_ = lean_box(0);
v___x_1385_ = lean_nat_dec_le(v___x_1382_, v___x_1382_);
if (v___x_1385_ == 0)
{
if (v___x_1383_ == 0)
{
lean_dec_ref(v___y_1379_);
lean_dec_ref(v_a_1349_);
v___y_1368_ = v___y_1377_;
v___y_1369_ = v___y_1380_;
v_a_1370_ = v_val_1381_;
goto v___jp_1367_;
}
else
{
size_t v___x_1386_; size_t v___x_1387_; lean_object* v___x_1388_; 
v___x_1386_ = ((size_t)0ULL);
v___x_1387_ = lean_usize_of_nat(v___x_1382_);
v___x_1388_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v___y_1379_, v___x_1386_, v___x_1387_, v___x_1384_, v_a_1349_);
lean_dec_ref(v___y_1379_);
if (lean_obj_tag(v___x_1388_) == 0)
{
lean_dec_ref(v___x_1388_);
v___y_1368_ = v___y_1377_;
v___y_1369_ = v___y_1380_;
v_a_1370_ = v_val_1381_;
goto v___jp_1367_;
}
else
{
lean_object* v_a_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1396_; 
lean_dec_ref(v_val_1381_);
lean_dec_ref(v___y_1380_);
lean_dec_ref(v___y_1377_);
lean_dec_ref(v_remoteUrl_1357_);
v_a_1389_ = lean_ctor_get(v___x_1388_, 0);
v_isSharedCheck_1396_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1391_ = v___x_1388_;
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_a_1389_);
lean_dec(v___x_1388_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1394_; 
if (v_isShared_1392_ == 0)
{
v___x_1394_ = v___x_1391_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_a_1389_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
return v___x_1394_;
}
}
}
}
}
else
{
size_t v___x_1397_; size_t v___x_1398_; lean_object* v___x_1399_; 
v___x_1397_ = ((size_t)0ULL);
v___x_1398_ = lean_usize_of_nat(v___x_1382_);
v___x_1399_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v___y_1379_, v___x_1397_, v___x_1398_, v___x_1384_, v_a_1349_);
lean_dec_ref(v___y_1379_);
if (lean_obj_tag(v___x_1399_) == 0)
{
lean_dec_ref(v___x_1399_);
v___y_1368_ = v___y_1377_;
v___y_1369_ = v___y_1380_;
v_a_1370_ = v_val_1381_;
goto v___jp_1367_;
}
else
{
lean_object* v_a_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1407_; 
lean_dec_ref(v_val_1381_);
lean_dec_ref(v___y_1380_);
lean_dec_ref(v___y_1377_);
lean_dec_ref(v_remoteUrl_1357_);
v_a_1400_ = lean_ctor_get(v___x_1399_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v___x_1399_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1402_ = v___x_1399_;
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_a_1400_);
lean_dec(v___x_1399_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1405_; 
if (v_isShared_1403_ == 0)
{
v___x_1405_ = v___x_1402_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v_a_1400_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
}
}
}
}
v___jp_1409_:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; 
v___x_1413_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1413_, 0, v___y_1411_);
lean_ctor_set(v___x_1413_, 1, v___y_1410_);
lean_ctor_set(v___x_1413_, 2, v_inputRev_x3f_1358_);
lean_ctor_set(v___x_1413_, 3, v_subDir_x3f_1359_);
v___x_1414_ = l_Lake_defaultManifestFile;
v___x_1415_ = l_Lake_joinRelative(v_pkgDir_1408_, v___x_1414_);
v___x_1416_ = lean_unsigned_to_nat(0u);
v___x_1417_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
v___x_1418_ = l_Lake_Manifest_load(v___x_1415_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v_a_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1426_; 
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
lean_ctor_set_tag(v___x_1421_, 1);
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
v___y_1377_ = v___x_1413_;
v___y_1378_ = v___x_1416_;
v___y_1379_ = v___x_1417_;
v___y_1380_ = v___y_1412_;
v_val_1381_ = v___x_1424_;
goto v___jp_1376_;
}
}
}
else
{
lean_object* v_a_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1434_; 
v_a_1427_ = lean_ctor_get(v___x_1418_, 0);
v_isSharedCheck_1434_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1434_ == 0)
{
v___x_1429_ = v___x_1418_;
v_isShared_1430_ = v_isSharedCheck_1434_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_a_1427_);
lean_dec(v___x_1418_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1434_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
lean_object* v___x_1432_; 
if (v_isShared_1430_ == 0)
{
lean_ctor_set_tag(v___x_1429_, 0);
v___x_1432_ = v___x_1429_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v_a_1427_);
v___x_1432_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
v___y_1377_ = v___x_1413_;
v___y_1378_ = v___x_1416_;
v___y_1379_ = v___x_1417_;
v___y_1380_ = v___y_1412_;
v_val_1381_ = v___x_1432_;
goto v___jp_1376_;
}
}
}
}
v___jp_1435_:
{
if (lean_obj_tag(v_subDir_x3f_1359_) == 1)
{
lean_object* v_val_1438_; lean_object* v___x_1439_; 
v_val_1438_ = lean_ctor_get(v_subDir_x3f_1359_, 0);
lean_inc(v_val_1438_);
v___x_1439_ = l_Lake_joinRelative(v_relPkgDir_1355_, v_val_1438_);
v___y_1410_ = v_a_1437_;
v___y_1411_ = v___y_1436_;
v___y_1412_ = v___x_1439_;
goto v___jp_1409_;
}
else
{
v___y_1410_ = v_a_1437_;
v___y_1411_ = v___y_1436_;
v___y_1412_ = v_relPkgDir_1355_;
goto v___jp_1409_;
}
}
v___jp_1440_:
{
lean_object* v___x_1442_; 
lean_inc(v_inputRev_x3f_1358_);
lean_inc_ref(v___y_1441_);
lean_inc_ref(v_pkgDir_1408_);
lean_inc_ref(v_a_1349_);
v___x_1442_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(v_a_1349_, v_name_1354_, v_pkgDir_1408_, v___y_1441_, v_inputRev_x3f_1358_);
if (lean_obj_tag(v___x_1442_) == 0)
{
lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1508_; 
v_isSharedCheck_1508_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1508_ == 0)
{
lean_object* v_unused_1509_; 
v_unused_1509_ = lean_ctor_get(v___x_1442_, 0);
lean_dec(v_unused_1509_);
v___x_1444_ = v___x_1442_;
v_isShared_1445_ = v_isSharedCheck_1508_;
goto v_resetjp_1443_;
}
else
{
lean_dec(v___x_1442_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1508_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; 
v___x_1446_ = lean_unsigned_to_nat(0u);
v___x_1447_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
lean_inc_ref(v_pkgDir_1408_);
v___x_1448_ = l_Lake_GitRepo_getHeadRevision(v_pkgDir_1408_, v___x_1447_);
if (lean_obj_tag(v___x_1448_) == 0)
{
lean_object* v_a_1449_; lean_object* v_a_1450_; lean_object* v___x_1451_; uint8_t v___x_1452_; 
lean_del_object(v___x_1444_);
v_a_1449_ = lean_ctor_get(v___x_1448_, 0);
lean_inc(v_a_1449_);
v_a_1450_ = lean_ctor_get(v___x_1448_, 1);
lean_inc(v_a_1450_);
lean_dec_ref(v___x_1448_);
v___x_1451_ = lean_array_get_size(v_a_1450_);
v___x_1452_ = lean_nat_dec_lt(v___x_1446_, v___x_1451_);
if (v___x_1452_ == 0)
{
lean_dec(v_a_1450_);
v___y_1436_ = v___y_1441_;
v_a_1437_ = v_a_1449_;
goto v___jp_1435_;
}
else
{
lean_object* v___x_1453_; uint8_t v___x_1454_; 
v___x_1453_ = lean_box(0);
v___x_1454_ = lean_nat_dec_le(v___x_1451_, v___x_1451_);
if (v___x_1454_ == 0)
{
if (v___x_1452_ == 0)
{
lean_dec(v_a_1450_);
v___y_1436_ = v___y_1441_;
v_a_1437_ = v_a_1449_;
goto v___jp_1435_;
}
else
{
size_t v___x_1455_; size_t v___x_1456_; lean_object* v___x_1457_; 
v___x_1455_ = ((size_t)0ULL);
v___x_1456_ = lean_usize_of_nat(v___x_1451_);
lean_inc_ref(v_a_1349_);
v___x_1457_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_1450_, v___x_1455_, v___x_1456_, v___x_1453_, v_a_1349_);
lean_dec(v_a_1450_);
if (lean_obj_tag(v___x_1457_) == 0)
{
lean_dec_ref(v___x_1457_);
v___y_1436_ = v___y_1441_;
v_a_1437_ = v_a_1449_;
goto v___jp_1435_;
}
else
{
lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1465_; 
lean_dec(v_a_1449_);
lean_dec_ref(v___y_1441_);
lean_dec_ref(v_pkgDir_1408_);
lean_dec(v_subDir_x3f_1359_);
lean_dec(v_inputRev_x3f_1358_);
lean_dec_ref(v_remoteUrl_1357_);
lean_dec_ref(v_relPkgDir_1355_);
lean_dec_ref(v_a_1349_);
v_a_1458_ = lean_ctor_get(v___x_1457_, 0);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1460_ = v___x_1457_;
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___x_1457_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1463_; 
if (v_isShared_1461_ == 0)
{
v___x_1463_ = v___x_1460_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_a_1458_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
return v___x_1463_;
}
}
}
}
}
else
{
size_t v___x_1466_; size_t v___x_1467_; lean_object* v___x_1468_; 
v___x_1466_ = ((size_t)0ULL);
v___x_1467_ = lean_usize_of_nat(v___x_1451_);
lean_inc_ref(v_a_1349_);
v___x_1468_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_1450_, v___x_1466_, v___x_1467_, v___x_1453_, v_a_1349_);
lean_dec(v_a_1450_);
if (lean_obj_tag(v___x_1468_) == 0)
{
lean_dec_ref(v___x_1468_);
v___y_1436_ = v___y_1441_;
v_a_1437_ = v_a_1449_;
goto v___jp_1435_;
}
else
{
lean_object* v_a_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1476_; 
lean_dec(v_a_1449_);
lean_dec_ref(v___y_1441_);
lean_dec_ref(v_pkgDir_1408_);
lean_dec(v_subDir_x3f_1359_);
lean_dec(v_inputRev_x3f_1358_);
lean_dec_ref(v_remoteUrl_1357_);
lean_dec_ref(v_relPkgDir_1355_);
lean_dec_ref(v_a_1349_);
v_a_1469_ = lean_ctor_get(v___x_1468_, 0);
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1468_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1471_ = v___x_1468_;
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_a_1469_);
lean_dec(v___x_1468_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1474_; 
if (v_isShared_1472_ == 0)
{
v___x_1474_ = v___x_1471_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_a_1469_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
}
}
}
}
else
{
lean_object* v_a_1477_; lean_object* v___x_1478_; uint8_t v___x_1479_; 
lean_dec_ref(v___y_1441_);
lean_dec_ref(v_pkgDir_1408_);
lean_dec(v_subDir_x3f_1359_);
lean_dec(v_inputRev_x3f_1358_);
lean_dec_ref(v_remoteUrl_1357_);
lean_dec_ref(v_relPkgDir_1355_);
v_a_1477_ = lean_ctor_get(v___x_1448_, 1);
lean_inc(v_a_1477_);
lean_dec_ref(v___x_1448_);
v___x_1478_ = lean_array_get_size(v_a_1477_);
v___x_1479_ = lean_nat_dec_lt(v___x_1446_, v___x_1478_);
if (v___x_1479_ == 0)
{
lean_object* v___x_1480_; lean_object* v___x_1482_; 
lean_dec(v_a_1477_);
lean_dec_ref(v_a_1349_);
v___x_1480_ = lean_box(0);
if (v_isShared_1445_ == 0)
{
lean_ctor_set_tag(v___x_1444_, 1);
lean_ctor_set(v___x_1444_, 0, v___x_1480_);
v___x_1482_ = v___x_1444_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v___x_1480_);
v___x_1482_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
return v___x_1482_;
}
}
else
{
lean_object* v___x_1484_; uint8_t v___x_1485_; 
lean_del_object(v___x_1444_);
v___x_1484_ = lean_box(0);
v___x_1485_ = lean_nat_dec_le(v___x_1478_, v___x_1478_);
if (v___x_1485_ == 0)
{
if (v___x_1479_ == 0)
{
lean_dec(v_a_1477_);
lean_dec_ref(v_a_1349_);
goto v___jp_1361_;
}
else
{
size_t v___x_1486_; size_t v___x_1487_; lean_object* v___x_1488_; 
v___x_1486_ = ((size_t)0ULL);
v___x_1487_ = lean_usize_of_nat(v___x_1478_);
v___x_1488_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_1477_, v___x_1486_, v___x_1487_, v___x_1484_, v_a_1349_);
lean_dec(v_a_1477_);
if (lean_obj_tag(v___x_1488_) == 0)
{
lean_dec_ref(v___x_1488_);
goto v___jp_1361_;
}
else
{
lean_object* v_a_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1496_; 
v_a_1489_ = lean_ctor_get(v___x_1488_, 0);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1488_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1491_ = v___x_1488_;
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_a_1489_);
lean_dec(v___x_1488_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1494_; 
if (v_isShared_1492_ == 0)
{
v___x_1494_ = v___x_1491_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_a_1489_);
v___x_1494_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
return v___x_1494_;
}
}
}
}
}
else
{
size_t v___x_1497_; size_t v___x_1498_; lean_object* v___x_1499_; 
v___x_1497_ = ((size_t)0ULL);
v___x_1498_ = lean_usize_of_nat(v___x_1478_);
v___x_1499_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_1477_, v___x_1497_, v___x_1498_, v___x_1484_, v_a_1349_);
lean_dec(v_a_1477_);
if (lean_obj_tag(v___x_1499_) == 0)
{
lean_dec_ref(v___x_1499_);
goto v___jp_1361_;
}
else
{
lean_object* v_a_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1507_; 
v_a_1500_ = lean_ctor_get(v___x_1499_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1502_ = v___x_1499_;
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_a_1500_);
lean_dec(v___x_1499_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1505_; 
if (v_isShared_1503_ == 0)
{
v___x_1505_ = v___x_1502_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_a_1500_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
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
lean_object* v_a_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1517_; 
lean_dec_ref(v___y_1441_);
lean_dec_ref(v_pkgDir_1408_);
lean_dec(v_subDir_x3f_1359_);
lean_dec(v_inputRev_x3f_1358_);
lean_dec_ref(v_remoteUrl_1357_);
lean_dec_ref(v_relPkgDir_1355_);
lean_dec_ref(v_a_1349_);
v_a_1510_ = lean_ctor_get(v___x_1442_, 0);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1512_ = v___x_1442_;
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_a_1510_);
lean_dec(v___x_1442_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v___x_1515_; 
if (v_isShared_1513_ == 0)
{
v___x_1515_ = v___x_1512_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_a_1510_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0___boxed(lean_object* v_a_1520_, lean_object* v_dep_1521_, lean_object* v_inherited_1522_, lean_object* v_lakeEnv_1523_, lean_object* v_wsDir_1524_, lean_object* v_name_1525_, lean_object* v_relPkgDir_1526_, lean_object* v_gitUrl_1527_, lean_object* v_remoteUrl_1528_, lean_object* v_inputRev_x3f_1529_, lean_object* v_subDir_x3f_1530_, lean_object* v_a_1531_){
_start:
{
uint8_t v_inherited_boxed_1532_; lean_object* v_res_1533_; 
v_inherited_boxed_1532_ = lean_unbox(v_inherited_1522_);
v_res_1533_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(v_a_1520_, v_dep_1521_, v_inherited_boxed_1532_, v_lakeEnv_1523_, v_wsDir_1524_, v_name_1525_, v_relPkgDir_1526_, v_gitUrl_1527_, v_remoteUrl_1528_, v_inputRev_x3f_1529_, v_subDir_x3f_1530_);
lean_dec_ref(v_lakeEnv_1523_);
lean_dec_ref(v_dep_1521_);
return v_res_1533_;
}
}
static lean_object* _init_l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1535_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__0));
v___x_1536_ = lean_string_utf8_byte_size(v___x_1535_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg(lean_object* v_s_1537_){
_start:
{
lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; uint8_t v___x_1541_; 
v___x_1538_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__0));
v___x_1539_ = lean_string_utf8_byte_size(v_s_1537_);
v___x_1540_ = lean_obj_once(&l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__1, &l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__1_once, _init_l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__1);
v___x_1541_ = lean_nat_dec_le(v___x_1540_, v___x_1539_);
if (v___x_1541_ == 0)
{
lean_object* v___x_1542_; 
lean_dec_ref(v_s_1537_);
v___x_1542_ = lean_box(0);
return v___x_1542_;
}
else
{
lean_object* v___x_1543_; uint8_t v___x_1544_; 
v___x_1543_ = lean_unsigned_to_nat(0u);
v___x_1544_ = lean_string_memcmp(v_s_1537_, v___x_1538_, v___x_1543_, v___x_1543_, v___x_1540_);
if (v___x_1544_ == 0)
{
lean_object* v___x_1545_; 
lean_dec_ref(v_s_1537_);
v___x_1545_ = lean_box(0);
return v___x_1545_;
}
else
{
lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
lean_inc_ref(v_s_1537_);
v___x_1546_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1546_, 0, v_s_1537_);
lean_ctor_set(v___x_1546_, 1, v___x_1543_);
lean_ctor_set(v___x_1546_, 2, v___x_1539_);
v___x_1547_ = l_String_Slice_pos_x21(v___x_1546_, v___x_1540_);
lean_dec_ref(v___x_1546_);
v___x_1548_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1548_, 0, v_s_1537_);
lean_ctor_set(v___x_1548_, 1, v___x_1547_);
lean_ctor_set(v___x_1548_, 2, v___x_1539_);
v___x_1549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1548_);
return v___x_1549_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2(lean_object* v_s_1550_, lean_object* v_pat_1551_){
_start:
{
lean_object* v___x_1552_; 
v___x_1552_ = l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg(v_s_1550_);
return v___x_1552_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___boxed(lean_object* v_s_1553_, lean_object* v_pat_1554_){
_start:
{
lean_object* v_res_1555_; 
v_res_1555_ = l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2(v_s_1553_, v_pat_1554_);
lean_dec_ref(v_pat_1554_);
return v_res_1555_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(lean_object* v_ver_1559_, lean_object* v_as_1560_, size_t v_sz_1561_, size_t v_i_1562_, lean_object* v_b_1563_){
_start:
{
uint8_t v___x_1564_; 
v___x_1564_ = lean_usize_dec_lt(v_i_1562_, v_sz_1561_);
if (v___x_1564_ == 0)
{
return v_b_1563_;
}
else
{
lean_object* v_a_1565_; lean_object* v_version_1566_; lean_object* v___x_1567_; uint8_t v___x_1568_; 
lean_dec_ref(v_b_1563_);
v_a_1565_ = lean_array_uget_borrowed(v_as_1560_, v_i_1562_);
v_version_1566_ = lean_ctor_get(v_a_1565_, 0);
v___x_1567_ = lean_box(0);
v___x_1568_ = l_Lake_VerRange_test(v_ver_1559_, v_version_1566_);
if (v___x_1568_ == 0)
{
lean_object* v___x_1569_; size_t v___x_1570_; size_t v___x_1571_; 
v___x_1569_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___closed__0));
v___x_1570_ = ((size_t)1ULL);
v___x_1571_ = lean_usize_add(v_i_1562_, v___x_1570_);
v_i_1562_ = v___x_1571_;
v_b_1563_ = v___x_1569_;
goto _start;
}
else
{
lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; 
lean_inc(v_a_1565_);
v___x_1573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1573_, 0, v_a_1565_);
v___x_1574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1573_);
v___x_1575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1574_);
lean_ctor_set(v___x_1575_, 1, v___x_1567_);
return v___x_1575_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___boxed(lean_object* v_ver_1576_, lean_object* v_as_1577_, lean_object* v_sz_1578_, lean_object* v_i_1579_, lean_object* v_b_1580_){
_start:
{
size_t v_sz_boxed_1581_; size_t v_i_boxed_1582_; lean_object* v_res_1583_; 
v_sz_boxed_1581_ = lean_unbox_usize(v_sz_1578_);
lean_dec(v_sz_1578_);
v_i_boxed_1582_ = lean_unbox_usize(v_i_1579_);
lean_dec(v_i_1579_);
v_res_1583_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(v_ver_1576_, v_as_1577_, v_sz_boxed_1581_, v_i_boxed_1582_, v_b_1580_);
lean_dec_ref(v_as_1577_);
lean_dec_ref(v_ver_1576_);
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize(lean_object* v_dep_1595_, uint8_t v_inherited_1596_, lean_object* v_lakeEnv_1597_, lean_object* v_wsDir_1598_, lean_object* v_relPkgsDir_1599_, lean_object* v_relParentDir_1600_, lean_object* v_a_1601_){
_start:
{
lean_object* v___y_1607_; lean_object* v___y_1608_; lean_object* v___y_1618_; lean_object* v___y_1619_; lean_object* v___y_1620_; lean_object* v___y_1621_; lean_object* v___y_1622_; lean_object* v___y_1623_; lean_object* v___y_1624_; lean_object* v___y_1628_; lean_object* v___y_1629_; lean_object* v___y_1630_; lean_object* v___y_1631_; lean_object* v___y_1632_; lean_object* v_rev_x3f_1633_; lean_object* v___y_1634_; lean_object* v_name_1637_; lean_object* v_scope_1638_; lean_object* v_version_x3f_1639_; lean_object* v_src_x3f_1640_; lean_object* v___y_1642_; lean_object* v___y_1643_; lean_object* v___y_1659_; lean_object* v___y_1660_; lean_object* v___y_1661_; lean_object* v___y_1662_; lean_object* v___y_1663_; lean_object* v___y_1664_; lean_object* v___y_1665_; lean_object* v_a_1666_; 
v_name_1637_ = lean_ctor_get(v_dep_1595_, 0);
v_scope_1638_ = lean_ctor_get(v_dep_1595_, 1);
v_version_x3f_1639_ = lean_ctor_get(v_dep_1595_, 2);
v_src_x3f_1640_ = lean_ctor_get(v_dep_1595_, 3);
lean_inc(v_src_x3f_1640_);
if (lean_obj_tag(v_src_x3f_1640_) == 1)
{
lean_object* v_val_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1792_; 
v_val_1709_ = lean_ctor_get(v_src_x3f_1640_, 0);
v_isSharedCheck_1792_ = !lean_is_exclusive(v_src_x3f_1640_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1711_ = v_src_x3f_1640_;
v_isShared_1712_ = v_isSharedCheck_1792_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_val_1709_);
lean_dec(v_src_x3f_1640_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1792_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
if (lean_obj_tag(v_val_1709_) == 0)
{
lean_object* v_dir_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1779_; 
lean_inc_ref(v_scope_1638_);
lean_inc(v_name_1637_);
lean_dec_ref(v_relPkgsDir_1599_);
lean_dec_ref(v_lakeEnv_1597_);
lean_dec_ref(v_dep_1595_);
v_dir_1713_ = lean_ctor_get(v_val_1709_, 0);
v_isSharedCheck_1779_ = !lean_is_exclusive(v_val_1709_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1715_ = v_val_1709_;
v_isShared_1716_ = v_isSharedCheck_1779_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_dir_1713_);
lean_dec(v_val_1709_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1779_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v_relPkgDir_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1721_; 
v_relPkgDir_1717_ = l_Lake_joinRelative(v_relParentDir_1600_, v_dir_1713_);
lean_inc_ref(v_relPkgDir_1717_);
v___x_1718_ = l_Lake_joinRelative(v_wsDir_1598_, v_relPkgDir_1717_);
v___x_1719_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
lean_inc_ref(v_relPkgDir_1717_);
if (v_isShared_1716_ == 0)
{
lean_ctor_set(v___x_1715_, 0, v_relPkgDir_1717_);
v___x_1721_ = v___x_1715_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_relPkgDir_1717_);
v___x_1721_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
lean_object* v_a_1723_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v_val_1735_; lean_object* v___x_1761_; 
v___x_1731_ = l_Lake_defaultManifestFile;
v___x_1732_ = l_Lake_joinRelative(v___x_1718_, v___x_1731_);
v___x_1733_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
v___x_1761_ = l_Lake_Manifest_load(v___x_1732_);
if (lean_obj_tag(v___x_1761_) == 0)
{
lean_object* v_a_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1769_; 
v_a_1762_ = lean_ctor_get(v___x_1761_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1761_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1764_ = v___x_1761_;
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_a_1762_);
lean_dec(v___x_1761_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1767_; 
if (v_isShared_1765_ == 0)
{
lean_ctor_set_tag(v___x_1764_, 1);
v___x_1767_ = v___x_1764_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_a_1762_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
v_val_1735_ = v___x_1767_;
goto v___jp_1734_;
}
}
}
else
{
lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1777_; 
v_a_1770_ = lean_ctor_get(v___x_1761_, 0);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1761_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1772_ = v___x_1761_;
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_a_1770_);
lean_dec(v___x_1761_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1775_; 
if (v_isShared_1773_ == 0)
{
lean_ctor_set_tag(v___x_1772_, 0);
v___x_1775_ = v___x_1772_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_a_1770_);
v___x_1775_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
v_val_1735_ = v___x_1775_;
goto v___jp_1734_;
}
}
}
v___jp_1722_:
{
lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1729_; 
v___x_1724_ = l_Lake_defaultConfigFile;
v___x_1725_ = lean_box(0);
v___x_1726_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1726_, 0, v_name_1637_);
lean_ctor_set(v___x_1726_, 1, v_scope_1638_);
lean_ctor_set(v___x_1726_, 2, v___x_1724_);
lean_ctor_set(v___x_1726_, 3, v___x_1725_);
lean_ctor_set(v___x_1726_, 4, v___x_1721_);
lean_ctor_set_uint8(v___x_1726_, sizeof(void*)*5, v_inherited_1596_);
v___x_1727_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1727_, 0, v_relPkgDir_1717_);
lean_ctor_set(v___x_1727_, 1, v___x_1719_);
lean_ctor_set(v___x_1727_, 2, v_a_1723_);
lean_ctor_set(v___x_1727_, 3, v___x_1726_);
if (v_isShared_1712_ == 0)
{
lean_ctor_set_tag(v___x_1711_, 0);
lean_ctor_set(v___x_1711_, 0, v___x_1727_);
v___x_1729_ = v___x_1711_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v___x_1727_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
return v___x_1729_;
}
}
v___jp_1734_:
{
uint8_t v___x_1736_; 
v___x_1736_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_1736_ == 0)
{
lean_dec_ref(v_a_1601_);
v_a_1723_ = v_val_1735_;
goto v___jp_1722_;
}
else
{
lean_object* v___x_1737_; uint8_t v___x_1738_; 
v___x_1737_ = lean_box(0);
v___x_1738_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_1738_ == 0)
{
if (v___x_1736_ == 0)
{
lean_dec_ref(v_a_1601_);
v_a_1723_ = v_val_1735_;
goto v___jp_1722_;
}
else
{
size_t v___x_1739_; size_t v___x_1740_; lean_object* v___x_1741_; 
v___x_1739_ = ((size_t)0ULL);
v___x_1740_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_1741_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v___x_1733_, v___x_1739_, v___x_1740_, v___x_1737_, v_a_1601_);
if (lean_obj_tag(v___x_1741_) == 0)
{
lean_dec_ref(v___x_1741_);
v_a_1723_ = v_val_1735_;
goto v___jp_1722_;
}
else
{
lean_object* v_a_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1749_; 
lean_dec_ref(v_val_1735_);
lean_dec_ref(v___x_1721_);
lean_dec_ref(v_relPkgDir_1717_);
lean_del_object(v___x_1711_);
lean_dec_ref(v_scope_1638_);
lean_dec(v_name_1637_);
v_a_1742_ = lean_ctor_get(v___x_1741_, 0);
v_isSharedCheck_1749_ = !lean_is_exclusive(v___x_1741_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1744_ = v___x_1741_;
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_a_1742_);
lean_dec(v___x_1741_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v___x_1747_; 
if (v_isShared_1745_ == 0)
{
v___x_1747_ = v___x_1744_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v_a_1742_);
v___x_1747_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
return v___x_1747_;
}
}
}
}
}
else
{
size_t v___x_1750_; size_t v___x_1751_; lean_object* v___x_1752_; 
v___x_1750_ = ((size_t)0ULL);
v___x_1751_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_1752_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v___x_1733_, v___x_1750_, v___x_1751_, v___x_1737_, v_a_1601_);
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_dec_ref(v___x_1752_);
v_a_1723_ = v_val_1735_;
goto v___jp_1722_;
}
else
{
lean_object* v_a_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1760_; 
lean_dec_ref(v_val_1735_);
lean_dec_ref(v___x_1721_);
lean_dec_ref(v_relPkgDir_1717_);
lean_del_object(v___x_1711_);
lean_dec_ref(v_scope_1638_);
lean_dec(v_name_1637_);
v_a_1753_ = lean_ctor_get(v___x_1752_, 0);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1755_ = v___x_1752_;
v_isShared_1756_ = v_isSharedCheck_1760_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_a_1753_);
lean_dec(v___x_1752_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1760_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v___x_1758_; 
if (v_isShared_1756_ == 0)
{
v___x_1758_ = v___x_1755_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v_a_1753_);
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
}
}
}
}
}
else
{
lean_object* v_url_1780_; lean_object* v_rev_1781_; lean_object* v_subDir_1782_; uint8_t v___x_1783_; lean_object* v_sname_1784_; lean_object* v___y_1786_; lean_object* v___x_1789_; 
lean_del_object(v___x_1711_);
lean_dec_ref(v_relParentDir_1600_);
v_url_1780_ = lean_ctor_get(v_val_1709_, 0);
lean_inc_ref(v_url_1780_);
v_rev_1781_ = lean_ctor_get(v_val_1709_, 1);
lean_inc(v_rev_1781_);
v_subDir_1782_ = lean_ctor_get(v_val_1709_, 2);
lean_inc(v_subDir_1782_);
lean_dec_ref(v_val_1709_);
v___x_1783_ = 0;
lean_inc(v_name_1637_);
v_sname_1784_ = l_Lean_Name_toString(v_name_1637_, v___x_1783_);
lean_inc_ref(v_url_1780_);
v___x_1789_ = l_Lake_Git_filterUrl_x3f(v_url_1780_);
if (lean_obj_tag(v___x_1789_) == 0)
{
lean_object* v___x_1790_; 
v___x_1790_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___y_1786_ = v___x_1790_;
goto v___jp_1785_;
}
else
{
lean_object* v_val_1791_; 
v_val_1791_ = lean_ctor_get(v___x_1789_, 0);
lean_inc(v_val_1791_);
lean_dec_ref(v___x_1789_);
v___y_1786_ = v_val_1791_;
goto v___jp_1785_;
}
v___jp_1785_:
{
lean_object* v___x_1787_; lean_object* v___x_1788_; 
lean_inc_ref(v_sname_1784_);
v___x_1787_ = l_Lake_joinRelative(v_relPkgsDir_1599_, v_sname_1784_);
v___x_1788_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(v_a_1601_, v_dep_1595_, v_inherited_1596_, v_lakeEnv_1597_, v_wsDir_1598_, v_sname_1784_, v___x_1787_, v_url_1780_, v___y_1786_, v_rev_1781_, v_subDir_1782_);
lean_dec_ref(v_lakeEnv_1597_);
lean_dec_ref(v_dep_1595_);
return v___x_1788_;
}
}
}
}
else
{
lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___y_1796_; lean_object* v___y_1797_; lean_object* v___y_1798_; lean_object* v___y_1799_; lean_object* v___y_1800_; lean_object* v___y_1801_; lean_object* v___y_1802_; lean_object* v_fst_1803_; lean_object* v_snd_1804_; lean_object* v___y_1832_; lean_object* v___y_1833_; lean_object* v_a_1834_; lean_object* v___y_1967_; lean_object* v___y_1968_; lean_object* v_fst_1969_; lean_object* v_snd_1970_; uint8_t v___x_1997_; lean_object* v_a_1999_; 
lean_dec(v_src_x3f_1640_);
lean_dec_ref(v_relParentDir_1600_);
v___x_1793_ = lean_string_utf8_byte_size(v_scope_1638_);
v___x_1794_ = lean_unsigned_to_nat(0u);
v___x_1997_ = lean_nat_dec_eq(v___x_1793_, v___x_1794_);
if (v___x_1997_ == 0)
{
if (lean_obj_tag(v_version_x3f_1639_) == 1)
{
lean_object* v_val_2009_; lean_object* v___x_2010_; 
v_val_2009_ = lean_ctor_get(v_version_x3f_1639_, 0);
lean_inc(v_val_2009_);
v___x_2010_ = l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg(v_val_2009_);
if (lean_obj_tag(v___x_2010_) == 1)
{
lean_object* v_val_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2019_; 
v_val_2011_ = lean_ctor_get(v___x_2010_, 0);
v_isSharedCheck_2019_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_2013_ = v___x_2010_;
v_isShared_2014_ = v_isSharedCheck_2019_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_val_2011_);
lean_dec(v___x_2010_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2019_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v___x_2015_; lean_object* v___x_2017_; 
v___x_2015_ = l_String_Slice_toString(v_val_2011_);
lean_dec(v_val_2011_);
if (v_isShared_2014_ == 0)
{
lean_ctor_set(v___x_2013_, 0, v___x_2015_);
v___x_2017_ = v___x_2013_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v___x_2015_);
v___x_2017_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
v_a_1999_ = v___x_2017_;
goto v___jp_1998_;
}
}
}
else
{
lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; 
lean_dec(v___x_2010_);
v___x_2020_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__8));
v___x_2021_ = lean_string_utf8_byte_size(v_val_2009_);
lean_inc(v_val_2009_);
v___x_2022_ = l___private_Lake_Util_Version_0__Lake_runVerParse(lean_box(0), v_val_2009_, v___x_2020_, v___x_1794_, v___x_2021_);
if (lean_obj_tag(v___x_2022_) == 0)
{
lean_object* v_a_2023_; lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2039_; 
lean_inc(v_name_1637_);
lean_dec_ref(v_relPkgsDir_1599_);
lean_dec_ref(v_wsDir_1598_);
lean_dec_ref(v_lakeEnv_1597_);
lean_dec_ref(v_dep_1595_);
v_a_2023_ = lean_ctor_get(v___x_2022_, 0);
v_isSharedCheck_2039_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2025_ = v___x_2022_;
v_isShared_2026_ = v_isSharedCheck_2039_;
goto v_resetjp_2024_;
}
else
{
lean_inc(v_a_2023_);
lean_dec(v___x_2022_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2039_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
uint8_t v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; uint8_t v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2037_; 
v___x_2027_ = 1;
v___x_2028_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1637_, v___x_2027_);
v___x_2029_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__9));
v___x_2030_ = lean_string_append(v___x_2028_, v___x_2029_);
v___x_2031_ = lean_string_append(v___x_2030_, v_a_2023_);
lean_dec(v_a_2023_);
v___x_2032_ = 3;
v___x_2033_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2033_, 0, v___x_2031_);
lean_ctor_set_uint8(v___x_2033_, sizeof(void*)*1, v___x_2032_);
v___x_2034_ = lean_apply_2(v_a_1601_, v___x_2033_, lean_box(0));
v___x_2035_ = lean_box(0);
if (v_isShared_2026_ == 0)
{
lean_ctor_set_tag(v___x_2025_, 1);
lean_ctor_set(v___x_2025_, 0, v___x_2035_);
v___x_2037_ = v___x_2025_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v___x_2035_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
return v___x_2037_;
}
}
}
else
{
lean_object* v_a_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2047_; 
v_a_2040_ = lean_ctor_get(v___x_2022_, 0);
v_isSharedCheck_2047_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2047_ == 0)
{
v___x_2042_ = v___x_2022_;
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_a_2040_);
lean_dec(v___x_2022_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2045_; 
if (v_isShared_2043_ == 0)
{
lean_ctor_set_tag(v___x_2042_, 2);
v___x_2045_ = v___x_2042_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v_a_2040_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
v_a_1999_ = v___x_2045_;
goto v___jp_1998_;
}
}
}
}
}
else
{
lean_object* v___x_2048_; 
v___x_2048_ = lean_box(0);
v_a_1999_ = v___x_2048_;
goto v___jp_1998_;
}
}
else
{
lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; uint8_t v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; 
lean_inc(v_name_1637_);
lean_dec_ref(v_relPkgsDir_1599_);
lean_dec_ref(v_wsDir_1598_);
lean_dec_ref(v_lakeEnv_1597_);
lean_dec_ref(v_dep_1595_);
v___x_2049_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1637_, v___x_1997_);
v___x_2050_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__10));
v___x_2051_ = lean_string_append(v___x_2049_, v___x_2050_);
v___x_2052_ = 3;
v___x_2053_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2053_, 0, v___x_2051_);
lean_ctor_set_uint8(v___x_2053_, sizeof(void*)*1, v___x_2052_);
v___x_2054_ = lean_apply_2(v_a_1601_, v___x_2053_, lean_box(0));
v___x_2055_ = lean_box(0);
v___x_2056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2056_, 0, v___x_2055_);
return v___x_2056_;
}
v___jp_1795_:
{
lean_object* v___x_1805_; uint8_t v___x_1806_; 
v___x_1805_ = lean_array_get_size(v_snd_1804_);
v___x_1806_ = lean_nat_dec_lt(v___x_1794_, v___x_1805_);
if (v___x_1806_ == 0)
{
lean_dec_ref(v_snd_1804_);
v___y_1659_ = v___y_1796_;
v___y_1660_ = v___y_1797_;
v___y_1661_ = v___y_1798_;
v___y_1662_ = v___y_1799_;
v___y_1663_ = v___y_1800_;
v___y_1664_ = v___y_1801_;
v___y_1665_ = v___y_1802_;
v_a_1666_ = v_fst_1803_;
goto v___jp_1658_;
}
else
{
lean_object* v___x_1807_; uint8_t v___x_1808_; 
v___x_1807_ = lean_box(0);
v___x_1808_ = lean_nat_dec_le(v___x_1805_, v___x_1805_);
if (v___x_1808_ == 0)
{
if (v___x_1806_ == 0)
{
lean_dec_ref(v_snd_1804_);
v___y_1659_ = v___y_1796_;
v___y_1660_ = v___y_1797_;
v___y_1661_ = v___y_1798_;
v___y_1662_ = v___y_1799_;
v___y_1663_ = v___y_1800_;
v___y_1664_ = v___y_1801_;
v___y_1665_ = v___y_1802_;
v_a_1666_ = v_fst_1803_;
goto v___jp_1658_;
}
else
{
size_t v___x_1809_; size_t v___x_1810_; lean_object* v___x_1811_; 
v___x_1809_ = ((size_t)0ULL);
v___x_1810_ = lean_usize_of_nat(v___x_1805_);
lean_inc_ref(v_a_1601_);
v___x_1811_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_snd_1804_, v___x_1809_, v___x_1810_, v___x_1807_, v_a_1601_);
lean_dec_ref(v_snd_1804_);
if (lean_obj_tag(v___x_1811_) == 0)
{
lean_dec_ref(v___x_1811_);
v___y_1659_ = v___y_1796_;
v___y_1660_ = v___y_1797_;
v___y_1661_ = v___y_1798_;
v___y_1662_ = v___y_1799_;
v___y_1663_ = v___y_1800_;
v___y_1664_ = v___y_1801_;
v___y_1665_ = v___y_1802_;
v_a_1666_ = v_fst_1803_;
goto v___jp_1658_;
}
else
{
lean_object* v_a_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1819_; 
lean_dec_ref(v_fst_1803_);
lean_dec_ref(v___y_1802_);
lean_dec_ref(v___y_1801_);
lean_dec_ref(v___y_1800_);
lean_dec(v___y_1799_);
lean_dec(v___y_1798_);
lean_dec_ref(v___y_1797_);
lean_dec_ref(v___y_1796_);
lean_dec_ref(v_a_1601_);
lean_dec_ref(v_wsDir_1598_);
lean_dec_ref(v_lakeEnv_1597_);
lean_dec_ref(v_dep_1595_);
v_a_1812_ = lean_ctor_get(v___x_1811_, 0);
v_isSharedCheck_1819_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1814_ = v___x_1811_;
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_a_1812_);
lean_dec(v___x_1811_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___x_1817_; 
if (v_isShared_1815_ == 0)
{
v___x_1817_ = v___x_1814_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v_a_1812_);
v___x_1817_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
return v___x_1817_;
}
}
}
}
}
else
{
size_t v___x_1820_; size_t v___x_1821_; lean_object* v___x_1822_; 
v___x_1820_ = ((size_t)0ULL);
v___x_1821_ = lean_usize_of_nat(v___x_1805_);
lean_inc_ref(v_a_1601_);
v___x_1822_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_snd_1804_, v___x_1820_, v___x_1821_, v___x_1807_, v_a_1601_);
lean_dec_ref(v_snd_1804_);
if (lean_obj_tag(v___x_1822_) == 0)
{
lean_dec_ref(v___x_1822_);
v___y_1659_ = v___y_1796_;
v___y_1660_ = v___y_1797_;
v___y_1661_ = v___y_1798_;
v___y_1662_ = v___y_1799_;
v___y_1663_ = v___y_1800_;
v___y_1664_ = v___y_1801_;
v___y_1665_ = v___y_1802_;
v_a_1666_ = v_fst_1803_;
goto v___jp_1658_;
}
else
{
lean_object* v_a_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1830_; 
lean_dec_ref(v_fst_1803_);
lean_dec_ref(v___y_1802_);
lean_dec_ref(v___y_1801_);
lean_dec_ref(v___y_1800_);
lean_dec(v___y_1799_);
lean_dec(v___y_1798_);
lean_dec_ref(v___y_1797_);
lean_dec_ref(v___y_1796_);
lean_dec_ref(v_a_1601_);
lean_dec_ref(v_wsDir_1598_);
lean_dec_ref(v_lakeEnv_1597_);
lean_dec_ref(v_dep_1595_);
v_a_1823_ = lean_ctor_get(v___x_1822_, 0);
v_isSharedCheck_1830_ = !lean_is_exclusive(v___x_1822_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1825_ = v___x_1822_;
v_isShared_1826_ = v_isSharedCheck_1830_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_a_1823_);
lean_dec(v___x_1822_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1830_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v___x_1828_; 
if (v_isShared_1826_ == 0)
{
v___x_1828_ = v___x_1825_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_a_1823_);
v___x_1828_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
return v___x_1828_;
}
}
}
}
}
}
v___jp_1831_:
{
if (lean_obj_tag(v_a_1834_) == 0)
{
lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; uint8_t v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; 
lean_inc_ref(v_scope_1638_);
lean_dec_ref(v_a_1834_);
lean_dec(v___y_1832_);
lean_dec_ref(v_relPkgsDir_1599_);
lean_dec_ref(v_wsDir_1598_);
lean_dec_ref(v_lakeEnv_1597_);
lean_dec_ref(v_dep_1595_);
v___x_1835_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
v___x_1836_ = lean_string_append(v_scope_1638_, v___x_1835_);
v___x_1837_ = lean_string_append(v___x_1836_, v___y_1833_);
lean_dec_ref(v___y_1833_);
v___x_1838_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__7));
v___x_1839_ = lean_string_append(v___x_1837_, v___x_1838_);
v___x_1840_ = 3;
v___x_1841_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1841_, 0, v___x_1839_);
lean_ctor_set_uint8(v___x_1841_, sizeof(void*)*1, v___x_1840_);
v___x_1842_ = lean_apply_2(v_a_1601_, v___x_1841_, lean_box(0));
v___x_1843_ = lean_box(0);
v___x_1844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1843_);
return v___x_1844_;
}
else
{
lean_object* v_a_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1965_; 
v_a_1845_ = lean_ctor_get(v_a_1834_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v_a_1834_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1847_ = v_a_1834_;
v_isShared_1848_ = v_isSharedCheck_1965_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_a_1845_);
lean_dec(v_a_1834_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1965_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
if (lean_obj_tag(v_a_1845_) == 0)
{
lean_object* v___x_1849_; uint8_t v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; 
lean_inc_ref(v_scope_1638_);
lean_del_object(v___x_1847_);
lean_dec_ref(v_relPkgsDir_1599_);
lean_dec_ref(v_wsDir_1598_);
lean_dec_ref(v_lakeEnv_1597_);
lean_dec_ref(v_dep_1595_);
v___x_1849_ = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed(v_scope_1638_, v___y_1833_, v___y_1832_);
lean_dec_ref(v___y_1833_);
v___x_1850_ = 3;
v___x_1851_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1851_, 0, v___x_1849_);
lean_ctor_set_uint8(v___x_1851_, sizeof(void*)*1, v___x_1850_);
v___x_1852_ = lean_apply_2(v_a_1601_, v___x_1851_, lean_box(0));
v___x_1853_ = lean_box(0);
v___x_1854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1853_);
return v___x_1854_;
}
else
{
lean_object* v_val_1855_; lean_object* v___x_1856_; 
v_val_1855_ = lean_ctor_get(v_a_1845_, 0);
lean_inc(v_val_1855_);
lean_dec_ref(v_a_1845_);
v___x_1856_ = l_Lake_RegistryPkg_gitSrc_x3f(v_val_1855_);
if (lean_obj_tag(v___x_1856_) == 1)
{
lean_object* v_val_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1964_; 
v_val_1857_ = lean_ctor_get(v___x_1856_, 0);
v_isSharedCheck_1964_ = !lean_is_exclusive(v___x_1856_);
if (v_isSharedCheck_1964_ == 0)
{
v___x_1859_ = v___x_1856_;
v_isShared_1860_ = v_isSharedCheck_1964_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_val_1857_);
lean_dec(v___x_1856_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1964_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
if (lean_obj_tag(v_val_1857_) == 0)
{
lean_object* v_url_1861_; lean_object* v_githubUrl_x3f_1862_; lean_object* v_defaultBranch_x3f_1863_; lean_object* v_subDir_x3f_1864_; lean_object* v_name_1865_; lean_object* v_fullName_1866_; lean_object* v___x_1867_; 
v_url_1861_ = lean_ctor_get(v_val_1857_, 1);
lean_inc_ref(v_url_1861_);
v_githubUrl_x3f_1862_ = lean_ctor_get(v_val_1857_, 2);
lean_inc(v_githubUrl_x3f_1862_);
v_defaultBranch_x3f_1863_ = lean_ctor_get(v_val_1857_, 3);
lean_inc(v_defaultBranch_x3f_1863_);
v_subDir_x3f_1864_ = lean_ctor_get(v_val_1857_, 4);
lean_inc(v_subDir_x3f_1864_);
lean_dec_ref(v_val_1857_);
v_name_1865_ = lean_ctor_get(v_val_1855_, 0);
lean_inc_ref(v_name_1865_);
v_fullName_1866_ = lean_ctor_get(v_val_1855_, 1);
lean_inc_ref(v_fullName_1866_);
lean_dec(v_val_1855_);
v___x_1867_ = l_Lake_joinRelative(v_relPkgsDir_1599_, v_name_1865_);
switch(lean_obj_tag(v___y_1832_))
{
case 0:
{
lean_object* v___x_1868_; 
lean_del_object(v___x_1847_);
lean_dec_ref(v___y_1833_);
v___x_1868_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
if (lean_obj_tag(v_defaultBranch_x3f_1863_) == 0)
{
uint8_t v___x_1869_; 
lean_dec_ref(v___x_1867_);
lean_dec_ref(v_fullName_1866_);
lean_dec(v_subDir_x3f_1864_);
lean_dec(v_githubUrl_x3f_1862_);
lean_dec_ref(v_url_1861_);
lean_dec_ref(v_wsDir_1598_);
lean_dec_ref(v_lakeEnv_1597_);
lean_dec_ref(v_dep_1595_);
v___x_1869_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_1869_ == 0)
{
lean_object* v___x_1870_; lean_object* v___x_1872_; 
lean_dec_ref(v_a_1601_);
v___x_1870_ = lean_box(0);
if (v_isShared_1860_ == 0)
{
lean_ctor_set(v___x_1859_, 0, v___x_1870_);
v___x_1872_ = v___x_1859_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v___x_1870_);
v___x_1872_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
return v___x_1872_;
}
}
else
{
lean_object* v___x_1874_; uint8_t v___x_1875_; 
lean_del_object(v___x_1859_);
v___x_1874_ = lean_box(0);
v___x_1875_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_1875_ == 0)
{
if (v___x_1869_ == 0)
{
lean_dec_ref(v_a_1601_);
goto v___jp_1603_;
}
else
{
size_t v___x_1876_; size_t v___x_1877_; lean_object* v___x_1878_; 
v___x_1876_ = ((size_t)0ULL);
v___x_1877_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_1878_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v___x_1868_, v___x_1876_, v___x_1877_, v___x_1874_, v_a_1601_);
if (lean_obj_tag(v___x_1878_) == 0)
{
lean_dec_ref(v___x_1878_);
goto v___jp_1603_;
}
else
{
lean_object* v_a_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1886_; 
v_a_1879_ = lean_ctor_get(v___x_1878_, 0);
v_isSharedCheck_1886_ = !lean_is_exclusive(v___x_1878_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1881_ = v___x_1878_;
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_a_1879_);
lean_dec(v___x_1878_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v___x_1884_; 
if (v_isShared_1882_ == 0)
{
v___x_1884_ = v___x_1881_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v_a_1879_);
v___x_1884_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
return v___x_1884_;
}
}
}
}
}
else
{
size_t v___x_1887_; size_t v___x_1888_; lean_object* v___x_1889_; 
v___x_1887_ = ((size_t)0ULL);
v___x_1888_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_1889_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v___x_1868_, v___x_1887_, v___x_1888_, v___x_1874_, v_a_1601_);
if (lean_obj_tag(v___x_1889_) == 0)
{
lean_dec_ref(v___x_1889_);
goto v___jp_1603_;
}
else
{
lean_object* v_a_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1897_; 
v_a_1890_ = lean_ctor_get(v___x_1889_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1889_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1892_ = v___x_1889_;
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_a_1890_);
lean_dec(v___x_1889_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1895_; 
if (v_isShared_1893_ == 0)
{
v___x_1895_ = v___x_1892_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_a_1890_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
return v___x_1895_;
}
}
}
}
}
}
else
{
lean_object* v_val_1898_; uint8_t v___x_1899_; 
lean_del_object(v___x_1859_);
v_val_1898_ = lean_ctor_get(v_defaultBranch_x3f_1863_, 0);
lean_inc(v_val_1898_);
lean_dec_ref(v_defaultBranch_x3f_1863_);
v___x_1899_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_1899_ == 0)
{
v___y_1628_ = v_fullName_1866_;
v___y_1629_ = v_subDir_x3f_1864_;
v___y_1630_ = v_githubUrl_x3f_1862_;
v___y_1631_ = v___x_1867_;
v___y_1632_ = v_url_1861_;
v_rev_x3f_1633_ = v_val_1898_;
v___y_1634_ = v_a_1601_;
goto v___jp_1627_;
}
else
{
lean_object* v___x_1900_; uint8_t v___x_1901_; 
v___x_1900_ = lean_box(0);
v___x_1901_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_1901_ == 0)
{
if (v___x_1899_ == 0)
{
v___y_1628_ = v_fullName_1866_;
v___y_1629_ = v_subDir_x3f_1864_;
v___y_1630_ = v_githubUrl_x3f_1862_;
v___y_1631_ = v___x_1867_;
v___y_1632_ = v_url_1861_;
v_rev_x3f_1633_ = v_val_1898_;
v___y_1634_ = v_a_1601_;
goto v___jp_1627_;
}
else
{
size_t v___x_1902_; size_t v___x_1903_; lean_object* v___x_1904_; 
v___x_1902_ = ((size_t)0ULL);
v___x_1903_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
lean_inc_ref(v_a_1601_);
v___x_1904_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v___x_1868_, v___x_1902_, v___x_1903_, v___x_1900_, v_a_1601_);
if (lean_obj_tag(v___x_1904_) == 0)
{
lean_dec_ref(v___x_1904_);
v___y_1628_ = v_fullName_1866_;
v___y_1629_ = v_subDir_x3f_1864_;
v___y_1630_ = v_githubUrl_x3f_1862_;
v___y_1631_ = v___x_1867_;
v___y_1632_ = v_url_1861_;
v_rev_x3f_1633_ = v_val_1898_;
v___y_1634_ = v_a_1601_;
goto v___jp_1627_;
}
else
{
lean_object* v_a_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1912_; 
lean_dec(v_val_1898_);
lean_dec_ref(v___x_1867_);
lean_dec_ref(v_fullName_1866_);
lean_dec(v_subDir_x3f_1864_);
lean_dec(v_githubUrl_x3f_1862_);
lean_dec_ref(v_url_1861_);
lean_dec_ref(v_a_1601_);
lean_dec_ref(v_wsDir_1598_);
lean_dec_ref(v_lakeEnv_1597_);
lean_dec_ref(v_dep_1595_);
v_a_1905_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1912_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1907_ = v___x_1904_;
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_a_1905_);
lean_dec(v___x_1904_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1910_; 
if (v_isShared_1908_ == 0)
{
v___x_1910_ = v___x_1907_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v_a_1905_);
v___x_1910_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
return v___x_1910_;
}
}
}
}
}
else
{
size_t v___x_1913_; size_t v___x_1914_; lean_object* v___x_1915_; 
v___x_1913_ = ((size_t)0ULL);
v___x_1914_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
lean_inc_ref(v_a_1601_);
v___x_1915_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v___x_1868_, v___x_1913_, v___x_1914_, v___x_1900_, v_a_1601_);
if (lean_obj_tag(v___x_1915_) == 0)
{
lean_dec_ref(v___x_1915_);
v___y_1628_ = v_fullName_1866_;
v___y_1629_ = v_subDir_x3f_1864_;
v___y_1630_ = v_githubUrl_x3f_1862_;
v___y_1631_ = v___x_1867_;
v___y_1632_ = v_url_1861_;
v_rev_x3f_1633_ = v_val_1898_;
v___y_1634_ = v_a_1601_;
goto v___jp_1627_;
}
else
{
lean_object* v_a_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1923_; 
lean_dec(v_val_1898_);
lean_dec_ref(v___x_1867_);
lean_dec_ref(v_fullName_1866_);
lean_dec(v_subDir_x3f_1864_);
lean_dec(v_githubUrl_x3f_1862_);
lean_dec_ref(v_url_1861_);
lean_dec_ref(v_a_1601_);
lean_dec_ref(v_wsDir_1598_);
lean_dec_ref(v_lakeEnv_1597_);
lean_dec_ref(v_dep_1595_);
v_a_1916_ = lean_ctor_get(v___x_1915_, 0);
v_isSharedCheck_1923_ = !lean_is_exclusive(v___x_1915_);
if (v_isSharedCheck_1923_ == 0)
{
v___x_1918_ = v___x_1915_;
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_a_1916_);
lean_dec(v___x_1915_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v___x_1921_; 
if (v_isShared_1919_ == 0)
{
v___x_1921_ = v___x_1918_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v_a_1916_);
v___x_1921_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
return v___x_1921_;
}
}
}
}
}
}
}
case 1:
{
lean_object* v_rev_1924_; lean_object* v___x_1925_; uint8_t v___x_1926_; 
lean_dec(v_defaultBranch_x3f_1863_);
lean_del_object(v___x_1859_);
lean_del_object(v___x_1847_);
lean_dec_ref(v___y_1833_);
v_rev_1924_ = lean_ctor_get(v___y_1832_, 0);
lean_inc_ref(v_rev_1924_);
lean_dec_ref(v___y_1832_);
v___x_1925_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
v___x_1926_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_1926_ == 0)
{
v___y_1628_ = v_fullName_1866_;
v___y_1629_ = v_subDir_x3f_1864_;
v___y_1630_ = v_githubUrl_x3f_1862_;
v___y_1631_ = v___x_1867_;
v___y_1632_ = v_url_1861_;
v_rev_x3f_1633_ = v_rev_1924_;
v___y_1634_ = v_a_1601_;
goto v___jp_1627_;
}
else
{
lean_object* v___x_1927_; uint8_t v___x_1928_; 
v___x_1927_ = lean_box(0);
v___x_1928_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_1928_ == 0)
{
if (v___x_1926_ == 0)
{
v___y_1628_ = v_fullName_1866_;
v___y_1629_ = v_subDir_x3f_1864_;
v___y_1630_ = v_githubUrl_x3f_1862_;
v___y_1631_ = v___x_1867_;
v___y_1632_ = v_url_1861_;
v_rev_x3f_1633_ = v_rev_1924_;
v___y_1634_ = v_a_1601_;
goto v___jp_1627_;
}
else
{
size_t v___x_1929_; size_t v___x_1930_; lean_object* v___x_1931_; 
v___x_1929_ = ((size_t)0ULL);
v___x_1930_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
lean_inc_ref(v_a_1601_);
v___x_1931_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v___x_1925_, v___x_1929_, v___x_1930_, v___x_1927_, v_a_1601_);
if (lean_obj_tag(v___x_1931_) == 0)
{
lean_dec_ref(v___x_1931_);
v___y_1628_ = v_fullName_1866_;
v___y_1629_ = v_subDir_x3f_1864_;
v___y_1630_ = v_githubUrl_x3f_1862_;
v___y_1631_ = v___x_1867_;
v___y_1632_ = v_url_1861_;
v_rev_x3f_1633_ = v_rev_1924_;
v___y_1634_ = v_a_1601_;
goto v___jp_1627_;
}
else
{
lean_object* v_a_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1939_; 
lean_dec_ref(v_rev_1924_);
lean_dec_ref(v___x_1867_);
lean_dec_ref(v_fullName_1866_);
lean_dec(v_subDir_x3f_1864_);
lean_dec(v_githubUrl_x3f_1862_);
lean_dec_ref(v_url_1861_);
lean_dec_ref(v_a_1601_);
lean_dec_ref(v_wsDir_1598_);
lean_dec_ref(v_lakeEnv_1597_);
lean_dec_ref(v_dep_1595_);
v_a_1932_ = lean_ctor_get(v___x_1931_, 0);
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1931_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1934_ = v___x_1931_;
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_a_1932_);
lean_dec(v___x_1931_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v___x_1937_; 
if (v_isShared_1935_ == 0)
{
v___x_1937_ = v___x_1934_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_a_1932_);
v___x_1937_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
return v___x_1937_;
}
}
}
}
}
else
{
size_t v___x_1940_; size_t v___x_1941_; lean_object* v___x_1942_; 
v___x_1940_ = ((size_t)0ULL);
v___x_1941_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
lean_inc_ref(v_a_1601_);
v___x_1942_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v___x_1925_, v___x_1940_, v___x_1941_, v___x_1927_, v_a_1601_);
if (lean_obj_tag(v___x_1942_) == 0)
{
lean_dec_ref(v___x_1942_);
v___y_1628_ = v_fullName_1866_;
v___y_1629_ = v_subDir_x3f_1864_;
v___y_1630_ = v_githubUrl_x3f_1862_;
v___y_1631_ = v___x_1867_;
v___y_1632_ = v_url_1861_;
v_rev_x3f_1633_ = v_rev_1924_;
v___y_1634_ = v_a_1601_;
goto v___jp_1627_;
}
else
{
lean_object* v_a_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1950_; 
lean_dec_ref(v_rev_1924_);
lean_dec_ref(v___x_1867_);
lean_dec_ref(v_fullName_1866_);
lean_dec(v_subDir_x3f_1864_);
lean_dec(v_githubUrl_x3f_1862_);
lean_dec_ref(v_url_1861_);
lean_dec_ref(v_a_1601_);
lean_dec_ref(v_wsDir_1598_);
lean_dec_ref(v_lakeEnv_1597_);
lean_dec_ref(v_dep_1595_);
v_a_1943_ = lean_ctor_get(v___x_1942_, 0);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1942_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1945_ = v___x_1942_;
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_a_1943_);
lean_dec(v___x_1942_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___x_1948_; 
if (v_isShared_1946_ == 0)
{
v___x_1948_ = v___x_1945_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v_a_1943_);
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
}
default: 
{
lean_object* v_ver_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; 
lean_dec(v_defaultBranch_x3f_1863_);
lean_del_object(v___x_1859_);
v_ver_1951_ = lean_ctor_get(v___y_1832_, 0);
lean_inc_ref(v_ver_1951_);
lean_dec_ref(v___y_1832_);
v___x_1952_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
lean_inc_ref(v___y_1833_);
lean_inc_ref(v_scope_1638_);
lean_inc_ref(v_lakeEnv_1597_);
v___x_1953_ = l_Lake_Reservoir_fetchPkgVersions(v_lakeEnv_1597_, v_scope_1638_, v___y_1833_, v___x_1952_);
if (lean_obj_tag(v___x_1953_) == 0)
{
lean_object* v_a_1954_; lean_object* v_a_1955_; lean_object* v___x_1957_; 
v_a_1954_ = lean_ctor_get(v___x_1953_, 0);
lean_inc(v_a_1954_);
v_a_1955_ = lean_ctor_get(v___x_1953_, 1);
lean_inc(v_a_1955_);
lean_dec_ref(v___x_1953_);
if (v_isShared_1848_ == 0)
{
lean_ctor_set(v___x_1847_, 0, v_a_1954_);
v___x_1957_ = v___x_1847_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_a_1954_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
v___y_1796_ = v_fullName_1866_;
v___y_1797_ = v_ver_1951_;
v___y_1798_ = v_subDir_x3f_1864_;
v___y_1799_ = v_githubUrl_x3f_1862_;
v___y_1800_ = v___x_1867_;
v___y_1801_ = v___y_1833_;
v___y_1802_ = v_url_1861_;
v_fst_1803_ = v___x_1957_;
v_snd_1804_ = v_a_1955_;
goto v___jp_1795_;
}
}
else
{
lean_object* v_a_1959_; lean_object* v_a_1960_; lean_object* v___x_1962_; 
v_a_1959_ = lean_ctor_get(v___x_1953_, 0);
lean_inc(v_a_1959_);
v_a_1960_ = lean_ctor_get(v___x_1953_, 1);
lean_inc(v_a_1960_);
lean_dec_ref(v___x_1953_);
if (v_isShared_1848_ == 0)
{
lean_ctor_set_tag(v___x_1847_, 0);
lean_ctor_set(v___x_1847_, 0, v_a_1959_);
v___x_1962_ = v___x_1847_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v_a_1959_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
v___y_1796_ = v_fullName_1866_;
v___y_1797_ = v_ver_1951_;
v___y_1798_ = v_subDir_x3f_1864_;
v___y_1799_ = v_githubUrl_x3f_1862_;
v___y_1800_ = v___x_1867_;
v___y_1801_ = v___y_1833_;
v___y_1802_ = v_url_1861_;
v_fst_1803_ = v___x_1962_;
v_snd_1804_ = v_a_1960_;
goto v___jp_1795_;
}
}
}
}
}
else
{
lean_del_object(v___x_1859_);
lean_dec(v_val_1857_);
lean_del_object(v___x_1847_);
lean_dec_ref(v___y_1833_);
lean_dec(v___y_1832_);
lean_dec_ref(v_relPkgsDir_1599_);
lean_dec_ref(v_wsDir_1598_);
lean_dec_ref(v_lakeEnv_1597_);
lean_dec_ref(v_dep_1595_);
v___y_1607_ = v_val_1855_;
v___y_1608_ = v_a_1601_;
goto v___jp_1606_;
}
}
}
else
{
lean_dec(v___x_1856_);
lean_del_object(v___x_1847_);
lean_dec_ref(v___y_1833_);
lean_dec(v___y_1832_);
lean_dec_ref(v_relPkgsDir_1599_);
lean_dec_ref(v_wsDir_1598_);
lean_dec_ref(v_lakeEnv_1597_);
lean_dec_ref(v_dep_1595_);
v___y_1607_ = v_val_1855_;
v___y_1608_ = v_a_1601_;
goto v___jp_1606_;
}
}
}
}
}
v___jp_1966_:
{
lean_object* v___x_1971_; uint8_t v___x_1972_; 
v___x_1971_ = lean_array_get_size(v_snd_1970_);
v___x_1972_ = lean_nat_dec_lt(v___x_1794_, v___x_1971_);
if (v___x_1972_ == 0)
{
lean_dec_ref(v_snd_1970_);
v___y_1832_ = v___y_1968_;
v___y_1833_ = v___y_1967_;
v_a_1834_ = v_fst_1969_;
goto v___jp_1831_;
}
else
{
lean_object* v___x_1973_; uint8_t v___x_1974_; 
v___x_1973_ = lean_box(0);
v___x_1974_ = lean_nat_dec_le(v___x_1971_, v___x_1971_);
if (v___x_1974_ == 0)
{
if (v___x_1972_ == 0)
{
lean_dec_ref(v_snd_1970_);
v___y_1832_ = v___y_1968_;
v___y_1833_ = v___y_1967_;
v_a_1834_ = v_fst_1969_;
goto v___jp_1831_;
}
else
{
size_t v___x_1975_; size_t v___x_1976_; lean_object* v___x_1977_; 
v___x_1975_ = ((size_t)0ULL);
v___x_1976_ = lean_usize_of_nat(v___x_1971_);
lean_inc_ref(v_a_1601_);
v___x_1977_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_snd_1970_, v___x_1975_, v___x_1976_, v___x_1973_, v_a_1601_);
lean_dec_ref(v_snd_1970_);
if (lean_obj_tag(v___x_1977_) == 0)
{
lean_dec_ref(v___x_1977_);
v___y_1832_ = v___y_1968_;
v___y_1833_ = v___y_1967_;
v_a_1834_ = v_fst_1969_;
goto v___jp_1831_;
}
else
{
lean_object* v_a_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1985_; 
lean_dec_ref(v_fst_1969_);
lean_dec(v___y_1968_);
lean_dec_ref(v___y_1967_);
lean_dec_ref(v_a_1601_);
lean_dec_ref(v_relPkgsDir_1599_);
lean_dec_ref(v_wsDir_1598_);
lean_dec_ref(v_lakeEnv_1597_);
lean_dec_ref(v_dep_1595_);
v_a_1978_ = lean_ctor_get(v___x_1977_, 0);
v_isSharedCheck_1985_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1980_ = v___x_1977_;
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_a_1978_);
lean_dec(v___x_1977_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v___x_1983_; 
if (v_isShared_1981_ == 0)
{
v___x_1983_ = v___x_1980_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v_a_1978_);
v___x_1983_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
return v___x_1983_;
}
}
}
}
}
else
{
size_t v___x_1986_; size_t v___x_1987_; lean_object* v___x_1988_; 
v___x_1986_ = ((size_t)0ULL);
v___x_1987_ = lean_usize_of_nat(v___x_1971_);
lean_inc_ref(v_a_1601_);
v___x_1988_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_snd_1970_, v___x_1986_, v___x_1987_, v___x_1973_, v_a_1601_);
lean_dec_ref(v_snd_1970_);
if (lean_obj_tag(v___x_1988_) == 0)
{
lean_dec_ref(v___x_1988_);
v___y_1832_ = v___y_1968_;
v___y_1833_ = v___y_1967_;
v_a_1834_ = v_fst_1969_;
goto v___jp_1831_;
}
else
{
lean_object* v_a_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_1996_; 
lean_dec_ref(v_fst_1969_);
lean_dec(v___y_1968_);
lean_dec_ref(v___y_1967_);
lean_dec_ref(v_a_1601_);
lean_dec_ref(v_relPkgsDir_1599_);
lean_dec_ref(v_wsDir_1598_);
lean_dec_ref(v_lakeEnv_1597_);
lean_dec_ref(v_dep_1595_);
v_a_1989_ = lean_ctor_get(v___x_1988_, 0);
v_isSharedCheck_1996_ = !lean_is_exclusive(v___x_1988_);
if (v_isSharedCheck_1996_ == 0)
{
v___x_1991_ = v___x_1988_;
v_isShared_1992_ = v_isSharedCheck_1996_;
goto v_resetjp_1990_;
}
else
{
lean_inc(v_a_1989_);
lean_dec(v___x_1988_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_1996_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v___x_1994_; 
if (v_isShared_1992_ == 0)
{
v___x_1994_ = v___x_1991_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v_a_1989_);
v___x_1994_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
return v___x_1994_;
}
}
}
}
}
}
v___jp_1998_:
{
lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; 
lean_inc(v_name_1637_);
v___x_2000_ = l_Lean_Name_toString(v_name_1637_, v___x_1997_);
v___x_2001_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
lean_inc_ref(v___x_2000_);
lean_inc_ref(v_scope_1638_);
lean_inc_ref(v_lakeEnv_1597_);
v___x_2002_ = l_Lake_Reservoir_fetchPkg_x3f(v_lakeEnv_1597_, v_scope_1638_, v___x_2000_, v___x_2001_);
if (lean_obj_tag(v___x_2002_) == 0)
{
lean_object* v_a_2003_; lean_object* v_a_2004_; lean_object* v___x_2005_; 
v_a_2003_ = lean_ctor_get(v___x_2002_, 0);
lean_inc(v_a_2003_);
v_a_2004_ = lean_ctor_get(v___x_2002_, 1);
lean_inc(v_a_2004_);
lean_dec_ref(v___x_2002_);
v___x_2005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2005_, 0, v_a_2003_);
v___y_1967_ = v___x_2000_;
v___y_1968_ = v_a_1999_;
v_fst_1969_ = v___x_2005_;
v_snd_1970_ = v_a_2004_;
goto v___jp_1966_;
}
else
{
lean_object* v_a_2006_; lean_object* v_a_2007_; lean_object* v___x_2008_; 
v_a_2006_ = lean_ctor_get(v___x_2002_, 0);
lean_inc(v_a_2006_);
v_a_2007_ = lean_ctor_get(v___x_2002_, 1);
lean_inc(v_a_2007_);
lean_dec_ref(v___x_2002_);
v___x_2008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2008_, 0, v_a_2006_);
v___y_1967_ = v___x_2000_;
v___y_1968_ = v_a_1999_;
v_fst_1969_ = v___x_2008_;
v_snd_1970_ = v_a_2007_;
goto v___jp_1966_;
}
}
}
v___jp_1603_:
{
lean_object* v___x_1604_; lean_object* v___x_1605_; 
v___x_1604_ = lean_box(0);
v___x_1605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1605_, 0, v___x_1604_);
return v___x_1605_;
}
v___jp_1606_:
{
lean_object* v_fullName_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; uint8_t v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; 
v_fullName_1609_ = lean_ctor_get(v___y_1607_, 1);
lean_inc_ref(v_fullName_1609_);
lean_dec_ref(v___y_1607_);
v___x_1610_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__0));
v___x_1611_ = lean_string_append(v_fullName_1609_, v___x_1610_);
v___x_1612_ = 3;
v___x_1613_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1613_, 0, v___x_1611_);
lean_ctor_set_uint8(v___x_1613_, sizeof(void*)*1, v___x_1612_);
v___x_1614_ = lean_apply_2(v___y_1608_, v___x_1613_, lean_box(0));
v___x_1615_ = lean_box(0);
v___x_1616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1616_, 0, v___x_1615_);
return v___x_1616_;
}
v___jp_1617_:
{
lean_object* v___x_1625_; lean_object* v___x_1626_; 
v___x_1625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1625_, 0, v___y_1620_);
v___x_1626_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit(v_dep_1595_, v_inherited_1596_, v_lakeEnv_1597_, v_wsDir_1598_, v___y_1618_, v___y_1621_, v___y_1623_, v___y_1624_, v___x_1625_, v___y_1619_, v___y_1622_);
lean_dec_ref(v_lakeEnv_1597_);
lean_dec_ref(v_dep_1595_);
return v___x_1626_;
}
v___jp_1627_:
{
if (lean_obj_tag(v___y_1630_) == 0)
{
lean_object* v___x_1635_; 
v___x_1635_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___y_1618_ = v___y_1628_;
v___y_1619_ = v___y_1629_;
v___y_1620_ = v_rev_x3f_1633_;
v___y_1621_ = v___y_1631_;
v___y_1622_ = v___y_1634_;
v___y_1623_ = v___y_1632_;
v___y_1624_ = v___x_1635_;
goto v___jp_1617_;
}
else
{
lean_object* v_val_1636_; 
v_val_1636_ = lean_ctor_get(v___y_1630_, 0);
lean_inc(v_val_1636_);
lean_dec_ref(v___y_1630_);
v___y_1618_ = v___y_1628_;
v___y_1619_ = v___y_1629_;
v___y_1620_ = v_rev_x3f_1633_;
v___y_1621_ = v___y_1631_;
v___y_1622_ = v___y_1634_;
v___y_1623_ = v___y_1632_;
v___y_1624_ = v_val_1636_;
goto v___jp_1617_;
}
}
v___jp_1641_:
{
lean_object* v_toString_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; uint8_t v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; 
v_toString_1644_ = lean_ctor_get(v___y_1642_, 0);
lean_inc_ref(v_toString_1644_);
lean_dec_ref(v___y_1642_);
v___x_1645_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
v___x_1646_ = lean_string_append(v_scope_1638_, v___x_1645_);
v___x_1647_ = lean_string_append(v___x_1646_, v___y_1643_);
lean_dec_ref(v___y_1643_);
v___x_1648_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__1));
v___x_1649_ = lean_string_append(v___x_1647_, v___x_1648_);
v___x_1650_ = lean_string_append(v___x_1649_, v_toString_1644_);
lean_dec_ref(v_toString_1644_);
v___x_1651_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__2));
v___x_1652_ = lean_string_append(v___x_1650_, v___x_1651_);
v___x_1653_ = 3;
v___x_1654_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1654_, 0, v___x_1652_);
lean_ctor_set_uint8(v___x_1654_, sizeof(void*)*1, v___x_1653_);
v___x_1655_ = lean_apply_2(v_a_1601_, v___x_1654_, lean_box(0));
v___x_1656_ = lean_box(0);
v___x_1657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1657_, 0, v___x_1656_);
return v___x_1657_;
}
v___jp_1658_:
{
if (lean_obj_tag(v_a_1666_) == 0)
{
lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1682_; 
lean_inc_ref(v_scope_1638_);
lean_dec_ref(v___y_1665_);
lean_dec_ref(v___y_1663_);
lean_dec(v___y_1662_);
lean_dec(v___y_1661_);
lean_dec_ref(v___y_1660_);
lean_dec_ref(v___y_1659_);
lean_dec_ref(v_wsDir_1598_);
lean_dec_ref(v_lakeEnv_1597_);
lean_dec_ref(v_dep_1595_);
v_isSharedCheck_1682_ = !lean_is_exclusive(v_a_1666_);
if (v_isSharedCheck_1682_ == 0)
{
lean_object* v_unused_1683_; 
v_unused_1683_ = lean_ctor_get(v_a_1666_, 0);
lean_dec(v_unused_1683_);
v___x_1668_ = v_a_1666_;
v_isShared_1669_ = v_isSharedCheck_1682_;
goto v_resetjp_1667_;
}
else
{
lean_dec(v_a_1666_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1682_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; uint8_t v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1680_; 
v___x_1670_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
v___x_1671_ = lean_string_append(v_scope_1638_, v___x_1670_);
v___x_1672_ = lean_string_append(v___x_1671_, v___y_1664_);
lean_dec_ref(v___y_1664_);
v___x_1673_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__3));
v___x_1674_ = lean_string_append(v___x_1672_, v___x_1673_);
v___x_1675_ = 3;
v___x_1676_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1676_, 0, v___x_1674_);
lean_ctor_set_uint8(v___x_1676_, sizeof(void*)*1, v___x_1675_);
v___x_1677_ = lean_apply_2(v_a_1601_, v___x_1676_, lean_box(0));
v___x_1678_ = lean_box(0);
if (v_isShared_1669_ == 0)
{
lean_ctor_set_tag(v___x_1668_, 1);
lean_ctor_set(v___x_1668_, 0, v___x_1678_);
v___x_1680_ = v___x_1668_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v___x_1678_);
v___x_1680_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
return v___x_1680_;
}
}
}
else
{
lean_object* v_a_1684_; lean_object* v___x_1685_; size_t v_sz_1686_; size_t v___x_1687_; lean_object* v___x_1688_; lean_object* v_fst_1689_; 
v_a_1684_ = lean_ctor_get(v_a_1666_, 0);
lean_inc(v_a_1684_);
lean_dec_ref(v_a_1666_);
v___x_1685_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___closed__0));
v_sz_1686_ = lean_array_size(v_a_1684_);
v___x_1687_ = ((size_t)0ULL);
v___x_1688_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(v___y_1660_, v_a_1684_, v_sz_1686_, v___x_1687_, v___x_1685_);
lean_dec(v_a_1684_);
v_fst_1689_ = lean_ctor_get(v___x_1688_, 0);
lean_inc(v_fst_1689_);
lean_dec_ref(v___x_1688_);
if (lean_obj_tag(v_fst_1689_) == 0)
{
lean_inc_ref(v_scope_1638_);
lean_dec_ref(v___y_1665_);
lean_dec_ref(v___y_1663_);
lean_dec(v___y_1662_);
lean_dec(v___y_1661_);
lean_dec_ref(v___y_1659_);
lean_dec_ref(v_wsDir_1598_);
lean_dec_ref(v_lakeEnv_1597_);
lean_dec_ref(v_dep_1595_);
v___y_1642_ = v___y_1660_;
v___y_1643_ = v___y_1664_;
goto v___jp_1641_;
}
else
{
lean_object* v_val_1690_; 
v_val_1690_ = lean_ctor_get(v_fst_1689_, 0);
lean_inc(v_val_1690_);
lean_dec_ref(v_fst_1689_);
if (lean_obj_tag(v_val_1690_) == 1)
{
lean_object* v_val_1691_; lean_object* v_version_1692_; lean_object* v_revision_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; uint8_t v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; 
lean_dec_ref(v___y_1660_);
v_val_1691_ = lean_ctor_get(v_val_1690_, 0);
lean_inc(v_val_1691_);
lean_dec_ref(v_val_1690_);
v_version_1692_ = lean_ctor_get(v_val_1691_, 0);
lean_inc_ref(v_version_1692_);
v_revision_1693_ = lean_ctor_get(v_val_1691_, 1);
lean_inc_ref(v_revision_1693_);
lean_dec(v_val_1691_);
v___x_1694_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
lean_inc_ref(v_scope_1638_);
v___x_1695_ = lean_string_append(v_scope_1638_, v___x_1694_);
v___x_1696_ = lean_string_append(v___x_1695_, v___y_1664_);
lean_dec_ref(v___y_1664_);
v___x_1697_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__4));
v___x_1698_ = lean_string_append(v___x_1696_, v___x_1697_);
v___x_1699_ = l_Lake_StdVer_toString(v_version_1692_);
v___x_1700_ = lean_string_append(v___x_1698_, v___x_1699_);
lean_dec_ref(v___x_1699_);
v___x_1701_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__5));
v___x_1702_ = lean_string_append(v___x_1700_, v___x_1701_);
v___x_1703_ = lean_string_append(v___x_1702_, v_revision_1693_);
v___x_1704_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__6));
v___x_1705_ = lean_string_append(v___x_1703_, v___x_1704_);
v___x_1706_ = 1;
v___x_1707_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1707_, 0, v___x_1705_);
lean_ctor_set_uint8(v___x_1707_, sizeof(void*)*1, v___x_1706_);
lean_inc_ref(v_a_1601_);
v___x_1708_ = lean_apply_2(v_a_1601_, v___x_1707_, lean_box(0));
v___y_1628_ = v___y_1659_;
v___y_1629_ = v___y_1661_;
v___y_1630_ = v___y_1662_;
v___y_1631_ = v___y_1663_;
v___y_1632_ = v___y_1665_;
v_rev_x3f_1633_ = v_revision_1693_;
v___y_1634_ = v_a_1601_;
goto v___jp_1627_;
}
else
{
lean_inc_ref(v_scope_1638_);
lean_dec(v_val_1690_);
lean_dec_ref(v___y_1665_);
lean_dec_ref(v___y_1663_);
lean_dec(v___y_1662_);
lean_dec(v___y_1661_);
lean_dec_ref(v___y_1659_);
lean_dec_ref(v_wsDir_1598_);
lean_dec_ref(v_lakeEnv_1597_);
lean_dec_ref(v_dep_1595_);
v___y_1642_ = v___y_1660_;
v___y_1643_ = v___y_1664_;
goto v___jp_1641_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize___boxed(lean_object* v_dep_2057_, lean_object* v_inherited_2058_, lean_object* v_lakeEnv_2059_, lean_object* v_wsDir_2060_, lean_object* v_relPkgsDir_2061_, lean_object* v_relParentDir_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_){
_start:
{
uint8_t v_inherited_boxed_2065_; lean_object* v_res_2066_; 
v_inherited_boxed_2065_ = lean_unbox(v_inherited_2058_);
v_res_2066_ = l_Lake_Dependency_materialize(v_dep_2057_, v_inherited_boxed_2065_, v_lakeEnv_2059_, v_wsDir_2060_, v_relPkgsDir_2061_, v_relParentDir_2062_, v_a_2063_);
return v_res_2066_;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__0(void){
_start:
{
uint32_t v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; 
v___x_2067_ = 0;
v___x_2068_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___x_2069_ = lean_alloc_ctor(11, 2, 4);
lean_ctor_set(v___x_2069_, 0, v___x_2068_);
lean_ctor_set(v___x_2069_, 1, v___x_2068_);
lean_ctor_set_uint32(v___x_2069_, sizeof(void*)*2, v___x_2067_);
return v___x_2069_;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1(void){
_start:
{
lean_object* v___x_2070_; lean_object* v___x_2071_; 
v___x_2070_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__0, &l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__0_once, _init_l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__0);
v___x_2071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2070_);
return v___x_2071_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep(lean_object* v_manifestEntry_2072_, lean_object* v_pkgDir_2073_, lean_object* v_relPkgDir_2074_, lean_object* v_remoteUrl_2075_, lean_object* v_a_2076_){
_start:
{
lean_object* v_a_2079_; lean_object* v_manifestFile_x3f_2082_; 
v_manifestFile_x3f_2082_ = lean_ctor_get(v_manifestEntry_2072_, 3);
if (lean_obj_tag(v_manifestFile_x3f_2082_) == 1)
{
lean_object* v_val_2083_; lean_object* v___f_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v_a_2089_; lean_object* v_a_2090_; lean_object* v___x_2119_; lean_object* v___x_2120_; 
v_val_2083_ = lean_ctor_get(v_manifestFile_x3f_2082_, 0);
v___f_2084_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0));
lean_inc(v_val_2083_);
v___x_2085_ = l_Lake_joinRelative(v_pkgDir_2073_, v_val_2083_);
v___x_2086_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__2, &l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__2_once, _init_l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__2);
v___x_2087_ = lean_unsigned_to_nat(0u);
v___x_2119_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
v___x_2120_ = l_Lake_Manifest_load(v___x_2085_);
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_object* v_a_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2128_; 
v_a_2121_ = lean_ctor_get(v___x_2120_, 0);
v_isSharedCheck_2128_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2123_ = v___x_2120_;
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_a_2121_);
lean_dec(v___x_2120_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v___x_2126_; 
if (v_isShared_2124_ == 0)
{
lean_ctor_set_tag(v___x_2123_, 1);
v___x_2126_ = v___x_2123_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v_a_2121_);
v___x_2126_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
v_a_2089_ = v___x_2126_;
v_a_2090_ = v___x_2119_;
goto v___jp_2088_;
}
}
}
else
{
lean_object* v_a_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2136_; 
v_a_2129_ = lean_ctor_get(v___x_2120_, 0);
v_isSharedCheck_2136_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2136_ == 0)
{
v___x_2131_ = v___x_2120_;
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_a_2129_);
lean_dec(v___x_2120_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v___x_2134_; 
if (v_isShared_2132_ == 0)
{
lean_ctor_set_tag(v___x_2131_, 0);
v___x_2134_ = v___x_2131_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v_a_2129_);
v___x_2134_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
v_a_2089_ = v___x_2134_;
v_a_2090_ = v___x_2119_;
goto v___jp_2088_;
}
}
}
v___jp_2088_:
{
lean_object* v___x_2091_; uint8_t v___x_2092_; 
v___x_2091_ = lean_array_get_size(v_a_2090_);
v___x_2092_ = lean_nat_dec_lt(v___x_2087_, v___x_2091_);
if (v___x_2092_ == 0)
{
lean_dec_ref(v_a_2090_);
lean_dec_ref(v_a_2076_);
v_a_2079_ = v_a_2089_;
goto v___jp_2078_;
}
else
{
lean_object* v___x_2093_; uint8_t v___x_2094_; 
v___x_2093_ = lean_box(0);
v___x_2094_ = lean_nat_dec_le(v___x_2091_, v___x_2091_);
if (v___x_2094_ == 0)
{
if (v___x_2092_ == 0)
{
lean_dec_ref(v_a_2090_);
lean_dec_ref(v_a_2076_);
v_a_2079_ = v_a_2089_;
goto v___jp_2078_;
}
else
{
size_t v___x_2095_; size_t v___x_2096_; lean_object* v___x_1281__overap_2097_; lean_object* v___x_2098_; 
v___x_2095_ = ((size_t)0ULL);
v___x_2096_ = lean_usize_of_nat(v___x_2091_);
v___x_1281__overap_2097_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2086_, v___f_2084_, v_a_2090_, v___x_2095_, v___x_2096_, v___x_2093_);
v___x_2098_ = lean_apply_2(v___x_1281__overap_2097_, v_a_2076_, lean_box(0));
if (lean_obj_tag(v___x_2098_) == 0)
{
lean_dec_ref(v___x_2098_);
v_a_2079_ = v_a_2089_;
goto v___jp_2078_;
}
else
{
lean_object* v_a_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2106_; 
lean_dec_ref(v_a_2089_);
lean_dec_ref(v_remoteUrl_2075_);
lean_dec_ref(v_relPkgDir_2074_);
lean_dec_ref(v_manifestEntry_2072_);
v_a_2099_ = lean_ctor_get(v___x_2098_, 0);
v_isSharedCheck_2106_ = !lean_is_exclusive(v___x_2098_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2101_ = v___x_2098_;
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_a_2099_);
lean_dec(v___x_2098_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2104_; 
if (v_isShared_2102_ == 0)
{
v___x_2104_ = v___x_2101_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v_a_2099_);
v___x_2104_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
return v___x_2104_;
}
}
}
}
}
else
{
size_t v___x_2107_; size_t v___x_2108_; lean_object* v___x_1291__overap_2109_; lean_object* v___x_2110_; 
v___x_2107_ = ((size_t)0ULL);
v___x_2108_ = lean_usize_of_nat(v___x_2091_);
v___x_1291__overap_2109_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2086_, v___f_2084_, v_a_2090_, v___x_2107_, v___x_2108_, v___x_2093_);
v___x_2110_ = lean_apply_2(v___x_1291__overap_2109_, v_a_2076_, lean_box(0));
if (lean_obj_tag(v___x_2110_) == 0)
{
lean_dec_ref(v___x_2110_);
v_a_2079_ = v_a_2089_;
goto v___jp_2078_;
}
else
{
lean_object* v_a_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2118_; 
lean_dec_ref(v_a_2089_);
lean_dec_ref(v_remoteUrl_2075_);
lean_dec_ref(v_relPkgDir_2074_);
lean_dec_ref(v_manifestEntry_2072_);
v_a_2111_ = lean_ctor_get(v___x_2110_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2110_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2113_ = v___x_2110_;
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_a_2111_);
lean_dec(v___x_2110_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v___x_2116_; 
if (v_isShared_2114_ == 0)
{
v___x_2116_ = v___x_2113_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_a_2111_);
v___x_2116_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
return v___x_2116_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2137_; 
lean_dec_ref(v_a_2076_);
lean_dec_ref(v_pkgDir_2073_);
v___x_2137_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1, &l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1_once, _init_l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1);
v_a_2079_ = v___x_2137_;
goto v___jp_2078_;
}
v___jp_2078_:
{
lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2080_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2080_, 0, v_relPkgDir_2074_);
lean_ctor_set(v___x_2080_, 1, v_remoteUrl_2075_);
lean_ctor_set(v___x_2080_, 2, v_a_2079_);
lean_ctor_set(v___x_2080_, 3, v_manifestEntry_2072_);
v___x_2081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2081_, 0, v___x_2080_);
return v___x_2081_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___boxed(lean_object* v_manifestEntry_2138_, lean_object* v_pkgDir_2139_, lean_object* v_relPkgDir_2140_, lean_object* v_remoteUrl_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_){
_start:
{
lean_object* v_res_2144_; 
v_res_2144_ = l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep(v_manifestEntry_2138_, v_pkgDir_2139_, v_relPkgDir_2140_, v_remoteUrl_2141_, v_a_2142_);
return v_res_2144_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize(lean_object* v_manifestEntry_2146_, lean_object* v_lakeEnv_2147_, lean_object* v_wsDir_2148_, lean_object* v_relPkgsDir_2149_, lean_object* v_a_2150_){
_start:
{
lean_object* v___y_2153_; lean_object* v___y_2154_; lean_object* v_a_2155_; lean_object* v___y_2159_; lean_object* v___y_2160_; lean_object* v___y_2161_; lean_object* v___y_2162_; lean_object* v_a_2163_; lean_object* v_a_2164_; lean_object* v_src_2191_; 
v_src_2191_ = lean_ctor_get(v_manifestEntry_2146_, 4);
lean_inc_ref(v_src_2191_);
if (lean_obj_tag(v_src_2191_) == 0)
{
lean_object* v_manifestFile_x3f_2192_; lean_object* v_dir_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2256_; 
lean_dec_ref(v_relPkgsDir_2149_);
v_manifestFile_x3f_2192_ = lean_ctor_get(v_manifestEntry_2146_, 3);
v_dir_2193_ = lean_ctor_get(v_src_2191_, 0);
v_isSharedCheck_2256_ = !lean_is_exclusive(v_src_2191_);
if (v_isSharedCheck_2256_ == 0)
{
v___x_2195_ = v_src_2191_;
v_isShared_2196_ = v_isSharedCheck_2256_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_dir_2193_);
lean_dec(v_src_2191_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2256_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
lean_object* v___x_2197_; lean_object* v_a_2199_; 
v___x_2197_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
if (lean_obj_tag(v_manifestFile_x3f_2192_) == 1)
{
lean_object* v_val_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v_a_2209_; lean_object* v_a_2210_; lean_object* v___x_2237_; lean_object* v___x_2238_; 
v_val_2204_ = lean_ctor_get(v_manifestFile_x3f_2192_, 0);
lean_inc_ref(v_dir_2193_);
v___x_2205_ = l_Lake_joinRelative(v_wsDir_2148_, v_dir_2193_);
lean_inc(v_val_2204_);
v___x_2206_ = l_Lake_joinRelative(v___x_2205_, v_val_2204_);
v___x_2207_ = lean_unsigned_to_nat(0u);
v___x_2237_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
v___x_2238_ = l_Lake_Manifest_load(v___x_2206_);
if (lean_obj_tag(v___x_2238_) == 0)
{
lean_object* v_a_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2246_; 
v_a_2239_ = lean_ctor_get(v___x_2238_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2238_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2241_ = v___x_2238_;
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_a_2239_);
lean_dec(v___x_2238_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v___x_2244_; 
if (v_isShared_2242_ == 0)
{
lean_ctor_set_tag(v___x_2241_, 1);
v___x_2244_ = v___x_2241_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_a_2239_);
v___x_2244_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
v_a_2209_ = v___x_2244_;
v_a_2210_ = v___x_2237_;
goto v___jp_2208_;
}
}
}
else
{
lean_object* v_a_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2254_; 
v_a_2247_ = lean_ctor_get(v___x_2238_, 0);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2238_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2249_ = v___x_2238_;
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_a_2247_);
lean_dec(v___x_2238_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v___x_2252_; 
if (v_isShared_2250_ == 0)
{
lean_ctor_set_tag(v___x_2249_, 0);
v___x_2252_ = v___x_2249_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_a_2247_);
v___x_2252_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
v_a_2209_ = v___x_2252_;
v_a_2210_ = v___x_2237_;
goto v___jp_2208_;
}
}
}
v___jp_2208_:
{
lean_object* v___x_2211_; uint8_t v___x_2212_; 
v___x_2211_ = lean_array_get_size(v_a_2210_);
v___x_2212_ = lean_nat_dec_lt(v___x_2207_, v___x_2211_);
if (v___x_2212_ == 0)
{
lean_dec_ref(v_a_2210_);
lean_dec_ref(v_a_2150_);
v_a_2199_ = v_a_2209_;
goto v___jp_2198_;
}
else
{
lean_object* v___x_2213_; uint8_t v___x_2214_; 
v___x_2213_ = lean_box(0);
v___x_2214_ = lean_nat_dec_le(v___x_2211_, v___x_2211_);
if (v___x_2214_ == 0)
{
if (v___x_2212_ == 0)
{
lean_dec_ref(v_a_2210_);
lean_dec_ref(v_a_2150_);
v_a_2199_ = v_a_2209_;
goto v___jp_2198_;
}
else
{
size_t v___x_2215_; size_t v___x_2216_; lean_object* v___x_2217_; 
v___x_2215_ = ((size_t)0ULL);
v___x_2216_ = lean_usize_of_nat(v___x_2211_);
v___x_2217_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_2210_, v___x_2215_, v___x_2216_, v___x_2213_, v_a_2150_);
lean_dec_ref(v_a_2210_);
if (lean_obj_tag(v___x_2217_) == 0)
{
lean_dec_ref(v___x_2217_);
v_a_2199_ = v_a_2209_;
goto v___jp_2198_;
}
else
{
lean_object* v_a_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2225_; 
lean_dec_ref(v_a_2209_);
lean_del_object(v___x_2195_);
lean_dec_ref(v_dir_2193_);
lean_dec_ref(v_manifestEntry_2146_);
v_a_2218_ = lean_ctor_get(v___x_2217_, 0);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2217_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2220_ = v___x_2217_;
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_a_2218_);
lean_dec(v___x_2217_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v___x_2223_; 
if (v_isShared_2221_ == 0)
{
v___x_2223_ = v___x_2220_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_a_2218_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
}
}
}
else
{
size_t v___x_2226_; size_t v___x_2227_; lean_object* v___x_2228_; 
v___x_2226_ = ((size_t)0ULL);
v___x_2227_ = lean_usize_of_nat(v___x_2211_);
v___x_2228_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_2210_, v___x_2226_, v___x_2227_, v___x_2213_, v_a_2150_);
lean_dec_ref(v_a_2210_);
if (lean_obj_tag(v___x_2228_) == 0)
{
lean_dec_ref(v___x_2228_);
v_a_2199_ = v_a_2209_;
goto v___jp_2198_;
}
else
{
lean_object* v_a_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2236_; 
lean_dec_ref(v_a_2209_);
lean_del_object(v___x_2195_);
lean_dec_ref(v_dir_2193_);
lean_dec_ref(v_manifestEntry_2146_);
v_a_2229_ = lean_ctor_get(v___x_2228_, 0);
v_isSharedCheck_2236_ = !lean_is_exclusive(v___x_2228_);
if (v_isSharedCheck_2236_ == 0)
{
v___x_2231_ = v___x_2228_;
v_isShared_2232_ = v_isSharedCheck_2236_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_a_2229_);
lean_dec(v___x_2228_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2236_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
lean_object* v___x_2234_; 
if (v_isShared_2232_ == 0)
{
v___x_2234_ = v___x_2231_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v_a_2229_);
v___x_2234_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
return v___x_2234_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2255_; 
lean_dec_ref(v_a_2150_);
lean_dec_ref(v_wsDir_2148_);
v___x_2255_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1, &l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1_once, _init_l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1);
v_a_2199_ = v___x_2255_;
goto v___jp_2198_;
}
v___jp_2198_:
{
lean_object* v___x_2200_; lean_object* v___x_2202_; 
v___x_2200_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2200_, 0, v_dir_2193_);
lean_ctor_set(v___x_2200_, 1, v___x_2197_);
lean_ctor_set(v___x_2200_, 2, v_a_2199_);
lean_ctor_set(v___x_2200_, 3, v_manifestEntry_2146_);
if (v_isShared_2196_ == 0)
{
lean_ctor_set(v___x_2195_, 0, v___x_2200_);
v___x_2202_ = v___x_2195_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v___x_2200_);
v___x_2202_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
return v___x_2202_;
}
}
}
}
else
{
lean_object* v_name_2257_; lean_object* v_manifestFile_x3f_2258_; lean_object* v_url_2259_; lean_object* v_rev_2260_; lean_object* v_subDir_x3f_2261_; uint8_t v___x_2262_; lean_object* v_sname_2263_; lean_object* v_relGitDir_2264_; lean_object* v_gitDir_2265_; lean_object* v___y_2267_; lean_object* v___y_2268_; lean_object* v___y_2269_; lean_object* v___y_2293_; lean_object* v___y_2294_; lean_object* v___y_2299_; lean_object* v___y_2303_; lean_object* v___y_2304_; lean_object* v___y_2315_; uint8_t v_a_2327_; lean_object* v___y_2337_; lean_object* v___y_2338_; uint8_t v_val_2339_; uint8_t v___y_2367_; lean_object* v_a_2368_; uint8_t v___x_2378_; lean_object* v___x_2411_; uint8_t v___x_2412_; 
v_name_2257_ = lean_ctor_get(v_manifestEntry_2146_, 0);
v_manifestFile_x3f_2258_ = lean_ctor_get(v_manifestEntry_2146_, 3);
v_url_2259_ = lean_ctor_get(v_src_2191_, 0);
lean_inc_ref(v_url_2259_);
v_rev_2260_ = lean_ctor_get(v_src_2191_, 1);
lean_inc_ref(v_rev_2260_);
v_subDir_x3f_2261_ = lean_ctor_get(v_src_2191_, 3);
lean_inc(v_subDir_x3f_2261_);
lean_dec_ref(v_src_2191_);
v___x_2262_ = 0;
lean_inc(v_name_2257_);
v_sname_2263_ = l_Lean_Name_toString(v_name_2257_, v___x_2262_);
lean_inc_ref(v_sname_2263_);
v_relGitDir_2264_ = l_Lake_joinRelative(v_relPkgsDir_2149_, v_sname_2263_);
lean_inc_ref(v_relGitDir_2264_);
v_gitDir_2265_ = l_Lake_joinRelative(v_wsDir_2148_, v_relGitDir_2264_);
v___x_2378_ = l_System_FilePath_isDir(v_gitDir_2265_);
v___x_2411_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
v___x_2412_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_2412_ == 0)
{
goto v___jp_2379_;
}
else
{
lean_object* v___x_2413_; uint8_t v___x_2414_; 
v___x_2413_ = lean_box(0);
v___x_2414_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_2414_ == 0)
{
if (v___x_2412_ == 0)
{
goto v___jp_2379_;
}
else
{
size_t v___x_2415_; size_t v___x_2416_; lean_object* v___x_2417_; 
v___x_2415_ = ((size_t)0ULL);
v___x_2416_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
lean_inc_ref(v_a_2150_);
v___x_2417_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v___x_2411_, v___x_2415_, v___x_2416_, v___x_2413_, v_a_2150_);
if (lean_obj_tag(v___x_2417_) == 0)
{
lean_dec_ref(v___x_2417_);
goto v___jp_2379_;
}
else
{
lean_object* v_a_2418_; lean_object* v___x_2420_; uint8_t v_isShared_2421_; uint8_t v_isSharedCheck_2425_; 
lean_dec_ref(v_gitDir_2265_);
lean_dec_ref(v_relGitDir_2264_);
lean_dec_ref(v_sname_2263_);
lean_dec(v_subDir_x3f_2261_);
lean_dec_ref(v_rev_2260_);
lean_dec_ref(v_url_2259_);
lean_dec_ref(v_a_2150_);
lean_dec_ref(v_manifestEntry_2146_);
v_a_2418_ = lean_ctor_get(v___x_2417_, 0);
v_isSharedCheck_2425_ = !lean_is_exclusive(v___x_2417_);
if (v_isSharedCheck_2425_ == 0)
{
v___x_2420_ = v___x_2417_;
v_isShared_2421_ = v_isSharedCheck_2425_;
goto v_resetjp_2419_;
}
else
{
lean_inc(v_a_2418_);
lean_dec(v___x_2417_);
v___x_2420_ = lean_box(0);
v_isShared_2421_ = v_isSharedCheck_2425_;
goto v_resetjp_2419_;
}
v_resetjp_2419_:
{
lean_object* v___x_2423_; 
if (v_isShared_2421_ == 0)
{
v___x_2423_ = v___x_2420_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2424_; 
v_reuseFailAlloc_2424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2424_, 0, v_a_2418_);
v___x_2423_ = v_reuseFailAlloc_2424_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
return v___x_2423_;
}
}
}
}
}
else
{
size_t v___x_2426_; size_t v___x_2427_; lean_object* v___x_2428_; 
v___x_2426_ = ((size_t)0ULL);
v___x_2427_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
lean_inc_ref(v_a_2150_);
v___x_2428_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v___x_2411_, v___x_2426_, v___x_2427_, v___x_2413_, v_a_2150_);
if (lean_obj_tag(v___x_2428_) == 0)
{
lean_dec_ref(v___x_2428_);
goto v___jp_2379_;
}
else
{
lean_object* v_a_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2436_; 
lean_dec_ref(v_gitDir_2265_);
lean_dec_ref(v_relGitDir_2264_);
lean_dec_ref(v_sname_2263_);
lean_dec(v_subDir_x3f_2261_);
lean_dec_ref(v_rev_2260_);
lean_dec_ref(v_url_2259_);
lean_dec_ref(v_a_2150_);
lean_dec_ref(v_manifestEntry_2146_);
v_a_2429_ = lean_ctor_get(v___x_2428_, 0);
v_isSharedCheck_2436_ = !lean_is_exclusive(v___x_2428_);
if (v_isSharedCheck_2436_ == 0)
{
v___x_2431_ = v___x_2428_;
v_isShared_2432_ = v_isSharedCheck_2436_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_a_2429_);
lean_dec(v___x_2428_);
v___x_2431_ = lean_box(0);
v_isShared_2432_ = v_isSharedCheck_2436_;
goto v_resetjp_2430_;
}
v_resetjp_2430_:
{
lean_object* v___x_2434_; 
if (v_isShared_2432_ == 0)
{
v___x_2434_ = v___x_2431_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v_a_2429_);
v___x_2434_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
return v___x_2434_;
}
}
}
}
}
v___jp_2266_:
{
if (lean_obj_tag(v_manifestFile_x3f_2258_) == 1)
{
lean_object* v_val_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; 
v_val_2270_ = lean_ctor_get(v_manifestFile_x3f_2258_, 0);
lean_inc(v_val_2270_);
v___x_2271_ = l_Lake_joinRelative(v_gitDir_2265_, v_val_2270_);
v___x_2272_ = lean_unsigned_to_nat(0u);
v___x_2273_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
v___x_2274_ = l_Lake_Manifest_load(v___x_2271_);
if (lean_obj_tag(v___x_2274_) == 0)
{
lean_object* v_a_2275_; lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2282_; 
v_a_2275_ = lean_ctor_get(v___x_2274_, 0);
v_isSharedCheck_2282_ = !lean_is_exclusive(v___x_2274_);
if (v_isSharedCheck_2282_ == 0)
{
v___x_2277_ = v___x_2274_;
v_isShared_2278_ = v_isSharedCheck_2282_;
goto v_resetjp_2276_;
}
else
{
lean_inc(v_a_2275_);
lean_dec(v___x_2274_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2282_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
lean_object* v___x_2280_; 
if (v_isShared_2278_ == 0)
{
lean_ctor_set_tag(v___x_2277_, 1);
v___x_2280_ = v___x_2277_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v_a_2275_);
v___x_2280_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
v___y_2159_ = v___y_2267_;
v___y_2160_ = v___x_2272_;
v___y_2161_ = v___y_2269_;
v___y_2162_ = v___y_2268_;
v_a_2163_ = v___x_2280_;
v_a_2164_ = v___x_2273_;
goto v___jp_2158_;
}
}
}
else
{
lean_object* v_a_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2290_; 
v_a_2283_ = lean_ctor_get(v___x_2274_, 0);
v_isSharedCheck_2290_ = !lean_is_exclusive(v___x_2274_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2285_ = v___x_2274_;
v_isShared_2286_ = v_isSharedCheck_2290_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_a_2283_);
lean_dec(v___x_2274_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2290_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v___x_2288_; 
if (v_isShared_2286_ == 0)
{
lean_ctor_set_tag(v___x_2285_, 0);
v___x_2288_ = v___x_2285_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v_a_2283_);
v___x_2288_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
v___y_2159_ = v___y_2267_;
v___y_2160_ = v___x_2272_;
v___y_2161_ = v___y_2269_;
v___y_2162_ = v___y_2268_;
v_a_2163_ = v___x_2288_;
v_a_2164_ = v___x_2273_;
goto v___jp_2158_;
}
}
}
}
else
{
lean_object* v___x_2291_; 
lean_dec_ref(v___y_2268_);
lean_dec_ref(v_gitDir_2265_);
v___x_2291_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1, &l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1_once, _init_l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1);
v___y_2153_ = v___y_2267_;
v___y_2154_ = v___y_2269_;
v_a_2155_ = v___x_2291_;
goto v___jp_2152_;
}
}
v___jp_2292_:
{
lean_object* v___x_2295_; 
v___x_2295_ = l_Lake_Git_filterUrl_x3f(v_url_2259_);
if (lean_obj_tag(v___x_2295_) == 0)
{
lean_object* v___x_2296_; 
v___x_2296_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___y_2267_ = v___y_2294_;
v___y_2268_ = v___y_2293_;
v___y_2269_ = v___x_2296_;
goto v___jp_2266_;
}
else
{
lean_object* v_val_2297_; 
v_val_2297_ = lean_ctor_get(v___x_2295_, 0);
lean_inc(v_val_2297_);
lean_dec_ref(v___x_2295_);
v___y_2267_ = v___y_2294_;
v___y_2268_ = v___y_2293_;
v___y_2269_ = v_val_2297_;
goto v___jp_2266_;
}
}
v___jp_2298_:
{
if (lean_obj_tag(v_subDir_x3f_2261_) == 0)
{
v___y_2293_ = v___y_2299_;
v___y_2294_ = v_relGitDir_2264_;
goto v___jp_2292_;
}
else
{
lean_object* v_val_2300_; lean_object* v___x_2301_; 
v_val_2300_ = lean_ctor_get(v_subDir_x3f_2261_, 0);
lean_inc(v_val_2300_);
lean_dec_ref(v_subDir_x3f_2261_);
v___x_2301_ = l_Lake_joinRelative(v_relGitDir_2264_, v_val_2300_);
v___y_2293_ = v___y_2299_;
v___y_2294_ = v___x_2301_;
goto v___jp_2292_;
}
}
v___jp_2302_:
{
lean_object* v___x_2305_; 
lean_inc_ref(v_gitDir_2265_);
lean_inc_ref(v_a_2150_);
v___x_2305_ = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_2150_, v_sname_2263_, v_gitDir_2265_, v___y_2304_, v___y_2303_);
if (lean_obj_tag(v___x_2305_) == 0)
{
lean_dec_ref(v___x_2305_);
v___y_2299_ = v_a_2150_;
goto v___jp_2298_;
}
else
{
lean_object* v_a_2306_; lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2313_; 
lean_dec_ref(v_gitDir_2265_);
lean_dec_ref(v_relGitDir_2264_);
lean_dec(v_subDir_x3f_2261_);
lean_dec_ref(v_url_2259_);
lean_dec_ref(v_a_2150_);
lean_dec_ref(v_manifestEntry_2146_);
v_a_2306_ = lean_ctor_get(v___x_2305_, 0);
v_isSharedCheck_2313_ = !lean_is_exclusive(v___x_2305_);
if (v_isSharedCheck_2313_ == 0)
{
v___x_2308_ = v___x_2305_;
v_isShared_2309_ = v_isSharedCheck_2313_;
goto v_resetjp_2307_;
}
else
{
lean_inc(v_a_2306_);
lean_dec(v___x_2305_);
v___x_2308_ = lean_box(0);
v_isShared_2309_ = v_isSharedCheck_2313_;
goto v_resetjp_2307_;
}
v_resetjp_2307_:
{
lean_object* v___x_2311_; 
if (v_isShared_2309_ == 0)
{
v___x_2311_ = v___x_2308_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v_a_2306_);
v___x_2311_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
return v___x_2311_;
}
}
}
}
v___jp_2314_:
{
lean_object* v___x_2316_; lean_object* v___x_2317_; 
v___x_2316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2316_, 0, v_rev_2260_);
lean_inc_ref(v_gitDir_2265_);
lean_inc_ref(v_a_2150_);
v___x_2317_ = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(v_a_2150_, v_sname_2263_, v_gitDir_2265_, v___y_2315_, v___x_2316_);
if (lean_obj_tag(v___x_2317_) == 0)
{
lean_dec_ref(v___x_2317_);
v___y_2299_ = v_a_2150_;
goto v___jp_2298_;
}
else
{
lean_object* v_a_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2325_; 
lean_dec_ref(v_gitDir_2265_);
lean_dec_ref(v_relGitDir_2264_);
lean_dec(v_subDir_x3f_2261_);
lean_dec_ref(v_url_2259_);
lean_dec_ref(v_a_2150_);
lean_dec_ref(v_manifestEntry_2146_);
v_a_2318_ = lean_ctor_get(v___x_2317_, 0);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_2317_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2320_ = v___x_2317_;
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_a_2318_);
lean_dec(v___x_2317_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2323_; 
if (v_isShared_2321_ == 0)
{
v___x_2323_ = v___x_2320_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v_a_2318_);
v___x_2323_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
return v___x_2323_;
}
}
}
}
v___jp_2326_:
{
if (v_a_2327_ == 0)
{
lean_dec_ref(v_sname_2263_);
v___y_2299_ = v_a_2150_;
goto v___jp_2298_;
}
else
{
lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; uint8_t v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; 
v___x_2328_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0));
v___x_2329_ = lean_string_append(v_sname_2263_, v___x_2328_);
v___x_2330_ = lean_string_append(v___x_2329_, v_gitDir_2265_);
v___x_2331_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1));
v___x_2332_ = lean_string_append(v___x_2330_, v___x_2331_);
v___x_2333_ = 2;
v___x_2334_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2334_, 0, v___x_2332_);
lean_ctor_set_uint8(v___x_2334_, sizeof(void*)*1, v___x_2333_);
lean_inc_ref(v_a_2150_);
v___x_2335_ = lean_apply_2(v_a_2150_, v___x_2334_, lean_box(0));
v___y_2299_ = v_a_2150_;
goto v___jp_2298_;
}
}
v___jp_2336_:
{
lean_object* v___x_2340_; uint8_t v___x_2341_; 
v___x_2340_ = lean_array_get_size(v___y_2337_);
v___x_2341_ = lean_nat_dec_lt(v___y_2338_, v___x_2340_);
if (v___x_2341_ == 0)
{
lean_dec_ref(v___y_2337_);
v_a_2327_ = v_val_2339_;
goto v___jp_2326_;
}
else
{
lean_object* v___x_2342_; uint8_t v___x_2343_; 
v___x_2342_ = lean_box(0);
v___x_2343_ = lean_nat_dec_le(v___x_2340_, v___x_2340_);
if (v___x_2343_ == 0)
{
if (v___x_2341_ == 0)
{
lean_dec_ref(v___y_2337_);
v_a_2327_ = v_val_2339_;
goto v___jp_2326_;
}
else
{
size_t v___x_2344_; size_t v___x_2345_; lean_object* v___x_2346_; 
v___x_2344_ = ((size_t)0ULL);
v___x_2345_ = lean_usize_of_nat(v___x_2340_);
lean_inc_ref(v_a_2150_);
v___x_2346_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v___y_2337_, v___x_2344_, v___x_2345_, v___x_2342_, v_a_2150_);
lean_dec_ref(v___y_2337_);
if (lean_obj_tag(v___x_2346_) == 0)
{
lean_dec_ref(v___x_2346_);
v_a_2327_ = v_val_2339_;
goto v___jp_2326_;
}
else
{
lean_object* v_a_2347_; lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2354_; 
lean_dec_ref(v_gitDir_2265_);
lean_dec_ref(v_relGitDir_2264_);
lean_dec_ref(v_sname_2263_);
lean_dec(v_subDir_x3f_2261_);
lean_dec_ref(v_url_2259_);
lean_dec_ref(v_a_2150_);
lean_dec_ref(v_manifestEntry_2146_);
v_a_2347_ = lean_ctor_get(v___x_2346_, 0);
v_isSharedCheck_2354_ = !lean_is_exclusive(v___x_2346_);
if (v_isSharedCheck_2354_ == 0)
{
v___x_2349_ = v___x_2346_;
v_isShared_2350_ = v_isSharedCheck_2354_;
goto v_resetjp_2348_;
}
else
{
lean_inc(v_a_2347_);
lean_dec(v___x_2346_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2354_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
lean_object* v___x_2352_; 
if (v_isShared_2350_ == 0)
{
v___x_2352_ = v___x_2349_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v_a_2347_);
v___x_2352_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
return v___x_2352_;
}
}
}
}
}
else
{
size_t v___x_2355_; size_t v___x_2356_; lean_object* v___x_2357_; 
v___x_2355_ = ((size_t)0ULL);
v___x_2356_ = lean_usize_of_nat(v___x_2340_);
lean_inc_ref(v_a_2150_);
v___x_2357_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v___y_2337_, v___x_2355_, v___x_2356_, v___x_2342_, v_a_2150_);
lean_dec_ref(v___y_2337_);
if (lean_obj_tag(v___x_2357_) == 0)
{
lean_dec_ref(v___x_2357_);
v_a_2327_ = v_val_2339_;
goto v___jp_2326_;
}
else
{
lean_object* v_a_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2365_; 
lean_dec_ref(v_gitDir_2265_);
lean_dec_ref(v_relGitDir_2264_);
lean_dec_ref(v_sname_2263_);
lean_dec(v_subDir_x3f_2261_);
lean_dec_ref(v_url_2259_);
lean_dec_ref(v_a_2150_);
lean_dec_ref(v_manifestEntry_2146_);
v_a_2358_ = lean_ctor_get(v___x_2357_, 0);
v_isSharedCheck_2365_ = !lean_is_exclusive(v___x_2357_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2360_ = v___x_2357_;
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_a_2358_);
lean_dec(v___x_2357_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___x_2363_; 
if (v_isShared_2361_ == 0)
{
v___x_2363_ = v___x_2360_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_a_2358_);
v___x_2363_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
return v___x_2363_;
}
}
}
}
}
}
v___jp_2366_:
{
lean_object* v___x_2369_; lean_object* v___x_2370_; uint8_t v___x_2371_; 
v___x_2369_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
v___x_2370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2370_, 0, v_rev_2260_);
lean_inc_ref(v___x_2370_);
v___x_2371_ = l_Option_instDecidableEq___redArg(v___x_2369_, v_a_2368_, v___x_2370_);
if (v___x_2371_ == 0)
{
lean_object* v_pkgUrlMap_2372_; lean_object* v___x_2373_; 
v_pkgUrlMap_2372_ = lean_ctor_get(v_lakeEnv_2147_, 5);
v___x_2373_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgUrlMap_2372_, v_name_2257_);
if (lean_obj_tag(v___x_2373_) == 0)
{
lean_inc_ref(v_url_2259_);
v___y_2303_ = v___x_2370_;
v___y_2304_ = v_url_2259_;
goto v___jp_2302_;
}
else
{
lean_object* v_val_2374_; 
v_val_2374_ = lean_ctor_get(v___x_2373_, 0);
lean_inc(v_val_2374_);
lean_dec_ref(v___x_2373_);
v___y_2303_ = v___x_2370_;
v___y_2304_ = v_val_2374_;
goto v___jp_2302_;
}
}
else
{
uint8_t v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; 
lean_dec_ref(v___x_2370_);
lean_inc_ref(v_gitDir_2265_);
v___x_2375_ = l_Lake_GitRepo_hasNoDiff(v_gitDir_2265_);
v___x_2376_ = lean_unsigned_to_nat(0u);
v___x_2377_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
if (v___x_2375_ == 0)
{
v___y_2337_ = v___x_2377_;
v___y_2338_ = v___x_2376_;
v_val_2339_ = v___y_2367_;
goto v___jp_2336_;
}
else
{
v___y_2337_ = v___x_2377_;
v___y_2338_ = v___x_2376_;
v_val_2339_ = v___x_2262_;
goto v___jp_2336_;
}
}
}
v___jp_2379_:
{
if (v___x_2378_ == 0)
{
lean_object* v_pkgUrlMap_2380_; lean_object* v___x_2381_; 
v_pkgUrlMap_2380_ = lean_ctor_get(v_lakeEnv_2147_, 5);
v___x_2381_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgUrlMap_2380_, v_name_2257_);
if (lean_obj_tag(v___x_2381_) == 0)
{
lean_inc_ref(v_url_2259_);
v___y_2315_ = v_url_2259_;
goto v___jp_2314_;
}
else
{
lean_object* v_val_2382_; 
v_val_2382_ = lean_ctor_get(v___x_2381_, 0);
lean_inc(v_val_2382_);
lean_dec_ref(v___x_2381_);
v___y_2315_ = v_val_2382_;
goto v___jp_2314_;
}
}
else
{
lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; uint8_t v___x_2386_; 
v___x_2383_ = ((lean_object*)(l_Lake_PackageEntry_materialize___closed__0));
lean_inc_ref(v_gitDir_2265_);
v___x_2384_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_2383_, v_gitDir_2265_);
v___x_2385_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
v___x_2386_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_2386_ == 0)
{
v___y_2367_ = v___x_2378_;
v_a_2368_ = v___x_2384_;
goto v___jp_2366_;
}
else
{
lean_object* v___x_2387_; uint8_t v___x_2388_; 
v___x_2387_ = lean_box(0);
v___x_2388_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_2388_ == 0)
{
if (v___x_2386_ == 0)
{
v___y_2367_ = v___x_2378_;
v_a_2368_ = v___x_2384_;
goto v___jp_2366_;
}
else
{
size_t v___x_2389_; size_t v___x_2390_; lean_object* v___x_2391_; 
v___x_2389_ = ((size_t)0ULL);
v___x_2390_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
lean_inc_ref(v_a_2150_);
v___x_2391_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v___x_2385_, v___x_2389_, v___x_2390_, v___x_2387_, v_a_2150_);
if (lean_obj_tag(v___x_2391_) == 0)
{
lean_dec_ref(v___x_2391_);
v___y_2367_ = v___x_2378_;
v_a_2368_ = v___x_2384_;
goto v___jp_2366_;
}
else
{
lean_object* v_a_2392_; lean_object* v___x_2394_; uint8_t v_isShared_2395_; uint8_t v_isSharedCheck_2399_; 
lean_dec(v___x_2384_);
lean_dec_ref(v_gitDir_2265_);
lean_dec_ref(v_relGitDir_2264_);
lean_dec_ref(v_sname_2263_);
lean_dec(v_subDir_x3f_2261_);
lean_dec_ref(v_rev_2260_);
lean_dec_ref(v_url_2259_);
lean_dec_ref(v_a_2150_);
lean_dec_ref(v_manifestEntry_2146_);
v_a_2392_ = lean_ctor_get(v___x_2391_, 0);
v_isSharedCheck_2399_ = !lean_is_exclusive(v___x_2391_);
if (v_isSharedCheck_2399_ == 0)
{
v___x_2394_ = v___x_2391_;
v_isShared_2395_ = v_isSharedCheck_2399_;
goto v_resetjp_2393_;
}
else
{
lean_inc(v_a_2392_);
lean_dec(v___x_2391_);
v___x_2394_ = lean_box(0);
v_isShared_2395_ = v_isSharedCheck_2399_;
goto v_resetjp_2393_;
}
v_resetjp_2393_:
{
lean_object* v___x_2397_; 
if (v_isShared_2395_ == 0)
{
v___x_2397_ = v___x_2394_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v_a_2392_);
v___x_2397_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
return v___x_2397_;
}
}
}
}
}
else
{
size_t v___x_2400_; size_t v___x_2401_; lean_object* v___x_2402_; 
v___x_2400_ = ((size_t)0ULL);
v___x_2401_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
lean_inc_ref(v_a_2150_);
v___x_2402_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v___x_2385_, v___x_2400_, v___x_2401_, v___x_2387_, v_a_2150_);
if (lean_obj_tag(v___x_2402_) == 0)
{
lean_dec_ref(v___x_2402_);
v___y_2367_ = v___x_2378_;
v_a_2368_ = v___x_2384_;
goto v___jp_2366_;
}
else
{
lean_object* v_a_2403_; lean_object* v___x_2405_; uint8_t v_isShared_2406_; uint8_t v_isSharedCheck_2410_; 
lean_dec(v___x_2384_);
lean_dec_ref(v_gitDir_2265_);
lean_dec_ref(v_relGitDir_2264_);
lean_dec_ref(v_sname_2263_);
lean_dec(v_subDir_x3f_2261_);
lean_dec_ref(v_rev_2260_);
lean_dec_ref(v_url_2259_);
lean_dec_ref(v_a_2150_);
lean_dec_ref(v_manifestEntry_2146_);
v_a_2403_ = lean_ctor_get(v___x_2402_, 0);
v_isSharedCheck_2410_ = !lean_is_exclusive(v___x_2402_);
if (v_isSharedCheck_2410_ == 0)
{
v___x_2405_ = v___x_2402_;
v_isShared_2406_ = v_isSharedCheck_2410_;
goto v_resetjp_2404_;
}
else
{
lean_inc(v_a_2403_);
lean_dec(v___x_2402_);
v___x_2405_ = lean_box(0);
v_isShared_2406_ = v_isSharedCheck_2410_;
goto v_resetjp_2404_;
}
v_resetjp_2404_:
{
lean_object* v___x_2408_; 
if (v_isShared_2406_ == 0)
{
v___x_2408_ = v___x_2405_;
goto v_reusejp_2407_;
}
else
{
lean_object* v_reuseFailAlloc_2409_; 
v_reuseFailAlloc_2409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2409_, 0, v_a_2403_);
v___x_2408_ = v_reuseFailAlloc_2409_;
goto v_reusejp_2407_;
}
v_reusejp_2407_:
{
return v___x_2408_;
}
}
}
}
}
}
}
}
v___jp_2152_:
{
lean_object* v___x_2156_; lean_object* v___x_2157_; 
v___x_2156_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2156_, 0, v___y_2153_);
lean_ctor_set(v___x_2156_, 1, v___y_2154_);
lean_ctor_set(v___x_2156_, 2, v_a_2155_);
lean_ctor_set(v___x_2156_, 3, v_manifestEntry_2146_);
v___x_2157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2157_, 0, v___x_2156_);
return v___x_2157_;
}
v___jp_2158_:
{
lean_object* v___x_2165_; uint8_t v___x_2166_; 
v___x_2165_ = lean_array_get_size(v_a_2164_);
v___x_2166_ = lean_nat_dec_lt(v___y_2160_, v___x_2165_);
if (v___x_2166_ == 0)
{
lean_dec_ref(v_a_2164_);
lean_dec_ref(v___y_2162_);
v___y_2153_ = v___y_2159_;
v___y_2154_ = v___y_2161_;
v_a_2155_ = v_a_2163_;
goto v___jp_2152_;
}
else
{
lean_object* v___x_2167_; uint8_t v___x_2168_; 
v___x_2167_ = lean_box(0);
v___x_2168_ = lean_nat_dec_le(v___x_2165_, v___x_2165_);
if (v___x_2168_ == 0)
{
if (v___x_2166_ == 0)
{
lean_dec_ref(v_a_2164_);
lean_dec_ref(v___y_2162_);
v___y_2153_ = v___y_2159_;
v___y_2154_ = v___y_2161_;
v_a_2155_ = v_a_2163_;
goto v___jp_2152_;
}
else
{
size_t v___x_2169_; size_t v___x_2170_; lean_object* v___x_2171_; 
v___x_2169_ = ((size_t)0ULL);
v___x_2170_ = lean_usize_of_nat(v___x_2165_);
v___x_2171_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_2164_, v___x_2169_, v___x_2170_, v___x_2167_, v___y_2162_);
lean_dec_ref(v_a_2164_);
if (lean_obj_tag(v___x_2171_) == 0)
{
lean_dec_ref(v___x_2171_);
v___y_2153_ = v___y_2159_;
v___y_2154_ = v___y_2161_;
v_a_2155_ = v_a_2163_;
goto v___jp_2152_;
}
else
{
lean_object* v_a_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2179_; 
lean_dec_ref(v_a_2163_);
lean_dec_ref(v___y_2161_);
lean_dec_ref(v___y_2159_);
lean_dec_ref(v_manifestEntry_2146_);
v_a_2172_ = lean_ctor_get(v___x_2171_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2171_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2174_ = v___x_2171_;
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_a_2172_);
lean_dec(v___x_2171_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v___x_2177_; 
if (v_isShared_2175_ == 0)
{
v___x_2177_ = v___x_2174_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_a_2172_);
v___x_2177_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
return v___x_2177_;
}
}
}
}
}
else
{
size_t v___x_2180_; size_t v___x_2181_; lean_object* v___x_2182_; 
v___x_2180_ = ((size_t)0ULL);
v___x_2181_ = lean_usize_of_nat(v___x_2165_);
v___x_2182_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(v_a_2164_, v___x_2180_, v___x_2181_, v___x_2167_, v___y_2162_);
lean_dec_ref(v_a_2164_);
if (lean_obj_tag(v___x_2182_) == 0)
{
lean_dec_ref(v___x_2182_);
v___y_2153_ = v___y_2159_;
v___y_2154_ = v___y_2161_;
v_a_2155_ = v_a_2163_;
goto v___jp_2152_;
}
else
{
lean_object* v_a_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2190_; 
lean_dec_ref(v_a_2163_);
lean_dec_ref(v___y_2161_);
lean_dec_ref(v___y_2159_);
lean_dec_ref(v_manifestEntry_2146_);
v_a_2183_ = lean_ctor_get(v___x_2182_, 0);
v_isSharedCheck_2190_ = !lean_is_exclusive(v___x_2182_);
if (v_isSharedCheck_2190_ == 0)
{
v___x_2185_ = v___x_2182_;
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
else
{
lean_inc(v_a_2183_);
lean_dec(v___x_2182_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
lean_object* v___x_2188_; 
if (v_isShared_2186_ == 0)
{
v___x_2188_ = v___x_2185_;
goto v_reusejp_2187_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v_a_2183_);
v___x_2188_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2187_;
}
v_reusejp_2187_:
{
return v___x_2188_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize___boxed(lean_object* v_manifestEntry_2437_, lean_object* v_lakeEnv_2438_, lean_object* v_wsDir_2439_, lean_object* v_relPkgsDir_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_){
_start:
{
lean_object* v_res_2443_; 
v_res_2443_ = l_Lake_PackageEntry_materialize(v_manifestEntry_2437_, v_lakeEnv_2438_, v_wsDir_2439_, v_relPkgsDir_2440_, v_a_2441_);
lean_dec_ref(v_lakeEnv_2438_);
return v_res_2443_;
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

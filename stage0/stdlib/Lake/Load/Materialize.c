// Lean compiler output
// Module: Lake.Load.Materialize
// Imports: public import Lake.Config.Env public import Lake.Load.Manifest public import Lake.Config.Package import Lake.Util.Git import Lake.Util.IO import Lake.Reservoir
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
lean_object* l_Lake_GitRepo_clean(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lake_GitRepo_hasNoDiff(lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lake_GitRepo_findRemoteRevision(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_getHeadRevision(lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_getRemoteUrl_x3f(lean_object*, lean_object*);
lean_object* lean_io_realpath(lean_object*);
extern lean_object* l_Lake_defaultConfigFile;
extern lean_object* l_Lake_defaultManifestFile;
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
lean_object* l_Lake_Manifest_load(lean_object*);
lean_object* l_Lake_resolvePath(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_System_FilePath_isDir(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lake_Git_filterUrl_x3f(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t l_Lake_VerRange_test(lean_object*, lean_object*);
lean_object* l_Lake_StdVer_toString(lean_object*);
lean_object* l_String_quote(lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_RegistryPkg_gitSrc_x3f(lean_object*);
lean_object* l_Lake_Reservoir_fetchPkgVersions(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Reservoir_fetchPkg_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_instInhabitedPackageEntry_default;
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_instDecidableEqString___boxed(lean_object*, lean_object*);
uint8_t l_Option_instDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_resolveRevision_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0_value;
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = ": repository '"};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1_value;
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "' has local changes"};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2_value;
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = ": checking out revision '"};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3_value;
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4_value;
static lean_once_cell_t l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__5;
static lean_once_cell_t l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__6;
static lean_once_cell_t l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__7;
static lean_once_cell_t l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8;
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
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_prettyName(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_scope(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_scope___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relManifestFile_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relManifestFile_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relManifestFile(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relManifestFile___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_manifestFile(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relConfigFile(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relConfigFile___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_configFile(lean_object*);
LEAN_EXPORT uint8_t l_Lake_MaterializedDep_fixedToolchain(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_fixedToolchain___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0;
static lean_once_cell_t l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1;
static const lean_closure_object l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__2 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__2_value;
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = ": package directory not found: "};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__3 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lake_Dependency_materialize___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 93, .m_capacity = 93, .m_length = 92, .m_data = ": ill-formed dependency: dependency is missing a source and is missing a scope for Reservoir"};
static const lean_object* l_Lake_Dependency_materialize___closed__8 = (const lean_object*)&l_Lake_Dependency_materialize___closed__8_value;
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 11}, .m_objs = {((lean_object*)&l_Lake_instInhabitedMaterializedDep_default___closed__0_value),((lean_object*)&l_Lake_instInhabitedMaterializedDep_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__0 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__0_value;
static const lean_ctor_object l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__0_value)}};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1_value;
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
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__5(void){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_29_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0));
v___x_30_ = lean_array_get_size(v___x_29_);
return v___x_30_;
}
}
static uint8_t _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__6(void){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; uint8_t v___x_33_; 
v___x_31_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__5);
v___x_32_ = lean_unsigned_to_nat(0u);
v___x_33_ = lean_nat_dec_lt(v___x_32_, v___x_31_);
return v___x_33_;
}
}
static uint8_t _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__7(void){
_start:
{
lean_object* v___x_34_; uint8_t v___x_35_; 
v___x_34_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__5);
v___x_35_ = lean_nat_dec_le(v___x_34_, v___x_34_);
return v___x_35_;
}
}
static size_t _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8(void){
_start:
{
lean_object* v___x_36_; size_t v___x_37_; 
v___x_36_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__5);
v___x_37_ = lean_usize_of_nat(v___x_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg(lean_object* v_name_38_, lean_object* v_repo_39_, lean_object* v_rev_x3f_40_, lean_object* v_a_41_){
_start:
{
lean_object* v___y_94_; uint8_t v_a_99_; lean_object* v___y_112_; lean_object* v_a_113_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_168_ = l_Lake_Git_defaultRemote;
v___x_169_ = lean_unsigned_to_nat(0u);
v___x_170_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0));
lean_inc_ref(v_repo_39_);
v___x_171_ = l_Lake_GitRepo_findRemoteRevision(v_repo_39_, v_rev_x3f_40_, v___x_168_, v___x_170_);
if (lean_obj_tag(v___x_171_) == 0)
{
lean_object* v_a_172_; lean_object* v_a_173_; lean_object* v___x_201_; uint8_t v___x_202_; 
v_a_172_ = lean_ctor_get(v___x_171_, 0);
lean_inc(v_a_172_);
v_a_173_ = lean_ctor_get(v___x_171_, 1);
lean_inc(v_a_173_);
lean_dec_ref_known(v___x_171_, 2);
v___x_201_ = lean_array_get_size(v_a_173_);
v___x_202_ = lean_nat_dec_lt(v___x_169_, v___x_201_);
if (v___x_202_ == 0)
{
lean_dec(v_a_173_);
goto v___jp_174_;
}
else
{
lean_object* v___x_203_; uint8_t v___x_204_; 
v___x_203_ = lean_box(0);
v___x_204_ = lean_nat_dec_le(v___x_201_, v___x_201_);
if (v___x_204_ == 0)
{
if (v___x_202_ == 0)
{
lean_dec(v_a_173_);
goto v___jp_174_;
}
else
{
size_t v___x_205_; size_t v___x_206_; lean_object* v___x_207_; 
v___x_205_ = ((size_t)0ULL);
v___x_206_ = lean_usize_of_nat(v___x_201_);
v___x_207_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_173_, v___x_205_, v___x_206_, v___x_203_, v_a_41_);
lean_dec(v_a_173_);
if (lean_obj_tag(v___x_207_) == 0)
{
lean_dec_ref_known(v___x_207_, 1);
goto v___jp_174_;
}
else
{
lean_dec(v_a_172_);
lean_dec_ref(v_repo_39_);
lean_dec_ref(v_name_38_);
return v___x_207_;
}
}
}
else
{
size_t v___x_208_; size_t v___x_209_; lean_object* v___x_210_; 
v___x_208_ = ((size_t)0ULL);
v___x_209_ = lean_usize_of_nat(v___x_201_);
v___x_210_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_173_, v___x_208_, v___x_209_, v___x_203_, v_a_41_);
lean_dec(v_a_173_);
if (lean_obj_tag(v___x_210_) == 0)
{
lean_dec_ref_known(v___x_210_, 1);
goto v___jp_174_;
}
else
{
lean_dec(v_a_172_);
lean_dec_ref(v_repo_39_);
lean_dec_ref(v_name_38_);
return v___x_210_;
}
}
}
v___jp_174_:
{
lean_object* v___x_175_; 
lean_inc_ref(v_repo_39_);
v___x_175_ = l_Lake_GitRepo_getHeadRevision(v_repo_39_, v___x_170_);
if (lean_obj_tag(v___x_175_) == 0)
{
lean_object* v_a_176_; lean_object* v_a_177_; lean_object* v___x_178_; uint8_t v___x_179_; 
v_a_176_ = lean_ctor_get(v___x_175_, 0);
lean_inc(v_a_176_);
v_a_177_ = lean_ctor_get(v___x_175_, 1);
lean_inc(v_a_177_);
lean_dec_ref_known(v___x_175_, 2);
v___x_178_ = lean_array_get_size(v_a_177_);
v___x_179_ = lean_nat_dec_lt(v___x_169_, v___x_178_);
if (v___x_179_ == 0)
{
lean_dec(v_a_177_);
v___y_112_ = v_a_172_;
v_a_113_ = v_a_176_;
goto v___jp_111_;
}
else
{
lean_object* v___x_180_; uint8_t v___x_181_; 
v___x_180_ = lean_box(0);
v___x_181_ = lean_nat_dec_le(v___x_178_, v___x_178_);
if (v___x_181_ == 0)
{
if (v___x_179_ == 0)
{
lean_dec(v_a_177_);
v___y_112_ = v_a_172_;
v_a_113_ = v_a_176_;
goto v___jp_111_;
}
else
{
size_t v___x_182_; size_t v___x_183_; lean_object* v___x_184_; 
v___x_182_ = ((size_t)0ULL);
v___x_183_ = lean_usize_of_nat(v___x_178_);
v___x_184_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_177_, v___x_182_, v___x_183_, v___x_180_, v_a_41_);
lean_dec(v_a_177_);
if (lean_obj_tag(v___x_184_) == 0)
{
lean_dec_ref_known(v___x_184_, 1);
v___y_112_ = v_a_172_;
v_a_113_ = v_a_176_;
goto v___jp_111_;
}
else
{
lean_dec(v_a_176_);
lean_dec(v_a_172_);
lean_dec_ref(v_repo_39_);
lean_dec_ref(v_name_38_);
return v___x_184_;
}
}
}
else
{
size_t v___x_185_; size_t v___x_186_; lean_object* v___x_187_; 
v___x_185_ = ((size_t)0ULL);
v___x_186_ = lean_usize_of_nat(v___x_178_);
v___x_187_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_177_, v___x_185_, v___x_186_, v___x_180_, v_a_41_);
lean_dec(v_a_177_);
if (lean_obj_tag(v___x_187_) == 0)
{
lean_dec_ref_known(v___x_187_, 1);
v___y_112_ = v_a_172_;
v_a_113_ = v_a_176_;
goto v___jp_111_;
}
else
{
lean_dec(v_a_176_);
lean_dec(v_a_172_);
lean_dec_ref(v_repo_39_);
lean_dec_ref(v_name_38_);
return v___x_187_;
}
}
}
}
else
{
lean_object* v_a_188_; lean_object* v___x_189_; uint8_t v___x_190_; 
lean_dec(v_a_172_);
lean_dec_ref(v_repo_39_);
lean_dec_ref(v_name_38_);
v_a_188_ = lean_ctor_get(v___x_175_, 1);
lean_inc(v_a_188_);
lean_dec_ref_known(v___x_175_, 2);
v___x_189_ = lean_array_get_size(v_a_188_);
v___x_190_ = lean_nat_dec_lt(v___x_169_, v___x_189_);
if (v___x_190_ == 0)
{
lean_object* v___x_191_; lean_object* v___x_192_; 
lean_dec(v_a_188_);
v___x_191_ = lean_box(0);
v___x_192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_192_, 0, v___x_191_);
return v___x_192_;
}
else
{
lean_object* v___x_193_; uint8_t v___x_194_; 
v___x_193_ = lean_box(0);
v___x_194_ = lean_nat_dec_le(v___x_189_, v___x_189_);
if (v___x_194_ == 0)
{
if (v___x_190_ == 0)
{
lean_dec(v_a_188_);
goto v___jp_162_;
}
else
{
size_t v___x_195_; size_t v___x_196_; lean_object* v___x_197_; 
v___x_195_ = ((size_t)0ULL);
v___x_196_ = lean_usize_of_nat(v___x_189_);
v___x_197_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_188_, v___x_195_, v___x_196_, v___x_193_, v_a_41_);
lean_dec(v_a_188_);
if (lean_obj_tag(v___x_197_) == 0)
{
lean_dec_ref_known(v___x_197_, 1);
goto v___jp_162_;
}
else
{
return v___x_197_;
}
}
}
else
{
size_t v___x_198_; size_t v___x_199_; lean_object* v___x_200_; 
v___x_198_ = ((size_t)0ULL);
v___x_199_ = lean_usize_of_nat(v___x_189_);
v___x_200_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_188_, v___x_198_, v___x_199_, v___x_193_, v_a_41_);
lean_dec(v_a_188_);
if (lean_obj_tag(v___x_200_) == 0)
{
lean_dec_ref_known(v___x_200_, 1);
goto v___jp_162_;
}
else
{
return v___x_200_;
}
}
}
}
}
}
else
{
lean_object* v_a_211_; lean_object* v___x_212_; uint8_t v___x_213_; 
lean_dec_ref(v_repo_39_);
lean_dec_ref(v_name_38_);
v_a_211_ = lean_ctor_get(v___x_171_, 1);
lean_inc(v_a_211_);
lean_dec_ref_known(v___x_171_, 2);
v___x_212_ = lean_array_get_size(v_a_211_);
v___x_213_ = lean_nat_dec_lt(v___x_169_, v___x_212_);
if (v___x_213_ == 0)
{
lean_object* v___x_214_; lean_object* v___x_215_; 
lean_dec(v_a_211_);
v___x_214_ = lean_box(0);
v___x_215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_215_, 0, v___x_214_);
return v___x_215_;
}
else
{
lean_object* v___x_216_; uint8_t v___x_217_; 
v___x_216_ = lean_box(0);
v___x_217_ = lean_nat_dec_le(v___x_212_, v___x_212_);
if (v___x_217_ == 0)
{
if (v___x_213_ == 0)
{
lean_dec(v_a_211_);
goto v___jp_165_;
}
else
{
size_t v___x_218_; size_t v___x_219_; lean_object* v___x_220_; 
v___x_218_ = ((size_t)0ULL);
v___x_219_ = lean_usize_of_nat(v___x_212_);
v___x_220_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_211_, v___x_218_, v___x_219_, v___x_216_, v_a_41_);
lean_dec(v_a_211_);
if (lean_obj_tag(v___x_220_) == 0)
{
lean_dec_ref_known(v___x_220_, 1);
goto v___jp_165_;
}
else
{
return v___x_220_;
}
}
}
else
{
size_t v___x_221_; size_t v___x_222_; lean_object* v___x_223_; 
v___x_221_ = ((size_t)0ULL);
v___x_222_ = lean_usize_of_nat(v___x_212_);
v___x_223_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_211_, v___x_221_, v___x_222_, v___x_216_, v_a_41_);
lean_dec(v_a_211_);
if (lean_obj_tag(v___x_223_) == 0)
{
lean_dec_ref_known(v___x_223_, 1);
goto v___jp_165_;
}
else
{
return v___x_223_;
}
}
}
}
v___jp_43_:
{
lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_44_ = lean_box(0);
v___x_45_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_45_, 0, v___x_44_);
return v___x_45_;
}
v___jp_46_:
{
lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_47_ = lean_unsigned_to_nat(0u);
v___x_48_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0));
v___x_49_ = l_Lake_GitRepo_clean(v_repo_39_, v___x_48_);
if (lean_obj_tag(v___x_49_) == 0)
{
lean_object* v_a_50_; lean_object* v_a_51_; lean_object* v___x_52_; uint8_t v___x_53_; 
v_a_50_ = lean_ctor_get(v___x_49_, 0);
lean_inc(v_a_50_);
v_a_51_ = lean_ctor_get(v___x_49_, 1);
lean_inc(v_a_51_);
lean_dec_ref_known(v___x_49_, 2);
v___x_52_ = lean_array_get_size(v_a_51_);
v___x_53_ = lean_nat_dec_lt(v___x_47_, v___x_52_);
if (v___x_53_ == 0)
{
lean_object* v___x_54_; 
lean_dec(v_a_51_);
v___x_54_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_54_, 0, v_a_50_);
return v___x_54_;
}
else
{
lean_object* v___x_55_; uint8_t v___x_56_; 
v___x_55_ = lean_box(0);
v___x_56_ = lean_nat_dec_le(v___x_52_, v___x_52_);
if (v___x_56_ == 0)
{
if (v___x_53_ == 0)
{
lean_object* v___x_57_; 
lean_dec(v_a_51_);
v___x_57_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_57_, 0, v_a_50_);
return v___x_57_;
}
else
{
size_t v___x_58_; size_t v___x_59_; lean_object* v___x_60_; 
v___x_58_ = ((size_t)0ULL);
v___x_59_ = lean_usize_of_nat(v___x_52_);
v___x_60_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_51_, v___x_58_, v___x_59_, v___x_55_, v_a_41_);
lean_dec(v_a_51_);
if (lean_obj_tag(v___x_60_) == 0)
{
lean_object* v___x_62_; uint8_t v_isShared_63_; uint8_t v_isSharedCheck_67_; 
v_isSharedCheck_67_ = !lean_is_exclusive(v___x_60_);
if (v_isSharedCheck_67_ == 0)
{
lean_object* v_unused_68_; 
v_unused_68_ = lean_ctor_get(v___x_60_, 0);
lean_dec(v_unused_68_);
v___x_62_ = v___x_60_;
v_isShared_63_ = v_isSharedCheck_67_;
goto v_resetjp_61_;
}
else
{
lean_dec(v___x_60_);
v___x_62_ = lean_box(0);
v_isShared_63_ = v_isSharedCheck_67_;
goto v_resetjp_61_;
}
v_resetjp_61_:
{
lean_object* v___x_65_; 
if (v_isShared_63_ == 0)
{
lean_ctor_set(v___x_62_, 0, v_a_50_);
v___x_65_ = v___x_62_;
goto v_reusejp_64_;
}
else
{
lean_object* v_reuseFailAlloc_66_; 
v_reuseFailAlloc_66_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_66_, 0, v_a_50_);
v___x_65_ = v_reuseFailAlloc_66_;
goto v_reusejp_64_;
}
v_reusejp_64_:
{
return v___x_65_;
}
}
}
else
{
lean_dec(v_a_50_);
return v___x_60_;
}
}
}
else
{
size_t v___x_69_; size_t v___x_70_; lean_object* v___x_71_; 
v___x_69_ = ((size_t)0ULL);
v___x_70_ = lean_usize_of_nat(v___x_52_);
v___x_71_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_51_, v___x_69_, v___x_70_, v___x_55_, v_a_41_);
lean_dec(v_a_51_);
if (lean_obj_tag(v___x_71_) == 0)
{
lean_object* v___x_73_; uint8_t v_isShared_74_; uint8_t v_isSharedCheck_78_; 
v_isSharedCheck_78_ = !lean_is_exclusive(v___x_71_);
if (v_isSharedCheck_78_ == 0)
{
lean_object* v_unused_79_; 
v_unused_79_ = lean_ctor_get(v___x_71_, 0);
lean_dec(v_unused_79_);
v___x_73_ = v___x_71_;
v_isShared_74_ = v_isSharedCheck_78_;
goto v_resetjp_72_;
}
else
{
lean_dec(v___x_71_);
v___x_73_ = lean_box(0);
v_isShared_74_ = v_isSharedCheck_78_;
goto v_resetjp_72_;
}
v_resetjp_72_:
{
lean_object* v___x_76_; 
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 0, v_a_50_);
v___x_76_ = v___x_73_;
goto v_reusejp_75_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_77_, 0, v_a_50_);
v___x_76_ = v_reuseFailAlloc_77_;
goto v_reusejp_75_;
}
v_reusejp_75_:
{
return v___x_76_;
}
}
}
else
{
lean_dec(v_a_50_);
return v___x_71_;
}
}
}
}
else
{
lean_object* v_a_80_; lean_object* v___x_81_; uint8_t v___x_82_; 
v_a_80_ = lean_ctor_get(v___x_49_, 1);
lean_inc(v_a_80_);
lean_dec_ref_known(v___x_49_, 2);
v___x_81_ = lean_array_get_size(v_a_80_);
v___x_82_ = lean_nat_dec_lt(v___x_47_, v___x_81_);
if (v___x_82_ == 0)
{
lean_object* v___x_83_; lean_object* v___x_84_; 
lean_dec(v_a_80_);
v___x_83_ = lean_box(0);
v___x_84_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_84_, 0, v___x_83_);
return v___x_84_;
}
else
{
lean_object* v___x_85_; uint8_t v___x_86_; 
v___x_85_ = lean_box(0);
v___x_86_ = lean_nat_dec_le(v___x_81_, v___x_81_);
if (v___x_86_ == 0)
{
if (v___x_82_ == 0)
{
lean_dec(v_a_80_);
goto v___jp_43_;
}
else
{
size_t v___x_87_; size_t v___x_88_; lean_object* v___x_89_; 
v___x_87_ = ((size_t)0ULL);
v___x_88_ = lean_usize_of_nat(v___x_81_);
v___x_89_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_80_, v___x_87_, v___x_88_, v___x_85_, v_a_41_);
lean_dec(v_a_80_);
if (lean_obj_tag(v___x_89_) == 0)
{
lean_dec_ref_known(v___x_89_, 1);
goto v___jp_43_;
}
else
{
return v___x_89_;
}
}
}
else
{
size_t v___x_90_; size_t v___x_91_; lean_object* v___x_92_; 
v___x_90_ = ((size_t)0ULL);
v___x_91_ = lean_usize_of_nat(v___x_81_);
v___x_92_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_80_, v___x_90_, v___x_91_, v___x_85_, v_a_41_);
lean_dec(v_a_80_);
if (lean_obj_tag(v___x_92_) == 0)
{
lean_dec_ref_known(v___x_92_, 1);
goto v___jp_43_;
}
else
{
return v___x_92_;
}
}
}
}
}
v___jp_93_:
{
if (lean_obj_tag(v___y_94_) == 0)
{
lean_dec_ref_known(v___y_94_, 1);
goto v___jp_46_;
}
else
{
lean_dec_ref(v_repo_39_);
return v___y_94_;
}
}
v___jp_95_:
{
lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_96_ = lean_box(0);
v___x_97_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
return v___x_97_;
}
v___jp_98_:
{
if (v_a_99_ == 0)
{
lean_object* v___x_100_; lean_object* v___x_101_; 
lean_dec_ref(v_repo_39_);
lean_dec_ref(v_name_38_);
v___x_100_ = lean_box(0);
v___x_101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
return v___x_101_;
}
else
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; uint8_t v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_102_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1));
v___x_103_ = lean_string_append(v_name_38_, v___x_102_);
v___x_104_ = lean_string_append(v___x_103_, v_repo_39_);
lean_dec_ref(v_repo_39_);
v___x_105_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_106_ = lean_string_append(v___x_104_, v___x_105_);
v___x_107_ = 2;
v___x_108_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_108_, 0, v___x_106_);
lean_ctor_set_uint8(v___x_108_, sizeof(void*)*1, v___x_107_);
lean_inc_ref(v_a_41_);
v___x_109_ = lean_apply_2(v_a_41_, v___x_108_, lean_box(0));
v___x_110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_110_, 0, v___x_109_);
return v___x_110_;
}
}
v___jp_111_:
{
uint8_t v___x_114_; 
v___x_114_ = lean_string_dec_eq(v_a_113_, v___y_112_);
lean_dec_ref(v_a_113_);
if (v___x_114_ == 0)
{
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; uint8_t v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_115_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3));
v___x_116_ = lean_string_append(v_name_38_, v___x_115_);
v___x_117_ = lean_string_append(v___x_116_, v___y_112_);
v___x_118_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
v___x_119_ = lean_string_append(v___x_117_, v___x_118_);
v___x_120_ = 1;
v___x_121_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_121_, 0, v___x_119_);
lean_ctor_set_uint8(v___x_121_, sizeof(void*)*1, v___x_120_);
lean_inc_ref(v_a_41_);
v___x_122_ = lean_apply_2(v_a_41_, v___x_121_, lean_box(0));
v___x_123_ = lean_unsigned_to_nat(0u);
v___x_124_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0));
lean_inc_ref(v_repo_39_);
v___x_125_ = l_Lake_GitRepo_checkoutDetach(v___y_112_, v_repo_39_, v___x_124_);
if (lean_obj_tag(v___x_125_) == 0)
{
lean_object* v_a_126_; lean_object* v___x_127_; uint8_t v___x_128_; 
v_a_126_ = lean_ctor_get(v___x_125_, 1);
lean_inc(v_a_126_);
lean_dec_ref_known(v___x_125_, 2);
v___x_127_ = lean_array_get_size(v_a_126_);
v___x_128_ = lean_nat_dec_lt(v___x_123_, v___x_127_);
if (v___x_128_ == 0)
{
lean_dec(v_a_126_);
goto v___jp_46_;
}
else
{
lean_object* v___x_129_; uint8_t v___x_130_; 
v___x_129_ = lean_box(0);
v___x_130_ = lean_nat_dec_le(v___x_127_, v___x_127_);
if (v___x_130_ == 0)
{
if (v___x_128_ == 0)
{
lean_dec(v_a_126_);
goto v___jp_46_;
}
else
{
size_t v___x_131_; size_t v___x_132_; lean_object* v___x_133_; 
v___x_131_ = ((size_t)0ULL);
v___x_132_ = lean_usize_of_nat(v___x_127_);
v___x_133_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_126_, v___x_131_, v___x_132_, v___x_129_, v_a_41_);
lean_dec(v_a_126_);
if (lean_obj_tag(v___x_133_) == 0)
{
lean_dec_ref_known(v___x_133_, 1);
goto v___jp_46_;
}
else
{
v___y_94_ = v___x_133_;
goto v___jp_93_;
}
}
}
else
{
size_t v___x_134_; size_t v___x_135_; lean_object* v___x_136_; 
v___x_134_ = ((size_t)0ULL);
v___x_135_ = lean_usize_of_nat(v___x_127_);
v___x_136_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_126_, v___x_134_, v___x_135_, v___x_129_, v_a_41_);
lean_dec(v_a_126_);
if (lean_obj_tag(v___x_136_) == 0)
{
lean_dec_ref_known(v___x_136_, 1);
goto v___jp_46_;
}
else
{
v___y_94_ = v___x_136_;
goto v___jp_93_;
}
}
}
}
else
{
lean_object* v_a_137_; lean_object* v___x_138_; uint8_t v___x_139_; 
v_a_137_ = lean_ctor_get(v___x_125_, 1);
lean_inc(v_a_137_);
lean_dec_ref_known(v___x_125_, 2);
v___x_138_ = lean_array_get_size(v_a_137_);
v___x_139_ = lean_nat_dec_lt(v___x_123_, v___x_138_);
if (v___x_139_ == 0)
{
lean_object* v___x_140_; lean_object* v___x_141_; 
lean_dec(v_a_137_);
lean_dec_ref(v_repo_39_);
v___x_140_ = lean_box(0);
v___x_141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_141_, 0, v___x_140_);
return v___x_141_;
}
else
{
lean_object* v___x_142_; uint8_t v___x_143_; 
v___x_142_ = lean_box(0);
v___x_143_ = lean_nat_dec_le(v___x_138_, v___x_138_);
if (v___x_143_ == 0)
{
if (v___x_139_ == 0)
{
lean_dec(v_a_137_);
lean_dec_ref(v_repo_39_);
goto v___jp_95_;
}
else
{
size_t v___x_144_; size_t v___x_145_; lean_object* v___x_146_; 
v___x_144_ = ((size_t)0ULL);
v___x_145_ = lean_usize_of_nat(v___x_138_);
v___x_146_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_137_, v___x_144_, v___x_145_, v___x_142_, v_a_41_);
lean_dec(v_a_137_);
if (lean_obj_tag(v___x_146_) == 0)
{
lean_dec_ref_known(v___x_146_, 1);
lean_dec_ref(v_repo_39_);
goto v___jp_95_;
}
else
{
v___y_94_ = v___x_146_;
goto v___jp_93_;
}
}
}
else
{
size_t v___x_147_; size_t v___x_148_; lean_object* v___x_149_; 
v___x_147_ = ((size_t)0ULL);
v___x_148_ = lean_usize_of_nat(v___x_138_);
v___x_149_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_137_, v___x_147_, v___x_148_, v___x_142_, v_a_41_);
lean_dec(v_a_137_);
if (lean_obj_tag(v___x_149_) == 0)
{
lean_dec_ref_known(v___x_149_, 1);
lean_dec_ref(v_repo_39_);
goto v___jp_95_;
}
else
{
v___y_94_ = v___x_149_;
goto v___jp_93_;
}
}
}
}
}
else
{
uint8_t v___x_150_; lean_object* v___x_151_; uint8_t v___x_152_; uint8_t v___x_153_; 
lean_dec_ref(v___y_112_);
lean_inc_ref(v_repo_39_);
v___x_150_ = l_Lake_GitRepo_hasNoDiff(v_repo_39_);
v___x_151_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0));
v___x_152_ = lean_bool_not(v___x_150_);
v___x_153_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__6);
if (v___x_153_ == 0)
{
v_a_99_ = v___x_152_;
goto v___jp_98_;
}
else
{
lean_object* v___x_154_; uint8_t v___x_155_; 
v___x_154_ = lean_box(0);
v___x_155_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__7);
if (v___x_155_ == 0)
{
if (v___x_153_ == 0)
{
v_a_99_ = v___x_152_;
goto v___jp_98_;
}
else
{
size_t v___x_156_; size_t v___x_157_; lean_object* v___x_158_; 
v___x_156_ = ((size_t)0ULL);
v___x_157_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8);
v___x_158_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_151_, v___x_156_, v___x_157_, v___x_154_, v_a_41_);
if (lean_obj_tag(v___x_158_) == 0)
{
lean_dec_ref_known(v___x_158_, 1);
v_a_99_ = v___x_152_;
goto v___jp_98_;
}
else
{
lean_dec_ref(v_repo_39_);
lean_dec_ref(v_name_38_);
return v___x_158_;
}
}
}
else
{
size_t v___x_159_; size_t v___x_160_; lean_object* v___x_161_; 
v___x_159_ = ((size_t)0ULL);
v___x_160_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8);
v___x_161_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_151_, v___x_159_, v___x_160_, v___x_154_, v_a_41_);
if (lean_obj_tag(v___x_161_) == 0)
{
lean_dec_ref_known(v___x_161_, 1);
v_a_99_ = v___x_152_;
goto v___jp_98_;
}
else
{
lean_dec_ref(v_repo_39_);
lean_dec_ref(v_name_38_);
return v___x_161_;
}
}
}
}
}
v___jp_162_:
{
lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_163_ = lean_box(0);
v___x_164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
return v___x_164_;
}
v___jp_165_:
{
lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_166_ = lean_box(0);
v___x_167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_167_, 0, v___x_166_);
return v___x_167_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___boxed(lean_object* v_name_224_, lean_object* v_repo_225_, lean_object* v_rev_x3f_226_, lean_object* v_a_227_, lean_object* v_a_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg(v_name_224_, v_repo_225_, v_rev_x3f_226_, v_a_227_);
lean_dec_ref(v_a_227_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg(lean_object* v_name_231_, lean_object* v_repo_232_, lean_object* v_url_233_, lean_object* v_rev_x3f_234_, lean_object* v_a_235_){
_start:
{
lean_object* v_a_241_; lean_object* v___y_339_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; uint8_t v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_343_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___closed__0));
lean_inc_ref(v_name_231_);
v___x_344_ = lean_string_append(v_name_231_, v___x_343_);
v___x_345_ = lean_string_append(v___x_344_, v_url_233_);
v___x_346_ = 1;
v___x_347_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_347_, 0, v___x_345_);
lean_ctor_set_uint8(v___x_347_, sizeof(void*)*1, v___x_346_);
lean_inc_ref(v_a_235_);
v___x_348_ = lean_apply_2(v_a_235_, v___x_347_, lean_box(0));
v___x_349_ = lean_unsigned_to_nat(0u);
v___x_350_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0));
lean_inc_ref(v_repo_232_);
v___x_351_ = l_Lake_GitRepo_clone(v_url_233_, v_repo_232_, v___x_350_);
if (lean_obj_tag(v___x_351_) == 0)
{
lean_object* v_a_352_; lean_object* v___x_353_; uint8_t v___x_354_; 
v_a_352_ = lean_ctor_get(v___x_351_, 1);
lean_inc(v_a_352_);
lean_dec_ref_known(v___x_351_, 2);
v___x_353_ = lean_array_get_size(v_a_352_);
v___x_354_ = lean_nat_dec_lt(v___x_349_, v___x_353_);
if (v___x_354_ == 0)
{
lean_dec(v_a_352_);
goto v___jp_299_;
}
else
{
lean_object* v___x_355_; uint8_t v___x_356_; 
v___x_355_ = lean_box(0);
v___x_356_ = lean_nat_dec_le(v___x_353_, v___x_353_);
if (v___x_356_ == 0)
{
if (v___x_354_ == 0)
{
lean_dec(v_a_352_);
goto v___jp_299_;
}
else
{
size_t v___x_357_; size_t v___x_358_; lean_object* v___x_359_; 
v___x_357_ = ((size_t)0ULL);
v___x_358_ = lean_usize_of_nat(v___x_353_);
v___x_359_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_352_, v___x_357_, v___x_358_, v___x_355_, v_a_235_);
lean_dec(v_a_352_);
if (lean_obj_tag(v___x_359_) == 0)
{
lean_dec_ref_known(v___x_359_, 1);
goto v___jp_299_;
}
else
{
v___y_339_ = v___x_359_;
goto v___jp_338_;
}
}
}
else
{
size_t v___x_360_; size_t v___x_361_; lean_object* v___x_362_; 
v___x_360_ = ((size_t)0ULL);
v___x_361_ = lean_usize_of_nat(v___x_353_);
v___x_362_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_352_, v___x_360_, v___x_361_, v___x_355_, v_a_235_);
lean_dec(v_a_352_);
if (lean_obj_tag(v___x_362_) == 0)
{
lean_dec_ref_known(v___x_362_, 1);
goto v___jp_299_;
}
else
{
v___y_339_ = v___x_362_;
goto v___jp_338_;
}
}
}
}
else
{
lean_object* v_a_363_; lean_object* v___x_364_; uint8_t v___x_365_; 
v_a_363_ = lean_ctor_get(v___x_351_, 1);
lean_inc(v_a_363_);
lean_dec_ref_known(v___x_351_, 2);
v___x_364_ = lean_array_get_size(v_a_363_);
v___x_365_ = lean_nat_dec_lt(v___x_349_, v___x_364_);
if (v___x_365_ == 0)
{
lean_object* v___x_366_; lean_object* v___x_367_; 
lean_dec(v_a_363_);
lean_dec(v_rev_x3f_234_);
lean_dec_ref(v_repo_232_);
lean_dec_ref(v_name_231_);
v___x_366_ = lean_box(0);
v___x_367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_367_, 0, v___x_366_);
return v___x_367_;
}
else
{
lean_object* v___x_368_; uint8_t v___x_369_; 
v___x_368_ = lean_box(0);
v___x_369_ = lean_nat_dec_le(v___x_364_, v___x_364_);
if (v___x_369_ == 0)
{
if (v___x_365_ == 0)
{
lean_dec(v_a_363_);
lean_dec(v_rev_x3f_234_);
lean_dec_ref(v_repo_232_);
lean_dec_ref(v_name_231_);
goto v___jp_340_;
}
else
{
size_t v___x_370_; size_t v___x_371_; lean_object* v___x_372_; 
v___x_370_ = ((size_t)0ULL);
v___x_371_ = lean_usize_of_nat(v___x_364_);
v___x_372_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_363_, v___x_370_, v___x_371_, v___x_368_, v_a_235_);
lean_dec(v_a_363_);
if (lean_obj_tag(v___x_372_) == 0)
{
lean_dec_ref_known(v___x_372_, 1);
lean_dec(v_rev_x3f_234_);
lean_dec_ref(v_repo_232_);
lean_dec_ref(v_name_231_);
goto v___jp_340_;
}
else
{
v___y_339_ = v___x_372_;
goto v___jp_338_;
}
}
}
else
{
size_t v___x_373_; size_t v___x_374_; lean_object* v___x_375_; 
v___x_373_ = ((size_t)0ULL);
v___x_374_ = lean_usize_of_nat(v___x_364_);
v___x_375_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_363_, v___x_373_, v___x_374_, v___x_368_, v_a_235_);
lean_dec(v_a_363_);
if (lean_obj_tag(v___x_375_) == 0)
{
lean_dec_ref_known(v___x_375_, 1);
lean_dec(v_rev_x3f_234_);
lean_dec_ref(v_repo_232_);
lean_dec_ref(v_name_231_);
goto v___jp_340_;
}
else
{
v___y_339_ = v___x_375_;
goto v___jp_338_;
}
}
}
}
v___jp_237_:
{
lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_238_ = lean_box(0);
v___x_239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
return v___x_239_;
}
v___jp_240_:
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; uint8_t v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_242_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3));
v___x_243_ = lean_string_append(v_name_231_, v___x_242_);
v___x_244_ = lean_string_append(v___x_243_, v_a_241_);
v___x_245_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
v___x_246_ = lean_string_append(v___x_244_, v___x_245_);
v___x_247_ = 1;
v___x_248_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_248_, 0, v___x_246_);
lean_ctor_set_uint8(v___x_248_, sizeof(void*)*1, v___x_247_);
lean_inc_ref(v_a_235_);
v___x_249_ = lean_apply_2(v_a_235_, v___x_248_, lean_box(0));
v___x_250_ = lean_unsigned_to_nat(0u);
v___x_251_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0));
v___x_252_ = l_Lake_GitRepo_checkoutDetach(v_a_241_, v_repo_232_, v___x_251_);
if (lean_obj_tag(v___x_252_) == 0)
{
lean_object* v_a_253_; lean_object* v_a_254_; lean_object* v___x_255_; uint8_t v___x_256_; 
v_a_253_ = lean_ctor_get(v___x_252_, 0);
lean_inc(v_a_253_);
v_a_254_ = lean_ctor_get(v___x_252_, 1);
lean_inc(v_a_254_);
lean_dec_ref_known(v___x_252_, 2);
v___x_255_ = lean_array_get_size(v_a_254_);
v___x_256_ = lean_nat_dec_lt(v___x_250_, v___x_255_);
if (v___x_256_ == 0)
{
lean_object* v___x_257_; 
lean_dec(v_a_254_);
v___x_257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_257_, 0, v_a_253_);
return v___x_257_;
}
else
{
lean_object* v___x_258_; uint8_t v___x_259_; 
v___x_258_ = lean_box(0);
v___x_259_ = lean_nat_dec_le(v___x_255_, v___x_255_);
if (v___x_259_ == 0)
{
if (v___x_256_ == 0)
{
lean_object* v___x_260_; 
lean_dec(v_a_254_);
v___x_260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_260_, 0, v_a_253_);
return v___x_260_;
}
else
{
size_t v___x_261_; size_t v___x_262_; lean_object* v___x_263_; 
v___x_261_ = ((size_t)0ULL);
v___x_262_ = lean_usize_of_nat(v___x_255_);
v___x_263_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_254_, v___x_261_, v___x_262_, v___x_258_, v_a_235_);
lean_dec(v_a_254_);
if (lean_obj_tag(v___x_263_) == 0)
{
lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_270_; 
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_263_);
if (v_isSharedCheck_270_ == 0)
{
lean_object* v_unused_271_; 
v_unused_271_ = lean_ctor_get(v___x_263_, 0);
lean_dec(v_unused_271_);
v___x_265_ = v___x_263_;
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
else
{
lean_dec(v___x_263_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_268_; 
if (v_isShared_266_ == 0)
{
lean_ctor_set(v___x_265_, 0, v_a_253_);
v___x_268_ = v___x_265_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_a_253_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
}
else
{
lean_dec(v_a_253_);
return v___x_263_;
}
}
}
else
{
size_t v___x_272_; size_t v___x_273_; lean_object* v___x_274_; 
v___x_272_ = ((size_t)0ULL);
v___x_273_ = lean_usize_of_nat(v___x_255_);
v___x_274_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_254_, v___x_272_, v___x_273_, v___x_258_, v_a_235_);
lean_dec(v_a_254_);
if (lean_obj_tag(v___x_274_) == 0)
{
lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_281_; 
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_274_);
if (v_isSharedCheck_281_ == 0)
{
lean_object* v_unused_282_; 
v_unused_282_ = lean_ctor_get(v___x_274_, 0);
lean_dec(v_unused_282_);
v___x_276_ = v___x_274_;
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
else
{
lean_dec(v___x_274_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_279_; 
if (v_isShared_277_ == 0)
{
lean_ctor_set(v___x_276_, 0, v_a_253_);
v___x_279_ = v___x_276_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v_a_253_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
}
else
{
lean_dec(v_a_253_);
return v___x_274_;
}
}
}
}
else
{
lean_object* v_a_283_; lean_object* v___x_284_; uint8_t v___x_285_; 
v_a_283_ = lean_ctor_get(v___x_252_, 1);
lean_inc(v_a_283_);
lean_dec_ref_known(v___x_252_, 2);
v___x_284_ = lean_array_get_size(v_a_283_);
v___x_285_ = lean_nat_dec_lt(v___x_250_, v___x_284_);
if (v___x_285_ == 0)
{
lean_object* v___x_286_; lean_object* v___x_287_; 
lean_dec(v_a_283_);
v___x_286_ = lean_box(0);
v___x_287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_287_, 0, v___x_286_);
return v___x_287_;
}
else
{
lean_object* v___x_288_; uint8_t v___x_289_; 
v___x_288_ = lean_box(0);
v___x_289_ = lean_nat_dec_le(v___x_284_, v___x_284_);
if (v___x_289_ == 0)
{
if (v___x_285_ == 0)
{
lean_dec(v_a_283_);
goto v___jp_237_;
}
else
{
size_t v___x_290_; size_t v___x_291_; lean_object* v___x_292_; 
v___x_290_ = ((size_t)0ULL);
v___x_291_ = lean_usize_of_nat(v___x_284_);
v___x_292_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_283_, v___x_290_, v___x_291_, v___x_288_, v_a_235_);
lean_dec(v_a_283_);
if (lean_obj_tag(v___x_292_) == 0)
{
lean_dec_ref_known(v___x_292_, 1);
goto v___jp_237_;
}
else
{
return v___x_292_;
}
}
}
else
{
size_t v___x_293_; size_t v___x_294_; lean_object* v___x_295_; 
v___x_293_ = ((size_t)0ULL);
v___x_294_ = lean_usize_of_nat(v___x_284_);
v___x_295_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_283_, v___x_293_, v___x_294_, v___x_288_, v_a_235_);
lean_dec(v_a_283_);
if (lean_obj_tag(v___x_295_) == 0)
{
lean_dec_ref_known(v___x_295_, 1);
goto v___jp_237_;
}
else
{
return v___x_295_;
}
}
}
}
}
v___jp_296_:
{
lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_297_ = lean_box(0);
v___x_298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
return v___x_298_;
}
v___jp_299_:
{
if (lean_obj_tag(v_rev_x3f_234_) == 1)
{
lean_object* v_val_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_335_; 
v_val_300_ = lean_ctor_get(v_rev_x3f_234_, 0);
v_isSharedCheck_335_ = !lean_is_exclusive(v_rev_x3f_234_);
if (v_isSharedCheck_335_ == 0)
{
v___x_302_ = v_rev_x3f_234_;
v_isShared_303_ = v_isSharedCheck_335_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_val_300_);
lean_dec(v_rev_x3f_234_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_335_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_304_ = l_Lake_Git_defaultRemote;
v___x_305_ = lean_unsigned_to_nat(0u);
v___x_306_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0));
lean_inc_ref(v_repo_232_);
v___x_307_ = l_Lake_GitRepo_resolveRemoteRevision(v_val_300_, v___x_304_, v_repo_232_, v___x_306_);
if (lean_obj_tag(v___x_307_) == 0)
{
lean_object* v_a_308_; lean_object* v_a_309_; lean_object* v___x_310_; uint8_t v___x_311_; 
lean_del_object(v___x_302_);
v_a_308_ = lean_ctor_get(v___x_307_, 0);
lean_inc(v_a_308_);
v_a_309_ = lean_ctor_get(v___x_307_, 1);
lean_inc(v_a_309_);
lean_dec_ref_known(v___x_307_, 2);
v___x_310_ = lean_array_get_size(v_a_309_);
v___x_311_ = lean_nat_dec_lt(v___x_305_, v___x_310_);
if (v___x_311_ == 0)
{
lean_dec(v_a_309_);
v_a_241_ = v_a_308_;
goto v___jp_240_;
}
else
{
lean_object* v___x_312_; uint8_t v___x_313_; 
v___x_312_ = lean_box(0);
v___x_313_ = lean_nat_dec_le(v___x_310_, v___x_310_);
if (v___x_313_ == 0)
{
if (v___x_311_ == 0)
{
lean_dec(v_a_309_);
v_a_241_ = v_a_308_;
goto v___jp_240_;
}
else
{
size_t v___x_314_; size_t v___x_315_; lean_object* v___x_316_; 
v___x_314_ = ((size_t)0ULL);
v___x_315_ = lean_usize_of_nat(v___x_310_);
v___x_316_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_309_, v___x_314_, v___x_315_, v___x_312_, v_a_235_);
lean_dec(v_a_309_);
if (lean_obj_tag(v___x_316_) == 0)
{
lean_dec_ref_known(v___x_316_, 1);
v_a_241_ = v_a_308_;
goto v___jp_240_;
}
else
{
lean_dec(v_a_308_);
lean_dec_ref(v_repo_232_);
lean_dec_ref(v_name_231_);
return v___x_316_;
}
}
}
else
{
size_t v___x_317_; size_t v___x_318_; lean_object* v___x_319_; 
v___x_317_ = ((size_t)0ULL);
v___x_318_ = lean_usize_of_nat(v___x_310_);
v___x_319_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_309_, v___x_317_, v___x_318_, v___x_312_, v_a_235_);
lean_dec(v_a_309_);
if (lean_obj_tag(v___x_319_) == 0)
{
lean_dec_ref_known(v___x_319_, 1);
v_a_241_ = v_a_308_;
goto v___jp_240_;
}
else
{
lean_dec(v_a_308_);
lean_dec_ref(v_repo_232_);
lean_dec_ref(v_name_231_);
return v___x_319_;
}
}
}
}
else
{
lean_object* v_a_320_; lean_object* v___x_321_; uint8_t v___x_322_; 
lean_dec_ref(v_repo_232_);
lean_dec_ref(v_name_231_);
v_a_320_ = lean_ctor_get(v___x_307_, 1);
lean_inc(v_a_320_);
lean_dec_ref_known(v___x_307_, 2);
v___x_321_ = lean_array_get_size(v_a_320_);
v___x_322_ = lean_nat_dec_lt(v___x_305_, v___x_321_);
if (v___x_322_ == 0)
{
lean_object* v___x_323_; lean_object* v___x_325_; 
lean_dec(v_a_320_);
v___x_323_ = lean_box(0);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 0, v___x_323_);
v___x_325_ = v___x_302_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v___x_323_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
else
{
lean_object* v___x_327_; uint8_t v___x_328_; 
lean_del_object(v___x_302_);
v___x_327_ = lean_box(0);
v___x_328_ = lean_nat_dec_le(v___x_321_, v___x_321_);
if (v___x_328_ == 0)
{
if (v___x_322_ == 0)
{
lean_dec(v_a_320_);
goto v___jp_296_;
}
else
{
size_t v___x_329_; size_t v___x_330_; lean_object* v___x_331_; 
v___x_329_ = ((size_t)0ULL);
v___x_330_ = lean_usize_of_nat(v___x_321_);
v___x_331_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_320_, v___x_329_, v___x_330_, v___x_327_, v_a_235_);
lean_dec(v_a_320_);
if (lean_obj_tag(v___x_331_) == 0)
{
lean_dec_ref_known(v___x_331_, 1);
goto v___jp_296_;
}
else
{
return v___x_331_;
}
}
}
else
{
size_t v___x_332_; size_t v___x_333_; lean_object* v___x_334_; 
v___x_332_ = ((size_t)0ULL);
v___x_333_ = lean_usize_of_nat(v___x_321_);
v___x_334_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_320_, v___x_332_, v___x_333_, v___x_327_, v_a_235_);
lean_dec(v_a_320_);
if (lean_obj_tag(v___x_334_) == 0)
{
lean_dec_ref_known(v___x_334_, 1);
goto v___jp_296_;
}
else
{
return v___x_334_;
}
}
}
}
}
}
else
{
lean_object* v___x_336_; lean_object* v___x_337_; 
lean_dec(v_rev_x3f_234_);
lean_dec_ref(v_repo_232_);
lean_dec_ref(v_name_231_);
v___x_336_ = lean_box(0);
v___x_337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
return v___x_337_;
}
}
v___jp_338_:
{
if (lean_obj_tag(v___y_339_) == 0)
{
lean_dec_ref_known(v___y_339_, 1);
goto v___jp_299_;
}
else
{
lean_dec(v_rev_x3f_234_);
lean_dec_ref(v_repo_232_);
lean_dec_ref(v_name_231_);
return v___y_339_;
}
}
v___jp_340_:
{
lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_341_ = lean_box(0);
v___x_342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
return v___x_342_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___boxed(lean_object* v_name_376_, lean_object* v_repo_377_, lean_object* v_url_378_, lean_object* v_rev_x3f_379_, lean_object* v_a_380_, lean_object* v_a_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg(v_name_376_, v_repo_377_, v_url_378_, v_rev_x3f_379_, v_a_380_);
lean_dec_ref(v_a_380_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(lean_object* v_a_383_, lean_object* v_name_384_, lean_object* v_repo_385_, lean_object* v_url_386_, lean_object* v_rev_x3f_387_){
_start:
{
lean_object* v_a_393_; lean_object* v___y_491_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; uint8_t v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_495_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___closed__0));
lean_inc_ref(v_name_384_);
v___x_496_ = lean_string_append(v_name_384_, v___x_495_);
v___x_497_ = lean_string_append(v___x_496_, v_url_386_);
v___x_498_ = 1;
v___x_499_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_499_, 0, v___x_497_);
lean_ctor_set_uint8(v___x_499_, sizeof(void*)*1, v___x_498_);
lean_inc_ref(v_a_383_);
v___x_500_ = lean_apply_2(v_a_383_, v___x_499_, lean_box(0));
v___x_501_ = lean_unsigned_to_nat(0u);
v___x_502_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0));
lean_inc_ref(v_repo_385_);
v___x_503_ = l_Lake_GitRepo_clone(v_url_386_, v_repo_385_, v___x_502_);
if (lean_obj_tag(v___x_503_) == 0)
{
lean_object* v_a_504_; lean_object* v___x_505_; uint8_t v___x_506_; 
v_a_504_ = lean_ctor_get(v___x_503_, 1);
lean_inc(v_a_504_);
lean_dec_ref_known(v___x_503_, 2);
v___x_505_ = lean_array_get_size(v_a_504_);
v___x_506_ = lean_nat_dec_lt(v___x_501_, v___x_505_);
if (v___x_506_ == 0)
{
lean_dec(v_a_504_);
goto v___jp_451_;
}
else
{
lean_object* v___x_507_; uint8_t v___x_508_; 
v___x_507_ = lean_box(0);
v___x_508_ = lean_nat_dec_le(v___x_505_, v___x_505_);
if (v___x_508_ == 0)
{
if (v___x_506_ == 0)
{
lean_dec(v_a_504_);
goto v___jp_451_;
}
else
{
size_t v___x_509_; size_t v___x_510_; lean_object* v___x_511_; 
v___x_509_ = ((size_t)0ULL);
v___x_510_ = lean_usize_of_nat(v___x_505_);
v___x_511_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_504_, v___x_509_, v___x_510_, v___x_507_, v_a_383_);
lean_dec(v_a_504_);
if (lean_obj_tag(v___x_511_) == 0)
{
lean_dec_ref_known(v___x_511_, 1);
goto v___jp_451_;
}
else
{
v___y_491_ = v___x_511_;
goto v___jp_490_;
}
}
}
else
{
size_t v___x_512_; size_t v___x_513_; lean_object* v___x_514_; 
v___x_512_ = ((size_t)0ULL);
v___x_513_ = lean_usize_of_nat(v___x_505_);
v___x_514_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_504_, v___x_512_, v___x_513_, v___x_507_, v_a_383_);
lean_dec(v_a_504_);
if (lean_obj_tag(v___x_514_) == 0)
{
lean_dec_ref_known(v___x_514_, 1);
goto v___jp_451_;
}
else
{
v___y_491_ = v___x_514_;
goto v___jp_490_;
}
}
}
}
else
{
lean_object* v_a_515_; lean_object* v___x_516_; uint8_t v___x_517_; 
v_a_515_ = lean_ctor_get(v___x_503_, 1);
lean_inc(v_a_515_);
lean_dec_ref_known(v___x_503_, 2);
v___x_516_ = lean_array_get_size(v_a_515_);
v___x_517_ = lean_nat_dec_lt(v___x_501_, v___x_516_);
if (v___x_517_ == 0)
{
lean_object* v___x_518_; lean_object* v___x_519_; 
lean_dec(v_a_515_);
lean_dec(v_rev_x3f_387_);
lean_dec_ref(v_repo_385_);
lean_dec_ref(v_name_384_);
v___x_518_ = lean_box(0);
v___x_519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_519_, 0, v___x_518_);
return v___x_519_;
}
else
{
lean_object* v___x_520_; uint8_t v___x_521_; 
v___x_520_ = lean_box(0);
v___x_521_ = lean_nat_dec_le(v___x_516_, v___x_516_);
if (v___x_521_ == 0)
{
if (v___x_517_ == 0)
{
lean_dec(v_a_515_);
lean_dec(v_rev_x3f_387_);
lean_dec_ref(v_repo_385_);
lean_dec_ref(v_name_384_);
goto v___jp_492_;
}
else
{
size_t v___x_522_; size_t v___x_523_; lean_object* v___x_524_; 
v___x_522_ = ((size_t)0ULL);
v___x_523_ = lean_usize_of_nat(v___x_516_);
v___x_524_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_515_, v___x_522_, v___x_523_, v___x_520_, v_a_383_);
lean_dec(v_a_515_);
if (lean_obj_tag(v___x_524_) == 0)
{
lean_dec_ref_known(v___x_524_, 1);
lean_dec(v_rev_x3f_387_);
lean_dec_ref(v_repo_385_);
lean_dec_ref(v_name_384_);
goto v___jp_492_;
}
else
{
v___y_491_ = v___x_524_;
goto v___jp_490_;
}
}
}
else
{
size_t v___x_525_; size_t v___x_526_; lean_object* v___x_527_; 
v___x_525_ = ((size_t)0ULL);
v___x_526_ = lean_usize_of_nat(v___x_516_);
v___x_527_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_515_, v___x_525_, v___x_526_, v___x_520_, v_a_383_);
lean_dec(v_a_515_);
if (lean_obj_tag(v___x_527_) == 0)
{
lean_dec_ref_known(v___x_527_, 1);
lean_dec(v_rev_x3f_387_);
lean_dec_ref(v_repo_385_);
lean_dec_ref(v_name_384_);
goto v___jp_492_;
}
else
{
v___y_491_ = v___x_527_;
goto v___jp_490_;
}
}
}
}
v___jp_389_:
{
lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_390_ = lean_box(0);
v___x_391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_391_, 0, v___x_390_);
return v___x_391_;
}
v___jp_392_:
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; uint8_t v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_394_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3));
v___x_395_ = lean_string_append(v_name_384_, v___x_394_);
v___x_396_ = lean_string_append(v___x_395_, v_a_393_);
v___x_397_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
v___x_398_ = lean_string_append(v___x_396_, v___x_397_);
v___x_399_ = 1;
v___x_400_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_400_, 0, v___x_398_);
lean_ctor_set_uint8(v___x_400_, sizeof(void*)*1, v___x_399_);
lean_inc_ref(v_a_383_);
v___x_401_ = lean_apply_2(v_a_383_, v___x_400_, lean_box(0));
v___x_402_ = lean_unsigned_to_nat(0u);
v___x_403_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0));
v___x_404_ = l_Lake_GitRepo_checkoutDetach(v_a_393_, v_repo_385_, v___x_403_);
if (lean_obj_tag(v___x_404_) == 0)
{
lean_object* v_a_405_; lean_object* v_a_406_; lean_object* v___x_407_; uint8_t v___x_408_; 
v_a_405_ = lean_ctor_get(v___x_404_, 0);
lean_inc(v_a_405_);
v_a_406_ = lean_ctor_get(v___x_404_, 1);
lean_inc(v_a_406_);
lean_dec_ref_known(v___x_404_, 2);
v___x_407_ = lean_array_get_size(v_a_406_);
v___x_408_ = lean_nat_dec_lt(v___x_402_, v___x_407_);
if (v___x_408_ == 0)
{
lean_object* v___x_409_; 
lean_dec(v_a_406_);
v___x_409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_409_, 0, v_a_405_);
return v___x_409_;
}
else
{
lean_object* v___x_410_; uint8_t v___x_411_; 
v___x_410_ = lean_box(0);
v___x_411_ = lean_nat_dec_le(v___x_407_, v___x_407_);
if (v___x_411_ == 0)
{
if (v___x_408_ == 0)
{
lean_object* v___x_412_; 
lean_dec(v_a_406_);
v___x_412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_412_, 0, v_a_405_);
return v___x_412_;
}
else
{
size_t v___x_413_; size_t v___x_414_; lean_object* v___x_415_; 
v___x_413_ = ((size_t)0ULL);
v___x_414_ = lean_usize_of_nat(v___x_407_);
v___x_415_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_406_, v___x_413_, v___x_414_, v___x_410_, v_a_383_);
lean_dec(v_a_406_);
if (lean_obj_tag(v___x_415_) == 0)
{
lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_422_; 
v_isSharedCheck_422_ = !lean_is_exclusive(v___x_415_);
if (v_isSharedCheck_422_ == 0)
{
lean_object* v_unused_423_; 
v_unused_423_ = lean_ctor_get(v___x_415_, 0);
lean_dec(v_unused_423_);
v___x_417_ = v___x_415_;
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
else
{
lean_dec(v___x_415_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_420_; 
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 0, v_a_405_);
v___x_420_ = v___x_417_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_a_405_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
}
else
{
lean_dec(v_a_405_);
return v___x_415_;
}
}
}
else
{
size_t v___x_424_; size_t v___x_425_; lean_object* v___x_426_; 
v___x_424_ = ((size_t)0ULL);
v___x_425_ = lean_usize_of_nat(v___x_407_);
v___x_426_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_406_, v___x_424_, v___x_425_, v___x_410_, v_a_383_);
lean_dec(v_a_406_);
if (lean_obj_tag(v___x_426_) == 0)
{
lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_433_; 
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_426_);
if (v_isSharedCheck_433_ == 0)
{
lean_object* v_unused_434_; 
v_unused_434_ = lean_ctor_get(v___x_426_, 0);
lean_dec(v_unused_434_);
v___x_428_ = v___x_426_;
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
else
{
lean_dec(v___x_426_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_431_; 
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 0, v_a_405_);
v___x_431_ = v___x_428_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_a_405_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
}
else
{
lean_dec(v_a_405_);
return v___x_426_;
}
}
}
}
else
{
lean_object* v_a_435_; lean_object* v___x_436_; uint8_t v___x_437_; 
v_a_435_ = lean_ctor_get(v___x_404_, 1);
lean_inc(v_a_435_);
lean_dec_ref_known(v___x_404_, 2);
v___x_436_ = lean_array_get_size(v_a_435_);
v___x_437_ = lean_nat_dec_lt(v___x_402_, v___x_436_);
if (v___x_437_ == 0)
{
lean_object* v___x_438_; lean_object* v___x_439_; 
lean_dec(v_a_435_);
v___x_438_ = lean_box(0);
v___x_439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_439_, 0, v___x_438_);
return v___x_439_;
}
else
{
lean_object* v___x_440_; uint8_t v___x_441_; 
v___x_440_ = lean_box(0);
v___x_441_ = lean_nat_dec_le(v___x_436_, v___x_436_);
if (v___x_441_ == 0)
{
if (v___x_437_ == 0)
{
lean_dec(v_a_435_);
goto v___jp_389_;
}
else
{
size_t v___x_442_; size_t v___x_443_; lean_object* v___x_444_; 
v___x_442_ = ((size_t)0ULL);
v___x_443_ = lean_usize_of_nat(v___x_436_);
v___x_444_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_435_, v___x_442_, v___x_443_, v___x_440_, v_a_383_);
lean_dec(v_a_435_);
if (lean_obj_tag(v___x_444_) == 0)
{
lean_dec_ref_known(v___x_444_, 1);
goto v___jp_389_;
}
else
{
return v___x_444_;
}
}
}
else
{
size_t v___x_445_; size_t v___x_446_; lean_object* v___x_447_; 
v___x_445_ = ((size_t)0ULL);
v___x_446_ = lean_usize_of_nat(v___x_436_);
v___x_447_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_435_, v___x_445_, v___x_446_, v___x_440_, v_a_383_);
lean_dec(v_a_435_);
if (lean_obj_tag(v___x_447_) == 0)
{
lean_dec_ref_known(v___x_447_, 1);
goto v___jp_389_;
}
else
{
return v___x_447_;
}
}
}
}
}
v___jp_448_:
{
lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_449_ = lean_box(0);
v___x_450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_450_, 0, v___x_449_);
return v___x_450_;
}
v___jp_451_:
{
if (lean_obj_tag(v_rev_x3f_387_) == 1)
{
lean_object* v_val_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_487_; 
v_val_452_ = lean_ctor_get(v_rev_x3f_387_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v_rev_x3f_387_);
if (v_isSharedCheck_487_ == 0)
{
v___x_454_ = v_rev_x3f_387_;
v_isShared_455_ = v_isSharedCheck_487_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_val_452_);
lean_dec(v_rev_x3f_387_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_487_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_456_ = l_Lake_Git_defaultRemote;
v___x_457_ = lean_unsigned_to_nat(0u);
v___x_458_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0));
lean_inc_ref(v_repo_385_);
v___x_459_ = l_Lake_GitRepo_resolveRemoteRevision(v_val_452_, v___x_456_, v_repo_385_, v___x_458_);
if (lean_obj_tag(v___x_459_) == 0)
{
lean_object* v_a_460_; lean_object* v_a_461_; lean_object* v___x_462_; uint8_t v___x_463_; 
lean_del_object(v___x_454_);
v_a_460_ = lean_ctor_get(v___x_459_, 0);
lean_inc(v_a_460_);
v_a_461_ = lean_ctor_get(v___x_459_, 1);
lean_inc(v_a_461_);
lean_dec_ref_known(v___x_459_, 2);
v___x_462_ = lean_array_get_size(v_a_461_);
v___x_463_ = lean_nat_dec_lt(v___x_457_, v___x_462_);
if (v___x_463_ == 0)
{
lean_dec(v_a_461_);
v_a_393_ = v_a_460_;
goto v___jp_392_;
}
else
{
lean_object* v___x_464_; uint8_t v___x_465_; 
v___x_464_ = lean_box(0);
v___x_465_ = lean_nat_dec_le(v___x_462_, v___x_462_);
if (v___x_465_ == 0)
{
if (v___x_463_ == 0)
{
lean_dec(v_a_461_);
v_a_393_ = v_a_460_;
goto v___jp_392_;
}
else
{
size_t v___x_466_; size_t v___x_467_; lean_object* v___x_468_; 
v___x_466_ = ((size_t)0ULL);
v___x_467_ = lean_usize_of_nat(v___x_462_);
v___x_468_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_461_, v___x_466_, v___x_467_, v___x_464_, v_a_383_);
lean_dec(v_a_461_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_dec_ref_known(v___x_468_, 1);
v_a_393_ = v_a_460_;
goto v___jp_392_;
}
else
{
lean_dec(v_a_460_);
lean_dec_ref(v_repo_385_);
lean_dec_ref(v_name_384_);
return v___x_468_;
}
}
}
else
{
size_t v___x_469_; size_t v___x_470_; lean_object* v___x_471_; 
v___x_469_ = ((size_t)0ULL);
v___x_470_ = lean_usize_of_nat(v___x_462_);
v___x_471_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_461_, v___x_469_, v___x_470_, v___x_464_, v_a_383_);
lean_dec(v_a_461_);
if (lean_obj_tag(v___x_471_) == 0)
{
lean_dec_ref_known(v___x_471_, 1);
v_a_393_ = v_a_460_;
goto v___jp_392_;
}
else
{
lean_dec(v_a_460_);
lean_dec_ref(v_repo_385_);
lean_dec_ref(v_name_384_);
return v___x_471_;
}
}
}
}
else
{
lean_object* v_a_472_; lean_object* v___x_473_; uint8_t v___x_474_; 
lean_dec_ref(v_repo_385_);
lean_dec_ref(v_name_384_);
v_a_472_ = lean_ctor_get(v___x_459_, 1);
lean_inc(v_a_472_);
lean_dec_ref_known(v___x_459_, 2);
v___x_473_ = lean_array_get_size(v_a_472_);
v___x_474_ = lean_nat_dec_lt(v___x_457_, v___x_473_);
if (v___x_474_ == 0)
{
lean_object* v___x_475_; lean_object* v___x_477_; 
lean_dec(v_a_472_);
v___x_475_ = lean_box(0);
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 0, v___x_475_);
v___x_477_ = v___x_454_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v___x_475_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
else
{
lean_object* v___x_479_; uint8_t v___x_480_; 
lean_del_object(v___x_454_);
v___x_479_ = lean_box(0);
v___x_480_ = lean_nat_dec_le(v___x_473_, v___x_473_);
if (v___x_480_ == 0)
{
if (v___x_474_ == 0)
{
lean_dec(v_a_472_);
goto v___jp_448_;
}
else
{
size_t v___x_481_; size_t v___x_482_; lean_object* v___x_483_; 
v___x_481_ = ((size_t)0ULL);
v___x_482_ = lean_usize_of_nat(v___x_473_);
v___x_483_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_472_, v___x_481_, v___x_482_, v___x_479_, v_a_383_);
lean_dec(v_a_472_);
if (lean_obj_tag(v___x_483_) == 0)
{
lean_dec_ref_known(v___x_483_, 1);
goto v___jp_448_;
}
else
{
return v___x_483_;
}
}
}
else
{
size_t v___x_484_; size_t v___x_485_; lean_object* v___x_486_; 
v___x_484_ = ((size_t)0ULL);
v___x_485_ = lean_usize_of_nat(v___x_473_);
v___x_486_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_472_, v___x_484_, v___x_485_, v___x_479_, v_a_383_);
lean_dec(v_a_472_);
if (lean_obj_tag(v___x_486_) == 0)
{
lean_dec_ref_known(v___x_486_, 1);
goto v___jp_448_;
}
else
{
return v___x_486_;
}
}
}
}
}
}
else
{
lean_object* v___x_488_; lean_object* v___x_489_; 
lean_dec(v_rev_x3f_387_);
lean_dec_ref(v_repo_385_);
lean_dec_ref(v_name_384_);
v___x_488_ = lean_box(0);
v___x_489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_489_, 0, v___x_488_);
return v___x_489_;
}
}
v___jp_490_:
{
if (lean_obj_tag(v___y_491_) == 0)
{
lean_dec_ref_known(v___y_491_, 1);
goto v___jp_451_;
}
else
{
lean_dec(v_rev_x3f_387_);
lean_dec_ref(v_repo_385_);
lean_dec_ref(v_name_384_);
return v___y_491_;
}
}
v___jp_492_:
{
lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_493_ = lean_box(0);
v___x_494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_494_, 0, v___x_493_);
return v___x_494_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0___boxed(lean_object* v_a_528_, lean_object* v_name_529_, lean_object* v_repo_530_, lean_object* v_url_531_, lean_object* v_rev_x3f_532_, lean_object* v_a_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(v_a_528_, v_name_529_, v_repo_530_, v_url_531_, v_rev_x3f_532_);
lean_dec_ref(v_a_528_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(lean_object* v_a_535_, lean_object* v_name_536_, lean_object* v_repo_537_, lean_object* v_rev_x3f_538_){
_start:
{
lean_object* v___y_591_; uint8_t v_a_596_; lean_object* v___y_609_; lean_object* v_a_610_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_665_ = l_Lake_Git_defaultRemote;
v___x_666_ = lean_unsigned_to_nat(0u);
v___x_667_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0));
lean_inc_ref(v_repo_537_);
v___x_668_ = l_Lake_GitRepo_findRemoteRevision(v_repo_537_, v_rev_x3f_538_, v___x_665_, v___x_667_);
if (lean_obj_tag(v___x_668_) == 0)
{
lean_object* v_a_669_; lean_object* v_a_670_; lean_object* v___x_698_; uint8_t v___x_699_; 
v_a_669_ = lean_ctor_get(v___x_668_, 0);
lean_inc(v_a_669_);
v_a_670_ = lean_ctor_get(v___x_668_, 1);
lean_inc(v_a_670_);
lean_dec_ref_known(v___x_668_, 2);
v___x_698_ = lean_array_get_size(v_a_670_);
v___x_699_ = lean_nat_dec_lt(v___x_666_, v___x_698_);
if (v___x_699_ == 0)
{
lean_dec(v_a_670_);
goto v___jp_671_;
}
else
{
lean_object* v___x_700_; uint8_t v___x_701_; 
v___x_700_ = lean_box(0);
v___x_701_ = lean_nat_dec_le(v___x_698_, v___x_698_);
if (v___x_701_ == 0)
{
if (v___x_699_ == 0)
{
lean_dec(v_a_670_);
goto v___jp_671_;
}
else
{
size_t v___x_702_; size_t v___x_703_; lean_object* v___x_704_; 
v___x_702_ = ((size_t)0ULL);
v___x_703_ = lean_usize_of_nat(v___x_698_);
v___x_704_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_670_, v___x_702_, v___x_703_, v___x_700_, v_a_535_);
lean_dec(v_a_670_);
if (lean_obj_tag(v___x_704_) == 0)
{
lean_dec_ref_known(v___x_704_, 1);
goto v___jp_671_;
}
else
{
lean_dec(v_a_669_);
lean_dec_ref(v_repo_537_);
lean_dec_ref(v_name_536_);
return v___x_704_;
}
}
}
else
{
size_t v___x_705_; size_t v___x_706_; lean_object* v___x_707_; 
v___x_705_ = ((size_t)0ULL);
v___x_706_ = lean_usize_of_nat(v___x_698_);
v___x_707_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_670_, v___x_705_, v___x_706_, v___x_700_, v_a_535_);
lean_dec(v_a_670_);
if (lean_obj_tag(v___x_707_) == 0)
{
lean_dec_ref_known(v___x_707_, 1);
goto v___jp_671_;
}
else
{
lean_dec(v_a_669_);
lean_dec_ref(v_repo_537_);
lean_dec_ref(v_name_536_);
return v___x_707_;
}
}
}
v___jp_671_:
{
lean_object* v___x_672_; 
lean_inc_ref(v_repo_537_);
v___x_672_ = l_Lake_GitRepo_getHeadRevision(v_repo_537_, v___x_667_);
if (lean_obj_tag(v___x_672_) == 0)
{
lean_object* v_a_673_; lean_object* v_a_674_; lean_object* v___x_675_; uint8_t v___x_676_; 
v_a_673_ = lean_ctor_get(v___x_672_, 0);
lean_inc(v_a_673_);
v_a_674_ = lean_ctor_get(v___x_672_, 1);
lean_inc(v_a_674_);
lean_dec_ref_known(v___x_672_, 2);
v___x_675_ = lean_array_get_size(v_a_674_);
v___x_676_ = lean_nat_dec_lt(v___x_666_, v___x_675_);
if (v___x_676_ == 0)
{
lean_dec(v_a_674_);
v___y_609_ = v_a_669_;
v_a_610_ = v_a_673_;
goto v___jp_608_;
}
else
{
lean_object* v___x_677_; uint8_t v___x_678_; 
v___x_677_ = lean_box(0);
v___x_678_ = lean_nat_dec_le(v___x_675_, v___x_675_);
if (v___x_678_ == 0)
{
if (v___x_676_ == 0)
{
lean_dec(v_a_674_);
v___y_609_ = v_a_669_;
v_a_610_ = v_a_673_;
goto v___jp_608_;
}
else
{
size_t v___x_679_; size_t v___x_680_; lean_object* v___x_681_; 
v___x_679_ = ((size_t)0ULL);
v___x_680_ = lean_usize_of_nat(v___x_675_);
v___x_681_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_674_, v___x_679_, v___x_680_, v___x_677_, v_a_535_);
lean_dec(v_a_674_);
if (lean_obj_tag(v___x_681_) == 0)
{
lean_dec_ref_known(v___x_681_, 1);
v___y_609_ = v_a_669_;
v_a_610_ = v_a_673_;
goto v___jp_608_;
}
else
{
lean_dec(v_a_673_);
lean_dec(v_a_669_);
lean_dec_ref(v_repo_537_);
lean_dec_ref(v_name_536_);
return v___x_681_;
}
}
}
else
{
size_t v___x_682_; size_t v___x_683_; lean_object* v___x_684_; 
v___x_682_ = ((size_t)0ULL);
v___x_683_ = lean_usize_of_nat(v___x_675_);
v___x_684_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_674_, v___x_682_, v___x_683_, v___x_677_, v_a_535_);
lean_dec(v_a_674_);
if (lean_obj_tag(v___x_684_) == 0)
{
lean_dec_ref_known(v___x_684_, 1);
v___y_609_ = v_a_669_;
v_a_610_ = v_a_673_;
goto v___jp_608_;
}
else
{
lean_dec(v_a_673_);
lean_dec(v_a_669_);
lean_dec_ref(v_repo_537_);
lean_dec_ref(v_name_536_);
return v___x_684_;
}
}
}
}
else
{
lean_object* v_a_685_; lean_object* v___x_686_; uint8_t v___x_687_; 
lean_dec(v_a_669_);
lean_dec_ref(v_repo_537_);
lean_dec_ref(v_name_536_);
v_a_685_ = lean_ctor_get(v___x_672_, 1);
lean_inc(v_a_685_);
lean_dec_ref_known(v___x_672_, 2);
v___x_686_ = lean_array_get_size(v_a_685_);
v___x_687_ = lean_nat_dec_lt(v___x_666_, v___x_686_);
if (v___x_687_ == 0)
{
lean_object* v___x_688_; lean_object* v___x_689_; 
lean_dec(v_a_685_);
v___x_688_ = lean_box(0);
v___x_689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_689_, 0, v___x_688_);
return v___x_689_;
}
else
{
lean_object* v___x_690_; uint8_t v___x_691_; 
v___x_690_ = lean_box(0);
v___x_691_ = lean_nat_dec_le(v___x_686_, v___x_686_);
if (v___x_691_ == 0)
{
if (v___x_687_ == 0)
{
lean_dec(v_a_685_);
goto v___jp_659_;
}
else
{
size_t v___x_692_; size_t v___x_693_; lean_object* v___x_694_; 
v___x_692_ = ((size_t)0ULL);
v___x_693_ = lean_usize_of_nat(v___x_686_);
v___x_694_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_685_, v___x_692_, v___x_693_, v___x_690_, v_a_535_);
lean_dec(v_a_685_);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_dec_ref_known(v___x_694_, 1);
goto v___jp_659_;
}
else
{
return v___x_694_;
}
}
}
else
{
size_t v___x_695_; size_t v___x_696_; lean_object* v___x_697_; 
v___x_695_ = ((size_t)0ULL);
v___x_696_ = lean_usize_of_nat(v___x_686_);
v___x_697_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_685_, v___x_695_, v___x_696_, v___x_690_, v_a_535_);
lean_dec(v_a_685_);
if (lean_obj_tag(v___x_697_) == 0)
{
lean_dec_ref_known(v___x_697_, 1);
goto v___jp_659_;
}
else
{
return v___x_697_;
}
}
}
}
}
}
else
{
lean_object* v_a_708_; lean_object* v___x_709_; uint8_t v___x_710_; 
lean_dec_ref(v_repo_537_);
lean_dec_ref(v_name_536_);
v_a_708_ = lean_ctor_get(v___x_668_, 1);
lean_inc(v_a_708_);
lean_dec_ref_known(v___x_668_, 2);
v___x_709_ = lean_array_get_size(v_a_708_);
v___x_710_ = lean_nat_dec_lt(v___x_666_, v___x_709_);
if (v___x_710_ == 0)
{
lean_object* v___x_711_; lean_object* v___x_712_; 
lean_dec(v_a_708_);
v___x_711_ = lean_box(0);
v___x_712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_712_, 0, v___x_711_);
return v___x_712_;
}
else
{
lean_object* v___x_713_; uint8_t v___x_714_; 
v___x_713_ = lean_box(0);
v___x_714_ = lean_nat_dec_le(v___x_709_, v___x_709_);
if (v___x_714_ == 0)
{
if (v___x_710_ == 0)
{
lean_dec(v_a_708_);
goto v___jp_662_;
}
else
{
size_t v___x_715_; size_t v___x_716_; lean_object* v___x_717_; 
v___x_715_ = ((size_t)0ULL);
v___x_716_ = lean_usize_of_nat(v___x_709_);
v___x_717_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_708_, v___x_715_, v___x_716_, v___x_713_, v_a_535_);
lean_dec(v_a_708_);
if (lean_obj_tag(v___x_717_) == 0)
{
lean_dec_ref_known(v___x_717_, 1);
goto v___jp_662_;
}
else
{
return v___x_717_;
}
}
}
else
{
size_t v___x_718_; size_t v___x_719_; lean_object* v___x_720_; 
v___x_718_ = ((size_t)0ULL);
v___x_719_ = lean_usize_of_nat(v___x_709_);
v___x_720_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_708_, v___x_718_, v___x_719_, v___x_713_, v_a_535_);
lean_dec(v_a_708_);
if (lean_obj_tag(v___x_720_) == 0)
{
lean_dec_ref_known(v___x_720_, 1);
goto v___jp_662_;
}
else
{
return v___x_720_;
}
}
}
}
v___jp_540_:
{
lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_541_ = lean_box(0);
v___x_542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
return v___x_542_;
}
v___jp_543_:
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_544_ = lean_unsigned_to_nat(0u);
v___x_545_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0));
v___x_546_ = l_Lake_GitRepo_clean(v_repo_537_, v___x_545_);
if (lean_obj_tag(v___x_546_) == 0)
{
lean_object* v_a_547_; lean_object* v_a_548_; lean_object* v___x_549_; uint8_t v___x_550_; 
v_a_547_ = lean_ctor_get(v___x_546_, 0);
lean_inc(v_a_547_);
v_a_548_ = lean_ctor_get(v___x_546_, 1);
lean_inc(v_a_548_);
lean_dec_ref_known(v___x_546_, 2);
v___x_549_ = lean_array_get_size(v_a_548_);
v___x_550_ = lean_nat_dec_lt(v___x_544_, v___x_549_);
if (v___x_550_ == 0)
{
lean_object* v___x_551_; 
lean_dec(v_a_548_);
v___x_551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_551_, 0, v_a_547_);
return v___x_551_;
}
else
{
lean_object* v___x_552_; uint8_t v___x_553_; 
v___x_552_ = lean_box(0);
v___x_553_ = lean_nat_dec_le(v___x_549_, v___x_549_);
if (v___x_553_ == 0)
{
if (v___x_550_ == 0)
{
lean_object* v___x_554_; 
lean_dec(v_a_548_);
v___x_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_554_, 0, v_a_547_);
return v___x_554_;
}
else
{
size_t v___x_555_; size_t v___x_556_; lean_object* v___x_557_; 
v___x_555_ = ((size_t)0ULL);
v___x_556_ = lean_usize_of_nat(v___x_549_);
v___x_557_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_548_, v___x_555_, v___x_556_, v___x_552_, v_a_535_);
lean_dec(v_a_548_);
if (lean_obj_tag(v___x_557_) == 0)
{
lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_564_; 
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_557_);
if (v_isSharedCheck_564_ == 0)
{
lean_object* v_unused_565_; 
v_unused_565_ = lean_ctor_get(v___x_557_, 0);
lean_dec(v_unused_565_);
v___x_559_ = v___x_557_;
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
else
{
lean_dec(v___x_557_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_562_; 
if (v_isShared_560_ == 0)
{
lean_ctor_set(v___x_559_, 0, v_a_547_);
v___x_562_ = v___x_559_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_a_547_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
}
else
{
lean_dec(v_a_547_);
return v___x_557_;
}
}
}
else
{
size_t v___x_566_; size_t v___x_567_; lean_object* v___x_568_; 
v___x_566_ = ((size_t)0ULL);
v___x_567_ = lean_usize_of_nat(v___x_549_);
v___x_568_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_548_, v___x_566_, v___x_567_, v___x_552_, v_a_535_);
lean_dec(v_a_548_);
if (lean_obj_tag(v___x_568_) == 0)
{
lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_575_; 
v_isSharedCheck_575_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_575_ == 0)
{
lean_object* v_unused_576_; 
v_unused_576_ = lean_ctor_get(v___x_568_, 0);
lean_dec(v_unused_576_);
v___x_570_ = v___x_568_;
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
else
{
lean_dec(v___x_568_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_573_; 
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 0, v_a_547_);
v___x_573_ = v___x_570_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v_a_547_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
}
else
{
lean_dec(v_a_547_);
return v___x_568_;
}
}
}
}
else
{
lean_object* v_a_577_; lean_object* v___x_578_; uint8_t v___x_579_; 
v_a_577_ = lean_ctor_get(v___x_546_, 1);
lean_inc(v_a_577_);
lean_dec_ref_known(v___x_546_, 2);
v___x_578_ = lean_array_get_size(v_a_577_);
v___x_579_ = lean_nat_dec_lt(v___x_544_, v___x_578_);
if (v___x_579_ == 0)
{
lean_object* v___x_580_; lean_object* v___x_581_; 
lean_dec(v_a_577_);
v___x_580_ = lean_box(0);
v___x_581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
return v___x_581_;
}
else
{
lean_object* v___x_582_; uint8_t v___x_583_; 
v___x_582_ = lean_box(0);
v___x_583_ = lean_nat_dec_le(v___x_578_, v___x_578_);
if (v___x_583_ == 0)
{
if (v___x_579_ == 0)
{
lean_dec(v_a_577_);
goto v___jp_540_;
}
else
{
size_t v___x_584_; size_t v___x_585_; lean_object* v___x_586_; 
v___x_584_ = ((size_t)0ULL);
v___x_585_ = lean_usize_of_nat(v___x_578_);
v___x_586_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_577_, v___x_584_, v___x_585_, v___x_582_, v_a_535_);
lean_dec(v_a_577_);
if (lean_obj_tag(v___x_586_) == 0)
{
lean_dec_ref_known(v___x_586_, 1);
goto v___jp_540_;
}
else
{
return v___x_586_;
}
}
}
else
{
size_t v___x_587_; size_t v___x_588_; lean_object* v___x_589_; 
v___x_587_ = ((size_t)0ULL);
v___x_588_ = lean_usize_of_nat(v___x_578_);
v___x_589_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_577_, v___x_587_, v___x_588_, v___x_582_, v_a_535_);
lean_dec(v_a_577_);
if (lean_obj_tag(v___x_589_) == 0)
{
lean_dec_ref_known(v___x_589_, 1);
goto v___jp_540_;
}
else
{
return v___x_589_;
}
}
}
}
}
v___jp_590_:
{
if (lean_obj_tag(v___y_591_) == 0)
{
lean_dec_ref_known(v___y_591_, 1);
goto v___jp_543_;
}
else
{
lean_dec_ref(v_repo_537_);
return v___y_591_;
}
}
v___jp_592_:
{
lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_593_ = lean_box(0);
v___x_594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_594_, 0, v___x_593_);
return v___x_594_;
}
v___jp_595_:
{
if (v_a_596_ == 0)
{
lean_object* v___x_597_; lean_object* v___x_598_; 
lean_dec_ref(v_repo_537_);
lean_dec_ref(v_name_536_);
v___x_597_ = lean_box(0);
v___x_598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_598_, 0, v___x_597_);
return v___x_598_;
}
else
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; uint8_t v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_599_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1));
v___x_600_ = lean_string_append(v_name_536_, v___x_599_);
v___x_601_ = lean_string_append(v___x_600_, v_repo_537_);
lean_dec_ref(v_repo_537_);
v___x_602_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_603_ = lean_string_append(v___x_601_, v___x_602_);
v___x_604_ = 2;
v___x_605_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_605_, 0, v___x_603_);
lean_ctor_set_uint8(v___x_605_, sizeof(void*)*1, v___x_604_);
lean_inc_ref(v_a_535_);
v___x_606_ = lean_apply_2(v_a_535_, v___x_605_, lean_box(0));
v___x_607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_607_, 0, v___x_606_);
return v___x_607_;
}
}
v___jp_608_:
{
uint8_t v___x_611_; 
v___x_611_ = lean_string_dec_eq(v_a_610_, v___y_609_);
lean_dec_ref(v_a_610_);
if (v___x_611_ == 0)
{
lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; uint8_t v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_612_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3));
v___x_613_ = lean_string_append(v_name_536_, v___x_612_);
v___x_614_ = lean_string_append(v___x_613_, v___y_609_);
v___x_615_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
v___x_616_ = lean_string_append(v___x_614_, v___x_615_);
v___x_617_ = 1;
v___x_618_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_618_, 0, v___x_616_);
lean_ctor_set_uint8(v___x_618_, sizeof(void*)*1, v___x_617_);
lean_inc_ref(v_a_535_);
v___x_619_ = lean_apply_2(v_a_535_, v___x_618_, lean_box(0));
v___x_620_ = lean_unsigned_to_nat(0u);
v___x_621_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0));
lean_inc_ref(v_repo_537_);
v___x_622_ = l_Lake_GitRepo_checkoutDetach(v___y_609_, v_repo_537_, v___x_621_);
if (lean_obj_tag(v___x_622_) == 0)
{
lean_object* v_a_623_; lean_object* v___x_624_; uint8_t v___x_625_; 
v_a_623_ = lean_ctor_get(v___x_622_, 1);
lean_inc(v_a_623_);
lean_dec_ref_known(v___x_622_, 2);
v___x_624_ = lean_array_get_size(v_a_623_);
v___x_625_ = lean_nat_dec_lt(v___x_620_, v___x_624_);
if (v___x_625_ == 0)
{
lean_dec(v_a_623_);
goto v___jp_543_;
}
else
{
lean_object* v___x_626_; uint8_t v___x_627_; 
v___x_626_ = lean_box(0);
v___x_627_ = lean_nat_dec_le(v___x_624_, v___x_624_);
if (v___x_627_ == 0)
{
if (v___x_625_ == 0)
{
lean_dec(v_a_623_);
goto v___jp_543_;
}
else
{
size_t v___x_628_; size_t v___x_629_; lean_object* v___x_630_; 
v___x_628_ = ((size_t)0ULL);
v___x_629_ = lean_usize_of_nat(v___x_624_);
v___x_630_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_623_, v___x_628_, v___x_629_, v___x_626_, v_a_535_);
lean_dec(v_a_623_);
if (lean_obj_tag(v___x_630_) == 0)
{
lean_dec_ref_known(v___x_630_, 1);
goto v___jp_543_;
}
else
{
v___y_591_ = v___x_630_;
goto v___jp_590_;
}
}
}
else
{
size_t v___x_631_; size_t v___x_632_; lean_object* v___x_633_; 
v___x_631_ = ((size_t)0ULL);
v___x_632_ = lean_usize_of_nat(v___x_624_);
v___x_633_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_623_, v___x_631_, v___x_632_, v___x_626_, v_a_535_);
lean_dec(v_a_623_);
if (lean_obj_tag(v___x_633_) == 0)
{
lean_dec_ref_known(v___x_633_, 1);
goto v___jp_543_;
}
else
{
v___y_591_ = v___x_633_;
goto v___jp_590_;
}
}
}
}
else
{
lean_object* v_a_634_; lean_object* v___x_635_; uint8_t v___x_636_; 
v_a_634_ = lean_ctor_get(v___x_622_, 1);
lean_inc(v_a_634_);
lean_dec_ref_known(v___x_622_, 2);
v___x_635_ = lean_array_get_size(v_a_634_);
v___x_636_ = lean_nat_dec_lt(v___x_620_, v___x_635_);
if (v___x_636_ == 0)
{
lean_object* v___x_637_; lean_object* v___x_638_; 
lean_dec(v_a_634_);
lean_dec_ref(v_repo_537_);
v___x_637_ = lean_box(0);
v___x_638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_638_, 0, v___x_637_);
return v___x_638_;
}
else
{
lean_object* v___x_639_; uint8_t v___x_640_; 
v___x_639_ = lean_box(0);
v___x_640_ = lean_nat_dec_le(v___x_635_, v___x_635_);
if (v___x_640_ == 0)
{
if (v___x_636_ == 0)
{
lean_dec(v_a_634_);
lean_dec_ref(v_repo_537_);
goto v___jp_592_;
}
else
{
size_t v___x_641_; size_t v___x_642_; lean_object* v___x_643_; 
v___x_641_ = ((size_t)0ULL);
v___x_642_ = lean_usize_of_nat(v___x_635_);
v___x_643_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_634_, v___x_641_, v___x_642_, v___x_639_, v_a_535_);
lean_dec(v_a_634_);
if (lean_obj_tag(v___x_643_) == 0)
{
lean_dec_ref_known(v___x_643_, 1);
lean_dec_ref(v_repo_537_);
goto v___jp_592_;
}
else
{
v___y_591_ = v___x_643_;
goto v___jp_590_;
}
}
}
else
{
size_t v___x_644_; size_t v___x_645_; lean_object* v___x_646_; 
v___x_644_ = ((size_t)0ULL);
v___x_645_ = lean_usize_of_nat(v___x_635_);
v___x_646_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_634_, v___x_644_, v___x_645_, v___x_639_, v_a_535_);
lean_dec(v_a_634_);
if (lean_obj_tag(v___x_646_) == 0)
{
lean_dec_ref_known(v___x_646_, 1);
lean_dec_ref(v_repo_537_);
goto v___jp_592_;
}
else
{
v___y_591_ = v___x_646_;
goto v___jp_590_;
}
}
}
}
}
else
{
uint8_t v___x_647_; lean_object* v___x_648_; uint8_t v___x_649_; uint8_t v___x_650_; 
lean_dec_ref(v___y_609_);
lean_inc_ref(v_repo_537_);
v___x_647_ = l_Lake_GitRepo_hasNoDiff(v_repo_537_);
v___x_648_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0));
v___x_649_ = lean_bool_not(v___x_647_);
v___x_650_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__6);
if (v___x_650_ == 0)
{
v_a_596_ = v___x_649_;
goto v___jp_595_;
}
else
{
lean_object* v___x_651_; uint8_t v___x_652_; 
v___x_651_ = lean_box(0);
v___x_652_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__7);
if (v___x_652_ == 0)
{
if (v___x_650_ == 0)
{
v_a_596_ = v___x_649_;
goto v___jp_595_;
}
else
{
size_t v___x_653_; size_t v___x_654_; lean_object* v___x_655_; 
v___x_653_ = ((size_t)0ULL);
v___x_654_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8);
v___x_655_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_648_, v___x_653_, v___x_654_, v___x_651_, v_a_535_);
if (lean_obj_tag(v___x_655_) == 0)
{
lean_dec_ref_known(v___x_655_, 1);
v_a_596_ = v___x_649_;
goto v___jp_595_;
}
else
{
lean_dec_ref(v_repo_537_);
lean_dec_ref(v_name_536_);
return v___x_655_;
}
}
}
else
{
size_t v___x_656_; size_t v___x_657_; lean_object* v___x_658_; 
v___x_656_ = ((size_t)0ULL);
v___x_657_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8);
v___x_658_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_648_, v___x_656_, v___x_657_, v___x_651_, v_a_535_);
if (lean_obj_tag(v___x_658_) == 0)
{
lean_dec_ref_known(v___x_658_, 1);
v_a_596_ = v___x_649_;
goto v___jp_595_;
}
else
{
lean_dec_ref(v_repo_537_);
lean_dec_ref(v_name_536_);
return v___x_658_;
}
}
}
}
}
v___jp_659_:
{
lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_660_ = lean_box(0);
v___x_661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_661_, 0, v___x_660_);
return v___x_661_;
}
v___jp_662_:
{
lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_663_ = lean_box(0);
v___x_664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_664_, 0, v___x_663_);
return v___x_664_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1___boxed(lean_object* v_a_721_, lean_object* v_name_722_, lean_object* v_repo_723_, lean_object* v_rev_x3f_724_, lean_object* v_a_725_){
_start:
{
lean_object* v_res_726_; 
v_res_726_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(v_a_721_, v_name_722_, v_repo_723_, v_rev_x3f_724_);
lean_dec_ref(v_a_721_);
return v_res_726_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo(lean_object* v_name_731_, lean_object* v_repo_732_, lean_object* v_url_733_, lean_object* v_rev_x3f_734_, lean_object* v_a_735_){
_start:
{
uint8_t v_a_738_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; uint8_t v_val_777_; 
v___x_773_ = l_Lake_Git_defaultRemote;
lean_inc_ref(v_repo_732_);
v___x_774_ = l_Lake_GitRepo_getRemoteUrl_x3f(v___x_773_, v_repo_732_);
v___x_775_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0));
if (lean_obj_tag(v___x_774_) == 1)
{
lean_object* v_val_787_; uint8_t v___x_788_; 
v_val_787_ = lean_ctor_get(v___x_774_, 0);
lean_inc(v_val_787_);
lean_dec_ref_known(v___x_774_, 1);
v___x_788_ = lean_string_dec_eq(v_val_787_, v_url_733_);
if (v___x_788_ == 0)
{
lean_object* v___x_789_; 
v___x_789_ = lean_io_realpath(v_val_787_);
if (lean_obj_tag(v___x_789_) == 0)
{
lean_object* v_a_790_; lean_object* v___x_791_; 
v_a_790_ = lean_ctor_get(v___x_789_, 0);
lean_inc(v_a_790_);
lean_dec_ref_known(v___x_789_, 1);
lean_inc_ref(v_url_733_);
v___x_791_ = lean_io_realpath(v_url_733_);
if (lean_obj_tag(v___x_791_) == 0)
{
lean_object* v_a_792_; uint8_t v___x_793_; 
v_a_792_ = lean_ctor_get(v___x_791_, 0);
lean_inc(v_a_792_);
lean_dec_ref_known(v___x_791_, 1);
v___x_793_ = lean_string_dec_eq(v_a_790_, v_a_792_);
lean_dec(v_a_792_);
lean_dec(v_a_790_);
v_val_777_ = v___x_793_;
goto v___jp_776_;
}
else
{
lean_dec_ref_known(v___x_791_, 1);
lean_dec(v_a_790_);
v_val_777_ = v___x_788_;
goto v___jp_776_;
}
}
else
{
lean_dec_ref_known(v___x_789_, 1);
v_val_777_ = v___x_788_;
goto v___jp_776_;
}
}
else
{
lean_dec(v_val_787_);
v_val_777_ = v___x_788_;
goto v___jp_776_;
}
}
else
{
uint8_t v___x_794_; 
lean_dec(v___x_774_);
v___x_794_ = 0;
v_val_777_ = v___x_794_;
goto v___jp_776_;
}
v___jp_737_:
{
if (v_a_738_ == 0)
{
uint8_t v___x_739_; 
v___x_739_ = l_System_Platform_isWindows;
if (v___x_739_ == 0)
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; uint8_t v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_740_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__0));
lean_inc_ref(v_name_731_);
v___x_741_ = lean_string_append(v_name_731_, v___x_740_);
v___x_742_ = lean_string_append(v___x_741_, v_repo_732_);
v___x_743_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__1));
v___x_744_ = lean_string_append(v___x_742_, v___x_743_);
v___x_745_ = 1;
v___x_746_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_746_, 0, v___x_744_);
lean_ctor_set_uint8(v___x_746_, sizeof(void*)*1, v___x_745_);
lean_inc_ref(v_a_735_);
v___x_747_ = lean_apply_2(v_a_735_, v___x_746_, lean_box(0));
v___x_748_ = l_IO_FS_removeDirAll(v_repo_732_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_object* v___x_749_; 
lean_dec_ref_known(v___x_748_, 1);
v___x_749_ = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(v_a_735_, v_name_731_, v_repo_732_, v_url_733_, v_rev_x3f_734_);
return v___x_749_;
}
else
{
lean_object* v_a_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_762_; 
lean_dec(v_rev_x3f_734_);
lean_dec_ref(v_url_733_);
lean_dec_ref(v_repo_732_);
lean_dec_ref(v_name_731_);
v_a_750_ = lean_ctor_get(v___x_748_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_762_ == 0)
{
v___x_752_ = v___x_748_;
v_isShared_753_ = v_isSharedCheck_762_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_a_750_);
lean_dec(v___x_748_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_762_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_754_; uint8_t v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_760_; 
v___x_754_ = lean_io_error_to_string(v_a_750_);
v___x_755_ = 3;
v___x_756_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_756_, 0, v___x_754_);
lean_ctor_set_uint8(v___x_756_, sizeof(void*)*1, v___x_755_);
lean_inc_ref(v_a_735_);
v___x_757_ = lean_apply_2(v_a_735_, v___x_756_, lean_box(0));
v___x_758_ = lean_box(0);
if (v_isShared_753_ == 0)
{
lean_ctor_set(v___x_752_, 0, v___x_758_);
v___x_760_ = v___x_752_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v___x_758_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
}
else
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; uint8_t v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
lean_dec_ref(v_url_733_);
v___x_763_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__2));
lean_inc_ref(v_name_731_);
v___x_764_ = lean_string_append(v_name_731_, v___x_763_);
v___x_765_ = lean_string_append(v___x_764_, v_repo_732_);
v___x_766_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__3));
v___x_767_ = lean_string_append(v___x_765_, v___x_766_);
v___x_768_ = 1;
v___x_769_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_769_, 0, v___x_767_);
lean_ctor_set_uint8(v___x_769_, sizeof(void*)*1, v___x_768_);
lean_inc_ref(v_a_735_);
v___x_770_ = lean_apply_2(v_a_735_, v___x_769_, lean_box(0));
v___x_771_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(v_a_735_, v_name_731_, v_repo_732_, v_rev_x3f_734_);
return v___x_771_;
}
}
else
{
lean_object* v___x_772_; 
lean_dec_ref(v_url_733_);
v___x_772_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(v_a_735_, v_name_731_, v_repo_732_, v_rev_x3f_734_);
return v___x_772_;
}
}
v___jp_776_:
{
uint8_t v___x_778_; 
v___x_778_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__6);
if (v___x_778_ == 0)
{
v_a_738_ = v_val_777_;
goto v___jp_737_;
}
else
{
lean_object* v___x_779_; uint8_t v___x_780_; 
v___x_779_ = lean_box(0);
v___x_780_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__7);
if (v___x_780_ == 0)
{
if (v___x_778_ == 0)
{
v_a_738_ = v_val_777_;
goto v___jp_737_;
}
else
{
size_t v___x_781_; size_t v___x_782_; lean_object* v___x_783_; 
v___x_781_ = ((size_t)0ULL);
v___x_782_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8);
v___x_783_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_775_, v___x_781_, v___x_782_, v___x_779_, v_a_735_);
if (lean_obj_tag(v___x_783_) == 0)
{
lean_dec_ref_known(v___x_783_, 1);
v_a_738_ = v_val_777_;
goto v___jp_737_;
}
else
{
lean_dec(v_rev_x3f_734_);
lean_dec_ref(v_url_733_);
lean_dec_ref(v_repo_732_);
lean_dec_ref(v_name_731_);
return v___x_783_;
}
}
}
else
{
size_t v___x_784_; size_t v___x_785_; lean_object* v___x_786_; 
v___x_784_ = ((size_t)0ULL);
v___x_785_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8);
v___x_786_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_775_, v___x_784_, v___x_785_, v___x_779_, v_a_735_);
if (lean_obj_tag(v___x_786_) == 0)
{
lean_dec_ref_known(v___x_786_, 1);
v_a_738_ = v_val_777_;
goto v___jp_737_;
}
else
{
lean_dec(v_rev_x3f_734_);
lean_dec_ref(v_url_733_);
lean_dec_ref(v_repo_732_);
lean_dec_ref(v_name_731_);
return v___x_786_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___boxed(lean_object* v_name_795_, lean_object* v_repo_796_, lean_object* v_url_797_, lean_object* v_rev_x3f_798_, lean_object* v_a_799_, lean_object* v_a_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo(v_name_795_, v_repo_796_, v_url_797_, v_rev_x3f_798_, v_a_799_);
lean_dec_ref(v_a_799_);
return v_res_801_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(lean_object* v_a_802_, lean_object* v_name_803_, lean_object* v_repo_804_, lean_object* v_url_805_, lean_object* v_rev_x3f_806_){
_start:
{
uint8_t v_a_809_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; uint8_t v_val_848_; 
v___x_844_ = l_Lake_Git_defaultRemote;
lean_inc_ref(v_repo_804_);
v___x_845_ = l_Lake_GitRepo_getRemoteUrl_x3f(v___x_844_, v_repo_804_);
v___x_846_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0));
if (lean_obj_tag(v___x_845_) == 1)
{
lean_object* v_val_858_; uint8_t v___x_859_; 
v_val_858_ = lean_ctor_get(v___x_845_, 0);
lean_inc(v_val_858_);
lean_dec_ref_known(v___x_845_, 1);
v___x_859_ = lean_string_dec_eq(v_val_858_, v_url_805_);
if (v___x_859_ == 0)
{
lean_object* v___x_860_; 
v___x_860_ = lean_io_realpath(v_val_858_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_object* v_a_861_; lean_object* v___x_862_; 
v_a_861_ = lean_ctor_get(v___x_860_, 0);
lean_inc(v_a_861_);
lean_dec_ref_known(v___x_860_, 1);
lean_inc_ref(v_url_805_);
v___x_862_ = lean_io_realpath(v_url_805_);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_object* v_a_863_; uint8_t v___x_864_; 
v_a_863_ = lean_ctor_get(v___x_862_, 0);
lean_inc(v_a_863_);
lean_dec_ref_known(v___x_862_, 1);
v___x_864_ = lean_string_dec_eq(v_a_861_, v_a_863_);
lean_dec(v_a_863_);
lean_dec(v_a_861_);
v_val_848_ = v___x_864_;
goto v___jp_847_;
}
else
{
lean_dec_ref_known(v___x_862_, 1);
lean_dec(v_a_861_);
v_val_848_ = v___x_859_;
goto v___jp_847_;
}
}
else
{
lean_dec_ref_known(v___x_860_, 1);
v_val_848_ = v___x_859_;
goto v___jp_847_;
}
}
else
{
lean_dec(v_val_858_);
v_val_848_ = v___x_859_;
goto v___jp_847_;
}
}
else
{
uint8_t v___x_865_; 
lean_dec(v___x_845_);
v___x_865_ = 0;
v_val_848_ = v___x_865_;
goto v___jp_847_;
}
v___jp_808_:
{
if (v_a_809_ == 0)
{
uint8_t v___x_810_; 
v___x_810_ = l_System_Platform_isWindows;
if (v___x_810_ == 0)
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; uint8_t v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_811_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__0));
lean_inc_ref(v_name_803_);
v___x_812_ = lean_string_append(v_name_803_, v___x_811_);
v___x_813_ = lean_string_append(v___x_812_, v_repo_804_);
v___x_814_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__1));
v___x_815_ = lean_string_append(v___x_813_, v___x_814_);
v___x_816_ = 1;
v___x_817_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_817_, 0, v___x_815_);
lean_ctor_set_uint8(v___x_817_, sizeof(void*)*1, v___x_816_);
lean_inc_ref(v_a_802_);
v___x_818_ = lean_apply_2(v_a_802_, v___x_817_, lean_box(0));
v___x_819_ = l_IO_FS_removeDirAll(v_repo_804_);
if (lean_obj_tag(v___x_819_) == 0)
{
lean_object* v___x_820_; 
lean_dec_ref_known(v___x_819_, 1);
v___x_820_ = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(v_a_802_, v_name_803_, v_repo_804_, v_url_805_, v_rev_x3f_806_);
return v___x_820_;
}
else
{
lean_object* v_a_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_833_; 
lean_dec(v_rev_x3f_806_);
lean_dec_ref(v_url_805_);
lean_dec_ref(v_repo_804_);
lean_dec_ref(v_name_803_);
v_a_821_ = lean_ctor_get(v___x_819_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_819_);
if (v_isSharedCheck_833_ == 0)
{
v___x_823_ = v___x_819_;
v_isShared_824_ = v_isSharedCheck_833_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_a_821_);
lean_dec(v___x_819_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_833_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_825_; uint8_t v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_831_; 
v___x_825_ = lean_io_error_to_string(v_a_821_);
v___x_826_ = 3;
v___x_827_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_827_, 0, v___x_825_);
lean_ctor_set_uint8(v___x_827_, sizeof(void*)*1, v___x_826_);
lean_inc_ref(v_a_802_);
v___x_828_ = lean_apply_2(v_a_802_, v___x_827_, lean_box(0));
v___x_829_ = lean_box(0);
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 0, v___x_829_);
v___x_831_ = v___x_823_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v___x_829_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
}
}
else
{
lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; uint8_t v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
lean_dec_ref(v_url_805_);
v___x_834_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__2));
lean_inc_ref(v_name_803_);
v___x_835_ = lean_string_append(v_name_803_, v___x_834_);
v___x_836_ = lean_string_append(v___x_835_, v_repo_804_);
v___x_837_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__3));
v___x_838_ = lean_string_append(v___x_836_, v___x_837_);
v___x_839_ = 1;
v___x_840_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_840_, 0, v___x_838_);
lean_ctor_set_uint8(v___x_840_, sizeof(void*)*1, v___x_839_);
lean_inc_ref(v_a_802_);
v___x_841_ = lean_apply_2(v_a_802_, v___x_840_, lean_box(0));
v___x_842_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(v_a_802_, v_name_803_, v_repo_804_, v_rev_x3f_806_);
return v___x_842_;
}
}
else
{
lean_object* v___x_843_; 
lean_dec_ref(v_url_805_);
v___x_843_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(v_a_802_, v_name_803_, v_repo_804_, v_rev_x3f_806_);
return v___x_843_;
}
}
v___jp_847_:
{
uint8_t v___x_849_; 
v___x_849_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__6);
if (v___x_849_ == 0)
{
v_a_809_ = v_val_848_;
goto v___jp_808_;
}
else
{
lean_object* v___x_850_; uint8_t v___x_851_; 
v___x_850_ = lean_box(0);
v___x_851_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__7);
if (v___x_851_ == 0)
{
if (v___x_849_ == 0)
{
v_a_809_ = v_val_848_;
goto v___jp_808_;
}
else
{
size_t v___x_852_; size_t v___x_853_; lean_object* v___x_854_; 
v___x_852_ = ((size_t)0ULL);
v___x_853_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8);
v___x_854_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_846_, v___x_852_, v___x_853_, v___x_850_, v_a_802_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_dec_ref_known(v___x_854_, 1);
v_a_809_ = v_val_848_;
goto v___jp_808_;
}
else
{
lean_dec(v_rev_x3f_806_);
lean_dec_ref(v_url_805_);
lean_dec_ref(v_repo_804_);
lean_dec_ref(v_name_803_);
return v___x_854_;
}
}
}
else
{
size_t v___x_855_; size_t v___x_856_; lean_object* v___x_857_; 
v___x_855_ = ((size_t)0ULL);
v___x_856_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8);
v___x_857_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_846_, v___x_855_, v___x_856_, v___x_850_, v_a_802_);
if (lean_obj_tag(v___x_857_) == 0)
{
lean_dec_ref_known(v___x_857_, 1);
v_a_809_ = v_val_848_;
goto v___jp_808_;
}
else
{
lean_dec(v_rev_x3f_806_);
lean_dec_ref(v_url_805_);
lean_dec_ref(v_repo_804_);
lean_dec_ref(v_name_803_);
return v___x_857_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0___boxed(lean_object* v_a_866_, lean_object* v_name_867_, lean_object* v_repo_868_, lean_object* v_url_869_, lean_object* v_rev_x3f_870_, lean_object* v_a_871_){
_start:
{
lean_object* v_res_872_; 
v_res_872_ = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_866_, v_name_867_, v_repo_868_, v_url_869_, v_rev_x3f_870_);
lean_dec_ref(v_a_866_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo(lean_object* v_name_873_, lean_object* v_repo_874_, lean_object* v_url_875_, lean_object* v_rev_x3f_876_, lean_object* v_a_877_){
_start:
{
uint8_t v___x_879_; lean_object* v___x_883_; uint8_t v___x_884_; 
v___x_879_ = l_System_FilePath_isDir(v_repo_874_);
v___x_883_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0));
v___x_884_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__6);
if (v___x_884_ == 0)
{
goto v___jp_880_;
}
else
{
lean_object* v___x_885_; uint8_t v___x_886_; 
v___x_885_ = lean_box(0);
v___x_886_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__7);
if (v___x_886_ == 0)
{
if (v___x_884_ == 0)
{
goto v___jp_880_;
}
else
{
size_t v___x_887_; size_t v___x_888_; lean_object* v___x_889_; 
v___x_887_ = ((size_t)0ULL);
v___x_888_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8);
v___x_889_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_883_, v___x_887_, v___x_888_, v___x_885_, v_a_877_);
if (lean_obj_tag(v___x_889_) == 0)
{
lean_dec_ref_known(v___x_889_, 1);
goto v___jp_880_;
}
else
{
lean_dec(v_rev_x3f_876_);
lean_dec_ref(v_url_875_);
lean_dec_ref(v_repo_874_);
lean_dec_ref(v_name_873_);
return v___x_889_;
}
}
}
else
{
size_t v___x_890_; size_t v___x_891_; lean_object* v___x_892_; 
v___x_890_ = ((size_t)0ULL);
v___x_891_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8);
v___x_892_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_883_, v___x_890_, v___x_891_, v___x_885_, v_a_877_);
if (lean_obj_tag(v___x_892_) == 0)
{
lean_dec_ref_known(v___x_892_, 1);
goto v___jp_880_;
}
else
{
lean_dec(v_rev_x3f_876_);
lean_dec_ref(v_url_875_);
lean_dec_ref(v_repo_874_);
lean_dec_ref(v_name_873_);
return v___x_892_;
}
}
}
v___jp_880_:
{
if (v___x_879_ == 0)
{
lean_object* v___x_881_; 
v___x_881_ = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(v_a_877_, v_name_873_, v_repo_874_, v_url_875_, v_rev_x3f_876_);
return v___x_881_;
}
else
{
lean_object* v___x_882_; 
v___x_882_ = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_877_, v_name_873_, v_repo_874_, v_url_875_, v_rev_x3f_876_);
return v___x_882_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___boxed(lean_object* v_name_893_, lean_object* v_repo_894_, lean_object* v_url_895_, lean_object* v_rev_x3f_896_, lean_object* v_a_897_, lean_object* v_a_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo(v_name_893_, v_repo_894_, v_url_895_, v_rev_x3f_896_, v_a_897_);
lean_dec_ref(v_a_897_);
return v_res_899_;
}
}
static lean_object* _init_l_Lake_instInhabitedMaterializedDep_default___closed__4(void){
_start:
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_906_ = l_Lake_instInhabitedPackageEntry_default;
v___x_907_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__3));
v___x_908_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___x_909_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_909_, 0, v___x_908_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
lean_ctor_set(v___x_909_, 2, v___x_908_);
lean_ctor_set(v___x_909_, 3, v___x_907_);
lean_ctor_set(v___x_909_, 4, v___x_906_);
return v___x_909_;
}
}
static lean_object* _init_l_Lake_instInhabitedMaterializedDep_default(void){
_start:
{
lean_object* v___x_910_; 
v___x_910_ = lean_obj_once(&l_Lake_instInhabitedMaterializedDep_default___closed__4, &l_Lake_instInhabitedMaterializedDep_default___closed__4_once, _init_l_Lake_instInhabitedMaterializedDep_default___closed__4);
return v___x_910_;
}
}
static lean_object* _init_l_Lake_instInhabitedMaterializedDep(void){
_start:
{
lean_object* v___x_911_; 
v___x_911_ = l_Lake_instInhabitedMaterializedDep_default;
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_name(lean_object* v_self_912_){
_start:
{
lean_object* v_manifestEntry_913_; lean_object* v_name_914_; 
v_manifestEntry_913_ = lean_ctor_get(v_self_912_, 4);
v_name_914_ = lean_ctor_get(v_manifestEntry_913_, 0);
lean_inc(v_name_914_);
return v_name_914_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_name___boxed(lean_object* v_self_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l_Lake_MaterializedDep_name(v_self_915_);
lean_dec_ref(v_self_915_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_prettyName(lean_object* v_self_917_){
_start:
{
lean_object* v_manifestEntry_918_; lean_object* v_name_919_; uint8_t v___x_920_; lean_object* v___x_921_; 
v_manifestEntry_918_ = lean_ctor_get(v_self_917_, 4);
lean_inc_ref(v_manifestEntry_918_);
lean_dec_ref(v_self_917_);
v_name_919_ = lean_ctor_get(v_manifestEntry_918_, 0);
lean_inc(v_name_919_);
lean_dec_ref(v_manifestEntry_918_);
v___x_920_ = 0;
v___x_921_ = l_Lean_Name_toString(v_name_919_, v___x_920_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_scope(lean_object* v_self_922_){
_start:
{
lean_object* v_manifestEntry_923_; lean_object* v_scope_924_; 
v_manifestEntry_923_ = lean_ctor_get(v_self_922_, 4);
v_scope_924_ = lean_ctor_get(v_manifestEntry_923_, 1);
lean_inc_ref(v_scope_924_);
return v_scope_924_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_scope___boxed(lean_object* v_self_925_){
_start:
{
lean_object* v_res_926_; 
v_res_926_ = l_Lake_MaterializedDep_scope(v_self_925_);
lean_dec_ref(v_self_925_);
return v_res_926_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relManifestFile_x3f(lean_object* v_self_927_){
_start:
{
lean_object* v_manifestEntry_928_; lean_object* v_manifestFile_x3f_929_; 
v_manifestEntry_928_ = lean_ctor_get(v_self_927_, 4);
v_manifestFile_x3f_929_ = lean_ctor_get(v_manifestEntry_928_, 3);
lean_inc(v_manifestFile_x3f_929_);
return v_manifestFile_x3f_929_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relManifestFile_x3f___boxed(lean_object* v_self_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l_Lake_MaterializedDep_relManifestFile_x3f(v_self_930_);
lean_dec_ref(v_self_930_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relManifestFile(lean_object* v_self_932_){
_start:
{
lean_object* v_manifestEntry_933_; lean_object* v_manifestFile_x3f_934_; 
v_manifestEntry_933_ = lean_ctor_get(v_self_932_, 4);
v_manifestFile_x3f_934_ = lean_ctor_get(v_manifestEntry_933_, 3);
if (lean_obj_tag(v_manifestFile_x3f_934_) == 0)
{
lean_object* v___x_935_; 
v___x_935_ = l_Lake_defaultManifestFile;
return v___x_935_;
}
else
{
lean_object* v_val_936_; 
v_val_936_ = lean_ctor_get(v_manifestFile_x3f_934_, 0);
lean_inc(v_val_936_);
return v_val_936_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relManifestFile___boxed(lean_object* v_self_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_Lake_MaterializedDep_relManifestFile(v_self_937_);
lean_dec_ref(v_self_937_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_manifestFile(lean_object* v_self_939_){
_start:
{
lean_object* v_manifestEntry_940_; lean_object* v_manifestFile_x3f_941_; 
v_manifestEntry_940_ = lean_ctor_get(v_self_939_, 4);
v_manifestFile_x3f_941_ = lean_ctor_get(v_manifestEntry_940_, 3);
if (lean_obj_tag(v_manifestFile_x3f_941_) == 0)
{
lean_object* v_pkgDir_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
v_pkgDir_942_ = lean_ctor_get(v_self_939_, 0);
lean_inc_ref(v_pkgDir_942_);
lean_dec_ref(v_self_939_);
v___x_943_ = l_Lake_defaultManifestFile;
v___x_944_ = l_Lake_joinRelative(v_pkgDir_942_, v___x_943_);
return v___x_944_;
}
else
{
lean_object* v_pkgDir_945_; lean_object* v_val_946_; lean_object* v___x_947_; 
lean_inc_ref(v_manifestFile_x3f_941_);
v_pkgDir_945_ = lean_ctor_get(v_self_939_, 0);
lean_inc_ref(v_pkgDir_945_);
lean_dec_ref(v_self_939_);
v_val_946_ = lean_ctor_get(v_manifestFile_x3f_941_, 0);
lean_inc(v_val_946_);
lean_dec_ref_known(v_manifestFile_x3f_941_, 1);
v___x_947_ = l_Lake_joinRelative(v_pkgDir_945_, v_val_946_);
return v___x_947_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relConfigFile(lean_object* v_self_948_){
_start:
{
lean_object* v_manifestEntry_949_; lean_object* v_configFile_950_; 
v_manifestEntry_949_ = lean_ctor_get(v_self_948_, 4);
v_configFile_950_ = lean_ctor_get(v_manifestEntry_949_, 2);
lean_inc_ref(v_configFile_950_);
return v_configFile_950_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relConfigFile___boxed(lean_object* v_self_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l_Lake_MaterializedDep_relConfigFile(v_self_951_);
lean_dec_ref(v_self_951_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_configFile(lean_object* v_self_953_){
_start:
{
lean_object* v_manifestEntry_954_; lean_object* v_pkgDir_955_; lean_object* v_configFile_956_; lean_object* v___x_957_; 
v_manifestEntry_954_ = lean_ctor_get(v_self_953_, 4);
lean_inc_ref(v_manifestEntry_954_);
v_pkgDir_955_ = lean_ctor_get(v_self_953_, 0);
lean_inc_ref(v_pkgDir_955_);
lean_dec_ref(v_self_953_);
v_configFile_956_ = lean_ctor_get(v_manifestEntry_954_, 2);
lean_inc_ref(v_configFile_956_);
lean_dec_ref(v_manifestEntry_954_);
v___x_957_ = l_Lake_joinRelative(v_pkgDir_955_, v_configFile_956_);
return v___x_957_;
}
}
LEAN_EXPORT uint8_t l_Lake_MaterializedDep_fixedToolchain(lean_object* v_self_958_){
_start:
{
lean_object* v_manifest_x3f_959_; 
v_manifest_x3f_959_ = lean_ctor_get(v_self_958_, 3);
if (lean_obj_tag(v_manifest_x3f_959_) == 1)
{
lean_object* v_a_960_; uint8_t v_fixedToolchain_961_; 
v_a_960_ = lean_ctor_get(v_manifest_x3f_959_, 0);
v_fixedToolchain_961_ = lean_ctor_get_uint8(v_a_960_, sizeof(void*)*4);
return v_fixedToolchain_961_;
}
else
{
uint8_t v___x_962_; 
v___x_962_ = 0;
return v___x_962_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_fixedToolchain___boxed(lean_object* v_self_963_){
_start:
{
uint8_t v_res_964_; lean_object* v_r_965_; 
v_res_964_ = l_Lake_MaterializedDep_fixedToolchain(v_self_963_);
lean_dec_ref(v_self_963_);
v_r_965_ = lean_box(v_res_964_);
return v_r_965_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed(lean_object* v_dep_974_){
_start:
{
lean_object* v_name_975_; lean_object* v_scope_976_; lean_object* v_version_977_; lean_object* v_fst_979_; lean_object* v_snd_980_; 
v_name_975_ = lean_ctor_get(v_dep_974_, 0);
lean_inc(v_name_975_);
v_scope_976_ = lean_ctor_get(v_dep_974_, 1);
lean_inc_ref(v_scope_976_);
v_version_977_ = lean_ctor_get(v_dep_974_, 2);
lean_inc(v_version_977_);
lean_dec_ref(v_dep_974_);
switch(lean_obj_tag(v_version_977_))
{
case 0:
{
lean_object* v___x_1003_; 
v___x_1003_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v_fst_979_ = v___x_1003_;
v_snd_980_ = v___x_1003_;
goto v___jp_978_;
}
case 1:
{
lean_object* v_rev_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1019_; 
v_rev_1004_ = lean_ctor_get(v_version_977_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v_version_977_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1006_ = v_version_977_;
v_isShared_1007_ = v_isSharedCheck_1019_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_rev_1004_);
lean_dec(v_version_977_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1019_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1011_; 
v___x_1008_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__5));
v___x_1009_ = l_String_quote(v_rev_1004_);
if (v_isShared_1007_ == 0)
{
lean_ctor_set_tag(v___x_1006_, 3);
lean_ctor_set(v___x_1006_, 0, v___x_1009_);
v___x_1011_ = v___x_1006_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v___x_1009_);
v___x_1011_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1012_ = l_Std_Format_defWidth;
v___x_1013_ = lean_unsigned_to_nat(0u);
v___x_1014_ = l_Std_Format_pretty(v___x_1011_, v___x_1012_, v___x_1013_, v___x_1013_);
v___x_1015_ = lean_string_append(v___x_1008_, v___x_1014_);
v___x_1016_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__6));
v___x_1017_ = lean_string_append(v___x_1016_, v___x_1014_);
lean_dec_ref(v___x_1014_);
v_fst_979_ = v___x_1015_;
v_snd_980_ = v___x_1017_;
goto v___jp_978_;
}
}
}
default: 
{
lean_object* v_ver_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1036_; 
v_ver_1020_ = lean_ctor_get(v_version_977_, 0);
v_isSharedCheck_1036_ = !lean_is_exclusive(v_version_977_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1022_ = v_version_977_;
v_isShared_1023_ = v_isSharedCheck_1036_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_ver_1020_);
lean_dec(v_version_977_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1036_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v_toString_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1028_; 
v_toString_1024_ = lean_ctor_get(v_ver_1020_, 0);
lean_inc_ref(v_toString_1024_);
lean_dec_ref(v_ver_1020_);
v___x_1025_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__5));
v___x_1026_ = l_String_quote(v_toString_1024_);
if (v_isShared_1023_ == 0)
{
lean_ctor_set_tag(v___x_1022_, 3);
lean_ctor_set(v___x_1022_, 0, v___x_1026_);
v___x_1028_ = v___x_1022_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v___x_1026_);
v___x_1028_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1029_ = l_Std_Format_defWidth;
v___x_1030_ = lean_unsigned_to_nat(0u);
v___x_1031_ = l_Std_Format_pretty(v___x_1028_, v___x_1029_, v___x_1030_, v___x_1030_);
v___x_1032_ = lean_string_append(v___x_1025_, v___x_1031_);
v___x_1033_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__7));
v___x_1034_ = lean_string_append(v___x_1033_, v___x_1031_);
lean_dec_ref(v___x_1031_);
v_fst_979_ = v___x_1032_;
v_snd_980_ = v___x_1034_;
goto v___jp_978_;
}
}
}
}
v___jp_978_:
{
lean_object* v___x_981_; lean_object* v___x_982_; uint8_t v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_981_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
lean_inc_ref(v_scope_976_);
v___x_982_ = lean_string_append(v_scope_976_, v___x_981_);
v___x_983_ = 0;
v___x_984_ = l_Lean_Name_toString(v_name_975_, v___x_983_);
v___x_985_ = lean_string_append(v___x_982_, v___x_984_);
v___x_986_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__1));
v___x_987_ = lean_string_append(v___x_985_, v___x_986_);
v___x_988_ = lean_string_append(v___x_987_, v_scope_976_);
v___x_989_ = lean_string_append(v___x_988_, v___x_981_);
v___x_990_ = lean_string_append(v___x_989_, v___x_984_);
v___x_991_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__2));
v___x_992_ = lean_string_append(v___x_990_, v___x_991_);
v___x_993_ = lean_string_append(v___x_992_, v_fst_979_);
lean_dec_ref(v_fst_979_);
v___x_994_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__3));
v___x_995_ = lean_string_append(v___x_993_, v___x_994_);
v___x_996_ = lean_string_append(v___x_995_, v_scope_976_);
lean_dec_ref(v_scope_976_);
v___x_997_ = lean_string_append(v___x_996_, v___x_981_);
v___x_998_ = lean_string_append(v___x_997_, v___x_984_);
lean_dec_ref(v___x_984_);
v___x_999_ = lean_string_append(v___x_998_, v___x_991_);
v___x_1000_ = lean_string_append(v___x_999_, v_snd_980_);
lean_dec_ref(v_snd_980_);
v___x_1001_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__4));
v___x_1002_ = lean_string_append(v___x_1000_, v___x_1001_);
return v___x_1002_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___lam__0(lean_object* v_x_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; 
lean_inc_ref(v___y_1039_);
v___x_1041_ = lean_apply_2(v___y_1039_, v___y_1038_, lean_box(0));
v___x_1042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1041_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___lam__0___boxed(lean_object* v_x_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___lam__0(v_x_1043_, v___y_1044_, v___y_1045_);
lean_dec_ref(v___y_1045_);
return v_res_1047_;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0(void){
_start:
{
lean_object* v___x_1048_; 
v___x_1048_ = l_instMonadEIO(lean_box(0));
return v___x_1048_;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1(void){
_start:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1049_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0, &l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0_once, _init_l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0);
v___x_1050_ = l_ReaderT_instMonad___redArg(v___x_1049_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep(lean_object* v_dep_1053_, uint8_t v_inherited_1054_, lean_object* v_wsDir_1055_, lean_object* v_name_1056_, lean_object* v_relPkgDir_1057_, lean_object* v_remoteUrl_1058_, lean_object* v_src_1059_, lean_object* v_a_1060_){
_start:
{
lean_object* v___y_1063_; lean_object* v_a_1064_; lean_object* v_pkgDir_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___f_1084_; lean_object* v___y_1086_; lean_object* v___y_1087_; lean_object* v___y_1088_; lean_object* v___y_1089_; lean_object* v_val_1090_; lean_object* v_a_1120_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v_val_1154_; lean_object* v___x_1182_; uint8_t v___x_1183_; 
lean_inc_ref(v_relPkgDir_1057_);
v_pkgDir_1081_ = l_Lake_joinRelative(v_wsDir_1055_, v_relPkgDir_1057_);
v___x_1082_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1, &l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1_once, _init_l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1);
lean_inc_ref(v_pkgDir_1081_);
v___x_1083_ = l_Lake_resolvePath(v_pkgDir_1081_);
v___f_1084_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__2));
v___x_1151_ = lean_unsigned_to_nat(0u);
v___x_1152_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0));
v___x_1182_ = lean_string_utf8_byte_size(v___x_1083_);
v___x_1183_ = lean_nat_dec_eq(v___x_1182_, v___x_1151_);
if (v___x_1183_ == 0)
{
lean_object* v___x_1184_; 
v___x_1184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1083_);
v_val_1154_ = v___x_1184_;
goto v___jp_1153_;
}
else
{
lean_object* v___x_1185_; 
lean_dec_ref(v___x_1083_);
v___x_1185_ = lean_box(0);
v_val_1154_ = v___x_1185_;
goto v___jp_1153_;
}
v___jp_1062_:
{
lean_object* v_name_1065_; lean_object* v_scope_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1077_; 
v_name_1065_ = lean_ctor_get(v_dep_1053_, 0);
v_scope_1066_ = lean_ctor_get(v_dep_1053_, 1);
v_isSharedCheck_1077_ = !lean_is_exclusive(v_dep_1053_);
if (v_isSharedCheck_1077_ == 0)
{
lean_object* v_unused_1078_; lean_object* v_unused_1079_; lean_object* v_unused_1080_; 
v_unused_1078_ = lean_ctor_get(v_dep_1053_, 4);
lean_dec(v_unused_1078_);
v_unused_1079_ = lean_ctor_get(v_dep_1053_, 3);
lean_dec(v_unused_1079_);
v_unused_1080_ = lean_ctor_get(v_dep_1053_, 2);
lean_dec(v_unused_1080_);
v___x_1068_ = v_dep_1053_;
v_isShared_1069_ = v_isSharedCheck_1077_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_scope_1066_);
lean_inc(v_name_1065_);
lean_dec(v_dep_1053_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1077_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1074_; 
v___x_1070_ = l_Lake_defaultConfigFile;
v___x_1071_ = lean_box(0);
v___x_1072_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1072_, 0, v_name_1065_);
lean_ctor_set(v___x_1072_, 1, v_scope_1066_);
lean_ctor_set(v___x_1072_, 2, v___x_1070_);
lean_ctor_set(v___x_1072_, 3, v___x_1071_);
lean_ctor_set(v___x_1072_, 4, v_src_1059_);
lean_ctor_set_uint8(v___x_1072_, sizeof(void*)*5, v_inherited_1054_);
if (v_isShared_1069_ == 0)
{
lean_ctor_set(v___x_1068_, 4, v___x_1072_);
lean_ctor_set(v___x_1068_, 3, v_a_1064_);
lean_ctor_set(v___x_1068_, 2, v_remoteUrl_1058_);
lean_ctor_set(v___x_1068_, 1, v_relPkgDir_1057_);
lean_ctor_set(v___x_1068_, 0, v___y_1063_);
v___x_1074_ = v___x_1068_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v___y_1063_);
lean_ctor_set(v_reuseFailAlloc_1076_, 1, v_relPkgDir_1057_);
lean_ctor_set(v_reuseFailAlloc_1076_, 2, v_remoteUrl_1058_);
lean_ctor_set(v_reuseFailAlloc_1076_, 3, v_a_1064_);
lean_ctor_set(v_reuseFailAlloc_1076_, 4, v___x_1072_);
v___x_1074_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
lean_object* v___x_1075_; 
v___x_1075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1074_);
return v___x_1075_;
}
}
}
v___jp_1085_:
{
lean_object* v___x_1091_; uint8_t v___x_1092_; 
v___x_1091_ = lean_array_get_size(v___y_1086_);
v___x_1092_ = lean_nat_dec_lt(v___y_1088_, v___x_1091_);
if (v___x_1092_ == 0)
{
lean_dec_ref(v___y_1087_);
v___y_1063_ = v___y_1089_;
v_a_1064_ = v_val_1090_;
goto v___jp_1062_;
}
else
{
lean_object* v___x_1093_; uint8_t v___x_1094_; 
v___x_1093_ = lean_box(0);
v___x_1094_ = lean_nat_dec_le(v___x_1091_, v___x_1091_);
if (v___x_1094_ == 0)
{
if (v___x_1092_ == 0)
{
lean_dec_ref(v___y_1087_);
v___y_1063_ = v___y_1089_;
v_a_1064_ = v_val_1090_;
goto v___jp_1062_;
}
else
{
size_t v___x_1095_; size_t v___x_1096_; lean_object* v___x_2388__overap_1097_; lean_object* v___x_1098_; 
v___x_1095_ = ((size_t)0ULL);
v___x_1096_ = lean_usize_of_nat(v___x_1091_);
lean_inc_ref(v___y_1086_);
v___x_2388__overap_1097_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___y_1087_, v___f_1084_, v___y_1086_, v___x_1095_, v___x_1096_, v___x_1093_);
lean_inc_ref(v_a_1060_);
v___x_1098_ = lean_apply_2(v___x_2388__overap_1097_, v_a_1060_, lean_box(0));
if (lean_obj_tag(v___x_1098_) == 0)
{
lean_dec_ref_known(v___x_1098_, 1);
v___y_1063_ = v___y_1089_;
v_a_1064_ = v_val_1090_;
goto v___jp_1062_;
}
else
{
lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1106_; 
lean_dec_ref(v_val_1090_);
lean_dec_ref(v___y_1089_);
lean_dec_ref(v_src_1059_);
lean_dec_ref(v_remoteUrl_1058_);
lean_dec_ref(v_relPkgDir_1057_);
lean_dec_ref(v_dep_1053_);
v_a_1099_ = lean_ctor_get(v___x_1098_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1101_ = v___x_1098_;
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_dec(v___x_1098_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1104_; 
if (v_isShared_1102_ == 0)
{
v___x_1104_ = v___x_1101_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_a_1099_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
}
}
}
else
{
size_t v___x_1107_; size_t v___x_1108_; lean_object* v___x_2398__overap_1109_; lean_object* v___x_1110_; 
v___x_1107_ = ((size_t)0ULL);
v___x_1108_ = lean_usize_of_nat(v___x_1091_);
lean_inc_ref(v___y_1086_);
v___x_2398__overap_1109_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___y_1087_, v___f_1084_, v___y_1086_, v___x_1107_, v___x_1108_, v___x_1093_);
lean_inc_ref(v_a_1060_);
v___x_1110_ = lean_apply_2(v___x_2398__overap_1109_, v_a_1060_, lean_box(0));
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_dec_ref_known(v___x_1110_, 1);
v___y_1063_ = v___y_1089_;
v_a_1064_ = v_val_1090_;
goto v___jp_1062_;
}
else
{
lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1118_; 
lean_dec_ref(v_val_1090_);
lean_dec_ref(v___y_1089_);
lean_dec_ref(v_src_1059_);
lean_dec_ref(v_remoteUrl_1058_);
lean_dec_ref(v_relPkgDir_1057_);
lean_dec_ref(v_dep_1053_);
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
return v___x_1116_;
}
}
}
}
}
}
v___jp_1119_:
{
if (lean_obj_tag(v_a_1120_) == 1)
{
lean_object* v_val_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
lean_dec_ref(v_pkgDir_1081_);
lean_dec_ref(v_name_1056_);
v_val_1121_ = lean_ctor_get(v_a_1120_, 0);
lean_inc_n(v_val_1121_, 2);
lean_dec_ref_known(v_a_1120_, 1);
v___x_1122_ = l_Lake_defaultManifestFile;
v___x_1123_ = l_Lake_joinRelative(v_val_1121_, v___x_1122_);
v___x_1124_ = lean_unsigned_to_nat(0u);
v___x_1125_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0));
v___x_1126_ = l_Lake_Manifest_load(v___x_1123_);
if (lean_obj_tag(v___x_1126_) == 0)
{
lean_object* v_a_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1134_; 
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
lean_ctor_set_tag(v___x_1129_, 1);
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
v___y_1086_ = v___x_1125_;
v___y_1087_ = v___x_1082_;
v___y_1088_ = v___x_1124_;
v___y_1089_ = v_val_1121_;
v_val_1090_ = v___x_1132_;
goto v___jp_1085_;
}
}
}
else
{
lean_object* v_a_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1142_; 
v_a_1135_ = lean_ctor_get(v___x_1126_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1137_ = v___x_1126_;
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_a_1135_);
lean_dec(v___x_1126_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1140_; 
if (v_isShared_1138_ == 0)
{
lean_ctor_set_tag(v___x_1137_, 0);
v___x_1140_ = v___x_1137_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_a_1135_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
v___y_1086_ = v___x_1125_;
v___y_1087_ = v___x_1082_;
v___y_1088_ = v___x_1124_;
v___y_1089_ = v_val_1121_;
v_val_1090_ = v___x_1140_;
goto v___jp_1085_;
}
}
}
}
else
{
lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; uint8_t v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; 
lean_dec(v_a_1120_);
lean_dec_ref(v_src_1059_);
lean_dec_ref(v_remoteUrl_1058_);
lean_dec_ref(v_relPkgDir_1057_);
lean_dec_ref(v_dep_1053_);
v___x_1143_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__3));
v___x_1144_ = lean_string_append(v_name_1056_, v___x_1143_);
v___x_1145_ = lean_string_append(v___x_1144_, v_pkgDir_1081_);
lean_dec_ref(v_pkgDir_1081_);
v___x_1146_ = 3;
v___x_1147_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1147_, 0, v___x_1145_);
lean_ctor_set_uint8(v___x_1147_, sizeof(void*)*1, v___x_1146_);
lean_inc_ref(v_a_1060_);
v___x_1148_ = lean_apply_2(v_a_1060_, v___x_1147_, lean_box(0));
v___x_1149_ = lean_box(0);
v___x_1150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1149_);
return v___x_1150_;
}
}
v___jp_1153_:
{
uint8_t v___x_1155_; 
v___x_1155_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__6);
if (v___x_1155_ == 0)
{
v_a_1120_ = v_val_1154_;
goto v___jp_1119_;
}
else
{
lean_object* v___x_1156_; uint8_t v___x_1157_; 
v___x_1156_ = lean_box(0);
v___x_1157_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__7);
if (v___x_1157_ == 0)
{
if (v___x_1155_ == 0)
{
v_a_1120_ = v_val_1154_;
goto v___jp_1119_;
}
else
{
size_t v___x_1158_; size_t v___x_1159_; lean_object* v___x_2450__overap_1160_; lean_object* v___x_1161_; 
v___x_1158_ = ((size_t)0ULL);
v___x_1159_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8);
v___x_2450__overap_1160_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1082_, v___f_1084_, v___x_1152_, v___x_1158_, v___x_1159_, v___x_1156_);
lean_inc_ref(v_a_1060_);
v___x_1161_ = lean_apply_2(v___x_2450__overap_1160_, v_a_1060_, lean_box(0));
if (lean_obj_tag(v___x_1161_) == 0)
{
lean_dec_ref_known(v___x_1161_, 1);
v_a_1120_ = v_val_1154_;
goto v___jp_1119_;
}
else
{
lean_object* v_a_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1169_; 
lean_dec(v_val_1154_);
lean_dec_ref(v_pkgDir_1081_);
lean_dec_ref(v_src_1059_);
lean_dec_ref(v_remoteUrl_1058_);
lean_dec_ref(v_relPkgDir_1057_);
lean_dec_ref(v_name_1056_);
lean_dec_ref(v_dep_1053_);
v_a_1162_ = lean_ctor_get(v___x_1161_, 0);
v_isSharedCheck_1169_ = !lean_is_exclusive(v___x_1161_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_1164_ = v___x_1161_;
v_isShared_1165_ = v_isSharedCheck_1169_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_a_1162_);
lean_dec(v___x_1161_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1169_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1167_; 
if (v_isShared_1165_ == 0)
{
v___x_1167_ = v___x_1164_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v_a_1162_);
v___x_1167_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
return v___x_1167_;
}
}
}
}
}
else
{
size_t v___x_1170_; size_t v___x_1171_; lean_object* v___x_2460__overap_1172_; lean_object* v___x_1173_; 
v___x_1170_ = ((size_t)0ULL);
v___x_1171_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8);
v___x_2460__overap_1172_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1082_, v___f_1084_, v___x_1152_, v___x_1170_, v___x_1171_, v___x_1156_);
lean_inc_ref(v_a_1060_);
v___x_1173_ = lean_apply_2(v___x_2460__overap_1172_, v_a_1060_, lean_box(0));
if (lean_obj_tag(v___x_1173_) == 0)
{
lean_dec_ref_known(v___x_1173_, 1);
v_a_1120_ = v_val_1154_;
goto v___jp_1119_;
}
else
{
lean_object* v_a_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1181_; 
lean_dec(v_val_1154_);
lean_dec_ref(v_pkgDir_1081_);
lean_dec_ref(v_src_1059_);
lean_dec_ref(v_remoteUrl_1058_);
lean_dec_ref(v_relPkgDir_1057_);
lean_dec_ref(v_name_1056_);
lean_dec_ref(v_dep_1053_);
v_a_1174_ = lean_ctor_get(v___x_1173_, 0);
v_isSharedCheck_1181_ = !lean_is_exclusive(v___x_1173_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1176_ = v___x_1173_;
v_isShared_1177_ = v_isSharedCheck_1181_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_a_1174_);
lean_dec(v___x_1173_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1181_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
lean_object* v___x_1179_; 
if (v_isShared_1177_ == 0)
{
v___x_1179_ = v___x_1176_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_a_1174_);
v___x_1179_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
return v___x_1179_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___boxed(lean_object* v_dep_1186_, lean_object* v_inherited_1187_, lean_object* v_wsDir_1188_, lean_object* v_name_1189_, lean_object* v_relPkgDir_1190_, lean_object* v_remoteUrl_1191_, lean_object* v_src_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_){
_start:
{
uint8_t v_inherited_boxed_1195_; lean_object* v_res_1196_; 
v_inherited_boxed_1195_ = lean_unbox(v_inherited_1187_);
v_res_1196_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep(v_dep_1186_, v_inherited_boxed_1195_, v_wsDir_1188_, v_name_1189_, v_relPkgDir_1190_, v_remoteUrl_1191_, v_src_1192_, v_a_1193_);
lean_dec_ref(v_a_1193_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(lean_object* v_a_1197_, lean_object* v_name_1198_, lean_object* v_repo_1199_, lean_object* v_url_1200_, lean_object* v_rev_x3f_1201_){
_start:
{
uint8_t v___x_1203_; lean_object* v___x_1207_; uint8_t v___x_1208_; 
v___x_1203_ = l_System_FilePath_isDir(v_repo_1199_);
v___x_1207_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0));
v___x_1208_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__6);
if (v___x_1208_ == 0)
{
goto v___jp_1204_;
}
else
{
lean_object* v___x_1209_; uint8_t v___x_1210_; 
v___x_1209_ = lean_box(0);
v___x_1210_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__7);
if (v___x_1210_ == 0)
{
if (v___x_1208_ == 0)
{
goto v___jp_1204_;
}
else
{
size_t v___x_1211_; size_t v___x_1212_; lean_object* v___x_1213_; 
v___x_1211_ = ((size_t)0ULL);
v___x_1212_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8);
v___x_1213_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_1207_, v___x_1211_, v___x_1212_, v___x_1209_, v_a_1197_);
if (lean_obj_tag(v___x_1213_) == 0)
{
lean_dec_ref_known(v___x_1213_, 1);
goto v___jp_1204_;
}
else
{
lean_dec(v_rev_x3f_1201_);
lean_dec_ref(v_url_1200_);
lean_dec_ref(v_repo_1199_);
lean_dec_ref(v_name_1198_);
return v___x_1213_;
}
}
}
else
{
size_t v___x_1214_; size_t v___x_1215_; lean_object* v___x_1216_; 
v___x_1214_ = ((size_t)0ULL);
v___x_1215_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8);
v___x_1216_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_1207_, v___x_1214_, v___x_1215_, v___x_1209_, v_a_1197_);
if (lean_obj_tag(v___x_1216_) == 0)
{
lean_dec_ref_known(v___x_1216_, 1);
goto v___jp_1204_;
}
else
{
lean_dec(v_rev_x3f_1201_);
lean_dec_ref(v_url_1200_);
lean_dec_ref(v_repo_1199_);
lean_dec_ref(v_name_1198_);
return v___x_1216_;
}
}
}
v___jp_1204_:
{
if (v___x_1203_ == 0)
{
lean_object* v___x_1205_; 
v___x_1205_ = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(v_a_1197_, v_name_1198_, v_repo_1199_, v_url_1200_, v_rev_x3f_1201_);
return v___x_1205_;
}
else
{
lean_object* v___x_1206_; 
v___x_1206_ = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1197_, v_name_1198_, v_repo_1199_, v_url_1200_, v_rev_x3f_1201_);
return v___x_1206_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0___boxed(lean_object* v_a_1217_, lean_object* v_name_1218_, lean_object* v_repo_1219_, lean_object* v_url_1220_, lean_object* v_rev_x3f_1221_, lean_object* v_a_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(v_a_1217_, v_name_1218_, v_repo_1219_, v_url_1220_, v_rev_x3f_1221_);
lean_dec_ref(v_a_1217_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit(lean_object* v_dep_1224_, uint8_t v_inherited_1225_, lean_object* v_lakeEnv_1226_, lean_object* v_wsDir_1227_, lean_object* v_name_1228_, lean_object* v_relPkgDir_1229_, lean_object* v_gitUrl_1230_, lean_object* v_remoteUrl_1231_, lean_object* v_inputRev_x3f_1232_, lean_object* v_subDir_x3f_1233_, lean_object* v_a_1234_){
_start:
{
lean_object* v_pkgUrlMap_1239_; lean_object* v_name_1240_; lean_object* v_scope_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1457_; 
v_pkgUrlMap_1239_ = lean_ctor_get(v_lakeEnv_1226_, 5);
v_name_1240_ = lean_ctor_get(v_dep_1224_, 0);
v_scope_1241_ = lean_ctor_get(v_dep_1224_, 1);
v_isSharedCheck_1457_ = !lean_is_exclusive(v_dep_1224_);
if (v_isSharedCheck_1457_ == 0)
{
lean_object* v_unused_1458_; lean_object* v_unused_1459_; lean_object* v_unused_1460_; 
v_unused_1458_ = lean_ctor_get(v_dep_1224_, 4);
lean_dec(v_unused_1458_);
v_unused_1459_ = lean_ctor_get(v_dep_1224_, 3);
lean_dec(v_unused_1459_);
v_unused_1460_ = lean_ctor_get(v_dep_1224_, 2);
lean_dec(v_unused_1460_);
v___x_1243_ = v_dep_1224_;
v_isShared_1244_ = v_isSharedCheck_1457_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_scope_1241_);
lean_inc(v_name_1240_);
lean_dec(v_dep_1224_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1457_;
goto v_resetjp_1242_;
}
v___jp_1236_:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1237_ = lean_box(0);
v___x_1238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1237_);
return v___x_1238_;
}
v_resetjp_1242_:
{
lean_object* v___y_1246_; lean_object* v___y_1247_; lean_object* v___y_1248_; lean_object* v_a_1249_; lean_object* v___y_1258_; lean_object* v___y_1259_; lean_object* v___y_1260_; lean_object* v___y_1261_; lean_object* v___y_1262_; lean_object* v_val_1263_; lean_object* v___y_1291_; lean_object* v___y_1292_; lean_object* v___y_1293_; lean_object* v_a_1294_; lean_object* v___y_1326_; lean_object* v___y_1327_; lean_object* v___y_1328_; lean_object* v___y_1329_; lean_object* v___y_1330_; lean_object* v_val_1331_; lean_object* v___y_1359_; lean_object* v___y_1360_; lean_object* v___y_1361_; lean_object* v___y_1372_; lean_object* v_a_1373_; lean_object* v_gitDir_1376_; lean_object* v___y_1378_; lean_object* v___x_1455_; 
lean_inc_ref(v_relPkgDir_1229_);
lean_inc_ref(v_wsDir_1227_);
v_gitDir_1376_ = l_Lake_joinRelative(v_wsDir_1227_, v_relPkgDir_1229_);
v___x_1455_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgUrlMap_1239_, v_name_1240_);
if (lean_obj_tag(v___x_1455_) == 0)
{
v___y_1378_ = v_gitUrl_1230_;
goto v___jp_1377_;
}
else
{
lean_object* v_val_1456_; 
lean_dec_ref(v_gitUrl_1230_);
v_val_1456_ = lean_ctor_get(v___x_1455_, 0);
lean_inc(v_val_1456_);
lean_dec_ref_known(v___x_1455_, 1);
v___y_1378_ = v_val_1456_;
goto v___jp_1377_;
}
v___jp_1245_:
{
lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1254_; 
v___x_1250_ = l_Lake_defaultConfigFile;
v___x_1251_ = lean_box(0);
v___x_1252_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1252_, 0, v_name_1240_);
lean_ctor_set(v___x_1252_, 1, v_scope_1241_);
lean_ctor_set(v___x_1252_, 2, v___x_1250_);
lean_ctor_set(v___x_1252_, 3, v___x_1251_);
lean_ctor_set(v___x_1252_, 4, v___y_1247_);
lean_ctor_set_uint8(v___x_1252_, sizeof(void*)*5, v_inherited_1225_);
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 4, v___x_1252_);
lean_ctor_set(v___x_1243_, 3, v_a_1249_);
lean_ctor_set(v___x_1243_, 2, v_remoteUrl_1231_);
lean_ctor_set(v___x_1243_, 1, v___y_1248_);
lean_ctor_set(v___x_1243_, 0, v___y_1246_);
v___x_1254_ = v___x_1243_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v___y_1246_);
lean_ctor_set(v_reuseFailAlloc_1256_, 1, v___y_1248_);
lean_ctor_set(v_reuseFailAlloc_1256_, 2, v_remoteUrl_1231_);
lean_ctor_set(v_reuseFailAlloc_1256_, 3, v_a_1249_);
lean_ctor_set(v_reuseFailAlloc_1256_, 4, v___x_1252_);
v___x_1254_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
lean_object* v___x_1255_; 
v___x_1255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1255_, 0, v___x_1254_);
return v___x_1255_;
}
}
v___jp_1257_:
{
lean_object* v___x_1264_; uint8_t v___x_1265_; 
v___x_1264_ = lean_array_get_size(v___y_1258_);
v___x_1265_ = lean_nat_dec_lt(v___y_1261_, v___x_1264_);
if (v___x_1265_ == 0)
{
v___y_1246_ = v___y_1259_;
v___y_1247_ = v___y_1260_;
v___y_1248_ = v___y_1262_;
v_a_1249_ = v_val_1263_;
goto v___jp_1245_;
}
else
{
lean_object* v___x_1266_; uint8_t v___x_1267_; 
v___x_1266_ = lean_box(0);
v___x_1267_ = lean_nat_dec_le(v___x_1264_, v___x_1264_);
if (v___x_1267_ == 0)
{
if (v___x_1265_ == 0)
{
v___y_1246_ = v___y_1259_;
v___y_1247_ = v___y_1260_;
v___y_1248_ = v___y_1262_;
v_a_1249_ = v_val_1263_;
goto v___jp_1245_;
}
else
{
size_t v___x_1268_; size_t v___x_1269_; lean_object* v___x_1270_; 
v___x_1268_ = ((size_t)0ULL);
v___x_1269_ = lean_usize_of_nat(v___x_1264_);
v___x_1270_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_1258_, v___x_1268_, v___x_1269_, v___x_1266_, v_a_1234_);
if (lean_obj_tag(v___x_1270_) == 0)
{
lean_dec_ref_known(v___x_1270_, 1);
v___y_1246_ = v___y_1259_;
v___y_1247_ = v___y_1260_;
v___y_1248_ = v___y_1262_;
v_a_1249_ = v_val_1263_;
goto v___jp_1245_;
}
else
{
lean_object* v_a_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1278_; 
lean_dec_ref(v_val_1263_);
lean_dec_ref(v___y_1262_);
lean_dec_ref(v___y_1260_);
lean_dec_ref(v___y_1259_);
lean_del_object(v___x_1243_);
lean_dec_ref(v_scope_1241_);
lean_dec(v_name_1240_);
lean_dec_ref(v_remoteUrl_1231_);
v_a_1271_ = lean_ctor_get(v___x_1270_, 0);
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1273_ = v___x_1270_;
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_a_1271_);
lean_dec(v___x_1270_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1276_; 
if (v_isShared_1274_ == 0)
{
v___x_1276_ = v___x_1273_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_a_1271_);
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
}
else
{
size_t v___x_1279_; size_t v___x_1280_; lean_object* v___x_1281_; 
v___x_1279_ = ((size_t)0ULL);
v___x_1280_ = lean_usize_of_nat(v___x_1264_);
v___x_1281_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_1258_, v___x_1279_, v___x_1280_, v___x_1266_, v_a_1234_);
if (lean_obj_tag(v___x_1281_) == 0)
{
lean_dec_ref_known(v___x_1281_, 1);
v___y_1246_ = v___y_1259_;
v___y_1247_ = v___y_1260_;
v___y_1248_ = v___y_1262_;
v_a_1249_ = v_val_1263_;
goto v___jp_1245_;
}
else
{
lean_object* v_a_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1289_; 
lean_dec_ref(v_val_1263_);
lean_dec_ref(v___y_1262_);
lean_dec_ref(v___y_1260_);
lean_dec_ref(v___y_1259_);
lean_del_object(v___x_1243_);
lean_dec_ref(v_scope_1241_);
lean_dec(v_name_1240_);
lean_dec_ref(v_remoteUrl_1231_);
v_a_1282_ = lean_ctor_get(v___x_1281_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1284_ = v___x_1281_;
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_a_1282_);
lean_dec(v___x_1281_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___x_1287_; 
if (v_isShared_1285_ == 0)
{
v___x_1287_ = v___x_1284_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_a_1282_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
return v___x_1287_;
}
}
}
}
}
}
v___jp_1290_:
{
if (lean_obj_tag(v_a_1294_) == 1)
{
lean_object* v_val_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
lean_dec_ref(v___y_1291_);
lean_dec_ref(v_name_1228_);
v_val_1295_ = lean_ctor_get(v_a_1294_, 0);
lean_inc_n(v_val_1295_, 2);
lean_dec_ref_known(v_a_1294_, 1);
v___x_1296_ = l_Lake_defaultManifestFile;
v___x_1297_ = l_Lake_joinRelative(v_val_1295_, v___x_1296_);
v___x_1298_ = lean_unsigned_to_nat(0u);
v___x_1299_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0));
v___x_1300_ = l_Lake_Manifest_load(v___x_1297_);
if (lean_obj_tag(v___x_1300_) == 0)
{
lean_object* v_a_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1308_; 
v_a_1301_ = lean_ctor_get(v___x_1300_, 0);
v_isSharedCheck_1308_ = !lean_is_exclusive(v___x_1300_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1303_ = v___x_1300_;
v_isShared_1304_ = v_isSharedCheck_1308_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_a_1301_);
lean_dec(v___x_1300_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1308_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
lean_object* v___x_1306_; 
if (v_isShared_1304_ == 0)
{
lean_ctor_set_tag(v___x_1303_, 1);
v___x_1306_ = v___x_1303_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v_a_1301_);
v___x_1306_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
v___y_1258_ = v___x_1299_;
v___y_1259_ = v_val_1295_;
v___y_1260_ = v___y_1292_;
v___y_1261_ = v___x_1298_;
v___y_1262_ = v___y_1293_;
v_val_1263_ = v___x_1306_;
goto v___jp_1257_;
}
}
}
else
{
lean_object* v_a_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1316_; 
v_a_1309_ = lean_ctor_get(v___x_1300_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1300_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1311_ = v___x_1300_;
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_a_1309_);
lean_dec(v___x_1300_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1314_; 
if (v_isShared_1312_ == 0)
{
lean_ctor_set_tag(v___x_1311_, 0);
v___x_1314_ = v___x_1311_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v_a_1309_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
v___y_1258_ = v___x_1299_;
v___y_1259_ = v_val_1295_;
v___y_1260_ = v___y_1292_;
v___y_1261_ = v___x_1298_;
v___y_1262_ = v___y_1293_;
v_val_1263_ = v___x_1314_;
goto v___jp_1257_;
}
}
}
}
else
{
lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; uint8_t v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
lean_dec(v_a_1294_);
lean_dec_ref(v___y_1293_);
lean_dec_ref(v___y_1292_);
lean_del_object(v___x_1243_);
lean_dec_ref(v_scope_1241_);
lean_dec(v_name_1240_);
lean_dec_ref(v_remoteUrl_1231_);
v___x_1317_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__3));
v___x_1318_ = lean_string_append(v_name_1228_, v___x_1317_);
v___x_1319_ = lean_string_append(v___x_1318_, v___y_1291_);
lean_dec_ref(v___y_1291_);
v___x_1320_ = 3;
v___x_1321_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1321_, 0, v___x_1319_);
lean_ctor_set_uint8(v___x_1321_, sizeof(void*)*1, v___x_1320_);
lean_inc_ref(v_a_1234_);
v___x_1322_ = lean_apply_2(v_a_1234_, v___x_1321_, lean_box(0));
v___x_1323_ = lean_box(0);
v___x_1324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1323_);
return v___x_1324_;
}
}
v___jp_1325_:
{
lean_object* v___x_1332_; uint8_t v___x_1333_; 
v___x_1332_ = lean_array_get_size(v___y_1328_);
v___x_1333_ = lean_nat_dec_lt(v___y_1329_, v___x_1332_);
if (v___x_1333_ == 0)
{
v___y_1291_ = v___y_1326_;
v___y_1292_ = v___y_1327_;
v___y_1293_ = v___y_1330_;
v_a_1294_ = v_val_1331_;
goto v___jp_1290_;
}
else
{
lean_object* v___x_1334_; uint8_t v___x_1335_; 
v___x_1334_ = lean_box(0);
v___x_1335_ = lean_nat_dec_le(v___x_1332_, v___x_1332_);
if (v___x_1335_ == 0)
{
if (v___x_1333_ == 0)
{
v___y_1291_ = v___y_1326_;
v___y_1292_ = v___y_1327_;
v___y_1293_ = v___y_1330_;
v_a_1294_ = v_val_1331_;
goto v___jp_1290_;
}
else
{
size_t v___x_1336_; size_t v___x_1337_; lean_object* v___x_1338_; 
v___x_1336_ = ((size_t)0ULL);
v___x_1337_ = lean_usize_of_nat(v___x_1332_);
v___x_1338_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_1328_, v___x_1336_, v___x_1337_, v___x_1334_, v_a_1234_);
if (lean_obj_tag(v___x_1338_) == 0)
{
lean_dec_ref_known(v___x_1338_, 1);
v___y_1291_ = v___y_1326_;
v___y_1292_ = v___y_1327_;
v___y_1293_ = v___y_1330_;
v_a_1294_ = v_val_1331_;
goto v___jp_1290_;
}
else
{
lean_object* v_a_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1346_; 
lean_dec(v_val_1331_);
lean_dec_ref(v___y_1330_);
lean_dec_ref(v___y_1327_);
lean_dec_ref(v___y_1326_);
lean_del_object(v___x_1243_);
lean_dec_ref(v_scope_1241_);
lean_dec(v_name_1240_);
lean_dec_ref(v_remoteUrl_1231_);
lean_dec_ref(v_name_1228_);
v_a_1339_ = lean_ctor_get(v___x_1338_, 0);
v_isSharedCheck_1346_ = !lean_is_exclusive(v___x_1338_);
if (v_isSharedCheck_1346_ == 0)
{
v___x_1341_ = v___x_1338_;
v_isShared_1342_ = v_isSharedCheck_1346_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_a_1339_);
lean_dec(v___x_1338_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1346_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1344_; 
if (v_isShared_1342_ == 0)
{
v___x_1344_ = v___x_1341_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v_a_1339_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
return v___x_1344_;
}
}
}
}
}
else
{
size_t v___x_1347_; size_t v___x_1348_; lean_object* v___x_1349_; 
v___x_1347_ = ((size_t)0ULL);
v___x_1348_ = lean_usize_of_nat(v___x_1332_);
v___x_1349_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_1328_, v___x_1347_, v___x_1348_, v___x_1334_, v_a_1234_);
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_dec_ref_known(v___x_1349_, 1);
v___y_1291_ = v___y_1326_;
v___y_1292_ = v___y_1327_;
v___y_1293_ = v___y_1330_;
v_a_1294_ = v_val_1331_;
goto v___jp_1290_;
}
else
{
lean_object* v_a_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1357_; 
lean_dec(v_val_1331_);
lean_dec_ref(v___y_1330_);
lean_dec_ref(v___y_1327_);
lean_dec_ref(v___y_1326_);
lean_del_object(v___x_1243_);
lean_dec_ref(v_scope_1241_);
lean_dec(v_name_1240_);
lean_dec_ref(v_remoteUrl_1231_);
lean_dec_ref(v_name_1228_);
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
}
v___jp_1358_:
{
lean_object* v_pkgDir_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; uint8_t v___x_1368_; 
lean_inc_ref(v___y_1361_);
v_pkgDir_1362_ = l_Lake_joinRelative(v_wsDir_1227_, v___y_1361_);
lean_inc_ref(v_pkgDir_1362_);
v___x_1363_ = l_Lake_resolvePath(v_pkgDir_1362_);
v___x_1364_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1364_, 0, v___y_1359_);
lean_ctor_set(v___x_1364_, 1, v___y_1360_);
lean_ctor_set(v___x_1364_, 2, v_inputRev_x3f_1232_);
lean_ctor_set(v___x_1364_, 3, v_subDir_x3f_1233_);
v___x_1365_ = lean_unsigned_to_nat(0u);
v___x_1366_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0));
v___x_1367_ = lean_string_utf8_byte_size(v___x_1363_);
v___x_1368_ = lean_nat_dec_eq(v___x_1367_, v___x_1365_);
if (v___x_1368_ == 0)
{
lean_object* v___x_1369_; 
v___x_1369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1369_, 0, v___x_1363_);
v___y_1326_ = v_pkgDir_1362_;
v___y_1327_ = v___x_1364_;
v___y_1328_ = v___x_1366_;
v___y_1329_ = v___x_1365_;
v___y_1330_ = v___y_1361_;
v_val_1331_ = v___x_1369_;
goto v___jp_1325_;
}
else
{
lean_object* v___x_1370_; 
lean_dec_ref(v___x_1363_);
v___x_1370_ = lean_box(0);
v___y_1326_ = v_pkgDir_1362_;
v___y_1327_ = v___x_1364_;
v___y_1328_ = v___x_1366_;
v___y_1329_ = v___x_1365_;
v___y_1330_ = v___y_1361_;
v_val_1331_ = v___x_1370_;
goto v___jp_1325_;
}
}
v___jp_1371_:
{
if (lean_obj_tag(v_subDir_x3f_1233_) == 1)
{
lean_object* v_val_1374_; lean_object* v___x_1375_; 
v_val_1374_ = lean_ctor_get(v_subDir_x3f_1233_, 0);
lean_inc(v_val_1374_);
v___x_1375_ = l_Lake_joinRelative(v_relPkgDir_1229_, v_val_1374_);
v___y_1359_ = v___y_1372_;
v___y_1360_ = v_a_1373_;
v___y_1361_ = v___x_1375_;
goto v___jp_1358_;
}
else
{
v___y_1359_ = v___y_1372_;
v___y_1360_ = v_a_1373_;
v___y_1361_ = v_relPkgDir_1229_;
goto v___jp_1358_;
}
}
v___jp_1377_:
{
lean_object* v___x_1379_; 
lean_inc(v_inputRev_x3f_1232_);
lean_inc_ref(v___y_1378_);
lean_inc_ref(v_gitDir_1376_);
lean_inc_ref(v_name_1228_);
v___x_1379_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(v_a_1234_, v_name_1228_, v_gitDir_1376_, v___y_1378_, v_inputRev_x3f_1232_);
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1445_; 
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1445_ == 0)
{
lean_object* v_unused_1446_; 
v_unused_1446_ = lean_ctor_get(v___x_1379_, 0);
lean_dec(v_unused_1446_);
v___x_1381_ = v___x_1379_;
v_isShared_1382_ = v_isSharedCheck_1445_;
goto v_resetjp_1380_;
}
else
{
lean_dec(v___x_1379_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1445_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; 
v___x_1383_ = lean_unsigned_to_nat(0u);
v___x_1384_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0));
v___x_1385_ = l_Lake_GitRepo_getHeadRevision(v_gitDir_1376_, v___x_1384_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_object* v_a_1386_; lean_object* v_a_1387_; lean_object* v___x_1388_; uint8_t v___x_1389_; 
lean_del_object(v___x_1381_);
v_a_1386_ = lean_ctor_get(v___x_1385_, 0);
lean_inc(v_a_1386_);
v_a_1387_ = lean_ctor_get(v___x_1385_, 1);
lean_inc(v_a_1387_);
lean_dec_ref_known(v___x_1385_, 2);
v___x_1388_ = lean_array_get_size(v_a_1387_);
v___x_1389_ = lean_nat_dec_lt(v___x_1383_, v___x_1388_);
if (v___x_1389_ == 0)
{
lean_dec(v_a_1387_);
v___y_1372_ = v___y_1378_;
v_a_1373_ = v_a_1386_;
goto v___jp_1371_;
}
else
{
lean_object* v___x_1390_; uint8_t v___x_1391_; 
v___x_1390_ = lean_box(0);
v___x_1391_ = lean_nat_dec_le(v___x_1388_, v___x_1388_);
if (v___x_1391_ == 0)
{
if (v___x_1389_ == 0)
{
lean_dec(v_a_1387_);
v___y_1372_ = v___y_1378_;
v_a_1373_ = v_a_1386_;
goto v___jp_1371_;
}
else
{
size_t v___x_1392_; size_t v___x_1393_; lean_object* v___x_1394_; 
v___x_1392_ = ((size_t)0ULL);
v___x_1393_ = lean_usize_of_nat(v___x_1388_);
v___x_1394_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_1387_, v___x_1392_, v___x_1393_, v___x_1390_, v_a_1234_);
lean_dec(v_a_1387_);
if (lean_obj_tag(v___x_1394_) == 0)
{
lean_dec_ref_known(v___x_1394_, 1);
v___y_1372_ = v___y_1378_;
v_a_1373_ = v_a_1386_;
goto v___jp_1371_;
}
else
{
lean_object* v_a_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1402_; 
lean_dec(v_a_1386_);
lean_dec_ref(v___y_1378_);
lean_del_object(v___x_1243_);
lean_dec_ref(v_scope_1241_);
lean_dec(v_name_1240_);
lean_dec(v_subDir_x3f_1233_);
lean_dec(v_inputRev_x3f_1232_);
lean_dec_ref(v_remoteUrl_1231_);
lean_dec_ref(v_relPkgDir_1229_);
lean_dec_ref(v_name_1228_);
lean_dec_ref(v_wsDir_1227_);
v_a_1395_ = lean_ctor_get(v___x_1394_, 0);
v_isSharedCheck_1402_ = !lean_is_exclusive(v___x_1394_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1397_ = v___x_1394_;
v_isShared_1398_ = v_isSharedCheck_1402_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_a_1395_);
lean_dec(v___x_1394_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1402_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v___x_1400_; 
if (v_isShared_1398_ == 0)
{
v___x_1400_ = v___x_1397_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v_a_1395_);
v___x_1400_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
return v___x_1400_;
}
}
}
}
}
else
{
size_t v___x_1403_; size_t v___x_1404_; lean_object* v___x_1405_; 
v___x_1403_ = ((size_t)0ULL);
v___x_1404_ = lean_usize_of_nat(v___x_1388_);
v___x_1405_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_1387_, v___x_1403_, v___x_1404_, v___x_1390_, v_a_1234_);
lean_dec(v_a_1387_);
if (lean_obj_tag(v___x_1405_) == 0)
{
lean_dec_ref_known(v___x_1405_, 1);
v___y_1372_ = v___y_1378_;
v_a_1373_ = v_a_1386_;
goto v___jp_1371_;
}
else
{
lean_object* v_a_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1413_; 
lean_dec(v_a_1386_);
lean_dec_ref(v___y_1378_);
lean_del_object(v___x_1243_);
lean_dec_ref(v_scope_1241_);
lean_dec(v_name_1240_);
lean_dec(v_subDir_x3f_1233_);
lean_dec(v_inputRev_x3f_1232_);
lean_dec_ref(v_remoteUrl_1231_);
lean_dec_ref(v_relPkgDir_1229_);
lean_dec_ref(v_name_1228_);
lean_dec_ref(v_wsDir_1227_);
v_a_1406_ = lean_ctor_get(v___x_1405_, 0);
v_isSharedCheck_1413_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1408_ = v___x_1405_;
v_isShared_1409_ = v_isSharedCheck_1413_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_a_1406_);
lean_dec(v___x_1405_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1413_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1411_; 
if (v_isShared_1409_ == 0)
{
v___x_1411_ = v___x_1408_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_a_1406_);
v___x_1411_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
return v___x_1411_;
}
}
}
}
}
}
else
{
lean_object* v_a_1414_; lean_object* v___x_1415_; uint8_t v___x_1416_; 
lean_dec_ref(v___y_1378_);
lean_del_object(v___x_1243_);
lean_dec_ref(v_scope_1241_);
lean_dec(v_name_1240_);
lean_dec(v_subDir_x3f_1233_);
lean_dec(v_inputRev_x3f_1232_);
lean_dec_ref(v_remoteUrl_1231_);
lean_dec_ref(v_relPkgDir_1229_);
lean_dec_ref(v_name_1228_);
lean_dec_ref(v_wsDir_1227_);
v_a_1414_ = lean_ctor_get(v___x_1385_, 1);
lean_inc(v_a_1414_);
lean_dec_ref_known(v___x_1385_, 2);
v___x_1415_ = lean_array_get_size(v_a_1414_);
v___x_1416_ = lean_nat_dec_lt(v___x_1383_, v___x_1415_);
if (v___x_1416_ == 0)
{
lean_object* v___x_1417_; lean_object* v___x_1419_; 
lean_dec(v_a_1414_);
v___x_1417_ = lean_box(0);
if (v_isShared_1382_ == 0)
{
lean_ctor_set_tag(v___x_1381_, 1);
lean_ctor_set(v___x_1381_, 0, v___x_1417_);
v___x_1419_ = v___x_1381_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v___x_1417_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
else
{
lean_object* v___x_1421_; uint8_t v___x_1422_; 
lean_del_object(v___x_1381_);
v___x_1421_ = lean_box(0);
v___x_1422_ = lean_nat_dec_le(v___x_1415_, v___x_1415_);
if (v___x_1422_ == 0)
{
if (v___x_1416_ == 0)
{
lean_dec(v_a_1414_);
goto v___jp_1236_;
}
else
{
size_t v___x_1423_; size_t v___x_1424_; lean_object* v___x_1425_; 
v___x_1423_ = ((size_t)0ULL);
v___x_1424_ = lean_usize_of_nat(v___x_1415_);
v___x_1425_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_1414_, v___x_1423_, v___x_1424_, v___x_1421_, v_a_1234_);
lean_dec(v_a_1414_);
if (lean_obj_tag(v___x_1425_) == 0)
{
lean_dec_ref_known(v___x_1425_, 1);
goto v___jp_1236_;
}
else
{
lean_object* v_a_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1433_; 
v_a_1426_ = lean_ctor_get(v___x_1425_, 0);
v_isSharedCheck_1433_ = !lean_is_exclusive(v___x_1425_);
if (v_isSharedCheck_1433_ == 0)
{
v___x_1428_ = v___x_1425_;
v_isShared_1429_ = v_isSharedCheck_1433_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_a_1426_);
lean_dec(v___x_1425_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1433_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v___x_1431_; 
if (v_isShared_1429_ == 0)
{
v___x_1431_ = v___x_1428_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v_a_1426_);
v___x_1431_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
return v___x_1431_;
}
}
}
}
}
else
{
size_t v___x_1434_; size_t v___x_1435_; lean_object* v___x_1436_; 
v___x_1434_ = ((size_t)0ULL);
v___x_1435_ = lean_usize_of_nat(v___x_1415_);
v___x_1436_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_1414_, v___x_1434_, v___x_1435_, v___x_1421_, v_a_1234_);
lean_dec(v_a_1414_);
if (lean_obj_tag(v___x_1436_) == 0)
{
lean_dec_ref_known(v___x_1436_, 1);
goto v___jp_1236_;
}
else
{
lean_object* v_a_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1444_; 
v_a_1437_ = lean_ctor_get(v___x_1436_, 0);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1439_ = v___x_1436_;
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_a_1437_);
lean_dec(v___x_1436_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v___x_1442_; 
if (v_isShared_1440_ == 0)
{
v___x_1442_ = v___x_1439_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v_a_1437_);
v___x_1442_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
return v___x_1442_;
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
lean_object* v_a_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1454_; 
lean_dec_ref(v___y_1378_);
lean_dec_ref(v_gitDir_1376_);
lean_del_object(v___x_1243_);
lean_dec_ref(v_scope_1241_);
lean_dec(v_name_1240_);
lean_dec(v_subDir_x3f_1233_);
lean_dec(v_inputRev_x3f_1232_);
lean_dec_ref(v_remoteUrl_1231_);
lean_dec_ref(v_relPkgDir_1229_);
lean_dec_ref(v_name_1228_);
lean_dec_ref(v_wsDir_1227_);
v_a_1447_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1449_ = v___x_1379_;
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_a_1447_);
lean_dec(v___x_1379_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1452_; 
if (v_isShared_1450_ == 0)
{
v___x_1452_ = v___x_1449_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_a_1447_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___boxed(lean_object* v_dep_1461_, lean_object* v_inherited_1462_, lean_object* v_lakeEnv_1463_, lean_object* v_wsDir_1464_, lean_object* v_name_1465_, lean_object* v_relPkgDir_1466_, lean_object* v_gitUrl_1467_, lean_object* v_remoteUrl_1468_, lean_object* v_inputRev_x3f_1469_, lean_object* v_subDir_x3f_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_){
_start:
{
uint8_t v_inherited_boxed_1473_; lean_object* v_res_1474_; 
v_inherited_boxed_1473_ = lean_unbox(v_inherited_1462_);
v_res_1474_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit(v_dep_1461_, v_inherited_boxed_1473_, v_lakeEnv_1463_, v_wsDir_1464_, v_name_1465_, v_relPkgDir_1466_, v_gitUrl_1467_, v_remoteUrl_1468_, v_inputRev_x3f_1469_, v_subDir_x3f_1470_, v_a_1471_);
lean_dec_ref(v_a_1471_);
lean_dec_ref(v_lakeEnv_1463_);
return v_res_1474_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(lean_object* v_a_1475_, lean_object* v_dep_1476_, uint8_t v_inherited_1477_, lean_object* v_lakeEnv_1478_, lean_object* v_wsDir_1479_, lean_object* v_name_1480_, lean_object* v_relPkgDir_1481_, lean_object* v_gitUrl_1482_, lean_object* v_remoteUrl_1483_, lean_object* v_inputRev_x3f_1484_, lean_object* v_subDir_x3f_1485_){
_start:
{
lean_object* v_pkgUrlMap_1490_; lean_object* v_name_1491_; lean_object* v_scope_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1708_; 
v_pkgUrlMap_1490_ = lean_ctor_get(v_lakeEnv_1478_, 5);
v_name_1491_ = lean_ctor_get(v_dep_1476_, 0);
v_scope_1492_ = lean_ctor_get(v_dep_1476_, 1);
v_isSharedCheck_1708_ = !lean_is_exclusive(v_dep_1476_);
if (v_isSharedCheck_1708_ == 0)
{
lean_object* v_unused_1709_; lean_object* v_unused_1710_; lean_object* v_unused_1711_; 
v_unused_1709_ = lean_ctor_get(v_dep_1476_, 4);
lean_dec(v_unused_1709_);
v_unused_1710_ = lean_ctor_get(v_dep_1476_, 3);
lean_dec(v_unused_1710_);
v_unused_1711_ = lean_ctor_get(v_dep_1476_, 2);
lean_dec(v_unused_1711_);
v___x_1494_ = v_dep_1476_;
v_isShared_1495_ = v_isSharedCheck_1708_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_scope_1492_);
lean_inc(v_name_1491_);
lean_dec(v_dep_1476_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1708_;
goto v_resetjp_1493_;
}
v___jp_1487_:
{
lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1488_ = lean_box(0);
v___x_1489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1489_, 0, v___x_1488_);
return v___x_1489_;
}
v_resetjp_1493_:
{
lean_object* v___y_1497_; lean_object* v___y_1498_; lean_object* v___y_1499_; lean_object* v_a_1500_; lean_object* v___y_1509_; lean_object* v___y_1510_; lean_object* v___y_1511_; lean_object* v___y_1512_; lean_object* v___y_1513_; lean_object* v_val_1514_; lean_object* v___y_1542_; lean_object* v___y_1543_; lean_object* v___y_1544_; lean_object* v_a_1545_; lean_object* v___y_1577_; lean_object* v___y_1578_; lean_object* v___y_1579_; lean_object* v___y_1580_; lean_object* v___y_1581_; lean_object* v_val_1582_; lean_object* v___y_1610_; lean_object* v___y_1611_; lean_object* v___y_1612_; lean_object* v___y_1623_; lean_object* v_a_1624_; lean_object* v_gitDir_1627_; lean_object* v___y_1629_; lean_object* v___x_1706_; 
lean_inc_ref(v_relPkgDir_1481_);
lean_inc_ref(v_wsDir_1479_);
v_gitDir_1627_ = l_Lake_joinRelative(v_wsDir_1479_, v_relPkgDir_1481_);
v___x_1706_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgUrlMap_1490_, v_name_1491_);
if (lean_obj_tag(v___x_1706_) == 0)
{
v___y_1629_ = v_gitUrl_1482_;
goto v___jp_1628_;
}
else
{
lean_object* v_val_1707_; 
lean_dec_ref(v_gitUrl_1482_);
v_val_1707_ = lean_ctor_get(v___x_1706_, 0);
lean_inc(v_val_1707_);
lean_dec_ref_known(v___x_1706_, 1);
v___y_1629_ = v_val_1707_;
goto v___jp_1628_;
}
v___jp_1496_:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1505_; 
v___x_1501_ = l_Lake_defaultConfigFile;
v___x_1502_ = lean_box(0);
v___x_1503_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1503_, 0, v_name_1491_);
lean_ctor_set(v___x_1503_, 1, v_scope_1492_);
lean_ctor_set(v___x_1503_, 2, v___x_1501_);
lean_ctor_set(v___x_1503_, 3, v___x_1502_);
lean_ctor_set(v___x_1503_, 4, v___y_1498_);
lean_ctor_set_uint8(v___x_1503_, sizeof(void*)*5, v_inherited_1477_);
if (v_isShared_1495_ == 0)
{
lean_ctor_set(v___x_1494_, 4, v___x_1503_);
lean_ctor_set(v___x_1494_, 3, v_a_1500_);
lean_ctor_set(v___x_1494_, 2, v_remoteUrl_1483_);
lean_ctor_set(v___x_1494_, 1, v___y_1497_);
lean_ctor_set(v___x_1494_, 0, v___y_1499_);
v___x_1505_ = v___x_1494_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v___y_1499_);
lean_ctor_set(v_reuseFailAlloc_1507_, 1, v___y_1497_);
lean_ctor_set(v_reuseFailAlloc_1507_, 2, v_remoteUrl_1483_);
lean_ctor_set(v_reuseFailAlloc_1507_, 3, v_a_1500_);
lean_ctor_set(v_reuseFailAlloc_1507_, 4, v___x_1503_);
v___x_1505_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
lean_object* v___x_1506_; 
v___x_1506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1505_);
return v___x_1506_;
}
}
v___jp_1508_:
{
lean_object* v___x_1515_; uint8_t v___x_1516_; 
v___x_1515_ = lean_array_get_size(v___y_1509_);
v___x_1516_ = lean_nat_dec_lt(v___y_1511_, v___x_1515_);
if (v___x_1516_ == 0)
{
v___y_1497_ = v___y_1510_;
v___y_1498_ = v___y_1512_;
v___y_1499_ = v___y_1513_;
v_a_1500_ = v_val_1514_;
goto v___jp_1496_;
}
else
{
lean_object* v___x_1517_; uint8_t v___x_1518_; 
v___x_1517_ = lean_box(0);
v___x_1518_ = lean_nat_dec_le(v___x_1515_, v___x_1515_);
if (v___x_1518_ == 0)
{
if (v___x_1516_ == 0)
{
v___y_1497_ = v___y_1510_;
v___y_1498_ = v___y_1512_;
v___y_1499_ = v___y_1513_;
v_a_1500_ = v_val_1514_;
goto v___jp_1496_;
}
else
{
size_t v___x_1519_; size_t v___x_1520_; lean_object* v___x_1521_; 
v___x_1519_ = ((size_t)0ULL);
v___x_1520_ = lean_usize_of_nat(v___x_1515_);
v___x_1521_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_1509_, v___x_1519_, v___x_1520_, v___x_1517_, v_a_1475_);
if (lean_obj_tag(v___x_1521_) == 0)
{
lean_dec_ref_known(v___x_1521_, 1);
v___y_1497_ = v___y_1510_;
v___y_1498_ = v___y_1512_;
v___y_1499_ = v___y_1513_;
v_a_1500_ = v_val_1514_;
goto v___jp_1496_;
}
else
{
lean_object* v_a_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1529_; 
lean_dec_ref(v_val_1514_);
lean_dec_ref(v___y_1513_);
lean_dec_ref(v___y_1512_);
lean_dec_ref(v___y_1510_);
lean_del_object(v___x_1494_);
lean_dec_ref(v_scope_1492_);
lean_dec(v_name_1491_);
lean_dec_ref(v_remoteUrl_1483_);
v_a_1522_ = lean_ctor_get(v___x_1521_, 0);
v_isSharedCheck_1529_ = !lean_is_exclusive(v___x_1521_);
if (v_isSharedCheck_1529_ == 0)
{
v___x_1524_ = v___x_1521_;
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_a_1522_);
lean_dec(v___x_1521_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
lean_object* v___x_1527_; 
if (v_isShared_1525_ == 0)
{
v___x_1527_ = v___x_1524_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_a_1522_);
v___x_1527_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
return v___x_1527_;
}
}
}
}
}
else
{
size_t v___x_1530_; size_t v___x_1531_; lean_object* v___x_1532_; 
v___x_1530_ = ((size_t)0ULL);
v___x_1531_ = lean_usize_of_nat(v___x_1515_);
v___x_1532_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_1509_, v___x_1530_, v___x_1531_, v___x_1517_, v_a_1475_);
if (lean_obj_tag(v___x_1532_) == 0)
{
lean_dec_ref_known(v___x_1532_, 1);
v___y_1497_ = v___y_1510_;
v___y_1498_ = v___y_1512_;
v___y_1499_ = v___y_1513_;
v_a_1500_ = v_val_1514_;
goto v___jp_1496_;
}
else
{
lean_object* v_a_1533_; lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1540_; 
lean_dec_ref(v_val_1514_);
lean_dec_ref(v___y_1513_);
lean_dec_ref(v___y_1512_);
lean_dec_ref(v___y_1510_);
lean_del_object(v___x_1494_);
lean_dec_ref(v_scope_1492_);
lean_dec(v_name_1491_);
lean_dec_ref(v_remoteUrl_1483_);
v_a_1533_ = lean_ctor_get(v___x_1532_, 0);
v_isSharedCheck_1540_ = !lean_is_exclusive(v___x_1532_);
if (v_isSharedCheck_1540_ == 0)
{
v___x_1535_ = v___x_1532_;
v_isShared_1536_ = v_isSharedCheck_1540_;
goto v_resetjp_1534_;
}
else
{
lean_inc(v_a_1533_);
lean_dec(v___x_1532_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1540_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
lean_object* v___x_1538_; 
if (v_isShared_1536_ == 0)
{
v___x_1538_ = v___x_1535_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v_a_1533_);
v___x_1538_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
return v___x_1538_;
}
}
}
}
}
}
v___jp_1541_:
{
if (lean_obj_tag(v_a_1545_) == 1)
{
lean_object* v_val_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; 
lean_dec_ref(v___y_1544_);
lean_dec_ref(v_name_1480_);
v_val_1546_ = lean_ctor_get(v_a_1545_, 0);
lean_inc_n(v_val_1546_, 2);
lean_dec_ref_known(v_a_1545_, 1);
v___x_1547_ = l_Lake_defaultManifestFile;
v___x_1548_ = l_Lake_joinRelative(v_val_1546_, v___x_1547_);
v___x_1549_ = lean_unsigned_to_nat(0u);
v___x_1550_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0));
v___x_1551_ = l_Lake_Manifest_load(v___x_1548_);
if (lean_obj_tag(v___x_1551_) == 0)
{
lean_object* v_a_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1559_; 
v_a_1552_ = lean_ctor_get(v___x_1551_, 0);
v_isSharedCheck_1559_ = !lean_is_exclusive(v___x_1551_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1554_ = v___x_1551_;
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_a_1552_);
lean_dec(v___x_1551_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v___x_1557_; 
if (v_isShared_1555_ == 0)
{
lean_ctor_set_tag(v___x_1554_, 1);
v___x_1557_ = v___x_1554_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v_a_1552_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
v___y_1509_ = v___x_1550_;
v___y_1510_ = v___y_1542_;
v___y_1511_ = v___x_1549_;
v___y_1512_ = v___y_1543_;
v___y_1513_ = v_val_1546_;
v_val_1514_ = v___x_1557_;
goto v___jp_1508_;
}
}
}
else
{
lean_object* v_a_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1567_; 
v_a_1560_ = lean_ctor_get(v___x_1551_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1551_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1562_ = v___x_1551_;
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_a_1560_);
lean_dec(v___x_1551_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1565_; 
if (v_isShared_1563_ == 0)
{
lean_ctor_set_tag(v___x_1562_, 0);
v___x_1565_ = v___x_1562_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_a_1560_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
v___y_1509_ = v___x_1550_;
v___y_1510_ = v___y_1542_;
v___y_1511_ = v___x_1549_;
v___y_1512_ = v___y_1543_;
v___y_1513_ = v_val_1546_;
v_val_1514_ = v___x_1565_;
goto v___jp_1508_;
}
}
}
}
else
{
lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; uint8_t v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; 
lean_dec(v_a_1545_);
lean_dec_ref(v___y_1543_);
lean_dec_ref(v___y_1542_);
lean_del_object(v___x_1494_);
lean_dec_ref(v_scope_1492_);
lean_dec(v_name_1491_);
lean_dec_ref(v_remoteUrl_1483_);
v___x_1568_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__3));
v___x_1569_ = lean_string_append(v_name_1480_, v___x_1568_);
v___x_1570_ = lean_string_append(v___x_1569_, v___y_1544_);
lean_dec_ref(v___y_1544_);
v___x_1571_ = 3;
v___x_1572_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1572_, 0, v___x_1570_);
lean_ctor_set_uint8(v___x_1572_, sizeof(void*)*1, v___x_1571_);
lean_inc_ref(v_a_1475_);
v___x_1573_ = lean_apply_2(v_a_1475_, v___x_1572_, lean_box(0));
v___x_1574_ = lean_box(0);
v___x_1575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1574_);
return v___x_1575_;
}
}
v___jp_1576_:
{
lean_object* v___x_1583_; uint8_t v___x_1584_; 
v___x_1583_ = lean_array_get_size(v___y_1579_);
v___x_1584_ = lean_nat_dec_lt(v___y_1580_, v___x_1583_);
if (v___x_1584_ == 0)
{
v___y_1542_ = v___y_1577_;
v___y_1543_ = v___y_1578_;
v___y_1544_ = v___y_1581_;
v_a_1545_ = v_val_1582_;
goto v___jp_1541_;
}
else
{
lean_object* v___x_1585_; uint8_t v___x_1586_; 
v___x_1585_ = lean_box(0);
v___x_1586_ = lean_nat_dec_le(v___x_1583_, v___x_1583_);
if (v___x_1586_ == 0)
{
if (v___x_1584_ == 0)
{
v___y_1542_ = v___y_1577_;
v___y_1543_ = v___y_1578_;
v___y_1544_ = v___y_1581_;
v_a_1545_ = v_val_1582_;
goto v___jp_1541_;
}
else
{
size_t v___x_1587_; size_t v___x_1588_; lean_object* v___x_1589_; 
v___x_1587_ = ((size_t)0ULL);
v___x_1588_ = lean_usize_of_nat(v___x_1583_);
v___x_1589_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_1579_, v___x_1587_, v___x_1588_, v___x_1585_, v_a_1475_);
if (lean_obj_tag(v___x_1589_) == 0)
{
lean_dec_ref_known(v___x_1589_, 1);
v___y_1542_ = v___y_1577_;
v___y_1543_ = v___y_1578_;
v___y_1544_ = v___y_1581_;
v_a_1545_ = v_val_1582_;
goto v___jp_1541_;
}
else
{
lean_object* v_a_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1597_; 
lean_dec(v_val_1582_);
lean_dec_ref(v___y_1581_);
lean_dec_ref(v___y_1578_);
lean_dec_ref(v___y_1577_);
lean_del_object(v___x_1494_);
lean_dec_ref(v_scope_1492_);
lean_dec(v_name_1491_);
lean_dec_ref(v_remoteUrl_1483_);
lean_dec_ref(v_name_1480_);
v_a_1590_ = lean_ctor_get(v___x_1589_, 0);
v_isSharedCheck_1597_ = !lean_is_exclusive(v___x_1589_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1592_ = v___x_1589_;
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_a_1590_);
lean_dec(v___x_1589_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___x_1595_; 
if (v_isShared_1593_ == 0)
{
v___x_1595_ = v___x_1592_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_a_1590_);
v___x_1595_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
return v___x_1595_;
}
}
}
}
}
else
{
size_t v___x_1598_; size_t v___x_1599_; lean_object* v___x_1600_; 
v___x_1598_ = ((size_t)0ULL);
v___x_1599_ = lean_usize_of_nat(v___x_1583_);
v___x_1600_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_1579_, v___x_1598_, v___x_1599_, v___x_1585_, v_a_1475_);
if (lean_obj_tag(v___x_1600_) == 0)
{
lean_dec_ref_known(v___x_1600_, 1);
v___y_1542_ = v___y_1577_;
v___y_1543_ = v___y_1578_;
v___y_1544_ = v___y_1581_;
v_a_1545_ = v_val_1582_;
goto v___jp_1541_;
}
else
{
lean_object* v_a_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1608_; 
lean_dec(v_val_1582_);
lean_dec_ref(v___y_1581_);
lean_dec_ref(v___y_1578_);
lean_dec_ref(v___y_1577_);
lean_del_object(v___x_1494_);
lean_dec_ref(v_scope_1492_);
lean_dec(v_name_1491_);
lean_dec_ref(v_remoteUrl_1483_);
lean_dec_ref(v_name_1480_);
v_a_1601_ = lean_ctor_get(v___x_1600_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v___x_1600_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1603_ = v___x_1600_;
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_a_1601_);
lean_dec(v___x_1600_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1606_; 
if (v_isShared_1604_ == 0)
{
v___x_1606_ = v___x_1603_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_a_1601_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
}
}
}
}
v___jp_1609_:
{
lean_object* v_pkgDir_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; uint8_t v___x_1619_; 
lean_inc_ref(v___y_1612_);
v_pkgDir_1613_ = l_Lake_joinRelative(v_wsDir_1479_, v___y_1612_);
lean_inc_ref(v_pkgDir_1613_);
v___x_1614_ = l_Lake_resolvePath(v_pkgDir_1613_);
v___x_1615_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1615_, 0, v___y_1610_);
lean_ctor_set(v___x_1615_, 1, v___y_1611_);
lean_ctor_set(v___x_1615_, 2, v_inputRev_x3f_1484_);
lean_ctor_set(v___x_1615_, 3, v_subDir_x3f_1485_);
v___x_1616_ = lean_unsigned_to_nat(0u);
v___x_1617_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0));
v___x_1618_ = lean_string_utf8_byte_size(v___x_1614_);
v___x_1619_ = lean_nat_dec_eq(v___x_1618_, v___x_1616_);
if (v___x_1619_ == 0)
{
lean_object* v___x_1620_; 
v___x_1620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1620_, 0, v___x_1614_);
v___y_1577_ = v___y_1612_;
v___y_1578_ = v___x_1615_;
v___y_1579_ = v___x_1617_;
v___y_1580_ = v___x_1616_;
v___y_1581_ = v_pkgDir_1613_;
v_val_1582_ = v___x_1620_;
goto v___jp_1576_;
}
else
{
lean_object* v___x_1621_; 
lean_dec_ref(v___x_1614_);
v___x_1621_ = lean_box(0);
v___y_1577_ = v___y_1612_;
v___y_1578_ = v___x_1615_;
v___y_1579_ = v___x_1617_;
v___y_1580_ = v___x_1616_;
v___y_1581_ = v_pkgDir_1613_;
v_val_1582_ = v___x_1621_;
goto v___jp_1576_;
}
}
v___jp_1622_:
{
if (lean_obj_tag(v_subDir_x3f_1485_) == 1)
{
lean_object* v_val_1625_; lean_object* v___x_1626_; 
v_val_1625_ = lean_ctor_get(v_subDir_x3f_1485_, 0);
lean_inc(v_val_1625_);
v___x_1626_ = l_Lake_joinRelative(v_relPkgDir_1481_, v_val_1625_);
v___y_1610_ = v___y_1623_;
v___y_1611_ = v_a_1624_;
v___y_1612_ = v___x_1626_;
goto v___jp_1609_;
}
else
{
v___y_1610_ = v___y_1623_;
v___y_1611_ = v_a_1624_;
v___y_1612_ = v_relPkgDir_1481_;
goto v___jp_1609_;
}
}
v___jp_1628_:
{
lean_object* v___x_1630_; 
lean_inc(v_inputRev_x3f_1484_);
lean_inc_ref(v___y_1629_);
lean_inc_ref(v_gitDir_1627_);
lean_inc_ref(v_name_1480_);
v___x_1630_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(v_a_1475_, v_name_1480_, v_gitDir_1627_, v___y_1629_, v_inputRev_x3f_1484_);
if (lean_obj_tag(v___x_1630_) == 0)
{
lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1696_; 
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1630_);
if (v_isSharedCheck_1696_ == 0)
{
lean_object* v_unused_1697_; 
v_unused_1697_ = lean_ctor_get(v___x_1630_, 0);
lean_dec(v_unused_1697_);
v___x_1632_ = v___x_1630_;
v_isShared_1633_ = v_isSharedCheck_1696_;
goto v_resetjp_1631_;
}
else
{
lean_dec(v___x_1630_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1696_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
v___x_1634_ = lean_unsigned_to_nat(0u);
v___x_1635_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0));
v___x_1636_ = l_Lake_GitRepo_getHeadRevision(v_gitDir_1627_, v___x_1635_);
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_object* v_a_1637_; lean_object* v_a_1638_; lean_object* v___x_1639_; uint8_t v___x_1640_; 
lean_del_object(v___x_1632_);
v_a_1637_ = lean_ctor_get(v___x_1636_, 0);
lean_inc(v_a_1637_);
v_a_1638_ = lean_ctor_get(v___x_1636_, 1);
lean_inc(v_a_1638_);
lean_dec_ref_known(v___x_1636_, 2);
v___x_1639_ = lean_array_get_size(v_a_1638_);
v___x_1640_ = lean_nat_dec_lt(v___x_1634_, v___x_1639_);
if (v___x_1640_ == 0)
{
lean_dec(v_a_1638_);
v___y_1623_ = v___y_1629_;
v_a_1624_ = v_a_1637_;
goto v___jp_1622_;
}
else
{
lean_object* v___x_1641_; uint8_t v___x_1642_; 
v___x_1641_ = lean_box(0);
v___x_1642_ = lean_nat_dec_le(v___x_1639_, v___x_1639_);
if (v___x_1642_ == 0)
{
if (v___x_1640_ == 0)
{
lean_dec(v_a_1638_);
v___y_1623_ = v___y_1629_;
v_a_1624_ = v_a_1637_;
goto v___jp_1622_;
}
else
{
size_t v___x_1643_; size_t v___x_1644_; lean_object* v___x_1645_; 
v___x_1643_ = ((size_t)0ULL);
v___x_1644_ = lean_usize_of_nat(v___x_1639_);
v___x_1645_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_1638_, v___x_1643_, v___x_1644_, v___x_1641_, v_a_1475_);
lean_dec(v_a_1638_);
if (lean_obj_tag(v___x_1645_) == 0)
{
lean_dec_ref_known(v___x_1645_, 1);
v___y_1623_ = v___y_1629_;
v_a_1624_ = v_a_1637_;
goto v___jp_1622_;
}
else
{
lean_object* v_a_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1653_; 
lean_dec(v_a_1637_);
lean_dec_ref(v___y_1629_);
lean_del_object(v___x_1494_);
lean_dec_ref(v_scope_1492_);
lean_dec(v_name_1491_);
lean_dec(v_subDir_x3f_1485_);
lean_dec(v_inputRev_x3f_1484_);
lean_dec_ref(v_remoteUrl_1483_);
lean_dec_ref(v_relPkgDir_1481_);
lean_dec_ref(v_name_1480_);
lean_dec_ref(v_wsDir_1479_);
v_a_1646_ = lean_ctor_get(v___x_1645_, 0);
v_isSharedCheck_1653_ = !lean_is_exclusive(v___x_1645_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1648_ = v___x_1645_;
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_a_1646_);
lean_dec(v___x_1645_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1651_; 
if (v_isShared_1649_ == 0)
{
v___x_1651_ = v___x_1648_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v_a_1646_);
v___x_1651_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
return v___x_1651_;
}
}
}
}
}
else
{
size_t v___x_1654_; size_t v___x_1655_; lean_object* v___x_1656_; 
v___x_1654_ = ((size_t)0ULL);
v___x_1655_ = lean_usize_of_nat(v___x_1639_);
v___x_1656_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_1638_, v___x_1654_, v___x_1655_, v___x_1641_, v_a_1475_);
lean_dec(v_a_1638_);
if (lean_obj_tag(v___x_1656_) == 0)
{
lean_dec_ref_known(v___x_1656_, 1);
v___y_1623_ = v___y_1629_;
v_a_1624_ = v_a_1637_;
goto v___jp_1622_;
}
else
{
lean_object* v_a_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1664_; 
lean_dec(v_a_1637_);
lean_dec_ref(v___y_1629_);
lean_del_object(v___x_1494_);
lean_dec_ref(v_scope_1492_);
lean_dec(v_name_1491_);
lean_dec(v_subDir_x3f_1485_);
lean_dec(v_inputRev_x3f_1484_);
lean_dec_ref(v_remoteUrl_1483_);
lean_dec_ref(v_relPkgDir_1481_);
lean_dec_ref(v_name_1480_);
lean_dec_ref(v_wsDir_1479_);
v_a_1657_ = lean_ctor_get(v___x_1656_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1659_ = v___x_1656_;
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_a_1657_);
lean_dec(v___x_1656_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1662_; 
if (v_isShared_1660_ == 0)
{
v___x_1662_ = v___x_1659_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_a_1657_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
return v___x_1662_;
}
}
}
}
}
}
else
{
lean_object* v_a_1665_; lean_object* v___x_1666_; uint8_t v___x_1667_; 
lean_dec_ref(v___y_1629_);
lean_del_object(v___x_1494_);
lean_dec_ref(v_scope_1492_);
lean_dec(v_name_1491_);
lean_dec(v_subDir_x3f_1485_);
lean_dec(v_inputRev_x3f_1484_);
lean_dec_ref(v_remoteUrl_1483_);
lean_dec_ref(v_relPkgDir_1481_);
lean_dec_ref(v_name_1480_);
lean_dec_ref(v_wsDir_1479_);
v_a_1665_ = lean_ctor_get(v___x_1636_, 1);
lean_inc(v_a_1665_);
lean_dec_ref_known(v___x_1636_, 2);
v___x_1666_ = lean_array_get_size(v_a_1665_);
v___x_1667_ = lean_nat_dec_lt(v___x_1634_, v___x_1666_);
if (v___x_1667_ == 0)
{
lean_object* v___x_1668_; lean_object* v___x_1670_; 
lean_dec(v_a_1665_);
v___x_1668_ = lean_box(0);
if (v_isShared_1633_ == 0)
{
lean_ctor_set_tag(v___x_1632_, 1);
lean_ctor_set(v___x_1632_, 0, v___x_1668_);
v___x_1670_ = v___x_1632_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v___x_1668_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
}
}
else
{
lean_object* v___x_1672_; uint8_t v___x_1673_; 
lean_del_object(v___x_1632_);
v___x_1672_ = lean_box(0);
v___x_1673_ = lean_nat_dec_le(v___x_1666_, v___x_1666_);
if (v___x_1673_ == 0)
{
if (v___x_1667_ == 0)
{
lean_dec(v_a_1665_);
goto v___jp_1487_;
}
else
{
size_t v___x_1674_; size_t v___x_1675_; lean_object* v___x_1676_; 
v___x_1674_ = ((size_t)0ULL);
v___x_1675_ = lean_usize_of_nat(v___x_1666_);
v___x_1676_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_1665_, v___x_1674_, v___x_1675_, v___x_1672_, v_a_1475_);
lean_dec(v_a_1665_);
if (lean_obj_tag(v___x_1676_) == 0)
{
lean_dec_ref_known(v___x_1676_, 1);
goto v___jp_1487_;
}
else
{
lean_object* v_a_1677_; lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1684_; 
v_a_1677_ = lean_ctor_get(v___x_1676_, 0);
v_isSharedCheck_1684_ = !lean_is_exclusive(v___x_1676_);
if (v_isSharedCheck_1684_ == 0)
{
v___x_1679_ = v___x_1676_;
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
else
{
lean_inc(v_a_1677_);
lean_dec(v___x_1676_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
lean_object* v___x_1682_; 
if (v_isShared_1680_ == 0)
{
v___x_1682_ = v___x_1679_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_a_1677_);
v___x_1682_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
return v___x_1682_;
}
}
}
}
}
else
{
size_t v___x_1685_; size_t v___x_1686_; lean_object* v___x_1687_; 
v___x_1685_ = ((size_t)0ULL);
v___x_1686_ = lean_usize_of_nat(v___x_1666_);
v___x_1687_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_1665_, v___x_1685_, v___x_1686_, v___x_1672_, v_a_1475_);
lean_dec(v_a_1665_);
if (lean_obj_tag(v___x_1687_) == 0)
{
lean_dec_ref_known(v___x_1687_, 1);
goto v___jp_1487_;
}
else
{
lean_object* v_a_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1695_; 
v_a_1688_ = lean_ctor_get(v___x_1687_, 0);
v_isSharedCheck_1695_ = !lean_is_exclusive(v___x_1687_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1690_ = v___x_1687_;
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_a_1688_);
lean_dec(v___x_1687_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v___x_1693_; 
if (v_isShared_1691_ == 0)
{
v___x_1693_ = v___x_1690_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_a_1688_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
return v___x_1693_;
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
lean_object* v_a_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1705_; 
lean_dec_ref(v___y_1629_);
lean_dec_ref(v_gitDir_1627_);
lean_del_object(v___x_1494_);
lean_dec_ref(v_scope_1492_);
lean_dec(v_name_1491_);
lean_dec(v_subDir_x3f_1485_);
lean_dec(v_inputRev_x3f_1484_);
lean_dec_ref(v_remoteUrl_1483_);
lean_dec_ref(v_relPkgDir_1481_);
lean_dec_ref(v_name_1480_);
lean_dec_ref(v_wsDir_1479_);
v_a_1698_ = lean_ctor_get(v___x_1630_, 0);
v_isSharedCheck_1705_ = !lean_is_exclusive(v___x_1630_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1700_ = v___x_1630_;
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_a_1698_);
lean_dec(v___x_1630_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1703_; 
if (v_isShared_1701_ == 0)
{
v___x_1703_ = v___x_1700_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v_a_1698_);
v___x_1703_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
return v___x_1703_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0___boxed(lean_object* v_a_1712_, lean_object* v_dep_1713_, lean_object* v_inherited_1714_, lean_object* v_lakeEnv_1715_, lean_object* v_wsDir_1716_, lean_object* v_name_1717_, lean_object* v_relPkgDir_1718_, lean_object* v_gitUrl_1719_, lean_object* v_remoteUrl_1720_, lean_object* v_inputRev_x3f_1721_, lean_object* v_subDir_x3f_1722_, lean_object* v_a_1723_){
_start:
{
uint8_t v_inherited_boxed_1724_; lean_object* v_res_1725_; 
v_inherited_boxed_1724_ = lean_unbox(v_inherited_1714_);
v_res_1725_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(v_a_1712_, v_dep_1713_, v_inherited_boxed_1724_, v_lakeEnv_1715_, v_wsDir_1716_, v_name_1717_, v_relPkgDir_1718_, v_gitUrl_1719_, v_remoteUrl_1720_, v_inputRev_x3f_1721_, v_subDir_x3f_1722_);
lean_dec_ref(v_lakeEnv_1715_);
lean_dec_ref(v_a_1712_);
return v_res_1725_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(lean_object* v_ver_1729_, lean_object* v_as_1730_, size_t v_sz_1731_, size_t v_i_1732_, lean_object* v_b_1733_){
_start:
{
uint8_t v___x_1734_; 
v___x_1734_ = lean_usize_dec_lt(v_i_1732_, v_sz_1731_);
if (v___x_1734_ == 0)
{
lean_inc_ref(v_b_1733_);
return v_b_1733_;
}
else
{
lean_object* v_a_1735_; lean_object* v_version_1736_; lean_object* v___x_1737_; uint8_t v___x_1738_; 
v_a_1735_ = lean_array_uget_borrowed(v_as_1730_, v_i_1732_);
v_version_1736_ = lean_ctor_get(v_a_1735_, 0);
v___x_1737_ = lean_box(0);
v___x_1738_ = l_Lake_VerRange_test(v_ver_1729_, v_version_1736_);
if (v___x_1738_ == 0)
{
lean_object* v___x_1739_; size_t v___x_1740_; size_t v___x_1741_; 
v___x_1739_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___closed__0));
v___x_1740_ = ((size_t)1ULL);
v___x_1741_ = lean_usize_add(v_i_1732_, v___x_1740_);
v_i_1732_ = v___x_1741_;
v_b_1733_ = v___x_1739_;
goto _start;
}
else
{
lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
lean_inc(v_a_1735_);
v___x_1743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1743_, 0, v_a_1735_);
v___x_1744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1744_, 0, v___x_1743_);
v___x_1745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1745_, 0, v___x_1744_);
lean_ctor_set(v___x_1745_, 1, v___x_1737_);
return v___x_1745_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___boxed(lean_object* v_ver_1746_, lean_object* v_as_1747_, lean_object* v_sz_1748_, lean_object* v_i_1749_, lean_object* v_b_1750_){
_start:
{
size_t v_sz_boxed_1751_; size_t v_i_boxed_1752_; lean_object* v_res_1753_; 
v_sz_boxed_1751_ = lean_unbox_usize(v_sz_1748_);
lean_dec(v_sz_1748_);
v_i_boxed_1752_ = lean_unbox_usize(v_i_1749_);
lean_dec(v_i_1749_);
v_res_1753_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(v_ver_1746_, v_as_1747_, v_sz_boxed_1751_, v_i_boxed_1752_, v_b_1750_);
lean_dec_ref(v_b_1750_);
lean_dec_ref(v_as_1747_);
lean_dec_ref(v_ver_1746_);
return v_res_1753_;
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize(lean_object* v_dep_1763_, uint8_t v_inherited_1764_, lean_object* v_lakeEnv_1765_, lean_object* v_wsDir_1766_, lean_object* v_relPkgsDir_1767_, lean_object* v_relParentDir_1768_, lean_object* v_a_1769_){
_start:
{
lean_object* v___y_1775_; lean_object* v___y_1776_; lean_object* v___y_1786_; lean_object* v___y_1787_; lean_object* v___y_1788_; lean_object* v___y_1789_; lean_object* v___y_1790_; lean_object* v___y_1791_; lean_object* v___y_1795_; lean_object* v___y_1796_; lean_object* v___y_1797_; lean_object* v___y_1798_; lean_object* v___y_1799_; lean_object* v_a_1800_; lean_object* v_src_x3f_1803_; 
v_src_x3f_1803_ = lean_ctor_get(v_dep_1763_, 3);
lean_inc(v_src_x3f_1803_);
if (lean_obj_tag(v_src_x3f_1803_) == 1)
{
lean_object* v_val_1804_; lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1952_; 
v_val_1804_ = lean_ctor_get(v_src_x3f_1803_, 0);
v_isSharedCheck_1952_ = !lean_is_exclusive(v_src_x3f_1803_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1806_ = v_src_x3f_1803_;
v_isShared_1807_ = v_isSharedCheck_1952_;
goto v_resetjp_1805_;
}
else
{
lean_inc(v_val_1804_);
lean_dec(v_src_x3f_1803_);
v___x_1806_ = lean_box(0);
v_isShared_1807_ = v_isSharedCheck_1952_;
goto v_resetjp_1805_;
}
v_resetjp_1805_:
{
if (lean_obj_tag(v_val_1804_) == 0)
{
lean_object* v_name_1808_; lean_object* v_scope_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1935_; 
lean_dec_ref(v_relPkgsDir_1767_);
lean_dec_ref(v_lakeEnv_1765_);
v_name_1808_ = lean_ctor_get(v_dep_1763_, 0);
v_scope_1809_ = lean_ctor_get(v_dep_1763_, 1);
v_isSharedCheck_1935_ = !lean_is_exclusive(v_dep_1763_);
if (v_isSharedCheck_1935_ == 0)
{
lean_object* v_unused_1936_; lean_object* v_unused_1937_; lean_object* v_unused_1938_; 
v_unused_1936_ = lean_ctor_get(v_dep_1763_, 4);
lean_dec(v_unused_1936_);
v_unused_1937_ = lean_ctor_get(v_dep_1763_, 3);
lean_dec(v_unused_1937_);
v_unused_1938_ = lean_ctor_get(v_dep_1763_, 2);
lean_dec(v_unused_1938_);
v___x_1811_ = v_dep_1763_;
v_isShared_1812_ = v_isSharedCheck_1935_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_scope_1809_);
lean_inc(v_name_1808_);
lean_dec(v_dep_1763_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1935_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v_dir_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1934_; 
v_dir_1813_ = lean_ctor_get(v_val_1804_, 0);
v_isSharedCheck_1934_ = !lean_is_exclusive(v_val_1804_);
if (v_isSharedCheck_1934_ == 0)
{
v___x_1815_ = v_val_1804_;
v_isShared_1816_ = v_isSharedCheck_1934_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_dir_1813_);
lean_dec(v_val_1804_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1934_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v_relPkgDir_1817_; lean_object* v___x_1819_; 
v_relPkgDir_1817_ = l_Lake_joinRelative(v_relParentDir_1768_, v_dir_1813_);
lean_inc_ref(v_relPkgDir_1817_);
if (v_isShared_1816_ == 0)
{
lean_ctor_set(v___x_1815_, 0, v_relPkgDir_1817_);
v___x_1819_ = v___x_1815_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v_relPkgDir_1817_);
v___x_1819_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
lean_object* v_pkgDir_1820_; lean_object* v___x_1821_; uint8_t v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___y_1826_; lean_object* v_a_1827_; lean_object* v___y_1836_; lean_object* v___y_1837_; lean_object* v___y_1838_; lean_object* v_val_1839_; lean_object* v_a_1867_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v_val_1901_; lean_object* v___x_1927_; uint8_t v___x_1928_; 
lean_inc_ref(v_relPkgDir_1817_);
v_pkgDir_1820_ = l_Lake_joinRelative(v_wsDir_1766_, v_relPkgDir_1817_);
lean_inc_ref(v_pkgDir_1820_);
v___x_1821_ = l_Lake_resolvePath(v_pkgDir_1820_);
v___x_1822_ = 0;
lean_inc(v_name_1808_);
v___x_1823_ = l_Lean_Name_toString(v_name_1808_, v___x_1822_);
v___x_1824_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___x_1898_ = lean_unsigned_to_nat(0u);
v___x_1899_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0));
v___x_1927_ = lean_string_utf8_byte_size(v___x_1821_);
v___x_1928_ = lean_nat_dec_eq(v___x_1927_, v___x_1898_);
if (v___x_1928_ == 0)
{
lean_object* v___x_1930_; 
if (v_isShared_1807_ == 0)
{
lean_ctor_set(v___x_1806_, 0, v___x_1821_);
v___x_1930_ = v___x_1806_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v___x_1821_);
v___x_1930_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
v_val_1901_ = v___x_1930_;
goto v___jp_1900_;
}
}
else
{
lean_object* v___x_1932_; 
lean_dec_ref(v___x_1821_);
lean_del_object(v___x_1806_);
v___x_1932_ = lean_box(0);
v_val_1901_ = v___x_1932_;
goto v___jp_1900_;
}
v___jp_1825_:
{
lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1832_; 
v___x_1828_ = l_Lake_defaultConfigFile;
v___x_1829_ = lean_box(0);
v___x_1830_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1830_, 0, v_name_1808_);
lean_ctor_set(v___x_1830_, 1, v_scope_1809_);
lean_ctor_set(v___x_1830_, 2, v___x_1828_);
lean_ctor_set(v___x_1830_, 3, v___x_1829_);
lean_ctor_set(v___x_1830_, 4, v___x_1819_);
lean_ctor_set_uint8(v___x_1830_, sizeof(void*)*5, v_inherited_1764_);
if (v_isShared_1812_ == 0)
{
lean_ctor_set(v___x_1811_, 4, v___x_1830_);
lean_ctor_set(v___x_1811_, 3, v_a_1827_);
lean_ctor_set(v___x_1811_, 2, v___x_1824_);
lean_ctor_set(v___x_1811_, 1, v_relPkgDir_1817_);
lean_ctor_set(v___x_1811_, 0, v___y_1826_);
v___x_1832_ = v___x_1811_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v___y_1826_);
lean_ctor_set(v_reuseFailAlloc_1834_, 1, v_relPkgDir_1817_);
lean_ctor_set(v_reuseFailAlloc_1834_, 2, v___x_1824_);
lean_ctor_set(v_reuseFailAlloc_1834_, 3, v_a_1827_);
lean_ctor_set(v_reuseFailAlloc_1834_, 4, v___x_1830_);
v___x_1832_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
lean_object* v___x_1833_; 
v___x_1833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1832_);
return v___x_1833_;
}
}
v___jp_1835_:
{
lean_object* v___x_1840_; uint8_t v___x_1841_; 
v___x_1840_ = lean_array_get_size(v___y_1838_);
v___x_1841_ = lean_nat_dec_lt(v___y_1837_, v___x_1840_);
if (v___x_1841_ == 0)
{
v___y_1826_ = v___y_1836_;
v_a_1827_ = v_val_1839_;
goto v___jp_1825_;
}
else
{
lean_object* v___x_1842_; uint8_t v___x_1843_; 
v___x_1842_ = lean_box(0);
v___x_1843_ = lean_nat_dec_le(v___x_1840_, v___x_1840_);
if (v___x_1843_ == 0)
{
if (v___x_1841_ == 0)
{
v___y_1826_ = v___y_1836_;
v_a_1827_ = v_val_1839_;
goto v___jp_1825_;
}
else
{
size_t v___x_1844_; size_t v___x_1845_; lean_object* v___x_1846_; 
v___x_1844_ = ((size_t)0ULL);
v___x_1845_ = lean_usize_of_nat(v___x_1840_);
v___x_1846_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_1838_, v___x_1844_, v___x_1845_, v___x_1842_, v_a_1769_);
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_dec_ref_known(v___x_1846_, 1);
v___y_1826_ = v___y_1836_;
v_a_1827_ = v_val_1839_;
goto v___jp_1825_;
}
else
{
lean_object* v_a_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1854_; 
lean_dec_ref(v_val_1839_);
lean_dec_ref(v___y_1836_);
lean_dec_ref(v___x_1819_);
lean_dec_ref(v_relPkgDir_1817_);
lean_del_object(v___x_1811_);
lean_dec_ref(v_scope_1809_);
lean_dec(v_name_1808_);
v_a_1847_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1849_ = v___x_1846_;
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_a_1847_);
lean_dec(v___x_1846_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___x_1852_; 
if (v_isShared_1850_ == 0)
{
v___x_1852_ = v___x_1849_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_a_1847_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
}
}
}
else
{
size_t v___x_1855_; size_t v___x_1856_; lean_object* v___x_1857_; 
v___x_1855_ = ((size_t)0ULL);
v___x_1856_ = lean_usize_of_nat(v___x_1840_);
v___x_1857_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_1838_, v___x_1855_, v___x_1856_, v___x_1842_, v_a_1769_);
if (lean_obj_tag(v___x_1857_) == 0)
{
lean_dec_ref_known(v___x_1857_, 1);
v___y_1826_ = v___y_1836_;
v_a_1827_ = v_val_1839_;
goto v___jp_1825_;
}
else
{
lean_object* v_a_1858_; lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_1865_; 
lean_dec_ref(v_val_1839_);
lean_dec_ref(v___y_1836_);
lean_dec_ref(v___x_1819_);
lean_dec_ref(v_relPkgDir_1817_);
lean_del_object(v___x_1811_);
lean_dec_ref(v_scope_1809_);
lean_dec(v_name_1808_);
v_a_1858_ = lean_ctor_get(v___x_1857_, 0);
v_isSharedCheck_1865_ = !lean_is_exclusive(v___x_1857_);
if (v_isSharedCheck_1865_ == 0)
{
v___x_1860_ = v___x_1857_;
v_isShared_1861_ = v_isSharedCheck_1865_;
goto v_resetjp_1859_;
}
else
{
lean_inc(v_a_1858_);
lean_dec(v___x_1857_);
v___x_1860_ = lean_box(0);
v_isShared_1861_ = v_isSharedCheck_1865_;
goto v_resetjp_1859_;
}
v_resetjp_1859_:
{
lean_object* v___x_1863_; 
if (v_isShared_1861_ == 0)
{
v___x_1863_ = v___x_1860_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v_a_1858_);
v___x_1863_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
return v___x_1863_;
}
}
}
}
}
}
v___jp_1866_:
{
if (lean_obj_tag(v_a_1867_) == 1)
{
lean_object* v_val_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; 
lean_dec_ref(v___x_1823_);
lean_dec_ref(v_pkgDir_1820_);
v_val_1868_ = lean_ctor_get(v_a_1867_, 0);
lean_inc_n(v_val_1868_, 2);
lean_dec_ref_known(v_a_1867_, 1);
v___x_1869_ = l_Lake_defaultManifestFile;
v___x_1870_ = l_Lake_joinRelative(v_val_1868_, v___x_1869_);
v___x_1871_ = lean_unsigned_to_nat(0u);
v___x_1872_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0));
v___x_1873_ = l_Lake_Manifest_load(v___x_1870_);
if (lean_obj_tag(v___x_1873_) == 0)
{
lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1881_; 
v_a_1874_ = lean_ctor_get(v___x_1873_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1876_ = v___x_1873_;
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1873_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1879_; 
if (v_isShared_1877_ == 0)
{
lean_ctor_set_tag(v___x_1876_, 1);
v___x_1879_ = v___x_1876_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_a_1874_);
v___x_1879_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
v___y_1836_ = v_val_1868_;
v___y_1837_ = v___x_1871_;
v___y_1838_ = v___x_1872_;
v_val_1839_ = v___x_1879_;
goto v___jp_1835_;
}
}
}
else
{
lean_object* v_a_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1889_; 
v_a_1882_ = lean_ctor_get(v___x_1873_, 0);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1884_ = v___x_1873_;
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_a_1882_);
lean_dec(v___x_1873_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1887_; 
if (v_isShared_1885_ == 0)
{
lean_ctor_set_tag(v___x_1884_, 0);
v___x_1887_ = v___x_1884_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_a_1882_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
v___y_1836_ = v_val_1868_;
v___y_1837_ = v___x_1871_;
v___y_1838_ = v___x_1872_;
v_val_1839_ = v___x_1887_;
goto v___jp_1835_;
}
}
}
}
else
{
lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; uint8_t v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; 
lean_dec(v_a_1867_);
lean_dec_ref(v___x_1819_);
lean_dec_ref(v_relPkgDir_1817_);
lean_del_object(v___x_1811_);
lean_dec_ref(v_scope_1809_);
lean_dec(v_name_1808_);
v___x_1890_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__3));
v___x_1891_ = lean_string_append(v___x_1823_, v___x_1890_);
v___x_1892_ = lean_string_append(v___x_1891_, v_pkgDir_1820_);
lean_dec_ref(v_pkgDir_1820_);
v___x_1893_ = 3;
v___x_1894_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1894_, 0, v___x_1892_);
lean_ctor_set_uint8(v___x_1894_, sizeof(void*)*1, v___x_1893_);
lean_inc_ref(v_a_1769_);
v___x_1895_ = lean_apply_2(v_a_1769_, v___x_1894_, lean_box(0));
v___x_1896_ = lean_box(0);
v___x_1897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1897_, 0, v___x_1896_);
return v___x_1897_;
}
}
v___jp_1900_:
{
uint8_t v___x_1902_; 
v___x_1902_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__6);
if (v___x_1902_ == 0)
{
v_a_1867_ = v_val_1901_;
goto v___jp_1866_;
}
else
{
lean_object* v___x_1903_; uint8_t v___x_1904_; 
v___x_1903_ = lean_box(0);
v___x_1904_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__7);
if (v___x_1904_ == 0)
{
if (v___x_1902_ == 0)
{
v_a_1867_ = v_val_1901_;
goto v___jp_1866_;
}
else
{
size_t v___x_1905_; size_t v___x_1906_; lean_object* v___x_1907_; 
v___x_1905_ = ((size_t)0ULL);
v___x_1906_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8);
v___x_1907_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_1899_, v___x_1905_, v___x_1906_, v___x_1903_, v_a_1769_);
if (lean_obj_tag(v___x_1907_) == 0)
{
lean_dec_ref_known(v___x_1907_, 1);
v_a_1867_ = v_val_1901_;
goto v___jp_1866_;
}
else
{
lean_object* v_a_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1915_; 
lean_dec(v_val_1901_);
lean_dec_ref(v___x_1823_);
lean_dec_ref(v_pkgDir_1820_);
lean_dec_ref(v___x_1819_);
lean_dec_ref(v_relPkgDir_1817_);
lean_del_object(v___x_1811_);
lean_dec_ref(v_scope_1809_);
lean_dec(v_name_1808_);
v_a_1908_ = lean_ctor_get(v___x_1907_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1907_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1910_ = v___x_1907_;
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_a_1908_);
lean_dec(v___x_1907_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v___x_1913_; 
if (v_isShared_1911_ == 0)
{
v___x_1913_ = v___x_1910_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_a_1908_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
}
}
}
else
{
size_t v___x_1916_; size_t v___x_1917_; lean_object* v___x_1918_; 
v___x_1916_ = ((size_t)0ULL);
v___x_1917_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8);
v___x_1918_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_1899_, v___x_1916_, v___x_1917_, v___x_1903_, v_a_1769_);
if (lean_obj_tag(v___x_1918_) == 0)
{
lean_dec_ref_known(v___x_1918_, 1);
v_a_1867_ = v_val_1901_;
goto v___jp_1866_;
}
else
{
lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1926_; 
lean_dec(v_val_1901_);
lean_dec_ref(v___x_1823_);
lean_dec_ref(v_pkgDir_1820_);
lean_dec_ref(v___x_1819_);
lean_dec_ref(v_relPkgDir_1817_);
lean_del_object(v___x_1811_);
lean_dec_ref(v_scope_1809_);
lean_dec(v_name_1808_);
v_a_1919_ = lean_ctor_get(v___x_1918_, 0);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1921_ = v___x_1918_;
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v___x_1918_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1924_; 
if (v_isShared_1922_ == 0)
{
v___x_1924_ = v___x_1921_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_a_1919_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
return v___x_1924_;
}
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
lean_object* v_name_1939_; lean_object* v_url_1940_; lean_object* v_rev_1941_; lean_object* v_subDir_1942_; lean_object* v___y_1944_; lean_object* v___x_1949_; 
lean_del_object(v___x_1806_);
lean_dec_ref(v_relParentDir_1768_);
v_name_1939_ = lean_ctor_get(v_dep_1763_, 0);
v_url_1940_ = lean_ctor_get(v_val_1804_, 0);
lean_inc_ref_n(v_url_1940_, 2);
v_rev_1941_ = lean_ctor_get(v_val_1804_, 1);
lean_inc(v_rev_1941_);
v_subDir_1942_ = lean_ctor_get(v_val_1804_, 2);
lean_inc(v_subDir_1942_);
lean_dec_ref_known(v_val_1804_, 3);
v___x_1949_ = l_Lake_Git_filterUrl_x3f(v_url_1940_);
if (lean_obj_tag(v___x_1949_) == 0)
{
lean_object* v___x_1950_; 
v___x_1950_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___y_1944_ = v___x_1950_;
goto v___jp_1943_;
}
else
{
lean_object* v_val_1951_; 
v_val_1951_ = lean_ctor_get(v___x_1949_, 0);
lean_inc(v_val_1951_);
lean_dec_ref_known(v___x_1949_, 1);
v___y_1944_ = v_val_1951_;
goto v___jp_1943_;
}
v___jp_1943_:
{
uint8_t v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; 
v___x_1945_ = 0;
lean_inc(v_name_1939_);
v___x_1946_ = l_Lean_Name_toString(v_name_1939_, v___x_1945_);
lean_inc_ref(v___x_1946_);
v___x_1947_ = l_Lake_joinRelative(v_relPkgsDir_1767_, v___x_1946_);
v___x_1948_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(v_a_1769_, v_dep_1763_, v_inherited_1764_, v_lakeEnv_1765_, v_wsDir_1766_, v___x_1946_, v___x_1947_, v_url_1940_, v___y_1944_, v_rev_1941_, v_subDir_1942_);
lean_dec_ref(v_lakeEnv_1765_);
return v___x_1948_;
}
}
}
}
else
{
lean_object* v_name_1953_; lean_object* v_scope_1954_; lean_object* v_version_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; uint8_t v___x_1958_; 
lean_dec(v_src_x3f_1803_);
lean_dec_ref(v_relParentDir_1768_);
v_name_1953_ = lean_ctor_get(v_dep_1763_, 0);
v_scope_1954_ = lean_ctor_get(v_dep_1763_, 1);
v_version_1955_ = lean_ctor_get(v_dep_1763_, 2);
v___x_1956_ = lean_string_utf8_byte_size(v_scope_1954_);
v___x_1957_ = lean_unsigned_to_nat(0u);
v___x_1958_ = lean_nat_dec_eq(v___x_1956_, v___x_1957_);
if (v___x_1958_ == 0)
{
lean_object* v___x_1959_; lean_object* v___y_1961_; lean_object* v___y_1977_; lean_object* v___y_1978_; lean_object* v___y_1979_; lean_object* v___y_1980_; lean_object* v___y_1981_; lean_object* v___y_1982_; lean_object* v_a_1983_; lean_object* v___y_2027_; lean_object* v___y_2028_; lean_object* v___y_2029_; lean_object* v___y_2030_; lean_object* v___y_2031_; lean_object* v___y_2032_; lean_object* v_fst_2033_; lean_object* v_snd_2034_; lean_object* v_a_2062_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v_fst_2197_; lean_object* v_snd_2198_; 
lean_inc(v_name_1953_);
v___x_1959_ = l_Lean_Name_toString(v_name_1953_, v___x_1958_);
v___x_2194_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0));
lean_inc_ref(v___x_1959_);
lean_inc_ref(v_scope_1954_);
lean_inc_ref(v_lakeEnv_1765_);
v___x_2195_ = l_Lake_Reservoir_fetchPkg_x3f(v_lakeEnv_1765_, v_scope_1954_, v___x_1959_, v___x_2194_);
if (lean_obj_tag(v___x_2195_) == 0)
{
lean_object* v_a_2225_; lean_object* v_a_2226_; lean_object* v___x_2227_; 
v_a_2225_ = lean_ctor_get(v___x_2195_, 0);
lean_inc(v_a_2225_);
v_a_2226_ = lean_ctor_get(v___x_2195_, 1);
lean_inc(v_a_2226_);
lean_dec_ref_known(v___x_2195_, 2);
v___x_2227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2227_, 0, v_a_2225_);
v_fst_2197_ = v___x_2227_;
v_snd_2198_ = v_a_2226_;
goto v___jp_2196_;
}
else
{
lean_object* v_a_2228_; lean_object* v_a_2229_; lean_object* v___x_2230_; 
v_a_2228_ = lean_ctor_get(v___x_2195_, 0);
lean_inc(v_a_2228_);
v_a_2229_ = lean_ctor_get(v___x_2195_, 1);
lean_inc(v_a_2229_);
lean_dec_ref_known(v___x_2195_, 2);
v___x_2230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2230_, 0, v_a_2228_);
v_fst_2197_ = v___x_2230_;
v_snd_2198_ = v_a_2229_;
goto v___jp_2196_;
}
v___jp_1960_:
{
lean_object* v_toString_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; uint8_t v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; 
v_toString_1962_ = lean_ctor_get(v___y_1961_, 0);
lean_inc_ref(v_toString_1962_);
lean_dec_ref(v___y_1961_);
v___x_1963_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
v___x_1964_ = lean_string_append(v_scope_1954_, v___x_1963_);
v___x_1965_ = lean_string_append(v___x_1964_, v___x_1959_);
lean_dec_ref(v___x_1959_);
v___x_1966_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__1));
v___x_1967_ = lean_string_append(v___x_1965_, v___x_1966_);
v___x_1968_ = lean_string_append(v___x_1967_, v_toString_1962_);
lean_dec_ref(v_toString_1962_);
v___x_1969_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__2));
v___x_1970_ = lean_string_append(v___x_1968_, v___x_1969_);
v___x_1971_ = 3;
v___x_1972_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1972_, 0, v___x_1970_);
lean_ctor_set_uint8(v___x_1972_, sizeof(void*)*1, v___x_1971_);
lean_inc_ref(v_a_1769_);
v___x_1973_ = lean_apply_2(v_a_1769_, v___x_1972_, lean_box(0));
v___x_1974_ = lean_box(0);
v___x_1975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1975_, 0, v___x_1974_);
return v___x_1975_;
}
v___jp_1976_:
{
if (lean_obj_tag(v_a_1983_) == 0)
{
lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_1999_; 
lean_inc_ref(v_scope_1954_);
lean_dec(v___y_1982_);
lean_dec_ref(v___y_1981_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
lean_dec_ref(v___y_1978_);
lean_dec_ref(v___y_1977_);
lean_dec_ref(v_wsDir_1766_);
lean_dec_ref(v_lakeEnv_1765_);
lean_dec_ref(v_dep_1763_);
v_isSharedCheck_1999_ = !lean_is_exclusive(v_a_1983_);
if (v_isSharedCheck_1999_ == 0)
{
lean_object* v_unused_2000_; 
v_unused_2000_ = lean_ctor_get(v_a_1983_, 0);
lean_dec(v_unused_2000_);
v___x_1985_ = v_a_1983_;
v_isShared_1986_ = v_isSharedCheck_1999_;
goto v_resetjp_1984_;
}
else
{
lean_dec(v_a_1983_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_1999_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; uint8_t v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1997_; 
v___x_1987_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
v___x_1988_ = lean_string_append(v_scope_1954_, v___x_1987_);
v___x_1989_ = lean_string_append(v___x_1988_, v___x_1959_);
lean_dec_ref(v___x_1959_);
v___x_1990_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__3));
v___x_1991_ = lean_string_append(v___x_1989_, v___x_1990_);
v___x_1992_ = 3;
v___x_1993_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1993_, 0, v___x_1991_);
lean_ctor_set_uint8(v___x_1993_, sizeof(void*)*1, v___x_1992_);
lean_inc_ref(v_a_1769_);
v___x_1994_ = lean_apply_2(v_a_1769_, v___x_1993_, lean_box(0));
v___x_1995_ = lean_box(0);
if (v_isShared_1986_ == 0)
{
lean_ctor_set_tag(v___x_1985_, 1);
lean_ctor_set(v___x_1985_, 0, v___x_1995_);
v___x_1997_ = v___x_1985_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v___x_1995_);
v___x_1997_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
return v___x_1997_;
}
}
}
else
{
lean_object* v_a_2001_; lean_object* v___x_2002_; size_t v_sz_2003_; size_t v___x_2004_; lean_object* v___x_2005_; lean_object* v_fst_2006_; 
v_a_2001_ = lean_ctor_get(v_a_1983_, 0);
lean_inc(v_a_2001_);
lean_dec_ref_known(v_a_1983_, 1);
v___x_2002_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___closed__0));
v_sz_2003_ = lean_array_size(v_a_2001_);
v___x_2004_ = ((size_t)0ULL);
v___x_2005_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(v___y_1977_, v_a_2001_, v_sz_2003_, v___x_2004_, v___x_2002_);
lean_dec(v_a_2001_);
v_fst_2006_ = lean_ctor_get(v___x_2005_, 0);
lean_inc(v_fst_2006_);
lean_dec_ref(v___x_2005_);
if (lean_obj_tag(v_fst_2006_) == 0)
{
lean_inc_ref(v_scope_1954_);
lean_dec(v___y_1982_);
lean_dec_ref(v___y_1981_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
lean_dec_ref(v___y_1978_);
lean_dec_ref(v_wsDir_1766_);
lean_dec_ref(v_lakeEnv_1765_);
lean_dec_ref(v_dep_1763_);
v___y_1961_ = v___y_1977_;
goto v___jp_1960_;
}
else
{
lean_object* v_val_2007_; 
v_val_2007_ = lean_ctor_get(v_fst_2006_, 0);
lean_inc(v_val_2007_);
lean_dec_ref_known(v_fst_2006_, 1);
if (lean_obj_tag(v_val_2007_) == 1)
{
lean_object* v_val_2008_; lean_object* v_version_2009_; lean_object* v_revision_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; uint8_t v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; 
lean_dec_ref(v___y_1977_);
v_val_2008_ = lean_ctor_get(v_val_2007_, 0);
lean_inc(v_val_2008_);
lean_dec_ref_known(v_val_2007_, 1);
v_version_2009_ = lean_ctor_get(v_val_2008_, 0);
lean_inc_ref(v_version_2009_);
v_revision_2010_ = lean_ctor_get(v_val_2008_, 1);
lean_inc_ref(v_revision_2010_);
lean_dec(v_val_2008_);
v___x_2011_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
lean_inc_ref(v_scope_1954_);
v___x_2012_ = lean_string_append(v_scope_1954_, v___x_2011_);
v___x_2013_ = lean_string_append(v___x_2012_, v___x_1959_);
lean_dec_ref(v___x_1959_);
v___x_2014_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__4));
v___x_2015_ = lean_string_append(v___x_2013_, v___x_2014_);
v___x_2016_ = l_Lake_StdVer_toString(v_version_2009_);
v___x_2017_ = lean_string_append(v___x_2015_, v___x_2016_);
lean_dec_ref(v___x_2016_);
v___x_2018_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__5));
v___x_2019_ = lean_string_append(v___x_2017_, v___x_2018_);
v___x_2020_ = lean_string_append(v___x_2019_, v_revision_2010_);
v___x_2021_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__6));
v___x_2022_ = lean_string_append(v___x_2020_, v___x_2021_);
v___x_2023_ = 1;
v___x_2024_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2024_, 0, v___x_2022_);
lean_ctor_set_uint8(v___x_2024_, sizeof(void*)*1, v___x_2023_);
lean_inc_ref(v_a_1769_);
v___x_2025_ = lean_apply_2(v_a_1769_, v___x_2024_, lean_box(0));
v___y_1795_ = v___y_1978_;
v___y_1796_ = v___y_1979_;
v___y_1797_ = v___y_1980_;
v___y_1798_ = v___y_1982_;
v___y_1799_ = v___y_1981_;
v_a_1800_ = v_revision_2010_;
goto v___jp_1794_;
}
else
{
lean_inc_ref(v_scope_1954_);
lean_dec(v_val_2007_);
lean_dec(v___y_1982_);
lean_dec_ref(v___y_1981_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
lean_dec_ref(v___y_1978_);
lean_dec_ref(v_wsDir_1766_);
lean_dec_ref(v_lakeEnv_1765_);
lean_dec_ref(v_dep_1763_);
v___y_1961_ = v___y_1977_;
goto v___jp_1960_;
}
}
}
}
v___jp_2026_:
{
lean_object* v___x_2035_; uint8_t v___x_2036_; 
v___x_2035_ = lean_array_get_size(v_snd_2034_);
v___x_2036_ = lean_nat_dec_lt(v___x_1957_, v___x_2035_);
if (v___x_2036_ == 0)
{
lean_dec_ref(v_snd_2034_);
v___y_1977_ = v___y_2027_;
v___y_1978_ = v___y_2028_;
v___y_1979_ = v___y_2029_;
v___y_1980_ = v___y_2030_;
v___y_1981_ = v___y_2032_;
v___y_1982_ = v___y_2031_;
v_a_1983_ = v_fst_2033_;
goto v___jp_1976_;
}
else
{
lean_object* v___x_2037_; uint8_t v___x_2038_; 
v___x_2037_ = lean_box(0);
v___x_2038_ = lean_nat_dec_le(v___x_2035_, v___x_2035_);
if (v___x_2038_ == 0)
{
if (v___x_2036_ == 0)
{
lean_dec_ref(v_snd_2034_);
v___y_1977_ = v___y_2027_;
v___y_1978_ = v___y_2028_;
v___y_1979_ = v___y_2029_;
v___y_1980_ = v___y_2030_;
v___y_1981_ = v___y_2032_;
v___y_1982_ = v___y_2031_;
v_a_1983_ = v_fst_2033_;
goto v___jp_1976_;
}
else
{
size_t v___x_2039_; size_t v___x_2040_; lean_object* v___x_2041_; 
v___x_2039_ = ((size_t)0ULL);
v___x_2040_ = lean_usize_of_nat(v___x_2035_);
v___x_2041_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_snd_2034_, v___x_2039_, v___x_2040_, v___x_2037_, v_a_1769_);
lean_dec_ref(v_snd_2034_);
if (lean_obj_tag(v___x_2041_) == 0)
{
lean_dec_ref_known(v___x_2041_, 1);
v___y_1977_ = v___y_2027_;
v___y_1978_ = v___y_2028_;
v___y_1979_ = v___y_2029_;
v___y_1980_ = v___y_2030_;
v___y_1981_ = v___y_2032_;
v___y_1982_ = v___y_2031_;
v_a_1983_ = v_fst_2033_;
goto v___jp_1976_;
}
else
{
lean_object* v_a_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2049_; 
lean_dec_ref(v_fst_2033_);
lean_dec_ref(v___y_2032_);
lean_dec(v___y_2031_);
lean_dec(v___y_2030_);
lean_dec_ref(v___y_2029_);
lean_dec_ref(v___y_2028_);
lean_dec_ref(v___y_2027_);
lean_dec_ref(v___x_1959_);
lean_dec_ref(v_wsDir_1766_);
lean_dec_ref(v_lakeEnv_1765_);
lean_dec_ref(v_dep_1763_);
v_a_2042_ = lean_ctor_get(v___x_2041_, 0);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2044_ = v___x_2041_;
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_a_2042_);
lean_dec(v___x_2041_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v___x_2047_; 
if (v_isShared_2045_ == 0)
{
v___x_2047_ = v___x_2044_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_a_2042_);
v___x_2047_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
return v___x_2047_;
}
}
}
}
}
else
{
size_t v___x_2050_; size_t v___x_2051_; lean_object* v___x_2052_; 
v___x_2050_ = ((size_t)0ULL);
v___x_2051_ = lean_usize_of_nat(v___x_2035_);
v___x_2052_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_snd_2034_, v___x_2050_, v___x_2051_, v___x_2037_, v_a_1769_);
lean_dec_ref(v_snd_2034_);
if (lean_obj_tag(v___x_2052_) == 0)
{
lean_dec_ref_known(v___x_2052_, 1);
v___y_1977_ = v___y_2027_;
v___y_1978_ = v___y_2028_;
v___y_1979_ = v___y_2029_;
v___y_1980_ = v___y_2030_;
v___y_1981_ = v___y_2032_;
v___y_1982_ = v___y_2031_;
v_a_1983_ = v_fst_2033_;
goto v___jp_1976_;
}
else
{
lean_object* v_a_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2060_; 
lean_dec_ref(v_fst_2033_);
lean_dec_ref(v___y_2032_);
lean_dec(v___y_2031_);
lean_dec(v___y_2030_);
lean_dec_ref(v___y_2029_);
lean_dec_ref(v___y_2028_);
lean_dec_ref(v___y_2027_);
lean_dec_ref(v___x_1959_);
lean_dec_ref(v_wsDir_1766_);
lean_dec_ref(v_lakeEnv_1765_);
lean_dec_ref(v_dep_1763_);
v_a_2053_ = lean_ctor_get(v___x_2052_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_2052_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2055_ = v___x_2052_;
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_a_2053_);
lean_dec(v___x_2052_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v___x_2058_; 
if (v_isShared_2056_ == 0)
{
v___x_2058_ = v___x_2055_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_a_2053_);
v___x_2058_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
return v___x_2058_;
}
}
}
}
}
}
v___jp_2061_:
{
if (lean_obj_tag(v_a_2062_) == 0)
{
lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; uint8_t v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; 
lean_inc_ref(v_scope_1954_);
lean_dec_ref_known(v_a_2062_, 1);
lean_dec_ref(v_relPkgsDir_1767_);
lean_dec_ref(v_wsDir_1766_);
lean_dec_ref(v_lakeEnv_1765_);
lean_dec_ref(v_dep_1763_);
v___x_2063_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
v___x_2064_ = lean_string_append(v_scope_1954_, v___x_2063_);
v___x_2065_ = lean_string_append(v___x_2064_, v___x_1959_);
lean_dec_ref(v___x_1959_);
v___x_2066_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__7));
v___x_2067_ = lean_string_append(v___x_2065_, v___x_2066_);
v___x_2068_ = 3;
v___x_2069_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2069_, 0, v___x_2067_);
lean_ctor_set_uint8(v___x_2069_, sizeof(void*)*1, v___x_2068_);
lean_inc_ref(v_a_1769_);
v___x_2070_ = lean_apply_2(v_a_1769_, v___x_2069_, lean_box(0));
v___x_2071_ = lean_box(0);
v___x_2072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2072_, 0, v___x_2071_);
return v___x_2072_;
}
else
{
lean_object* v_a_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2193_; 
v_a_2073_ = lean_ctor_get(v_a_2062_, 0);
v_isSharedCheck_2193_ = !lean_is_exclusive(v_a_2062_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_2075_ = v_a_2062_;
v_isShared_2076_ = v_isSharedCheck_2193_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_a_2073_);
lean_dec(v_a_2062_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2193_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
if (lean_obj_tag(v_a_2073_) == 0)
{
lean_object* v___x_2077_; uint8_t v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; 
lean_del_object(v___x_2075_);
lean_dec_ref(v___x_1959_);
lean_dec_ref(v_relPkgsDir_1767_);
lean_dec_ref(v_wsDir_1766_);
lean_dec_ref(v_lakeEnv_1765_);
v___x_2077_ = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed(v_dep_1763_);
v___x_2078_ = 3;
v___x_2079_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2079_, 0, v___x_2077_);
lean_ctor_set_uint8(v___x_2079_, sizeof(void*)*1, v___x_2078_);
lean_inc_ref(v_a_1769_);
v___x_2080_ = lean_apply_2(v_a_1769_, v___x_2079_, lean_box(0));
v___x_2081_ = lean_box(0);
v___x_2082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2081_);
return v___x_2082_;
}
else
{
lean_object* v_val_2083_; lean_object* v___x_2084_; 
v_val_2083_ = lean_ctor_get(v_a_2073_, 0);
lean_inc(v_val_2083_);
lean_dec_ref_known(v_a_2073_, 1);
v___x_2084_ = l_Lake_RegistryPkg_gitSrc_x3f(v_val_2083_);
if (lean_obj_tag(v___x_2084_) == 1)
{
lean_object* v_val_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2192_; 
v_val_2085_ = lean_ctor_get(v___x_2084_, 0);
v_isSharedCheck_2192_ = !lean_is_exclusive(v___x_2084_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2087_ = v___x_2084_;
v_isShared_2088_ = v_isSharedCheck_2192_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_val_2085_);
lean_dec(v___x_2084_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2192_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
if (lean_obj_tag(v_val_2085_) == 0)
{
lean_object* v_url_2089_; lean_object* v_githubUrl_x3f_2090_; lean_object* v_defaultBranch_x3f_2091_; lean_object* v_subDir_x3f_2092_; lean_object* v_name_2093_; lean_object* v_fullName_2094_; lean_object* v___x_2095_; 
v_url_2089_ = lean_ctor_get(v_val_2085_, 1);
lean_inc_ref(v_url_2089_);
v_githubUrl_x3f_2090_ = lean_ctor_get(v_val_2085_, 2);
lean_inc(v_githubUrl_x3f_2090_);
v_defaultBranch_x3f_2091_ = lean_ctor_get(v_val_2085_, 3);
lean_inc(v_defaultBranch_x3f_2091_);
v_subDir_x3f_2092_ = lean_ctor_get(v_val_2085_, 4);
lean_inc(v_subDir_x3f_2092_);
lean_dec_ref_known(v_val_2085_, 5);
v_name_2093_ = lean_ctor_get(v_val_2083_, 0);
lean_inc_ref(v_name_2093_);
v_fullName_2094_ = lean_ctor_get(v_val_2083_, 1);
lean_inc_ref(v_fullName_2094_);
lean_dec(v_val_2083_);
v___x_2095_ = l_Lake_joinRelative(v_relPkgsDir_1767_, v_name_2093_);
switch(lean_obj_tag(v_version_1955_))
{
case 0:
{
lean_object* v___x_2096_; 
lean_del_object(v___x_2075_);
lean_dec_ref(v___x_1959_);
v___x_2096_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0));
if (lean_obj_tag(v_defaultBranch_x3f_2091_) == 0)
{
uint8_t v___x_2097_; 
lean_dec_ref(v___x_2095_);
lean_dec_ref(v_fullName_2094_);
lean_dec(v_subDir_x3f_2092_);
lean_dec(v_githubUrl_x3f_2090_);
lean_dec_ref(v_url_2089_);
lean_dec_ref(v_wsDir_1766_);
lean_dec_ref(v_lakeEnv_1765_);
lean_dec_ref(v_dep_1763_);
v___x_2097_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__6);
if (v___x_2097_ == 0)
{
lean_object* v___x_2098_; lean_object* v___x_2100_; 
v___x_2098_ = lean_box(0);
if (v_isShared_2088_ == 0)
{
lean_ctor_set(v___x_2087_, 0, v___x_2098_);
v___x_2100_ = v___x_2087_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v___x_2098_);
v___x_2100_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
return v___x_2100_;
}
}
else
{
lean_object* v___x_2102_; uint8_t v___x_2103_; 
lean_del_object(v___x_2087_);
v___x_2102_ = lean_box(0);
v___x_2103_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__7);
if (v___x_2103_ == 0)
{
if (v___x_2097_ == 0)
{
goto v___jp_1771_;
}
else
{
size_t v___x_2104_; size_t v___x_2105_; lean_object* v___x_2106_; 
v___x_2104_ = ((size_t)0ULL);
v___x_2105_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8);
v___x_2106_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_2096_, v___x_2104_, v___x_2105_, v___x_2102_, v_a_1769_);
if (lean_obj_tag(v___x_2106_) == 0)
{
lean_dec_ref_known(v___x_2106_, 1);
goto v___jp_1771_;
}
else
{
lean_object* v_a_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2114_; 
v_a_2107_ = lean_ctor_get(v___x_2106_, 0);
v_isSharedCheck_2114_ = !lean_is_exclusive(v___x_2106_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_2109_ = v___x_2106_;
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_a_2107_);
lean_dec(v___x_2106_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v___x_2112_; 
if (v_isShared_2110_ == 0)
{
v___x_2112_ = v___x_2109_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v_a_2107_);
v___x_2112_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
return v___x_2112_;
}
}
}
}
}
else
{
size_t v___x_2115_; size_t v___x_2116_; lean_object* v___x_2117_; 
v___x_2115_ = ((size_t)0ULL);
v___x_2116_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8);
v___x_2117_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_2096_, v___x_2115_, v___x_2116_, v___x_2102_, v_a_1769_);
if (lean_obj_tag(v___x_2117_) == 0)
{
lean_dec_ref_known(v___x_2117_, 1);
goto v___jp_1771_;
}
else
{
lean_object* v_a_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2125_; 
v_a_2118_ = lean_ctor_get(v___x_2117_, 0);
v_isSharedCheck_2125_ = !lean_is_exclusive(v___x_2117_);
if (v_isSharedCheck_2125_ == 0)
{
v___x_2120_ = v___x_2117_;
v_isShared_2121_ = v_isSharedCheck_2125_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_a_2118_);
lean_dec(v___x_2117_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2125_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v___x_2123_; 
if (v_isShared_2121_ == 0)
{
v___x_2123_ = v___x_2120_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v_a_2118_);
v___x_2123_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
return v___x_2123_;
}
}
}
}
}
}
else
{
lean_object* v_val_2126_; uint8_t v___x_2127_; 
lean_del_object(v___x_2087_);
v_val_2126_ = lean_ctor_get(v_defaultBranch_x3f_2091_, 0);
lean_inc(v_val_2126_);
lean_dec_ref_known(v_defaultBranch_x3f_2091_, 1);
v___x_2127_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__6);
if (v___x_2127_ == 0)
{
v___y_1795_ = v_url_2089_;
v___y_1796_ = v_fullName_2094_;
v___y_1797_ = v_subDir_x3f_2092_;
v___y_1798_ = v_githubUrl_x3f_2090_;
v___y_1799_ = v___x_2095_;
v_a_1800_ = v_val_2126_;
goto v___jp_1794_;
}
else
{
lean_object* v___x_2128_; uint8_t v___x_2129_; 
v___x_2128_ = lean_box(0);
v___x_2129_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__7);
if (v___x_2129_ == 0)
{
if (v___x_2127_ == 0)
{
v___y_1795_ = v_url_2089_;
v___y_1796_ = v_fullName_2094_;
v___y_1797_ = v_subDir_x3f_2092_;
v___y_1798_ = v_githubUrl_x3f_2090_;
v___y_1799_ = v___x_2095_;
v_a_1800_ = v_val_2126_;
goto v___jp_1794_;
}
else
{
size_t v___x_2130_; size_t v___x_2131_; lean_object* v___x_2132_; 
v___x_2130_ = ((size_t)0ULL);
v___x_2131_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8);
v___x_2132_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_2096_, v___x_2130_, v___x_2131_, v___x_2128_, v_a_1769_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_dec_ref_known(v___x_2132_, 1);
v___y_1795_ = v_url_2089_;
v___y_1796_ = v_fullName_2094_;
v___y_1797_ = v_subDir_x3f_2092_;
v___y_1798_ = v_githubUrl_x3f_2090_;
v___y_1799_ = v___x_2095_;
v_a_1800_ = v_val_2126_;
goto v___jp_1794_;
}
else
{
lean_object* v_a_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2140_; 
lean_dec(v_val_2126_);
lean_dec_ref(v___x_2095_);
lean_dec_ref(v_fullName_2094_);
lean_dec(v_subDir_x3f_2092_);
lean_dec(v_githubUrl_x3f_2090_);
lean_dec_ref(v_url_2089_);
lean_dec_ref(v_wsDir_1766_);
lean_dec_ref(v_lakeEnv_1765_);
lean_dec_ref(v_dep_1763_);
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
v___x_2142_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8);
v___x_2143_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_2096_, v___x_2141_, v___x_2142_, v___x_2128_, v_a_1769_);
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_dec_ref_known(v___x_2143_, 1);
v___y_1795_ = v_url_2089_;
v___y_1796_ = v_fullName_2094_;
v___y_1797_ = v_subDir_x3f_2092_;
v___y_1798_ = v_githubUrl_x3f_2090_;
v___y_1799_ = v___x_2095_;
v_a_1800_ = v_val_2126_;
goto v___jp_1794_;
}
else
{
lean_object* v_a_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2151_; 
lean_dec(v_val_2126_);
lean_dec_ref(v___x_2095_);
lean_dec_ref(v_fullName_2094_);
lean_dec(v_subDir_x3f_2092_);
lean_dec(v_githubUrl_x3f_2090_);
lean_dec_ref(v_url_2089_);
lean_dec_ref(v_wsDir_1766_);
lean_dec_ref(v_lakeEnv_1765_);
lean_dec_ref(v_dep_1763_);
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
case 1:
{
lean_object* v_rev_2152_; lean_object* v___x_2153_; uint8_t v___x_2154_; 
lean_dec(v_defaultBranch_x3f_2091_);
lean_del_object(v___x_2087_);
lean_del_object(v___x_2075_);
lean_dec_ref(v___x_1959_);
v_rev_2152_ = lean_ctor_get(v_version_1955_, 0);
v___x_2153_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0));
v___x_2154_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__6);
if (v___x_2154_ == 0)
{
lean_inc_ref(v_rev_2152_);
v___y_1795_ = v_url_2089_;
v___y_1796_ = v_fullName_2094_;
v___y_1797_ = v_subDir_x3f_2092_;
v___y_1798_ = v_githubUrl_x3f_2090_;
v___y_1799_ = v___x_2095_;
v_a_1800_ = v_rev_2152_;
goto v___jp_1794_;
}
else
{
lean_object* v___x_2155_; uint8_t v___x_2156_; 
v___x_2155_ = lean_box(0);
v___x_2156_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__7);
if (v___x_2156_ == 0)
{
if (v___x_2154_ == 0)
{
lean_inc_ref(v_rev_2152_);
v___y_1795_ = v_url_2089_;
v___y_1796_ = v_fullName_2094_;
v___y_1797_ = v_subDir_x3f_2092_;
v___y_1798_ = v_githubUrl_x3f_2090_;
v___y_1799_ = v___x_2095_;
v_a_1800_ = v_rev_2152_;
goto v___jp_1794_;
}
else
{
size_t v___x_2157_; size_t v___x_2158_; lean_object* v___x_2159_; 
v___x_2157_ = ((size_t)0ULL);
v___x_2158_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8);
v___x_2159_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_2153_, v___x_2157_, v___x_2158_, v___x_2155_, v_a_1769_);
if (lean_obj_tag(v___x_2159_) == 0)
{
lean_dec_ref_known(v___x_2159_, 1);
lean_inc_ref(v_rev_2152_);
v___y_1795_ = v_url_2089_;
v___y_1796_ = v_fullName_2094_;
v___y_1797_ = v_subDir_x3f_2092_;
v___y_1798_ = v_githubUrl_x3f_2090_;
v___y_1799_ = v___x_2095_;
v_a_1800_ = v_rev_2152_;
goto v___jp_1794_;
}
else
{
lean_object* v_a_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2167_; 
lean_dec_ref(v___x_2095_);
lean_dec_ref(v_fullName_2094_);
lean_dec(v_subDir_x3f_2092_);
lean_dec(v_githubUrl_x3f_2090_);
lean_dec_ref(v_url_2089_);
lean_dec_ref(v_wsDir_1766_);
lean_dec_ref(v_lakeEnv_1765_);
lean_dec_ref(v_dep_1763_);
v_a_2160_ = lean_ctor_get(v___x_2159_, 0);
v_isSharedCheck_2167_ = !lean_is_exclusive(v___x_2159_);
if (v_isSharedCheck_2167_ == 0)
{
v___x_2162_ = v___x_2159_;
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_a_2160_);
lean_dec(v___x_2159_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v___x_2165_; 
if (v_isShared_2163_ == 0)
{
v___x_2165_ = v___x_2162_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v_a_2160_);
v___x_2165_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
return v___x_2165_;
}
}
}
}
}
else
{
size_t v___x_2168_; size_t v___x_2169_; lean_object* v___x_2170_; 
v___x_2168_ = ((size_t)0ULL);
v___x_2169_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8);
v___x_2170_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_2153_, v___x_2168_, v___x_2169_, v___x_2155_, v_a_1769_);
if (lean_obj_tag(v___x_2170_) == 0)
{
lean_dec_ref_known(v___x_2170_, 1);
lean_inc_ref(v_rev_2152_);
v___y_1795_ = v_url_2089_;
v___y_1796_ = v_fullName_2094_;
v___y_1797_ = v_subDir_x3f_2092_;
v___y_1798_ = v_githubUrl_x3f_2090_;
v___y_1799_ = v___x_2095_;
v_a_1800_ = v_rev_2152_;
goto v___jp_1794_;
}
else
{
lean_object* v_a_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2178_; 
lean_dec_ref(v___x_2095_);
lean_dec_ref(v_fullName_2094_);
lean_dec(v_subDir_x3f_2092_);
lean_dec(v_githubUrl_x3f_2090_);
lean_dec_ref(v_url_2089_);
lean_dec_ref(v_wsDir_1766_);
lean_dec_ref(v_lakeEnv_1765_);
lean_dec_ref(v_dep_1763_);
v_a_2171_ = lean_ctor_get(v___x_2170_, 0);
v_isSharedCheck_2178_ = !lean_is_exclusive(v___x_2170_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2173_ = v___x_2170_;
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_a_2171_);
lean_dec(v___x_2170_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v___x_2176_; 
if (v_isShared_2174_ == 0)
{
v___x_2176_ = v___x_2173_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_a_2171_);
v___x_2176_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
return v___x_2176_;
}
}
}
}
}
}
default: 
{
lean_object* v_ver_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; 
lean_dec(v_defaultBranch_x3f_2091_);
lean_del_object(v___x_2087_);
v_ver_2179_ = lean_ctor_get(v_version_1955_, 0);
v___x_2180_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0));
lean_inc_ref(v___x_1959_);
lean_inc_ref(v_scope_1954_);
lean_inc_ref(v_lakeEnv_1765_);
v___x_2181_ = l_Lake_Reservoir_fetchPkgVersions(v_lakeEnv_1765_, v_scope_1954_, v___x_1959_, v___x_2180_);
if (lean_obj_tag(v___x_2181_) == 0)
{
lean_object* v_a_2182_; lean_object* v_a_2183_; lean_object* v___x_2185_; 
v_a_2182_ = lean_ctor_get(v___x_2181_, 0);
lean_inc(v_a_2182_);
v_a_2183_ = lean_ctor_get(v___x_2181_, 1);
lean_inc(v_a_2183_);
lean_dec_ref_known(v___x_2181_, 2);
if (v_isShared_2076_ == 0)
{
lean_ctor_set(v___x_2075_, 0, v_a_2182_);
v___x_2185_ = v___x_2075_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_a_2182_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
lean_inc_ref(v_ver_2179_);
v___y_2027_ = v_ver_2179_;
v___y_2028_ = v_url_2089_;
v___y_2029_ = v_fullName_2094_;
v___y_2030_ = v_subDir_x3f_2092_;
v___y_2031_ = v_githubUrl_x3f_2090_;
v___y_2032_ = v___x_2095_;
v_fst_2033_ = v___x_2185_;
v_snd_2034_ = v_a_2183_;
goto v___jp_2026_;
}
}
else
{
lean_object* v_a_2187_; lean_object* v_a_2188_; lean_object* v___x_2190_; 
v_a_2187_ = lean_ctor_get(v___x_2181_, 0);
lean_inc(v_a_2187_);
v_a_2188_ = lean_ctor_get(v___x_2181_, 1);
lean_inc(v_a_2188_);
lean_dec_ref_known(v___x_2181_, 2);
if (v_isShared_2076_ == 0)
{
lean_ctor_set_tag(v___x_2075_, 0);
lean_ctor_set(v___x_2075_, 0, v_a_2187_);
v___x_2190_ = v___x_2075_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_a_2187_);
v___x_2190_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
lean_inc_ref(v_ver_2179_);
v___y_2027_ = v_ver_2179_;
v___y_2028_ = v_url_2089_;
v___y_2029_ = v_fullName_2094_;
v___y_2030_ = v_subDir_x3f_2092_;
v___y_2031_ = v_githubUrl_x3f_2090_;
v___y_2032_ = v___x_2095_;
v_fst_2033_ = v___x_2190_;
v_snd_2034_ = v_a_2188_;
goto v___jp_2026_;
}
}
}
}
}
else
{
lean_del_object(v___x_2087_);
lean_dec(v_val_2085_);
lean_del_object(v___x_2075_);
lean_dec_ref(v___x_1959_);
lean_dec_ref(v_relPkgsDir_1767_);
lean_dec_ref(v_wsDir_1766_);
lean_dec_ref(v_lakeEnv_1765_);
lean_dec_ref(v_dep_1763_);
v___y_1775_ = v_val_2083_;
v___y_1776_ = v_a_1769_;
goto v___jp_1774_;
}
}
}
else
{
lean_dec(v___x_2084_);
lean_del_object(v___x_2075_);
lean_dec_ref(v___x_1959_);
lean_dec_ref(v_relPkgsDir_1767_);
lean_dec_ref(v_wsDir_1766_);
lean_dec_ref(v_lakeEnv_1765_);
lean_dec_ref(v_dep_1763_);
v___y_1775_ = v_val_2083_;
v___y_1776_ = v_a_1769_;
goto v___jp_1774_;
}
}
}
}
}
v___jp_2196_:
{
lean_object* v___x_2199_; uint8_t v___x_2200_; 
v___x_2199_ = lean_array_get_size(v_snd_2198_);
v___x_2200_ = lean_nat_dec_lt(v___x_1957_, v___x_2199_);
if (v___x_2200_ == 0)
{
lean_dec_ref(v_snd_2198_);
v_a_2062_ = v_fst_2197_;
goto v___jp_2061_;
}
else
{
lean_object* v___x_2201_; uint8_t v___x_2202_; 
v___x_2201_ = lean_box(0);
v___x_2202_ = lean_nat_dec_le(v___x_2199_, v___x_2199_);
if (v___x_2202_ == 0)
{
if (v___x_2200_ == 0)
{
lean_dec_ref(v_snd_2198_);
v_a_2062_ = v_fst_2197_;
goto v___jp_2061_;
}
else
{
size_t v___x_2203_; size_t v___x_2204_; lean_object* v___x_2205_; 
v___x_2203_ = ((size_t)0ULL);
v___x_2204_ = lean_usize_of_nat(v___x_2199_);
v___x_2205_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_snd_2198_, v___x_2203_, v___x_2204_, v___x_2201_, v_a_1769_);
lean_dec_ref(v_snd_2198_);
if (lean_obj_tag(v___x_2205_) == 0)
{
lean_dec_ref_known(v___x_2205_, 1);
v_a_2062_ = v_fst_2197_;
goto v___jp_2061_;
}
else
{
lean_object* v_a_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2213_; 
lean_dec_ref(v_fst_2197_);
lean_dec_ref(v___x_1959_);
lean_dec_ref(v_relPkgsDir_1767_);
lean_dec_ref(v_wsDir_1766_);
lean_dec_ref(v_lakeEnv_1765_);
lean_dec_ref(v_dep_1763_);
v_a_2206_ = lean_ctor_get(v___x_2205_, 0);
v_isSharedCheck_2213_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2208_ = v___x_2205_;
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_a_2206_);
lean_dec(v___x_2205_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2211_; 
if (v_isShared_2209_ == 0)
{
v___x_2211_ = v___x_2208_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v_a_2206_);
v___x_2211_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
return v___x_2211_;
}
}
}
}
}
else
{
size_t v___x_2214_; size_t v___x_2215_; lean_object* v___x_2216_; 
v___x_2214_ = ((size_t)0ULL);
v___x_2215_ = lean_usize_of_nat(v___x_2199_);
v___x_2216_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_snd_2198_, v___x_2214_, v___x_2215_, v___x_2201_, v_a_1769_);
lean_dec_ref(v_snd_2198_);
if (lean_obj_tag(v___x_2216_) == 0)
{
lean_dec_ref_known(v___x_2216_, 1);
v_a_2062_ = v_fst_2197_;
goto v___jp_2061_;
}
else
{
lean_object* v_a_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2224_; 
lean_dec_ref(v_fst_2197_);
lean_dec_ref(v___x_1959_);
lean_dec_ref(v_relPkgsDir_1767_);
lean_dec_ref(v_wsDir_1766_);
lean_dec_ref(v_lakeEnv_1765_);
lean_dec_ref(v_dep_1763_);
v_a_2217_ = lean_ctor_get(v___x_2216_, 0);
v_isSharedCheck_2224_ = !lean_is_exclusive(v___x_2216_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2219_ = v___x_2216_;
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_a_2217_);
lean_dec(v___x_2216_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
lean_object* v___x_2222_; 
if (v_isShared_2220_ == 0)
{
v___x_2222_ = v___x_2219_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v_a_2217_);
v___x_2222_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
return v___x_2222_;
}
}
}
}
}
}
}
else
{
uint8_t v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; uint8_t v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; 
lean_inc(v_name_1953_);
lean_dec_ref(v_relPkgsDir_1767_);
lean_dec_ref(v_wsDir_1766_);
lean_dec_ref(v_lakeEnv_1765_);
lean_dec_ref(v_dep_1763_);
v___x_2231_ = 0;
v___x_2232_ = l_Lean_Name_toString(v_name_1953_, v___x_2231_);
v___x_2233_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__8));
v___x_2234_ = lean_string_append(v___x_2232_, v___x_2233_);
v___x_2235_ = 3;
v___x_2236_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2236_, 0, v___x_2234_);
lean_ctor_set_uint8(v___x_2236_, sizeof(void*)*1, v___x_2235_);
lean_inc_ref(v_a_1769_);
v___x_2237_ = lean_apply_2(v_a_1769_, v___x_2236_, lean_box(0));
v___x_2238_ = lean_box(0);
v___x_2239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2239_, 0, v___x_2238_);
return v___x_2239_;
}
}
v___jp_1771_:
{
lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1772_ = lean_box(0);
v___x_1773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1773_, 0, v___x_1772_);
return v___x_1773_;
}
v___jp_1774_:
{
lean_object* v_fullName_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; uint8_t v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
v_fullName_1777_ = lean_ctor_get(v___y_1775_, 1);
lean_inc_ref(v_fullName_1777_);
lean_dec_ref(v___y_1775_);
v___x_1778_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__0));
v___x_1779_ = lean_string_append(v_fullName_1777_, v___x_1778_);
v___x_1780_ = 3;
v___x_1781_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1781_, 0, v___x_1779_);
lean_ctor_set_uint8(v___x_1781_, sizeof(void*)*1, v___x_1780_);
lean_inc_ref(v___y_1776_);
v___x_1782_ = lean_apply_2(v___y_1776_, v___x_1781_, lean_box(0));
v___x_1783_ = lean_box(0);
v___x_1784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1784_, 0, v___x_1783_);
return v___x_1784_;
}
v___jp_1785_:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; 
v___x_1792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1792_, 0, v___y_1788_);
v___x_1793_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(v_a_1769_, v_dep_1763_, v_inherited_1764_, v_lakeEnv_1765_, v_wsDir_1766_, v___y_1787_, v___y_1790_, v___y_1786_, v___y_1791_, v___x_1792_, v___y_1789_);
lean_dec_ref(v_lakeEnv_1765_);
return v___x_1793_;
}
v___jp_1794_:
{
if (lean_obj_tag(v___y_1798_) == 0)
{
lean_object* v___x_1801_; 
v___x_1801_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___y_1786_ = v___y_1795_;
v___y_1787_ = v___y_1796_;
v___y_1788_ = v_a_1800_;
v___y_1789_ = v___y_1797_;
v___y_1790_ = v___y_1799_;
v___y_1791_ = v___x_1801_;
goto v___jp_1785_;
}
else
{
lean_object* v_val_1802_; 
v_val_1802_ = lean_ctor_get(v___y_1798_, 0);
lean_inc(v_val_1802_);
lean_dec_ref_known(v___y_1798_, 1);
v___y_1786_ = v___y_1795_;
v___y_1787_ = v___y_1796_;
v___y_1788_ = v_a_1800_;
v___y_1789_ = v___y_1797_;
v___y_1790_ = v___y_1799_;
v___y_1791_ = v_val_1802_;
goto v___jp_1785_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize___boxed(lean_object* v_dep_2240_, lean_object* v_inherited_2241_, lean_object* v_lakeEnv_2242_, lean_object* v_wsDir_2243_, lean_object* v_relPkgsDir_2244_, lean_object* v_relParentDir_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_){
_start:
{
uint8_t v_inherited_boxed_2248_; lean_object* v_res_2249_; 
v_inherited_boxed_2248_ = lean_unbox(v_inherited_2241_);
v_res_2249_ = l_Lake_Dependency_materialize(v_dep_2240_, v_inherited_boxed_2248_, v_lakeEnv_2242_, v_wsDir_2243_, v_relPkgsDir_2244_, v_relParentDir_2245_, v_a_2246_);
lean_dec_ref(v_a_2246_);
return v_res_2249_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep(lean_object* v_manifestEntry_2255_, lean_object* v_wsDir_2256_, lean_object* v_relPkgDir_2257_, lean_object* v_remoteUrl_2258_, lean_object* v_a_2259_){
_start:
{
lean_object* v___y_2262_; lean_object* v_a_2263_; lean_object* v_pkgDir_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___f_2269_; lean_object* v___y_2271_; lean_object* v___y_2272_; lean_object* v___y_2273_; lean_object* v___y_2274_; lean_object* v_val_2275_; lean_object* v_a_2305_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v_val_2345_; lean_object* v___x_2373_; uint8_t v___x_2374_; 
lean_inc_ref(v_relPkgDir_2257_);
v_pkgDir_2266_ = l_Lake_joinRelative(v_wsDir_2256_, v_relPkgDir_2257_);
v___x_2267_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1, &l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1_once, _init_l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1);
lean_inc_ref(v_pkgDir_2266_);
v___x_2268_ = l_Lake_resolvePath(v_pkgDir_2266_);
v___f_2269_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__2));
v___x_2342_ = lean_unsigned_to_nat(0u);
v___x_2343_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0));
v___x_2373_ = lean_string_utf8_byte_size(v___x_2268_);
v___x_2374_ = lean_nat_dec_eq(v___x_2373_, v___x_2342_);
if (v___x_2374_ == 0)
{
lean_object* v___x_2375_; 
v___x_2375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2375_, 0, v___x_2268_);
v_val_2345_ = v___x_2375_;
goto v___jp_2344_;
}
else
{
lean_object* v___x_2376_; 
lean_dec_ref(v___x_2268_);
v___x_2376_ = lean_box(0);
v_val_2345_ = v___x_2376_;
goto v___jp_2344_;
}
v___jp_2261_:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2264_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2264_, 0, v___y_2262_);
lean_ctor_set(v___x_2264_, 1, v_relPkgDir_2257_);
lean_ctor_set(v___x_2264_, 2, v_remoteUrl_2258_);
lean_ctor_set(v___x_2264_, 3, v_a_2263_);
lean_ctor_set(v___x_2264_, 4, v_manifestEntry_2255_);
v___x_2265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2265_, 0, v___x_2264_);
return v___x_2265_;
}
v___jp_2270_:
{
lean_object* v___x_2276_; uint8_t v___x_2277_; 
v___x_2276_ = lean_array_get_size(v___y_2272_);
v___x_2277_ = lean_nat_dec_lt(v___y_2274_, v___x_2276_);
if (v___x_2277_ == 0)
{
lean_dec_ref(v___y_2271_);
v___y_2262_ = v___y_2273_;
v_a_2263_ = v_val_2275_;
goto v___jp_2261_;
}
else
{
lean_object* v___x_2278_; uint8_t v___x_2279_; 
v___x_2278_ = lean_box(0);
v___x_2279_ = lean_nat_dec_le(v___x_2276_, v___x_2276_);
if (v___x_2279_ == 0)
{
if (v___x_2277_ == 0)
{
lean_dec_ref(v___y_2271_);
v___y_2262_ = v___y_2273_;
v_a_2263_ = v_val_2275_;
goto v___jp_2261_;
}
else
{
size_t v___x_2280_; size_t v___x_2281_; lean_object* v___x_2400__overap_2282_; lean_object* v___x_2283_; 
v___x_2280_ = ((size_t)0ULL);
v___x_2281_ = lean_usize_of_nat(v___x_2276_);
lean_inc_ref(v___y_2272_);
v___x_2400__overap_2282_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___y_2271_, v___f_2269_, v___y_2272_, v___x_2280_, v___x_2281_, v___x_2278_);
lean_inc_ref(v_a_2259_);
v___x_2283_ = lean_apply_2(v___x_2400__overap_2282_, v_a_2259_, lean_box(0));
if (lean_obj_tag(v___x_2283_) == 0)
{
lean_dec_ref_known(v___x_2283_, 1);
v___y_2262_ = v___y_2273_;
v_a_2263_ = v_val_2275_;
goto v___jp_2261_;
}
else
{
lean_object* v_a_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2291_; 
lean_dec_ref(v_val_2275_);
lean_dec_ref(v___y_2273_);
lean_dec_ref(v_remoteUrl_2258_);
lean_dec_ref(v_relPkgDir_2257_);
lean_dec_ref(v_manifestEntry_2255_);
v_a_2284_ = lean_ctor_get(v___x_2283_, 0);
v_isSharedCheck_2291_ = !lean_is_exclusive(v___x_2283_);
if (v_isSharedCheck_2291_ == 0)
{
v___x_2286_ = v___x_2283_;
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_a_2284_);
lean_dec(v___x_2283_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v___x_2289_; 
if (v_isShared_2287_ == 0)
{
v___x_2289_ = v___x_2286_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v_a_2284_);
v___x_2289_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
return v___x_2289_;
}
}
}
}
}
else
{
size_t v___x_2292_; size_t v___x_2293_; lean_object* v___x_2410__overap_2294_; lean_object* v___x_2295_; 
v___x_2292_ = ((size_t)0ULL);
v___x_2293_ = lean_usize_of_nat(v___x_2276_);
lean_inc_ref(v___y_2272_);
v___x_2410__overap_2294_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___y_2271_, v___f_2269_, v___y_2272_, v___x_2292_, v___x_2293_, v___x_2278_);
lean_inc_ref(v_a_2259_);
v___x_2295_ = lean_apply_2(v___x_2410__overap_2294_, v_a_2259_, lean_box(0));
if (lean_obj_tag(v___x_2295_) == 0)
{
lean_dec_ref_known(v___x_2295_, 1);
v___y_2262_ = v___y_2273_;
v_a_2263_ = v_val_2275_;
goto v___jp_2261_;
}
else
{
lean_object* v_a_2296_; lean_object* v___x_2298_; uint8_t v_isShared_2299_; uint8_t v_isSharedCheck_2303_; 
lean_dec_ref(v_val_2275_);
lean_dec_ref(v___y_2273_);
lean_dec_ref(v_remoteUrl_2258_);
lean_dec_ref(v_relPkgDir_2257_);
lean_dec_ref(v_manifestEntry_2255_);
v_a_2296_ = lean_ctor_get(v___x_2295_, 0);
v_isSharedCheck_2303_ = !lean_is_exclusive(v___x_2295_);
if (v_isSharedCheck_2303_ == 0)
{
v___x_2298_ = v___x_2295_;
v_isShared_2299_ = v_isSharedCheck_2303_;
goto v_resetjp_2297_;
}
else
{
lean_inc(v_a_2296_);
lean_dec(v___x_2295_);
v___x_2298_ = lean_box(0);
v_isShared_2299_ = v_isSharedCheck_2303_;
goto v_resetjp_2297_;
}
v_resetjp_2297_:
{
lean_object* v___x_2301_; 
if (v_isShared_2299_ == 0)
{
v___x_2301_ = v___x_2298_;
goto v_reusejp_2300_;
}
else
{
lean_object* v_reuseFailAlloc_2302_; 
v_reuseFailAlloc_2302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2302_, 0, v_a_2296_);
v___x_2301_ = v_reuseFailAlloc_2302_;
goto v_reusejp_2300_;
}
v_reusejp_2300_:
{
return v___x_2301_;
}
}
}
}
}
}
v___jp_2304_:
{
if (lean_obj_tag(v_a_2305_) == 1)
{
lean_object* v_manifestFile_x3f_2306_; 
lean_dec_ref(v_pkgDir_2266_);
v_manifestFile_x3f_2306_ = lean_ctor_get(v_manifestEntry_2255_, 3);
if (lean_obj_tag(v_manifestFile_x3f_2306_) == 1)
{
lean_object* v_val_2307_; lean_object* v_val_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; 
v_val_2307_ = lean_ctor_get(v_a_2305_, 0);
lean_inc_n(v_val_2307_, 2);
lean_dec_ref_known(v_a_2305_, 1);
v_val_2308_ = lean_ctor_get(v_manifestFile_x3f_2306_, 0);
lean_inc(v_val_2308_);
v___x_2309_ = l_Lake_joinRelative(v_val_2307_, v_val_2308_);
v___x_2310_ = lean_unsigned_to_nat(0u);
v___x_2311_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0));
v___x_2312_ = l_Lake_Manifest_load(v___x_2309_);
if (lean_obj_tag(v___x_2312_) == 0)
{
lean_object* v_a_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2320_; 
v_a_2313_ = lean_ctor_get(v___x_2312_, 0);
v_isSharedCheck_2320_ = !lean_is_exclusive(v___x_2312_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2315_ = v___x_2312_;
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_a_2313_);
lean_dec(v___x_2312_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2318_; 
if (v_isShared_2316_ == 0)
{
lean_ctor_set_tag(v___x_2315_, 1);
v___x_2318_ = v___x_2315_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_a_2313_);
v___x_2318_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
v___y_2271_ = v___x_2267_;
v___y_2272_ = v___x_2311_;
v___y_2273_ = v_val_2307_;
v___y_2274_ = v___x_2310_;
v_val_2275_ = v___x_2318_;
goto v___jp_2270_;
}
}
}
else
{
lean_object* v_a_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2328_; 
v_a_2321_ = lean_ctor_get(v___x_2312_, 0);
v_isSharedCheck_2328_ = !lean_is_exclusive(v___x_2312_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2323_ = v___x_2312_;
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_a_2321_);
lean_dec(v___x_2312_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v___x_2326_; 
if (v_isShared_2324_ == 0)
{
lean_ctor_set_tag(v___x_2323_, 0);
v___x_2326_ = v___x_2323_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v_a_2321_);
v___x_2326_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
v___y_2271_ = v___x_2267_;
v___y_2272_ = v___x_2311_;
v___y_2273_ = v_val_2307_;
v___y_2274_ = v___x_2310_;
v_val_2275_ = v___x_2326_;
goto v___jp_2270_;
}
}
}
}
else
{
lean_object* v_val_2329_; lean_object* v___x_2330_; 
v_val_2329_ = lean_ctor_get(v_a_2305_, 0);
lean_inc(v_val_2329_);
lean_dec_ref_known(v_a_2305_, 1);
v___x_2330_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1));
v___y_2262_ = v_val_2329_;
v_a_2263_ = v___x_2330_;
goto v___jp_2261_;
}
}
else
{
lean_object* v_name_2331_; uint8_t v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; uint8_t v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; 
lean_dec(v_a_2305_);
lean_dec_ref(v_remoteUrl_2258_);
lean_dec_ref(v_relPkgDir_2257_);
v_name_2331_ = lean_ctor_get(v_manifestEntry_2255_, 0);
lean_inc(v_name_2331_);
lean_dec_ref(v_manifestEntry_2255_);
v___x_2332_ = 0;
v___x_2333_ = l_Lean_Name_toString(v_name_2331_, v___x_2332_);
v___x_2334_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__3));
v___x_2335_ = lean_string_append(v___x_2333_, v___x_2334_);
v___x_2336_ = lean_string_append(v___x_2335_, v_pkgDir_2266_);
lean_dec_ref(v_pkgDir_2266_);
v___x_2337_ = 3;
v___x_2338_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2338_, 0, v___x_2336_);
lean_ctor_set_uint8(v___x_2338_, sizeof(void*)*1, v___x_2337_);
lean_inc_ref(v_a_2259_);
v___x_2339_ = lean_apply_2(v_a_2259_, v___x_2338_, lean_box(0));
v___x_2340_ = lean_box(0);
v___x_2341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2341_, 0, v___x_2340_);
return v___x_2341_;
}
}
v___jp_2344_:
{
uint8_t v___x_2346_; 
v___x_2346_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__6);
if (v___x_2346_ == 0)
{
v_a_2305_ = v_val_2345_;
goto v___jp_2304_;
}
else
{
lean_object* v___x_2347_; uint8_t v___x_2348_; 
v___x_2347_ = lean_box(0);
v___x_2348_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__7);
if (v___x_2348_ == 0)
{
if (v___x_2346_ == 0)
{
v_a_2305_ = v_val_2345_;
goto v___jp_2304_;
}
else
{
size_t v___x_2349_; size_t v___x_2350_; lean_object* v___x_2466__overap_2351_; lean_object* v___x_2352_; 
v___x_2349_ = ((size_t)0ULL);
v___x_2350_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8);
v___x_2466__overap_2351_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2267_, v___f_2269_, v___x_2343_, v___x_2349_, v___x_2350_, v___x_2347_);
lean_inc_ref(v_a_2259_);
v___x_2352_ = lean_apply_2(v___x_2466__overap_2351_, v_a_2259_, lean_box(0));
if (lean_obj_tag(v___x_2352_) == 0)
{
lean_dec_ref_known(v___x_2352_, 1);
v_a_2305_ = v_val_2345_;
goto v___jp_2304_;
}
else
{
lean_object* v_a_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2360_; 
lean_dec(v_val_2345_);
lean_dec_ref(v_pkgDir_2266_);
lean_dec_ref(v_remoteUrl_2258_);
lean_dec_ref(v_relPkgDir_2257_);
lean_dec_ref(v_manifestEntry_2255_);
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
size_t v___x_2361_; size_t v___x_2362_; lean_object* v___x_2476__overap_2363_; lean_object* v___x_2364_; 
v___x_2361_ = ((size_t)0ULL);
v___x_2362_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8);
v___x_2476__overap_2363_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2267_, v___f_2269_, v___x_2343_, v___x_2361_, v___x_2362_, v___x_2347_);
lean_inc_ref(v_a_2259_);
v___x_2364_ = lean_apply_2(v___x_2476__overap_2363_, v_a_2259_, lean_box(0));
if (lean_obj_tag(v___x_2364_) == 0)
{
lean_dec_ref_known(v___x_2364_, 1);
v_a_2305_ = v_val_2345_;
goto v___jp_2304_;
}
else
{
lean_object* v_a_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2372_; 
lean_dec(v_val_2345_);
lean_dec_ref(v_pkgDir_2266_);
lean_dec_ref(v_remoteUrl_2258_);
lean_dec_ref(v_relPkgDir_2257_);
lean_dec_ref(v_manifestEntry_2255_);
v_a_2365_ = lean_ctor_get(v___x_2364_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v___x_2364_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2367_ = v___x_2364_;
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_a_2365_);
lean_dec(v___x_2364_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
lean_object* v___x_2370_; 
if (v_isShared_2368_ == 0)
{
v___x_2370_ = v___x_2367_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v_a_2365_);
v___x_2370_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
return v___x_2370_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___boxed(lean_object* v_manifestEntry_2377_, lean_object* v_wsDir_2378_, lean_object* v_relPkgDir_2379_, lean_object* v_remoteUrl_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_){
_start:
{
lean_object* v_res_2383_; 
v_res_2383_ = l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep(v_manifestEntry_2377_, v_wsDir_2378_, v_relPkgDir_2379_, v_remoteUrl_2380_, v_a_2381_);
lean_dec_ref(v_a_2381_);
return v_res_2383_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize(lean_object* v_manifestEntry_2385_, lean_object* v_lakeEnv_2386_, lean_object* v_wsDir_2387_, lean_object* v_relPkgsDir_2388_, lean_object* v_a_2389_){
_start:
{
lean_object* v___y_2392_; lean_object* v___y_2393_; lean_object* v___y_2394_; lean_object* v_a_2395_; lean_object* v___y_2399_; lean_object* v___y_2400_; lean_object* v___y_2401_; lean_object* v___y_2402_; lean_object* v___y_2403_; lean_object* v___y_2404_; lean_object* v_val_2405_; lean_object* v_src_2432_; 
v_src_2432_ = lean_ctor_get(v_manifestEntry_2385_, 4);
lean_inc_ref(v_src_2432_);
if (lean_obj_tag(v_src_2432_) == 0)
{
lean_object* v_name_2433_; lean_object* v_manifestFile_x3f_2434_; lean_object* v_dir_2435_; lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2549_; 
lean_dec_ref(v_relPkgsDir_2388_);
v_name_2433_ = lean_ctor_get(v_manifestEntry_2385_, 0);
v_manifestFile_x3f_2434_ = lean_ctor_get(v_manifestEntry_2385_, 3);
v_dir_2435_ = lean_ctor_get(v_src_2432_, 0);
v_isSharedCheck_2549_ = !lean_is_exclusive(v_src_2432_);
if (v_isSharedCheck_2549_ == 0)
{
v___x_2437_ = v_src_2432_;
v_isShared_2438_ = v_isSharedCheck_2549_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_dir_2435_);
lean_dec(v_src_2432_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2549_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
lean_object* v_pkgDir_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___y_2443_; lean_object* v_a_2444_; lean_object* v___y_2450_; lean_object* v___y_2451_; lean_object* v___y_2452_; lean_object* v_val_2453_; lean_object* v_a_2481_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v_val_2519_; lean_object* v___x_2545_; uint8_t v___x_2546_; 
lean_inc_ref(v_dir_2435_);
v_pkgDir_2439_ = l_Lake_joinRelative(v_wsDir_2387_, v_dir_2435_);
lean_inc_ref(v_pkgDir_2439_);
v___x_2440_ = l_Lake_resolvePath(v_pkgDir_2439_);
v___x_2441_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___x_2516_ = lean_unsigned_to_nat(0u);
v___x_2517_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0));
v___x_2545_ = lean_string_utf8_byte_size(v___x_2440_);
v___x_2546_ = lean_nat_dec_eq(v___x_2545_, v___x_2516_);
if (v___x_2546_ == 0)
{
lean_object* v___x_2547_; 
v___x_2547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2547_, 0, v___x_2440_);
v_val_2519_ = v___x_2547_;
goto v___jp_2518_;
}
else
{
lean_object* v___x_2548_; 
lean_dec_ref(v___x_2440_);
v___x_2548_ = lean_box(0);
v_val_2519_ = v___x_2548_;
goto v___jp_2518_;
}
v___jp_2442_:
{
lean_object* v___x_2445_; lean_object* v___x_2447_; 
v___x_2445_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2445_, 0, v___y_2443_);
lean_ctor_set(v___x_2445_, 1, v_dir_2435_);
lean_ctor_set(v___x_2445_, 2, v___x_2441_);
lean_ctor_set(v___x_2445_, 3, v_a_2444_);
lean_ctor_set(v___x_2445_, 4, v_manifestEntry_2385_);
if (v_isShared_2438_ == 0)
{
lean_ctor_set(v___x_2437_, 0, v___x_2445_);
v___x_2447_ = v___x_2437_;
goto v_reusejp_2446_;
}
else
{
lean_object* v_reuseFailAlloc_2448_; 
v_reuseFailAlloc_2448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2448_, 0, v___x_2445_);
v___x_2447_ = v_reuseFailAlloc_2448_;
goto v_reusejp_2446_;
}
v_reusejp_2446_:
{
return v___x_2447_;
}
}
v___jp_2449_:
{
lean_object* v___x_2454_; uint8_t v___x_2455_; 
v___x_2454_ = lean_array_get_size(v___y_2451_);
v___x_2455_ = lean_nat_dec_lt(v___y_2452_, v___x_2454_);
if (v___x_2455_ == 0)
{
v___y_2443_ = v___y_2450_;
v_a_2444_ = v_val_2453_;
goto v___jp_2442_;
}
else
{
lean_object* v___x_2456_; uint8_t v___x_2457_; 
v___x_2456_ = lean_box(0);
v___x_2457_ = lean_nat_dec_le(v___x_2454_, v___x_2454_);
if (v___x_2457_ == 0)
{
if (v___x_2455_ == 0)
{
v___y_2443_ = v___y_2450_;
v_a_2444_ = v_val_2453_;
goto v___jp_2442_;
}
else
{
size_t v___x_2458_; size_t v___x_2459_; lean_object* v___x_2460_; 
v___x_2458_ = ((size_t)0ULL);
v___x_2459_ = lean_usize_of_nat(v___x_2454_);
v___x_2460_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_2451_, v___x_2458_, v___x_2459_, v___x_2456_, v_a_2389_);
if (lean_obj_tag(v___x_2460_) == 0)
{
lean_dec_ref_known(v___x_2460_, 1);
v___y_2443_ = v___y_2450_;
v_a_2444_ = v_val_2453_;
goto v___jp_2442_;
}
else
{
lean_object* v_a_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2468_; 
lean_dec_ref(v_val_2453_);
lean_dec_ref(v___y_2450_);
lean_del_object(v___x_2437_);
lean_dec_ref(v_dir_2435_);
lean_dec_ref(v_manifestEntry_2385_);
v_a_2461_ = lean_ctor_get(v___x_2460_, 0);
v_isSharedCheck_2468_ = !lean_is_exclusive(v___x_2460_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2463_ = v___x_2460_;
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_a_2461_);
lean_dec(v___x_2460_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v___x_2466_; 
if (v_isShared_2464_ == 0)
{
v___x_2466_ = v___x_2463_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_a_2461_);
v___x_2466_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
return v___x_2466_;
}
}
}
}
}
else
{
size_t v___x_2469_; size_t v___x_2470_; lean_object* v___x_2471_; 
v___x_2469_ = ((size_t)0ULL);
v___x_2470_ = lean_usize_of_nat(v___x_2454_);
v___x_2471_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_2451_, v___x_2469_, v___x_2470_, v___x_2456_, v_a_2389_);
if (lean_obj_tag(v___x_2471_) == 0)
{
lean_dec_ref_known(v___x_2471_, 1);
v___y_2443_ = v___y_2450_;
v_a_2444_ = v_val_2453_;
goto v___jp_2442_;
}
else
{
lean_object* v_a_2472_; lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2479_; 
lean_dec_ref(v_val_2453_);
lean_dec_ref(v___y_2450_);
lean_del_object(v___x_2437_);
lean_dec_ref(v_dir_2435_);
lean_dec_ref(v_manifestEntry_2385_);
v_a_2472_ = lean_ctor_get(v___x_2471_, 0);
v_isSharedCheck_2479_ = !lean_is_exclusive(v___x_2471_);
if (v_isSharedCheck_2479_ == 0)
{
v___x_2474_ = v___x_2471_;
v_isShared_2475_ = v_isSharedCheck_2479_;
goto v_resetjp_2473_;
}
else
{
lean_inc(v_a_2472_);
lean_dec(v___x_2471_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2479_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
lean_object* v___x_2477_; 
if (v_isShared_2475_ == 0)
{
v___x_2477_ = v___x_2474_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v_a_2472_);
v___x_2477_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
return v___x_2477_;
}
}
}
}
}
}
v___jp_2480_:
{
if (lean_obj_tag(v_a_2481_) == 1)
{
lean_dec_ref(v_pkgDir_2439_);
if (lean_obj_tag(v_manifestFile_x3f_2434_) == 1)
{
lean_object* v_val_2482_; lean_object* v_val_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; 
v_val_2482_ = lean_ctor_get(v_a_2481_, 0);
lean_inc_n(v_val_2482_, 2);
lean_dec_ref_known(v_a_2481_, 1);
v_val_2483_ = lean_ctor_get(v_manifestFile_x3f_2434_, 0);
lean_inc(v_val_2483_);
v___x_2484_ = l_Lake_joinRelative(v_val_2482_, v_val_2483_);
v___x_2485_ = lean_unsigned_to_nat(0u);
v___x_2486_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0));
v___x_2487_ = l_Lake_Manifest_load(v___x_2484_);
if (lean_obj_tag(v___x_2487_) == 0)
{
lean_object* v_a_2488_; lean_object* v___x_2490_; uint8_t v_isShared_2491_; uint8_t v_isSharedCheck_2495_; 
v_a_2488_ = lean_ctor_get(v___x_2487_, 0);
v_isSharedCheck_2495_ = !lean_is_exclusive(v___x_2487_);
if (v_isSharedCheck_2495_ == 0)
{
v___x_2490_ = v___x_2487_;
v_isShared_2491_ = v_isSharedCheck_2495_;
goto v_resetjp_2489_;
}
else
{
lean_inc(v_a_2488_);
lean_dec(v___x_2487_);
v___x_2490_ = lean_box(0);
v_isShared_2491_ = v_isSharedCheck_2495_;
goto v_resetjp_2489_;
}
v_resetjp_2489_:
{
lean_object* v___x_2493_; 
if (v_isShared_2491_ == 0)
{
lean_ctor_set_tag(v___x_2490_, 1);
v___x_2493_ = v___x_2490_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2494_; 
v_reuseFailAlloc_2494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2494_, 0, v_a_2488_);
v___x_2493_ = v_reuseFailAlloc_2494_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
v___y_2450_ = v_val_2482_;
v___y_2451_ = v___x_2486_;
v___y_2452_ = v___x_2485_;
v_val_2453_ = v___x_2493_;
goto v___jp_2449_;
}
}
}
else
{
lean_object* v_a_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2503_; 
v_a_2496_ = lean_ctor_get(v___x_2487_, 0);
v_isSharedCheck_2503_ = !lean_is_exclusive(v___x_2487_);
if (v_isSharedCheck_2503_ == 0)
{
v___x_2498_ = v___x_2487_;
v_isShared_2499_ = v_isSharedCheck_2503_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_a_2496_);
lean_dec(v___x_2487_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2503_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
lean_object* v___x_2501_; 
if (v_isShared_2499_ == 0)
{
lean_ctor_set_tag(v___x_2498_, 0);
v___x_2501_ = v___x_2498_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v_a_2496_);
v___x_2501_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2500_;
}
v_reusejp_2500_:
{
v___y_2450_ = v_val_2482_;
v___y_2451_ = v___x_2486_;
v___y_2452_ = v___x_2485_;
v_val_2453_ = v___x_2501_;
goto v___jp_2449_;
}
}
}
}
else
{
lean_object* v_val_2504_; lean_object* v___x_2505_; 
v_val_2504_ = lean_ctor_get(v_a_2481_, 0);
lean_inc(v_val_2504_);
lean_dec_ref_known(v_a_2481_, 1);
v___x_2505_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1));
v___y_2443_ = v_val_2504_;
v_a_2444_ = v___x_2505_;
goto v___jp_2442_;
}
}
else
{
uint8_t v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; uint8_t v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; 
lean_inc(v_name_2433_);
lean_dec(v_a_2481_);
lean_del_object(v___x_2437_);
lean_dec_ref(v_dir_2435_);
lean_dec_ref(v_manifestEntry_2385_);
v___x_2506_ = 0;
v___x_2507_ = l_Lean_Name_toString(v_name_2433_, v___x_2506_);
v___x_2508_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__3));
v___x_2509_ = lean_string_append(v___x_2507_, v___x_2508_);
v___x_2510_ = lean_string_append(v___x_2509_, v_pkgDir_2439_);
lean_dec_ref(v_pkgDir_2439_);
v___x_2511_ = 3;
v___x_2512_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2512_, 0, v___x_2510_);
lean_ctor_set_uint8(v___x_2512_, sizeof(void*)*1, v___x_2511_);
lean_inc_ref(v_a_2389_);
v___x_2513_ = lean_apply_2(v_a_2389_, v___x_2512_, lean_box(0));
v___x_2514_ = lean_box(0);
v___x_2515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2515_, 0, v___x_2514_);
return v___x_2515_;
}
}
v___jp_2518_:
{
uint8_t v___x_2520_; 
v___x_2520_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__6);
if (v___x_2520_ == 0)
{
v_a_2481_ = v_val_2519_;
goto v___jp_2480_;
}
else
{
lean_object* v___x_2521_; uint8_t v___x_2522_; 
v___x_2521_ = lean_box(0);
v___x_2522_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__7);
if (v___x_2522_ == 0)
{
if (v___x_2520_ == 0)
{
v_a_2481_ = v_val_2519_;
goto v___jp_2480_;
}
else
{
size_t v___x_2523_; size_t v___x_2524_; lean_object* v___x_2525_; 
v___x_2523_ = ((size_t)0ULL);
v___x_2524_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8);
v___x_2525_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_2517_, v___x_2523_, v___x_2524_, v___x_2521_, v_a_2389_);
if (lean_obj_tag(v___x_2525_) == 0)
{
lean_dec_ref_known(v___x_2525_, 1);
v_a_2481_ = v_val_2519_;
goto v___jp_2480_;
}
else
{
lean_object* v_a_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2533_; 
lean_dec(v_val_2519_);
lean_dec_ref(v_pkgDir_2439_);
lean_del_object(v___x_2437_);
lean_dec_ref(v_dir_2435_);
lean_dec_ref(v_manifestEntry_2385_);
v_a_2526_ = lean_ctor_get(v___x_2525_, 0);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2525_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2528_ = v___x_2525_;
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_a_2526_);
lean_dec(v___x_2525_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v___x_2531_; 
if (v_isShared_2529_ == 0)
{
v___x_2531_ = v___x_2528_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v_a_2526_);
v___x_2531_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
return v___x_2531_;
}
}
}
}
}
else
{
size_t v___x_2534_; size_t v___x_2535_; lean_object* v___x_2536_; 
v___x_2534_ = ((size_t)0ULL);
v___x_2535_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8);
v___x_2536_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_2517_, v___x_2534_, v___x_2535_, v___x_2521_, v_a_2389_);
if (lean_obj_tag(v___x_2536_) == 0)
{
lean_dec_ref_known(v___x_2536_, 1);
v_a_2481_ = v_val_2519_;
goto v___jp_2480_;
}
else
{
lean_object* v_a_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2544_; 
lean_dec(v_val_2519_);
lean_dec_ref(v_pkgDir_2439_);
lean_del_object(v___x_2437_);
lean_dec_ref(v_dir_2435_);
lean_dec_ref(v_manifestEntry_2385_);
v_a_2537_ = lean_ctor_get(v___x_2536_, 0);
v_isSharedCheck_2544_ = !lean_is_exclusive(v___x_2536_);
if (v_isSharedCheck_2544_ == 0)
{
v___x_2539_ = v___x_2536_;
v_isShared_2540_ = v_isSharedCheck_2544_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_a_2537_);
lean_dec(v___x_2536_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2544_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v___x_2542_; 
if (v_isShared_2540_ == 0)
{
v___x_2542_ = v___x_2539_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v_a_2537_);
v___x_2542_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
return v___x_2542_;
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
lean_object* v_name_2550_; lean_object* v_manifestFile_x3f_2551_; lean_object* v_url_2552_; lean_object* v_rev_2553_; lean_object* v_subDir_x3f_2554_; uint8_t v___x_2555_; lean_object* v___x_2556_; lean_object* v___y_2558_; lean_object* v___y_2559_; lean_object* v___y_2560_; lean_object* v___y_2561_; lean_object* v_a_2562_; lean_object* v___y_2596_; lean_object* v___y_2597_; lean_object* v___y_2598_; lean_object* v___y_2599_; lean_object* v___y_2600_; lean_object* v___y_2601_; lean_object* v_val_2602_; lean_object* v___y_2630_; lean_object* v___y_2631_; lean_object* v___y_2632_; lean_object* v___y_2642_; lean_object* v___y_2643_; lean_object* v_relGitDir_2647_; lean_object* v___y_2649_; lean_object* v_gitDir_2652_; lean_object* v___y_2654_; lean_object* v___y_2666_; lean_object* v___y_2667_; uint8_t v_a_2678_; lean_object* v_a_2688_; uint8_t v___x_2723_; lean_object* v___x_2756_; uint8_t v___x_2757_; 
v_name_2550_ = lean_ctor_get(v_manifestEntry_2385_, 0);
v_manifestFile_x3f_2551_ = lean_ctor_get(v_manifestEntry_2385_, 3);
v_url_2552_ = lean_ctor_get(v_src_2432_, 0);
lean_inc_ref(v_url_2552_);
v_rev_2553_ = lean_ctor_get(v_src_2432_, 1);
lean_inc_ref(v_rev_2553_);
v_subDir_x3f_2554_ = lean_ctor_get(v_src_2432_, 3);
lean_inc(v_subDir_x3f_2554_);
lean_dec_ref_known(v_src_2432_, 4);
v___x_2555_ = 0;
lean_inc(v_name_2550_);
v___x_2556_ = l_Lean_Name_toString(v_name_2550_, v___x_2555_);
lean_inc_ref(v___x_2556_);
v_relGitDir_2647_ = l_Lake_joinRelative(v_relPkgsDir_2388_, v___x_2556_);
lean_inc_ref(v_relGitDir_2647_);
lean_inc_ref(v_wsDir_2387_);
v_gitDir_2652_ = l_Lake_joinRelative(v_wsDir_2387_, v_relGitDir_2647_);
v___x_2723_ = l_System_FilePath_isDir(v_gitDir_2652_);
v___x_2756_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0));
v___x_2757_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__6);
if (v___x_2757_ == 0)
{
goto v___jp_2724_;
}
else
{
lean_object* v___x_2758_; uint8_t v___x_2759_; 
v___x_2758_ = lean_box(0);
v___x_2759_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__7);
if (v___x_2759_ == 0)
{
if (v___x_2757_ == 0)
{
goto v___jp_2724_;
}
else
{
size_t v___x_2760_; size_t v___x_2761_; lean_object* v___x_2762_; 
v___x_2760_ = ((size_t)0ULL);
v___x_2761_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8);
v___x_2762_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_2756_, v___x_2760_, v___x_2761_, v___x_2758_, v_a_2389_);
if (lean_obj_tag(v___x_2762_) == 0)
{
lean_dec_ref_known(v___x_2762_, 1);
goto v___jp_2724_;
}
else
{
lean_object* v_a_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2770_; 
lean_dec_ref(v_gitDir_2652_);
lean_dec_ref(v_relGitDir_2647_);
lean_dec_ref(v___x_2556_);
lean_dec(v_subDir_x3f_2554_);
lean_dec_ref(v_rev_2553_);
lean_dec_ref(v_url_2552_);
lean_dec_ref(v_wsDir_2387_);
lean_dec_ref(v_manifestEntry_2385_);
v_a_2763_ = lean_ctor_get(v___x_2762_, 0);
v_isSharedCheck_2770_ = !lean_is_exclusive(v___x_2762_);
if (v_isSharedCheck_2770_ == 0)
{
v___x_2765_ = v___x_2762_;
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_a_2763_);
lean_dec(v___x_2762_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
lean_object* v___x_2768_; 
if (v_isShared_2766_ == 0)
{
v___x_2768_ = v___x_2765_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v_a_2763_);
v___x_2768_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
return v___x_2768_;
}
}
}
}
}
else
{
size_t v___x_2771_; size_t v___x_2772_; lean_object* v___x_2773_; 
v___x_2771_ = ((size_t)0ULL);
v___x_2772_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8);
v___x_2773_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_2756_, v___x_2771_, v___x_2772_, v___x_2758_, v_a_2389_);
if (lean_obj_tag(v___x_2773_) == 0)
{
lean_dec_ref_known(v___x_2773_, 1);
goto v___jp_2724_;
}
else
{
lean_object* v_a_2774_; lean_object* v___x_2776_; uint8_t v_isShared_2777_; uint8_t v_isSharedCheck_2781_; 
lean_dec_ref(v_gitDir_2652_);
lean_dec_ref(v_relGitDir_2647_);
lean_dec_ref(v___x_2556_);
lean_dec(v_subDir_x3f_2554_);
lean_dec_ref(v_rev_2553_);
lean_dec_ref(v_url_2552_);
lean_dec_ref(v_wsDir_2387_);
lean_dec_ref(v_manifestEntry_2385_);
v_a_2774_ = lean_ctor_get(v___x_2773_, 0);
v_isSharedCheck_2781_ = !lean_is_exclusive(v___x_2773_);
if (v_isSharedCheck_2781_ == 0)
{
v___x_2776_ = v___x_2773_;
v_isShared_2777_ = v_isSharedCheck_2781_;
goto v_resetjp_2775_;
}
else
{
lean_inc(v_a_2774_);
lean_dec(v___x_2773_);
v___x_2776_ = lean_box(0);
v_isShared_2777_ = v_isSharedCheck_2781_;
goto v_resetjp_2775_;
}
v_resetjp_2775_:
{
lean_object* v___x_2779_; 
if (v_isShared_2777_ == 0)
{
v___x_2779_ = v___x_2776_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v_a_2774_);
v___x_2779_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
return v___x_2779_;
}
}
}
}
}
v___jp_2557_:
{
if (lean_obj_tag(v_a_2562_) == 1)
{
lean_dec_ref(v___y_2559_);
lean_dec_ref(v___x_2556_);
if (lean_obj_tag(v_manifestFile_x3f_2551_) == 1)
{
lean_object* v_val_2563_; lean_object* v_val_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; 
v_val_2563_ = lean_ctor_get(v_a_2562_, 0);
lean_inc_n(v_val_2563_, 2);
lean_dec_ref_known(v_a_2562_, 1);
v_val_2564_ = lean_ctor_get(v_manifestFile_x3f_2551_, 0);
lean_inc(v_val_2564_);
v___x_2565_ = l_Lake_joinRelative(v_val_2563_, v_val_2564_);
v___x_2566_ = lean_unsigned_to_nat(0u);
v___x_2567_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0));
v___x_2568_ = l_Lake_Manifest_load(v___x_2565_);
if (lean_obj_tag(v___x_2568_) == 0)
{
lean_object* v_a_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2576_; 
v_a_2569_ = lean_ctor_get(v___x_2568_, 0);
v_isSharedCheck_2576_ = !lean_is_exclusive(v___x_2568_);
if (v_isSharedCheck_2576_ == 0)
{
v___x_2571_ = v___x_2568_;
v_isShared_2572_ = v_isSharedCheck_2576_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_a_2569_);
lean_dec(v___x_2568_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2576_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v___x_2574_; 
if (v_isShared_2572_ == 0)
{
lean_ctor_set_tag(v___x_2571_, 1);
v___x_2574_ = v___x_2571_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_a_2569_);
v___x_2574_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
v___y_2399_ = v___y_2558_;
v___y_2400_ = v___x_2567_;
v___y_2401_ = v_val_2563_;
v___y_2402_ = v___y_2560_;
v___y_2403_ = v___x_2566_;
v___y_2404_ = v___y_2561_;
v_val_2405_ = v___x_2574_;
goto v___jp_2398_;
}
}
}
else
{
lean_object* v_a_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2584_; 
v_a_2577_ = lean_ctor_get(v___x_2568_, 0);
v_isSharedCheck_2584_ = !lean_is_exclusive(v___x_2568_);
if (v_isSharedCheck_2584_ == 0)
{
v___x_2579_ = v___x_2568_;
v_isShared_2580_ = v_isSharedCheck_2584_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_a_2577_);
lean_dec(v___x_2568_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2584_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v___x_2582_; 
if (v_isShared_2580_ == 0)
{
lean_ctor_set_tag(v___x_2579_, 0);
v___x_2582_ = v___x_2579_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v_a_2577_);
v___x_2582_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
v___y_2399_ = v___y_2558_;
v___y_2400_ = v___x_2567_;
v___y_2401_ = v_val_2563_;
v___y_2402_ = v___y_2560_;
v___y_2403_ = v___x_2566_;
v___y_2404_ = v___y_2561_;
v_val_2405_ = v___x_2582_;
goto v___jp_2398_;
}
}
}
}
else
{
lean_object* v_val_2585_; lean_object* v___x_2586_; 
v_val_2585_ = lean_ctor_get(v_a_2562_, 0);
lean_inc(v_val_2585_);
lean_dec_ref_known(v_a_2562_, 1);
v___x_2586_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1));
v___y_2392_ = v___y_2558_;
v___y_2393_ = v_val_2585_;
v___y_2394_ = v___y_2560_;
v_a_2395_ = v___x_2586_;
goto v___jp_2391_;
}
}
else
{
lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; uint8_t v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; 
lean_dec(v_a_2562_);
lean_dec_ref(v___y_2560_);
lean_dec_ref(v___y_2558_);
lean_dec_ref(v_manifestEntry_2385_);
v___x_2587_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__3));
v___x_2588_ = lean_string_append(v___x_2556_, v___x_2587_);
v___x_2589_ = lean_string_append(v___x_2588_, v___y_2559_);
lean_dec_ref(v___y_2559_);
v___x_2590_ = 3;
v___x_2591_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2591_, 0, v___x_2589_);
lean_ctor_set_uint8(v___x_2591_, sizeof(void*)*1, v___x_2590_);
lean_inc_ref(v___y_2561_);
v___x_2592_ = lean_apply_2(v___y_2561_, v___x_2591_, lean_box(0));
v___x_2593_ = lean_box(0);
v___x_2594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2594_, 0, v___x_2593_);
return v___x_2594_;
}
}
v___jp_2595_:
{
lean_object* v___x_2603_; uint8_t v___x_2604_; 
v___x_2603_ = lean_array_get_size(v___y_2600_);
v___x_2604_ = lean_nat_dec_lt(v___y_2598_, v___x_2603_);
if (v___x_2604_ == 0)
{
v___y_2558_ = v___y_2596_;
v___y_2559_ = v___y_2597_;
v___y_2560_ = v___y_2599_;
v___y_2561_ = v___y_2601_;
v_a_2562_ = v_val_2602_;
goto v___jp_2557_;
}
else
{
lean_object* v___x_2605_; uint8_t v___x_2606_; 
v___x_2605_ = lean_box(0);
v___x_2606_ = lean_nat_dec_le(v___x_2603_, v___x_2603_);
if (v___x_2606_ == 0)
{
if (v___x_2604_ == 0)
{
v___y_2558_ = v___y_2596_;
v___y_2559_ = v___y_2597_;
v___y_2560_ = v___y_2599_;
v___y_2561_ = v___y_2601_;
v_a_2562_ = v_val_2602_;
goto v___jp_2557_;
}
else
{
size_t v___x_2607_; size_t v___x_2608_; lean_object* v___x_2609_; 
v___x_2607_ = ((size_t)0ULL);
v___x_2608_ = lean_usize_of_nat(v___x_2603_);
v___x_2609_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_2600_, v___x_2607_, v___x_2608_, v___x_2605_, v___y_2601_);
if (lean_obj_tag(v___x_2609_) == 0)
{
lean_dec_ref_known(v___x_2609_, 1);
v___y_2558_ = v___y_2596_;
v___y_2559_ = v___y_2597_;
v___y_2560_ = v___y_2599_;
v___y_2561_ = v___y_2601_;
v_a_2562_ = v_val_2602_;
goto v___jp_2557_;
}
else
{
lean_object* v_a_2610_; lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2617_; 
lean_dec(v_val_2602_);
lean_dec_ref(v___y_2599_);
lean_dec_ref(v___y_2597_);
lean_dec_ref(v___y_2596_);
lean_dec_ref(v___x_2556_);
lean_dec_ref(v_manifestEntry_2385_);
v_a_2610_ = lean_ctor_get(v___x_2609_, 0);
v_isSharedCheck_2617_ = !lean_is_exclusive(v___x_2609_);
if (v_isSharedCheck_2617_ == 0)
{
v___x_2612_ = v___x_2609_;
v_isShared_2613_ = v_isSharedCheck_2617_;
goto v_resetjp_2611_;
}
else
{
lean_inc(v_a_2610_);
lean_dec(v___x_2609_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_2617_;
goto v_resetjp_2611_;
}
v_resetjp_2611_:
{
lean_object* v___x_2615_; 
if (v_isShared_2613_ == 0)
{
v___x_2615_ = v___x_2612_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v_a_2610_);
v___x_2615_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
return v___x_2615_;
}
}
}
}
}
else
{
size_t v___x_2618_; size_t v___x_2619_; lean_object* v___x_2620_; 
v___x_2618_ = ((size_t)0ULL);
v___x_2619_ = lean_usize_of_nat(v___x_2603_);
v___x_2620_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_2600_, v___x_2618_, v___x_2619_, v___x_2605_, v___y_2601_);
if (lean_obj_tag(v___x_2620_) == 0)
{
lean_dec_ref_known(v___x_2620_, 1);
v___y_2558_ = v___y_2596_;
v___y_2559_ = v___y_2597_;
v___y_2560_ = v___y_2599_;
v___y_2561_ = v___y_2601_;
v_a_2562_ = v_val_2602_;
goto v___jp_2557_;
}
else
{
lean_object* v_a_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2628_; 
lean_dec(v_val_2602_);
lean_dec_ref(v___y_2599_);
lean_dec_ref(v___y_2597_);
lean_dec_ref(v___y_2596_);
lean_dec_ref(v___x_2556_);
lean_dec_ref(v_manifestEntry_2385_);
v_a_2621_ = lean_ctor_get(v___x_2620_, 0);
v_isSharedCheck_2628_ = !lean_is_exclusive(v___x_2620_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2623_ = v___x_2620_;
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_a_2621_);
lean_dec(v___x_2620_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v___x_2626_; 
if (v_isShared_2624_ == 0)
{
v___x_2626_ = v___x_2623_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v_a_2621_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
return v___x_2626_;
}
}
}
}
}
}
v___jp_2629_:
{
lean_object* v_pkgDir_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; uint8_t v___x_2638_; 
lean_inc_ref(v___y_2630_);
v_pkgDir_2633_ = l_Lake_joinRelative(v_wsDir_2387_, v___y_2630_);
lean_inc_ref(v_pkgDir_2633_);
v___x_2634_ = l_Lake_resolvePath(v_pkgDir_2633_);
v___x_2635_ = lean_unsigned_to_nat(0u);
v___x_2636_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0));
v___x_2637_ = lean_string_utf8_byte_size(v___x_2634_);
v___x_2638_ = lean_nat_dec_eq(v___x_2637_, v___x_2635_);
if (v___x_2638_ == 0)
{
lean_object* v___x_2639_; 
v___x_2639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2639_, 0, v___x_2634_);
v___y_2596_ = v___y_2632_;
v___y_2597_ = v_pkgDir_2633_;
v___y_2598_ = v___x_2635_;
v___y_2599_ = v___y_2630_;
v___y_2600_ = v___x_2636_;
v___y_2601_ = v___y_2631_;
v_val_2602_ = v___x_2639_;
goto v___jp_2595_;
}
else
{
lean_object* v___x_2640_; 
lean_dec_ref(v___x_2634_);
v___x_2640_ = lean_box(0);
v___y_2596_ = v___y_2632_;
v___y_2597_ = v_pkgDir_2633_;
v___y_2598_ = v___x_2635_;
v___y_2599_ = v___y_2630_;
v___y_2600_ = v___x_2636_;
v___y_2601_ = v___y_2631_;
v_val_2602_ = v___x_2640_;
goto v___jp_2595_;
}
}
v___jp_2641_:
{
lean_object* v___x_2644_; 
v___x_2644_ = l_Lake_Git_filterUrl_x3f(v_url_2552_);
if (lean_obj_tag(v___x_2644_) == 0)
{
lean_object* v___x_2645_; 
v___x_2645_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___y_2630_ = v___y_2643_;
v___y_2631_ = v___y_2642_;
v___y_2632_ = v___x_2645_;
goto v___jp_2629_;
}
else
{
lean_object* v_val_2646_; 
v_val_2646_ = lean_ctor_get(v___x_2644_, 0);
lean_inc(v_val_2646_);
lean_dec_ref_known(v___x_2644_, 1);
v___y_2630_ = v___y_2643_;
v___y_2631_ = v___y_2642_;
v___y_2632_ = v_val_2646_;
goto v___jp_2629_;
}
}
v___jp_2648_:
{
if (lean_obj_tag(v_subDir_x3f_2554_) == 0)
{
v___y_2642_ = v___y_2649_;
v___y_2643_ = v_relGitDir_2647_;
goto v___jp_2641_;
}
else
{
lean_object* v_val_2650_; lean_object* v___x_2651_; 
v_val_2650_ = lean_ctor_get(v_subDir_x3f_2554_, 0);
lean_inc(v_val_2650_);
lean_dec_ref_known(v_subDir_x3f_2554_, 1);
v___x_2651_ = l_Lake_joinRelative(v_relGitDir_2647_, v_val_2650_);
v___y_2642_ = v___y_2649_;
v___y_2643_ = v___x_2651_;
goto v___jp_2641_;
}
}
v___jp_2653_:
{
lean_object* v___x_2655_; lean_object* v___x_2656_; 
v___x_2655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2655_, 0, v_rev_2553_);
lean_inc_ref(v___x_2556_);
v___x_2656_ = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(v_a_2389_, v___x_2556_, v_gitDir_2652_, v___y_2654_, v___x_2655_);
if (lean_obj_tag(v___x_2656_) == 0)
{
lean_dec_ref_known(v___x_2656_, 1);
v___y_2649_ = v_a_2389_;
goto v___jp_2648_;
}
else
{
lean_object* v_a_2657_; lean_object* v___x_2659_; uint8_t v_isShared_2660_; uint8_t v_isSharedCheck_2664_; 
lean_dec_ref(v_relGitDir_2647_);
lean_dec_ref(v___x_2556_);
lean_dec(v_subDir_x3f_2554_);
lean_dec_ref(v_url_2552_);
lean_dec_ref(v_wsDir_2387_);
lean_dec_ref(v_manifestEntry_2385_);
v_a_2657_ = lean_ctor_get(v___x_2656_, 0);
v_isSharedCheck_2664_ = !lean_is_exclusive(v___x_2656_);
if (v_isSharedCheck_2664_ == 0)
{
v___x_2659_ = v___x_2656_;
v_isShared_2660_ = v_isSharedCheck_2664_;
goto v_resetjp_2658_;
}
else
{
lean_inc(v_a_2657_);
lean_dec(v___x_2656_);
v___x_2659_ = lean_box(0);
v_isShared_2660_ = v_isSharedCheck_2664_;
goto v_resetjp_2658_;
}
v_resetjp_2658_:
{
lean_object* v___x_2662_; 
if (v_isShared_2660_ == 0)
{
v___x_2662_ = v___x_2659_;
goto v_reusejp_2661_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v_a_2657_);
v___x_2662_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2661_;
}
v_reusejp_2661_:
{
return v___x_2662_;
}
}
}
}
v___jp_2665_:
{
lean_object* v___x_2668_; 
lean_inc_ref(v___x_2556_);
v___x_2668_ = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_2389_, v___x_2556_, v_gitDir_2652_, v___y_2667_, v___y_2666_);
if (lean_obj_tag(v___x_2668_) == 0)
{
lean_dec_ref_known(v___x_2668_, 1);
v___y_2649_ = v_a_2389_;
goto v___jp_2648_;
}
else
{
lean_object* v_a_2669_; lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2676_; 
lean_dec_ref(v_relGitDir_2647_);
lean_dec_ref(v___x_2556_);
lean_dec(v_subDir_x3f_2554_);
lean_dec_ref(v_url_2552_);
lean_dec_ref(v_wsDir_2387_);
lean_dec_ref(v_manifestEntry_2385_);
v_a_2669_ = lean_ctor_get(v___x_2668_, 0);
v_isSharedCheck_2676_ = !lean_is_exclusive(v___x_2668_);
if (v_isSharedCheck_2676_ == 0)
{
v___x_2671_ = v___x_2668_;
v_isShared_2672_ = v_isSharedCheck_2676_;
goto v_resetjp_2670_;
}
else
{
lean_inc(v_a_2669_);
lean_dec(v___x_2668_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_2676_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
lean_object* v___x_2674_; 
if (v_isShared_2672_ == 0)
{
v___x_2674_ = v___x_2671_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v_a_2669_);
v___x_2674_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
return v___x_2674_;
}
}
}
}
v___jp_2677_:
{
if (v_a_2678_ == 0)
{
lean_dec_ref(v_gitDir_2652_);
v___y_2649_ = v_a_2389_;
goto v___jp_2648_;
}
else
{
lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; uint8_t v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; 
v___x_2679_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1));
lean_inc_ref(v___x_2556_);
v___x_2680_ = lean_string_append(v___x_2556_, v___x_2679_);
v___x_2681_ = lean_string_append(v___x_2680_, v_gitDir_2652_);
lean_dec_ref(v_gitDir_2652_);
v___x_2682_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_2683_ = lean_string_append(v___x_2681_, v___x_2682_);
v___x_2684_ = 2;
v___x_2685_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2685_, 0, v___x_2683_);
lean_ctor_set_uint8(v___x_2685_, sizeof(void*)*1, v___x_2684_);
lean_inc_ref(v_a_2389_);
v___x_2686_ = lean_apply_2(v_a_2389_, v___x_2685_, lean_box(0));
v___y_2649_ = v_a_2389_;
goto v___jp_2648_;
}
}
v___jp_2687_:
{
lean_object* v___x_2689_; lean_object* v___x_2690_; uint8_t v___x_2691_; 
v___x_2689_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
v___x_2690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2690_, 0, v_rev_2553_);
lean_inc_ref(v___x_2690_);
v___x_2691_ = l_Option_instDecidableEq___redArg(v___x_2689_, v_a_2688_, v___x_2690_);
if (v___x_2691_ == 0)
{
lean_object* v_pkgUrlMap_2692_; lean_object* v___x_2693_; 
v_pkgUrlMap_2692_ = lean_ctor_get(v_lakeEnv_2386_, 5);
v___x_2693_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgUrlMap_2692_, v_name_2550_);
if (lean_obj_tag(v___x_2693_) == 0)
{
lean_inc_ref(v_url_2552_);
v___y_2666_ = v___x_2690_;
v___y_2667_ = v_url_2552_;
goto v___jp_2665_;
}
else
{
lean_object* v_val_2694_; 
v_val_2694_ = lean_ctor_get(v___x_2693_, 0);
lean_inc(v_val_2694_);
lean_dec_ref_known(v___x_2693_, 1);
v___y_2666_ = v___x_2690_;
v___y_2667_ = v_val_2694_;
goto v___jp_2665_;
}
}
else
{
uint8_t v___x_2695_; lean_object* v___x_2696_; uint8_t v___x_2697_; uint8_t v___x_2698_; 
lean_dec_ref_known(v___x_2690_, 1);
lean_inc_ref(v_gitDir_2652_);
v___x_2695_ = l_Lake_GitRepo_hasNoDiff(v_gitDir_2652_);
v___x_2696_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0));
v___x_2697_ = lean_bool_not(v___x_2695_);
v___x_2698_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__6);
if (v___x_2698_ == 0)
{
v_a_2678_ = v___x_2697_;
goto v___jp_2677_;
}
else
{
lean_object* v___x_2699_; uint8_t v___x_2700_; 
v___x_2699_ = lean_box(0);
v___x_2700_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__7);
if (v___x_2700_ == 0)
{
if (v___x_2698_ == 0)
{
v_a_2678_ = v___x_2697_;
goto v___jp_2677_;
}
else
{
size_t v___x_2701_; size_t v___x_2702_; lean_object* v___x_2703_; 
v___x_2701_ = ((size_t)0ULL);
v___x_2702_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8);
v___x_2703_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_2696_, v___x_2701_, v___x_2702_, v___x_2699_, v_a_2389_);
if (lean_obj_tag(v___x_2703_) == 0)
{
lean_dec_ref_known(v___x_2703_, 1);
v_a_2678_ = v___x_2697_;
goto v___jp_2677_;
}
else
{
lean_object* v_a_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2711_; 
lean_dec_ref(v_gitDir_2652_);
lean_dec_ref(v_relGitDir_2647_);
lean_dec_ref(v___x_2556_);
lean_dec(v_subDir_x3f_2554_);
lean_dec_ref(v_url_2552_);
lean_dec_ref(v_wsDir_2387_);
lean_dec_ref(v_manifestEntry_2385_);
v_a_2704_ = lean_ctor_get(v___x_2703_, 0);
v_isSharedCheck_2711_ = !lean_is_exclusive(v___x_2703_);
if (v_isSharedCheck_2711_ == 0)
{
v___x_2706_ = v___x_2703_;
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_a_2704_);
lean_dec(v___x_2703_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
lean_object* v___x_2709_; 
if (v_isShared_2707_ == 0)
{
v___x_2709_ = v___x_2706_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v_a_2704_);
v___x_2709_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
return v___x_2709_;
}
}
}
}
}
else
{
size_t v___x_2712_; size_t v___x_2713_; lean_object* v___x_2714_; 
v___x_2712_ = ((size_t)0ULL);
v___x_2713_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8);
v___x_2714_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_2696_, v___x_2712_, v___x_2713_, v___x_2699_, v_a_2389_);
if (lean_obj_tag(v___x_2714_) == 0)
{
lean_dec_ref_known(v___x_2714_, 1);
v_a_2678_ = v___x_2697_;
goto v___jp_2677_;
}
else
{
lean_object* v_a_2715_; lean_object* v___x_2717_; uint8_t v_isShared_2718_; uint8_t v_isSharedCheck_2722_; 
lean_dec_ref(v_gitDir_2652_);
lean_dec_ref(v_relGitDir_2647_);
lean_dec_ref(v___x_2556_);
lean_dec(v_subDir_x3f_2554_);
lean_dec_ref(v_url_2552_);
lean_dec_ref(v_wsDir_2387_);
lean_dec_ref(v_manifestEntry_2385_);
v_a_2715_ = lean_ctor_get(v___x_2714_, 0);
v_isSharedCheck_2722_ = !lean_is_exclusive(v___x_2714_);
if (v_isSharedCheck_2722_ == 0)
{
v___x_2717_ = v___x_2714_;
v_isShared_2718_ = v_isSharedCheck_2722_;
goto v_resetjp_2716_;
}
else
{
lean_inc(v_a_2715_);
lean_dec(v___x_2714_);
v___x_2717_ = lean_box(0);
v_isShared_2718_ = v_isSharedCheck_2722_;
goto v_resetjp_2716_;
}
v_resetjp_2716_:
{
lean_object* v___x_2720_; 
if (v_isShared_2718_ == 0)
{
v___x_2720_ = v___x_2717_;
goto v_reusejp_2719_;
}
else
{
lean_object* v_reuseFailAlloc_2721_; 
v_reuseFailAlloc_2721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2721_, 0, v_a_2715_);
v___x_2720_ = v_reuseFailAlloc_2721_;
goto v_reusejp_2719_;
}
v_reusejp_2719_:
{
return v___x_2720_;
}
}
}
}
}
}
}
v___jp_2724_:
{
if (v___x_2723_ == 0)
{
lean_object* v_pkgUrlMap_2725_; lean_object* v___x_2726_; 
v_pkgUrlMap_2725_ = lean_ctor_get(v_lakeEnv_2386_, 5);
v___x_2726_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgUrlMap_2725_, v_name_2550_);
if (lean_obj_tag(v___x_2726_) == 0)
{
lean_inc_ref(v_url_2552_);
v___y_2654_ = v_url_2552_;
goto v___jp_2653_;
}
else
{
lean_object* v_val_2727_; 
v_val_2727_ = lean_ctor_get(v___x_2726_, 0);
lean_inc(v_val_2727_);
lean_dec_ref_known(v___x_2726_, 1);
v___y_2654_ = v_val_2727_;
goto v___jp_2653_;
}
}
else
{
lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; uint8_t v___x_2731_; 
v___x_2728_ = ((lean_object*)(l_Lake_PackageEntry_materialize___closed__0));
lean_inc_ref(v_gitDir_2652_);
v___x_2729_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_2728_, v_gitDir_2652_);
v___x_2730_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0));
v___x_2731_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__6);
if (v___x_2731_ == 0)
{
v_a_2688_ = v___x_2729_;
goto v___jp_2687_;
}
else
{
lean_object* v___x_2732_; uint8_t v___x_2733_; 
v___x_2732_ = lean_box(0);
v___x_2733_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__7);
if (v___x_2733_ == 0)
{
if (v___x_2731_ == 0)
{
v_a_2688_ = v___x_2729_;
goto v___jp_2687_;
}
else
{
size_t v___x_2734_; size_t v___x_2735_; lean_object* v___x_2736_; 
v___x_2734_ = ((size_t)0ULL);
v___x_2735_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8);
v___x_2736_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_2730_, v___x_2734_, v___x_2735_, v___x_2732_, v_a_2389_);
if (lean_obj_tag(v___x_2736_) == 0)
{
lean_dec_ref_known(v___x_2736_, 1);
v_a_2688_ = v___x_2729_;
goto v___jp_2687_;
}
else
{
lean_object* v_a_2737_; lean_object* v___x_2739_; uint8_t v_isShared_2740_; uint8_t v_isSharedCheck_2744_; 
lean_dec(v___x_2729_);
lean_dec_ref(v_gitDir_2652_);
lean_dec_ref(v_relGitDir_2647_);
lean_dec_ref(v___x_2556_);
lean_dec(v_subDir_x3f_2554_);
lean_dec_ref(v_rev_2553_);
lean_dec_ref(v_url_2552_);
lean_dec_ref(v_wsDir_2387_);
lean_dec_ref(v_manifestEntry_2385_);
v_a_2737_ = lean_ctor_get(v___x_2736_, 0);
v_isSharedCheck_2744_ = !lean_is_exclusive(v___x_2736_);
if (v_isSharedCheck_2744_ == 0)
{
v___x_2739_ = v___x_2736_;
v_isShared_2740_ = v_isSharedCheck_2744_;
goto v_resetjp_2738_;
}
else
{
lean_inc(v_a_2737_);
lean_dec(v___x_2736_);
v___x_2739_ = lean_box(0);
v_isShared_2740_ = v_isSharedCheck_2744_;
goto v_resetjp_2738_;
}
v_resetjp_2738_:
{
lean_object* v___x_2742_; 
if (v_isShared_2740_ == 0)
{
v___x_2742_ = v___x_2739_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v_a_2737_);
v___x_2742_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
return v___x_2742_;
}
}
}
}
}
else
{
size_t v___x_2745_; size_t v___x_2746_; lean_object* v___x_2747_; 
v___x_2745_ = ((size_t)0ULL);
v___x_2746_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8, &l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__8);
v___x_2747_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_2730_, v___x_2745_, v___x_2746_, v___x_2732_, v_a_2389_);
if (lean_obj_tag(v___x_2747_) == 0)
{
lean_dec_ref_known(v___x_2747_, 1);
v_a_2688_ = v___x_2729_;
goto v___jp_2687_;
}
else
{
lean_object* v_a_2748_; lean_object* v___x_2750_; uint8_t v_isShared_2751_; uint8_t v_isSharedCheck_2755_; 
lean_dec(v___x_2729_);
lean_dec_ref(v_gitDir_2652_);
lean_dec_ref(v_relGitDir_2647_);
lean_dec_ref(v___x_2556_);
lean_dec(v_subDir_x3f_2554_);
lean_dec_ref(v_rev_2553_);
lean_dec_ref(v_url_2552_);
lean_dec_ref(v_wsDir_2387_);
lean_dec_ref(v_manifestEntry_2385_);
v_a_2748_ = lean_ctor_get(v___x_2747_, 0);
v_isSharedCheck_2755_ = !lean_is_exclusive(v___x_2747_);
if (v_isSharedCheck_2755_ == 0)
{
v___x_2750_ = v___x_2747_;
v_isShared_2751_ = v_isSharedCheck_2755_;
goto v_resetjp_2749_;
}
else
{
lean_inc(v_a_2748_);
lean_dec(v___x_2747_);
v___x_2750_ = lean_box(0);
v_isShared_2751_ = v_isSharedCheck_2755_;
goto v_resetjp_2749_;
}
v_resetjp_2749_:
{
lean_object* v___x_2753_; 
if (v_isShared_2751_ == 0)
{
v___x_2753_ = v___x_2750_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v_a_2748_);
v___x_2753_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
return v___x_2753_;
}
}
}
}
}
}
}
}
v___jp_2391_:
{
lean_object* v___x_2396_; lean_object* v___x_2397_; 
v___x_2396_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2396_, 0, v___y_2393_);
lean_ctor_set(v___x_2396_, 1, v___y_2394_);
lean_ctor_set(v___x_2396_, 2, v___y_2392_);
lean_ctor_set(v___x_2396_, 3, v_a_2395_);
lean_ctor_set(v___x_2396_, 4, v_manifestEntry_2385_);
v___x_2397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2397_, 0, v___x_2396_);
return v___x_2397_;
}
v___jp_2398_:
{
lean_object* v___x_2406_; uint8_t v___x_2407_; 
v___x_2406_ = lean_array_get_size(v___y_2400_);
v___x_2407_ = lean_nat_dec_lt(v___y_2403_, v___x_2406_);
if (v___x_2407_ == 0)
{
v___y_2392_ = v___y_2399_;
v___y_2393_ = v___y_2401_;
v___y_2394_ = v___y_2402_;
v_a_2395_ = v_val_2405_;
goto v___jp_2391_;
}
else
{
lean_object* v___x_2408_; uint8_t v___x_2409_; 
v___x_2408_ = lean_box(0);
v___x_2409_ = lean_nat_dec_le(v___x_2406_, v___x_2406_);
if (v___x_2409_ == 0)
{
if (v___x_2407_ == 0)
{
v___y_2392_ = v___y_2399_;
v___y_2393_ = v___y_2401_;
v___y_2394_ = v___y_2402_;
v_a_2395_ = v_val_2405_;
goto v___jp_2391_;
}
else
{
size_t v___x_2410_; size_t v___x_2411_; lean_object* v___x_2412_; 
v___x_2410_ = ((size_t)0ULL);
v___x_2411_ = lean_usize_of_nat(v___x_2406_);
v___x_2412_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_2400_, v___x_2410_, v___x_2411_, v___x_2408_, v___y_2404_);
if (lean_obj_tag(v___x_2412_) == 0)
{
lean_dec_ref_known(v___x_2412_, 1);
v___y_2392_ = v___y_2399_;
v___y_2393_ = v___y_2401_;
v___y_2394_ = v___y_2402_;
v_a_2395_ = v_val_2405_;
goto v___jp_2391_;
}
else
{
lean_object* v_a_2413_; lean_object* v___x_2415_; uint8_t v_isShared_2416_; uint8_t v_isSharedCheck_2420_; 
lean_dec_ref(v_val_2405_);
lean_dec_ref(v___y_2402_);
lean_dec_ref(v___y_2401_);
lean_dec_ref(v___y_2399_);
lean_dec_ref(v_manifestEntry_2385_);
v_a_2413_ = lean_ctor_get(v___x_2412_, 0);
v_isSharedCheck_2420_ = !lean_is_exclusive(v___x_2412_);
if (v_isSharedCheck_2420_ == 0)
{
v___x_2415_ = v___x_2412_;
v_isShared_2416_ = v_isSharedCheck_2420_;
goto v_resetjp_2414_;
}
else
{
lean_inc(v_a_2413_);
lean_dec(v___x_2412_);
v___x_2415_ = lean_box(0);
v_isShared_2416_ = v_isSharedCheck_2420_;
goto v_resetjp_2414_;
}
v_resetjp_2414_:
{
lean_object* v___x_2418_; 
if (v_isShared_2416_ == 0)
{
v___x_2418_ = v___x_2415_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v_a_2413_);
v___x_2418_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2417_;
}
v_reusejp_2417_:
{
return v___x_2418_;
}
}
}
}
}
else
{
size_t v___x_2421_; size_t v___x_2422_; lean_object* v___x_2423_; 
v___x_2421_ = ((size_t)0ULL);
v___x_2422_ = lean_usize_of_nat(v___x_2406_);
v___x_2423_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_2400_, v___x_2421_, v___x_2422_, v___x_2408_, v___y_2404_);
if (lean_obj_tag(v___x_2423_) == 0)
{
lean_dec_ref_known(v___x_2423_, 1);
v___y_2392_ = v___y_2399_;
v___y_2393_ = v___y_2401_;
v___y_2394_ = v___y_2402_;
v_a_2395_ = v_val_2405_;
goto v___jp_2391_;
}
else
{
lean_object* v_a_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2431_; 
lean_dec_ref(v_val_2405_);
lean_dec_ref(v___y_2402_);
lean_dec_ref(v___y_2401_);
lean_dec_ref(v___y_2399_);
lean_dec_ref(v_manifestEntry_2385_);
v_a_2424_ = lean_ctor_get(v___x_2423_, 0);
v_isSharedCheck_2431_ = !lean_is_exclusive(v___x_2423_);
if (v_isSharedCheck_2431_ == 0)
{
v___x_2426_ = v___x_2423_;
v_isShared_2427_ = v_isSharedCheck_2431_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_a_2424_);
lean_dec(v___x_2423_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2431_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v___x_2429_; 
if (v_isShared_2427_ == 0)
{
v___x_2429_ = v___x_2426_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v_a_2424_);
v___x_2429_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
return v___x_2429_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize___boxed(lean_object* v_manifestEntry_2782_, lean_object* v_lakeEnv_2783_, lean_object* v_wsDir_2784_, lean_object* v_relPkgsDir_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_){
_start:
{
lean_object* v_res_2788_; 
v_res_2788_ = l_Lake_PackageEntry_materialize(v_manifestEntry_2782_, v_lakeEnv_2783_, v_wsDir_2784_, v_relPkgsDir_2785_, v_a_2786_);
lean_dec_ref(v_a_2786_);
lean_dec_ref(v_lakeEnv_2783_);
return v_res_2788_;
}
}
lean_object* runtime_initialize_Lake_Config_Env(uint8_t builtin);
lean_object* runtime_initialize_Lake_Load_Manifest(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Package(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Git(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_IO(uint8_t builtin);
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
res = runtime_initialize_Lake_Util_IO(builtin);
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
lean_object* initialize_Lake_Util_IO(uint8_t builtin);
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
res = initialize_Lake_Util_IO(builtin);
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

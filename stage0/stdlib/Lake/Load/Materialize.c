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
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = ": repository '"};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0_value;
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "' has local changes"};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1_value;
static const lean_array_object l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2_value;
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = ": checking out revision '"};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3_value;
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
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
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg(lean_object* v_name_29_, lean_object* v_repo_30_, lean_object* v_rev_x3f_31_, lean_object* v_a_32_){
_start:
{
uint8_t v_a_35_; lean_object* v___y_48_; lean_object* v___y_49_; uint8_t v_val_50_; lean_object* v___y_115_; lean_object* v___y_117_; lean_object* v_a_118_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_165_ = l_Lake_Git_defaultRemote;
v___x_166_ = lean_unsigned_to_nat(0u);
v___x_167_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
lean_inc_ref(v_repo_30_);
v___x_168_ = l_Lake_GitRepo_findRemoteRevision(v_repo_30_, v_rev_x3f_31_, v___x_165_, v___x_167_);
if (lean_obj_tag(v___x_168_) == 0)
{
lean_object* v_a_169_; lean_object* v_a_170_; lean_object* v___x_198_; uint8_t v___x_199_; 
v_a_169_ = lean_ctor_get(v___x_168_, 0);
lean_inc(v_a_169_);
v_a_170_ = lean_ctor_get(v___x_168_, 1);
lean_inc(v_a_170_);
lean_dec_ref_known(v___x_168_, 2);
v___x_198_ = lean_array_get_size(v_a_170_);
v___x_199_ = lean_nat_dec_lt(v___x_166_, v___x_198_);
if (v___x_199_ == 0)
{
lean_dec(v_a_170_);
goto v___jp_171_;
}
else
{
lean_object* v___x_200_; uint8_t v___x_201_; 
v___x_200_ = lean_box(0);
v___x_201_ = lean_nat_dec_le(v___x_198_, v___x_198_);
if (v___x_201_ == 0)
{
if (v___x_199_ == 0)
{
lean_dec(v_a_170_);
goto v___jp_171_;
}
else
{
size_t v___x_202_; size_t v___x_203_; lean_object* v___x_204_; 
v___x_202_ = ((size_t)0ULL);
v___x_203_ = lean_usize_of_nat(v___x_198_);
v___x_204_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_170_, v___x_202_, v___x_203_, v___x_200_, v_a_32_);
lean_dec(v_a_170_);
if (lean_obj_tag(v___x_204_) == 0)
{
lean_dec_ref_known(v___x_204_, 1);
goto v___jp_171_;
}
else
{
lean_dec(v_a_169_);
lean_dec_ref(v_repo_30_);
lean_dec_ref(v_name_29_);
return v___x_204_;
}
}
}
else
{
size_t v___x_205_; size_t v___x_206_; lean_object* v___x_207_; 
v___x_205_ = ((size_t)0ULL);
v___x_206_ = lean_usize_of_nat(v___x_198_);
v___x_207_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_170_, v___x_205_, v___x_206_, v___x_200_, v_a_32_);
lean_dec(v_a_170_);
if (lean_obj_tag(v___x_207_) == 0)
{
lean_dec_ref_known(v___x_207_, 1);
goto v___jp_171_;
}
else
{
lean_dec(v_a_169_);
lean_dec_ref(v_repo_30_);
lean_dec_ref(v_name_29_);
return v___x_207_;
}
}
}
v___jp_171_:
{
lean_object* v___x_172_; 
lean_inc_ref(v_repo_30_);
v___x_172_ = l_Lake_GitRepo_getHeadRevision(v_repo_30_, v___x_167_);
if (lean_obj_tag(v___x_172_) == 0)
{
lean_object* v_a_173_; lean_object* v_a_174_; lean_object* v___x_175_; uint8_t v___x_176_; 
v_a_173_ = lean_ctor_get(v___x_172_, 0);
lean_inc(v_a_173_);
v_a_174_ = lean_ctor_get(v___x_172_, 1);
lean_inc(v_a_174_);
lean_dec_ref_known(v___x_172_, 2);
v___x_175_ = lean_array_get_size(v_a_174_);
v___x_176_ = lean_nat_dec_lt(v___x_166_, v___x_175_);
if (v___x_176_ == 0)
{
lean_dec(v_a_174_);
v___y_117_ = v_a_169_;
v_a_118_ = v_a_173_;
goto v___jp_116_;
}
else
{
lean_object* v___x_177_; uint8_t v___x_178_; 
v___x_177_ = lean_box(0);
v___x_178_ = lean_nat_dec_le(v___x_175_, v___x_175_);
if (v___x_178_ == 0)
{
if (v___x_176_ == 0)
{
lean_dec(v_a_174_);
v___y_117_ = v_a_169_;
v_a_118_ = v_a_173_;
goto v___jp_116_;
}
else
{
size_t v___x_179_; size_t v___x_180_; lean_object* v___x_181_; 
v___x_179_ = ((size_t)0ULL);
v___x_180_ = lean_usize_of_nat(v___x_175_);
v___x_181_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_174_, v___x_179_, v___x_180_, v___x_177_, v_a_32_);
lean_dec(v_a_174_);
if (lean_obj_tag(v___x_181_) == 0)
{
lean_dec_ref_known(v___x_181_, 1);
v___y_117_ = v_a_169_;
v_a_118_ = v_a_173_;
goto v___jp_116_;
}
else
{
lean_dec(v_a_173_);
lean_dec(v_a_169_);
lean_dec_ref(v_repo_30_);
lean_dec_ref(v_name_29_);
return v___x_181_;
}
}
}
else
{
size_t v___x_182_; size_t v___x_183_; lean_object* v___x_184_; 
v___x_182_ = ((size_t)0ULL);
v___x_183_ = lean_usize_of_nat(v___x_175_);
v___x_184_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_174_, v___x_182_, v___x_183_, v___x_177_, v_a_32_);
lean_dec(v_a_174_);
if (lean_obj_tag(v___x_184_) == 0)
{
lean_dec_ref_known(v___x_184_, 1);
v___y_117_ = v_a_169_;
v_a_118_ = v_a_173_;
goto v___jp_116_;
}
else
{
lean_dec(v_a_173_);
lean_dec(v_a_169_);
lean_dec_ref(v_repo_30_);
lean_dec_ref(v_name_29_);
return v___x_184_;
}
}
}
}
else
{
lean_object* v_a_185_; lean_object* v___x_186_; uint8_t v___x_187_; 
lean_dec(v_a_169_);
lean_dec_ref(v_repo_30_);
lean_dec_ref(v_name_29_);
v_a_185_ = lean_ctor_get(v___x_172_, 1);
lean_inc(v_a_185_);
lean_dec_ref_known(v___x_172_, 2);
v___x_186_ = lean_array_get_size(v_a_185_);
v___x_187_ = lean_nat_dec_lt(v___x_166_, v___x_186_);
if (v___x_187_ == 0)
{
lean_object* v___x_188_; lean_object* v___x_189_; 
lean_dec(v_a_185_);
v___x_188_ = lean_box(0);
v___x_189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_189_, 0, v___x_188_);
return v___x_189_;
}
else
{
lean_object* v___x_190_; uint8_t v___x_191_; 
v___x_190_ = lean_box(0);
v___x_191_ = lean_nat_dec_le(v___x_186_, v___x_186_);
if (v___x_191_ == 0)
{
if (v___x_187_ == 0)
{
lean_dec(v_a_185_);
goto v___jp_159_;
}
else
{
size_t v___x_192_; size_t v___x_193_; lean_object* v___x_194_; 
v___x_192_ = ((size_t)0ULL);
v___x_193_ = lean_usize_of_nat(v___x_186_);
v___x_194_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_185_, v___x_192_, v___x_193_, v___x_190_, v_a_32_);
lean_dec(v_a_185_);
if (lean_obj_tag(v___x_194_) == 0)
{
lean_dec_ref_known(v___x_194_, 1);
goto v___jp_159_;
}
else
{
return v___x_194_;
}
}
}
else
{
size_t v___x_195_; size_t v___x_196_; lean_object* v___x_197_; 
v___x_195_ = ((size_t)0ULL);
v___x_196_ = lean_usize_of_nat(v___x_186_);
v___x_197_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_185_, v___x_195_, v___x_196_, v___x_190_, v_a_32_);
lean_dec(v_a_185_);
if (lean_obj_tag(v___x_197_) == 0)
{
lean_dec_ref_known(v___x_197_, 1);
goto v___jp_159_;
}
else
{
return v___x_197_;
}
}
}
}
}
}
else
{
lean_object* v_a_208_; lean_object* v___x_209_; uint8_t v___x_210_; 
lean_dec_ref(v_repo_30_);
lean_dec_ref(v_name_29_);
v_a_208_ = lean_ctor_get(v___x_168_, 1);
lean_inc(v_a_208_);
lean_dec_ref_known(v___x_168_, 2);
v___x_209_ = lean_array_get_size(v_a_208_);
v___x_210_ = lean_nat_dec_lt(v___x_166_, v___x_209_);
if (v___x_210_ == 0)
{
lean_object* v___x_211_; lean_object* v___x_212_; 
lean_dec(v_a_208_);
v___x_211_ = lean_box(0);
v___x_212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_212_, 0, v___x_211_);
return v___x_212_;
}
else
{
lean_object* v___x_213_; uint8_t v___x_214_; 
v___x_213_ = lean_box(0);
v___x_214_ = lean_nat_dec_le(v___x_209_, v___x_209_);
if (v___x_214_ == 0)
{
if (v___x_210_ == 0)
{
lean_dec(v_a_208_);
goto v___jp_162_;
}
else
{
size_t v___x_215_; size_t v___x_216_; lean_object* v___x_217_; 
v___x_215_ = ((size_t)0ULL);
v___x_216_ = lean_usize_of_nat(v___x_209_);
v___x_217_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_208_, v___x_215_, v___x_216_, v___x_213_, v_a_32_);
lean_dec(v_a_208_);
if (lean_obj_tag(v___x_217_) == 0)
{
lean_dec_ref_known(v___x_217_, 1);
goto v___jp_162_;
}
else
{
return v___x_217_;
}
}
}
else
{
size_t v___x_218_; size_t v___x_219_; lean_object* v___x_220_; 
v___x_218_ = ((size_t)0ULL);
v___x_219_ = lean_usize_of_nat(v___x_209_);
v___x_220_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_208_, v___x_218_, v___x_219_, v___x_213_, v_a_32_);
lean_dec(v_a_208_);
if (lean_obj_tag(v___x_220_) == 0)
{
lean_dec_ref_known(v___x_220_, 1);
goto v___jp_162_;
}
else
{
return v___x_220_;
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
v___x_51_ = lean_array_get_size(v___y_49_);
v___x_52_ = lean_nat_dec_lt(v___y_48_, v___x_51_);
if (v___x_52_ == 0)
{
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
v_a_35_ = v_val_50_;
goto v___jp_34_;
}
else
{
size_t v___x_55_; size_t v___x_56_; lean_object* v___x_57_; 
v___x_55_ = ((size_t)0ULL);
v___x_56_ = lean_usize_of_nat(v___x_51_);
v___x_57_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_49_, v___x_55_, v___x_56_, v___x_53_, v_a_32_);
if (lean_obj_tag(v___x_57_) == 0)
{
lean_dec_ref_known(v___x_57_, 1);
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
v___x_60_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_49_, v___x_58_, v___x_59_, v___x_53_, v_a_32_);
if (lean_obj_tag(v___x_60_) == 0)
{
lean_dec_ref_known(v___x_60_, 1);
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
lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_65_ = lean_box(0);
v___x_66_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_66_, 0, v___x_65_);
return v___x_66_;
}
v___jp_67_:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_68_ = lean_unsigned_to_nat(0u);
v___x_69_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_70_ = l_Lake_GitRepo_clean(v_repo_30_, v___x_69_);
if (lean_obj_tag(v___x_70_) == 0)
{
lean_object* v_a_71_; lean_object* v_a_72_; lean_object* v___x_73_; uint8_t v___x_74_; 
v_a_71_ = lean_ctor_get(v___x_70_, 0);
lean_inc(v_a_71_);
v_a_72_ = lean_ctor_get(v___x_70_, 1);
lean_inc(v_a_72_);
lean_dec_ref_known(v___x_70_, 2);
v___x_73_ = lean_array_get_size(v_a_72_);
v___x_74_ = lean_nat_dec_lt(v___x_68_, v___x_73_);
if (v___x_74_ == 0)
{
lean_object* v___x_75_; 
lean_dec(v_a_72_);
v___x_75_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_75_, 0, v_a_71_);
return v___x_75_;
}
else
{
lean_object* v___x_76_; uint8_t v___x_77_; 
v___x_76_ = lean_box(0);
v___x_77_ = lean_nat_dec_le(v___x_73_, v___x_73_);
if (v___x_77_ == 0)
{
if (v___x_74_ == 0)
{
lean_object* v___x_78_; 
lean_dec(v_a_72_);
v___x_78_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_78_, 0, v_a_71_);
return v___x_78_;
}
else
{
size_t v___x_79_; size_t v___x_80_; lean_object* v___x_81_; 
v___x_79_ = ((size_t)0ULL);
v___x_80_ = lean_usize_of_nat(v___x_73_);
v___x_81_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_72_, v___x_79_, v___x_80_, v___x_76_, v_a_32_);
lean_dec(v_a_72_);
if (lean_obj_tag(v___x_81_) == 0)
{
lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_88_; 
v_isSharedCheck_88_ = !lean_is_exclusive(v___x_81_);
if (v_isSharedCheck_88_ == 0)
{
lean_object* v_unused_89_; 
v_unused_89_ = lean_ctor_get(v___x_81_, 0);
lean_dec(v_unused_89_);
v___x_83_ = v___x_81_;
v_isShared_84_ = v_isSharedCheck_88_;
goto v_resetjp_82_;
}
else
{
lean_dec(v___x_81_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_88_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
lean_object* v___x_86_; 
if (v_isShared_84_ == 0)
{
lean_ctor_set(v___x_83_, 0, v_a_71_);
v___x_86_ = v___x_83_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v_a_71_);
v___x_86_ = v_reuseFailAlloc_87_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
return v___x_86_;
}
}
}
else
{
lean_dec(v_a_71_);
return v___x_81_;
}
}
}
else
{
size_t v___x_90_; size_t v___x_91_; lean_object* v___x_92_; 
v___x_90_ = ((size_t)0ULL);
v___x_91_ = lean_usize_of_nat(v___x_73_);
v___x_92_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_72_, v___x_90_, v___x_91_, v___x_76_, v_a_32_);
lean_dec(v_a_72_);
if (lean_obj_tag(v___x_92_) == 0)
{
lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_99_; 
v_isSharedCheck_99_ = !lean_is_exclusive(v___x_92_);
if (v_isSharedCheck_99_ == 0)
{
lean_object* v_unused_100_; 
v_unused_100_ = lean_ctor_get(v___x_92_, 0);
lean_dec(v_unused_100_);
v___x_94_ = v___x_92_;
v_isShared_95_ = v_isSharedCheck_99_;
goto v_resetjp_93_;
}
else
{
lean_dec(v___x_92_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_99_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v___x_97_; 
if (v_isShared_95_ == 0)
{
lean_ctor_set(v___x_94_, 0, v_a_71_);
v___x_97_ = v___x_94_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v_a_71_);
v___x_97_ = v_reuseFailAlloc_98_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
return v___x_97_;
}
}
}
else
{
lean_dec(v_a_71_);
return v___x_92_;
}
}
}
}
else
{
lean_object* v_a_101_; lean_object* v___x_102_; uint8_t v___x_103_; 
v_a_101_ = lean_ctor_get(v___x_70_, 1);
lean_inc(v_a_101_);
lean_dec_ref_known(v___x_70_, 2);
v___x_102_ = lean_array_get_size(v_a_101_);
v___x_103_ = lean_nat_dec_lt(v___x_68_, v___x_102_);
if (v___x_103_ == 0)
{
lean_object* v___x_104_; lean_object* v___x_105_; 
lean_dec(v_a_101_);
v___x_104_ = lean_box(0);
v___x_105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_105_, 0, v___x_104_);
return v___x_105_;
}
else
{
lean_object* v___x_106_; uint8_t v___x_107_; 
v___x_106_ = lean_box(0);
v___x_107_ = lean_nat_dec_le(v___x_102_, v___x_102_);
if (v___x_107_ == 0)
{
if (v___x_103_ == 0)
{
lean_dec(v_a_101_);
goto v___jp_64_;
}
else
{
size_t v___x_108_; size_t v___x_109_; lean_object* v___x_110_; 
v___x_108_ = ((size_t)0ULL);
v___x_109_ = lean_usize_of_nat(v___x_102_);
v___x_110_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_101_, v___x_108_, v___x_109_, v___x_106_, v_a_32_);
lean_dec(v_a_101_);
if (lean_obj_tag(v___x_110_) == 0)
{
lean_dec_ref_known(v___x_110_, 1);
goto v___jp_64_;
}
else
{
return v___x_110_;
}
}
}
else
{
size_t v___x_111_; size_t v___x_112_; lean_object* v___x_113_; 
v___x_111_ = ((size_t)0ULL);
v___x_112_ = lean_usize_of_nat(v___x_102_);
v___x_113_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_101_, v___x_111_, v___x_112_, v___x_106_, v_a_32_);
lean_dec(v_a_101_);
if (lean_obj_tag(v___x_113_) == 0)
{
lean_dec_ref_known(v___x_113_, 1);
goto v___jp_64_;
}
else
{
return v___x_113_;
}
}
}
}
}
v___jp_114_:
{
if (lean_obj_tag(v___y_115_) == 0)
{
lean_dec_ref_known(v___y_115_, 1);
goto v___jp_67_;
}
else
{
lean_dec_ref(v_repo_30_);
return v___y_115_;
}
}
v___jp_116_:
{
uint8_t v___x_119_; 
v___x_119_ = lean_string_dec_eq(v_a_118_, v___y_117_);
lean_dec_ref(v_a_118_);
if (v___x_119_ == 0)
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; uint8_t v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_120_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3));
v___x_121_ = lean_string_append(v_name_29_, v___x_120_);
v___x_122_ = lean_string_append(v___x_121_, v___y_117_);
v___x_123_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
v___x_124_ = lean_string_append(v___x_122_, v___x_123_);
v___x_125_ = 1;
v___x_126_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_126_, 0, v___x_124_);
lean_ctor_set_uint8(v___x_126_, sizeof(void*)*1, v___x_125_);
lean_inc_ref(v_a_32_);
v___x_127_ = lean_apply_2(v_a_32_, v___x_126_, lean_box(0));
v___x_128_ = lean_unsigned_to_nat(0u);
v___x_129_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
lean_inc_ref(v_repo_30_);
v___x_130_ = l_Lake_GitRepo_checkoutDetach(v___y_117_, v_repo_30_, v___x_129_);
if (lean_obj_tag(v___x_130_) == 0)
{
lean_object* v_a_131_; lean_object* v___x_132_; uint8_t v___x_133_; 
v_a_131_ = lean_ctor_get(v___x_130_, 1);
lean_inc(v_a_131_);
lean_dec_ref_known(v___x_130_, 2);
v___x_132_ = lean_array_get_size(v_a_131_);
v___x_133_ = lean_nat_dec_lt(v___x_128_, v___x_132_);
if (v___x_133_ == 0)
{
lean_dec(v_a_131_);
goto v___jp_67_;
}
else
{
lean_object* v___x_134_; uint8_t v___x_135_; 
v___x_134_ = lean_box(0);
v___x_135_ = lean_nat_dec_le(v___x_132_, v___x_132_);
if (v___x_135_ == 0)
{
if (v___x_133_ == 0)
{
lean_dec(v_a_131_);
goto v___jp_67_;
}
else
{
size_t v___x_136_; size_t v___x_137_; lean_object* v___x_138_; 
v___x_136_ = ((size_t)0ULL);
v___x_137_ = lean_usize_of_nat(v___x_132_);
v___x_138_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_131_, v___x_136_, v___x_137_, v___x_134_, v_a_32_);
lean_dec(v_a_131_);
if (lean_obj_tag(v___x_138_) == 0)
{
lean_dec_ref_known(v___x_138_, 1);
goto v___jp_67_;
}
else
{
v___y_115_ = v___x_138_;
goto v___jp_114_;
}
}
}
else
{
size_t v___x_139_; size_t v___x_140_; lean_object* v___x_141_; 
v___x_139_ = ((size_t)0ULL);
v___x_140_ = lean_usize_of_nat(v___x_132_);
v___x_141_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_131_, v___x_139_, v___x_140_, v___x_134_, v_a_32_);
lean_dec(v_a_131_);
if (lean_obj_tag(v___x_141_) == 0)
{
lean_dec_ref_known(v___x_141_, 1);
goto v___jp_67_;
}
else
{
v___y_115_ = v___x_141_;
goto v___jp_114_;
}
}
}
}
else
{
lean_object* v_a_142_; lean_object* v___x_143_; uint8_t v___x_144_; 
v_a_142_ = lean_ctor_get(v___x_130_, 1);
lean_inc(v_a_142_);
lean_dec_ref_known(v___x_130_, 2);
v___x_143_ = lean_array_get_size(v_a_142_);
v___x_144_ = lean_nat_dec_lt(v___x_128_, v___x_143_);
if (v___x_144_ == 0)
{
lean_object* v___x_145_; lean_object* v___x_146_; 
lean_dec(v_a_142_);
lean_dec_ref(v_repo_30_);
v___x_145_ = lean_box(0);
v___x_146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_146_, 0, v___x_145_);
return v___x_146_;
}
else
{
lean_object* v___x_147_; uint8_t v___x_148_; 
v___x_147_ = lean_box(0);
v___x_148_ = lean_nat_dec_le(v___x_143_, v___x_143_);
if (v___x_148_ == 0)
{
if (v___x_144_ == 0)
{
lean_dec(v_a_142_);
lean_dec_ref(v_repo_30_);
goto v___jp_61_;
}
else
{
size_t v___x_149_; size_t v___x_150_; lean_object* v___x_151_; 
v___x_149_ = ((size_t)0ULL);
v___x_150_ = lean_usize_of_nat(v___x_143_);
v___x_151_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_142_, v___x_149_, v___x_150_, v___x_147_, v_a_32_);
lean_dec(v_a_142_);
if (lean_obj_tag(v___x_151_) == 0)
{
lean_dec_ref_known(v___x_151_, 1);
lean_dec_ref(v_repo_30_);
goto v___jp_61_;
}
else
{
v___y_115_ = v___x_151_;
goto v___jp_114_;
}
}
}
else
{
size_t v___x_152_; size_t v___x_153_; lean_object* v___x_154_; 
v___x_152_ = ((size_t)0ULL);
v___x_153_ = lean_usize_of_nat(v___x_143_);
v___x_154_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_142_, v___x_152_, v___x_153_, v___x_147_, v_a_32_);
lean_dec(v_a_142_);
if (lean_obj_tag(v___x_154_) == 0)
{
lean_dec_ref_known(v___x_154_, 1);
lean_dec_ref(v_repo_30_);
goto v___jp_61_;
}
else
{
v___y_115_ = v___x_154_;
goto v___jp_114_;
}
}
}
}
}
else
{
uint8_t v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
lean_dec_ref(v___y_117_);
lean_inc_ref(v_repo_30_);
v___x_155_ = l_Lake_GitRepo_hasNoDiff(v_repo_30_);
v___x_156_ = lean_unsigned_to_nat(0u);
v___x_157_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
if (v___x_155_ == 0)
{
v___y_48_ = v___x_156_;
v___y_49_ = v___x_157_;
v_val_50_ = v___x_119_;
goto v___jp_47_;
}
else
{
uint8_t v___x_158_; 
v___x_158_ = 0;
v___y_48_ = v___x_156_;
v___y_49_ = v___x_157_;
v_val_50_ = v___x_158_;
goto v___jp_47_;
}
}
}
v___jp_159_:
{
lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_160_ = lean_box(0);
v___x_161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_161_, 0, v___x_160_);
return v___x_161_;
}
v___jp_162_:
{
lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_163_ = lean_box(0);
v___x_164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
return v___x_164_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___boxed(lean_object* v_name_221_, lean_object* v_repo_222_, lean_object* v_rev_x3f_223_, lean_object* v_a_224_, lean_object* v_a_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg(v_name_221_, v_repo_222_, v_rev_x3f_223_, v_a_224_);
lean_dec_ref(v_a_224_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg(lean_object* v_name_228_, lean_object* v_repo_229_, lean_object* v_url_230_, lean_object* v_rev_x3f_231_, lean_object* v_a_232_){
_start:
{
lean_object* v_a_238_; lean_object* v___y_336_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; uint8_t v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_340_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___closed__0));
lean_inc_ref(v_name_228_);
v___x_341_ = lean_string_append(v_name_228_, v___x_340_);
v___x_342_ = lean_string_append(v___x_341_, v_url_230_);
v___x_343_ = 1;
v___x_344_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_344_, 0, v___x_342_);
lean_ctor_set_uint8(v___x_344_, sizeof(void*)*1, v___x_343_);
lean_inc_ref(v_a_232_);
v___x_345_ = lean_apply_2(v_a_232_, v___x_344_, lean_box(0));
v___x_346_ = lean_unsigned_to_nat(0u);
v___x_347_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
lean_inc_ref(v_repo_229_);
v___x_348_ = l_Lake_GitRepo_clone(v_url_230_, v_repo_229_, v___x_347_);
if (lean_obj_tag(v___x_348_) == 0)
{
lean_object* v_a_349_; lean_object* v___x_350_; uint8_t v___x_351_; 
v_a_349_ = lean_ctor_get(v___x_348_, 1);
lean_inc(v_a_349_);
lean_dec_ref_known(v___x_348_, 2);
v___x_350_ = lean_array_get_size(v_a_349_);
v___x_351_ = lean_nat_dec_lt(v___x_346_, v___x_350_);
if (v___x_351_ == 0)
{
lean_dec(v_a_349_);
goto v___jp_296_;
}
else
{
lean_object* v___x_352_; uint8_t v___x_353_; 
v___x_352_ = lean_box(0);
v___x_353_ = lean_nat_dec_le(v___x_350_, v___x_350_);
if (v___x_353_ == 0)
{
if (v___x_351_ == 0)
{
lean_dec(v_a_349_);
goto v___jp_296_;
}
else
{
size_t v___x_354_; size_t v___x_355_; lean_object* v___x_356_; 
v___x_354_ = ((size_t)0ULL);
v___x_355_ = lean_usize_of_nat(v___x_350_);
v___x_356_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_349_, v___x_354_, v___x_355_, v___x_352_, v_a_232_);
lean_dec(v_a_349_);
if (lean_obj_tag(v___x_356_) == 0)
{
lean_dec_ref_known(v___x_356_, 1);
goto v___jp_296_;
}
else
{
v___y_336_ = v___x_356_;
goto v___jp_335_;
}
}
}
else
{
size_t v___x_357_; size_t v___x_358_; lean_object* v___x_359_; 
v___x_357_ = ((size_t)0ULL);
v___x_358_ = lean_usize_of_nat(v___x_350_);
v___x_359_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_349_, v___x_357_, v___x_358_, v___x_352_, v_a_232_);
lean_dec(v_a_349_);
if (lean_obj_tag(v___x_359_) == 0)
{
lean_dec_ref_known(v___x_359_, 1);
goto v___jp_296_;
}
else
{
v___y_336_ = v___x_359_;
goto v___jp_335_;
}
}
}
}
else
{
lean_object* v_a_360_; lean_object* v___x_361_; uint8_t v___x_362_; 
v_a_360_ = lean_ctor_get(v___x_348_, 1);
lean_inc(v_a_360_);
lean_dec_ref_known(v___x_348_, 2);
v___x_361_ = lean_array_get_size(v_a_360_);
v___x_362_ = lean_nat_dec_lt(v___x_346_, v___x_361_);
if (v___x_362_ == 0)
{
lean_object* v___x_363_; lean_object* v___x_364_; 
lean_dec(v_a_360_);
lean_dec(v_rev_x3f_231_);
lean_dec_ref(v_repo_229_);
lean_dec_ref(v_name_228_);
v___x_363_ = lean_box(0);
v___x_364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_364_, 0, v___x_363_);
return v___x_364_;
}
else
{
lean_object* v___x_365_; uint8_t v___x_366_; 
v___x_365_ = lean_box(0);
v___x_366_ = lean_nat_dec_le(v___x_361_, v___x_361_);
if (v___x_366_ == 0)
{
if (v___x_362_ == 0)
{
lean_dec(v_a_360_);
lean_dec(v_rev_x3f_231_);
lean_dec_ref(v_repo_229_);
lean_dec_ref(v_name_228_);
goto v___jp_337_;
}
else
{
size_t v___x_367_; size_t v___x_368_; lean_object* v___x_369_; 
v___x_367_ = ((size_t)0ULL);
v___x_368_ = lean_usize_of_nat(v___x_361_);
v___x_369_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_360_, v___x_367_, v___x_368_, v___x_365_, v_a_232_);
lean_dec(v_a_360_);
if (lean_obj_tag(v___x_369_) == 0)
{
lean_dec_ref_known(v___x_369_, 1);
lean_dec(v_rev_x3f_231_);
lean_dec_ref(v_repo_229_);
lean_dec_ref(v_name_228_);
goto v___jp_337_;
}
else
{
v___y_336_ = v___x_369_;
goto v___jp_335_;
}
}
}
else
{
size_t v___x_370_; size_t v___x_371_; lean_object* v___x_372_; 
v___x_370_ = ((size_t)0ULL);
v___x_371_ = lean_usize_of_nat(v___x_361_);
v___x_372_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_360_, v___x_370_, v___x_371_, v___x_365_, v_a_232_);
lean_dec(v_a_360_);
if (lean_obj_tag(v___x_372_) == 0)
{
lean_dec_ref_known(v___x_372_, 1);
lean_dec(v_rev_x3f_231_);
lean_dec_ref(v_repo_229_);
lean_dec_ref(v_name_228_);
goto v___jp_337_;
}
else
{
v___y_336_ = v___x_372_;
goto v___jp_335_;
}
}
}
}
v___jp_234_:
{
lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_235_ = lean_box(0);
v___x_236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
return v___x_236_;
}
v___jp_237_:
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; uint8_t v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_239_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3));
v___x_240_ = lean_string_append(v_name_228_, v___x_239_);
v___x_241_ = lean_string_append(v___x_240_, v_a_238_);
v___x_242_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
v___x_243_ = lean_string_append(v___x_241_, v___x_242_);
v___x_244_ = 1;
v___x_245_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_245_, 0, v___x_243_);
lean_ctor_set_uint8(v___x_245_, sizeof(void*)*1, v___x_244_);
lean_inc_ref(v_a_232_);
v___x_246_ = lean_apply_2(v_a_232_, v___x_245_, lean_box(0));
v___x_247_ = lean_unsigned_to_nat(0u);
v___x_248_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_249_ = l_Lake_GitRepo_checkoutDetach(v_a_238_, v_repo_229_, v___x_248_);
if (lean_obj_tag(v___x_249_) == 0)
{
lean_object* v_a_250_; lean_object* v_a_251_; lean_object* v___x_252_; uint8_t v___x_253_; 
v_a_250_ = lean_ctor_get(v___x_249_, 0);
lean_inc(v_a_250_);
v_a_251_ = lean_ctor_get(v___x_249_, 1);
lean_inc(v_a_251_);
lean_dec_ref_known(v___x_249_, 2);
v___x_252_ = lean_array_get_size(v_a_251_);
v___x_253_ = lean_nat_dec_lt(v___x_247_, v___x_252_);
if (v___x_253_ == 0)
{
lean_object* v___x_254_; 
lean_dec(v_a_251_);
v___x_254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_254_, 0, v_a_250_);
return v___x_254_;
}
else
{
lean_object* v___x_255_; uint8_t v___x_256_; 
v___x_255_ = lean_box(0);
v___x_256_ = lean_nat_dec_le(v___x_252_, v___x_252_);
if (v___x_256_ == 0)
{
if (v___x_253_ == 0)
{
lean_object* v___x_257_; 
lean_dec(v_a_251_);
v___x_257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_257_, 0, v_a_250_);
return v___x_257_;
}
else
{
size_t v___x_258_; size_t v___x_259_; lean_object* v___x_260_; 
v___x_258_ = ((size_t)0ULL);
v___x_259_ = lean_usize_of_nat(v___x_252_);
v___x_260_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_251_, v___x_258_, v___x_259_, v___x_255_, v_a_232_);
lean_dec(v_a_251_);
if (lean_obj_tag(v___x_260_) == 0)
{
lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_267_; 
v_isSharedCheck_267_ = !lean_is_exclusive(v___x_260_);
if (v_isSharedCheck_267_ == 0)
{
lean_object* v_unused_268_; 
v_unused_268_ = lean_ctor_get(v___x_260_, 0);
lean_dec(v_unused_268_);
v___x_262_ = v___x_260_;
v_isShared_263_ = v_isSharedCheck_267_;
goto v_resetjp_261_;
}
else
{
lean_dec(v___x_260_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_267_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___x_265_; 
if (v_isShared_263_ == 0)
{
lean_ctor_set(v___x_262_, 0, v_a_250_);
v___x_265_ = v___x_262_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v_a_250_);
v___x_265_ = v_reuseFailAlloc_266_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
return v___x_265_;
}
}
}
else
{
lean_dec(v_a_250_);
return v___x_260_;
}
}
}
else
{
size_t v___x_269_; size_t v___x_270_; lean_object* v___x_271_; 
v___x_269_ = ((size_t)0ULL);
v___x_270_ = lean_usize_of_nat(v___x_252_);
v___x_271_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_251_, v___x_269_, v___x_270_, v___x_255_, v_a_232_);
lean_dec(v_a_251_);
if (lean_obj_tag(v___x_271_) == 0)
{
lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_278_; 
v_isSharedCheck_278_ = !lean_is_exclusive(v___x_271_);
if (v_isSharedCheck_278_ == 0)
{
lean_object* v_unused_279_; 
v_unused_279_ = lean_ctor_get(v___x_271_, 0);
lean_dec(v_unused_279_);
v___x_273_ = v___x_271_;
v_isShared_274_ = v_isSharedCheck_278_;
goto v_resetjp_272_;
}
else
{
lean_dec(v___x_271_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_278_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v___x_276_; 
if (v_isShared_274_ == 0)
{
lean_ctor_set(v___x_273_, 0, v_a_250_);
v___x_276_ = v___x_273_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v_a_250_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
}
else
{
lean_dec(v_a_250_);
return v___x_271_;
}
}
}
}
else
{
lean_object* v_a_280_; lean_object* v___x_281_; uint8_t v___x_282_; 
v_a_280_ = lean_ctor_get(v___x_249_, 1);
lean_inc(v_a_280_);
lean_dec_ref_known(v___x_249_, 2);
v___x_281_ = lean_array_get_size(v_a_280_);
v___x_282_ = lean_nat_dec_lt(v___x_247_, v___x_281_);
if (v___x_282_ == 0)
{
lean_object* v___x_283_; lean_object* v___x_284_; 
lean_dec(v_a_280_);
v___x_283_ = lean_box(0);
v___x_284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_284_, 0, v___x_283_);
return v___x_284_;
}
else
{
lean_object* v___x_285_; uint8_t v___x_286_; 
v___x_285_ = lean_box(0);
v___x_286_ = lean_nat_dec_le(v___x_281_, v___x_281_);
if (v___x_286_ == 0)
{
if (v___x_282_ == 0)
{
lean_dec(v_a_280_);
goto v___jp_234_;
}
else
{
size_t v___x_287_; size_t v___x_288_; lean_object* v___x_289_; 
v___x_287_ = ((size_t)0ULL);
v___x_288_ = lean_usize_of_nat(v___x_281_);
v___x_289_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_280_, v___x_287_, v___x_288_, v___x_285_, v_a_232_);
lean_dec(v_a_280_);
if (lean_obj_tag(v___x_289_) == 0)
{
lean_dec_ref_known(v___x_289_, 1);
goto v___jp_234_;
}
else
{
return v___x_289_;
}
}
}
else
{
size_t v___x_290_; size_t v___x_291_; lean_object* v___x_292_; 
v___x_290_ = ((size_t)0ULL);
v___x_291_ = lean_usize_of_nat(v___x_281_);
v___x_292_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_280_, v___x_290_, v___x_291_, v___x_285_, v_a_232_);
lean_dec(v_a_280_);
if (lean_obj_tag(v___x_292_) == 0)
{
lean_dec_ref_known(v___x_292_, 1);
goto v___jp_234_;
}
else
{
return v___x_292_;
}
}
}
}
}
v___jp_293_:
{
lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_294_ = lean_box(0);
v___x_295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
return v___x_295_;
}
v___jp_296_:
{
if (lean_obj_tag(v_rev_x3f_231_) == 1)
{
lean_object* v_val_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_332_; 
v_val_297_ = lean_ctor_get(v_rev_x3f_231_, 0);
v_isSharedCheck_332_ = !lean_is_exclusive(v_rev_x3f_231_);
if (v_isSharedCheck_332_ == 0)
{
v___x_299_ = v_rev_x3f_231_;
v_isShared_300_ = v_isSharedCheck_332_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_val_297_);
lean_dec(v_rev_x3f_231_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_332_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_301_ = l_Lake_Git_defaultRemote;
v___x_302_ = lean_unsigned_to_nat(0u);
v___x_303_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
lean_inc_ref(v_repo_229_);
v___x_304_ = l_Lake_GitRepo_resolveRemoteRevision(v_val_297_, v___x_301_, v_repo_229_, v___x_303_);
if (lean_obj_tag(v___x_304_) == 0)
{
lean_object* v_a_305_; lean_object* v_a_306_; lean_object* v___x_307_; uint8_t v___x_308_; 
lean_del_object(v___x_299_);
v_a_305_ = lean_ctor_get(v___x_304_, 0);
lean_inc(v_a_305_);
v_a_306_ = lean_ctor_get(v___x_304_, 1);
lean_inc(v_a_306_);
lean_dec_ref_known(v___x_304_, 2);
v___x_307_ = lean_array_get_size(v_a_306_);
v___x_308_ = lean_nat_dec_lt(v___x_302_, v___x_307_);
if (v___x_308_ == 0)
{
lean_dec(v_a_306_);
v_a_238_ = v_a_305_;
goto v___jp_237_;
}
else
{
lean_object* v___x_309_; uint8_t v___x_310_; 
v___x_309_ = lean_box(0);
v___x_310_ = lean_nat_dec_le(v___x_307_, v___x_307_);
if (v___x_310_ == 0)
{
if (v___x_308_ == 0)
{
lean_dec(v_a_306_);
v_a_238_ = v_a_305_;
goto v___jp_237_;
}
else
{
size_t v___x_311_; size_t v___x_312_; lean_object* v___x_313_; 
v___x_311_ = ((size_t)0ULL);
v___x_312_ = lean_usize_of_nat(v___x_307_);
v___x_313_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_306_, v___x_311_, v___x_312_, v___x_309_, v_a_232_);
lean_dec(v_a_306_);
if (lean_obj_tag(v___x_313_) == 0)
{
lean_dec_ref_known(v___x_313_, 1);
v_a_238_ = v_a_305_;
goto v___jp_237_;
}
else
{
lean_dec(v_a_305_);
lean_dec_ref(v_repo_229_);
lean_dec_ref(v_name_228_);
return v___x_313_;
}
}
}
else
{
size_t v___x_314_; size_t v___x_315_; lean_object* v___x_316_; 
v___x_314_ = ((size_t)0ULL);
v___x_315_ = lean_usize_of_nat(v___x_307_);
v___x_316_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_306_, v___x_314_, v___x_315_, v___x_309_, v_a_232_);
lean_dec(v_a_306_);
if (lean_obj_tag(v___x_316_) == 0)
{
lean_dec_ref_known(v___x_316_, 1);
v_a_238_ = v_a_305_;
goto v___jp_237_;
}
else
{
lean_dec(v_a_305_);
lean_dec_ref(v_repo_229_);
lean_dec_ref(v_name_228_);
return v___x_316_;
}
}
}
}
else
{
lean_object* v_a_317_; lean_object* v___x_318_; uint8_t v___x_319_; 
lean_dec_ref(v_repo_229_);
lean_dec_ref(v_name_228_);
v_a_317_ = lean_ctor_get(v___x_304_, 1);
lean_inc(v_a_317_);
lean_dec_ref_known(v___x_304_, 2);
v___x_318_ = lean_array_get_size(v_a_317_);
v___x_319_ = lean_nat_dec_lt(v___x_302_, v___x_318_);
if (v___x_319_ == 0)
{
lean_object* v___x_320_; lean_object* v___x_322_; 
lean_dec(v_a_317_);
v___x_320_ = lean_box(0);
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 0, v___x_320_);
v___x_322_ = v___x_299_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v___x_320_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
else
{
lean_object* v___x_324_; uint8_t v___x_325_; 
lean_del_object(v___x_299_);
v___x_324_ = lean_box(0);
v___x_325_ = lean_nat_dec_le(v___x_318_, v___x_318_);
if (v___x_325_ == 0)
{
if (v___x_319_ == 0)
{
lean_dec(v_a_317_);
goto v___jp_293_;
}
else
{
size_t v___x_326_; size_t v___x_327_; lean_object* v___x_328_; 
v___x_326_ = ((size_t)0ULL);
v___x_327_ = lean_usize_of_nat(v___x_318_);
v___x_328_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_317_, v___x_326_, v___x_327_, v___x_324_, v_a_232_);
lean_dec(v_a_317_);
if (lean_obj_tag(v___x_328_) == 0)
{
lean_dec_ref_known(v___x_328_, 1);
goto v___jp_293_;
}
else
{
return v___x_328_;
}
}
}
else
{
size_t v___x_329_; size_t v___x_330_; lean_object* v___x_331_; 
v___x_329_ = ((size_t)0ULL);
v___x_330_ = lean_usize_of_nat(v___x_318_);
v___x_331_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_317_, v___x_329_, v___x_330_, v___x_324_, v_a_232_);
lean_dec(v_a_317_);
if (lean_obj_tag(v___x_331_) == 0)
{
lean_dec_ref_known(v___x_331_, 1);
goto v___jp_293_;
}
else
{
return v___x_331_;
}
}
}
}
}
}
else
{
lean_object* v___x_333_; lean_object* v___x_334_; 
lean_dec(v_rev_x3f_231_);
lean_dec_ref(v_repo_229_);
lean_dec_ref(v_name_228_);
v___x_333_ = lean_box(0);
v___x_334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
return v___x_334_;
}
}
v___jp_335_:
{
if (lean_obj_tag(v___y_336_) == 0)
{
lean_dec_ref_known(v___y_336_, 1);
goto v___jp_296_;
}
else
{
lean_dec(v_rev_x3f_231_);
lean_dec_ref(v_repo_229_);
lean_dec_ref(v_name_228_);
return v___y_336_;
}
}
v___jp_337_:
{
lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_338_ = lean_box(0);
v___x_339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
return v___x_339_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___boxed(lean_object* v_name_373_, lean_object* v_repo_374_, lean_object* v_url_375_, lean_object* v_rev_x3f_376_, lean_object* v_a_377_, lean_object* v_a_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg(v_name_373_, v_repo_374_, v_url_375_, v_rev_x3f_376_, v_a_377_);
lean_dec_ref(v_a_377_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(lean_object* v_a_380_, lean_object* v_name_381_, lean_object* v_repo_382_, lean_object* v_url_383_, lean_object* v_rev_x3f_384_){
_start:
{
lean_object* v_a_390_; lean_object* v___y_488_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; uint8_t v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_492_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___closed__0));
lean_inc_ref(v_name_381_);
v___x_493_ = lean_string_append(v_name_381_, v___x_492_);
v___x_494_ = lean_string_append(v___x_493_, v_url_383_);
v___x_495_ = 1;
v___x_496_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_496_, 0, v___x_494_);
lean_ctor_set_uint8(v___x_496_, sizeof(void*)*1, v___x_495_);
lean_inc_ref(v_a_380_);
v___x_497_ = lean_apply_2(v_a_380_, v___x_496_, lean_box(0));
v___x_498_ = lean_unsigned_to_nat(0u);
v___x_499_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
lean_inc_ref(v_repo_382_);
v___x_500_ = l_Lake_GitRepo_clone(v_url_383_, v_repo_382_, v___x_499_);
if (lean_obj_tag(v___x_500_) == 0)
{
lean_object* v_a_501_; lean_object* v___x_502_; uint8_t v___x_503_; 
v_a_501_ = lean_ctor_get(v___x_500_, 1);
lean_inc(v_a_501_);
lean_dec_ref_known(v___x_500_, 2);
v___x_502_ = lean_array_get_size(v_a_501_);
v___x_503_ = lean_nat_dec_lt(v___x_498_, v___x_502_);
if (v___x_503_ == 0)
{
lean_dec(v_a_501_);
goto v___jp_448_;
}
else
{
lean_object* v___x_504_; uint8_t v___x_505_; 
v___x_504_ = lean_box(0);
v___x_505_ = lean_nat_dec_le(v___x_502_, v___x_502_);
if (v___x_505_ == 0)
{
if (v___x_503_ == 0)
{
lean_dec(v_a_501_);
goto v___jp_448_;
}
else
{
size_t v___x_506_; size_t v___x_507_; lean_object* v___x_508_; 
v___x_506_ = ((size_t)0ULL);
v___x_507_ = lean_usize_of_nat(v___x_502_);
v___x_508_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_501_, v___x_506_, v___x_507_, v___x_504_, v_a_380_);
lean_dec(v_a_501_);
if (lean_obj_tag(v___x_508_) == 0)
{
lean_dec_ref_known(v___x_508_, 1);
goto v___jp_448_;
}
else
{
v___y_488_ = v___x_508_;
goto v___jp_487_;
}
}
}
else
{
size_t v___x_509_; size_t v___x_510_; lean_object* v___x_511_; 
v___x_509_ = ((size_t)0ULL);
v___x_510_ = lean_usize_of_nat(v___x_502_);
v___x_511_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_501_, v___x_509_, v___x_510_, v___x_504_, v_a_380_);
lean_dec(v_a_501_);
if (lean_obj_tag(v___x_511_) == 0)
{
lean_dec_ref_known(v___x_511_, 1);
goto v___jp_448_;
}
else
{
v___y_488_ = v___x_511_;
goto v___jp_487_;
}
}
}
}
else
{
lean_object* v_a_512_; lean_object* v___x_513_; uint8_t v___x_514_; 
v_a_512_ = lean_ctor_get(v___x_500_, 1);
lean_inc(v_a_512_);
lean_dec_ref_known(v___x_500_, 2);
v___x_513_ = lean_array_get_size(v_a_512_);
v___x_514_ = lean_nat_dec_lt(v___x_498_, v___x_513_);
if (v___x_514_ == 0)
{
lean_object* v___x_515_; lean_object* v___x_516_; 
lean_dec(v_a_512_);
lean_dec(v_rev_x3f_384_);
lean_dec_ref(v_repo_382_);
lean_dec_ref(v_name_381_);
v___x_515_ = lean_box(0);
v___x_516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_516_, 0, v___x_515_);
return v___x_516_;
}
else
{
lean_object* v___x_517_; uint8_t v___x_518_; 
v___x_517_ = lean_box(0);
v___x_518_ = lean_nat_dec_le(v___x_513_, v___x_513_);
if (v___x_518_ == 0)
{
if (v___x_514_ == 0)
{
lean_dec(v_a_512_);
lean_dec(v_rev_x3f_384_);
lean_dec_ref(v_repo_382_);
lean_dec_ref(v_name_381_);
goto v___jp_489_;
}
else
{
size_t v___x_519_; size_t v___x_520_; lean_object* v___x_521_; 
v___x_519_ = ((size_t)0ULL);
v___x_520_ = lean_usize_of_nat(v___x_513_);
v___x_521_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_512_, v___x_519_, v___x_520_, v___x_517_, v_a_380_);
lean_dec(v_a_512_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_dec_ref_known(v___x_521_, 1);
lean_dec(v_rev_x3f_384_);
lean_dec_ref(v_repo_382_);
lean_dec_ref(v_name_381_);
goto v___jp_489_;
}
else
{
v___y_488_ = v___x_521_;
goto v___jp_487_;
}
}
}
else
{
size_t v___x_522_; size_t v___x_523_; lean_object* v___x_524_; 
v___x_522_ = ((size_t)0ULL);
v___x_523_ = lean_usize_of_nat(v___x_513_);
v___x_524_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_512_, v___x_522_, v___x_523_, v___x_517_, v_a_380_);
lean_dec(v_a_512_);
if (lean_obj_tag(v___x_524_) == 0)
{
lean_dec_ref_known(v___x_524_, 1);
lean_dec(v_rev_x3f_384_);
lean_dec_ref(v_repo_382_);
lean_dec_ref(v_name_381_);
goto v___jp_489_;
}
else
{
v___y_488_ = v___x_524_;
goto v___jp_487_;
}
}
}
}
v___jp_386_:
{
lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_387_ = lean_box(0);
v___x_388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_388_, 0, v___x_387_);
return v___x_388_;
}
v___jp_389_:
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; uint8_t v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_391_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3));
v___x_392_ = lean_string_append(v_name_381_, v___x_391_);
v___x_393_ = lean_string_append(v___x_392_, v_a_390_);
v___x_394_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
v___x_395_ = lean_string_append(v___x_393_, v___x_394_);
v___x_396_ = 1;
v___x_397_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_397_, 0, v___x_395_);
lean_ctor_set_uint8(v___x_397_, sizeof(void*)*1, v___x_396_);
lean_inc_ref(v_a_380_);
v___x_398_ = lean_apply_2(v_a_380_, v___x_397_, lean_box(0));
v___x_399_ = lean_unsigned_to_nat(0u);
v___x_400_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_401_ = l_Lake_GitRepo_checkoutDetach(v_a_390_, v_repo_382_, v___x_400_);
if (lean_obj_tag(v___x_401_) == 0)
{
lean_object* v_a_402_; lean_object* v_a_403_; lean_object* v___x_404_; uint8_t v___x_405_; 
v_a_402_ = lean_ctor_get(v___x_401_, 0);
lean_inc(v_a_402_);
v_a_403_ = lean_ctor_get(v___x_401_, 1);
lean_inc(v_a_403_);
lean_dec_ref_known(v___x_401_, 2);
v___x_404_ = lean_array_get_size(v_a_403_);
v___x_405_ = lean_nat_dec_lt(v___x_399_, v___x_404_);
if (v___x_405_ == 0)
{
lean_object* v___x_406_; 
lean_dec(v_a_403_);
v___x_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_406_, 0, v_a_402_);
return v___x_406_;
}
else
{
lean_object* v___x_407_; uint8_t v___x_408_; 
v___x_407_ = lean_box(0);
v___x_408_ = lean_nat_dec_le(v___x_404_, v___x_404_);
if (v___x_408_ == 0)
{
if (v___x_405_ == 0)
{
lean_object* v___x_409_; 
lean_dec(v_a_403_);
v___x_409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_409_, 0, v_a_402_);
return v___x_409_;
}
else
{
size_t v___x_410_; size_t v___x_411_; lean_object* v___x_412_; 
v___x_410_ = ((size_t)0ULL);
v___x_411_ = lean_usize_of_nat(v___x_404_);
v___x_412_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_403_, v___x_410_, v___x_411_, v___x_407_, v_a_380_);
lean_dec(v_a_403_);
if (lean_obj_tag(v___x_412_) == 0)
{
lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_419_; 
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_412_);
if (v_isSharedCheck_419_ == 0)
{
lean_object* v_unused_420_; 
v_unused_420_ = lean_ctor_get(v___x_412_, 0);
lean_dec(v_unused_420_);
v___x_414_ = v___x_412_;
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
else
{
lean_dec(v___x_412_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_417_; 
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 0, v_a_402_);
v___x_417_ = v___x_414_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_a_402_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
else
{
lean_dec(v_a_402_);
return v___x_412_;
}
}
}
else
{
size_t v___x_421_; size_t v___x_422_; lean_object* v___x_423_; 
v___x_421_ = ((size_t)0ULL);
v___x_422_ = lean_usize_of_nat(v___x_404_);
v___x_423_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_403_, v___x_421_, v___x_422_, v___x_407_, v_a_380_);
lean_dec(v_a_403_);
if (lean_obj_tag(v___x_423_) == 0)
{
lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_430_; 
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_423_);
if (v_isSharedCheck_430_ == 0)
{
lean_object* v_unused_431_; 
v_unused_431_ = lean_ctor_get(v___x_423_, 0);
lean_dec(v_unused_431_);
v___x_425_ = v___x_423_;
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
else
{
lean_dec(v___x_423_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_428_; 
if (v_isShared_426_ == 0)
{
lean_ctor_set(v___x_425_, 0, v_a_402_);
v___x_428_ = v___x_425_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_a_402_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
else
{
lean_dec(v_a_402_);
return v___x_423_;
}
}
}
}
else
{
lean_object* v_a_432_; lean_object* v___x_433_; uint8_t v___x_434_; 
v_a_432_ = lean_ctor_get(v___x_401_, 1);
lean_inc(v_a_432_);
lean_dec_ref_known(v___x_401_, 2);
v___x_433_ = lean_array_get_size(v_a_432_);
v___x_434_ = lean_nat_dec_lt(v___x_399_, v___x_433_);
if (v___x_434_ == 0)
{
lean_object* v___x_435_; lean_object* v___x_436_; 
lean_dec(v_a_432_);
v___x_435_ = lean_box(0);
v___x_436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_436_, 0, v___x_435_);
return v___x_436_;
}
else
{
lean_object* v___x_437_; uint8_t v___x_438_; 
v___x_437_ = lean_box(0);
v___x_438_ = lean_nat_dec_le(v___x_433_, v___x_433_);
if (v___x_438_ == 0)
{
if (v___x_434_ == 0)
{
lean_dec(v_a_432_);
goto v___jp_386_;
}
else
{
size_t v___x_439_; size_t v___x_440_; lean_object* v___x_441_; 
v___x_439_ = ((size_t)0ULL);
v___x_440_ = lean_usize_of_nat(v___x_433_);
v___x_441_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_432_, v___x_439_, v___x_440_, v___x_437_, v_a_380_);
lean_dec(v_a_432_);
if (lean_obj_tag(v___x_441_) == 0)
{
lean_dec_ref_known(v___x_441_, 1);
goto v___jp_386_;
}
else
{
return v___x_441_;
}
}
}
else
{
size_t v___x_442_; size_t v___x_443_; lean_object* v___x_444_; 
v___x_442_ = ((size_t)0ULL);
v___x_443_ = lean_usize_of_nat(v___x_433_);
v___x_444_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_432_, v___x_442_, v___x_443_, v___x_437_, v_a_380_);
lean_dec(v_a_432_);
if (lean_obj_tag(v___x_444_) == 0)
{
lean_dec_ref_known(v___x_444_, 1);
goto v___jp_386_;
}
else
{
return v___x_444_;
}
}
}
}
}
v___jp_445_:
{
lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_446_ = lean_box(0);
v___x_447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_447_, 0, v___x_446_);
return v___x_447_;
}
v___jp_448_:
{
if (lean_obj_tag(v_rev_x3f_384_) == 1)
{
lean_object* v_val_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_484_; 
v_val_449_ = lean_ctor_get(v_rev_x3f_384_, 0);
v_isSharedCheck_484_ = !lean_is_exclusive(v_rev_x3f_384_);
if (v_isSharedCheck_484_ == 0)
{
v___x_451_ = v_rev_x3f_384_;
v_isShared_452_ = v_isSharedCheck_484_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_val_449_);
lean_dec(v_rev_x3f_384_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_484_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_453_ = l_Lake_Git_defaultRemote;
v___x_454_ = lean_unsigned_to_nat(0u);
v___x_455_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
lean_inc_ref(v_repo_382_);
v___x_456_ = l_Lake_GitRepo_resolveRemoteRevision(v_val_449_, v___x_453_, v_repo_382_, v___x_455_);
if (lean_obj_tag(v___x_456_) == 0)
{
lean_object* v_a_457_; lean_object* v_a_458_; lean_object* v___x_459_; uint8_t v___x_460_; 
lean_del_object(v___x_451_);
v_a_457_ = lean_ctor_get(v___x_456_, 0);
lean_inc(v_a_457_);
v_a_458_ = lean_ctor_get(v___x_456_, 1);
lean_inc(v_a_458_);
lean_dec_ref_known(v___x_456_, 2);
v___x_459_ = lean_array_get_size(v_a_458_);
v___x_460_ = lean_nat_dec_lt(v___x_454_, v___x_459_);
if (v___x_460_ == 0)
{
lean_dec(v_a_458_);
v_a_390_ = v_a_457_;
goto v___jp_389_;
}
else
{
lean_object* v___x_461_; uint8_t v___x_462_; 
v___x_461_ = lean_box(0);
v___x_462_ = lean_nat_dec_le(v___x_459_, v___x_459_);
if (v___x_462_ == 0)
{
if (v___x_460_ == 0)
{
lean_dec(v_a_458_);
v_a_390_ = v_a_457_;
goto v___jp_389_;
}
else
{
size_t v___x_463_; size_t v___x_464_; lean_object* v___x_465_; 
v___x_463_ = ((size_t)0ULL);
v___x_464_ = lean_usize_of_nat(v___x_459_);
v___x_465_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_458_, v___x_463_, v___x_464_, v___x_461_, v_a_380_);
lean_dec(v_a_458_);
if (lean_obj_tag(v___x_465_) == 0)
{
lean_dec_ref_known(v___x_465_, 1);
v_a_390_ = v_a_457_;
goto v___jp_389_;
}
else
{
lean_dec(v_a_457_);
lean_dec_ref(v_repo_382_);
lean_dec_ref(v_name_381_);
return v___x_465_;
}
}
}
else
{
size_t v___x_466_; size_t v___x_467_; lean_object* v___x_468_; 
v___x_466_ = ((size_t)0ULL);
v___x_467_ = lean_usize_of_nat(v___x_459_);
v___x_468_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_458_, v___x_466_, v___x_467_, v___x_461_, v_a_380_);
lean_dec(v_a_458_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_dec_ref_known(v___x_468_, 1);
v_a_390_ = v_a_457_;
goto v___jp_389_;
}
else
{
lean_dec(v_a_457_);
lean_dec_ref(v_repo_382_);
lean_dec_ref(v_name_381_);
return v___x_468_;
}
}
}
}
else
{
lean_object* v_a_469_; lean_object* v___x_470_; uint8_t v___x_471_; 
lean_dec_ref(v_repo_382_);
lean_dec_ref(v_name_381_);
v_a_469_ = lean_ctor_get(v___x_456_, 1);
lean_inc(v_a_469_);
lean_dec_ref_known(v___x_456_, 2);
v___x_470_ = lean_array_get_size(v_a_469_);
v___x_471_ = lean_nat_dec_lt(v___x_454_, v___x_470_);
if (v___x_471_ == 0)
{
lean_object* v___x_472_; lean_object* v___x_474_; 
lean_dec(v_a_469_);
v___x_472_ = lean_box(0);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 0, v___x_472_);
v___x_474_ = v___x_451_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v___x_472_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
else
{
lean_object* v___x_476_; uint8_t v___x_477_; 
lean_del_object(v___x_451_);
v___x_476_ = lean_box(0);
v___x_477_ = lean_nat_dec_le(v___x_470_, v___x_470_);
if (v___x_477_ == 0)
{
if (v___x_471_ == 0)
{
lean_dec(v_a_469_);
goto v___jp_445_;
}
else
{
size_t v___x_478_; size_t v___x_479_; lean_object* v___x_480_; 
v___x_478_ = ((size_t)0ULL);
v___x_479_ = lean_usize_of_nat(v___x_470_);
v___x_480_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_469_, v___x_478_, v___x_479_, v___x_476_, v_a_380_);
lean_dec(v_a_469_);
if (lean_obj_tag(v___x_480_) == 0)
{
lean_dec_ref_known(v___x_480_, 1);
goto v___jp_445_;
}
else
{
return v___x_480_;
}
}
}
else
{
size_t v___x_481_; size_t v___x_482_; lean_object* v___x_483_; 
v___x_481_ = ((size_t)0ULL);
v___x_482_ = lean_usize_of_nat(v___x_470_);
v___x_483_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_469_, v___x_481_, v___x_482_, v___x_476_, v_a_380_);
lean_dec(v_a_469_);
if (lean_obj_tag(v___x_483_) == 0)
{
lean_dec_ref_known(v___x_483_, 1);
goto v___jp_445_;
}
else
{
return v___x_483_;
}
}
}
}
}
}
else
{
lean_object* v___x_485_; lean_object* v___x_486_; 
lean_dec(v_rev_x3f_384_);
lean_dec_ref(v_repo_382_);
lean_dec_ref(v_name_381_);
v___x_485_ = lean_box(0);
v___x_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
return v___x_486_;
}
}
v___jp_487_:
{
if (lean_obj_tag(v___y_488_) == 0)
{
lean_dec_ref_known(v___y_488_, 1);
goto v___jp_448_;
}
else
{
lean_dec(v_rev_x3f_384_);
lean_dec_ref(v_repo_382_);
lean_dec_ref(v_name_381_);
return v___y_488_;
}
}
v___jp_489_:
{
lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_490_ = lean_box(0);
v___x_491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_491_, 0, v___x_490_);
return v___x_491_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0___boxed(lean_object* v_a_525_, lean_object* v_name_526_, lean_object* v_repo_527_, lean_object* v_url_528_, lean_object* v_rev_x3f_529_, lean_object* v_a_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(v_a_525_, v_name_526_, v_repo_527_, v_url_528_, v_rev_x3f_529_);
lean_dec_ref(v_a_525_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(lean_object* v_a_532_, lean_object* v_name_533_, lean_object* v_repo_534_, lean_object* v_rev_x3f_535_){
_start:
{
uint8_t v_a_538_; lean_object* v___y_551_; lean_object* v___y_552_; uint8_t v_val_553_; lean_object* v___y_618_; lean_object* v___y_620_; lean_object* v_a_621_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_668_ = l_Lake_Git_defaultRemote;
v___x_669_ = lean_unsigned_to_nat(0u);
v___x_670_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
lean_inc_ref(v_repo_534_);
v___x_671_ = l_Lake_GitRepo_findRemoteRevision(v_repo_534_, v_rev_x3f_535_, v___x_668_, v___x_670_);
if (lean_obj_tag(v___x_671_) == 0)
{
lean_object* v_a_672_; lean_object* v_a_673_; lean_object* v___x_701_; uint8_t v___x_702_; 
v_a_672_ = lean_ctor_get(v___x_671_, 0);
lean_inc(v_a_672_);
v_a_673_ = lean_ctor_get(v___x_671_, 1);
lean_inc(v_a_673_);
lean_dec_ref_known(v___x_671_, 2);
v___x_701_ = lean_array_get_size(v_a_673_);
v___x_702_ = lean_nat_dec_lt(v___x_669_, v___x_701_);
if (v___x_702_ == 0)
{
lean_dec(v_a_673_);
goto v___jp_674_;
}
else
{
lean_object* v___x_703_; uint8_t v___x_704_; 
v___x_703_ = lean_box(0);
v___x_704_ = lean_nat_dec_le(v___x_701_, v___x_701_);
if (v___x_704_ == 0)
{
if (v___x_702_ == 0)
{
lean_dec(v_a_673_);
goto v___jp_674_;
}
else
{
size_t v___x_705_; size_t v___x_706_; lean_object* v___x_707_; 
v___x_705_ = ((size_t)0ULL);
v___x_706_ = lean_usize_of_nat(v___x_701_);
v___x_707_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_673_, v___x_705_, v___x_706_, v___x_703_, v_a_532_);
lean_dec(v_a_673_);
if (lean_obj_tag(v___x_707_) == 0)
{
lean_dec_ref_known(v___x_707_, 1);
goto v___jp_674_;
}
else
{
lean_dec(v_a_672_);
lean_dec_ref(v_repo_534_);
lean_dec_ref(v_name_533_);
return v___x_707_;
}
}
}
else
{
size_t v___x_708_; size_t v___x_709_; lean_object* v___x_710_; 
v___x_708_ = ((size_t)0ULL);
v___x_709_ = lean_usize_of_nat(v___x_701_);
v___x_710_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_673_, v___x_708_, v___x_709_, v___x_703_, v_a_532_);
lean_dec(v_a_673_);
if (lean_obj_tag(v___x_710_) == 0)
{
lean_dec_ref_known(v___x_710_, 1);
goto v___jp_674_;
}
else
{
lean_dec(v_a_672_);
lean_dec_ref(v_repo_534_);
lean_dec_ref(v_name_533_);
return v___x_710_;
}
}
}
v___jp_674_:
{
lean_object* v___x_675_; 
lean_inc_ref(v_repo_534_);
v___x_675_ = l_Lake_GitRepo_getHeadRevision(v_repo_534_, v___x_670_);
if (lean_obj_tag(v___x_675_) == 0)
{
lean_object* v_a_676_; lean_object* v_a_677_; lean_object* v___x_678_; uint8_t v___x_679_; 
v_a_676_ = lean_ctor_get(v___x_675_, 0);
lean_inc(v_a_676_);
v_a_677_ = lean_ctor_get(v___x_675_, 1);
lean_inc(v_a_677_);
lean_dec_ref_known(v___x_675_, 2);
v___x_678_ = lean_array_get_size(v_a_677_);
v___x_679_ = lean_nat_dec_lt(v___x_669_, v___x_678_);
if (v___x_679_ == 0)
{
lean_dec(v_a_677_);
v___y_620_ = v_a_672_;
v_a_621_ = v_a_676_;
goto v___jp_619_;
}
else
{
lean_object* v___x_680_; uint8_t v___x_681_; 
v___x_680_ = lean_box(0);
v___x_681_ = lean_nat_dec_le(v___x_678_, v___x_678_);
if (v___x_681_ == 0)
{
if (v___x_679_ == 0)
{
lean_dec(v_a_677_);
v___y_620_ = v_a_672_;
v_a_621_ = v_a_676_;
goto v___jp_619_;
}
else
{
size_t v___x_682_; size_t v___x_683_; lean_object* v___x_684_; 
v___x_682_ = ((size_t)0ULL);
v___x_683_ = lean_usize_of_nat(v___x_678_);
v___x_684_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_677_, v___x_682_, v___x_683_, v___x_680_, v_a_532_);
lean_dec(v_a_677_);
if (lean_obj_tag(v___x_684_) == 0)
{
lean_dec_ref_known(v___x_684_, 1);
v___y_620_ = v_a_672_;
v_a_621_ = v_a_676_;
goto v___jp_619_;
}
else
{
lean_dec(v_a_676_);
lean_dec(v_a_672_);
lean_dec_ref(v_repo_534_);
lean_dec_ref(v_name_533_);
return v___x_684_;
}
}
}
else
{
size_t v___x_685_; size_t v___x_686_; lean_object* v___x_687_; 
v___x_685_ = ((size_t)0ULL);
v___x_686_ = lean_usize_of_nat(v___x_678_);
v___x_687_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_677_, v___x_685_, v___x_686_, v___x_680_, v_a_532_);
lean_dec(v_a_677_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_dec_ref_known(v___x_687_, 1);
v___y_620_ = v_a_672_;
v_a_621_ = v_a_676_;
goto v___jp_619_;
}
else
{
lean_dec(v_a_676_);
lean_dec(v_a_672_);
lean_dec_ref(v_repo_534_);
lean_dec_ref(v_name_533_);
return v___x_687_;
}
}
}
}
else
{
lean_object* v_a_688_; lean_object* v___x_689_; uint8_t v___x_690_; 
lean_dec(v_a_672_);
lean_dec_ref(v_repo_534_);
lean_dec_ref(v_name_533_);
v_a_688_ = lean_ctor_get(v___x_675_, 1);
lean_inc(v_a_688_);
lean_dec_ref_known(v___x_675_, 2);
v___x_689_ = lean_array_get_size(v_a_688_);
v___x_690_ = lean_nat_dec_lt(v___x_669_, v___x_689_);
if (v___x_690_ == 0)
{
lean_object* v___x_691_; lean_object* v___x_692_; 
lean_dec(v_a_688_);
v___x_691_ = lean_box(0);
v___x_692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_692_, 0, v___x_691_);
return v___x_692_;
}
else
{
lean_object* v___x_693_; uint8_t v___x_694_; 
v___x_693_ = lean_box(0);
v___x_694_ = lean_nat_dec_le(v___x_689_, v___x_689_);
if (v___x_694_ == 0)
{
if (v___x_690_ == 0)
{
lean_dec(v_a_688_);
goto v___jp_662_;
}
else
{
size_t v___x_695_; size_t v___x_696_; lean_object* v___x_697_; 
v___x_695_ = ((size_t)0ULL);
v___x_696_ = lean_usize_of_nat(v___x_689_);
v___x_697_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_688_, v___x_695_, v___x_696_, v___x_693_, v_a_532_);
lean_dec(v_a_688_);
if (lean_obj_tag(v___x_697_) == 0)
{
lean_dec_ref_known(v___x_697_, 1);
goto v___jp_662_;
}
else
{
return v___x_697_;
}
}
}
else
{
size_t v___x_698_; size_t v___x_699_; lean_object* v___x_700_; 
v___x_698_ = ((size_t)0ULL);
v___x_699_ = lean_usize_of_nat(v___x_689_);
v___x_700_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_688_, v___x_698_, v___x_699_, v___x_693_, v_a_532_);
lean_dec(v_a_688_);
if (lean_obj_tag(v___x_700_) == 0)
{
lean_dec_ref_known(v___x_700_, 1);
goto v___jp_662_;
}
else
{
return v___x_700_;
}
}
}
}
}
}
else
{
lean_object* v_a_711_; lean_object* v___x_712_; uint8_t v___x_713_; 
lean_dec_ref(v_repo_534_);
lean_dec_ref(v_name_533_);
v_a_711_ = lean_ctor_get(v___x_671_, 1);
lean_inc(v_a_711_);
lean_dec_ref_known(v___x_671_, 2);
v___x_712_ = lean_array_get_size(v_a_711_);
v___x_713_ = lean_nat_dec_lt(v___x_669_, v___x_712_);
if (v___x_713_ == 0)
{
lean_object* v___x_714_; lean_object* v___x_715_; 
lean_dec(v_a_711_);
v___x_714_ = lean_box(0);
v___x_715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_715_, 0, v___x_714_);
return v___x_715_;
}
else
{
lean_object* v___x_716_; uint8_t v___x_717_; 
v___x_716_ = lean_box(0);
v___x_717_ = lean_nat_dec_le(v___x_712_, v___x_712_);
if (v___x_717_ == 0)
{
if (v___x_713_ == 0)
{
lean_dec(v_a_711_);
goto v___jp_665_;
}
else
{
size_t v___x_718_; size_t v___x_719_; lean_object* v___x_720_; 
v___x_718_ = ((size_t)0ULL);
v___x_719_ = lean_usize_of_nat(v___x_712_);
v___x_720_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_711_, v___x_718_, v___x_719_, v___x_716_, v_a_532_);
lean_dec(v_a_711_);
if (lean_obj_tag(v___x_720_) == 0)
{
lean_dec_ref_known(v___x_720_, 1);
goto v___jp_665_;
}
else
{
return v___x_720_;
}
}
}
else
{
size_t v___x_721_; size_t v___x_722_; lean_object* v___x_723_; 
v___x_721_ = ((size_t)0ULL);
v___x_722_ = lean_usize_of_nat(v___x_712_);
v___x_723_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_711_, v___x_721_, v___x_722_, v___x_716_, v_a_532_);
lean_dec(v_a_711_);
if (lean_obj_tag(v___x_723_) == 0)
{
lean_dec_ref_known(v___x_723_, 1);
goto v___jp_665_;
}
else
{
return v___x_723_;
}
}
}
}
v___jp_537_:
{
if (v_a_538_ == 0)
{
lean_object* v___x_539_; lean_object* v___x_540_; 
lean_dec_ref(v_repo_534_);
lean_dec_ref(v_name_533_);
v___x_539_ = lean_box(0);
v___x_540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_540_, 0, v___x_539_);
return v___x_540_;
}
else
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; uint8_t v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_541_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0));
v___x_542_ = lean_string_append(v_name_533_, v___x_541_);
v___x_543_ = lean_string_append(v___x_542_, v_repo_534_);
lean_dec_ref(v_repo_534_);
v___x_544_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1));
v___x_545_ = lean_string_append(v___x_543_, v___x_544_);
v___x_546_ = 2;
v___x_547_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_547_, 0, v___x_545_);
lean_ctor_set_uint8(v___x_547_, sizeof(void*)*1, v___x_546_);
lean_inc_ref(v_a_532_);
v___x_548_ = lean_apply_2(v_a_532_, v___x_547_, lean_box(0));
v___x_549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_549_, 0, v___x_548_);
return v___x_549_;
}
}
v___jp_550_:
{
lean_object* v___x_554_; uint8_t v___x_555_; 
v___x_554_ = lean_array_get_size(v___y_552_);
v___x_555_ = lean_nat_dec_lt(v___y_551_, v___x_554_);
if (v___x_555_ == 0)
{
v_a_538_ = v_val_553_;
goto v___jp_537_;
}
else
{
lean_object* v___x_556_; uint8_t v___x_557_; 
v___x_556_ = lean_box(0);
v___x_557_ = lean_nat_dec_le(v___x_554_, v___x_554_);
if (v___x_557_ == 0)
{
if (v___x_555_ == 0)
{
v_a_538_ = v_val_553_;
goto v___jp_537_;
}
else
{
size_t v___x_558_; size_t v___x_559_; lean_object* v___x_560_; 
v___x_558_ = ((size_t)0ULL);
v___x_559_ = lean_usize_of_nat(v___x_554_);
v___x_560_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_552_, v___x_558_, v___x_559_, v___x_556_, v_a_532_);
if (lean_obj_tag(v___x_560_) == 0)
{
lean_dec_ref_known(v___x_560_, 1);
v_a_538_ = v_val_553_;
goto v___jp_537_;
}
else
{
lean_dec_ref(v_repo_534_);
lean_dec_ref(v_name_533_);
return v___x_560_;
}
}
}
else
{
size_t v___x_561_; size_t v___x_562_; lean_object* v___x_563_; 
v___x_561_ = ((size_t)0ULL);
v___x_562_ = lean_usize_of_nat(v___x_554_);
v___x_563_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_552_, v___x_561_, v___x_562_, v___x_556_, v_a_532_);
if (lean_obj_tag(v___x_563_) == 0)
{
lean_dec_ref_known(v___x_563_, 1);
v_a_538_ = v_val_553_;
goto v___jp_537_;
}
else
{
lean_dec_ref(v_repo_534_);
lean_dec_ref(v_name_533_);
return v___x_563_;
}
}
}
}
v___jp_564_:
{
lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_565_ = lean_box(0);
v___x_566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_566_, 0, v___x_565_);
return v___x_566_;
}
v___jp_567_:
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = lean_box(0);
v___x_569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_569_, 0, v___x_568_);
return v___x_569_;
}
v___jp_570_:
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_571_ = lean_unsigned_to_nat(0u);
v___x_572_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_573_ = l_Lake_GitRepo_clean(v_repo_534_, v___x_572_);
if (lean_obj_tag(v___x_573_) == 0)
{
lean_object* v_a_574_; lean_object* v_a_575_; lean_object* v___x_576_; uint8_t v___x_577_; 
v_a_574_ = lean_ctor_get(v___x_573_, 0);
lean_inc(v_a_574_);
v_a_575_ = lean_ctor_get(v___x_573_, 1);
lean_inc(v_a_575_);
lean_dec_ref_known(v___x_573_, 2);
v___x_576_ = lean_array_get_size(v_a_575_);
v___x_577_ = lean_nat_dec_lt(v___x_571_, v___x_576_);
if (v___x_577_ == 0)
{
lean_object* v___x_578_; 
lean_dec(v_a_575_);
v___x_578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_578_, 0, v_a_574_);
return v___x_578_;
}
else
{
lean_object* v___x_579_; uint8_t v___x_580_; 
v___x_579_ = lean_box(0);
v___x_580_ = lean_nat_dec_le(v___x_576_, v___x_576_);
if (v___x_580_ == 0)
{
if (v___x_577_ == 0)
{
lean_object* v___x_581_; 
lean_dec(v_a_575_);
v___x_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_581_, 0, v_a_574_);
return v___x_581_;
}
else
{
size_t v___x_582_; size_t v___x_583_; lean_object* v___x_584_; 
v___x_582_ = ((size_t)0ULL);
v___x_583_ = lean_usize_of_nat(v___x_576_);
v___x_584_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_575_, v___x_582_, v___x_583_, v___x_579_, v_a_532_);
lean_dec(v_a_575_);
if (lean_obj_tag(v___x_584_) == 0)
{
lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_591_; 
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_591_ == 0)
{
lean_object* v_unused_592_; 
v_unused_592_ = lean_ctor_get(v___x_584_, 0);
lean_dec(v_unused_592_);
v___x_586_ = v___x_584_;
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
else
{
lean_dec(v___x_584_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_589_; 
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 0, v_a_574_);
v___x_589_ = v___x_586_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_a_574_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
}
else
{
lean_dec(v_a_574_);
return v___x_584_;
}
}
}
else
{
size_t v___x_593_; size_t v___x_594_; lean_object* v___x_595_; 
v___x_593_ = ((size_t)0ULL);
v___x_594_ = lean_usize_of_nat(v___x_576_);
v___x_595_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_575_, v___x_593_, v___x_594_, v___x_579_, v_a_532_);
lean_dec(v_a_575_);
if (lean_obj_tag(v___x_595_) == 0)
{
lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_602_; 
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_602_ == 0)
{
lean_object* v_unused_603_; 
v_unused_603_ = lean_ctor_get(v___x_595_, 0);
lean_dec(v_unused_603_);
v___x_597_ = v___x_595_;
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
else
{
lean_dec(v___x_595_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_600_; 
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 0, v_a_574_);
v___x_600_ = v___x_597_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_a_574_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
else
{
lean_dec(v_a_574_);
return v___x_595_;
}
}
}
}
else
{
lean_object* v_a_604_; lean_object* v___x_605_; uint8_t v___x_606_; 
v_a_604_ = lean_ctor_get(v___x_573_, 1);
lean_inc(v_a_604_);
lean_dec_ref_known(v___x_573_, 2);
v___x_605_ = lean_array_get_size(v_a_604_);
v___x_606_ = lean_nat_dec_lt(v___x_571_, v___x_605_);
if (v___x_606_ == 0)
{
lean_object* v___x_607_; lean_object* v___x_608_; 
lean_dec(v_a_604_);
v___x_607_ = lean_box(0);
v___x_608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_608_, 0, v___x_607_);
return v___x_608_;
}
else
{
lean_object* v___x_609_; uint8_t v___x_610_; 
v___x_609_ = lean_box(0);
v___x_610_ = lean_nat_dec_le(v___x_605_, v___x_605_);
if (v___x_610_ == 0)
{
if (v___x_606_ == 0)
{
lean_dec(v_a_604_);
goto v___jp_567_;
}
else
{
size_t v___x_611_; size_t v___x_612_; lean_object* v___x_613_; 
v___x_611_ = ((size_t)0ULL);
v___x_612_ = lean_usize_of_nat(v___x_605_);
v___x_613_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_604_, v___x_611_, v___x_612_, v___x_609_, v_a_532_);
lean_dec(v_a_604_);
if (lean_obj_tag(v___x_613_) == 0)
{
lean_dec_ref_known(v___x_613_, 1);
goto v___jp_567_;
}
else
{
return v___x_613_;
}
}
}
else
{
size_t v___x_614_; size_t v___x_615_; lean_object* v___x_616_; 
v___x_614_ = ((size_t)0ULL);
v___x_615_ = lean_usize_of_nat(v___x_605_);
v___x_616_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_604_, v___x_614_, v___x_615_, v___x_609_, v_a_532_);
lean_dec(v_a_604_);
if (lean_obj_tag(v___x_616_) == 0)
{
lean_dec_ref_known(v___x_616_, 1);
goto v___jp_567_;
}
else
{
return v___x_616_;
}
}
}
}
}
v___jp_617_:
{
if (lean_obj_tag(v___y_618_) == 0)
{
lean_dec_ref_known(v___y_618_, 1);
goto v___jp_570_;
}
else
{
lean_dec_ref(v_repo_534_);
return v___y_618_;
}
}
v___jp_619_:
{
uint8_t v___x_622_; 
v___x_622_ = lean_string_dec_eq(v_a_621_, v___y_620_);
lean_dec_ref(v_a_621_);
if (v___x_622_ == 0)
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; uint8_t v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_623_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3));
v___x_624_ = lean_string_append(v_name_533_, v___x_623_);
v___x_625_ = lean_string_append(v___x_624_, v___y_620_);
v___x_626_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
v___x_627_ = lean_string_append(v___x_625_, v___x_626_);
v___x_628_ = 1;
v___x_629_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_629_, 0, v___x_627_);
lean_ctor_set_uint8(v___x_629_, sizeof(void*)*1, v___x_628_);
lean_inc_ref(v_a_532_);
v___x_630_ = lean_apply_2(v_a_532_, v___x_629_, lean_box(0));
v___x_631_ = lean_unsigned_to_nat(0u);
v___x_632_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
lean_inc_ref(v_repo_534_);
v___x_633_ = l_Lake_GitRepo_checkoutDetach(v___y_620_, v_repo_534_, v___x_632_);
if (lean_obj_tag(v___x_633_) == 0)
{
lean_object* v_a_634_; lean_object* v___x_635_; uint8_t v___x_636_; 
v_a_634_ = lean_ctor_get(v___x_633_, 1);
lean_inc(v_a_634_);
lean_dec_ref_known(v___x_633_, 2);
v___x_635_ = lean_array_get_size(v_a_634_);
v___x_636_ = lean_nat_dec_lt(v___x_631_, v___x_635_);
if (v___x_636_ == 0)
{
lean_dec(v_a_634_);
goto v___jp_570_;
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
lean_dec(v_a_634_);
goto v___jp_570_;
}
else
{
size_t v___x_639_; size_t v___x_640_; lean_object* v___x_641_; 
v___x_639_ = ((size_t)0ULL);
v___x_640_ = lean_usize_of_nat(v___x_635_);
v___x_641_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_634_, v___x_639_, v___x_640_, v___x_637_, v_a_532_);
lean_dec(v_a_634_);
if (lean_obj_tag(v___x_641_) == 0)
{
lean_dec_ref_known(v___x_641_, 1);
goto v___jp_570_;
}
else
{
v___y_618_ = v___x_641_;
goto v___jp_617_;
}
}
}
else
{
size_t v___x_642_; size_t v___x_643_; lean_object* v___x_644_; 
v___x_642_ = ((size_t)0ULL);
v___x_643_ = lean_usize_of_nat(v___x_635_);
v___x_644_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_634_, v___x_642_, v___x_643_, v___x_637_, v_a_532_);
lean_dec(v_a_634_);
if (lean_obj_tag(v___x_644_) == 0)
{
lean_dec_ref_known(v___x_644_, 1);
goto v___jp_570_;
}
else
{
v___y_618_ = v___x_644_;
goto v___jp_617_;
}
}
}
}
else
{
lean_object* v_a_645_; lean_object* v___x_646_; uint8_t v___x_647_; 
v_a_645_ = lean_ctor_get(v___x_633_, 1);
lean_inc(v_a_645_);
lean_dec_ref_known(v___x_633_, 2);
v___x_646_ = lean_array_get_size(v_a_645_);
v___x_647_ = lean_nat_dec_lt(v___x_631_, v___x_646_);
if (v___x_647_ == 0)
{
lean_object* v___x_648_; lean_object* v___x_649_; 
lean_dec(v_a_645_);
lean_dec_ref(v_repo_534_);
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
lean_dec_ref(v_repo_534_);
goto v___jp_564_;
}
else
{
size_t v___x_652_; size_t v___x_653_; lean_object* v___x_654_; 
v___x_652_ = ((size_t)0ULL);
v___x_653_ = lean_usize_of_nat(v___x_646_);
v___x_654_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_645_, v___x_652_, v___x_653_, v___x_650_, v_a_532_);
lean_dec(v_a_645_);
if (lean_obj_tag(v___x_654_) == 0)
{
lean_dec_ref_known(v___x_654_, 1);
lean_dec_ref(v_repo_534_);
goto v___jp_564_;
}
else
{
v___y_618_ = v___x_654_;
goto v___jp_617_;
}
}
}
else
{
size_t v___x_655_; size_t v___x_656_; lean_object* v___x_657_; 
v___x_655_ = ((size_t)0ULL);
v___x_656_ = lean_usize_of_nat(v___x_646_);
v___x_657_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_645_, v___x_655_, v___x_656_, v___x_650_, v_a_532_);
lean_dec(v_a_645_);
if (lean_obj_tag(v___x_657_) == 0)
{
lean_dec_ref_known(v___x_657_, 1);
lean_dec_ref(v_repo_534_);
goto v___jp_564_;
}
else
{
v___y_618_ = v___x_657_;
goto v___jp_617_;
}
}
}
}
}
else
{
uint8_t v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
lean_dec_ref(v___y_620_);
lean_inc_ref(v_repo_534_);
v___x_658_ = l_Lake_GitRepo_hasNoDiff(v_repo_534_);
v___x_659_ = lean_unsigned_to_nat(0u);
v___x_660_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
if (v___x_658_ == 0)
{
v___y_551_ = v___x_659_;
v___y_552_ = v___x_660_;
v_val_553_ = v___x_622_;
goto v___jp_550_;
}
else
{
uint8_t v___x_661_; 
v___x_661_ = 0;
v___y_551_ = v___x_659_;
v___y_552_ = v___x_660_;
v_val_553_ = v___x_661_;
goto v___jp_550_;
}
}
}
v___jp_662_:
{
lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_663_ = lean_box(0);
v___x_664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_664_, 0, v___x_663_);
return v___x_664_;
}
v___jp_665_:
{
lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_666_ = lean_box(0);
v___x_667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_667_, 0, v___x_666_);
return v___x_667_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1___boxed(lean_object* v_a_724_, lean_object* v_name_725_, lean_object* v_repo_726_, lean_object* v_rev_x3f_727_, lean_object* v_a_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(v_a_724_, v_name_725_, v_repo_726_, v_rev_x3f_727_);
lean_dec_ref(v_a_724_);
return v_res_729_;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4(void){
_start:
{
lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_734_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_735_ = lean_array_get_size(v___x_734_);
return v___x_735_;
}
}
static uint8_t _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5(void){
_start:
{
lean_object* v___x_736_; lean_object* v___x_737_; uint8_t v___x_738_; 
v___x_736_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4);
v___x_737_ = lean_unsigned_to_nat(0u);
v___x_738_ = lean_nat_dec_lt(v___x_737_, v___x_736_);
return v___x_738_;
}
}
static uint8_t _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6(void){
_start:
{
lean_object* v___x_739_; uint8_t v___x_740_; 
v___x_739_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4);
v___x_740_ = lean_nat_dec_le(v___x_739_, v___x_739_);
return v___x_740_;
}
}
static size_t _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7(void){
_start:
{
lean_object* v___x_741_; size_t v___x_742_; 
v___x_741_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4);
v___x_742_ = lean_usize_of_nat(v___x_741_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo(lean_object* v_name_743_, lean_object* v_repo_744_, lean_object* v_url_745_, lean_object* v_rev_x3f_746_, lean_object* v_a_747_){
_start:
{
uint8_t v_a_750_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; uint8_t v_val_789_; 
v___x_785_ = l_Lake_Git_defaultRemote;
lean_inc_ref(v_repo_744_);
v___x_786_ = l_Lake_GitRepo_getRemoteUrl_x3f(v___x_785_, v_repo_744_);
v___x_787_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
if (lean_obj_tag(v___x_786_) == 1)
{
lean_object* v_val_799_; uint8_t v___x_800_; 
v_val_799_ = lean_ctor_get(v___x_786_, 0);
lean_inc(v_val_799_);
lean_dec_ref_known(v___x_786_, 1);
v___x_800_ = lean_string_dec_eq(v_val_799_, v_url_745_);
if (v___x_800_ == 0)
{
lean_object* v___x_801_; 
v___x_801_ = lean_io_realpath(v_val_799_);
if (lean_obj_tag(v___x_801_) == 0)
{
lean_object* v_a_802_; lean_object* v___x_803_; 
v_a_802_ = lean_ctor_get(v___x_801_, 0);
lean_inc(v_a_802_);
lean_dec_ref_known(v___x_801_, 1);
lean_inc_ref(v_url_745_);
v___x_803_ = lean_io_realpath(v_url_745_);
if (lean_obj_tag(v___x_803_) == 0)
{
lean_object* v_a_804_; uint8_t v___x_805_; 
v_a_804_ = lean_ctor_get(v___x_803_, 0);
lean_inc(v_a_804_);
lean_dec_ref_known(v___x_803_, 1);
v___x_805_ = lean_string_dec_eq(v_a_802_, v_a_804_);
lean_dec(v_a_804_);
lean_dec(v_a_802_);
v_val_789_ = v___x_805_;
goto v___jp_788_;
}
else
{
lean_dec_ref_known(v___x_803_, 1);
lean_dec(v_a_802_);
v_val_789_ = v___x_800_;
goto v___jp_788_;
}
}
else
{
lean_dec_ref_known(v___x_801_, 1);
v_val_789_ = v___x_800_;
goto v___jp_788_;
}
}
else
{
lean_dec(v_val_799_);
v_val_789_ = v___x_800_;
goto v___jp_788_;
}
}
else
{
uint8_t v___x_806_; 
lean_dec(v___x_786_);
v___x_806_ = 0;
v_val_789_ = v___x_806_;
goto v___jp_788_;
}
v___jp_749_:
{
if (v_a_750_ == 0)
{
uint8_t v___x_751_; 
v___x_751_ = l_System_Platform_isWindows;
if (v___x_751_ == 0)
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; uint8_t v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_752_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__0));
lean_inc_ref(v_name_743_);
v___x_753_ = lean_string_append(v_name_743_, v___x_752_);
v___x_754_ = lean_string_append(v___x_753_, v_repo_744_);
v___x_755_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__1));
v___x_756_ = lean_string_append(v___x_754_, v___x_755_);
v___x_757_ = 1;
v___x_758_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_758_, 0, v___x_756_);
lean_ctor_set_uint8(v___x_758_, sizeof(void*)*1, v___x_757_);
lean_inc_ref(v_a_747_);
v___x_759_ = lean_apply_2(v_a_747_, v___x_758_, lean_box(0));
v___x_760_ = l_IO_FS_removeDirAll(v_repo_744_);
if (lean_obj_tag(v___x_760_) == 0)
{
lean_object* v___x_761_; 
lean_dec_ref_known(v___x_760_, 1);
v___x_761_ = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(v_a_747_, v_name_743_, v_repo_744_, v_url_745_, v_rev_x3f_746_);
return v___x_761_;
}
else
{
lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_774_; 
lean_dec(v_rev_x3f_746_);
lean_dec_ref(v_url_745_);
lean_dec_ref(v_repo_744_);
lean_dec_ref(v_name_743_);
v_a_762_ = lean_ctor_get(v___x_760_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_760_);
if (v_isSharedCheck_774_ == 0)
{
v___x_764_ = v___x_760_;
v_isShared_765_ = v_isSharedCheck_774_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_dec(v___x_760_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_774_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_766_; uint8_t v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_772_; 
v___x_766_ = lean_io_error_to_string(v_a_762_);
v___x_767_ = 3;
v___x_768_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_768_, 0, v___x_766_);
lean_ctor_set_uint8(v___x_768_, sizeof(void*)*1, v___x_767_);
lean_inc_ref(v_a_747_);
v___x_769_ = lean_apply_2(v_a_747_, v___x_768_, lean_box(0));
v___x_770_ = lean_box(0);
if (v_isShared_765_ == 0)
{
lean_ctor_set(v___x_764_, 0, v___x_770_);
v___x_772_ = v___x_764_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v___x_770_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
}
}
else
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; uint8_t v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
lean_dec_ref(v_url_745_);
v___x_775_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__2));
lean_inc_ref(v_name_743_);
v___x_776_ = lean_string_append(v_name_743_, v___x_775_);
v___x_777_ = lean_string_append(v___x_776_, v_repo_744_);
v___x_778_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__3));
v___x_779_ = lean_string_append(v___x_777_, v___x_778_);
v___x_780_ = 1;
v___x_781_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_781_, 0, v___x_779_);
lean_ctor_set_uint8(v___x_781_, sizeof(void*)*1, v___x_780_);
lean_inc_ref(v_a_747_);
v___x_782_ = lean_apply_2(v_a_747_, v___x_781_, lean_box(0));
v___x_783_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(v_a_747_, v_name_743_, v_repo_744_, v_rev_x3f_746_);
return v___x_783_;
}
}
else
{
lean_object* v___x_784_; 
lean_dec_ref(v_url_745_);
v___x_784_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(v_a_747_, v_name_743_, v_repo_744_, v_rev_x3f_746_);
return v___x_784_;
}
}
v___jp_788_:
{
uint8_t v___x_790_; 
v___x_790_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_790_ == 0)
{
v_a_750_ = v_val_789_;
goto v___jp_749_;
}
else
{
lean_object* v___x_791_; uint8_t v___x_792_; 
v___x_791_ = lean_box(0);
v___x_792_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_792_ == 0)
{
if (v___x_790_ == 0)
{
v_a_750_ = v_val_789_;
goto v___jp_749_;
}
else
{
size_t v___x_793_; size_t v___x_794_; lean_object* v___x_795_; 
v___x_793_ = ((size_t)0ULL);
v___x_794_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_795_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_787_, v___x_793_, v___x_794_, v___x_791_, v_a_747_);
if (lean_obj_tag(v___x_795_) == 0)
{
lean_dec_ref_known(v___x_795_, 1);
v_a_750_ = v_val_789_;
goto v___jp_749_;
}
else
{
lean_dec(v_rev_x3f_746_);
lean_dec_ref(v_url_745_);
lean_dec_ref(v_repo_744_);
lean_dec_ref(v_name_743_);
return v___x_795_;
}
}
}
else
{
size_t v___x_796_; size_t v___x_797_; lean_object* v___x_798_; 
v___x_796_ = ((size_t)0ULL);
v___x_797_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_798_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_787_, v___x_796_, v___x_797_, v___x_791_, v_a_747_);
if (lean_obj_tag(v___x_798_) == 0)
{
lean_dec_ref_known(v___x_798_, 1);
v_a_750_ = v_val_789_;
goto v___jp_749_;
}
else
{
lean_dec(v_rev_x3f_746_);
lean_dec_ref(v_url_745_);
lean_dec_ref(v_repo_744_);
lean_dec_ref(v_name_743_);
return v___x_798_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___boxed(lean_object* v_name_807_, lean_object* v_repo_808_, lean_object* v_url_809_, lean_object* v_rev_x3f_810_, lean_object* v_a_811_, lean_object* v_a_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo(v_name_807_, v_repo_808_, v_url_809_, v_rev_x3f_810_, v_a_811_);
lean_dec_ref(v_a_811_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(lean_object* v_a_814_, lean_object* v_name_815_, lean_object* v_repo_816_, lean_object* v_url_817_, lean_object* v_rev_x3f_818_){
_start:
{
uint8_t v_a_821_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; uint8_t v_val_860_; 
v___x_856_ = l_Lake_Git_defaultRemote;
lean_inc_ref(v_repo_816_);
v___x_857_ = l_Lake_GitRepo_getRemoteUrl_x3f(v___x_856_, v_repo_816_);
v___x_858_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
if (lean_obj_tag(v___x_857_) == 1)
{
lean_object* v_val_870_; uint8_t v___x_871_; 
v_val_870_ = lean_ctor_get(v___x_857_, 0);
lean_inc(v_val_870_);
lean_dec_ref_known(v___x_857_, 1);
v___x_871_ = lean_string_dec_eq(v_val_870_, v_url_817_);
if (v___x_871_ == 0)
{
lean_object* v___x_872_; 
v___x_872_ = lean_io_realpath(v_val_870_);
if (lean_obj_tag(v___x_872_) == 0)
{
lean_object* v_a_873_; lean_object* v___x_874_; 
v_a_873_ = lean_ctor_get(v___x_872_, 0);
lean_inc(v_a_873_);
lean_dec_ref_known(v___x_872_, 1);
lean_inc_ref(v_url_817_);
v___x_874_ = lean_io_realpath(v_url_817_);
if (lean_obj_tag(v___x_874_) == 0)
{
lean_object* v_a_875_; uint8_t v___x_876_; 
v_a_875_ = lean_ctor_get(v___x_874_, 0);
lean_inc(v_a_875_);
lean_dec_ref_known(v___x_874_, 1);
v___x_876_ = lean_string_dec_eq(v_a_873_, v_a_875_);
lean_dec(v_a_875_);
lean_dec(v_a_873_);
v_val_860_ = v___x_876_;
goto v___jp_859_;
}
else
{
lean_dec_ref_known(v___x_874_, 1);
lean_dec(v_a_873_);
v_val_860_ = v___x_871_;
goto v___jp_859_;
}
}
else
{
lean_dec_ref_known(v___x_872_, 1);
v_val_860_ = v___x_871_;
goto v___jp_859_;
}
}
else
{
lean_dec(v_val_870_);
v_val_860_ = v___x_871_;
goto v___jp_859_;
}
}
else
{
uint8_t v___x_877_; 
lean_dec(v___x_857_);
v___x_877_ = 0;
v_val_860_ = v___x_877_;
goto v___jp_859_;
}
v___jp_820_:
{
if (v_a_821_ == 0)
{
uint8_t v___x_822_; 
v___x_822_ = l_System_Platform_isWindows;
if (v___x_822_ == 0)
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; uint8_t v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_823_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__0));
lean_inc_ref(v_name_815_);
v___x_824_ = lean_string_append(v_name_815_, v___x_823_);
v___x_825_ = lean_string_append(v___x_824_, v_repo_816_);
v___x_826_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__1));
v___x_827_ = lean_string_append(v___x_825_, v___x_826_);
v___x_828_ = 1;
v___x_829_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_829_, 0, v___x_827_);
lean_ctor_set_uint8(v___x_829_, sizeof(void*)*1, v___x_828_);
lean_inc_ref(v_a_814_);
v___x_830_ = lean_apply_2(v_a_814_, v___x_829_, lean_box(0));
v___x_831_ = l_IO_FS_removeDirAll(v_repo_816_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_object* v___x_832_; 
lean_dec_ref_known(v___x_831_, 1);
v___x_832_ = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(v_a_814_, v_name_815_, v_repo_816_, v_url_817_, v_rev_x3f_818_);
return v___x_832_;
}
else
{
lean_object* v_a_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_845_; 
lean_dec(v_rev_x3f_818_);
lean_dec_ref(v_url_817_);
lean_dec_ref(v_repo_816_);
lean_dec_ref(v_name_815_);
v_a_833_ = lean_ctor_get(v___x_831_, 0);
v_isSharedCheck_845_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_845_ == 0)
{
v___x_835_ = v___x_831_;
v_isShared_836_ = v_isSharedCheck_845_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_a_833_);
lean_dec(v___x_831_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_845_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_837_; uint8_t v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_843_; 
v___x_837_ = lean_io_error_to_string(v_a_833_);
v___x_838_ = 3;
v___x_839_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_839_, 0, v___x_837_);
lean_ctor_set_uint8(v___x_839_, sizeof(void*)*1, v___x_838_);
lean_inc_ref(v_a_814_);
v___x_840_ = lean_apply_2(v_a_814_, v___x_839_, lean_box(0));
v___x_841_ = lean_box(0);
if (v_isShared_836_ == 0)
{
lean_ctor_set(v___x_835_, 0, v___x_841_);
v___x_843_ = v___x_835_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v___x_841_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
}
}
else
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; uint8_t v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
lean_dec_ref(v_url_817_);
v___x_846_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__2));
lean_inc_ref(v_name_815_);
v___x_847_ = lean_string_append(v_name_815_, v___x_846_);
v___x_848_ = lean_string_append(v___x_847_, v_repo_816_);
v___x_849_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__3));
v___x_850_ = lean_string_append(v___x_848_, v___x_849_);
v___x_851_ = 1;
v___x_852_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_852_, 0, v___x_850_);
lean_ctor_set_uint8(v___x_852_, sizeof(void*)*1, v___x_851_);
lean_inc_ref(v_a_814_);
v___x_853_ = lean_apply_2(v_a_814_, v___x_852_, lean_box(0));
v___x_854_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(v_a_814_, v_name_815_, v_repo_816_, v_rev_x3f_818_);
return v___x_854_;
}
}
else
{
lean_object* v___x_855_; 
lean_dec_ref(v_url_817_);
v___x_855_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(v_a_814_, v_name_815_, v_repo_816_, v_rev_x3f_818_);
return v___x_855_;
}
}
v___jp_859_:
{
uint8_t v___x_861_; 
v___x_861_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_861_ == 0)
{
v_a_821_ = v_val_860_;
goto v___jp_820_;
}
else
{
lean_object* v___x_862_; uint8_t v___x_863_; 
v___x_862_ = lean_box(0);
v___x_863_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_863_ == 0)
{
if (v___x_861_ == 0)
{
v_a_821_ = v_val_860_;
goto v___jp_820_;
}
else
{
size_t v___x_864_; size_t v___x_865_; lean_object* v___x_866_; 
v___x_864_ = ((size_t)0ULL);
v___x_865_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_866_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_858_, v___x_864_, v___x_865_, v___x_862_, v_a_814_);
if (lean_obj_tag(v___x_866_) == 0)
{
lean_dec_ref_known(v___x_866_, 1);
v_a_821_ = v_val_860_;
goto v___jp_820_;
}
else
{
lean_dec(v_rev_x3f_818_);
lean_dec_ref(v_url_817_);
lean_dec_ref(v_repo_816_);
lean_dec_ref(v_name_815_);
return v___x_866_;
}
}
}
else
{
size_t v___x_867_; size_t v___x_868_; lean_object* v___x_869_; 
v___x_867_ = ((size_t)0ULL);
v___x_868_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_869_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_858_, v___x_867_, v___x_868_, v___x_862_, v_a_814_);
if (lean_obj_tag(v___x_869_) == 0)
{
lean_dec_ref_known(v___x_869_, 1);
v_a_821_ = v_val_860_;
goto v___jp_820_;
}
else
{
lean_dec(v_rev_x3f_818_);
lean_dec_ref(v_url_817_);
lean_dec_ref(v_repo_816_);
lean_dec_ref(v_name_815_);
return v___x_869_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0___boxed(lean_object* v_a_878_, lean_object* v_name_879_, lean_object* v_repo_880_, lean_object* v_url_881_, lean_object* v_rev_x3f_882_, lean_object* v_a_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_878_, v_name_879_, v_repo_880_, v_url_881_, v_rev_x3f_882_);
lean_dec_ref(v_a_878_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo(lean_object* v_name_885_, lean_object* v_repo_886_, lean_object* v_url_887_, lean_object* v_rev_x3f_888_, lean_object* v_a_889_){
_start:
{
uint8_t v___x_891_; lean_object* v___x_895_; uint8_t v___x_896_; 
v___x_891_ = l_System_FilePath_isDir(v_repo_886_);
v___x_895_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_896_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_896_ == 0)
{
goto v___jp_892_;
}
else
{
lean_object* v___x_897_; uint8_t v___x_898_; 
v___x_897_ = lean_box(0);
v___x_898_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_898_ == 0)
{
if (v___x_896_ == 0)
{
goto v___jp_892_;
}
else
{
size_t v___x_899_; size_t v___x_900_; lean_object* v___x_901_; 
v___x_899_ = ((size_t)0ULL);
v___x_900_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_901_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_895_, v___x_899_, v___x_900_, v___x_897_, v_a_889_);
if (lean_obj_tag(v___x_901_) == 0)
{
lean_dec_ref_known(v___x_901_, 1);
goto v___jp_892_;
}
else
{
lean_dec(v_rev_x3f_888_);
lean_dec_ref(v_url_887_);
lean_dec_ref(v_repo_886_);
lean_dec_ref(v_name_885_);
return v___x_901_;
}
}
}
else
{
size_t v___x_902_; size_t v___x_903_; lean_object* v___x_904_; 
v___x_902_ = ((size_t)0ULL);
v___x_903_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_904_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_895_, v___x_902_, v___x_903_, v___x_897_, v_a_889_);
if (lean_obj_tag(v___x_904_) == 0)
{
lean_dec_ref_known(v___x_904_, 1);
goto v___jp_892_;
}
else
{
lean_dec(v_rev_x3f_888_);
lean_dec_ref(v_url_887_);
lean_dec_ref(v_repo_886_);
lean_dec_ref(v_name_885_);
return v___x_904_;
}
}
}
v___jp_892_:
{
if (v___x_891_ == 0)
{
lean_object* v___x_893_; 
v___x_893_ = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(v_a_889_, v_name_885_, v_repo_886_, v_url_887_, v_rev_x3f_888_);
return v___x_893_;
}
else
{
lean_object* v___x_894_; 
v___x_894_ = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_889_, v_name_885_, v_repo_886_, v_url_887_, v_rev_x3f_888_);
return v___x_894_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___boxed(lean_object* v_name_905_, lean_object* v_repo_906_, lean_object* v_url_907_, lean_object* v_rev_x3f_908_, lean_object* v_a_909_, lean_object* v_a_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo(v_name_905_, v_repo_906_, v_url_907_, v_rev_x3f_908_, v_a_909_);
lean_dec_ref(v_a_909_);
return v_res_911_;
}
}
static lean_object* _init_l_Lake_instInhabitedMaterializedDep_default___closed__4(void){
_start:
{
lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_918_ = l_Lake_instInhabitedPackageEntry_default;
v___x_919_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__3));
v___x_920_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___x_921_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_921_, 0, v___x_920_);
lean_ctor_set(v___x_921_, 1, v___x_920_);
lean_ctor_set(v___x_921_, 2, v___x_920_);
lean_ctor_set(v___x_921_, 3, v___x_919_);
lean_ctor_set(v___x_921_, 4, v___x_918_);
return v___x_921_;
}
}
static lean_object* _init_l_Lake_instInhabitedMaterializedDep_default(void){
_start:
{
lean_object* v___x_922_; 
v___x_922_ = lean_obj_once(&l_Lake_instInhabitedMaterializedDep_default___closed__4, &l_Lake_instInhabitedMaterializedDep_default___closed__4_once, _init_l_Lake_instInhabitedMaterializedDep_default___closed__4);
return v___x_922_;
}
}
static lean_object* _init_l_Lake_instInhabitedMaterializedDep(void){
_start:
{
lean_object* v___x_923_; 
v___x_923_ = l_Lake_instInhabitedMaterializedDep_default;
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_name(lean_object* v_self_924_){
_start:
{
lean_object* v_manifestEntry_925_; lean_object* v_name_926_; 
v_manifestEntry_925_ = lean_ctor_get(v_self_924_, 4);
v_name_926_ = lean_ctor_get(v_manifestEntry_925_, 0);
lean_inc(v_name_926_);
return v_name_926_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_name___boxed(lean_object* v_self_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l_Lake_MaterializedDep_name(v_self_927_);
lean_dec_ref(v_self_927_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_prettyName(lean_object* v_self_929_){
_start:
{
lean_object* v_manifestEntry_930_; lean_object* v_name_931_; uint8_t v___x_932_; lean_object* v___x_933_; 
v_manifestEntry_930_ = lean_ctor_get(v_self_929_, 4);
lean_inc_ref(v_manifestEntry_930_);
lean_dec_ref(v_self_929_);
v_name_931_ = lean_ctor_get(v_manifestEntry_930_, 0);
lean_inc(v_name_931_);
lean_dec_ref(v_manifestEntry_930_);
v___x_932_ = 0;
v___x_933_ = l_Lean_Name_toString(v_name_931_, v___x_932_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_scope(lean_object* v_self_934_){
_start:
{
lean_object* v_manifestEntry_935_; lean_object* v_scope_936_; 
v_manifestEntry_935_ = lean_ctor_get(v_self_934_, 4);
v_scope_936_ = lean_ctor_get(v_manifestEntry_935_, 1);
lean_inc_ref(v_scope_936_);
return v_scope_936_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_scope___boxed(lean_object* v_self_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_Lake_MaterializedDep_scope(v_self_937_);
lean_dec_ref(v_self_937_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relManifestFile_x3f(lean_object* v_self_939_){
_start:
{
lean_object* v_manifestEntry_940_; lean_object* v_manifestFile_x3f_941_; 
v_manifestEntry_940_ = lean_ctor_get(v_self_939_, 4);
v_manifestFile_x3f_941_ = lean_ctor_get(v_manifestEntry_940_, 3);
lean_inc(v_manifestFile_x3f_941_);
return v_manifestFile_x3f_941_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relManifestFile_x3f___boxed(lean_object* v_self_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l_Lake_MaterializedDep_relManifestFile_x3f(v_self_942_);
lean_dec_ref(v_self_942_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relManifestFile(lean_object* v_self_944_){
_start:
{
lean_object* v_manifestEntry_945_; lean_object* v_manifestFile_x3f_946_; 
v_manifestEntry_945_ = lean_ctor_get(v_self_944_, 4);
v_manifestFile_x3f_946_ = lean_ctor_get(v_manifestEntry_945_, 3);
if (lean_obj_tag(v_manifestFile_x3f_946_) == 0)
{
lean_object* v___x_947_; 
v___x_947_ = l_Lake_defaultManifestFile;
return v___x_947_;
}
else
{
lean_object* v_val_948_; 
v_val_948_ = lean_ctor_get(v_manifestFile_x3f_946_, 0);
lean_inc(v_val_948_);
return v_val_948_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relManifestFile___boxed(lean_object* v_self_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l_Lake_MaterializedDep_relManifestFile(v_self_949_);
lean_dec_ref(v_self_949_);
return v_res_950_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_manifestFile(lean_object* v_self_951_){
_start:
{
lean_object* v_manifestEntry_952_; lean_object* v_manifestFile_x3f_953_; 
v_manifestEntry_952_ = lean_ctor_get(v_self_951_, 4);
v_manifestFile_x3f_953_ = lean_ctor_get(v_manifestEntry_952_, 3);
if (lean_obj_tag(v_manifestFile_x3f_953_) == 0)
{
lean_object* v_pkgDir_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
v_pkgDir_954_ = lean_ctor_get(v_self_951_, 0);
lean_inc_ref(v_pkgDir_954_);
lean_dec_ref(v_self_951_);
v___x_955_ = l_Lake_defaultManifestFile;
v___x_956_ = l_Lake_joinRelative(v_pkgDir_954_, v___x_955_);
return v___x_956_;
}
else
{
lean_object* v_pkgDir_957_; lean_object* v_val_958_; lean_object* v___x_959_; 
lean_inc_ref(v_manifestFile_x3f_953_);
v_pkgDir_957_ = lean_ctor_get(v_self_951_, 0);
lean_inc_ref(v_pkgDir_957_);
lean_dec_ref(v_self_951_);
v_val_958_ = lean_ctor_get(v_manifestFile_x3f_953_, 0);
lean_inc(v_val_958_);
lean_dec_ref_known(v_manifestFile_x3f_953_, 1);
v___x_959_ = l_Lake_joinRelative(v_pkgDir_957_, v_val_958_);
return v___x_959_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relConfigFile(lean_object* v_self_960_){
_start:
{
lean_object* v_manifestEntry_961_; lean_object* v_configFile_962_; 
v_manifestEntry_961_ = lean_ctor_get(v_self_960_, 4);
v_configFile_962_ = lean_ctor_get(v_manifestEntry_961_, 2);
lean_inc_ref(v_configFile_962_);
return v_configFile_962_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relConfigFile___boxed(lean_object* v_self_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Lake_MaterializedDep_relConfigFile(v_self_963_);
lean_dec_ref(v_self_963_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_configFile(lean_object* v_self_965_){
_start:
{
lean_object* v_manifestEntry_966_; lean_object* v_pkgDir_967_; lean_object* v_configFile_968_; lean_object* v___x_969_; 
v_manifestEntry_966_ = lean_ctor_get(v_self_965_, 4);
lean_inc_ref(v_manifestEntry_966_);
v_pkgDir_967_ = lean_ctor_get(v_self_965_, 0);
lean_inc_ref(v_pkgDir_967_);
lean_dec_ref(v_self_965_);
v_configFile_968_ = lean_ctor_get(v_manifestEntry_966_, 2);
lean_inc_ref(v_configFile_968_);
lean_dec_ref(v_manifestEntry_966_);
v___x_969_ = l_Lake_joinRelative(v_pkgDir_967_, v_configFile_968_);
return v___x_969_;
}
}
LEAN_EXPORT uint8_t l_Lake_MaterializedDep_fixedToolchain(lean_object* v_self_970_){
_start:
{
lean_object* v_manifest_x3f_971_; 
v_manifest_x3f_971_ = lean_ctor_get(v_self_970_, 3);
if (lean_obj_tag(v_manifest_x3f_971_) == 1)
{
lean_object* v_a_972_; uint8_t v_fixedToolchain_973_; 
v_a_972_ = lean_ctor_get(v_manifest_x3f_971_, 0);
v_fixedToolchain_973_ = lean_ctor_get_uint8(v_a_972_, sizeof(void*)*4);
return v_fixedToolchain_973_;
}
else
{
uint8_t v___x_974_; 
v___x_974_ = 0;
return v___x_974_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_fixedToolchain___boxed(lean_object* v_self_975_){
_start:
{
uint8_t v_res_976_; lean_object* v_r_977_; 
v_res_976_ = l_Lake_MaterializedDep_fixedToolchain(v_self_975_);
lean_dec_ref(v_self_975_);
v_r_977_ = lean_box(v_res_976_);
return v_r_977_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed(lean_object* v_dep_986_){
_start:
{
lean_object* v_name_987_; lean_object* v_scope_988_; lean_object* v_version_989_; lean_object* v_fst_991_; lean_object* v_snd_992_; 
v_name_987_ = lean_ctor_get(v_dep_986_, 0);
lean_inc(v_name_987_);
v_scope_988_ = lean_ctor_get(v_dep_986_, 1);
lean_inc_ref(v_scope_988_);
v_version_989_ = lean_ctor_get(v_dep_986_, 2);
lean_inc(v_version_989_);
lean_dec_ref(v_dep_986_);
switch(lean_obj_tag(v_version_989_))
{
case 0:
{
lean_object* v___x_1015_; 
v___x_1015_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v_fst_991_ = v___x_1015_;
v_snd_992_ = v___x_1015_;
goto v___jp_990_;
}
case 1:
{
lean_object* v_rev_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1031_; 
v_rev_1016_ = lean_ctor_get(v_version_989_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v_version_989_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1018_ = v_version_989_;
v_isShared_1019_ = v_isSharedCheck_1031_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_rev_1016_);
lean_dec(v_version_989_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1031_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1023_; 
v___x_1020_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__5));
v___x_1021_ = l_String_quote(v_rev_1016_);
if (v_isShared_1019_ == 0)
{
lean_ctor_set_tag(v___x_1018_, 3);
lean_ctor_set(v___x_1018_, 0, v___x_1021_);
v___x_1023_ = v___x_1018_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v___x_1021_);
v___x_1023_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1024_ = l_Std_Format_defWidth;
v___x_1025_ = lean_unsigned_to_nat(0u);
v___x_1026_ = l_Std_Format_pretty(v___x_1023_, v___x_1024_, v___x_1025_, v___x_1025_);
v___x_1027_ = lean_string_append(v___x_1020_, v___x_1026_);
v___x_1028_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__6));
v___x_1029_ = lean_string_append(v___x_1028_, v___x_1026_);
lean_dec_ref(v___x_1026_);
v_fst_991_ = v___x_1027_;
v_snd_992_ = v___x_1029_;
goto v___jp_990_;
}
}
}
default: 
{
lean_object* v_ver_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1048_; 
v_ver_1032_ = lean_ctor_get(v_version_989_, 0);
v_isSharedCheck_1048_ = !lean_is_exclusive(v_version_989_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1034_ = v_version_989_;
v_isShared_1035_ = v_isSharedCheck_1048_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_ver_1032_);
lean_dec(v_version_989_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1048_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v_toString_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1040_; 
v_toString_1036_ = lean_ctor_get(v_ver_1032_, 0);
lean_inc_ref(v_toString_1036_);
lean_dec_ref(v_ver_1032_);
v___x_1037_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__5));
v___x_1038_ = l_String_quote(v_toString_1036_);
if (v_isShared_1035_ == 0)
{
lean_ctor_set_tag(v___x_1034_, 3);
lean_ctor_set(v___x_1034_, 0, v___x_1038_);
v___x_1040_ = v___x_1034_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v___x_1038_);
v___x_1040_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1041_ = l_Std_Format_defWidth;
v___x_1042_ = lean_unsigned_to_nat(0u);
v___x_1043_ = l_Std_Format_pretty(v___x_1040_, v___x_1041_, v___x_1042_, v___x_1042_);
v___x_1044_ = lean_string_append(v___x_1037_, v___x_1043_);
v___x_1045_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__7));
v___x_1046_ = lean_string_append(v___x_1045_, v___x_1043_);
lean_dec_ref(v___x_1043_);
v_fst_991_ = v___x_1044_;
v_snd_992_ = v___x_1046_;
goto v___jp_990_;
}
}
}
}
v___jp_990_:
{
lean_object* v___x_993_; lean_object* v___x_994_; uint8_t v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_993_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
lean_inc_ref(v_scope_988_);
v___x_994_ = lean_string_append(v_scope_988_, v___x_993_);
v___x_995_ = 0;
v___x_996_ = l_Lean_Name_toString(v_name_987_, v___x_995_);
v___x_997_ = lean_string_append(v___x_994_, v___x_996_);
v___x_998_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__1));
v___x_999_ = lean_string_append(v___x_997_, v___x_998_);
v___x_1000_ = lean_string_append(v___x_999_, v_scope_988_);
v___x_1001_ = lean_string_append(v___x_1000_, v___x_993_);
v___x_1002_ = lean_string_append(v___x_1001_, v___x_996_);
v___x_1003_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__2));
v___x_1004_ = lean_string_append(v___x_1002_, v___x_1003_);
v___x_1005_ = lean_string_append(v___x_1004_, v_fst_991_);
lean_dec_ref(v_fst_991_);
v___x_1006_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__3));
v___x_1007_ = lean_string_append(v___x_1005_, v___x_1006_);
v___x_1008_ = lean_string_append(v___x_1007_, v_scope_988_);
lean_dec_ref(v_scope_988_);
v___x_1009_ = lean_string_append(v___x_1008_, v___x_993_);
v___x_1010_ = lean_string_append(v___x_1009_, v___x_996_);
lean_dec_ref(v___x_996_);
v___x_1011_ = lean_string_append(v___x_1010_, v___x_1003_);
v___x_1012_ = lean_string_append(v___x_1011_, v_snd_992_);
lean_dec_ref(v_snd_992_);
v___x_1013_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__4));
v___x_1014_ = lean_string_append(v___x_1012_, v___x_1013_);
return v___x_1014_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___lam__0(lean_object* v_x_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_){
_start:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; 
lean_inc_ref(v___y_1051_);
v___x_1053_ = lean_apply_2(v___y_1051_, v___y_1050_, lean_box(0));
v___x_1054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1053_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___lam__0___boxed(lean_object* v_x_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___lam__0(v_x_1055_, v___y_1056_, v___y_1057_);
lean_dec_ref(v___y_1057_);
return v_res_1059_;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0(void){
_start:
{
lean_object* v___x_1060_; 
v___x_1060_ = l_instMonadEIO(lean_box(0));
return v___x_1060_;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1(void){
_start:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1061_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0, &l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0_once, _init_l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0);
v___x_1062_ = l_ReaderT_instMonad___redArg(v___x_1061_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep(lean_object* v_dep_1065_, uint8_t v_inherited_1066_, lean_object* v_wsDir_1067_, lean_object* v_name_1068_, lean_object* v_relPkgDir_1069_, lean_object* v_remoteUrl_1070_, lean_object* v_src_1071_, lean_object* v_a_1072_){
_start:
{
lean_object* v___y_1075_; lean_object* v_a_1076_; lean_object* v_pkgDir_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___f_1096_; lean_object* v___y_1098_; lean_object* v___y_1099_; lean_object* v___y_1100_; lean_object* v___y_1101_; lean_object* v_val_1102_; lean_object* v_a_1132_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v_val_1166_; lean_object* v___x_1194_; uint8_t v___x_1195_; 
lean_inc_ref(v_relPkgDir_1069_);
v_pkgDir_1093_ = l_Lake_joinRelative(v_wsDir_1067_, v_relPkgDir_1069_);
v___x_1094_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1, &l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1_once, _init_l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1);
lean_inc_ref(v_pkgDir_1093_);
v___x_1095_ = l_Lake_resolvePath(v_pkgDir_1093_);
v___f_1096_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__2));
v___x_1163_ = lean_unsigned_to_nat(0u);
v___x_1164_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_1194_ = lean_string_utf8_byte_size(v___x_1095_);
v___x_1195_ = lean_nat_dec_eq(v___x_1194_, v___x_1163_);
if (v___x_1195_ == 0)
{
lean_object* v___x_1196_; 
v___x_1196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1095_);
v_val_1166_ = v___x_1196_;
goto v___jp_1165_;
}
else
{
lean_object* v___x_1197_; 
lean_dec_ref(v___x_1095_);
v___x_1197_ = lean_box(0);
v_val_1166_ = v___x_1197_;
goto v___jp_1165_;
}
v___jp_1074_:
{
lean_object* v_name_1077_; lean_object* v_scope_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1089_; 
v_name_1077_ = lean_ctor_get(v_dep_1065_, 0);
v_scope_1078_ = lean_ctor_get(v_dep_1065_, 1);
v_isSharedCheck_1089_ = !lean_is_exclusive(v_dep_1065_);
if (v_isSharedCheck_1089_ == 0)
{
lean_object* v_unused_1090_; lean_object* v_unused_1091_; lean_object* v_unused_1092_; 
v_unused_1090_ = lean_ctor_get(v_dep_1065_, 4);
lean_dec(v_unused_1090_);
v_unused_1091_ = lean_ctor_get(v_dep_1065_, 3);
lean_dec(v_unused_1091_);
v_unused_1092_ = lean_ctor_get(v_dep_1065_, 2);
lean_dec(v_unused_1092_);
v___x_1080_ = v_dep_1065_;
v_isShared_1081_ = v_isSharedCheck_1089_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_scope_1078_);
lean_inc(v_name_1077_);
lean_dec(v_dep_1065_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1089_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1086_; 
v___x_1082_ = l_Lake_defaultConfigFile;
v___x_1083_ = lean_box(0);
v___x_1084_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1084_, 0, v_name_1077_);
lean_ctor_set(v___x_1084_, 1, v_scope_1078_);
lean_ctor_set(v___x_1084_, 2, v___x_1082_);
lean_ctor_set(v___x_1084_, 3, v___x_1083_);
lean_ctor_set(v___x_1084_, 4, v_src_1071_);
lean_ctor_set_uint8(v___x_1084_, sizeof(void*)*5, v_inherited_1066_);
if (v_isShared_1081_ == 0)
{
lean_ctor_set(v___x_1080_, 4, v___x_1084_);
lean_ctor_set(v___x_1080_, 3, v_a_1076_);
lean_ctor_set(v___x_1080_, 2, v_remoteUrl_1070_);
lean_ctor_set(v___x_1080_, 1, v_relPkgDir_1069_);
lean_ctor_set(v___x_1080_, 0, v___y_1075_);
v___x_1086_ = v___x_1080_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v___y_1075_);
lean_ctor_set(v_reuseFailAlloc_1088_, 1, v_relPkgDir_1069_);
lean_ctor_set(v_reuseFailAlloc_1088_, 2, v_remoteUrl_1070_);
lean_ctor_set(v_reuseFailAlloc_1088_, 3, v_a_1076_);
lean_ctor_set(v_reuseFailAlloc_1088_, 4, v___x_1084_);
v___x_1086_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
lean_object* v___x_1087_; 
v___x_1087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1086_);
return v___x_1087_;
}
}
}
v___jp_1097_:
{
lean_object* v___x_1103_; uint8_t v___x_1104_; 
v___x_1103_ = lean_array_get_size(v___y_1098_);
v___x_1104_ = lean_nat_dec_lt(v___y_1100_, v___x_1103_);
if (v___x_1104_ == 0)
{
lean_dec_ref(v___y_1099_);
v___y_1075_ = v___y_1101_;
v_a_1076_ = v_val_1102_;
goto v___jp_1074_;
}
else
{
lean_object* v___x_1105_; uint8_t v___x_1106_; 
v___x_1105_ = lean_box(0);
v___x_1106_ = lean_nat_dec_le(v___x_1103_, v___x_1103_);
if (v___x_1106_ == 0)
{
if (v___x_1104_ == 0)
{
lean_dec_ref(v___y_1099_);
v___y_1075_ = v___y_1101_;
v_a_1076_ = v_val_1102_;
goto v___jp_1074_;
}
else
{
size_t v___x_1107_; size_t v___x_1108_; lean_object* v___x_2388__overap_1109_; lean_object* v___x_1110_; 
v___x_1107_ = ((size_t)0ULL);
v___x_1108_ = lean_usize_of_nat(v___x_1103_);
lean_inc_ref(v___y_1098_);
v___x_2388__overap_1109_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___y_1099_, v___f_1096_, v___y_1098_, v___x_1107_, v___x_1108_, v___x_1105_);
lean_inc_ref(v_a_1072_);
v___x_1110_ = lean_apply_2(v___x_2388__overap_1109_, v_a_1072_, lean_box(0));
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_dec_ref_known(v___x_1110_, 1);
v___y_1075_ = v___y_1101_;
v_a_1076_ = v_val_1102_;
goto v___jp_1074_;
}
else
{
lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1118_; 
lean_dec_ref(v_val_1102_);
lean_dec_ref(v___y_1101_);
lean_dec_ref(v_src_1071_);
lean_dec_ref(v_remoteUrl_1070_);
lean_dec_ref(v_relPkgDir_1069_);
lean_dec_ref(v_dep_1065_);
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
else
{
size_t v___x_1119_; size_t v___x_1120_; lean_object* v___x_2398__overap_1121_; lean_object* v___x_1122_; 
v___x_1119_ = ((size_t)0ULL);
v___x_1120_ = lean_usize_of_nat(v___x_1103_);
lean_inc_ref(v___y_1098_);
v___x_2398__overap_1121_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___y_1099_, v___f_1096_, v___y_1098_, v___x_1119_, v___x_1120_, v___x_1105_);
lean_inc_ref(v_a_1072_);
v___x_1122_ = lean_apply_2(v___x_2398__overap_1121_, v_a_1072_, lean_box(0));
if (lean_obj_tag(v___x_1122_) == 0)
{
lean_dec_ref_known(v___x_1122_, 1);
v___y_1075_ = v___y_1101_;
v_a_1076_ = v_val_1102_;
goto v___jp_1074_;
}
else
{
lean_object* v_a_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1130_; 
lean_dec_ref(v_val_1102_);
lean_dec_ref(v___y_1101_);
lean_dec_ref(v_src_1071_);
lean_dec_ref(v_remoteUrl_1070_);
lean_dec_ref(v_relPkgDir_1069_);
lean_dec_ref(v_dep_1065_);
v_a_1123_ = lean_ctor_get(v___x_1122_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_1122_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1125_ = v___x_1122_;
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_a_1123_);
lean_dec(v___x_1122_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1128_; 
if (v_isShared_1126_ == 0)
{
v___x_1128_ = v___x_1125_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_a_1123_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
}
}
}
}
v___jp_1131_:
{
if (lean_obj_tag(v_a_1132_) == 1)
{
lean_object* v_val_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; 
lean_dec_ref(v_pkgDir_1093_);
lean_dec_ref(v_name_1068_);
v_val_1133_ = lean_ctor_get(v_a_1132_, 0);
lean_inc_n(v_val_1133_, 2);
lean_dec_ref_known(v_a_1132_, 1);
v___x_1134_ = l_Lake_defaultManifestFile;
v___x_1135_ = l_Lake_joinRelative(v_val_1133_, v___x_1134_);
v___x_1136_ = lean_unsigned_to_nat(0u);
v___x_1137_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_1138_ = l_Lake_Manifest_load(v___x_1135_);
if (lean_obj_tag(v___x_1138_) == 0)
{
lean_object* v_a_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1146_; 
v_a_1139_ = lean_ctor_get(v___x_1138_, 0);
v_isSharedCheck_1146_ = !lean_is_exclusive(v___x_1138_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1141_ = v___x_1138_;
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_a_1139_);
lean_dec(v___x_1138_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1144_; 
if (v_isShared_1142_ == 0)
{
lean_ctor_set_tag(v___x_1141_, 1);
v___x_1144_ = v___x_1141_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v_a_1139_);
v___x_1144_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
v___y_1098_ = v___x_1137_;
v___y_1099_ = v___x_1094_;
v___y_1100_ = v___x_1136_;
v___y_1101_ = v_val_1133_;
v_val_1102_ = v___x_1144_;
goto v___jp_1097_;
}
}
}
else
{
lean_object* v_a_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1154_; 
v_a_1147_ = lean_ctor_get(v___x_1138_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1138_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1149_ = v___x_1138_;
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_a_1147_);
lean_dec(v___x_1138_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1152_; 
if (v_isShared_1150_ == 0)
{
lean_ctor_set_tag(v___x_1149_, 0);
v___x_1152_ = v___x_1149_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_a_1147_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
v___y_1098_ = v___x_1137_;
v___y_1099_ = v___x_1094_;
v___y_1100_ = v___x_1136_;
v___y_1101_ = v_val_1133_;
v_val_1102_ = v___x_1152_;
goto v___jp_1097_;
}
}
}
}
else
{
lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; uint8_t v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
lean_dec(v_a_1132_);
lean_dec_ref(v_src_1071_);
lean_dec_ref(v_remoteUrl_1070_);
lean_dec_ref(v_relPkgDir_1069_);
lean_dec_ref(v_dep_1065_);
v___x_1155_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__3));
v___x_1156_ = lean_string_append(v_name_1068_, v___x_1155_);
v___x_1157_ = lean_string_append(v___x_1156_, v_pkgDir_1093_);
lean_dec_ref(v_pkgDir_1093_);
v___x_1158_ = 3;
v___x_1159_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1159_, 0, v___x_1157_);
lean_ctor_set_uint8(v___x_1159_, sizeof(void*)*1, v___x_1158_);
lean_inc_ref(v_a_1072_);
v___x_1160_ = lean_apply_2(v_a_1072_, v___x_1159_, lean_box(0));
v___x_1161_ = lean_box(0);
v___x_1162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1162_, 0, v___x_1161_);
return v___x_1162_;
}
}
v___jp_1165_:
{
uint8_t v___x_1167_; 
v___x_1167_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_1167_ == 0)
{
v_a_1132_ = v_val_1166_;
goto v___jp_1131_;
}
else
{
lean_object* v___x_1168_; uint8_t v___x_1169_; 
v___x_1168_ = lean_box(0);
v___x_1169_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_1169_ == 0)
{
if (v___x_1167_ == 0)
{
v_a_1132_ = v_val_1166_;
goto v___jp_1131_;
}
else
{
size_t v___x_1170_; size_t v___x_1171_; lean_object* v___x_2450__overap_1172_; lean_object* v___x_1173_; 
v___x_1170_ = ((size_t)0ULL);
v___x_1171_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_2450__overap_1172_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1094_, v___f_1096_, v___x_1164_, v___x_1170_, v___x_1171_, v___x_1168_);
lean_inc_ref(v_a_1072_);
v___x_1173_ = lean_apply_2(v___x_2450__overap_1172_, v_a_1072_, lean_box(0));
if (lean_obj_tag(v___x_1173_) == 0)
{
lean_dec_ref_known(v___x_1173_, 1);
v_a_1132_ = v_val_1166_;
goto v___jp_1131_;
}
else
{
lean_object* v_a_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1181_; 
lean_dec(v_val_1166_);
lean_dec_ref(v_pkgDir_1093_);
lean_dec_ref(v_src_1071_);
lean_dec_ref(v_remoteUrl_1070_);
lean_dec_ref(v_relPkgDir_1069_);
lean_dec_ref(v_name_1068_);
lean_dec_ref(v_dep_1065_);
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
else
{
size_t v___x_1182_; size_t v___x_1183_; lean_object* v___x_2460__overap_1184_; lean_object* v___x_1185_; 
v___x_1182_ = ((size_t)0ULL);
v___x_1183_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_2460__overap_1184_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1094_, v___f_1096_, v___x_1164_, v___x_1182_, v___x_1183_, v___x_1168_);
lean_inc_ref(v_a_1072_);
v___x_1185_ = lean_apply_2(v___x_2460__overap_1184_, v_a_1072_, lean_box(0));
if (lean_obj_tag(v___x_1185_) == 0)
{
lean_dec_ref_known(v___x_1185_, 1);
v_a_1132_ = v_val_1166_;
goto v___jp_1131_;
}
else
{
lean_object* v_a_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1193_; 
lean_dec(v_val_1166_);
lean_dec_ref(v_pkgDir_1093_);
lean_dec_ref(v_src_1071_);
lean_dec_ref(v_remoteUrl_1070_);
lean_dec_ref(v_relPkgDir_1069_);
lean_dec_ref(v_name_1068_);
lean_dec_ref(v_dep_1065_);
v_a_1186_ = lean_ctor_get(v___x_1185_, 0);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1188_ = v___x_1185_;
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_a_1186_);
lean_dec(v___x_1185_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1191_; 
if (v_isShared_1189_ == 0)
{
v___x_1191_ = v___x_1188_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_a_1186_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___boxed(lean_object* v_dep_1198_, lean_object* v_inherited_1199_, lean_object* v_wsDir_1200_, lean_object* v_name_1201_, lean_object* v_relPkgDir_1202_, lean_object* v_remoteUrl_1203_, lean_object* v_src_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_){
_start:
{
uint8_t v_inherited_boxed_1207_; lean_object* v_res_1208_; 
v_inherited_boxed_1207_ = lean_unbox(v_inherited_1199_);
v_res_1208_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep(v_dep_1198_, v_inherited_boxed_1207_, v_wsDir_1200_, v_name_1201_, v_relPkgDir_1202_, v_remoteUrl_1203_, v_src_1204_, v_a_1205_);
lean_dec_ref(v_a_1205_);
return v_res_1208_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(lean_object* v_a_1209_, lean_object* v_name_1210_, lean_object* v_repo_1211_, lean_object* v_url_1212_, lean_object* v_rev_x3f_1213_){
_start:
{
uint8_t v___x_1215_; lean_object* v___x_1219_; uint8_t v___x_1220_; 
v___x_1215_ = l_System_FilePath_isDir(v_repo_1211_);
v___x_1219_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_1220_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_1220_ == 0)
{
goto v___jp_1216_;
}
else
{
lean_object* v___x_1221_; uint8_t v___x_1222_; 
v___x_1221_ = lean_box(0);
v___x_1222_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_1222_ == 0)
{
if (v___x_1220_ == 0)
{
goto v___jp_1216_;
}
else
{
size_t v___x_1223_; size_t v___x_1224_; lean_object* v___x_1225_; 
v___x_1223_ = ((size_t)0ULL);
v___x_1224_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_1225_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_1219_, v___x_1223_, v___x_1224_, v___x_1221_, v_a_1209_);
if (lean_obj_tag(v___x_1225_) == 0)
{
lean_dec_ref_known(v___x_1225_, 1);
goto v___jp_1216_;
}
else
{
lean_dec(v_rev_x3f_1213_);
lean_dec_ref(v_url_1212_);
lean_dec_ref(v_repo_1211_);
lean_dec_ref(v_name_1210_);
return v___x_1225_;
}
}
}
else
{
size_t v___x_1226_; size_t v___x_1227_; lean_object* v___x_1228_; 
v___x_1226_ = ((size_t)0ULL);
v___x_1227_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_1228_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_1219_, v___x_1226_, v___x_1227_, v___x_1221_, v_a_1209_);
if (lean_obj_tag(v___x_1228_) == 0)
{
lean_dec_ref_known(v___x_1228_, 1);
goto v___jp_1216_;
}
else
{
lean_dec(v_rev_x3f_1213_);
lean_dec_ref(v_url_1212_);
lean_dec_ref(v_repo_1211_);
lean_dec_ref(v_name_1210_);
return v___x_1228_;
}
}
}
v___jp_1216_:
{
if (v___x_1215_ == 0)
{
lean_object* v___x_1217_; 
v___x_1217_ = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(v_a_1209_, v_name_1210_, v_repo_1211_, v_url_1212_, v_rev_x3f_1213_);
return v___x_1217_;
}
else
{
lean_object* v___x_1218_; 
v___x_1218_ = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1209_, v_name_1210_, v_repo_1211_, v_url_1212_, v_rev_x3f_1213_);
return v___x_1218_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0___boxed(lean_object* v_a_1229_, lean_object* v_name_1230_, lean_object* v_repo_1231_, lean_object* v_url_1232_, lean_object* v_rev_x3f_1233_, lean_object* v_a_1234_){
_start:
{
lean_object* v_res_1235_; 
v_res_1235_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(v_a_1229_, v_name_1230_, v_repo_1231_, v_url_1232_, v_rev_x3f_1233_);
lean_dec_ref(v_a_1229_);
return v_res_1235_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit(lean_object* v_dep_1236_, uint8_t v_inherited_1237_, lean_object* v_lakeEnv_1238_, lean_object* v_wsDir_1239_, lean_object* v_name_1240_, lean_object* v_relPkgDir_1241_, lean_object* v_gitUrl_1242_, lean_object* v_remoteUrl_1243_, lean_object* v_inputRev_x3f_1244_, lean_object* v_subDir_x3f_1245_, lean_object* v_a_1246_){
_start:
{
lean_object* v_pkgUrlMap_1251_; lean_object* v_name_1252_; lean_object* v_scope_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1469_; 
v_pkgUrlMap_1251_ = lean_ctor_get(v_lakeEnv_1238_, 5);
v_name_1252_ = lean_ctor_get(v_dep_1236_, 0);
v_scope_1253_ = lean_ctor_get(v_dep_1236_, 1);
v_isSharedCheck_1469_ = !lean_is_exclusive(v_dep_1236_);
if (v_isSharedCheck_1469_ == 0)
{
lean_object* v_unused_1470_; lean_object* v_unused_1471_; lean_object* v_unused_1472_; 
v_unused_1470_ = lean_ctor_get(v_dep_1236_, 4);
lean_dec(v_unused_1470_);
v_unused_1471_ = lean_ctor_get(v_dep_1236_, 3);
lean_dec(v_unused_1471_);
v_unused_1472_ = lean_ctor_get(v_dep_1236_, 2);
lean_dec(v_unused_1472_);
v___x_1255_ = v_dep_1236_;
v_isShared_1256_ = v_isSharedCheck_1469_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_scope_1253_);
lean_inc(v_name_1252_);
lean_dec(v_dep_1236_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1469_;
goto v_resetjp_1254_;
}
v___jp_1248_:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1249_ = lean_box(0);
v___x_1250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1249_);
return v___x_1250_;
}
v_resetjp_1254_:
{
lean_object* v___y_1258_; lean_object* v___y_1259_; lean_object* v___y_1260_; lean_object* v_a_1261_; lean_object* v___y_1270_; lean_object* v___y_1271_; lean_object* v___y_1272_; lean_object* v___y_1273_; lean_object* v___y_1274_; lean_object* v_val_1275_; lean_object* v___y_1303_; lean_object* v___y_1304_; lean_object* v___y_1305_; lean_object* v_a_1306_; lean_object* v___y_1338_; lean_object* v___y_1339_; lean_object* v___y_1340_; lean_object* v___y_1341_; lean_object* v___y_1342_; lean_object* v_val_1343_; lean_object* v___y_1371_; lean_object* v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1384_; lean_object* v_a_1385_; lean_object* v_gitDir_1388_; lean_object* v___y_1390_; lean_object* v___x_1467_; 
lean_inc_ref(v_relPkgDir_1241_);
lean_inc_ref(v_wsDir_1239_);
v_gitDir_1388_ = l_Lake_joinRelative(v_wsDir_1239_, v_relPkgDir_1241_);
v___x_1467_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgUrlMap_1251_, v_name_1252_);
if (lean_obj_tag(v___x_1467_) == 0)
{
v___y_1390_ = v_gitUrl_1242_;
goto v___jp_1389_;
}
else
{
lean_object* v_val_1468_; 
lean_dec_ref(v_gitUrl_1242_);
v_val_1468_ = lean_ctor_get(v___x_1467_, 0);
lean_inc(v_val_1468_);
lean_dec_ref_known(v___x_1467_, 1);
v___y_1390_ = v_val_1468_;
goto v___jp_1389_;
}
v___jp_1257_:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1266_; 
v___x_1262_ = l_Lake_defaultConfigFile;
v___x_1263_ = lean_box(0);
v___x_1264_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1264_, 0, v_name_1252_);
lean_ctor_set(v___x_1264_, 1, v_scope_1253_);
lean_ctor_set(v___x_1264_, 2, v___x_1262_);
lean_ctor_set(v___x_1264_, 3, v___x_1263_);
lean_ctor_set(v___x_1264_, 4, v___y_1259_);
lean_ctor_set_uint8(v___x_1264_, sizeof(void*)*5, v_inherited_1237_);
if (v_isShared_1256_ == 0)
{
lean_ctor_set(v___x_1255_, 4, v___x_1264_);
lean_ctor_set(v___x_1255_, 3, v_a_1261_);
lean_ctor_set(v___x_1255_, 2, v_remoteUrl_1243_);
lean_ctor_set(v___x_1255_, 1, v___y_1260_);
lean_ctor_set(v___x_1255_, 0, v___y_1258_);
v___x_1266_ = v___x_1255_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v___y_1258_);
lean_ctor_set(v_reuseFailAlloc_1268_, 1, v___y_1260_);
lean_ctor_set(v_reuseFailAlloc_1268_, 2, v_remoteUrl_1243_);
lean_ctor_set(v_reuseFailAlloc_1268_, 3, v_a_1261_);
lean_ctor_set(v_reuseFailAlloc_1268_, 4, v___x_1264_);
v___x_1266_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
lean_object* v___x_1267_; 
v___x_1267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1267_, 0, v___x_1266_);
return v___x_1267_;
}
}
v___jp_1269_:
{
lean_object* v___x_1276_; uint8_t v___x_1277_; 
v___x_1276_ = lean_array_get_size(v___y_1270_);
v___x_1277_ = lean_nat_dec_lt(v___y_1273_, v___x_1276_);
if (v___x_1277_ == 0)
{
v___y_1258_ = v___y_1271_;
v___y_1259_ = v___y_1272_;
v___y_1260_ = v___y_1274_;
v_a_1261_ = v_val_1275_;
goto v___jp_1257_;
}
else
{
lean_object* v___x_1278_; uint8_t v___x_1279_; 
v___x_1278_ = lean_box(0);
v___x_1279_ = lean_nat_dec_le(v___x_1276_, v___x_1276_);
if (v___x_1279_ == 0)
{
if (v___x_1277_ == 0)
{
v___y_1258_ = v___y_1271_;
v___y_1259_ = v___y_1272_;
v___y_1260_ = v___y_1274_;
v_a_1261_ = v_val_1275_;
goto v___jp_1257_;
}
else
{
size_t v___x_1280_; size_t v___x_1281_; lean_object* v___x_1282_; 
v___x_1280_ = ((size_t)0ULL);
v___x_1281_ = lean_usize_of_nat(v___x_1276_);
v___x_1282_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_1270_, v___x_1280_, v___x_1281_, v___x_1278_, v_a_1246_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_dec_ref_known(v___x_1282_, 1);
v___y_1258_ = v___y_1271_;
v___y_1259_ = v___y_1272_;
v___y_1260_ = v___y_1274_;
v_a_1261_ = v_val_1275_;
goto v___jp_1257_;
}
else
{
lean_object* v_a_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1290_; 
lean_dec_ref(v_val_1275_);
lean_dec_ref(v___y_1274_);
lean_dec_ref(v___y_1272_);
lean_dec_ref(v___y_1271_);
lean_del_object(v___x_1255_);
lean_dec_ref(v_scope_1253_);
lean_dec(v_name_1252_);
lean_dec_ref(v_remoteUrl_1243_);
v_a_1283_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1285_ = v___x_1282_;
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_a_1283_);
lean_dec(v___x_1282_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1288_; 
if (v_isShared_1286_ == 0)
{
v___x_1288_ = v___x_1285_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_a_1283_);
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
}
else
{
size_t v___x_1291_; size_t v___x_1292_; lean_object* v___x_1293_; 
v___x_1291_ = ((size_t)0ULL);
v___x_1292_ = lean_usize_of_nat(v___x_1276_);
v___x_1293_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_1270_, v___x_1291_, v___x_1292_, v___x_1278_, v_a_1246_);
if (lean_obj_tag(v___x_1293_) == 0)
{
lean_dec_ref_known(v___x_1293_, 1);
v___y_1258_ = v___y_1271_;
v___y_1259_ = v___y_1272_;
v___y_1260_ = v___y_1274_;
v_a_1261_ = v_val_1275_;
goto v___jp_1257_;
}
else
{
lean_object* v_a_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1301_; 
lean_dec_ref(v_val_1275_);
lean_dec_ref(v___y_1274_);
lean_dec_ref(v___y_1272_);
lean_dec_ref(v___y_1271_);
lean_del_object(v___x_1255_);
lean_dec_ref(v_scope_1253_);
lean_dec(v_name_1252_);
lean_dec_ref(v_remoteUrl_1243_);
v_a_1294_ = lean_ctor_get(v___x_1293_, 0);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1296_ = v___x_1293_;
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_a_1294_);
lean_dec(v___x_1293_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1299_; 
if (v_isShared_1297_ == 0)
{
v___x_1299_ = v___x_1296_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_a_1294_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
}
}
}
}
v___jp_1302_:
{
if (lean_obj_tag(v_a_1306_) == 1)
{
lean_object* v_val_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; 
lean_dec_ref(v___y_1303_);
lean_dec_ref(v_name_1240_);
v_val_1307_ = lean_ctor_get(v_a_1306_, 0);
lean_inc_n(v_val_1307_, 2);
lean_dec_ref_known(v_a_1306_, 1);
v___x_1308_ = l_Lake_defaultManifestFile;
v___x_1309_ = l_Lake_joinRelative(v_val_1307_, v___x_1308_);
v___x_1310_ = lean_unsigned_to_nat(0u);
v___x_1311_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_1312_ = l_Lake_Manifest_load(v___x_1309_);
if (lean_obj_tag(v___x_1312_) == 0)
{
lean_object* v_a_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1320_; 
v_a_1313_ = lean_ctor_get(v___x_1312_, 0);
v_isSharedCheck_1320_ = !lean_is_exclusive(v___x_1312_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1315_ = v___x_1312_;
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_a_1313_);
lean_dec(v___x_1312_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___x_1318_; 
if (v_isShared_1316_ == 0)
{
lean_ctor_set_tag(v___x_1315_, 1);
v___x_1318_ = v___x_1315_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_a_1313_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
v___y_1270_ = v___x_1311_;
v___y_1271_ = v_val_1307_;
v___y_1272_ = v___y_1304_;
v___y_1273_ = v___x_1310_;
v___y_1274_ = v___y_1305_;
v_val_1275_ = v___x_1318_;
goto v___jp_1269_;
}
}
}
else
{
lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1328_; 
v_a_1321_ = lean_ctor_get(v___x_1312_, 0);
v_isSharedCheck_1328_ = !lean_is_exclusive(v___x_1312_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1323_ = v___x_1312_;
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_dec(v___x_1312_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1326_; 
if (v_isShared_1324_ == 0)
{
lean_ctor_set_tag(v___x_1323_, 0);
v___x_1326_ = v___x_1323_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_a_1321_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
v___y_1270_ = v___x_1311_;
v___y_1271_ = v_val_1307_;
v___y_1272_ = v___y_1304_;
v___y_1273_ = v___x_1310_;
v___y_1274_ = v___y_1305_;
v_val_1275_ = v___x_1326_;
goto v___jp_1269_;
}
}
}
}
else
{
lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; uint8_t v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; 
lean_dec(v_a_1306_);
lean_dec_ref(v___y_1305_);
lean_dec_ref(v___y_1304_);
lean_del_object(v___x_1255_);
lean_dec_ref(v_scope_1253_);
lean_dec(v_name_1252_);
lean_dec_ref(v_remoteUrl_1243_);
v___x_1329_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__3));
v___x_1330_ = lean_string_append(v_name_1240_, v___x_1329_);
v___x_1331_ = lean_string_append(v___x_1330_, v___y_1303_);
lean_dec_ref(v___y_1303_);
v___x_1332_ = 3;
v___x_1333_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1333_, 0, v___x_1331_);
lean_ctor_set_uint8(v___x_1333_, sizeof(void*)*1, v___x_1332_);
lean_inc_ref(v_a_1246_);
v___x_1334_ = lean_apply_2(v_a_1246_, v___x_1333_, lean_box(0));
v___x_1335_ = lean_box(0);
v___x_1336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1336_, 0, v___x_1335_);
return v___x_1336_;
}
}
v___jp_1337_:
{
lean_object* v___x_1344_; uint8_t v___x_1345_; 
v___x_1344_ = lean_array_get_size(v___y_1340_);
v___x_1345_ = lean_nat_dec_lt(v___y_1341_, v___x_1344_);
if (v___x_1345_ == 0)
{
v___y_1303_ = v___y_1338_;
v___y_1304_ = v___y_1339_;
v___y_1305_ = v___y_1342_;
v_a_1306_ = v_val_1343_;
goto v___jp_1302_;
}
else
{
lean_object* v___x_1346_; uint8_t v___x_1347_; 
v___x_1346_ = lean_box(0);
v___x_1347_ = lean_nat_dec_le(v___x_1344_, v___x_1344_);
if (v___x_1347_ == 0)
{
if (v___x_1345_ == 0)
{
v___y_1303_ = v___y_1338_;
v___y_1304_ = v___y_1339_;
v___y_1305_ = v___y_1342_;
v_a_1306_ = v_val_1343_;
goto v___jp_1302_;
}
else
{
size_t v___x_1348_; size_t v___x_1349_; lean_object* v___x_1350_; 
v___x_1348_ = ((size_t)0ULL);
v___x_1349_ = lean_usize_of_nat(v___x_1344_);
v___x_1350_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_1340_, v___x_1348_, v___x_1349_, v___x_1346_, v_a_1246_);
if (lean_obj_tag(v___x_1350_) == 0)
{
lean_dec_ref_known(v___x_1350_, 1);
v___y_1303_ = v___y_1338_;
v___y_1304_ = v___y_1339_;
v___y_1305_ = v___y_1342_;
v_a_1306_ = v_val_1343_;
goto v___jp_1302_;
}
else
{
lean_object* v_a_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1358_; 
lean_dec(v_val_1343_);
lean_dec_ref(v___y_1342_);
lean_dec_ref(v___y_1339_);
lean_dec_ref(v___y_1338_);
lean_del_object(v___x_1255_);
lean_dec_ref(v_scope_1253_);
lean_dec(v_name_1252_);
lean_dec_ref(v_remoteUrl_1243_);
lean_dec_ref(v_name_1240_);
v_a_1351_ = lean_ctor_get(v___x_1350_, 0);
v_isSharedCheck_1358_ = !lean_is_exclusive(v___x_1350_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1353_ = v___x_1350_;
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_a_1351_);
lean_dec(v___x_1350_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1356_; 
if (v_isShared_1354_ == 0)
{
v___x_1356_ = v___x_1353_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_a_1351_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
}
}
}
else
{
size_t v___x_1359_; size_t v___x_1360_; lean_object* v___x_1361_; 
v___x_1359_ = ((size_t)0ULL);
v___x_1360_ = lean_usize_of_nat(v___x_1344_);
v___x_1361_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_1340_, v___x_1359_, v___x_1360_, v___x_1346_, v_a_1246_);
if (lean_obj_tag(v___x_1361_) == 0)
{
lean_dec_ref_known(v___x_1361_, 1);
v___y_1303_ = v___y_1338_;
v___y_1304_ = v___y_1339_;
v___y_1305_ = v___y_1342_;
v_a_1306_ = v_val_1343_;
goto v___jp_1302_;
}
else
{
lean_object* v_a_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1369_; 
lean_dec(v_val_1343_);
lean_dec_ref(v___y_1342_);
lean_dec_ref(v___y_1339_);
lean_dec_ref(v___y_1338_);
lean_del_object(v___x_1255_);
lean_dec_ref(v_scope_1253_);
lean_dec(v_name_1252_);
lean_dec_ref(v_remoteUrl_1243_);
lean_dec_ref(v_name_1240_);
v_a_1362_ = lean_ctor_get(v___x_1361_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1364_ = v___x_1361_;
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_a_1362_);
lean_dec(v___x_1361_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1367_; 
if (v_isShared_1365_ == 0)
{
v___x_1367_ = v___x_1364_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_a_1362_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
}
}
}
v___jp_1370_:
{
lean_object* v_pkgDir_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; uint8_t v___x_1380_; 
lean_inc_ref(v___y_1373_);
v_pkgDir_1374_ = l_Lake_joinRelative(v_wsDir_1239_, v___y_1373_);
lean_inc_ref(v_pkgDir_1374_);
v___x_1375_ = l_Lake_resolvePath(v_pkgDir_1374_);
v___x_1376_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1376_, 0, v___y_1371_);
lean_ctor_set(v___x_1376_, 1, v___y_1372_);
lean_ctor_set(v___x_1376_, 2, v_inputRev_x3f_1244_);
lean_ctor_set(v___x_1376_, 3, v_subDir_x3f_1245_);
v___x_1377_ = lean_unsigned_to_nat(0u);
v___x_1378_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_1379_ = lean_string_utf8_byte_size(v___x_1375_);
v___x_1380_ = lean_nat_dec_eq(v___x_1379_, v___x_1377_);
if (v___x_1380_ == 0)
{
lean_object* v___x_1381_; 
v___x_1381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1381_, 0, v___x_1375_);
v___y_1338_ = v_pkgDir_1374_;
v___y_1339_ = v___x_1376_;
v___y_1340_ = v___x_1378_;
v___y_1341_ = v___x_1377_;
v___y_1342_ = v___y_1373_;
v_val_1343_ = v___x_1381_;
goto v___jp_1337_;
}
else
{
lean_object* v___x_1382_; 
lean_dec_ref(v___x_1375_);
v___x_1382_ = lean_box(0);
v___y_1338_ = v_pkgDir_1374_;
v___y_1339_ = v___x_1376_;
v___y_1340_ = v___x_1378_;
v___y_1341_ = v___x_1377_;
v___y_1342_ = v___y_1373_;
v_val_1343_ = v___x_1382_;
goto v___jp_1337_;
}
}
v___jp_1383_:
{
if (lean_obj_tag(v_subDir_x3f_1245_) == 1)
{
lean_object* v_val_1386_; lean_object* v___x_1387_; 
v_val_1386_ = lean_ctor_get(v_subDir_x3f_1245_, 0);
lean_inc(v_val_1386_);
v___x_1387_ = l_Lake_joinRelative(v_relPkgDir_1241_, v_val_1386_);
v___y_1371_ = v___y_1384_;
v___y_1372_ = v_a_1385_;
v___y_1373_ = v___x_1387_;
goto v___jp_1370_;
}
else
{
v___y_1371_ = v___y_1384_;
v___y_1372_ = v_a_1385_;
v___y_1373_ = v_relPkgDir_1241_;
goto v___jp_1370_;
}
}
v___jp_1389_:
{
lean_object* v___x_1391_; 
lean_inc(v_inputRev_x3f_1244_);
lean_inc_ref(v___y_1390_);
lean_inc_ref(v_gitDir_1388_);
lean_inc_ref(v_name_1240_);
v___x_1391_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(v_a_1246_, v_name_1240_, v_gitDir_1388_, v___y_1390_, v_inputRev_x3f_1244_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1457_; 
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1457_ == 0)
{
lean_object* v_unused_1458_; 
v_unused_1458_ = lean_ctor_get(v___x_1391_, 0);
lean_dec(v_unused_1458_);
v___x_1393_ = v___x_1391_;
v_isShared_1394_ = v_isSharedCheck_1457_;
goto v_resetjp_1392_;
}
else
{
lean_dec(v___x_1391_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1457_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; 
v___x_1395_ = lean_unsigned_to_nat(0u);
v___x_1396_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_1397_ = l_Lake_GitRepo_getHeadRevision(v_gitDir_1388_, v___x_1396_);
if (lean_obj_tag(v___x_1397_) == 0)
{
lean_object* v_a_1398_; lean_object* v_a_1399_; lean_object* v___x_1400_; uint8_t v___x_1401_; 
lean_del_object(v___x_1393_);
v_a_1398_ = lean_ctor_get(v___x_1397_, 0);
lean_inc(v_a_1398_);
v_a_1399_ = lean_ctor_get(v___x_1397_, 1);
lean_inc(v_a_1399_);
lean_dec_ref_known(v___x_1397_, 2);
v___x_1400_ = lean_array_get_size(v_a_1399_);
v___x_1401_ = lean_nat_dec_lt(v___x_1395_, v___x_1400_);
if (v___x_1401_ == 0)
{
lean_dec(v_a_1399_);
v___y_1384_ = v___y_1390_;
v_a_1385_ = v_a_1398_;
goto v___jp_1383_;
}
else
{
lean_object* v___x_1402_; uint8_t v___x_1403_; 
v___x_1402_ = lean_box(0);
v___x_1403_ = lean_nat_dec_le(v___x_1400_, v___x_1400_);
if (v___x_1403_ == 0)
{
if (v___x_1401_ == 0)
{
lean_dec(v_a_1399_);
v___y_1384_ = v___y_1390_;
v_a_1385_ = v_a_1398_;
goto v___jp_1383_;
}
else
{
size_t v___x_1404_; size_t v___x_1405_; lean_object* v___x_1406_; 
v___x_1404_ = ((size_t)0ULL);
v___x_1405_ = lean_usize_of_nat(v___x_1400_);
v___x_1406_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_1399_, v___x_1404_, v___x_1405_, v___x_1402_, v_a_1246_);
lean_dec(v_a_1399_);
if (lean_obj_tag(v___x_1406_) == 0)
{
lean_dec_ref_known(v___x_1406_, 1);
v___y_1384_ = v___y_1390_;
v_a_1385_ = v_a_1398_;
goto v___jp_1383_;
}
else
{
lean_object* v_a_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1414_; 
lean_dec(v_a_1398_);
lean_dec_ref(v___y_1390_);
lean_del_object(v___x_1255_);
lean_dec_ref(v_scope_1253_);
lean_dec(v_name_1252_);
lean_dec(v_subDir_x3f_1245_);
lean_dec(v_inputRev_x3f_1244_);
lean_dec_ref(v_remoteUrl_1243_);
lean_dec_ref(v_relPkgDir_1241_);
lean_dec_ref(v_name_1240_);
lean_dec_ref(v_wsDir_1239_);
v_a_1407_ = lean_ctor_get(v___x_1406_, 0);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1409_ = v___x_1406_;
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_a_1407_);
lean_dec(v___x_1406_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1412_; 
if (v_isShared_1410_ == 0)
{
v___x_1412_ = v___x_1409_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_a_1407_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
return v___x_1412_;
}
}
}
}
}
else
{
size_t v___x_1415_; size_t v___x_1416_; lean_object* v___x_1417_; 
v___x_1415_ = ((size_t)0ULL);
v___x_1416_ = lean_usize_of_nat(v___x_1400_);
v___x_1417_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_1399_, v___x_1415_, v___x_1416_, v___x_1402_, v_a_1246_);
lean_dec(v_a_1399_);
if (lean_obj_tag(v___x_1417_) == 0)
{
lean_dec_ref_known(v___x_1417_, 1);
v___y_1384_ = v___y_1390_;
v_a_1385_ = v_a_1398_;
goto v___jp_1383_;
}
else
{
lean_object* v_a_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1425_; 
lean_dec(v_a_1398_);
lean_dec_ref(v___y_1390_);
lean_del_object(v___x_1255_);
lean_dec_ref(v_scope_1253_);
lean_dec(v_name_1252_);
lean_dec(v_subDir_x3f_1245_);
lean_dec(v_inputRev_x3f_1244_);
lean_dec_ref(v_remoteUrl_1243_);
lean_dec_ref(v_relPkgDir_1241_);
lean_dec_ref(v_name_1240_);
lean_dec_ref(v_wsDir_1239_);
v_a_1418_ = lean_ctor_get(v___x_1417_, 0);
v_isSharedCheck_1425_ = !lean_is_exclusive(v___x_1417_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1420_ = v___x_1417_;
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_a_1418_);
lean_dec(v___x_1417_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v___x_1423_; 
if (v_isShared_1421_ == 0)
{
v___x_1423_ = v___x_1420_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_a_1418_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
}
}
}
}
else
{
lean_object* v_a_1426_; lean_object* v___x_1427_; uint8_t v___x_1428_; 
lean_dec_ref(v___y_1390_);
lean_del_object(v___x_1255_);
lean_dec_ref(v_scope_1253_);
lean_dec(v_name_1252_);
lean_dec(v_subDir_x3f_1245_);
lean_dec(v_inputRev_x3f_1244_);
lean_dec_ref(v_remoteUrl_1243_);
lean_dec_ref(v_relPkgDir_1241_);
lean_dec_ref(v_name_1240_);
lean_dec_ref(v_wsDir_1239_);
v_a_1426_ = lean_ctor_get(v___x_1397_, 1);
lean_inc(v_a_1426_);
lean_dec_ref_known(v___x_1397_, 2);
v___x_1427_ = lean_array_get_size(v_a_1426_);
v___x_1428_ = lean_nat_dec_lt(v___x_1395_, v___x_1427_);
if (v___x_1428_ == 0)
{
lean_object* v___x_1429_; lean_object* v___x_1431_; 
lean_dec(v_a_1426_);
v___x_1429_ = lean_box(0);
if (v_isShared_1394_ == 0)
{
lean_ctor_set_tag(v___x_1393_, 1);
lean_ctor_set(v___x_1393_, 0, v___x_1429_);
v___x_1431_ = v___x_1393_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v___x_1429_);
v___x_1431_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
return v___x_1431_;
}
}
else
{
lean_object* v___x_1433_; uint8_t v___x_1434_; 
lean_del_object(v___x_1393_);
v___x_1433_ = lean_box(0);
v___x_1434_ = lean_nat_dec_le(v___x_1427_, v___x_1427_);
if (v___x_1434_ == 0)
{
if (v___x_1428_ == 0)
{
lean_dec(v_a_1426_);
goto v___jp_1248_;
}
else
{
size_t v___x_1435_; size_t v___x_1436_; lean_object* v___x_1437_; 
v___x_1435_ = ((size_t)0ULL);
v___x_1436_ = lean_usize_of_nat(v___x_1427_);
v___x_1437_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_1426_, v___x_1435_, v___x_1436_, v___x_1433_, v_a_1246_);
lean_dec(v_a_1426_);
if (lean_obj_tag(v___x_1437_) == 0)
{
lean_dec_ref_known(v___x_1437_, 1);
goto v___jp_1248_;
}
else
{
lean_object* v_a_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1445_; 
v_a_1438_ = lean_ctor_get(v___x_1437_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1437_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1440_ = v___x_1437_;
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_a_1438_);
lean_dec(v___x_1437_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1443_; 
if (v_isShared_1441_ == 0)
{
v___x_1443_ = v___x_1440_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_a_1438_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
}
}
else
{
size_t v___x_1446_; size_t v___x_1447_; lean_object* v___x_1448_; 
v___x_1446_ = ((size_t)0ULL);
v___x_1447_ = lean_usize_of_nat(v___x_1427_);
v___x_1448_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_1426_, v___x_1446_, v___x_1447_, v___x_1433_, v_a_1246_);
lean_dec(v_a_1426_);
if (lean_obj_tag(v___x_1448_) == 0)
{
lean_dec_ref_known(v___x_1448_, 1);
goto v___jp_1248_;
}
else
{
lean_object* v_a_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1456_; 
v_a_1449_ = lean_ctor_get(v___x_1448_, 0);
v_isSharedCheck_1456_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1451_ = v___x_1448_;
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_a_1449_);
lean_dec(v___x_1448_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1454_; 
if (v_isShared_1452_ == 0)
{
v___x_1454_ = v___x_1451_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_a_1449_);
v___x_1454_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
return v___x_1454_;
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
lean_object* v_a_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1466_; 
lean_dec_ref(v___y_1390_);
lean_dec_ref(v_gitDir_1388_);
lean_del_object(v___x_1255_);
lean_dec_ref(v_scope_1253_);
lean_dec(v_name_1252_);
lean_dec(v_subDir_x3f_1245_);
lean_dec(v_inputRev_x3f_1244_);
lean_dec_ref(v_remoteUrl_1243_);
lean_dec_ref(v_relPkgDir_1241_);
lean_dec_ref(v_name_1240_);
lean_dec_ref(v_wsDir_1239_);
v_a_1459_ = lean_ctor_get(v___x_1391_, 0);
v_isSharedCheck_1466_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1466_ == 0)
{
v___x_1461_ = v___x_1391_;
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_a_1459_);
lean_dec(v___x_1391_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v___x_1464_; 
if (v_isShared_1462_ == 0)
{
v___x_1464_ = v___x_1461_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v_a_1459_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
return v___x_1464_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___boxed(lean_object* v_dep_1473_, lean_object* v_inherited_1474_, lean_object* v_lakeEnv_1475_, lean_object* v_wsDir_1476_, lean_object* v_name_1477_, lean_object* v_relPkgDir_1478_, lean_object* v_gitUrl_1479_, lean_object* v_remoteUrl_1480_, lean_object* v_inputRev_x3f_1481_, lean_object* v_subDir_x3f_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_){
_start:
{
uint8_t v_inherited_boxed_1485_; lean_object* v_res_1486_; 
v_inherited_boxed_1485_ = lean_unbox(v_inherited_1474_);
v_res_1486_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit(v_dep_1473_, v_inherited_boxed_1485_, v_lakeEnv_1475_, v_wsDir_1476_, v_name_1477_, v_relPkgDir_1478_, v_gitUrl_1479_, v_remoteUrl_1480_, v_inputRev_x3f_1481_, v_subDir_x3f_1482_, v_a_1483_);
lean_dec_ref(v_a_1483_);
lean_dec_ref(v_lakeEnv_1475_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(lean_object* v_a_1487_, lean_object* v_dep_1488_, uint8_t v_inherited_1489_, lean_object* v_lakeEnv_1490_, lean_object* v_wsDir_1491_, lean_object* v_name_1492_, lean_object* v_relPkgDir_1493_, lean_object* v_gitUrl_1494_, lean_object* v_remoteUrl_1495_, lean_object* v_inputRev_x3f_1496_, lean_object* v_subDir_x3f_1497_){
_start:
{
lean_object* v_pkgUrlMap_1502_; lean_object* v_name_1503_; lean_object* v_scope_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1720_; 
v_pkgUrlMap_1502_ = lean_ctor_get(v_lakeEnv_1490_, 5);
v_name_1503_ = lean_ctor_get(v_dep_1488_, 0);
v_scope_1504_ = lean_ctor_get(v_dep_1488_, 1);
v_isSharedCheck_1720_ = !lean_is_exclusive(v_dep_1488_);
if (v_isSharedCheck_1720_ == 0)
{
lean_object* v_unused_1721_; lean_object* v_unused_1722_; lean_object* v_unused_1723_; 
v_unused_1721_ = lean_ctor_get(v_dep_1488_, 4);
lean_dec(v_unused_1721_);
v_unused_1722_ = lean_ctor_get(v_dep_1488_, 3);
lean_dec(v_unused_1722_);
v_unused_1723_ = lean_ctor_get(v_dep_1488_, 2);
lean_dec(v_unused_1723_);
v___x_1506_ = v_dep_1488_;
v_isShared_1507_ = v_isSharedCheck_1720_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_scope_1504_);
lean_inc(v_name_1503_);
lean_dec(v_dep_1488_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1720_;
goto v_resetjp_1505_;
}
v___jp_1499_:
{
lean_object* v___x_1500_; lean_object* v___x_1501_; 
v___x_1500_ = lean_box(0);
v___x_1501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1501_, 0, v___x_1500_);
return v___x_1501_;
}
v_resetjp_1505_:
{
lean_object* v___y_1509_; lean_object* v___y_1510_; lean_object* v___y_1511_; lean_object* v_a_1512_; lean_object* v___y_1521_; lean_object* v___y_1522_; lean_object* v___y_1523_; lean_object* v___y_1524_; lean_object* v___y_1525_; lean_object* v_val_1526_; lean_object* v___y_1554_; lean_object* v___y_1555_; lean_object* v___y_1556_; lean_object* v_a_1557_; lean_object* v___y_1589_; lean_object* v___y_1590_; lean_object* v___y_1591_; lean_object* v___y_1592_; lean_object* v___y_1593_; lean_object* v_val_1594_; lean_object* v___y_1622_; lean_object* v___y_1623_; lean_object* v___y_1624_; lean_object* v___y_1635_; lean_object* v_a_1636_; lean_object* v_gitDir_1639_; lean_object* v___y_1641_; lean_object* v___x_1718_; 
lean_inc_ref(v_relPkgDir_1493_);
lean_inc_ref(v_wsDir_1491_);
v_gitDir_1639_ = l_Lake_joinRelative(v_wsDir_1491_, v_relPkgDir_1493_);
v___x_1718_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgUrlMap_1502_, v_name_1503_);
if (lean_obj_tag(v___x_1718_) == 0)
{
v___y_1641_ = v_gitUrl_1494_;
goto v___jp_1640_;
}
else
{
lean_object* v_val_1719_; 
lean_dec_ref(v_gitUrl_1494_);
v_val_1719_ = lean_ctor_get(v___x_1718_, 0);
lean_inc(v_val_1719_);
lean_dec_ref_known(v___x_1718_, 1);
v___y_1641_ = v_val_1719_;
goto v___jp_1640_;
}
v___jp_1508_:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1517_; 
v___x_1513_ = l_Lake_defaultConfigFile;
v___x_1514_ = lean_box(0);
v___x_1515_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1515_, 0, v_name_1503_);
lean_ctor_set(v___x_1515_, 1, v_scope_1504_);
lean_ctor_set(v___x_1515_, 2, v___x_1513_);
lean_ctor_set(v___x_1515_, 3, v___x_1514_);
lean_ctor_set(v___x_1515_, 4, v___y_1510_);
lean_ctor_set_uint8(v___x_1515_, sizeof(void*)*5, v_inherited_1489_);
if (v_isShared_1507_ == 0)
{
lean_ctor_set(v___x_1506_, 4, v___x_1515_);
lean_ctor_set(v___x_1506_, 3, v_a_1512_);
lean_ctor_set(v___x_1506_, 2, v_remoteUrl_1495_);
lean_ctor_set(v___x_1506_, 1, v___y_1509_);
lean_ctor_set(v___x_1506_, 0, v___y_1511_);
v___x_1517_ = v___x_1506_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v___y_1511_);
lean_ctor_set(v_reuseFailAlloc_1519_, 1, v___y_1509_);
lean_ctor_set(v_reuseFailAlloc_1519_, 2, v_remoteUrl_1495_);
lean_ctor_set(v_reuseFailAlloc_1519_, 3, v_a_1512_);
lean_ctor_set(v_reuseFailAlloc_1519_, 4, v___x_1515_);
v___x_1517_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
lean_object* v___x_1518_; 
v___x_1518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1518_, 0, v___x_1517_);
return v___x_1518_;
}
}
v___jp_1520_:
{
lean_object* v___x_1527_; uint8_t v___x_1528_; 
v___x_1527_ = lean_array_get_size(v___y_1521_);
v___x_1528_ = lean_nat_dec_lt(v___y_1523_, v___x_1527_);
if (v___x_1528_ == 0)
{
v___y_1509_ = v___y_1522_;
v___y_1510_ = v___y_1524_;
v___y_1511_ = v___y_1525_;
v_a_1512_ = v_val_1526_;
goto v___jp_1508_;
}
else
{
lean_object* v___x_1529_; uint8_t v___x_1530_; 
v___x_1529_ = lean_box(0);
v___x_1530_ = lean_nat_dec_le(v___x_1527_, v___x_1527_);
if (v___x_1530_ == 0)
{
if (v___x_1528_ == 0)
{
v___y_1509_ = v___y_1522_;
v___y_1510_ = v___y_1524_;
v___y_1511_ = v___y_1525_;
v_a_1512_ = v_val_1526_;
goto v___jp_1508_;
}
else
{
size_t v___x_1531_; size_t v___x_1532_; lean_object* v___x_1533_; 
v___x_1531_ = ((size_t)0ULL);
v___x_1532_ = lean_usize_of_nat(v___x_1527_);
v___x_1533_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_1521_, v___x_1531_, v___x_1532_, v___x_1529_, v_a_1487_);
if (lean_obj_tag(v___x_1533_) == 0)
{
lean_dec_ref_known(v___x_1533_, 1);
v___y_1509_ = v___y_1522_;
v___y_1510_ = v___y_1524_;
v___y_1511_ = v___y_1525_;
v_a_1512_ = v_val_1526_;
goto v___jp_1508_;
}
else
{
lean_object* v_a_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1541_; 
lean_dec_ref(v_val_1526_);
lean_dec_ref(v___y_1525_);
lean_dec_ref(v___y_1524_);
lean_dec_ref(v___y_1522_);
lean_del_object(v___x_1506_);
lean_dec_ref(v_scope_1504_);
lean_dec(v_name_1503_);
lean_dec_ref(v_remoteUrl_1495_);
v_a_1534_ = lean_ctor_get(v___x_1533_, 0);
v_isSharedCheck_1541_ = !lean_is_exclusive(v___x_1533_);
if (v_isSharedCheck_1541_ == 0)
{
v___x_1536_ = v___x_1533_;
v_isShared_1537_ = v_isSharedCheck_1541_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_a_1534_);
lean_dec(v___x_1533_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1541_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
lean_object* v___x_1539_; 
if (v_isShared_1537_ == 0)
{
v___x_1539_ = v___x_1536_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_a_1534_);
v___x_1539_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
return v___x_1539_;
}
}
}
}
}
else
{
size_t v___x_1542_; size_t v___x_1543_; lean_object* v___x_1544_; 
v___x_1542_ = ((size_t)0ULL);
v___x_1543_ = lean_usize_of_nat(v___x_1527_);
v___x_1544_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_1521_, v___x_1542_, v___x_1543_, v___x_1529_, v_a_1487_);
if (lean_obj_tag(v___x_1544_) == 0)
{
lean_dec_ref_known(v___x_1544_, 1);
v___y_1509_ = v___y_1522_;
v___y_1510_ = v___y_1524_;
v___y_1511_ = v___y_1525_;
v_a_1512_ = v_val_1526_;
goto v___jp_1508_;
}
else
{
lean_object* v_a_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1552_; 
lean_dec_ref(v_val_1526_);
lean_dec_ref(v___y_1525_);
lean_dec_ref(v___y_1524_);
lean_dec_ref(v___y_1522_);
lean_del_object(v___x_1506_);
lean_dec_ref(v_scope_1504_);
lean_dec(v_name_1503_);
lean_dec_ref(v_remoteUrl_1495_);
v_a_1545_ = lean_ctor_get(v___x_1544_, 0);
v_isSharedCheck_1552_ = !lean_is_exclusive(v___x_1544_);
if (v_isSharedCheck_1552_ == 0)
{
v___x_1547_ = v___x_1544_;
v_isShared_1548_ = v_isSharedCheck_1552_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_a_1545_);
lean_dec(v___x_1544_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1552_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___x_1550_; 
if (v_isShared_1548_ == 0)
{
v___x_1550_ = v___x_1547_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v_a_1545_);
v___x_1550_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
return v___x_1550_;
}
}
}
}
}
}
v___jp_1553_:
{
if (lean_obj_tag(v_a_1557_) == 1)
{
lean_object* v_val_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; 
lean_dec_ref(v___y_1556_);
lean_dec_ref(v_name_1492_);
v_val_1558_ = lean_ctor_get(v_a_1557_, 0);
lean_inc_n(v_val_1558_, 2);
lean_dec_ref_known(v_a_1557_, 1);
v___x_1559_ = l_Lake_defaultManifestFile;
v___x_1560_ = l_Lake_joinRelative(v_val_1558_, v___x_1559_);
v___x_1561_ = lean_unsigned_to_nat(0u);
v___x_1562_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_1563_ = l_Lake_Manifest_load(v___x_1560_);
if (lean_obj_tag(v___x_1563_) == 0)
{
lean_object* v_a_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1571_; 
v_a_1564_ = lean_ctor_get(v___x_1563_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1566_ = v___x_1563_;
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_a_1564_);
lean_dec(v___x_1563_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1569_; 
if (v_isShared_1567_ == 0)
{
lean_ctor_set_tag(v___x_1566_, 1);
v___x_1569_ = v___x_1566_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_a_1564_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
v___y_1521_ = v___x_1562_;
v___y_1522_ = v___y_1554_;
v___y_1523_ = v___x_1561_;
v___y_1524_ = v___y_1555_;
v___y_1525_ = v_val_1558_;
v_val_1526_ = v___x_1569_;
goto v___jp_1520_;
}
}
}
else
{
lean_object* v_a_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1579_; 
v_a_1572_ = lean_ctor_get(v___x_1563_, 0);
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1574_ = v___x_1563_;
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_a_1572_);
lean_dec(v___x_1563_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v___x_1577_; 
if (v_isShared_1575_ == 0)
{
lean_ctor_set_tag(v___x_1574_, 0);
v___x_1577_ = v___x_1574_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_a_1572_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
v___y_1521_ = v___x_1562_;
v___y_1522_ = v___y_1554_;
v___y_1523_ = v___x_1561_;
v___y_1524_ = v___y_1555_;
v___y_1525_ = v_val_1558_;
v_val_1526_ = v___x_1577_;
goto v___jp_1520_;
}
}
}
}
else
{
lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; uint8_t v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; 
lean_dec(v_a_1557_);
lean_dec_ref(v___y_1555_);
lean_dec_ref(v___y_1554_);
lean_del_object(v___x_1506_);
lean_dec_ref(v_scope_1504_);
lean_dec(v_name_1503_);
lean_dec_ref(v_remoteUrl_1495_);
v___x_1580_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__3));
v___x_1581_ = lean_string_append(v_name_1492_, v___x_1580_);
v___x_1582_ = lean_string_append(v___x_1581_, v___y_1556_);
lean_dec_ref(v___y_1556_);
v___x_1583_ = 3;
v___x_1584_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1584_, 0, v___x_1582_);
lean_ctor_set_uint8(v___x_1584_, sizeof(void*)*1, v___x_1583_);
lean_inc_ref(v_a_1487_);
v___x_1585_ = lean_apply_2(v_a_1487_, v___x_1584_, lean_box(0));
v___x_1586_ = lean_box(0);
v___x_1587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1587_, 0, v___x_1586_);
return v___x_1587_;
}
}
v___jp_1588_:
{
lean_object* v___x_1595_; uint8_t v___x_1596_; 
v___x_1595_ = lean_array_get_size(v___y_1591_);
v___x_1596_ = lean_nat_dec_lt(v___y_1592_, v___x_1595_);
if (v___x_1596_ == 0)
{
v___y_1554_ = v___y_1589_;
v___y_1555_ = v___y_1590_;
v___y_1556_ = v___y_1593_;
v_a_1557_ = v_val_1594_;
goto v___jp_1553_;
}
else
{
lean_object* v___x_1597_; uint8_t v___x_1598_; 
v___x_1597_ = lean_box(0);
v___x_1598_ = lean_nat_dec_le(v___x_1595_, v___x_1595_);
if (v___x_1598_ == 0)
{
if (v___x_1596_ == 0)
{
v___y_1554_ = v___y_1589_;
v___y_1555_ = v___y_1590_;
v___y_1556_ = v___y_1593_;
v_a_1557_ = v_val_1594_;
goto v___jp_1553_;
}
else
{
size_t v___x_1599_; size_t v___x_1600_; lean_object* v___x_1601_; 
v___x_1599_ = ((size_t)0ULL);
v___x_1600_ = lean_usize_of_nat(v___x_1595_);
v___x_1601_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_1591_, v___x_1599_, v___x_1600_, v___x_1597_, v_a_1487_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_dec_ref_known(v___x_1601_, 1);
v___y_1554_ = v___y_1589_;
v___y_1555_ = v___y_1590_;
v___y_1556_ = v___y_1593_;
v_a_1557_ = v_val_1594_;
goto v___jp_1553_;
}
else
{
lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1609_; 
lean_dec(v_val_1594_);
lean_dec_ref(v___y_1593_);
lean_dec_ref(v___y_1590_);
lean_dec_ref(v___y_1589_);
lean_del_object(v___x_1506_);
lean_dec_ref(v_scope_1504_);
lean_dec(v_name_1503_);
lean_dec_ref(v_remoteUrl_1495_);
lean_dec_ref(v_name_1492_);
v_a_1602_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1604_ = v___x_1601_;
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_dec(v___x_1601_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1607_; 
if (v_isShared_1605_ == 0)
{
v___x_1607_ = v___x_1604_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_a_1602_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
}
}
else
{
size_t v___x_1610_; size_t v___x_1611_; lean_object* v___x_1612_; 
v___x_1610_ = ((size_t)0ULL);
v___x_1611_ = lean_usize_of_nat(v___x_1595_);
v___x_1612_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_1591_, v___x_1610_, v___x_1611_, v___x_1597_, v_a_1487_);
if (lean_obj_tag(v___x_1612_) == 0)
{
lean_dec_ref_known(v___x_1612_, 1);
v___y_1554_ = v___y_1589_;
v___y_1555_ = v___y_1590_;
v___y_1556_ = v___y_1593_;
v_a_1557_ = v_val_1594_;
goto v___jp_1553_;
}
else
{
lean_object* v_a_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1620_; 
lean_dec(v_val_1594_);
lean_dec_ref(v___y_1593_);
lean_dec_ref(v___y_1590_);
lean_dec_ref(v___y_1589_);
lean_del_object(v___x_1506_);
lean_dec_ref(v_scope_1504_);
lean_dec(v_name_1503_);
lean_dec_ref(v_remoteUrl_1495_);
lean_dec_ref(v_name_1492_);
v_a_1613_ = lean_ctor_get(v___x_1612_, 0);
v_isSharedCheck_1620_ = !lean_is_exclusive(v___x_1612_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1615_ = v___x_1612_;
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_a_1613_);
lean_dec(v___x_1612_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v___x_1618_; 
if (v_isShared_1616_ == 0)
{
v___x_1618_ = v___x_1615_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_a_1613_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
return v___x_1618_;
}
}
}
}
}
}
v___jp_1621_:
{
lean_object* v_pkgDir_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; uint8_t v___x_1631_; 
lean_inc_ref(v___y_1624_);
v_pkgDir_1625_ = l_Lake_joinRelative(v_wsDir_1491_, v___y_1624_);
lean_inc_ref(v_pkgDir_1625_);
v___x_1626_ = l_Lake_resolvePath(v_pkgDir_1625_);
v___x_1627_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1627_, 0, v___y_1622_);
lean_ctor_set(v___x_1627_, 1, v___y_1623_);
lean_ctor_set(v___x_1627_, 2, v_inputRev_x3f_1496_);
lean_ctor_set(v___x_1627_, 3, v_subDir_x3f_1497_);
v___x_1628_ = lean_unsigned_to_nat(0u);
v___x_1629_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_1630_ = lean_string_utf8_byte_size(v___x_1626_);
v___x_1631_ = lean_nat_dec_eq(v___x_1630_, v___x_1628_);
if (v___x_1631_ == 0)
{
lean_object* v___x_1632_; 
v___x_1632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1626_);
v___y_1589_ = v___y_1624_;
v___y_1590_ = v___x_1627_;
v___y_1591_ = v___x_1629_;
v___y_1592_ = v___x_1628_;
v___y_1593_ = v_pkgDir_1625_;
v_val_1594_ = v___x_1632_;
goto v___jp_1588_;
}
else
{
lean_object* v___x_1633_; 
lean_dec_ref(v___x_1626_);
v___x_1633_ = lean_box(0);
v___y_1589_ = v___y_1624_;
v___y_1590_ = v___x_1627_;
v___y_1591_ = v___x_1629_;
v___y_1592_ = v___x_1628_;
v___y_1593_ = v_pkgDir_1625_;
v_val_1594_ = v___x_1633_;
goto v___jp_1588_;
}
}
v___jp_1634_:
{
if (lean_obj_tag(v_subDir_x3f_1497_) == 1)
{
lean_object* v_val_1637_; lean_object* v___x_1638_; 
v_val_1637_ = lean_ctor_get(v_subDir_x3f_1497_, 0);
lean_inc(v_val_1637_);
v___x_1638_ = l_Lake_joinRelative(v_relPkgDir_1493_, v_val_1637_);
v___y_1622_ = v___y_1635_;
v___y_1623_ = v_a_1636_;
v___y_1624_ = v___x_1638_;
goto v___jp_1621_;
}
else
{
v___y_1622_ = v___y_1635_;
v___y_1623_ = v_a_1636_;
v___y_1624_ = v_relPkgDir_1493_;
goto v___jp_1621_;
}
}
v___jp_1640_:
{
lean_object* v___x_1642_; 
lean_inc(v_inputRev_x3f_1496_);
lean_inc_ref(v___y_1641_);
lean_inc_ref(v_gitDir_1639_);
lean_inc_ref(v_name_1492_);
v___x_1642_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(v_a_1487_, v_name_1492_, v_gitDir_1639_, v___y_1641_, v_inputRev_x3f_1496_);
if (lean_obj_tag(v___x_1642_) == 0)
{
lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1708_; 
v_isSharedCheck_1708_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1708_ == 0)
{
lean_object* v_unused_1709_; 
v_unused_1709_ = lean_ctor_get(v___x_1642_, 0);
lean_dec(v_unused_1709_);
v___x_1644_ = v___x_1642_;
v_isShared_1645_ = v_isSharedCheck_1708_;
goto v_resetjp_1643_;
}
else
{
lean_dec(v___x_1642_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1708_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; 
v___x_1646_ = lean_unsigned_to_nat(0u);
v___x_1647_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_1648_ = l_Lake_GitRepo_getHeadRevision(v_gitDir_1639_, v___x_1647_);
if (lean_obj_tag(v___x_1648_) == 0)
{
lean_object* v_a_1649_; lean_object* v_a_1650_; lean_object* v___x_1651_; uint8_t v___x_1652_; 
lean_del_object(v___x_1644_);
v_a_1649_ = lean_ctor_get(v___x_1648_, 0);
lean_inc(v_a_1649_);
v_a_1650_ = lean_ctor_get(v___x_1648_, 1);
lean_inc(v_a_1650_);
lean_dec_ref_known(v___x_1648_, 2);
v___x_1651_ = lean_array_get_size(v_a_1650_);
v___x_1652_ = lean_nat_dec_lt(v___x_1646_, v___x_1651_);
if (v___x_1652_ == 0)
{
lean_dec(v_a_1650_);
v___y_1635_ = v___y_1641_;
v_a_1636_ = v_a_1649_;
goto v___jp_1634_;
}
else
{
lean_object* v___x_1653_; uint8_t v___x_1654_; 
v___x_1653_ = lean_box(0);
v___x_1654_ = lean_nat_dec_le(v___x_1651_, v___x_1651_);
if (v___x_1654_ == 0)
{
if (v___x_1652_ == 0)
{
lean_dec(v_a_1650_);
v___y_1635_ = v___y_1641_;
v_a_1636_ = v_a_1649_;
goto v___jp_1634_;
}
else
{
size_t v___x_1655_; size_t v___x_1656_; lean_object* v___x_1657_; 
v___x_1655_ = ((size_t)0ULL);
v___x_1656_ = lean_usize_of_nat(v___x_1651_);
v___x_1657_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_1650_, v___x_1655_, v___x_1656_, v___x_1653_, v_a_1487_);
lean_dec(v_a_1650_);
if (lean_obj_tag(v___x_1657_) == 0)
{
lean_dec_ref_known(v___x_1657_, 1);
v___y_1635_ = v___y_1641_;
v_a_1636_ = v_a_1649_;
goto v___jp_1634_;
}
else
{
lean_object* v_a_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1665_; 
lean_dec(v_a_1649_);
lean_dec_ref(v___y_1641_);
lean_del_object(v___x_1506_);
lean_dec_ref(v_scope_1504_);
lean_dec(v_name_1503_);
lean_dec(v_subDir_x3f_1497_);
lean_dec(v_inputRev_x3f_1496_);
lean_dec_ref(v_remoteUrl_1495_);
lean_dec_ref(v_relPkgDir_1493_);
lean_dec_ref(v_name_1492_);
lean_dec_ref(v_wsDir_1491_);
v_a_1658_ = lean_ctor_get(v___x_1657_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1660_ = v___x_1657_;
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_a_1658_);
lean_dec(v___x_1657_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1663_; 
if (v_isShared_1661_ == 0)
{
v___x_1663_ = v___x_1660_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v_a_1658_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
}
}
}
else
{
size_t v___x_1666_; size_t v___x_1667_; lean_object* v___x_1668_; 
v___x_1666_ = ((size_t)0ULL);
v___x_1667_ = lean_usize_of_nat(v___x_1651_);
v___x_1668_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_1650_, v___x_1666_, v___x_1667_, v___x_1653_, v_a_1487_);
lean_dec(v_a_1650_);
if (lean_obj_tag(v___x_1668_) == 0)
{
lean_dec_ref_known(v___x_1668_, 1);
v___y_1635_ = v___y_1641_;
v_a_1636_ = v_a_1649_;
goto v___jp_1634_;
}
else
{
lean_object* v_a_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1676_; 
lean_dec(v_a_1649_);
lean_dec_ref(v___y_1641_);
lean_del_object(v___x_1506_);
lean_dec_ref(v_scope_1504_);
lean_dec(v_name_1503_);
lean_dec(v_subDir_x3f_1497_);
lean_dec(v_inputRev_x3f_1496_);
lean_dec_ref(v_remoteUrl_1495_);
lean_dec_ref(v_relPkgDir_1493_);
lean_dec_ref(v_name_1492_);
lean_dec_ref(v_wsDir_1491_);
v_a_1669_ = lean_ctor_get(v___x_1668_, 0);
v_isSharedCheck_1676_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1671_ = v___x_1668_;
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_a_1669_);
lean_dec(v___x_1668_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1674_; 
if (v_isShared_1672_ == 0)
{
v___x_1674_ = v___x_1671_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v_a_1669_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
return v___x_1674_;
}
}
}
}
}
}
else
{
lean_object* v_a_1677_; lean_object* v___x_1678_; uint8_t v___x_1679_; 
lean_dec_ref(v___y_1641_);
lean_del_object(v___x_1506_);
lean_dec_ref(v_scope_1504_);
lean_dec(v_name_1503_);
lean_dec(v_subDir_x3f_1497_);
lean_dec(v_inputRev_x3f_1496_);
lean_dec_ref(v_remoteUrl_1495_);
lean_dec_ref(v_relPkgDir_1493_);
lean_dec_ref(v_name_1492_);
lean_dec_ref(v_wsDir_1491_);
v_a_1677_ = lean_ctor_get(v___x_1648_, 1);
lean_inc(v_a_1677_);
lean_dec_ref_known(v___x_1648_, 2);
v___x_1678_ = lean_array_get_size(v_a_1677_);
v___x_1679_ = lean_nat_dec_lt(v___x_1646_, v___x_1678_);
if (v___x_1679_ == 0)
{
lean_object* v___x_1680_; lean_object* v___x_1682_; 
lean_dec(v_a_1677_);
v___x_1680_ = lean_box(0);
if (v_isShared_1645_ == 0)
{
lean_ctor_set_tag(v___x_1644_, 1);
lean_ctor_set(v___x_1644_, 0, v___x_1680_);
v___x_1682_ = v___x_1644_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v___x_1680_);
v___x_1682_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
return v___x_1682_;
}
}
else
{
lean_object* v___x_1684_; uint8_t v___x_1685_; 
lean_del_object(v___x_1644_);
v___x_1684_ = lean_box(0);
v___x_1685_ = lean_nat_dec_le(v___x_1678_, v___x_1678_);
if (v___x_1685_ == 0)
{
if (v___x_1679_ == 0)
{
lean_dec(v_a_1677_);
goto v___jp_1499_;
}
else
{
size_t v___x_1686_; size_t v___x_1687_; lean_object* v___x_1688_; 
v___x_1686_ = ((size_t)0ULL);
v___x_1687_ = lean_usize_of_nat(v___x_1678_);
v___x_1688_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_1677_, v___x_1686_, v___x_1687_, v___x_1684_, v_a_1487_);
lean_dec(v_a_1677_);
if (lean_obj_tag(v___x_1688_) == 0)
{
lean_dec_ref_known(v___x_1688_, 1);
goto v___jp_1499_;
}
else
{
lean_object* v_a_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1696_; 
v_a_1689_ = lean_ctor_get(v___x_1688_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1688_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1691_ = v___x_1688_;
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_a_1689_);
lean_dec(v___x_1688_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v___x_1694_; 
if (v_isShared_1692_ == 0)
{
v___x_1694_ = v___x_1691_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_a_1689_);
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
}
else
{
size_t v___x_1697_; size_t v___x_1698_; lean_object* v___x_1699_; 
v___x_1697_ = ((size_t)0ULL);
v___x_1698_ = lean_usize_of_nat(v___x_1678_);
v___x_1699_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_1677_, v___x_1697_, v___x_1698_, v___x_1684_, v_a_1487_);
lean_dec(v_a_1677_);
if (lean_obj_tag(v___x_1699_) == 0)
{
lean_dec_ref_known(v___x_1699_, 1);
goto v___jp_1499_;
}
else
{
lean_object* v_a_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1707_; 
v_a_1700_ = lean_ctor_get(v___x_1699_, 0);
v_isSharedCheck_1707_ = !lean_is_exclusive(v___x_1699_);
if (v_isSharedCheck_1707_ == 0)
{
v___x_1702_ = v___x_1699_;
v_isShared_1703_ = v_isSharedCheck_1707_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_a_1700_);
lean_dec(v___x_1699_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1707_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v___x_1705_; 
if (v_isShared_1703_ == 0)
{
v___x_1705_ = v___x_1702_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v_a_1700_);
v___x_1705_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
return v___x_1705_;
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
lean_object* v_a_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1717_; 
lean_dec_ref(v___y_1641_);
lean_dec_ref(v_gitDir_1639_);
lean_del_object(v___x_1506_);
lean_dec_ref(v_scope_1504_);
lean_dec(v_name_1503_);
lean_dec(v_subDir_x3f_1497_);
lean_dec(v_inputRev_x3f_1496_);
lean_dec_ref(v_remoteUrl_1495_);
lean_dec_ref(v_relPkgDir_1493_);
lean_dec_ref(v_name_1492_);
lean_dec_ref(v_wsDir_1491_);
v_a_1710_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1717_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1717_ == 0)
{
v___x_1712_ = v___x_1642_;
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_a_1710_);
lean_dec(v___x_1642_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v___x_1715_; 
if (v_isShared_1713_ == 0)
{
v___x_1715_ = v___x_1712_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v_a_1710_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0___boxed(lean_object* v_a_1724_, lean_object* v_dep_1725_, lean_object* v_inherited_1726_, lean_object* v_lakeEnv_1727_, lean_object* v_wsDir_1728_, lean_object* v_name_1729_, lean_object* v_relPkgDir_1730_, lean_object* v_gitUrl_1731_, lean_object* v_remoteUrl_1732_, lean_object* v_inputRev_x3f_1733_, lean_object* v_subDir_x3f_1734_, lean_object* v_a_1735_){
_start:
{
uint8_t v_inherited_boxed_1736_; lean_object* v_res_1737_; 
v_inherited_boxed_1736_ = lean_unbox(v_inherited_1726_);
v_res_1737_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(v_a_1724_, v_dep_1725_, v_inherited_boxed_1736_, v_lakeEnv_1727_, v_wsDir_1728_, v_name_1729_, v_relPkgDir_1730_, v_gitUrl_1731_, v_remoteUrl_1732_, v_inputRev_x3f_1733_, v_subDir_x3f_1734_);
lean_dec_ref(v_lakeEnv_1727_);
lean_dec_ref(v_a_1724_);
return v_res_1737_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(lean_object* v_ver_1741_, lean_object* v_as_1742_, size_t v_sz_1743_, size_t v_i_1744_, lean_object* v_b_1745_){
_start:
{
uint8_t v___x_1746_; 
v___x_1746_ = lean_usize_dec_lt(v_i_1744_, v_sz_1743_);
if (v___x_1746_ == 0)
{
lean_inc_ref(v_b_1745_);
return v_b_1745_;
}
else
{
lean_object* v_a_1747_; lean_object* v_version_1748_; lean_object* v___x_1749_; uint8_t v___x_1750_; 
v_a_1747_ = lean_array_uget_borrowed(v_as_1742_, v_i_1744_);
v_version_1748_ = lean_ctor_get(v_a_1747_, 0);
v___x_1749_ = lean_box(0);
v___x_1750_ = l_Lake_VerRange_test(v_ver_1741_, v_version_1748_);
if (v___x_1750_ == 0)
{
lean_object* v___x_1751_; size_t v___x_1752_; size_t v___x_1753_; 
v___x_1751_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___closed__0));
v___x_1752_ = ((size_t)1ULL);
v___x_1753_ = lean_usize_add(v_i_1744_, v___x_1752_);
v_i_1744_ = v___x_1753_;
v_b_1745_ = v___x_1751_;
goto _start;
}
else
{
lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; 
lean_inc(v_a_1747_);
v___x_1755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1755_, 0, v_a_1747_);
v___x_1756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1755_);
v___x_1757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1757_, 0, v___x_1756_);
lean_ctor_set(v___x_1757_, 1, v___x_1749_);
return v___x_1757_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___boxed(lean_object* v_ver_1758_, lean_object* v_as_1759_, lean_object* v_sz_1760_, lean_object* v_i_1761_, lean_object* v_b_1762_){
_start:
{
size_t v_sz_boxed_1763_; size_t v_i_boxed_1764_; lean_object* v_res_1765_; 
v_sz_boxed_1763_ = lean_unbox_usize(v_sz_1760_);
lean_dec(v_sz_1760_);
v_i_boxed_1764_ = lean_unbox_usize(v_i_1761_);
lean_dec(v_i_1761_);
v_res_1765_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(v_ver_1758_, v_as_1759_, v_sz_boxed_1763_, v_i_boxed_1764_, v_b_1762_);
lean_dec_ref(v_b_1762_);
lean_dec_ref(v_as_1759_);
lean_dec_ref(v_ver_1758_);
return v_res_1765_;
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize(lean_object* v_dep_1775_, uint8_t v_inherited_1776_, lean_object* v_lakeEnv_1777_, lean_object* v_wsDir_1778_, lean_object* v_relPkgsDir_1779_, lean_object* v_relParentDir_1780_, lean_object* v_a_1781_){
_start:
{
lean_object* v___y_1787_; lean_object* v___y_1788_; lean_object* v___y_1798_; lean_object* v___y_1799_; lean_object* v___y_1800_; lean_object* v___y_1801_; lean_object* v___y_1802_; lean_object* v___y_1803_; lean_object* v___y_1807_; lean_object* v___y_1808_; lean_object* v___y_1809_; lean_object* v___y_1810_; lean_object* v___y_1811_; lean_object* v_a_1812_; lean_object* v_src_x3f_1815_; 
v_src_x3f_1815_ = lean_ctor_get(v_dep_1775_, 3);
lean_inc(v_src_x3f_1815_);
if (lean_obj_tag(v_src_x3f_1815_) == 1)
{
lean_object* v_val_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1964_; 
v_val_1816_ = lean_ctor_get(v_src_x3f_1815_, 0);
v_isSharedCheck_1964_ = !lean_is_exclusive(v_src_x3f_1815_);
if (v_isSharedCheck_1964_ == 0)
{
v___x_1818_ = v_src_x3f_1815_;
v_isShared_1819_ = v_isSharedCheck_1964_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_val_1816_);
lean_dec(v_src_x3f_1815_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1964_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
if (lean_obj_tag(v_val_1816_) == 0)
{
lean_object* v_name_1820_; lean_object* v_scope_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1947_; 
lean_dec_ref(v_relPkgsDir_1779_);
lean_dec_ref(v_lakeEnv_1777_);
v_name_1820_ = lean_ctor_get(v_dep_1775_, 0);
v_scope_1821_ = lean_ctor_get(v_dep_1775_, 1);
v_isSharedCheck_1947_ = !lean_is_exclusive(v_dep_1775_);
if (v_isSharedCheck_1947_ == 0)
{
lean_object* v_unused_1948_; lean_object* v_unused_1949_; lean_object* v_unused_1950_; 
v_unused_1948_ = lean_ctor_get(v_dep_1775_, 4);
lean_dec(v_unused_1948_);
v_unused_1949_ = lean_ctor_get(v_dep_1775_, 3);
lean_dec(v_unused_1949_);
v_unused_1950_ = lean_ctor_get(v_dep_1775_, 2);
lean_dec(v_unused_1950_);
v___x_1823_ = v_dep_1775_;
v_isShared_1824_ = v_isSharedCheck_1947_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_scope_1821_);
lean_inc(v_name_1820_);
lean_dec(v_dep_1775_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1947_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v_dir_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1946_; 
v_dir_1825_ = lean_ctor_get(v_val_1816_, 0);
v_isSharedCheck_1946_ = !lean_is_exclusive(v_val_1816_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1827_ = v_val_1816_;
v_isShared_1828_ = v_isSharedCheck_1946_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_dir_1825_);
lean_dec(v_val_1816_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1946_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v_relPkgDir_1829_; lean_object* v___x_1831_; 
v_relPkgDir_1829_ = l_Lake_joinRelative(v_relParentDir_1780_, v_dir_1825_);
lean_inc_ref(v_relPkgDir_1829_);
if (v_isShared_1828_ == 0)
{
lean_ctor_set(v___x_1827_, 0, v_relPkgDir_1829_);
v___x_1831_ = v___x_1827_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_relPkgDir_1829_);
v___x_1831_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
lean_object* v_pkgDir_1832_; lean_object* v___x_1833_; uint8_t v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___y_1838_; lean_object* v_a_1839_; lean_object* v___y_1848_; lean_object* v___y_1849_; lean_object* v___y_1850_; lean_object* v_val_1851_; lean_object* v_a_1879_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v_val_1913_; lean_object* v___x_1939_; uint8_t v___x_1940_; 
lean_inc_ref(v_relPkgDir_1829_);
v_pkgDir_1832_ = l_Lake_joinRelative(v_wsDir_1778_, v_relPkgDir_1829_);
lean_inc_ref(v_pkgDir_1832_);
v___x_1833_ = l_Lake_resolvePath(v_pkgDir_1832_);
v___x_1834_ = 0;
lean_inc(v_name_1820_);
v___x_1835_ = l_Lean_Name_toString(v_name_1820_, v___x_1834_);
v___x_1836_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___x_1910_ = lean_unsigned_to_nat(0u);
v___x_1911_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_1939_ = lean_string_utf8_byte_size(v___x_1833_);
v___x_1940_ = lean_nat_dec_eq(v___x_1939_, v___x_1910_);
if (v___x_1940_ == 0)
{
lean_object* v___x_1942_; 
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 0, v___x_1833_);
v___x_1942_ = v___x_1818_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v___x_1833_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
v_val_1913_ = v___x_1942_;
goto v___jp_1912_;
}
}
else
{
lean_object* v___x_1944_; 
lean_dec_ref(v___x_1833_);
lean_del_object(v___x_1818_);
v___x_1944_ = lean_box(0);
v_val_1913_ = v___x_1944_;
goto v___jp_1912_;
}
v___jp_1837_:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1844_; 
v___x_1840_ = l_Lake_defaultConfigFile;
v___x_1841_ = lean_box(0);
v___x_1842_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1842_, 0, v_name_1820_);
lean_ctor_set(v___x_1842_, 1, v_scope_1821_);
lean_ctor_set(v___x_1842_, 2, v___x_1840_);
lean_ctor_set(v___x_1842_, 3, v___x_1841_);
lean_ctor_set(v___x_1842_, 4, v___x_1831_);
lean_ctor_set_uint8(v___x_1842_, sizeof(void*)*5, v_inherited_1776_);
if (v_isShared_1824_ == 0)
{
lean_ctor_set(v___x_1823_, 4, v___x_1842_);
lean_ctor_set(v___x_1823_, 3, v_a_1839_);
lean_ctor_set(v___x_1823_, 2, v___x_1836_);
lean_ctor_set(v___x_1823_, 1, v_relPkgDir_1829_);
lean_ctor_set(v___x_1823_, 0, v___y_1838_);
v___x_1844_ = v___x_1823_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v___y_1838_);
lean_ctor_set(v_reuseFailAlloc_1846_, 1, v_relPkgDir_1829_);
lean_ctor_set(v_reuseFailAlloc_1846_, 2, v___x_1836_);
lean_ctor_set(v_reuseFailAlloc_1846_, 3, v_a_1839_);
lean_ctor_set(v_reuseFailAlloc_1846_, 4, v___x_1842_);
v___x_1844_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
lean_object* v___x_1845_; 
v___x_1845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1845_, 0, v___x_1844_);
return v___x_1845_;
}
}
v___jp_1847_:
{
lean_object* v___x_1852_; uint8_t v___x_1853_; 
v___x_1852_ = lean_array_get_size(v___y_1850_);
v___x_1853_ = lean_nat_dec_lt(v___y_1849_, v___x_1852_);
if (v___x_1853_ == 0)
{
v___y_1838_ = v___y_1848_;
v_a_1839_ = v_val_1851_;
goto v___jp_1837_;
}
else
{
lean_object* v___x_1854_; uint8_t v___x_1855_; 
v___x_1854_ = lean_box(0);
v___x_1855_ = lean_nat_dec_le(v___x_1852_, v___x_1852_);
if (v___x_1855_ == 0)
{
if (v___x_1853_ == 0)
{
v___y_1838_ = v___y_1848_;
v_a_1839_ = v_val_1851_;
goto v___jp_1837_;
}
else
{
size_t v___x_1856_; size_t v___x_1857_; lean_object* v___x_1858_; 
v___x_1856_ = ((size_t)0ULL);
v___x_1857_ = lean_usize_of_nat(v___x_1852_);
v___x_1858_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_1850_, v___x_1856_, v___x_1857_, v___x_1854_, v_a_1781_);
if (lean_obj_tag(v___x_1858_) == 0)
{
lean_dec_ref_known(v___x_1858_, 1);
v___y_1838_ = v___y_1848_;
v_a_1839_ = v_val_1851_;
goto v___jp_1837_;
}
else
{
lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1866_; 
lean_dec_ref(v_val_1851_);
lean_dec_ref(v___y_1848_);
lean_dec_ref(v___x_1831_);
lean_dec_ref(v_relPkgDir_1829_);
lean_del_object(v___x_1823_);
lean_dec_ref(v_scope_1821_);
lean_dec(v_name_1820_);
v_a_1859_ = lean_ctor_get(v___x_1858_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1858_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1861_ = v___x_1858_;
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_dec(v___x_1858_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1864_; 
if (v_isShared_1862_ == 0)
{
v___x_1864_ = v___x_1861_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_a_1859_);
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
size_t v___x_1867_; size_t v___x_1868_; lean_object* v___x_1869_; 
v___x_1867_ = ((size_t)0ULL);
v___x_1868_ = lean_usize_of_nat(v___x_1852_);
v___x_1869_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_1850_, v___x_1867_, v___x_1868_, v___x_1854_, v_a_1781_);
if (lean_obj_tag(v___x_1869_) == 0)
{
lean_dec_ref_known(v___x_1869_, 1);
v___y_1838_ = v___y_1848_;
v_a_1839_ = v_val_1851_;
goto v___jp_1837_;
}
else
{
lean_object* v_a_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1877_; 
lean_dec_ref(v_val_1851_);
lean_dec_ref(v___y_1848_);
lean_dec_ref(v___x_1831_);
lean_dec_ref(v_relPkgDir_1829_);
lean_del_object(v___x_1823_);
lean_dec_ref(v_scope_1821_);
lean_dec(v_name_1820_);
v_a_1870_ = lean_ctor_get(v___x_1869_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1869_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1872_ = v___x_1869_;
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_a_1870_);
lean_dec(v___x_1869_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1875_; 
if (v_isShared_1873_ == 0)
{
v___x_1875_ = v___x_1872_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_a_1870_);
v___x_1875_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
return v___x_1875_;
}
}
}
}
}
}
v___jp_1878_:
{
if (lean_obj_tag(v_a_1879_) == 1)
{
lean_object* v_val_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; 
lean_dec_ref(v___x_1835_);
lean_dec_ref(v_pkgDir_1832_);
v_val_1880_ = lean_ctor_get(v_a_1879_, 0);
lean_inc_n(v_val_1880_, 2);
lean_dec_ref_known(v_a_1879_, 1);
v___x_1881_ = l_Lake_defaultManifestFile;
v___x_1882_ = l_Lake_joinRelative(v_val_1880_, v___x_1881_);
v___x_1883_ = lean_unsigned_to_nat(0u);
v___x_1884_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_1885_ = l_Lake_Manifest_load(v___x_1882_);
if (lean_obj_tag(v___x_1885_) == 0)
{
lean_object* v_a_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1893_; 
v_a_1886_ = lean_ctor_get(v___x_1885_, 0);
v_isSharedCheck_1893_ = !lean_is_exclusive(v___x_1885_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1888_ = v___x_1885_;
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_a_1886_);
lean_dec(v___x_1885_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___x_1891_; 
if (v_isShared_1889_ == 0)
{
lean_ctor_set_tag(v___x_1888_, 1);
v___x_1891_ = v___x_1888_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_a_1886_);
v___x_1891_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
v___y_1848_ = v_val_1880_;
v___y_1849_ = v___x_1883_;
v___y_1850_ = v___x_1884_;
v_val_1851_ = v___x_1891_;
goto v___jp_1847_;
}
}
}
else
{
lean_object* v_a_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1901_; 
v_a_1894_ = lean_ctor_get(v___x_1885_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v___x_1885_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1896_ = v___x_1885_;
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_a_1894_);
lean_dec(v___x_1885_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1899_; 
if (v_isShared_1897_ == 0)
{
lean_ctor_set_tag(v___x_1896_, 0);
v___x_1899_ = v___x_1896_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v_a_1894_);
v___x_1899_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
v___y_1848_ = v_val_1880_;
v___y_1849_ = v___x_1883_;
v___y_1850_ = v___x_1884_;
v_val_1851_ = v___x_1899_;
goto v___jp_1847_;
}
}
}
}
else
{
lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; uint8_t v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; 
lean_dec(v_a_1879_);
lean_dec_ref(v___x_1831_);
lean_dec_ref(v_relPkgDir_1829_);
lean_del_object(v___x_1823_);
lean_dec_ref(v_scope_1821_);
lean_dec(v_name_1820_);
v___x_1902_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__3));
v___x_1903_ = lean_string_append(v___x_1835_, v___x_1902_);
v___x_1904_ = lean_string_append(v___x_1903_, v_pkgDir_1832_);
lean_dec_ref(v_pkgDir_1832_);
v___x_1905_ = 3;
v___x_1906_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1906_, 0, v___x_1904_);
lean_ctor_set_uint8(v___x_1906_, sizeof(void*)*1, v___x_1905_);
lean_inc_ref(v_a_1781_);
v___x_1907_ = lean_apply_2(v_a_1781_, v___x_1906_, lean_box(0));
v___x_1908_ = lean_box(0);
v___x_1909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1909_, 0, v___x_1908_);
return v___x_1909_;
}
}
v___jp_1912_:
{
uint8_t v___x_1914_; 
v___x_1914_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_1914_ == 0)
{
v_a_1879_ = v_val_1913_;
goto v___jp_1878_;
}
else
{
lean_object* v___x_1915_; uint8_t v___x_1916_; 
v___x_1915_ = lean_box(0);
v___x_1916_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_1916_ == 0)
{
if (v___x_1914_ == 0)
{
v_a_1879_ = v_val_1913_;
goto v___jp_1878_;
}
else
{
size_t v___x_1917_; size_t v___x_1918_; lean_object* v___x_1919_; 
v___x_1917_ = ((size_t)0ULL);
v___x_1918_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_1919_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_1911_, v___x_1917_, v___x_1918_, v___x_1915_, v_a_1781_);
if (lean_obj_tag(v___x_1919_) == 0)
{
lean_dec_ref_known(v___x_1919_, 1);
v_a_1879_ = v_val_1913_;
goto v___jp_1878_;
}
else
{
lean_object* v_a_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1927_; 
lean_dec(v_val_1913_);
lean_dec_ref(v___x_1835_);
lean_dec_ref(v_pkgDir_1832_);
lean_dec_ref(v___x_1831_);
lean_dec_ref(v_relPkgDir_1829_);
lean_del_object(v___x_1823_);
lean_dec_ref(v_scope_1821_);
lean_dec(v_name_1820_);
v_a_1920_ = lean_ctor_get(v___x_1919_, 0);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1922_ = v___x_1919_;
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_a_1920_);
lean_dec(v___x_1919_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1925_; 
if (v_isShared_1923_ == 0)
{
v___x_1925_ = v___x_1922_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v_a_1920_);
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
}
else
{
size_t v___x_1928_; size_t v___x_1929_; lean_object* v___x_1930_; 
v___x_1928_ = ((size_t)0ULL);
v___x_1929_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_1930_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_1911_, v___x_1928_, v___x_1929_, v___x_1915_, v_a_1781_);
if (lean_obj_tag(v___x_1930_) == 0)
{
lean_dec_ref_known(v___x_1930_, 1);
v_a_1879_ = v_val_1913_;
goto v___jp_1878_;
}
else
{
lean_object* v_a_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1938_; 
lean_dec(v_val_1913_);
lean_dec_ref(v___x_1835_);
lean_dec_ref(v_pkgDir_1832_);
lean_dec_ref(v___x_1831_);
lean_dec_ref(v_relPkgDir_1829_);
lean_del_object(v___x_1823_);
lean_dec_ref(v_scope_1821_);
lean_dec(v_name_1820_);
v_a_1931_ = lean_ctor_get(v___x_1930_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1930_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1933_ = v___x_1930_;
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_a_1931_);
lean_dec(v___x_1930_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___x_1936_; 
if (v_isShared_1934_ == 0)
{
v___x_1936_ = v___x_1933_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_a_1931_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
return v___x_1936_;
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
lean_object* v_name_1951_; lean_object* v_url_1952_; lean_object* v_rev_1953_; lean_object* v_subDir_1954_; lean_object* v___y_1956_; lean_object* v___x_1961_; 
lean_del_object(v___x_1818_);
lean_dec_ref(v_relParentDir_1780_);
v_name_1951_ = lean_ctor_get(v_dep_1775_, 0);
v_url_1952_ = lean_ctor_get(v_val_1816_, 0);
lean_inc_ref_n(v_url_1952_, 2);
v_rev_1953_ = lean_ctor_get(v_val_1816_, 1);
lean_inc(v_rev_1953_);
v_subDir_1954_ = lean_ctor_get(v_val_1816_, 2);
lean_inc(v_subDir_1954_);
lean_dec_ref_known(v_val_1816_, 3);
v___x_1961_ = l_Lake_Git_filterUrl_x3f(v_url_1952_);
if (lean_obj_tag(v___x_1961_) == 0)
{
lean_object* v___x_1962_; 
v___x_1962_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___y_1956_ = v___x_1962_;
goto v___jp_1955_;
}
else
{
lean_object* v_val_1963_; 
v_val_1963_ = lean_ctor_get(v___x_1961_, 0);
lean_inc(v_val_1963_);
lean_dec_ref_known(v___x_1961_, 1);
v___y_1956_ = v_val_1963_;
goto v___jp_1955_;
}
v___jp_1955_:
{
uint8_t v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___x_1957_ = 0;
lean_inc(v_name_1951_);
v___x_1958_ = l_Lean_Name_toString(v_name_1951_, v___x_1957_);
lean_inc_ref(v___x_1958_);
v___x_1959_ = l_Lake_joinRelative(v_relPkgsDir_1779_, v___x_1958_);
v___x_1960_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(v_a_1781_, v_dep_1775_, v_inherited_1776_, v_lakeEnv_1777_, v_wsDir_1778_, v___x_1958_, v___x_1959_, v_url_1952_, v___y_1956_, v_rev_1953_, v_subDir_1954_);
lean_dec_ref(v_lakeEnv_1777_);
return v___x_1960_;
}
}
}
}
else
{
lean_object* v_name_1965_; lean_object* v_scope_1966_; lean_object* v_version_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; uint8_t v___x_1970_; 
lean_dec(v_src_x3f_1815_);
lean_dec_ref(v_relParentDir_1780_);
v_name_1965_ = lean_ctor_get(v_dep_1775_, 0);
v_scope_1966_ = lean_ctor_get(v_dep_1775_, 1);
v_version_1967_ = lean_ctor_get(v_dep_1775_, 2);
v___x_1968_ = lean_string_utf8_byte_size(v_scope_1966_);
v___x_1969_ = lean_unsigned_to_nat(0u);
v___x_1970_ = lean_nat_dec_eq(v___x_1968_, v___x_1969_);
if (v___x_1970_ == 0)
{
lean_object* v___x_1971_; lean_object* v___y_1973_; lean_object* v___y_1989_; lean_object* v___y_1990_; lean_object* v___y_1991_; lean_object* v___y_1992_; lean_object* v___y_1993_; lean_object* v___y_1994_; lean_object* v_a_1995_; lean_object* v___y_2039_; lean_object* v___y_2040_; lean_object* v___y_2041_; lean_object* v___y_2042_; lean_object* v___y_2043_; lean_object* v___y_2044_; lean_object* v_fst_2045_; lean_object* v_snd_2046_; lean_object* v_a_2074_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v_fst_2209_; lean_object* v_snd_2210_; 
lean_inc(v_name_1965_);
v___x_1971_ = l_Lean_Name_toString(v_name_1965_, v___x_1970_);
v___x_2206_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
lean_inc_ref(v___x_1971_);
lean_inc_ref(v_scope_1966_);
lean_inc_ref(v_lakeEnv_1777_);
v___x_2207_ = l_Lake_Reservoir_fetchPkg_x3f(v_lakeEnv_1777_, v_scope_1966_, v___x_1971_, v___x_2206_);
if (lean_obj_tag(v___x_2207_) == 0)
{
lean_object* v_a_2237_; lean_object* v_a_2238_; lean_object* v___x_2239_; 
v_a_2237_ = lean_ctor_get(v___x_2207_, 0);
lean_inc(v_a_2237_);
v_a_2238_ = lean_ctor_get(v___x_2207_, 1);
lean_inc(v_a_2238_);
lean_dec_ref_known(v___x_2207_, 2);
v___x_2239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2239_, 0, v_a_2237_);
v_fst_2209_ = v___x_2239_;
v_snd_2210_ = v_a_2238_;
goto v___jp_2208_;
}
else
{
lean_object* v_a_2240_; lean_object* v_a_2241_; lean_object* v___x_2242_; 
v_a_2240_ = lean_ctor_get(v___x_2207_, 0);
lean_inc(v_a_2240_);
v_a_2241_ = lean_ctor_get(v___x_2207_, 1);
lean_inc(v_a_2241_);
lean_dec_ref_known(v___x_2207_, 2);
v___x_2242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2242_, 0, v_a_2240_);
v_fst_2209_ = v___x_2242_;
v_snd_2210_ = v_a_2241_;
goto v___jp_2208_;
}
v___jp_1972_:
{
lean_object* v_toString_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; uint8_t v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; 
v_toString_1974_ = lean_ctor_get(v___y_1973_, 0);
lean_inc_ref(v_toString_1974_);
lean_dec_ref(v___y_1973_);
v___x_1975_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
v___x_1976_ = lean_string_append(v_scope_1966_, v___x_1975_);
v___x_1977_ = lean_string_append(v___x_1976_, v___x_1971_);
lean_dec_ref(v___x_1971_);
v___x_1978_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__1));
v___x_1979_ = lean_string_append(v___x_1977_, v___x_1978_);
v___x_1980_ = lean_string_append(v___x_1979_, v_toString_1974_);
lean_dec_ref(v_toString_1974_);
v___x_1981_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__2));
v___x_1982_ = lean_string_append(v___x_1980_, v___x_1981_);
v___x_1983_ = 3;
v___x_1984_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1984_, 0, v___x_1982_);
lean_ctor_set_uint8(v___x_1984_, sizeof(void*)*1, v___x_1983_);
lean_inc_ref(v_a_1781_);
v___x_1985_ = lean_apply_2(v_a_1781_, v___x_1984_, lean_box(0));
v___x_1986_ = lean_box(0);
v___x_1987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1987_, 0, v___x_1986_);
return v___x_1987_;
}
v___jp_1988_:
{
if (lean_obj_tag(v_a_1995_) == 0)
{
lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2011_; 
lean_inc_ref(v_scope_1966_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
lean_dec(v___y_1992_);
lean_dec_ref(v___y_1991_);
lean_dec_ref(v___y_1990_);
lean_dec_ref(v___y_1989_);
lean_dec_ref(v_wsDir_1778_);
lean_dec_ref(v_lakeEnv_1777_);
lean_dec_ref(v_dep_1775_);
v_isSharedCheck_2011_ = !lean_is_exclusive(v_a_1995_);
if (v_isSharedCheck_2011_ == 0)
{
lean_object* v_unused_2012_; 
v_unused_2012_ = lean_ctor_get(v_a_1995_, 0);
lean_dec(v_unused_2012_);
v___x_1997_ = v_a_1995_;
v_isShared_1998_ = v_isSharedCheck_2011_;
goto v_resetjp_1996_;
}
else
{
lean_dec(v_a_1995_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2011_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; uint8_t v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2009_; 
v___x_1999_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
v___x_2000_ = lean_string_append(v_scope_1966_, v___x_1999_);
v___x_2001_ = lean_string_append(v___x_2000_, v___x_1971_);
lean_dec_ref(v___x_1971_);
v___x_2002_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__3));
v___x_2003_ = lean_string_append(v___x_2001_, v___x_2002_);
v___x_2004_ = 3;
v___x_2005_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2005_, 0, v___x_2003_);
lean_ctor_set_uint8(v___x_2005_, sizeof(void*)*1, v___x_2004_);
lean_inc_ref(v_a_1781_);
v___x_2006_ = lean_apply_2(v_a_1781_, v___x_2005_, lean_box(0));
v___x_2007_ = lean_box(0);
if (v_isShared_1998_ == 0)
{
lean_ctor_set_tag(v___x_1997_, 1);
lean_ctor_set(v___x_1997_, 0, v___x_2007_);
v___x_2009_ = v___x_1997_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v___x_2007_);
v___x_2009_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
return v___x_2009_;
}
}
}
else
{
lean_object* v_a_2013_; lean_object* v___x_2014_; size_t v_sz_2015_; size_t v___x_2016_; lean_object* v___x_2017_; lean_object* v_fst_2018_; 
v_a_2013_ = lean_ctor_get(v_a_1995_, 0);
lean_inc(v_a_2013_);
lean_dec_ref_known(v_a_1995_, 1);
v___x_2014_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___closed__0));
v_sz_2015_ = lean_array_size(v_a_2013_);
v___x_2016_ = ((size_t)0ULL);
v___x_2017_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(v___y_1989_, v_a_2013_, v_sz_2015_, v___x_2016_, v___x_2014_);
lean_dec(v_a_2013_);
v_fst_2018_ = lean_ctor_get(v___x_2017_, 0);
lean_inc(v_fst_2018_);
lean_dec_ref(v___x_2017_);
if (lean_obj_tag(v_fst_2018_) == 0)
{
lean_inc_ref(v_scope_1966_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
lean_dec(v___y_1992_);
lean_dec_ref(v___y_1991_);
lean_dec_ref(v___y_1990_);
lean_dec_ref(v_wsDir_1778_);
lean_dec_ref(v_lakeEnv_1777_);
lean_dec_ref(v_dep_1775_);
v___y_1973_ = v___y_1989_;
goto v___jp_1972_;
}
else
{
lean_object* v_val_2019_; 
v_val_2019_ = lean_ctor_get(v_fst_2018_, 0);
lean_inc(v_val_2019_);
lean_dec_ref_known(v_fst_2018_, 1);
if (lean_obj_tag(v_val_2019_) == 1)
{
lean_object* v_val_2020_; lean_object* v_version_2021_; lean_object* v_revision_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; uint8_t v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; 
lean_dec_ref(v___y_1989_);
v_val_2020_ = lean_ctor_get(v_val_2019_, 0);
lean_inc(v_val_2020_);
lean_dec_ref_known(v_val_2019_, 1);
v_version_2021_ = lean_ctor_get(v_val_2020_, 0);
lean_inc_ref(v_version_2021_);
v_revision_2022_ = lean_ctor_get(v_val_2020_, 1);
lean_inc_ref(v_revision_2022_);
lean_dec(v_val_2020_);
v___x_2023_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
lean_inc_ref(v_scope_1966_);
v___x_2024_ = lean_string_append(v_scope_1966_, v___x_2023_);
v___x_2025_ = lean_string_append(v___x_2024_, v___x_1971_);
lean_dec_ref(v___x_1971_);
v___x_2026_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__4));
v___x_2027_ = lean_string_append(v___x_2025_, v___x_2026_);
v___x_2028_ = l_Lake_StdVer_toString(v_version_2021_);
v___x_2029_ = lean_string_append(v___x_2027_, v___x_2028_);
lean_dec_ref(v___x_2028_);
v___x_2030_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__5));
v___x_2031_ = lean_string_append(v___x_2029_, v___x_2030_);
v___x_2032_ = lean_string_append(v___x_2031_, v_revision_2022_);
v___x_2033_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__6));
v___x_2034_ = lean_string_append(v___x_2032_, v___x_2033_);
v___x_2035_ = 1;
v___x_2036_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2036_, 0, v___x_2034_);
lean_ctor_set_uint8(v___x_2036_, sizeof(void*)*1, v___x_2035_);
lean_inc_ref(v_a_1781_);
v___x_2037_ = lean_apply_2(v_a_1781_, v___x_2036_, lean_box(0));
v___y_1807_ = v___y_1990_;
v___y_1808_ = v___y_1991_;
v___y_1809_ = v___y_1992_;
v___y_1810_ = v___y_1994_;
v___y_1811_ = v___y_1993_;
v_a_1812_ = v_revision_2022_;
goto v___jp_1806_;
}
else
{
lean_inc_ref(v_scope_1966_);
lean_dec(v_val_2019_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
lean_dec(v___y_1992_);
lean_dec_ref(v___y_1991_);
lean_dec_ref(v___y_1990_);
lean_dec_ref(v_wsDir_1778_);
lean_dec_ref(v_lakeEnv_1777_);
lean_dec_ref(v_dep_1775_);
v___y_1973_ = v___y_1989_;
goto v___jp_1972_;
}
}
}
}
v___jp_2038_:
{
lean_object* v___x_2047_; uint8_t v___x_2048_; 
v___x_2047_ = lean_array_get_size(v_snd_2046_);
v___x_2048_ = lean_nat_dec_lt(v___x_1969_, v___x_2047_);
if (v___x_2048_ == 0)
{
lean_dec_ref(v_snd_2046_);
v___y_1989_ = v___y_2039_;
v___y_1990_ = v___y_2040_;
v___y_1991_ = v___y_2041_;
v___y_1992_ = v___y_2042_;
v___y_1993_ = v___y_2044_;
v___y_1994_ = v___y_2043_;
v_a_1995_ = v_fst_2045_;
goto v___jp_1988_;
}
else
{
lean_object* v___x_2049_; uint8_t v___x_2050_; 
v___x_2049_ = lean_box(0);
v___x_2050_ = lean_nat_dec_le(v___x_2047_, v___x_2047_);
if (v___x_2050_ == 0)
{
if (v___x_2048_ == 0)
{
lean_dec_ref(v_snd_2046_);
v___y_1989_ = v___y_2039_;
v___y_1990_ = v___y_2040_;
v___y_1991_ = v___y_2041_;
v___y_1992_ = v___y_2042_;
v___y_1993_ = v___y_2044_;
v___y_1994_ = v___y_2043_;
v_a_1995_ = v_fst_2045_;
goto v___jp_1988_;
}
else
{
size_t v___x_2051_; size_t v___x_2052_; lean_object* v___x_2053_; 
v___x_2051_ = ((size_t)0ULL);
v___x_2052_ = lean_usize_of_nat(v___x_2047_);
v___x_2053_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_snd_2046_, v___x_2051_, v___x_2052_, v___x_2049_, v_a_1781_);
lean_dec_ref(v_snd_2046_);
if (lean_obj_tag(v___x_2053_) == 0)
{
lean_dec_ref_known(v___x_2053_, 1);
v___y_1989_ = v___y_2039_;
v___y_1990_ = v___y_2040_;
v___y_1991_ = v___y_2041_;
v___y_1992_ = v___y_2042_;
v___y_1993_ = v___y_2044_;
v___y_1994_ = v___y_2043_;
v_a_1995_ = v_fst_2045_;
goto v___jp_1988_;
}
else
{
lean_object* v_a_2054_; lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2061_; 
lean_dec_ref(v_fst_2045_);
lean_dec_ref(v___y_2044_);
lean_dec(v___y_2043_);
lean_dec(v___y_2042_);
lean_dec_ref(v___y_2041_);
lean_dec_ref(v___y_2040_);
lean_dec_ref(v___y_2039_);
lean_dec_ref(v___x_1971_);
lean_dec_ref(v_wsDir_1778_);
lean_dec_ref(v_lakeEnv_1777_);
lean_dec_ref(v_dep_1775_);
v_a_2054_ = lean_ctor_get(v___x_2053_, 0);
v_isSharedCheck_2061_ = !lean_is_exclusive(v___x_2053_);
if (v_isSharedCheck_2061_ == 0)
{
v___x_2056_ = v___x_2053_;
v_isShared_2057_ = v_isSharedCheck_2061_;
goto v_resetjp_2055_;
}
else
{
lean_inc(v_a_2054_);
lean_dec(v___x_2053_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2061_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
lean_object* v___x_2059_; 
if (v_isShared_2057_ == 0)
{
v___x_2059_ = v___x_2056_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v_a_2054_);
v___x_2059_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
return v___x_2059_;
}
}
}
}
}
else
{
size_t v___x_2062_; size_t v___x_2063_; lean_object* v___x_2064_; 
v___x_2062_ = ((size_t)0ULL);
v___x_2063_ = lean_usize_of_nat(v___x_2047_);
v___x_2064_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_snd_2046_, v___x_2062_, v___x_2063_, v___x_2049_, v_a_1781_);
lean_dec_ref(v_snd_2046_);
if (lean_obj_tag(v___x_2064_) == 0)
{
lean_dec_ref_known(v___x_2064_, 1);
v___y_1989_ = v___y_2039_;
v___y_1990_ = v___y_2040_;
v___y_1991_ = v___y_2041_;
v___y_1992_ = v___y_2042_;
v___y_1993_ = v___y_2044_;
v___y_1994_ = v___y_2043_;
v_a_1995_ = v_fst_2045_;
goto v___jp_1988_;
}
else
{
lean_object* v_a_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2072_; 
lean_dec_ref(v_fst_2045_);
lean_dec_ref(v___y_2044_);
lean_dec(v___y_2043_);
lean_dec(v___y_2042_);
lean_dec_ref(v___y_2041_);
lean_dec_ref(v___y_2040_);
lean_dec_ref(v___y_2039_);
lean_dec_ref(v___x_1971_);
lean_dec_ref(v_wsDir_1778_);
lean_dec_ref(v_lakeEnv_1777_);
lean_dec_ref(v_dep_1775_);
v_a_2065_ = lean_ctor_get(v___x_2064_, 0);
v_isSharedCheck_2072_ = !lean_is_exclusive(v___x_2064_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_2067_ = v___x_2064_;
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_a_2065_);
lean_dec(v___x_2064_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v___x_2070_; 
if (v_isShared_2068_ == 0)
{
v___x_2070_ = v___x_2067_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_a_2065_);
v___x_2070_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
return v___x_2070_;
}
}
}
}
}
}
v___jp_2073_:
{
if (lean_obj_tag(v_a_2074_) == 0)
{
lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; uint8_t v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; 
lean_inc_ref(v_scope_1966_);
lean_dec_ref_known(v_a_2074_, 1);
lean_dec_ref(v_relPkgsDir_1779_);
lean_dec_ref(v_wsDir_1778_);
lean_dec_ref(v_lakeEnv_1777_);
lean_dec_ref(v_dep_1775_);
v___x_2075_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
v___x_2076_ = lean_string_append(v_scope_1966_, v___x_2075_);
v___x_2077_ = lean_string_append(v___x_2076_, v___x_1971_);
lean_dec_ref(v___x_1971_);
v___x_2078_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__7));
v___x_2079_ = lean_string_append(v___x_2077_, v___x_2078_);
v___x_2080_ = 3;
v___x_2081_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2081_, 0, v___x_2079_);
lean_ctor_set_uint8(v___x_2081_, sizeof(void*)*1, v___x_2080_);
lean_inc_ref(v_a_1781_);
v___x_2082_ = lean_apply_2(v_a_1781_, v___x_2081_, lean_box(0));
v___x_2083_ = lean_box(0);
v___x_2084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2084_, 0, v___x_2083_);
return v___x_2084_;
}
else
{
lean_object* v_a_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2205_; 
v_a_2085_ = lean_ctor_get(v_a_2074_, 0);
v_isSharedCheck_2205_ = !lean_is_exclusive(v_a_2074_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2087_ = v_a_2074_;
v_isShared_2088_ = v_isSharedCheck_2205_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_a_2085_);
lean_dec(v_a_2074_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2205_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
if (lean_obj_tag(v_a_2085_) == 0)
{
lean_object* v___x_2089_; uint8_t v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
lean_del_object(v___x_2087_);
lean_dec_ref(v___x_1971_);
lean_dec_ref(v_relPkgsDir_1779_);
lean_dec_ref(v_wsDir_1778_);
lean_dec_ref(v_lakeEnv_1777_);
v___x_2089_ = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed(v_dep_1775_);
v___x_2090_ = 3;
v___x_2091_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2091_, 0, v___x_2089_);
lean_ctor_set_uint8(v___x_2091_, sizeof(void*)*1, v___x_2090_);
lean_inc_ref(v_a_1781_);
v___x_2092_ = lean_apply_2(v_a_1781_, v___x_2091_, lean_box(0));
v___x_2093_ = lean_box(0);
v___x_2094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2093_);
return v___x_2094_;
}
else
{
lean_object* v_val_2095_; lean_object* v___x_2096_; 
v_val_2095_ = lean_ctor_get(v_a_2085_, 0);
lean_inc(v_val_2095_);
lean_dec_ref_known(v_a_2085_, 1);
v___x_2096_ = l_Lake_RegistryPkg_gitSrc_x3f(v_val_2095_);
if (lean_obj_tag(v___x_2096_) == 1)
{
lean_object* v_val_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2204_; 
v_val_2097_ = lean_ctor_get(v___x_2096_, 0);
v_isSharedCheck_2204_ = !lean_is_exclusive(v___x_2096_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2099_ = v___x_2096_;
v_isShared_2100_ = v_isSharedCheck_2204_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_val_2097_);
lean_dec(v___x_2096_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2204_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
if (lean_obj_tag(v_val_2097_) == 0)
{
lean_object* v_url_2101_; lean_object* v_githubUrl_x3f_2102_; lean_object* v_defaultBranch_x3f_2103_; lean_object* v_subDir_x3f_2104_; lean_object* v_name_2105_; lean_object* v_fullName_2106_; lean_object* v___x_2107_; 
v_url_2101_ = lean_ctor_get(v_val_2097_, 1);
lean_inc_ref(v_url_2101_);
v_githubUrl_x3f_2102_ = lean_ctor_get(v_val_2097_, 2);
lean_inc(v_githubUrl_x3f_2102_);
v_defaultBranch_x3f_2103_ = lean_ctor_get(v_val_2097_, 3);
lean_inc(v_defaultBranch_x3f_2103_);
v_subDir_x3f_2104_ = lean_ctor_get(v_val_2097_, 4);
lean_inc(v_subDir_x3f_2104_);
lean_dec_ref_known(v_val_2097_, 5);
v_name_2105_ = lean_ctor_get(v_val_2095_, 0);
lean_inc_ref(v_name_2105_);
v_fullName_2106_ = lean_ctor_get(v_val_2095_, 1);
lean_inc_ref(v_fullName_2106_);
lean_dec(v_val_2095_);
v___x_2107_ = l_Lake_joinRelative(v_relPkgsDir_1779_, v_name_2105_);
switch(lean_obj_tag(v_version_1967_))
{
case 0:
{
lean_object* v___x_2108_; 
lean_del_object(v___x_2087_);
lean_dec_ref(v___x_1971_);
v___x_2108_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
if (lean_obj_tag(v_defaultBranch_x3f_2103_) == 0)
{
uint8_t v___x_2109_; 
lean_dec_ref(v___x_2107_);
lean_dec_ref(v_fullName_2106_);
lean_dec(v_subDir_x3f_2104_);
lean_dec(v_githubUrl_x3f_2102_);
lean_dec_ref(v_url_2101_);
lean_dec_ref(v_wsDir_1778_);
lean_dec_ref(v_lakeEnv_1777_);
lean_dec_ref(v_dep_1775_);
v___x_2109_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_2109_ == 0)
{
lean_object* v___x_2110_; lean_object* v___x_2112_; 
v___x_2110_ = lean_box(0);
if (v_isShared_2100_ == 0)
{
lean_ctor_set(v___x_2099_, 0, v___x_2110_);
v___x_2112_ = v___x_2099_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v___x_2110_);
v___x_2112_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
return v___x_2112_;
}
}
else
{
lean_object* v___x_2114_; uint8_t v___x_2115_; 
lean_del_object(v___x_2099_);
v___x_2114_ = lean_box(0);
v___x_2115_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_2115_ == 0)
{
if (v___x_2109_ == 0)
{
goto v___jp_1783_;
}
else
{
size_t v___x_2116_; size_t v___x_2117_; lean_object* v___x_2118_; 
v___x_2116_ = ((size_t)0ULL);
v___x_2117_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_2118_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_2108_, v___x_2116_, v___x_2117_, v___x_2114_, v_a_1781_);
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_dec_ref_known(v___x_2118_, 1);
goto v___jp_1783_;
}
else
{
lean_object* v_a_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2126_; 
v_a_2119_ = lean_ctor_get(v___x_2118_, 0);
v_isSharedCheck_2126_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2121_ = v___x_2118_;
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_a_2119_);
lean_dec(v___x_2118_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v___x_2124_; 
if (v_isShared_2122_ == 0)
{
v___x_2124_ = v___x_2121_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v_a_2119_);
v___x_2124_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
return v___x_2124_;
}
}
}
}
}
else
{
size_t v___x_2127_; size_t v___x_2128_; lean_object* v___x_2129_; 
v___x_2127_ = ((size_t)0ULL);
v___x_2128_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_2129_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_2108_, v___x_2127_, v___x_2128_, v___x_2114_, v_a_1781_);
if (lean_obj_tag(v___x_2129_) == 0)
{
lean_dec_ref_known(v___x_2129_, 1);
goto v___jp_1783_;
}
else
{
lean_object* v_a_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2137_; 
v_a_2130_ = lean_ctor_get(v___x_2129_, 0);
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2129_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2132_ = v___x_2129_;
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_a_2130_);
lean_dec(v___x_2129_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v___x_2135_; 
if (v_isShared_2133_ == 0)
{
v___x_2135_ = v___x_2132_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_a_2130_);
v___x_2135_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
return v___x_2135_;
}
}
}
}
}
}
else
{
lean_object* v_val_2138_; uint8_t v___x_2139_; 
lean_del_object(v___x_2099_);
v_val_2138_ = lean_ctor_get(v_defaultBranch_x3f_2103_, 0);
lean_inc(v_val_2138_);
lean_dec_ref_known(v_defaultBranch_x3f_2103_, 1);
v___x_2139_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_2139_ == 0)
{
v___y_1807_ = v_url_2101_;
v___y_1808_ = v_fullName_2106_;
v___y_1809_ = v_subDir_x3f_2104_;
v___y_1810_ = v_githubUrl_x3f_2102_;
v___y_1811_ = v___x_2107_;
v_a_1812_ = v_val_2138_;
goto v___jp_1806_;
}
else
{
lean_object* v___x_2140_; uint8_t v___x_2141_; 
v___x_2140_ = lean_box(0);
v___x_2141_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_2141_ == 0)
{
if (v___x_2139_ == 0)
{
v___y_1807_ = v_url_2101_;
v___y_1808_ = v_fullName_2106_;
v___y_1809_ = v_subDir_x3f_2104_;
v___y_1810_ = v_githubUrl_x3f_2102_;
v___y_1811_ = v___x_2107_;
v_a_1812_ = v_val_2138_;
goto v___jp_1806_;
}
else
{
size_t v___x_2142_; size_t v___x_2143_; lean_object* v___x_2144_; 
v___x_2142_ = ((size_t)0ULL);
v___x_2143_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_2144_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_2108_, v___x_2142_, v___x_2143_, v___x_2140_, v_a_1781_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_dec_ref_known(v___x_2144_, 1);
v___y_1807_ = v_url_2101_;
v___y_1808_ = v_fullName_2106_;
v___y_1809_ = v_subDir_x3f_2104_;
v___y_1810_ = v_githubUrl_x3f_2102_;
v___y_1811_ = v___x_2107_;
v_a_1812_ = v_val_2138_;
goto v___jp_1806_;
}
else
{
lean_object* v_a_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2152_; 
lean_dec(v_val_2138_);
lean_dec_ref(v___x_2107_);
lean_dec_ref(v_fullName_2106_);
lean_dec(v_subDir_x3f_2104_);
lean_dec(v_githubUrl_x3f_2102_);
lean_dec_ref(v_url_2101_);
lean_dec_ref(v_wsDir_1778_);
lean_dec_ref(v_lakeEnv_1777_);
lean_dec_ref(v_dep_1775_);
v_a_2145_ = lean_ctor_get(v___x_2144_, 0);
v_isSharedCheck_2152_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_2147_ = v___x_2144_;
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_a_2145_);
lean_dec(v___x_2144_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
lean_object* v___x_2150_; 
if (v_isShared_2148_ == 0)
{
v___x_2150_ = v___x_2147_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v_a_2145_);
v___x_2150_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
return v___x_2150_;
}
}
}
}
}
else
{
size_t v___x_2153_; size_t v___x_2154_; lean_object* v___x_2155_; 
v___x_2153_ = ((size_t)0ULL);
v___x_2154_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_2155_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_2108_, v___x_2153_, v___x_2154_, v___x_2140_, v_a_1781_);
if (lean_obj_tag(v___x_2155_) == 0)
{
lean_dec_ref_known(v___x_2155_, 1);
v___y_1807_ = v_url_2101_;
v___y_1808_ = v_fullName_2106_;
v___y_1809_ = v_subDir_x3f_2104_;
v___y_1810_ = v_githubUrl_x3f_2102_;
v___y_1811_ = v___x_2107_;
v_a_1812_ = v_val_2138_;
goto v___jp_1806_;
}
else
{
lean_object* v_a_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2163_; 
lean_dec(v_val_2138_);
lean_dec_ref(v___x_2107_);
lean_dec_ref(v_fullName_2106_);
lean_dec(v_subDir_x3f_2104_);
lean_dec(v_githubUrl_x3f_2102_);
lean_dec_ref(v_url_2101_);
lean_dec_ref(v_wsDir_1778_);
lean_dec_ref(v_lakeEnv_1777_);
lean_dec_ref(v_dep_1775_);
v_a_2156_ = lean_ctor_get(v___x_2155_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2155_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2158_ = v___x_2155_;
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_a_2156_);
lean_dec(v___x_2155_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v___x_2161_; 
if (v_isShared_2159_ == 0)
{
v___x_2161_ = v___x_2158_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v_a_2156_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
return v___x_2161_;
}
}
}
}
}
}
}
case 1:
{
lean_object* v_rev_2164_; lean_object* v___x_2165_; uint8_t v___x_2166_; 
lean_dec(v_defaultBranch_x3f_2103_);
lean_del_object(v___x_2099_);
lean_del_object(v___x_2087_);
lean_dec_ref(v___x_1971_);
v_rev_2164_ = lean_ctor_get(v_version_1967_, 0);
v___x_2165_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_2166_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_2166_ == 0)
{
lean_inc_ref(v_rev_2164_);
v___y_1807_ = v_url_2101_;
v___y_1808_ = v_fullName_2106_;
v___y_1809_ = v_subDir_x3f_2104_;
v___y_1810_ = v_githubUrl_x3f_2102_;
v___y_1811_ = v___x_2107_;
v_a_1812_ = v_rev_2164_;
goto v___jp_1806_;
}
else
{
lean_object* v___x_2167_; uint8_t v___x_2168_; 
v___x_2167_ = lean_box(0);
v___x_2168_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_2168_ == 0)
{
if (v___x_2166_ == 0)
{
lean_inc_ref(v_rev_2164_);
v___y_1807_ = v_url_2101_;
v___y_1808_ = v_fullName_2106_;
v___y_1809_ = v_subDir_x3f_2104_;
v___y_1810_ = v_githubUrl_x3f_2102_;
v___y_1811_ = v___x_2107_;
v_a_1812_ = v_rev_2164_;
goto v___jp_1806_;
}
else
{
size_t v___x_2169_; size_t v___x_2170_; lean_object* v___x_2171_; 
v___x_2169_ = ((size_t)0ULL);
v___x_2170_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_2171_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_2165_, v___x_2169_, v___x_2170_, v___x_2167_, v_a_1781_);
if (lean_obj_tag(v___x_2171_) == 0)
{
lean_dec_ref_known(v___x_2171_, 1);
lean_inc_ref(v_rev_2164_);
v___y_1807_ = v_url_2101_;
v___y_1808_ = v_fullName_2106_;
v___y_1809_ = v_subDir_x3f_2104_;
v___y_1810_ = v_githubUrl_x3f_2102_;
v___y_1811_ = v___x_2107_;
v_a_1812_ = v_rev_2164_;
goto v___jp_1806_;
}
else
{
lean_object* v_a_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2179_; 
lean_dec_ref(v___x_2107_);
lean_dec_ref(v_fullName_2106_);
lean_dec(v_subDir_x3f_2104_);
lean_dec(v_githubUrl_x3f_2102_);
lean_dec_ref(v_url_2101_);
lean_dec_ref(v_wsDir_1778_);
lean_dec_ref(v_lakeEnv_1777_);
lean_dec_ref(v_dep_1775_);
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
v___x_2181_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_2182_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_2165_, v___x_2180_, v___x_2181_, v___x_2167_, v_a_1781_);
if (lean_obj_tag(v___x_2182_) == 0)
{
lean_dec_ref_known(v___x_2182_, 1);
lean_inc_ref(v_rev_2164_);
v___y_1807_ = v_url_2101_;
v___y_1808_ = v_fullName_2106_;
v___y_1809_ = v_subDir_x3f_2104_;
v___y_1810_ = v_githubUrl_x3f_2102_;
v___y_1811_ = v___x_2107_;
v_a_1812_ = v_rev_2164_;
goto v___jp_1806_;
}
else
{
lean_object* v_a_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2190_; 
lean_dec_ref(v___x_2107_);
lean_dec_ref(v_fullName_2106_);
lean_dec(v_subDir_x3f_2104_);
lean_dec(v_githubUrl_x3f_2102_);
lean_dec_ref(v_url_2101_);
lean_dec_ref(v_wsDir_1778_);
lean_dec_ref(v_lakeEnv_1777_);
lean_dec_ref(v_dep_1775_);
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
default: 
{
lean_object* v_ver_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; 
lean_dec(v_defaultBranch_x3f_2103_);
lean_del_object(v___x_2099_);
v_ver_2191_ = lean_ctor_get(v_version_1967_, 0);
v___x_2192_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
lean_inc_ref(v___x_1971_);
lean_inc_ref(v_scope_1966_);
lean_inc_ref(v_lakeEnv_1777_);
v___x_2193_ = l_Lake_Reservoir_fetchPkgVersions(v_lakeEnv_1777_, v_scope_1966_, v___x_1971_, v___x_2192_);
if (lean_obj_tag(v___x_2193_) == 0)
{
lean_object* v_a_2194_; lean_object* v_a_2195_; lean_object* v___x_2197_; 
v_a_2194_ = lean_ctor_get(v___x_2193_, 0);
lean_inc(v_a_2194_);
v_a_2195_ = lean_ctor_get(v___x_2193_, 1);
lean_inc(v_a_2195_);
lean_dec_ref_known(v___x_2193_, 2);
if (v_isShared_2088_ == 0)
{
lean_ctor_set(v___x_2087_, 0, v_a_2194_);
v___x_2197_ = v___x_2087_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_a_2194_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
lean_inc_ref(v_ver_2191_);
v___y_2039_ = v_ver_2191_;
v___y_2040_ = v_url_2101_;
v___y_2041_ = v_fullName_2106_;
v___y_2042_ = v_subDir_x3f_2104_;
v___y_2043_ = v_githubUrl_x3f_2102_;
v___y_2044_ = v___x_2107_;
v_fst_2045_ = v___x_2197_;
v_snd_2046_ = v_a_2195_;
goto v___jp_2038_;
}
}
else
{
lean_object* v_a_2199_; lean_object* v_a_2200_; lean_object* v___x_2202_; 
v_a_2199_ = lean_ctor_get(v___x_2193_, 0);
lean_inc(v_a_2199_);
v_a_2200_ = lean_ctor_get(v___x_2193_, 1);
lean_inc(v_a_2200_);
lean_dec_ref_known(v___x_2193_, 2);
if (v_isShared_2088_ == 0)
{
lean_ctor_set_tag(v___x_2087_, 0);
lean_ctor_set(v___x_2087_, 0, v_a_2199_);
v___x_2202_ = v___x_2087_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v_a_2199_);
v___x_2202_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
lean_inc_ref(v_ver_2191_);
v___y_2039_ = v_ver_2191_;
v___y_2040_ = v_url_2101_;
v___y_2041_ = v_fullName_2106_;
v___y_2042_ = v_subDir_x3f_2104_;
v___y_2043_ = v_githubUrl_x3f_2102_;
v___y_2044_ = v___x_2107_;
v_fst_2045_ = v___x_2202_;
v_snd_2046_ = v_a_2200_;
goto v___jp_2038_;
}
}
}
}
}
else
{
lean_del_object(v___x_2099_);
lean_dec(v_val_2097_);
lean_del_object(v___x_2087_);
lean_dec_ref(v___x_1971_);
lean_dec_ref(v_relPkgsDir_1779_);
lean_dec_ref(v_wsDir_1778_);
lean_dec_ref(v_lakeEnv_1777_);
lean_dec_ref(v_dep_1775_);
v___y_1787_ = v_val_2095_;
v___y_1788_ = v_a_1781_;
goto v___jp_1786_;
}
}
}
else
{
lean_dec(v___x_2096_);
lean_del_object(v___x_2087_);
lean_dec_ref(v___x_1971_);
lean_dec_ref(v_relPkgsDir_1779_);
lean_dec_ref(v_wsDir_1778_);
lean_dec_ref(v_lakeEnv_1777_);
lean_dec_ref(v_dep_1775_);
v___y_1787_ = v_val_2095_;
v___y_1788_ = v_a_1781_;
goto v___jp_1786_;
}
}
}
}
}
v___jp_2208_:
{
lean_object* v___x_2211_; uint8_t v___x_2212_; 
v___x_2211_ = lean_array_get_size(v_snd_2210_);
v___x_2212_ = lean_nat_dec_lt(v___x_1969_, v___x_2211_);
if (v___x_2212_ == 0)
{
lean_dec_ref(v_snd_2210_);
v_a_2074_ = v_fst_2209_;
goto v___jp_2073_;
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
lean_dec_ref(v_snd_2210_);
v_a_2074_ = v_fst_2209_;
goto v___jp_2073_;
}
else
{
size_t v___x_2215_; size_t v___x_2216_; lean_object* v___x_2217_; 
v___x_2215_ = ((size_t)0ULL);
v___x_2216_ = lean_usize_of_nat(v___x_2211_);
v___x_2217_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_snd_2210_, v___x_2215_, v___x_2216_, v___x_2213_, v_a_1781_);
lean_dec_ref(v_snd_2210_);
if (lean_obj_tag(v___x_2217_) == 0)
{
lean_dec_ref_known(v___x_2217_, 1);
v_a_2074_ = v_fst_2209_;
goto v___jp_2073_;
}
else
{
lean_object* v_a_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2225_; 
lean_dec_ref(v_fst_2209_);
lean_dec_ref(v___x_1971_);
lean_dec_ref(v_relPkgsDir_1779_);
lean_dec_ref(v_wsDir_1778_);
lean_dec_ref(v_lakeEnv_1777_);
lean_dec_ref(v_dep_1775_);
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
v___x_2228_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_snd_2210_, v___x_2226_, v___x_2227_, v___x_2213_, v_a_1781_);
lean_dec_ref(v_snd_2210_);
if (lean_obj_tag(v___x_2228_) == 0)
{
lean_dec_ref_known(v___x_2228_, 1);
v_a_2074_ = v_fst_2209_;
goto v___jp_2073_;
}
else
{
lean_object* v_a_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2236_; 
lean_dec_ref(v_fst_2209_);
lean_dec_ref(v___x_1971_);
lean_dec_ref(v_relPkgsDir_1779_);
lean_dec_ref(v_wsDir_1778_);
lean_dec_ref(v_lakeEnv_1777_);
lean_dec_ref(v_dep_1775_);
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
uint8_t v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; uint8_t v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; 
lean_inc(v_name_1965_);
lean_dec_ref(v_relPkgsDir_1779_);
lean_dec_ref(v_wsDir_1778_);
lean_dec_ref(v_lakeEnv_1777_);
lean_dec_ref(v_dep_1775_);
v___x_2243_ = 0;
v___x_2244_ = l_Lean_Name_toString(v_name_1965_, v___x_2243_);
v___x_2245_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__8));
v___x_2246_ = lean_string_append(v___x_2244_, v___x_2245_);
v___x_2247_ = 3;
v___x_2248_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2248_, 0, v___x_2246_);
lean_ctor_set_uint8(v___x_2248_, sizeof(void*)*1, v___x_2247_);
lean_inc_ref(v_a_1781_);
v___x_2249_ = lean_apply_2(v_a_1781_, v___x_2248_, lean_box(0));
v___x_2250_ = lean_box(0);
v___x_2251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2251_, 0, v___x_2250_);
return v___x_2251_;
}
}
v___jp_1783_:
{
lean_object* v___x_1784_; lean_object* v___x_1785_; 
v___x_1784_ = lean_box(0);
v___x_1785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1785_, 0, v___x_1784_);
return v___x_1785_;
}
v___jp_1786_:
{
lean_object* v_fullName_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; uint8_t v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
v_fullName_1789_ = lean_ctor_get(v___y_1787_, 1);
lean_inc_ref(v_fullName_1789_);
lean_dec_ref(v___y_1787_);
v___x_1790_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__0));
v___x_1791_ = lean_string_append(v_fullName_1789_, v___x_1790_);
v___x_1792_ = 3;
v___x_1793_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1793_, 0, v___x_1791_);
lean_ctor_set_uint8(v___x_1793_, sizeof(void*)*1, v___x_1792_);
lean_inc_ref(v___y_1788_);
v___x_1794_ = lean_apply_2(v___y_1788_, v___x_1793_, lean_box(0));
v___x_1795_ = lean_box(0);
v___x_1796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1796_, 0, v___x_1795_);
return v___x_1796_;
}
v___jp_1797_:
{
lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1804_, 0, v___y_1800_);
v___x_1805_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(v_a_1781_, v_dep_1775_, v_inherited_1776_, v_lakeEnv_1777_, v_wsDir_1778_, v___y_1799_, v___y_1802_, v___y_1798_, v___y_1803_, v___x_1804_, v___y_1801_);
lean_dec_ref(v_lakeEnv_1777_);
return v___x_1805_;
}
v___jp_1806_:
{
if (lean_obj_tag(v___y_1810_) == 0)
{
lean_object* v___x_1813_; 
v___x_1813_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___y_1798_ = v___y_1807_;
v___y_1799_ = v___y_1808_;
v___y_1800_ = v_a_1812_;
v___y_1801_ = v___y_1809_;
v___y_1802_ = v___y_1811_;
v___y_1803_ = v___x_1813_;
goto v___jp_1797_;
}
else
{
lean_object* v_val_1814_; 
v_val_1814_ = lean_ctor_get(v___y_1810_, 0);
lean_inc(v_val_1814_);
lean_dec_ref_known(v___y_1810_, 1);
v___y_1798_ = v___y_1807_;
v___y_1799_ = v___y_1808_;
v___y_1800_ = v_a_1812_;
v___y_1801_ = v___y_1809_;
v___y_1802_ = v___y_1811_;
v___y_1803_ = v_val_1814_;
goto v___jp_1797_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize___boxed(lean_object* v_dep_2252_, lean_object* v_inherited_2253_, lean_object* v_lakeEnv_2254_, lean_object* v_wsDir_2255_, lean_object* v_relPkgsDir_2256_, lean_object* v_relParentDir_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_){
_start:
{
uint8_t v_inherited_boxed_2260_; lean_object* v_res_2261_; 
v_inherited_boxed_2260_ = lean_unbox(v_inherited_2253_);
v_res_2261_ = l_Lake_Dependency_materialize(v_dep_2252_, v_inherited_boxed_2260_, v_lakeEnv_2254_, v_wsDir_2255_, v_relPkgsDir_2256_, v_relParentDir_2257_, v_a_2258_);
lean_dec_ref(v_a_2258_);
return v_res_2261_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep(lean_object* v_manifestEntry_2267_, lean_object* v_wsDir_2268_, lean_object* v_relPkgDir_2269_, lean_object* v_remoteUrl_2270_, lean_object* v_a_2271_){
_start:
{
lean_object* v___y_2274_; lean_object* v_a_2275_; lean_object* v_pkgDir_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___f_2281_; lean_object* v___y_2283_; lean_object* v___y_2284_; lean_object* v___y_2285_; lean_object* v___y_2286_; lean_object* v_val_2287_; lean_object* v_a_2317_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v_val_2357_; lean_object* v___x_2385_; uint8_t v___x_2386_; 
lean_inc_ref(v_relPkgDir_2269_);
v_pkgDir_2278_ = l_Lake_joinRelative(v_wsDir_2268_, v_relPkgDir_2269_);
v___x_2279_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1, &l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1_once, _init_l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1);
lean_inc_ref(v_pkgDir_2278_);
v___x_2280_ = l_Lake_resolvePath(v_pkgDir_2278_);
v___f_2281_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__2));
v___x_2354_ = lean_unsigned_to_nat(0u);
v___x_2355_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_2385_ = lean_string_utf8_byte_size(v___x_2280_);
v___x_2386_ = lean_nat_dec_eq(v___x_2385_, v___x_2354_);
if (v___x_2386_ == 0)
{
lean_object* v___x_2387_; 
v___x_2387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2387_, 0, v___x_2280_);
v_val_2357_ = v___x_2387_;
goto v___jp_2356_;
}
else
{
lean_object* v___x_2388_; 
lean_dec_ref(v___x_2280_);
v___x_2388_ = lean_box(0);
v_val_2357_ = v___x_2388_;
goto v___jp_2356_;
}
v___jp_2273_:
{
lean_object* v___x_2276_; lean_object* v___x_2277_; 
v___x_2276_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2276_, 0, v___y_2274_);
lean_ctor_set(v___x_2276_, 1, v_relPkgDir_2269_);
lean_ctor_set(v___x_2276_, 2, v_remoteUrl_2270_);
lean_ctor_set(v___x_2276_, 3, v_a_2275_);
lean_ctor_set(v___x_2276_, 4, v_manifestEntry_2267_);
v___x_2277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2277_, 0, v___x_2276_);
return v___x_2277_;
}
v___jp_2282_:
{
lean_object* v___x_2288_; uint8_t v___x_2289_; 
v___x_2288_ = lean_array_get_size(v___y_2283_);
v___x_2289_ = lean_nat_dec_lt(v___y_2284_, v___x_2288_);
if (v___x_2289_ == 0)
{
lean_dec_ref(v___y_2285_);
v___y_2274_ = v___y_2286_;
v_a_2275_ = v_val_2287_;
goto v___jp_2273_;
}
else
{
lean_object* v___x_2290_; uint8_t v___x_2291_; 
v___x_2290_ = lean_box(0);
v___x_2291_ = lean_nat_dec_le(v___x_2288_, v___x_2288_);
if (v___x_2291_ == 0)
{
if (v___x_2289_ == 0)
{
lean_dec_ref(v___y_2285_);
v___y_2274_ = v___y_2286_;
v_a_2275_ = v_val_2287_;
goto v___jp_2273_;
}
else
{
size_t v___x_2292_; size_t v___x_2293_; lean_object* v___x_2400__overap_2294_; lean_object* v___x_2295_; 
v___x_2292_ = ((size_t)0ULL);
v___x_2293_ = lean_usize_of_nat(v___x_2288_);
lean_inc_ref(v___y_2283_);
v___x_2400__overap_2294_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___y_2285_, v___f_2281_, v___y_2283_, v___x_2292_, v___x_2293_, v___x_2290_);
lean_inc_ref(v_a_2271_);
v___x_2295_ = lean_apply_2(v___x_2400__overap_2294_, v_a_2271_, lean_box(0));
if (lean_obj_tag(v___x_2295_) == 0)
{
lean_dec_ref_known(v___x_2295_, 1);
v___y_2274_ = v___y_2286_;
v_a_2275_ = v_val_2287_;
goto v___jp_2273_;
}
else
{
lean_object* v_a_2296_; lean_object* v___x_2298_; uint8_t v_isShared_2299_; uint8_t v_isSharedCheck_2303_; 
lean_dec_ref(v_val_2287_);
lean_dec_ref(v___y_2286_);
lean_dec_ref(v_remoteUrl_2270_);
lean_dec_ref(v_relPkgDir_2269_);
lean_dec_ref(v_manifestEntry_2267_);
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
else
{
size_t v___x_2304_; size_t v___x_2305_; lean_object* v___x_2410__overap_2306_; lean_object* v___x_2307_; 
v___x_2304_ = ((size_t)0ULL);
v___x_2305_ = lean_usize_of_nat(v___x_2288_);
lean_inc_ref(v___y_2283_);
v___x_2410__overap_2306_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___y_2285_, v___f_2281_, v___y_2283_, v___x_2304_, v___x_2305_, v___x_2290_);
lean_inc_ref(v_a_2271_);
v___x_2307_ = lean_apply_2(v___x_2410__overap_2306_, v_a_2271_, lean_box(0));
if (lean_obj_tag(v___x_2307_) == 0)
{
lean_dec_ref_known(v___x_2307_, 1);
v___y_2274_ = v___y_2286_;
v_a_2275_ = v_val_2287_;
goto v___jp_2273_;
}
else
{
lean_object* v_a_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2315_; 
lean_dec_ref(v_val_2287_);
lean_dec_ref(v___y_2286_);
lean_dec_ref(v_remoteUrl_2270_);
lean_dec_ref(v_relPkgDir_2269_);
lean_dec_ref(v_manifestEntry_2267_);
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
}
v___jp_2316_:
{
if (lean_obj_tag(v_a_2317_) == 1)
{
lean_object* v_manifestFile_x3f_2318_; 
lean_dec_ref(v_pkgDir_2278_);
v_manifestFile_x3f_2318_ = lean_ctor_get(v_manifestEntry_2267_, 3);
if (lean_obj_tag(v_manifestFile_x3f_2318_) == 1)
{
lean_object* v_val_2319_; lean_object* v_val_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; 
v_val_2319_ = lean_ctor_get(v_a_2317_, 0);
lean_inc_n(v_val_2319_, 2);
lean_dec_ref_known(v_a_2317_, 1);
v_val_2320_ = lean_ctor_get(v_manifestFile_x3f_2318_, 0);
lean_inc(v_val_2320_);
v___x_2321_ = l_Lake_joinRelative(v_val_2319_, v_val_2320_);
v___x_2322_ = lean_unsigned_to_nat(0u);
v___x_2323_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_2324_ = l_Lake_Manifest_load(v___x_2321_);
if (lean_obj_tag(v___x_2324_) == 0)
{
lean_object* v_a_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2332_; 
v_a_2325_ = lean_ctor_get(v___x_2324_, 0);
v_isSharedCheck_2332_ = !lean_is_exclusive(v___x_2324_);
if (v_isSharedCheck_2332_ == 0)
{
v___x_2327_ = v___x_2324_;
v_isShared_2328_ = v_isSharedCheck_2332_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_a_2325_);
lean_dec(v___x_2324_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2332_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v___x_2330_; 
if (v_isShared_2328_ == 0)
{
lean_ctor_set_tag(v___x_2327_, 1);
v___x_2330_ = v___x_2327_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v_a_2325_);
v___x_2330_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
v___y_2283_ = v___x_2323_;
v___y_2284_ = v___x_2322_;
v___y_2285_ = v___x_2279_;
v___y_2286_ = v_val_2319_;
v_val_2287_ = v___x_2330_;
goto v___jp_2282_;
}
}
}
else
{
lean_object* v_a_2333_; lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2340_; 
v_a_2333_ = lean_ctor_get(v___x_2324_, 0);
v_isSharedCheck_2340_ = !lean_is_exclusive(v___x_2324_);
if (v_isSharedCheck_2340_ == 0)
{
v___x_2335_ = v___x_2324_;
v_isShared_2336_ = v_isSharedCheck_2340_;
goto v_resetjp_2334_;
}
else
{
lean_inc(v_a_2333_);
lean_dec(v___x_2324_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2340_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
lean_object* v___x_2338_; 
if (v_isShared_2336_ == 0)
{
lean_ctor_set_tag(v___x_2335_, 0);
v___x_2338_ = v___x_2335_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v_a_2333_);
v___x_2338_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
v___y_2283_ = v___x_2323_;
v___y_2284_ = v___x_2322_;
v___y_2285_ = v___x_2279_;
v___y_2286_ = v_val_2319_;
v_val_2287_ = v___x_2338_;
goto v___jp_2282_;
}
}
}
}
else
{
lean_object* v_val_2341_; lean_object* v___x_2342_; 
v_val_2341_ = lean_ctor_get(v_a_2317_, 0);
lean_inc(v_val_2341_);
lean_dec_ref_known(v_a_2317_, 1);
v___x_2342_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1));
v___y_2274_ = v_val_2341_;
v_a_2275_ = v___x_2342_;
goto v___jp_2273_;
}
}
else
{
lean_object* v_name_2343_; uint8_t v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; uint8_t v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; 
lean_dec(v_a_2317_);
lean_dec_ref(v_remoteUrl_2270_);
lean_dec_ref(v_relPkgDir_2269_);
v_name_2343_ = lean_ctor_get(v_manifestEntry_2267_, 0);
lean_inc(v_name_2343_);
lean_dec_ref(v_manifestEntry_2267_);
v___x_2344_ = 0;
v___x_2345_ = l_Lean_Name_toString(v_name_2343_, v___x_2344_);
v___x_2346_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__3));
v___x_2347_ = lean_string_append(v___x_2345_, v___x_2346_);
v___x_2348_ = lean_string_append(v___x_2347_, v_pkgDir_2278_);
lean_dec_ref(v_pkgDir_2278_);
v___x_2349_ = 3;
v___x_2350_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2350_, 0, v___x_2348_);
lean_ctor_set_uint8(v___x_2350_, sizeof(void*)*1, v___x_2349_);
lean_inc_ref(v_a_2271_);
v___x_2351_ = lean_apply_2(v_a_2271_, v___x_2350_, lean_box(0));
v___x_2352_ = lean_box(0);
v___x_2353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2353_, 0, v___x_2352_);
return v___x_2353_;
}
}
v___jp_2356_:
{
uint8_t v___x_2358_; 
v___x_2358_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_2358_ == 0)
{
v_a_2317_ = v_val_2357_;
goto v___jp_2316_;
}
else
{
lean_object* v___x_2359_; uint8_t v___x_2360_; 
v___x_2359_ = lean_box(0);
v___x_2360_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_2360_ == 0)
{
if (v___x_2358_ == 0)
{
v_a_2317_ = v_val_2357_;
goto v___jp_2316_;
}
else
{
size_t v___x_2361_; size_t v___x_2362_; lean_object* v___x_2466__overap_2363_; lean_object* v___x_2364_; 
v___x_2361_ = ((size_t)0ULL);
v___x_2362_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_2466__overap_2363_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2279_, v___f_2281_, v___x_2355_, v___x_2361_, v___x_2362_, v___x_2359_);
lean_inc_ref(v_a_2271_);
v___x_2364_ = lean_apply_2(v___x_2466__overap_2363_, v_a_2271_, lean_box(0));
if (lean_obj_tag(v___x_2364_) == 0)
{
lean_dec_ref_known(v___x_2364_, 1);
v_a_2317_ = v_val_2357_;
goto v___jp_2316_;
}
else
{
lean_object* v_a_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2372_; 
lean_dec(v_val_2357_);
lean_dec_ref(v_pkgDir_2278_);
lean_dec_ref(v_remoteUrl_2270_);
lean_dec_ref(v_relPkgDir_2269_);
lean_dec_ref(v_manifestEntry_2267_);
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
else
{
size_t v___x_2373_; size_t v___x_2374_; lean_object* v___x_2476__overap_2375_; lean_object* v___x_2376_; 
v___x_2373_ = ((size_t)0ULL);
v___x_2374_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_2476__overap_2375_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2279_, v___f_2281_, v___x_2355_, v___x_2373_, v___x_2374_, v___x_2359_);
lean_inc_ref(v_a_2271_);
v___x_2376_ = lean_apply_2(v___x_2476__overap_2375_, v_a_2271_, lean_box(0));
if (lean_obj_tag(v___x_2376_) == 0)
{
lean_dec_ref_known(v___x_2376_, 1);
v_a_2317_ = v_val_2357_;
goto v___jp_2316_;
}
else
{
lean_object* v_a_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2384_; 
lean_dec(v_val_2357_);
lean_dec_ref(v_pkgDir_2278_);
lean_dec_ref(v_remoteUrl_2270_);
lean_dec_ref(v_relPkgDir_2269_);
lean_dec_ref(v_manifestEntry_2267_);
v_a_2377_ = lean_ctor_get(v___x_2376_, 0);
v_isSharedCheck_2384_ = !lean_is_exclusive(v___x_2376_);
if (v_isSharedCheck_2384_ == 0)
{
v___x_2379_ = v___x_2376_;
v_isShared_2380_ = v_isSharedCheck_2384_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_a_2377_);
lean_dec(v___x_2376_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2384_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v___x_2382_; 
if (v_isShared_2380_ == 0)
{
v___x_2382_ = v___x_2379_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v_a_2377_);
v___x_2382_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
return v___x_2382_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___boxed(lean_object* v_manifestEntry_2389_, lean_object* v_wsDir_2390_, lean_object* v_relPkgDir_2391_, lean_object* v_remoteUrl_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_){
_start:
{
lean_object* v_res_2395_; 
v_res_2395_ = l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep(v_manifestEntry_2389_, v_wsDir_2390_, v_relPkgDir_2391_, v_remoteUrl_2392_, v_a_2393_);
lean_dec_ref(v_a_2393_);
return v_res_2395_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize(lean_object* v_manifestEntry_2397_, lean_object* v_lakeEnv_2398_, lean_object* v_wsDir_2399_, lean_object* v_relPkgsDir_2400_, lean_object* v_a_2401_){
_start:
{
lean_object* v___y_2404_; lean_object* v___y_2405_; lean_object* v___y_2406_; lean_object* v_a_2407_; lean_object* v___y_2411_; lean_object* v___y_2412_; lean_object* v___y_2413_; lean_object* v___y_2414_; lean_object* v___y_2415_; lean_object* v___y_2416_; lean_object* v_val_2417_; lean_object* v_src_2444_; 
v_src_2444_ = lean_ctor_get(v_manifestEntry_2397_, 4);
lean_inc_ref(v_src_2444_);
if (lean_obj_tag(v_src_2444_) == 0)
{
lean_object* v_name_2445_; lean_object* v_manifestFile_x3f_2446_; lean_object* v_dir_2447_; lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2561_; 
lean_dec_ref(v_relPkgsDir_2400_);
v_name_2445_ = lean_ctor_get(v_manifestEntry_2397_, 0);
v_manifestFile_x3f_2446_ = lean_ctor_get(v_manifestEntry_2397_, 3);
v_dir_2447_ = lean_ctor_get(v_src_2444_, 0);
v_isSharedCheck_2561_ = !lean_is_exclusive(v_src_2444_);
if (v_isSharedCheck_2561_ == 0)
{
v___x_2449_ = v_src_2444_;
v_isShared_2450_ = v_isSharedCheck_2561_;
goto v_resetjp_2448_;
}
else
{
lean_inc(v_dir_2447_);
lean_dec(v_src_2444_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_2561_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
lean_object* v_pkgDir_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___y_2455_; lean_object* v_a_2456_; lean_object* v___y_2462_; lean_object* v___y_2463_; lean_object* v___y_2464_; lean_object* v_val_2465_; lean_object* v_a_2493_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v_val_2531_; lean_object* v___x_2557_; uint8_t v___x_2558_; 
lean_inc_ref(v_dir_2447_);
v_pkgDir_2451_ = l_Lake_joinRelative(v_wsDir_2399_, v_dir_2447_);
lean_inc_ref(v_pkgDir_2451_);
v___x_2452_ = l_Lake_resolvePath(v_pkgDir_2451_);
v___x_2453_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___x_2528_ = lean_unsigned_to_nat(0u);
v___x_2529_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_2557_ = lean_string_utf8_byte_size(v___x_2452_);
v___x_2558_ = lean_nat_dec_eq(v___x_2557_, v___x_2528_);
if (v___x_2558_ == 0)
{
lean_object* v___x_2559_; 
v___x_2559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2559_, 0, v___x_2452_);
v_val_2531_ = v___x_2559_;
goto v___jp_2530_;
}
else
{
lean_object* v___x_2560_; 
lean_dec_ref(v___x_2452_);
v___x_2560_ = lean_box(0);
v_val_2531_ = v___x_2560_;
goto v___jp_2530_;
}
v___jp_2454_:
{
lean_object* v___x_2457_; lean_object* v___x_2459_; 
v___x_2457_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2457_, 0, v___y_2455_);
lean_ctor_set(v___x_2457_, 1, v_dir_2447_);
lean_ctor_set(v___x_2457_, 2, v___x_2453_);
lean_ctor_set(v___x_2457_, 3, v_a_2456_);
lean_ctor_set(v___x_2457_, 4, v_manifestEntry_2397_);
if (v_isShared_2450_ == 0)
{
lean_ctor_set(v___x_2449_, 0, v___x_2457_);
v___x_2459_ = v___x_2449_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v___x_2457_);
v___x_2459_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2458_;
}
v_reusejp_2458_:
{
return v___x_2459_;
}
}
v___jp_2461_:
{
lean_object* v___x_2466_; uint8_t v___x_2467_; 
v___x_2466_ = lean_array_get_size(v___y_2464_);
v___x_2467_ = lean_nat_dec_lt(v___y_2463_, v___x_2466_);
if (v___x_2467_ == 0)
{
v___y_2455_ = v___y_2462_;
v_a_2456_ = v_val_2465_;
goto v___jp_2454_;
}
else
{
lean_object* v___x_2468_; uint8_t v___x_2469_; 
v___x_2468_ = lean_box(0);
v___x_2469_ = lean_nat_dec_le(v___x_2466_, v___x_2466_);
if (v___x_2469_ == 0)
{
if (v___x_2467_ == 0)
{
v___y_2455_ = v___y_2462_;
v_a_2456_ = v_val_2465_;
goto v___jp_2454_;
}
else
{
size_t v___x_2470_; size_t v___x_2471_; lean_object* v___x_2472_; 
v___x_2470_ = ((size_t)0ULL);
v___x_2471_ = lean_usize_of_nat(v___x_2466_);
v___x_2472_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_2464_, v___x_2470_, v___x_2471_, v___x_2468_, v_a_2401_);
if (lean_obj_tag(v___x_2472_) == 0)
{
lean_dec_ref_known(v___x_2472_, 1);
v___y_2455_ = v___y_2462_;
v_a_2456_ = v_val_2465_;
goto v___jp_2454_;
}
else
{
lean_object* v_a_2473_; lean_object* v___x_2475_; uint8_t v_isShared_2476_; uint8_t v_isSharedCheck_2480_; 
lean_dec_ref(v_val_2465_);
lean_dec_ref(v___y_2462_);
lean_del_object(v___x_2449_);
lean_dec_ref(v_dir_2447_);
lean_dec_ref(v_manifestEntry_2397_);
v_a_2473_ = lean_ctor_get(v___x_2472_, 0);
v_isSharedCheck_2480_ = !lean_is_exclusive(v___x_2472_);
if (v_isSharedCheck_2480_ == 0)
{
v___x_2475_ = v___x_2472_;
v_isShared_2476_ = v_isSharedCheck_2480_;
goto v_resetjp_2474_;
}
else
{
lean_inc(v_a_2473_);
lean_dec(v___x_2472_);
v___x_2475_ = lean_box(0);
v_isShared_2476_ = v_isSharedCheck_2480_;
goto v_resetjp_2474_;
}
v_resetjp_2474_:
{
lean_object* v___x_2478_; 
if (v_isShared_2476_ == 0)
{
v___x_2478_ = v___x_2475_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v_a_2473_);
v___x_2478_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
return v___x_2478_;
}
}
}
}
}
else
{
size_t v___x_2481_; size_t v___x_2482_; lean_object* v___x_2483_; 
v___x_2481_ = ((size_t)0ULL);
v___x_2482_ = lean_usize_of_nat(v___x_2466_);
v___x_2483_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_2464_, v___x_2481_, v___x_2482_, v___x_2468_, v_a_2401_);
if (lean_obj_tag(v___x_2483_) == 0)
{
lean_dec_ref_known(v___x_2483_, 1);
v___y_2455_ = v___y_2462_;
v_a_2456_ = v_val_2465_;
goto v___jp_2454_;
}
else
{
lean_object* v_a_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2491_; 
lean_dec_ref(v_val_2465_);
lean_dec_ref(v___y_2462_);
lean_del_object(v___x_2449_);
lean_dec_ref(v_dir_2447_);
lean_dec_ref(v_manifestEntry_2397_);
v_a_2484_ = lean_ctor_get(v___x_2483_, 0);
v_isSharedCheck_2491_ = !lean_is_exclusive(v___x_2483_);
if (v_isSharedCheck_2491_ == 0)
{
v___x_2486_ = v___x_2483_;
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_a_2484_);
lean_dec(v___x_2483_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
lean_object* v___x_2489_; 
if (v_isShared_2487_ == 0)
{
v___x_2489_ = v___x_2486_;
goto v_reusejp_2488_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v_a_2484_);
v___x_2489_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2488_;
}
v_reusejp_2488_:
{
return v___x_2489_;
}
}
}
}
}
}
v___jp_2492_:
{
if (lean_obj_tag(v_a_2493_) == 1)
{
lean_dec_ref(v_pkgDir_2451_);
if (lean_obj_tag(v_manifestFile_x3f_2446_) == 1)
{
lean_object* v_val_2494_; lean_object* v_val_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; 
v_val_2494_ = lean_ctor_get(v_a_2493_, 0);
lean_inc_n(v_val_2494_, 2);
lean_dec_ref_known(v_a_2493_, 1);
v_val_2495_ = lean_ctor_get(v_manifestFile_x3f_2446_, 0);
lean_inc(v_val_2495_);
v___x_2496_ = l_Lake_joinRelative(v_val_2494_, v_val_2495_);
v___x_2497_ = lean_unsigned_to_nat(0u);
v___x_2498_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_2499_ = l_Lake_Manifest_load(v___x_2496_);
if (lean_obj_tag(v___x_2499_) == 0)
{
lean_object* v_a_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2507_; 
v_a_2500_ = lean_ctor_get(v___x_2499_, 0);
v_isSharedCheck_2507_ = !lean_is_exclusive(v___x_2499_);
if (v_isSharedCheck_2507_ == 0)
{
v___x_2502_ = v___x_2499_;
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_a_2500_);
lean_dec(v___x_2499_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
lean_object* v___x_2505_; 
if (v_isShared_2503_ == 0)
{
lean_ctor_set_tag(v___x_2502_, 1);
v___x_2505_ = v___x_2502_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v_a_2500_);
v___x_2505_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
v___y_2462_ = v_val_2494_;
v___y_2463_ = v___x_2497_;
v___y_2464_ = v___x_2498_;
v_val_2465_ = v___x_2505_;
goto v___jp_2461_;
}
}
}
else
{
lean_object* v_a_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2515_; 
v_a_2508_ = lean_ctor_get(v___x_2499_, 0);
v_isSharedCheck_2515_ = !lean_is_exclusive(v___x_2499_);
if (v_isSharedCheck_2515_ == 0)
{
v___x_2510_ = v___x_2499_;
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_a_2508_);
lean_dec(v___x_2499_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
lean_object* v___x_2513_; 
if (v_isShared_2511_ == 0)
{
lean_ctor_set_tag(v___x_2510_, 0);
v___x_2513_ = v___x_2510_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v_a_2508_);
v___x_2513_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2512_;
}
v_reusejp_2512_:
{
v___y_2462_ = v_val_2494_;
v___y_2463_ = v___x_2497_;
v___y_2464_ = v___x_2498_;
v_val_2465_ = v___x_2513_;
goto v___jp_2461_;
}
}
}
}
else
{
lean_object* v_val_2516_; lean_object* v___x_2517_; 
v_val_2516_ = lean_ctor_get(v_a_2493_, 0);
lean_inc(v_val_2516_);
lean_dec_ref_known(v_a_2493_, 1);
v___x_2517_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1));
v___y_2455_ = v_val_2516_;
v_a_2456_ = v___x_2517_;
goto v___jp_2454_;
}
}
else
{
uint8_t v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; uint8_t v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; 
lean_inc(v_name_2445_);
lean_dec(v_a_2493_);
lean_del_object(v___x_2449_);
lean_dec_ref(v_dir_2447_);
lean_dec_ref(v_manifestEntry_2397_);
v___x_2518_ = 0;
v___x_2519_ = l_Lean_Name_toString(v_name_2445_, v___x_2518_);
v___x_2520_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__3));
v___x_2521_ = lean_string_append(v___x_2519_, v___x_2520_);
v___x_2522_ = lean_string_append(v___x_2521_, v_pkgDir_2451_);
lean_dec_ref(v_pkgDir_2451_);
v___x_2523_ = 3;
v___x_2524_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2524_, 0, v___x_2522_);
lean_ctor_set_uint8(v___x_2524_, sizeof(void*)*1, v___x_2523_);
lean_inc_ref(v_a_2401_);
v___x_2525_ = lean_apply_2(v_a_2401_, v___x_2524_, lean_box(0));
v___x_2526_ = lean_box(0);
v___x_2527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2527_, 0, v___x_2526_);
return v___x_2527_;
}
}
v___jp_2530_:
{
uint8_t v___x_2532_; 
v___x_2532_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_2532_ == 0)
{
v_a_2493_ = v_val_2531_;
goto v___jp_2492_;
}
else
{
lean_object* v___x_2533_; uint8_t v___x_2534_; 
v___x_2533_ = lean_box(0);
v___x_2534_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_2534_ == 0)
{
if (v___x_2532_ == 0)
{
v_a_2493_ = v_val_2531_;
goto v___jp_2492_;
}
else
{
size_t v___x_2535_; size_t v___x_2536_; lean_object* v___x_2537_; 
v___x_2535_ = ((size_t)0ULL);
v___x_2536_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_2537_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_2529_, v___x_2535_, v___x_2536_, v___x_2533_, v_a_2401_);
if (lean_obj_tag(v___x_2537_) == 0)
{
lean_dec_ref_known(v___x_2537_, 1);
v_a_2493_ = v_val_2531_;
goto v___jp_2492_;
}
else
{
lean_object* v_a_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2545_; 
lean_dec(v_val_2531_);
lean_dec_ref(v_pkgDir_2451_);
lean_del_object(v___x_2449_);
lean_dec_ref(v_dir_2447_);
lean_dec_ref(v_manifestEntry_2397_);
v_a_2538_ = lean_ctor_get(v___x_2537_, 0);
v_isSharedCheck_2545_ = !lean_is_exclusive(v___x_2537_);
if (v_isSharedCheck_2545_ == 0)
{
v___x_2540_ = v___x_2537_;
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_a_2538_);
lean_dec(v___x_2537_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v___x_2543_; 
if (v_isShared_2541_ == 0)
{
v___x_2543_ = v___x_2540_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v_a_2538_);
v___x_2543_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
return v___x_2543_;
}
}
}
}
}
else
{
size_t v___x_2546_; size_t v___x_2547_; lean_object* v___x_2548_; 
v___x_2546_ = ((size_t)0ULL);
v___x_2547_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_2548_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_2529_, v___x_2546_, v___x_2547_, v___x_2533_, v_a_2401_);
if (lean_obj_tag(v___x_2548_) == 0)
{
lean_dec_ref_known(v___x_2548_, 1);
v_a_2493_ = v_val_2531_;
goto v___jp_2492_;
}
else
{
lean_object* v_a_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2556_; 
lean_dec(v_val_2531_);
lean_dec_ref(v_pkgDir_2451_);
lean_del_object(v___x_2449_);
lean_dec_ref(v_dir_2447_);
lean_dec_ref(v_manifestEntry_2397_);
v_a_2549_ = lean_ctor_get(v___x_2548_, 0);
v_isSharedCheck_2556_ = !lean_is_exclusive(v___x_2548_);
if (v_isSharedCheck_2556_ == 0)
{
v___x_2551_ = v___x_2548_;
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_a_2549_);
lean_dec(v___x_2548_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
lean_object* v___x_2554_; 
if (v_isShared_2552_ == 0)
{
v___x_2554_ = v___x_2551_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v_a_2549_);
v___x_2554_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
return v___x_2554_;
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
lean_object* v_name_2562_; lean_object* v_manifestFile_x3f_2563_; lean_object* v_url_2564_; lean_object* v_rev_2565_; lean_object* v_subDir_x3f_2566_; uint8_t v___x_2567_; lean_object* v___x_2568_; lean_object* v___y_2570_; lean_object* v___y_2571_; lean_object* v___y_2572_; lean_object* v___y_2573_; lean_object* v_a_2574_; lean_object* v___y_2608_; lean_object* v___y_2609_; lean_object* v___y_2610_; lean_object* v___y_2611_; lean_object* v___y_2612_; lean_object* v___y_2613_; lean_object* v_val_2614_; lean_object* v___y_2642_; lean_object* v___y_2643_; lean_object* v___y_2644_; lean_object* v___y_2654_; lean_object* v___y_2655_; lean_object* v_relGitDir_2659_; lean_object* v___y_2661_; lean_object* v_gitDir_2664_; lean_object* v___y_2666_; lean_object* v___y_2667_; lean_object* v___y_2678_; uint8_t v_a_2690_; lean_object* v___y_2700_; lean_object* v___y_2701_; uint8_t v_val_2702_; uint8_t v___y_2730_; lean_object* v_a_2731_; uint8_t v___x_2741_; lean_object* v___x_2774_; uint8_t v___x_2775_; 
v_name_2562_ = lean_ctor_get(v_manifestEntry_2397_, 0);
v_manifestFile_x3f_2563_ = lean_ctor_get(v_manifestEntry_2397_, 3);
v_url_2564_ = lean_ctor_get(v_src_2444_, 0);
lean_inc_ref(v_url_2564_);
v_rev_2565_ = lean_ctor_get(v_src_2444_, 1);
lean_inc_ref(v_rev_2565_);
v_subDir_x3f_2566_ = lean_ctor_get(v_src_2444_, 3);
lean_inc(v_subDir_x3f_2566_);
lean_dec_ref_known(v_src_2444_, 4);
v___x_2567_ = 0;
lean_inc(v_name_2562_);
v___x_2568_ = l_Lean_Name_toString(v_name_2562_, v___x_2567_);
lean_inc_ref(v___x_2568_);
v_relGitDir_2659_ = l_Lake_joinRelative(v_relPkgsDir_2400_, v___x_2568_);
lean_inc_ref(v_relGitDir_2659_);
lean_inc_ref(v_wsDir_2399_);
v_gitDir_2664_ = l_Lake_joinRelative(v_wsDir_2399_, v_relGitDir_2659_);
v___x_2741_ = l_System_FilePath_isDir(v_gitDir_2664_);
v___x_2774_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_2775_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_2775_ == 0)
{
goto v___jp_2742_;
}
else
{
lean_object* v___x_2776_; uint8_t v___x_2777_; 
v___x_2776_ = lean_box(0);
v___x_2777_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_2777_ == 0)
{
if (v___x_2775_ == 0)
{
goto v___jp_2742_;
}
else
{
size_t v___x_2778_; size_t v___x_2779_; lean_object* v___x_2780_; 
v___x_2778_ = ((size_t)0ULL);
v___x_2779_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_2780_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_2774_, v___x_2778_, v___x_2779_, v___x_2776_, v_a_2401_);
if (lean_obj_tag(v___x_2780_) == 0)
{
lean_dec_ref_known(v___x_2780_, 1);
goto v___jp_2742_;
}
else
{
lean_object* v_a_2781_; lean_object* v___x_2783_; uint8_t v_isShared_2784_; uint8_t v_isSharedCheck_2788_; 
lean_dec_ref(v_gitDir_2664_);
lean_dec_ref(v_relGitDir_2659_);
lean_dec_ref(v___x_2568_);
lean_dec(v_subDir_x3f_2566_);
lean_dec_ref(v_rev_2565_);
lean_dec_ref(v_url_2564_);
lean_dec_ref(v_wsDir_2399_);
lean_dec_ref(v_manifestEntry_2397_);
v_a_2781_ = lean_ctor_get(v___x_2780_, 0);
v_isSharedCheck_2788_ = !lean_is_exclusive(v___x_2780_);
if (v_isSharedCheck_2788_ == 0)
{
v___x_2783_ = v___x_2780_;
v_isShared_2784_ = v_isSharedCheck_2788_;
goto v_resetjp_2782_;
}
else
{
lean_inc(v_a_2781_);
lean_dec(v___x_2780_);
v___x_2783_ = lean_box(0);
v_isShared_2784_ = v_isSharedCheck_2788_;
goto v_resetjp_2782_;
}
v_resetjp_2782_:
{
lean_object* v___x_2786_; 
if (v_isShared_2784_ == 0)
{
v___x_2786_ = v___x_2783_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v_a_2781_);
v___x_2786_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
return v___x_2786_;
}
}
}
}
}
else
{
size_t v___x_2789_; size_t v___x_2790_; lean_object* v___x_2791_; 
v___x_2789_ = ((size_t)0ULL);
v___x_2790_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_2791_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_2774_, v___x_2789_, v___x_2790_, v___x_2776_, v_a_2401_);
if (lean_obj_tag(v___x_2791_) == 0)
{
lean_dec_ref_known(v___x_2791_, 1);
goto v___jp_2742_;
}
else
{
lean_object* v_a_2792_; lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2799_; 
lean_dec_ref(v_gitDir_2664_);
lean_dec_ref(v_relGitDir_2659_);
lean_dec_ref(v___x_2568_);
lean_dec(v_subDir_x3f_2566_);
lean_dec_ref(v_rev_2565_);
lean_dec_ref(v_url_2564_);
lean_dec_ref(v_wsDir_2399_);
lean_dec_ref(v_manifestEntry_2397_);
v_a_2792_ = lean_ctor_get(v___x_2791_, 0);
v_isSharedCheck_2799_ = !lean_is_exclusive(v___x_2791_);
if (v_isSharedCheck_2799_ == 0)
{
v___x_2794_ = v___x_2791_;
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
else
{
lean_inc(v_a_2792_);
lean_dec(v___x_2791_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
v_resetjp_2793_:
{
lean_object* v___x_2797_; 
if (v_isShared_2795_ == 0)
{
v___x_2797_ = v___x_2794_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v_a_2792_);
v___x_2797_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
return v___x_2797_;
}
}
}
}
}
v___jp_2569_:
{
if (lean_obj_tag(v_a_2574_) == 1)
{
lean_dec_ref(v___y_2570_);
lean_dec_ref(v___x_2568_);
if (lean_obj_tag(v_manifestFile_x3f_2563_) == 1)
{
lean_object* v_val_2575_; lean_object* v_val_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; 
v_val_2575_ = lean_ctor_get(v_a_2574_, 0);
lean_inc_n(v_val_2575_, 2);
lean_dec_ref_known(v_a_2574_, 1);
v_val_2576_ = lean_ctor_get(v_manifestFile_x3f_2563_, 0);
lean_inc(v_val_2576_);
v___x_2577_ = l_Lake_joinRelative(v_val_2575_, v_val_2576_);
v___x_2578_ = lean_unsigned_to_nat(0u);
v___x_2579_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_2580_ = l_Lake_Manifest_load(v___x_2577_);
if (lean_obj_tag(v___x_2580_) == 0)
{
lean_object* v_a_2581_; lean_object* v___x_2583_; uint8_t v_isShared_2584_; uint8_t v_isSharedCheck_2588_; 
v_a_2581_ = lean_ctor_get(v___x_2580_, 0);
v_isSharedCheck_2588_ = !lean_is_exclusive(v___x_2580_);
if (v_isSharedCheck_2588_ == 0)
{
v___x_2583_ = v___x_2580_;
v_isShared_2584_ = v_isSharedCheck_2588_;
goto v_resetjp_2582_;
}
else
{
lean_inc(v_a_2581_);
lean_dec(v___x_2580_);
v___x_2583_ = lean_box(0);
v_isShared_2584_ = v_isSharedCheck_2588_;
goto v_resetjp_2582_;
}
v_resetjp_2582_:
{
lean_object* v___x_2586_; 
if (v_isShared_2584_ == 0)
{
lean_ctor_set_tag(v___x_2583_, 1);
v___x_2586_ = v___x_2583_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v_a_2581_);
v___x_2586_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
v___y_2411_ = v___y_2571_;
v___y_2412_ = v_val_2575_;
v___y_2413_ = v___x_2578_;
v___y_2414_ = v___x_2579_;
v___y_2415_ = v___y_2572_;
v___y_2416_ = v___y_2573_;
v_val_2417_ = v___x_2586_;
goto v___jp_2410_;
}
}
}
else
{
lean_object* v_a_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2596_; 
v_a_2589_ = lean_ctor_get(v___x_2580_, 0);
v_isSharedCheck_2596_ = !lean_is_exclusive(v___x_2580_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2591_ = v___x_2580_;
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_a_2589_);
lean_dec(v___x_2580_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___x_2594_; 
if (v_isShared_2592_ == 0)
{
lean_ctor_set_tag(v___x_2591_, 0);
v___x_2594_ = v___x_2591_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v_a_2589_);
v___x_2594_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
v___y_2411_ = v___y_2571_;
v___y_2412_ = v_val_2575_;
v___y_2413_ = v___x_2578_;
v___y_2414_ = v___x_2579_;
v___y_2415_ = v___y_2572_;
v___y_2416_ = v___y_2573_;
v_val_2417_ = v___x_2594_;
goto v___jp_2410_;
}
}
}
}
else
{
lean_object* v_val_2597_; lean_object* v___x_2598_; 
v_val_2597_ = lean_ctor_get(v_a_2574_, 0);
lean_inc(v_val_2597_);
lean_dec_ref_known(v_a_2574_, 1);
v___x_2598_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1));
v___y_2404_ = v___y_2571_;
v___y_2405_ = v_val_2597_;
v___y_2406_ = v___y_2573_;
v_a_2407_ = v___x_2598_;
goto v___jp_2403_;
}
}
else
{
lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; uint8_t v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; 
lean_dec(v_a_2574_);
lean_dec_ref(v___y_2573_);
lean_dec_ref(v___y_2571_);
lean_dec_ref(v_manifestEntry_2397_);
v___x_2599_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__3));
v___x_2600_ = lean_string_append(v___x_2568_, v___x_2599_);
v___x_2601_ = lean_string_append(v___x_2600_, v___y_2570_);
lean_dec_ref(v___y_2570_);
v___x_2602_ = 3;
v___x_2603_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2603_, 0, v___x_2601_);
lean_ctor_set_uint8(v___x_2603_, sizeof(void*)*1, v___x_2602_);
lean_inc_ref(v___y_2572_);
v___x_2604_ = lean_apply_2(v___y_2572_, v___x_2603_, lean_box(0));
v___x_2605_ = lean_box(0);
v___x_2606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2606_, 0, v___x_2605_);
return v___x_2606_;
}
}
v___jp_2607_:
{
lean_object* v___x_2615_; uint8_t v___x_2616_; 
v___x_2615_ = lean_array_get_size(v___y_2611_);
v___x_2616_ = lean_nat_dec_lt(v___y_2610_, v___x_2615_);
if (v___x_2616_ == 0)
{
v___y_2570_ = v___y_2609_;
v___y_2571_ = v___y_2608_;
v___y_2572_ = v___y_2613_;
v___y_2573_ = v___y_2612_;
v_a_2574_ = v_val_2614_;
goto v___jp_2569_;
}
else
{
lean_object* v___x_2617_; uint8_t v___x_2618_; 
v___x_2617_ = lean_box(0);
v___x_2618_ = lean_nat_dec_le(v___x_2615_, v___x_2615_);
if (v___x_2618_ == 0)
{
if (v___x_2616_ == 0)
{
v___y_2570_ = v___y_2609_;
v___y_2571_ = v___y_2608_;
v___y_2572_ = v___y_2613_;
v___y_2573_ = v___y_2612_;
v_a_2574_ = v_val_2614_;
goto v___jp_2569_;
}
else
{
size_t v___x_2619_; size_t v___x_2620_; lean_object* v___x_2621_; 
v___x_2619_ = ((size_t)0ULL);
v___x_2620_ = lean_usize_of_nat(v___x_2615_);
v___x_2621_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_2611_, v___x_2619_, v___x_2620_, v___x_2617_, v___y_2613_);
if (lean_obj_tag(v___x_2621_) == 0)
{
lean_dec_ref_known(v___x_2621_, 1);
v___y_2570_ = v___y_2609_;
v___y_2571_ = v___y_2608_;
v___y_2572_ = v___y_2613_;
v___y_2573_ = v___y_2612_;
v_a_2574_ = v_val_2614_;
goto v___jp_2569_;
}
else
{
lean_object* v_a_2622_; lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2629_; 
lean_dec(v_val_2614_);
lean_dec_ref(v___y_2612_);
lean_dec_ref(v___y_2609_);
lean_dec_ref(v___y_2608_);
lean_dec_ref(v___x_2568_);
lean_dec_ref(v_manifestEntry_2397_);
v_a_2622_ = lean_ctor_get(v___x_2621_, 0);
v_isSharedCheck_2629_ = !lean_is_exclusive(v___x_2621_);
if (v_isSharedCheck_2629_ == 0)
{
v___x_2624_ = v___x_2621_;
v_isShared_2625_ = v_isSharedCheck_2629_;
goto v_resetjp_2623_;
}
else
{
lean_inc(v_a_2622_);
lean_dec(v___x_2621_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2629_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
lean_object* v___x_2627_; 
if (v_isShared_2625_ == 0)
{
v___x_2627_ = v___x_2624_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v_a_2622_);
v___x_2627_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
return v___x_2627_;
}
}
}
}
}
else
{
size_t v___x_2630_; size_t v___x_2631_; lean_object* v___x_2632_; 
v___x_2630_ = ((size_t)0ULL);
v___x_2631_ = lean_usize_of_nat(v___x_2615_);
v___x_2632_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_2611_, v___x_2630_, v___x_2631_, v___x_2617_, v___y_2613_);
if (lean_obj_tag(v___x_2632_) == 0)
{
lean_dec_ref_known(v___x_2632_, 1);
v___y_2570_ = v___y_2609_;
v___y_2571_ = v___y_2608_;
v___y_2572_ = v___y_2613_;
v___y_2573_ = v___y_2612_;
v_a_2574_ = v_val_2614_;
goto v___jp_2569_;
}
else
{
lean_object* v_a_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2640_; 
lean_dec(v_val_2614_);
lean_dec_ref(v___y_2612_);
lean_dec_ref(v___y_2609_);
lean_dec_ref(v___y_2608_);
lean_dec_ref(v___x_2568_);
lean_dec_ref(v_manifestEntry_2397_);
v_a_2633_ = lean_ctor_get(v___x_2632_, 0);
v_isSharedCheck_2640_ = !lean_is_exclusive(v___x_2632_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2635_ = v___x_2632_;
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_a_2633_);
lean_dec(v___x_2632_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
lean_object* v___x_2638_; 
if (v_isShared_2636_ == 0)
{
v___x_2638_ = v___x_2635_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v_a_2633_);
v___x_2638_ = v_reuseFailAlloc_2639_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
return v___x_2638_;
}
}
}
}
}
}
v___jp_2641_:
{
lean_object* v_pkgDir_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; uint8_t v___x_2650_; 
lean_inc_ref(v___y_2643_);
v_pkgDir_2645_ = l_Lake_joinRelative(v_wsDir_2399_, v___y_2643_);
lean_inc_ref(v_pkgDir_2645_);
v___x_2646_ = l_Lake_resolvePath(v_pkgDir_2645_);
v___x_2647_ = lean_unsigned_to_nat(0u);
v___x_2648_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_2649_ = lean_string_utf8_byte_size(v___x_2646_);
v___x_2650_ = lean_nat_dec_eq(v___x_2649_, v___x_2647_);
if (v___x_2650_ == 0)
{
lean_object* v___x_2651_; 
v___x_2651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2651_, 0, v___x_2646_);
v___y_2608_ = v___y_2644_;
v___y_2609_ = v_pkgDir_2645_;
v___y_2610_ = v___x_2647_;
v___y_2611_ = v___x_2648_;
v___y_2612_ = v___y_2643_;
v___y_2613_ = v___y_2642_;
v_val_2614_ = v___x_2651_;
goto v___jp_2607_;
}
else
{
lean_object* v___x_2652_; 
lean_dec_ref(v___x_2646_);
v___x_2652_ = lean_box(0);
v___y_2608_ = v___y_2644_;
v___y_2609_ = v_pkgDir_2645_;
v___y_2610_ = v___x_2647_;
v___y_2611_ = v___x_2648_;
v___y_2612_ = v___y_2643_;
v___y_2613_ = v___y_2642_;
v_val_2614_ = v___x_2652_;
goto v___jp_2607_;
}
}
v___jp_2653_:
{
lean_object* v___x_2656_; 
v___x_2656_ = l_Lake_Git_filterUrl_x3f(v_url_2564_);
if (lean_obj_tag(v___x_2656_) == 0)
{
lean_object* v___x_2657_; 
v___x_2657_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___y_2642_ = v___y_2654_;
v___y_2643_ = v___y_2655_;
v___y_2644_ = v___x_2657_;
goto v___jp_2641_;
}
else
{
lean_object* v_val_2658_; 
v_val_2658_ = lean_ctor_get(v___x_2656_, 0);
lean_inc(v_val_2658_);
lean_dec_ref_known(v___x_2656_, 1);
v___y_2642_ = v___y_2654_;
v___y_2643_ = v___y_2655_;
v___y_2644_ = v_val_2658_;
goto v___jp_2641_;
}
}
v___jp_2660_:
{
if (lean_obj_tag(v_subDir_x3f_2566_) == 0)
{
v___y_2654_ = v___y_2661_;
v___y_2655_ = v_relGitDir_2659_;
goto v___jp_2653_;
}
else
{
lean_object* v_val_2662_; lean_object* v___x_2663_; 
v_val_2662_ = lean_ctor_get(v_subDir_x3f_2566_, 0);
lean_inc(v_val_2662_);
lean_dec_ref_known(v_subDir_x3f_2566_, 1);
v___x_2663_ = l_Lake_joinRelative(v_relGitDir_2659_, v_val_2662_);
v___y_2654_ = v___y_2661_;
v___y_2655_ = v___x_2663_;
goto v___jp_2653_;
}
}
v___jp_2665_:
{
lean_object* v___x_2668_; 
lean_inc_ref(v___x_2568_);
v___x_2668_ = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_2401_, v___x_2568_, v_gitDir_2664_, v___y_2667_, v___y_2666_);
if (lean_obj_tag(v___x_2668_) == 0)
{
lean_dec_ref_known(v___x_2668_, 1);
v___y_2661_ = v_a_2401_;
goto v___jp_2660_;
}
else
{
lean_object* v_a_2669_; lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2676_; 
lean_dec_ref(v_relGitDir_2659_);
lean_dec_ref(v___x_2568_);
lean_dec(v_subDir_x3f_2566_);
lean_dec_ref(v_url_2564_);
lean_dec_ref(v_wsDir_2399_);
lean_dec_ref(v_manifestEntry_2397_);
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
lean_object* v___x_2679_; lean_object* v___x_2680_; 
v___x_2679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2679_, 0, v_rev_2565_);
lean_inc_ref(v___x_2568_);
v___x_2680_ = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(v_a_2401_, v___x_2568_, v_gitDir_2664_, v___y_2678_, v___x_2679_);
if (lean_obj_tag(v___x_2680_) == 0)
{
lean_dec_ref_known(v___x_2680_, 1);
v___y_2661_ = v_a_2401_;
goto v___jp_2660_;
}
else
{
lean_object* v_a_2681_; lean_object* v___x_2683_; uint8_t v_isShared_2684_; uint8_t v_isSharedCheck_2688_; 
lean_dec_ref(v_relGitDir_2659_);
lean_dec_ref(v___x_2568_);
lean_dec(v_subDir_x3f_2566_);
lean_dec_ref(v_url_2564_);
lean_dec_ref(v_wsDir_2399_);
lean_dec_ref(v_manifestEntry_2397_);
v_a_2681_ = lean_ctor_get(v___x_2680_, 0);
v_isSharedCheck_2688_ = !lean_is_exclusive(v___x_2680_);
if (v_isSharedCheck_2688_ == 0)
{
v___x_2683_ = v___x_2680_;
v_isShared_2684_ = v_isSharedCheck_2688_;
goto v_resetjp_2682_;
}
else
{
lean_inc(v_a_2681_);
lean_dec(v___x_2680_);
v___x_2683_ = lean_box(0);
v_isShared_2684_ = v_isSharedCheck_2688_;
goto v_resetjp_2682_;
}
v_resetjp_2682_:
{
lean_object* v___x_2686_; 
if (v_isShared_2684_ == 0)
{
v___x_2686_ = v___x_2683_;
goto v_reusejp_2685_;
}
else
{
lean_object* v_reuseFailAlloc_2687_; 
v_reuseFailAlloc_2687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2687_, 0, v_a_2681_);
v___x_2686_ = v_reuseFailAlloc_2687_;
goto v_reusejp_2685_;
}
v_reusejp_2685_:
{
return v___x_2686_;
}
}
}
}
v___jp_2689_:
{
if (v_a_2690_ == 0)
{
lean_dec_ref(v_gitDir_2664_);
v___y_2661_ = v_a_2401_;
goto v___jp_2660_;
}
else
{
lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; uint8_t v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; 
v___x_2691_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0));
lean_inc_ref(v___x_2568_);
v___x_2692_ = lean_string_append(v___x_2568_, v___x_2691_);
v___x_2693_ = lean_string_append(v___x_2692_, v_gitDir_2664_);
lean_dec_ref(v_gitDir_2664_);
v___x_2694_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1));
v___x_2695_ = lean_string_append(v___x_2693_, v___x_2694_);
v___x_2696_ = 2;
v___x_2697_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2697_, 0, v___x_2695_);
lean_ctor_set_uint8(v___x_2697_, sizeof(void*)*1, v___x_2696_);
lean_inc_ref(v_a_2401_);
v___x_2698_ = lean_apply_2(v_a_2401_, v___x_2697_, lean_box(0));
v___y_2661_ = v_a_2401_;
goto v___jp_2660_;
}
}
v___jp_2699_:
{
lean_object* v___x_2703_; uint8_t v___x_2704_; 
v___x_2703_ = lean_array_get_size(v___y_2701_);
v___x_2704_ = lean_nat_dec_lt(v___y_2700_, v___x_2703_);
if (v___x_2704_ == 0)
{
v_a_2690_ = v_val_2702_;
goto v___jp_2689_;
}
else
{
lean_object* v___x_2705_; uint8_t v___x_2706_; 
v___x_2705_ = lean_box(0);
v___x_2706_ = lean_nat_dec_le(v___x_2703_, v___x_2703_);
if (v___x_2706_ == 0)
{
if (v___x_2704_ == 0)
{
v_a_2690_ = v_val_2702_;
goto v___jp_2689_;
}
else
{
size_t v___x_2707_; size_t v___x_2708_; lean_object* v___x_2709_; 
v___x_2707_ = ((size_t)0ULL);
v___x_2708_ = lean_usize_of_nat(v___x_2703_);
v___x_2709_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_2701_, v___x_2707_, v___x_2708_, v___x_2705_, v_a_2401_);
if (lean_obj_tag(v___x_2709_) == 0)
{
lean_dec_ref_known(v___x_2709_, 1);
v_a_2690_ = v_val_2702_;
goto v___jp_2689_;
}
else
{
lean_object* v_a_2710_; lean_object* v___x_2712_; uint8_t v_isShared_2713_; uint8_t v_isSharedCheck_2717_; 
lean_dec_ref(v_gitDir_2664_);
lean_dec_ref(v_relGitDir_2659_);
lean_dec_ref(v___x_2568_);
lean_dec(v_subDir_x3f_2566_);
lean_dec_ref(v_url_2564_);
lean_dec_ref(v_wsDir_2399_);
lean_dec_ref(v_manifestEntry_2397_);
v_a_2710_ = lean_ctor_get(v___x_2709_, 0);
v_isSharedCheck_2717_ = !lean_is_exclusive(v___x_2709_);
if (v_isSharedCheck_2717_ == 0)
{
v___x_2712_ = v___x_2709_;
v_isShared_2713_ = v_isSharedCheck_2717_;
goto v_resetjp_2711_;
}
else
{
lean_inc(v_a_2710_);
lean_dec(v___x_2709_);
v___x_2712_ = lean_box(0);
v_isShared_2713_ = v_isSharedCheck_2717_;
goto v_resetjp_2711_;
}
v_resetjp_2711_:
{
lean_object* v___x_2715_; 
if (v_isShared_2713_ == 0)
{
v___x_2715_ = v___x_2712_;
goto v_reusejp_2714_;
}
else
{
lean_object* v_reuseFailAlloc_2716_; 
v_reuseFailAlloc_2716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2716_, 0, v_a_2710_);
v___x_2715_ = v_reuseFailAlloc_2716_;
goto v_reusejp_2714_;
}
v_reusejp_2714_:
{
return v___x_2715_;
}
}
}
}
}
else
{
size_t v___x_2718_; size_t v___x_2719_; lean_object* v___x_2720_; 
v___x_2718_ = ((size_t)0ULL);
v___x_2719_ = lean_usize_of_nat(v___x_2703_);
v___x_2720_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_2701_, v___x_2718_, v___x_2719_, v___x_2705_, v_a_2401_);
if (lean_obj_tag(v___x_2720_) == 0)
{
lean_dec_ref_known(v___x_2720_, 1);
v_a_2690_ = v_val_2702_;
goto v___jp_2689_;
}
else
{
lean_object* v_a_2721_; lean_object* v___x_2723_; uint8_t v_isShared_2724_; uint8_t v_isSharedCheck_2728_; 
lean_dec_ref(v_gitDir_2664_);
lean_dec_ref(v_relGitDir_2659_);
lean_dec_ref(v___x_2568_);
lean_dec(v_subDir_x3f_2566_);
lean_dec_ref(v_url_2564_);
lean_dec_ref(v_wsDir_2399_);
lean_dec_ref(v_manifestEntry_2397_);
v_a_2721_ = lean_ctor_get(v___x_2720_, 0);
v_isSharedCheck_2728_ = !lean_is_exclusive(v___x_2720_);
if (v_isSharedCheck_2728_ == 0)
{
v___x_2723_ = v___x_2720_;
v_isShared_2724_ = v_isSharedCheck_2728_;
goto v_resetjp_2722_;
}
else
{
lean_inc(v_a_2721_);
lean_dec(v___x_2720_);
v___x_2723_ = lean_box(0);
v_isShared_2724_ = v_isSharedCheck_2728_;
goto v_resetjp_2722_;
}
v_resetjp_2722_:
{
lean_object* v___x_2726_; 
if (v_isShared_2724_ == 0)
{
v___x_2726_ = v___x_2723_;
goto v_reusejp_2725_;
}
else
{
lean_object* v_reuseFailAlloc_2727_; 
v_reuseFailAlloc_2727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2727_, 0, v_a_2721_);
v___x_2726_ = v_reuseFailAlloc_2727_;
goto v_reusejp_2725_;
}
v_reusejp_2725_:
{
return v___x_2726_;
}
}
}
}
}
}
v___jp_2729_:
{
lean_object* v___x_2732_; lean_object* v___x_2733_; uint8_t v___x_2734_; 
v___x_2732_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
v___x_2733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2733_, 0, v_rev_2565_);
lean_inc_ref(v___x_2733_);
v___x_2734_ = l_Option_instDecidableEq___redArg(v___x_2732_, v_a_2731_, v___x_2733_);
if (v___x_2734_ == 0)
{
lean_object* v_pkgUrlMap_2735_; lean_object* v___x_2736_; 
v_pkgUrlMap_2735_ = lean_ctor_get(v_lakeEnv_2398_, 5);
v___x_2736_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgUrlMap_2735_, v_name_2562_);
if (lean_obj_tag(v___x_2736_) == 0)
{
lean_inc_ref(v_url_2564_);
v___y_2666_ = v___x_2733_;
v___y_2667_ = v_url_2564_;
goto v___jp_2665_;
}
else
{
lean_object* v_val_2737_; 
v_val_2737_ = lean_ctor_get(v___x_2736_, 0);
lean_inc(v_val_2737_);
lean_dec_ref_known(v___x_2736_, 1);
v___y_2666_ = v___x_2733_;
v___y_2667_ = v_val_2737_;
goto v___jp_2665_;
}
}
else
{
uint8_t v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; 
lean_dec_ref_known(v___x_2733_, 1);
lean_inc_ref(v_gitDir_2664_);
v___x_2738_ = l_Lake_GitRepo_hasNoDiff(v_gitDir_2664_);
v___x_2739_ = lean_unsigned_to_nat(0u);
v___x_2740_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
if (v___x_2738_ == 0)
{
v___y_2700_ = v___x_2739_;
v___y_2701_ = v___x_2740_;
v_val_2702_ = v___y_2730_;
goto v___jp_2699_;
}
else
{
v___y_2700_ = v___x_2739_;
v___y_2701_ = v___x_2740_;
v_val_2702_ = v___x_2567_;
goto v___jp_2699_;
}
}
}
v___jp_2742_:
{
if (v___x_2741_ == 0)
{
lean_object* v_pkgUrlMap_2743_; lean_object* v___x_2744_; 
v_pkgUrlMap_2743_ = lean_ctor_get(v_lakeEnv_2398_, 5);
v___x_2744_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgUrlMap_2743_, v_name_2562_);
if (lean_obj_tag(v___x_2744_) == 0)
{
lean_inc_ref(v_url_2564_);
v___y_2678_ = v_url_2564_;
goto v___jp_2677_;
}
else
{
lean_object* v_val_2745_; 
v_val_2745_ = lean_ctor_get(v___x_2744_, 0);
lean_inc(v_val_2745_);
lean_dec_ref_known(v___x_2744_, 1);
v___y_2678_ = v_val_2745_;
goto v___jp_2677_;
}
}
else
{
lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; uint8_t v___x_2749_; 
v___x_2746_ = ((lean_object*)(l_Lake_PackageEntry_materialize___closed__0));
lean_inc_ref(v_gitDir_2664_);
v___x_2747_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_2746_, v_gitDir_2664_);
v___x_2748_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_2749_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_2749_ == 0)
{
v___y_2730_ = v___x_2741_;
v_a_2731_ = v___x_2747_;
goto v___jp_2729_;
}
else
{
lean_object* v___x_2750_; uint8_t v___x_2751_; 
v___x_2750_ = lean_box(0);
v___x_2751_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_2751_ == 0)
{
if (v___x_2749_ == 0)
{
v___y_2730_ = v___x_2741_;
v_a_2731_ = v___x_2747_;
goto v___jp_2729_;
}
else
{
size_t v___x_2752_; size_t v___x_2753_; lean_object* v___x_2754_; 
v___x_2752_ = ((size_t)0ULL);
v___x_2753_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_2754_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_2748_, v___x_2752_, v___x_2753_, v___x_2750_, v_a_2401_);
if (lean_obj_tag(v___x_2754_) == 0)
{
lean_dec_ref_known(v___x_2754_, 1);
v___y_2730_ = v___x_2741_;
v_a_2731_ = v___x_2747_;
goto v___jp_2729_;
}
else
{
lean_object* v_a_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2762_; 
lean_dec(v___x_2747_);
lean_dec_ref(v_gitDir_2664_);
lean_dec_ref(v_relGitDir_2659_);
lean_dec_ref(v___x_2568_);
lean_dec(v_subDir_x3f_2566_);
lean_dec_ref(v_rev_2565_);
lean_dec_ref(v_url_2564_);
lean_dec_ref(v_wsDir_2399_);
lean_dec_ref(v_manifestEntry_2397_);
v_a_2755_ = lean_ctor_get(v___x_2754_, 0);
v_isSharedCheck_2762_ = !lean_is_exclusive(v___x_2754_);
if (v_isSharedCheck_2762_ == 0)
{
v___x_2757_ = v___x_2754_;
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_a_2755_);
lean_dec(v___x_2754_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v___x_2760_; 
if (v_isShared_2758_ == 0)
{
v___x_2760_ = v___x_2757_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_a_2755_);
v___x_2760_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
return v___x_2760_;
}
}
}
}
}
else
{
size_t v___x_2763_; size_t v___x_2764_; lean_object* v___x_2765_; 
v___x_2763_ = ((size_t)0ULL);
v___x_2764_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_2765_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_2748_, v___x_2763_, v___x_2764_, v___x_2750_, v_a_2401_);
if (lean_obj_tag(v___x_2765_) == 0)
{
lean_dec_ref_known(v___x_2765_, 1);
v___y_2730_ = v___x_2741_;
v_a_2731_ = v___x_2747_;
goto v___jp_2729_;
}
else
{
lean_object* v_a_2766_; lean_object* v___x_2768_; uint8_t v_isShared_2769_; uint8_t v_isSharedCheck_2773_; 
lean_dec(v___x_2747_);
lean_dec_ref(v_gitDir_2664_);
lean_dec_ref(v_relGitDir_2659_);
lean_dec_ref(v___x_2568_);
lean_dec(v_subDir_x3f_2566_);
lean_dec_ref(v_rev_2565_);
lean_dec_ref(v_url_2564_);
lean_dec_ref(v_wsDir_2399_);
lean_dec_ref(v_manifestEntry_2397_);
v_a_2766_ = lean_ctor_get(v___x_2765_, 0);
v_isSharedCheck_2773_ = !lean_is_exclusive(v___x_2765_);
if (v_isSharedCheck_2773_ == 0)
{
v___x_2768_ = v___x_2765_;
v_isShared_2769_ = v_isSharedCheck_2773_;
goto v_resetjp_2767_;
}
else
{
lean_inc(v_a_2766_);
lean_dec(v___x_2765_);
v___x_2768_ = lean_box(0);
v_isShared_2769_ = v_isSharedCheck_2773_;
goto v_resetjp_2767_;
}
v_resetjp_2767_:
{
lean_object* v___x_2771_; 
if (v_isShared_2769_ == 0)
{
v___x_2771_ = v___x_2768_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2772_, 0, v_a_2766_);
v___x_2771_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
return v___x_2771_;
}
}
}
}
}
}
}
}
v___jp_2403_:
{
lean_object* v___x_2408_; lean_object* v___x_2409_; 
v___x_2408_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2408_, 0, v___y_2405_);
lean_ctor_set(v___x_2408_, 1, v___y_2406_);
lean_ctor_set(v___x_2408_, 2, v___y_2404_);
lean_ctor_set(v___x_2408_, 3, v_a_2407_);
lean_ctor_set(v___x_2408_, 4, v_manifestEntry_2397_);
v___x_2409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2409_, 0, v___x_2408_);
return v___x_2409_;
}
v___jp_2410_:
{
lean_object* v___x_2418_; uint8_t v___x_2419_; 
v___x_2418_ = lean_array_get_size(v___y_2414_);
v___x_2419_ = lean_nat_dec_lt(v___y_2413_, v___x_2418_);
if (v___x_2419_ == 0)
{
v___y_2404_ = v___y_2411_;
v___y_2405_ = v___y_2412_;
v___y_2406_ = v___y_2416_;
v_a_2407_ = v_val_2417_;
goto v___jp_2403_;
}
else
{
lean_object* v___x_2420_; uint8_t v___x_2421_; 
v___x_2420_ = lean_box(0);
v___x_2421_ = lean_nat_dec_le(v___x_2418_, v___x_2418_);
if (v___x_2421_ == 0)
{
if (v___x_2419_ == 0)
{
v___y_2404_ = v___y_2411_;
v___y_2405_ = v___y_2412_;
v___y_2406_ = v___y_2416_;
v_a_2407_ = v_val_2417_;
goto v___jp_2403_;
}
else
{
size_t v___x_2422_; size_t v___x_2423_; lean_object* v___x_2424_; 
v___x_2422_ = ((size_t)0ULL);
v___x_2423_ = lean_usize_of_nat(v___x_2418_);
v___x_2424_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_2414_, v___x_2422_, v___x_2423_, v___x_2420_, v___y_2415_);
if (lean_obj_tag(v___x_2424_) == 0)
{
lean_dec_ref_known(v___x_2424_, 1);
v___y_2404_ = v___y_2411_;
v___y_2405_ = v___y_2412_;
v___y_2406_ = v___y_2416_;
v_a_2407_ = v_val_2417_;
goto v___jp_2403_;
}
else
{
lean_object* v_a_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2432_; 
lean_dec_ref(v_val_2417_);
lean_dec_ref(v___y_2416_);
lean_dec_ref(v___y_2412_);
lean_dec_ref(v___y_2411_);
lean_dec_ref(v_manifestEntry_2397_);
v_a_2425_ = lean_ctor_get(v___x_2424_, 0);
v_isSharedCheck_2432_ = !lean_is_exclusive(v___x_2424_);
if (v_isSharedCheck_2432_ == 0)
{
v___x_2427_ = v___x_2424_;
v_isShared_2428_ = v_isSharedCheck_2432_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_a_2425_);
lean_dec(v___x_2424_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2432_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v___x_2430_; 
if (v_isShared_2428_ == 0)
{
v___x_2430_ = v___x_2427_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v_a_2425_);
v___x_2430_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
return v___x_2430_;
}
}
}
}
}
else
{
size_t v___x_2433_; size_t v___x_2434_; lean_object* v___x_2435_; 
v___x_2433_ = ((size_t)0ULL);
v___x_2434_ = lean_usize_of_nat(v___x_2418_);
v___x_2435_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_2414_, v___x_2433_, v___x_2434_, v___x_2420_, v___y_2415_);
if (lean_obj_tag(v___x_2435_) == 0)
{
lean_dec_ref_known(v___x_2435_, 1);
v___y_2404_ = v___y_2411_;
v___y_2405_ = v___y_2412_;
v___y_2406_ = v___y_2416_;
v_a_2407_ = v_val_2417_;
goto v___jp_2403_;
}
else
{
lean_object* v_a_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2443_; 
lean_dec_ref(v_val_2417_);
lean_dec_ref(v___y_2416_);
lean_dec_ref(v___y_2412_);
lean_dec_ref(v___y_2411_);
lean_dec_ref(v_manifestEntry_2397_);
v_a_2436_ = lean_ctor_get(v___x_2435_, 0);
v_isSharedCheck_2443_ = !lean_is_exclusive(v___x_2435_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2438_ = v___x_2435_;
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_a_2436_);
lean_dec(v___x_2435_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
lean_object* v___x_2441_; 
if (v_isShared_2439_ == 0)
{
v___x_2441_ = v___x_2438_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v_a_2436_);
v___x_2441_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
return v___x_2441_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize___boxed(lean_object* v_manifestEntry_2800_, lean_object* v_lakeEnv_2801_, lean_object* v_wsDir_2802_, lean_object* v_relPkgsDir_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_){
_start:
{
lean_object* v_res_2806_; 
v_res_2806_ = l_Lake_PackageEntry_materialize(v_manifestEntry_2800_, v_lakeEnv_2801_, v_wsDir_2802_, v_relPkgsDir_2803_, v_a_2804_);
lean_dec_ref(v_a_2804_);
lean_dec_ref(v_lakeEnv_2801_);
return v_res_2806_;
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

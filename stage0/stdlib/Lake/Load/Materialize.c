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
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lake_defaultConfigFile;
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
extern lean_object* l_Lake_defaultManifestFile;
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lake_Manifest_load(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lake_resolvePath(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_gcAuto(lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_pruneRemote(lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_GitRepo_hasNoDiff(lean_object*);
lean_object* l_Lake_GitRepo_clean(lean_object*, lean_object*);
lean_object* l_instDecidableEqString___boxed(lean_object*, lean_object*);
uint8_t l_Option_instDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_checkoutDetach(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_resolveRevision_x3f(lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_fetchRevision_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_addRemote(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_GitRev_isFullSha1(lean_object*);
lean_object* l_Lake_GitRepo_findCommit_x3f(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_setRemoteUrl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_createDirAll(lean_object*);
lean_object* l_Lake_GitRepo_quietInit(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lake_GitRepo_getRemoteUrl_x3f(lean_object*, lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
uint8_t l_System_FilePath_pathExists(lean_object*);
extern lean_object* l_Lake_Git_defaultRemote;
extern lean_object* l_Lake_Git_upstreamBranch;
lean_object* l_Lake_GitRepo_getHeadRevision(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lake_removeDirAllIfExists(lean_object*);
lean_object* l_Lake_copyDirAll(lean_object*, lean_object*);
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
lean_object* l_instMonadEIO___redArg();
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
extern lean_object* l_Lake_instInhabitedPackageEntry_default;
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = ": failed to resolve path:\n  "};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__0 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__0_value;
static const lean_closure_object l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__1 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__1_value;
static lean_once_cell_t l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__2;
static lean_once_cell_t l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3;
static const lean_array_object l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4_value;
static lean_once_cell_t l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__5;
static lean_once_cell_t l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6;
static lean_once_cell_t l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7;
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = ": repository has local changes:\n  "};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff___closed__0 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = ": checking out revision '"};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__0 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__0_value;
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__1 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HEAD"};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__0 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__0_value;
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = ": failed to fetch the package revision\n  "};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__1 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__1_value;
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "\nfrom the Git repository at\n  "};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__2 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__2_value;
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = ": fetching revision '"};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__3 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__3_value;
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "' from "};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__4 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__4_value;
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = ": remote URL changed\n  old: "};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__5 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__5_value;
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "\n  new: "};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__6 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__6_value;
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = ": materializing new dependency"};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__7 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__7_value;
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = ".git"};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__8 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__8_value;
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
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_mkPath(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_mkPath___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = ": package directory not found: "};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0_value;
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lake_PackageEntry_materialize_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lake_PackageEntry_materialize_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lake_PackageEntry_materialize_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lake_PackageEntry_materialize_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___lam__0(lean_object* v_x_1_, lean_object* v___y_2_, lean_object* v___y_3_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
lean_inc_ref(v___y_3_);
v___x_5_ = lean_apply_2(v___y_3_, v___y_2_, lean_box(0));
v___x_6_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT void l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1_ = stack[0].m_obj;
lean_object* v___y_2_ = stack[1].m_obj;
lean_object* v___y_3_ = stack[2].m_obj;
lean_object* v_res_7_;
v_res_7_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___lam__0(v_x_1_, v___y_2_, v___y_3_);
stack->m_obj
 = v_res_7_;
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___lam__0___boxed(lean_object* v_x_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___lam__0(v_x_8_, v___y_9_, v___y_10_);
lean_dec_ref(v___y_10_);
return v_res_12_;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__2(void){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = l_instMonadEIO___redArg();
return v___x_15_;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3(void){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_16_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__2, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__2_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__2);
v___x_17_ = l_ReaderT_instMonad___redArg(v___x_16_);
return v___x_17_;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__5(void){
_start:
{
lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_20_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_21_ = lean_array_get_size(v___x_20_);
return v___x_21_;
}
}
static uint8_t _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6(void){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; uint8_t v___x_24_; 
v___x_22_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__5, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__5);
v___x_23_ = lean_unsigned_to_nat(0u);
v___x_24_ = lean_nat_dec_lt(v___x_23_, v___x_22_);
return v___x_24_;
}
}
static size_t _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7(void){
_start:
{
lean_object* v___x_25_; size_t v___x_26_; 
v___x_25_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__5, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__5);
v___x_26_ = lean_usize_of_nat(v___x_25_);
return v___x_26_;
}
}
lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl(lean_object* v_name_27_, lean_object* v_url_28_, lean_object* v_a_29_){
_start:
{
lean_object* v_a_32_; lean_object* v___f_49_; lean_object* v___y_51_; lean_object* v___y_52_; lean_object* v___y_53_; lean_object* v_val_54_; uint8_t v_a_71_; lean_object* v___x_81_; lean_object* v___x_82_; uint8_t v___x_83_; uint8_t v___x_84_; 
v___f_49_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__1));
v___x_81_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3);
v___x_82_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_83_ = l_System_FilePath_pathExists(v_url_28_);
v___x_84_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_84_ == 0)
{
v_a_71_ = v___x_83_;
goto v___jp_70_;
}
else
{
lean_object* v___x_85_; size_t v___x_86_; size_t v___x_87_; lean_object* v___x_1286__overap_88_; lean_object* v___x_89_; 
v___x_85_ = lean_box(0);
v___x_86_ = ((size_t)0ULL);
v___x_87_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_1286__overap_88_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_81_, v___f_49_, v___x_82_, v___x_86_, v___x_87_, v___x_85_);
lean_inc_ref(v_a_29_);
v___x_89_ = lean_apply_2(v___x_1286__overap_88_, v_a_29_, lean_box(0));
if (lean_obj_tag(v___x_89_) == 0)
{
lean_dec_ref_known(v___x_89_, 1);
v_a_71_ = v___x_83_;
goto v___jp_70_;
}
else
{
lean_object* v_a_90_; lean_object* v___x_92_; uint8_t v_isShared_93_; uint8_t v_isSharedCheck_97_; 
lean_dec_ref(v_url_28_);
lean_dec_ref(v_name_27_);
v_a_90_ = lean_ctor_get(v___x_89_, 0);
v_isSharedCheck_97_ = !lean_is_exclusive(v___x_89_);
if (v_isSharedCheck_97_ == 0)
{
v___x_92_ = v___x_89_;
v_isShared_93_ = v_isSharedCheck_97_;
goto v_resetjp_91_;
}
else
{
lean_inc(v_a_90_);
lean_dec(v___x_89_);
v___x_92_ = lean_box(0);
v_isShared_93_ = v_isSharedCheck_97_;
goto v_resetjp_91_;
}
v_resetjp_91_:
{
lean_object* v___x_95_; 
if (v_isShared_93_ == 0)
{
v___x_95_ = v___x_92_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v_a_90_);
v___x_95_ = v_reuseFailAlloc_96_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
return v___x_95_;
}
}
}
}
v___jp_31_:
{
if (lean_obj_tag(v_a_32_) == 1)
{
lean_object* v_val_33_; lean_object* v___x_35_; uint8_t v_isShared_36_; uint8_t v_isSharedCheck_40_; 
lean_dec_ref(v_url_28_);
lean_dec_ref(v_name_27_);
v_val_33_ = lean_ctor_get(v_a_32_, 0);
v_isSharedCheck_40_ = !lean_is_exclusive(v_a_32_);
if (v_isSharedCheck_40_ == 0)
{
v___x_35_ = v_a_32_;
v_isShared_36_ = v_isSharedCheck_40_;
goto v_resetjp_34_;
}
else
{
lean_inc(v_val_33_);
lean_dec(v_a_32_);
v___x_35_ = lean_box(0);
v_isShared_36_ = v_isSharedCheck_40_;
goto v_resetjp_34_;
}
v_resetjp_34_:
{
lean_object* v___x_38_; 
if (v_isShared_36_ == 0)
{
lean_ctor_set_tag(v___x_35_, 0);
v___x_38_ = v___x_35_;
goto v_reusejp_37_;
}
else
{
lean_object* v_reuseFailAlloc_39_; 
v_reuseFailAlloc_39_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_39_, 0, v_val_33_);
v___x_38_ = v_reuseFailAlloc_39_;
goto v_reusejp_37_;
}
v_reusejp_37_:
{
return v___x_38_;
}
}
}
else
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; uint8_t v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
lean_dec(v_a_32_);
v___x_41_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__0));
v___x_42_ = lean_string_append(v_name_27_, v___x_41_);
v___x_43_ = lean_string_append(v___x_42_, v_url_28_);
lean_dec_ref(v_url_28_);
v___x_44_ = 3;
v___x_45_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_45_, 0, v___x_43_);
lean_ctor_set_uint8(v___x_45_, sizeof(void*)*1, v___x_44_);
lean_inc_ref(v_a_29_);
v___x_46_ = lean_apply_2(v_a_29_, v___x_45_, lean_box(0));
v___x_47_ = lean_box(0);
v___x_48_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_48_, 0, v___x_47_);
return v___x_48_;
}
}
v___jp_50_:
{
lean_object* v___x_55_; uint8_t v___x_56_; 
v___x_55_ = lean_array_get_size(v___y_53_);
v___x_56_ = lean_nat_dec_lt(v___y_52_, v___x_55_);
if (v___x_56_ == 0)
{
v_a_32_ = v_val_54_;
goto v___jp_31_;
}
else
{
lean_object* v___x_57_; size_t v___x_58_; size_t v___x_59_; lean_object* v___x_1563__overap_60_; lean_object* v___x_61_; 
v___x_57_ = lean_box(0);
v___x_58_ = ((size_t)0ULL);
v___x_59_ = lean_usize_of_nat(v___x_55_);
lean_inc_ref(v___y_53_);
lean_inc_ref(v___y_51_);
v___x_1563__overap_60_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___y_51_, v___f_49_, v___y_53_, v___x_58_, v___x_59_, v___x_57_);
lean_inc_ref(v_a_29_);
v___x_61_ = lean_apply_2(v___x_1563__overap_60_, v_a_29_, lean_box(0));
if (lean_obj_tag(v___x_61_) == 0)
{
lean_dec_ref_known(v___x_61_, 1);
v_a_32_ = v_val_54_;
goto v___jp_31_;
}
else
{
lean_object* v_a_62_; lean_object* v___x_64_; uint8_t v_isShared_65_; uint8_t v_isSharedCheck_69_; 
lean_dec(v_val_54_);
lean_dec_ref(v_url_28_);
lean_dec_ref(v_name_27_);
v_a_62_ = lean_ctor_get(v___x_61_, 0);
v_isSharedCheck_69_ = !lean_is_exclusive(v___x_61_);
if (v_isSharedCheck_69_ == 0)
{
v___x_64_ = v___x_61_;
v_isShared_65_ = v_isSharedCheck_69_;
goto v_resetjp_63_;
}
else
{
lean_inc(v_a_62_);
lean_dec(v___x_61_);
v___x_64_ = lean_box(0);
v_isShared_65_ = v_isSharedCheck_69_;
goto v_resetjp_63_;
}
v_resetjp_63_:
{
lean_object* v___x_67_; 
if (v_isShared_65_ == 0)
{
v___x_67_ = v___x_64_;
goto v_reusejp_66_;
}
else
{
lean_object* v_reuseFailAlloc_68_; 
v_reuseFailAlloc_68_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_68_, 0, v_a_62_);
v___x_67_ = v_reuseFailAlloc_68_;
goto v_reusejp_66_;
}
v_reusejp_66_:
{
return v___x_67_;
}
}
}
}
}
v___jp_70_:
{
if (v_a_71_ == 0)
{
lean_object* v___x_72_; 
lean_dec_ref(v_name_27_);
v___x_72_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_72_, 0, v_url_28_);
return v___x_72_;
}
else
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; uint8_t v___x_78_; 
v___x_73_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3);
v___x_74_ = lean_unsigned_to_nat(0u);
v___x_75_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_url_28_);
v___x_76_ = l_Lake_resolvePath(v_url_28_);
v___x_77_ = lean_string_utf8_byte_size(v___x_76_);
v___x_78_ = lean_nat_dec_eq(v___x_77_, v___x_74_);
if (v___x_78_ == 0)
{
lean_object* v___x_79_; 
v___x_79_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_79_, 0, v___x_76_);
v___y_51_ = v___x_73_;
v___y_52_ = v___x_74_;
v___y_53_ = v___x_75_;
v_val_54_ = v___x_79_;
goto v___jp_50_;
}
else
{
lean_object* v___x_80_; 
lean_dec_ref(v___x_76_);
v___x_80_ = lean_box(0);
v___y_51_ = v___x_73_;
v___y_52_ = v___x_74_;
v___y_53_ = v___x_75_;
v_val_54_ = v___x_80_;
goto v___jp_50_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_27_ = stack[0].m_obj;
lean_object* v_url_28_ = stack[1].m_obj;
lean_object* v_a_29_ = stack[2].m_obj;
lean_object* v_res_98_;
v_res_98_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl(v_name_27_, v_url_28_, v_a_29_);
stack->m_obj
 = v_res_98_;
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___boxed(lean_object* v_name_99_, lean_object* v_url_100_, lean_object* v_a_101_, lean_object* v_a_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl(v_name_99_, v_url_100_, v_a_101_);
lean_dec_ref(v_a_101_);
return v_res_103_;
}
}
lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff(lean_object* v_name_105_, lean_object* v_repo_106_, lean_object* v_a_107_){
_start:
{
uint8_t v_a_110_; lean_object* v___f_120_; lean_object* v___x_121_; lean_object* v___x_122_; uint8_t v_val_124_; uint8_t v___x_131_; 
v___f_120_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__1));
v___x_121_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3);
v___x_122_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_106_);
v___x_131_ = l_Lake_GitRepo_hasNoDiff(v_repo_106_);
if (v___x_131_ == 0)
{
uint8_t v___x_132_; 
v___x_132_ = 1;
v_val_124_ = v___x_132_;
goto v___jp_123_;
}
else
{
uint8_t v___x_133_; 
v___x_133_ = 0;
v_val_124_ = v___x_133_;
goto v___jp_123_;
}
v___jp_109_:
{
if (v_a_110_ == 0)
{
lean_object* v___x_111_; lean_object* v___x_112_; 
lean_dec_ref(v_repo_106_);
lean_dec_ref(v_name_105_);
v___x_111_ = lean_box(0);
v___x_112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_112_, 0, v___x_111_);
return v___x_112_;
}
else
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; uint8_t v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_113_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff___closed__0));
v___x_114_ = lean_string_append(v_name_105_, v___x_113_);
v___x_115_ = lean_string_append(v___x_114_, v_repo_106_);
lean_dec_ref(v_repo_106_);
v___x_116_ = 2;
v___x_117_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_117_, 0, v___x_115_);
lean_ctor_set_uint8(v___x_117_, sizeof(void*)*1, v___x_116_);
lean_inc_ref(v_a_107_);
v___x_118_ = lean_apply_2(v_a_107_, v___x_117_, lean_box(0));
v___x_119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_119_, 0, v___x_118_);
return v___x_119_;
}
}
v___jp_123_:
{
uint8_t v___x_125_; 
v___x_125_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_125_ == 0)
{
v_a_110_ = v_val_124_;
goto v___jp_109_;
}
else
{
lean_object* v___x_126_; size_t v___x_127_; size_t v___x_128_; lean_object* v___x_786__overap_129_; lean_object* v___x_130_; 
v___x_126_ = lean_box(0);
v___x_127_ = ((size_t)0ULL);
v___x_128_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_786__overap_129_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_121_, v___f_120_, v___x_122_, v___x_127_, v___x_128_, v___x_126_);
lean_inc_ref(v_a_107_);
v___x_130_ = lean_apply_2(v___x_786__overap_129_, v_a_107_, lean_box(0));
if (lean_obj_tag(v___x_130_) == 0)
{
lean_dec_ref_known(v___x_130_, 1);
v_a_110_ = v_val_124_;
goto v___jp_109_;
}
else
{
lean_dec_ref(v_repo_106_);
lean_dec_ref(v_name_105_);
return v___x_130_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_105_ = stack[0].m_obj;
lean_object* v_repo_106_ = stack[1].m_obj;
lean_object* v_a_107_ = stack[2].m_obj;
lean_object* v_res_134_;
v_res_134_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff(v_name_105_, v_repo_106_, v_a_107_);
stack->m_obj
 = v_res_134_;
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff___boxed(lean_object* v_name_135_, lean_object* v_repo_136_, lean_object* v_a_137_, lean_object* v_a_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff(v_name_135_, v_repo_136_, v_a_137_);
lean_dec_ref(v_a_137_);
return v_res_139_;
}
}
lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout(lean_object* v_name_142_, lean_object* v_repo_143_, lean_object* v_rev_144_, lean_object* v_a_145_){
_start:
{
uint8_t v_a_148_; lean_object* v___f_158_; lean_object* v___y_160_; lean_object* v___y_161_; lean_object* v___y_162_; uint8_t v_val_163_; lean_object* v___y_179_; lean_object* v___y_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; uint8_t v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___f_158_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__1));
v___x_213_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__0));
lean_inc_ref(v_name_142_);
v___x_214_ = lean_string_append(v_name_142_, v___x_213_);
v___x_215_ = lean_string_append(v___x_214_, v_rev_144_);
v___x_216_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__1));
v___x_217_ = lean_string_append(v___x_215_, v___x_216_);
v___x_218_ = 1;
v___x_219_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_219_, 0, v___x_217_);
lean_ctor_set_uint8(v___x_219_, sizeof(void*)*1, v___x_218_);
lean_inc_ref(v_a_145_);
v___x_220_ = lean_apply_2(v_a_145_, v___x_219_, lean_box(0));
v___x_221_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3);
v___x_222_ = lean_unsigned_to_nat(0u);
v___x_223_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_143_);
v___x_224_ = l_Lake_GitRepo_checkoutDetach(v_rev_144_, v_repo_143_, v___x_223_);
if (lean_obj_tag(v___x_224_) == 0)
{
lean_object* v_a_225_; lean_object* v___x_226_; uint8_t v___x_227_; 
v_a_225_ = lean_ctor_get(v___x_224_, 1);
lean_inc(v_a_225_);
lean_dec_ref_known(v___x_224_, 2);
v___x_226_ = lean_array_get_size(v_a_225_);
v___x_227_ = lean_nat_dec_lt(v___x_222_, v___x_226_);
if (v___x_227_ == 0)
{
lean_dec(v_a_225_);
goto v___jp_180_;
}
else
{
lean_object* v___x_228_; size_t v___x_229_; size_t v___x_230_; lean_object* v___x_2319__overap_231_; lean_object* v___x_232_; 
v___x_228_ = lean_box(0);
v___x_229_ = ((size_t)0ULL);
v___x_230_ = lean_usize_of_nat(v___x_226_);
v___x_2319__overap_231_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_221_, v___f_158_, v_a_225_, v___x_229_, v___x_230_, v___x_228_);
lean_inc_ref(v_a_145_);
v___x_232_ = lean_apply_2(v___x_2319__overap_231_, v_a_145_, lean_box(0));
if (lean_obj_tag(v___x_232_) == 0)
{
lean_dec_ref_known(v___x_232_, 1);
goto v___jp_180_;
}
else
{
v___y_212_ = v___x_232_;
goto v___jp_211_;
}
}
}
else
{
lean_object* v_a_233_; lean_object* v___x_234_; uint8_t v___x_235_; 
v_a_233_ = lean_ctor_get(v___x_224_, 1);
lean_inc(v_a_233_);
lean_dec_ref_known(v___x_224_, 2);
v___x_234_ = lean_array_get_size(v_a_233_);
v___x_235_ = lean_nat_dec_lt(v___x_222_, v___x_234_);
if (v___x_235_ == 0)
{
lean_object* v___x_236_; lean_object* v___x_237_; 
lean_dec(v_a_233_);
lean_dec_ref(v_repo_143_);
lean_dec_ref(v_name_142_);
v___x_236_ = lean_box(0);
v___x_237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
return v___x_237_;
}
else
{
lean_object* v___x_238_; size_t v___x_239_; size_t v___x_240_; lean_object* v___x_2336__overap_241_; lean_object* v___x_242_; 
v___x_238_ = lean_box(0);
v___x_239_ = ((size_t)0ULL);
v___x_240_ = lean_usize_of_nat(v___x_234_);
v___x_2336__overap_241_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_221_, v___f_158_, v_a_233_, v___x_239_, v___x_240_, v___x_238_);
lean_inc_ref(v_a_145_);
v___x_242_ = lean_apply_2(v___x_2336__overap_241_, v_a_145_, lean_box(0));
if (lean_obj_tag(v___x_242_) == 0)
{
lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_249_; 
lean_dec_ref(v_repo_143_);
lean_dec_ref(v_name_142_);
v_isSharedCheck_249_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_249_ == 0)
{
lean_object* v_unused_250_; 
v_unused_250_ = lean_ctor_get(v___x_242_, 0);
lean_dec(v_unused_250_);
v___x_244_ = v___x_242_;
v_isShared_245_ = v_isSharedCheck_249_;
goto v_resetjp_243_;
}
else
{
lean_dec(v___x_242_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_249_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v___x_247_; 
if (v_isShared_245_ == 0)
{
lean_ctor_set_tag(v___x_244_, 1);
lean_ctor_set(v___x_244_, 0, v___x_238_);
v___x_247_ = v___x_244_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v___x_238_);
v___x_247_ = v_reuseFailAlloc_248_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
return v___x_247_;
}
}
}
else
{
v___y_212_ = v___x_242_;
goto v___jp_211_;
}
}
}
v___jp_147_:
{
if (v_a_148_ == 0)
{
lean_object* v___x_149_; lean_object* v___x_150_; 
lean_dec_ref(v_repo_143_);
lean_dec_ref(v_name_142_);
v___x_149_ = lean_box(0);
v___x_150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_150_, 0, v___x_149_);
return v___x_150_;
}
else
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; uint8_t v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_151_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff___closed__0));
v___x_152_ = lean_string_append(v_name_142_, v___x_151_);
v___x_153_ = lean_string_append(v___x_152_, v_repo_143_);
lean_dec_ref(v_repo_143_);
v___x_154_ = 2;
v___x_155_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_155_, 0, v___x_153_);
lean_ctor_set_uint8(v___x_155_, sizeof(void*)*1, v___x_154_);
lean_inc_ref(v_a_145_);
v___x_156_ = lean_apply_2(v_a_145_, v___x_155_, lean_box(0));
v___x_157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
return v___x_157_;
}
}
v___jp_159_:
{
lean_object* v___x_164_; uint8_t v___x_165_; 
v___x_164_ = lean_array_get_size(v___y_160_);
v___x_165_ = lean_nat_dec_lt(v___y_162_, v___x_164_);
if (v___x_165_ == 0)
{
v_a_148_ = v_val_163_;
goto v___jp_147_;
}
else
{
lean_object* v___x_166_; size_t v___x_167_; size_t v___x_168_; lean_object* v___x_2656__overap_169_; lean_object* v___x_170_; 
v___x_166_ = lean_box(0);
v___x_167_ = ((size_t)0ULL);
v___x_168_ = lean_usize_of_nat(v___x_164_);
lean_inc_ref(v___y_160_);
lean_inc_ref(v___y_161_);
v___x_2656__overap_169_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___y_161_, v___f_158_, v___y_160_, v___x_167_, v___x_168_, v___x_166_);
lean_inc_ref(v_a_145_);
v___x_170_ = lean_apply_2(v___x_2656__overap_169_, v_a_145_, lean_box(0));
if (lean_obj_tag(v___x_170_) == 0)
{
lean_dec_ref_known(v___x_170_, 1);
v_a_148_ = v_val_163_;
goto v___jp_147_;
}
else
{
lean_dec_ref(v_repo_143_);
lean_dec_ref(v_name_142_);
return v___x_170_;
}
}
}
v___jp_171_:
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; uint8_t v___x_175_; 
v___x_172_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3);
v___x_173_ = lean_unsigned_to_nat(0u);
v___x_174_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_143_);
v___x_175_ = l_Lake_GitRepo_hasNoDiff(v_repo_143_);
if (v___x_175_ == 0)
{
uint8_t v___x_176_; 
v___x_176_ = 1;
v___y_160_ = v___x_174_;
v___y_161_ = v___x_172_;
v___y_162_ = v___x_173_;
v_val_163_ = v___x_176_;
goto v___jp_159_;
}
else
{
uint8_t v___x_177_; 
v___x_177_ = 0;
v___y_160_ = v___x_174_;
v___y_161_ = v___x_172_;
v___y_162_ = v___x_173_;
v_val_163_ = v___x_177_;
goto v___jp_159_;
}
}
v___jp_178_:
{
if (lean_obj_tag(v___y_179_) == 0)
{
lean_dec_ref_known(v___y_179_, 1);
goto v___jp_171_;
}
else
{
lean_dec_ref(v_repo_143_);
lean_dec_ref(v_name_142_);
return v___y_179_;
}
}
v___jp_180_:
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_181_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3);
v___x_182_ = lean_unsigned_to_nat(0u);
v___x_183_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_143_);
v___x_184_ = l_Lake_GitRepo_clean(v_repo_143_, v___x_183_);
if (lean_obj_tag(v___x_184_) == 0)
{
lean_object* v_a_185_; lean_object* v___x_186_; uint8_t v___x_187_; 
v_a_185_ = lean_ctor_get(v___x_184_, 1);
lean_inc(v_a_185_);
lean_dec_ref_known(v___x_184_, 2);
v___x_186_ = lean_array_get_size(v_a_185_);
v___x_187_ = lean_nat_dec_lt(v___x_182_, v___x_186_);
if (v___x_187_ == 0)
{
lean_dec(v_a_185_);
goto v___jp_171_;
}
else
{
lean_object* v___x_188_; size_t v___x_189_; size_t v___x_190_; lean_object* v___x_2692__overap_191_; lean_object* v___x_192_; 
v___x_188_ = lean_box(0);
v___x_189_ = ((size_t)0ULL);
v___x_190_ = lean_usize_of_nat(v___x_186_);
v___x_2692__overap_191_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_181_, v___f_158_, v_a_185_, v___x_189_, v___x_190_, v___x_188_);
lean_inc_ref(v_a_145_);
v___x_192_ = lean_apply_2(v___x_2692__overap_191_, v_a_145_, lean_box(0));
if (lean_obj_tag(v___x_192_) == 0)
{
lean_dec_ref_known(v___x_192_, 1);
goto v___jp_171_;
}
else
{
v___y_179_ = v___x_192_;
goto v___jp_178_;
}
}
}
else
{
lean_object* v_a_193_; lean_object* v___x_194_; uint8_t v___x_195_; 
v_a_193_ = lean_ctor_get(v___x_184_, 1);
lean_inc(v_a_193_);
lean_dec_ref_known(v___x_184_, 2);
v___x_194_ = lean_array_get_size(v_a_193_);
v___x_195_ = lean_nat_dec_lt(v___x_182_, v___x_194_);
if (v___x_195_ == 0)
{
lean_object* v___x_196_; lean_object* v___x_197_; 
lean_dec(v_a_193_);
lean_dec_ref(v_repo_143_);
lean_dec_ref(v_name_142_);
v___x_196_ = lean_box(0);
v___x_197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_197_, 0, v___x_196_);
return v___x_197_;
}
else
{
lean_object* v___x_198_; size_t v___x_199_; size_t v___x_200_; lean_object* v___x_2709__overap_201_; lean_object* v___x_202_; 
v___x_198_ = lean_box(0);
v___x_199_ = ((size_t)0ULL);
v___x_200_ = lean_usize_of_nat(v___x_194_);
v___x_2709__overap_201_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_181_, v___f_158_, v_a_193_, v___x_199_, v___x_200_, v___x_198_);
lean_inc_ref(v_a_145_);
v___x_202_ = lean_apply_2(v___x_2709__overap_201_, v_a_145_, lean_box(0));
if (lean_obj_tag(v___x_202_) == 0)
{
lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_209_; 
lean_dec_ref(v_repo_143_);
lean_dec_ref(v_name_142_);
v_isSharedCheck_209_ = !lean_is_exclusive(v___x_202_);
if (v_isSharedCheck_209_ == 0)
{
lean_object* v_unused_210_; 
v_unused_210_ = lean_ctor_get(v___x_202_, 0);
lean_dec(v_unused_210_);
v___x_204_ = v___x_202_;
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
else
{
lean_dec(v___x_202_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_207_; 
if (v_isShared_205_ == 0)
{
lean_ctor_set_tag(v___x_204_, 1);
lean_ctor_set(v___x_204_, 0, v___x_198_);
v___x_207_ = v___x_204_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v___x_198_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
return v___x_207_;
}
}
}
else
{
v___y_179_ = v___x_202_;
goto v___jp_178_;
}
}
}
}
v___jp_211_:
{
if (lean_obj_tag(v___y_212_) == 0)
{
lean_dec_ref_known(v___y_212_, 1);
goto v___jp_180_;
}
else
{
lean_dec_ref(v_repo_143_);
lean_dec_ref(v_name_142_);
return v___y_212_;
}
}
}
}
LEAN_EXPORT void l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_142_ = stack[0].m_obj;
lean_object* v_repo_143_ = stack[1].m_obj;
lean_object* v_rev_144_ = stack[2].m_obj;
lean_object* v_a_145_ = stack[3].m_obj;
lean_object* v_res_251_;
v_res_251_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout(v_name_142_, v_repo_143_, v_rev_144_, v_a_145_);
stack->m_obj
 = v_res_251_;
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___boxed(lean_object* v_name_252_, lean_object* v_repo_253_, lean_object* v_rev_254_, lean_object* v_a_255_, lean_object* v_a_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout(v_name_252_, v_repo_253_, v_rev_254_, v_a_255_);
lean_dec_ref(v_a_255_);
return v_res_257_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(lean_object* v_as_258_, size_t v_i_259_, size_t v_stop_260_, lean_object* v_b_261_, lean_object* v___y_262_){
_start:
{
uint8_t v___x_264_; 
v___x_264_ = lean_usize_dec_eq(v_i_259_, v_stop_260_);
if (v___x_264_ == 0)
{
lean_object* v___x_265_; lean_object* v___x_266_; size_t v___x_267_; size_t v___x_268_; 
v___x_265_ = lean_array_uget_borrowed(v_as_258_, v_i_259_);
lean_inc_ref(v___y_262_);
lean_inc(v___x_265_);
v___x_266_ = lean_apply_2(v___y_262_, v___x_265_, lean_box(0));
v___x_267_ = ((size_t)1ULL);
v___x_268_ = lean_usize_add(v_i_259_, v___x_267_);
v_i_259_ = v___x_268_;
v_b_261_ = v___x_266_;
goto _start;
}
else
{
lean_object* v___x_270_; 
v___x_270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_270_, 0, v_b_261_);
return v___x_270_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_258_ = stack[0].m_obj;
size_t v_i_259_ = stack[1].m_num;
size_t v_stop_260_ = stack[2].m_num;
lean_object* v_b_261_ = stack[3].m_obj;
lean_object* v___y_262_ = stack[4].m_obj;
lean_object* v_res_271_;
v_res_271_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_as_258_, v_i_259_, v_stop_260_, v_b_261_, v___y_262_);
stack->m_obj
 = v_res_271_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0___boxed(lean_object* v_as_272_, lean_object* v_i_273_, lean_object* v_stop_274_, lean_object* v_b_275_, lean_object* v___y_276_, lean_object* v___y_277_){
_start:
{
size_t v_i_boxed_278_; size_t v_stop_boxed_279_; lean_object* v_res_280_; 
v_i_boxed_278_ = lean_unbox_usize(v_i_273_);
lean_dec(v_i_273_);
v_stop_boxed_279_ = lean_unbox_usize(v_stop_274_);
lean_dec(v_stop_274_);
v_res_280_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_as_272_, v_i_boxed_278_, v_stop_boxed_279_, v_b_275_, v___y_276_);
lean_dec_ref(v___y_276_);
lean_dec_ref(v_as_272_);
return v_res_280_;
}
}
lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo(lean_object* v_name_290_, lean_object* v_repo_291_, lean_object* v_url_292_, lean_object* v_rev_x3f_293_, lean_object* v_a_294_){
_start:
{
lean_object* v___y_306_; lean_object* v___y_345_; lean_object* v___y_346_; lean_object* v___y_348_; lean_object* v___y_349_; lean_object* v___y_378_; lean_object* v___y_379_; uint8_t v_a_380_; lean_object* v___y_388_; uint8_t v_a_389_; lean_object* v___y_397_; lean_object* v___y_398_; lean_object* v___y_399_; lean_object* v___y_400_; uint8_t v_val_401_; uint8_t v___y_409_; lean_object* v___y_410_; lean_object* v___y_411_; uint8_t v___y_417_; lean_object* v___y_418_; lean_object* v___y_419_; lean_object* v___y_420_; uint8_t v___y_422_; lean_object* v___y_423_; lean_object* v___y_424_; uint8_t v___y_453_; lean_object* v___y_454_; lean_object* v___y_455_; lean_object* v___y_456_; lean_object* v___y_458_; lean_object* v___y_459_; lean_object* v___y_460_; uint8_t v_val_461_; lean_object* v___y_469_; lean_object* v___y_470_; lean_object* v___y_471_; lean_object* v___y_472_; lean_object* v_a_473_; lean_object* v___y_516_; lean_object* v___y_517_; lean_object* v___y_518_; lean_object* v___y_519_; lean_object* v_a_520_; lean_object* v___y_542_; lean_object* v___y_543_; lean_object* v___y_544_; lean_object* v___y_545_; lean_object* v___y_584_; lean_object* v___y_585_; lean_object* v___y_586_; lean_object* v___y_587_; lean_object* v___y_589_; lean_object* v___y_590_; lean_object* v___y_591_; lean_object* v___y_620_; lean_object* v___y_621_; lean_object* v___y_622_; lean_object* v___y_623_; lean_object* v___y_625_; uint8_t v_a_626_; lean_object* v___y_634_; uint8_t v_a_635_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; uint8_t v_val_646_; lean_object* v___y_654_; uint8_t v___y_655_; uint8_t v___y_656_; lean_object* v___y_661_; uint8_t v___y_662_; uint8_t v___y_663_; lean_object* v___y_664_; lean_object* v___y_666_; uint8_t v___y_667_; uint8_t v___y_668_; lean_object* v___y_697_; uint8_t v___y_698_; uint8_t v___y_699_; lean_object* v___y_700_; lean_object* v___y_702_; lean_object* v___y_703_; lean_object* v___y_704_; uint8_t v___y_705_; lean_object* v___y_706_; uint8_t v___y_707_; lean_object* v_a_708_; lean_object* v___y_752_; lean_object* v___y_753_; lean_object* v___y_754_; uint8_t v_val_755_; lean_object* v___y_763_; lean_object* v___y_764_; lean_object* v___y_765_; lean_object* v___y_766_; lean_object* v_a_767_; lean_object* v___y_784_; lean_object* v___y_785_; lean_object* v___y_786_; lean_object* v___y_787_; lean_object* v___y_797_; lean_object* v___y_798_; lean_object* v___y_799_; lean_object* v___y_800_; lean_object* v___y_802_; lean_object* v___y_803_; lean_object* v___y_804_; lean_object* v___y_805_; lean_object* v___y_807_; lean_object* v___y_808_; lean_object* v___y_809_; lean_object* v_a_810_; lean_object* v___y_883_; lean_object* v___y_884_; lean_object* v___y_885_; uint8_t v_a_886_; lean_object* v___y_948_; lean_object* v___y_949_; lean_object* v_a_950_; lean_object* v___y_961_; lean_object* v___y_962_; lean_object* v_a_963_; lean_object* v___y_974_; lean_object* v___y_975_; lean_object* v___y_976_; lean_object* v___y_977_; lean_object* v_val_978_; lean_object* v___y_986_; lean_object* v___y_987_; uint8_t v_a_988_; lean_object* v___y_997_; 
if (lean_obj_tag(v_rev_x3f_293_) == 0)
{
lean_object* v___x_1006_; 
v___x_1006_ = l_Lake_Git_upstreamBranch;
v___y_997_ = v___x_1006_;
goto v___jp_996_;
}
else
{
lean_object* v_val_1007_; 
v_val_1007_ = lean_ctor_get(v_rev_x3f_293_, 0);
lean_inc(v_val_1007_);
lean_dec_ref_known(v_rev_x3f_293_, 1);
v___y_997_ = v_val_1007_;
goto v___jp_996_;
}
v___jp_296_:
{
lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_297_ = lean_box(0);
v___x_298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
return v___x_298_;
}
v___jp_299_:
{
lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_300_ = lean_box(0);
v___x_301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
return v___x_301_;
}
v___jp_302_:
{
lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_303_ = lean_box(0);
v___x_304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_304_, 0, v___x_303_);
return v___x_304_;
}
v___jp_305_:
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_307_ = lean_unsigned_to_nat(0u);
v___x_308_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_309_ = l_Lake_GitRepo_gcAuto(v_repo_291_, v___x_308_);
if (lean_obj_tag(v___x_309_) == 0)
{
lean_object* v_a_310_; lean_object* v_a_311_; lean_object* v___x_312_; uint8_t v___x_313_; 
v_a_310_ = lean_ctor_get(v___x_309_, 0);
lean_inc(v_a_310_);
v_a_311_ = lean_ctor_get(v___x_309_, 1);
lean_inc(v_a_311_);
lean_dec_ref_known(v___x_309_, 2);
v___x_312_ = lean_array_get_size(v_a_311_);
v___x_313_ = lean_nat_dec_lt(v___x_307_, v___x_312_);
if (v___x_313_ == 0)
{
lean_object* v___x_314_; 
lean_dec(v_a_311_);
v___x_314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_314_, 0, v_a_310_);
return v___x_314_;
}
else
{
lean_object* v___x_315_; size_t v___x_316_; size_t v___x_317_; lean_object* v___x_318_; 
v___x_315_ = lean_box(0);
v___x_316_ = ((size_t)0ULL);
v___x_317_ = lean_usize_of_nat(v___x_312_);
v___x_318_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_311_, v___x_316_, v___x_317_, v___x_315_, v___y_306_);
lean_dec(v_a_311_);
if (lean_obj_tag(v___x_318_) == 0)
{
lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_325_; 
v_isSharedCheck_325_ = !lean_is_exclusive(v___x_318_);
if (v_isSharedCheck_325_ == 0)
{
lean_object* v_unused_326_; 
v_unused_326_ = lean_ctor_get(v___x_318_, 0);
lean_dec(v_unused_326_);
v___x_320_ = v___x_318_;
v_isShared_321_ = v_isSharedCheck_325_;
goto v_resetjp_319_;
}
else
{
lean_dec(v___x_318_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_325_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_323_; 
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 0, v_a_310_);
v___x_323_ = v___x_320_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v_a_310_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
}
else
{
lean_dec(v_a_310_);
return v___x_318_;
}
}
}
else
{
lean_object* v_a_327_; lean_object* v___x_328_; uint8_t v___x_329_; 
v_a_327_ = lean_ctor_get(v___x_309_, 1);
lean_inc(v_a_327_);
lean_dec_ref_known(v___x_309_, 2);
v___x_328_ = lean_array_get_size(v_a_327_);
v___x_329_ = lean_nat_dec_lt(v___x_307_, v___x_328_);
if (v___x_329_ == 0)
{
lean_object* v___x_330_; lean_object* v___x_331_; 
lean_dec(v_a_327_);
v___x_330_ = lean_box(0);
v___x_331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_331_, 0, v___x_330_);
return v___x_331_;
}
else
{
lean_object* v___x_332_; size_t v___x_333_; size_t v___x_334_; lean_object* v___x_335_; 
v___x_332_ = lean_box(0);
v___x_333_ = ((size_t)0ULL);
v___x_334_ = lean_usize_of_nat(v___x_328_);
v___x_335_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_327_, v___x_333_, v___x_334_, v___x_332_, v___y_306_);
lean_dec(v_a_327_);
if (lean_obj_tag(v___x_335_) == 0)
{
lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_342_; 
v_isSharedCheck_342_ = !lean_is_exclusive(v___x_335_);
if (v_isSharedCheck_342_ == 0)
{
lean_object* v_unused_343_; 
v_unused_343_ = lean_ctor_get(v___x_335_, 0);
lean_dec(v_unused_343_);
v___x_337_ = v___x_335_;
v_isShared_338_ = v_isSharedCheck_342_;
goto v_resetjp_336_;
}
else
{
lean_dec(v___x_335_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_342_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___x_340_; 
if (v_isShared_338_ == 0)
{
lean_ctor_set_tag(v___x_337_, 1);
lean_ctor_set(v___x_337_, 0, v___x_332_);
v___x_340_ = v___x_337_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v___x_332_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
return v___x_340_;
}
}
}
else
{
return v___x_335_;
}
}
}
}
v___jp_344_:
{
if (lean_obj_tag(v___y_346_) == 0)
{
lean_dec_ref_known(v___y_346_, 1);
v___y_306_ = v___y_345_;
goto v___jp_305_;
}
else
{
lean_dec_ref(v_repo_291_);
return v___y_346_;
}
}
v___jp_347_:
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_350_ = lean_unsigned_to_nat(0u);
v___x_351_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_291_);
lean_inc_ref(v___y_348_);
v___x_352_ = l_Lake_GitRepo_pruneRemote(v___y_348_, v_repo_291_, v___x_351_);
if (lean_obj_tag(v___x_352_) == 0)
{
lean_object* v_a_353_; lean_object* v___x_354_; uint8_t v___x_355_; 
v_a_353_ = lean_ctor_get(v___x_352_, 1);
lean_inc(v_a_353_);
lean_dec_ref_known(v___x_352_, 2);
v___x_354_ = lean_array_get_size(v_a_353_);
v___x_355_ = lean_nat_dec_lt(v___x_350_, v___x_354_);
if (v___x_355_ == 0)
{
lean_dec(v_a_353_);
v___y_306_ = v___y_349_;
goto v___jp_305_;
}
else
{
lean_object* v___x_356_; size_t v___x_357_; size_t v___x_358_; lean_object* v___x_359_; 
v___x_356_ = lean_box(0);
v___x_357_ = ((size_t)0ULL);
v___x_358_ = lean_usize_of_nat(v___x_354_);
v___x_359_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_353_, v___x_357_, v___x_358_, v___x_356_, v___y_349_);
lean_dec(v_a_353_);
if (lean_obj_tag(v___x_359_) == 0)
{
lean_dec_ref_known(v___x_359_, 1);
v___y_306_ = v___y_349_;
goto v___jp_305_;
}
else
{
v___y_345_ = v___y_349_;
v___y_346_ = v___x_359_;
goto v___jp_344_;
}
}
}
else
{
lean_object* v_a_360_; lean_object* v___x_361_; uint8_t v___x_362_; 
v_a_360_ = lean_ctor_get(v___x_352_, 1);
lean_inc(v_a_360_);
lean_dec_ref_known(v___x_352_, 2);
v___x_361_ = lean_array_get_size(v_a_360_);
v___x_362_ = lean_nat_dec_lt(v___x_350_, v___x_361_);
if (v___x_362_ == 0)
{
lean_object* v___x_363_; lean_object* v___x_364_; 
lean_dec(v_a_360_);
lean_dec_ref(v_repo_291_);
v___x_363_ = lean_box(0);
v___x_364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_364_, 0, v___x_363_);
return v___x_364_;
}
else
{
lean_object* v___x_365_; size_t v___x_366_; size_t v___x_367_; lean_object* v___x_368_; 
v___x_365_ = lean_box(0);
v___x_366_ = ((size_t)0ULL);
v___x_367_ = lean_usize_of_nat(v___x_361_);
v___x_368_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_360_, v___x_366_, v___x_367_, v___x_365_, v___y_349_);
lean_dec(v_a_360_);
if (lean_obj_tag(v___x_368_) == 0)
{
lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_375_; 
lean_dec_ref(v_repo_291_);
v_isSharedCheck_375_ = !lean_is_exclusive(v___x_368_);
if (v_isSharedCheck_375_ == 0)
{
lean_object* v_unused_376_; 
v_unused_376_ = lean_ctor_get(v___x_368_, 0);
lean_dec(v_unused_376_);
v___x_370_ = v___x_368_;
v_isShared_371_ = v_isSharedCheck_375_;
goto v_resetjp_369_;
}
else
{
lean_dec(v___x_368_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_375_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_373_; 
if (v_isShared_371_ == 0)
{
lean_ctor_set_tag(v___x_370_, 1);
lean_ctor_set(v___x_370_, 0, v___x_365_);
v___x_373_ = v___x_370_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v___x_365_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
}
else
{
v___y_345_ = v___y_349_;
v___y_346_ = v___x_368_;
goto v___jp_344_;
}
}
}
}
v___jp_377_:
{
if (v_a_380_ == 0)
{
lean_dec_ref(v_name_290_);
v___y_348_ = v___y_378_;
v___y_349_ = v___y_379_;
goto v___jp_347_;
}
else
{
lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; uint8_t v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_381_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff___closed__0));
v___x_382_ = lean_string_append(v_name_290_, v___x_381_);
v___x_383_ = lean_string_append(v___x_382_, v_repo_291_);
v___x_384_ = 2;
v___x_385_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_385_, 0, v___x_383_);
lean_ctor_set_uint8(v___x_385_, sizeof(void*)*1, v___x_384_);
lean_inc_ref(v___y_379_);
v___x_386_ = lean_apply_2(v___y_379_, v___x_385_, lean_box(0));
v___y_348_ = v___y_378_;
v___y_349_ = v___y_379_;
goto v___jp_347_;
}
}
v___jp_387_:
{
if (v_a_389_ == 0)
{
lean_dec_ref(v_repo_291_);
lean_dec_ref(v_name_290_);
goto v___jp_302_;
}
else
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; uint8_t v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_390_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff___closed__0));
v___x_391_ = lean_string_append(v_name_290_, v___x_390_);
v___x_392_ = lean_string_append(v___x_391_, v_repo_291_);
lean_dec_ref(v_repo_291_);
v___x_393_ = 2;
v___x_394_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_394_, 0, v___x_392_);
lean_ctor_set_uint8(v___x_394_, sizeof(void*)*1, v___x_393_);
lean_inc_ref(v___y_388_);
v___x_395_ = lean_apply_2(v___y_388_, v___x_394_, lean_box(0));
goto v___jp_302_;
}
}
v___jp_396_:
{
lean_object* v___x_402_; uint8_t v___x_403_; 
v___x_402_ = lean_array_get_size(v___y_399_);
v___x_403_ = lean_nat_dec_lt(v___y_397_, v___x_402_);
if (v___x_403_ == 0)
{
v___y_378_ = v___y_398_;
v___y_379_ = v___y_400_;
v_a_380_ = v_val_401_;
goto v___jp_377_;
}
else
{
lean_object* v___x_404_; size_t v___x_405_; size_t v___x_406_; lean_object* v___x_407_; 
v___x_404_ = lean_box(0);
v___x_405_ = ((size_t)0ULL);
v___x_406_ = lean_usize_of_nat(v___x_402_);
v___x_407_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_399_, v___x_405_, v___x_406_, v___x_404_, v___y_400_);
if (lean_obj_tag(v___x_407_) == 0)
{
lean_dec_ref_known(v___x_407_, 1);
v___y_378_ = v___y_398_;
v___y_379_ = v___y_400_;
v_a_380_ = v_val_401_;
goto v___jp_377_;
}
else
{
lean_dec_ref(v_name_290_);
if (lean_obj_tag(v___x_407_) == 0)
{
lean_dec_ref_known(v___x_407_, 1);
v___y_348_ = v___y_398_;
v___y_349_ = v___y_400_;
goto v___jp_347_;
}
else
{
lean_dec_ref(v_repo_291_);
return v___x_407_;
}
}
}
}
v___jp_408_:
{
lean_object* v___x_412_; lean_object* v___x_413_; uint8_t v___x_414_; 
v___x_412_ = lean_unsigned_to_nat(0u);
v___x_413_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_291_);
v___x_414_ = l_Lake_GitRepo_hasNoDiff(v_repo_291_);
if (v___x_414_ == 0)
{
uint8_t v___x_415_; 
v___x_415_ = 1;
v___y_397_ = v___x_412_;
v___y_398_ = v___y_410_;
v___y_399_ = v___x_413_;
v___y_400_ = v___y_411_;
v_val_401_ = v___x_415_;
goto v___jp_396_;
}
else
{
v___y_397_ = v___x_412_;
v___y_398_ = v___y_410_;
v___y_399_ = v___x_413_;
v___y_400_ = v___y_411_;
v_val_401_ = v___y_409_;
goto v___jp_396_;
}
}
v___jp_416_:
{
if (lean_obj_tag(v___y_420_) == 0)
{
lean_dec_ref_known(v___y_420_, 1);
v___y_409_ = v___y_417_;
v___y_410_ = v___y_418_;
v___y_411_ = v___y_419_;
goto v___jp_408_;
}
else
{
lean_dec_ref(v_repo_291_);
lean_dec_ref(v_name_290_);
return v___y_420_;
}
}
v___jp_421_:
{
lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_425_ = lean_unsigned_to_nat(0u);
v___x_426_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_291_);
v___x_427_ = l_Lake_GitRepo_clean(v_repo_291_, v___x_426_);
if (lean_obj_tag(v___x_427_) == 0)
{
lean_object* v_a_428_; lean_object* v___x_429_; uint8_t v___x_430_; 
v_a_428_ = lean_ctor_get(v___x_427_, 1);
lean_inc(v_a_428_);
lean_dec_ref_known(v___x_427_, 2);
v___x_429_ = lean_array_get_size(v_a_428_);
v___x_430_ = lean_nat_dec_lt(v___x_425_, v___x_429_);
if (v___x_430_ == 0)
{
lean_dec(v_a_428_);
v___y_409_ = v___y_422_;
v___y_410_ = v___y_423_;
v___y_411_ = v___y_424_;
goto v___jp_408_;
}
else
{
lean_object* v___x_431_; size_t v___x_432_; size_t v___x_433_; lean_object* v___x_434_; 
v___x_431_ = lean_box(0);
v___x_432_ = ((size_t)0ULL);
v___x_433_ = lean_usize_of_nat(v___x_429_);
v___x_434_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_428_, v___x_432_, v___x_433_, v___x_431_, v___y_424_);
lean_dec(v_a_428_);
if (lean_obj_tag(v___x_434_) == 0)
{
lean_dec_ref_known(v___x_434_, 1);
v___y_409_ = v___y_422_;
v___y_410_ = v___y_423_;
v___y_411_ = v___y_424_;
goto v___jp_408_;
}
else
{
v___y_417_ = v___y_422_;
v___y_418_ = v___y_423_;
v___y_419_ = v___y_424_;
v___y_420_ = v___x_434_;
goto v___jp_416_;
}
}
}
else
{
lean_object* v_a_435_; lean_object* v___x_436_; uint8_t v___x_437_; 
v_a_435_ = lean_ctor_get(v___x_427_, 1);
lean_inc(v_a_435_);
lean_dec_ref_known(v___x_427_, 2);
v___x_436_ = lean_array_get_size(v_a_435_);
v___x_437_ = lean_nat_dec_lt(v___x_425_, v___x_436_);
if (v___x_437_ == 0)
{
lean_object* v___x_438_; lean_object* v___x_439_; 
lean_dec(v_a_435_);
lean_dec_ref(v_repo_291_);
lean_dec_ref(v_name_290_);
v___x_438_ = lean_box(0);
v___x_439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_439_, 0, v___x_438_);
return v___x_439_;
}
else
{
lean_object* v___x_440_; size_t v___x_441_; size_t v___x_442_; lean_object* v___x_443_; 
v___x_440_ = lean_box(0);
v___x_441_ = ((size_t)0ULL);
v___x_442_ = lean_usize_of_nat(v___x_436_);
v___x_443_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_435_, v___x_441_, v___x_442_, v___x_440_, v___y_424_);
lean_dec(v_a_435_);
if (lean_obj_tag(v___x_443_) == 0)
{
lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_450_; 
lean_dec_ref(v_repo_291_);
lean_dec_ref(v_name_290_);
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_450_ == 0)
{
lean_object* v_unused_451_; 
v_unused_451_ = lean_ctor_get(v___x_443_, 0);
lean_dec(v_unused_451_);
v___x_445_ = v___x_443_;
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
else
{
lean_dec(v___x_443_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_448_; 
if (v_isShared_446_ == 0)
{
lean_ctor_set_tag(v___x_445_, 1);
lean_ctor_set(v___x_445_, 0, v___x_440_);
v___x_448_ = v___x_445_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v___x_440_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
}
else
{
v___y_417_ = v___y_422_;
v___y_418_ = v___y_423_;
v___y_419_ = v___y_424_;
v___y_420_ = v___x_443_;
goto v___jp_416_;
}
}
}
}
v___jp_452_:
{
if (lean_obj_tag(v___y_456_) == 0)
{
lean_dec_ref_known(v___y_456_, 1);
v___y_422_ = v___y_453_;
v___y_423_ = v___y_454_;
v___y_424_ = v___y_455_;
goto v___jp_421_;
}
else
{
lean_dec_ref(v_repo_291_);
lean_dec_ref(v_name_290_);
return v___y_456_;
}
}
v___jp_457_:
{
lean_object* v___x_462_; uint8_t v___x_463_; 
v___x_462_ = lean_array_get_size(v___y_460_);
v___x_463_ = lean_nat_dec_lt(v___y_459_, v___x_462_);
if (v___x_463_ == 0)
{
v___y_388_ = v___y_458_;
v_a_389_ = v_val_461_;
goto v___jp_387_;
}
else
{
lean_object* v___x_464_; size_t v___x_465_; size_t v___x_466_; lean_object* v___x_467_; 
v___x_464_ = lean_box(0);
v___x_465_ = ((size_t)0ULL);
v___x_466_ = lean_usize_of_nat(v___x_462_);
v___x_467_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_460_, v___x_465_, v___x_466_, v___x_464_, v___y_458_);
if (lean_obj_tag(v___x_467_) == 0)
{
lean_dec_ref_known(v___x_467_, 1);
v___y_388_ = v___y_458_;
v_a_389_ = v_val_461_;
goto v___jp_387_;
}
else
{
lean_dec_ref(v_repo_291_);
lean_dec_ref(v_name_290_);
if (lean_obj_tag(v___x_467_) == 0)
{
lean_dec_ref_known(v___x_467_, 1);
goto v___jp_302_;
}
else
{
return v___x_467_;
}
}
}
}
v___jp_468_:
{
lean_object* v___x_474_; uint8_t v___x_475_; 
v___x_474_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
v___x_475_ = l_Option_instDecidableEq___redArg(v___x_474_, v_a_473_, v___y_471_);
if (v___x_475_ == 0)
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; uint8_t v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_476_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__0));
lean_inc_ref(v_name_290_);
v___x_477_ = lean_string_append(v_name_290_, v___x_476_);
v___x_478_ = lean_string_append(v___x_477_, v___y_472_);
v___x_479_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__1));
v___x_480_ = lean_string_append(v___x_478_, v___x_479_);
v___x_481_ = 1;
v___x_482_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_482_, 0, v___x_480_);
lean_ctor_set_uint8(v___x_482_, sizeof(void*)*1, v___x_481_);
lean_inc_ref(v___y_470_);
v___x_483_ = lean_apply_2(v___y_470_, v___x_482_, lean_box(0));
v___x_484_ = lean_unsigned_to_nat(0u);
v___x_485_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_291_);
v___x_486_ = l_Lake_GitRepo_checkoutDetach(v___y_472_, v_repo_291_, v___x_485_);
if (lean_obj_tag(v___x_486_) == 0)
{
lean_object* v_a_487_; lean_object* v___x_488_; uint8_t v___x_489_; 
v_a_487_ = lean_ctor_get(v___x_486_, 1);
lean_inc(v_a_487_);
lean_dec_ref_known(v___x_486_, 2);
v___x_488_ = lean_array_get_size(v_a_487_);
v___x_489_ = lean_nat_dec_lt(v___x_484_, v___x_488_);
if (v___x_489_ == 0)
{
lean_dec(v_a_487_);
v___y_422_ = v___x_475_;
v___y_423_ = v___y_469_;
v___y_424_ = v___y_470_;
goto v___jp_421_;
}
else
{
lean_object* v___x_490_; size_t v___x_491_; size_t v___x_492_; lean_object* v___x_493_; 
v___x_490_ = lean_box(0);
v___x_491_ = ((size_t)0ULL);
v___x_492_ = lean_usize_of_nat(v___x_488_);
v___x_493_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_487_, v___x_491_, v___x_492_, v___x_490_, v___y_470_);
lean_dec(v_a_487_);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_dec_ref_known(v___x_493_, 1);
v___y_422_ = v___x_475_;
v___y_423_ = v___y_469_;
v___y_424_ = v___y_470_;
goto v___jp_421_;
}
else
{
v___y_453_ = v___x_475_;
v___y_454_ = v___y_469_;
v___y_455_ = v___y_470_;
v___y_456_ = v___x_493_;
goto v___jp_452_;
}
}
}
else
{
lean_object* v_a_494_; lean_object* v___x_495_; uint8_t v___x_496_; 
v_a_494_ = lean_ctor_get(v___x_486_, 1);
lean_inc(v_a_494_);
lean_dec_ref_known(v___x_486_, 2);
v___x_495_ = lean_array_get_size(v_a_494_);
v___x_496_ = lean_nat_dec_lt(v___x_484_, v___x_495_);
if (v___x_496_ == 0)
{
lean_object* v___x_497_; lean_object* v___x_498_; 
lean_dec(v_a_494_);
lean_dec_ref(v_repo_291_);
lean_dec_ref(v_name_290_);
v___x_497_ = lean_box(0);
v___x_498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_498_, 0, v___x_497_);
return v___x_498_;
}
else
{
lean_object* v___x_499_; size_t v___x_500_; size_t v___x_501_; lean_object* v___x_502_; 
v___x_499_ = lean_box(0);
v___x_500_ = ((size_t)0ULL);
v___x_501_ = lean_usize_of_nat(v___x_495_);
v___x_502_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_494_, v___x_500_, v___x_501_, v___x_499_, v___y_470_);
lean_dec(v_a_494_);
if (lean_obj_tag(v___x_502_) == 0)
{
lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_509_; 
lean_dec_ref(v_repo_291_);
lean_dec_ref(v_name_290_);
v_isSharedCheck_509_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_509_ == 0)
{
lean_object* v_unused_510_; 
v_unused_510_ = lean_ctor_get(v___x_502_, 0);
lean_dec(v_unused_510_);
v___x_504_ = v___x_502_;
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
else
{
lean_dec(v___x_502_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v___x_507_; 
if (v_isShared_505_ == 0)
{
lean_ctor_set_tag(v___x_504_, 1);
lean_ctor_set(v___x_504_, 0, v___x_499_);
v___x_507_ = v___x_504_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v___x_499_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
}
else
{
v___y_453_ = v___x_475_;
v___y_454_ = v___y_469_;
v___y_455_ = v___y_470_;
v___y_456_ = v___x_502_;
goto v___jp_452_;
}
}
}
}
else
{
lean_object* v___x_511_; lean_object* v___x_512_; uint8_t v___x_513_; 
lean_dec_ref(v___y_472_);
v___x_511_ = lean_unsigned_to_nat(0u);
v___x_512_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_291_);
v___x_513_ = l_Lake_GitRepo_hasNoDiff(v_repo_291_);
if (v___x_513_ == 0)
{
v___y_458_ = v___y_470_;
v___y_459_ = v___x_511_;
v___y_460_ = v___x_512_;
v_val_461_ = v___x_475_;
goto v___jp_457_;
}
else
{
uint8_t v___x_514_; 
v___x_514_ = 0;
v___y_458_ = v___y_470_;
v___y_459_ = v___x_511_;
v___y_460_ = v___x_512_;
v_val_461_ = v___x_514_;
goto v___jp_457_;
}
}
}
v___jp_515_:
{
if (lean_obj_tag(v_a_520_) == 1)
{
lean_object* v_val_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; uint8_t v___x_525_; 
lean_dec_ref(v___y_519_);
lean_dec_ref(v___y_517_);
v_val_521_ = lean_ctor_get(v_a_520_, 0);
lean_inc(v_val_521_);
v___x_522_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_523_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__0));
lean_inc_ref(v_repo_291_);
v___x_524_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_523_, v_repo_291_);
v___x_525_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_525_ == 0)
{
v___y_469_ = v___y_516_;
v___y_470_ = v___y_518_;
v___y_471_ = v_a_520_;
v___y_472_ = v_val_521_;
v_a_473_ = v___x_524_;
goto v___jp_468_;
}
else
{
lean_object* v___x_526_; size_t v___x_527_; size_t v___x_528_; lean_object* v___x_529_; 
v___x_526_ = lean_box(0);
v___x_527_ = ((size_t)0ULL);
v___x_528_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_529_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_522_, v___x_527_, v___x_528_, v___x_526_, v___y_518_);
if (lean_obj_tag(v___x_529_) == 0)
{
lean_dec_ref_known(v___x_529_, 1);
v___y_469_ = v___y_516_;
v___y_470_ = v___y_518_;
v___y_471_ = v_a_520_;
v___y_472_ = v_val_521_;
v_a_473_ = v___x_524_;
goto v___jp_468_;
}
else
{
lean_dec(v___x_524_);
lean_dec(v_val_521_);
lean_dec_ref_known(v_a_520_, 1);
lean_dec_ref(v_repo_291_);
lean_dec_ref(v_name_290_);
return v___x_529_;
}
}
}
else
{
lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; uint8_t v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
lean_dec(v_a_520_);
lean_dec_ref(v_repo_291_);
v___x_530_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__1));
v___x_531_ = lean_string_append(v_name_290_, v___x_530_);
v___x_532_ = lean_string_append(v___x_531_, v___y_519_);
lean_dec_ref(v___y_519_);
v___x_533_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__2));
v___x_534_ = lean_string_append(v___x_532_, v___x_533_);
v___x_535_ = lean_string_append(v___x_534_, v___y_517_);
lean_dec_ref(v___y_517_);
v___x_536_ = 3;
v___x_537_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_537_, 0, v___x_535_);
lean_ctor_set_uint8(v___x_537_, sizeof(void*)*1, v___x_536_);
lean_inc_ref(v___y_518_);
v___x_538_ = lean_apply_2(v___y_518_, v___x_537_, lean_box(0));
v___x_539_ = lean_box(0);
v___x_540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_540_, 0, v___x_539_);
return v___x_540_;
}
}
v___jp_541_:
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; uint8_t v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_546_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__3));
lean_inc_ref(v_name_290_);
v___x_547_ = lean_string_append(v_name_290_, v___x_546_);
v___x_548_ = lean_string_append(v___x_547_, v___y_544_);
v___x_549_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__4));
v___x_550_ = lean_string_append(v___x_548_, v___x_549_);
v___x_551_ = lean_string_append(v___x_550_, v___y_543_);
v___x_552_ = 1;
v___x_553_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_553_, 0, v___x_551_);
lean_ctor_set_uint8(v___x_553_, sizeof(void*)*1, v___x_552_);
lean_inc_ref(v___y_545_);
v___x_554_ = lean_apply_2(v___y_545_, v___x_553_, lean_box(0));
v___x_555_ = lean_unsigned_to_nat(0u);
v___x_556_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v___y_544_);
lean_inc_ref(v___y_542_);
lean_inc_ref(v_repo_291_);
v___x_557_ = l_Lake_GitRepo_fetchRevision_x3f(v_repo_291_, v___y_542_, v___y_544_, v___x_556_);
if (lean_obj_tag(v___x_557_) == 0)
{
lean_object* v_a_558_; lean_object* v_a_559_; lean_object* v___x_560_; uint8_t v___x_561_; 
v_a_558_ = lean_ctor_get(v___x_557_, 0);
lean_inc(v_a_558_);
v_a_559_ = lean_ctor_get(v___x_557_, 1);
lean_inc(v_a_559_);
lean_dec_ref_known(v___x_557_, 2);
v___x_560_ = lean_array_get_size(v_a_559_);
v___x_561_ = lean_nat_dec_lt(v___x_555_, v___x_560_);
if (v___x_561_ == 0)
{
lean_dec(v_a_559_);
v___y_516_ = v___y_542_;
v___y_517_ = v___y_543_;
v___y_518_ = v___y_545_;
v___y_519_ = v___y_544_;
v_a_520_ = v_a_558_;
goto v___jp_515_;
}
else
{
lean_object* v___x_562_; size_t v___x_563_; size_t v___x_564_; lean_object* v___x_565_; 
v___x_562_ = lean_box(0);
v___x_563_ = ((size_t)0ULL);
v___x_564_ = lean_usize_of_nat(v___x_560_);
v___x_565_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_559_, v___x_563_, v___x_564_, v___x_562_, v___y_545_);
lean_dec(v_a_559_);
if (lean_obj_tag(v___x_565_) == 0)
{
lean_dec_ref_known(v___x_565_, 1);
v___y_516_ = v___y_542_;
v___y_517_ = v___y_543_;
v___y_518_ = v___y_545_;
v___y_519_ = v___y_544_;
v_a_520_ = v_a_558_;
goto v___jp_515_;
}
else
{
lean_dec(v_a_558_);
lean_dec_ref(v___y_544_);
lean_dec_ref(v___y_543_);
lean_dec_ref(v_repo_291_);
lean_dec_ref(v_name_290_);
return v___x_565_;
}
}
}
else
{
lean_object* v_a_566_; lean_object* v___x_567_; uint8_t v___x_568_; 
lean_dec_ref(v___y_544_);
lean_dec_ref(v___y_543_);
lean_dec_ref(v_repo_291_);
lean_dec_ref(v_name_290_);
v_a_566_ = lean_ctor_get(v___x_557_, 1);
lean_inc(v_a_566_);
lean_dec_ref_known(v___x_557_, 2);
v___x_567_ = lean_array_get_size(v_a_566_);
v___x_568_ = lean_nat_dec_lt(v___x_555_, v___x_567_);
if (v___x_568_ == 0)
{
lean_object* v___x_569_; lean_object* v___x_570_; 
lean_dec(v_a_566_);
v___x_569_ = lean_box(0);
v___x_570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_570_, 0, v___x_569_);
return v___x_570_;
}
else
{
lean_object* v___x_571_; size_t v___x_572_; size_t v___x_573_; lean_object* v___x_574_; 
v___x_571_ = lean_box(0);
v___x_572_ = ((size_t)0ULL);
v___x_573_ = lean_usize_of_nat(v___x_567_);
v___x_574_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_566_, v___x_572_, v___x_573_, v___x_571_, v___y_545_);
lean_dec(v_a_566_);
if (lean_obj_tag(v___x_574_) == 0)
{
lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_581_; 
v_isSharedCheck_581_ = !lean_is_exclusive(v___x_574_);
if (v_isSharedCheck_581_ == 0)
{
lean_object* v_unused_582_; 
v_unused_582_ = lean_ctor_get(v___x_574_, 0);
lean_dec(v_unused_582_);
v___x_576_ = v___x_574_;
v_isShared_577_ = v_isSharedCheck_581_;
goto v_resetjp_575_;
}
else
{
lean_dec(v___x_574_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_581_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_579_; 
if (v_isShared_577_ == 0)
{
lean_ctor_set_tag(v___x_576_, 1);
lean_ctor_set(v___x_576_, 0, v___x_571_);
v___x_579_ = v___x_576_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v___x_571_);
v___x_579_ = v_reuseFailAlloc_580_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
return v___x_579_;
}
}
}
else
{
return v___x_574_;
}
}
}
}
v___jp_583_:
{
if (lean_obj_tag(v___y_587_) == 0)
{
lean_dec_ref_known(v___y_587_, 1);
v___y_542_ = v___y_584_;
v___y_543_ = v___y_585_;
v___y_544_ = v___y_586_;
v___y_545_ = v_a_294_;
goto v___jp_541_;
}
else
{
lean_dec_ref(v___y_586_);
lean_dec_ref(v___y_585_);
lean_dec_ref(v_repo_291_);
lean_dec_ref(v_name_290_);
return v___y_587_;
}
}
v___jp_588_:
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_592_ = lean_unsigned_to_nat(0u);
v___x_593_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_291_);
lean_inc_ref(v___y_590_);
lean_inc_ref(v___y_589_);
v___x_594_ = l_Lake_GitRepo_addRemote(v___y_589_, v___y_590_, v_repo_291_, v___x_593_);
if (lean_obj_tag(v___x_594_) == 0)
{
lean_object* v_a_595_; lean_object* v___x_596_; uint8_t v___x_597_; 
v_a_595_ = lean_ctor_get(v___x_594_, 1);
lean_inc(v_a_595_);
lean_dec_ref_known(v___x_594_, 2);
v___x_596_ = lean_array_get_size(v_a_595_);
v___x_597_ = lean_nat_dec_lt(v___x_592_, v___x_596_);
if (v___x_597_ == 0)
{
lean_dec(v_a_595_);
v___y_542_ = v___y_589_;
v___y_543_ = v___y_590_;
v___y_544_ = v___y_591_;
v___y_545_ = v_a_294_;
goto v___jp_541_;
}
else
{
lean_object* v___x_598_; size_t v___x_599_; size_t v___x_600_; lean_object* v___x_601_; 
v___x_598_ = lean_box(0);
v___x_599_ = ((size_t)0ULL);
v___x_600_ = lean_usize_of_nat(v___x_596_);
v___x_601_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_595_, v___x_599_, v___x_600_, v___x_598_, v_a_294_);
lean_dec(v_a_595_);
if (lean_obj_tag(v___x_601_) == 0)
{
lean_dec_ref_known(v___x_601_, 1);
v___y_542_ = v___y_589_;
v___y_543_ = v___y_590_;
v___y_544_ = v___y_591_;
v___y_545_ = v_a_294_;
goto v___jp_541_;
}
else
{
v___y_584_ = v___y_589_;
v___y_585_ = v___y_590_;
v___y_586_ = v___y_591_;
v___y_587_ = v___x_601_;
goto v___jp_583_;
}
}
}
else
{
lean_object* v_a_602_; lean_object* v___x_603_; uint8_t v___x_604_; 
v_a_602_ = lean_ctor_get(v___x_594_, 1);
lean_inc(v_a_602_);
lean_dec_ref_known(v___x_594_, 2);
v___x_603_ = lean_array_get_size(v_a_602_);
v___x_604_ = lean_nat_dec_lt(v___x_592_, v___x_603_);
if (v___x_604_ == 0)
{
lean_object* v___x_605_; lean_object* v___x_606_; 
lean_dec(v_a_602_);
lean_dec_ref(v___y_591_);
lean_dec_ref(v___y_590_);
lean_dec_ref(v_repo_291_);
lean_dec_ref(v_name_290_);
v___x_605_ = lean_box(0);
v___x_606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_606_, 0, v___x_605_);
return v___x_606_;
}
else
{
lean_object* v___x_607_; size_t v___x_608_; size_t v___x_609_; lean_object* v___x_610_; 
v___x_607_ = lean_box(0);
v___x_608_ = ((size_t)0ULL);
v___x_609_ = lean_usize_of_nat(v___x_603_);
v___x_610_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_602_, v___x_608_, v___x_609_, v___x_607_, v_a_294_);
lean_dec(v_a_602_);
if (lean_obj_tag(v___x_610_) == 0)
{
lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_617_; 
lean_dec_ref(v___y_591_);
lean_dec_ref(v___y_590_);
lean_dec_ref(v_repo_291_);
lean_dec_ref(v_name_290_);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_617_ == 0)
{
lean_object* v_unused_618_; 
v_unused_618_ = lean_ctor_get(v___x_610_, 0);
lean_dec(v_unused_618_);
v___x_612_ = v___x_610_;
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
else
{
lean_dec(v___x_610_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___x_615_; 
if (v_isShared_613_ == 0)
{
lean_ctor_set_tag(v___x_612_, 1);
lean_ctor_set(v___x_612_, 0, v___x_607_);
v___x_615_ = v___x_612_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v___x_607_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
else
{
v___y_584_ = v___y_589_;
v___y_585_ = v___y_590_;
v___y_586_ = v___y_591_;
v___y_587_ = v___x_610_;
goto v___jp_583_;
}
}
}
}
v___jp_619_:
{
if (lean_obj_tag(v___y_623_) == 0)
{
lean_dec_ref_known(v___y_623_, 1);
v___y_589_ = v___y_620_;
v___y_590_ = v___y_621_;
v___y_591_ = v___y_622_;
goto v___jp_588_;
}
else
{
lean_dec_ref(v___y_622_);
lean_dec_ref(v___y_621_);
lean_dec_ref(v_repo_291_);
lean_dec_ref(v_name_290_);
return v___y_623_;
}
}
v___jp_624_:
{
if (v_a_626_ == 0)
{
lean_dec_ref(v_repo_291_);
lean_dec_ref(v_name_290_);
goto v___jp_299_;
}
else
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; uint8_t v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_627_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff___closed__0));
v___x_628_ = lean_string_append(v_name_290_, v___x_627_);
v___x_629_ = lean_string_append(v___x_628_, v_repo_291_);
lean_dec_ref(v_repo_291_);
v___x_630_ = 2;
v___x_631_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_631_, 0, v___x_629_);
lean_ctor_set_uint8(v___x_631_, sizeof(void*)*1, v___x_630_);
lean_inc_ref(v___y_625_);
v___x_632_ = lean_apply_2(v___y_625_, v___x_631_, lean_box(0));
goto v___jp_299_;
}
}
v___jp_633_:
{
if (v_a_635_ == 0)
{
lean_dec_ref(v_repo_291_);
lean_dec_ref(v_name_290_);
goto v___jp_296_;
}
else
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; uint8_t v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_636_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff___closed__0));
v___x_637_ = lean_string_append(v_name_290_, v___x_636_);
v___x_638_ = lean_string_append(v___x_637_, v_repo_291_);
lean_dec_ref(v_repo_291_);
v___x_639_ = 2;
v___x_640_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_640_, 0, v___x_638_);
lean_ctor_set_uint8(v___x_640_, sizeof(void*)*1, v___x_639_);
lean_inc_ref(v___y_634_);
v___x_641_ = lean_apply_2(v___y_634_, v___x_640_, lean_box(0));
goto v___jp_296_;
}
}
v___jp_642_:
{
lean_object* v___x_647_; uint8_t v___x_648_; 
v___x_647_ = lean_array_get_size(v___y_644_);
v___x_648_ = lean_nat_dec_lt(v___y_643_, v___x_647_);
if (v___x_648_ == 0)
{
v___y_625_ = v___y_645_;
v_a_626_ = v_val_646_;
goto v___jp_624_;
}
else
{
lean_object* v___x_649_; size_t v___x_650_; size_t v___x_651_; lean_object* v___x_652_; 
v___x_649_ = lean_box(0);
v___x_650_ = ((size_t)0ULL);
v___x_651_ = lean_usize_of_nat(v___x_647_);
v___x_652_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_644_, v___x_650_, v___x_651_, v___x_649_, v___y_645_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_dec_ref_known(v___x_652_, 1);
v___y_625_ = v___y_645_;
v_a_626_ = v_val_646_;
goto v___jp_624_;
}
else
{
lean_dec_ref(v_repo_291_);
lean_dec_ref(v_name_290_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_dec_ref_known(v___x_652_, 1);
goto v___jp_299_;
}
else
{
return v___x_652_;
}
}
}
}
v___jp_653_:
{
lean_object* v___x_657_; lean_object* v___x_658_; uint8_t v___x_659_; 
v___x_657_ = lean_unsigned_to_nat(0u);
v___x_658_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_291_);
v___x_659_ = l_Lake_GitRepo_hasNoDiff(v_repo_291_);
if (v___x_659_ == 0)
{
v___y_643_ = v___x_657_;
v___y_644_ = v___x_658_;
v___y_645_ = v___y_654_;
v_val_646_ = v___y_656_;
goto v___jp_642_;
}
else
{
v___y_643_ = v___x_657_;
v___y_644_ = v___x_658_;
v___y_645_ = v___y_654_;
v_val_646_ = v___y_655_;
goto v___jp_642_;
}
}
v___jp_660_:
{
if (lean_obj_tag(v___y_664_) == 0)
{
lean_dec_ref_known(v___y_664_, 1);
v___y_654_ = v___y_661_;
v___y_655_ = v___y_662_;
v___y_656_ = v___y_663_;
goto v___jp_653_;
}
else
{
lean_dec_ref(v_repo_291_);
lean_dec_ref(v_name_290_);
return v___y_664_;
}
}
v___jp_665_:
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_669_ = lean_unsigned_to_nat(0u);
v___x_670_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_291_);
v___x_671_ = l_Lake_GitRepo_clean(v_repo_291_, v___x_670_);
if (lean_obj_tag(v___x_671_) == 0)
{
lean_object* v_a_672_; lean_object* v___x_673_; uint8_t v___x_674_; 
v_a_672_ = lean_ctor_get(v___x_671_, 1);
lean_inc(v_a_672_);
lean_dec_ref_known(v___x_671_, 2);
v___x_673_ = lean_array_get_size(v_a_672_);
v___x_674_ = lean_nat_dec_lt(v___x_669_, v___x_673_);
if (v___x_674_ == 0)
{
lean_dec(v_a_672_);
v___y_654_ = v___y_666_;
v___y_655_ = v___y_667_;
v___y_656_ = v___y_668_;
goto v___jp_653_;
}
else
{
lean_object* v___x_675_; size_t v___x_676_; size_t v___x_677_; lean_object* v___x_678_; 
v___x_675_ = lean_box(0);
v___x_676_ = ((size_t)0ULL);
v___x_677_ = lean_usize_of_nat(v___x_673_);
v___x_678_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_672_, v___x_676_, v___x_677_, v___x_675_, v___y_666_);
lean_dec(v_a_672_);
if (lean_obj_tag(v___x_678_) == 0)
{
lean_dec_ref_known(v___x_678_, 1);
v___y_654_ = v___y_666_;
v___y_655_ = v___y_667_;
v___y_656_ = v___y_668_;
goto v___jp_653_;
}
else
{
v___y_661_ = v___y_666_;
v___y_662_ = v___y_667_;
v___y_663_ = v___y_668_;
v___y_664_ = v___x_678_;
goto v___jp_660_;
}
}
}
else
{
lean_object* v_a_679_; lean_object* v___x_680_; uint8_t v___x_681_; 
v_a_679_ = lean_ctor_get(v___x_671_, 1);
lean_inc(v_a_679_);
lean_dec_ref_known(v___x_671_, 2);
v___x_680_ = lean_array_get_size(v_a_679_);
v___x_681_ = lean_nat_dec_lt(v___x_669_, v___x_680_);
if (v___x_681_ == 0)
{
lean_object* v___x_682_; lean_object* v___x_683_; 
lean_dec(v_a_679_);
lean_dec_ref(v_repo_291_);
lean_dec_ref(v_name_290_);
v___x_682_ = lean_box(0);
v___x_683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_683_, 0, v___x_682_);
return v___x_683_;
}
else
{
lean_object* v___x_684_; size_t v___x_685_; size_t v___x_686_; lean_object* v___x_687_; 
v___x_684_ = lean_box(0);
v___x_685_ = ((size_t)0ULL);
v___x_686_ = lean_usize_of_nat(v___x_680_);
v___x_687_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_679_, v___x_685_, v___x_686_, v___x_684_, v___y_666_);
lean_dec(v_a_679_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_694_; 
lean_dec_ref(v_repo_291_);
lean_dec_ref(v_name_290_);
v_isSharedCheck_694_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_694_ == 0)
{
lean_object* v_unused_695_; 
v_unused_695_ = lean_ctor_get(v___x_687_, 0);
lean_dec(v_unused_695_);
v___x_689_ = v___x_687_;
v_isShared_690_ = v_isSharedCheck_694_;
goto v_resetjp_688_;
}
else
{
lean_dec(v___x_687_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_694_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v___x_692_; 
if (v_isShared_690_ == 0)
{
lean_ctor_set_tag(v___x_689_, 1);
lean_ctor_set(v___x_689_, 0, v___x_684_);
v___x_692_ = v___x_689_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v___x_684_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
return v___x_692_;
}
}
}
else
{
v___y_661_ = v___y_666_;
v___y_662_ = v___y_667_;
v___y_663_ = v___y_668_;
v___y_664_ = v___x_687_;
goto v___jp_660_;
}
}
}
}
v___jp_696_:
{
if (lean_obj_tag(v___y_700_) == 0)
{
lean_dec_ref_known(v___y_700_, 1);
v___y_666_ = v___y_697_;
v___y_667_ = v___y_698_;
v___y_668_ = v___y_699_;
goto v___jp_665_;
}
else
{
lean_dec_ref(v_repo_291_);
lean_dec_ref(v_name_290_);
return v___y_700_;
}
}
v___jp_701_:
{
if (lean_obj_tag(v_a_708_) == 0)
{
v___y_542_ = v___y_702_;
v___y_543_ = v___y_704_;
v___y_544_ = v___y_706_;
v___y_545_ = v___y_703_;
goto v___jp_541_;
}
else
{
lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_749_; 
v_isSharedCheck_749_ = !lean_is_exclusive(v_a_708_);
if (v_isSharedCheck_749_ == 0)
{
lean_object* v_unused_750_; 
v_unused_750_ = lean_ctor_get(v_a_708_, 0);
lean_dec(v_unused_750_);
v___x_710_ = v_a_708_;
v_isShared_711_ = v_isSharedCheck_749_;
goto v_resetjp_709_;
}
else
{
lean_dec(v_a_708_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_749_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
if (v___y_707_ == 0)
{
lean_del_object(v___x_710_);
v___y_542_ = v___y_702_;
v___y_543_ = v___y_704_;
v___y_544_ = v___y_706_;
v___y_545_ = v___y_703_;
goto v___jp_541_;
}
else
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; uint8_t v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
lean_dec_ref(v___y_704_);
v___x_712_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__0));
lean_inc_ref(v_name_290_);
v___x_713_ = lean_string_append(v_name_290_, v___x_712_);
v___x_714_ = lean_string_append(v___x_713_, v___y_706_);
v___x_715_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__1));
v___x_716_ = lean_string_append(v___x_714_, v___x_715_);
v___x_717_ = 1;
v___x_718_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_718_, 0, v___x_716_);
lean_ctor_set_uint8(v___x_718_, sizeof(void*)*1, v___x_717_);
lean_inc_ref(v___y_703_);
v___x_719_ = lean_apply_2(v___y_703_, v___x_718_, lean_box(0));
v___x_720_ = lean_unsigned_to_nat(0u);
v___x_721_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_291_);
v___x_722_ = l_Lake_GitRepo_checkoutDetach(v___y_706_, v_repo_291_, v___x_721_);
if (lean_obj_tag(v___x_722_) == 0)
{
lean_object* v_a_723_; lean_object* v___x_724_; uint8_t v___x_725_; 
lean_del_object(v___x_710_);
v_a_723_ = lean_ctor_get(v___x_722_, 1);
lean_inc(v_a_723_);
lean_dec_ref_known(v___x_722_, 2);
v___x_724_ = lean_array_get_size(v_a_723_);
v___x_725_ = lean_nat_dec_lt(v___x_720_, v___x_724_);
if (v___x_725_ == 0)
{
lean_dec(v_a_723_);
v___y_666_ = v___y_703_;
v___y_667_ = v___y_705_;
v___y_668_ = v___y_707_;
goto v___jp_665_;
}
else
{
lean_object* v___x_726_; size_t v___x_727_; size_t v___x_728_; lean_object* v___x_729_; 
v___x_726_ = lean_box(0);
v___x_727_ = ((size_t)0ULL);
v___x_728_ = lean_usize_of_nat(v___x_724_);
v___x_729_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_723_, v___x_727_, v___x_728_, v___x_726_, v___y_703_);
lean_dec(v_a_723_);
if (lean_obj_tag(v___x_729_) == 0)
{
lean_dec_ref_known(v___x_729_, 1);
v___y_666_ = v___y_703_;
v___y_667_ = v___y_705_;
v___y_668_ = v___y_707_;
goto v___jp_665_;
}
else
{
v___y_697_ = v___y_703_;
v___y_698_ = v___y_705_;
v___y_699_ = v___y_707_;
v___y_700_ = v___x_729_;
goto v___jp_696_;
}
}
}
else
{
lean_object* v_a_730_; lean_object* v___x_731_; uint8_t v___x_732_; 
v_a_730_ = lean_ctor_get(v___x_722_, 1);
lean_inc(v_a_730_);
lean_dec_ref_known(v___x_722_, 2);
v___x_731_ = lean_array_get_size(v_a_730_);
v___x_732_ = lean_nat_dec_lt(v___x_720_, v___x_731_);
if (v___x_732_ == 0)
{
lean_object* v___x_733_; lean_object* v___x_735_; 
lean_dec(v_a_730_);
lean_dec_ref(v_repo_291_);
lean_dec_ref(v_name_290_);
v___x_733_ = lean_box(0);
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 0, v___x_733_);
v___x_735_ = v___x_710_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v___x_733_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
else
{
lean_object* v___x_737_; size_t v___x_738_; size_t v___x_739_; lean_object* v___x_740_; 
lean_del_object(v___x_710_);
v___x_737_ = lean_box(0);
v___x_738_ = ((size_t)0ULL);
v___x_739_ = lean_usize_of_nat(v___x_731_);
v___x_740_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_730_, v___x_738_, v___x_739_, v___x_737_, v___y_703_);
lean_dec(v_a_730_);
if (lean_obj_tag(v___x_740_) == 0)
{
lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_747_; 
lean_dec_ref(v_repo_291_);
lean_dec_ref(v_name_290_);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_740_);
if (v_isSharedCheck_747_ == 0)
{
lean_object* v_unused_748_; 
v_unused_748_ = lean_ctor_get(v___x_740_, 0);
lean_dec(v_unused_748_);
v___x_742_ = v___x_740_;
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
else
{
lean_dec(v___x_740_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_745_; 
if (v_isShared_743_ == 0)
{
lean_ctor_set_tag(v___x_742_, 1);
lean_ctor_set(v___x_742_, 0, v___x_737_);
v___x_745_ = v___x_742_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v___x_737_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
else
{
v___y_697_ = v___y_703_;
v___y_698_ = v___y_705_;
v___y_699_ = v___y_707_;
v___y_700_ = v___x_740_;
goto v___jp_696_;
}
}
}
}
}
}
}
v___jp_751_:
{
lean_object* v___x_756_; uint8_t v___x_757_; 
v___x_756_ = lean_array_get_size(v___y_754_);
v___x_757_ = lean_nat_dec_lt(v___y_752_, v___x_756_);
if (v___x_757_ == 0)
{
v___y_634_ = v___y_753_;
v_a_635_ = v_val_755_;
goto v___jp_633_;
}
else
{
lean_object* v___x_758_; size_t v___x_759_; size_t v___x_760_; lean_object* v___x_761_; 
v___x_758_ = lean_box(0);
v___x_759_ = ((size_t)0ULL);
v___x_760_ = lean_usize_of_nat(v___x_756_);
v___x_761_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_754_, v___x_759_, v___x_760_, v___x_758_, v___y_753_);
if (lean_obj_tag(v___x_761_) == 0)
{
lean_dec_ref_known(v___x_761_, 1);
v___y_634_ = v___y_753_;
v_a_635_ = v_val_755_;
goto v___jp_633_;
}
else
{
lean_dec_ref(v_repo_291_);
lean_dec_ref(v_name_290_);
if (lean_obj_tag(v___x_761_) == 0)
{
lean_dec_ref_known(v___x_761_, 1);
goto v___jp_296_;
}
else
{
return v___x_761_;
}
}
}
}
v___jp_762_:
{
lean_object* v___x_768_; lean_object* v___x_769_; uint8_t v___x_770_; 
v___x_768_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
lean_inc_ref(v___y_766_);
v___x_769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_769_, 0, v___y_766_);
v___x_770_ = l_Option_instDecidableEq___redArg(v___x_768_, v_a_767_, v___x_769_);
if (v___x_770_ == 0)
{
uint8_t v___x_771_; 
v___x_771_ = l_Lake_GitRev_isFullSha1(v___y_766_);
if (v___x_771_ == 0)
{
v___y_542_ = v___y_763_;
v___y_543_ = v___y_765_;
v___y_544_ = v___y_766_;
v___y_545_ = v___y_764_;
goto v___jp_541_;
}
else
{
lean_object* v___x_772_; lean_object* v___x_773_; uint8_t v___x_774_; 
v___x_772_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_291_);
lean_inc_ref(v___y_766_);
v___x_773_ = l_Lake_GitRepo_findCommit_x3f(v___y_766_, v_repo_291_);
v___x_774_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_774_ == 0)
{
v___y_702_ = v___y_763_;
v___y_703_ = v___y_764_;
v___y_704_ = v___y_765_;
v___y_705_ = v___x_770_;
v___y_706_ = v___y_766_;
v___y_707_ = v___x_771_;
v_a_708_ = v___x_773_;
goto v___jp_701_;
}
else
{
lean_object* v___x_775_; size_t v___x_776_; size_t v___x_777_; lean_object* v___x_778_; 
v___x_775_ = lean_box(0);
v___x_776_ = ((size_t)0ULL);
v___x_777_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_778_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_772_, v___x_776_, v___x_777_, v___x_775_, v___y_764_);
if (lean_obj_tag(v___x_778_) == 0)
{
lean_dec_ref_known(v___x_778_, 1);
v___y_702_ = v___y_763_;
v___y_703_ = v___y_764_;
v___y_704_ = v___y_765_;
v___y_705_ = v___x_770_;
v___y_706_ = v___y_766_;
v___y_707_ = v___x_771_;
v_a_708_ = v___x_773_;
goto v___jp_701_;
}
else
{
lean_dec(v___x_773_);
lean_dec_ref(v___y_766_);
lean_dec_ref(v___y_765_);
lean_dec_ref(v_repo_291_);
lean_dec_ref(v_name_290_);
return v___x_778_;
}
}
}
}
else
{
lean_object* v___x_779_; lean_object* v___x_780_; uint8_t v___x_781_; 
lean_dec_ref(v___y_766_);
lean_dec_ref(v___y_765_);
v___x_779_ = lean_unsigned_to_nat(0u);
v___x_780_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_291_);
v___x_781_ = l_Lake_GitRepo_hasNoDiff(v_repo_291_);
if (v___x_781_ == 0)
{
v___y_752_ = v___x_779_;
v___y_753_ = v___y_764_;
v___y_754_ = v___x_780_;
v_val_755_ = v___x_770_;
goto v___jp_751_;
}
else
{
uint8_t v___x_782_; 
v___x_782_ = 0;
v___y_752_ = v___x_779_;
v___y_753_ = v___y_764_;
v___y_754_ = v___x_780_;
v_val_755_ = v___x_782_;
goto v___jp_751_;
}
}
}
v___jp_783_:
{
lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; uint8_t v___x_791_; 
v___x_788_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_789_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__0));
lean_inc_ref(v_repo_291_);
v___x_790_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_789_, v_repo_291_);
v___x_791_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_791_ == 0)
{
v___y_763_ = v___y_784_;
v___y_764_ = v___y_787_;
v___y_765_ = v___y_785_;
v___y_766_ = v___y_786_;
v_a_767_ = v___x_790_;
goto v___jp_762_;
}
else
{
lean_object* v___x_792_; size_t v___x_793_; size_t v___x_794_; lean_object* v___x_795_; 
v___x_792_ = lean_box(0);
v___x_793_ = ((size_t)0ULL);
v___x_794_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_795_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_788_, v___x_793_, v___x_794_, v___x_792_, v___y_787_);
if (lean_obj_tag(v___x_795_) == 0)
{
lean_dec_ref_known(v___x_795_, 1);
v___y_763_ = v___y_784_;
v___y_764_ = v___y_787_;
v___y_765_ = v___y_785_;
v___y_766_ = v___y_786_;
v_a_767_ = v___x_790_;
goto v___jp_762_;
}
else
{
lean_dec(v___x_790_);
lean_dec_ref(v___y_786_);
lean_dec_ref(v___y_785_);
lean_dec_ref(v_repo_291_);
lean_dec_ref(v_name_290_);
return v___x_795_;
}
}
}
v___jp_796_:
{
if (lean_obj_tag(v___y_800_) == 0)
{
lean_dec_ref_known(v___y_800_, 1);
v___y_784_ = v___y_797_;
v___y_785_ = v___y_798_;
v___y_786_ = v___y_799_;
v___y_787_ = v_a_294_;
goto v___jp_783_;
}
else
{
lean_dec_ref(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec_ref(v_repo_291_);
lean_dec_ref(v_name_290_);
return v___y_800_;
}
}
v___jp_801_:
{
if (lean_obj_tag(v___y_805_) == 0)
{
lean_dec_ref_known(v___y_805_, 1);
v___y_784_ = v___y_802_;
v___y_785_ = v___y_803_;
v___y_786_ = v___y_804_;
v___y_787_ = v_a_294_;
goto v___jp_783_;
}
else
{
lean_dec_ref(v___y_804_);
lean_dec_ref(v___y_803_);
lean_dec_ref(v_repo_291_);
lean_dec_ref(v_name_290_);
return v___y_805_;
}
}
v___jp_806_:
{
if (lean_obj_tag(v_a_810_) == 1)
{
lean_object* v_val_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_854_; 
v_val_811_ = lean_ctor_get(v_a_810_, 0);
v_isSharedCheck_854_ = !lean_is_exclusive(v_a_810_);
if (v_isSharedCheck_854_ == 0)
{
v___x_813_ = v_a_810_;
v_isShared_814_ = v_isSharedCheck_854_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_val_811_);
lean_dec(v_a_810_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_854_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
uint8_t v___x_815_; 
v___x_815_ = lean_string_dec_eq(v_val_811_, v___y_808_);
if (v___x_815_ == 0)
{
lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; uint8_t v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_816_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__5));
lean_inc_ref(v_name_290_);
v___x_817_ = lean_string_append(v_name_290_, v___x_816_);
v___x_818_ = lean_string_append(v___x_817_, v_val_811_);
lean_dec(v_val_811_);
v___x_819_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__6));
v___x_820_ = lean_string_append(v___x_818_, v___x_819_);
v___x_821_ = lean_string_append(v___x_820_, v___y_808_);
v___x_822_ = 1;
v___x_823_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_823_, 0, v___x_821_);
lean_ctor_set_uint8(v___x_823_, sizeof(void*)*1, v___x_822_);
lean_inc_ref(v_a_294_);
v___x_824_ = lean_apply_2(v_a_294_, v___x_823_, lean_box(0));
v___x_825_ = lean_unsigned_to_nat(0u);
v___x_826_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_291_);
lean_inc_ref(v___y_808_);
lean_inc_ref(v___y_807_);
v___x_827_ = l_Lake_GitRepo_setRemoteUrl(v___y_807_, v___y_808_, v_repo_291_, v___x_826_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_object* v_a_828_; lean_object* v___x_829_; uint8_t v___x_830_; 
lean_del_object(v___x_813_);
v_a_828_ = lean_ctor_get(v___x_827_, 1);
lean_inc(v_a_828_);
lean_dec_ref_known(v___x_827_, 2);
v___x_829_ = lean_array_get_size(v_a_828_);
v___x_830_ = lean_nat_dec_lt(v___x_825_, v___x_829_);
if (v___x_830_ == 0)
{
lean_dec(v_a_828_);
v___y_784_ = v___y_807_;
v___y_785_ = v___y_808_;
v___y_786_ = v___y_809_;
v___y_787_ = v_a_294_;
goto v___jp_783_;
}
else
{
lean_object* v___x_831_; size_t v___x_832_; size_t v___x_833_; lean_object* v___x_834_; 
v___x_831_ = lean_box(0);
v___x_832_ = ((size_t)0ULL);
v___x_833_ = lean_usize_of_nat(v___x_829_);
v___x_834_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_828_, v___x_832_, v___x_833_, v___x_831_, v_a_294_);
lean_dec(v_a_828_);
if (lean_obj_tag(v___x_834_) == 0)
{
lean_dec_ref_known(v___x_834_, 1);
v___y_784_ = v___y_807_;
v___y_785_ = v___y_808_;
v___y_786_ = v___y_809_;
v___y_787_ = v_a_294_;
goto v___jp_783_;
}
else
{
v___y_802_ = v___y_807_;
v___y_803_ = v___y_808_;
v___y_804_ = v___y_809_;
v___y_805_ = v___x_834_;
goto v___jp_801_;
}
}
}
else
{
lean_object* v_a_835_; lean_object* v___x_836_; uint8_t v___x_837_; 
v_a_835_ = lean_ctor_get(v___x_827_, 1);
lean_inc(v_a_835_);
lean_dec_ref_known(v___x_827_, 2);
v___x_836_ = lean_array_get_size(v_a_835_);
v___x_837_ = lean_nat_dec_lt(v___x_825_, v___x_836_);
if (v___x_837_ == 0)
{
lean_object* v___x_838_; lean_object* v___x_840_; 
lean_dec(v_a_835_);
lean_dec_ref(v___y_809_);
lean_dec_ref(v___y_808_);
lean_dec_ref(v_repo_291_);
lean_dec_ref(v_name_290_);
v___x_838_ = lean_box(0);
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 0, v___x_838_);
v___x_840_ = v___x_813_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v___x_838_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
else
{
lean_object* v___x_842_; size_t v___x_843_; size_t v___x_844_; lean_object* v___x_845_; 
lean_del_object(v___x_813_);
v___x_842_ = lean_box(0);
v___x_843_ = ((size_t)0ULL);
v___x_844_ = lean_usize_of_nat(v___x_836_);
v___x_845_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_835_, v___x_843_, v___x_844_, v___x_842_, v_a_294_);
lean_dec(v_a_835_);
if (lean_obj_tag(v___x_845_) == 0)
{
lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_852_; 
lean_dec_ref(v___y_809_);
lean_dec_ref(v___y_808_);
lean_dec_ref(v_repo_291_);
lean_dec_ref(v_name_290_);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_852_ == 0)
{
lean_object* v_unused_853_; 
v_unused_853_ = lean_ctor_get(v___x_845_, 0);
lean_dec(v_unused_853_);
v___x_847_ = v___x_845_;
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
else
{
lean_dec(v___x_845_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_850_; 
if (v_isShared_848_ == 0)
{
lean_ctor_set_tag(v___x_847_, 1);
lean_ctor_set(v___x_847_, 0, v___x_842_);
v___x_850_ = v___x_847_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v___x_842_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
else
{
v___y_802_ = v___y_807_;
v___y_803_ = v___y_808_;
v___y_804_ = v___y_809_;
v___y_805_ = v___x_845_;
goto v___jp_801_;
}
}
}
}
else
{
lean_del_object(v___x_813_);
lean_dec(v_val_811_);
v___y_784_ = v___y_807_;
v___y_785_ = v___y_808_;
v___y_786_ = v___y_809_;
v___y_787_ = v_a_294_;
goto v___jp_783_;
}
}
}
else
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
lean_dec(v_a_810_);
v___x_855_ = lean_unsigned_to_nat(0u);
v___x_856_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_291_);
lean_inc_ref(v___y_808_);
lean_inc_ref(v___y_807_);
v___x_857_ = l_Lake_GitRepo_addRemote(v___y_807_, v___y_808_, v_repo_291_, v___x_856_);
if (lean_obj_tag(v___x_857_) == 0)
{
lean_object* v_a_858_; lean_object* v___x_859_; uint8_t v___x_860_; 
v_a_858_ = lean_ctor_get(v___x_857_, 1);
lean_inc(v_a_858_);
lean_dec_ref_known(v___x_857_, 2);
v___x_859_ = lean_array_get_size(v_a_858_);
v___x_860_ = lean_nat_dec_lt(v___x_855_, v___x_859_);
if (v___x_860_ == 0)
{
lean_dec(v_a_858_);
v___y_784_ = v___y_807_;
v___y_785_ = v___y_808_;
v___y_786_ = v___y_809_;
v___y_787_ = v_a_294_;
goto v___jp_783_;
}
else
{
lean_object* v___x_861_; size_t v___x_862_; size_t v___x_863_; lean_object* v___x_864_; 
v___x_861_ = lean_box(0);
v___x_862_ = ((size_t)0ULL);
v___x_863_ = lean_usize_of_nat(v___x_859_);
v___x_864_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_858_, v___x_862_, v___x_863_, v___x_861_, v_a_294_);
lean_dec(v_a_858_);
if (lean_obj_tag(v___x_864_) == 0)
{
lean_dec_ref_known(v___x_864_, 1);
v___y_784_ = v___y_807_;
v___y_785_ = v___y_808_;
v___y_786_ = v___y_809_;
v___y_787_ = v_a_294_;
goto v___jp_783_;
}
else
{
v___y_797_ = v___y_807_;
v___y_798_ = v___y_808_;
v___y_799_ = v___y_809_;
v___y_800_ = v___x_864_;
goto v___jp_796_;
}
}
}
else
{
lean_object* v_a_865_; lean_object* v___x_866_; uint8_t v___x_867_; 
v_a_865_ = lean_ctor_get(v___x_857_, 1);
lean_inc(v_a_865_);
lean_dec_ref_known(v___x_857_, 2);
v___x_866_ = lean_array_get_size(v_a_865_);
v___x_867_ = lean_nat_dec_lt(v___x_855_, v___x_866_);
if (v___x_867_ == 0)
{
lean_object* v___x_868_; lean_object* v___x_869_; 
lean_dec(v_a_865_);
lean_dec_ref(v___y_809_);
lean_dec_ref(v___y_808_);
lean_dec_ref(v_repo_291_);
lean_dec_ref(v_name_290_);
v___x_868_ = lean_box(0);
v___x_869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_869_, 0, v___x_868_);
return v___x_869_;
}
else
{
lean_object* v___x_870_; size_t v___x_871_; size_t v___x_872_; lean_object* v___x_873_; 
v___x_870_ = lean_box(0);
v___x_871_ = ((size_t)0ULL);
v___x_872_ = lean_usize_of_nat(v___x_866_);
v___x_873_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_865_, v___x_871_, v___x_872_, v___x_870_, v_a_294_);
lean_dec(v_a_865_);
if (lean_obj_tag(v___x_873_) == 0)
{
lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_880_; 
lean_dec_ref(v___y_809_);
lean_dec_ref(v___y_808_);
lean_dec_ref(v_repo_291_);
lean_dec_ref(v_name_290_);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_873_);
if (v_isSharedCheck_880_ == 0)
{
lean_object* v_unused_881_; 
v_unused_881_ = lean_ctor_get(v___x_873_, 0);
lean_dec(v_unused_881_);
v___x_875_ = v___x_873_;
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
else
{
lean_dec(v___x_873_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_878_; 
if (v_isShared_876_ == 0)
{
lean_ctor_set_tag(v___x_875_, 1);
lean_ctor_set(v___x_875_, 0, v___x_870_);
v___x_878_ = v___x_875_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v___x_870_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
else
{
v___y_797_ = v___y_807_;
v___y_798_ = v___y_808_;
v___y_799_ = v___y_809_;
v___y_800_ = v___x_873_;
goto v___jp_796_;
}
}
}
}
}
v___jp_882_:
{
if (v_a_886_ == 0)
{
lean_object* v___x_887_; lean_object* v___x_888_; uint8_t v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_887_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__7));
lean_inc_ref(v_name_290_);
v___x_888_ = lean_string_append(v_name_290_, v___x_887_);
v___x_889_ = 1;
v___x_890_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_890_, 0, v___x_888_);
lean_ctor_set_uint8(v___x_890_, sizeof(void*)*1, v___x_889_);
lean_inc_ref(v_a_294_);
v___x_891_ = lean_apply_2(v_a_294_, v___x_890_, lean_box(0));
lean_inc_ref(v_repo_291_);
v___x_892_ = l_IO_FS_createDirAll(v_repo_291_);
if (lean_obj_tag(v___x_892_) == 0)
{
lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_925_; 
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_892_);
if (v_isSharedCheck_925_ == 0)
{
lean_object* v_unused_926_; 
v_unused_926_ = lean_ctor_get(v___x_892_, 0);
lean_dec(v_unused_926_);
v___x_894_ = v___x_892_;
v_isShared_895_ = v_isSharedCheck_925_;
goto v_resetjp_893_;
}
else
{
lean_dec(v___x_892_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_925_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_896_ = lean_unsigned_to_nat(0u);
v___x_897_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_291_);
v___x_898_ = l_Lake_GitRepo_quietInit(v_repo_291_, v___x_897_);
if (lean_obj_tag(v___x_898_) == 0)
{
lean_object* v_a_899_; lean_object* v___x_900_; uint8_t v___x_901_; 
lean_del_object(v___x_894_);
v_a_899_ = lean_ctor_get(v___x_898_, 1);
lean_inc(v_a_899_);
lean_dec_ref_known(v___x_898_, 2);
v___x_900_ = lean_array_get_size(v_a_899_);
v___x_901_ = lean_nat_dec_lt(v___x_896_, v___x_900_);
if (v___x_901_ == 0)
{
lean_dec(v_a_899_);
v___y_589_ = v___y_883_;
v___y_590_ = v___y_884_;
v___y_591_ = v___y_885_;
goto v___jp_588_;
}
else
{
lean_object* v___x_902_; size_t v___x_903_; size_t v___x_904_; lean_object* v___x_905_; 
v___x_902_ = lean_box(0);
v___x_903_ = ((size_t)0ULL);
v___x_904_ = lean_usize_of_nat(v___x_900_);
v___x_905_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_899_, v___x_903_, v___x_904_, v___x_902_, v_a_294_);
lean_dec(v_a_899_);
if (lean_obj_tag(v___x_905_) == 0)
{
lean_dec_ref_known(v___x_905_, 1);
v___y_589_ = v___y_883_;
v___y_590_ = v___y_884_;
v___y_591_ = v___y_885_;
goto v___jp_588_;
}
else
{
v___y_620_ = v___y_883_;
v___y_621_ = v___y_884_;
v___y_622_ = v___y_885_;
v___y_623_ = v___x_905_;
goto v___jp_619_;
}
}
}
else
{
lean_object* v_a_906_; lean_object* v___x_907_; uint8_t v___x_908_; 
v_a_906_ = lean_ctor_get(v___x_898_, 1);
lean_inc(v_a_906_);
lean_dec_ref_known(v___x_898_, 2);
v___x_907_ = lean_array_get_size(v_a_906_);
v___x_908_ = lean_nat_dec_lt(v___x_896_, v___x_907_);
if (v___x_908_ == 0)
{
lean_object* v___x_909_; lean_object* v___x_911_; 
lean_dec(v_a_906_);
lean_dec_ref(v___y_885_);
lean_dec_ref(v___y_884_);
lean_dec_ref(v_repo_291_);
lean_dec_ref(v_name_290_);
v___x_909_ = lean_box(0);
if (v_isShared_895_ == 0)
{
lean_ctor_set_tag(v___x_894_, 1);
lean_ctor_set(v___x_894_, 0, v___x_909_);
v___x_911_ = v___x_894_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v___x_909_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
else
{
lean_object* v___x_913_; size_t v___x_914_; size_t v___x_915_; lean_object* v___x_916_; 
lean_del_object(v___x_894_);
v___x_913_ = lean_box(0);
v___x_914_ = ((size_t)0ULL);
v___x_915_ = lean_usize_of_nat(v___x_907_);
v___x_916_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_906_, v___x_914_, v___x_915_, v___x_913_, v_a_294_);
lean_dec(v_a_906_);
if (lean_obj_tag(v___x_916_) == 0)
{
lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_923_; 
lean_dec_ref(v___y_885_);
lean_dec_ref(v___y_884_);
lean_dec_ref(v_repo_291_);
lean_dec_ref(v_name_290_);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_916_);
if (v_isSharedCheck_923_ == 0)
{
lean_object* v_unused_924_; 
v_unused_924_ = lean_ctor_get(v___x_916_, 0);
lean_dec(v_unused_924_);
v___x_918_ = v___x_916_;
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
else
{
lean_dec(v___x_916_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_921_; 
if (v_isShared_919_ == 0)
{
lean_ctor_set_tag(v___x_918_, 1);
lean_ctor_set(v___x_918_, 0, v___x_913_);
v___x_921_ = v___x_918_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v___x_913_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
}
else
{
v___y_620_ = v___y_883_;
v___y_621_ = v___y_884_;
v___y_622_ = v___y_885_;
v___y_623_ = v___x_916_;
goto v___jp_619_;
}
}
}
}
}
else
{
lean_object* v_a_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_939_; 
lean_dec_ref(v___y_885_);
lean_dec_ref(v___y_884_);
lean_dec_ref(v_repo_291_);
lean_dec_ref(v_name_290_);
v_a_927_ = lean_ctor_get(v___x_892_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_892_);
if (v_isSharedCheck_939_ == 0)
{
v___x_929_ = v___x_892_;
v_isShared_930_ = v_isSharedCheck_939_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_a_927_);
lean_dec(v___x_892_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_939_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_931_; uint8_t v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_937_; 
v___x_931_ = lean_io_error_to_string(v_a_927_);
v___x_932_ = 3;
v___x_933_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_933_, 0, v___x_931_);
lean_ctor_set_uint8(v___x_933_, sizeof(void*)*1, v___x_932_);
lean_inc_ref(v_a_294_);
v___x_934_ = lean_apply_2(v_a_294_, v___x_933_, lean_box(0));
v___x_935_ = lean_box(0);
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 0, v___x_935_);
v___x_937_ = v___x_929_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v___x_935_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
}
}
else
{
lean_object* v___x_940_; lean_object* v___x_941_; uint8_t v___x_942_; 
v___x_940_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_291_);
lean_inc_ref(v___y_883_);
v___x_941_ = l_Lake_GitRepo_getRemoteUrl_x3f(v___y_883_, v_repo_291_);
v___x_942_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_942_ == 0)
{
v___y_807_ = v___y_883_;
v___y_808_ = v___y_884_;
v___y_809_ = v___y_885_;
v_a_810_ = v___x_941_;
goto v___jp_806_;
}
else
{
lean_object* v___x_943_; size_t v___x_944_; size_t v___x_945_; lean_object* v___x_946_; 
v___x_943_ = lean_box(0);
v___x_944_ = ((size_t)0ULL);
v___x_945_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_946_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_940_, v___x_944_, v___x_945_, v___x_943_, v_a_294_);
if (lean_obj_tag(v___x_946_) == 0)
{
lean_dec_ref_known(v___x_946_, 1);
v___y_807_ = v___y_883_;
v___y_808_ = v___y_884_;
v___y_809_ = v___y_885_;
v_a_810_ = v___x_941_;
goto v___jp_806_;
}
else
{
lean_dec(v___x_941_);
lean_dec_ref(v___y_885_);
lean_dec_ref(v___y_884_);
lean_dec_ref(v_repo_291_);
lean_dec_ref(v_name_290_);
return v___x_946_;
}
}
}
}
v___jp_947_:
{
lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; uint8_t v___x_954_; uint8_t v___x_955_; 
v___x_951_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_952_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__8));
lean_inc_ref(v_repo_291_);
v___x_953_ = l_System_FilePath_join(v_repo_291_, v___x_952_);
v___x_954_ = l_System_FilePath_pathExists(v___x_953_);
lean_dec_ref(v___x_953_);
v___x_955_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_955_ == 0)
{
v___y_883_ = v___y_948_;
v___y_884_ = v_a_950_;
v___y_885_ = v___y_949_;
v_a_886_ = v___x_954_;
goto v___jp_882_;
}
else
{
lean_object* v___x_956_; size_t v___x_957_; size_t v___x_958_; lean_object* v___x_959_; 
v___x_956_ = lean_box(0);
v___x_957_ = ((size_t)0ULL);
v___x_958_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_959_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_951_, v___x_957_, v___x_958_, v___x_956_, v_a_294_);
if (lean_obj_tag(v___x_959_) == 0)
{
lean_dec_ref_known(v___x_959_, 1);
v___y_883_ = v___y_948_;
v___y_884_ = v_a_950_;
v___y_885_ = v___y_949_;
v_a_886_ = v___x_954_;
goto v___jp_882_;
}
else
{
lean_dec_ref(v_a_950_);
lean_dec_ref(v___y_949_);
lean_dec_ref(v_repo_291_);
lean_dec_ref(v_name_290_);
return v___x_959_;
}
}
}
v___jp_960_:
{
if (lean_obj_tag(v_a_963_) == 1)
{
lean_object* v_val_964_; 
lean_dec_ref(v_url_292_);
v_val_964_ = lean_ctor_get(v_a_963_, 0);
lean_inc(v_val_964_);
lean_dec_ref_known(v_a_963_, 1);
v___y_948_ = v___y_961_;
v___y_949_ = v___y_962_;
v_a_950_ = v_val_964_;
goto v___jp_947_;
}
else
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; uint8_t v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
lean_dec(v_a_963_);
lean_dec_ref(v___y_962_);
lean_dec_ref(v_repo_291_);
v___x_965_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__0));
v___x_966_ = lean_string_append(v_name_290_, v___x_965_);
v___x_967_ = lean_string_append(v___x_966_, v_url_292_);
lean_dec_ref(v_url_292_);
v___x_968_ = 3;
v___x_969_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_969_, 0, v___x_967_);
lean_ctor_set_uint8(v___x_969_, sizeof(void*)*1, v___x_968_);
lean_inc_ref(v_a_294_);
v___x_970_ = lean_apply_2(v_a_294_, v___x_969_, lean_box(0));
v___x_971_ = lean_box(0);
v___x_972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_972_, 0, v___x_971_);
return v___x_972_;
}
}
v___jp_973_:
{
lean_object* v___x_979_; uint8_t v___x_980_; 
v___x_979_ = lean_array_get_size(v___y_977_);
v___x_980_ = lean_nat_dec_lt(v___y_975_, v___x_979_);
if (v___x_980_ == 0)
{
v___y_961_ = v___y_974_;
v___y_962_ = v___y_976_;
v_a_963_ = v_val_978_;
goto v___jp_960_;
}
else
{
lean_object* v___x_981_; size_t v___x_982_; size_t v___x_983_; lean_object* v___x_984_; 
v___x_981_ = lean_box(0);
v___x_982_ = ((size_t)0ULL);
v___x_983_ = lean_usize_of_nat(v___x_979_);
v___x_984_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_977_, v___x_982_, v___x_983_, v___x_981_, v_a_294_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_dec_ref_known(v___x_984_, 1);
v___y_961_ = v___y_974_;
v___y_962_ = v___y_976_;
v_a_963_ = v_val_978_;
goto v___jp_960_;
}
else
{
lean_dec(v_val_978_);
lean_dec_ref(v___y_976_);
lean_dec_ref(v_url_292_);
lean_dec_ref(v_repo_291_);
lean_dec_ref(v_name_290_);
return v___x_984_;
}
}
}
v___jp_985_:
{
if (v_a_988_ == 0)
{
v___y_948_ = v___y_986_;
v___y_949_ = v___y_987_;
v_a_950_ = v_url_292_;
goto v___jp_947_;
}
else
{
lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; uint8_t v___x_993_; 
v___x_989_ = lean_unsigned_to_nat(0u);
v___x_990_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_url_292_);
v___x_991_ = l_Lake_resolvePath(v_url_292_);
v___x_992_ = lean_string_utf8_byte_size(v___x_991_);
v___x_993_ = lean_nat_dec_eq(v___x_992_, v___x_989_);
if (v___x_993_ == 0)
{
lean_object* v___x_994_; 
v___x_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_994_, 0, v___x_991_);
v___y_974_ = v___y_986_;
v___y_975_ = v___x_989_;
v___y_976_ = v___y_987_;
v___y_977_ = v___x_990_;
v_val_978_ = v___x_994_;
goto v___jp_973_;
}
else
{
lean_object* v___x_995_; 
lean_dec_ref(v___x_991_);
v___x_995_ = lean_box(0);
v___y_974_ = v___y_986_;
v___y_975_ = v___x_989_;
v___y_976_ = v___y_987_;
v___y_977_ = v___x_990_;
v_val_978_ = v___x_995_;
goto v___jp_973_;
}
}
}
v___jp_996_:
{
lean_object* v_remote_998_; lean_object* v___x_999_; uint8_t v___x_1000_; uint8_t v___x_1001_; 
v_remote_998_ = l_Lake_Git_defaultRemote;
v___x_999_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_1000_ = l_System_FilePath_pathExists(v_url_292_);
v___x_1001_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_1001_ == 0)
{
v___y_986_ = v_remote_998_;
v___y_987_ = v___y_997_;
v_a_988_ = v___x_1000_;
goto v___jp_985_;
}
else
{
lean_object* v___x_1002_; size_t v___x_1003_; size_t v___x_1004_; lean_object* v___x_1005_; 
v___x_1002_ = lean_box(0);
v___x_1003_ = ((size_t)0ULL);
v___x_1004_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_1005_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_999_, v___x_1003_, v___x_1004_, v___x_1002_, v_a_294_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_dec_ref_known(v___x_1005_, 1);
v___y_986_ = v_remote_998_;
v___y_987_ = v___y_997_;
v_a_988_ = v___x_1000_;
goto v___jp_985_;
}
else
{
lean_dec_ref(v___y_997_);
lean_dec_ref(v_url_292_);
lean_dec_ref(v_repo_291_);
lean_dec_ref(v_name_290_);
return v___x_1005_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_290_ = stack[0].m_obj;
lean_object* v_repo_291_ = stack[1].m_obj;
lean_object* v_url_292_ = stack[2].m_obj;
lean_object* v_rev_x3f_293_ = stack[3].m_obj;
lean_object* v_a_294_ = stack[4].m_obj;
lean_object* v_res_1008_;
v_res_1008_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo(v_name_290_, v_repo_291_, v_url_292_, v_rev_x3f_293_, v_a_294_);
stack->m_obj
 = v_res_1008_;
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___boxed(lean_object* v_name_1009_, lean_object* v_repo_1010_, lean_object* v_url_1011_, lean_object* v_rev_x3f_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo(v_name_1009_, v_repo_1010_, v_url_1011_, v_rev_x3f_1012_, v_a_1013_);
lean_dec_ref(v_a_1013_);
return v_res_1015_;
}
}
static lean_object* _init_l_Lake_instInhabitedMaterializedDep_default___closed__4(void){
_start:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1022_ = l_Lake_instInhabitedPackageEntry_default;
v___x_1023_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__3));
v___x_1024_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___x_1025_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1024_);
lean_ctor_set(v___x_1025_, 1, v___x_1024_);
lean_ctor_set(v___x_1025_, 2, v___x_1024_);
lean_ctor_set(v___x_1025_, 3, v___x_1023_);
lean_ctor_set(v___x_1025_, 4, v___x_1022_);
return v___x_1025_;
}
}
static lean_object* _init_l_Lake_instInhabitedMaterializedDep_default(void){
_start:
{
lean_object* v___x_1026_; 
v___x_1026_ = lean_obj_once(&l_Lake_instInhabitedMaterializedDep_default___closed__4, &l_Lake_instInhabitedMaterializedDep_default___closed__4_once, _init_l_Lake_instInhabitedMaterializedDep_default___closed__4);
return v___x_1026_;
}
}
static lean_object* _init_l_Lake_instInhabitedMaterializedDep(void){
_start:
{
lean_object* v___x_1027_; 
v___x_1027_ = l_Lake_instInhabitedMaterializedDep_default;
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_name(lean_object* v_self_1028_){
_start:
{
lean_object* v_manifestEntry_1029_; lean_object* v_name_1030_; 
v_manifestEntry_1029_ = lean_ctor_get(v_self_1028_, 4);
v_name_1030_ = lean_ctor_get(v_manifestEntry_1029_, 0);
lean_inc(v_name_1030_);
return v_name_1030_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_name___boxed(lean_object* v_self_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l_Lake_MaterializedDep_name(v_self_1031_);
lean_dec_ref(v_self_1031_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_prettyName(lean_object* v_self_1033_){
_start:
{
lean_object* v_manifestEntry_1034_; lean_object* v_name_1035_; uint8_t v___x_1036_; lean_object* v___x_1037_; 
v_manifestEntry_1034_ = lean_ctor_get(v_self_1033_, 4);
lean_inc_ref(v_manifestEntry_1034_);
lean_dec_ref(v_self_1033_);
v_name_1035_ = lean_ctor_get(v_manifestEntry_1034_, 0);
lean_inc(v_name_1035_);
lean_dec_ref(v_manifestEntry_1034_);
v___x_1036_ = 0;
v___x_1037_ = l_Lean_Name_toString(v_name_1035_, v___x_1036_);
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_scope(lean_object* v_self_1038_){
_start:
{
lean_object* v_manifestEntry_1039_; lean_object* v_scope_1040_; 
v_manifestEntry_1039_ = lean_ctor_get(v_self_1038_, 4);
v_scope_1040_ = lean_ctor_get(v_manifestEntry_1039_, 1);
lean_inc_ref(v_scope_1040_);
return v_scope_1040_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_scope___boxed(lean_object* v_self_1041_){
_start:
{
lean_object* v_res_1042_; 
v_res_1042_ = l_Lake_MaterializedDep_scope(v_self_1041_);
lean_dec_ref(v_self_1041_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relManifestFile_x3f(lean_object* v_self_1043_){
_start:
{
lean_object* v_manifestEntry_1044_; lean_object* v_manifestFile_x3f_1045_; 
v_manifestEntry_1044_ = lean_ctor_get(v_self_1043_, 4);
v_manifestFile_x3f_1045_ = lean_ctor_get(v_manifestEntry_1044_, 3);
lean_inc(v_manifestFile_x3f_1045_);
return v_manifestFile_x3f_1045_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relManifestFile_x3f___boxed(lean_object* v_self_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l_Lake_MaterializedDep_relManifestFile_x3f(v_self_1046_);
lean_dec_ref(v_self_1046_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relManifestFile(lean_object* v_self_1048_){
_start:
{
lean_object* v_manifestEntry_1049_; lean_object* v_manifestFile_x3f_1050_; 
v_manifestEntry_1049_ = lean_ctor_get(v_self_1048_, 4);
v_manifestFile_x3f_1050_ = lean_ctor_get(v_manifestEntry_1049_, 3);
if (lean_obj_tag(v_manifestFile_x3f_1050_) == 0)
{
lean_object* v___x_1051_; 
v___x_1051_ = l_Lake_defaultManifestFile;
return v___x_1051_;
}
else
{
lean_object* v_val_1052_; 
v_val_1052_ = lean_ctor_get(v_manifestFile_x3f_1050_, 0);
lean_inc(v_val_1052_);
return v_val_1052_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relManifestFile___boxed(lean_object* v_self_1053_){
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l_Lake_MaterializedDep_relManifestFile(v_self_1053_);
lean_dec_ref(v_self_1053_);
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_manifestFile(lean_object* v_self_1055_){
_start:
{
lean_object* v_manifestEntry_1056_; lean_object* v_manifestFile_x3f_1057_; 
v_manifestEntry_1056_ = lean_ctor_get(v_self_1055_, 4);
v_manifestFile_x3f_1057_ = lean_ctor_get(v_manifestEntry_1056_, 3);
if (lean_obj_tag(v_manifestFile_x3f_1057_) == 0)
{
lean_object* v_pkgDir_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; 
v_pkgDir_1058_ = lean_ctor_get(v_self_1055_, 0);
lean_inc_ref(v_pkgDir_1058_);
lean_dec_ref(v_self_1055_);
v___x_1059_ = l_Lake_defaultManifestFile;
v___x_1060_ = l_Lake_joinRelative(v_pkgDir_1058_, v___x_1059_);
return v___x_1060_;
}
else
{
lean_object* v_pkgDir_1061_; lean_object* v_val_1062_; lean_object* v___x_1063_; 
lean_inc_ref(v_manifestFile_x3f_1057_);
v_pkgDir_1061_ = lean_ctor_get(v_self_1055_, 0);
lean_inc_ref(v_pkgDir_1061_);
lean_dec_ref(v_self_1055_);
v_val_1062_ = lean_ctor_get(v_manifestFile_x3f_1057_, 0);
lean_inc(v_val_1062_);
lean_dec_ref_known(v_manifestFile_x3f_1057_, 1);
v___x_1063_ = l_Lake_joinRelative(v_pkgDir_1061_, v_val_1062_);
return v___x_1063_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relConfigFile(lean_object* v_self_1064_){
_start:
{
lean_object* v_manifestEntry_1065_; lean_object* v_configFile_1066_; 
v_manifestEntry_1065_ = lean_ctor_get(v_self_1064_, 4);
v_configFile_1066_ = lean_ctor_get(v_manifestEntry_1065_, 2);
lean_inc_ref(v_configFile_1066_);
return v_configFile_1066_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relConfigFile___boxed(lean_object* v_self_1067_){
_start:
{
lean_object* v_res_1068_; 
v_res_1068_ = l_Lake_MaterializedDep_relConfigFile(v_self_1067_);
lean_dec_ref(v_self_1067_);
return v_res_1068_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_configFile(lean_object* v_self_1069_){
_start:
{
lean_object* v_manifestEntry_1070_; lean_object* v_pkgDir_1071_; lean_object* v_configFile_1072_; lean_object* v___x_1073_; 
v_manifestEntry_1070_ = lean_ctor_get(v_self_1069_, 4);
lean_inc_ref(v_manifestEntry_1070_);
v_pkgDir_1071_ = lean_ctor_get(v_self_1069_, 0);
lean_inc_ref(v_pkgDir_1071_);
lean_dec_ref(v_self_1069_);
v_configFile_1072_ = lean_ctor_get(v_manifestEntry_1070_, 2);
lean_inc_ref(v_configFile_1072_);
lean_dec_ref(v_manifestEntry_1070_);
v___x_1073_ = l_Lake_joinRelative(v_pkgDir_1071_, v_configFile_1072_);
return v___x_1073_;
}
}
uint8_t l_Lake_MaterializedDep_fixedToolchain(lean_object* v_self_1074_){
_start:
{
lean_object* v_manifest_x3f_1075_; 
v_manifest_x3f_1075_ = lean_ctor_get(v_self_1074_, 3);
if (lean_obj_tag(v_manifest_x3f_1075_) == 1)
{
lean_object* v_a_1076_; uint8_t v_fixedToolchain_1077_; 
v_a_1076_ = lean_ctor_get(v_manifest_x3f_1075_, 0);
v_fixedToolchain_1077_ = lean_ctor_get_uint8(v_a_1076_, sizeof(void*)*4);
return v_fixedToolchain_1077_;
}
else
{
uint8_t v___x_1078_; 
v___x_1078_ = 0;
return v___x_1078_;
}
}
}
LEAN_EXPORT void l_Lake_MaterializedDep_fixedToolchain_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_1074_ = stack[0].m_obj;
uint8_t v_res_1079_;
v_res_1079_ = l_Lake_MaterializedDep_fixedToolchain(v_self_1074_);
stack->m_num = v_res_1079_;
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_fixedToolchain___boxed(lean_object* v_self_1080_){
_start:
{
uint8_t v_res_1081_; lean_object* v_r_1082_; 
v_res_1081_ = l_Lake_MaterializedDep_fixedToolchain(v_self_1080_);
lean_dec_ref(v_self_1080_);
v_r_1082_ = lean_box(v_res_1081_);
return v_r_1082_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed(lean_object* v_dep_1091_){
_start:
{
lean_object* v_name_1092_; lean_object* v_scope_1093_; lean_object* v_version_1094_; lean_object* v_fst_1096_; lean_object* v_snd_1097_; 
v_name_1092_ = lean_ctor_get(v_dep_1091_, 0);
lean_inc(v_name_1092_);
v_scope_1093_ = lean_ctor_get(v_dep_1091_, 1);
lean_inc_ref(v_scope_1093_);
v_version_1094_ = lean_ctor_get(v_dep_1091_, 2);
lean_inc(v_version_1094_);
lean_dec_ref(v_dep_1091_);
switch(lean_obj_tag(v_version_1094_))
{
case 0:
{
lean_object* v___x_1120_; 
v___x_1120_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v_fst_1096_ = v___x_1120_;
v_snd_1097_ = v___x_1120_;
goto v___jp_1095_;
}
case 1:
{
lean_object* v_rev_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1136_; 
v_rev_1121_ = lean_ctor_get(v_version_1094_, 0);
v_isSharedCheck_1136_ = !lean_is_exclusive(v_version_1094_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1123_ = v_version_1094_;
v_isShared_1124_ = v_isSharedCheck_1136_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_rev_1121_);
lean_dec(v_version_1094_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1136_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1128_; 
v___x_1125_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__5));
v___x_1126_ = l_String_quote(v_rev_1121_);
if (v_isShared_1124_ == 0)
{
lean_ctor_set_tag(v___x_1123_, 3);
lean_ctor_set(v___x_1123_, 0, v___x_1126_);
v___x_1128_ = v___x_1123_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v___x_1126_);
v___x_1128_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1129_ = l_Std_Format_defWidth;
v___x_1130_ = lean_unsigned_to_nat(0u);
v___x_1131_ = l_Std_Format_pretty(v___x_1128_, v___x_1129_, v___x_1130_, v___x_1130_);
v___x_1132_ = lean_string_append(v___x_1125_, v___x_1131_);
v___x_1133_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__6));
v___x_1134_ = lean_string_append(v___x_1133_, v___x_1131_);
lean_dec_ref(v___x_1131_);
v_fst_1096_ = v___x_1132_;
v_snd_1097_ = v___x_1134_;
goto v___jp_1095_;
}
}
}
default: 
{
lean_object* v_ver_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1153_; 
v_ver_1137_ = lean_ctor_get(v_version_1094_, 0);
v_isSharedCheck_1153_ = !lean_is_exclusive(v_version_1094_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1139_ = v_version_1094_;
v_isShared_1140_ = v_isSharedCheck_1153_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_ver_1137_);
lean_dec(v_version_1094_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1153_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v_toString_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1145_; 
v_toString_1141_ = lean_ctor_get(v_ver_1137_, 0);
lean_inc_ref(v_toString_1141_);
lean_dec_ref(v_ver_1137_);
v___x_1142_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__5));
v___x_1143_ = l_String_quote(v_toString_1141_);
if (v_isShared_1140_ == 0)
{
lean_ctor_set_tag(v___x_1139_, 3);
lean_ctor_set(v___x_1139_, 0, v___x_1143_);
v___x_1145_ = v___x_1139_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v___x_1143_);
v___x_1145_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1146_ = l_Std_Format_defWidth;
v___x_1147_ = lean_unsigned_to_nat(0u);
v___x_1148_ = l_Std_Format_pretty(v___x_1145_, v___x_1146_, v___x_1147_, v___x_1147_);
v___x_1149_ = lean_string_append(v___x_1142_, v___x_1148_);
v___x_1150_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__7));
v___x_1151_ = lean_string_append(v___x_1150_, v___x_1148_);
lean_dec_ref(v___x_1148_);
v_fst_1096_ = v___x_1149_;
v_snd_1097_ = v___x_1151_;
goto v___jp_1095_;
}
}
}
}
v___jp_1095_:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; uint8_t v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1098_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
lean_inc_ref(v_scope_1093_);
v___x_1099_ = lean_string_append(v_scope_1093_, v___x_1098_);
v___x_1100_ = 0;
v___x_1101_ = l_Lean_Name_toString(v_name_1092_, v___x_1100_);
v___x_1102_ = lean_string_append(v___x_1099_, v___x_1101_);
v___x_1103_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__1));
v___x_1104_ = lean_string_append(v___x_1102_, v___x_1103_);
v___x_1105_ = lean_string_append(v___x_1104_, v_scope_1093_);
v___x_1106_ = lean_string_append(v___x_1105_, v___x_1098_);
v___x_1107_ = lean_string_append(v___x_1106_, v___x_1101_);
v___x_1108_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__2));
v___x_1109_ = lean_string_append(v___x_1107_, v___x_1108_);
v___x_1110_ = lean_string_append(v___x_1109_, v_fst_1096_);
lean_dec_ref(v_fst_1096_);
v___x_1111_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__3));
v___x_1112_ = lean_string_append(v___x_1110_, v___x_1111_);
v___x_1113_ = lean_string_append(v___x_1112_, v_scope_1093_);
lean_dec_ref(v_scope_1093_);
v___x_1114_ = lean_string_append(v___x_1113_, v___x_1098_);
v___x_1115_ = lean_string_append(v___x_1114_, v___x_1101_);
lean_dec_ref(v___x_1101_);
v___x_1116_ = lean_string_append(v___x_1115_, v___x_1108_);
v___x_1117_ = lean_string_append(v___x_1116_, v_snd_1097_);
lean_dec_ref(v_snd_1097_);
v___x_1118_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__4));
v___x_1119_ = lean_string_append(v___x_1117_, v___x_1118_);
return v___x_1119_;
}
}
}
lean_object* l___private_Lake_Load_Materialize_0__Lake_mkPath(lean_object* v_wsDir_1154_, lean_object* v_relPkgsDir_1155_, lean_object* v_relSrc_1156_, lean_object* v_dirName_1157_, uint8_t v_copy_1158_, uint8_t v_update_1159_){
_start:
{
if (v_copy_1158_ == 0)
{
lean_object* v___x_1161_; 
lean_dec_ref(v_dirName_1157_);
lean_dec_ref(v_relPkgsDir_1155_);
lean_dec_ref(v_wsDir_1154_);
v___x_1161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1161_, 0, v_relSrc_1156_);
return v___x_1161_;
}
else
{
lean_object* v_relDst_1162_; lean_object* v_dst_1163_; 
v_relDst_1162_ = l_Lake_joinRelative(v_relPkgsDir_1155_, v_dirName_1157_);
lean_inc_ref(v_relDst_1162_);
lean_inc_ref(v_wsDir_1154_);
v_dst_1163_ = l_Lake_joinRelative(v_wsDir_1154_, v_relDst_1162_);
if (v_update_1159_ == 0)
{
uint8_t v___x_1183_; 
v___x_1183_ = l_System_FilePath_pathExists(v_dst_1163_);
if (v___x_1183_ == 0)
{
goto v___jp_1164_;
}
else
{
lean_object* v___x_1184_; 
lean_dec_ref(v_dst_1163_);
lean_dec_ref(v_relSrc_1156_);
lean_dec_ref(v_wsDir_1154_);
v___x_1184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1184_, 0, v_relDst_1162_);
return v___x_1184_;
}
}
else
{
lean_object* v___x_1185_; 
v___x_1185_ = l_Lake_removeDirAllIfExists(v_dst_1163_);
if (lean_obj_tag(v___x_1185_) == 0)
{
lean_dec_ref_known(v___x_1185_, 1);
goto v___jp_1164_;
}
else
{
lean_object* v_a_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1193_; 
lean_dec_ref(v_dst_1163_);
lean_dec_ref(v_relDst_1162_);
lean_dec_ref(v_relSrc_1156_);
lean_dec_ref(v_wsDir_1154_);
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
v___jp_1164_:
{
lean_object* v_src_1165_; lean_object* v___x_1166_; 
v_src_1165_ = l_Lake_joinRelative(v_wsDir_1154_, v_relSrc_1156_);
v___x_1166_ = l_Lake_copyDirAll(v_src_1165_, v_dst_1163_);
if (lean_obj_tag(v___x_1166_) == 0)
{
lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1173_; 
v_isSharedCheck_1173_ = !lean_is_exclusive(v___x_1166_);
if (v_isSharedCheck_1173_ == 0)
{
lean_object* v_unused_1174_; 
v_unused_1174_ = lean_ctor_get(v___x_1166_, 0);
lean_dec(v_unused_1174_);
v___x_1168_ = v___x_1166_;
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
else
{
lean_dec(v___x_1166_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1171_; 
if (v_isShared_1169_ == 0)
{
lean_ctor_set(v___x_1168_, 0, v_relDst_1162_);
v___x_1171_ = v___x_1168_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_relDst_1162_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
return v___x_1171_;
}
}
}
else
{
lean_object* v_a_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1182_; 
lean_dec_ref(v_relDst_1162_);
v_a_1175_ = lean_ctor_get(v___x_1166_, 0);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1166_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1177_ = v___x_1166_;
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_a_1175_);
lean_dec(v___x_1166_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1180_; 
if (v_isShared_1178_ == 0)
{
v___x_1180_ = v___x_1177_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_a_1175_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Load_Materialize_0__Lake_mkPath_0interp(lean_interpreter_value* stack)
{
lean_object* v_wsDir_1154_ = stack[0].m_obj;
lean_object* v_relPkgsDir_1155_ = stack[1].m_obj;
lean_object* v_relSrc_1156_ = stack[2].m_obj;
lean_object* v_dirName_1157_ = stack[3].m_obj;
uint8_t v_copy_1158_ = stack[4].m_num;
uint8_t v_update_1159_ = stack[5].m_num;
lean_object* v_res_1194_;
v_res_1194_ = l___private_Lake_Load_Materialize_0__Lake_mkPath(v_wsDir_1154_, v_relPkgsDir_1155_, v_relSrc_1156_, v_dirName_1157_, v_copy_1158_, v_update_1159_);
stack->m_obj
 = v_res_1194_;
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_mkPath___boxed(lean_object* v_wsDir_1195_, lean_object* v_relPkgsDir_1196_, lean_object* v_relSrc_1197_, lean_object* v_dirName_1198_, lean_object* v_copy_1199_, lean_object* v_update_1200_, lean_object* v_a_1201_){
_start:
{
uint8_t v_copy_boxed_1202_; uint8_t v_update_boxed_1203_; lean_object* v_res_1204_; 
v_copy_boxed_1202_ = lean_unbox(v_copy_1199_);
v_update_boxed_1203_ = lean_unbox(v_update_1200_);
v_res_1204_ = l___private_Lake_Load_Materialize_0__Lake_mkPath(v_wsDir_1195_, v_relPkgsDir_1196_, v_relSrc_1197_, v_dirName_1198_, v_copy_boxed_1202_, v_update_boxed_1203_);
return v_res_1204_;
}
}
lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep(lean_object* v_dep_1206_, uint8_t v_inherited_1207_, lean_object* v_wsDir_1208_, lean_object* v_name_1209_, lean_object* v_relPkgDir_1210_, lean_object* v_remoteUrl_1211_, lean_object* v_src_1212_, lean_object* v_a_1213_){
_start:
{
lean_object* v___y_1216_; lean_object* v_a_1217_; lean_object* v___f_1234_; lean_object* v___y_1236_; lean_object* v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1239_; lean_object* v_val_1240_; lean_object* v_pkgDir_1256_; lean_object* v_a_1258_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v_val_1294_; lean_object* v___x_1309_; lean_object* v___x_1310_; uint8_t v___x_1311_; 
v___f_1234_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__1));
lean_inc_ref(v_relPkgDir_1210_);
v_pkgDir_1256_ = l_Lake_joinRelative(v_wsDir_1208_, v_relPkgDir_1210_);
v___x_1290_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3);
v___x_1291_ = lean_unsigned_to_nat(0u);
v___x_1292_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_pkgDir_1256_);
v___x_1309_ = l_Lake_resolvePath(v_pkgDir_1256_);
v___x_1310_ = lean_string_utf8_byte_size(v___x_1309_);
v___x_1311_ = lean_nat_dec_eq(v___x_1310_, v___x_1291_);
if (v___x_1311_ == 0)
{
lean_object* v___x_1312_; 
v___x_1312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1312_, 0, v___x_1309_);
v_val_1294_ = v___x_1312_;
goto v___jp_1293_;
}
else
{
lean_object* v___x_1313_; 
lean_dec_ref(v___x_1309_);
v___x_1313_ = lean_box(0);
v_val_1294_ = v___x_1313_;
goto v___jp_1293_;
}
v___jp_1215_:
{
lean_object* v_name_1218_; lean_object* v_scope_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1230_; 
v_name_1218_ = lean_ctor_get(v_dep_1206_, 0);
v_scope_1219_ = lean_ctor_get(v_dep_1206_, 1);
v_isSharedCheck_1230_ = !lean_is_exclusive(v_dep_1206_);
if (v_isSharedCheck_1230_ == 0)
{
lean_object* v_unused_1231_; lean_object* v_unused_1232_; lean_object* v_unused_1233_; 
v_unused_1231_ = lean_ctor_get(v_dep_1206_, 4);
lean_dec(v_unused_1231_);
v_unused_1232_ = lean_ctor_get(v_dep_1206_, 3);
lean_dec(v_unused_1232_);
v_unused_1233_ = lean_ctor_get(v_dep_1206_, 2);
lean_dec(v_unused_1233_);
v___x_1221_ = v_dep_1206_;
v_isShared_1222_ = v_isSharedCheck_1230_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_scope_1219_);
lean_inc(v_name_1218_);
lean_dec(v_dep_1206_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1230_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1227_; 
v___x_1223_ = l_Lake_defaultConfigFile;
v___x_1224_ = lean_box(0);
v___x_1225_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1225_, 0, v_name_1218_);
lean_ctor_set(v___x_1225_, 1, v_scope_1219_);
lean_ctor_set(v___x_1225_, 2, v___x_1223_);
lean_ctor_set(v___x_1225_, 3, v___x_1224_);
lean_ctor_set(v___x_1225_, 4, v_src_1212_);
lean_ctor_set_uint8(v___x_1225_, sizeof(void*)*5, v_inherited_1207_);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 4, v___x_1225_);
lean_ctor_set(v___x_1221_, 3, v_a_1217_);
lean_ctor_set(v___x_1221_, 2, v_remoteUrl_1211_);
lean_ctor_set(v___x_1221_, 1, v_relPkgDir_1210_);
lean_ctor_set(v___x_1221_, 0, v___y_1216_);
v___x_1227_ = v___x_1221_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v___y_1216_);
lean_ctor_set(v_reuseFailAlloc_1229_, 1, v_relPkgDir_1210_);
lean_ctor_set(v_reuseFailAlloc_1229_, 2, v_remoteUrl_1211_);
lean_ctor_set(v_reuseFailAlloc_1229_, 3, v_a_1217_);
lean_ctor_set(v_reuseFailAlloc_1229_, 4, v___x_1225_);
v___x_1227_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
lean_object* v___x_1228_; 
v___x_1228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1228_, 0, v___x_1227_);
return v___x_1228_;
}
}
}
v___jp_1235_:
{
lean_object* v___x_1241_; uint8_t v___x_1242_; 
v___x_1241_ = lean_array_get_size(v___y_1237_);
v___x_1242_ = lean_nat_dec_lt(v___y_1239_, v___x_1241_);
if (v___x_1242_ == 0)
{
v___y_1216_ = v___y_1236_;
v_a_1217_ = v_val_1240_;
goto v___jp_1215_;
}
else
{
lean_object* v___x_1243_; size_t v___x_1244_; size_t v___x_1245_; lean_object* v___x_1819__overap_1246_; lean_object* v___x_1247_; 
v___x_1243_ = lean_box(0);
v___x_1244_ = ((size_t)0ULL);
v___x_1245_ = lean_usize_of_nat(v___x_1241_);
lean_inc_ref(v___y_1237_);
lean_inc_ref(v___y_1238_);
v___x_1819__overap_1246_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___y_1238_, v___f_1234_, v___y_1237_, v___x_1244_, v___x_1245_, v___x_1243_);
lean_inc_ref(v_a_1213_);
v___x_1247_ = lean_apply_2(v___x_1819__overap_1246_, v_a_1213_, lean_box(0));
if (lean_obj_tag(v___x_1247_) == 0)
{
lean_dec_ref_known(v___x_1247_, 1);
v___y_1216_ = v___y_1236_;
v_a_1217_ = v_val_1240_;
goto v___jp_1215_;
}
else
{
lean_object* v_a_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1255_; 
lean_dec_ref(v_val_1240_);
lean_dec_ref(v___y_1236_);
lean_dec_ref(v_src_1212_);
lean_dec_ref(v_remoteUrl_1211_);
lean_dec_ref(v_relPkgDir_1210_);
lean_dec_ref(v_dep_1206_);
v_a_1248_ = lean_ctor_get(v___x_1247_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1247_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1250_ = v___x_1247_;
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_a_1248_);
lean_dec(v___x_1247_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1253_; 
if (v_isShared_1251_ == 0)
{
v___x_1253_ = v___x_1250_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_a_1248_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
}
}
}
v___jp_1257_:
{
if (lean_obj_tag(v_a_1258_) == 1)
{
lean_object* v_val_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
lean_dec_ref(v_pkgDir_1256_);
lean_dec_ref(v_name_1209_);
v_val_1259_ = lean_ctor_get(v_a_1258_, 0);
lean_inc_n(v_val_1259_, 2);
lean_dec_ref_known(v_a_1258_, 1);
v___x_1260_ = l_Lake_defaultManifestFile;
v___x_1261_ = l_Lake_joinRelative(v_val_1259_, v___x_1260_);
v___x_1262_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3);
v___x_1263_ = lean_unsigned_to_nat(0u);
v___x_1264_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_1265_ = l_Lake_Manifest_load(v___x_1261_);
if (lean_obj_tag(v___x_1265_) == 0)
{
lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1273_; 
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
lean_ctor_set_tag(v___x_1268_, 1);
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
v___y_1236_ = v_val_1259_;
v___y_1237_ = v___x_1264_;
v___y_1238_ = v___x_1262_;
v___y_1239_ = v___x_1263_;
v_val_1240_ = v___x_1271_;
goto v___jp_1235_;
}
}
}
else
{
lean_object* v_a_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1281_; 
v_a_1274_ = lean_ctor_get(v___x_1265_, 0);
v_isSharedCheck_1281_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1276_ = v___x_1265_;
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_a_1274_);
lean_dec(v___x_1265_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1279_; 
if (v_isShared_1277_ == 0)
{
lean_ctor_set_tag(v___x_1276_, 0);
v___x_1279_ = v___x_1276_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v_a_1274_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
v___y_1236_ = v_val_1259_;
v___y_1237_ = v___x_1264_;
v___y_1238_ = v___x_1262_;
v___y_1239_ = v___x_1263_;
v_val_1240_ = v___x_1279_;
goto v___jp_1235_;
}
}
}
}
else
{
lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; uint8_t v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; 
lean_dec(v_a_1258_);
lean_dec_ref(v_src_1212_);
lean_dec_ref(v_remoteUrl_1211_);
lean_dec_ref(v_relPkgDir_1210_);
lean_dec_ref(v_dep_1206_);
v___x_1282_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0));
v___x_1283_ = lean_string_append(v_name_1209_, v___x_1282_);
v___x_1284_ = lean_string_append(v___x_1283_, v_pkgDir_1256_);
lean_dec_ref(v_pkgDir_1256_);
v___x_1285_ = 3;
v___x_1286_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1286_, 0, v___x_1284_);
lean_ctor_set_uint8(v___x_1286_, sizeof(void*)*1, v___x_1285_);
lean_inc_ref(v_a_1213_);
v___x_1287_ = lean_apply_2(v_a_1213_, v___x_1286_, lean_box(0));
v___x_1288_ = lean_box(0);
v___x_1289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1289_, 0, v___x_1288_);
return v___x_1289_;
}
}
v___jp_1293_:
{
uint8_t v___x_1295_; 
v___x_1295_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_1295_ == 0)
{
v_a_1258_ = v_val_1294_;
goto v___jp_1257_;
}
else
{
lean_object* v___x_1296_; size_t v___x_1297_; size_t v___x_1298_; lean_object* v___x_1865__overap_1299_; lean_object* v___x_1300_; 
v___x_1296_ = lean_box(0);
v___x_1297_ = ((size_t)0ULL);
v___x_1298_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_1865__overap_1299_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1290_, v___f_1234_, v___x_1292_, v___x_1297_, v___x_1298_, v___x_1296_);
lean_inc_ref(v_a_1213_);
v___x_1300_ = lean_apply_2(v___x_1865__overap_1299_, v_a_1213_, lean_box(0));
if (lean_obj_tag(v___x_1300_) == 0)
{
lean_dec_ref_known(v___x_1300_, 1);
v_a_1258_ = v_val_1294_;
goto v___jp_1257_;
}
else
{
lean_object* v_a_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1308_; 
lean_dec(v_val_1294_);
lean_dec_ref(v_pkgDir_1256_);
lean_dec_ref(v_src_1212_);
lean_dec_ref(v_remoteUrl_1211_);
lean_dec_ref(v_relPkgDir_1210_);
lean_dec_ref(v_name_1209_);
lean_dec_ref(v_dep_1206_);
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
return v___x_1306_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep_0interp(lean_interpreter_value* stack)
{
lean_object* v_dep_1206_ = stack[0].m_obj;
uint8_t v_inherited_1207_ = stack[1].m_num;
lean_object* v_wsDir_1208_ = stack[2].m_obj;
lean_object* v_name_1209_ = stack[3].m_obj;
lean_object* v_relPkgDir_1210_ = stack[4].m_obj;
lean_object* v_remoteUrl_1211_ = stack[5].m_obj;
lean_object* v_src_1212_ = stack[6].m_obj;
lean_object* v_a_1213_ = stack[7].m_obj;
lean_object* v_res_1314_;
v_res_1314_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep(v_dep_1206_, v_inherited_1207_, v_wsDir_1208_, v_name_1209_, v_relPkgDir_1210_, v_remoteUrl_1211_, v_src_1212_, v_a_1213_);
stack->m_obj
 = v_res_1314_;
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___boxed(lean_object* v_dep_1315_, lean_object* v_inherited_1316_, lean_object* v_wsDir_1317_, lean_object* v_name_1318_, lean_object* v_relPkgDir_1319_, lean_object* v_remoteUrl_1320_, lean_object* v_src_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_){
_start:
{
uint8_t v_inherited_boxed_1324_; lean_object* v_res_1325_; 
v_inherited_boxed_1324_ = lean_unbox(v_inherited_1316_);
v_res_1325_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep(v_dep_1315_, v_inherited_boxed_1324_, v_wsDir_1317_, v_name_1318_, v_relPkgDir_1319_, v_remoteUrl_1320_, v_src_1321_, v_a_1322_);
lean_dec_ref(v_a_1322_);
return v_res_1325_;
}
}
lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(lean_object* v_a_1326_, lean_object* v_name_1327_, lean_object* v_repo_1328_, lean_object* v_url_1329_, lean_object* v_rev_x3f_1330_){
_start:
{
lean_object* v___y_1342_; lean_object* v___y_1381_; lean_object* v___y_1382_; lean_object* v___y_1384_; lean_object* v___y_1385_; lean_object* v___y_1414_; lean_object* v___y_1415_; uint8_t v_a_1416_; lean_object* v___y_1424_; uint8_t v_a_1425_; lean_object* v___y_1433_; lean_object* v___y_1434_; lean_object* v___y_1435_; lean_object* v___y_1436_; uint8_t v_val_1437_; uint8_t v___y_1445_; lean_object* v___y_1446_; lean_object* v___y_1447_; uint8_t v___y_1453_; lean_object* v___y_1454_; lean_object* v___y_1455_; lean_object* v___y_1456_; uint8_t v___y_1458_; lean_object* v___y_1459_; lean_object* v___y_1460_; uint8_t v___y_1489_; lean_object* v___y_1490_; lean_object* v___y_1491_; lean_object* v___y_1492_; lean_object* v___y_1494_; lean_object* v___y_1495_; lean_object* v___y_1496_; uint8_t v_val_1497_; lean_object* v___y_1505_; lean_object* v___y_1506_; lean_object* v___y_1507_; lean_object* v___y_1508_; lean_object* v_a_1509_; lean_object* v___y_1552_; lean_object* v___y_1553_; lean_object* v___y_1554_; lean_object* v___y_1555_; lean_object* v_a_1556_; lean_object* v___y_1578_; lean_object* v___y_1579_; lean_object* v___y_1580_; lean_object* v___y_1581_; lean_object* v___y_1620_; lean_object* v___y_1621_; lean_object* v___y_1622_; lean_object* v___y_1623_; lean_object* v___y_1625_; lean_object* v___y_1626_; lean_object* v___y_1627_; lean_object* v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1659_; lean_object* v___y_1661_; uint8_t v_a_1662_; lean_object* v___y_1670_; uint8_t v_a_1671_; lean_object* v___y_1679_; lean_object* v___y_1680_; lean_object* v___y_1681_; uint8_t v_val_1682_; uint8_t v___y_1690_; uint8_t v___y_1691_; lean_object* v___y_1692_; uint8_t v___y_1697_; uint8_t v___y_1698_; lean_object* v___y_1699_; lean_object* v___y_1700_; uint8_t v___y_1702_; uint8_t v___y_1703_; lean_object* v___y_1704_; uint8_t v___y_1733_; uint8_t v___y_1734_; lean_object* v___y_1735_; lean_object* v___y_1736_; lean_object* v___y_1738_; uint8_t v___y_1739_; lean_object* v___y_1740_; lean_object* v___y_1741_; uint8_t v___y_1742_; lean_object* v___y_1743_; lean_object* v_a_1744_; lean_object* v___y_1788_; lean_object* v___y_1789_; lean_object* v___y_1790_; uint8_t v_val_1791_; lean_object* v___y_1799_; lean_object* v___y_1800_; lean_object* v___y_1801_; lean_object* v___y_1802_; lean_object* v_a_1803_; lean_object* v___y_1820_; lean_object* v___y_1821_; lean_object* v___y_1822_; lean_object* v___y_1823_; lean_object* v___y_1833_; lean_object* v___y_1834_; lean_object* v___y_1835_; lean_object* v___y_1836_; lean_object* v___y_1838_; lean_object* v___y_1839_; lean_object* v___y_1840_; lean_object* v___y_1841_; lean_object* v___y_1843_; lean_object* v___y_1844_; lean_object* v___y_1845_; lean_object* v_a_1846_; lean_object* v___y_1919_; lean_object* v___y_1920_; lean_object* v___y_1921_; uint8_t v_a_1922_; lean_object* v___y_1984_; lean_object* v___y_1985_; lean_object* v_a_1986_; lean_object* v___y_1997_; lean_object* v___y_1998_; lean_object* v_a_1999_; lean_object* v___y_2010_; lean_object* v___y_2011_; lean_object* v___y_2012_; lean_object* v___y_2013_; lean_object* v_val_2014_; lean_object* v___y_2022_; lean_object* v___y_2023_; uint8_t v_a_2024_; lean_object* v___y_2033_; 
if (lean_obj_tag(v_rev_x3f_1330_) == 0)
{
lean_object* v___x_2042_; 
v___x_2042_ = l_Lake_Git_upstreamBranch;
v___y_2033_ = v___x_2042_;
goto v___jp_2032_;
}
else
{
lean_object* v_val_2043_; 
v_val_2043_ = lean_ctor_get(v_rev_x3f_1330_, 0);
lean_inc(v_val_2043_);
lean_dec_ref_known(v_rev_x3f_1330_, 1);
v___y_2033_ = v_val_2043_;
goto v___jp_2032_;
}
v___jp_1332_:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1333_ = lean_box(0);
v___x_1334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1333_);
return v___x_1334_;
}
v___jp_1335_:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; 
v___x_1336_ = lean_box(0);
v___x_1337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1337_, 0, v___x_1336_);
return v___x_1337_;
}
v___jp_1338_:
{
lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1339_ = lean_box(0);
v___x_1340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1340_, 0, v___x_1339_);
return v___x_1340_;
}
v___jp_1341_:
{
lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; 
v___x_1343_ = lean_unsigned_to_nat(0u);
v___x_1344_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_1345_ = l_Lake_GitRepo_gcAuto(v_repo_1328_, v___x_1344_);
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_object* v_a_1346_; lean_object* v_a_1347_; lean_object* v___x_1348_; uint8_t v___x_1349_; 
v_a_1346_ = lean_ctor_get(v___x_1345_, 0);
lean_inc(v_a_1346_);
v_a_1347_ = lean_ctor_get(v___x_1345_, 1);
lean_inc(v_a_1347_);
lean_dec_ref_known(v___x_1345_, 2);
v___x_1348_ = lean_array_get_size(v_a_1347_);
v___x_1349_ = lean_nat_dec_lt(v___x_1343_, v___x_1348_);
if (v___x_1349_ == 0)
{
lean_object* v___x_1350_; 
lean_dec(v_a_1347_);
v___x_1350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1350_, 0, v_a_1346_);
return v___x_1350_;
}
else
{
lean_object* v___x_1351_; size_t v___x_1352_; size_t v___x_1353_; lean_object* v___x_1354_; 
v___x_1351_ = lean_box(0);
v___x_1352_ = ((size_t)0ULL);
v___x_1353_ = lean_usize_of_nat(v___x_1348_);
v___x_1354_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1347_, v___x_1352_, v___x_1353_, v___x_1351_, v___y_1342_);
lean_dec(v_a_1347_);
if (lean_obj_tag(v___x_1354_) == 0)
{
lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1361_; 
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1361_ == 0)
{
lean_object* v_unused_1362_; 
v_unused_1362_ = lean_ctor_get(v___x_1354_, 0);
lean_dec(v_unused_1362_);
v___x_1356_ = v___x_1354_;
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
else
{
lean_dec(v___x_1354_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v___x_1359_; 
if (v_isShared_1357_ == 0)
{
lean_ctor_set(v___x_1356_, 0, v_a_1346_);
v___x_1359_ = v___x_1356_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_a_1346_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
}
else
{
lean_dec(v_a_1346_);
return v___x_1354_;
}
}
}
else
{
lean_object* v_a_1363_; lean_object* v___x_1364_; uint8_t v___x_1365_; 
v_a_1363_ = lean_ctor_get(v___x_1345_, 1);
lean_inc(v_a_1363_);
lean_dec_ref_known(v___x_1345_, 2);
v___x_1364_ = lean_array_get_size(v_a_1363_);
v___x_1365_ = lean_nat_dec_lt(v___x_1343_, v___x_1364_);
if (v___x_1365_ == 0)
{
lean_object* v___x_1366_; lean_object* v___x_1367_; 
lean_dec(v_a_1363_);
v___x_1366_ = lean_box(0);
v___x_1367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1367_, 0, v___x_1366_);
return v___x_1367_;
}
else
{
lean_object* v___x_1368_; size_t v___x_1369_; size_t v___x_1370_; lean_object* v___x_1371_; 
v___x_1368_ = lean_box(0);
v___x_1369_ = ((size_t)0ULL);
v___x_1370_ = lean_usize_of_nat(v___x_1364_);
v___x_1371_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1363_, v___x_1369_, v___x_1370_, v___x_1368_, v___y_1342_);
lean_dec(v_a_1363_);
if (lean_obj_tag(v___x_1371_) == 0)
{
lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1378_; 
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1371_);
if (v_isSharedCheck_1378_ == 0)
{
lean_object* v_unused_1379_; 
v_unused_1379_ = lean_ctor_get(v___x_1371_, 0);
lean_dec(v_unused_1379_);
v___x_1373_ = v___x_1371_;
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
else
{
lean_dec(v___x_1371_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1376_; 
if (v_isShared_1374_ == 0)
{
lean_ctor_set_tag(v___x_1373_, 1);
lean_ctor_set(v___x_1373_, 0, v___x_1368_);
v___x_1376_ = v___x_1373_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v___x_1368_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
else
{
return v___x_1371_;
}
}
}
}
v___jp_1380_:
{
if (lean_obj_tag(v___y_1382_) == 0)
{
lean_dec_ref_known(v___y_1382_, 1);
v___y_1342_ = v___y_1381_;
goto v___jp_1341_;
}
else
{
lean_dec_ref(v_repo_1328_);
return v___y_1382_;
}
}
v___jp_1383_:
{
lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; 
v___x_1386_ = lean_unsigned_to_nat(0u);
v___x_1387_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1328_);
lean_inc_ref(v___y_1384_);
v___x_1388_ = l_Lake_GitRepo_pruneRemote(v___y_1384_, v_repo_1328_, v___x_1387_);
if (lean_obj_tag(v___x_1388_) == 0)
{
lean_object* v_a_1389_; lean_object* v___x_1390_; uint8_t v___x_1391_; 
v_a_1389_ = lean_ctor_get(v___x_1388_, 1);
lean_inc(v_a_1389_);
lean_dec_ref_known(v___x_1388_, 2);
v___x_1390_ = lean_array_get_size(v_a_1389_);
v___x_1391_ = lean_nat_dec_lt(v___x_1386_, v___x_1390_);
if (v___x_1391_ == 0)
{
lean_dec(v_a_1389_);
v___y_1342_ = v___y_1385_;
goto v___jp_1341_;
}
else
{
lean_object* v___x_1392_; size_t v___x_1393_; size_t v___x_1394_; lean_object* v___x_1395_; 
v___x_1392_ = lean_box(0);
v___x_1393_ = ((size_t)0ULL);
v___x_1394_ = lean_usize_of_nat(v___x_1390_);
v___x_1395_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1389_, v___x_1393_, v___x_1394_, v___x_1392_, v___y_1385_);
lean_dec(v_a_1389_);
if (lean_obj_tag(v___x_1395_) == 0)
{
lean_dec_ref_known(v___x_1395_, 1);
v___y_1342_ = v___y_1385_;
goto v___jp_1341_;
}
else
{
v___y_1381_ = v___y_1385_;
v___y_1382_ = v___x_1395_;
goto v___jp_1380_;
}
}
}
else
{
lean_object* v_a_1396_; lean_object* v___x_1397_; uint8_t v___x_1398_; 
v_a_1396_ = lean_ctor_get(v___x_1388_, 1);
lean_inc(v_a_1396_);
lean_dec_ref_known(v___x_1388_, 2);
v___x_1397_ = lean_array_get_size(v_a_1396_);
v___x_1398_ = lean_nat_dec_lt(v___x_1386_, v___x_1397_);
if (v___x_1398_ == 0)
{
lean_object* v___x_1399_; lean_object* v___x_1400_; 
lean_dec(v_a_1396_);
lean_dec_ref(v_repo_1328_);
v___x_1399_ = lean_box(0);
v___x_1400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1400_, 0, v___x_1399_);
return v___x_1400_;
}
else
{
lean_object* v___x_1401_; size_t v___x_1402_; size_t v___x_1403_; lean_object* v___x_1404_; 
v___x_1401_ = lean_box(0);
v___x_1402_ = ((size_t)0ULL);
v___x_1403_ = lean_usize_of_nat(v___x_1397_);
v___x_1404_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1396_, v___x_1402_, v___x_1403_, v___x_1401_, v___y_1385_);
lean_dec(v_a_1396_);
if (lean_obj_tag(v___x_1404_) == 0)
{
lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1411_; 
lean_dec_ref(v_repo_1328_);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1411_ == 0)
{
lean_object* v_unused_1412_; 
v_unused_1412_ = lean_ctor_get(v___x_1404_, 0);
lean_dec(v_unused_1412_);
v___x_1406_ = v___x_1404_;
v_isShared_1407_ = v_isSharedCheck_1411_;
goto v_resetjp_1405_;
}
else
{
lean_dec(v___x_1404_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1411_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v___x_1409_; 
if (v_isShared_1407_ == 0)
{
lean_ctor_set_tag(v___x_1406_, 1);
lean_ctor_set(v___x_1406_, 0, v___x_1401_);
v___x_1409_ = v___x_1406_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v___x_1401_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
}
else
{
v___y_1381_ = v___y_1385_;
v___y_1382_ = v___x_1404_;
goto v___jp_1380_;
}
}
}
}
v___jp_1413_:
{
if (v_a_1416_ == 0)
{
lean_dec_ref(v_name_1327_);
v___y_1384_ = v___y_1414_;
v___y_1385_ = v___y_1415_;
goto v___jp_1383_;
}
else
{
lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; uint8_t v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; 
v___x_1417_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff___closed__0));
v___x_1418_ = lean_string_append(v_name_1327_, v___x_1417_);
v___x_1419_ = lean_string_append(v___x_1418_, v_repo_1328_);
v___x_1420_ = 2;
v___x_1421_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1421_, 0, v___x_1419_);
lean_ctor_set_uint8(v___x_1421_, sizeof(void*)*1, v___x_1420_);
lean_inc_ref(v___y_1415_);
v___x_1422_ = lean_apply_2(v___y_1415_, v___x_1421_, lean_box(0));
v___y_1384_ = v___y_1414_;
v___y_1385_ = v___y_1415_;
goto v___jp_1383_;
}
}
v___jp_1423_:
{
if (v_a_1425_ == 0)
{
lean_dec_ref(v_repo_1328_);
lean_dec_ref(v_name_1327_);
goto v___jp_1338_;
}
else
{
lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; uint8_t v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1426_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff___closed__0));
v___x_1427_ = lean_string_append(v_name_1327_, v___x_1426_);
v___x_1428_ = lean_string_append(v___x_1427_, v_repo_1328_);
lean_dec_ref(v_repo_1328_);
v___x_1429_ = 2;
v___x_1430_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1430_, 0, v___x_1428_);
lean_ctor_set_uint8(v___x_1430_, sizeof(void*)*1, v___x_1429_);
lean_inc_ref(v___y_1424_);
v___x_1431_ = lean_apply_2(v___y_1424_, v___x_1430_, lean_box(0));
goto v___jp_1338_;
}
}
v___jp_1432_:
{
lean_object* v___x_1438_; uint8_t v___x_1439_; 
v___x_1438_ = lean_array_get_size(v___y_1433_);
v___x_1439_ = lean_nat_dec_lt(v___y_1436_, v___x_1438_);
if (v___x_1439_ == 0)
{
v___y_1414_ = v___y_1434_;
v___y_1415_ = v___y_1435_;
v_a_1416_ = v_val_1437_;
goto v___jp_1413_;
}
else
{
lean_object* v___x_1440_; size_t v___x_1441_; size_t v___x_1442_; lean_object* v___x_1443_; 
v___x_1440_ = lean_box(0);
v___x_1441_ = ((size_t)0ULL);
v___x_1442_ = lean_usize_of_nat(v___x_1438_);
v___x_1443_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_1433_, v___x_1441_, v___x_1442_, v___x_1440_, v___y_1435_);
if (lean_obj_tag(v___x_1443_) == 0)
{
lean_dec_ref_known(v___x_1443_, 1);
v___y_1414_ = v___y_1434_;
v___y_1415_ = v___y_1435_;
v_a_1416_ = v_val_1437_;
goto v___jp_1413_;
}
else
{
lean_dec_ref(v_name_1327_);
if (lean_obj_tag(v___x_1443_) == 0)
{
lean_dec_ref_known(v___x_1443_, 1);
v___y_1384_ = v___y_1434_;
v___y_1385_ = v___y_1435_;
goto v___jp_1383_;
}
else
{
lean_dec_ref(v_repo_1328_);
return v___x_1443_;
}
}
}
}
v___jp_1444_:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; uint8_t v___x_1450_; 
v___x_1448_ = lean_unsigned_to_nat(0u);
v___x_1449_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1328_);
v___x_1450_ = l_Lake_GitRepo_hasNoDiff(v_repo_1328_);
if (v___x_1450_ == 0)
{
uint8_t v___x_1451_; 
v___x_1451_ = 1;
v___y_1433_ = v___x_1449_;
v___y_1434_ = v___y_1446_;
v___y_1435_ = v___y_1447_;
v___y_1436_ = v___x_1448_;
v_val_1437_ = v___x_1451_;
goto v___jp_1432_;
}
else
{
v___y_1433_ = v___x_1449_;
v___y_1434_ = v___y_1446_;
v___y_1435_ = v___y_1447_;
v___y_1436_ = v___x_1448_;
v_val_1437_ = v___y_1445_;
goto v___jp_1432_;
}
}
v___jp_1452_:
{
if (lean_obj_tag(v___y_1456_) == 0)
{
lean_dec_ref_known(v___y_1456_, 1);
v___y_1445_ = v___y_1453_;
v___y_1446_ = v___y_1454_;
v___y_1447_ = v___y_1455_;
goto v___jp_1444_;
}
else
{
lean_dec_ref(v_repo_1328_);
lean_dec_ref(v_name_1327_);
return v___y_1456_;
}
}
v___jp_1457_:
{
lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1461_ = lean_unsigned_to_nat(0u);
v___x_1462_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1328_);
v___x_1463_ = l_Lake_GitRepo_clean(v_repo_1328_, v___x_1462_);
if (lean_obj_tag(v___x_1463_) == 0)
{
lean_object* v_a_1464_; lean_object* v___x_1465_; uint8_t v___x_1466_; 
v_a_1464_ = lean_ctor_get(v___x_1463_, 1);
lean_inc(v_a_1464_);
lean_dec_ref_known(v___x_1463_, 2);
v___x_1465_ = lean_array_get_size(v_a_1464_);
v___x_1466_ = lean_nat_dec_lt(v___x_1461_, v___x_1465_);
if (v___x_1466_ == 0)
{
lean_dec(v_a_1464_);
v___y_1445_ = v___y_1458_;
v___y_1446_ = v___y_1459_;
v___y_1447_ = v___y_1460_;
goto v___jp_1444_;
}
else
{
lean_object* v___x_1467_; size_t v___x_1468_; size_t v___x_1469_; lean_object* v___x_1470_; 
v___x_1467_ = lean_box(0);
v___x_1468_ = ((size_t)0ULL);
v___x_1469_ = lean_usize_of_nat(v___x_1465_);
v___x_1470_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1464_, v___x_1468_, v___x_1469_, v___x_1467_, v___y_1460_);
lean_dec(v_a_1464_);
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_dec_ref_known(v___x_1470_, 1);
v___y_1445_ = v___y_1458_;
v___y_1446_ = v___y_1459_;
v___y_1447_ = v___y_1460_;
goto v___jp_1444_;
}
else
{
v___y_1453_ = v___y_1458_;
v___y_1454_ = v___y_1459_;
v___y_1455_ = v___y_1460_;
v___y_1456_ = v___x_1470_;
goto v___jp_1452_;
}
}
}
else
{
lean_object* v_a_1471_; lean_object* v___x_1472_; uint8_t v___x_1473_; 
v_a_1471_ = lean_ctor_get(v___x_1463_, 1);
lean_inc(v_a_1471_);
lean_dec_ref_known(v___x_1463_, 2);
v___x_1472_ = lean_array_get_size(v_a_1471_);
v___x_1473_ = lean_nat_dec_lt(v___x_1461_, v___x_1472_);
if (v___x_1473_ == 0)
{
lean_object* v___x_1474_; lean_object* v___x_1475_; 
lean_dec(v_a_1471_);
lean_dec_ref(v_repo_1328_);
lean_dec_ref(v_name_1327_);
v___x_1474_ = lean_box(0);
v___x_1475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1475_, 0, v___x_1474_);
return v___x_1475_;
}
else
{
lean_object* v___x_1476_; size_t v___x_1477_; size_t v___x_1478_; lean_object* v___x_1479_; 
v___x_1476_ = lean_box(0);
v___x_1477_ = ((size_t)0ULL);
v___x_1478_ = lean_usize_of_nat(v___x_1472_);
v___x_1479_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1471_, v___x_1477_, v___x_1478_, v___x_1476_, v___y_1460_);
lean_dec(v_a_1471_);
if (lean_obj_tag(v___x_1479_) == 0)
{
lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1486_; 
lean_dec_ref(v_repo_1328_);
lean_dec_ref(v_name_1327_);
v_isSharedCheck_1486_ = !lean_is_exclusive(v___x_1479_);
if (v_isSharedCheck_1486_ == 0)
{
lean_object* v_unused_1487_; 
v_unused_1487_ = lean_ctor_get(v___x_1479_, 0);
lean_dec(v_unused_1487_);
v___x_1481_ = v___x_1479_;
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
else
{
lean_dec(v___x_1479_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1484_; 
if (v_isShared_1482_ == 0)
{
lean_ctor_set_tag(v___x_1481_, 1);
lean_ctor_set(v___x_1481_, 0, v___x_1476_);
v___x_1484_ = v___x_1481_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v___x_1476_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
else
{
v___y_1453_ = v___y_1458_;
v___y_1454_ = v___y_1459_;
v___y_1455_ = v___y_1460_;
v___y_1456_ = v___x_1479_;
goto v___jp_1452_;
}
}
}
}
v___jp_1488_:
{
if (lean_obj_tag(v___y_1492_) == 0)
{
lean_dec_ref_known(v___y_1492_, 1);
v___y_1458_ = v___y_1489_;
v___y_1459_ = v___y_1490_;
v___y_1460_ = v___y_1491_;
goto v___jp_1457_;
}
else
{
lean_dec_ref(v_repo_1328_);
lean_dec_ref(v_name_1327_);
return v___y_1492_;
}
}
v___jp_1493_:
{
lean_object* v___x_1498_; uint8_t v___x_1499_; 
v___x_1498_ = lean_array_get_size(v___y_1496_);
v___x_1499_ = lean_nat_dec_lt(v___y_1494_, v___x_1498_);
if (v___x_1499_ == 0)
{
v___y_1424_ = v___y_1495_;
v_a_1425_ = v_val_1497_;
goto v___jp_1423_;
}
else
{
lean_object* v___x_1500_; size_t v___x_1501_; size_t v___x_1502_; lean_object* v___x_1503_; 
v___x_1500_ = lean_box(0);
v___x_1501_ = ((size_t)0ULL);
v___x_1502_ = lean_usize_of_nat(v___x_1498_);
v___x_1503_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_1496_, v___x_1501_, v___x_1502_, v___x_1500_, v___y_1495_);
if (lean_obj_tag(v___x_1503_) == 0)
{
lean_dec_ref_known(v___x_1503_, 1);
v___y_1424_ = v___y_1495_;
v_a_1425_ = v_val_1497_;
goto v___jp_1423_;
}
else
{
lean_dec_ref(v_repo_1328_);
lean_dec_ref(v_name_1327_);
if (lean_obj_tag(v___x_1503_) == 0)
{
lean_dec_ref_known(v___x_1503_, 1);
goto v___jp_1338_;
}
else
{
return v___x_1503_;
}
}
}
}
v___jp_1504_:
{
lean_object* v___x_1510_; uint8_t v___x_1511_; 
v___x_1510_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
v___x_1511_ = l_Option_instDecidableEq___redArg(v___x_1510_, v_a_1509_, v___y_1506_);
if (v___x_1511_ == 0)
{
lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; uint8_t v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1512_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__0));
lean_inc_ref(v_name_1327_);
v___x_1513_ = lean_string_append(v_name_1327_, v___x_1512_);
v___x_1514_ = lean_string_append(v___x_1513_, v___y_1505_);
v___x_1515_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__1));
v___x_1516_ = lean_string_append(v___x_1514_, v___x_1515_);
v___x_1517_ = 1;
v___x_1518_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1518_, 0, v___x_1516_);
lean_ctor_set_uint8(v___x_1518_, sizeof(void*)*1, v___x_1517_);
lean_inc_ref(v___y_1508_);
v___x_1519_ = lean_apply_2(v___y_1508_, v___x_1518_, lean_box(0));
v___x_1520_ = lean_unsigned_to_nat(0u);
v___x_1521_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1328_);
v___x_1522_ = l_Lake_GitRepo_checkoutDetach(v___y_1505_, v_repo_1328_, v___x_1521_);
if (lean_obj_tag(v___x_1522_) == 0)
{
lean_object* v_a_1523_; lean_object* v___x_1524_; uint8_t v___x_1525_; 
v_a_1523_ = lean_ctor_get(v___x_1522_, 1);
lean_inc(v_a_1523_);
lean_dec_ref_known(v___x_1522_, 2);
v___x_1524_ = lean_array_get_size(v_a_1523_);
v___x_1525_ = lean_nat_dec_lt(v___x_1520_, v___x_1524_);
if (v___x_1525_ == 0)
{
lean_dec(v_a_1523_);
v___y_1458_ = v___x_1511_;
v___y_1459_ = v___y_1507_;
v___y_1460_ = v___y_1508_;
goto v___jp_1457_;
}
else
{
lean_object* v___x_1526_; size_t v___x_1527_; size_t v___x_1528_; lean_object* v___x_1529_; 
v___x_1526_ = lean_box(0);
v___x_1527_ = ((size_t)0ULL);
v___x_1528_ = lean_usize_of_nat(v___x_1524_);
v___x_1529_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1523_, v___x_1527_, v___x_1528_, v___x_1526_, v___y_1508_);
lean_dec(v_a_1523_);
if (lean_obj_tag(v___x_1529_) == 0)
{
lean_dec_ref_known(v___x_1529_, 1);
v___y_1458_ = v___x_1511_;
v___y_1459_ = v___y_1507_;
v___y_1460_ = v___y_1508_;
goto v___jp_1457_;
}
else
{
v___y_1489_ = v___x_1511_;
v___y_1490_ = v___y_1507_;
v___y_1491_ = v___y_1508_;
v___y_1492_ = v___x_1529_;
goto v___jp_1488_;
}
}
}
else
{
lean_object* v_a_1530_; lean_object* v___x_1531_; uint8_t v___x_1532_; 
v_a_1530_ = lean_ctor_get(v___x_1522_, 1);
lean_inc(v_a_1530_);
lean_dec_ref_known(v___x_1522_, 2);
v___x_1531_ = lean_array_get_size(v_a_1530_);
v___x_1532_ = lean_nat_dec_lt(v___x_1520_, v___x_1531_);
if (v___x_1532_ == 0)
{
lean_object* v___x_1533_; lean_object* v___x_1534_; 
lean_dec(v_a_1530_);
lean_dec_ref(v_repo_1328_);
lean_dec_ref(v_name_1327_);
v___x_1533_ = lean_box(0);
v___x_1534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1533_);
return v___x_1534_;
}
else
{
lean_object* v___x_1535_; size_t v___x_1536_; size_t v___x_1537_; lean_object* v___x_1538_; 
v___x_1535_ = lean_box(0);
v___x_1536_ = ((size_t)0ULL);
v___x_1537_ = lean_usize_of_nat(v___x_1531_);
v___x_1538_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1530_, v___x_1536_, v___x_1537_, v___x_1535_, v___y_1508_);
lean_dec(v_a_1530_);
if (lean_obj_tag(v___x_1538_) == 0)
{
lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1545_; 
lean_dec_ref(v_repo_1328_);
lean_dec_ref(v_name_1327_);
v_isSharedCheck_1545_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1545_ == 0)
{
lean_object* v_unused_1546_; 
v_unused_1546_ = lean_ctor_get(v___x_1538_, 0);
lean_dec(v_unused_1546_);
v___x_1540_ = v___x_1538_;
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
else
{
lean_dec(v___x_1538_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v___x_1543_; 
if (v_isShared_1541_ == 0)
{
lean_ctor_set_tag(v___x_1540_, 1);
lean_ctor_set(v___x_1540_, 0, v___x_1535_);
v___x_1543_ = v___x_1540_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v___x_1535_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
}
else
{
v___y_1489_ = v___x_1511_;
v___y_1490_ = v___y_1507_;
v___y_1491_ = v___y_1508_;
v___y_1492_ = v___x_1538_;
goto v___jp_1488_;
}
}
}
}
else
{
lean_object* v___x_1547_; lean_object* v___x_1548_; uint8_t v___x_1549_; 
lean_dec_ref(v___y_1505_);
v___x_1547_ = lean_unsigned_to_nat(0u);
v___x_1548_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1328_);
v___x_1549_ = l_Lake_GitRepo_hasNoDiff(v_repo_1328_);
if (v___x_1549_ == 0)
{
v___y_1494_ = v___x_1547_;
v___y_1495_ = v___y_1508_;
v___y_1496_ = v___x_1548_;
v_val_1497_ = v___x_1511_;
goto v___jp_1493_;
}
else
{
uint8_t v___x_1550_; 
v___x_1550_ = 0;
v___y_1494_ = v___x_1547_;
v___y_1495_ = v___y_1508_;
v___y_1496_ = v___x_1548_;
v_val_1497_ = v___x_1550_;
goto v___jp_1493_;
}
}
}
v___jp_1551_:
{
if (lean_obj_tag(v_a_1556_) == 1)
{
lean_object* v_val_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; uint8_t v___x_1561_; 
lean_dec_ref(v___y_1553_);
lean_dec_ref(v___y_1552_);
v_val_1557_ = lean_ctor_get(v_a_1556_, 0);
lean_inc(v_val_1557_);
v___x_1558_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_1559_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__0));
lean_inc_ref(v_repo_1328_);
v___x_1560_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_1559_, v_repo_1328_);
v___x_1561_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_1561_ == 0)
{
v___y_1505_ = v_val_1557_;
v___y_1506_ = v_a_1556_;
v___y_1507_ = v___y_1554_;
v___y_1508_ = v___y_1555_;
v_a_1509_ = v___x_1560_;
goto v___jp_1504_;
}
else
{
lean_object* v___x_1562_; size_t v___x_1563_; size_t v___x_1564_; lean_object* v___x_1565_; 
v___x_1562_ = lean_box(0);
v___x_1563_ = ((size_t)0ULL);
v___x_1564_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_1565_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_1558_, v___x_1563_, v___x_1564_, v___x_1562_, v___y_1555_);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_dec_ref_known(v___x_1565_, 1);
v___y_1505_ = v_val_1557_;
v___y_1506_ = v_a_1556_;
v___y_1507_ = v___y_1554_;
v___y_1508_ = v___y_1555_;
v_a_1509_ = v___x_1560_;
goto v___jp_1504_;
}
else
{
lean_dec(v___x_1560_);
lean_dec_ref_known(v_a_1556_, 1);
lean_dec(v_val_1557_);
lean_dec_ref(v_repo_1328_);
lean_dec_ref(v_name_1327_);
return v___x_1565_;
}
}
}
else
{
lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; uint8_t v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; 
lean_dec(v_a_1556_);
lean_dec_ref(v_repo_1328_);
v___x_1566_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__1));
v___x_1567_ = lean_string_append(v_name_1327_, v___x_1566_);
v___x_1568_ = lean_string_append(v___x_1567_, v___y_1552_);
lean_dec_ref(v___y_1552_);
v___x_1569_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__2));
v___x_1570_ = lean_string_append(v___x_1568_, v___x_1569_);
v___x_1571_ = lean_string_append(v___x_1570_, v___y_1553_);
lean_dec_ref(v___y_1553_);
v___x_1572_ = 3;
v___x_1573_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1573_, 0, v___x_1571_);
lean_ctor_set_uint8(v___x_1573_, sizeof(void*)*1, v___x_1572_);
lean_inc_ref(v___y_1555_);
v___x_1574_ = lean_apply_2(v___y_1555_, v___x_1573_, lean_box(0));
v___x_1575_ = lean_box(0);
v___x_1576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1575_);
return v___x_1576_;
}
}
v___jp_1577_:
{
lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; uint8_t v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1582_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__3));
lean_inc_ref(v_name_1327_);
v___x_1583_ = lean_string_append(v_name_1327_, v___x_1582_);
v___x_1584_ = lean_string_append(v___x_1583_, v___y_1578_);
v___x_1585_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__4));
v___x_1586_ = lean_string_append(v___x_1584_, v___x_1585_);
v___x_1587_ = lean_string_append(v___x_1586_, v___y_1579_);
v___x_1588_ = 1;
v___x_1589_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1589_, 0, v___x_1587_);
lean_ctor_set_uint8(v___x_1589_, sizeof(void*)*1, v___x_1588_);
lean_inc_ref(v___y_1581_);
v___x_1590_ = lean_apply_2(v___y_1581_, v___x_1589_, lean_box(0));
v___x_1591_ = lean_unsigned_to_nat(0u);
v___x_1592_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v___y_1578_);
lean_inc_ref(v___y_1580_);
lean_inc_ref(v_repo_1328_);
v___x_1593_ = l_Lake_GitRepo_fetchRevision_x3f(v_repo_1328_, v___y_1580_, v___y_1578_, v___x_1592_);
if (lean_obj_tag(v___x_1593_) == 0)
{
lean_object* v_a_1594_; lean_object* v_a_1595_; lean_object* v___x_1596_; uint8_t v___x_1597_; 
v_a_1594_ = lean_ctor_get(v___x_1593_, 0);
lean_inc(v_a_1594_);
v_a_1595_ = lean_ctor_get(v___x_1593_, 1);
lean_inc(v_a_1595_);
lean_dec_ref_known(v___x_1593_, 2);
v___x_1596_ = lean_array_get_size(v_a_1595_);
v___x_1597_ = lean_nat_dec_lt(v___x_1591_, v___x_1596_);
if (v___x_1597_ == 0)
{
lean_dec(v_a_1595_);
v___y_1552_ = v___y_1578_;
v___y_1553_ = v___y_1579_;
v___y_1554_ = v___y_1580_;
v___y_1555_ = v___y_1581_;
v_a_1556_ = v_a_1594_;
goto v___jp_1551_;
}
else
{
lean_object* v___x_1598_; size_t v___x_1599_; size_t v___x_1600_; lean_object* v___x_1601_; 
v___x_1598_ = lean_box(0);
v___x_1599_ = ((size_t)0ULL);
v___x_1600_ = lean_usize_of_nat(v___x_1596_);
v___x_1601_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1595_, v___x_1599_, v___x_1600_, v___x_1598_, v___y_1581_);
lean_dec(v_a_1595_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_dec_ref_known(v___x_1601_, 1);
v___y_1552_ = v___y_1578_;
v___y_1553_ = v___y_1579_;
v___y_1554_ = v___y_1580_;
v___y_1555_ = v___y_1581_;
v_a_1556_ = v_a_1594_;
goto v___jp_1551_;
}
else
{
lean_dec(v_a_1594_);
lean_dec_ref(v___y_1579_);
lean_dec_ref(v___y_1578_);
lean_dec_ref(v_repo_1328_);
lean_dec_ref(v_name_1327_);
return v___x_1601_;
}
}
}
else
{
lean_object* v_a_1602_; lean_object* v___x_1603_; uint8_t v___x_1604_; 
lean_dec_ref(v___y_1579_);
lean_dec_ref(v___y_1578_);
lean_dec_ref(v_repo_1328_);
lean_dec_ref(v_name_1327_);
v_a_1602_ = lean_ctor_get(v___x_1593_, 1);
lean_inc(v_a_1602_);
lean_dec_ref_known(v___x_1593_, 2);
v___x_1603_ = lean_array_get_size(v_a_1602_);
v___x_1604_ = lean_nat_dec_lt(v___x_1591_, v___x_1603_);
if (v___x_1604_ == 0)
{
lean_object* v___x_1605_; lean_object* v___x_1606_; 
lean_dec(v_a_1602_);
v___x_1605_ = lean_box(0);
v___x_1606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1606_, 0, v___x_1605_);
return v___x_1606_;
}
else
{
lean_object* v___x_1607_; size_t v___x_1608_; size_t v___x_1609_; lean_object* v___x_1610_; 
v___x_1607_ = lean_box(0);
v___x_1608_ = ((size_t)0ULL);
v___x_1609_ = lean_usize_of_nat(v___x_1603_);
v___x_1610_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1602_, v___x_1608_, v___x_1609_, v___x_1607_, v___y_1581_);
lean_dec(v_a_1602_);
if (lean_obj_tag(v___x_1610_) == 0)
{
lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1617_; 
v_isSharedCheck_1617_ = !lean_is_exclusive(v___x_1610_);
if (v_isSharedCheck_1617_ == 0)
{
lean_object* v_unused_1618_; 
v_unused_1618_ = lean_ctor_get(v___x_1610_, 0);
lean_dec(v_unused_1618_);
v___x_1612_ = v___x_1610_;
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
else
{
lean_dec(v___x_1610_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v___x_1615_; 
if (v_isShared_1613_ == 0)
{
lean_ctor_set_tag(v___x_1612_, 1);
lean_ctor_set(v___x_1612_, 0, v___x_1607_);
v___x_1615_ = v___x_1612_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v___x_1607_);
v___x_1615_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
return v___x_1615_;
}
}
}
else
{
return v___x_1610_;
}
}
}
}
v___jp_1619_:
{
if (lean_obj_tag(v___y_1623_) == 0)
{
lean_dec_ref_known(v___y_1623_, 1);
v___y_1578_ = v___y_1620_;
v___y_1579_ = v___y_1621_;
v___y_1580_ = v___y_1622_;
v___y_1581_ = v_a_1326_;
goto v___jp_1577_;
}
else
{
lean_dec_ref(v___y_1621_);
lean_dec_ref(v___y_1620_);
lean_dec_ref(v_repo_1328_);
lean_dec_ref(v_name_1327_);
return v___y_1623_;
}
}
v___jp_1624_:
{
lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1628_ = lean_unsigned_to_nat(0u);
v___x_1629_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1328_);
lean_inc_ref(v___y_1626_);
lean_inc_ref(v___y_1627_);
v___x_1630_ = l_Lake_GitRepo_addRemote(v___y_1627_, v___y_1626_, v_repo_1328_, v___x_1629_);
if (lean_obj_tag(v___x_1630_) == 0)
{
lean_object* v_a_1631_; lean_object* v___x_1632_; uint8_t v___x_1633_; 
v_a_1631_ = lean_ctor_get(v___x_1630_, 1);
lean_inc(v_a_1631_);
lean_dec_ref_known(v___x_1630_, 2);
v___x_1632_ = lean_array_get_size(v_a_1631_);
v___x_1633_ = lean_nat_dec_lt(v___x_1628_, v___x_1632_);
if (v___x_1633_ == 0)
{
lean_dec(v_a_1631_);
v___y_1578_ = v___y_1625_;
v___y_1579_ = v___y_1626_;
v___y_1580_ = v___y_1627_;
v___y_1581_ = v_a_1326_;
goto v___jp_1577_;
}
else
{
lean_object* v___x_1634_; size_t v___x_1635_; size_t v___x_1636_; lean_object* v___x_1637_; 
v___x_1634_ = lean_box(0);
v___x_1635_ = ((size_t)0ULL);
v___x_1636_ = lean_usize_of_nat(v___x_1632_);
v___x_1637_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1631_, v___x_1635_, v___x_1636_, v___x_1634_, v_a_1326_);
lean_dec(v_a_1631_);
if (lean_obj_tag(v___x_1637_) == 0)
{
lean_dec_ref_known(v___x_1637_, 1);
v___y_1578_ = v___y_1625_;
v___y_1579_ = v___y_1626_;
v___y_1580_ = v___y_1627_;
v___y_1581_ = v_a_1326_;
goto v___jp_1577_;
}
else
{
v___y_1620_ = v___y_1625_;
v___y_1621_ = v___y_1626_;
v___y_1622_ = v___y_1627_;
v___y_1623_ = v___x_1637_;
goto v___jp_1619_;
}
}
}
else
{
lean_object* v_a_1638_; lean_object* v___x_1639_; uint8_t v___x_1640_; 
v_a_1638_ = lean_ctor_get(v___x_1630_, 1);
lean_inc(v_a_1638_);
lean_dec_ref_known(v___x_1630_, 2);
v___x_1639_ = lean_array_get_size(v_a_1638_);
v___x_1640_ = lean_nat_dec_lt(v___x_1628_, v___x_1639_);
if (v___x_1640_ == 0)
{
lean_object* v___x_1641_; lean_object* v___x_1642_; 
lean_dec(v_a_1638_);
lean_dec_ref(v___y_1626_);
lean_dec_ref(v___y_1625_);
lean_dec_ref(v_repo_1328_);
lean_dec_ref(v_name_1327_);
v___x_1641_ = lean_box(0);
v___x_1642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1642_, 0, v___x_1641_);
return v___x_1642_;
}
else
{
lean_object* v___x_1643_; size_t v___x_1644_; size_t v___x_1645_; lean_object* v___x_1646_; 
v___x_1643_ = lean_box(0);
v___x_1644_ = ((size_t)0ULL);
v___x_1645_ = lean_usize_of_nat(v___x_1639_);
v___x_1646_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1638_, v___x_1644_, v___x_1645_, v___x_1643_, v_a_1326_);
lean_dec(v_a_1638_);
if (lean_obj_tag(v___x_1646_) == 0)
{
lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1653_; 
lean_dec_ref(v___y_1626_);
lean_dec_ref(v___y_1625_);
lean_dec_ref(v_repo_1328_);
lean_dec_ref(v_name_1327_);
v_isSharedCheck_1653_ = !lean_is_exclusive(v___x_1646_);
if (v_isSharedCheck_1653_ == 0)
{
lean_object* v_unused_1654_; 
v_unused_1654_ = lean_ctor_get(v___x_1646_, 0);
lean_dec(v_unused_1654_);
v___x_1648_ = v___x_1646_;
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
else
{
lean_dec(v___x_1646_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1651_; 
if (v_isShared_1649_ == 0)
{
lean_ctor_set_tag(v___x_1648_, 1);
lean_ctor_set(v___x_1648_, 0, v___x_1643_);
v___x_1651_ = v___x_1648_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v___x_1643_);
v___x_1651_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
return v___x_1651_;
}
}
}
else
{
v___y_1620_ = v___y_1625_;
v___y_1621_ = v___y_1626_;
v___y_1622_ = v___y_1627_;
v___y_1623_ = v___x_1646_;
goto v___jp_1619_;
}
}
}
}
v___jp_1655_:
{
if (lean_obj_tag(v___y_1659_) == 0)
{
lean_dec_ref_known(v___y_1659_, 1);
v___y_1625_ = v___y_1656_;
v___y_1626_ = v___y_1657_;
v___y_1627_ = v___y_1658_;
goto v___jp_1624_;
}
else
{
lean_dec_ref(v___y_1657_);
lean_dec_ref(v___y_1656_);
lean_dec_ref(v_repo_1328_);
lean_dec_ref(v_name_1327_);
return v___y_1659_;
}
}
v___jp_1660_:
{
if (v_a_1662_ == 0)
{
lean_dec_ref(v_repo_1328_);
lean_dec_ref(v_name_1327_);
goto v___jp_1335_;
}
else
{
lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; uint8_t v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; 
v___x_1663_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff___closed__0));
v___x_1664_ = lean_string_append(v_name_1327_, v___x_1663_);
v___x_1665_ = lean_string_append(v___x_1664_, v_repo_1328_);
lean_dec_ref(v_repo_1328_);
v___x_1666_ = 2;
v___x_1667_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1667_, 0, v___x_1665_);
lean_ctor_set_uint8(v___x_1667_, sizeof(void*)*1, v___x_1666_);
lean_inc_ref(v___y_1661_);
v___x_1668_ = lean_apply_2(v___y_1661_, v___x_1667_, lean_box(0));
goto v___jp_1335_;
}
}
v___jp_1669_:
{
if (v_a_1671_ == 0)
{
lean_dec_ref(v_repo_1328_);
lean_dec_ref(v_name_1327_);
goto v___jp_1332_;
}
else
{
lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; uint8_t v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1672_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff___closed__0));
v___x_1673_ = lean_string_append(v_name_1327_, v___x_1672_);
v___x_1674_ = lean_string_append(v___x_1673_, v_repo_1328_);
lean_dec_ref(v_repo_1328_);
v___x_1675_ = 2;
v___x_1676_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1676_, 0, v___x_1674_);
lean_ctor_set_uint8(v___x_1676_, sizeof(void*)*1, v___x_1675_);
lean_inc_ref(v___y_1670_);
v___x_1677_ = lean_apply_2(v___y_1670_, v___x_1676_, lean_box(0));
goto v___jp_1332_;
}
}
v___jp_1678_:
{
lean_object* v___x_1683_; uint8_t v___x_1684_; 
v___x_1683_ = lean_array_get_size(v___y_1679_);
v___x_1684_ = lean_nat_dec_lt(v___y_1680_, v___x_1683_);
if (v___x_1684_ == 0)
{
v___y_1661_ = v___y_1681_;
v_a_1662_ = v_val_1682_;
goto v___jp_1660_;
}
else
{
lean_object* v___x_1685_; size_t v___x_1686_; size_t v___x_1687_; lean_object* v___x_1688_; 
v___x_1685_ = lean_box(0);
v___x_1686_ = ((size_t)0ULL);
v___x_1687_ = lean_usize_of_nat(v___x_1683_);
v___x_1688_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_1679_, v___x_1686_, v___x_1687_, v___x_1685_, v___y_1681_);
if (lean_obj_tag(v___x_1688_) == 0)
{
lean_dec_ref_known(v___x_1688_, 1);
v___y_1661_ = v___y_1681_;
v_a_1662_ = v_val_1682_;
goto v___jp_1660_;
}
else
{
lean_dec_ref(v_repo_1328_);
lean_dec_ref(v_name_1327_);
if (lean_obj_tag(v___x_1688_) == 0)
{
lean_dec_ref_known(v___x_1688_, 1);
goto v___jp_1335_;
}
else
{
return v___x_1688_;
}
}
}
}
v___jp_1689_:
{
lean_object* v___x_1693_; lean_object* v___x_1694_; uint8_t v___x_1695_; 
v___x_1693_ = lean_unsigned_to_nat(0u);
v___x_1694_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1328_);
v___x_1695_ = l_Lake_GitRepo_hasNoDiff(v_repo_1328_);
if (v___x_1695_ == 0)
{
v___y_1679_ = v___x_1694_;
v___y_1680_ = v___x_1693_;
v___y_1681_ = v___y_1692_;
v_val_1682_ = v___y_1691_;
goto v___jp_1678_;
}
else
{
v___y_1679_ = v___x_1694_;
v___y_1680_ = v___x_1693_;
v___y_1681_ = v___y_1692_;
v_val_1682_ = v___y_1690_;
goto v___jp_1678_;
}
}
v___jp_1696_:
{
if (lean_obj_tag(v___y_1700_) == 0)
{
lean_dec_ref_known(v___y_1700_, 1);
v___y_1690_ = v___y_1697_;
v___y_1691_ = v___y_1698_;
v___y_1692_ = v___y_1699_;
goto v___jp_1689_;
}
else
{
lean_dec_ref(v_repo_1328_);
lean_dec_ref(v_name_1327_);
return v___y_1700_;
}
}
v___jp_1701_:
{
lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; 
v___x_1705_ = lean_unsigned_to_nat(0u);
v___x_1706_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1328_);
v___x_1707_ = l_Lake_GitRepo_clean(v_repo_1328_, v___x_1706_);
if (lean_obj_tag(v___x_1707_) == 0)
{
lean_object* v_a_1708_; lean_object* v___x_1709_; uint8_t v___x_1710_; 
v_a_1708_ = lean_ctor_get(v___x_1707_, 1);
lean_inc(v_a_1708_);
lean_dec_ref_known(v___x_1707_, 2);
v___x_1709_ = lean_array_get_size(v_a_1708_);
v___x_1710_ = lean_nat_dec_lt(v___x_1705_, v___x_1709_);
if (v___x_1710_ == 0)
{
lean_dec(v_a_1708_);
v___y_1690_ = v___y_1702_;
v___y_1691_ = v___y_1703_;
v___y_1692_ = v___y_1704_;
goto v___jp_1689_;
}
else
{
lean_object* v___x_1711_; size_t v___x_1712_; size_t v___x_1713_; lean_object* v___x_1714_; 
v___x_1711_ = lean_box(0);
v___x_1712_ = ((size_t)0ULL);
v___x_1713_ = lean_usize_of_nat(v___x_1709_);
v___x_1714_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1708_, v___x_1712_, v___x_1713_, v___x_1711_, v___y_1704_);
lean_dec(v_a_1708_);
if (lean_obj_tag(v___x_1714_) == 0)
{
lean_dec_ref_known(v___x_1714_, 1);
v___y_1690_ = v___y_1702_;
v___y_1691_ = v___y_1703_;
v___y_1692_ = v___y_1704_;
goto v___jp_1689_;
}
else
{
v___y_1697_ = v___y_1702_;
v___y_1698_ = v___y_1703_;
v___y_1699_ = v___y_1704_;
v___y_1700_ = v___x_1714_;
goto v___jp_1696_;
}
}
}
else
{
lean_object* v_a_1715_; lean_object* v___x_1716_; uint8_t v___x_1717_; 
v_a_1715_ = lean_ctor_get(v___x_1707_, 1);
lean_inc(v_a_1715_);
lean_dec_ref_known(v___x_1707_, 2);
v___x_1716_ = lean_array_get_size(v_a_1715_);
v___x_1717_ = lean_nat_dec_lt(v___x_1705_, v___x_1716_);
if (v___x_1717_ == 0)
{
lean_object* v___x_1718_; lean_object* v___x_1719_; 
lean_dec(v_a_1715_);
lean_dec_ref(v_repo_1328_);
lean_dec_ref(v_name_1327_);
v___x_1718_ = lean_box(0);
v___x_1719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1719_, 0, v___x_1718_);
return v___x_1719_;
}
else
{
lean_object* v___x_1720_; size_t v___x_1721_; size_t v___x_1722_; lean_object* v___x_1723_; 
v___x_1720_ = lean_box(0);
v___x_1721_ = ((size_t)0ULL);
v___x_1722_ = lean_usize_of_nat(v___x_1716_);
v___x_1723_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1715_, v___x_1721_, v___x_1722_, v___x_1720_, v___y_1704_);
lean_dec(v_a_1715_);
if (lean_obj_tag(v___x_1723_) == 0)
{
lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1730_; 
lean_dec_ref(v_repo_1328_);
lean_dec_ref(v_name_1327_);
v_isSharedCheck_1730_ = !lean_is_exclusive(v___x_1723_);
if (v_isSharedCheck_1730_ == 0)
{
lean_object* v_unused_1731_; 
v_unused_1731_ = lean_ctor_get(v___x_1723_, 0);
lean_dec(v_unused_1731_);
v___x_1725_ = v___x_1723_;
v_isShared_1726_ = v_isSharedCheck_1730_;
goto v_resetjp_1724_;
}
else
{
lean_dec(v___x_1723_);
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
lean_ctor_set(v___x_1725_, 0, v___x_1720_);
v___x_1728_ = v___x_1725_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v___x_1720_);
v___x_1728_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
return v___x_1728_;
}
}
}
else
{
v___y_1697_ = v___y_1702_;
v___y_1698_ = v___y_1703_;
v___y_1699_ = v___y_1704_;
v___y_1700_ = v___x_1723_;
goto v___jp_1696_;
}
}
}
}
v___jp_1732_:
{
if (lean_obj_tag(v___y_1736_) == 0)
{
lean_dec_ref_known(v___y_1736_, 1);
v___y_1702_ = v___y_1733_;
v___y_1703_ = v___y_1734_;
v___y_1704_ = v___y_1735_;
goto v___jp_1701_;
}
else
{
lean_dec_ref(v_repo_1328_);
lean_dec_ref(v_name_1327_);
return v___y_1736_;
}
}
v___jp_1737_:
{
if (lean_obj_tag(v_a_1744_) == 0)
{
v___y_1578_ = v___y_1738_;
v___y_1579_ = v___y_1740_;
v___y_1580_ = v___y_1741_;
v___y_1581_ = v___y_1743_;
goto v___jp_1577_;
}
else
{
lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1785_; 
v_isSharedCheck_1785_ = !lean_is_exclusive(v_a_1744_);
if (v_isSharedCheck_1785_ == 0)
{
lean_object* v_unused_1786_; 
v_unused_1786_ = lean_ctor_get(v_a_1744_, 0);
lean_dec(v_unused_1786_);
v___x_1746_ = v_a_1744_;
v_isShared_1747_ = v_isSharedCheck_1785_;
goto v_resetjp_1745_;
}
else
{
lean_dec(v_a_1744_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1785_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
if (v___y_1742_ == 0)
{
lean_del_object(v___x_1746_);
v___y_1578_ = v___y_1738_;
v___y_1579_ = v___y_1740_;
v___y_1580_ = v___y_1741_;
v___y_1581_ = v___y_1743_;
goto v___jp_1577_;
}
else
{
lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; uint8_t v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; 
lean_dec_ref(v___y_1740_);
v___x_1748_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__0));
lean_inc_ref(v_name_1327_);
v___x_1749_ = lean_string_append(v_name_1327_, v___x_1748_);
v___x_1750_ = lean_string_append(v___x_1749_, v___y_1738_);
v___x_1751_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__1));
v___x_1752_ = lean_string_append(v___x_1750_, v___x_1751_);
v___x_1753_ = 1;
v___x_1754_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1754_, 0, v___x_1752_);
lean_ctor_set_uint8(v___x_1754_, sizeof(void*)*1, v___x_1753_);
lean_inc_ref(v___y_1743_);
v___x_1755_ = lean_apply_2(v___y_1743_, v___x_1754_, lean_box(0));
v___x_1756_ = lean_unsigned_to_nat(0u);
v___x_1757_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1328_);
v___x_1758_ = l_Lake_GitRepo_checkoutDetach(v___y_1738_, v_repo_1328_, v___x_1757_);
if (lean_obj_tag(v___x_1758_) == 0)
{
lean_object* v_a_1759_; lean_object* v___x_1760_; uint8_t v___x_1761_; 
lean_del_object(v___x_1746_);
v_a_1759_ = lean_ctor_get(v___x_1758_, 1);
lean_inc(v_a_1759_);
lean_dec_ref_known(v___x_1758_, 2);
v___x_1760_ = lean_array_get_size(v_a_1759_);
v___x_1761_ = lean_nat_dec_lt(v___x_1756_, v___x_1760_);
if (v___x_1761_ == 0)
{
lean_dec(v_a_1759_);
v___y_1702_ = v___y_1739_;
v___y_1703_ = v___y_1742_;
v___y_1704_ = v___y_1743_;
goto v___jp_1701_;
}
else
{
lean_object* v___x_1762_; size_t v___x_1763_; size_t v___x_1764_; lean_object* v___x_1765_; 
v___x_1762_ = lean_box(0);
v___x_1763_ = ((size_t)0ULL);
v___x_1764_ = lean_usize_of_nat(v___x_1760_);
v___x_1765_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1759_, v___x_1763_, v___x_1764_, v___x_1762_, v___y_1743_);
lean_dec(v_a_1759_);
if (lean_obj_tag(v___x_1765_) == 0)
{
lean_dec_ref_known(v___x_1765_, 1);
v___y_1702_ = v___y_1739_;
v___y_1703_ = v___y_1742_;
v___y_1704_ = v___y_1743_;
goto v___jp_1701_;
}
else
{
v___y_1733_ = v___y_1739_;
v___y_1734_ = v___y_1742_;
v___y_1735_ = v___y_1743_;
v___y_1736_ = v___x_1765_;
goto v___jp_1732_;
}
}
}
else
{
lean_object* v_a_1766_; lean_object* v___x_1767_; uint8_t v___x_1768_; 
v_a_1766_ = lean_ctor_get(v___x_1758_, 1);
lean_inc(v_a_1766_);
lean_dec_ref_known(v___x_1758_, 2);
v___x_1767_ = lean_array_get_size(v_a_1766_);
v___x_1768_ = lean_nat_dec_lt(v___x_1756_, v___x_1767_);
if (v___x_1768_ == 0)
{
lean_object* v___x_1769_; lean_object* v___x_1771_; 
lean_dec(v_a_1766_);
lean_dec_ref(v_repo_1328_);
lean_dec_ref(v_name_1327_);
v___x_1769_ = lean_box(0);
if (v_isShared_1747_ == 0)
{
lean_ctor_set(v___x_1746_, 0, v___x_1769_);
v___x_1771_ = v___x_1746_;
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
else
{
lean_object* v___x_1773_; size_t v___x_1774_; size_t v___x_1775_; lean_object* v___x_1776_; 
lean_del_object(v___x_1746_);
v___x_1773_ = lean_box(0);
v___x_1774_ = ((size_t)0ULL);
v___x_1775_ = lean_usize_of_nat(v___x_1767_);
v___x_1776_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1766_, v___x_1774_, v___x_1775_, v___x_1773_, v___y_1743_);
lean_dec(v_a_1766_);
if (lean_obj_tag(v___x_1776_) == 0)
{
lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1783_; 
lean_dec_ref(v_repo_1328_);
lean_dec_ref(v_name_1327_);
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1783_ == 0)
{
lean_object* v_unused_1784_; 
v_unused_1784_ = lean_ctor_get(v___x_1776_, 0);
lean_dec(v_unused_1784_);
v___x_1778_ = v___x_1776_;
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
else
{
lean_dec(v___x_1776_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v___x_1781_; 
if (v_isShared_1779_ == 0)
{
lean_ctor_set_tag(v___x_1778_, 1);
lean_ctor_set(v___x_1778_, 0, v___x_1773_);
v___x_1781_ = v___x_1778_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v___x_1773_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
return v___x_1781_;
}
}
}
else
{
v___y_1733_ = v___y_1739_;
v___y_1734_ = v___y_1742_;
v___y_1735_ = v___y_1743_;
v___y_1736_ = v___x_1776_;
goto v___jp_1732_;
}
}
}
}
}
}
}
v___jp_1787_:
{
lean_object* v___x_1792_; uint8_t v___x_1793_; 
v___x_1792_ = lean_array_get_size(v___y_1788_);
v___x_1793_ = lean_nat_dec_lt(v___y_1789_, v___x_1792_);
if (v___x_1793_ == 0)
{
v___y_1670_ = v___y_1790_;
v_a_1671_ = v_val_1791_;
goto v___jp_1669_;
}
else
{
lean_object* v___x_1794_; size_t v___x_1795_; size_t v___x_1796_; lean_object* v___x_1797_; 
v___x_1794_ = lean_box(0);
v___x_1795_ = ((size_t)0ULL);
v___x_1796_ = lean_usize_of_nat(v___x_1792_);
v___x_1797_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_1788_, v___x_1795_, v___x_1796_, v___x_1794_, v___y_1790_);
if (lean_obj_tag(v___x_1797_) == 0)
{
lean_dec_ref_known(v___x_1797_, 1);
v___y_1670_ = v___y_1790_;
v_a_1671_ = v_val_1791_;
goto v___jp_1669_;
}
else
{
lean_dec_ref(v_repo_1328_);
lean_dec_ref(v_name_1327_);
if (lean_obj_tag(v___x_1797_) == 0)
{
lean_dec_ref_known(v___x_1797_, 1);
goto v___jp_1332_;
}
else
{
return v___x_1797_;
}
}
}
}
v___jp_1798_:
{
lean_object* v___x_1804_; lean_object* v___x_1805_; uint8_t v___x_1806_; 
v___x_1804_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
lean_inc_ref(v___y_1799_);
v___x_1805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1805_, 0, v___y_1799_);
v___x_1806_ = l_Option_instDecidableEq___redArg(v___x_1804_, v_a_1803_, v___x_1805_);
if (v___x_1806_ == 0)
{
uint8_t v___x_1807_; 
v___x_1807_ = l_Lake_GitRev_isFullSha1(v___y_1799_);
if (v___x_1807_ == 0)
{
v___y_1578_ = v___y_1799_;
v___y_1579_ = v___y_1800_;
v___y_1580_ = v___y_1801_;
v___y_1581_ = v___y_1802_;
goto v___jp_1577_;
}
else
{
lean_object* v___x_1808_; lean_object* v___x_1809_; uint8_t v___x_1810_; 
v___x_1808_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1328_);
lean_inc_ref(v___y_1799_);
v___x_1809_ = l_Lake_GitRepo_findCommit_x3f(v___y_1799_, v_repo_1328_);
v___x_1810_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_1810_ == 0)
{
v___y_1738_ = v___y_1799_;
v___y_1739_ = v___x_1806_;
v___y_1740_ = v___y_1800_;
v___y_1741_ = v___y_1801_;
v___y_1742_ = v___x_1807_;
v___y_1743_ = v___y_1802_;
v_a_1744_ = v___x_1809_;
goto v___jp_1737_;
}
else
{
lean_object* v___x_1811_; size_t v___x_1812_; size_t v___x_1813_; lean_object* v___x_1814_; 
v___x_1811_ = lean_box(0);
v___x_1812_ = ((size_t)0ULL);
v___x_1813_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_1814_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_1808_, v___x_1812_, v___x_1813_, v___x_1811_, v___y_1802_);
if (lean_obj_tag(v___x_1814_) == 0)
{
lean_dec_ref_known(v___x_1814_, 1);
v___y_1738_ = v___y_1799_;
v___y_1739_ = v___x_1806_;
v___y_1740_ = v___y_1800_;
v___y_1741_ = v___y_1801_;
v___y_1742_ = v___x_1807_;
v___y_1743_ = v___y_1802_;
v_a_1744_ = v___x_1809_;
goto v___jp_1737_;
}
else
{
lean_dec(v___x_1809_);
lean_dec_ref(v___y_1800_);
lean_dec_ref(v___y_1799_);
lean_dec_ref(v_repo_1328_);
lean_dec_ref(v_name_1327_);
return v___x_1814_;
}
}
}
}
else
{
lean_object* v___x_1815_; lean_object* v___x_1816_; uint8_t v___x_1817_; 
lean_dec_ref(v___y_1800_);
lean_dec_ref(v___y_1799_);
v___x_1815_ = lean_unsigned_to_nat(0u);
v___x_1816_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1328_);
v___x_1817_ = l_Lake_GitRepo_hasNoDiff(v_repo_1328_);
if (v___x_1817_ == 0)
{
v___y_1788_ = v___x_1816_;
v___y_1789_ = v___x_1815_;
v___y_1790_ = v___y_1802_;
v_val_1791_ = v___x_1806_;
goto v___jp_1787_;
}
else
{
uint8_t v___x_1818_; 
v___x_1818_ = 0;
v___y_1788_ = v___x_1816_;
v___y_1789_ = v___x_1815_;
v___y_1790_ = v___y_1802_;
v_val_1791_ = v___x_1818_;
goto v___jp_1787_;
}
}
}
v___jp_1819_:
{
lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; uint8_t v___x_1827_; 
v___x_1824_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_1825_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__0));
lean_inc_ref(v_repo_1328_);
v___x_1826_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_1825_, v_repo_1328_);
v___x_1827_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_1827_ == 0)
{
v___y_1799_ = v___y_1820_;
v___y_1800_ = v___y_1821_;
v___y_1801_ = v___y_1822_;
v___y_1802_ = v___y_1823_;
v_a_1803_ = v___x_1826_;
goto v___jp_1798_;
}
else
{
lean_object* v___x_1828_; size_t v___x_1829_; size_t v___x_1830_; lean_object* v___x_1831_; 
v___x_1828_ = lean_box(0);
v___x_1829_ = ((size_t)0ULL);
v___x_1830_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_1831_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_1824_, v___x_1829_, v___x_1830_, v___x_1828_, v___y_1823_);
if (lean_obj_tag(v___x_1831_) == 0)
{
lean_dec_ref_known(v___x_1831_, 1);
v___y_1799_ = v___y_1820_;
v___y_1800_ = v___y_1821_;
v___y_1801_ = v___y_1822_;
v___y_1802_ = v___y_1823_;
v_a_1803_ = v___x_1826_;
goto v___jp_1798_;
}
else
{
lean_dec(v___x_1826_);
lean_dec_ref(v___y_1821_);
lean_dec_ref(v___y_1820_);
lean_dec_ref(v_repo_1328_);
lean_dec_ref(v_name_1327_);
return v___x_1831_;
}
}
}
v___jp_1832_:
{
if (lean_obj_tag(v___y_1836_) == 0)
{
lean_dec_ref_known(v___y_1836_, 1);
v___y_1820_ = v___y_1833_;
v___y_1821_ = v___y_1834_;
v___y_1822_ = v___y_1835_;
v___y_1823_ = v_a_1326_;
goto v___jp_1819_;
}
else
{
lean_dec_ref(v___y_1834_);
lean_dec_ref(v___y_1833_);
lean_dec_ref(v_repo_1328_);
lean_dec_ref(v_name_1327_);
return v___y_1836_;
}
}
v___jp_1837_:
{
if (lean_obj_tag(v___y_1841_) == 0)
{
lean_dec_ref_known(v___y_1841_, 1);
v___y_1820_ = v___y_1838_;
v___y_1821_ = v___y_1839_;
v___y_1822_ = v___y_1840_;
v___y_1823_ = v_a_1326_;
goto v___jp_1819_;
}
else
{
lean_dec_ref(v___y_1839_);
lean_dec_ref(v___y_1838_);
lean_dec_ref(v_repo_1328_);
lean_dec_ref(v_name_1327_);
return v___y_1841_;
}
}
v___jp_1842_:
{
if (lean_obj_tag(v_a_1846_) == 1)
{
lean_object* v_val_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1890_; 
v_val_1847_ = lean_ctor_get(v_a_1846_, 0);
v_isSharedCheck_1890_ = !lean_is_exclusive(v_a_1846_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1849_ = v_a_1846_;
v_isShared_1850_ = v_isSharedCheck_1890_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_val_1847_);
lean_dec(v_a_1846_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1890_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
uint8_t v___x_1851_; 
v___x_1851_ = lean_string_dec_eq(v_val_1847_, v___y_1844_);
if (v___x_1851_ == 0)
{
lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; uint8_t v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; 
v___x_1852_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__5));
lean_inc_ref(v_name_1327_);
v___x_1853_ = lean_string_append(v_name_1327_, v___x_1852_);
v___x_1854_ = lean_string_append(v___x_1853_, v_val_1847_);
lean_dec(v_val_1847_);
v___x_1855_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__6));
v___x_1856_ = lean_string_append(v___x_1854_, v___x_1855_);
v___x_1857_ = lean_string_append(v___x_1856_, v___y_1844_);
v___x_1858_ = 1;
v___x_1859_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1859_, 0, v___x_1857_);
lean_ctor_set_uint8(v___x_1859_, sizeof(void*)*1, v___x_1858_);
lean_inc_ref(v_a_1326_);
v___x_1860_ = lean_apply_2(v_a_1326_, v___x_1859_, lean_box(0));
v___x_1861_ = lean_unsigned_to_nat(0u);
v___x_1862_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1328_);
lean_inc_ref(v___y_1844_);
lean_inc_ref(v___y_1845_);
v___x_1863_ = l_Lake_GitRepo_setRemoteUrl(v___y_1845_, v___y_1844_, v_repo_1328_, v___x_1862_);
if (lean_obj_tag(v___x_1863_) == 0)
{
lean_object* v_a_1864_; lean_object* v___x_1865_; uint8_t v___x_1866_; 
lean_del_object(v___x_1849_);
v_a_1864_ = lean_ctor_get(v___x_1863_, 1);
lean_inc(v_a_1864_);
lean_dec_ref_known(v___x_1863_, 2);
v___x_1865_ = lean_array_get_size(v_a_1864_);
v___x_1866_ = lean_nat_dec_lt(v___x_1861_, v___x_1865_);
if (v___x_1866_ == 0)
{
lean_dec(v_a_1864_);
v___y_1820_ = v___y_1843_;
v___y_1821_ = v___y_1844_;
v___y_1822_ = v___y_1845_;
v___y_1823_ = v_a_1326_;
goto v___jp_1819_;
}
else
{
lean_object* v___x_1867_; size_t v___x_1868_; size_t v___x_1869_; lean_object* v___x_1870_; 
v___x_1867_ = lean_box(0);
v___x_1868_ = ((size_t)0ULL);
v___x_1869_ = lean_usize_of_nat(v___x_1865_);
v___x_1870_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1864_, v___x_1868_, v___x_1869_, v___x_1867_, v_a_1326_);
lean_dec(v_a_1864_);
if (lean_obj_tag(v___x_1870_) == 0)
{
lean_dec_ref_known(v___x_1870_, 1);
v___y_1820_ = v___y_1843_;
v___y_1821_ = v___y_1844_;
v___y_1822_ = v___y_1845_;
v___y_1823_ = v_a_1326_;
goto v___jp_1819_;
}
else
{
v___y_1838_ = v___y_1843_;
v___y_1839_ = v___y_1844_;
v___y_1840_ = v___y_1845_;
v___y_1841_ = v___x_1870_;
goto v___jp_1837_;
}
}
}
else
{
lean_object* v_a_1871_; lean_object* v___x_1872_; uint8_t v___x_1873_; 
v_a_1871_ = lean_ctor_get(v___x_1863_, 1);
lean_inc(v_a_1871_);
lean_dec_ref_known(v___x_1863_, 2);
v___x_1872_ = lean_array_get_size(v_a_1871_);
v___x_1873_ = lean_nat_dec_lt(v___x_1861_, v___x_1872_);
if (v___x_1873_ == 0)
{
lean_object* v___x_1874_; lean_object* v___x_1876_; 
lean_dec(v_a_1871_);
lean_dec_ref(v___y_1844_);
lean_dec_ref(v___y_1843_);
lean_dec_ref(v_repo_1328_);
lean_dec_ref(v_name_1327_);
v___x_1874_ = lean_box(0);
if (v_isShared_1850_ == 0)
{
lean_ctor_set(v___x_1849_, 0, v___x_1874_);
v___x_1876_ = v___x_1849_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v___x_1874_);
v___x_1876_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
return v___x_1876_;
}
}
else
{
lean_object* v___x_1878_; size_t v___x_1879_; size_t v___x_1880_; lean_object* v___x_1881_; 
lean_del_object(v___x_1849_);
v___x_1878_ = lean_box(0);
v___x_1879_ = ((size_t)0ULL);
v___x_1880_ = lean_usize_of_nat(v___x_1872_);
v___x_1881_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1871_, v___x_1879_, v___x_1880_, v___x_1878_, v_a_1326_);
lean_dec(v_a_1871_);
if (lean_obj_tag(v___x_1881_) == 0)
{
lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1888_; 
lean_dec_ref(v___y_1844_);
lean_dec_ref(v___y_1843_);
lean_dec_ref(v_repo_1328_);
lean_dec_ref(v_name_1327_);
v_isSharedCheck_1888_ = !lean_is_exclusive(v___x_1881_);
if (v_isSharedCheck_1888_ == 0)
{
lean_object* v_unused_1889_; 
v_unused_1889_ = lean_ctor_get(v___x_1881_, 0);
lean_dec(v_unused_1889_);
v___x_1883_ = v___x_1881_;
v_isShared_1884_ = v_isSharedCheck_1888_;
goto v_resetjp_1882_;
}
else
{
lean_dec(v___x_1881_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1888_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1886_; 
if (v_isShared_1884_ == 0)
{
lean_ctor_set_tag(v___x_1883_, 1);
lean_ctor_set(v___x_1883_, 0, v___x_1878_);
v___x_1886_ = v___x_1883_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v___x_1878_);
v___x_1886_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
return v___x_1886_;
}
}
}
else
{
v___y_1838_ = v___y_1843_;
v___y_1839_ = v___y_1844_;
v___y_1840_ = v___y_1845_;
v___y_1841_ = v___x_1881_;
goto v___jp_1837_;
}
}
}
}
else
{
lean_del_object(v___x_1849_);
lean_dec(v_val_1847_);
v___y_1820_ = v___y_1843_;
v___y_1821_ = v___y_1844_;
v___y_1822_ = v___y_1845_;
v___y_1823_ = v_a_1326_;
goto v___jp_1819_;
}
}
}
else
{
lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; 
lean_dec(v_a_1846_);
v___x_1891_ = lean_unsigned_to_nat(0u);
v___x_1892_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1328_);
lean_inc_ref(v___y_1844_);
lean_inc_ref(v___y_1845_);
v___x_1893_ = l_Lake_GitRepo_addRemote(v___y_1845_, v___y_1844_, v_repo_1328_, v___x_1892_);
if (lean_obj_tag(v___x_1893_) == 0)
{
lean_object* v_a_1894_; lean_object* v___x_1895_; uint8_t v___x_1896_; 
v_a_1894_ = lean_ctor_get(v___x_1893_, 1);
lean_inc(v_a_1894_);
lean_dec_ref_known(v___x_1893_, 2);
v___x_1895_ = lean_array_get_size(v_a_1894_);
v___x_1896_ = lean_nat_dec_lt(v___x_1891_, v___x_1895_);
if (v___x_1896_ == 0)
{
lean_dec(v_a_1894_);
v___y_1820_ = v___y_1843_;
v___y_1821_ = v___y_1844_;
v___y_1822_ = v___y_1845_;
v___y_1823_ = v_a_1326_;
goto v___jp_1819_;
}
else
{
lean_object* v___x_1897_; size_t v___x_1898_; size_t v___x_1899_; lean_object* v___x_1900_; 
v___x_1897_ = lean_box(0);
v___x_1898_ = ((size_t)0ULL);
v___x_1899_ = lean_usize_of_nat(v___x_1895_);
v___x_1900_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1894_, v___x_1898_, v___x_1899_, v___x_1897_, v_a_1326_);
lean_dec(v_a_1894_);
if (lean_obj_tag(v___x_1900_) == 0)
{
lean_dec_ref_known(v___x_1900_, 1);
v___y_1820_ = v___y_1843_;
v___y_1821_ = v___y_1844_;
v___y_1822_ = v___y_1845_;
v___y_1823_ = v_a_1326_;
goto v___jp_1819_;
}
else
{
v___y_1833_ = v___y_1843_;
v___y_1834_ = v___y_1844_;
v___y_1835_ = v___y_1845_;
v___y_1836_ = v___x_1900_;
goto v___jp_1832_;
}
}
}
else
{
lean_object* v_a_1901_; lean_object* v___x_1902_; uint8_t v___x_1903_; 
v_a_1901_ = lean_ctor_get(v___x_1893_, 1);
lean_inc(v_a_1901_);
lean_dec_ref_known(v___x_1893_, 2);
v___x_1902_ = lean_array_get_size(v_a_1901_);
v___x_1903_ = lean_nat_dec_lt(v___x_1891_, v___x_1902_);
if (v___x_1903_ == 0)
{
lean_object* v___x_1904_; lean_object* v___x_1905_; 
lean_dec(v_a_1901_);
lean_dec_ref(v___y_1844_);
lean_dec_ref(v___y_1843_);
lean_dec_ref(v_repo_1328_);
lean_dec_ref(v_name_1327_);
v___x_1904_ = lean_box(0);
v___x_1905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1904_);
return v___x_1905_;
}
else
{
lean_object* v___x_1906_; size_t v___x_1907_; size_t v___x_1908_; lean_object* v___x_1909_; 
v___x_1906_ = lean_box(0);
v___x_1907_ = ((size_t)0ULL);
v___x_1908_ = lean_usize_of_nat(v___x_1902_);
v___x_1909_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1901_, v___x_1907_, v___x_1908_, v___x_1906_, v_a_1326_);
lean_dec(v_a_1901_);
if (lean_obj_tag(v___x_1909_) == 0)
{
lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1916_; 
lean_dec_ref(v___y_1844_);
lean_dec_ref(v___y_1843_);
lean_dec_ref(v_repo_1328_);
lean_dec_ref(v_name_1327_);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1909_);
if (v_isSharedCheck_1916_ == 0)
{
lean_object* v_unused_1917_; 
v_unused_1917_ = lean_ctor_get(v___x_1909_, 0);
lean_dec(v_unused_1917_);
v___x_1911_ = v___x_1909_;
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
else
{
lean_dec(v___x_1909_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v___x_1914_; 
if (v_isShared_1912_ == 0)
{
lean_ctor_set_tag(v___x_1911_, 1);
lean_ctor_set(v___x_1911_, 0, v___x_1906_);
v___x_1914_ = v___x_1911_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v___x_1906_);
v___x_1914_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
return v___x_1914_;
}
}
}
else
{
v___y_1833_ = v___y_1843_;
v___y_1834_ = v___y_1844_;
v___y_1835_ = v___y_1845_;
v___y_1836_ = v___x_1909_;
goto v___jp_1832_;
}
}
}
}
}
v___jp_1918_:
{
if (v_a_1922_ == 0)
{
lean_object* v___x_1923_; lean_object* v___x_1924_; uint8_t v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
v___x_1923_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__7));
lean_inc_ref(v_name_1327_);
v___x_1924_ = lean_string_append(v_name_1327_, v___x_1923_);
v___x_1925_ = 1;
v___x_1926_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1926_, 0, v___x_1924_);
lean_ctor_set_uint8(v___x_1926_, sizeof(void*)*1, v___x_1925_);
lean_inc_ref(v_a_1326_);
v___x_1927_ = lean_apply_2(v_a_1326_, v___x_1926_, lean_box(0));
lean_inc_ref(v_repo_1328_);
v___x_1928_ = l_IO_FS_createDirAll(v_repo_1328_);
if (lean_obj_tag(v___x_1928_) == 0)
{
lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1961_; 
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_1961_ == 0)
{
lean_object* v_unused_1962_; 
v_unused_1962_ = lean_ctor_get(v___x_1928_, 0);
lean_dec(v_unused_1962_);
v___x_1930_ = v___x_1928_;
v_isShared_1931_ = v_isSharedCheck_1961_;
goto v_resetjp_1929_;
}
else
{
lean_dec(v___x_1928_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1961_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1932_ = lean_unsigned_to_nat(0u);
v___x_1933_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1328_);
v___x_1934_ = l_Lake_GitRepo_quietInit(v_repo_1328_, v___x_1933_);
if (lean_obj_tag(v___x_1934_) == 0)
{
lean_object* v_a_1935_; lean_object* v___x_1936_; uint8_t v___x_1937_; 
lean_del_object(v___x_1930_);
v_a_1935_ = lean_ctor_get(v___x_1934_, 1);
lean_inc(v_a_1935_);
lean_dec_ref_known(v___x_1934_, 2);
v___x_1936_ = lean_array_get_size(v_a_1935_);
v___x_1937_ = lean_nat_dec_lt(v___x_1932_, v___x_1936_);
if (v___x_1937_ == 0)
{
lean_dec(v_a_1935_);
v___y_1625_ = v___y_1919_;
v___y_1626_ = v___y_1920_;
v___y_1627_ = v___y_1921_;
goto v___jp_1624_;
}
else
{
lean_object* v___x_1938_; size_t v___x_1939_; size_t v___x_1940_; lean_object* v___x_1941_; 
v___x_1938_ = lean_box(0);
v___x_1939_ = ((size_t)0ULL);
v___x_1940_ = lean_usize_of_nat(v___x_1936_);
v___x_1941_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1935_, v___x_1939_, v___x_1940_, v___x_1938_, v_a_1326_);
lean_dec(v_a_1935_);
if (lean_obj_tag(v___x_1941_) == 0)
{
lean_dec_ref_known(v___x_1941_, 1);
v___y_1625_ = v___y_1919_;
v___y_1626_ = v___y_1920_;
v___y_1627_ = v___y_1921_;
goto v___jp_1624_;
}
else
{
v___y_1656_ = v___y_1919_;
v___y_1657_ = v___y_1920_;
v___y_1658_ = v___y_1921_;
v___y_1659_ = v___x_1941_;
goto v___jp_1655_;
}
}
}
else
{
lean_object* v_a_1942_; lean_object* v___x_1943_; uint8_t v___x_1944_; 
v_a_1942_ = lean_ctor_get(v___x_1934_, 1);
lean_inc(v_a_1942_);
lean_dec_ref_known(v___x_1934_, 2);
v___x_1943_ = lean_array_get_size(v_a_1942_);
v___x_1944_ = lean_nat_dec_lt(v___x_1932_, v___x_1943_);
if (v___x_1944_ == 0)
{
lean_object* v___x_1945_; lean_object* v___x_1947_; 
lean_dec(v_a_1942_);
lean_dec_ref(v___y_1920_);
lean_dec_ref(v___y_1919_);
lean_dec_ref(v_repo_1328_);
lean_dec_ref(v_name_1327_);
v___x_1945_ = lean_box(0);
if (v_isShared_1931_ == 0)
{
lean_ctor_set_tag(v___x_1930_, 1);
lean_ctor_set(v___x_1930_, 0, v___x_1945_);
v___x_1947_ = v___x_1930_;
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
else
{
lean_object* v___x_1949_; size_t v___x_1950_; size_t v___x_1951_; lean_object* v___x_1952_; 
lean_del_object(v___x_1930_);
v___x_1949_ = lean_box(0);
v___x_1950_ = ((size_t)0ULL);
v___x_1951_ = lean_usize_of_nat(v___x_1943_);
v___x_1952_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1942_, v___x_1950_, v___x_1951_, v___x_1949_, v_a_1326_);
lean_dec(v_a_1942_);
if (lean_obj_tag(v___x_1952_) == 0)
{
lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1959_; 
lean_dec_ref(v___y_1920_);
lean_dec_ref(v___y_1919_);
lean_dec_ref(v_repo_1328_);
lean_dec_ref(v_name_1327_);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___x_1952_);
if (v_isSharedCheck_1959_ == 0)
{
lean_object* v_unused_1960_; 
v_unused_1960_ = lean_ctor_get(v___x_1952_, 0);
lean_dec(v_unused_1960_);
v___x_1954_ = v___x_1952_;
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
else
{
lean_dec(v___x_1952_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1957_; 
if (v_isShared_1955_ == 0)
{
lean_ctor_set_tag(v___x_1954_, 1);
lean_ctor_set(v___x_1954_, 0, v___x_1949_);
v___x_1957_ = v___x_1954_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v___x_1949_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
else
{
v___y_1656_ = v___y_1919_;
v___y_1657_ = v___y_1920_;
v___y_1658_ = v___y_1921_;
v___y_1659_ = v___x_1952_;
goto v___jp_1655_;
}
}
}
}
}
else
{
lean_object* v_a_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1975_; 
lean_dec_ref(v___y_1920_);
lean_dec_ref(v___y_1919_);
lean_dec_ref(v_repo_1328_);
lean_dec_ref(v_name_1327_);
v_a_1963_ = lean_ctor_get(v___x_1928_, 0);
v_isSharedCheck_1975_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_1975_ == 0)
{
v___x_1965_ = v___x_1928_;
v_isShared_1966_ = v_isSharedCheck_1975_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_a_1963_);
lean_dec(v___x_1928_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1975_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v___x_1967_; uint8_t v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1973_; 
v___x_1967_ = lean_io_error_to_string(v_a_1963_);
v___x_1968_ = 3;
v___x_1969_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1969_, 0, v___x_1967_);
lean_ctor_set_uint8(v___x_1969_, sizeof(void*)*1, v___x_1968_);
lean_inc_ref(v_a_1326_);
v___x_1970_ = lean_apply_2(v_a_1326_, v___x_1969_, lean_box(0));
v___x_1971_ = lean_box(0);
if (v_isShared_1966_ == 0)
{
lean_ctor_set(v___x_1965_, 0, v___x_1971_);
v___x_1973_ = v___x_1965_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v___x_1971_);
v___x_1973_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
return v___x_1973_;
}
}
}
}
else
{
lean_object* v___x_1976_; lean_object* v___x_1977_; uint8_t v___x_1978_; 
v___x_1976_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1328_);
lean_inc_ref(v___y_1921_);
v___x_1977_ = l_Lake_GitRepo_getRemoteUrl_x3f(v___y_1921_, v_repo_1328_);
v___x_1978_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_1978_ == 0)
{
v___y_1843_ = v___y_1919_;
v___y_1844_ = v___y_1920_;
v___y_1845_ = v___y_1921_;
v_a_1846_ = v___x_1977_;
goto v___jp_1842_;
}
else
{
lean_object* v___x_1979_; size_t v___x_1980_; size_t v___x_1981_; lean_object* v___x_1982_; 
v___x_1979_ = lean_box(0);
v___x_1980_ = ((size_t)0ULL);
v___x_1981_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_1982_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_1976_, v___x_1980_, v___x_1981_, v___x_1979_, v_a_1326_);
if (lean_obj_tag(v___x_1982_) == 0)
{
lean_dec_ref_known(v___x_1982_, 1);
v___y_1843_ = v___y_1919_;
v___y_1844_ = v___y_1920_;
v___y_1845_ = v___y_1921_;
v_a_1846_ = v___x_1977_;
goto v___jp_1842_;
}
else
{
lean_dec(v___x_1977_);
lean_dec_ref(v___y_1920_);
lean_dec_ref(v___y_1919_);
lean_dec_ref(v_repo_1328_);
lean_dec_ref(v_name_1327_);
return v___x_1982_;
}
}
}
}
v___jp_1983_:
{
lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; uint8_t v___x_1990_; uint8_t v___x_1991_; 
v___x_1987_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_1988_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__8));
lean_inc_ref(v_repo_1328_);
v___x_1989_ = l_System_FilePath_join(v_repo_1328_, v___x_1988_);
v___x_1990_ = l_System_FilePath_pathExists(v___x_1989_);
lean_dec_ref(v___x_1989_);
v___x_1991_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_1991_ == 0)
{
v___y_1919_ = v___y_1984_;
v___y_1920_ = v_a_1986_;
v___y_1921_ = v___y_1985_;
v_a_1922_ = v___x_1990_;
goto v___jp_1918_;
}
else
{
lean_object* v___x_1992_; size_t v___x_1993_; size_t v___x_1994_; lean_object* v___x_1995_; 
v___x_1992_ = lean_box(0);
v___x_1993_ = ((size_t)0ULL);
v___x_1994_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_1995_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_1987_, v___x_1993_, v___x_1994_, v___x_1992_, v_a_1326_);
if (lean_obj_tag(v___x_1995_) == 0)
{
lean_dec_ref_known(v___x_1995_, 1);
v___y_1919_ = v___y_1984_;
v___y_1920_ = v_a_1986_;
v___y_1921_ = v___y_1985_;
v_a_1922_ = v___x_1990_;
goto v___jp_1918_;
}
else
{
lean_dec_ref(v_a_1986_);
lean_dec_ref(v___y_1984_);
lean_dec_ref(v_repo_1328_);
lean_dec_ref(v_name_1327_);
return v___x_1995_;
}
}
}
v___jp_1996_:
{
if (lean_obj_tag(v_a_1999_) == 1)
{
lean_object* v_val_2000_; 
lean_dec_ref(v_url_1329_);
v_val_2000_ = lean_ctor_get(v_a_1999_, 0);
lean_inc(v_val_2000_);
lean_dec_ref_known(v_a_1999_, 1);
v___y_1984_ = v___y_1997_;
v___y_1985_ = v___y_1998_;
v_a_1986_ = v_val_2000_;
goto v___jp_1983_;
}
else
{
lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; uint8_t v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; 
lean_dec(v_a_1999_);
lean_dec_ref(v___y_1997_);
lean_dec_ref(v_repo_1328_);
v___x_2001_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__0));
v___x_2002_ = lean_string_append(v_name_1327_, v___x_2001_);
v___x_2003_ = lean_string_append(v___x_2002_, v_url_1329_);
lean_dec_ref(v_url_1329_);
v___x_2004_ = 3;
v___x_2005_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2005_, 0, v___x_2003_);
lean_ctor_set_uint8(v___x_2005_, sizeof(void*)*1, v___x_2004_);
lean_inc_ref(v_a_1326_);
v___x_2006_ = lean_apply_2(v_a_1326_, v___x_2005_, lean_box(0));
v___x_2007_ = lean_box(0);
v___x_2008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2008_, 0, v___x_2007_);
return v___x_2008_;
}
}
v___jp_2009_:
{
lean_object* v___x_2015_; uint8_t v___x_2016_; 
v___x_2015_ = lean_array_get_size(v___y_2012_);
v___x_2016_ = lean_nat_dec_lt(v___y_2010_, v___x_2015_);
if (v___x_2016_ == 0)
{
v___y_1997_ = v___y_2011_;
v___y_1998_ = v___y_2013_;
v_a_1999_ = v_val_2014_;
goto v___jp_1996_;
}
else
{
lean_object* v___x_2017_; size_t v___x_2018_; size_t v___x_2019_; lean_object* v___x_2020_; 
v___x_2017_ = lean_box(0);
v___x_2018_ = ((size_t)0ULL);
v___x_2019_ = lean_usize_of_nat(v___x_2015_);
v___x_2020_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_2012_, v___x_2018_, v___x_2019_, v___x_2017_, v_a_1326_);
if (lean_obj_tag(v___x_2020_) == 0)
{
lean_dec_ref_known(v___x_2020_, 1);
v___y_1997_ = v___y_2011_;
v___y_1998_ = v___y_2013_;
v_a_1999_ = v_val_2014_;
goto v___jp_1996_;
}
else
{
lean_dec(v_val_2014_);
lean_dec_ref(v___y_2011_);
lean_dec_ref(v_url_1329_);
lean_dec_ref(v_repo_1328_);
lean_dec_ref(v_name_1327_);
return v___x_2020_;
}
}
}
v___jp_2021_:
{
if (v_a_2024_ == 0)
{
v___y_1984_ = v___y_2022_;
v___y_1985_ = v___y_2023_;
v_a_1986_ = v_url_1329_;
goto v___jp_1983_;
}
else
{
lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; uint8_t v___x_2029_; 
v___x_2025_ = lean_unsigned_to_nat(0u);
v___x_2026_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_url_1329_);
v___x_2027_ = l_Lake_resolvePath(v_url_1329_);
v___x_2028_ = lean_string_utf8_byte_size(v___x_2027_);
v___x_2029_ = lean_nat_dec_eq(v___x_2028_, v___x_2025_);
if (v___x_2029_ == 0)
{
lean_object* v___x_2030_; 
v___x_2030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2030_, 0, v___x_2027_);
v___y_2010_ = v___x_2025_;
v___y_2011_ = v___y_2022_;
v___y_2012_ = v___x_2026_;
v___y_2013_ = v___y_2023_;
v_val_2014_ = v___x_2030_;
goto v___jp_2009_;
}
else
{
lean_object* v___x_2031_; 
lean_dec_ref(v___x_2027_);
v___x_2031_ = lean_box(0);
v___y_2010_ = v___x_2025_;
v___y_2011_ = v___y_2022_;
v___y_2012_ = v___x_2026_;
v___y_2013_ = v___y_2023_;
v_val_2014_ = v___x_2031_;
goto v___jp_2009_;
}
}
}
v___jp_2032_:
{
lean_object* v_remote_2034_; lean_object* v___x_2035_; uint8_t v___x_2036_; uint8_t v___x_2037_; 
v_remote_2034_ = l_Lake_Git_defaultRemote;
v___x_2035_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_2036_ = l_System_FilePath_pathExists(v_url_1329_);
v___x_2037_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_2037_ == 0)
{
v___y_2022_ = v___y_2033_;
v___y_2023_ = v_remote_2034_;
v_a_2024_ = v___x_2036_;
goto v___jp_2021_;
}
else
{
lean_object* v___x_2038_; size_t v___x_2039_; size_t v___x_2040_; lean_object* v___x_2041_; 
v___x_2038_ = lean_box(0);
v___x_2039_ = ((size_t)0ULL);
v___x_2040_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_2041_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_2035_, v___x_2039_, v___x_2040_, v___x_2038_, v_a_1326_);
if (lean_obj_tag(v___x_2041_) == 0)
{
lean_dec_ref_known(v___x_2041_, 1);
v___y_2022_ = v___y_2033_;
v___y_2023_ = v_remote_2034_;
v_a_2024_ = v___x_2036_;
goto v___jp_2021_;
}
else
{
lean_dec_ref(v___y_2033_);
lean_dec_ref(v_url_1329_);
lean_dec_ref(v_repo_1328_);
lean_dec_ref(v_name_1327_);
return v___x_2041_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1326_ = stack[0].m_obj;
lean_object* v_name_1327_ = stack[1].m_obj;
lean_object* v_repo_1328_ = stack[2].m_obj;
lean_object* v_url_1329_ = stack[3].m_obj;
lean_object* v_rev_x3f_1330_ = stack[4].m_obj;
lean_object* v_res_2044_;
v_res_2044_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(v_a_1326_, v_name_1327_, v_repo_1328_, v_url_1329_, v_rev_x3f_1330_);
stack->m_obj
 = v_res_2044_;
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0___boxed(lean_object* v_a_2045_, lean_object* v_name_2046_, lean_object* v_repo_2047_, lean_object* v_url_2048_, lean_object* v_rev_x3f_2049_, lean_object* v_a_2050_){
_start:
{
lean_object* v_res_2051_; 
v_res_2051_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(v_a_2045_, v_name_2046_, v_repo_2047_, v_url_2048_, v_rev_x3f_2049_);
lean_dec_ref(v_a_2045_);
return v_res_2051_;
}
}
lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit(lean_object* v_dep_2052_, uint8_t v_inherited_2053_, lean_object* v_lakeEnv_2054_, lean_object* v_wsDir_2055_, lean_object* v_name_2056_, lean_object* v_relPkgDir_2057_, lean_object* v_gitUrl_2058_, lean_object* v_remoteUrl_2059_, lean_object* v_inputRev_x3f_2060_, lean_object* v_subDir_x3f_2061_, lean_object* v_a_2062_){
_start:
{
lean_object* v_pkgUrlMap_2064_; lean_object* v_name_2065_; lean_object* v_scope_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2242_; 
v_pkgUrlMap_2064_ = lean_ctor_get(v_lakeEnv_2054_, 5);
v_name_2065_ = lean_ctor_get(v_dep_2052_, 0);
v_scope_2066_ = lean_ctor_get(v_dep_2052_, 1);
v_isSharedCheck_2242_ = !lean_is_exclusive(v_dep_2052_);
if (v_isSharedCheck_2242_ == 0)
{
lean_object* v_unused_2243_; lean_object* v_unused_2244_; lean_object* v_unused_2245_; 
v_unused_2243_ = lean_ctor_get(v_dep_2052_, 4);
lean_dec(v_unused_2243_);
v_unused_2244_ = lean_ctor_get(v_dep_2052_, 3);
lean_dec(v_unused_2244_);
v_unused_2245_ = lean_ctor_get(v_dep_2052_, 2);
lean_dec(v_unused_2245_);
v___x_2068_ = v_dep_2052_;
v_isShared_2069_ = v_isSharedCheck_2242_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_scope_2066_);
lean_inc(v_name_2065_);
lean_dec(v_dep_2052_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2242_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___y_2071_; lean_object* v___y_2072_; lean_object* v___y_2073_; lean_object* v_a_2074_; lean_object* v___y_2083_; lean_object* v___y_2084_; lean_object* v___y_2085_; lean_object* v___y_2086_; lean_object* v___y_2087_; lean_object* v_val_2088_; lean_object* v___y_2104_; lean_object* v___y_2105_; lean_object* v___y_2106_; lean_object* v_a_2107_; lean_object* v___y_2139_; lean_object* v___y_2140_; lean_object* v___y_2141_; lean_object* v___y_2142_; lean_object* v___y_2143_; lean_object* v_val_2144_; lean_object* v___y_2160_; lean_object* v___y_2161_; lean_object* v___y_2162_; lean_object* v___y_2173_; lean_object* v_a_2174_; lean_object* v_gitDir_2177_; lean_object* v___y_2179_; lean_object* v___x_2240_; 
lean_inc_ref(v_relPkgDir_2057_);
lean_inc_ref(v_wsDir_2055_);
v_gitDir_2177_ = l_Lake_joinRelative(v_wsDir_2055_, v_relPkgDir_2057_);
v___x_2240_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgUrlMap_2064_, v_name_2065_);
if (lean_obj_tag(v___x_2240_) == 0)
{
v___y_2179_ = v_gitUrl_2058_;
goto v___jp_2178_;
}
else
{
lean_object* v_val_2241_; 
lean_dec_ref(v_gitUrl_2058_);
v_val_2241_ = lean_ctor_get(v___x_2240_, 0);
lean_inc(v_val_2241_);
lean_dec_ref_known(v___x_2240_, 1);
v___y_2179_ = v_val_2241_;
goto v___jp_2178_;
}
v___jp_2070_:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2079_; 
v___x_2075_ = l_Lake_defaultConfigFile;
v___x_2076_ = lean_box(0);
v___x_2077_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_2077_, 0, v_name_2065_);
lean_ctor_set(v___x_2077_, 1, v_scope_2066_);
lean_ctor_set(v___x_2077_, 2, v___x_2075_);
lean_ctor_set(v___x_2077_, 3, v___x_2076_);
lean_ctor_set(v___x_2077_, 4, v___y_2071_);
lean_ctor_set_uint8(v___x_2077_, sizeof(void*)*5, v_inherited_2053_);
if (v_isShared_2069_ == 0)
{
lean_ctor_set(v___x_2068_, 4, v___x_2077_);
lean_ctor_set(v___x_2068_, 3, v_a_2074_);
lean_ctor_set(v___x_2068_, 2, v_remoteUrl_2059_);
lean_ctor_set(v___x_2068_, 1, v___y_2072_);
lean_ctor_set(v___x_2068_, 0, v___y_2073_);
v___x_2079_ = v___x_2068_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v___y_2073_);
lean_ctor_set(v_reuseFailAlloc_2081_, 1, v___y_2072_);
lean_ctor_set(v_reuseFailAlloc_2081_, 2, v_remoteUrl_2059_);
lean_ctor_set(v_reuseFailAlloc_2081_, 3, v_a_2074_);
lean_ctor_set(v_reuseFailAlloc_2081_, 4, v___x_2077_);
v___x_2079_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
lean_object* v___x_2080_; 
v___x_2080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2079_);
return v___x_2080_;
}
}
v___jp_2082_:
{
lean_object* v___x_2089_; uint8_t v___x_2090_; 
v___x_2089_ = lean_array_get_size(v___y_2083_);
v___x_2090_ = lean_nat_dec_lt(v___y_2084_, v___x_2089_);
if (v___x_2090_ == 0)
{
v___y_2071_ = v___y_2085_;
v___y_2072_ = v___y_2086_;
v___y_2073_ = v___y_2087_;
v_a_2074_ = v_val_2088_;
goto v___jp_2070_;
}
else
{
lean_object* v___x_2091_; size_t v___x_2092_; size_t v___x_2093_; lean_object* v___x_2094_; 
v___x_2091_ = lean_box(0);
v___x_2092_ = ((size_t)0ULL);
v___x_2093_ = lean_usize_of_nat(v___x_2089_);
v___x_2094_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_2083_, v___x_2092_, v___x_2093_, v___x_2091_, v_a_2062_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_dec_ref_known(v___x_2094_, 1);
v___y_2071_ = v___y_2085_;
v___y_2072_ = v___y_2086_;
v___y_2073_ = v___y_2087_;
v_a_2074_ = v_val_2088_;
goto v___jp_2070_;
}
else
{
lean_object* v_a_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2102_; 
lean_dec_ref(v_val_2088_);
lean_dec_ref(v___y_2087_);
lean_dec_ref(v___y_2086_);
lean_dec_ref(v___y_2085_);
lean_del_object(v___x_2068_);
lean_dec_ref(v_scope_2066_);
lean_dec(v_name_2065_);
lean_dec_ref(v_remoteUrl_2059_);
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2102_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2102_ == 0)
{
v___x_2097_ = v___x_2094_;
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_a_2095_);
lean_dec(v___x_2094_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2100_; 
if (v_isShared_2098_ == 0)
{
v___x_2100_ = v___x_2097_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v_a_2095_);
v___x_2100_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
return v___x_2100_;
}
}
}
}
}
v___jp_2103_:
{
if (lean_obj_tag(v_a_2107_) == 1)
{
lean_object* v_val_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; 
lean_dec_ref(v___y_2106_);
lean_dec_ref(v_name_2056_);
v_val_2108_ = lean_ctor_get(v_a_2107_, 0);
lean_inc_n(v_val_2108_, 2);
lean_dec_ref_known(v_a_2107_, 1);
v___x_2109_ = l_Lake_defaultManifestFile;
v___x_2110_ = l_Lake_joinRelative(v_val_2108_, v___x_2109_);
v___x_2111_ = lean_unsigned_to_nat(0u);
v___x_2112_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_2113_ = l_Lake_Manifest_load(v___x_2110_);
if (lean_obj_tag(v___x_2113_) == 0)
{
lean_object* v_a_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2121_; 
v_a_2114_ = lean_ctor_get(v___x_2113_, 0);
v_isSharedCheck_2121_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2121_ == 0)
{
v___x_2116_ = v___x_2113_;
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_a_2114_);
lean_dec(v___x_2113_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
lean_object* v___x_2119_; 
if (v_isShared_2117_ == 0)
{
lean_ctor_set_tag(v___x_2116_, 1);
v___x_2119_ = v___x_2116_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v_a_2114_);
v___x_2119_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
v___y_2083_ = v___x_2112_;
v___y_2084_ = v___x_2111_;
v___y_2085_ = v___y_2104_;
v___y_2086_ = v___y_2105_;
v___y_2087_ = v_val_2108_;
v_val_2088_ = v___x_2119_;
goto v___jp_2082_;
}
}
}
else
{
lean_object* v_a_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2129_; 
v_a_2122_ = lean_ctor_get(v___x_2113_, 0);
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2124_ = v___x_2113_;
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_a_2122_);
lean_dec(v___x_2113_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2127_; 
if (v_isShared_2125_ == 0)
{
lean_ctor_set_tag(v___x_2124_, 0);
v___x_2127_ = v___x_2124_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_a_2122_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
v___y_2083_ = v___x_2112_;
v___y_2084_ = v___x_2111_;
v___y_2085_ = v___y_2104_;
v___y_2086_ = v___y_2105_;
v___y_2087_ = v_val_2108_;
v_val_2088_ = v___x_2127_;
goto v___jp_2082_;
}
}
}
}
else
{
lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; uint8_t v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; 
lean_dec(v_a_2107_);
lean_dec_ref(v___y_2105_);
lean_dec_ref(v___y_2104_);
lean_del_object(v___x_2068_);
lean_dec_ref(v_scope_2066_);
lean_dec(v_name_2065_);
lean_dec_ref(v_remoteUrl_2059_);
v___x_2130_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0));
v___x_2131_ = lean_string_append(v_name_2056_, v___x_2130_);
v___x_2132_ = lean_string_append(v___x_2131_, v___y_2106_);
lean_dec_ref(v___y_2106_);
v___x_2133_ = 3;
v___x_2134_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2134_, 0, v___x_2132_);
lean_ctor_set_uint8(v___x_2134_, sizeof(void*)*1, v___x_2133_);
lean_inc_ref(v_a_2062_);
v___x_2135_ = lean_apply_2(v_a_2062_, v___x_2134_, lean_box(0));
v___x_2136_ = lean_box(0);
v___x_2137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2137_, 0, v___x_2136_);
return v___x_2137_;
}
}
v___jp_2138_:
{
lean_object* v___x_2145_; uint8_t v___x_2146_; 
v___x_2145_ = lean_array_get_size(v___y_2139_);
v___x_2146_ = lean_nat_dec_lt(v___y_2143_, v___x_2145_);
if (v___x_2146_ == 0)
{
v___y_2104_ = v___y_2140_;
v___y_2105_ = v___y_2141_;
v___y_2106_ = v___y_2142_;
v_a_2107_ = v_val_2144_;
goto v___jp_2103_;
}
else
{
lean_object* v___x_2147_; size_t v___x_2148_; size_t v___x_2149_; lean_object* v___x_2150_; 
v___x_2147_ = lean_box(0);
v___x_2148_ = ((size_t)0ULL);
v___x_2149_ = lean_usize_of_nat(v___x_2145_);
v___x_2150_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_2139_, v___x_2148_, v___x_2149_, v___x_2147_, v_a_2062_);
if (lean_obj_tag(v___x_2150_) == 0)
{
lean_dec_ref_known(v___x_2150_, 1);
v___y_2104_ = v___y_2140_;
v___y_2105_ = v___y_2141_;
v___y_2106_ = v___y_2142_;
v_a_2107_ = v_val_2144_;
goto v___jp_2103_;
}
else
{
lean_object* v_a_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2158_; 
lean_dec(v_val_2144_);
lean_dec_ref(v___y_2142_);
lean_dec_ref(v___y_2141_);
lean_dec_ref(v___y_2140_);
lean_del_object(v___x_2068_);
lean_dec_ref(v_scope_2066_);
lean_dec(v_name_2065_);
lean_dec_ref(v_remoteUrl_2059_);
lean_dec_ref(v_name_2056_);
v_a_2151_ = lean_ctor_get(v___x_2150_, 0);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2150_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2153_ = v___x_2150_;
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_a_2151_);
lean_dec(v___x_2150_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2156_; 
if (v_isShared_2154_ == 0)
{
v___x_2156_ = v___x_2153_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_a_2151_);
v___x_2156_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
return v___x_2156_;
}
}
}
}
}
v___jp_2159_:
{
lean_object* v___x_2163_; lean_object* v_pkgDir_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; uint8_t v___x_2169_; 
v___x_2163_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2163_, 0, v___y_2161_);
lean_ctor_set(v___x_2163_, 1, v___y_2160_);
lean_ctor_set(v___x_2163_, 2, v_inputRev_x3f_2060_);
lean_ctor_set(v___x_2163_, 3, v_subDir_x3f_2061_);
lean_inc_ref(v___y_2162_);
v_pkgDir_2164_ = l_Lake_joinRelative(v_wsDir_2055_, v___y_2162_);
v___x_2165_ = lean_unsigned_to_nat(0u);
v___x_2166_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_pkgDir_2164_);
v___x_2167_ = l_Lake_resolvePath(v_pkgDir_2164_);
v___x_2168_ = lean_string_utf8_byte_size(v___x_2167_);
v___x_2169_ = lean_nat_dec_eq(v___x_2168_, v___x_2165_);
if (v___x_2169_ == 0)
{
lean_object* v___x_2170_; 
v___x_2170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2170_, 0, v___x_2167_);
v___y_2139_ = v___x_2166_;
v___y_2140_ = v___x_2163_;
v___y_2141_ = v___y_2162_;
v___y_2142_ = v_pkgDir_2164_;
v___y_2143_ = v___x_2165_;
v_val_2144_ = v___x_2170_;
goto v___jp_2138_;
}
else
{
lean_object* v___x_2171_; 
lean_dec_ref(v___x_2167_);
v___x_2171_ = lean_box(0);
v___y_2139_ = v___x_2166_;
v___y_2140_ = v___x_2163_;
v___y_2141_ = v___y_2162_;
v___y_2142_ = v_pkgDir_2164_;
v___y_2143_ = v___x_2165_;
v_val_2144_ = v___x_2171_;
goto v___jp_2138_;
}
}
v___jp_2172_:
{
if (lean_obj_tag(v_subDir_x3f_2061_) == 1)
{
lean_object* v_val_2175_; lean_object* v___x_2176_; 
v_val_2175_ = lean_ctor_get(v_subDir_x3f_2061_, 0);
lean_inc(v_val_2175_);
v___x_2176_ = l_Lake_joinRelative(v_relPkgDir_2057_, v_val_2175_);
v___y_2160_ = v_a_2174_;
v___y_2161_ = v___y_2173_;
v___y_2162_ = v___x_2176_;
goto v___jp_2159_;
}
else
{
v___y_2160_ = v_a_2174_;
v___y_2161_ = v___y_2173_;
v___y_2162_ = v_relPkgDir_2057_;
goto v___jp_2159_;
}
}
v___jp_2178_:
{
lean_object* v___x_2180_; 
lean_inc(v_inputRev_x3f_2060_);
lean_inc_ref(v___y_2179_);
lean_inc_ref(v_gitDir_2177_);
lean_inc_ref(v_name_2056_);
v___x_2180_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(v_a_2062_, v_name_2056_, v_gitDir_2177_, v___y_2179_, v_inputRev_x3f_2060_);
if (lean_obj_tag(v___x_2180_) == 0)
{
lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2230_; 
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2180_);
if (v_isSharedCheck_2230_ == 0)
{
lean_object* v_unused_2231_; 
v_unused_2231_ = lean_ctor_get(v___x_2180_, 0);
lean_dec(v_unused_2231_);
v___x_2182_ = v___x_2180_;
v_isShared_2183_ = v_isSharedCheck_2230_;
goto v_resetjp_2181_;
}
else
{
lean_dec(v___x_2180_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2230_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; 
v___x_2184_ = lean_unsigned_to_nat(0u);
v___x_2185_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_2186_ = l_Lake_GitRepo_getHeadRevision(v_gitDir_2177_, v___x_2185_);
if (lean_obj_tag(v___x_2186_) == 0)
{
lean_object* v_a_2187_; lean_object* v_a_2188_; lean_object* v___x_2189_; uint8_t v___x_2190_; 
lean_del_object(v___x_2182_);
v_a_2187_ = lean_ctor_get(v___x_2186_, 0);
lean_inc(v_a_2187_);
v_a_2188_ = lean_ctor_get(v___x_2186_, 1);
lean_inc(v_a_2188_);
lean_dec_ref_known(v___x_2186_, 2);
v___x_2189_ = lean_array_get_size(v_a_2188_);
v___x_2190_ = lean_nat_dec_lt(v___x_2184_, v___x_2189_);
if (v___x_2190_ == 0)
{
lean_dec(v_a_2188_);
v___y_2173_ = v___y_2179_;
v_a_2174_ = v_a_2187_;
goto v___jp_2172_;
}
else
{
lean_object* v___x_2191_; size_t v___x_2192_; size_t v___x_2193_; lean_object* v___x_2194_; 
v___x_2191_ = lean_box(0);
v___x_2192_ = ((size_t)0ULL);
v___x_2193_ = lean_usize_of_nat(v___x_2189_);
v___x_2194_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_2188_, v___x_2192_, v___x_2193_, v___x_2191_, v_a_2062_);
lean_dec(v_a_2188_);
if (lean_obj_tag(v___x_2194_) == 0)
{
lean_dec_ref_known(v___x_2194_, 1);
v___y_2173_ = v___y_2179_;
v_a_2174_ = v_a_2187_;
goto v___jp_2172_;
}
else
{
lean_object* v_a_2195_; lean_object* v___x_2197_; uint8_t v_isShared_2198_; uint8_t v_isSharedCheck_2202_; 
lean_dec(v_a_2187_);
lean_dec_ref(v___y_2179_);
lean_del_object(v___x_2068_);
lean_dec_ref(v_scope_2066_);
lean_dec(v_name_2065_);
lean_dec(v_subDir_x3f_2061_);
lean_dec(v_inputRev_x3f_2060_);
lean_dec_ref(v_remoteUrl_2059_);
lean_dec_ref(v_relPkgDir_2057_);
lean_dec_ref(v_name_2056_);
lean_dec_ref(v_wsDir_2055_);
v_a_2195_ = lean_ctor_get(v___x_2194_, 0);
v_isSharedCheck_2202_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2202_ == 0)
{
v___x_2197_ = v___x_2194_;
v_isShared_2198_ = v_isSharedCheck_2202_;
goto v_resetjp_2196_;
}
else
{
lean_inc(v_a_2195_);
lean_dec(v___x_2194_);
v___x_2197_ = lean_box(0);
v_isShared_2198_ = v_isSharedCheck_2202_;
goto v_resetjp_2196_;
}
v_resetjp_2196_:
{
lean_object* v___x_2200_; 
if (v_isShared_2198_ == 0)
{
v___x_2200_ = v___x_2197_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v_a_2195_);
v___x_2200_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
return v___x_2200_;
}
}
}
}
}
else
{
lean_object* v_a_2203_; lean_object* v___x_2204_; uint8_t v___x_2205_; 
lean_dec_ref(v___y_2179_);
lean_del_object(v___x_2068_);
lean_dec_ref(v_scope_2066_);
lean_dec(v_name_2065_);
lean_dec(v_subDir_x3f_2061_);
lean_dec(v_inputRev_x3f_2060_);
lean_dec_ref(v_remoteUrl_2059_);
lean_dec_ref(v_relPkgDir_2057_);
lean_dec_ref(v_name_2056_);
lean_dec_ref(v_wsDir_2055_);
v_a_2203_ = lean_ctor_get(v___x_2186_, 1);
lean_inc(v_a_2203_);
lean_dec_ref_known(v___x_2186_, 2);
v___x_2204_ = lean_array_get_size(v_a_2203_);
v___x_2205_ = lean_nat_dec_lt(v___x_2184_, v___x_2204_);
if (v___x_2205_ == 0)
{
lean_object* v___x_2206_; lean_object* v___x_2208_; 
lean_dec(v_a_2203_);
v___x_2206_ = lean_box(0);
if (v_isShared_2183_ == 0)
{
lean_ctor_set_tag(v___x_2182_, 1);
lean_ctor_set(v___x_2182_, 0, v___x_2206_);
v___x_2208_ = v___x_2182_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v___x_2206_);
v___x_2208_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
return v___x_2208_;
}
}
else
{
lean_object* v___x_2210_; size_t v___x_2211_; size_t v___x_2212_; lean_object* v___x_2213_; 
lean_del_object(v___x_2182_);
v___x_2210_ = lean_box(0);
v___x_2211_ = ((size_t)0ULL);
v___x_2212_ = lean_usize_of_nat(v___x_2204_);
v___x_2213_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_2203_, v___x_2211_, v___x_2212_, v___x_2210_, v_a_2062_);
lean_dec(v_a_2203_);
if (lean_obj_tag(v___x_2213_) == 0)
{
lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2220_; 
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_2213_);
if (v_isSharedCheck_2220_ == 0)
{
lean_object* v_unused_2221_; 
v_unused_2221_ = lean_ctor_get(v___x_2213_, 0);
lean_dec(v_unused_2221_);
v___x_2215_ = v___x_2213_;
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
else
{
lean_dec(v___x_2213_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2218_; 
if (v_isShared_2216_ == 0)
{
lean_ctor_set_tag(v___x_2215_, 1);
lean_ctor_set(v___x_2215_, 0, v___x_2210_);
v___x_2218_ = v___x_2215_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v___x_2210_);
v___x_2218_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
return v___x_2218_;
}
}
}
else
{
lean_object* v_a_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2229_; 
v_a_2222_ = lean_ctor_get(v___x_2213_, 0);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2213_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2224_ = v___x_2213_;
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_a_2222_);
lean_dec(v___x_2213_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
lean_object* v___x_2227_; 
if (v_isShared_2225_ == 0)
{
v___x_2227_ = v___x_2224_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v_a_2222_);
v___x_2227_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
return v___x_2227_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2239_; 
lean_dec_ref(v___y_2179_);
lean_dec_ref(v_gitDir_2177_);
lean_del_object(v___x_2068_);
lean_dec_ref(v_scope_2066_);
lean_dec(v_name_2065_);
lean_dec(v_subDir_x3f_2061_);
lean_dec(v_inputRev_x3f_2060_);
lean_dec_ref(v_remoteUrl_2059_);
lean_dec_ref(v_relPkgDir_2057_);
lean_dec_ref(v_name_2056_);
lean_dec_ref(v_wsDir_2055_);
v_a_2232_ = lean_ctor_get(v___x_2180_, 0);
v_isSharedCheck_2239_ = !lean_is_exclusive(v___x_2180_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2234_ = v___x_2180_;
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_a_2232_);
lean_dec(v___x_2180_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
lean_object* v___x_2237_; 
if (v_isShared_2235_ == 0)
{
v___x_2237_ = v___x_2234_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_a_2232_);
v___x_2237_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
return v___x_2237_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_0interp(lean_interpreter_value* stack)
{
lean_object* v_dep_2052_ = stack[0].m_obj;
uint8_t v_inherited_2053_ = stack[1].m_num;
lean_object* v_lakeEnv_2054_ = stack[2].m_obj;
lean_object* v_wsDir_2055_ = stack[3].m_obj;
lean_object* v_name_2056_ = stack[4].m_obj;
lean_object* v_relPkgDir_2057_ = stack[5].m_obj;
lean_object* v_gitUrl_2058_ = stack[6].m_obj;
lean_object* v_remoteUrl_2059_ = stack[7].m_obj;
lean_object* v_inputRev_x3f_2060_ = stack[8].m_obj;
lean_object* v_subDir_x3f_2061_ = stack[9].m_obj;
lean_object* v_a_2062_ = stack[10].m_obj;
lean_object* v_res_2246_;
v_res_2246_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit(v_dep_2052_, v_inherited_2053_, v_lakeEnv_2054_, v_wsDir_2055_, v_name_2056_, v_relPkgDir_2057_, v_gitUrl_2058_, v_remoteUrl_2059_, v_inputRev_x3f_2060_, v_subDir_x3f_2061_, v_a_2062_);
stack->m_obj
 = v_res_2246_;
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___boxed(lean_object* v_dep_2247_, lean_object* v_inherited_2248_, lean_object* v_lakeEnv_2249_, lean_object* v_wsDir_2250_, lean_object* v_name_2251_, lean_object* v_relPkgDir_2252_, lean_object* v_gitUrl_2253_, lean_object* v_remoteUrl_2254_, lean_object* v_inputRev_x3f_2255_, lean_object* v_subDir_x3f_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_){
_start:
{
uint8_t v_inherited_boxed_2259_; lean_object* v_res_2260_; 
v_inherited_boxed_2259_ = lean_unbox(v_inherited_2248_);
v_res_2260_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit(v_dep_2247_, v_inherited_boxed_2259_, v_lakeEnv_2249_, v_wsDir_2250_, v_name_2251_, v_relPkgDir_2252_, v_gitUrl_2253_, v_remoteUrl_2254_, v_inputRev_x3f_2255_, v_subDir_x3f_2256_, v_a_2257_);
lean_dec_ref(v_a_2257_);
lean_dec_ref(v_lakeEnv_2249_);
return v_res_2260_;
}
}
lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(lean_object* v_a_2261_, lean_object* v_dep_2262_, uint8_t v_inherited_2263_, lean_object* v_lakeEnv_2264_, lean_object* v_wsDir_2265_, lean_object* v_name_2266_, lean_object* v_relPkgDir_2267_, lean_object* v_gitUrl_2268_, lean_object* v_remoteUrl_2269_, lean_object* v_inputRev_x3f_2270_, lean_object* v_subDir_x3f_2271_){
_start:
{
lean_object* v_pkgUrlMap_2273_; lean_object* v_name_2274_; lean_object* v_scope_2275_; lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2451_; 
v_pkgUrlMap_2273_ = lean_ctor_get(v_lakeEnv_2264_, 5);
v_name_2274_ = lean_ctor_get(v_dep_2262_, 0);
v_scope_2275_ = lean_ctor_get(v_dep_2262_, 1);
v_isSharedCheck_2451_ = !lean_is_exclusive(v_dep_2262_);
if (v_isSharedCheck_2451_ == 0)
{
lean_object* v_unused_2452_; lean_object* v_unused_2453_; lean_object* v_unused_2454_; 
v_unused_2452_ = lean_ctor_get(v_dep_2262_, 4);
lean_dec(v_unused_2452_);
v_unused_2453_ = lean_ctor_get(v_dep_2262_, 3);
lean_dec(v_unused_2453_);
v_unused_2454_ = lean_ctor_get(v_dep_2262_, 2);
lean_dec(v_unused_2454_);
v___x_2277_ = v_dep_2262_;
v_isShared_2278_ = v_isSharedCheck_2451_;
goto v_resetjp_2276_;
}
else
{
lean_inc(v_scope_2275_);
lean_inc(v_name_2274_);
lean_dec(v_dep_2262_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2451_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
lean_object* v___y_2280_; lean_object* v___y_2281_; lean_object* v___y_2282_; lean_object* v_a_2283_; lean_object* v___y_2292_; lean_object* v___y_2293_; lean_object* v___y_2294_; lean_object* v___y_2295_; lean_object* v___y_2296_; lean_object* v_val_2297_; lean_object* v___y_2313_; lean_object* v___y_2314_; lean_object* v___y_2315_; lean_object* v_a_2316_; lean_object* v___y_2348_; lean_object* v___y_2349_; lean_object* v___y_2350_; lean_object* v___y_2351_; lean_object* v___y_2352_; lean_object* v_val_2353_; lean_object* v___y_2369_; lean_object* v___y_2370_; lean_object* v___y_2371_; lean_object* v___y_2382_; lean_object* v_a_2383_; lean_object* v_gitDir_2386_; lean_object* v___y_2388_; lean_object* v___x_2449_; 
lean_inc_ref(v_relPkgDir_2267_);
lean_inc_ref(v_wsDir_2265_);
v_gitDir_2386_ = l_Lake_joinRelative(v_wsDir_2265_, v_relPkgDir_2267_);
v___x_2449_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgUrlMap_2273_, v_name_2274_);
if (lean_obj_tag(v___x_2449_) == 0)
{
v___y_2388_ = v_gitUrl_2268_;
goto v___jp_2387_;
}
else
{
lean_object* v_val_2450_; 
lean_dec_ref(v_gitUrl_2268_);
v_val_2450_ = lean_ctor_get(v___x_2449_, 0);
lean_inc(v_val_2450_);
lean_dec_ref_known(v___x_2449_, 1);
v___y_2388_ = v_val_2450_;
goto v___jp_2387_;
}
v___jp_2279_:
{
lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2288_; 
v___x_2284_ = l_Lake_defaultConfigFile;
v___x_2285_ = lean_box(0);
v___x_2286_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_2286_, 0, v_name_2274_);
lean_ctor_set(v___x_2286_, 1, v_scope_2275_);
lean_ctor_set(v___x_2286_, 2, v___x_2284_);
lean_ctor_set(v___x_2286_, 3, v___x_2285_);
lean_ctor_set(v___x_2286_, 4, v___y_2282_);
lean_ctor_set_uint8(v___x_2286_, sizeof(void*)*5, v_inherited_2263_);
if (v_isShared_2278_ == 0)
{
lean_ctor_set(v___x_2277_, 4, v___x_2286_);
lean_ctor_set(v___x_2277_, 3, v_a_2283_);
lean_ctor_set(v___x_2277_, 2, v_remoteUrl_2269_);
lean_ctor_set(v___x_2277_, 1, v___y_2280_);
lean_ctor_set(v___x_2277_, 0, v___y_2281_);
v___x_2288_ = v___x_2277_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v___y_2281_);
lean_ctor_set(v_reuseFailAlloc_2290_, 1, v___y_2280_);
lean_ctor_set(v_reuseFailAlloc_2290_, 2, v_remoteUrl_2269_);
lean_ctor_set(v_reuseFailAlloc_2290_, 3, v_a_2283_);
lean_ctor_set(v_reuseFailAlloc_2290_, 4, v___x_2286_);
v___x_2288_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
lean_object* v___x_2289_; 
v___x_2289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2289_, 0, v___x_2288_);
return v___x_2289_;
}
}
v___jp_2291_:
{
lean_object* v___x_2298_; uint8_t v___x_2299_; 
v___x_2298_ = lean_array_get_size(v___y_2295_);
v___x_2299_ = lean_nat_dec_lt(v___y_2296_, v___x_2298_);
if (v___x_2299_ == 0)
{
v___y_2280_ = v___y_2293_;
v___y_2281_ = v___y_2292_;
v___y_2282_ = v___y_2294_;
v_a_2283_ = v_val_2297_;
goto v___jp_2279_;
}
else
{
lean_object* v___x_2300_; size_t v___x_2301_; size_t v___x_2302_; lean_object* v___x_2303_; 
v___x_2300_ = lean_box(0);
v___x_2301_ = ((size_t)0ULL);
v___x_2302_ = lean_usize_of_nat(v___x_2298_);
v___x_2303_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_2295_, v___x_2301_, v___x_2302_, v___x_2300_, v_a_2261_);
if (lean_obj_tag(v___x_2303_) == 0)
{
lean_dec_ref_known(v___x_2303_, 1);
v___y_2280_ = v___y_2293_;
v___y_2281_ = v___y_2292_;
v___y_2282_ = v___y_2294_;
v_a_2283_ = v_val_2297_;
goto v___jp_2279_;
}
else
{
lean_object* v_a_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2311_; 
lean_dec_ref(v_val_2297_);
lean_dec_ref(v___y_2294_);
lean_dec_ref(v___y_2293_);
lean_dec_ref(v___y_2292_);
lean_del_object(v___x_2277_);
lean_dec_ref(v_scope_2275_);
lean_dec(v_name_2274_);
lean_dec_ref(v_remoteUrl_2269_);
v_a_2304_ = lean_ctor_get(v___x_2303_, 0);
v_isSharedCheck_2311_ = !lean_is_exclusive(v___x_2303_);
if (v_isSharedCheck_2311_ == 0)
{
v___x_2306_ = v___x_2303_;
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_a_2304_);
lean_dec(v___x_2303_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v___x_2309_; 
if (v_isShared_2307_ == 0)
{
v___x_2309_ = v___x_2306_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v_a_2304_);
v___x_2309_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
return v___x_2309_;
}
}
}
}
}
v___jp_2312_:
{
if (lean_obj_tag(v_a_2316_) == 1)
{
lean_object* v_val_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; 
lean_dec_ref(v___y_2315_);
lean_dec_ref(v_name_2266_);
v_val_2317_ = lean_ctor_get(v_a_2316_, 0);
lean_inc_n(v_val_2317_, 2);
lean_dec_ref_known(v_a_2316_, 1);
v___x_2318_ = l_Lake_defaultManifestFile;
v___x_2319_ = l_Lake_joinRelative(v_val_2317_, v___x_2318_);
v___x_2320_ = lean_unsigned_to_nat(0u);
v___x_2321_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_2322_ = l_Lake_Manifest_load(v___x_2319_);
if (lean_obj_tag(v___x_2322_) == 0)
{
lean_object* v_a_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2330_; 
v_a_2323_ = lean_ctor_get(v___x_2322_, 0);
v_isSharedCheck_2330_ = !lean_is_exclusive(v___x_2322_);
if (v_isSharedCheck_2330_ == 0)
{
v___x_2325_ = v___x_2322_;
v_isShared_2326_ = v_isSharedCheck_2330_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_a_2323_);
lean_dec(v___x_2322_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2330_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v___x_2328_; 
if (v_isShared_2326_ == 0)
{
lean_ctor_set_tag(v___x_2325_, 1);
v___x_2328_ = v___x_2325_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v_a_2323_);
v___x_2328_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
v___y_2292_ = v_val_2317_;
v___y_2293_ = v___y_2313_;
v___y_2294_ = v___y_2314_;
v___y_2295_ = v___x_2321_;
v___y_2296_ = v___x_2320_;
v_val_2297_ = v___x_2328_;
goto v___jp_2291_;
}
}
}
else
{
lean_object* v_a_2331_; lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2338_; 
v_a_2331_ = lean_ctor_get(v___x_2322_, 0);
v_isSharedCheck_2338_ = !lean_is_exclusive(v___x_2322_);
if (v_isSharedCheck_2338_ == 0)
{
v___x_2333_ = v___x_2322_;
v_isShared_2334_ = v_isSharedCheck_2338_;
goto v_resetjp_2332_;
}
else
{
lean_inc(v_a_2331_);
lean_dec(v___x_2322_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2338_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
lean_object* v___x_2336_; 
if (v_isShared_2334_ == 0)
{
lean_ctor_set_tag(v___x_2333_, 0);
v___x_2336_ = v___x_2333_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v_a_2331_);
v___x_2336_ = v_reuseFailAlloc_2337_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
v___y_2292_ = v_val_2317_;
v___y_2293_ = v___y_2313_;
v___y_2294_ = v___y_2314_;
v___y_2295_ = v___x_2321_;
v___y_2296_ = v___x_2320_;
v_val_2297_ = v___x_2336_;
goto v___jp_2291_;
}
}
}
}
else
{
lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; uint8_t v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; 
lean_dec(v_a_2316_);
lean_dec_ref(v___y_2314_);
lean_dec_ref(v___y_2313_);
lean_del_object(v___x_2277_);
lean_dec_ref(v_scope_2275_);
lean_dec(v_name_2274_);
lean_dec_ref(v_remoteUrl_2269_);
v___x_2339_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0));
v___x_2340_ = lean_string_append(v_name_2266_, v___x_2339_);
v___x_2341_ = lean_string_append(v___x_2340_, v___y_2315_);
lean_dec_ref(v___y_2315_);
v___x_2342_ = 3;
v___x_2343_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2343_, 0, v___x_2341_);
lean_ctor_set_uint8(v___x_2343_, sizeof(void*)*1, v___x_2342_);
lean_inc_ref(v_a_2261_);
v___x_2344_ = lean_apply_2(v_a_2261_, v___x_2343_, lean_box(0));
v___x_2345_ = lean_box(0);
v___x_2346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2346_, 0, v___x_2345_);
return v___x_2346_;
}
}
v___jp_2347_:
{
lean_object* v___x_2354_; uint8_t v___x_2355_; 
v___x_2354_ = lean_array_get_size(v___y_2352_);
v___x_2355_ = lean_nat_dec_lt(v___y_2348_, v___x_2354_);
if (v___x_2355_ == 0)
{
v___y_2313_ = v___y_2349_;
v___y_2314_ = v___y_2350_;
v___y_2315_ = v___y_2351_;
v_a_2316_ = v_val_2353_;
goto v___jp_2312_;
}
else
{
lean_object* v___x_2356_; size_t v___x_2357_; size_t v___x_2358_; lean_object* v___x_2359_; 
v___x_2356_ = lean_box(0);
v___x_2357_ = ((size_t)0ULL);
v___x_2358_ = lean_usize_of_nat(v___x_2354_);
v___x_2359_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_2352_, v___x_2357_, v___x_2358_, v___x_2356_, v_a_2261_);
if (lean_obj_tag(v___x_2359_) == 0)
{
lean_dec_ref_known(v___x_2359_, 1);
v___y_2313_ = v___y_2349_;
v___y_2314_ = v___y_2350_;
v___y_2315_ = v___y_2351_;
v_a_2316_ = v_val_2353_;
goto v___jp_2312_;
}
else
{
lean_object* v_a_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2367_; 
lean_dec(v_val_2353_);
lean_dec_ref(v___y_2351_);
lean_dec_ref(v___y_2350_);
lean_dec_ref(v___y_2349_);
lean_del_object(v___x_2277_);
lean_dec_ref(v_scope_2275_);
lean_dec(v_name_2274_);
lean_dec_ref(v_remoteUrl_2269_);
lean_dec_ref(v_name_2266_);
v_a_2360_ = lean_ctor_get(v___x_2359_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2359_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2362_ = v___x_2359_;
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_a_2360_);
lean_dec(v___x_2359_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v___x_2365_; 
if (v_isShared_2363_ == 0)
{
v___x_2365_ = v___x_2362_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v_a_2360_);
v___x_2365_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
return v___x_2365_;
}
}
}
}
}
v___jp_2368_:
{
lean_object* v___x_2372_; lean_object* v_pkgDir_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; uint8_t v___x_2378_; 
v___x_2372_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2372_, 0, v___y_2370_);
lean_ctor_set(v___x_2372_, 1, v___y_2369_);
lean_ctor_set(v___x_2372_, 2, v_inputRev_x3f_2270_);
lean_ctor_set(v___x_2372_, 3, v_subDir_x3f_2271_);
lean_inc_ref(v___y_2371_);
v_pkgDir_2373_ = l_Lake_joinRelative(v_wsDir_2265_, v___y_2371_);
v___x_2374_ = lean_unsigned_to_nat(0u);
v___x_2375_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_pkgDir_2373_);
v___x_2376_ = l_Lake_resolvePath(v_pkgDir_2373_);
v___x_2377_ = lean_string_utf8_byte_size(v___x_2376_);
v___x_2378_ = lean_nat_dec_eq(v___x_2377_, v___x_2374_);
if (v___x_2378_ == 0)
{
lean_object* v___x_2379_; 
v___x_2379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2379_, 0, v___x_2376_);
v___y_2348_ = v___x_2374_;
v___y_2349_ = v___y_2371_;
v___y_2350_ = v___x_2372_;
v___y_2351_ = v_pkgDir_2373_;
v___y_2352_ = v___x_2375_;
v_val_2353_ = v___x_2379_;
goto v___jp_2347_;
}
else
{
lean_object* v___x_2380_; 
lean_dec_ref(v___x_2376_);
v___x_2380_ = lean_box(0);
v___y_2348_ = v___x_2374_;
v___y_2349_ = v___y_2371_;
v___y_2350_ = v___x_2372_;
v___y_2351_ = v_pkgDir_2373_;
v___y_2352_ = v___x_2375_;
v_val_2353_ = v___x_2380_;
goto v___jp_2347_;
}
}
v___jp_2381_:
{
if (lean_obj_tag(v_subDir_x3f_2271_) == 1)
{
lean_object* v_val_2384_; lean_object* v___x_2385_; 
v_val_2384_ = lean_ctor_get(v_subDir_x3f_2271_, 0);
lean_inc(v_val_2384_);
v___x_2385_ = l_Lake_joinRelative(v_relPkgDir_2267_, v_val_2384_);
v___y_2369_ = v_a_2383_;
v___y_2370_ = v___y_2382_;
v___y_2371_ = v___x_2385_;
goto v___jp_2368_;
}
else
{
v___y_2369_ = v_a_2383_;
v___y_2370_ = v___y_2382_;
v___y_2371_ = v_relPkgDir_2267_;
goto v___jp_2368_;
}
}
v___jp_2387_:
{
lean_object* v___x_2389_; 
lean_inc(v_inputRev_x3f_2270_);
lean_inc_ref(v___y_2388_);
lean_inc_ref(v_gitDir_2386_);
lean_inc_ref(v_name_2266_);
v___x_2389_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(v_a_2261_, v_name_2266_, v_gitDir_2386_, v___y_2388_, v_inputRev_x3f_2270_);
if (lean_obj_tag(v___x_2389_) == 0)
{
lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2439_; 
v_isSharedCheck_2439_ = !lean_is_exclusive(v___x_2389_);
if (v_isSharedCheck_2439_ == 0)
{
lean_object* v_unused_2440_; 
v_unused_2440_ = lean_ctor_get(v___x_2389_, 0);
lean_dec(v_unused_2440_);
v___x_2391_ = v___x_2389_;
v_isShared_2392_ = v_isSharedCheck_2439_;
goto v_resetjp_2390_;
}
else
{
lean_dec(v___x_2389_);
v___x_2391_ = lean_box(0);
v_isShared_2392_ = v_isSharedCheck_2439_;
goto v_resetjp_2390_;
}
v_resetjp_2390_:
{
lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; 
v___x_2393_ = lean_unsigned_to_nat(0u);
v___x_2394_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_2395_ = l_Lake_GitRepo_getHeadRevision(v_gitDir_2386_, v___x_2394_);
if (lean_obj_tag(v___x_2395_) == 0)
{
lean_object* v_a_2396_; lean_object* v_a_2397_; lean_object* v___x_2398_; uint8_t v___x_2399_; 
lean_del_object(v___x_2391_);
v_a_2396_ = lean_ctor_get(v___x_2395_, 0);
lean_inc(v_a_2396_);
v_a_2397_ = lean_ctor_get(v___x_2395_, 1);
lean_inc(v_a_2397_);
lean_dec_ref_known(v___x_2395_, 2);
v___x_2398_ = lean_array_get_size(v_a_2397_);
v___x_2399_ = lean_nat_dec_lt(v___x_2393_, v___x_2398_);
if (v___x_2399_ == 0)
{
lean_dec(v_a_2397_);
v___y_2382_ = v___y_2388_;
v_a_2383_ = v_a_2396_;
goto v___jp_2381_;
}
else
{
lean_object* v___x_2400_; size_t v___x_2401_; size_t v___x_2402_; lean_object* v___x_2403_; 
v___x_2400_ = lean_box(0);
v___x_2401_ = ((size_t)0ULL);
v___x_2402_ = lean_usize_of_nat(v___x_2398_);
v___x_2403_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_2397_, v___x_2401_, v___x_2402_, v___x_2400_, v_a_2261_);
lean_dec(v_a_2397_);
if (lean_obj_tag(v___x_2403_) == 0)
{
lean_dec_ref_known(v___x_2403_, 1);
v___y_2382_ = v___y_2388_;
v_a_2383_ = v_a_2396_;
goto v___jp_2381_;
}
else
{
lean_object* v_a_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2411_; 
lean_dec(v_a_2396_);
lean_dec_ref(v___y_2388_);
lean_del_object(v___x_2277_);
lean_dec_ref(v_scope_2275_);
lean_dec(v_name_2274_);
lean_dec(v_subDir_x3f_2271_);
lean_dec(v_inputRev_x3f_2270_);
lean_dec_ref(v_remoteUrl_2269_);
lean_dec_ref(v_relPkgDir_2267_);
lean_dec_ref(v_name_2266_);
lean_dec_ref(v_wsDir_2265_);
v_a_2404_ = lean_ctor_get(v___x_2403_, 0);
v_isSharedCheck_2411_ = !lean_is_exclusive(v___x_2403_);
if (v_isSharedCheck_2411_ == 0)
{
v___x_2406_ = v___x_2403_;
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
else
{
lean_inc(v_a_2404_);
lean_dec(v___x_2403_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
lean_object* v___x_2409_; 
if (v_isShared_2407_ == 0)
{
v___x_2409_ = v___x_2406_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v_a_2404_);
v___x_2409_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
return v___x_2409_;
}
}
}
}
}
else
{
lean_object* v_a_2412_; lean_object* v___x_2413_; uint8_t v___x_2414_; 
lean_dec_ref(v___y_2388_);
lean_del_object(v___x_2277_);
lean_dec_ref(v_scope_2275_);
lean_dec(v_name_2274_);
lean_dec(v_subDir_x3f_2271_);
lean_dec(v_inputRev_x3f_2270_);
lean_dec_ref(v_remoteUrl_2269_);
lean_dec_ref(v_relPkgDir_2267_);
lean_dec_ref(v_name_2266_);
lean_dec_ref(v_wsDir_2265_);
v_a_2412_ = lean_ctor_get(v___x_2395_, 1);
lean_inc(v_a_2412_);
lean_dec_ref_known(v___x_2395_, 2);
v___x_2413_ = lean_array_get_size(v_a_2412_);
v___x_2414_ = lean_nat_dec_lt(v___x_2393_, v___x_2413_);
if (v___x_2414_ == 0)
{
lean_object* v___x_2415_; lean_object* v___x_2417_; 
lean_dec(v_a_2412_);
v___x_2415_ = lean_box(0);
if (v_isShared_2392_ == 0)
{
lean_ctor_set_tag(v___x_2391_, 1);
lean_ctor_set(v___x_2391_, 0, v___x_2415_);
v___x_2417_ = v___x_2391_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v___x_2415_);
v___x_2417_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
return v___x_2417_;
}
}
else
{
lean_object* v___x_2419_; size_t v___x_2420_; size_t v___x_2421_; lean_object* v___x_2422_; 
lean_del_object(v___x_2391_);
v___x_2419_ = lean_box(0);
v___x_2420_ = ((size_t)0ULL);
v___x_2421_ = lean_usize_of_nat(v___x_2413_);
v___x_2422_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_2412_, v___x_2420_, v___x_2421_, v___x_2419_, v_a_2261_);
lean_dec(v_a_2412_);
if (lean_obj_tag(v___x_2422_) == 0)
{
lean_object* v___x_2424_; uint8_t v_isShared_2425_; uint8_t v_isSharedCheck_2429_; 
v_isSharedCheck_2429_ = !lean_is_exclusive(v___x_2422_);
if (v_isSharedCheck_2429_ == 0)
{
lean_object* v_unused_2430_; 
v_unused_2430_ = lean_ctor_get(v___x_2422_, 0);
lean_dec(v_unused_2430_);
v___x_2424_ = v___x_2422_;
v_isShared_2425_ = v_isSharedCheck_2429_;
goto v_resetjp_2423_;
}
else
{
lean_dec(v___x_2422_);
v___x_2424_ = lean_box(0);
v_isShared_2425_ = v_isSharedCheck_2429_;
goto v_resetjp_2423_;
}
v_resetjp_2423_:
{
lean_object* v___x_2427_; 
if (v_isShared_2425_ == 0)
{
lean_ctor_set_tag(v___x_2424_, 1);
lean_ctor_set(v___x_2424_, 0, v___x_2419_);
v___x_2427_ = v___x_2424_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v___x_2419_);
v___x_2427_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
return v___x_2427_;
}
}
}
else
{
lean_object* v_a_2431_; lean_object* v___x_2433_; uint8_t v_isShared_2434_; uint8_t v_isSharedCheck_2438_; 
v_a_2431_ = lean_ctor_get(v___x_2422_, 0);
v_isSharedCheck_2438_ = !lean_is_exclusive(v___x_2422_);
if (v_isSharedCheck_2438_ == 0)
{
v___x_2433_ = v___x_2422_;
v_isShared_2434_ = v_isSharedCheck_2438_;
goto v_resetjp_2432_;
}
else
{
lean_inc(v_a_2431_);
lean_dec(v___x_2422_);
v___x_2433_ = lean_box(0);
v_isShared_2434_ = v_isSharedCheck_2438_;
goto v_resetjp_2432_;
}
v_resetjp_2432_:
{
lean_object* v___x_2436_; 
if (v_isShared_2434_ == 0)
{
v___x_2436_ = v___x_2433_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v_a_2431_);
v___x_2436_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
return v___x_2436_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2441_; lean_object* v___x_2443_; uint8_t v_isShared_2444_; uint8_t v_isSharedCheck_2448_; 
lean_dec_ref(v___y_2388_);
lean_dec_ref(v_gitDir_2386_);
lean_del_object(v___x_2277_);
lean_dec_ref(v_scope_2275_);
lean_dec(v_name_2274_);
lean_dec(v_subDir_x3f_2271_);
lean_dec(v_inputRev_x3f_2270_);
lean_dec_ref(v_remoteUrl_2269_);
lean_dec_ref(v_relPkgDir_2267_);
lean_dec_ref(v_name_2266_);
lean_dec_ref(v_wsDir_2265_);
v_a_2441_ = lean_ctor_get(v___x_2389_, 0);
v_isSharedCheck_2448_ = !lean_is_exclusive(v___x_2389_);
if (v_isSharedCheck_2448_ == 0)
{
v___x_2443_ = v___x_2389_;
v_isShared_2444_ = v_isSharedCheck_2448_;
goto v_resetjp_2442_;
}
else
{
lean_inc(v_a_2441_);
lean_dec(v___x_2389_);
v___x_2443_ = lean_box(0);
v_isShared_2444_ = v_isSharedCheck_2448_;
goto v_resetjp_2442_;
}
v_resetjp_2442_:
{
lean_object* v___x_2446_; 
if (v_isShared_2444_ == 0)
{
v___x_2446_ = v___x_2443_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2447_; 
v_reuseFailAlloc_2447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2447_, 0, v_a_2441_);
v___x_2446_ = v_reuseFailAlloc_2447_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
return v___x_2446_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2261_ = stack[0].m_obj;
lean_object* v_dep_2262_ = stack[1].m_obj;
uint8_t v_inherited_2263_ = stack[2].m_num;
lean_object* v_lakeEnv_2264_ = stack[3].m_obj;
lean_object* v_wsDir_2265_ = stack[4].m_obj;
lean_object* v_name_2266_ = stack[5].m_obj;
lean_object* v_relPkgDir_2267_ = stack[6].m_obj;
lean_object* v_gitUrl_2268_ = stack[7].m_obj;
lean_object* v_remoteUrl_2269_ = stack[8].m_obj;
lean_object* v_inputRev_x3f_2270_ = stack[9].m_obj;
lean_object* v_subDir_x3f_2271_ = stack[10].m_obj;
lean_object* v_res_2455_;
v_res_2455_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(v_a_2261_, v_dep_2262_, v_inherited_2263_, v_lakeEnv_2264_, v_wsDir_2265_, v_name_2266_, v_relPkgDir_2267_, v_gitUrl_2268_, v_remoteUrl_2269_, v_inputRev_x3f_2270_, v_subDir_x3f_2271_);
stack->m_obj
 = v_res_2455_;
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0___boxed(lean_object* v_a_2456_, lean_object* v_dep_2457_, lean_object* v_inherited_2458_, lean_object* v_lakeEnv_2459_, lean_object* v_wsDir_2460_, lean_object* v_name_2461_, lean_object* v_relPkgDir_2462_, lean_object* v_gitUrl_2463_, lean_object* v_remoteUrl_2464_, lean_object* v_inputRev_x3f_2465_, lean_object* v_subDir_x3f_2466_, lean_object* v_a_2467_){
_start:
{
uint8_t v_inherited_boxed_2468_; lean_object* v_res_2469_; 
v_inherited_boxed_2468_ = lean_unbox(v_inherited_2458_);
v_res_2469_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(v_a_2456_, v_dep_2457_, v_inherited_boxed_2468_, v_lakeEnv_2459_, v_wsDir_2460_, v_name_2461_, v_relPkgDir_2462_, v_gitUrl_2463_, v_remoteUrl_2464_, v_inputRev_x3f_2465_, v_subDir_x3f_2466_);
lean_dec_ref(v_lakeEnv_2459_);
lean_dec_ref(v_a_2456_);
return v_res_2469_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(lean_object* v_ver_2473_, lean_object* v_as_2474_, size_t v_sz_2475_, size_t v_i_2476_, lean_object* v_b_2477_){
_start:
{
uint8_t v___x_2478_; 
v___x_2478_ = lean_usize_dec_lt(v_i_2476_, v_sz_2475_);
if (v___x_2478_ == 0)
{
lean_inc_ref(v_b_2477_);
return v_b_2477_;
}
else
{
lean_object* v_a_2479_; lean_object* v_version_2480_; lean_object* v___x_2481_; uint8_t v___x_2482_; 
v_a_2479_ = lean_array_uget_borrowed(v_as_2474_, v_i_2476_);
v_version_2480_ = lean_ctor_get(v_a_2479_, 0);
v___x_2481_ = lean_box(0);
v___x_2482_ = l_Lake_VerRange_test(v_ver_2473_, v_version_2480_);
if (v___x_2482_ == 0)
{
lean_object* v___x_2483_; size_t v___x_2484_; size_t v___x_2485_; 
v___x_2483_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___closed__0));
v___x_2484_ = ((size_t)1ULL);
v___x_2485_ = lean_usize_add(v_i_2476_, v___x_2484_);
v_i_2476_ = v___x_2485_;
v_b_2477_ = v___x_2483_;
goto _start;
}
else
{
lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; 
lean_inc(v_a_2479_);
v___x_2487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2487_, 0, v_a_2479_);
v___x_2488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2488_, 0, v___x_2487_);
v___x_2489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2489_, 0, v___x_2488_);
lean_ctor_set(v___x_2489_, 1, v___x_2481_);
return v___x_2489_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_ver_2473_ = stack[0].m_obj;
lean_object* v_as_2474_ = stack[1].m_obj;
size_t v_sz_2475_ = stack[2].m_num;
size_t v_i_2476_ = stack[3].m_num;
lean_object* v_b_2477_ = stack[4].m_obj;
lean_object* v_res_2490_;
v_res_2490_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(v_ver_2473_, v_as_2474_, v_sz_2475_, v_i_2476_, v_b_2477_);
stack->m_obj
 = v_res_2490_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___boxed(lean_object* v_ver_2491_, lean_object* v_as_2492_, lean_object* v_sz_2493_, lean_object* v_i_2494_, lean_object* v_b_2495_){
_start:
{
size_t v_sz_boxed_2496_; size_t v_i_boxed_2497_; lean_object* v_res_2498_; 
v_sz_boxed_2496_ = lean_unbox_usize(v_sz_2493_);
lean_dec(v_sz_2493_);
v_i_boxed_2497_ = lean_unbox_usize(v_i_2494_);
lean_dec(v_i_2494_);
v_res_2498_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(v_ver_2491_, v_as_2492_, v_sz_boxed_2496_, v_i_boxed_2497_, v_b_2495_);
lean_dec_ref(v_b_2495_);
lean_dec_ref(v_as_2492_);
lean_dec_ref(v_ver_2491_);
return v_res_2498_;
}
}
lean_object* l_Lake_Dependency_materialize(lean_object* v_dep_2508_, uint8_t v_inherited_2509_, lean_object* v_lakeEnv_2510_, lean_object* v_wsDir_2511_, lean_object* v_relPkgsDir_2512_, lean_object* v_relParentDir_2513_, lean_object* v_a_2514_){
_start:
{
lean_object* v___y_2517_; lean_object* v___y_2518_; lean_object* v___y_2528_; lean_object* v___y_2529_; lean_object* v___y_2530_; lean_object* v___y_2531_; lean_object* v___y_2532_; lean_object* v___y_2533_; lean_object* v___y_2537_; lean_object* v___y_2538_; lean_object* v___y_2539_; lean_object* v___y_2540_; lean_object* v___y_2541_; lean_object* v_a_2542_; lean_object* v_a_2546_; lean_object* v_name_2553_; lean_object* v_scope_2554_; lean_object* v_version_2555_; lean_object* v_src_x3f_2556_; lean_object* v___y_2558_; lean_object* v___y_2559_; lean_object* v___y_2560_; lean_object* v___y_2561_; lean_object* v_a_2562_; lean_object* v___y_2569_; lean_object* v___y_2570_; lean_object* v___y_2571_; lean_object* v___y_2572_; lean_object* v___y_2573_; lean_object* v___y_2574_; lean_object* v_val_2575_; lean_object* v___y_2591_; lean_object* v___y_2592_; lean_object* v___y_2593_; lean_object* v___y_2594_; lean_object* v___y_2595_; lean_object* v_a_2596_; lean_object* v___y_2628_; lean_object* v___y_2629_; lean_object* v___y_2630_; lean_object* v___y_2631_; lean_object* v___y_2632_; lean_object* v___y_2633_; lean_object* v___y_2634_; lean_object* v_val_2635_; 
v_name_2553_ = lean_ctor_get(v_dep_2508_, 0);
v_scope_2554_ = lean_ctor_get(v_dep_2508_, 1);
v_version_2555_ = lean_ctor_get(v_dep_2508_, 2);
v_src_x3f_2556_ = lean_ctor_get(v_dep_2508_, 3);
lean_inc(v_src_x3f_2556_);
if (lean_obj_tag(v_src_x3f_2556_) == 1)
{
lean_object* v_val_2650_; lean_object* v___x_2652_; uint8_t v_isShared_2653_; uint8_t v_isSharedCheck_2700_; 
v_val_2650_ = lean_ctor_get(v_src_x3f_2556_, 0);
v_isSharedCheck_2700_ = !lean_is_exclusive(v_src_x3f_2556_);
if (v_isSharedCheck_2700_ == 0)
{
v___x_2652_ = v_src_x3f_2556_;
v_isShared_2653_ = v_isSharedCheck_2700_;
goto v_resetjp_2651_;
}
else
{
lean_inc(v_val_2650_);
lean_dec(v_src_x3f_2556_);
v___x_2652_ = lean_box(0);
v_isShared_2653_ = v_isSharedCheck_2700_;
goto v_resetjp_2651_;
}
v_resetjp_2651_:
{
if (lean_obj_tag(v_val_2650_) == 0)
{
lean_object* v_dir_2654_; uint8_t v_copy_2655_; lean_object* v___x_2657_; uint8_t v_isShared_2658_; uint8_t v_isSharedCheck_2687_; 
lean_inc_ref(v_scope_2554_);
lean_inc(v_name_2553_);
lean_dec_ref(v_lakeEnv_2510_);
lean_dec_ref(v_dep_2508_);
v_dir_2654_ = lean_ctor_get(v_val_2650_, 0);
v_copy_2655_ = lean_ctor_get_uint8(v_val_2650_, sizeof(void*)*1);
v_isSharedCheck_2687_ = !lean_is_exclusive(v_val_2650_);
if (v_isSharedCheck_2687_ == 0)
{
v___x_2657_ = v_val_2650_;
v_isShared_2658_ = v_isSharedCheck_2687_;
goto v_resetjp_2656_;
}
else
{
lean_inc(v_dir_2654_);
lean_dec(v_val_2650_);
v___x_2657_ = lean_box(0);
v_isShared_2658_ = v_isSharedCheck_2687_;
goto v_resetjp_2656_;
}
v_resetjp_2656_:
{
lean_object* v_relSrc_2659_; lean_object* v_a_2661_; 
v_relSrc_2659_ = l_Lake_joinRelative(v_relParentDir_2513_, v_dir_2654_);
if (v_copy_2655_ == 0)
{
lean_dec_ref(v_relPkgsDir_2512_);
lean_inc_ref(v_relSrc_2659_);
v_a_2661_ = v_relSrc_2659_;
goto v___jp_2660_;
}
else
{
uint8_t v___x_2678_; lean_object* v___x_2679_; lean_object* v_relDst_2680_; lean_object* v_dst_2681_; lean_object* v___x_2682_; 
v___x_2678_ = 0;
lean_inc(v_name_2553_);
v___x_2679_ = l_Lean_Name_toString(v_name_2553_, v___x_2678_);
v_relDst_2680_ = l_Lake_joinRelative(v_relPkgsDir_2512_, v___x_2679_);
lean_inc_ref(v_relDst_2680_);
lean_inc_ref(v_wsDir_2511_);
v_dst_2681_ = l_Lake_joinRelative(v_wsDir_2511_, v_relDst_2680_);
v___x_2682_ = l_Lake_removeDirAllIfExists(v_dst_2681_);
if (lean_obj_tag(v___x_2682_) == 0)
{
lean_object* v_src_2683_; lean_object* v___x_2684_; 
lean_dec_ref_known(v___x_2682_, 1);
lean_inc_ref(v_relSrc_2659_);
lean_inc_ref(v_wsDir_2511_);
v_src_2683_ = l_Lake_joinRelative(v_wsDir_2511_, v_relSrc_2659_);
v___x_2684_ = l_Lake_copyDirAll(v_src_2683_, v_dst_2681_);
if (lean_obj_tag(v___x_2684_) == 0)
{
lean_dec_ref_known(v___x_2684_, 1);
v_a_2661_ = v_relDst_2680_;
goto v___jp_2660_;
}
else
{
lean_object* v_a_2685_; 
lean_dec_ref(v_relDst_2680_);
lean_dec_ref(v_relSrc_2659_);
lean_del_object(v___x_2657_);
lean_del_object(v___x_2652_);
lean_dec_ref(v_scope_2554_);
lean_dec(v_name_2553_);
lean_dec_ref(v_wsDir_2511_);
v_a_2685_ = lean_ctor_get(v___x_2684_, 0);
lean_inc(v_a_2685_);
lean_dec_ref_known(v___x_2684_, 1);
v_a_2546_ = v_a_2685_;
goto v___jp_2545_;
}
}
else
{
lean_object* v_a_2686_; 
lean_dec_ref(v_dst_2681_);
lean_dec_ref(v_relDst_2680_);
lean_dec_ref(v_relSrc_2659_);
lean_del_object(v___x_2657_);
lean_del_object(v___x_2652_);
lean_dec_ref(v_scope_2554_);
lean_dec(v_name_2553_);
lean_dec_ref(v_wsDir_2511_);
v_a_2686_ = lean_ctor_get(v___x_2682_, 0);
lean_inc(v_a_2686_);
lean_dec_ref_known(v___x_2682_, 1);
v_a_2546_ = v_a_2686_;
goto v___jp_2545_;
}
}
v___jp_2660_:
{
uint8_t v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2666_; 
v___x_2662_ = 0;
lean_inc(v_name_2553_);
v___x_2663_ = l_Lean_Name_toString(v_name_2553_, v___x_2662_);
v___x_2664_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
if (v_isShared_2658_ == 0)
{
lean_ctor_set(v___x_2657_, 0, v_relSrc_2659_);
v___x_2666_ = v___x_2657_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v_relSrc_2659_);
lean_ctor_set_uint8(v_reuseFailAlloc_2677_, sizeof(void*)*1, v_copy_2655_);
v___x_2666_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
lean_object* v_pkgDir_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; uint8_t v___x_2672_; 
lean_inc_ref(v_a_2661_);
v_pkgDir_2667_ = l_Lake_joinRelative(v_wsDir_2511_, v_a_2661_);
v___x_2668_ = lean_unsigned_to_nat(0u);
v___x_2669_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_pkgDir_2667_);
v___x_2670_ = l_Lake_resolvePath(v_pkgDir_2667_);
v___x_2671_ = lean_string_utf8_byte_size(v___x_2670_);
v___x_2672_ = lean_nat_dec_eq(v___x_2671_, v___x_2668_);
if (v___x_2672_ == 0)
{
lean_object* v___x_2674_; 
if (v_isShared_2653_ == 0)
{
lean_ctor_set(v___x_2652_, 0, v___x_2670_);
v___x_2674_ = v___x_2652_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v___x_2670_);
v___x_2674_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
v___y_2628_ = v___x_2664_;
v___y_2629_ = v___x_2669_;
v___y_2630_ = v___x_2663_;
v___y_2631_ = v_pkgDir_2667_;
v___y_2632_ = v___x_2668_;
v___y_2633_ = v___x_2666_;
v___y_2634_ = v_a_2661_;
v_val_2635_ = v___x_2674_;
goto v___jp_2627_;
}
}
else
{
lean_object* v___x_2676_; 
lean_dec_ref(v___x_2670_);
lean_del_object(v___x_2652_);
v___x_2676_ = lean_box(0);
v___y_2628_ = v___x_2664_;
v___y_2629_ = v___x_2669_;
v___y_2630_ = v___x_2663_;
v___y_2631_ = v_pkgDir_2667_;
v___y_2632_ = v___x_2668_;
v___y_2633_ = v___x_2666_;
v___y_2634_ = v_a_2661_;
v_val_2635_ = v___x_2676_;
goto v___jp_2627_;
}
}
}
}
}
else
{
lean_object* v_url_2688_; lean_object* v_rev_2689_; lean_object* v_subDir_2690_; lean_object* v___y_2692_; lean_object* v___x_2697_; 
lean_del_object(v___x_2652_);
lean_dec_ref(v_relParentDir_2513_);
v_url_2688_ = lean_ctor_get(v_val_2650_, 0);
lean_inc_ref_n(v_url_2688_, 2);
v_rev_2689_ = lean_ctor_get(v_val_2650_, 1);
lean_inc(v_rev_2689_);
v_subDir_2690_ = lean_ctor_get(v_val_2650_, 2);
lean_inc(v_subDir_2690_);
lean_dec_ref_known(v_val_2650_, 3);
v___x_2697_ = l_Lake_Git_filterUrl_x3f(v_url_2688_);
if (lean_obj_tag(v___x_2697_) == 0)
{
lean_object* v___x_2698_; 
v___x_2698_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___y_2692_ = v___x_2698_;
goto v___jp_2691_;
}
else
{
lean_object* v_val_2699_; 
v_val_2699_ = lean_ctor_get(v___x_2697_, 0);
lean_inc(v_val_2699_);
lean_dec_ref_known(v___x_2697_, 1);
v___y_2692_ = v_val_2699_;
goto v___jp_2691_;
}
v___jp_2691_:
{
uint8_t v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; 
v___x_2693_ = 0;
lean_inc(v_name_2553_);
v___x_2694_ = l_Lean_Name_toString(v_name_2553_, v___x_2693_);
lean_inc_ref(v___x_2694_);
v___x_2695_ = l_Lake_joinRelative(v_relPkgsDir_2512_, v___x_2694_);
v___x_2696_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(v_a_2514_, v_dep_2508_, v_inherited_2509_, v_lakeEnv_2510_, v_wsDir_2511_, v___x_2694_, v___x_2695_, v_url_2688_, v___y_2692_, v_rev_2689_, v_subDir_2690_);
lean_dec_ref(v_lakeEnv_2510_);
return v___x_2696_;
}
}
}
}
else
{
lean_object* v___x_2701_; lean_object* v___x_2702_; uint8_t v___x_2703_; 
lean_dec(v_src_x3f_2556_);
lean_dec_ref(v_relParentDir_2513_);
v___x_2701_ = lean_string_utf8_byte_size(v_scope_2554_);
v___x_2702_ = lean_unsigned_to_nat(0u);
v___x_2703_ = lean_nat_dec_eq(v___x_2701_, v___x_2702_);
if (v___x_2703_ == 0)
{
lean_object* v___x_2704_; lean_object* v___y_2706_; lean_object* v___y_2722_; lean_object* v___y_2723_; lean_object* v___y_2724_; lean_object* v___y_2725_; lean_object* v___y_2726_; lean_object* v___y_2727_; lean_object* v_a_2728_; lean_object* v___y_2772_; lean_object* v___y_2773_; lean_object* v___y_2774_; lean_object* v___y_2775_; lean_object* v___y_2776_; lean_object* v___y_2777_; lean_object* v_fst_2778_; lean_object* v_snd_2779_; lean_object* v_a_2795_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v_fst_2902_; lean_object* v_snd_2903_; 
lean_inc(v_name_2553_);
v___x_2704_ = l_Lean_Name_toString(v_name_2553_, v___x_2703_);
v___x_2899_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_scope_2554_);
lean_inc_ref(v_lakeEnv_2510_);
v___x_2900_ = l_Lake_Reservoir_fetchPkg_x3f(v_lakeEnv_2510_, v_scope_2554_, v___x_2704_, v___x_2899_);
if (lean_obj_tag(v___x_2900_) == 0)
{
lean_object* v_a_2918_; lean_object* v_a_2919_; lean_object* v___x_2920_; 
v_a_2918_ = lean_ctor_get(v___x_2900_, 0);
lean_inc(v_a_2918_);
v_a_2919_ = lean_ctor_get(v___x_2900_, 1);
lean_inc(v_a_2919_);
lean_dec_ref_known(v___x_2900_, 2);
v___x_2920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2920_, 0, v_a_2918_);
v_fst_2902_ = v___x_2920_;
v_snd_2903_ = v_a_2919_;
goto v___jp_2901_;
}
else
{
lean_object* v_a_2921_; lean_object* v_a_2922_; lean_object* v___x_2923_; 
v_a_2921_ = lean_ctor_get(v___x_2900_, 0);
lean_inc(v_a_2921_);
v_a_2922_ = lean_ctor_get(v___x_2900_, 1);
lean_inc(v_a_2922_);
lean_dec_ref_known(v___x_2900_, 2);
v___x_2923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2923_, 0, v_a_2921_);
v_fst_2902_ = v___x_2923_;
v_snd_2903_ = v_a_2922_;
goto v___jp_2901_;
}
v___jp_2705_:
{
lean_object* v_toString_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; uint8_t v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; 
v_toString_2707_ = lean_ctor_get(v___y_2706_, 0);
lean_inc_ref(v_toString_2707_);
lean_dec_ref(v___y_2706_);
v___x_2708_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
v___x_2709_ = lean_string_append(v_scope_2554_, v___x_2708_);
v___x_2710_ = lean_string_append(v___x_2709_, v___x_2704_);
lean_dec_ref(v___x_2704_);
v___x_2711_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__1));
v___x_2712_ = lean_string_append(v___x_2710_, v___x_2711_);
v___x_2713_ = lean_string_append(v___x_2712_, v_toString_2707_);
lean_dec_ref(v_toString_2707_);
v___x_2714_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__2));
v___x_2715_ = lean_string_append(v___x_2713_, v___x_2714_);
v___x_2716_ = 3;
v___x_2717_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2717_, 0, v___x_2715_);
lean_ctor_set_uint8(v___x_2717_, sizeof(void*)*1, v___x_2716_);
lean_inc_ref(v_a_2514_);
v___x_2718_ = lean_apply_2(v_a_2514_, v___x_2717_, lean_box(0));
v___x_2719_ = lean_box(0);
v___x_2720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2720_, 0, v___x_2719_);
return v___x_2720_;
}
v___jp_2721_:
{
if (lean_obj_tag(v_a_2728_) == 0)
{
lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2744_; 
lean_inc_ref(v_scope_2554_);
lean_dec_ref(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec_ref(v___y_2725_);
lean_dec(v___y_2724_);
lean_dec(v___y_2723_);
lean_dec_ref(v___y_2722_);
lean_dec_ref(v_wsDir_2511_);
lean_dec_ref(v_lakeEnv_2510_);
lean_dec_ref(v_dep_2508_);
v_isSharedCheck_2744_ = !lean_is_exclusive(v_a_2728_);
if (v_isSharedCheck_2744_ == 0)
{
lean_object* v_unused_2745_; 
v_unused_2745_ = lean_ctor_get(v_a_2728_, 0);
lean_dec(v_unused_2745_);
v___x_2730_ = v_a_2728_;
v_isShared_2731_ = v_isSharedCheck_2744_;
goto v_resetjp_2729_;
}
else
{
lean_dec(v_a_2728_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2744_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; uint8_t v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2742_; 
v___x_2732_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
v___x_2733_ = lean_string_append(v_scope_2554_, v___x_2732_);
v___x_2734_ = lean_string_append(v___x_2733_, v___x_2704_);
lean_dec_ref(v___x_2704_);
v___x_2735_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__3));
v___x_2736_ = lean_string_append(v___x_2734_, v___x_2735_);
v___x_2737_ = 3;
v___x_2738_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2738_, 0, v___x_2736_);
lean_ctor_set_uint8(v___x_2738_, sizeof(void*)*1, v___x_2737_);
lean_inc_ref(v_a_2514_);
v___x_2739_ = lean_apply_2(v_a_2514_, v___x_2738_, lean_box(0));
v___x_2740_ = lean_box(0);
if (v_isShared_2731_ == 0)
{
lean_ctor_set_tag(v___x_2730_, 1);
lean_ctor_set(v___x_2730_, 0, v___x_2740_);
v___x_2742_ = v___x_2730_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v___x_2740_);
v___x_2742_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
return v___x_2742_;
}
}
}
else
{
lean_object* v_a_2746_; lean_object* v___x_2747_; size_t v_sz_2748_; size_t v___x_2749_; lean_object* v___x_2750_; lean_object* v_fst_2751_; 
v_a_2746_ = lean_ctor_get(v_a_2728_, 0);
lean_inc(v_a_2746_);
lean_dec_ref_known(v_a_2728_, 1);
v___x_2747_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___closed__0));
v_sz_2748_ = lean_array_size(v_a_2746_);
v___x_2749_ = ((size_t)0ULL);
v___x_2750_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(v___y_2722_, v_a_2746_, v_sz_2748_, v___x_2749_, v___x_2747_);
lean_dec(v_a_2746_);
v_fst_2751_ = lean_ctor_get(v___x_2750_, 0);
lean_inc(v_fst_2751_);
lean_dec_ref(v___x_2750_);
if (lean_obj_tag(v_fst_2751_) == 0)
{
lean_inc_ref(v_scope_2554_);
lean_dec_ref(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec_ref(v___y_2725_);
lean_dec(v___y_2724_);
lean_dec(v___y_2723_);
lean_dec_ref(v_wsDir_2511_);
lean_dec_ref(v_lakeEnv_2510_);
lean_dec_ref(v_dep_2508_);
v___y_2706_ = v___y_2722_;
goto v___jp_2705_;
}
else
{
lean_object* v_val_2752_; 
v_val_2752_ = lean_ctor_get(v_fst_2751_, 0);
lean_inc(v_val_2752_);
lean_dec_ref_known(v_fst_2751_, 1);
if (lean_obj_tag(v_val_2752_) == 1)
{
lean_object* v_val_2753_; lean_object* v_version_2754_; lean_object* v_revision_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; uint8_t v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; 
lean_dec_ref(v___y_2722_);
v_val_2753_ = lean_ctor_get(v_val_2752_, 0);
lean_inc(v_val_2753_);
lean_dec_ref_known(v_val_2752_, 1);
v_version_2754_ = lean_ctor_get(v_val_2753_, 0);
lean_inc_ref(v_version_2754_);
v_revision_2755_ = lean_ctor_get(v_val_2753_, 1);
lean_inc_ref(v_revision_2755_);
lean_dec(v_val_2753_);
v___x_2756_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
lean_inc_ref(v_scope_2554_);
v___x_2757_ = lean_string_append(v_scope_2554_, v___x_2756_);
v___x_2758_ = lean_string_append(v___x_2757_, v___x_2704_);
lean_dec_ref(v___x_2704_);
v___x_2759_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__4));
v___x_2760_ = lean_string_append(v___x_2758_, v___x_2759_);
v___x_2761_ = l_Lake_StdVer_toString(v_version_2754_);
v___x_2762_ = lean_string_append(v___x_2760_, v___x_2761_);
lean_dec_ref(v___x_2761_);
v___x_2763_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__5));
v___x_2764_ = lean_string_append(v___x_2762_, v___x_2763_);
v___x_2765_ = lean_string_append(v___x_2764_, v_revision_2755_);
v___x_2766_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__6));
v___x_2767_ = lean_string_append(v___x_2765_, v___x_2766_);
v___x_2768_ = 1;
v___x_2769_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2769_, 0, v___x_2767_);
lean_ctor_set_uint8(v___x_2769_, sizeof(void*)*1, v___x_2768_);
lean_inc_ref(v_a_2514_);
v___x_2770_ = lean_apply_2(v_a_2514_, v___x_2769_, lean_box(0));
v___y_2537_ = v___y_2723_;
v___y_2538_ = v___y_2724_;
v___y_2539_ = v___y_2725_;
v___y_2540_ = v___y_2726_;
v___y_2541_ = v___y_2727_;
v_a_2542_ = v_revision_2755_;
goto v___jp_2536_;
}
else
{
lean_inc_ref(v_scope_2554_);
lean_dec(v_val_2752_);
lean_dec_ref(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec_ref(v___y_2725_);
lean_dec(v___y_2724_);
lean_dec(v___y_2723_);
lean_dec_ref(v_wsDir_2511_);
lean_dec_ref(v_lakeEnv_2510_);
lean_dec_ref(v_dep_2508_);
v___y_2706_ = v___y_2722_;
goto v___jp_2705_;
}
}
}
}
v___jp_2771_:
{
lean_object* v___x_2780_; uint8_t v___x_2781_; 
v___x_2780_ = lean_array_get_size(v_snd_2779_);
v___x_2781_ = lean_nat_dec_lt(v___x_2702_, v___x_2780_);
if (v___x_2781_ == 0)
{
lean_dec_ref(v_snd_2779_);
v___y_2722_ = v___y_2772_;
v___y_2723_ = v___y_2773_;
v___y_2724_ = v___y_2774_;
v___y_2725_ = v___y_2775_;
v___y_2726_ = v___y_2776_;
v___y_2727_ = v___y_2777_;
v_a_2728_ = v_fst_2778_;
goto v___jp_2721_;
}
else
{
lean_object* v___x_2782_; size_t v___x_2783_; size_t v___x_2784_; lean_object* v___x_2785_; 
v___x_2782_ = lean_box(0);
v___x_2783_ = ((size_t)0ULL);
v___x_2784_ = lean_usize_of_nat(v___x_2780_);
v___x_2785_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_snd_2779_, v___x_2783_, v___x_2784_, v___x_2782_, v_a_2514_);
lean_dec_ref(v_snd_2779_);
if (lean_obj_tag(v___x_2785_) == 0)
{
lean_dec_ref_known(v___x_2785_, 1);
v___y_2722_ = v___y_2772_;
v___y_2723_ = v___y_2773_;
v___y_2724_ = v___y_2774_;
v___y_2725_ = v___y_2775_;
v___y_2726_ = v___y_2776_;
v___y_2727_ = v___y_2777_;
v_a_2728_ = v_fst_2778_;
goto v___jp_2721_;
}
else
{
lean_object* v_a_2786_; lean_object* v___x_2788_; uint8_t v_isShared_2789_; uint8_t v_isSharedCheck_2793_; 
lean_dec_ref(v_fst_2778_);
lean_dec_ref(v___y_2777_);
lean_dec_ref(v___y_2776_);
lean_dec_ref(v___y_2775_);
lean_dec(v___y_2774_);
lean_dec(v___y_2773_);
lean_dec_ref(v___y_2772_);
lean_dec_ref(v___x_2704_);
lean_dec_ref(v_wsDir_2511_);
lean_dec_ref(v_lakeEnv_2510_);
lean_dec_ref(v_dep_2508_);
v_a_2786_ = lean_ctor_get(v___x_2785_, 0);
v_isSharedCheck_2793_ = !lean_is_exclusive(v___x_2785_);
if (v_isSharedCheck_2793_ == 0)
{
v___x_2788_ = v___x_2785_;
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
else
{
lean_inc(v_a_2786_);
lean_dec(v___x_2785_);
v___x_2788_ = lean_box(0);
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
v_resetjp_2787_:
{
lean_object* v___x_2791_; 
if (v_isShared_2789_ == 0)
{
v___x_2791_ = v___x_2788_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v_a_2786_);
v___x_2791_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
return v___x_2791_;
}
}
}
}
}
v___jp_2794_:
{
if (lean_obj_tag(v_a_2795_) == 0)
{
lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; uint8_t v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; 
lean_inc_ref(v_scope_2554_);
lean_dec_ref_known(v_a_2795_, 1);
lean_dec_ref(v_relPkgsDir_2512_);
lean_dec_ref(v_wsDir_2511_);
lean_dec_ref(v_lakeEnv_2510_);
lean_dec_ref(v_dep_2508_);
v___x_2796_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
v___x_2797_ = lean_string_append(v_scope_2554_, v___x_2796_);
v___x_2798_ = lean_string_append(v___x_2797_, v___x_2704_);
lean_dec_ref(v___x_2704_);
v___x_2799_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__7));
v___x_2800_ = lean_string_append(v___x_2798_, v___x_2799_);
v___x_2801_ = 3;
v___x_2802_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2802_, 0, v___x_2800_);
lean_ctor_set_uint8(v___x_2802_, sizeof(void*)*1, v___x_2801_);
lean_inc_ref(v_a_2514_);
v___x_2803_ = lean_apply_2(v_a_2514_, v___x_2802_, lean_box(0));
v___x_2804_ = lean_box(0);
v___x_2805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2805_, 0, v___x_2804_);
return v___x_2805_;
}
else
{
lean_object* v_a_2806_; lean_object* v___x_2808_; uint8_t v_isShared_2809_; uint8_t v_isSharedCheck_2898_; 
v_a_2806_ = lean_ctor_get(v_a_2795_, 0);
v_isSharedCheck_2898_ = !lean_is_exclusive(v_a_2795_);
if (v_isSharedCheck_2898_ == 0)
{
v___x_2808_ = v_a_2795_;
v_isShared_2809_ = v_isSharedCheck_2898_;
goto v_resetjp_2807_;
}
else
{
lean_inc(v_a_2806_);
lean_dec(v_a_2795_);
v___x_2808_ = lean_box(0);
v_isShared_2809_ = v_isSharedCheck_2898_;
goto v_resetjp_2807_;
}
v_resetjp_2807_:
{
if (lean_obj_tag(v_a_2806_) == 0)
{
lean_object* v___x_2810_; uint8_t v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; 
lean_del_object(v___x_2808_);
lean_dec_ref(v___x_2704_);
lean_dec_ref(v_relPkgsDir_2512_);
lean_dec_ref(v_wsDir_2511_);
lean_dec_ref(v_lakeEnv_2510_);
v___x_2810_ = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed(v_dep_2508_);
v___x_2811_ = 3;
v___x_2812_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2812_, 0, v___x_2810_);
lean_ctor_set_uint8(v___x_2812_, sizeof(void*)*1, v___x_2811_);
lean_inc_ref(v_a_2514_);
v___x_2813_ = lean_apply_2(v_a_2514_, v___x_2812_, lean_box(0));
v___x_2814_ = lean_box(0);
v___x_2815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2815_, 0, v___x_2814_);
return v___x_2815_;
}
else
{
lean_object* v_val_2816_; lean_object* v___x_2817_; 
v_val_2816_ = lean_ctor_get(v_a_2806_, 0);
lean_inc(v_val_2816_);
lean_dec_ref_known(v_a_2806_, 1);
v___x_2817_ = l_Lake_RegistryPkg_gitSrc_x3f(v_val_2816_);
if (lean_obj_tag(v___x_2817_) == 1)
{
lean_object* v_val_2818_; lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2897_; 
v_val_2818_ = lean_ctor_get(v___x_2817_, 0);
v_isSharedCheck_2897_ = !lean_is_exclusive(v___x_2817_);
if (v_isSharedCheck_2897_ == 0)
{
v___x_2820_ = v___x_2817_;
v_isShared_2821_ = v_isSharedCheck_2897_;
goto v_resetjp_2819_;
}
else
{
lean_inc(v_val_2818_);
lean_dec(v___x_2817_);
v___x_2820_ = lean_box(0);
v_isShared_2821_ = v_isSharedCheck_2897_;
goto v_resetjp_2819_;
}
v_resetjp_2819_:
{
if (lean_obj_tag(v_val_2818_) == 0)
{
lean_object* v_url_2822_; lean_object* v_githubUrl_x3f_2823_; lean_object* v_defaultBranch_x3f_2824_; lean_object* v_subDir_x3f_2825_; lean_object* v_name_2826_; lean_object* v_fullName_2827_; lean_object* v___x_2828_; 
v_url_2822_ = lean_ctor_get(v_val_2818_, 1);
lean_inc_ref(v_url_2822_);
v_githubUrl_x3f_2823_ = lean_ctor_get(v_val_2818_, 2);
lean_inc(v_githubUrl_x3f_2823_);
v_defaultBranch_x3f_2824_ = lean_ctor_get(v_val_2818_, 3);
lean_inc(v_defaultBranch_x3f_2824_);
v_subDir_x3f_2825_ = lean_ctor_get(v_val_2818_, 4);
lean_inc(v_subDir_x3f_2825_);
lean_dec_ref_known(v_val_2818_, 5);
v_name_2826_ = lean_ctor_get(v_val_2816_, 0);
lean_inc_ref(v_name_2826_);
v_fullName_2827_ = lean_ctor_get(v_val_2816_, 1);
lean_inc_ref(v_fullName_2827_);
lean_dec(v_val_2816_);
v___x_2828_ = l_Lake_joinRelative(v_relPkgsDir_2512_, v_name_2826_);
switch(lean_obj_tag(v_version_2555_))
{
case 0:
{
lean_object* v___x_2829_; 
lean_del_object(v___x_2808_);
lean_dec_ref(v___x_2704_);
v___x_2829_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
if (lean_obj_tag(v_defaultBranch_x3f_2824_) == 0)
{
uint8_t v___x_2830_; 
lean_dec_ref(v___x_2828_);
lean_dec_ref(v_fullName_2827_);
lean_dec(v_subDir_x3f_2825_);
lean_dec(v_githubUrl_x3f_2823_);
lean_dec_ref(v_url_2822_);
lean_dec_ref(v_wsDir_2511_);
lean_dec_ref(v_lakeEnv_2510_);
lean_dec_ref(v_dep_2508_);
v___x_2830_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_2830_ == 0)
{
lean_object* v___x_2831_; lean_object* v___x_2833_; 
v___x_2831_ = lean_box(0);
if (v_isShared_2821_ == 0)
{
lean_ctor_set(v___x_2820_, 0, v___x_2831_);
v___x_2833_ = v___x_2820_;
goto v_reusejp_2832_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v___x_2831_);
v___x_2833_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2832_;
}
v_reusejp_2832_:
{
return v___x_2833_;
}
}
else
{
lean_object* v___x_2835_; size_t v___x_2836_; size_t v___x_2837_; lean_object* v___x_2838_; 
lean_del_object(v___x_2820_);
v___x_2835_ = lean_box(0);
v___x_2836_ = ((size_t)0ULL);
v___x_2837_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_2838_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_2829_, v___x_2836_, v___x_2837_, v___x_2835_, v_a_2514_);
if (lean_obj_tag(v___x_2838_) == 0)
{
lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2845_; 
v_isSharedCheck_2845_ = !lean_is_exclusive(v___x_2838_);
if (v_isSharedCheck_2845_ == 0)
{
lean_object* v_unused_2846_; 
v_unused_2846_ = lean_ctor_get(v___x_2838_, 0);
lean_dec(v_unused_2846_);
v___x_2840_ = v___x_2838_;
v_isShared_2841_ = v_isSharedCheck_2845_;
goto v_resetjp_2839_;
}
else
{
lean_dec(v___x_2838_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_2845_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
lean_object* v___x_2843_; 
if (v_isShared_2841_ == 0)
{
lean_ctor_set_tag(v___x_2840_, 1);
lean_ctor_set(v___x_2840_, 0, v___x_2835_);
v___x_2843_ = v___x_2840_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2844_; 
v_reuseFailAlloc_2844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2844_, 0, v___x_2835_);
v___x_2843_ = v_reuseFailAlloc_2844_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
return v___x_2843_;
}
}
}
else
{
lean_object* v_a_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2854_; 
v_a_2847_ = lean_ctor_get(v___x_2838_, 0);
v_isSharedCheck_2854_ = !lean_is_exclusive(v___x_2838_);
if (v_isSharedCheck_2854_ == 0)
{
v___x_2849_ = v___x_2838_;
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_a_2847_);
lean_dec(v___x_2838_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
lean_object* v___x_2852_; 
if (v_isShared_2850_ == 0)
{
v___x_2852_ = v___x_2849_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v_a_2847_);
v___x_2852_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
return v___x_2852_;
}
}
}
}
}
else
{
lean_object* v_val_2855_; uint8_t v___x_2856_; 
lean_del_object(v___x_2820_);
v_val_2855_ = lean_ctor_get(v_defaultBranch_x3f_2824_, 0);
lean_inc(v_val_2855_);
lean_dec_ref_known(v_defaultBranch_x3f_2824_, 1);
v___x_2856_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_2856_ == 0)
{
v___y_2537_ = v_subDir_x3f_2825_;
v___y_2538_ = v_githubUrl_x3f_2823_;
v___y_2539_ = v_fullName_2827_;
v___y_2540_ = v___x_2828_;
v___y_2541_ = v_url_2822_;
v_a_2542_ = v_val_2855_;
goto v___jp_2536_;
}
else
{
lean_object* v___x_2857_; size_t v___x_2858_; size_t v___x_2859_; lean_object* v___x_2860_; 
v___x_2857_ = lean_box(0);
v___x_2858_ = ((size_t)0ULL);
v___x_2859_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_2860_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_2829_, v___x_2858_, v___x_2859_, v___x_2857_, v_a_2514_);
if (lean_obj_tag(v___x_2860_) == 0)
{
lean_dec_ref_known(v___x_2860_, 1);
v___y_2537_ = v_subDir_x3f_2825_;
v___y_2538_ = v_githubUrl_x3f_2823_;
v___y_2539_ = v_fullName_2827_;
v___y_2540_ = v___x_2828_;
v___y_2541_ = v_url_2822_;
v_a_2542_ = v_val_2855_;
goto v___jp_2536_;
}
else
{
lean_object* v_a_2861_; lean_object* v___x_2863_; uint8_t v_isShared_2864_; uint8_t v_isSharedCheck_2868_; 
lean_dec(v_val_2855_);
lean_dec_ref(v___x_2828_);
lean_dec_ref(v_fullName_2827_);
lean_dec(v_subDir_x3f_2825_);
lean_dec(v_githubUrl_x3f_2823_);
lean_dec_ref(v_url_2822_);
lean_dec_ref(v_wsDir_2511_);
lean_dec_ref(v_lakeEnv_2510_);
lean_dec_ref(v_dep_2508_);
v_a_2861_ = lean_ctor_get(v___x_2860_, 0);
v_isSharedCheck_2868_ = !lean_is_exclusive(v___x_2860_);
if (v_isSharedCheck_2868_ == 0)
{
v___x_2863_ = v___x_2860_;
v_isShared_2864_ = v_isSharedCheck_2868_;
goto v_resetjp_2862_;
}
else
{
lean_inc(v_a_2861_);
lean_dec(v___x_2860_);
v___x_2863_ = lean_box(0);
v_isShared_2864_ = v_isSharedCheck_2868_;
goto v_resetjp_2862_;
}
v_resetjp_2862_:
{
lean_object* v___x_2866_; 
if (v_isShared_2864_ == 0)
{
v___x_2866_ = v___x_2863_;
goto v_reusejp_2865_;
}
else
{
lean_object* v_reuseFailAlloc_2867_; 
v_reuseFailAlloc_2867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2867_, 0, v_a_2861_);
v___x_2866_ = v_reuseFailAlloc_2867_;
goto v_reusejp_2865_;
}
v_reusejp_2865_:
{
return v___x_2866_;
}
}
}
}
}
}
case 1:
{
lean_object* v_rev_2869_; lean_object* v___x_2870_; uint8_t v___x_2871_; 
lean_dec(v_defaultBranch_x3f_2824_);
lean_del_object(v___x_2820_);
lean_del_object(v___x_2808_);
lean_dec_ref(v___x_2704_);
v_rev_2869_ = lean_ctor_get(v_version_2555_, 0);
v___x_2870_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_2871_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_2871_ == 0)
{
lean_inc_ref(v_rev_2869_);
v___y_2537_ = v_subDir_x3f_2825_;
v___y_2538_ = v_githubUrl_x3f_2823_;
v___y_2539_ = v_fullName_2827_;
v___y_2540_ = v___x_2828_;
v___y_2541_ = v_url_2822_;
v_a_2542_ = v_rev_2869_;
goto v___jp_2536_;
}
else
{
lean_object* v___x_2872_; size_t v___x_2873_; size_t v___x_2874_; lean_object* v___x_2875_; 
v___x_2872_ = lean_box(0);
v___x_2873_ = ((size_t)0ULL);
v___x_2874_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_2875_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_2870_, v___x_2873_, v___x_2874_, v___x_2872_, v_a_2514_);
if (lean_obj_tag(v___x_2875_) == 0)
{
lean_dec_ref_known(v___x_2875_, 1);
lean_inc_ref(v_rev_2869_);
v___y_2537_ = v_subDir_x3f_2825_;
v___y_2538_ = v_githubUrl_x3f_2823_;
v___y_2539_ = v_fullName_2827_;
v___y_2540_ = v___x_2828_;
v___y_2541_ = v_url_2822_;
v_a_2542_ = v_rev_2869_;
goto v___jp_2536_;
}
else
{
lean_object* v_a_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2883_; 
lean_dec_ref(v___x_2828_);
lean_dec_ref(v_fullName_2827_);
lean_dec(v_subDir_x3f_2825_);
lean_dec(v_githubUrl_x3f_2823_);
lean_dec_ref(v_url_2822_);
lean_dec_ref(v_wsDir_2511_);
lean_dec_ref(v_lakeEnv_2510_);
lean_dec_ref(v_dep_2508_);
v_a_2876_ = lean_ctor_get(v___x_2875_, 0);
v_isSharedCheck_2883_ = !lean_is_exclusive(v___x_2875_);
if (v_isSharedCheck_2883_ == 0)
{
v___x_2878_ = v___x_2875_;
v_isShared_2879_ = v_isSharedCheck_2883_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_a_2876_);
lean_dec(v___x_2875_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2883_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
lean_object* v___x_2881_; 
if (v_isShared_2879_ == 0)
{
v___x_2881_ = v___x_2878_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v_a_2876_);
v___x_2881_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
return v___x_2881_;
}
}
}
}
}
default: 
{
lean_object* v_ver_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; 
lean_dec(v_defaultBranch_x3f_2824_);
lean_del_object(v___x_2820_);
v_ver_2884_ = lean_ctor_get(v_version_2555_, 0);
v___x_2885_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_scope_2554_);
lean_inc_ref(v_lakeEnv_2510_);
v___x_2886_ = l_Lake_Reservoir_fetchPkgVersions(v_lakeEnv_2510_, v_scope_2554_, v___x_2704_, v___x_2885_);
if (lean_obj_tag(v___x_2886_) == 0)
{
lean_object* v_a_2887_; lean_object* v_a_2888_; lean_object* v___x_2890_; 
v_a_2887_ = lean_ctor_get(v___x_2886_, 0);
lean_inc(v_a_2887_);
v_a_2888_ = lean_ctor_get(v___x_2886_, 1);
lean_inc(v_a_2888_);
lean_dec_ref_known(v___x_2886_, 2);
if (v_isShared_2809_ == 0)
{
lean_ctor_set(v___x_2808_, 0, v_a_2887_);
v___x_2890_ = v___x_2808_;
goto v_reusejp_2889_;
}
else
{
lean_object* v_reuseFailAlloc_2891_; 
v_reuseFailAlloc_2891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2891_, 0, v_a_2887_);
v___x_2890_ = v_reuseFailAlloc_2891_;
goto v_reusejp_2889_;
}
v_reusejp_2889_:
{
lean_inc_ref(v_ver_2884_);
v___y_2772_ = v_ver_2884_;
v___y_2773_ = v_subDir_x3f_2825_;
v___y_2774_ = v_githubUrl_x3f_2823_;
v___y_2775_ = v_fullName_2827_;
v___y_2776_ = v___x_2828_;
v___y_2777_ = v_url_2822_;
v_fst_2778_ = v___x_2890_;
v_snd_2779_ = v_a_2888_;
goto v___jp_2771_;
}
}
else
{
lean_object* v_a_2892_; lean_object* v_a_2893_; lean_object* v___x_2895_; 
v_a_2892_ = lean_ctor_get(v___x_2886_, 0);
lean_inc(v_a_2892_);
v_a_2893_ = lean_ctor_get(v___x_2886_, 1);
lean_inc(v_a_2893_);
lean_dec_ref_known(v___x_2886_, 2);
if (v_isShared_2809_ == 0)
{
lean_ctor_set_tag(v___x_2808_, 0);
lean_ctor_set(v___x_2808_, 0, v_a_2892_);
v___x_2895_ = v___x_2808_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v_a_2892_);
v___x_2895_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
lean_inc_ref(v_ver_2884_);
v___y_2772_ = v_ver_2884_;
v___y_2773_ = v_subDir_x3f_2825_;
v___y_2774_ = v_githubUrl_x3f_2823_;
v___y_2775_ = v_fullName_2827_;
v___y_2776_ = v___x_2828_;
v___y_2777_ = v_url_2822_;
v_fst_2778_ = v___x_2895_;
v_snd_2779_ = v_a_2893_;
goto v___jp_2771_;
}
}
}
}
}
else
{
lean_del_object(v___x_2820_);
lean_dec(v_val_2818_);
lean_del_object(v___x_2808_);
lean_dec_ref(v___x_2704_);
lean_dec_ref(v_relPkgsDir_2512_);
lean_dec_ref(v_wsDir_2511_);
lean_dec_ref(v_lakeEnv_2510_);
lean_dec_ref(v_dep_2508_);
v___y_2517_ = v_val_2816_;
v___y_2518_ = v_a_2514_;
goto v___jp_2516_;
}
}
}
else
{
lean_dec(v___x_2817_);
lean_del_object(v___x_2808_);
lean_dec_ref(v___x_2704_);
lean_dec_ref(v_relPkgsDir_2512_);
lean_dec_ref(v_wsDir_2511_);
lean_dec_ref(v_lakeEnv_2510_);
lean_dec_ref(v_dep_2508_);
v___y_2517_ = v_val_2816_;
v___y_2518_ = v_a_2514_;
goto v___jp_2516_;
}
}
}
}
}
v___jp_2901_:
{
lean_object* v___x_2904_; uint8_t v___x_2905_; 
v___x_2904_ = lean_array_get_size(v_snd_2903_);
v___x_2905_ = lean_nat_dec_lt(v___x_2702_, v___x_2904_);
if (v___x_2905_ == 0)
{
lean_dec_ref(v_snd_2903_);
v_a_2795_ = v_fst_2902_;
goto v___jp_2794_;
}
else
{
lean_object* v___x_2906_; size_t v___x_2907_; size_t v___x_2908_; lean_object* v___x_2909_; 
v___x_2906_ = lean_box(0);
v___x_2907_ = ((size_t)0ULL);
v___x_2908_ = lean_usize_of_nat(v___x_2904_);
v___x_2909_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_snd_2903_, v___x_2907_, v___x_2908_, v___x_2906_, v_a_2514_);
lean_dec_ref(v_snd_2903_);
if (lean_obj_tag(v___x_2909_) == 0)
{
lean_dec_ref_known(v___x_2909_, 1);
v_a_2795_ = v_fst_2902_;
goto v___jp_2794_;
}
else
{
lean_object* v_a_2910_; lean_object* v___x_2912_; uint8_t v_isShared_2913_; uint8_t v_isSharedCheck_2917_; 
lean_dec_ref(v_fst_2902_);
lean_dec_ref(v___x_2704_);
lean_dec_ref(v_relPkgsDir_2512_);
lean_dec_ref(v_wsDir_2511_);
lean_dec_ref(v_lakeEnv_2510_);
lean_dec_ref(v_dep_2508_);
v_a_2910_ = lean_ctor_get(v___x_2909_, 0);
v_isSharedCheck_2917_ = !lean_is_exclusive(v___x_2909_);
if (v_isSharedCheck_2917_ == 0)
{
v___x_2912_ = v___x_2909_;
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
else
{
lean_inc(v_a_2910_);
lean_dec(v___x_2909_);
v___x_2912_ = lean_box(0);
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
v_resetjp_2911_:
{
lean_object* v___x_2915_; 
if (v_isShared_2913_ == 0)
{
v___x_2915_ = v___x_2912_;
goto v_reusejp_2914_;
}
else
{
lean_object* v_reuseFailAlloc_2916_; 
v_reuseFailAlloc_2916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2916_, 0, v_a_2910_);
v___x_2915_ = v_reuseFailAlloc_2916_;
goto v_reusejp_2914_;
}
v_reusejp_2914_:
{
return v___x_2915_;
}
}
}
}
}
}
else
{
uint8_t v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; uint8_t v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; 
lean_inc(v_name_2553_);
lean_dec_ref(v_relPkgsDir_2512_);
lean_dec_ref(v_wsDir_2511_);
lean_dec_ref(v_lakeEnv_2510_);
lean_dec_ref(v_dep_2508_);
v___x_2924_ = 0;
v___x_2925_ = l_Lean_Name_toString(v_name_2553_, v___x_2924_);
v___x_2926_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__8));
v___x_2927_ = lean_string_append(v___x_2925_, v___x_2926_);
v___x_2928_ = 3;
v___x_2929_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2929_, 0, v___x_2927_);
lean_ctor_set_uint8(v___x_2929_, sizeof(void*)*1, v___x_2928_);
lean_inc_ref(v_a_2514_);
v___x_2930_ = lean_apply_2(v_a_2514_, v___x_2929_, lean_box(0));
v___x_2931_ = lean_box(0);
v___x_2932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2932_, 0, v___x_2931_);
return v___x_2932_;
}
}
v___jp_2516_:
{
lean_object* v_fullName_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; uint8_t v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; 
v_fullName_2519_ = lean_ctor_get(v___y_2517_, 1);
lean_inc_ref(v_fullName_2519_);
lean_dec_ref(v___y_2517_);
v___x_2520_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__0));
v___x_2521_ = lean_string_append(v_fullName_2519_, v___x_2520_);
v___x_2522_ = 3;
v___x_2523_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2523_, 0, v___x_2521_);
lean_ctor_set_uint8(v___x_2523_, sizeof(void*)*1, v___x_2522_);
lean_inc_ref(v___y_2518_);
v___x_2524_ = lean_apply_2(v___y_2518_, v___x_2523_, lean_box(0));
v___x_2525_ = lean_box(0);
v___x_2526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2526_, 0, v___x_2525_);
return v___x_2526_;
}
v___jp_2527_:
{
lean_object* v___x_2534_; lean_object* v___x_2535_; 
v___x_2534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2534_, 0, v___y_2532_);
v___x_2535_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(v_a_2514_, v_dep_2508_, v_inherited_2509_, v_lakeEnv_2510_, v_wsDir_2511_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2533_, v___x_2534_, v___y_2528_);
lean_dec_ref(v_lakeEnv_2510_);
return v___x_2535_;
}
v___jp_2536_:
{
if (lean_obj_tag(v___y_2538_) == 0)
{
lean_object* v___x_2543_; 
v___x_2543_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___y_2528_ = v___y_2537_;
v___y_2529_ = v___y_2539_;
v___y_2530_ = v___y_2540_;
v___y_2531_ = v___y_2541_;
v___y_2532_ = v_a_2542_;
v___y_2533_ = v___x_2543_;
goto v___jp_2527_;
}
else
{
lean_object* v_val_2544_; 
v_val_2544_ = lean_ctor_get(v___y_2538_, 0);
lean_inc(v_val_2544_);
lean_dec_ref_known(v___y_2538_, 1);
v___y_2528_ = v___y_2537_;
v___y_2529_ = v___y_2539_;
v___y_2530_ = v___y_2540_;
v___y_2531_ = v___y_2541_;
v___y_2532_ = v_a_2542_;
v___y_2533_ = v_val_2544_;
goto v___jp_2527_;
}
}
v___jp_2545_:
{
lean_object* v___x_2547_; uint8_t v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2547_ = lean_io_error_to_string(v_a_2546_);
v___x_2548_ = 3;
v___x_2549_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2549_, 0, v___x_2547_);
lean_ctor_set_uint8(v___x_2549_, sizeof(void*)*1, v___x_2548_);
lean_inc_ref(v_a_2514_);
v___x_2550_ = lean_apply_2(v_a_2514_, v___x_2549_, lean_box(0));
v___x_2551_ = lean_box(0);
v___x_2552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2552_, 0, v___x_2551_);
return v___x_2552_;
}
v___jp_2557_:
{
lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; 
v___x_2563_ = l_Lake_defaultConfigFile;
v___x_2564_ = lean_box(0);
v___x_2565_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_2565_, 0, v_name_2553_);
lean_ctor_set(v___x_2565_, 1, v_scope_2554_);
lean_ctor_set(v___x_2565_, 2, v___x_2563_);
lean_ctor_set(v___x_2565_, 3, v___x_2564_);
lean_ctor_set(v___x_2565_, 4, v___y_2560_);
lean_ctor_set_uint8(v___x_2565_, sizeof(void*)*5, v_inherited_2509_);
lean_inc_ref(v___y_2558_);
v___x_2566_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2566_, 0, v___y_2559_);
lean_ctor_set(v___x_2566_, 1, v___y_2561_);
lean_ctor_set(v___x_2566_, 2, v___y_2558_);
lean_ctor_set(v___x_2566_, 3, v_a_2562_);
lean_ctor_set(v___x_2566_, 4, v___x_2565_);
v___x_2567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2567_, 0, v___x_2566_);
return v___x_2567_;
}
v___jp_2568_:
{
lean_object* v___x_2576_; uint8_t v___x_2577_; 
v___x_2576_ = lean_array_get_size(v___y_2573_);
v___x_2577_ = lean_nat_dec_lt(v___y_2570_, v___x_2576_);
if (v___x_2577_ == 0)
{
v___y_2558_ = v___y_2569_;
v___y_2559_ = v___y_2571_;
v___y_2560_ = v___y_2572_;
v___y_2561_ = v___y_2574_;
v_a_2562_ = v_val_2575_;
goto v___jp_2557_;
}
else
{
lean_object* v___x_2578_; size_t v___x_2579_; size_t v___x_2580_; lean_object* v___x_2581_; 
v___x_2578_ = lean_box(0);
v___x_2579_ = ((size_t)0ULL);
v___x_2580_ = lean_usize_of_nat(v___x_2576_);
v___x_2581_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_2573_, v___x_2579_, v___x_2580_, v___x_2578_, v_a_2514_);
if (lean_obj_tag(v___x_2581_) == 0)
{
lean_dec_ref_known(v___x_2581_, 1);
v___y_2558_ = v___y_2569_;
v___y_2559_ = v___y_2571_;
v___y_2560_ = v___y_2572_;
v___y_2561_ = v___y_2574_;
v_a_2562_ = v_val_2575_;
goto v___jp_2557_;
}
else
{
lean_object* v_a_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2589_; 
lean_dec_ref(v_val_2575_);
lean_dec_ref(v___y_2574_);
lean_dec_ref(v___y_2572_);
lean_dec_ref(v___y_2571_);
lean_dec_ref(v_scope_2554_);
lean_dec(v_name_2553_);
v_a_2582_ = lean_ctor_get(v___x_2581_, 0);
v_isSharedCheck_2589_ = !lean_is_exclusive(v___x_2581_);
if (v_isSharedCheck_2589_ == 0)
{
v___x_2584_ = v___x_2581_;
v_isShared_2585_ = v_isSharedCheck_2589_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_a_2582_);
lean_dec(v___x_2581_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2589_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v___x_2587_; 
if (v_isShared_2585_ == 0)
{
v___x_2587_ = v___x_2584_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v_a_2582_);
v___x_2587_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
return v___x_2587_;
}
}
}
}
}
v___jp_2590_:
{
if (lean_obj_tag(v_a_2596_) == 1)
{
lean_object* v_val_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; 
lean_dec_ref(v___y_2593_);
lean_dec_ref(v___y_2592_);
v_val_2597_ = lean_ctor_get(v_a_2596_, 0);
lean_inc_n(v_val_2597_, 2);
lean_dec_ref_known(v_a_2596_, 1);
v___x_2598_ = l_Lake_defaultManifestFile;
v___x_2599_ = l_Lake_joinRelative(v_val_2597_, v___x_2598_);
v___x_2600_ = lean_unsigned_to_nat(0u);
v___x_2601_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_2602_ = l_Lake_Manifest_load(v___x_2599_);
if (lean_obj_tag(v___x_2602_) == 0)
{
lean_object* v_a_2603_; lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2610_; 
v_a_2603_ = lean_ctor_get(v___x_2602_, 0);
v_isSharedCheck_2610_ = !lean_is_exclusive(v___x_2602_);
if (v_isSharedCheck_2610_ == 0)
{
v___x_2605_ = v___x_2602_;
v_isShared_2606_ = v_isSharedCheck_2610_;
goto v_resetjp_2604_;
}
else
{
lean_inc(v_a_2603_);
lean_dec(v___x_2602_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2610_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
lean_object* v___x_2608_; 
if (v_isShared_2606_ == 0)
{
lean_ctor_set_tag(v___x_2605_, 1);
v___x_2608_ = v___x_2605_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v_a_2603_);
v___x_2608_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
v___y_2569_ = v___y_2591_;
v___y_2570_ = v___x_2600_;
v___y_2571_ = v_val_2597_;
v___y_2572_ = v___y_2594_;
v___y_2573_ = v___x_2601_;
v___y_2574_ = v___y_2595_;
v_val_2575_ = v___x_2608_;
goto v___jp_2568_;
}
}
}
else
{
lean_object* v_a_2611_; lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2618_; 
v_a_2611_ = lean_ctor_get(v___x_2602_, 0);
v_isSharedCheck_2618_ = !lean_is_exclusive(v___x_2602_);
if (v_isSharedCheck_2618_ == 0)
{
v___x_2613_ = v___x_2602_;
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
else
{
lean_inc(v_a_2611_);
lean_dec(v___x_2602_);
v___x_2613_ = lean_box(0);
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
v_resetjp_2612_:
{
lean_object* v___x_2616_; 
if (v_isShared_2614_ == 0)
{
lean_ctor_set_tag(v___x_2613_, 0);
v___x_2616_ = v___x_2613_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v_a_2611_);
v___x_2616_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
v___y_2569_ = v___y_2591_;
v___y_2570_ = v___x_2600_;
v___y_2571_ = v_val_2597_;
v___y_2572_ = v___y_2594_;
v___y_2573_ = v___x_2601_;
v___y_2574_ = v___y_2595_;
v_val_2575_ = v___x_2616_;
goto v___jp_2568_;
}
}
}
}
else
{
lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; uint8_t v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; 
lean_dec(v_a_2596_);
lean_dec_ref(v___y_2595_);
lean_dec_ref(v___y_2594_);
lean_dec_ref(v_scope_2554_);
lean_dec(v_name_2553_);
v___x_2619_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0));
v___x_2620_ = lean_string_append(v___y_2592_, v___x_2619_);
v___x_2621_ = lean_string_append(v___x_2620_, v___y_2593_);
lean_dec_ref(v___y_2593_);
v___x_2622_ = 3;
v___x_2623_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2623_, 0, v___x_2621_);
lean_ctor_set_uint8(v___x_2623_, sizeof(void*)*1, v___x_2622_);
lean_inc_ref(v_a_2514_);
v___x_2624_ = lean_apply_2(v_a_2514_, v___x_2623_, lean_box(0));
v___x_2625_ = lean_box(0);
v___x_2626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2626_, 0, v___x_2625_);
return v___x_2626_;
}
}
v___jp_2627_:
{
lean_object* v___x_2636_; uint8_t v___x_2637_; 
v___x_2636_ = lean_array_get_size(v___y_2629_);
v___x_2637_ = lean_nat_dec_lt(v___y_2632_, v___x_2636_);
if (v___x_2637_ == 0)
{
v___y_2591_ = v___y_2628_;
v___y_2592_ = v___y_2630_;
v___y_2593_ = v___y_2631_;
v___y_2594_ = v___y_2633_;
v___y_2595_ = v___y_2634_;
v_a_2596_ = v_val_2635_;
goto v___jp_2590_;
}
else
{
lean_object* v___x_2638_; size_t v___x_2639_; size_t v___x_2640_; lean_object* v___x_2641_; 
v___x_2638_ = lean_box(0);
v___x_2639_ = ((size_t)0ULL);
v___x_2640_ = lean_usize_of_nat(v___x_2636_);
v___x_2641_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_2629_, v___x_2639_, v___x_2640_, v___x_2638_, v_a_2514_);
if (lean_obj_tag(v___x_2641_) == 0)
{
lean_dec_ref_known(v___x_2641_, 1);
v___y_2591_ = v___y_2628_;
v___y_2592_ = v___y_2630_;
v___y_2593_ = v___y_2631_;
v___y_2594_ = v___y_2633_;
v___y_2595_ = v___y_2634_;
v_a_2596_ = v_val_2635_;
goto v___jp_2590_;
}
else
{
lean_object* v_a_2642_; lean_object* v___x_2644_; uint8_t v_isShared_2645_; uint8_t v_isSharedCheck_2649_; 
lean_dec(v_val_2635_);
lean_dec_ref(v___y_2634_);
lean_dec_ref(v___y_2633_);
lean_dec_ref(v___y_2631_);
lean_dec_ref(v___y_2630_);
lean_dec_ref(v_scope_2554_);
lean_dec(v_name_2553_);
v_a_2642_ = lean_ctor_get(v___x_2641_, 0);
v_isSharedCheck_2649_ = !lean_is_exclusive(v___x_2641_);
if (v_isSharedCheck_2649_ == 0)
{
v___x_2644_ = v___x_2641_;
v_isShared_2645_ = v_isSharedCheck_2649_;
goto v_resetjp_2643_;
}
else
{
lean_inc(v_a_2642_);
lean_dec(v___x_2641_);
v___x_2644_ = lean_box(0);
v_isShared_2645_ = v_isSharedCheck_2649_;
goto v_resetjp_2643_;
}
v_resetjp_2643_:
{
lean_object* v___x_2647_; 
if (v_isShared_2645_ == 0)
{
v___x_2647_ = v___x_2644_;
goto v_reusejp_2646_;
}
else
{
lean_object* v_reuseFailAlloc_2648_; 
v_reuseFailAlloc_2648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2648_, 0, v_a_2642_);
v___x_2647_ = v_reuseFailAlloc_2648_;
goto v_reusejp_2646_;
}
v_reusejp_2646_:
{
return v___x_2647_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lake_Dependency_materialize_0interp(lean_interpreter_value* stack)
{
lean_object* v_dep_2508_ = stack[0].m_obj;
uint8_t v_inherited_2509_ = stack[1].m_num;
lean_object* v_lakeEnv_2510_ = stack[2].m_obj;
lean_object* v_wsDir_2511_ = stack[3].m_obj;
lean_object* v_relPkgsDir_2512_ = stack[4].m_obj;
lean_object* v_relParentDir_2513_ = stack[5].m_obj;
lean_object* v_a_2514_ = stack[6].m_obj;
lean_object* v_res_2933_;
v_res_2933_ = l_Lake_Dependency_materialize(v_dep_2508_, v_inherited_2509_, v_lakeEnv_2510_, v_wsDir_2511_, v_relPkgsDir_2512_, v_relParentDir_2513_, v_a_2514_);
stack->m_obj
 = v_res_2933_;
}
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize___boxed(lean_object* v_dep_2934_, lean_object* v_inherited_2935_, lean_object* v_lakeEnv_2936_, lean_object* v_wsDir_2937_, lean_object* v_relPkgsDir_2938_, lean_object* v_relParentDir_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_){
_start:
{
uint8_t v_inherited_boxed_2942_; lean_object* v_res_2943_; 
v_inherited_boxed_2942_ = lean_unbox(v_inherited_2935_);
v_res_2943_ = l_Lake_Dependency_materialize(v_dep_2934_, v_inherited_boxed_2942_, v_lakeEnv_2936_, v_wsDir_2937_, v_relPkgsDir_2938_, v_relParentDir_2939_, v_a_2940_);
lean_dec_ref(v_a_2940_);
return v_res_2943_;
}
}
lean_object* l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep(lean_object* v_manifestEntry_2949_, lean_object* v_wsDir_2950_, lean_object* v_relPkgDir_2951_, lean_object* v_remoteUrl_2952_, lean_object* v_a_2953_){
_start:
{
lean_object* v___y_2956_; lean_object* v_a_2957_; lean_object* v___f_2960_; lean_object* v___y_2962_; lean_object* v___y_2963_; lean_object* v___y_2964_; lean_object* v___y_2965_; lean_object* v_val_2966_; lean_object* v_pkgDir_2982_; lean_object* v_a_2984_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v_val_3026_; lean_object* v___x_3041_; lean_object* v___x_3042_; uint8_t v___x_3043_; 
v___f_2960_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__1));
lean_inc_ref(v_relPkgDir_2951_);
v_pkgDir_2982_ = l_Lake_joinRelative(v_wsDir_2950_, v_relPkgDir_2951_);
v___x_3022_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3);
v___x_3023_ = lean_unsigned_to_nat(0u);
v___x_3024_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_pkgDir_2982_);
v___x_3041_ = l_Lake_resolvePath(v_pkgDir_2982_);
v___x_3042_ = lean_string_utf8_byte_size(v___x_3041_);
v___x_3043_ = lean_nat_dec_eq(v___x_3042_, v___x_3023_);
if (v___x_3043_ == 0)
{
lean_object* v___x_3044_; 
v___x_3044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3044_, 0, v___x_3041_);
v_val_3026_ = v___x_3044_;
goto v___jp_3025_;
}
else
{
lean_object* v___x_3045_; 
lean_dec_ref(v___x_3041_);
v___x_3045_ = lean_box(0);
v_val_3026_ = v___x_3045_;
goto v___jp_3025_;
}
v___jp_2955_:
{
lean_object* v___x_2958_; lean_object* v___x_2959_; 
v___x_2958_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2958_, 0, v___y_2956_);
lean_ctor_set(v___x_2958_, 1, v_relPkgDir_2951_);
lean_ctor_set(v___x_2958_, 2, v_remoteUrl_2952_);
lean_ctor_set(v___x_2958_, 3, v_a_2957_);
lean_ctor_set(v___x_2958_, 4, v_manifestEntry_2949_);
v___x_2959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2959_, 0, v___x_2958_);
return v___x_2959_;
}
v___jp_2961_:
{
lean_object* v___x_2967_; uint8_t v___x_2968_; 
v___x_2967_ = lean_array_get_size(v___y_2965_);
v___x_2968_ = lean_nat_dec_lt(v___y_2964_, v___x_2967_);
if (v___x_2968_ == 0)
{
v___y_2956_ = v___y_2963_;
v_a_2957_ = v_val_2966_;
goto v___jp_2955_;
}
else
{
lean_object* v___x_2969_; size_t v___x_2970_; size_t v___x_2971_; lean_object* v___x_1877__overap_2972_; lean_object* v___x_2973_; 
v___x_2969_ = lean_box(0);
v___x_2970_ = ((size_t)0ULL);
v___x_2971_ = lean_usize_of_nat(v___x_2967_);
lean_inc_ref(v___y_2965_);
lean_inc_ref(v___y_2962_);
v___x_1877__overap_2972_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___y_2962_, v___f_2960_, v___y_2965_, v___x_2970_, v___x_2971_, v___x_2969_);
lean_inc_ref(v_a_2953_);
v___x_2973_ = lean_apply_2(v___x_1877__overap_2972_, v_a_2953_, lean_box(0));
if (lean_obj_tag(v___x_2973_) == 0)
{
lean_dec_ref_known(v___x_2973_, 1);
v___y_2956_ = v___y_2963_;
v_a_2957_ = v_val_2966_;
goto v___jp_2955_;
}
else
{
lean_object* v_a_2974_; lean_object* v___x_2976_; uint8_t v_isShared_2977_; uint8_t v_isSharedCheck_2981_; 
lean_dec_ref(v_val_2966_);
lean_dec_ref(v___y_2963_);
lean_dec_ref(v_remoteUrl_2952_);
lean_dec_ref(v_relPkgDir_2951_);
lean_dec_ref(v_manifestEntry_2949_);
v_a_2974_ = lean_ctor_get(v___x_2973_, 0);
v_isSharedCheck_2981_ = !lean_is_exclusive(v___x_2973_);
if (v_isSharedCheck_2981_ == 0)
{
v___x_2976_ = v___x_2973_;
v_isShared_2977_ = v_isSharedCheck_2981_;
goto v_resetjp_2975_;
}
else
{
lean_inc(v_a_2974_);
lean_dec(v___x_2973_);
v___x_2976_ = lean_box(0);
v_isShared_2977_ = v_isSharedCheck_2981_;
goto v_resetjp_2975_;
}
v_resetjp_2975_:
{
lean_object* v___x_2979_; 
if (v_isShared_2977_ == 0)
{
v___x_2979_ = v___x_2976_;
goto v_reusejp_2978_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v_a_2974_);
v___x_2979_ = v_reuseFailAlloc_2980_;
goto v_reusejp_2978_;
}
v_reusejp_2978_:
{
return v___x_2979_;
}
}
}
}
}
v___jp_2983_:
{
if (lean_obj_tag(v_a_2984_) == 1)
{
lean_object* v_manifestFile_x3f_2985_; 
lean_dec_ref(v_pkgDir_2982_);
v_manifestFile_x3f_2985_ = lean_ctor_get(v_manifestEntry_2949_, 3);
if (lean_obj_tag(v_manifestFile_x3f_2985_) == 1)
{
lean_object* v_val_2986_; lean_object* v_val_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; 
v_val_2986_ = lean_ctor_get(v_a_2984_, 0);
lean_inc_n(v_val_2986_, 2);
lean_dec_ref_known(v_a_2984_, 1);
v_val_2987_ = lean_ctor_get(v_manifestFile_x3f_2985_, 0);
lean_inc(v_val_2987_);
v___x_2988_ = l_Lake_joinRelative(v_val_2986_, v_val_2987_);
v___x_2989_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3);
v___x_2990_ = lean_unsigned_to_nat(0u);
v___x_2991_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_2992_ = l_Lake_Manifest_load(v___x_2988_);
if (lean_obj_tag(v___x_2992_) == 0)
{
lean_object* v_a_2993_; lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3000_; 
v_a_2993_ = lean_ctor_get(v___x_2992_, 0);
v_isSharedCheck_3000_ = !lean_is_exclusive(v___x_2992_);
if (v_isSharedCheck_3000_ == 0)
{
v___x_2995_ = v___x_2992_;
v_isShared_2996_ = v_isSharedCheck_3000_;
goto v_resetjp_2994_;
}
else
{
lean_inc(v_a_2993_);
lean_dec(v___x_2992_);
v___x_2995_ = lean_box(0);
v_isShared_2996_ = v_isSharedCheck_3000_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
lean_object* v___x_2998_; 
if (v_isShared_2996_ == 0)
{
lean_ctor_set_tag(v___x_2995_, 1);
v___x_2998_ = v___x_2995_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v_a_2993_);
v___x_2998_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
v___y_2962_ = v___x_2989_;
v___y_2963_ = v_val_2986_;
v___y_2964_ = v___x_2990_;
v___y_2965_ = v___x_2991_;
v_val_2966_ = v___x_2998_;
goto v___jp_2961_;
}
}
}
else
{
lean_object* v_a_3001_; lean_object* v___x_3003_; uint8_t v_isShared_3004_; uint8_t v_isSharedCheck_3008_; 
v_a_3001_ = lean_ctor_get(v___x_2992_, 0);
v_isSharedCheck_3008_ = !lean_is_exclusive(v___x_2992_);
if (v_isSharedCheck_3008_ == 0)
{
v___x_3003_ = v___x_2992_;
v_isShared_3004_ = v_isSharedCheck_3008_;
goto v_resetjp_3002_;
}
else
{
lean_inc(v_a_3001_);
lean_dec(v___x_2992_);
v___x_3003_ = lean_box(0);
v_isShared_3004_ = v_isSharedCheck_3008_;
goto v_resetjp_3002_;
}
v_resetjp_3002_:
{
lean_object* v___x_3006_; 
if (v_isShared_3004_ == 0)
{
lean_ctor_set_tag(v___x_3003_, 0);
v___x_3006_ = v___x_3003_;
goto v_reusejp_3005_;
}
else
{
lean_object* v_reuseFailAlloc_3007_; 
v_reuseFailAlloc_3007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3007_, 0, v_a_3001_);
v___x_3006_ = v_reuseFailAlloc_3007_;
goto v_reusejp_3005_;
}
v_reusejp_3005_:
{
v___y_2962_ = v___x_2989_;
v___y_2963_ = v_val_2986_;
v___y_2964_ = v___x_2990_;
v___y_2965_ = v___x_2991_;
v_val_2966_ = v___x_3006_;
goto v___jp_2961_;
}
}
}
}
else
{
lean_object* v_val_3009_; lean_object* v___x_3010_; 
v_val_3009_ = lean_ctor_get(v_a_2984_, 0);
lean_inc(v_val_3009_);
lean_dec_ref_known(v_a_2984_, 1);
v___x_3010_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1));
v___y_2956_ = v_val_3009_;
v_a_2957_ = v___x_3010_;
goto v___jp_2955_;
}
}
else
{
lean_object* v_name_3011_; uint8_t v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; uint8_t v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; 
lean_dec(v_a_2984_);
lean_dec_ref(v_remoteUrl_2952_);
lean_dec_ref(v_relPkgDir_2951_);
v_name_3011_ = lean_ctor_get(v_manifestEntry_2949_, 0);
lean_inc(v_name_3011_);
lean_dec_ref(v_manifestEntry_2949_);
v___x_3012_ = 0;
v___x_3013_ = l_Lean_Name_toString(v_name_3011_, v___x_3012_);
v___x_3014_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0));
v___x_3015_ = lean_string_append(v___x_3013_, v___x_3014_);
v___x_3016_ = lean_string_append(v___x_3015_, v_pkgDir_2982_);
lean_dec_ref(v_pkgDir_2982_);
v___x_3017_ = 3;
v___x_3018_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3018_, 0, v___x_3016_);
lean_ctor_set_uint8(v___x_3018_, sizeof(void*)*1, v___x_3017_);
lean_inc_ref(v_a_2953_);
v___x_3019_ = lean_apply_2(v_a_2953_, v___x_3018_, lean_box(0));
v___x_3020_ = lean_box(0);
v___x_3021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3021_, 0, v___x_3020_);
return v___x_3021_;
}
}
v___jp_3025_:
{
uint8_t v___x_3027_; 
v___x_3027_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_3027_ == 0)
{
v_a_2984_ = v_val_3026_;
goto v___jp_2983_;
}
else
{
lean_object* v___x_3028_; size_t v___x_3029_; size_t v___x_3030_; lean_object* v___x_1931__overap_3031_; lean_object* v___x_3032_; 
v___x_3028_ = lean_box(0);
v___x_3029_ = ((size_t)0ULL);
v___x_3030_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_1931__overap_3031_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3022_, v___f_2960_, v___x_3024_, v___x_3029_, v___x_3030_, v___x_3028_);
lean_inc_ref(v_a_2953_);
v___x_3032_ = lean_apply_2(v___x_1931__overap_3031_, v_a_2953_, lean_box(0));
if (lean_obj_tag(v___x_3032_) == 0)
{
lean_dec_ref_known(v___x_3032_, 1);
v_a_2984_ = v_val_3026_;
goto v___jp_2983_;
}
else
{
lean_object* v_a_3033_; lean_object* v___x_3035_; uint8_t v_isShared_3036_; uint8_t v_isSharedCheck_3040_; 
lean_dec(v_val_3026_);
lean_dec_ref(v_pkgDir_2982_);
lean_dec_ref(v_remoteUrl_2952_);
lean_dec_ref(v_relPkgDir_2951_);
lean_dec_ref(v_manifestEntry_2949_);
v_a_3033_ = lean_ctor_get(v___x_3032_, 0);
v_isSharedCheck_3040_ = !lean_is_exclusive(v___x_3032_);
if (v_isSharedCheck_3040_ == 0)
{
v___x_3035_ = v___x_3032_;
v_isShared_3036_ = v_isSharedCheck_3040_;
goto v_resetjp_3034_;
}
else
{
lean_inc(v_a_3033_);
lean_dec(v___x_3032_);
v___x_3035_ = lean_box(0);
v_isShared_3036_ = v_isSharedCheck_3040_;
goto v_resetjp_3034_;
}
v_resetjp_3034_:
{
lean_object* v___x_3038_; 
if (v_isShared_3036_ == 0)
{
v___x_3038_ = v___x_3035_;
goto v_reusejp_3037_;
}
else
{
lean_object* v_reuseFailAlloc_3039_; 
v_reuseFailAlloc_3039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3039_, 0, v_a_3033_);
v___x_3038_ = v_reuseFailAlloc_3039_;
goto v_reusejp_3037_;
}
v_reusejp_3037_:
{
return v___x_3038_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep_0interp(lean_interpreter_value* stack)
{
lean_object* v_manifestEntry_2949_ = stack[0].m_obj;
lean_object* v_wsDir_2950_ = stack[1].m_obj;
lean_object* v_relPkgDir_2951_ = stack[2].m_obj;
lean_object* v_remoteUrl_2952_ = stack[3].m_obj;
lean_object* v_a_2953_ = stack[4].m_obj;
lean_object* v_res_3046_;
v_res_3046_ = l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep(v_manifestEntry_2949_, v_wsDir_2950_, v_relPkgDir_2951_, v_remoteUrl_2952_, v_a_2953_);
stack->m_obj
 = v_res_3046_;
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___boxed(lean_object* v_manifestEntry_3047_, lean_object* v_wsDir_3048_, lean_object* v_relPkgDir_3049_, lean_object* v_remoteUrl_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_){
_start:
{
lean_object* v_res_3053_; 
v_res_3053_ = l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep(v_manifestEntry_3047_, v_wsDir_3048_, v_relPkgDir_3049_, v_remoteUrl_3050_, v_a_3051_);
lean_dec_ref(v_a_3051_);
return v_res_3053_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lake_PackageEntry_materialize_spec__0___redArg(lean_object* v_t_3054_, lean_object* v_k_3055_, lean_object* v_fallback_3056_){
_start:
{
if (lean_obj_tag(v_t_3054_) == 0)
{
lean_object* v_k_3057_; lean_object* v_v_3058_; lean_object* v_l_3059_; lean_object* v_r_3060_; uint8_t v___x_3061_; 
v_k_3057_ = lean_ctor_get(v_t_3054_, 1);
v_v_3058_ = lean_ctor_get(v_t_3054_, 2);
v_l_3059_ = lean_ctor_get(v_t_3054_, 3);
v_r_3060_ = lean_ctor_get(v_t_3054_, 4);
v___x_3061_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3055_, v_k_3057_);
switch(v___x_3061_)
{
case 0:
{
v_t_3054_ = v_l_3059_;
goto _start;
}
case 1:
{
lean_inc(v_v_3058_);
return v_v_3058_;
}
default: 
{
v_t_3054_ = v_r_3060_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_3056_);
return v_fallback_3056_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lake_PackageEntry_materialize_spec__0___redArg___boxed(lean_object* v_t_3064_, lean_object* v_k_3065_, lean_object* v_fallback_3066_){
_start:
{
lean_object* v_res_3067_; 
v_res_3067_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lake_PackageEntry_materialize_spec__0___redArg(v_t_3064_, v_k_3065_, v_fallback_3066_);
lean_dec(v_fallback_3066_);
lean_dec(v_k_3065_);
lean_dec(v_t_3064_);
return v_res_3067_;
}
}
lean_object* l_Lake_PackageEntry_materialize(lean_object* v_manifestEntry_3068_, lean_object* v_lakeEnv_3069_, lean_object* v_wsDir_3070_, lean_object* v_relPkgsDir_3071_, lean_object* v_a_3072_){
_start:
{
lean_object* v___y_3075_; lean_object* v___y_3076_; lean_object* v___y_3077_; lean_object* v_a_3078_; lean_object* v___y_3082_; lean_object* v___y_3083_; lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v_val_3087_; lean_object* v___y_3103_; lean_object* v___y_3104_; lean_object* v___y_3105_; lean_object* v_a_3106_; lean_object* v___y_3110_; lean_object* v___y_3111_; lean_object* v___y_3112_; lean_object* v___y_3113_; lean_object* v___y_3114_; lean_object* v_val_3115_; lean_object* v_name_3130_; lean_object* v_manifestFile_x3f_3131_; lean_object* v_src_3132_; lean_object* v___y_3134_; lean_object* v___y_3135_; lean_object* v___y_3136_; lean_object* v_a_3137_; lean_object* v___y_3181_; lean_object* v___y_3182_; lean_object* v___y_3183_; lean_object* v___y_3184_; lean_object* v___y_3185_; lean_object* v_val_3186_; lean_object* v_a_3202_; 
v_name_3130_ = lean_ctor_get(v_manifestEntry_3068_, 0);
v_manifestFile_x3f_3131_ = lean_ctor_get(v_manifestEntry_3068_, 3);
v_src_3132_ = lean_ctor_get(v_manifestEntry_3068_, 4);
lean_inc_ref(v_src_3132_);
if (lean_obj_tag(v_src_3132_) == 0)
{
uint8_t v_copy_3212_; 
v_copy_3212_ = lean_ctor_get_uint8(v_src_3132_, sizeof(void*)*1);
if (v_copy_3212_ == 0)
{
lean_object* v_dir_3213_; 
lean_dec_ref(v_relPkgsDir_3071_);
v_dir_3213_ = lean_ctor_get(v_src_3132_, 0);
lean_inc_ref(v_dir_3213_);
lean_dec_ref_known(v_src_3132_, 1);
v_a_3202_ = v_dir_3213_;
goto v___jp_3201_;
}
else
{
lean_object* v_dir_3214_; lean_object* v___x_3216_; uint8_t v_isShared_3217_; uint8_t v_isSharedCheck_3240_; 
v_dir_3214_ = lean_ctor_get(v_src_3132_, 0);
v_isSharedCheck_3240_ = !lean_is_exclusive(v_src_3132_);
if (v_isSharedCheck_3240_ == 0)
{
v___x_3216_ = v_src_3132_;
v_isShared_3217_ = v_isSharedCheck_3240_;
goto v_resetjp_3215_;
}
else
{
lean_inc(v_dir_3214_);
lean_dec(v_src_3132_);
v___x_3216_ = lean_box(0);
v_isShared_3217_ = v_isSharedCheck_3240_;
goto v_resetjp_3215_;
}
v_resetjp_3215_:
{
uint8_t v___x_3218_; lean_object* v___x_3219_; lean_object* v_relDst_3220_; lean_object* v_dst_3221_; uint8_t v___x_3222_; 
v___x_3218_ = 0;
lean_inc(v_name_3130_);
v___x_3219_ = l_Lean_Name_toString(v_name_3130_, v___x_3218_);
v_relDst_3220_ = l_Lake_joinRelative(v_relPkgsDir_3071_, v___x_3219_);
lean_inc_ref(v_relDst_3220_);
lean_inc_ref(v_wsDir_3070_);
v_dst_3221_ = l_Lake_joinRelative(v_wsDir_3070_, v_relDst_3220_);
v___x_3222_ = l_System_FilePath_pathExists(v_dst_3221_);
if (v___x_3222_ == 0)
{
lean_object* v_src_3223_; lean_object* v___x_3224_; 
lean_inc_ref(v_wsDir_3070_);
v_src_3223_ = l_Lake_joinRelative(v_wsDir_3070_, v_dir_3214_);
v___x_3224_ = l_Lake_copyDirAll(v_src_3223_, v_dst_3221_);
if (lean_obj_tag(v___x_3224_) == 0)
{
lean_dec_ref_known(v___x_3224_, 1);
lean_del_object(v___x_3216_);
v_a_3202_ = v_relDst_3220_;
goto v___jp_3201_;
}
else
{
lean_object* v_a_3225_; lean_object* v___x_3227_; uint8_t v_isShared_3228_; uint8_t v_isSharedCheck_3239_; 
lean_dec_ref(v_relDst_3220_);
lean_dec_ref(v_wsDir_3070_);
lean_dec_ref(v_manifestEntry_3068_);
v_a_3225_ = lean_ctor_get(v___x_3224_, 0);
v_isSharedCheck_3239_ = !lean_is_exclusive(v___x_3224_);
if (v_isSharedCheck_3239_ == 0)
{
v___x_3227_ = v___x_3224_;
v_isShared_3228_ = v_isSharedCheck_3239_;
goto v_resetjp_3226_;
}
else
{
lean_inc(v_a_3225_);
lean_dec(v___x_3224_);
v___x_3227_ = lean_box(0);
v_isShared_3228_ = v_isSharedCheck_3239_;
goto v_resetjp_3226_;
}
v_resetjp_3226_:
{
lean_object* v___x_3229_; uint8_t v___x_3230_; lean_object* v___x_3232_; 
v___x_3229_ = lean_io_error_to_string(v_a_3225_);
v___x_3230_ = 3;
if (v_isShared_3217_ == 0)
{
lean_ctor_set(v___x_3216_, 0, v___x_3229_);
v___x_3232_ = v___x_3216_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3238_; 
v_reuseFailAlloc_3238_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3238_, 0, v___x_3229_);
v___x_3232_ = v_reuseFailAlloc_3238_;
goto v_reusejp_3231_;
}
v_reusejp_3231_:
{
lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3236_; 
lean_ctor_set_uint8(v___x_3232_, sizeof(void*)*1, v___x_3230_);
lean_inc_ref(v_a_3072_);
v___x_3233_ = lean_apply_2(v_a_3072_, v___x_3232_, lean_box(0));
v___x_3234_ = lean_box(0);
if (v_isShared_3228_ == 0)
{
lean_ctor_set(v___x_3227_, 0, v___x_3234_);
v___x_3236_ = v___x_3227_;
goto v_reusejp_3235_;
}
else
{
lean_object* v_reuseFailAlloc_3237_; 
v_reuseFailAlloc_3237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3237_, 0, v___x_3234_);
v___x_3236_ = v_reuseFailAlloc_3237_;
goto v_reusejp_3235_;
}
v_reusejp_3235_:
{
return v___x_3236_;
}
}
}
}
}
else
{
lean_dec_ref(v_dst_3221_);
lean_del_object(v___x_3216_);
lean_dec_ref(v_dir_3214_);
v_a_3202_ = v_relDst_3220_;
goto v___jp_3201_;
}
}
}
}
else
{
lean_object* v_url_3241_; lean_object* v_rev_3242_; lean_object* v_subDir_x3f_3243_; lean_object* v_pkgUrlMap_3244_; uint8_t v___x_3245_; lean_object* v___x_3246_; lean_object* v___y_3248_; lean_object* v___y_3249_; lean_object* v___y_3250_; lean_object* v_a_3251_; lean_object* v___y_3285_; lean_object* v___y_3286_; lean_object* v___y_3287_; lean_object* v___y_3288_; lean_object* v___y_3289_; lean_object* v_val_3290_; lean_object* v_relGitDir_3305_; lean_object* v_repo_3306_; lean_object* v_url_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; 
v_url_3241_ = lean_ctor_get(v_src_3132_, 0);
lean_inc_ref(v_url_3241_);
v_rev_3242_ = lean_ctor_get(v_src_3132_, 1);
lean_inc_ref(v_rev_3242_);
v_subDir_x3f_3243_ = lean_ctor_get(v_src_3132_, 3);
lean_inc(v_subDir_x3f_3243_);
lean_dec_ref_known(v_src_3132_, 4);
v_pkgUrlMap_3244_ = lean_ctor_get(v_lakeEnv_3069_, 5);
v___x_3245_ = 0;
lean_inc(v_name_3130_);
v___x_3246_ = l_Lean_Name_toString(v_name_3130_, v___x_3245_);
lean_inc_ref_n(v___x_3246_, 2);
v_relGitDir_3305_ = l_Lake_joinRelative(v_relPkgsDir_3071_, v___x_3246_);
lean_inc_ref(v_relGitDir_3305_);
lean_inc_ref(v_wsDir_3070_);
v_repo_3306_ = l_Lake_joinRelative(v_wsDir_3070_, v_relGitDir_3305_);
v_url_3307_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lake_PackageEntry_materialize_spec__0___redArg(v_pkgUrlMap_3244_, v_name_3130_, v_url_3241_);
lean_dec_ref(v_url_3241_);
v___x_3308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3308_, 0, v_rev_3242_);
lean_inc(v_url_3307_);
v___x_3309_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(v_a_3072_, v___x_3246_, v_repo_3306_, v_url_3307_, v___x_3308_);
if (lean_obj_tag(v___x_3309_) == 0)
{
lean_object* v___y_3311_; lean_object* v___y_3312_; lean_object* v___y_3322_; 
lean_dec_ref_known(v___x_3309_, 1);
if (lean_obj_tag(v_subDir_x3f_3243_) == 0)
{
v___y_3322_ = v_relGitDir_3305_;
goto v___jp_3321_;
}
else
{
lean_object* v_val_3326_; lean_object* v___x_3327_; 
v_val_3326_ = lean_ctor_get(v_subDir_x3f_3243_, 0);
lean_inc(v_val_3326_);
lean_dec_ref_known(v_subDir_x3f_3243_, 1);
v___x_3327_ = l_Lake_joinRelative(v_relGitDir_3305_, v_val_3326_);
v___y_3322_ = v___x_3327_;
goto v___jp_3321_;
}
v___jp_3310_:
{
lean_object* v_pkgDir_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; uint8_t v___x_3318_; 
lean_inc_ref(v___y_3311_);
v_pkgDir_3313_ = l_Lake_joinRelative(v_wsDir_3070_, v___y_3311_);
v___x_3314_ = lean_unsigned_to_nat(0u);
v___x_3315_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_pkgDir_3313_);
v___x_3316_ = l_Lake_resolvePath(v_pkgDir_3313_);
v___x_3317_ = lean_string_utf8_byte_size(v___x_3316_);
v___x_3318_ = lean_nat_dec_eq(v___x_3317_, v___x_3314_);
if (v___x_3318_ == 0)
{
lean_object* v___x_3319_; 
v___x_3319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3319_, 0, v___x_3316_);
v___y_3285_ = v___x_3315_;
v___y_3286_ = v___y_3311_;
v___y_3287_ = v___x_3314_;
v___y_3288_ = v_pkgDir_3313_;
v___y_3289_ = v___y_3312_;
v_val_3290_ = v___x_3319_;
goto v___jp_3284_;
}
else
{
lean_object* v___x_3320_; 
lean_dec_ref(v___x_3316_);
v___x_3320_ = lean_box(0);
v___y_3285_ = v___x_3315_;
v___y_3286_ = v___y_3311_;
v___y_3287_ = v___x_3314_;
v___y_3288_ = v_pkgDir_3313_;
v___y_3289_ = v___y_3312_;
v_val_3290_ = v___x_3320_;
goto v___jp_3284_;
}
}
v___jp_3321_:
{
lean_object* v___x_3323_; 
v___x_3323_ = l_Lake_Git_filterUrl_x3f(v_url_3307_);
if (lean_obj_tag(v___x_3323_) == 0)
{
lean_object* v___x_3324_; 
v___x_3324_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___y_3311_ = v___y_3322_;
v___y_3312_ = v___x_3324_;
goto v___jp_3310_;
}
else
{
lean_object* v_val_3325_; 
v_val_3325_ = lean_ctor_get(v___x_3323_, 0);
lean_inc(v_val_3325_);
lean_dec_ref_known(v___x_3323_, 1);
v___y_3311_ = v___y_3322_;
v___y_3312_ = v_val_3325_;
goto v___jp_3310_;
}
}
}
else
{
lean_object* v_a_3328_; lean_object* v___x_3330_; uint8_t v_isShared_3331_; uint8_t v_isSharedCheck_3335_; 
lean_dec(v_url_3307_);
lean_dec_ref(v_relGitDir_3305_);
lean_dec_ref(v___x_3246_);
lean_dec(v_subDir_x3f_3243_);
lean_dec_ref(v_wsDir_3070_);
lean_dec_ref(v_manifestEntry_3068_);
v_a_3328_ = lean_ctor_get(v___x_3309_, 0);
v_isSharedCheck_3335_ = !lean_is_exclusive(v___x_3309_);
if (v_isSharedCheck_3335_ == 0)
{
v___x_3330_ = v___x_3309_;
v_isShared_3331_ = v_isSharedCheck_3335_;
goto v_resetjp_3329_;
}
else
{
lean_inc(v_a_3328_);
lean_dec(v___x_3309_);
v___x_3330_ = lean_box(0);
v_isShared_3331_ = v_isSharedCheck_3335_;
goto v_resetjp_3329_;
}
v_resetjp_3329_:
{
lean_object* v___x_3333_; 
if (v_isShared_3331_ == 0)
{
v___x_3333_ = v___x_3330_;
goto v_reusejp_3332_;
}
else
{
lean_object* v_reuseFailAlloc_3334_; 
v_reuseFailAlloc_3334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3334_, 0, v_a_3328_);
v___x_3333_ = v_reuseFailAlloc_3334_;
goto v_reusejp_3332_;
}
v_reusejp_3332_:
{
return v___x_3333_;
}
}
}
v___jp_3247_:
{
if (lean_obj_tag(v_a_3251_) == 1)
{
lean_dec_ref(v___y_3249_);
lean_dec_ref(v___x_3246_);
if (lean_obj_tag(v_manifestFile_x3f_3131_) == 1)
{
lean_object* v_val_3252_; lean_object* v_val_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; 
v_val_3252_ = lean_ctor_get(v_a_3251_, 0);
lean_inc_n(v_val_3252_, 2);
lean_dec_ref_known(v_a_3251_, 1);
v_val_3253_ = lean_ctor_get(v_manifestFile_x3f_3131_, 0);
lean_inc(v_val_3253_);
v___x_3254_ = l_Lake_joinRelative(v_val_3252_, v_val_3253_);
v___x_3255_ = lean_unsigned_to_nat(0u);
v___x_3256_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_3257_ = l_Lake_Manifest_load(v___x_3254_);
if (lean_obj_tag(v___x_3257_) == 0)
{
lean_object* v_a_3258_; lean_object* v___x_3260_; uint8_t v_isShared_3261_; uint8_t v_isSharedCheck_3265_; 
v_a_3258_ = lean_ctor_get(v___x_3257_, 0);
v_isSharedCheck_3265_ = !lean_is_exclusive(v___x_3257_);
if (v_isSharedCheck_3265_ == 0)
{
v___x_3260_ = v___x_3257_;
v_isShared_3261_ = v_isSharedCheck_3265_;
goto v_resetjp_3259_;
}
else
{
lean_inc(v_a_3258_);
lean_dec(v___x_3257_);
v___x_3260_ = lean_box(0);
v_isShared_3261_ = v_isSharedCheck_3265_;
goto v_resetjp_3259_;
}
v_resetjp_3259_:
{
lean_object* v___x_3263_; 
if (v_isShared_3261_ == 0)
{
lean_ctor_set_tag(v___x_3260_, 1);
v___x_3263_ = v___x_3260_;
goto v_reusejp_3262_;
}
else
{
lean_object* v_reuseFailAlloc_3264_; 
v_reuseFailAlloc_3264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3264_, 0, v_a_3258_);
v___x_3263_ = v_reuseFailAlloc_3264_;
goto v_reusejp_3262_;
}
v_reusejp_3262_:
{
v___y_3082_ = v___x_3255_;
v___y_3083_ = v_val_3252_;
v___y_3084_ = v___y_3248_;
v___y_3085_ = v___x_3256_;
v___y_3086_ = v___y_3250_;
v_val_3087_ = v___x_3263_;
goto v___jp_3081_;
}
}
}
else
{
lean_object* v_a_3266_; lean_object* v___x_3268_; uint8_t v_isShared_3269_; uint8_t v_isSharedCheck_3273_; 
v_a_3266_ = lean_ctor_get(v___x_3257_, 0);
v_isSharedCheck_3273_ = !lean_is_exclusive(v___x_3257_);
if (v_isSharedCheck_3273_ == 0)
{
v___x_3268_ = v___x_3257_;
v_isShared_3269_ = v_isSharedCheck_3273_;
goto v_resetjp_3267_;
}
else
{
lean_inc(v_a_3266_);
lean_dec(v___x_3257_);
v___x_3268_ = lean_box(0);
v_isShared_3269_ = v_isSharedCheck_3273_;
goto v_resetjp_3267_;
}
v_resetjp_3267_:
{
lean_object* v___x_3271_; 
if (v_isShared_3269_ == 0)
{
lean_ctor_set_tag(v___x_3268_, 0);
v___x_3271_ = v___x_3268_;
goto v_reusejp_3270_;
}
else
{
lean_object* v_reuseFailAlloc_3272_; 
v_reuseFailAlloc_3272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3272_, 0, v_a_3266_);
v___x_3271_ = v_reuseFailAlloc_3272_;
goto v_reusejp_3270_;
}
v_reusejp_3270_:
{
v___y_3082_ = v___x_3255_;
v___y_3083_ = v_val_3252_;
v___y_3084_ = v___y_3248_;
v___y_3085_ = v___x_3256_;
v___y_3086_ = v___y_3250_;
v_val_3087_ = v___x_3271_;
goto v___jp_3081_;
}
}
}
}
else
{
lean_object* v_val_3274_; lean_object* v___x_3275_; 
v_val_3274_ = lean_ctor_get(v_a_3251_, 0);
lean_inc(v_val_3274_);
lean_dec_ref_known(v_a_3251_, 1);
v___x_3275_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1));
v___y_3075_ = v___y_3248_;
v___y_3076_ = v_val_3274_;
v___y_3077_ = v___y_3250_;
v_a_3078_ = v___x_3275_;
goto v___jp_3074_;
}
}
else
{
lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; uint8_t v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; 
lean_dec(v_a_3251_);
lean_dec_ref(v___y_3250_);
lean_dec_ref(v___y_3248_);
lean_dec_ref(v_manifestEntry_3068_);
v___x_3276_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0));
v___x_3277_ = lean_string_append(v___x_3246_, v___x_3276_);
v___x_3278_ = lean_string_append(v___x_3277_, v___y_3249_);
lean_dec_ref(v___y_3249_);
v___x_3279_ = 3;
v___x_3280_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3280_, 0, v___x_3278_);
lean_ctor_set_uint8(v___x_3280_, sizeof(void*)*1, v___x_3279_);
lean_inc_ref(v_a_3072_);
v___x_3281_ = lean_apply_2(v_a_3072_, v___x_3280_, lean_box(0));
v___x_3282_ = lean_box(0);
v___x_3283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3283_, 0, v___x_3282_);
return v___x_3283_;
}
}
v___jp_3284_:
{
lean_object* v___x_3291_; uint8_t v___x_3292_; 
v___x_3291_ = lean_array_get_size(v___y_3285_);
v___x_3292_ = lean_nat_dec_lt(v___y_3287_, v___x_3291_);
if (v___x_3292_ == 0)
{
v___y_3248_ = v___y_3286_;
v___y_3249_ = v___y_3288_;
v___y_3250_ = v___y_3289_;
v_a_3251_ = v_val_3290_;
goto v___jp_3247_;
}
else
{
lean_object* v___x_3293_; size_t v___x_3294_; size_t v___x_3295_; lean_object* v___x_3296_; 
v___x_3293_ = lean_box(0);
v___x_3294_ = ((size_t)0ULL);
v___x_3295_ = lean_usize_of_nat(v___x_3291_);
v___x_3296_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_3285_, v___x_3294_, v___x_3295_, v___x_3293_, v_a_3072_);
if (lean_obj_tag(v___x_3296_) == 0)
{
lean_dec_ref_known(v___x_3296_, 1);
v___y_3248_ = v___y_3286_;
v___y_3249_ = v___y_3288_;
v___y_3250_ = v___y_3289_;
v_a_3251_ = v_val_3290_;
goto v___jp_3247_;
}
else
{
lean_object* v_a_3297_; lean_object* v___x_3299_; uint8_t v_isShared_3300_; uint8_t v_isSharedCheck_3304_; 
lean_dec(v_val_3290_);
lean_dec_ref(v___y_3289_);
lean_dec_ref(v___y_3288_);
lean_dec_ref(v___y_3286_);
lean_dec_ref(v___x_3246_);
lean_dec_ref(v_manifestEntry_3068_);
v_a_3297_ = lean_ctor_get(v___x_3296_, 0);
v_isSharedCheck_3304_ = !lean_is_exclusive(v___x_3296_);
if (v_isSharedCheck_3304_ == 0)
{
v___x_3299_ = v___x_3296_;
v_isShared_3300_ = v_isSharedCheck_3304_;
goto v_resetjp_3298_;
}
else
{
lean_inc(v_a_3297_);
lean_dec(v___x_3296_);
v___x_3299_ = lean_box(0);
v_isShared_3300_ = v_isSharedCheck_3304_;
goto v_resetjp_3298_;
}
v_resetjp_3298_:
{
lean_object* v___x_3302_; 
if (v_isShared_3300_ == 0)
{
v___x_3302_ = v___x_3299_;
goto v_reusejp_3301_;
}
else
{
lean_object* v_reuseFailAlloc_3303_; 
v_reuseFailAlloc_3303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3303_, 0, v_a_3297_);
v___x_3302_ = v_reuseFailAlloc_3303_;
goto v_reusejp_3301_;
}
v_reusejp_3301_:
{
return v___x_3302_;
}
}
}
}
}
}
v___jp_3074_:
{
lean_object* v___x_3079_; lean_object* v___x_3080_; 
v___x_3079_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3079_, 0, v___y_3076_);
lean_ctor_set(v___x_3079_, 1, v___y_3075_);
lean_ctor_set(v___x_3079_, 2, v___y_3077_);
lean_ctor_set(v___x_3079_, 3, v_a_3078_);
lean_ctor_set(v___x_3079_, 4, v_manifestEntry_3068_);
v___x_3080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3080_, 0, v___x_3079_);
return v___x_3080_;
}
v___jp_3081_:
{
lean_object* v___x_3088_; uint8_t v___x_3089_; 
v___x_3088_ = lean_array_get_size(v___y_3085_);
v___x_3089_ = lean_nat_dec_lt(v___y_3082_, v___x_3088_);
if (v___x_3089_ == 0)
{
v___y_3075_ = v___y_3084_;
v___y_3076_ = v___y_3083_;
v___y_3077_ = v___y_3086_;
v_a_3078_ = v_val_3087_;
goto v___jp_3074_;
}
else
{
lean_object* v___x_3090_; size_t v___x_3091_; size_t v___x_3092_; lean_object* v___x_3093_; 
v___x_3090_ = lean_box(0);
v___x_3091_ = ((size_t)0ULL);
v___x_3092_ = lean_usize_of_nat(v___x_3088_);
v___x_3093_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_3085_, v___x_3091_, v___x_3092_, v___x_3090_, v_a_3072_);
if (lean_obj_tag(v___x_3093_) == 0)
{
lean_dec_ref_known(v___x_3093_, 1);
v___y_3075_ = v___y_3084_;
v___y_3076_ = v___y_3083_;
v___y_3077_ = v___y_3086_;
v_a_3078_ = v_val_3087_;
goto v___jp_3074_;
}
else
{
lean_object* v_a_3094_; lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3101_; 
lean_dec_ref(v_val_3087_);
lean_dec_ref(v___y_3086_);
lean_dec_ref(v___y_3084_);
lean_dec_ref(v___y_3083_);
lean_dec_ref(v_manifestEntry_3068_);
v_a_3094_ = lean_ctor_get(v___x_3093_, 0);
v_isSharedCheck_3101_ = !lean_is_exclusive(v___x_3093_);
if (v_isSharedCheck_3101_ == 0)
{
v___x_3096_ = v___x_3093_;
v_isShared_3097_ = v_isSharedCheck_3101_;
goto v_resetjp_3095_;
}
else
{
lean_inc(v_a_3094_);
lean_dec(v___x_3093_);
v___x_3096_ = lean_box(0);
v_isShared_3097_ = v_isSharedCheck_3101_;
goto v_resetjp_3095_;
}
v_resetjp_3095_:
{
lean_object* v___x_3099_; 
if (v_isShared_3097_ == 0)
{
v___x_3099_ = v___x_3096_;
goto v_reusejp_3098_;
}
else
{
lean_object* v_reuseFailAlloc_3100_; 
v_reuseFailAlloc_3100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3100_, 0, v_a_3094_);
v___x_3099_ = v_reuseFailAlloc_3100_;
goto v_reusejp_3098_;
}
v_reusejp_3098_:
{
return v___x_3099_;
}
}
}
}
}
v___jp_3102_:
{
lean_object* v___x_3107_; lean_object* v___x_3108_; 
lean_inc_ref(v___y_3105_);
v___x_3107_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3107_, 0, v___y_3103_);
lean_ctor_set(v___x_3107_, 1, v___y_3104_);
lean_ctor_set(v___x_3107_, 2, v___y_3105_);
lean_ctor_set(v___x_3107_, 3, v_a_3106_);
lean_ctor_set(v___x_3107_, 4, v_manifestEntry_3068_);
v___x_3108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3108_, 0, v___x_3107_);
return v___x_3108_;
}
v___jp_3109_:
{
lean_object* v___x_3116_; uint8_t v___x_3117_; 
v___x_3116_ = lean_array_get_size(v___y_3114_);
v___x_3117_ = lean_nat_dec_lt(v___y_3111_, v___x_3116_);
if (v___x_3117_ == 0)
{
v___y_3103_ = v___y_3110_;
v___y_3104_ = v___y_3112_;
v___y_3105_ = v___y_3113_;
v_a_3106_ = v_val_3115_;
goto v___jp_3102_;
}
else
{
lean_object* v___x_3118_; size_t v___x_3119_; size_t v___x_3120_; lean_object* v___x_3121_; 
v___x_3118_ = lean_box(0);
v___x_3119_ = ((size_t)0ULL);
v___x_3120_ = lean_usize_of_nat(v___x_3116_);
v___x_3121_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_3114_, v___x_3119_, v___x_3120_, v___x_3118_, v_a_3072_);
if (lean_obj_tag(v___x_3121_) == 0)
{
lean_dec_ref_known(v___x_3121_, 1);
v___y_3103_ = v___y_3110_;
v___y_3104_ = v___y_3112_;
v___y_3105_ = v___y_3113_;
v_a_3106_ = v_val_3115_;
goto v___jp_3102_;
}
else
{
lean_object* v_a_3122_; lean_object* v___x_3124_; uint8_t v_isShared_3125_; uint8_t v_isSharedCheck_3129_; 
lean_dec_ref(v_val_3115_);
lean_dec_ref(v___y_3112_);
lean_dec_ref(v___y_3110_);
lean_dec_ref(v_manifestEntry_3068_);
v_a_3122_ = lean_ctor_get(v___x_3121_, 0);
v_isSharedCheck_3129_ = !lean_is_exclusive(v___x_3121_);
if (v_isSharedCheck_3129_ == 0)
{
v___x_3124_ = v___x_3121_;
v_isShared_3125_ = v_isSharedCheck_3129_;
goto v_resetjp_3123_;
}
else
{
lean_inc(v_a_3122_);
lean_dec(v___x_3121_);
v___x_3124_ = lean_box(0);
v_isShared_3125_ = v_isSharedCheck_3129_;
goto v_resetjp_3123_;
}
v_resetjp_3123_:
{
lean_object* v___x_3127_; 
if (v_isShared_3125_ == 0)
{
v___x_3127_ = v___x_3124_;
goto v_reusejp_3126_;
}
else
{
lean_object* v_reuseFailAlloc_3128_; 
v_reuseFailAlloc_3128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3128_, 0, v_a_3122_);
v___x_3127_ = v_reuseFailAlloc_3128_;
goto v_reusejp_3126_;
}
v_reusejp_3126_:
{
return v___x_3127_;
}
}
}
}
}
v___jp_3133_:
{
if (lean_obj_tag(v_a_3137_) == 1)
{
lean_dec_ref(v___y_3134_);
if (lean_obj_tag(v_manifestFile_x3f_3131_) == 1)
{
lean_object* v_val_3138_; lean_object* v_val_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; 
v_val_3138_ = lean_ctor_get(v_a_3137_, 0);
lean_inc_n(v_val_3138_, 2);
lean_dec_ref_known(v_a_3137_, 1);
v_val_3139_ = lean_ctor_get(v_manifestFile_x3f_3131_, 0);
lean_inc(v_val_3139_);
v___x_3140_ = l_Lake_joinRelative(v_val_3138_, v_val_3139_);
v___x_3141_ = lean_unsigned_to_nat(0u);
v___x_3142_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_3143_ = l_Lake_Manifest_load(v___x_3140_);
if (lean_obj_tag(v___x_3143_) == 0)
{
lean_object* v_a_3144_; lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3151_; 
v_a_3144_ = lean_ctor_get(v___x_3143_, 0);
v_isSharedCheck_3151_ = !lean_is_exclusive(v___x_3143_);
if (v_isSharedCheck_3151_ == 0)
{
v___x_3146_ = v___x_3143_;
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
else
{
lean_inc(v_a_3144_);
lean_dec(v___x_3143_);
v___x_3146_ = lean_box(0);
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
v_resetjp_3145_:
{
lean_object* v___x_3149_; 
if (v_isShared_3147_ == 0)
{
lean_ctor_set_tag(v___x_3146_, 1);
v___x_3149_ = v___x_3146_;
goto v_reusejp_3148_;
}
else
{
lean_object* v_reuseFailAlloc_3150_; 
v_reuseFailAlloc_3150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3150_, 0, v_a_3144_);
v___x_3149_ = v_reuseFailAlloc_3150_;
goto v_reusejp_3148_;
}
v_reusejp_3148_:
{
v___y_3110_ = v_val_3138_;
v___y_3111_ = v___x_3141_;
v___y_3112_ = v___y_3135_;
v___y_3113_ = v___y_3136_;
v___y_3114_ = v___x_3142_;
v_val_3115_ = v___x_3149_;
goto v___jp_3109_;
}
}
}
else
{
lean_object* v_a_3152_; lean_object* v___x_3154_; uint8_t v_isShared_3155_; uint8_t v_isSharedCheck_3159_; 
v_a_3152_ = lean_ctor_get(v___x_3143_, 0);
v_isSharedCheck_3159_ = !lean_is_exclusive(v___x_3143_);
if (v_isSharedCheck_3159_ == 0)
{
v___x_3154_ = v___x_3143_;
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
else
{
lean_inc(v_a_3152_);
lean_dec(v___x_3143_);
v___x_3154_ = lean_box(0);
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
v_resetjp_3153_:
{
lean_object* v___x_3157_; 
if (v_isShared_3155_ == 0)
{
lean_ctor_set_tag(v___x_3154_, 0);
v___x_3157_ = v___x_3154_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3158_; 
v_reuseFailAlloc_3158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3158_, 0, v_a_3152_);
v___x_3157_ = v_reuseFailAlloc_3158_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
v___y_3110_ = v_val_3138_;
v___y_3111_ = v___x_3141_;
v___y_3112_ = v___y_3135_;
v___y_3113_ = v___y_3136_;
v___y_3114_ = v___x_3142_;
v_val_3115_ = v___x_3157_;
goto v___jp_3109_;
}
}
}
}
else
{
lean_object* v_val_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3169_; 
v_val_3160_ = lean_ctor_get(v_a_3137_, 0);
v_isSharedCheck_3169_ = !lean_is_exclusive(v_a_3137_);
if (v_isSharedCheck_3169_ == 0)
{
v___x_3162_ = v_a_3137_;
v_isShared_3163_ = v_isSharedCheck_3169_;
goto v_resetjp_3161_;
}
else
{
lean_inc(v_val_3160_);
lean_dec(v_a_3137_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3169_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
uint32_t v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3167_; 
v___x_3164_ = 0;
lean_inc_ref_n(v___y_3136_, 2);
v___x_3165_ = lean_alloc_ctor(11, 2, 4);
lean_ctor_set(v___x_3165_, 0, v___y_3136_);
lean_ctor_set(v___x_3165_, 1, v___y_3136_);
lean_ctor_set_uint32(v___x_3165_, sizeof(void*)*2, v___x_3164_);
if (v_isShared_3163_ == 0)
{
lean_ctor_set_tag(v___x_3162_, 0);
lean_ctor_set(v___x_3162_, 0, v___x_3165_);
v___x_3167_ = v___x_3162_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3168_; 
v_reuseFailAlloc_3168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3168_, 0, v___x_3165_);
v___x_3167_ = v_reuseFailAlloc_3168_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
v___y_3103_ = v_val_3160_;
v___y_3104_ = v___y_3135_;
v___y_3105_ = v___y_3136_;
v_a_3106_ = v___x_3167_;
goto v___jp_3102_;
}
}
}
}
else
{
uint8_t v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; uint8_t v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; 
lean_inc(v_name_3130_);
lean_dec(v_a_3137_);
lean_dec_ref(v___y_3135_);
lean_dec_ref(v_manifestEntry_3068_);
v___x_3170_ = 0;
v___x_3171_ = l_Lean_Name_toString(v_name_3130_, v___x_3170_);
v___x_3172_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0));
v___x_3173_ = lean_string_append(v___x_3171_, v___x_3172_);
v___x_3174_ = lean_string_append(v___x_3173_, v___y_3134_);
lean_dec_ref(v___y_3134_);
v___x_3175_ = 3;
v___x_3176_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3176_, 0, v___x_3174_);
lean_ctor_set_uint8(v___x_3176_, sizeof(void*)*1, v___x_3175_);
lean_inc_ref(v_a_3072_);
v___x_3177_ = lean_apply_2(v_a_3072_, v___x_3176_, lean_box(0));
v___x_3178_ = lean_box(0);
v___x_3179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3179_, 0, v___x_3178_);
return v___x_3179_;
}
}
v___jp_3180_:
{
lean_object* v___x_3187_; uint8_t v___x_3188_; 
v___x_3187_ = lean_array_get_size(v___y_3183_);
v___x_3188_ = lean_nat_dec_lt(v___y_3185_, v___x_3187_);
if (v___x_3188_ == 0)
{
v___y_3134_ = v___y_3181_;
v___y_3135_ = v___y_3182_;
v___y_3136_ = v___y_3184_;
v_a_3137_ = v_val_3186_;
goto v___jp_3133_;
}
else
{
lean_object* v___x_3189_; size_t v___x_3190_; size_t v___x_3191_; lean_object* v___x_3192_; 
v___x_3189_ = lean_box(0);
v___x_3190_ = ((size_t)0ULL);
v___x_3191_ = lean_usize_of_nat(v___x_3187_);
v___x_3192_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_3183_, v___x_3190_, v___x_3191_, v___x_3189_, v_a_3072_);
if (lean_obj_tag(v___x_3192_) == 0)
{
lean_dec_ref_known(v___x_3192_, 1);
v___y_3134_ = v___y_3181_;
v___y_3135_ = v___y_3182_;
v___y_3136_ = v___y_3184_;
v_a_3137_ = v_val_3186_;
goto v___jp_3133_;
}
else
{
lean_object* v_a_3193_; lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3200_; 
lean_dec(v_val_3186_);
lean_dec_ref(v___y_3182_);
lean_dec_ref(v___y_3181_);
lean_dec_ref(v_manifestEntry_3068_);
v_a_3193_ = lean_ctor_get(v___x_3192_, 0);
v_isSharedCheck_3200_ = !lean_is_exclusive(v___x_3192_);
if (v_isSharedCheck_3200_ == 0)
{
v___x_3195_ = v___x_3192_;
v_isShared_3196_ = v_isSharedCheck_3200_;
goto v_resetjp_3194_;
}
else
{
lean_inc(v_a_3193_);
lean_dec(v___x_3192_);
v___x_3195_ = lean_box(0);
v_isShared_3196_ = v_isSharedCheck_3200_;
goto v_resetjp_3194_;
}
v_resetjp_3194_:
{
lean_object* v___x_3198_; 
if (v_isShared_3196_ == 0)
{
v___x_3198_ = v___x_3195_;
goto v_reusejp_3197_;
}
else
{
lean_object* v_reuseFailAlloc_3199_; 
v_reuseFailAlloc_3199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3199_, 0, v_a_3193_);
v___x_3198_ = v_reuseFailAlloc_3199_;
goto v_reusejp_3197_;
}
v_reusejp_3197_:
{
return v___x_3198_;
}
}
}
}
}
v___jp_3201_:
{
lean_object* v___x_3203_; lean_object* v_pkgDir_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; uint8_t v___x_3209_; 
v___x_3203_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
lean_inc_ref(v_a_3202_);
v_pkgDir_3204_ = l_Lake_joinRelative(v_wsDir_3070_, v_a_3202_);
v___x_3205_ = lean_unsigned_to_nat(0u);
v___x_3206_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_pkgDir_3204_);
v___x_3207_ = l_Lake_resolvePath(v_pkgDir_3204_);
v___x_3208_ = lean_string_utf8_byte_size(v___x_3207_);
v___x_3209_ = lean_nat_dec_eq(v___x_3208_, v___x_3205_);
if (v___x_3209_ == 0)
{
lean_object* v___x_3210_; 
v___x_3210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3210_, 0, v___x_3207_);
v___y_3181_ = v_pkgDir_3204_;
v___y_3182_ = v_a_3202_;
v___y_3183_ = v___x_3206_;
v___y_3184_ = v___x_3203_;
v___y_3185_ = v___x_3205_;
v_val_3186_ = v___x_3210_;
goto v___jp_3180_;
}
else
{
lean_object* v___x_3211_; 
lean_dec_ref(v___x_3207_);
v___x_3211_ = lean_box(0);
v___y_3181_ = v_pkgDir_3204_;
v___y_3182_ = v_a_3202_;
v___y_3183_ = v___x_3206_;
v___y_3184_ = v___x_3203_;
v___y_3185_ = v___x_3205_;
v_val_3186_ = v___x_3211_;
goto v___jp_3180_;
}
}
}
}
LEAN_EXPORT void l_Lake_PackageEntry_materialize_0interp(lean_interpreter_value* stack)
{
lean_object* v_manifestEntry_3068_ = stack[0].m_obj;
lean_object* v_lakeEnv_3069_ = stack[1].m_obj;
lean_object* v_wsDir_3070_ = stack[2].m_obj;
lean_object* v_relPkgsDir_3071_ = stack[3].m_obj;
lean_object* v_a_3072_ = stack[4].m_obj;
lean_object* v_res_3336_;
v_res_3336_ = l_Lake_PackageEntry_materialize(v_manifestEntry_3068_, v_lakeEnv_3069_, v_wsDir_3070_, v_relPkgsDir_3071_, v_a_3072_);
stack->m_obj
 = v_res_3336_;
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize___boxed(lean_object* v_manifestEntry_3337_, lean_object* v_lakeEnv_3338_, lean_object* v_wsDir_3339_, lean_object* v_relPkgsDir_3340_, lean_object* v_a_3341_, lean_object* v_a_3342_){
_start:
{
lean_object* v_res_3343_; 
v_res_3343_ = l_Lake_PackageEntry_materialize(v_manifestEntry_3337_, v_lakeEnv_3338_, v_wsDir_3339_, v_relPkgsDir_3340_, v_a_3341_);
lean_dec_ref(v_a_3341_);
lean_dec_ref(v_lakeEnv_3338_);
return v_res_3343_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lake_PackageEntry_materialize_spec__0(lean_object* v_00_u03b4_3344_, lean_object* v_t_3345_, lean_object* v_k_3346_, lean_object* v_fallback_3347_){
_start:
{
lean_object* v___x_3348_; 
v___x_3348_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lake_PackageEntry_materialize_spec__0___redArg(v_t_3345_, v_k_3346_, v_fallback_3347_);
return v___x_3348_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lake_PackageEntry_materialize_spec__0___boxed(lean_object* v_00_u03b4_3349_, lean_object* v_t_3350_, lean_object* v_k_3351_, lean_object* v_fallback_3352_){
_start:
{
lean_object* v_res_3353_; 
v_res_3353_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lake_PackageEntry_materialize_spec__0(v_00_u03b4_3349_, v_t_3350_, v_k_3351_, v_fallback_3352_);
lean_dec(v_fallback_3352_);
lean_dec(v_k_3351_);
lean_dec(v_t_3350_);
return v_res_3353_;
}
}
lean_object* runtime_initialize_Lake_Config_Env(uint8_t builtin);
lean_object* runtime_initialize_Lake_Load_Manifest(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Package(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Git(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_IO(uint8_t builtin);
lean_object* runtime_initialize_Lake_Reservoir(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Load_Materialize(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
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

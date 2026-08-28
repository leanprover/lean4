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
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
extern lean_object* l_Lake_instInhabitedPackageEntry_default;
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = ": failed to resolve path:\n  "};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__0 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__0_value;
static lean_once_cell_t l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__1;
static lean_once_cell_t l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__2;
static const lean_closure_object l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3_value;
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
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___lam__0(lean_object* v_x_1_, lean_object* v___y_2_, lean_object* v___y_3_){
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
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___lam__0___boxed(lean_object* v_x_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___lam__0(v_x_7_, v___y_8_, v___y_9_);
lean_dec_ref(v___y_9_);
return v_res_11_;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__1(void){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = l_instMonadEIO(lean_box(0));
return v___x_13_;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__2(void){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_14_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__1, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__1_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__1);
v___x_15_ = l_ReaderT_instMonad___redArg(v___x_14_);
return v___x_15_;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__5(void){
_start:
{
lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_19_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_20_ = lean_array_get_size(v___x_19_);
return v___x_20_;
}
}
static uint8_t _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6(void){
_start:
{
lean_object* v___x_21_; lean_object* v___x_22_; uint8_t v___x_23_; 
v___x_21_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__5, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__5);
v___x_22_ = lean_unsigned_to_nat(0u);
v___x_23_ = lean_nat_dec_lt(v___x_22_, v___x_21_);
return v___x_23_;
}
}
static size_t _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7(void){
_start:
{
lean_object* v___x_24_; size_t v___x_25_; 
v___x_24_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__5, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__5);
v___x_25_ = lean_usize_of_nat(v___x_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl(lean_object* v_name_26_, lean_object* v_url_27_, lean_object* v_a_28_){
_start:
{
lean_object* v_a_31_; lean_object* v___x_48_; uint8_t v___x_49_; lean_object* v___f_50_; lean_object* v___y_52_; lean_object* v___y_53_; lean_object* v___y_54_; lean_object* v_val_55_; lean_object* v___x_80_; uint8_t v___x_81_; 
v___x_48_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__2, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__2_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__2);
v___x_49_ = l_System_FilePath_pathExists(v_url_27_);
v___f_50_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3));
v___x_80_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_81_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_81_ == 0)
{
goto v___jp_71_;
}
else
{
lean_object* v___x_82_; size_t v___x_83_; size_t v___x_84_; lean_object* v___x_1286__overap_85_; lean_object* v___x_86_; 
v___x_82_ = lean_box(0);
v___x_83_ = ((size_t)0ULL);
v___x_84_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_1286__overap_85_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_48_, v___f_50_, v___x_80_, v___x_83_, v___x_84_, v___x_82_);
lean_inc_ref(v_a_28_);
v___x_86_ = lean_apply_2(v___x_1286__overap_85_, v_a_28_, lean_box(0));
if (lean_obj_tag(v___x_86_) == 0)
{
lean_dec_ref_known(v___x_86_, 1);
goto v___jp_71_;
}
else
{
lean_object* v_a_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_94_; 
lean_dec_ref(v_url_27_);
lean_dec_ref(v_name_26_);
v_a_87_ = lean_ctor_get(v___x_86_, 0);
v_isSharedCheck_94_ = !lean_is_exclusive(v___x_86_);
if (v_isSharedCheck_94_ == 0)
{
v___x_89_ = v___x_86_;
v_isShared_90_ = v_isSharedCheck_94_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_a_87_);
lean_dec(v___x_86_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_94_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v___x_92_; 
if (v_isShared_90_ == 0)
{
v___x_92_ = v___x_89_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v_a_87_);
v___x_92_ = v_reuseFailAlloc_93_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
return v___x_92_;
}
}
}
}
v___jp_30_:
{
if (lean_obj_tag(v_a_31_) == 1)
{
lean_object* v_val_32_; lean_object* v___x_34_; uint8_t v_isShared_35_; uint8_t v_isSharedCheck_39_; 
lean_dec_ref(v_url_27_);
lean_dec_ref(v_name_26_);
v_val_32_ = lean_ctor_get(v_a_31_, 0);
v_isSharedCheck_39_ = !lean_is_exclusive(v_a_31_);
if (v_isSharedCheck_39_ == 0)
{
v___x_34_ = v_a_31_;
v_isShared_35_ = v_isSharedCheck_39_;
goto v_resetjp_33_;
}
else
{
lean_inc(v_val_32_);
lean_dec(v_a_31_);
v___x_34_ = lean_box(0);
v_isShared_35_ = v_isSharedCheck_39_;
goto v_resetjp_33_;
}
v_resetjp_33_:
{
lean_object* v___x_37_; 
if (v_isShared_35_ == 0)
{
lean_ctor_set_tag(v___x_34_, 0);
v___x_37_ = v___x_34_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v_val_32_);
v___x_37_ = v_reuseFailAlloc_38_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
return v___x_37_;
}
}
}
else
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; uint8_t v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
lean_dec(v_a_31_);
v___x_40_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__0));
v___x_41_ = lean_string_append(v_name_26_, v___x_40_);
v___x_42_ = lean_string_append(v___x_41_, v_url_27_);
lean_dec_ref(v_url_27_);
v___x_43_ = 3;
v___x_44_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_44_, 0, v___x_42_);
lean_ctor_set_uint8(v___x_44_, sizeof(void*)*1, v___x_43_);
lean_inc_ref(v_a_28_);
v___x_45_ = lean_apply_2(v_a_28_, v___x_44_, lean_box(0));
v___x_46_ = lean_box(0);
v___x_47_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_47_, 0, v___x_46_);
return v___x_47_;
}
}
v___jp_51_:
{
lean_object* v___x_56_; uint8_t v___x_57_; 
v___x_56_ = lean_array_get_size(v___y_52_);
v___x_57_ = lean_nat_dec_lt(v___y_54_, v___x_56_);
if (v___x_57_ == 0)
{
lean_dec_ref(v___y_53_);
v_a_31_ = v_val_55_;
goto v___jp_30_;
}
else
{
lean_object* v___x_58_; size_t v___x_59_; size_t v___x_60_; lean_object* v___x_1563__overap_61_; lean_object* v___x_62_; 
v___x_58_ = lean_box(0);
v___x_59_ = ((size_t)0ULL);
v___x_60_ = lean_usize_of_nat(v___x_56_);
lean_inc_ref(v___y_52_);
v___x_1563__overap_61_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___y_53_, v___f_50_, v___y_52_, v___x_59_, v___x_60_, v___x_58_);
lean_inc_ref(v_a_28_);
v___x_62_ = lean_apply_2(v___x_1563__overap_61_, v_a_28_, lean_box(0));
if (lean_obj_tag(v___x_62_) == 0)
{
lean_dec_ref_known(v___x_62_, 1);
v_a_31_ = v_val_55_;
goto v___jp_30_;
}
else
{
lean_object* v_a_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_70_; 
lean_dec(v_val_55_);
lean_dec_ref(v_url_27_);
lean_dec_ref(v_name_26_);
v_a_63_ = lean_ctor_get(v___x_62_, 0);
v_isSharedCheck_70_ = !lean_is_exclusive(v___x_62_);
if (v_isSharedCheck_70_ == 0)
{
v___x_65_ = v___x_62_;
v_isShared_66_ = v_isSharedCheck_70_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_a_63_);
lean_dec(v___x_62_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_70_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
lean_object* v___x_68_; 
if (v_isShared_66_ == 0)
{
v___x_68_ = v___x_65_;
goto v_reusejp_67_;
}
else
{
lean_object* v_reuseFailAlloc_69_; 
v_reuseFailAlloc_69_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_69_, 0, v_a_63_);
v___x_68_ = v_reuseFailAlloc_69_;
goto v_reusejp_67_;
}
v_reusejp_67_:
{
return v___x_68_;
}
}
}
}
}
v___jp_71_:
{
if (v___x_49_ == 0)
{
lean_object* v___x_72_; 
lean_dec_ref(v_name_26_);
v___x_72_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_72_, 0, v_url_27_);
return v___x_72_;
}
else
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; uint8_t v___x_77_; 
lean_inc_ref(v_url_27_);
v___x_73_ = l_Lake_resolvePath(v_url_27_);
v___x_74_ = lean_unsigned_to_nat(0u);
v___x_75_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_76_ = lean_string_utf8_byte_size(v___x_73_);
v___x_77_ = lean_nat_dec_eq(v___x_76_, v___x_74_);
if (v___x_77_ == 0)
{
lean_object* v___x_78_; 
v___x_78_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_78_, 0, v___x_73_);
v___y_52_ = v___x_75_;
v___y_53_ = v___x_48_;
v___y_54_ = v___x_74_;
v_val_55_ = v___x_78_;
goto v___jp_51_;
}
else
{
lean_object* v___x_79_; 
lean_dec_ref(v___x_73_);
v___x_79_ = lean_box(0);
v___y_52_ = v___x_75_;
v___y_53_ = v___x_48_;
v___y_54_ = v___x_74_;
v_val_55_ = v___x_79_;
goto v___jp_51_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___boxed(lean_object* v_name_95_, lean_object* v_url_96_, lean_object* v_a_97_, lean_object* v_a_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl(v_name_95_, v_url_96_, v_a_97_);
lean_dec_ref(v_a_97_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff(lean_object* v_name_101_, lean_object* v_repo_102_, lean_object* v_a_103_){
_start:
{
uint8_t v_a_106_; lean_object* v___x_116_; uint8_t v___x_117_; lean_object* v___f_118_; lean_object* v___x_119_; uint8_t v_val_121_; 
v___x_116_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__2, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__2_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__2);
lean_inc_ref(v_repo_102_);
v___x_117_ = l_Lake_GitRepo_hasNoDiff(v_repo_102_);
v___f_118_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3));
v___x_119_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
if (v___x_117_ == 0)
{
uint8_t v___x_128_; 
v___x_128_ = 1;
v_val_121_ = v___x_128_;
goto v___jp_120_;
}
else
{
uint8_t v___x_129_; 
v___x_129_ = 0;
v_val_121_ = v___x_129_;
goto v___jp_120_;
}
v___jp_105_:
{
if (v_a_106_ == 0)
{
lean_object* v___x_107_; lean_object* v___x_108_; 
lean_dec_ref(v_repo_102_);
lean_dec_ref(v_name_101_);
v___x_107_ = lean_box(0);
v___x_108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_108_, 0, v___x_107_);
return v___x_108_;
}
else
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; uint8_t v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_109_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff___closed__0));
v___x_110_ = lean_string_append(v_name_101_, v___x_109_);
v___x_111_ = lean_string_append(v___x_110_, v_repo_102_);
lean_dec_ref(v_repo_102_);
v___x_112_ = 2;
v___x_113_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_113_, 0, v___x_111_);
lean_ctor_set_uint8(v___x_113_, sizeof(void*)*1, v___x_112_);
lean_inc_ref(v_a_103_);
v___x_114_ = lean_apply_2(v_a_103_, v___x_113_, lean_box(0));
v___x_115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_115_, 0, v___x_114_);
return v___x_115_;
}
}
v___jp_120_:
{
uint8_t v___x_122_; 
v___x_122_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_122_ == 0)
{
v_a_106_ = v_val_121_;
goto v___jp_105_;
}
else
{
lean_object* v___x_123_; size_t v___x_124_; size_t v___x_125_; lean_object* v___x_786__overap_126_; lean_object* v___x_127_; 
v___x_123_ = lean_box(0);
v___x_124_ = ((size_t)0ULL);
v___x_125_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_786__overap_126_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_116_, v___f_118_, v___x_119_, v___x_124_, v___x_125_, v___x_123_);
lean_inc_ref(v_a_103_);
v___x_127_ = lean_apply_2(v___x_786__overap_126_, v_a_103_, lean_box(0));
if (lean_obj_tag(v___x_127_) == 0)
{
lean_dec_ref_known(v___x_127_, 1);
v_a_106_ = v_val_121_;
goto v___jp_105_;
}
else
{
lean_dec_ref(v_repo_102_);
lean_dec_ref(v_name_101_);
return v___x_127_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff___boxed(lean_object* v_name_130_, lean_object* v_repo_131_, lean_object* v_a_132_, lean_object* v_a_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff(v_name_130_, v_repo_131_, v_a_132_);
lean_dec_ref(v_a_132_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout(lean_object* v_name_137_, lean_object* v_repo_138_, lean_object* v_rev_139_, lean_object* v_a_140_){
_start:
{
uint8_t v_a_143_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; uint8_t v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___f_165_; lean_object* v___y_167_; lean_object* v___y_168_; lean_object* v___y_169_; uint8_t v_val_170_; lean_object* v___y_183_; lean_object* v___y_213_; 
v___x_153_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__0));
lean_inc_ref(v_name_137_);
v___x_154_ = lean_string_append(v_name_137_, v___x_153_);
v___x_155_ = lean_string_append(v___x_154_, v_rev_139_);
v___x_156_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__1));
v___x_157_ = lean_string_append(v___x_155_, v___x_156_);
v___x_158_ = 1;
v___x_159_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_159_, 0, v___x_157_);
lean_ctor_set_uint8(v___x_159_, sizeof(void*)*1, v___x_158_);
lean_inc_ref(v_a_140_);
v___x_160_ = lean_apply_2(v_a_140_, v___x_159_, lean_box(0));
v___x_161_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__2, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__2_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__2);
v___x_162_ = lean_unsigned_to_nat(0u);
v___x_163_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_138_);
v___x_164_ = l_Lake_GitRepo_checkoutDetach(v_rev_139_, v_repo_138_, v___x_163_);
v___f_165_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3));
if (lean_obj_tag(v___x_164_) == 0)
{
lean_object* v_a_214_; lean_object* v___x_215_; uint8_t v___x_216_; 
v_a_214_ = lean_ctor_get(v___x_164_, 1);
lean_inc(v_a_214_);
lean_dec_ref_known(v___x_164_, 2);
v___x_215_ = lean_array_get_size(v_a_214_);
v___x_216_ = lean_nat_dec_lt(v___x_162_, v___x_215_);
if (v___x_216_ == 0)
{
lean_dec(v_a_214_);
goto v___jp_184_;
}
else
{
lean_object* v___x_217_; size_t v___x_218_; size_t v___x_219_; lean_object* v___x_2319__overap_220_; lean_object* v___x_221_; 
v___x_217_ = lean_box(0);
v___x_218_ = ((size_t)0ULL);
v___x_219_ = lean_usize_of_nat(v___x_215_);
v___x_2319__overap_220_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_161_, v___f_165_, v_a_214_, v___x_218_, v___x_219_, v___x_217_);
lean_inc_ref(v_a_140_);
v___x_221_ = lean_apply_2(v___x_2319__overap_220_, v_a_140_, lean_box(0));
if (lean_obj_tag(v___x_221_) == 0)
{
lean_dec_ref_known(v___x_221_, 1);
goto v___jp_184_;
}
else
{
v___y_213_ = v___x_221_;
goto v___jp_212_;
}
}
}
else
{
lean_object* v_a_222_; lean_object* v___x_223_; uint8_t v___x_224_; 
v_a_222_ = lean_ctor_get(v___x_164_, 1);
lean_inc(v_a_222_);
lean_dec_ref_known(v___x_164_, 2);
v___x_223_ = lean_array_get_size(v_a_222_);
v___x_224_ = lean_nat_dec_lt(v___x_162_, v___x_223_);
if (v___x_224_ == 0)
{
lean_object* v___x_225_; lean_object* v___x_226_; 
lean_dec(v_a_222_);
lean_dec_ref(v_repo_138_);
lean_dec_ref(v_name_137_);
v___x_225_ = lean_box(0);
v___x_226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_226_, 0, v___x_225_);
return v___x_226_;
}
else
{
lean_object* v___x_227_; size_t v___x_228_; size_t v___x_229_; lean_object* v___x_2336__overap_230_; lean_object* v___x_231_; 
v___x_227_ = lean_box(0);
v___x_228_ = ((size_t)0ULL);
v___x_229_ = lean_usize_of_nat(v___x_223_);
v___x_2336__overap_230_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_161_, v___f_165_, v_a_222_, v___x_228_, v___x_229_, v___x_227_);
lean_inc_ref(v_a_140_);
v___x_231_ = lean_apply_2(v___x_2336__overap_230_, v_a_140_, lean_box(0));
if (lean_obj_tag(v___x_231_) == 0)
{
lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_238_; 
lean_dec_ref(v_repo_138_);
lean_dec_ref(v_name_137_);
v_isSharedCheck_238_ = !lean_is_exclusive(v___x_231_);
if (v_isSharedCheck_238_ == 0)
{
lean_object* v_unused_239_; 
v_unused_239_ = lean_ctor_get(v___x_231_, 0);
lean_dec(v_unused_239_);
v___x_233_ = v___x_231_;
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
else
{
lean_dec(v___x_231_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v___x_236_; 
if (v_isShared_234_ == 0)
{
lean_ctor_set_tag(v___x_233_, 1);
lean_ctor_set(v___x_233_, 0, v___x_227_);
v___x_236_ = v___x_233_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v___x_227_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
}
else
{
v___y_213_ = v___x_231_;
goto v___jp_212_;
}
}
}
v___jp_142_:
{
if (v_a_143_ == 0)
{
lean_object* v___x_144_; lean_object* v___x_145_; 
lean_dec_ref(v_repo_138_);
lean_dec_ref(v_name_137_);
v___x_144_ = lean_box(0);
v___x_145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_145_, 0, v___x_144_);
return v___x_145_;
}
else
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; uint8_t v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_146_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff___closed__0));
v___x_147_ = lean_string_append(v_name_137_, v___x_146_);
v___x_148_ = lean_string_append(v___x_147_, v_repo_138_);
lean_dec_ref(v_repo_138_);
v___x_149_ = 2;
v___x_150_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_150_, 0, v___x_148_);
lean_ctor_set_uint8(v___x_150_, sizeof(void*)*1, v___x_149_);
lean_inc_ref(v_a_140_);
v___x_151_ = lean_apply_2(v_a_140_, v___x_150_, lean_box(0));
v___x_152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_152_, 0, v___x_151_);
return v___x_152_;
}
}
v___jp_166_:
{
lean_object* v___x_171_; uint8_t v___x_172_; 
v___x_171_ = lean_array_get_size(v___y_169_);
v___x_172_ = lean_nat_dec_lt(v___y_167_, v___x_171_);
if (v___x_172_ == 0)
{
lean_dec_ref(v___y_169_);
lean_dec_ref(v___y_168_);
v_a_143_ = v_val_170_;
goto v___jp_142_;
}
else
{
lean_object* v___x_173_; size_t v___x_174_; size_t v___x_175_; lean_object* v___x_2659__overap_176_; lean_object* v___x_177_; 
v___x_173_ = lean_box(0);
v___x_174_ = ((size_t)0ULL);
v___x_175_ = lean_usize_of_nat(v___x_171_);
v___x_2659__overap_176_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___y_168_, v___f_165_, v___y_169_, v___x_174_, v___x_175_, v___x_173_);
lean_inc_ref(v_a_140_);
v___x_177_ = lean_apply_2(v___x_2659__overap_176_, v_a_140_, lean_box(0));
if (lean_obj_tag(v___x_177_) == 0)
{
lean_dec_ref_known(v___x_177_, 1);
v_a_143_ = v_val_170_;
goto v___jp_142_;
}
else
{
lean_dec_ref(v_repo_138_);
lean_dec_ref(v_name_137_);
return v___x_177_;
}
}
}
v___jp_178_:
{
uint8_t v___x_179_; 
lean_inc_ref(v_repo_138_);
v___x_179_ = l_Lake_GitRepo_hasNoDiff(v_repo_138_);
if (v___x_179_ == 0)
{
uint8_t v___x_180_; 
v___x_180_ = 1;
v___y_167_ = v___x_162_;
v___y_168_ = v___x_161_;
v___y_169_ = v___x_163_;
v_val_170_ = v___x_180_;
goto v___jp_166_;
}
else
{
uint8_t v___x_181_; 
v___x_181_ = 0;
v___y_167_ = v___x_162_;
v___y_168_ = v___x_161_;
v___y_169_ = v___x_163_;
v_val_170_ = v___x_181_;
goto v___jp_166_;
}
}
v___jp_182_:
{
if (lean_obj_tag(v___y_183_) == 0)
{
lean_dec_ref_known(v___y_183_, 1);
goto v___jp_178_;
}
else
{
lean_dec_ref(v_repo_138_);
lean_dec_ref(v_name_137_);
return v___y_183_;
}
}
v___jp_184_:
{
lean_object* v___x_185_; 
lean_inc_ref(v_repo_138_);
v___x_185_ = l_Lake_GitRepo_clean(v_repo_138_, v___x_163_);
if (lean_obj_tag(v___x_185_) == 0)
{
lean_object* v_a_186_; lean_object* v___x_187_; uint8_t v___x_188_; 
v_a_186_ = lean_ctor_get(v___x_185_, 1);
lean_inc(v_a_186_);
lean_dec_ref_known(v___x_185_, 2);
v___x_187_ = lean_array_get_size(v_a_186_);
v___x_188_ = lean_nat_dec_lt(v___x_162_, v___x_187_);
if (v___x_188_ == 0)
{
lean_dec(v_a_186_);
goto v___jp_178_;
}
else
{
lean_object* v___x_189_; size_t v___x_190_; size_t v___x_191_; lean_object* v___x_2692__overap_192_; lean_object* v___x_193_; 
v___x_189_ = lean_box(0);
v___x_190_ = ((size_t)0ULL);
v___x_191_ = lean_usize_of_nat(v___x_187_);
v___x_2692__overap_192_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_161_, v___f_165_, v_a_186_, v___x_190_, v___x_191_, v___x_189_);
lean_inc_ref(v_a_140_);
v___x_193_ = lean_apply_2(v___x_2692__overap_192_, v_a_140_, lean_box(0));
if (lean_obj_tag(v___x_193_) == 0)
{
lean_dec_ref_known(v___x_193_, 1);
goto v___jp_178_;
}
else
{
v___y_183_ = v___x_193_;
goto v___jp_182_;
}
}
}
else
{
lean_object* v_a_194_; lean_object* v___x_195_; uint8_t v___x_196_; 
v_a_194_ = lean_ctor_get(v___x_185_, 1);
lean_inc(v_a_194_);
lean_dec_ref_known(v___x_185_, 2);
v___x_195_ = lean_array_get_size(v_a_194_);
v___x_196_ = lean_nat_dec_lt(v___x_162_, v___x_195_);
if (v___x_196_ == 0)
{
lean_object* v___x_197_; lean_object* v___x_198_; 
lean_dec(v_a_194_);
lean_dec_ref(v_repo_138_);
lean_dec_ref(v_name_137_);
v___x_197_ = lean_box(0);
v___x_198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_198_, 0, v___x_197_);
return v___x_198_;
}
else
{
lean_object* v___x_199_; size_t v___x_200_; size_t v___x_201_; lean_object* v___x_2709__overap_202_; lean_object* v___x_203_; 
v___x_199_ = lean_box(0);
v___x_200_ = ((size_t)0ULL);
v___x_201_ = lean_usize_of_nat(v___x_195_);
v___x_2709__overap_202_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_161_, v___f_165_, v_a_194_, v___x_200_, v___x_201_, v___x_199_);
lean_inc_ref(v_a_140_);
v___x_203_ = lean_apply_2(v___x_2709__overap_202_, v_a_140_, lean_box(0));
if (lean_obj_tag(v___x_203_) == 0)
{
lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_210_; 
lean_dec_ref(v_repo_138_);
lean_dec_ref(v_name_137_);
v_isSharedCheck_210_ = !lean_is_exclusive(v___x_203_);
if (v_isSharedCheck_210_ == 0)
{
lean_object* v_unused_211_; 
v_unused_211_ = lean_ctor_get(v___x_203_, 0);
lean_dec(v_unused_211_);
v___x_205_ = v___x_203_;
v_isShared_206_ = v_isSharedCheck_210_;
goto v_resetjp_204_;
}
else
{
lean_dec(v___x_203_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_210_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_208_; 
if (v_isShared_206_ == 0)
{
lean_ctor_set_tag(v___x_205_, 1);
lean_ctor_set(v___x_205_, 0, v___x_199_);
v___x_208_ = v___x_205_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v___x_199_);
v___x_208_ = v_reuseFailAlloc_209_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
return v___x_208_;
}
}
}
else
{
v___y_183_ = v___x_203_;
goto v___jp_182_;
}
}
}
}
v___jp_212_:
{
if (lean_obj_tag(v___y_213_) == 0)
{
lean_dec_ref_known(v___y_213_, 1);
goto v___jp_184_;
}
else
{
lean_dec_ref(v_repo_138_);
lean_dec_ref(v_name_137_);
return v___y_213_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___boxed(lean_object* v_name_240_, lean_object* v_repo_241_, lean_object* v_rev_242_, lean_object* v_a_243_, lean_object* v_a_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout(v_name_240_, v_repo_241_, v_rev_242_, v_a_243_);
lean_dec_ref(v_a_243_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(lean_object* v_as_246_, size_t v_i_247_, size_t v_stop_248_, lean_object* v_b_249_, lean_object* v___y_250_){
_start:
{
uint8_t v___x_252_; 
v___x_252_ = lean_usize_dec_eq(v_i_247_, v_stop_248_);
if (v___x_252_ == 0)
{
lean_object* v___x_253_; lean_object* v___x_254_; size_t v___x_255_; size_t v___x_256_; 
v___x_253_ = lean_array_uget_borrowed(v_as_246_, v_i_247_);
lean_inc_ref(v___y_250_);
lean_inc(v___x_253_);
v___x_254_ = lean_apply_2(v___y_250_, v___x_253_, lean_box(0));
v___x_255_ = ((size_t)1ULL);
v___x_256_ = lean_usize_add(v_i_247_, v___x_255_);
v_i_247_ = v___x_256_;
v_b_249_ = v___x_254_;
goto _start;
}
else
{
lean_object* v___x_258_; 
v___x_258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_258_, 0, v_b_249_);
return v___x_258_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0___boxed(lean_object* v_as_259_, lean_object* v_i_260_, lean_object* v_stop_261_, lean_object* v_b_262_, lean_object* v___y_263_, lean_object* v___y_264_){
_start:
{
size_t v_i_boxed_265_; size_t v_stop_boxed_266_; lean_object* v_res_267_; 
v_i_boxed_265_ = lean_unbox_usize(v_i_260_);
lean_dec(v_i_260_);
v_stop_boxed_266_ = lean_unbox_usize(v_stop_261_);
lean_dec(v_stop_261_);
v_res_267_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_as_259_, v_i_boxed_265_, v_stop_boxed_266_, v_b_262_, v___y_263_);
lean_dec_ref(v___y_263_);
lean_dec_ref(v_as_259_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo(lean_object* v_name_277_, lean_object* v_repo_278_, lean_object* v_url_279_, lean_object* v_rev_x3f_280_, lean_object* v_a_281_){
_start:
{
lean_object* v___y_293_; lean_object* v___y_332_; lean_object* v___y_333_; lean_object* v___y_335_; lean_object* v___y_336_; lean_object* v___y_365_; lean_object* v___y_366_; uint8_t v_a_367_; lean_object* v___y_375_; uint8_t v_a_376_; lean_object* v___y_384_; lean_object* v___y_385_; lean_object* v___y_386_; lean_object* v___y_387_; uint8_t v_val_388_; lean_object* v___y_396_; lean_object* v___y_397_; uint8_t v___y_398_; lean_object* v___y_404_; lean_object* v___y_405_; uint8_t v___y_406_; lean_object* v___y_407_; lean_object* v___y_409_; lean_object* v___y_410_; uint8_t v___y_411_; lean_object* v___y_440_; lean_object* v___y_441_; uint8_t v___y_442_; lean_object* v___y_443_; lean_object* v___y_445_; lean_object* v___y_446_; lean_object* v___y_447_; uint8_t v_val_448_; lean_object* v___y_456_; lean_object* v___y_457_; lean_object* v___y_458_; lean_object* v___y_459_; lean_object* v_a_460_; lean_object* v___y_503_; lean_object* v___y_504_; lean_object* v___y_505_; lean_object* v___y_506_; lean_object* v_a_507_; lean_object* v___y_529_; lean_object* v___y_530_; lean_object* v___y_531_; lean_object* v___y_532_; lean_object* v___y_571_; lean_object* v___y_572_; lean_object* v___y_573_; lean_object* v___y_574_; lean_object* v___y_576_; lean_object* v___y_577_; lean_object* v___y_578_; lean_object* v___y_607_; lean_object* v___y_608_; lean_object* v___y_609_; lean_object* v___y_610_; lean_object* v___y_612_; uint8_t v_a_613_; lean_object* v___y_621_; uint8_t v_a_622_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___y_632_; uint8_t v_val_633_; uint8_t v___y_641_; lean_object* v___y_642_; uint8_t v___y_643_; uint8_t v___y_648_; lean_object* v___y_649_; uint8_t v___y_650_; lean_object* v___y_651_; uint8_t v___y_653_; lean_object* v___y_654_; uint8_t v___y_655_; uint8_t v___y_684_; lean_object* v___y_685_; uint8_t v___y_686_; lean_object* v___y_687_; uint8_t v___y_689_; lean_object* v___y_690_; lean_object* v___y_691_; lean_object* v___y_692_; uint8_t v___y_693_; lean_object* v___y_694_; lean_object* v_a_695_; lean_object* v___y_739_; lean_object* v___y_740_; lean_object* v___y_741_; uint8_t v_val_742_; lean_object* v___y_750_; lean_object* v___y_751_; lean_object* v___y_752_; lean_object* v___y_753_; lean_object* v_a_754_; lean_object* v___y_771_; lean_object* v___y_772_; lean_object* v___y_773_; lean_object* v___y_774_; lean_object* v___y_784_; lean_object* v___y_785_; lean_object* v___y_786_; lean_object* v___y_787_; lean_object* v___y_789_; lean_object* v___y_790_; lean_object* v___y_791_; lean_object* v___y_792_; lean_object* v___y_794_; lean_object* v___y_795_; lean_object* v___y_796_; lean_object* v_a_797_; lean_object* v___y_870_; lean_object* v___y_871_; lean_object* v___y_872_; uint8_t v_a_873_; lean_object* v___y_935_; lean_object* v___y_936_; lean_object* v_a_937_; lean_object* v___y_948_; lean_object* v___y_949_; lean_object* v_a_950_; lean_object* v___y_961_; lean_object* v___y_962_; lean_object* v___y_963_; lean_object* v___y_964_; lean_object* v_val_965_; lean_object* v___y_973_; lean_object* v___y_974_; uint8_t v_a_975_; lean_object* v___y_984_; 
if (lean_obj_tag(v_rev_x3f_280_) == 0)
{
lean_object* v___x_993_; 
v___x_993_ = l_Lake_Git_upstreamBranch;
v___y_984_ = v___x_993_;
goto v___jp_983_;
}
else
{
lean_object* v_val_994_; 
v_val_994_ = lean_ctor_get(v_rev_x3f_280_, 0);
lean_inc(v_val_994_);
lean_dec_ref_known(v_rev_x3f_280_, 1);
v___y_984_ = v_val_994_;
goto v___jp_983_;
}
v___jp_283_:
{
lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_284_ = lean_box(0);
v___x_285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
return v___x_285_;
}
v___jp_286_:
{
lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_287_ = lean_box(0);
v___x_288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_288_, 0, v___x_287_);
return v___x_288_;
}
v___jp_289_:
{
lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_290_ = lean_box(0);
v___x_291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_291_, 0, v___x_290_);
return v___x_291_;
}
v___jp_292_:
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_294_ = lean_unsigned_to_nat(0u);
v___x_295_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_296_ = l_Lake_GitRepo_gcAuto(v_repo_278_, v___x_295_);
if (lean_obj_tag(v___x_296_) == 0)
{
lean_object* v_a_297_; lean_object* v_a_298_; lean_object* v___x_299_; uint8_t v___x_300_; 
v_a_297_ = lean_ctor_get(v___x_296_, 0);
lean_inc(v_a_297_);
v_a_298_ = lean_ctor_get(v___x_296_, 1);
lean_inc(v_a_298_);
lean_dec_ref_known(v___x_296_, 2);
v___x_299_ = lean_array_get_size(v_a_298_);
v___x_300_ = lean_nat_dec_lt(v___x_294_, v___x_299_);
if (v___x_300_ == 0)
{
lean_object* v___x_301_; 
lean_dec(v_a_298_);
v___x_301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_301_, 0, v_a_297_);
return v___x_301_;
}
else
{
lean_object* v___x_302_; size_t v___x_303_; size_t v___x_304_; lean_object* v___x_305_; 
v___x_302_ = lean_box(0);
v___x_303_ = ((size_t)0ULL);
v___x_304_ = lean_usize_of_nat(v___x_299_);
v___x_305_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_298_, v___x_303_, v___x_304_, v___x_302_, v___y_293_);
lean_dec(v_a_298_);
if (lean_obj_tag(v___x_305_) == 0)
{
lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_312_; 
v_isSharedCheck_312_ = !lean_is_exclusive(v___x_305_);
if (v_isSharedCheck_312_ == 0)
{
lean_object* v_unused_313_; 
v_unused_313_ = lean_ctor_get(v___x_305_, 0);
lean_dec(v_unused_313_);
v___x_307_ = v___x_305_;
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
else
{
lean_dec(v___x_305_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_310_; 
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 0, v_a_297_);
v___x_310_ = v___x_307_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v_a_297_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
}
else
{
lean_dec(v_a_297_);
return v___x_305_;
}
}
}
else
{
lean_object* v_a_314_; lean_object* v___x_315_; uint8_t v___x_316_; 
v_a_314_ = lean_ctor_get(v___x_296_, 1);
lean_inc(v_a_314_);
lean_dec_ref_known(v___x_296_, 2);
v___x_315_ = lean_array_get_size(v_a_314_);
v___x_316_ = lean_nat_dec_lt(v___x_294_, v___x_315_);
if (v___x_316_ == 0)
{
lean_object* v___x_317_; lean_object* v___x_318_; 
lean_dec(v_a_314_);
v___x_317_ = lean_box(0);
v___x_318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
return v___x_318_;
}
else
{
lean_object* v___x_319_; size_t v___x_320_; size_t v___x_321_; lean_object* v___x_322_; 
v___x_319_ = lean_box(0);
v___x_320_ = ((size_t)0ULL);
v___x_321_ = lean_usize_of_nat(v___x_315_);
v___x_322_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_314_, v___x_320_, v___x_321_, v___x_319_, v___y_293_);
lean_dec(v_a_314_);
if (lean_obj_tag(v___x_322_) == 0)
{
lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_329_; 
v_isSharedCheck_329_ = !lean_is_exclusive(v___x_322_);
if (v_isSharedCheck_329_ == 0)
{
lean_object* v_unused_330_; 
v_unused_330_ = lean_ctor_get(v___x_322_, 0);
lean_dec(v_unused_330_);
v___x_324_ = v___x_322_;
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
else
{
lean_dec(v___x_322_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_327_; 
if (v_isShared_325_ == 0)
{
lean_ctor_set_tag(v___x_324_, 1);
lean_ctor_set(v___x_324_, 0, v___x_319_);
v___x_327_ = v___x_324_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v___x_319_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
}
else
{
return v___x_322_;
}
}
}
}
v___jp_331_:
{
if (lean_obj_tag(v___y_333_) == 0)
{
lean_dec_ref_known(v___y_333_, 1);
v___y_293_ = v___y_332_;
goto v___jp_292_;
}
else
{
lean_dec_ref(v_repo_278_);
return v___y_333_;
}
}
v___jp_334_:
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_337_ = lean_unsigned_to_nat(0u);
v___x_338_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_278_);
lean_inc_ref(v___y_336_);
v___x_339_ = l_Lake_GitRepo_pruneRemote(v___y_336_, v_repo_278_, v___x_338_);
if (lean_obj_tag(v___x_339_) == 0)
{
lean_object* v_a_340_; lean_object* v___x_341_; uint8_t v___x_342_; 
v_a_340_ = lean_ctor_get(v___x_339_, 1);
lean_inc(v_a_340_);
lean_dec_ref_known(v___x_339_, 2);
v___x_341_ = lean_array_get_size(v_a_340_);
v___x_342_ = lean_nat_dec_lt(v___x_337_, v___x_341_);
if (v___x_342_ == 0)
{
lean_dec(v_a_340_);
v___y_293_ = v___y_335_;
goto v___jp_292_;
}
else
{
lean_object* v___x_343_; size_t v___x_344_; size_t v___x_345_; lean_object* v___x_346_; 
v___x_343_ = lean_box(0);
v___x_344_ = ((size_t)0ULL);
v___x_345_ = lean_usize_of_nat(v___x_341_);
v___x_346_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_340_, v___x_344_, v___x_345_, v___x_343_, v___y_335_);
lean_dec(v_a_340_);
if (lean_obj_tag(v___x_346_) == 0)
{
lean_dec_ref_known(v___x_346_, 1);
v___y_293_ = v___y_335_;
goto v___jp_292_;
}
else
{
v___y_332_ = v___y_335_;
v___y_333_ = v___x_346_;
goto v___jp_331_;
}
}
}
else
{
lean_object* v_a_347_; lean_object* v___x_348_; uint8_t v___x_349_; 
v_a_347_ = lean_ctor_get(v___x_339_, 1);
lean_inc(v_a_347_);
lean_dec_ref_known(v___x_339_, 2);
v___x_348_ = lean_array_get_size(v_a_347_);
v___x_349_ = lean_nat_dec_lt(v___x_337_, v___x_348_);
if (v___x_349_ == 0)
{
lean_object* v___x_350_; lean_object* v___x_351_; 
lean_dec(v_a_347_);
lean_dec_ref(v_repo_278_);
v___x_350_ = lean_box(0);
v___x_351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_351_, 0, v___x_350_);
return v___x_351_;
}
else
{
lean_object* v___x_352_; size_t v___x_353_; size_t v___x_354_; lean_object* v___x_355_; 
v___x_352_ = lean_box(0);
v___x_353_ = ((size_t)0ULL);
v___x_354_ = lean_usize_of_nat(v___x_348_);
v___x_355_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_347_, v___x_353_, v___x_354_, v___x_352_, v___y_335_);
lean_dec(v_a_347_);
if (lean_obj_tag(v___x_355_) == 0)
{
lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_362_; 
lean_dec_ref(v_repo_278_);
v_isSharedCheck_362_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_362_ == 0)
{
lean_object* v_unused_363_; 
v_unused_363_ = lean_ctor_get(v___x_355_, 0);
lean_dec(v_unused_363_);
v___x_357_ = v___x_355_;
v_isShared_358_ = v_isSharedCheck_362_;
goto v_resetjp_356_;
}
else
{
lean_dec(v___x_355_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_362_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_360_; 
if (v_isShared_358_ == 0)
{
lean_ctor_set_tag(v___x_357_, 1);
lean_ctor_set(v___x_357_, 0, v___x_352_);
v___x_360_ = v___x_357_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v___x_352_);
v___x_360_ = v_reuseFailAlloc_361_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
return v___x_360_;
}
}
}
else
{
v___y_332_ = v___y_335_;
v___y_333_ = v___x_355_;
goto v___jp_331_;
}
}
}
}
v___jp_364_:
{
if (v_a_367_ == 0)
{
lean_dec_ref(v_name_277_);
v___y_335_ = v___y_365_;
v___y_336_ = v___y_366_;
goto v___jp_334_;
}
else
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; uint8_t v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_368_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff___closed__0));
v___x_369_ = lean_string_append(v_name_277_, v___x_368_);
v___x_370_ = lean_string_append(v___x_369_, v_repo_278_);
v___x_371_ = 2;
v___x_372_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_372_, 0, v___x_370_);
lean_ctor_set_uint8(v___x_372_, sizeof(void*)*1, v___x_371_);
lean_inc_ref(v___y_365_);
v___x_373_ = lean_apply_2(v___y_365_, v___x_372_, lean_box(0));
v___y_335_ = v___y_365_;
v___y_336_ = v___y_366_;
goto v___jp_334_;
}
}
v___jp_374_:
{
if (v_a_376_ == 0)
{
lean_dec_ref(v_repo_278_);
lean_dec_ref(v_name_277_);
goto v___jp_283_;
}
else
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; uint8_t v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_377_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff___closed__0));
v___x_378_ = lean_string_append(v_name_277_, v___x_377_);
v___x_379_ = lean_string_append(v___x_378_, v_repo_278_);
lean_dec_ref(v_repo_278_);
v___x_380_ = 2;
v___x_381_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_381_, 0, v___x_379_);
lean_ctor_set_uint8(v___x_381_, sizeof(void*)*1, v___x_380_);
lean_inc_ref(v___y_375_);
v___x_382_ = lean_apply_2(v___y_375_, v___x_381_, lean_box(0));
goto v___jp_283_;
}
}
v___jp_383_:
{
lean_object* v___x_389_; uint8_t v___x_390_; 
v___x_389_ = lean_array_get_size(v___y_387_);
v___x_390_ = lean_nat_dec_lt(v___y_386_, v___x_389_);
if (v___x_390_ == 0)
{
v___y_365_ = v___y_384_;
v___y_366_ = v___y_385_;
v_a_367_ = v_val_388_;
goto v___jp_364_;
}
else
{
lean_object* v___x_391_; size_t v___x_392_; size_t v___x_393_; lean_object* v___x_394_; 
v___x_391_ = lean_box(0);
v___x_392_ = ((size_t)0ULL);
v___x_393_ = lean_usize_of_nat(v___x_389_);
v___x_394_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_387_, v___x_392_, v___x_393_, v___x_391_, v___y_384_);
if (lean_obj_tag(v___x_394_) == 0)
{
lean_dec_ref_known(v___x_394_, 1);
v___y_365_ = v___y_384_;
v___y_366_ = v___y_385_;
v_a_367_ = v_val_388_;
goto v___jp_364_;
}
else
{
lean_dec_ref(v_name_277_);
if (lean_obj_tag(v___x_394_) == 0)
{
lean_dec_ref_known(v___x_394_, 1);
v___y_335_ = v___y_384_;
v___y_336_ = v___y_385_;
goto v___jp_334_;
}
else
{
lean_dec_ref(v_repo_278_);
return v___x_394_;
}
}
}
}
v___jp_395_:
{
uint8_t v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
lean_inc_ref(v_repo_278_);
v___x_399_ = l_Lake_GitRepo_hasNoDiff(v_repo_278_);
v___x_400_ = lean_unsigned_to_nat(0u);
v___x_401_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
if (v___x_399_ == 0)
{
uint8_t v___x_402_; 
v___x_402_ = 1;
v___y_384_ = v___y_396_;
v___y_385_ = v___y_397_;
v___y_386_ = v___x_400_;
v___y_387_ = v___x_401_;
v_val_388_ = v___x_402_;
goto v___jp_383_;
}
else
{
v___y_384_ = v___y_396_;
v___y_385_ = v___y_397_;
v___y_386_ = v___x_400_;
v___y_387_ = v___x_401_;
v_val_388_ = v___y_398_;
goto v___jp_383_;
}
}
v___jp_403_:
{
if (lean_obj_tag(v___y_407_) == 0)
{
lean_dec_ref_known(v___y_407_, 1);
v___y_396_ = v___y_404_;
v___y_397_ = v___y_405_;
v___y_398_ = v___y_406_;
goto v___jp_395_;
}
else
{
lean_dec_ref(v_repo_278_);
lean_dec_ref(v_name_277_);
return v___y_407_;
}
}
v___jp_408_:
{
lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_412_ = lean_unsigned_to_nat(0u);
v___x_413_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_278_);
v___x_414_ = l_Lake_GitRepo_clean(v_repo_278_, v___x_413_);
if (lean_obj_tag(v___x_414_) == 0)
{
lean_object* v_a_415_; lean_object* v___x_416_; uint8_t v___x_417_; 
v_a_415_ = lean_ctor_get(v___x_414_, 1);
lean_inc(v_a_415_);
lean_dec_ref_known(v___x_414_, 2);
v___x_416_ = lean_array_get_size(v_a_415_);
v___x_417_ = lean_nat_dec_lt(v___x_412_, v___x_416_);
if (v___x_417_ == 0)
{
lean_dec(v_a_415_);
v___y_396_ = v___y_409_;
v___y_397_ = v___y_410_;
v___y_398_ = v___y_411_;
goto v___jp_395_;
}
else
{
lean_object* v___x_418_; size_t v___x_419_; size_t v___x_420_; lean_object* v___x_421_; 
v___x_418_ = lean_box(0);
v___x_419_ = ((size_t)0ULL);
v___x_420_ = lean_usize_of_nat(v___x_416_);
v___x_421_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_415_, v___x_419_, v___x_420_, v___x_418_, v___y_409_);
lean_dec(v_a_415_);
if (lean_obj_tag(v___x_421_) == 0)
{
lean_dec_ref_known(v___x_421_, 1);
v___y_396_ = v___y_409_;
v___y_397_ = v___y_410_;
v___y_398_ = v___y_411_;
goto v___jp_395_;
}
else
{
v___y_404_ = v___y_409_;
v___y_405_ = v___y_410_;
v___y_406_ = v___y_411_;
v___y_407_ = v___x_421_;
goto v___jp_403_;
}
}
}
else
{
lean_object* v_a_422_; lean_object* v___x_423_; uint8_t v___x_424_; 
v_a_422_ = lean_ctor_get(v___x_414_, 1);
lean_inc(v_a_422_);
lean_dec_ref_known(v___x_414_, 2);
v___x_423_ = lean_array_get_size(v_a_422_);
v___x_424_ = lean_nat_dec_lt(v___x_412_, v___x_423_);
if (v___x_424_ == 0)
{
lean_object* v___x_425_; lean_object* v___x_426_; 
lean_dec(v_a_422_);
lean_dec_ref(v_repo_278_);
lean_dec_ref(v_name_277_);
v___x_425_ = lean_box(0);
v___x_426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_426_, 0, v___x_425_);
return v___x_426_;
}
else
{
lean_object* v___x_427_; size_t v___x_428_; size_t v___x_429_; lean_object* v___x_430_; 
v___x_427_ = lean_box(0);
v___x_428_ = ((size_t)0ULL);
v___x_429_ = lean_usize_of_nat(v___x_423_);
v___x_430_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_422_, v___x_428_, v___x_429_, v___x_427_, v___y_409_);
lean_dec(v_a_422_);
if (lean_obj_tag(v___x_430_) == 0)
{
lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_437_; 
lean_dec_ref(v_repo_278_);
lean_dec_ref(v_name_277_);
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_430_);
if (v_isSharedCheck_437_ == 0)
{
lean_object* v_unused_438_; 
v_unused_438_ = lean_ctor_get(v___x_430_, 0);
lean_dec(v_unused_438_);
v___x_432_ = v___x_430_;
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
else
{
lean_dec(v___x_430_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_435_; 
if (v_isShared_433_ == 0)
{
lean_ctor_set_tag(v___x_432_, 1);
lean_ctor_set(v___x_432_, 0, v___x_427_);
v___x_435_ = v___x_432_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v___x_427_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
else
{
v___y_404_ = v___y_409_;
v___y_405_ = v___y_410_;
v___y_406_ = v___y_411_;
v___y_407_ = v___x_430_;
goto v___jp_403_;
}
}
}
}
v___jp_439_:
{
if (lean_obj_tag(v___y_443_) == 0)
{
lean_dec_ref_known(v___y_443_, 1);
v___y_409_ = v___y_440_;
v___y_410_ = v___y_441_;
v___y_411_ = v___y_442_;
goto v___jp_408_;
}
else
{
lean_dec_ref(v_repo_278_);
lean_dec_ref(v_name_277_);
return v___y_443_;
}
}
v___jp_444_:
{
lean_object* v___x_449_; uint8_t v___x_450_; 
v___x_449_ = lean_array_get_size(v___y_447_);
v___x_450_ = lean_nat_dec_lt(v___y_445_, v___x_449_);
if (v___x_450_ == 0)
{
v___y_375_ = v___y_446_;
v_a_376_ = v_val_448_;
goto v___jp_374_;
}
else
{
lean_object* v___x_451_; size_t v___x_452_; size_t v___x_453_; lean_object* v___x_454_; 
v___x_451_ = lean_box(0);
v___x_452_ = ((size_t)0ULL);
v___x_453_ = lean_usize_of_nat(v___x_449_);
v___x_454_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_447_, v___x_452_, v___x_453_, v___x_451_, v___y_446_);
if (lean_obj_tag(v___x_454_) == 0)
{
lean_dec_ref_known(v___x_454_, 1);
v___y_375_ = v___y_446_;
v_a_376_ = v_val_448_;
goto v___jp_374_;
}
else
{
lean_dec_ref(v_repo_278_);
lean_dec_ref(v_name_277_);
if (lean_obj_tag(v___x_454_) == 0)
{
lean_dec_ref_known(v___x_454_, 1);
goto v___jp_283_;
}
else
{
return v___x_454_;
}
}
}
}
v___jp_455_:
{
lean_object* v___x_461_; uint8_t v___x_462_; 
v___x_461_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
v___x_462_ = l_Option_instDecidableEq___redArg(v___x_461_, v_a_460_, v___y_459_);
if (v___x_462_ == 0)
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; uint8_t v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_463_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__0));
lean_inc_ref(v_name_277_);
v___x_464_ = lean_string_append(v_name_277_, v___x_463_);
v___x_465_ = lean_string_append(v___x_464_, v___y_456_);
v___x_466_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__1));
v___x_467_ = lean_string_append(v___x_465_, v___x_466_);
v___x_468_ = 1;
v___x_469_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_469_, 0, v___x_467_);
lean_ctor_set_uint8(v___x_469_, sizeof(void*)*1, v___x_468_);
lean_inc_ref(v___y_457_);
v___x_470_ = lean_apply_2(v___y_457_, v___x_469_, lean_box(0));
v___x_471_ = lean_unsigned_to_nat(0u);
v___x_472_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_278_);
v___x_473_ = l_Lake_GitRepo_checkoutDetach(v___y_456_, v_repo_278_, v___x_472_);
if (lean_obj_tag(v___x_473_) == 0)
{
lean_object* v_a_474_; lean_object* v___x_475_; uint8_t v___x_476_; 
v_a_474_ = lean_ctor_get(v___x_473_, 1);
lean_inc(v_a_474_);
lean_dec_ref_known(v___x_473_, 2);
v___x_475_ = lean_array_get_size(v_a_474_);
v___x_476_ = lean_nat_dec_lt(v___x_471_, v___x_475_);
if (v___x_476_ == 0)
{
lean_dec(v_a_474_);
v___y_409_ = v___y_457_;
v___y_410_ = v___y_458_;
v___y_411_ = v___x_462_;
goto v___jp_408_;
}
else
{
lean_object* v___x_477_; size_t v___x_478_; size_t v___x_479_; lean_object* v___x_480_; 
v___x_477_ = lean_box(0);
v___x_478_ = ((size_t)0ULL);
v___x_479_ = lean_usize_of_nat(v___x_475_);
v___x_480_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_474_, v___x_478_, v___x_479_, v___x_477_, v___y_457_);
lean_dec(v_a_474_);
if (lean_obj_tag(v___x_480_) == 0)
{
lean_dec_ref_known(v___x_480_, 1);
v___y_409_ = v___y_457_;
v___y_410_ = v___y_458_;
v___y_411_ = v___x_462_;
goto v___jp_408_;
}
else
{
v___y_440_ = v___y_457_;
v___y_441_ = v___y_458_;
v___y_442_ = v___x_462_;
v___y_443_ = v___x_480_;
goto v___jp_439_;
}
}
}
else
{
lean_object* v_a_481_; lean_object* v___x_482_; uint8_t v___x_483_; 
v_a_481_ = lean_ctor_get(v___x_473_, 1);
lean_inc(v_a_481_);
lean_dec_ref_known(v___x_473_, 2);
v___x_482_ = lean_array_get_size(v_a_481_);
v___x_483_ = lean_nat_dec_lt(v___x_471_, v___x_482_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; lean_object* v___x_485_; 
lean_dec(v_a_481_);
lean_dec_ref(v_repo_278_);
lean_dec_ref(v_name_277_);
v___x_484_ = lean_box(0);
v___x_485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_485_, 0, v___x_484_);
return v___x_485_;
}
else
{
lean_object* v___x_486_; size_t v___x_487_; size_t v___x_488_; lean_object* v___x_489_; 
v___x_486_ = lean_box(0);
v___x_487_ = ((size_t)0ULL);
v___x_488_ = lean_usize_of_nat(v___x_482_);
v___x_489_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_481_, v___x_487_, v___x_488_, v___x_486_, v___y_457_);
lean_dec(v_a_481_);
if (lean_obj_tag(v___x_489_) == 0)
{
lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_496_; 
lean_dec_ref(v_repo_278_);
lean_dec_ref(v_name_277_);
v_isSharedCheck_496_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_496_ == 0)
{
lean_object* v_unused_497_; 
v_unused_497_ = lean_ctor_get(v___x_489_, 0);
lean_dec(v_unused_497_);
v___x_491_ = v___x_489_;
v_isShared_492_ = v_isSharedCheck_496_;
goto v_resetjp_490_;
}
else
{
lean_dec(v___x_489_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_496_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v___x_494_; 
if (v_isShared_492_ == 0)
{
lean_ctor_set_tag(v___x_491_, 1);
lean_ctor_set(v___x_491_, 0, v___x_486_);
v___x_494_ = v___x_491_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v___x_486_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
}
else
{
v___y_440_ = v___y_457_;
v___y_441_ = v___y_458_;
v___y_442_ = v___x_462_;
v___y_443_ = v___x_489_;
goto v___jp_439_;
}
}
}
}
else
{
uint8_t v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
lean_dec_ref(v___y_456_);
lean_inc_ref(v_repo_278_);
v___x_498_ = l_Lake_GitRepo_hasNoDiff(v_repo_278_);
v___x_499_ = lean_unsigned_to_nat(0u);
v___x_500_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
if (v___x_498_ == 0)
{
v___y_445_ = v___x_499_;
v___y_446_ = v___y_457_;
v___y_447_ = v___x_500_;
v_val_448_ = v___x_462_;
goto v___jp_444_;
}
else
{
uint8_t v___x_501_; 
v___x_501_ = 0;
v___y_445_ = v___x_499_;
v___y_446_ = v___y_457_;
v___y_447_ = v___x_500_;
v_val_448_ = v___x_501_;
goto v___jp_444_;
}
}
}
v___jp_502_:
{
if (lean_obj_tag(v_a_507_) == 1)
{
lean_object* v_val_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; uint8_t v___x_512_; 
lean_dec_ref(v___y_506_);
lean_dec_ref(v___y_505_);
v_val_508_ = lean_ctor_get(v_a_507_, 0);
lean_inc(v_val_508_);
v___x_509_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__0));
lean_inc_ref(v_repo_278_);
v___x_510_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_509_, v_repo_278_);
v___x_511_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_512_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_512_ == 0)
{
v___y_456_ = v_val_508_;
v___y_457_ = v___y_503_;
v___y_458_ = v___y_504_;
v___y_459_ = v_a_507_;
v_a_460_ = v___x_510_;
goto v___jp_455_;
}
else
{
lean_object* v___x_513_; size_t v___x_514_; size_t v___x_515_; lean_object* v___x_516_; 
v___x_513_ = lean_box(0);
v___x_514_ = ((size_t)0ULL);
v___x_515_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_516_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_511_, v___x_514_, v___x_515_, v___x_513_, v___y_503_);
if (lean_obj_tag(v___x_516_) == 0)
{
lean_dec_ref_known(v___x_516_, 1);
v___y_456_ = v_val_508_;
v___y_457_ = v___y_503_;
v___y_458_ = v___y_504_;
v___y_459_ = v_a_507_;
v_a_460_ = v___x_510_;
goto v___jp_455_;
}
else
{
lean_dec(v___x_510_);
lean_dec(v_val_508_);
lean_dec_ref_known(v_a_507_, 1);
lean_dec_ref(v_repo_278_);
lean_dec_ref(v_name_277_);
return v___x_516_;
}
}
}
else
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; uint8_t v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
lean_dec(v_a_507_);
lean_dec_ref(v_repo_278_);
v___x_517_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__1));
v___x_518_ = lean_string_append(v_name_277_, v___x_517_);
v___x_519_ = lean_string_append(v___x_518_, v___y_505_);
lean_dec_ref(v___y_505_);
v___x_520_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__2));
v___x_521_ = lean_string_append(v___x_519_, v___x_520_);
v___x_522_ = lean_string_append(v___x_521_, v___y_506_);
lean_dec_ref(v___y_506_);
v___x_523_ = 3;
v___x_524_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_524_, 0, v___x_522_);
lean_ctor_set_uint8(v___x_524_, sizeof(void*)*1, v___x_523_);
lean_inc_ref(v___y_503_);
v___x_525_ = lean_apply_2(v___y_503_, v___x_524_, lean_box(0));
v___x_526_ = lean_box(0);
v___x_527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_527_, 0, v___x_526_);
return v___x_527_;
}
}
v___jp_528_:
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; uint8_t v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_533_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__3));
lean_inc_ref(v_name_277_);
v___x_534_ = lean_string_append(v_name_277_, v___x_533_);
v___x_535_ = lean_string_append(v___x_534_, v___y_530_);
v___x_536_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__4));
v___x_537_ = lean_string_append(v___x_535_, v___x_536_);
v___x_538_ = lean_string_append(v___x_537_, v___y_531_);
v___x_539_ = 1;
v___x_540_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_540_, 0, v___x_538_);
lean_ctor_set_uint8(v___x_540_, sizeof(void*)*1, v___x_539_);
lean_inc_ref(v___y_532_);
v___x_541_ = lean_apply_2(v___y_532_, v___x_540_, lean_box(0));
v___x_542_ = lean_unsigned_to_nat(0u);
v___x_543_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v___y_530_);
lean_inc_ref(v___y_529_);
lean_inc_ref(v_repo_278_);
v___x_544_ = l_Lake_GitRepo_fetchRevision_x3f(v_repo_278_, v___y_529_, v___y_530_, v___x_543_);
if (lean_obj_tag(v___x_544_) == 0)
{
lean_object* v_a_545_; lean_object* v_a_546_; lean_object* v___x_547_; uint8_t v___x_548_; 
v_a_545_ = lean_ctor_get(v___x_544_, 0);
lean_inc(v_a_545_);
v_a_546_ = lean_ctor_get(v___x_544_, 1);
lean_inc(v_a_546_);
lean_dec_ref_known(v___x_544_, 2);
v___x_547_ = lean_array_get_size(v_a_546_);
v___x_548_ = lean_nat_dec_lt(v___x_542_, v___x_547_);
if (v___x_548_ == 0)
{
lean_dec(v_a_546_);
v___y_503_ = v___y_532_;
v___y_504_ = v___y_529_;
v___y_505_ = v___y_530_;
v___y_506_ = v___y_531_;
v_a_507_ = v_a_545_;
goto v___jp_502_;
}
else
{
lean_object* v___x_549_; size_t v___x_550_; size_t v___x_551_; lean_object* v___x_552_; 
v___x_549_ = lean_box(0);
v___x_550_ = ((size_t)0ULL);
v___x_551_ = lean_usize_of_nat(v___x_547_);
v___x_552_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_546_, v___x_550_, v___x_551_, v___x_549_, v___y_532_);
lean_dec(v_a_546_);
if (lean_obj_tag(v___x_552_) == 0)
{
lean_dec_ref_known(v___x_552_, 1);
v___y_503_ = v___y_532_;
v___y_504_ = v___y_529_;
v___y_505_ = v___y_530_;
v___y_506_ = v___y_531_;
v_a_507_ = v_a_545_;
goto v___jp_502_;
}
else
{
lean_dec(v_a_545_);
lean_dec_ref(v___y_531_);
lean_dec_ref(v___y_530_);
lean_dec_ref(v_repo_278_);
lean_dec_ref(v_name_277_);
return v___x_552_;
}
}
}
else
{
lean_object* v_a_553_; lean_object* v___x_554_; uint8_t v___x_555_; 
lean_dec_ref(v___y_531_);
lean_dec_ref(v___y_530_);
lean_dec_ref(v_repo_278_);
lean_dec_ref(v_name_277_);
v_a_553_ = lean_ctor_get(v___x_544_, 1);
lean_inc(v_a_553_);
lean_dec_ref_known(v___x_544_, 2);
v___x_554_ = lean_array_get_size(v_a_553_);
v___x_555_ = lean_nat_dec_lt(v___x_542_, v___x_554_);
if (v___x_555_ == 0)
{
lean_object* v___x_556_; lean_object* v___x_557_; 
lean_dec(v_a_553_);
v___x_556_ = lean_box(0);
v___x_557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_557_, 0, v___x_556_);
return v___x_557_;
}
else
{
lean_object* v___x_558_; size_t v___x_559_; size_t v___x_560_; lean_object* v___x_561_; 
v___x_558_ = lean_box(0);
v___x_559_ = ((size_t)0ULL);
v___x_560_ = lean_usize_of_nat(v___x_554_);
v___x_561_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_553_, v___x_559_, v___x_560_, v___x_558_, v___y_532_);
lean_dec(v_a_553_);
if (lean_obj_tag(v___x_561_) == 0)
{
lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_568_; 
v_isSharedCheck_568_ = !lean_is_exclusive(v___x_561_);
if (v_isSharedCheck_568_ == 0)
{
lean_object* v_unused_569_; 
v_unused_569_ = lean_ctor_get(v___x_561_, 0);
lean_dec(v_unused_569_);
v___x_563_ = v___x_561_;
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
else
{
lean_dec(v___x_561_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_566_; 
if (v_isShared_564_ == 0)
{
lean_ctor_set_tag(v___x_563_, 1);
lean_ctor_set(v___x_563_, 0, v___x_558_);
v___x_566_ = v___x_563_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v___x_558_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
return v___x_566_;
}
}
}
else
{
return v___x_561_;
}
}
}
}
v___jp_570_:
{
if (lean_obj_tag(v___y_574_) == 0)
{
lean_dec_ref_known(v___y_574_, 1);
v___y_529_ = v___y_571_;
v___y_530_ = v___y_572_;
v___y_531_ = v___y_573_;
v___y_532_ = v_a_281_;
goto v___jp_528_;
}
else
{
lean_dec_ref(v___y_573_);
lean_dec_ref(v___y_572_);
lean_dec_ref(v_repo_278_);
lean_dec_ref(v_name_277_);
return v___y_574_;
}
}
v___jp_575_:
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_579_ = lean_unsigned_to_nat(0u);
v___x_580_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_278_);
lean_inc_ref(v___y_578_);
lean_inc_ref(v___y_576_);
v___x_581_ = l_Lake_GitRepo_addRemote(v___y_576_, v___y_578_, v_repo_278_, v___x_580_);
if (lean_obj_tag(v___x_581_) == 0)
{
lean_object* v_a_582_; lean_object* v___x_583_; uint8_t v___x_584_; 
v_a_582_ = lean_ctor_get(v___x_581_, 1);
lean_inc(v_a_582_);
lean_dec_ref_known(v___x_581_, 2);
v___x_583_ = lean_array_get_size(v_a_582_);
v___x_584_ = lean_nat_dec_lt(v___x_579_, v___x_583_);
if (v___x_584_ == 0)
{
lean_dec(v_a_582_);
v___y_529_ = v___y_576_;
v___y_530_ = v___y_577_;
v___y_531_ = v___y_578_;
v___y_532_ = v_a_281_;
goto v___jp_528_;
}
else
{
lean_object* v___x_585_; size_t v___x_586_; size_t v___x_587_; lean_object* v___x_588_; 
v___x_585_ = lean_box(0);
v___x_586_ = ((size_t)0ULL);
v___x_587_ = lean_usize_of_nat(v___x_583_);
v___x_588_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_582_, v___x_586_, v___x_587_, v___x_585_, v_a_281_);
lean_dec(v_a_582_);
if (lean_obj_tag(v___x_588_) == 0)
{
lean_dec_ref_known(v___x_588_, 1);
v___y_529_ = v___y_576_;
v___y_530_ = v___y_577_;
v___y_531_ = v___y_578_;
v___y_532_ = v_a_281_;
goto v___jp_528_;
}
else
{
v___y_571_ = v___y_576_;
v___y_572_ = v___y_577_;
v___y_573_ = v___y_578_;
v___y_574_ = v___x_588_;
goto v___jp_570_;
}
}
}
else
{
lean_object* v_a_589_; lean_object* v___x_590_; uint8_t v___x_591_; 
v_a_589_ = lean_ctor_get(v___x_581_, 1);
lean_inc(v_a_589_);
lean_dec_ref_known(v___x_581_, 2);
v___x_590_ = lean_array_get_size(v_a_589_);
v___x_591_ = lean_nat_dec_lt(v___x_579_, v___x_590_);
if (v___x_591_ == 0)
{
lean_object* v___x_592_; lean_object* v___x_593_; 
lean_dec(v_a_589_);
lean_dec_ref(v___y_578_);
lean_dec_ref(v___y_577_);
lean_dec_ref(v_repo_278_);
lean_dec_ref(v_name_277_);
v___x_592_ = lean_box(0);
v___x_593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_593_, 0, v___x_592_);
return v___x_593_;
}
else
{
lean_object* v___x_594_; size_t v___x_595_; size_t v___x_596_; lean_object* v___x_597_; 
v___x_594_ = lean_box(0);
v___x_595_ = ((size_t)0ULL);
v___x_596_ = lean_usize_of_nat(v___x_590_);
v___x_597_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_589_, v___x_595_, v___x_596_, v___x_594_, v_a_281_);
lean_dec(v_a_589_);
if (lean_obj_tag(v___x_597_) == 0)
{
lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_604_; 
lean_dec_ref(v___y_578_);
lean_dec_ref(v___y_577_);
lean_dec_ref(v_repo_278_);
lean_dec_ref(v_name_277_);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_604_ == 0)
{
lean_object* v_unused_605_; 
v_unused_605_ = lean_ctor_get(v___x_597_, 0);
lean_dec(v_unused_605_);
v___x_599_ = v___x_597_;
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
else
{
lean_dec(v___x_597_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_602_; 
if (v_isShared_600_ == 0)
{
lean_ctor_set_tag(v___x_599_, 1);
lean_ctor_set(v___x_599_, 0, v___x_594_);
v___x_602_ = v___x_599_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v___x_594_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
else
{
v___y_571_ = v___y_576_;
v___y_572_ = v___y_577_;
v___y_573_ = v___y_578_;
v___y_574_ = v___x_597_;
goto v___jp_570_;
}
}
}
}
v___jp_606_:
{
if (lean_obj_tag(v___y_610_) == 0)
{
lean_dec_ref_known(v___y_610_, 1);
v___y_576_ = v___y_607_;
v___y_577_ = v___y_608_;
v___y_578_ = v___y_609_;
goto v___jp_575_;
}
else
{
lean_dec_ref(v___y_609_);
lean_dec_ref(v___y_608_);
lean_dec_ref(v_repo_278_);
lean_dec_ref(v_name_277_);
return v___y_610_;
}
}
v___jp_611_:
{
if (v_a_613_ == 0)
{
lean_dec_ref(v_repo_278_);
lean_dec_ref(v_name_277_);
goto v___jp_286_;
}
else
{
lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; uint8_t v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_614_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff___closed__0));
v___x_615_ = lean_string_append(v_name_277_, v___x_614_);
v___x_616_ = lean_string_append(v___x_615_, v_repo_278_);
lean_dec_ref(v_repo_278_);
v___x_617_ = 2;
v___x_618_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_618_, 0, v___x_616_);
lean_ctor_set_uint8(v___x_618_, sizeof(void*)*1, v___x_617_);
lean_inc_ref(v___y_612_);
v___x_619_ = lean_apply_2(v___y_612_, v___x_618_, lean_box(0));
goto v___jp_286_;
}
}
v___jp_620_:
{
if (v_a_622_ == 0)
{
lean_dec_ref(v_repo_278_);
lean_dec_ref(v_name_277_);
goto v___jp_289_;
}
else
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; uint8_t v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_623_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff___closed__0));
v___x_624_ = lean_string_append(v_name_277_, v___x_623_);
v___x_625_ = lean_string_append(v___x_624_, v_repo_278_);
lean_dec_ref(v_repo_278_);
v___x_626_ = 2;
v___x_627_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_627_, 0, v___x_625_);
lean_ctor_set_uint8(v___x_627_, sizeof(void*)*1, v___x_626_);
lean_inc_ref(v___y_621_);
v___x_628_ = lean_apply_2(v___y_621_, v___x_627_, lean_box(0));
goto v___jp_289_;
}
}
v___jp_629_:
{
lean_object* v___x_634_; uint8_t v___x_635_; 
v___x_634_ = lean_array_get_size(v___y_630_);
v___x_635_ = lean_nat_dec_lt(v___y_632_, v___x_634_);
if (v___x_635_ == 0)
{
v___y_612_ = v___y_631_;
v_a_613_ = v_val_633_;
goto v___jp_611_;
}
else
{
lean_object* v___x_636_; size_t v___x_637_; size_t v___x_638_; lean_object* v___x_639_; 
v___x_636_ = lean_box(0);
v___x_637_ = ((size_t)0ULL);
v___x_638_ = lean_usize_of_nat(v___x_634_);
v___x_639_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_630_, v___x_637_, v___x_638_, v___x_636_, v___y_631_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_dec_ref_known(v___x_639_, 1);
v___y_612_ = v___y_631_;
v_a_613_ = v_val_633_;
goto v___jp_611_;
}
else
{
lean_dec_ref(v_repo_278_);
lean_dec_ref(v_name_277_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_dec_ref_known(v___x_639_, 1);
goto v___jp_286_;
}
else
{
return v___x_639_;
}
}
}
}
v___jp_640_:
{
uint8_t v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
lean_inc_ref(v_repo_278_);
v___x_644_ = l_Lake_GitRepo_hasNoDiff(v_repo_278_);
v___x_645_ = lean_unsigned_to_nat(0u);
v___x_646_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
if (v___x_644_ == 0)
{
v___y_630_ = v___x_646_;
v___y_631_ = v___y_642_;
v___y_632_ = v___x_645_;
v_val_633_ = v___y_643_;
goto v___jp_629_;
}
else
{
v___y_630_ = v___x_646_;
v___y_631_ = v___y_642_;
v___y_632_ = v___x_645_;
v_val_633_ = v___y_641_;
goto v___jp_629_;
}
}
v___jp_647_:
{
if (lean_obj_tag(v___y_651_) == 0)
{
lean_dec_ref_known(v___y_651_, 1);
v___y_641_ = v___y_648_;
v___y_642_ = v___y_649_;
v___y_643_ = v___y_650_;
goto v___jp_640_;
}
else
{
lean_dec_ref(v_repo_278_);
lean_dec_ref(v_name_277_);
return v___y_651_;
}
}
v___jp_652_:
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_656_ = lean_unsigned_to_nat(0u);
v___x_657_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_278_);
v___x_658_ = l_Lake_GitRepo_clean(v_repo_278_, v___x_657_);
if (lean_obj_tag(v___x_658_) == 0)
{
lean_object* v_a_659_; lean_object* v___x_660_; uint8_t v___x_661_; 
v_a_659_ = lean_ctor_get(v___x_658_, 1);
lean_inc(v_a_659_);
lean_dec_ref_known(v___x_658_, 2);
v___x_660_ = lean_array_get_size(v_a_659_);
v___x_661_ = lean_nat_dec_lt(v___x_656_, v___x_660_);
if (v___x_661_ == 0)
{
lean_dec(v_a_659_);
v___y_641_ = v___y_653_;
v___y_642_ = v___y_654_;
v___y_643_ = v___y_655_;
goto v___jp_640_;
}
else
{
lean_object* v___x_662_; size_t v___x_663_; size_t v___x_664_; lean_object* v___x_665_; 
v___x_662_ = lean_box(0);
v___x_663_ = ((size_t)0ULL);
v___x_664_ = lean_usize_of_nat(v___x_660_);
v___x_665_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_659_, v___x_663_, v___x_664_, v___x_662_, v___y_654_);
lean_dec(v_a_659_);
if (lean_obj_tag(v___x_665_) == 0)
{
lean_dec_ref_known(v___x_665_, 1);
v___y_641_ = v___y_653_;
v___y_642_ = v___y_654_;
v___y_643_ = v___y_655_;
goto v___jp_640_;
}
else
{
v___y_648_ = v___y_653_;
v___y_649_ = v___y_654_;
v___y_650_ = v___y_655_;
v___y_651_ = v___x_665_;
goto v___jp_647_;
}
}
}
else
{
lean_object* v_a_666_; lean_object* v___x_667_; uint8_t v___x_668_; 
v_a_666_ = lean_ctor_get(v___x_658_, 1);
lean_inc(v_a_666_);
lean_dec_ref_known(v___x_658_, 2);
v___x_667_ = lean_array_get_size(v_a_666_);
v___x_668_ = lean_nat_dec_lt(v___x_656_, v___x_667_);
if (v___x_668_ == 0)
{
lean_object* v___x_669_; lean_object* v___x_670_; 
lean_dec(v_a_666_);
lean_dec_ref(v_repo_278_);
lean_dec_ref(v_name_277_);
v___x_669_ = lean_box(0);
v___x_670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_670_, 0, v___x_669_);
return v___x_670_;
}
else
{
lean_object* v___x_671_; size_t v___x_672_; size_t v___x_673_; lean_object* v___x_674_; 
v___x_671_ = lean_box(0);
v___x_672_ = ((size_t)0ULL);
v___x_673_ = lean_usize_of_nat(v___x_667_);
v___x_674_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_666_, v___x_672_, v___x_673_, v___x_671_, v___y_654_);
lean_dec(v_a_666_);
if (lean_obj_tag(v___x_674_) == 0)
{
lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_681_; 
lean_dec_ref(v_repo_278_);
lean_dec_ref(v_name_277_);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_681_ == 0)
{
lean_object* v_unused_682_; 
v_unused_682_ = lean_ctor_get(v___x_674_, 0);
lean_dec(v_unused_682_);
v___x_676_ = v___x_674_;
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
else
{
lean_dec(v___x_674_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_679_; 
if (v_isShared_677_ == 0)
{
lean_ctor_set_tag(v___x_676_, 1);
lean_ctor_set(v___x_676_, 0, v___x_671_);
v___x_679_ = v___x_676_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v___x_671_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
else
{
v___y_648_ = v___y_653_;
v___y_649_ = v___y_654_;
v___y_650_ = v___y_655_;
v___y_651_ = v___x_674_;
goto v___jp_647_;
}
}
}
}
v___jp_683_:
{
if (lean_obj_tag(v___y_687_) == 0)
{
lean_dec_ref_known(v___y_687_, 1);
v___y_653_ = v___y_684_;
v___y_654_ = v___y_685_;
v___y_655_ = v___y_686_;
goto v___jp_652_;
}
else
{
lean_dec_ref(v_repo_278_);
lean_dec_ref(v_name_277_);
return v___y_687_;
}
}
v___jp_688_:
{
if (lean_obj_tag(v_a_695_) == 0)
{
v___y_529_ = v___y_690_;
v___y_530_ = v___y_692_;
v___y_531_ = v___y_694_;
v___y_532_ = v___y_691_;
goto v___jp_528_;
}
else
{
lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_736_; 
v_isSharedCheck_736_ = !lean_is_exclusive(v_a_695_);
if (v_isSharedCheck_736_ == 0)
{
lean_object* v_unused_737_; 
v_unused_737_ = lean_ctor_get(v_a_695_, 0);
lean_dec(v_unused_737_);
v___x_697_ = v_a_695_;
v_isShared_698_ = v_isSharedCheck_736_;
goto v_resetjp_696_;
}
else
{
lean_dec(v_a_695_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_736_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
if (v___y_693_ == 0)
{
lean_del_object(v___x_697_);
v___y_529_ = v___y_690_;
v___y_530_ = v___y_692_;
v___y_531_ = v___y_694_;
v___y_532_ = v___y_691_;
goto v___jp_528_;
}
else
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; uint8_t v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
lean_dec_ref(v___y_694_);
v___x_699_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__0));
lean_inc_ref(v_name_277_);
v___x_700_ = lean_string_append(v_name_277_, v___x_699_);
v___x_701_ = lean_string_append(v___x_700_, v___y_692_);
v___x_702_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__1));
v___x_703_ = lean_string_append(v___x_701_, v___x_702_);
v___x_704_ = 1;
v___x_705_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_705_, 0, v___x_703_);
lean_ctor_set_uint8(v___x_705_, sizeof(void*)*1, v___x_704_);
lean_inc_ref(v___y_691_);
v___x_706_ = lean_apply_2(v___y_691_, v___x_705_, lean_box(0));
v___x_707_ = lean_unsigned_to_nat(0u);
v___x_708_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_278_);
v___x_709_ = l_Lake_GitRepo_checkoutDetach(v___y_692_, v_repo_278_, v___x_708_);
if (lean_obj_tag(v___x_709_) == 0)
{
lean_object* v_a_710_; lean_object* v___x_711_; uint8_t v___x_712_; 
lean_del_object(v___x_697_);
v_a_710_ = lean_ctor_get(v___x_709_, 1);
lean_inc(v_a_710_);
lean_dec_ref_known(v___x_709_, 2);
v___x_711_ = lean_array_get_size(v_a_710_);
v___x_712_ = lean_nat_dec_lt(v___x_707_, v___x_711_);
if (v___x_712_ == 0)
{
lean_dec(v_a_710_);
v___y_653_ = v___y_689_;
v___y_654_ = v___y_691_;
v___y_655_ = v___y_693_;
goto v___jp_652_;
}
else
{
lean_object* v___x_713_; size_t v___x_714_; size_t v___x_715_; lean_object* v___x_716_; 
v___x_713_ = lean_box(0);
v___x_714_ = ((size_t)0ULL);
v___x_715_ = lean_usize_of_nat(v___x_711_);
v___x_716_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_710_, v___x_714_, v___x_715_, v___x_713_, v___y_691_);
lean_dec(v_a_710_);
if (lean_obj_tag(v___x_716_) == 0)
{
lean_dec_ref_known(v___x_716_, 1);
v___y_653_ = v___y_689_;
v___y_654_ = v___y_691_;
v___y_655_ = v___y_693_;
goto v___jp_652_;
}
else
{
v___y_684_ = v___y_689_;
v___y_685_ = v___y_691_;
v___y_686_ = v___y_693_;
v___y_687_ = v___x_716_;
goto v___jp_683_;
}
}
}
else
{
lean_object* v_a_717_; lean_object* v___x_718_; uint8_t v___x_719_; 
v_a_717_ = lean_ctor_get(v___x_709_, 1);
lean_inc(v_a_717_);
lean_dec_ref_known(v___x_709_, 2);
v___x_718_ = lean_array_get_size(v_a_717_);
v___x_719_ = lean_nat_dec_lt(v___x_707_, v___x_718_);
if (v___x_719_ == 0)
{
lean_object* v___x_720_; lean_object* v___x_722_; 
lean_dec(v_a_717_);
lean_dec_ref(v_repo_278_);
lean_dec_ref(v_name_277_);
v___x_720_ = lean_box(0);
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 0, v___x_720_);
v___x_722_ = v___x_697_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v___x_720_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
else
{
lean_object* v___x_724_; size_t v___x_725_; size_t v___x_726_; lean_object* v___x_727_; 
lean_del_object(v___x_697_);
v___x_724_ = lean_box(0);
v___x_725_ = ((size_t)0ULL);
v___x_726_ = lean_usize_of_nat(v___x_718_);
v___x_727_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_717_, v___x_725_, v___x_726_, v___x_724_, v___y_691_);
lean_dec(v_a_717_);
if (lean_obj_tag(v___x_727_) == 0)
{
lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_734_; 
lean_dec_ref(v_repo_278_);
lean_dec_ref(v_name_277_);
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_734_ == 0)
{
lean_object* v_unused_735_; 
v_unused_735_ = lean_ctor_get(v___x_727_, 0);
lean_dec(v_unused_735_);
v___x_729_ = v___x_727_;
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
else
{
lean_dec(v___x_727_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_732_; 
if (v_isShared_730_ == 0)
{
lean_ctor_set_tag(v___x_729_, 1);
lean_ctor_set(v___x_729_, 0, v___x_724_);
v___x_732_ = v___x_729_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v___x_724_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
else
{
v___y_684_ = v___y_689_;
v___y_685_ = v___y_691_;
v___y_686_ = v___y_693_;
v___y_687_ = v___x_727_;
goto v___jp_683_;
}
}
}
}
}
}
}
v___jp_738_:
{
lean_object* v___x_743_; uint8_t v___x_744_; 
v___x_743_ = lean_array_get_size(v___y_739_);
v___x_744_ = lean_nat_dec_lt(v___y_740_, v___x_743_);
if (v___x_744_ == 0)
{
v___y_621_ = v___y_741_;
v_a_622_ = v_val_742_;
goto v___jp_620_;
}
else
{
lean_object* v___x_745_; size_t v___x_746_; size_t v___x_747_; lean_object* v___x_748_; 
v___x_745_ = lean_box(0);
v___x_746_ = ((size_t)0ULL);
v___x_747_ = lean_usize_of_nat(v___x_743_);
v___x_748_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_739_, v___x_746_, v___x_747_, v___x_745_, v___y_741_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_dec_ref_known(v___x_748_, 1);
v___y_621_ = v___y_741_;
v_a_622_ = v_val_742_;
goto v___jp_620_;
}
else
{
lean_dec_ref(v_repo_278_);
lean_dec_ref(v_name_277_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_dec_ref_known(v___x_748_, 1);
goto v___jp_289_;
}
else
{
return v___x_748_;
}
}
}
}
v___jp_749_:
{
lean_object* v___x_755_; lean_object* v___x_756_; uint8_t v___x_757_; 
v___x_755_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
lean_inc_ref(v___y_752_);
v___x_756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_756_, 0, v___y_752_);
v___x_757_ = l_Option_instDecidableEq___redArg(v___x_755_, v_a_754_, v___x_756_);
if (v___x_757_ == 0)
{
uint8_t v___x_758_; 
v___x_758_ = l_Lake_GitRev_isFullSha1(v___y_752_);
if (v___x_758_ == 0)
{
v___y_529_ = v___y_750_;
v___y_530_ = v___y_752_;
v___y_531_ = v___y_753_;
v___y_532_ = v___y_751_;
goto v___jp_528_;
}
else
{
lean_object* v___x_759_; lean_object* v___x_760_; uint8_t v___x_761_; 
lean_inc_ref(v_repo_278_);
lean_inc_ref(v___y_752_);
v___x_759_ = l_Lake_GitRepo_findCommit_x3f(v___y_752_, v_repo_278_);
v___x_760_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_761_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_761_ == 0)
{
v___y_689_ = v___x_757_;
v___y_690_ = v___y_750_;
v___y_691_ = v___y_751_;
v___y_692_ = v___y_752_;
v___y_693_ = v___x_758_;
v___y_694_ = v___y_753_;
v_a_695_ = v___x_759_;
goto v___jp_688_;
}
else
{
lean_object* v___x_762_; size_t v___x_763_; size_t v___x_764_; lean_object* v___x_765_; 
v___x_762_ = lean_box(0);
v___x_763_ = ((size_t)0ULL);
v___x_764_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_765_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_760_, v___x_763_, v___x_764_, v___x_762_, v___y_751_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_dec_ref_known(v___x_765_, 1);
v___y_689_ = v___x_757_;
v___y_690_ = v___y_750_;
v___y_691_ = v___y_751_;
v___y_692_ = v___y_752_;
v___y_693_ = v___x_758_;
v___y_694_ = v___y_753_;
v_a_695_ = v___x_759_;
goto v___jp_688_;
}
else
{
lean_dec(v___x_759_);
lean_dec_ref(v___y_753_);
lean_dec_ref(v___y_752_);
lean_dec_ref(v_repo_278_);
lean_dec_ref(v_name_277_);
return v___x_765_;
}
}
}
}
else
{
uint8_t v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
lean_dec_ref(v___y_753_);
lean_dec_ref(v___y_752_);
lean_inc_ref(v_repo_278_);
v___x_766_ = l_Lake_GitRepo_hasNoDiff(v_repo_278_);
v___x_767_ = lean_unsigned_to_nat(0u);
v___x_768_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
if (v___x_766_ == 0)
{
v___y_739_ = v___x_768_;
v___y_740_ = v___x_767_;
v___y_741_ = v___y_751_;
v_val_742_ = v___x_757_;
goto v___jp_738_;
}
else
{
uint8_t v___x_769_; 
v___x_769_ = 0;
v___y_739_ = v___x_768_;
v___y_740_ = v___x_767_;
v___y_741_ = v___y_751_;
v_val_742_ = v___x_769_;
goto v___jp_738_;
}
}
}
v___jp_770_:
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; uint8_t v___x_778_; 
v___x_775_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__0));
lean_inc_ref(v_repo_278_);
v___x_776_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_775_, v_repo_278_);
v___x_777_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_778_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_778_ == 0)
{
v___y_750_ = v___y_771_;
v___y_751_ = v___y_774_;
v___y_752_ = v___y_772_;
v___y_753_ = v___y_773_;
v_a_754_ = v___x_776_;
goto v___jp_749_;
}
else
{
lean_object* v___x_779_; size_t v___x_780_; size_t v___x_781_; lean_object* v___x_782_; 
v___x_779_ = lean_box(0);
v___x_780_ = ((size_t)0ULL);
v___x_781_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_782_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_777_, v___x_780_, v___x_781_, v___x_779_, v___y_774_);
if (lean_obj_tag(v___x_782_) == 0)
{
lean_dec_ref_known(v___x_782_, 1);
v___y_750_ = v___y_771_;
v___y_751_ = v___y_774_;
v___y_752_ = v___y_772_;
v___y_753_ = v___y_773_;
v_a_754_ = v___x_776_;
goto v___jp_749_;
}
else
{
lean_dec(v___x_776_);
lean_dec_ref(v___y_773_);
lean_dec_ref(v___y_772_);
lean_dec_ref(v_repo_278_);
lean_dec_ref(v_name_277_);
return v___x_782_;
}
}
}
v___jp_783_:
{
if (lean_obj_tag(v___y_787_) == 0)
{
lean_dec_ref_known(v___y_787_, 1);
v___y_771_ = v___y_784_;
v___y_772_ = v___y_785_;
v___y_773_ = v___y_786_;
v___y_774_ = v_a_281_;
goto v___jp_770_;
}
else
{
lean_dec_ref(v___y_786_);
lean_dec_ref(v___y_785_);
lean_dec_ref(v_repo_278_);
lean_dec_ref(v_name_277_);
return v___y_787_;
}
}
v___jp_788_:
{
if (lean_obj_tag(v___y_792_) == 0)
{
lean_dec_ref_known(v___y_792_, 1);
v___y_771_ = v___y_789_;
v___y_772_ = v___y_790_;
v___y_773_ = v___y_791_;
v___y_774_ = v_a_281_;
goto v___jp_770_;
}
else
{
lean_dec_ref(v___y_791_);
lean_dec_ref(v___y_790_);
lean_dec_ref(v_repo_278_);
lean_dec_ref(v_name_277_);
return v___y_792_;
}
}
v___jp_793_:
{
if (lean_obj_tag(v_a_797_) == 1)
{
lean_object* v_val_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_841_; 
v_val_798_ = lean_ctor_get(v_a_797_, 0);
v_isSharedCheck_841_ = !lean_is_exclusive(v_a_797_);
if (v_isSharedCheck_841_ == 0)
{
v___x_800_ = v_a_797_;
v_isShared_801_ = v_isSharedCheck_841_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_val_798_);
lean_dec(v_a_797_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_841_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
uint8_t v___x_802_; 
v___x_802_ = lean_string_dec_eq(v_val_798_, v___y_796_);
if (v___x_802_ == 0)
{
lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; uint8_t v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_803_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__5));
lean_inc_ref(v_name_277_);
v___x_804_ = lean_string_append(v_name_277_, v___x_803_);
v___x_805_ = lean_string_append(v___x_804_, v_val_798_);
lean_dec(v_val_798_);
v___x_806_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__6));
v___x_807_ = lean_string_append(v___x_805_, v___x_806_);
v___x_808_ = lean_string_append(v___x_807_, v___y_796_);
v___x_809_ = 1;
v___x_810_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_810_, 0, v___x_808_);
lean_ctor_set_uint8(v___x_810_, sizeof(void*)*1, v___x_809_);
lean_inc_ref(v_a_281_);
v___x_811_ = lean_apply_2(v_a_281_, v___x_810_, lean_box(0));
v___x_812_ = lean_unsigned_to_nat(0u);
v___x_813_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_278_);
lean_inc_ref(v___y_796_);
lean_inc_ref(v___y_794_);
v___x_814_ = l_Lake_GitRepo_setRemoteUrl(v___y_794_, v___y_796_, v_repo_278_, v___x_813_);
if (lean_obj_tag(v___x_814_) == 0)
{
lean_object* v_a_815_; lean_object* v___x_816_; uint8_t v___x_817_; 
lean_del_object(v___x_800_);
v_a_815_ = lean_ctor_get(v___x_814_, 1);
lean_inc(v_a_815_);
lean_dec_ref_known(v___x_814_, 2);
v___x_816_ = lean_array_get_size(v_a_815_);
v___x_817_ = lean_nat_dec_lt(v___x_812_, v___x_816_);
if (v___x_817_ == 0)
{
lean_dec(v_a_815_);
v___y_771_ = v___y_794_;
v___y_772_ = v___y_795_;
v___y_773_ = v___y_796_;
v___y_774_ = v_a_281_;
goto v___jp_770_;
}
else
{
lean_object* v___x_818_; size_t v___x_819_; size_t v___x_820_; lean_object* v___x_821_; 
v___x_818_ = lean_box(0);
v___x_819_ = ((size_t)0ULL);
v___x_820_ = lean_usize_of_nat(v___x_816_);
v___x_821_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_815_, v___x_819_, v___x_820_, v___x_818_, v_a_281_);
lean_dec(v_a_815_);
if (lean_obj_tag(v___x_821_) == 0)
{
lean_dec_ref_known(v___x_821_, 1);
v___y_771_ = v___y_794_;
v___y_772_ = v___y_795_;
v___y_773_ = v___y_796_;
v___y_774_ = v_a_281_;
goto v___jp_770_;
}
else
{
v___y_789_ = v___y_794_;
v___y_790_ = v___y_795_;
v___y_791_ = v___y_796_;
v___y_792_ = v___x_821_;
goto v___jp_788_;
}
}
}
else
{
lean_object* v_a_822_; lean_object* v___x_823_; uint8_t v___x_824_; 
v_a_822_ = lean_ctor_get(v___x_814_, 1);
lean_inc(v_a_822_);
lean_dec_ref_known(v___x_814_, 2);
v___x_823_ = lean_array_get_size(v_a_822_);
v___x_824_ = lean_nat_dec_lt(v___x_812_, v___x_823_);
if (v___x_824_ == 0)
{
lean_object* v___x_825_; lean_object* v___x_827_; 
lean_dec(v_a_822_);
lean_dec_ref(v___y_796_);
lean_dec_ref(v___y_795_);
lean_dec_ref(v_repo_278_);
lean_dec_ref(v_name_277_);
v___x_825_ = lean_box(0);
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 0, v___x_825_);
v___x_827_ = v___x_800_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v___x_825_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
else
{
lean_object* v___x_829_; size_t v___x_830_; size_t v___x_831_; lean_object* v___x_832_; 
lean_del_object(v___x_800_);
v___x_829_ = lean_box(0);
v___x_830_ = ((size_t)0ULL);
v___x_831_ = lean_usize_of_nat(v___x_823_);
v___x_832_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_822_, v___x_830_, v___x_831_, v___x_829_, v_a_281_);
lean_dec(v_a_822_);
if (lean_obj_tag(v___x_832_) == 0)
{
lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_839_; 
lean_dec_ref(v___y_796_);
lean_dec_ref(v___y_795_);
lean_dec_ref(v_repo_278_);
lean_dec_ref(v_name_277_);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_832_);
if (v_isSharedCheck_839_ == 0)
{
lean_object* v_unused_840_; 
v_unused_840_ = lean_ctor_get(v___x_832_, 0);
lean_dec(v_unused_840_);
v___x_834_ = v___x_832_;
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
else
{
lean_dec(v___x_832_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_837_; 
if (v_isShared_835_ == 0)
{
lean_ctor_set_tag(v___x_834_, 1);
lean_ctor_set(v___x_834_, 0, v___x_829_);
v___x_837_ = v___x_834_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v___x_829_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
else
{
v___y_789_ = v___y_794_;
v___y_790_ = v___y_795_;
v___y_791_ = v___y_796_;
v___y_792_ = v___x_832_;
goto v___jp_788_;
}
}
}
}
else
{
lean_del_object(v___x_800_);
lean_dec(v_val_798_);
v___y_771_ = v___y_794_;
v___y_772_ = v___y_795_;
v___y_773_ = v___y_796_;
v___y_774_ = v_a_281_;
goto v___jp_770_;
}
}
}
else
{
lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
lean_dec(v_a_797_);
v___x_842_ = lean_unsigned_to_nat(0u);
v___x_843_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_278_);
lean_inc_ref(v___y_796_);
lean_inc_ref(v___y_794_);
v___x_844_ = l_Lake_GitRepo_addRemote(v___y_794_, v___y_796_, v_repo_278_, v___x_843_);
if (lean_obj_tag(v___x_844_) == 0)
{
lean_object* v_a_845_; lean_object* v___x_846_; uint8_t v___x_847_; 
v_a_845_ = lean_ctor_get(v___x_844_, 1);
lean_inc(v_a_845_);
lean_dec_ref_known(v___x_844_, 2);
v___x_846_ = lean_array_get_size(v_a_845_);
v___x_847_ = lean_nat_dec_lt(v___x_842_, v___x_846_);
if (v___x_847_ == 0)
{
lean_dec(v_a_845_);
v___y_771_ = v___y_794_;
v___y_772_ = v___y_795_;
v___y_773_ = v___y_796_;
v___y_774_ = v_a_281_;
goto v___jp_770_;
}
else
{
lean_object* v___x_848_; size_t v___x_849_; size_t v___x_850_; lean_object* v___x_851_; 
v___x_848_ = lean_box(0);
v___x_849_ = ((size_t)0ULL);
v___x_850_ = lean_usize_of_nat(v___x_846_);
v___x_851_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_845_, v___x_849_, v___x_850_, v___x_848_, v_a_281_);
lean_dec(v_a_845_);
if (lean_obj_tag(v___x_851_) == 0)
{
lean_dec_ref_known(v___x_851_, 1);
v___y_771_ = v___y_794_;
v___y_772_ = v___y_795_;
v___y_773_ = v___y_796_;
v___y_774_ = v_a_281_;
goto v___jp_770_;
}
else
{
v___y_784_ = v___y_794_;
v___y_785_ = v___y_795_;
v___y_786_ = v___y_796_;
v___y_787_ = v___x_851_;
goto v___jp_783_;
}
}
}
else
{
lean_object* v_a_852_; lean_object* v___x_853_; uint8_t v___x_854_; 
v_a_852_ = lean_ctor_get(v___x_844_, 1);
lean_inc(v_a_852_);
lean_dec_ref_known(v___x_844_, 2);
v___x_853_ = lean_array_get_size(v_a_852_);
v___x_854_ = lean_nat_dec_lt(v___x_842_, v___x_853_);
if (v___x_854_ == 0)
{
lean_object* v___x_855_; lean_object* v___x_856_; 
lean_dec(v_a_852_);
lean_dec_ref(v___y_796_);
lean_dec_ref(v___y_795_);
lean_dec_ref(v_repo_278_);
lean_dec_ref(v_name_277_);
v___x_855_ = lean_box(0);
v___x_856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_856_, 0, v___x_855_);
return v___x_856_;
}
else
{
lean_object* v___x_857_; size_t v___x_858_; size_t v___x_859_; lean_object* v___x_860_; 
v___x_857_ = lean_box(0);
v___x_858_ = ((size_t)0ULL);
v___x_859_ = lean_usize_of_nat(v___x_853_);
v___x_860_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_852_, v___x_858_, v___x_859_, v___x_857_, v_a_281_);
lean_dec(v_a_852_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_867_; 
lean_dec_ref(v___y_796_);
lean_dec_ref(v___y_795_);
lean_dec_ref(v_repo_278_);
lean_dec_ref(v_name_277_);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_867_ == 0)
{
lean_object* v_unused_868_; 
v_unused_868_ = lean_ctor_get(v___x_860_, 0);
lean_dec(v_unused_868_);
v___x_862_ = v___x_860_;
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
else
{
lean_dec(v___x_860_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_865_; 
if (v_isShared_863_ == 0)
{
lean_ctor_set_tag(v___x_862_, 1);
lean_ctor_set(v___x_862_, 0, v___x_857_);
v___x_865_ = v___x_862_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v___x_857_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
else
{
v___y_784_ = v___y_794_;
v___y_785_ = v___y_795_;
v___y_786_ = v___y_796_;
v___y_787_ = v___x_860_;
goto v___jp_783_;
}
}
}
}
}
v___jp_869_:
{
if (v_a_873_ == 0)
{
lean_object* v___x_874_; lean_object* v___x_875_; uint8_t v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_874_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__7));
lean_inc_ref(v_name_277_);
v___x_875_ = lean_string_append(v_name_277_, v___x_874_);
v___x_876_ = 1;
v___x_877_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_877_, 0, v___x_875_);
lean_ctor_set_uint8(v___x_877_, sizeof(void*)*1, v___x_876_);
lean_inc_ref(v_a_281_);
v___x_878_ = lean_apply_2(v_a_281_, v___x_877_, lean_box(0));
lean_inc_ref(v_repo_278_);
v___x_879_ = l_IO_FS_createDirAll(v_repo_278_);
if (lean_obj_tag(v___x_879_) == 0)
{
lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_912_; 
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_879_);
if (v_isSharedCheck_912_ == 0)
{
lean_object* v_unused_913_; 
v_unused_913_ = lean_ctor_get(v___x_879_, 0);
lean_dec(v_unused_913_);
v___x_881_ = v___x_879_;
v_isShared_882_ = v_isSharedCheck_912_;
goto v_resetjp_880_;
}
else
{
lean_dec(v___x_879_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_912_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_883_ = lean_unsigned_to_nat(0u);
v___x_884_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_278_);
v___x_885_ = l_Lake_GitRepo_quietInit(v_repo_278_, v___x_884_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v_a_886_; lean_object* v___x_887_; uint8_t v___x_888_; 
lean_del_object(v___x_881_);
v_a_886_ = lean_ctor_get(v___x_885_, 1);
lean_inc(v_a_886_);
lean_dec_ref_known(v___x_885_, 2);
v___x_887_ = lean_array_get_size(v_a_886_);
v___x_888_ = lean_nat_dec_lt(v___x_883_, v___x_887_);
if (v___x_888_ == 0)
{
lean_dec(v_a_886_);
v___y_576_ = v___y_870_;
v___y_577_ = v___y_871_;
v___y_578_ = v___y_872_;
goto v___jp_575_;
}
else
{
lean_object* v___x_889_; size_t v___x_890_; size_t v___x_891_; lean_object* v___x_892_; 
v___x_889_ = lean_box(0);
v___x_890_ = ((size_t)0ULL);
v___x_891_ = lean_usize_of_nat(v___x_887_);
v___x_892_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_886_, v___x_890_, v___x_891_, v___x_889_, v_a_281_);
lean_dec(v_a_886_);
if (lean_obj_tag(v___x_892_) == 0)
{
lean_dec_ref_known(v___x_892_, 1);
v___y_576_ = v___y_870_;
v___y_577_ = v___y_871_;
v___y_578_ = v___y_872_;
goto v___jp_575_;
}
else
{
v___y_607_ = v___y_870_;
v___y_608_ = v___y_871_;
v___y_609_ = v___y_872_;
v___y_610_ = v___x_892_;
goto v___jp_606_;
}
}
}
else
{
lean_object* v_a_893_; lean_object* v___x_894_; uint8_t v___x_895_; 
v_a_893_ = lean_ctor_get(v___x_885_, 1);
lean_inc(v_a_893_);
lean_dec_ref_known(v___x_885_, 2);
v___x_894_ = lean_array_get_size(v_a_893_);
v___x_895_ = lean_nat_dec_lt(v___x_883_, v___x_894_);
if (v___x_895_ == 0)
{
lean_object* v___x_896_; lean_object* v___x_898_; 
lean_dec(v_a_893_);
lean_dec_ref(v___y_872_);
lean_dec_ref(v___y_871_);
lean_dec_ref(v_repo_278_);
lean_dec_ref(v_name_277_);
v___x_896_ = lean_box(0);
if (v_isShared_882_ == 0)
{
lean_ctor_set_tag(v___x_881_, 1);
lean_ctor_set(v___x_881_, 0, v___x_896_);
v___x_898_ = v___x_881_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v___x_896_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
else
{
lean_object* v___x_900_; size_t v___x_901_; size_t v___x_902_; lean_object* v___x_903_; 
lean_del_object(v___x_881_);
v___x_900_ = lean_box(0);
v___x_901_ = ((size_t)0ULL);
v___x_902_ = lean_usize_of_nat(v___x_894_);
v___x_903_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_893_, v___x_901_, v___x_902_, v___x_900_, v_a_281_);
lean_dec(v_a_893_);
if (lean_obj_tag(v___x_903_) == 0)
{
lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_910_; 
lean_dec_ref(v___y_872_);
lean_dec_ref(v___y_871_);
lean_dec_ref(v_repo_278_);
lean_dec_ref(v_name_277_);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_903_);
if (v_isSharedCheck_910_ == 0)
{
lean_object* v_unused_911_; 
v_unused_911_ = lean_ctor_get(v___x_903_, 0);
lean_dec(v_unused_911_);
v___x_905_ = v___x_903_;
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
else
{
lean_dec(v___x_903_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_908_; 
if (v_isShared_906_ == 0)
{
lean_ctor_set_tag(v___x_905_, 1);
lean_ctor_set(v___x_905_, 0, v___x_900_);
v___x_908_ = v___x_905_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v___x_900_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
}
else
{
v___y_607_ = v___y_870_;
v___y_608_ = v___y_871_;
v___y_609_ = v___y_872_;
v___y_610_ = v___x_903_;
goto v___jp_606_;
}
}
}
}
}
else
{
lean_object* v_a_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_926_; 
lean_dec_ref(v___y_872_);
lean_dec_ref(v___y_871_);
lean_dec_ref(v_repo_278_);
lean_dec_ref(v_name_277_);
v_a_914_ = lean_ctor_get(v___x_879_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_879_);
if (v_isSharedCheck_926_ == 0)
{
v___x_916_ = v___x_879_;
v_isShared_917_ = v_isSharedCheck_926_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_a_914_);
lean_dec(v___x_879_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_926_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_918_; uint8_t v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_924_; 
v___x_918_ = lean_io_error_to_string(v_a_914_);
v___x_919_ = 3;
v___x_920_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_920_, 0, v___x_918_);
lean_ctor_set_uint8(v___x_920_, sizeof(void*)*1, v___x_919_);
lean_inc_ref(v_a_281_);
v___x_921_ = lean_apply_2(v_a_281_, v___x_920_, lean_box(0));
v___x_922_ = lean_box(0);
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 0, v___x_922_);
v___x_924_ = v___x_916_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v___x_922_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
}
}
}
}
else
{
lean_object* v___x_927_; lean_object* v___x_928_; uint8_t v___x_929_; 
lean_inc_ref(v_repo_278_);
lean_inc_ref(v___y_870_);
v___x_927_ = l_Lake_GitRepo_getRemoteUrl_x3f(v___y_870_, v_repo_278_);
v___x_928_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_929_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_929_ == 0)
{
v___y_794_ = v___y_870_;
v___y_795_ = v___y_871_;
v___y_796_ = v___y_872_;
v_a_797_ = v___x_927_;
goto v___jp_793_;
}
else
{
lean_object* v___x_930_; size_t v___x_931_; size_t v___x_932_; lean_object* v___x_933_; 
v___x_930_ = lean_box(0);
v___x_931_ = ((size_t)0ULL);
v___x_932_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_933_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_928_, v___x_931_, v___x_932_, v___x_930_, v_a_281_);
if (lean_obj_tag(v___x_933_) == 0)
{
lean_dec_ref_known(v___x_933_, 1);
v___y_794_ = v___y_870_;
v___y_795_ = v___y_871_;
v___y_796_ = v___y_872_;
v_a_797_ = v___x_927_;
goto v___jp_793_;
}
else
{
lean_dec(v___x_927_);
lean_dec_ref(v___y_872_);
lean_dec_ref(v___y_871_);
lean_dec_ref(v_repo_278_);
lean_dec_ref(v_name_277_);
return v___x_933_;
}
}
}
}
v___jp_934_:
{
lean_object* v___x_938_; lean_object* v___x_939_; uint8_t v___x_940_; lean_object* v___x_941_; uint8_t v___x_942_; 
v___x_938_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__8));
lean_inc_ref(v_repo_278_);
v___x_939_ = l_System_FilePath_join(v_repo_278_, v___x_938_);
v___x_940_ = l_System_FilePath_pathExists(v___x_939_);
lean_dec_ref(v___x_939_);
v___x_941_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_942_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_942_ == 0)
{
v___y_870_ = v___y_935_;
v___y_871_ = v___y_936_;
v___y_872_ = v_a_937_;
v_a_873_ = v___x_940_;
goto v___jp_869_;
}
else
{
lean_object* v___x_943_; size_t v___x_944_; size_t v___x_945_; lean_object* v___x_946_; 
v___x_943_ = lean_box(0);
v___x_944_ = ((size_t)0ULL);
v___x_945_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_946_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_941_, v___x_944_, v___x_945_, v___x_943_, v_a_281_);
if (lean_obj_tag(v___x_946_) == 0)
{
lean_dec_ref_known(v___x_946_, 1);
v___y_870_ = v___y_935_;
v___y_871_ = v___y_936_;
v___y_872_ = v_a_937_;
v_a_873_ = v___x_940_;
goto v___jp_869_;
}
else
{
lean_dec_ref(v_a_937_);
lean_dec_ref(v___y_936_);
lean_dec_ref(v_repo_278_);
lean_dec_ref(v_name_277_);
return v___x_946_;
}
}
}
v___jp_947_:
{
if (lean_obj_tag(v_a_950_) == 1)
{
lean_object* v_val_951_; 
lean_dec_ref(v_url_279_);
v_val_951_ = lean_ctor_get(v_a_950_, 0);
lean_inc(v_val_951_);
lean_dec_ref_known(v_a_950_, 1);
v___y_935_ = v___y_948_;
v___y_936_ = v___y_949_;
v_a_937_ = v_val_951_;
goto v___jp_934_;
}
else
{
lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; uint8_t v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
lean_dec(v_a_950_);
lean_dec_ref(v___y_949_);
lean_dec_ref(v_repo_278_);
v___x_952_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__0));
v___x_953_ = lean_string_append(v_name_277_, v___x_952_);
v___x_954_ = lean_string_append(v___x_953_, v_url_279_);
lean_dec_ref(v_url_279_);
v___x_955_ = 3;
v___x_956_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_956_, 0, v___x_954_);
lean_ctor_set_uint8(v___x_956_, sizeof(void*)*1, v___x_955_);
lean_inc_ref(v_a_281_);
v___x_957_ = lean_apply_2(v_a_281_, v___x_956_, lean_box(0));
v___x_958_ = lean_box(0);
v___x_959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_959_, 0, v___x_958_);
return v___x_959_;
}
}
v___jp_960_:
{
lean_object* v___x_966_; uint8_t v___x_967_; 
v___x_966_ = lean_array_get_size(v___y_964_);
v___x_967_ = lean_nat_dec_lt(v___y_961_, v___x_966_);
if (v___x_967_ == 0)
{
v___y_948_ = v___y_962_;
v___y_949_ = v___y_963_;
v_a_950_ = v_val_965_;
goto v___jp_947_;
}
else
{
lean_object* v___x_968_; size_t v___x_969_; size_t v___x_970_; lean_object* v___x_971_; 
v___x_968_ = lean_box(0);
v___x_969_ = ((size_t)0ULL);
v___x_970_ = lean_usize_of_nat(v___x_966_);
v___x_971_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_964_, v___x_969_, v___x_970_, v___x_968_, v_a_281_);
if (lean_obj_tag(v___x_971_) == 0)
{
lean_dec_ref_known(v___x_971_, 1);
v___y_948_ = v___y_962_;
v___y_949_ = v___y_963_;
v_a_950_ = v_val_965_;
goto v___jp_947_;
}
else
{
lean_dec(v_val_965_);
lean_dec_ref(v___y_963_);
lean_dec_ref(v_url_279_);
lean_dec_ref(v_repo_278_);
lean_dec_ref(v_name_277_);
return v___x_971_;
}
}
}
v___jp_972_:
{
if (v_a_975_ == 0)
{
v___y_935_ = v___y_973_;
v___y_936_ = v___y_974_;
v_a_937_ = v_url_279_;
goto v___jp_934_;
}
else
{
lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; uint8_t v___x_980_; 
lean_inc_ref(v_url_279_);
v___x_976_ = l_Lake_resolvePath(v_url_279_);
v___x_977_ = lean_unsigned_to_nat(0u);
v___x_978_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_979_ = lean_string_utf8_byte_size(v___x_976_);
v___x_980_ = lean_nat_dec_eq(v___x_979_, v___x_977_);
if (v___x_980_ == 0)
{
lean_object* v___x_981_; 
v___x_981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_981_, 0, v___x_976_);
v___y_961_ = v___x_977_;
v___y_962_ = v___y_973_;
v___y_963_ = v___y_974_;
v___y_964_ = v___x_978_;
v_val_965_ = v___x_981_;
goto v___jp_960_;
}
else
{
lean_object* v___x_982_; 
lean_dec_ref(v___x_976_);
v___x_982_ = lean_box(0);
v___y_961_ = v___x_977_;
v___y_962_ = v___y_973_;
v___y_963_ = v___y_974_;
v___y_964_ = v___x_978_;
v_val_965_ = v___x_982_;
goto v___jp_960_;
}
}
}
v___jp_983_:
{
uint8_t v___x_985_; lean_object* v_remote_986_; lean_object* v___x_987_; uint8_t v___x_988_; 
v___x_985_ = l_System_FilePath_pathExists(v_url_279_);
v_remote_986_ = l_Lake_Git_defaultRemote;
v___x_987_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_988_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_988_ == 0)
{
v___y_973_ = v_remote_986_;
v___y_974_ = v___y_984_;
v_a_975_ = v___x_985_;
goto v___jp_972_;
}
else
{
lean_object* v___x_989_; size_t v___x_990_; size_t v___x_991_; lean_object* v___x_992_; 
v___x_989_ = lean_box(0);
v___x_990_ = ((size_t)0ULL);
v___x_991_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_992_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_987_, v___x_990_, v___x_991_, v___x_989_, v_a_281_);
if (lean_obj_tag(v___x_992_) == 0)
{
lean_dec_ref_known(v___x_992_, 1);
v___y_973_ = v_remote_986_;
v___y_974_ = v___y_984_;
v_a_975_ = v___x_985_;
goto v___jp_972_;
}
else
{
lean_dec_ref(v___y_984_);
lean_dec_ref(v_url_279_);
lean_dec_ref(v_repo_278_);
lean_dec_ref(v_name_277_);
return v___x_992_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___boxed(lean_object* v_name_995_, lean_object* v_repo_996_, lean_object* v_url_997_, lean_object* v_rev_x3f_998_, lean_object* v_a_999_, lean_object* v_a_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo(v_name_995_, v_repo_996_, v_url_997_, v_rev_x3f_998_, v_a_999_);
lean_dec_ref(v_a_999_);
return v_res_1001_;
}
}
static lean_object* _init_l_Lake_instInhabitedMaterializedDep_default___closed__4(void){
_start:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1008_ = l_Lake_instInhabitedPackageEntry_default;
v___x_1009_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__3));
v___x_1010_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___x_1011_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1010_);
lean_ctor_set(v___x_1011_, 1, v___x_1010_);
lean_ctor_set(v___x_1011_, 2, v___x_1010_);
lean_ctor_set(v___x_1011_, 3, v___x_1009_);
lean_ctor_set(v___x_1011_, 4, v___x_1008_);
return v___x_1011_;
}
}
static lean_object* _init_l_Lake_instInhabitedMaterializedDep_default(void){
_start:
{
lean_object* v___x_1012_; 
v___x_1012_ = lean_obj_once(&l_Lake_instInhabitedMaterializedDep_default___closed__4, &l_Lake_instInhabitedMaterializedDep_default___closed__4_once, _init_l_Lake_instInhabitedMaterializedDep_default___closed__4);
return v___x_1012_;
}
}
static lean_object* _init_l_Lake_instInhabitedMaterializedDep(void){
_start:
{
lean_object* v___x_1013_; 
v___x_1013_ = l_Lake_instInhabitedMaterializedDep_default;
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_name(lean_object* v_self_1014_){
_start:
{
lean_object* v_manifestEntry_1015_; lean_object* v_name_1016_; 
v_manifestEntry_1015_ = lean_ctor_get(v_self_1014_, 4);
v_name_1016_ = lean_ctor_get(v_manifestEntry_1015_, 0);
lean_inc(v_name_1016_);
return v_name_1016_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_name___boxed(lean_object* v_self_1017_){
_start:
{
lean_object* v_res_1018_; 
v_res_1018_ = l_Lake_MaterializedDep_name(v_self_1017_);
lean_dec_ref(v_self_1017_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_prettyName(lean_object* v_self_1019_){
_start:
{
lean_object* v_manifestEntry_1020_; lean_object* v_name_1021_; uint8_t v___x_1022_; lean_object* v___x_1023_; 
v_manifestEntry_1020_ = lean_ctor_get(v_self_1019_, 4);
lean_inc_ref(v_manifestEntry_1020_);
lean_dec_ref(v_self_1019_);
v_name_1021_ = lean_ctor_get(v_manifestEntry_1020_, 0);
lean_inc(v_name_1021_);
lean_dec_ref(v_manifestEntry_1020_);
v___x_1022_ = 0;
v___x_1023_ = l_Lean_Name_toString(v_name_1021_, v___x_1022_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_scope(lean_object* v_self_1024_){
_start:
{
lean_object* v_manifestEntry_1025_; lean_object* v_scope_1026_; 
v_manifestEntry_1025_ = lean_ctor_get(v_self_1024_, 4);
v_scope_1026_ = lean_ctor_get(v_manifestEntry_1025_, 1);
lean_inc_ref(v_scope_1026_);
return v_scope_1026_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_scope___boxed(lean_object* v_self_1027_){
_start:
{
lean_object* v_res_1028_; 
v_res_1028_ = l_Lake_MaterializedDep_scope(v_self_1027_);
lean_dec_ref(v_self_1027_);
return v_res_1028_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relManifestFile_x3f(lean_object* v_self_1029_){
_start:
{
lean_object* v_manifestEntry_1030_; lean_object* v_manifestFile_x3f_1031_; 
v_manifestEntry_1030_ = lean_ctor_get(v_self_1029_, 4);
v_manifestFile_x3f_1031_ = lean_ctor_get(v_manifestEntry_1030_, 3);
lean_inc(v_manifestFile_x3f_1031_);
return v_manifestFile_x3f_1031_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relManifestFile_x3f___boxed(lean_object* v_self_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l_Lake_MaterializedDep_relManifestFile_x3f(v_self_1032_);
lean_dec_ref(v_self_1032_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relManifestFile(lean_object* v_self_1034_){
_start:
{
lean_object* v_manifestEntry_1035_; lean_object* v_manifestFile_x3f_1036_; 
v_manifestEntry_1035_ = lean_ctor_get(v_self_1034_, 4);
v_manifestFile_x3f_1036_ = lean_ctor_get(v_manifestEntry_1035_, 3);
if (lean_obj_tag(v_manifestFile_x3f_1036_) == 0)
{
lean_object* v___x_1037_; 
v___x_1037_ = l_Lake_defaultManifestFile;
return v___x_1037_;
}
else
{
lean_object* v_val_1038_; 
v_val_1038_ = lean_ctor_get(v_manifestFile_x3f_1036_, 0);
lean_inc(v_val_1038_);
return v_val_1038_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relManifestFile___boxed(lean_object* v_self_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l_Lake_MaterializedDep_relManifestFile(v_self_1039_);
lean_dec_ref(v_self_1039_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_manifestFile(lean_object* v_self_1041_){
_start:
{
lean_object* v_manifestEntry_1042_; lean_object* v_manifestFile_x3f_1043_; 
v_manifestEntry_1042_ = lean_ctor_get(v_self_1041_, 4);
v_manifestFile_x3f_1043_ = lean_ctor_get(v_manifestEntry_1042_, 3);
if (lean_obj_tag(v_manifestFile_x3f_1043_) == 0)
{
lean_object* v_pkgDir_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; 
v_pkgDir_1044_ = lean_ctor_get(v_self_1041_, 0);
lean_inc_ref(v_pkgDir_1044_);
lean_dec_ref(v_self_1041_);
v___x_1045_ = l_Lake_defaultManifestFile;
v___x_1046_ = l_Lake_joinRelative(v_pkgDir_1044_, v___x_1045_);
return v___x_1046_;
}
else
{
lean_object* v_pkgDir_1047_; lean_object* v_val_1048_; lean_object* v___x_1049_; 
lean_inc_ref(v_manifestFile_x3f_1043_);
v_pkgDir_1047_ = lean_ctor_get(v_self_1041_, 0);
lean_inc_ref(v_pkgDir_1047_);
lean_dec_ref(v_self_1041_);
v_val_1048_ = lean_ctor_get(v_manifestFile_x3f_1043_, 0);
lean_inc(v_val_1048_);
lean_dec_ref_known(v_manifestFile_x3f_1043_, 1);
v___x_1049_ = l_Lake_joinRelative(v_pkgDir_1047_, v_val_1048_);
return v___x_1049_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relConfigFile(lean_object* v_self_1050_){
_start:
{
lean_object* v_manifestEntry_1051_; lean_object* v_configFile_1052_; 
v_manifestEntry_1051_ = lean_ctor_get(v_self_1050_, 4);
v_configFile_1052_ = lean_ctor_get(v_manifestEntry_1051_, 2);
lean_inc_ref(v_configFile_1052_);
return v_configFile_1052_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relConfigFile___boxed(lean_object* v_self_1053_){
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l_Lake_MaterializedDep_relConfigFile(v_self_1053_);
lean_dec_ref(v_self_1053_);
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_configFile(lean_object* v_self_1055_){
_start:
{
lean_object* v_manifestEntry_1056_; lean_object* v_pkgDir_1057_; lean_object* v_configFile_1058_; lean_object* v___x_1059_; 
v_manifestEntry_1056_ = lean_ctor_get(v_self_1055_, 4);
lean_inc_ref(v_manifestEntry_1056_);
v_pkgDir_1057_ = lean_ctor_get(v_self_1055_, 0);
lean_inc_ref(v_pkgDir_1057_);
lean_dec_ref(v_self_1055_);
v_configFile_1058_ = lean_ctor_get(v_manifestEntry_1056_, 2);
lean_inc_ref(v_configFile_1058_);
lean_dec_ref(v_manifestEntry_1056_);
v___x_1059_ = l_Lake_joinRelative(v_pkgDir_1057_, v_configFile_1058_);
return v___x_1059_;
}
}
LEAN_EXPORT uint8_t l_Lake_MaterializedDep_fixedToolchain(lean_object* v_self_1060_){
_start:
{
lean_object* v_manifest_x3f_1061_; 
v_manifest_x3f_1061_ = lean_ctor_get(v_self_1060_, 3);
if (lean_obj_tag(v_manifest_x3f_1061_) == 1)
{
lean_object* v_a_1062_; uint8_t v_fixedToolchain_1063_; 
v_a_1062_ = lean_ctor_get(v_manifest_x3f_1061_, 0);
v_fixedToolchain_1063_ = lean_ctor_get_uint8(v_a_1062_, sizeof(void*)*4);
return v_fixedToolchain_1063_;
}
else
{
uint8_t v___x_1064_; 
v___x_1064_ = 0;
return v___x_1064_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_fixedToolchain___boxed(lean_object* v_self_1065_){
_start:
{
uint8_t v_res_1066_; lean_object* v_r_1067_; 
v_res_1066_ = l_Lake_MaterializedDep_fixedToolchain(v_self_1065_);
lean_dec_ref(v_self_1065_);
v_r_1067_ = lean_box(v_res_1066_);
return v_r_1067_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed(lean_object* v_dep_1076_){
_start:
{
lean_object* v_name_1077_; lean_object* v_scope_1078_; lean_object* v_version_1079_; lean_object* v_fst_1081_; lean_object* v_snd_1082_; 
v_name_1077_ = lean_ctor_get(v_dep_1076_, 0);
lean_inc(v_name_1077_);
v_scope_1078_ = lean_ctor_get(v_dep_1076_, 1);
lean_inc_ref(v_scope_1078_);
v_version_1079_ = lean_ctor_get(v_dep_1076_, 2);
lean_inc(v_version_1079_);
lean_dec_ref(v_dep_1076_);
switch(lean_obj_tag(v_version_1079_))
{
case 0:
{
lean_object* v___x_1105_; 
v___x_1105_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v_fst_1081_ = v___x_1105_;
v_snd_1082_ = v___x_1105_;
goto v___jp_1080_;
}
case 1:
{
lean_object* v_rev_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1121_; 
v_rev_1106_ = lean_ctor_get(v_version_1079_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v_version_1079_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1108_ = v_version_1079_;
v_isShared_1109_ = v_isSharedCheck_1121_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_rev_1106_);
lean_dec(v_version_1079_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1121_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1113_; 
v___x_1110_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__5));
v___x_1111_ = l_String_quote(v_rev_1106_);
if (v_isShared_1109_ == 0)
{
lean_ctor_set_tag(v___x_1108_, 3);
lean_ctor_set(v___x_1108_, 0, v___x_1111_);
v___x_1113_ = v___x_1108_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v___x_1111_);
v___x_1113_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1114_ = l_Std_Format_defWidth;
v___x_1115_ = lean_unsigned_to_nat(0u);
v___x_1116_ = l_Std_Format_pretty(v___x_1113_, v___x_1114_, v___x_1115_, v___x_1115_);
v___x_1117_ = lean_string_append(v___x_1110_, v___x_1116_);
v___x_1118_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__6));
v___x_1119_ = lean_string_append(v___x_1118_, v___x_1116_);
lean_dec_ref(v___x_1116_);
v_fst_1081_ = v___x_1117_;
v_snd_1082_ = v___x_1119_;
goto v___jp_1080_;
}
}
}
default: 
{
lean_object* v_ver_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1138_; 
v_ver_1122_ = lean_ctor_get(v_version_1079_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v_version_1079_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1124_ = v_version_1079_;
v_isShared_1125_ = v_isSharedCheck_1138_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_ver_1122_);
lean_dec(v_version_1079_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1138_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v_toString_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1130_; 
v_toString_1126_ = lean_ctor_get(v_ver_1122_, 0);
lean_inc_ref(v_toString_1126_);
lean_dec_ref(v_ver_1122_);
v___x_1127_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__5));
v___x_1128_ = l_String_quote(v_toString_1126_);
if (v_isShared_1125_ == 0)
{
lean_ctor_set_tag(v___x_1124_, 3);
lean_ctor_set(v___x_1124_, 0, v___x_1128_);
v___x_1130_ = v___x_1124_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v___x_1128_);
v___x_1130_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1131_ = l_Std_Format_defWidth;
v___x_1132_ = lean_unsigned_to_nat(0u);
v___x_1133_ = l_Std_Format_pretty(v___x_1130_, v___x_1131_, v___x_1132_, v___x_1132_);
v___x_1134_ = lean_string_append(v___x_1127_, v___x_1133_);
v___x_1135_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__7));
v___x_1136_ = lean_string_append(v___x_1135_, v___x_1133_);
lean_dec_ref(v___x_1133_);
v_fst_1081_ = v___x_1134_;
v_snd_1082_ = v___x_1136_;
goto v___jp_1080_;
}
}
}
}
v___jp_1080_:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; uint8_t v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1083_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
lean_inc_ref(v_scope_1078_);
v___x_1084_ = lean_string_append(v_scope_1078_, v___x_1083_);
v___x_1085_ = 0;
v___x_1086_ = l_Lean_Name_toString(v_name_1077_, v___x_1085_);
v___x_1087_ = lean_string_append(v___x_1084_, v___x_1086_);
v___x_1088_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__1));
v___x_1089_ = lean_string_append(v___x_1087_, v___x_1088_);
v___x_1090_ = lean_string_append(v___x_1089_, v_scope_1078_);
v___x_1091_ = lean_string_append(v___x_1090_, v___x_1083_);
v___x_1092_ = lean_string_append(v___x_1091_, v___x_1086_);
v___x_1093_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__2));
v___x_1094_ = lean_string_append(v___x_1092_, v___x_1093_);
v___x_1095_ = lean_string_append(v___x_1094_, v_fst_1081_);
lean_dec_ref(v_fst_1081_);
v___x_1096_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__3));
v___x_1097_ = lean_string_append(v___x_1095_, v___x_1096_);
v___x_1098_ = lean_string_append(v___x_1097_, v_scope_1078_);
lean_dec_ref(v_scope_1078_);
v___x_1099_ = lean_string_append(v___x_1098_, v___x_1083_);
v___x_1100_ = lean_string_append(v___x_1099_, v___x_1086_);
lean_dec_ref(v___x_1086_);
v___x_1101_ = lean_string_append(v___x_1100_, v___x_1093_);
v___x_1102_ = lean_string_append(v___x_1101_, v_snd_1082_);
lean_dec_ref(v_snd_1082_);
v___x_1103_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__4));
v___x_1104_ = lean_string_append(v___x_1102_, v___x_1103_);
return v___x_1104_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep(lean_object* v_dep_1140_, uint8_t v_inherited_1141_, lean_object* v_wsDir_1142_, lean_object* v_name_1143_, lean_object* v_relPkgDir_1144_, lean_object* v_remoteUrl_1145_, lean_object* v_src_1146_, lean_object* v_a_1147_){
_start:
{
lean_object* v___y_1150_; lean_object* v_a_1151_; lean_object* v_pkgDir_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___f_1171_; lean_object* v___y_1173_; lean_object* v___y_1174_; lean_object* v___y_1175_; lean_object* v___y_1176_; lean_object* v_val_1177_; lean_object* v_a_1194_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v_val_1228_; lean_object* v___x_1243_; uint8_t v___x_1244_; 
lean_inc_ref(v_relPkgDir_1144_);
v_pkgDir_1168_ = l_Lake_joinRelative(v_wsDir_1142_, v_relPkgDir_1144_);
v___x_1169_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__2, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__2_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__2);
lean_inc_ref(v_pkgDir_1168_);
v___x_1170_ = l_Lake_resolvePath(v_pkgDir_1168_);
v___f_1171_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3));
v___x_1225_ = lean_unsigned_to_nat(0u);
v___x_1226_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_1243_ = lean_string_utf8_byte_size(v___x_1170_);
v___x_1244_ = lean_nat_dec_eq(v___x_1243_, v___x_1225_);
if (v___x_1244_ == 0)
{
lean_object* v___x_1245_; 
v___x_1245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1245_, 0, v___x_1170_);
v_val_1228_ = v___x_1245_;
goto v___jp_1227_;
}
else
{
lean_object* v___x_1246_; 
lean_dec_ref(v___x_1170_);
v___x_1246_ = lean_box(0);
v_val_1228_ = v___x_1246_;
goto v___jp_1227_;
}
v___jp_1149_:
{
lean_object* v_name_1152_; lean_object* v_scope_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1164_; 
v_name_1152_ = lean_ctor_get(v_dep_1140_, 0);
v_scope_1153_ = lean_ctor_get(v_dep_1140_, 1);
v_isSharedCheck_1164_ = !lean_is_exclusive(v_dep_1140_);
if (v_isSharedCheck_1164_ == 0)
{
lean_object* v_unused_1165_; lean_object* v_unused_1166_; lean_object* v_unused_1167_; 
v_unused_1165_ = lean_ctor_get(v_dep_1140_, 4);
lean_dec(v_unused_1165_);
v_unused_1166_ = lean_ctor_get(v_dep_1140_, 3);
lean_dec(v_unused_1166_);
v_unused_1167_ = lean_ctor_get(v_dep_1140_, 2);
lean_dec(v_unused_1167_);
v___x_1155_ = v_dep_1140_;
v_isShared_1156_ = v_isSharedCheck_1164_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_scope_1153_);
lean_inc(v_name_1152_);
lean_dec(v_dep_1140_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1164_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1161_; 
v___x_1157_ = l_Lake_defaultConfigFile;
v___x_1158_ = lean_box(0);
v___x_1159_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1159_, 0, v_name_1152_);
lean_ctor_set(v___x_1159_, 1, v_scope_1153_);
lean_ctor_set(v___x_1159_, 2, v___x_1157_);
lean_ctor_set(v___x_1159_, 3, v___x_1158_);
lean_ctor_set(v___x_1159_, 4, v_src_1146_);
lean_ctor_set_uint8(v___x_1159_, sizeof(void*)*5, v_inherited_1141_);
if (v_isShared_1156_ == 0)
{
lean_ctor_set(v___x_1155_, 4, v___x_1159_);
lean_ctor_set(v___x_1155_, 3, v_a_1151_);
lean_ctor_set(v___x_1155_, 2, v_remoteUrl_1145_);
lean_ctor_set(v___x_1155_, 1, v_relPkgDir_1144_);
lean_ctor_set(v___x_1155_, 0, v___y_1150_);
v___x_1161_ = v___x_1155_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v___y_1150_);
lean_ctor_set(v_reuseFailAlloc_1163_, 1, v_relPkgDir_1144_);
lean_ctor_set(v_reuseFailAlloc_1163_, 2, v_remoteUrl_1145_);
lean_ctor_set(v_reuseFailAlloc_1163_, 3, v_a_1151_);
lean_ctor_set(v_reuseFailAlloc_1163_, 4, v___x_1159_);
v___x_1161_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
lean_object* v___x_1162_; 
v___x_1162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1162_, 0, v___x_1161_);
return v___x_1162_;
}
}
}
v___jp_1172_:
{
lean_object* v___x_1178_; uint8_t v___x_1179_; 
v___x_1178_ = lean_array_get_size(v___y_1175_);
v___x_1179_ = lean_nat_dec_lt(v___y_1176_, v___x_1178_);
if (v___x_1179_ == 0)
{
lean_dec_ref(v___y_1173_);
v___y_1150_ = v___y_1174_;
v_a_1151_ = v_val_1177_;
goto v___jp_1149_;
}
else
{
lean_object* v___x_1180_; size_t v___x_1181_; size_t v___x_1182_; lean_object* v___x_1819__overap_1183_; lean_object* v___x_1184_; 
v___x_1180_ = lean_box(0);
v___x_1181_ = ((size_t)0ULL);
v___x_1182_ = lean_usize_of_nat(v___x_1178_);
lean_inc_ref(v___y_1175_);
v___x_1819__overap_1183_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___y_1173_, v___f_1171_, v___y_1175_, v___x_1181_, v___x_1182_, v___x_1180_);
lean_inc_ref(v_a_1147_);
v___x_1184_ = lean_apply_2(v___x_1819__overap_1183_, v_a_1147_, lean_box(0));
if (lean_obj_tag(v___x_1184_) == 0)
{
lean_dec_ref_known(v___x_1184_, 1);
v___y_1150_ = v___y_1174_;
v_a_1151_ = v_val_1177_;
goto v___jp_1149_;
}
else
{
lean_object* v_a_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1192_; 
lean_dec_ref(v_val_1177_);
lean_dec_ref(v___y_1174_);
lean_dec_ref(v_src_1146_);
lean_dec_ref(v_remoteUrl_1145_);
lean_dec_ref(v_relPkgDir_1144_);
lean_dec_ref(v_dep_1140_);
v_a_1185_ = lean_ctor_get(v___x_1184_, 0);
v_isSharedCheck_1192_ = !lean_is_exclusive(v___x_1184_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1187_ = v___x_1184_;
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_a_1185_);
lean_dec(v___x_1184_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v___x_1190_; 
if (v_isShared_1188_ == 0)
{
v___x_1190_ = v___x_1187_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_a_1185_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
}
}
}
v___jp_1193_:
{
if (lean_obj_tag(v_a_1194_) == 1)
{
lean_object* v_val_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
lean_dec_ref(v_pkgDir_1168_);
lean_dec_ref(v_name_1143_);
v_val_1195_ = lean_ctor_get(v_a_1194_, 0);
lean_inc_n(v_val_1195_, 2);
lean_dec_ref_known(v_a_1194_, 1);
v___x_1196_ = l_Lake_defaultManifestFile;
v___x_1197_ = l_Lake_joinRelative(v_val_1195_, v___x_1196_);
v___x_1198_ = lean_unsigned_to_nat(0u);
v___x_1199_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_1200_ = l_Lake_Manifest_load(v___x_1197_);
if (lean_obj_tag(v___x_1200_) == 0)
{
lean_object* v_a_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1208_; 
v_a_1201_ = lean_ctor_get(v___x_1200_, 0);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1200_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1203_ = v___x_1200_;
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_a_1201_);
lean_dec(v___x_1200_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___x_1206_; 
if (v_isShared_1204_ == 0)
{
lean_ctor_set_tag(v___x_1203_, 1);
v___x_1206_ = v___x_1203_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_a_1201_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
v___y_1173_ = v___x_1169_;
v___y_1174_ = v_val_1195_;
v___y_1175_ = v___x_1199_;
v___y_1176_ = v___x_1198_;
v_val_1177_ = v___x_1206_;
goto v___jp_1172_;
}
}
}
else
{
lean_object* v_a_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1216_; 
v_a_1209_ = lean_ctor_get(v___x_1200_, 0);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1200_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1211_ = v___x_1200_;
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_a_1209_);
lean_dec(v___x_1200_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1214_; 
if (v_isShared_1212_ == 0)
{
lean_ctor_set_tag(v___x_1211_, 0);
v___x_1214_ = v___x_1211_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_a_1209_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
v___y_1173_ = v___x_1169_;
v___y_1174_ = v_val_1195_;
v___y_1175_ = v___x_1199_;
v___y_1176_ = v___x_1198_;
v_val_1177_ = v___x_1214_;
goto v___jp_1172_;
}
}
}
}
else
{
lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; uint8_t v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; 
lean_dec(v_a_1194_);
lean_dec_ref(v_src_1146_);
lean_dec_ref(v_remoteUrl_1145_);
lean_dec_ref(v_relPkgDir_1144_);
lean_dec_ref(v_dep_1140_);
v___x_1217_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0));
v___x_1218_ = lean_string_append(v_name_1143_, v___x_1217_);
v___x_1219_ = lean_string_append(v___x_1218_, v_pkgDir_1168_);
lean_dec_ref(v_pkgDir_1168_);
v___x_1220_ = 3;
v___x_1221_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1221_, 0, v___x_1219_);
lean_ctor_set_uint8(v___x_1221_, sizeof(void*)*1, v___x_1220_);
lean_inc_ref(v_a_1147_);
v___x_1222_ = lean_apply_2(v_a_1147_, v___x_1221_, lean_box(0));
v___x_1223_ = lean_box(0);
v___x_1224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1223_);
return v___x_1224_;
}
}
v___jp_1227_:
{
uint8_t v___x_1229_; 
v___x_1229_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_1229_ == 0)
{
v_a_1194_ = v_val_1228_;
goto v___jp_1193_;
}
else
{
lean_object* v___x_1230_; size_t v___x_1231_; size_t v___x_1232_; lean_object* v___x_1865__overap_1233_; lean_object* v___x_1234_; 
v___x_1230_ = lean_box(0);
v___x_1231_ = ((size_t)0ULL);
v___x_1232_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_1865__overap_1233_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1169_, v___f_1171_, v___x_1226_, v___x_1231_, v___x_1232_, v___x_1230_);
lean_inc_ref(v_a_1147_);
v___x_1234_ = lean_apply_2(v___x_1865__overap_1233_, v_a_1147_, lean_box(0));
if (lean_obj_tag(v___x_1234_) == 0)
{
lean_dec_ref_known(v___x_1234_, 1);
v_a_1194_ = v_val_1228_;
goto v___jp_1193_;
}
else
{
lean_object* v_a_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1242_; 
lean_dec(v_val_1228_);
lean_dec_ref(v_pkgDir_1168_);
lean_dec_ref(v_src_1146_);
lean_dec_ref(v_remoteUrl_1145_);
lean_dec_ref(v_relPkgDir_1144_);
lean_dec_ref(v_name_1143_);
lean_dec_ref(v_dep_1140_);
v_a_1235_ = lean_ctor_get(v___x_1234_, 0);
v_isSharedCheck_1242_ = !lean_is_exclusive(v___x_1234_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1237_ = v___x_1234_;
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_a_1235_);
lean_dec(v___x_1234_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___x_1240_; 
if (v_isShared_1238_ == 0)
{
v___x_1240_ = v___x_1237_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_a_1235_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___boxed(lean_object* v_dep_1247_, lean_object* v_inherited_1248_, lean_object* v_wsDir_1249_, lean_object* v_name_1250_, lean_object* v_relPkgDir_1251_, lean_object* v_remoteUrl_1252_, lean_object* v_src_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_){
_start:
{
uint8_t v_inherited_boxed_1256_; lean_object* v_res_1257_; 
v_inherited_boxed_1256_ = lean_unbox(v_inherited_1248_);
v_res_1257_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep(v_dep_1247_, v_inherited_boxed_1256_, v_wsDir_1249_, v_name_1250_, v_relPkgDir_1251_, v_remoteUrl_1252_, v_src_1253_, v_a_1254_);
lean_dec_ref(v_a_1254_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(lean_object* v_a_1258_, lean_object* v_name_1259_, lean_object* v_repo_1260_, lean_object* v_url_1261_, lean_object* v_rev_x3f_1262_){
_start:
{
lean_object* v___y_1274_; lean_object* v___y_1313_; lean_object* v___y_1314_; lean_object* v___y_1316_; lean_object* v___y_1317_; lean_object* v___y_1346_; lean_object* v___y_1347_; uint8_t v_a_1348_; lean_object* v___y_1356_; uint8_t v_a_1357_; lean_object* v___y_1365_; lean_object* v___y_1366_; lean_object* v___y_1367_; lean_object* v___y_1368_; uint8_t v_val_1369_; lean_object* v___y_1377_; uint8_t v___y_1378_; lean_object* v___y_1379_; lean_object* v___y_1385_; lean_object* v___y_1386_; uint8_t v___y_1387_; lean_object* v___y_1388_; lean_object* v___y_1390_; lean_object* v___y_1391_; uint8_t v___y_1392_; lean_object* v___y_1421_; uint8_t v___y_1422_; lean_object* v___y_1423_; lean_object* v___y_1424_; lean_object* v___y_1426_; lean_object* v___y_1427_; lean_object* v___y_1428_; uint8_t v_val_1429_; lean_object* v___y_1437_; lean_object* v___y_1438_; lean_object* v___y_1439_; lean_object* v___y_1440_; lean_object* v_a_1441_; lean_object* v___y_1484_; lean_object* v___y_1485_; lean_object* v___y_1486_; lean_object* v___y_1487_; lean_object* v_a_1488_; lean_object* v___y_1510_; lean_object* v___y_1511_; lean_object* v___y_1512_; lean_object* v___y_1513_; lean_object* v___y_1552_; lean_object* v___y_1553_; lean_object* v___y_1554_; lean_object* v___y_1555_; lean_object* v___y_1557_; lean_object* v___y_1558_; lean_object* v___y_1559_; lean_object* v___y_1588_; lean_object* v___y_1589_; lean_object* v___y_1590_; lean_object* v___y_1591_; lean_object* v___y_1593_; uint8_t v_a_1594_; lean_object* v___y_1602_; uint8_t v_a_1603_; lean_object* v___y_1611_; lean_object* v___y_1612_; lean_object* v___y_1613_; uint8_t v_val_1614_; uint8_t v___y_1622_; uint8_t v___y_1623_; lean_object* v___y_1624_; uint8_t v___y_1629_; uint8_t v___y_1630_; lean_object* v___y_1631_; lean_object* v___y_1632_; uint8_t v___y_1634_; uint8_t v___y_1635_; lean_object* v___y_1636_; uint8_t v___y_1665_; uint8_t v___y_1666_; lean_object* v___y_1667_; lean_object* v___y_1668_; lean_object* v___y_1670_; uint8_t v___y_1671_; lean_object* v___y_1672_; uint8_t v___y_1673_; lean_object* v___y_1674_; lean_object* v___y_1675_; lean_object* v_a_1676_; lean_object* v___y_1720_; lean_object* v___y_1721_; lean_object* v___y_1722_; uint8_t v_val_1723_; lean_object* v___y_1731_; lean_object* v___y_1732_; lean_object* v___y_1733_; lean_object* v___y_1734_; lean_object* v_a_1735_; lean_object* v___y_1752_; lean_object* v___y_1753_; lean_object* v___y_1754_; lean_object* v___y_1755_; lean_object* v___y_1765_; lean_object* v___y_1766_; lean_object* v___y_1767_; lean_object* v___y_1768_; lean_object* v___y_1770_; lean_object* v___y_1771_; lean_object* v___y_1772_; lean_object* v___y_1773_; lean_object* v___y_1775_; lean_object* v___y_1776_; lean_object* v___y_1777_; lean_object* v_a_1778_; lean_object* v___y_1851_; lean_object* v___y_1852_; lean_object* v___y_1853_; uint8_t v_a_1854_; lean_object* v___y_1916_; lean_object* v___y_1917_; lean_object* v_a_1918_; lean_object* v___y_1929_; lean_object* v___y_1930_; lean_object* v_a_1931_; lean_object* v___y_1942_; lean_object* v___y_1943_; lean_object* v___y_1944_; lean_object* v___y_1945_; lean_object* v_val_1946_; lean_object* v___y_1954_; lean_object* v___y_1955_; uint8_t v_a_1956_; lean_object* v___y_1965_; 
if (lean_obj_tag(v_rev_x3f_1262_) == 0)
{
lean_object* v___x_1974_; 
v___x_1974_ = l_Lake_Git_upstreamBranch;
v___y_1965_ = v___x_1974_;
goto v___jp_1964_;
}
else
{
lean_object* v_val_1975_; 
v_val_1975_ = lean_ctor_get(v_rev_x3f_1262_, 0);
lean_inc(v_val_1975_);
lean_dec_ref_known(v_rev_x3f_1262_, 1);
v___y_1965_ = v_val_1975_;
goto v___jp_1964_;
}
v___jp_1264_:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; 
v___x_1265_ = lean_box(0);
v___x_1266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1266_, 0, v___x_1265_);
return v___x_1266_;
}
v___jp_1267_:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1268_ = lean_box(0);
v___x_1269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1269_, 0, v___x_1268_);
return v___x_1269_;
}
v___jp_1270_:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1271_ = lean_box(0);
v___x_1272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1272_, 0, v___x_1271_);
return v___x_1272_;
}
v___jp_1273_:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1275_ = lean_unsigned_to_nat(0u);
v___x_1276_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_1277_ = l_Lake_GitRepo_gcAuto(v_repo_1260_, v___x_1276_);
if (lean_obj_tag(v___x_1277_) == 0)
{
lean_object* v_a_1278_; lean_object* v_a_1279_; lean_object* v___x_1280_; uint8_t v___x_1281_; 
v_a_1278_ = lean_ctor_get(v___x_1277_, 0);
lean_inc(v_a_1278_);
v_a_1279_ = lean_ctor_get(v___x_1277_, 1);
lean_inc(v_a_1279_);
lean_dec_ref_known(v___x_1277_, 2);
v___x_1280_ = lean_array_get_size(v_a_1279_);
v___x_1281_ = lean_nat_dec_lt(v___x_1275_, v___x_1280_);
if (v___x_1281_ == 0)
{
lean_object* v___x_1282_; 
lean_dec(v_a_1279_);
v___x_1282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1282_, 0, v_a_1278_);
return v___x_1282_;
}
else
{
lean_object* v___x_1283_; size_t v___x_1284_; size_t v___x_1285_; lean_object* v___x_1286_; 
v___x_1283_ = lean_box(0);
v___x_1284_ = ((size_t)0ULL);
v___x_1285_ = lean_usize_of_nat(v___x_1280_);
v___x_1286_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1279_, v___x_1284_, v___x_1285_, v___x_1283_, v___y_1274_);
lean_dec(v_a_1279_);
if (lean_obj_tag(v___x_1286_) == 0)
{
lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1293_; 
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1293_ == 0)
{
lean_object* v_unused_1294_; 
v_unused_1294_ = lean_ctor_get(v___x_1286_, 0);
lean_dec(v_unused_1294_);
v___x_1288_ = v___x_1286_;
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
else
{
lean_dec(v___x_1286_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1291_; 
if (v_isShared_1289_ == 0)
{
lean_ctor_set(v___x_1288_, 0, v_a_1278_);
v___x_1291_ = v___x_1288_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_a_1278_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
else
{
lean_dec(v_a_1278_);
return v___x_1286_;
}
}
}
else
{
lean_object* v_a_1295_; lean_object* v___x_1296_; uint8_t v___x_1297_; 
v_a_1295_ = lean_ctor_get(v___x_1277_, 1);
lean_inc(v_a_1295_);
lean_dec_ref_known(v___x_1277_, 2);
v___x_1296_ = lean_array_get_size(v_a_1295_);
v___x_1297_ = lean_nat_dec_lt(v___x_1275_, v___x_1296_);
if (v___x_1297_ == 0)
{
lean_object* v___x_1298_; lean_object* v___x_1299_; 
lean_dec(v_a_1295_);
v___x_1298_ = lean_box(0);
v___x_1299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1298_);
return v___x_1299_;
}
else
{
lean_object* v___x_1300_; size_t v___x_1301_; size_t v___x_1302_; lean_object* v___x_1303_; 
v___x_1300_ = lean_box(0);
v___x_1301_ = ((size_t)0ULL);
v___x_1302_ = lean_usize_of_nat(v___x_1296_);
v___x_1303_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1295_, v___x_1301_, v___x_1302_, v___x_1300_, v___y_1274_);
lean_dec(v_a_1295_);
if (lean_obj_tag(v___x_1303_) == 0)
{
lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1310_; 
v_isSharedCheck_1310_ = !lean_is_exclusive(v___x_1303_);
if (v_isSharedCheck_1310_ == 0)
{
lean_object* v_unused_1311_; 
v_unused_1311_ = lean_ctor_get(v___x_1303_, 0);
lean_dec(v_unused_1311_);
v___x_1305_ = v___x_1303_;
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
else
{
lean_dec(v___x_1303_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v___x_1308_; 
if (v_isShared_1306_ == 0)
{
lean_ctor_set_tag(v___x_1305_, 1);
lean_ctor_set(v___x_1305_, 0, v___x_1300_);
v___x_1308_ = v___x_1305_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v___x_1300_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
}
else
{
return v___x_1303_;
}
}
}
}
v___jp_1312_:
{
if (lean_obj_tag(v___y_1314_) == 0)
{
lean_dec_ref_known(v___y_1314_, 1);
v___y_1274_ = v___y_1313_;
goto v___jp_1273_;
}
else
{
lean_dec_ref(v_repo_1260_);
return v___y_1314_;
}
}
v___jp_1315_:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1318_ = lean_unsigned_to_nat(0u);
v___x_1319_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1260_);
lean_inc_ref(v___y_1317_);
v___x_1320_ = l_Lake_GitRepo_pruneRemote(v___y_1317_, v_repo_1260_, v___x_1319_);
if (lean_obj_tag(v___x_1320_) == 0)
{
lean_object* v_a_1321_; lean_object* v___x_1322_; uint8_t v___x_1323_; 
v_a_1321_ = lean_ctor_get(v___x_1320_, 1);
lean_inc(v_a_1321_);
lean_dec_ref_known(v___x_1320_, 2);
v___x_1322_ = lean_array_get_size(v_a_1321_);
v___x_1323_ = lean_nat_dec_lt(v___x_1318_, v___x_1322_);
if (v___x_1323_ == 0)
{
lean_dec(v_a_1321_);
v___y_1274_ = v___y_1316_;
goto v___jp_1273_;
}
else
{
lean_object* v___x_1324_; size_t v___x_1325_; size_t v___x_1326_; lean_object* v___x_1327_; 
v___x_1324_ = lean_box(0);
v___x_1325_ = ((size_t)0ULL);
v___x_1326_ = lean_usize_of_nat(v___x_1322_);
v___x_1327_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1321_, v___x_1325_, v___x_1326_, v___x_1324_, v___y_1316_);
lean_dec(v_a_1321_);
if (lean_obj_tag(v___x_1327_) == 0)
{
lean_dec_ref_known(v___x_1327_, 1);
v___y_1274_ = v___y_1316_;
goto v___jp_1273_;
}
else
{
v___y_1313_ = v___y_1316_;
v___y_1314_ = v___x_1327_;
goto v___jp_1312_;
}
}
}
else
{
lean_object* v_a_1328_; lean_object* v___x_1329_; uint8_t v___x_1330_; 
v_a_1328_ = lean_ctor_get(v___x_1320_, 1);
lean_inc(v_a_1328_);
lean_dec_ref_known(v___x_1320_, 2);
v___x_1329_ = lean_array_get_size(v_a_1328_);
v___x_1330_ = lean_nat_dec_lt(v___x_1318_, v___x_1329_);
if (v___x_1330_ == 0)
{
lean_object* v___x_1331_; lean_object* v___x_1332_; 
lean_dec(v_a_1328_);
lean_dec_ref(v_repo_1260_);
v___x_1331_ = lean_box(0);
v___x_1332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1331_);
return v___x_1332_;
}
else
{
lean_object* v___x_1333_; size_t v___x_1334_; size_t v___x_1335_; lean_object* v___x_1336_; 
v___x_1333_ = lean_box(0);
v___x_1334_ = ((size_t)0ULL);
v___x_1335_ = lean_usize_of_nat(v___x_1329_);
v___x_1336_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1328_, v___x_1334_, v___x_1335_, v___x_1333_, v___y_1316_);
lean_dec(v_a_1328_);
if (lean_obj_tag(v___x_1336_) == 0)
{
lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1343_; 
lean_dec_ref(v_repo_1260_);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1336_);
if (v_isSharedCheck_1343_ == 0)
{
lean_object* v_unused_1344_; 
v_unused_1344_ = lean_ctor_get(v___x_1336_, 0);
lean_dec(v_unused_1344_);
v___x_1338_ = v___x_1336_;
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
else
{
lean_dec(v___x_1336_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v___x_1341_; 
if (v_isShared_1339_ == 0)
{
lean_ctor_set_tag(v___x_1338_, 1);
lean_ctor_set(v___x_1338_, 0, v___x_1333_);
v___x_1341_ = v___x_1338_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v___x_1333_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
return v___x_1341_;
}
}
}
else
{
v___y_1313_ = v___y_1316_;
v___y_1314_ = v___x_1336_;
goto v___jp_1312_;
}
}
}
}
v___jp_1345_:
{
if (v_a_1348_ == 0)
{
lean_dec_ref(v_name_1259_);
v___y_1316_ = v___y_1346_;
v___y_1317_ = v___y_1347_;
goto v___jp_1315_;
}
else
{
lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; uint8_t v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; 
v___x_1349_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff___closed__0));
v___x_1350_ = lean_string_append(v_name_1259_, v___x_1349_);
v___x_1351_ = lean_string_append(v___x_1350_, v_repo_1260_);
v___x_1352_ = 2;
v___x_1353_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1353_, 0, v___x_1351_);
lean_ctor_set_uint8(v___x_1353_, sizeof(void*)*1, v___x_1352_);
lean_inc_ref(v___y_1346_);
v___x_1354_ = lean_apply_2(v___y_1346_, v___x_1353_, lean_box(0));
v___y_1316_ = v___y_1346_;
v___y_1317_ = v___y_1347_;
goto v___jp_1315_;
}
}
v___jp_1355_:
{
if (v_a_1357_ == 0)
{
lean_dec_ref(v_repo_1260_);
lean_dec_ref(v_name_1259_);
goto v___jp_1264_;
}
else
{
lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; uint8_t v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1358_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff___closed__0));
v___x_1359_ = lean_string_append(v_name_1259_, v___x_1358_);
v___x_1360_ = lean_string_append(v___x_1359_, v_repo_1260_);
lean_dec_ref(v_repo_1260_);
v___x_1361_ = 2;
v___x_1362_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1362_, 0, v___x_1360_);
lean_ctor_set_uint8(v___x_1362_, sizeof(void*)*1, v___x_1361_);
lean_inc_ref(v___y_1356_);
v___x_1363_ = lean_apply_2(v___y_1356_, v___x_1362_, lean_box(0));
goto v___jp_1264_;
}
}
v___jp_1364_:
{
lean_object* v___x_1370_; uint8_t v___x_1371_; 
v___x_1370_ = lean_array_get_size(v___y_1365_);
v___x_1371_ = lean_nat_dec_lt(v___y_1368_, v___x_1370_);
if (v___x_1371_ == 0)
{
v___y_1346_ = v___y_1366_;
v___y_1347_ = v___y_1367_;
v_a_1348_ = v_val_1369_;
goto v___jp_1345_;
}
else
{
lean_object* v___x_1372_; size_t v___x_1373_; size_t v___x_1374_; lean_object* v___x_1375_; 
v___x_1372_ = lean_box(0);
v___x_1373_ = ((size_t)0ULL);
v___x_1374_ = lean_usize_of_nat(v___x_1370_);
v___x_1375_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_1365_, v___x_1373_, v___x_1374_, v___x_1372_, v___y_1366_);
if (lean_obj_tag(v___x_1375_) == 0)
{
lean_dec_ref_known(v___x_1375_, 1);
v___y_1346_ = v___y_1366_;
v___y_1347_ = v___y_1367_;
v_a_1348_ = v_val_1369_;
goto v___jp_1345_;
}
else
{
lean_dec_ref(v_name_1259_);
if (lean_obj_tag(v___x_1375_) == 0)
{
lean_dec_ref_known(v___x_1375_, 1);
v___y_1316_ = v___y_1366_;
v___y_1317_ = v___y_1367_;
goto v___jp_1315_;
}
else
{
lean_dec_ref(v_repo_1260_);
return v___x_1375_;
}
}
}
}
v___jp_1376_:
{
uint8_t v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; 
lean_inc_ref(v_repo_1260_);
v___x_1380_ = l_Lake_GitRepo_hasNoDiff(v_repo_1260_);
v___x_1381_ = lean_unsigned_to_nat(0u);
v___x_1382_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
if (v___x_1380_ == 0)
{
uint8_t v___x_1383_; 
v___x_1383_ = 1;
v___y_1365_ = v___x_1382_;
v___y_1366_ = v___y_1377_;
v___y_1367_ = v___y_1379_;
v___y_1368_ = v___x_1381_;
v_val_1369_ = v___x_1383_;
goto v___jp_1364_;
}
else
{
v___y_1365_ = v___x_1382_;
v___y_1366_ = v___y_1377_;
v___y_1367_ = v___y_1379_;
v___y_1368_ = v___x_1381_;
v_val_1369_ = v___y_1378_;
goto v___jp_1364_;
}
}
v___jp_1384_:
{
if (lean_obj_tag(v___y_1388_) == 0)
{
lean_dec_ref_known(v___y_1388_, 1);
v___y_1377_ = v___y_1385_;
v___y_1378_ = v___y_1387_;
v___y_1379_ = v___y_1386_;
goto v___jp_1376_;
}
else
{
lean_dec_ref(v_repo_1260_);
lean_dec_ref(v_name_1259_);
return v___y_1388_;
}
}
v___jp_1389_:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1393_ = lean_unsigned_to_nat(0u);
v___x_1394_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1260_);
v___x_1395_ = l_Lake_GitRepo_clean(v_repo_1260_, v___x_1394_);
if (lean_obj_tag(v___x_1395_) == 0)
{
lean_object* v_a_1396_; lean_object* v___x_1397_; uint8_t v___x_1398_; 
v_a_1396_ = lean_ctor_get(v___x_1395_, 1);
lean_inc(v_a_1396_);
lean_dec_ref_known(v___x_1395_, 2);
v___x_1397_ = lean_array_get_size(v_a_1396_);
v___x_1398_ = lean_nat_dec_lt(v___x_1393_, v___x_1397_);
if (v___x_1398_ == 0)
{
lean_dec(v_a_1396_);
v___y_1377_ = v___y_1390_;
v___y_1378_ = v___y_1392_;
v___y_1379_ = v___y_1391_;
goto v___jp_1376_;
}
else
{
lean_object* v___x_1399_; size_t v___x_1400_; size_t v___x_1401_; lean_object* v___x_1402_; 
v___x_1399_ = lean_box(0);
v___x_1400_ = ((size_t)0ULL);
v___x_1401_ = lean_usize_of_nat(v___x_1397_);
v___x_1402_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1396_, v___x_1400_, v___x_1401_, v___x_1399_, v___y_1390_);
lean_dec(v_a_1396_);
if (lean_obj_tag(v___x_1402_) == 0)
{
lean_dec_ref_known(v___x_1402_, 1);
v___y_1377_ = v___y_1390_;
v___y_1378_ = v___y_1392_;
v___y_1379_ = v___y_1391_;
goto v___jp_1376_;
}
else
{
v___y_1385_ = v___y_1390_;
v___y_1386_ = v___y_1391_;
v___y_1387_ = v___y_1392_;
v___y_1388_ = v___x_1402_;
goto v___jp_1384_;
}
}
}
else
{
lean_object* v_a_1403_; lean_object* v___x_1404_; uint8_t v___x_1405_; 
v_a_1403_ = lean_ctor_get(v___x_1395_, 1);
lean_inc(v_a_1403_);
lean_dec_ref_known(v___x_1395_, 2);
v___x_1404_ = lean_array_get_size(v_a_1403_);
v___x_1405_ = lean_nat_dec_lt(v___x_1393_, v___x_1404_);
if (v___x_1405_ == 0)
{
lean_object* v___x_1406_; lean_object* v___x_1407_; 
lean_dec(v_a_1403_);
lean_dec_ref(v_repo_1260_);
lean_dec_ref(v_name_1259_);
v___x_1406_ = lean_box(0);
v___x_1407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1407_, 0, v___x_1406_);
return v___x_1407_;
}
else
{
lean_object* v___x_1408_; size_t v___x_1409_; size_t v___x_1410_; lean_object* v___x_1411_; 
v___x_1408_ = lean_box(0);
v___x_1409_ = ((size_t)0ULL);
v___x_1410_ = lean_usize_of_nat(v___x_1404_);
v___x_1411_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1403_, v___x_1409_, v___x_1410_, v___x_1408_, v___y_1390_);
lean_dec(v_a_1403_);
if (lean_obj_tag(v___x_1411_) == 0)
{
lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1418_; 
lean_dec_ref(v_repo_1260_);
lean_dec_ref(v_name_1259_);
v_isSharedCheck_1418_ = !lean_is_exclusive(v___x_1411_);
if (v_isSharedCheck_1418_ == 0)
{
lean_object* v_unused_1419_; 
v_unused_1419_ = lean_ctor_get(v___x_1411_, 0);
lean_dec(v_unused_1419_);
v___x_1413_ = v___x_1411_;
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
else
{
lean_dec(v___x_1411_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___x_1416_; 
if (v_isShared_1414_ == 0)
{
lean_ctor_set_tag(v___x_1413_, 1);
lean_ctor_set(v___x_1413_, 0, v___x_1408_);
v___x_1416_ = v___x_1413_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v___x_1408_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
}
else
{
v___y_1385_ = v___y_1390_;
v___y_1386_ = v___y_1391_;
v___y_1387_ = v___y_1392_;
v___y_1388_ = v___x_1411_;
goto v___jp_1384_;
}
}
}
}
v___jp_1420_:
{
if (lean_obj_tag(v___y_1424_) == 0)
{
lean_dec_ref_known(v___y_1424_, 1);
v___y_1390_ = v___y_1421_;
v___y_1391_ = v___y_1423_;
v___y_1392_ = v___y_1422_;
goto v___jp_1389_;
}
else
{
lean_dec_ref(v_repo_1260_);
lean_dec_ref(v_name_1259_);
return v___y_1424_;
}
}
v___jp_1425_:
{
lean_object* v___x_1430_; uint8_t v___x_1431_; 
v___x_1430_ = lean_array_get_size(v___y_1427_);
v___x_1431_ = lean_nat_dec_lt(v___y_1428_, v___x_1430_);
if (v___x_1431_ == 0)
{
v___y_1356_ = v___y_1426_;
v_a_1357_ = v_val_1429_;
goto v___jp_1355_;
}
else
{
lean_object* v___x_1432_; size_t v___x_1433_; size_t v___x_1434_; lean_object* v___x_1435_; 
v___x_1432_ = lean_box(0);
v___x_1433_ = ((size_t)0ULL);
v___x_1434_ = lean_usize_of_nat(v___x_1430_);
v___x_1435_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_1427_, v___x_1433_, v___x_1434_, v___x_1432_, v___y_1426_);
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_dec_ref_known(v___x_1435_, 1);
v___y_1356_ = v___y_1426_;
v_a_1357_ = v_val_1429_;
goto v___jp_1355_;
}
else
{
lean_dec_ref(v_repo_1260_);
lean_dec_ref(v_name_1259_);
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_dec_ref_known(v___x_1435_, 1);
goto v___jp_1264_;
}
else
{
return v___x_1435_;
}
}
}
}
v___jp_1436_:
{
lean_object* v___x_1442_; uint8_t v___x_1443_; 
v___x_1442_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
v___x_1443_ = l_Option_instDecidableEq___redArg(v___x_1442_, v_a_1441_, v___y_1437_);
if (v___x_1443_ == 0)
{
lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; uint8_t v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1444_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__0));
lean_inc_ref(v_name_1259_);
v___x_1445_ = lean_string_append(v_name_1259_, v___x_1444_);
v___x_1446_ = lean_string_append(v___x_1445_, v___y_1439_);
v___x_1447_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__1));
v___x_1448_ = lean_string_append(v___x_1446_, v___x_1447_);
v___x_1449_ = 1;
v___x_1450_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1450_, 0, v___x_1448_);
lean_ctor_set_uint8(v___x_1450_, sizeof(void*)*1, v___x_1449_);
lean_inc_ref(v___y_1438_);
v___x_1451_ = lean_apply_2(v___y_1438_, v___x_1450_, lean_box(0));
v___x_1452_ = lean_unsigned_to_nat(0u);
v___x_1453_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1260_);
v___x_1454_ = l_Lake_GitRepo_checkoutDetach(v___y_1439_, v_repo_1260_, v___x_1453_);
if (lean_obj_tag(v___x_1454_) == 0)
{
lean_object* v_a_1455_; lean_object* v___x_1456_; uint8_t v___x_1457_; 
v_a_1455_ = lean_ctor_get(v___x_1454_, 1);
lean_inc(v_a_1455_);
lean_dec_ref_known(v___x_1454_, 2);
v___x_1456_ = lean_array_get_size(v_a_1455_);
v___x_1457_ = lean_nat_dec_lt(v___x_1452_, v___x_1456_);
if (v___x_1457_ == 0)
{
lean_dec(v_a_1455_);
v___y_1390_ = v___y_1438_;
v___y_1391_ = v___y_1440_;
v___y_1392_ = v___x_1443_;
goto v___jp_1389_;
}
else
{
lean_object* v___x_1458_; size_t v___x_1459_; size_t v___x_1460_; lean_object* v___x_1461_; 
v___x_1458_ = lean_box(0);
v___x_1459_ = ((size_t)0ULL);
v___x_1460_ = lean_usize_of_nat(v___x_1456_);
v___x_1461_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1455_, v___x_1459_, v___x_1460_, v___x_1458_, v___y_1438_);
lean_dec(v_a_1455_);
if (lean_obj_tag(v___x_1461_) == 0)
{
lean_dec_ref_known(v___x_1461_, 1);
v___y_1390_ = v___y_1438_;
v___y_1391_ = v___y_1440_;
v___y_1392_ = v___x_1443_;
goto v___jp_1389_;
}
else
{
v___y_1421_ = v___y_1438_;
v___y_1422_ = v___x_1443_;
v___y_1423_ = v___y_1440_;
v___y_1424_ = v___x_1461_;
goto v___jp_1420_;
}
}
}
else
{
lean_object* v_a_1462_; lean_object* v___x_1463_; uint8_t v___x_1464_; 
v_a_1462_ = lean_ctor_get(v___x_1454_, 1);
lean_inc(v_a_1462_);
lean_dec_ref_known(v___x_1454_, 2);
v___x_1463_ = lean_array_get_size(v_a_1462_);
v___x_1464_ = lean_nat_dec_lt(v___x_1452_, v___x_1463_);
if (v___x_1464_ == 0)
{
lean_object* v___x_1465_; lean_object* v___x_1466_; 
lean_dec(v_a_1462_);
lean_dec_ref(v_repo_1260_);
lean_dec_ref(v_name_1259_);
v___x_1465_ = lean_box(0);
v___x_1466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1466_, 0, v___x_1465_);
return v___x_1466_;
}
else
{
lean_object* v___x_1467_; size_t v___x_1468_; size_t v___x_1469_; lean_object* v___x_1470_; 
v___x_1467_ = lean_box(0);
v___x_1468_ = ((size_t)0ULL);
v___x_1469_ = lean_usize_of_nat(v___x_1463_);
v___x_1470_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1462_, v___x_1468_, v___x_1469_, v___x_1467_, v___y_1438_);
lean_dec(v_a_1462_);
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1477_; 
lean_dec_ref(v_repo_1260_);
lean_dec_ref(v_name_1259_);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1477_ == 0)
{
lean_object* v_unused_1478_; 
v_unused_1478_ = lean_ctor_get(v___x_1470_, 0);
lean_dec(v_unused_1478_);
v___x_1472_ = v___x_1470_;
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
else
{
lean_dec(v___x_1470_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1475_; 
if (v_isShared_1473_ == 0)
{
lean_ctor_set_tag(v___x_1472_, 1);
lean_ctor_set(v___x_1472_, 0, v___x_1467_);
v___x_1475_ = v___x_1472_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v___x_1467_);
v___x_1475_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
return v___x_1475_;
}
}
}
else
{
v___y_1421_ = v___y_1438_;
v___y_1422_ = v___x_1443_;
v___y_1423_ = v___y_1440_;
v___y_1424_ = v___x_1470_;
goto v___jp_1420_;
}
}
}
}
else
{
uint8_t v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; 
lean_dec_ref(v___y_1439_);
lean_inc_ref(v_repo_1260_);
v___x_1479_ = l_Lake_GitRepo_hasNoDiff(v_repo_1260_);
v___x_1480_ = lean_unsigned_to_nat(0u);
v___x_1481_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
if (v___x_1479_ == 0)
{
v___y_1426_ = v___y_1438_;
v___y_1427_ = v___x_1481_;
v___y_1428_ = v___x_1480_;
v_val_1429_ = v___x_1443_;
goto v___jp_1425_;
}
else
{
uint8_t v___x_1482_; 
v___x_1482_ = 0;
v___y_1426_ = v___y_1438_;
v___y_1427_ = v___x_1481_;
v___y_1428_ = v___x_1480_;
v_val_1429_ = v___x_1482_;
goto v___jp_1425_;
}
}
}
v___jp_1483_:
{
if (lean_obj_tag(v_a_1488_) == 1)
{
lean_object* v_val_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; uint8_t v___x_1493_; 
lean_dec_ref(v___y_1487_);
lean_dec_ref(v___y_1484_);
v_val_1489_ = lean_ctor_get(v_a_1488_, 0);
lean_inc(v_val_1489_);
v___x_1490_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__0));
lean_inc_ref(v_repo_1260_);
v___x_1491_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_1490_, v_repo_1260_);
v___x_1492_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_1493_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_1493_ == 0)
{
v___y_1437_ = v_a_1488_;
v___y_1438_ = v___y_1485_;
v___y_1439_ = v_val_1489_;
v___y_1440_ = v___y_1486_;
v_a_1441_ = v___x_1491_;
goto v___jp_1436_;
}
else
{
lean_object* v___x_1494_; size_t v___x_1495_; size_t v___x_1496_; lean_object* v___x_1497_; 
v___x_1494_ = lean_box(0);
v___x_1495_ = ((size_t)0ULL);
v___x_1496_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_1497_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_1492_, v___x_1495_, v___x_1496_, v___x_1494_, v___y_1485_);
if (lean_obj_tag(v___x_1497_) == 0)
{
lean_dec_ref_known(v___x_1497_, 1);
v___y_1437_ = v_a_1488_;
v___y_1438_ = v___y_1485_;
v___y_1439_ = v_val_1489_;
v___y_1440_ = v___y_1486_;
v_a_1441_ = v___x_1491_;
goto v___jp_1436_;
}
else
{
lean_dec(v___x_1491_);
lean_dec_ref_known(v_a_1488_, 1);
lean_dec(v_val_1489_);
lean_dec_ref(v_repo_1260_);
lean_dec_ref(v_name_1259_);
return v___x_1497_;
}
}
}
else
{
lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; uint8_t v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; 
lean_dec(v_a_1488_);
lean_dec_ref(v_repo_1260_);
v___x_1498_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__1));
v___x_1499_ = lean_string_append(v_name_1259_, v___x_1498_);
v___x_1500_ = lean_string_append(v___x_1499_, v___y_1487_);
lean_dec_ref(v___y_1487_);
v___x_1501_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__2));
v___x_1502_ = lean_string_append(v___x_1500_, v___x_1501_);
v___x_1503_ = lean_string_append(v___x_1502_, v___y_1484_);
lean_dec_ref(v___y_1484_);
v___x_1504_ = 3;
v___x_1505_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1505_, 0, v___x_1503_);
lean_ctor_set_uint8(v___x_1505_, sizeof(void*)*1, v___x_1504_);
lean_inc_ref(v___y_1485_);
v___x_1506_ = lean_apply_2(v___y_1485_, v___x_1505_, lean_box(0));
v___x_1507_ = lean_box(0);
v___x_1508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1507_);
return v___x_1508_;
}
}
v___jp_1509_:
{
lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; uint8_t v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; 
v___x_1514_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__3));
lean_inc_ref(v_name_1259_);
v___x_1515_ = lean_string_append(v_name_1259_, v___x_1514_);
v___x_1516_ = lean_string_append(v___x_1515_, v___y_1512_);
v___x_1517_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__4));
v___x_1518_ = lean_string_append(v___x_1516_, v___x_1517_);
v___x_1519_ = lean_string_append(v___x_1518_, v___y_1510_);
v___x_1520_ = 1;
v___x_1521_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1521_, 0, v___x_1519_);
lean_ctor_set_uint8(v___x_1521_, sizeof(void*)*1, v___x_1520_);
lean_inc_ref(v___y_1513_);
v___x_1522_ = lean_apply_2(v___y_1513_, v___x_1521_, lean_box(0));
v___x_1523_ = lean_unsigned_to_nat(0u);
v___x_1524_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v___y_1512_);
lean_inc_ref(v___y_1511_);
lean_inc_ref(v_repo_1260_);
v___x_1525_ = l_Lake_GitRepo_fetchRevision_x3f(v_repo_1260_, v___y_1511_, v___y_1512_, v___x_1524_);
if (lean_obj_tag(v___x_1525_) == 0)
{
lean_object* v_a_1526_; lean_object* v_a_1527_; lean_object* v___x_1528_; uint8_t v___x_1529_; 
v_a_1526_ = lean_ctor_get(v___x_1525_, 0);
lean_inc(v_a_1526_);
v_a_1527_ = lean_ctor_get(v___x_1525_, 1);
lean_inc(v_a_1527_);
lean_dec_ref_known(v___x_1525_, 2);
v___x_1528_ = lean_array_get_size(v_a_1527_);
v___x_1529_ = lean_nat_dec_lt(v___x_1523_, v___x_1528_);
if (v___x_1529_ == 0)
{
lean_dec(v_a_1527_);
v___y_1484_ = v___y_1510_;
v___y_1485_ = v___y_1513_;
v___y_1486_ = v___y_1511_;
v___y_1487_ = v___y_1512_;
v_a_1488_ = v_a_1526_;
goto v___jp_1483_;
}
else
{
lean_object* v___x_1530_; size_t v___x_1531_; size_t v___x_1532_; lean_object* v___x_1533_; 
v___x_1530_ = lean_box(0);
v___x_1531_ = ((size_t)0ULL);
v___x_1532_ = lean_usize_of_nat(v___x_1528_);
v___x_1533_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1527_, v___x_1531_, v___x_1532_, v___x_1530_, v___y_1513_);
lean_dec(v_a_1527_);
if (lean_obj_tag(v___x_1533_) == 0)
{
lean_dec_ref_known(v___x_1533_, 1);
v___y_1484_ = v___y_1510_;
v___y_1485_ = v___y_1513_;
v___y_1486_ = v___y_1511_;
v___y_1487_ = v___y_1512_;
v_a_1488_ = v_a_1526_;
goto v___jp_1483_;
}
else
{
lean_dec(v_a_1526_);
lean_dec_ref(v___y_1512_);
lean_dec_ref(v___y_1510_);
lean_dec_ref(v_repo_1260_);
lean_dec_ref(v_name_1259_);
return v___x_1533_;
}
}
}
else
{
lean_object* v_a_1534_; lean_object* v___x_1535_; uint8_t v___x_1536_; 
lean_dec_ref(v___y_1512_);
lean_dec_ref(v___y_1510_);
lean_dec_ref(v_repo_1260_);
lean_dec_ref(v_name_1259_);
v_a_1534_ = lean_ctor_get(v___x_1525_, 1);
lean_inc(v_a_1534_);
lean_dec_ref_known(v___x_1525_, 2);
v___x_1535_ = lean_array_get_size(v_a_1534_);
v___x_1536_ = lean_nat_dec_lt(v___x_1523_, v___x_1535_);
if (v___x_1536_ == 0)
{
lean_object* v___x_1537_; lean_object* v___x_1538_; 
lean_dec(v_a_1534_);
v___x_1537_ = lean_box(0);
v___x_1538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1537_);
return v___x_1538_;
}
else
{
lean_object* v___x_1539_; size_t v___x_1540_; size_t v___x_1541_; lean_object* v___x_1542_; 
v___x_1539_ = lean_box(0);
v___x_1540_ = ((size_t)0ULL);
v___x_1541_ = lean_usize_of_nat(v___x_1535_);
v___x_1542_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1534_, v___x_1540_, v___x_1541_, v___x_1539_, v___y_1513_);
lean_dec(v_a_1534_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1549_; 
v_isSharedCheck_1549_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1549_ == 0)
{
lean_object* v_unused_1550_; 
v_unused_1550_ = lean_ctor_get(v___x_1542_, 0);
lean_dec(v_unused_1550_);
v___x_1544_ = v___x_1542_;
v_isShared_1545_ = v_isSharedCheck_1549_;
goto v_resetjp_1543_;
}
else
{
lean_dec(v___x_1542_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1549_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v___x_1547_; 
if (v_isShared_1545_ == 0)
{
lean_ctor_set_tag(v___x_1544_, 1);
lean_ctor_set(v___x_1544_, 0, v___x_1539_);
v___x_1547_ = v___x_1544_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v___x_1539_);
v___x_1547_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
return v___x_1547_;
}
}
}
else
{
return v___x_1542_;
}
}
}
}
v___jp_1551_:
{
if (lean_obj_tag(v___y_1555_) == 0)
{
lean_dec_ref_known(v___y_1555_, 1);
v___y_1510_ = v___y_1552_;
v___y_1511_ = v___y_1553_;
v___y_1512_ = v___y_1554_;
v___y_1513_ = v_a_1258_;
goto v___jp_1509_;
}
else
{
lean_dec_ref(v___y_1554_);
lean_dec_ref(v___y_1552_);
lean_dec_ref(v_repo_1260_);
lean_dec_ref(v_name_1259_);
return v___y_1555_;
}
}
v___jp_1556_:
{
lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1560_ = lean_unsigned_to_nat(0u);
v___x_1561_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1260_);
lean_inc_ref(v___y_1557_);
lean_inc_ref(v___y_1558_);
v___x_1562_ = l_Lake_GitRepo_addRemote(v___y_1558_, v___y_1557_, v_repo_1260_, v___x_1561_);
if (lean_obj_tag(v___x_1562_) == 0)
{
lean_object* v_a_1563_; lean_object* v___x_1564_; uint8_t v___x_1565_; 
v_a_1563_ = lean_ctor_get(v___x_1562_, 1);
lean_inc(v_a_1563_);
lean_dec_ref_known(v___x_1562_, 2);
v___x_1564_ = lean_array_get_size(v_a_1563_);
v___x_1565_ = lean_nat_dec_lt(v___x_1560_, v___x_1564_);
if (v___x_1565_ == 0)
{
lean_dec(v_a_1563_);
v___y_1510_ = v___y_1557_;
v___y_1511_ = v___y_1558_;
v___y_1512_ = v___y_1559_;
v___y_1513_ = v_a_1258_;
goto v___jp_1509_;
}
else
{
lean_object* v___x_1566_; size_t v___x_1567_; size_t v___x_1568_; lean_object* v___x_1569_; 
v___x_1566_ = lean_box(0);
v___x_1567_ = ((size_t)0ULL);
v___x_1568_ = lean_usize_of_nat(v___x_1564_);
v___x_1569_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1563_, v___x_1567_, v___x_1568_, v___x_1566_, v_a_1258_);
lean_dec(v_a_1563_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_dec_ref_known(v___x_1569_, 1);
v___y_1510_ = v___y_1557_;
v___y_1511_ = v___y_1558_;
v___y_1512_ = v___y_1559_;
v___y_1513_ = v_a_1258_;
goto v___jp_1509_;
}
else
{
v___y_1552_ = v___y_1557_;
v___y_1553_ = v___y_1558_;
v___y_1554_ = v___y_1559_;
v___y_1555_ = v___x_1569_;
goto v___jp_1551_;
}
}
}
else
{
lean_object* v_a_1570_; lean_object* v___x_1571_; uint8_t v___x_1572_; 
v_a_1570_ = lean_ctor_get(v___x_1562_, 1);
lean_inc(v_a_1570_);
lean_dec_ref_known(v___x_1562_, 2);
v___x_1571_ = lean_array_get_size(v_a_1570_);
v___x_1572_ = lean_nat_dec_lt(v___x_1560_, v___x_1571_);
if (v___x_1572_ == 0)
{
lean_object* v___x_1573_; lean_object* v___x_1574_; 
lean_dec(v_a_1570_);
lean_dec_ref(v___y_1559_);
lean_dec_ref(v___y_1557_);
lean_dec_ref(v_repo_1260_);
lean_dec_ref(v_name_1259_);
v___x_1573_ = lean_box(0);
v___x_1574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1573_);
return v___x_1574_;
}
else
{
lean_object* v___x_1575_; size_t v___x_1576_; size_t v___x_1577_; lean_object* v___x_1578_; 
v___x_1575_ = lean_box(0);
v___x_1576_ = ((size_t)0ULL);
v___x_1577_ = lean_usize_of_nat(v___x_1571_);
v___x_1578_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1570_, v___x_1576_, v___x_1577_, v___x_1575_, v_a_1258_);
lean_dec(v_a_1570_);
if (lean_obj_tag(v___x_1578_) == 0)
{
lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1585_; 
lean_dec_ref(v___y_1559_);
lean_dec_ref(v___y_1557_);
lean_dec_ref(v_repo_1260_);
lean_dec_ref(v_name_1259_);
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1578_);
if (v_isSharedCheck_1585_ == 0)
{
lean_object* v_unused_1586_; 
v_unused_1586_ = lean_ctor_get(v___x_1578_, 0);
lean_dec(v_unused_1586_);
v___x_1580_ = v___x_1578_;
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
else
{
lean_dec(v___x_1578_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v___x_1583_; 
if (v_isShared_1581_ == 0)
{
lean_ctor_set_tag(v___x_1580_, 1);
lean_ctor_set(v___x_1580_, 0, v___x_1575_);
v___x_1583_ = v___x_1580_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v___x_1575_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
}
else
{
v___y_1552_ = v___y_1557_;
v___y_1553_ = v___y_1558_;
v___y_1554_ = v___y_1559_;
v___y_1555_ = v___x_1578_;
goto v___jp_1551_;
}
}
}
}
v___jp_1587_:
{
if (lean_obj_tag(v___y_1591_) == 0)
{
lean_dec_ref_known(v___y_1591_, 1);
v___y_1557_ = v___y_1588_;
v___y_1558_ = v___y_1589_;
v___y_1559_ = v___y_1590_;
goto v___jp_1556_;
}
else
{
lean_dec_ref(v___y_1590_);
lean_dec_ref(v___y_1588_);
lean_dec_ref(v_repo_1260_);
lean_dec_ref(v_name_1259_);
return v___y_1591_;
}
}
v___jp_1592_:
{
if (v_a_1594_ == 0)
{
lean_dec_ref(v_repo_1260_);
lean_dec_ref(v_name_1259_);
goto v___jp_1267_;
}
else
{
lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; uint8_t v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; 
v___x_1595_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff___closed__0));
v___x_1596_ = lean_string_append(v_name_1259_, v___x_1595_);
v___x_1597_ = lean_string_append(v___x_1596_, v_repo_1260_);
lean_dec_ref(v_repo_1260_);
v___x_1598_ = 2;
v___x_1599_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1599_, 0, v___x_1597_);
lean_ctor_set_uint8(v___x_1599_, sizeof(void*)*1, v___x_1598_);
lean_inc_ref(v___y_1593_);
v___x_1600_ = lean_apply_2(v___y_1593_, v___x_1599_, lean_box(0));
goto v___jp_1267_;
}
}
v___jp_1601_:
{
if (v_a_1603_ == 0)
{
lean_dec_ref(v_repo_1260_);
lean_dec_ref(v_name_1259_);
goto v___jp_1270_;
}
else
{
lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; uint8_t v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; 
v___x_1604_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff___closed__0));
v___x_1605_ = lean_string_append(v_name_1259_, v___x_1604_);
v___x_1606_ = lean_string_append(v___x_1605_, v_repo_1260_);
lean_dec_ref(v_repo_1260_);
v___x_1607_ = 2;
v___x_1608_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1608_, 0, v___x_1606_);
lean_ctor_set_uint8(v___x_1608_, sizeof(void*)*1, v___x_1607_);
lean_inc_ref(v___y_1602_);
v___x_1609_ = lean_apply_2(v___y_1602_, v___x_1608_, lean_box(0));
goto v___jp_1270_;
}
}
v___jp_1610_:
{
lean_object* v___x_1615_; uint8_t v___x_1616_; 
v___x_1615_ = lean_array_get_size(v___y_1612_);
v___x_1616_ = lean_nat_dec_lt(v___y_1611_, v___x_1615_);
if (v___x_1616_ == 0)
{
v___y_1593_ = v___y_1613_;
v_a_1594_ = v_val_1614_;
goto v___jp_1592_;
}
else
{
lean_object* v___x_1617_; size_t v___x_1618_; size_t v___x_1619_; lean_object* v___x_1620_; 
v___x_1617_ = lean_box(0);
v___x_1618_ = ((size_t)0ULL);
v___x_1619_ = lean_usize_of_nat(v___x_1615_);
v___x_1620_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_1612_, v___x_1618_, v___x_1619_, v___x_1617_, v___y_1613_);
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_dec_ref_known(v___x_1620_, 1);
v___y_1593_ = v___y_1613_;
v_a_1594_ = v_val_1614_;
goto v___jp_1592_;
}
else
{
lean_dec_ref(v_repo_1260_);
lean_dec_ref(v_name_1259_);
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_dec_ref_known(v___x_1620_, 1);
goto v___jp_1267_;
}
else
{
return v___x_1620_;
}
}
}
}
v___jp_1621_:
{
uint8_t v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; 
lean_inc_ref(v_repo_1260_);
v___x_1625_ = l_Lake_GitRepo_hasNoDiff(v_repo_1260_);
v___x_1626_ = lean_unsigned_to_nat(0u);
v___x_1627_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
if (v___x_1625_ == 0)
{
v___y_1611_ = v___x_1626_;
v___y_1612_ = v___x_1627_;
v___y_1613_ = v___y_1624_;
v_val_1614_ = v___y_1622_;
goto v___jp_1610_;
}
else
{
v___y_1611_ = v___x_1626_;
v___y_1612_ = v___x_1627_;
v___y_1613_ = v___y_1624_;
v_val_1614_ = v___y_1623_;
goto v___jp_1610_;
}
}
v___jp_1628_:
{
if (lean_obj_tag(v___y_1632_) == 0)
{
lean_dec_ref_known(v___y_1632_, 1);
v___y_1622_ = v___y_1629_;
v___y_1623_ = v___y_1630_;
v___y_1624_ = v___y_1631_;
goto v___jp_1621_;
}
else
{
lean_dec_ref(v_repo_1260_);
lean_dec_ref(v_name_1259_);
return v___y_1632_;
}
}
v___jp_1633_:
{
lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; 
v___x_1637_ = lean_unsigned_to_nat(0u);
v___x_1638_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1260_);
v___x_1639_ = l_Lake_GitRepo_clean(v_repo_1260_, v___x_1638_);
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_object* v_a_1640_; lean_object* v___x_1641_; uint8_t v___x_1642_; 
v_a_1640_ = lean_ctor_get(v___x_1639_, 1);
lean_inc(v_a_1640_);
lean_dec_ref_known(v___x_1639_, 2);
v___x_1641_ = lean_array_get_size(v_a_1640_);
v___x_1642_ = lean_nat_dec_lt(v___x_1637_, v___x_1641_);
if (v___x_1642_ == 0)
{
lean_dec(v_a_1640_);
v___y_1622_ = v___y_1634_;
v___y_1623_ = v___y_1635_;
v___y_1624_ = v___y_1636_;
goto v___jp_1621_;
}
else
{
lean_object* v___x_1643_; size_t v___x_1644_; size_t v___x_1645_; lean_object* v___x_1646_; 
v___x_1643_ = lean_box(0);
v___x_1644_ = ((size_t)0ULL);
v___x_1645_ = lean_usize_of_nat(v___x_1641_);
v___x_1646_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1640_, v___x_1644_, v___x_1645_, v___x_1643_, v___y_1636_);
lean_dec(v_a_1640_);
if (lean_obj_tag(v___x_1646_) == 0)
{
lean_dec_ref_known(v___x_1646_, 1);
v___y_1622_ = v___y_1634_;
v___y_1623_ = v___y_1635_;
v___y_1624_ = v___y_1636_;
goto v___jp_1621_;
}
else
{
v___y_1629_ = v___y_1634_;
v___y_1630_ = v___y_1635_;
v___y_1631_ = v___y_1636_;
v___y_1632_ = v___x_1646_;
goto v___jp_1628_;
}
}
}
else
{
lean_object* v_a_1647_; lean_object* v___x_1648_; uint8_t v___x_1649_; 
v_a_1647_ = lean_ctor_get(v___x_1639_, 1);
lean_inc(v_a_1647_);
lean_dec_ref_known(v___x_1639_, 2);
v___x_1648_ = lean_array_get_size(v_a_1647_);
v___x_1649_ = lean_nat_dec_lt(v___x_1637_, v___x_1648_);
if (v___x_1649_ == 0)
{
lean_object* v___x_1650_; lean_object* v___x_1651_; 
lean_dec(v_a_1647_);
lean_dec_ref(v_repo_1260_);
lean_dec_ref(v_name_1259_);
v___x_1650_ = lean_box(0);
v___x_1651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1650_);
return v___x_1651_;
}
else
{
lean_object* v___x_1652_; size_t v___x_1653_; size_t v___x_1654_; lean_object* v___x_1655_; 
v___x_1652_ = lean_box(0);
v___x_1653_ = ((size_t)0ULL);
v___x_1654_ = lean_usize_of_nat(v___x_1648_);
v___x_1655_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1647_, v___x_1653_, v___x_1654_, v___x_1652_, v___y_1636_);
lean_dec(v_a_1647_);
if (lean_obj_tag(v___x_1655_) == 0)
{
lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1662_; 
lean_dec_ref(v_repo_1260_);
lean_dec_ref(v_name_1259_);
v_isSharedCheck_1662_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1662_ == 0)
{
lean_object* v_unused_1663_; 
v_unused_1663_ = lean_ctor_get(v___x_1655_, 0);
lean_dec(v_unused_1663_);
v___x_1657_ = v___x_1655_;
v_isShared_1658_ = v_isSharedCheck_1662_;
goto v_resetjp_1656_;
}
else
{
lean_dec(v___x_1655_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1662_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v___x_1660_; 
if (v_isShared_1658_ == 0)
{
lean_ctor_set_tag(v___x_1657_, 1);
lean_ctor_set(v___x_1657_, 0, v___x_1652_);
v___x_1660_ = v___x_1657_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v___x_1652_);
v___x_1660_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
return v___x_1660_;
}
}
}
else
{
v___y_1629_ = v___y_1634_;
v___y_1630_ = v___y_1635_;
v___y_1631_ = v___y_1636_;
v___y_1632_ = v___x_1655_;
goto v___jp_1628_;
}
}
}
}
v___jp_1664_:
{
if (lean_obj_tag(v___y_1668_) == 0)
{
lean_dec_ref_known(v___y_1668_, 1);
v___y_1634_ = v___y_1665_;
v___y_1635_ = v___y_1666_;
v___y_1636_ = v___y_1667_;
goto v___jp_1633_;
}
else
{
lean_dec_ref(v_repo_1260_);
lean_dec_ref(v_name_1259_);
return v___y_1668_;
}
}
v___jp_1669_:
{
if (lean_obj_tag(v_a_1676_) == 0)
{
v___y_1510_ = v___y_1670_;
v___y_1511_ = v___y_1672_;
v___y_1512_ = v___y_1674_;
v___y_1513_ = v___y_1675_;
goto v___jp_1509_;
}
else
{
lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1717_; 
v_isSharedCheck_1717_ = !lean_is_exclusive(v_a_1676_);
if (v_isSharedCheck_1717_ == 0)
{
lean_object* v_unused_1718_; 
v_unused_1718_ = lean_ctor_get(v_a_1676_, 0);
lean_dec(v_unused_1718_);
v___x_1678_ = v_a_1676_;
v_isShared_1679_ = v_isSharedCheck_1717_;
goto v_resetjp_1677_;
}
else
{
lean_dec(v_a_1676_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1717_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
if (v___y_1671_ == 0)
{
lean_del_object(v___x_1678_);
v___y_1510_ = v___y_1670_;
v___y_1511_ = v___y_1672_;
v___y_1512_ = v___y_1674_;
v___y_1513_ = v___y_1675_;
goto v___jp_1509_;
}
else
{
lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; uint8_t v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; 
lean_dec_ref(v___y_1670_);
v___x_1680_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__0));
lean_inc_ref(v_name_1259_);
v___x_1681_ = lean_string_append(v_name_1259_, v___x_1680_);
v___x_1682_ = lean_string_append(v___x_1681_, v___y_1674_);
v___x_1683_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__1));
v___x_1684_ = lean_string_append(v___x_1682_, v___x_1683_);
v___x_1685_ = 1;
v___x_1686_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1686_, 0, v___x_1684_);
lean_ctor_set_uint8(v___x_1686_, sizeof(void*)*1, v___x_1685_);
lean_inc_ref(v___y_1675_);
v___x_1687_ = lean_apply_2(v___y_1675_, v___x_1686_, lean_box(0));
v___x_1688_ = lean_unsigned_to_nat(0u);
v___x_1689_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1260_);
v___x_1690_ = l_Lake_GitRepo_checkoutDetach(v___y_1674_, v_repo_1260_, v___x_1689_);
if (lean_obj_tag(v___x_1690_) == 0)
{
lean_object* v_a_1691_; lean_object* v___x_1692_; uint8_t v___x_1693_; 
lean_del_object(v___x_1678_);
v_a_1691_ = lean_ctor_get(v___x_1690_, 1);
lean_inc(v_a_1691_);
lean_dec_ref_known(v___x_1690_, 2);
v___x_1692_ = lean_array_get_size(v_a_1691_);
v___x_1693_ = lean_nat_dec_lt(v___x_1688_, v___x_1692_);
if (v___x_1693_ == 0)
{
lean_dec(v_a_1691_);
v___y_1634_ = v___y_1671_;
v___y_1635_ = v___y_1673_;
v___y_1636_ = v___y_1675_;
goto v___jp_1633_;
}
else
{
lean_object* v___x_1694_; size_t v___x_1695_; size_t v___x_1696_; lean_object* v___x_1697_; 
v___x_1694_ = lean_box(0);
v___x_1695_ = ((size_t)0ULL);
v___x_1696_ = lean_usize_of_nat(v___x_1692_);
v___x_1697_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1691_, v___x_1695_, v___x_1696_, v___x_1694_, v___y_1675_);
lean_dec(v_a_1691_);
if (lean_obj_tag(v___x_1697_) == 0)
{
lean_dec_ref_known(v___x_1697_, 1);
v___y_1634_ = v___y_1671_;
v___y_1635_ = v___y_1673_;
v___y_1636_ = v___y_1675_;
goto v___jp_1633_;
}
else
{
v___y_1665_ = v___y_1671_;
v___y_1666_ = v___y_1673_;
v___y_1667_ = v___y_1675_;
v___y_1668_ = v___x_1697_;
goto v___jp_1664_;
}
}
}
else
{
lean_object* v_a_1698_; lean_object* v___x_1699_; uint8_t v___x_1700_; 
v_a_1698_ = lean_ctor_get(v___x_1690_, 1);
lean_inc(v_a_1698_);
lean_dec_ref_known(v___x_1690_, 2);
v___x_1699_ = lean_array_get_size(v_a_1698_);
v___x_1700_ = lean_nat_dec_lt(v___x_1688_, v___x_1699_);
if (v___x_1700_ == 0)
{
lean_object* v___x_1701_; lean_object* v___x_1703_; 
lean_dec(v_a_1698_);
lean_dec_ref(v_repo_1260_);
lean_dec_ref(v_name_1259_);
v___x_1701_ = lean_box(0);
if (v_isShared_1679_ == 0)
{
lean_ctor_set(v___x_1678_, 0, v___x_1701_);
v___x_1703_ = v___x_1678_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v___x_1701_);
v___x_1703_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
return v___x_1703_;
}
}
else
{
lean_object* v___x_1705_; size_t v___x_1706_; size_t v___x_1707_; lean_object* v___x_1708_; 
lean_del_object(v___x_1678_);
v___x_1705_ = lean_box(0);
v___x_1706_ = ((size_t)0ULL);
v___x_1707_ = lean_usize_of_nat(v___x_1699_);
v___x_1708_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1698_, v___x_1706_, v___x_1707_, v___x_1705_, v___y_1675_);
lean_dec(v_a_1698_);
if (lean_obj_tag(v___x_1708_) == 0)
{
lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1715_; 
lean_dec_ref(v_repo_1260_);
lean_dec_ref(v_name_1259_);
v_isSharedCheck_1715_ = !lean_is_exclusive(v___x_1708_);
if (v_isSharedCheck_1715_ == 0)
{
lean_object* v_unused_1716_; 
v_unused_1716_ = lean_ctor_get(v___x_1708_, 0);
lean_dec(v_unused_1716_);
v___x_1710_ = v___x_1708_;
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
else
{
lean_dec(v___x_1708_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___x_1713_; 
if (v_isShared_1711_ == 0)
{
lean_ctor_set_tag(v___x_1710_, 1);
lean_ctor_set(v___x_1710_, 0, v___x_1705_);
v___x_1713_ = v___x_1710_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v___x_1705_);
v___x_1713_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
return v___x_1713_;
}
}
}
else
{
v___y_1665_ = v___y_1671_;
v___y_1666_ = v___y_1673_;
v___y_1667_ = v___y_1675_;
v___y_1668_ = v___x_1708_;
goto v___jp_1664_;
}
}
}
}
}
}
}
v___jp_1719_:
{
lean_object* v___x_1724_; uint8_t v___x_1725_; 
v___x_1724_ = lean_array_get_size(v___y_1720_);
v___x_1725_ = lean_nat_dec_lt(v___y_1721_, v___x_1724_);
if (v___x_1725_ == 0)
{
v___y_1602_ = v___y_1722_;
v_a_1603_ = v_val_1723_;
goto v___jp_1601_;
}
else
{
lean_object* v___x_1726_; size_t v___x_1727_; size_t v___x_1728_; lean_object* v___x_1729_; 
v___x_1726_ = lean_box(0);
v___x_1727_ = ((size_t)0ULL);
v___x_1728_ = lean_usize_of_nat(v___x_1724_);
v___x_1729_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_1720_, v___x_1727_, v___x_1728_, v___x_1726_, v___y_1722_);
if (lean_obj_tag(v___x_1729_) == 0)
{
lean_dec_ref_known(v___x_1729_, 1);
v___y_1602_ = v___y_1722_;
v_a_1603_ = v_val_1723_;
goto v___jp_1601_;
}
else
{
lean_dec_ref(v_repo_1260_);
lean_dec_ref(v_name_1259_);
if (lean_obj_tag(v___x_1729_) == 0)
{
lean_dec_ref_known(v___x_1729_, 1);
goto v___jp_1270_;
}
else
{
return v___x_1729_;
}
}
}
}
v___jp_1730_:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; uint8_t v___x_1738_; 
v___x_1736_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
lean_inc_ref(v___y_1734_);
v___x_1737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1737_, 0, v___y_1734_);
v___x_1738_ = l_Option_instDecidableEq___redArg(v___x_1736_, v_a_1735_, v___x_1737_);
if (v___x_1738_ == 0)
{
uint8_t v___x_1739_; 
v___x_1739_ = l_Lake_GitRev_isFullSha1(v___y_1734_);
if (v___x_1739_ == 0)
{
v___y_1510_ = v___y_1731_;
v___y_1511_ = v___y_1732_;
v___y_1512_ = v___y_1734_;
v___y_1513_ = v___y_1733_;
goto v___jp_1509_;
}
else
{
lean_object* v___x_1740_; lean_object* v___x_1741_; uint8_t v___x_1742_; 
lean_inc_ref(v_repo_1260_);
lean_inc_ref(v___y_1734_);
v___x_1740_ = l_Lake_GitRepo_findCommit_x3f(v___y_1734_, v_repo_1260_);
v___x_1741_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_1742_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_1742_ == 0)
{
v___y_1670_ = v___y_1731_;
v___y_1671_ = v___x_1739_;
v___y_1672_ = v___y_1732_;
v___y_1673_ = v___x_1738_;
v___y_1674_ = v___y_1734_;
v___y_1675_ = v___y_1733_;
v_a_1676_ = v___x_1740_;
goto v___jp_1669_;
}
else
{
lean_object* v___x_1743_; size_t v___x_1744_; size_t v___x_1745_; lean_object* v___x_1746_; 
v___x_1743_ = lean_box(0);
v___x_1744_ = ((size_t)0ULL);
v___x_1745_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_1746_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_1741_, v___x_1744_, v___x_1745_, v___x_1743_, v___y_1733_);
if (lean_obj_tag(v___x_1746_) == 0)
{
lean_dec_ref_known(v___x_1746_, 1);
v___y_1670_ = v___y_1731_;
v___y_1671_ = v___x_1739_;
v___y_1672_ = v___y_1732_;
v___y_1673_ = v___x_1738_;
v___y_1674_ = v___y_1734_;
v___y_1675_ = v___y_1733_;
v_a_1676_ = v___x_1740_;
goto v___jp_1669_;
}
else
{
lean_dec(v___x_1740_);
lean_dec_ref(v___y_1734_);
lean_dec_ref(v___y_1731_);
lean_dec_ref(v_repo_1260_);
lean_dec_ref(v_name_1259_);
return v___x_1746_;
}
}
}
}
else
{
uint8_t v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; 
lean_dec_ref(v___y_1734_);
lean_dec_ref(v___y_1731_);
lean_inc_ref(v_repo_1260_);
v___x_1747_ = l_Lake_GitRepo_hasNoDiff(v_repo_1260_);
v___x_1748_ = lean_unsigned_to_nat(0u);
v___x_1749_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
if (v___x_1747_ == 0)
{
v___y_1720_ = v___x_1749_;
v___y_1721_ = v___x_1748_;
v___y_1722_ = v___y_1733_;
v_val_1723_ = v___x_1738_;
goto v___jp_1719_;
}
else
{
uint8_t v___x_1750_; 
v___x_1750_ = 0;
v___y_1720_ = v___x_1749_;
v___y_1721_ = v___x_1748_;
v___y_1722_ = v___y_1733_;
v_val_1723_ = v___x_1750_;
goto v___jp_1719_;
}
}
}
v___jp_1751_:
{
lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; uint8_t v___x_1759_; 
v___x_1756_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__0));
lean_inc_ref(v_repo_1260_);
v___x_1757_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_1756_, v_repo_1260_);
v___x_1758_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_1759_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_1759_ == 0)
{
v___y_1731_ = v___y_1752_;
v___y_1732_ = v___y_1753_;
v___y_1733_ = v___y_1755_;
v___y_1734_ = v___y_1754_;
v_a_1735_ = v___x_1757_;
goto v___jp_1730_;
}
else
{
lean_object* v___x_1760_; size_t v___x_1761_; size_t v___x_1762_; lean_object* v___x_1763_; 
v___x_1760_ = lean_box(0);
v___x_1761_ = ((size_t)0ULL);
v___x_1762_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_1763_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_1758_, v___x_1761_, v___x_1762_, v___x_1760_, v___y_1755_);
if (lean_obj_tag(v___x_1763_) == 0)
{
lean_dec_ref_known(v___x_1763_, 1);
v___y_1731_ = v___y_1752_;
v___y_1732_ = v___y_1753_;
v___y_1733_ = v___y_1755_;
v___y_1734_ = v___y_1754_;
v_a_1735_ = v___x_1757_;
goto v___jp_1730_;
}
else
{
lean_dec(v___x_1757_);
lean_dec_ref(v___y_1754_);
lean_dec_ref(v___y_1752_);
lean_dec_ref(v_repo_1260_);
lean_dec_ref(v_name_1259_);
return v___x_1763_;
}
}
}
v___jp_1764_:
{
if (lean_obj_tag(v___y_1768_) == 0)
{
lean_dec_ref_known(v___y_1768_, 1);
v___y_1752_ = v___y_1765_;
v___y_1753_ = v___y_1766_;
v___y_1754_ = v___y_1767_;
v___y_1755_ = v_a_1258_;
goto v___jp_1751_;
}
else
{
lean_dec_ref(v___y_1767_);
lean_dec_ref(v___y_1765_);
lean_dec_ref(v_repo_1260_);
lean_dec_ref(v_name_1259_);
return v___y_1768_;
}
}
v___jp_1769_:
{
if (lean_obj_tag(v___y_1773_) == 0)
{
lean_dec_ref_known(v___y_1773_, 1);
v___y_1752_ = v___y_1770_;
v___y_1753_ = v___y_1771_;
v___y_1754_ = v___y_1772_;
v___y_1755_ = v_a_1258_;
goto v___jp_1751_;
}
else
{
lean_dec_ref(v___y_1772_);
lean_dec_ref(v___y_1770_);
lean_dec_ref(v_repo_1260_);
lean_dec_ref(v_name_1259_);
return v___y_1773_;
}
}
v___jp_1774_:
{
if (lean_obj_tag(v_a_1778_) == 1)
{
lean_object* v_val_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1822_; 
v_val_1779_ = lean_ctor_get(v_a_1778_, 0);
v_isSharedCheck_1822_ = !lean_is_exclusive(v_a_1778_);
if (v_isSharedCheck_1822_ == 0)
{
v___x_1781_ = v_a_1778_;
v_isShared_1782_ = v_isSharedCheck_1822_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_val_1779_);
lean_dec(v_a_1778_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1822_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
uint8_t v___x_1783_; 
v___x_1783_ = lean_string_dec_eq(v_val_1779_, v___y_1775_);
if (v___x_1783_ == 0)
{
lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; uint8_t v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; 
v___x_1784_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__5));
lean_inc_ref(v_name_1259_);
v___x_1785_ = lean_string_append(v_name_1259_, v___x_1784_);
v___x_1786_ = lean_string_append(v___x_1785_, v_val_1779_);
lean_dec(v_val_1779_);
v___x_1787_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__6));
v___x_1788_ = lean_string_append(v___x_1786_, v___x_1787_);
v___x_1789_ = lean_string_append(v___x_1788_, v___y_1775_);
v___x_1790_ = 1;
v___x_1791_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1791_, 0, v___x_1789_);
lean_ctor_set_uint8(v___x_1791_, sizeof(void*)*1, v___x_1790_);
lean_inc_ref(v_a_1258_);
v___x_1792_ = lean_apply_2(v_a_1258_, v___x_1791_, lean_box(0));
v___x_1793_ = lean_unsigned_to_nat(0u);
v___x_1794_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1260_);
lean_inc_ref(v___y_1775_);
lean_inc_ref(v___y_1776_);
v___x_1795_ = l_Lake_GitRepo_setRemoteUrl(v___y_1776_, v___y_1775_, v_repo_1260_, v___x_1794_);
if (lean_obj_tag(v___x_1795_) == 0)
{
lean_object* v_a_1796_; lean_object* v___x_1797_; uint8_t v___x_1798_; 
lean_del_object(v___x_1781_);
v_a_1796_ = lean_ctor_get(v___x_1795_, 1);
lean_inc(v_a_1796_);
lean_dec_ref_known(v___x_1795_, 2);
v___x_1797_ = lean_array_get_size(v_a_1796_);
v___x_1798_ = lean_nat_dec_lt(v___x_1793_, v___x_1797_);
if (v___x_1798_ == 0)
{
lean_dec(v_a_1796_);
v___y_1752_ = v___y_1775_;
v___y_1753_ = v___y_1776_;
v___y_1754_ = v___y_1777_;
v___y_1755_ = v_a_1258_;
goto v___jp_1751_;
}
else
{
lean_object* v___x_1799_; size_t v___x_1800_; size_t v___x_1801_; lean_object* v___x_1802_; 
v___x_1799_ = lean_box(0);
v___x_1800_ = ((size_t)0ULL);
v___x_1801_ = lean_usize_of_nat(v___x_1797_);
v___x_1802_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1796_, v___x_1800_, v___x_1801_, v___x_1799_, v_a_1258_);
lean_dec(v_a_1796_);
if (lean_obj_tag(v___x_1802_) == 0)
{
lean_dec_ref_known(v___x_1802_, 1);
v___y_1752_ = v___y_1775_;
v___y_1753_ = v___y_1776_;
v___y_1754_ = v___y_1777_;
v___y_1755_ = v_a_1258_;
goto v___jp_1751_;
}
else
{
v___y_1770_ = v___y_1775_;
v___y_1771_ = v___y_1776_;
v___y_1772_ = v___y_1777_;
v___y_1773_ = v___x_1802_;
goto v___jp_1769_;
}
}
}
else
{
lean_object* v_a_1803_; lean_object* v___x_1804_; uint8_t v___x_1805_; 
v_a_1803_ = lean_ctor_get(v___x_1795_, 1);
lean_inc(v_a_1803_);
lean_dec_ref_known(v___x_1795_, 2);
v___x_1804_ = lean_array_get_size(v_a_1803_);
v___x_1805_ = lean_nat_dec_lt(v___x_1793_, v___x_1804_);
if (v___x_1805_ == 0)
{
lean_object* v___x_1806_; lean_object* v___x_1808_; 
lean_dec(v_a_1803_);
lean_dec_ref(v___y_1777_);
lean_dec_ref(v___y_1775_);
lean_dec_ref(v_repo_1260_);
lean_dec_ref(v_name_1259_);
v___x_1806_ = lean_box(0);
if (v_isShared_1782_ == 0)
{
lean_ctor_set(v___x_1781_, 0, v___x_1806_);
v___x_1808_ = v___x_1781_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v___x_1806_);
v___x_1808_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
return v___x_1808_;
}
}
else
{
lean_object* v___x_1810_; size_t v___x_1811_; size_t v___x_1812_; lean_object* v___x_1813_; 
lean_del_object(v___x_1781_);
v___x_1810_ = lean_box(0);
v___x_1811_ = ((size_t)0ULL);
v___x_1812_ = lean_usize_of_nat(v___x_1804_);
v___x_1813_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1803_, v___x_1811_, v___x_1812_, v___x_1810_, v_a_1258_);
lean_dec(v_a_1803_);
if (lean_obj_tag(v___x_1813_) == 0)
{
lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1820_; 
lean_dec_ref(v___y_1777_);
lean_dec_ref(v___y_1775_);
lean_dec_ref(v_repo_1260_);
lean_dec_ref(v_name_1259_);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1820_ == 0)
{
lean_object* v_unused_1821_; 
v_unused_1821_ = lean_ctor_get(v___x_1813_, 0);
lean_dec(v_unused_1821_);
v___x_1815_ = v___x_1813_;
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
else
{
lean_dec(v___x_1813_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1818_; 
if (v_isShared_1816_ == 0)
{
lean_ctor_set_tag(v___x_1815_, 1);
lean_ctor_set(v___x_1815_, 0, v___x_1810_);
v___x_1818_ = v___x_1815_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v___x_1810_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
return v___x_1818_;
}
}
}
else
{
v___y_1770_ = v___y_1775_;
v___y_1771_ = v___y_1776_;
v___y_1772_ = v___y_1777_;
v___y_1773_ = v___x_1813_;
goto v___jp_1769_;
}
}
}
}
else
{
lean_del_object(v___x_1781_);
lean_dec(v_val_1779_);
v___y_1752_ = v___y_1775_;
v___y_1753_ = v___y_1776_;
v___y_1754_ = v___y_1777_;
v___y_1755_ = v_a_1258_;
goto v___jp_1751_;
}
}
}
else
{
lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; 
lean_dec(v_a_1778_);
v___x_1823_ = lean_unsigned_to_nat(0u);
v___x_1824_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1260_);
lean_inc_ref(v___y_1775_);
lean_inc_ref(v___y_1776_);
v___x_1825_ = l_Lake_GitRepo_addRemote(v___y_1776_, v___y_1775_, v_repo_1260_, v___x_1824_);
if (lean_obj_tag(v___x_1825_) == 0)
{
lean_object* v_a_1826_; lean_object* v___x_1827_; uint8_t v___x_1828_; 
v_a_1826_ = lean_ctor_get(v___x_1825_, 1);
lean_inc(v_a_1826_);
lean_dec_ref_known(v___x_1825_, 2);
v___x_1827_ = lean_array_get_size(v_a_1826_);
v___x_1828_ = lean_nat_dec_lt(v___x_1823_, v___x_1827_);
if (v___x_1828_ == 0)
{
lean_dec(v_a_1826_);
v___y_1752_ = v___y_1775_;
v___y_1753_ = v___y_1776_;
v___y_1754_ = v___y_1777_;
v___y_1755_ = v_a_1258_;
goto v___jp_1751_;
}
else
{
lean_object* v___x_1829_; size_t v___x_1830_; size_t v___x_1831_; lean_object* v___x_1832_; 
v___x_1829_ = lean_box(0);
v___x_1830_ = ((size_t)0ULL);
v___x_1831_ = lean_usize_of_nat(v___x_1827_);
v___x_1832_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1826_, v___x_1830_, v___x_1831_, v___x_1829_, v_a_1258_);
lean_dec(v_a_1826_);
if (lean_obj_tag(v___x_1832_) == 0)
{
lean_dec_ref_known(v___x_1832_, 1);
v___y_1752_ = v___y_1775_;
v___y_1753_ = v___y_1776_;
v___y_1754_ = v___y_1777_;
v___y_1755_ = v_a_1258_;
goto v___jp_1751_;
}
else
{
v___y_1765_ = v___y_1775_;
v___y_1766_ = v___y_1776_;
v___y_1767_ = v___y_1777_;
v___y_1768_ = v___x_1832_;
goto v___jp_1764_;
}
}
}
else
{
lean_object* v_a_1833_; lean_object* v___x_1834_; uint8_t v___x_1835_; 
v_a_1833_ = lean_ctor_get(v___x_1825_, 1);
lean_inc(v_a_1833_);
lean_dec_ref_known(v___x_1825_, 2);
v___x_1834_ = lean_array_get_size(v_a_1833_);
v___x_1835_ = lean_nat_dec_lt(v___x_1823_, v___x_1834_);
if (v___x_1835_ == 0)
{
lean_object* v___x_1836_; lean_object* v___x_1837_; 
lean_dec(v_a_1833_);
lean_dec_ref(v___y_1777_);
lean_dec_ref(v___y_1775_);
lean_dec_ref(v_repo_1260_);
lean_dec_ref(v_name_1259_);
v___x_1836_ = lean_box(0);
v___x_1837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1837_, 0, v___x_1836_);
return v___x_1837_;
}
else
{
lean_object* v___x_1838_; size_t v___x_1839_; size_t v___x_1840_; lean_object* v___x_1841_; 
v___x_1838_ = lean_box(0);
v___x_1839_ = ((size_t)0ULL);
v___x_1840_ = lean_usize_of_nat(v___x_1834_);
v___x_1841_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1833_, v___x_1839_, v___x_1840_, v___x_1838_, v_a_1258_);
lean_dec(v_a_1833_);
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1848_; 
lean_dec_ref(v___y_1777_);
lean_dec_ref(v___y_1775_);
lean_dec_ref(v_repo_1260_);
lean_dec_ref(v_name_1259_);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1848_ == 0)
{
lean_object* v_unused_1849_; 
v_unused_1849_ = lean_ctor_get(v___x_1841_, 0);
lean_dec(v_unused_1849_);
v___x_1843_ = v___x_1841_;
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
else
{
lean_dec(v___x_1841_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1846_; 
if (v_isShared_1844_ == 0)
{
lean_ctor_set_tag(v___x_1843_, 1);
lean_ctor_set(v___x_1843_, 0, v___x_1838_);
v___x_1846_ = v___x_1843_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v___x_1838_);
v___x_1846_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
return v___x_1846_;
}
}
}
else
{
v___y_1765_ = v___y_1775_;
v___y_1766_ = v___y_1776_;
v___y_1767_ = v___y_1777_;
v___y_1768_ = v___x_1841_;
goto v___jp_1764_;
}
}
}
}
}
v___jp_1850_:
{
if (v_a_1854_ == 0)
{
lean_object* v___x_1855_; lean_object* v___x_1856_; uint8_t v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; 
v___x_1855_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__7));
lean_inc_ref(v_name_1259_);
v___x_1856_ = lean_string_append(v_name_1259_, v___x_1855_);
v___x_1857_ = 1;
v___x_1858_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1858_, 0, v___x_1856_);
lean_ctor_set_uint8(v___x_1858_, sizeof(void*)*1, v___x_1857_);
lean_inc_ref(v_a_1258_);
v___x_1859_ = lean_apply_2(v_a_1258_, v___x_1858_, lean_box(0));
lean_inc_ref(v_repo_1260_);
v___x_1860_ = l_IO_FS_createDirAll(v_repo_1260_);
if (lean_obj_tag(v___x_1860_) == 0)
{
lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1893_; 
v_isSharedCheck_1893_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1893_ == 0)
{
lean_object* v_unused_1894_; 
v_unused_1894_ = lean_ctor_get(v___x_1860_, 0);
lean_dec(v_unused_1894_);
v___x_1862_ = v___x_1860_;
v_isShared_1863_ = v_isSharedCheck_1893_;
goto v_resetjp_1861_;
}
else
{
lean_dec(v___x_1860_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1893_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; 
v___x_1864_ = lean_unsigned_to_nat(0u);
v___x_1865_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1260_);
v___x_1866_ = l_Lake_GitRepo_quietInit(v_repo_1260_, v___x_1865_);
if (lean_obj_tag(v___x_1866_) == 0)
{
lean_object* v_a_1867_; lean_object* v___x_1868_; uint8_t v___x_1869_; 
lean_del_object(v___x_1862_);
v_a_1867_ = lean_ctor_get(v___x_1866_, 1);
lean_inc(v_a_1867_);
lean_dec_ref_known(v___x_1866_, 2);
v___x_1868_ = lean_array_get_size(v_a_1867_);
v___x_1869_ = lean_nat_dec_lt(v___x_1864_, v___x_1868_);
if (v___x_1869_ == 0)
{
lean_dec(v_a_1867_);
v___y_1557_ = v___y_1851_;
v___y_1558_ = v___y_1852_;
v___y_1559_ = v___y_1853_;
goto v___jp_1556_;
}
else
{
lean_object* v___x_1870_; size_t v___x_1871_; size_t v___x_1872_; lean_object* v___x_1873_; 
v___x_1870_ = lean_box(0);
v___x_1871_ = ((size_t)0ULL);
v___x_1872_ = lean_usize_of_nat(v___x_1868_);
v___x_1873_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1867_, v___x_1871_, v___x_1872_, v___x_1870_, v_a_1258_);
lean_dec(v_a_1867_);
if (lean_obj_tag(v___x_1873_) == 0)
{
lean_dec_ref_known(v___x_1873_, 1);
v___y_1557_ = v___y_1851_;
v___y_1558_ = v___y_1852_;
v___y_1559_ = v___y_1853_;
goto v___jp_1556_;
}
else
{
v___y_1588_ = v___y_1851_;
v___y_1589_ = v___y_1852_;
v___y_1590_ = v___y_1853_;
v___y_1591_ = v___x_1873_;
goto v___jp_1587_;
}
}
}
else
{
lean_object* v_a_1874_; lean_object* v___x_1875_; uint8_t v___x_1876_; 
v_a_1874_ = lean_ctor_get(v___x_1866_, 1);
lean_inc(v_a_1874_);
lean_dec_ref_known(v___x_1866_, 2);
v___x_1875_ = lean_array_get_size(v_a_1874_);
v___x_1876_ = lean_nat_dec_lt(v___x_1864_, v___x_1875_);
if (v___x_1876_ == 0)
{
lean_object* v___x_1877_; lean_object* v___x_1879_; 
lean_dec(v_a_1874_);
lean_dec_ref(v___y_1853_);
lean_dec_ref(v___y_1851_);
lean_dec_ref(v_repo_1260_);
lean_dec_ref(v_name_1259_);
v___x_1877_ = lean_box(0);
if (v_isShared_1863_ == 0)
{
lean_ctor_set_tag(v___x_1862_, 1);
lean_ctor_set(v___x_1862_, 0, v___x_1877_);
v___x_1879_ = v___x_1862_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v___x_1877_);
v___x_1879_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
return v___x_1879_;
}
}
else
{
lean_object* v___x_1881_; size_t v___x_1882_; size_t v___x_1883_; lean_object* v___x_1884_; 
lean_del_object(v___x_1862_);
v___x_1881_ = lean_box(0);
v___x_1882_ = ((size_t)0ULL);
v___x_1883_ = lean_usize_of_nat(v___x_1875_);
v___x_1884_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1874_, v___x_1882_, v___x_1883_, v___x_1881_, v_a_1258_);
lean_dec(v_a_1874_);
if (lean_obj_tag(v___x_1884_) == 0)
{
lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1891_; 
lean_dec_ref(v___y_1853_);
lean_dec_ref(v___y_1851_);
lean_dec_ref(v_repo_1260_);
lean_dec_ref(v_name_1259_);
v_isSharedCheck_1891_ = !lean_is_exclusive(v___x_1884_);
if (v_isSharedCheck_1891_ == 0)
{
lean_object* v_unused_1892_; 
v_unused_1892_ = lean_ctor_get(v___x_1884_, 0);
lean_dec(v_unused_1892_);
v___x_1886_ = v___x_1884_;
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
else
{
lean_dec(v___x_1884_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1889_; 
if (v_isShared_1887_ == 0)
{
lean_ctor_set_tag(v___x_1886_, 1);
lean_ctor_set(v___x_1886_, 0, v___x_1881_);
v___x_1889_ = v___x_1886_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v___x_1881_);
v___x_1889_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
return v___x_1889_;
}
}
}
else
{
v___y_1588_ = v___y_1851_;
v___y_1589_ = v___y_1852_;
v___y_1590_ = v___y_1853_;
v___y_1591_ = v___x_1884_;
goto v___jp_1587_;
}
}
}
}
}
else
{
lean_object* v_a_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1907_; 
lean_dec_ref(v___y_1853_);
lean_dec_ref(v___y_1851_);
lean_dec_ref(v_repo_1260_);
lean_dec_ref(v_name_1259_);
v_a_1895_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1907_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1907_ == 0)
{
v___x_1897_ = v___x_1860_;
v_isShared_1898_ = v_isSharedCheck_1907_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_a_1895_);
lean_dec(v___x_1860_);
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
lean_inc_ref(v_a_1258_);
v___x_1902_ = lean_apply_2(v_a_1258_, v___x_1901_, lean_box(0));
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
else
{
lean_object* v___x_1908_; lean_object* v___x_1909_; uint8_t v___x_1910_; 
lean_inc_ref(v_repo_1260_);
lean_inc_ref(v___y_1852_);
v___x_1908_ = l_Lake_GitRepo_getRemoteUrl_x3f(v___y_1852_, v_repo_1260_);
v___x_1909_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_1910_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_1910_ == 0)
{
v___y_1775_ = v___y_1851_;
v___y_1776_ = v___y_1852_;
v___y_1777_ = v___y_1853_;
v_a_1778_ = v___x_1908_;
goto v___jp_1774_;
}
else
{
lean_object* v___x_1911_; size_t v___x_1912_; size_t v___x_1913_; lean_object* v___x_1914_; 
v___x_1911_ = lean_box(0);
v___x_1912_ = ((size_t)0ULL);
v___x_1913_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_1914_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_1909_, v___x_1912_, v___x_1913_, v___x_1911_, v_a_1258_);
if (lean_obj_tag(v___x_1914_) == 0)
{
lean_dec_ref_known(v___x_1914_, 1);
v___y_1775_ = v___y_1851_;
v___y_1776_ = v___y_1852_;
v___y_1777_ = v___y_1853_;
v_a_1778_ = v___x_1908_;
goto v___jp_1774_;
}
else
{
lean_dec(v___x_1908_);
lean_dec_ref(v___y_1853_);
lean_dec_ref(v___y_1851_);
lean_dec_ref(v_repo_1260_);
lean_dec_ref(v_name_1259_);
return v___x_1914_;
}
}
}
}
v___jp_1915_:
{
lean_object* v___x_1919_; lean_object* v___x_1920_; uint8_t v___x_1921_; lean_object* v___x_1922_; uint8_t v___x_1923_; 
v___x_1919_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__8));
lean_inc_ref(v_repo_1260_);
v___x_1920_ = l_System_FilePath_join(v_repo_1260_, v___x_1919_);
v___x_1921_ = l_System_FilePath_pathExists(v___x_1920_);
lean_dec_ref(v___x_1920_);
v___x_1922_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_1923_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_1923_ == 0)
{
v___y_1851_ = v_a_1918_;
v___y_1852_ = v___y_1916_;
v___y_1853_ = v___y_1917_;
v_a_1854_ = v___x_1921_;
goto v___jp_1850_;
}
else
{
lean_object* v___x_1924_; size_t v___x_1925_; size_t v___x_1926_; lean_object* v___x_1927_; 
v___x_1924_ = lean_box(0);
v___x_1925_ = ((size_t)0ULL);
v___x_1926_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_1927_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_1922_, v___x_1925_, v___x_1926_, v___x_1924_, v_a_1258_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_dec_ref_known(v___x_1927_, 1);
v___y_1851_ = v_a_1918_;
v___y_1852_ = v___y_1916_;
v___y_1853_ = v___y_1917_;
v_a_1854_ = v___x_1921_;
goto v___jp_1850_;
}
else
{
lean_dec_ref(v_a_1918_);
lean_dec_ref(v___y_1917_);
lean_dec_ref(v_repo_1260_);
lean_dec_ref(v_name_1259_);
return v___x_1927_;
}
}
}
v___jp_1928_:
{
if (lean_obj_tag(v_a_1931_) == 1)
{
lean_object* v_val_1932_; 
lean_dec_ref(v_url_1261_);
v_val_1932_ = lean_ctor_get(v_a_1931_, 0);
lean_inc(v_val_1932_);
lean_dec_ref_known(v_a_1931_, 1);
v___y_1916_ = v___y_1929_;
v___y_1917_ = v___y_1930_;
v_a_1918_ = v_val_1932_;
goto v___jp_1915_;
}
else
{
lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; uint8_t v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; 
lean_dec(v_a_1931_);
lean_dec_ref(v___y_1930_);
lean_dec_ref(v_repo_1260_);
v___x_1933_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__0));
v___x_1934_ = lean_string_append(v_name_1259_, v___x_1933_);
v___x_1935_ = lean_string_append(v___x_1934_, v_url_1261_);
lean_dec_ref(v_url_1261_);
v___x_1936_ = 3;
v___x_1937_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1937_, 0, v___x_1935_);
lean_ctor_set_uint8(v___x_1937_, sizeof(void*)*1, v___x_1936_);
lean_inc_ref(v_a_1258_);
v___x_1938_ = lean_apply_2(v_a_1258_, v___x_1937_, lean_box(0));
v___x_1939_ = lean_box(0);
v___x_1940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1940_, 0, v___x_1939_);
return v___x_1940_;
}
}
v___jp_1941_:
{
lean_object* v___x_1947_; uint8_t v___x_1948_; 
v___x_1947_ = lean_array_get_size(v___y_1945_);
v___x_1948_ = lean_nat_dec_lt(v___y_1944_, v___x_1947_);
if (v___x_1948_ == 0)
{
v___y_1929_ = v___y_1942_;
v___y_1930_ = v___y_1943_;
v_a_1931_ = v_val_1946_;
goto v___jp_1928_;
}
else
{
lean_object* v___x_1949_; size_t v___x_1950_; size_t v___x_1951_; lean_object* v___x_1952_; 
v___x_1949_ = lean_box(0);
v___x_1950_ = ((size_t)0ULL);
v___x_1951_ = lean_usize_of_nat(v___x_1947_);
v___x_1952_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_1945_, v___x_1950_, v___x_1951_, v___x_1949_, v_a_1258_);
if (lean_obj_tag(v___x_1952_) == 0)
{
lean_dec_ref_known(v___x_1952_, 1);
v___y_1929_ = v___y_1942_;
v___y_1930_ = v___y_1943_;
v_a_1931_ = v_val_1946_;
goto v___jp_1928_;
}
else
{
lean_dec(v_val_1946_);
lean_dec_ref(v___y_1943_);
lean_dec_ref(v_url_1261_);
lean_dec_ref(v_repo_1260_);
lean_dec_ref(v_name_1259_);
return v___x_1952_;
}
}
}
v___jp_1953_:
{
if (v_a_1956_ == 0)
{
v___y_1916_ = v___y_1954_;
v___y_1917_ = v___y_1955_;
v_a_1918_ = v_url_1261_;
goto v___jp_1915_;
}
else
{
lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; uint8_t v___x_1961_; 
lean_inc_ref(v_url_1261_);
v___x_1957_ = l_Lake_resolvePath(v_url_1261_);
v___x_1958_ = lean_unsigned_to_nat(0u);
v___x_1959_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_1960_ = lean_string_utf8_byte_size(v___x_1957_);
v___x_1961_ = lean_nat_dec_eq(v___x_1960_, v___x_1958_);
if (v___x_1961_ == 0)
{
lean_object* v___x_1962_; 
v___x_1962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1962_, 0, v___x_1957_);
v___y_1942_ = v___y_1954_;
v___y_1943_ = v___y_1955_;
v___y_1944_ = v___x_1958_;
v___y_1945_ = v___x_1959_;
v_val_1946_ = v___x_1962_;
goto v___jp_1941_;
}
else
{
lean_object* v___x_1963_; 
lean_dec_ref(v___x_1957_);
v___x_1963_ = lean_box(0);
v___y_1942_ = v___y_1954_;
v___y_1943_ = v___y_1955_;
v___y_1944_ = v___x_1958_;
v___y_1945_ = v___x_1959_;
v_val_1946_ = v___x_1963_;
goto v___jp_1941_;
}
}
}
v___jp_1964_:
{
uint8_t v___x_1966_; lean_object* v_remote_1967_; lean_object* v___x_1968_; uint8_t v___x_1969_; 
v___x_1966_ = l_System_FilePath_pathExists(v_url_1261_);
v_remote_1967_ = l_Lake_Git_defaultRemote;
v___x_1968_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_1969_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_1969_ == 0)
{
v___y_1954_ = v_remote_1967_;
v___y_1955_ = v___y_1965_;
v_a_1956_ = v___x_1966_;
goto v___jp_1953_;
}
else
{
lean_object* v___x_1970_; size_t v___x_1971_; size_t v___x_1972_; lean_object* v___x_1973_; 
v___x_1970_ = lean_box(0);
v___x_1971_ = ((size_t)0ULL);
v___x_1972_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_1973_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_1968_, v___x_1971_, v___x_1972_, v___x_1970_, v_a_1258_);
if (lean_obj_tag(v___x_1973_) == 0)
{
lean_dec_ref_known(v___x_1973_, 1);
v___y_1954_ = v_remote_1967_;
v___y_1955_ = v___y_1965_;
v_a_1956_ = v___x_1966_;
goto v___jp_1953_;
}
else
{
lean_dec_ref(v___y_1965_);
lean_dec_ref(v_url_1261_);
lean_dec_ref(v_repo_1260_);
lean_dec_ref(v_name_1259_);
return v___x_1973_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0___boxed(lean_object* v_a_1976_, lean_object* v_name_1977_, lean_object* v_repo_1978_, lean_object* v_url_1979_, lean_object* v_rev_x3f_1980_, lean_object* v_a_1981_){
_start:
{
lean_object* v_res_1982_; 
v_res_1982_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(v_a_1976_, v_name_1977_, v_repo_1978_, v_url_1979_, v_rev_x3f_1980_);
lean_dec_ref(v_a_1976_);
return v_res_1982_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit(lean_object* v_dep_1983_, uint8_t v_inherited_1984_, lean_object* v_lakeEnv_1985_, lean_object* v_wsDir_1986_, lean_object* v_name_1987_, lean_object* v_relPkgDir_1988_, lean_object* v_gitUrl_1989_, lean_object* v_remoteUrl_1990_, lean_object* v_inputRev_x3f_1991_, lean_object* v_subDir_x3f_1992_, lean_object* v_a_1993_){
_start:
{
lean_object* v_pkgUrlMap_1995_; lean_object* v_name_1996_; lean_object* v_scope_1997_; lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2173_; 
v_pkgUrlMap_1995_ = lean_ctor_get(v_lakeEnv_1985_, 5);
v_name_1996_ = lean_ctor_get(v_dep_1983_, 0);
v_scope_1997_ = lean_ctor_get(v_dep_1983_, 1);
v_isSharedCheck_2173_ = !lean_is_exclusive(v_dep_1983_);
if (v_isSharedCheck_2173_ == 0)
{
lean_object* v_unused_2174_; lean_object* v_unused_2175_; lean_object* v_unused_2176_; 
v_unused_2174_ = lean_ctor_get(v_dep_1983_, 4);
lean_dec(v_unused_2174_);
v_unused_2175_ = lean_ctor_get(v_dep_1983_, 3);
lean_dec(v_unused_2175_);
v_unused_2176_ = lean_ctor_get(v_dep_1983_, 2);
lean_dec(v_unused_2176_);
v___x_1999_ = v_dep_1983_;
v_isShared_2000_ = v_isSharedCheck_2173_;
goto v_resetjp_1998_;
}
else
{
lean_inc(v_scope_1997_);
lean_inc(v_name_1996_);
lean_dec(v_dep_1983_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2173_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
lean_object* v___y_2002_; lean_object* v___y_2003_; lean_object* v___y_2004_; lean_object* v_a_2005_; lean_object* v___y_2014_; lean_object* v___y_2015_; lean_object* v___y_2016_; lean_object* v___y_2017_; lean_object* v___y_2018_; lean_object* v_val_2019_; lean_object* v___y_2035_; lean_object* v___y_2036_; lean_object* v___y_2037_; lean_object* v_a_2038_; lean_object* v___y_2070_; lean_object* v___y_2071_; lean_object* v___y_2072_; lean_object* v___y_2073_; lean_object* v___y_2074_; lean_object* v_val_2075_; lean_object* v___y_2091_; lean_object* v___y_2092_; lean_object* v___y_2093_; lean_object* v___y_2104_; lean_object* v_a_2105_; lean_object* v_gitDir_2108_; lean_object* v___y_2110_; lean_object* v___x_2171_; 
lean_inc_ref(v_relPkgDir_1988_);
lean_inc_ref(v_wsDir_1986_);
v_gitDir_2108_ = l_Lake_joinRelative(v_wsDir_1986_, v_relPkgDir_1988_);
v___x_2171_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgUrlMap_1995_, v_name_1996_);
if (lean_obj_tag(v___x_2171_) == 0)
{
v___y_2110_ = v_gitUrl_1989_;
goto v___jp_2109_;
}
else
{
lean_object* v_val_2172_; 
lean_dec_ref(v_gitUrl_1989_);
v_val_2172_ = lean_ctor_get(v___x_2171_, 0);
lean_inc(v_val_2172_);
lean_dec_ref_known(v___x_2171_, 1);
v___y_2110_ = v_val_2172_;
goto v___jp_2109_;
}
v___jp_2001_:
{
lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2010_; 
v___x_2006_ = l_Lake_defaultConfigFile;
v___x_2007_ = lean_box(0);
v___x_2008_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_2008_, 0, v_name_1996_);
lean_ctor_set(v___x_2008_, 1, v_scope_1997_);
lean_ctor_set(v___x_2008_, 2, v___x_2006_);
lean_ctor_set(v___x_2008_, 3, v___x_2007_);
lean_ctor_set(v___x_2008_, 4, v___y_2003_);
lean_ctor_set_uint8(v___x_2008_, sizeof(void*)*5, v_inherited_1984_);
if (v_isShared_2000_ == 0)
{
lean_ctor_set(v___x_1999_, 4, v___x_2008_);
lean_ctor_set(v___x_1999_, 3, v_a_2005_);
lean_ctor_set(v___x_1999_, 2, v_remoteUrl_1990_);
lean_ctor_set(v___x_1999_, 1, v___y_2002_);
lean_ctor_set(v___x_1999_, 0, v___y_2004_);
v___x_2010_ = v___x_1999_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v___y_2004_);
lean_ctor_set(v_reuseFailAlloc_2012_, 1, v___y_2002_);
lean_ctor_set(v_reuseFailAlloc_2012_, 2, v_remoteUrl_1990_);
lean_ctor_set(v_reuseFailAlloc_2012_, 3, v_a_2005_);
lean_ctor_set(v_reuseFailAlloc_2012_, 4, v___x_2008_);
v___x_2010_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
lean_object* v___x_2011_; 
v___x_2011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2011_, 0, v___x_2010_);
return v___x_2011_;
}
}
v___jp_2013_:
{
lean_object* v___x_2020_; uint8_t v___x_2021_; 
v___x_2020_ = lean_array_get_size(v___y_2014_);
v___x_2021_ = lean_nat_dec_lt(v___y_2015_, v___x_2020_);
if (v___x_2021_ == 0)
{
v___y_2002_ = v___y_2016_;
v___y_2003_ = v___y_2017_;
v___y_2004_ = v___y_2018_;
v_a_2005_ = v_val_2019_;
goto v___jp_2001_;
}
else
{
lean_object* v___x_2022_; size_t v___x_2023_; size_t v___x_2024_; lean_object* v___x_2025_; 
v___x_2022_ = lean_box(0);
v___x_2023_ = ((size_t)0ULL);
v___x_2024_ = lean_usize_of_nat(v___x_2020_);
v___x_2025_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_2014_, v___x_2023_, v___x_2024_, v___x_2022_, v_a_1993_);
if (lean_obj_tag(v___x_2025_) == 0)
{
lean_dec_ref_known(v___x_2025_, 1);
v___y_2002_ = v___y_2016_;
v___y_2003_ = v___y_2017_;
v___y_2004_ = v___y_2018_;
v_a_2005_ = v_val_2019_;
goto v___jp_2001_;
}
else
{
lean_object* v_a_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2033_; 
lean_dec_ref(v_val_2019_);
lean_dec_ref(v___y_2018_);
lean_dec_ref(v___y_2017_);
lean_dec_ref(v___y_2016_);
lean_del_object(v___x_1999_);
lean_dec_ref(v_scope_1997_);
lean_dec(v_name_1996_);
lean_dec_ref(v_remoteUrl_1990_);
v_a_2026_ = lean_ctor_get(v___x_2025_, 0);
v_isSharedCheck_2033_ = !lean_is_exclusive(v___x_2025_);
if (v_isSharedCheck_2033_ == 0)
{
v___x_2028_ = v___x_2025_;
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_a_2026_);
lean_dec(v___x_2025_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v___x_2031_; 
if (v_isShared_2029_ == 0)
{
v___x_2031_ = v___x_2028_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_a_2026_);
v___x_2031_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
return v___x_2031_;
}
}
}
}
}
v___jp_2034_:
{
if (lean_obj_tag(v_a_2038_) == 1)
{
lean_object* v_val_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; 
lean_dec_ref(v___y_2036_);
lean_dec_ref(v_name_1987_);
v_val_2039_ = lean_ctor_get(v_a_2038_, 0);
lean_inc_n(v_val_2039_, 2);
lean_dec_ref_known(v_a_2038_, 1);
v___x_2040_ = l_Lake_defaultManifestFile;
v___x_2041_ = l_Lake_joinRelative(v_val_2039_, v___x_2040_);
v___x_2042_ = lean_unsigned_to_nat(0u);
v___x_2043_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_2044_ = l_Lake_Manifest_load(v___x_2041_);
if (lean_obj_tag(v___x_2044_) == 0)
{
lean_object* v_a_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2052_; 
v_a_2045_ = lean_ctor_get(v___x_2044_, 0);
v_isSharedCheck_2052_ = !lean_is_exclusive(v___x_2044_);
if (v_isSharedCheck_2052_ == 0)
{
v___x_2047_ = v___x_2044_;
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_a_2045_);
lean_dec(v___x_2044_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v___x_2050_; 
if (v_isShared_2048_ == 0)
{
lean_ctor_set_tag(v___x_2047_, 1);
v___x_2050_ = v___x_2047_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_a_2045_);
v___x_2050_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
v___y_2014_ = v___x_2043_;
v___y_2015_ = v___x_2042_;
v___y_2016_ = v___y_2035_;
v___y_2017_ = v___y_2037_;
v___y_2018_ = v_val_2039_;
v_val_2019_ = v___x_2050_;
goto v___jp_2013_;
}
}
}
else
{
lean_object* v_a_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2060_; 
v_a_2053_ = lean_ctor_get(v___x_2044_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_2044_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2055_ = v___x_2044_;
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_a_2053_);
lean_dec(v___x_2044_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v___x_2058_; 
if (v_isShared_2056_ == 0)
{
lean_ctor_set_tag(v___x_2055_, 0);
v___x_2058_ = v___x_2055_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_a_2053_);
v___x_2058_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
v___y_2014_ = v___x_2043_;
v___y_2015_ = v___x_2042_;
v___y_2016_ = v___y_2035_;
v___y_2017_ = v___y_2037_;
v___y_2018_ = v_val_2039_;
v_val_2019_ = v___x_2058_;
goto v___jp_2013_;
}
}
}
}
else
{
lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; uint8_t v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; 
lean_dec(v_a_2038_);
lean_dec_ref(v___y_2037_);
lean_dec_ref(v___y_2035_);
lean_del_object(v___x_1999_);
lean_dec_ref(v_scope_1997_);
lean_dec(v_name_1996_);
lean_dec_ref(v_remoteUrl_1990_);
v___x_2061_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0));
v___x_2062_ = lean_string_append(v_name_1987_, v___x_2061_);
v___x_2063_ = lean_string_append(v___x_2062_, v___y_2036_);
lean_dec_ref(v___y_2036_);
v___x_2064_ = 3;
v___x_2065_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2065_, 0, v___x_2063_);
lean_ctor_set_uint8(v___x_2065_, sizeof(void*)*1, v___x_2064_);
lean_inc_ref(v_a_1993_);
v___x_2066_ = lean_apply_2(v_a_1993_, v___x_2065_, lean_box(0));
v___x_2067_ = lean_box(0);
v___x_2068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2068_, 0, v___x_2067_);
return v___x_2068_;
}
}
v___jp_2069_:
{
lean_object* v___x_2076_; uint8_t v___x_2077_; 
v___x_2076_ = lean_array_get_size(v___y_2073_);
v___x_2077_ = lean_nat_dec_lt(v___y_2074_, v___x_2076_);
if (v___x_2077_ == 0)
{
v___y_2035_ = v___y_2070_;
v___y_2036_ = v___y_2071_;
v___y_2037_ = v___y_2072_;
v_a_2038_ = v_val_2075_;
goto v___jp_2034_;
}
else
{
lean_object* v___x_2078_; size_t v___x_2079_; size_t v___x_2080_; lean_object* v___x_2081_; 
v___x_2078_ = lean_box(0);
v___x_2079_ = ((size_t)0ULL);
v___x_2080_ = lean_usize_of_nat(v___x_2076_);
v___x_2081_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_2073_, v___x_2079_, v___x_2080_, v___x_2078_, v_a_1993_);
if (lean_obj_tag(v___x_2081_) == 0)
{
lean_dec_ref_known(v___x_2081_, 1);
v___y_2035_ = v___y_2070_;
v___y_2036_ = v___y_2071_;
v___y_2037_ = v___y_2072_;
v_a_2038_ = v_val_2075_;
goto v___jp_2034_;
}
else
{
lean_object* v_a_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2089_; 
lean_dec(v_val_2075_);
lean_dec_ref(v___y_2072_);
lean_dec_ref(v___y_2071_);
lean_dec_ref(v___y_2070_);
lean_del_object(v___x_1999_);
lean_dec_ref(v_scope_1997_);
lean_dec(v_name_1996_);
lean_dec_ref(v_remoteUrl_1990_);
lean_dec_ref(v_name_1987_);
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
return v___x_2087_;
}
}
}
}
}
v___jp_2090_:
{
lean_object* v_pkgDir_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; uint8_t v___x_2100_; 
lean_inc_ref(v___y_2093_);
v_pkgDir_2094_ = l_Lake_joinRelative(v_wsDir_1986_, v___y_2093_);
lean_inc_ref(v_pkgDir_2094_);
v___x_2095_ = l_Lake_resolvePath(v_pkgDir_2094_);
v___x_2096_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2096_, 0, v___y_2092_);
lean_ctor_set(v___x_2096_, 1, v___y_2091_);
lean_ctor_set(v___x_2096_, 2, v_inputRev_x3f_1991_);
lean_ctor_set(v___x_2096_, 3, v_subDir_x3f_1992_);
v___x_2097_ = lean_unsigned_to_nat(0u);
v___x_2098_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_2099_ = lean_string_utf8_byte_size(v___x_2095_);
v___x_2100_ = lean_nat_dec_eq(v___x_2099_, v___x_2097_);
if (v___x_2100_ == 0)
{
lean_object* v___x_2101_; 
v___x_2101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2101_, 0, v___x_2095_);
v___y_2070_ = v___y_2093_;
v___y_2071_ = v_pkgDir_2094_;
v___y_2072_ = v___x_2096_;
v___y_2073_ = v___x_2098_;
v___y_2074_ = v___x_2097_;
v_val_2075_ = v___x_2101_;
goto v___jp_2069_;
}
else
{
lean_object* v___x_2102_; 
lean_dec_ref(v___x_2095_);
v___x_2102_ = lean_box(0);
v___y_2070_ = v___y_2093_;
v___y_2071_ = v_pkgDir_2094_;
v___y_2072_ = v___x_2096_;
v___y_2073_ = v___x_2098_;
v___y_2074_ = v___x_2097_;
v_val_2075_ = v___x_2102_;
goto v___jp_2069_;
}
}
v___jp_2103_:
{
if (lean_obj_tag(v_subDir_x3f_1992_) == 1)
{
lean_object* v_val_2106_; lean_object* v___x_2107_; 
v_val_2106_ = lean_ctor_get(v_subDir_x3f_1992_, 0);
lean_inc(v_val_2106_);
v___x_2107_ = l_Lake_joinRelative(v_relPkgDir_1988_, v_val_2106_);
v___y_2091_ = v_a_2105_;
v___y_2092_ = v___y_2104_;
v___y_2093_ = v___x_2107_;
goto v___jp_2090_;
}
else
{
v___y_2091_ = v_a_2105_;
v___y_2092_ = v___y_2104_;
v___y_2093_ = v_relPkgDir_1988_;
goto v___jp_2090_;
}
}
v___jp_2109_:
{
lean_object* v___x_2111_; 
lean_inc(v_inputRev_x3f_1991_);
lean_inc_ref(v___y_2110_);
lean_inc_ref(v_gitDir_2108_);
lean_inc_ref(v_name_1987_);
v___x_2111_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(v_a_1993_, v_name_1987_, v_gitDir_2108_, v___y_2110_, v_inputRev_x3f_1991_);
if (lean_obj_tag(v___x_2111_) == 0)
{
lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2161_; 
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2161_ == 0)
{
lean_object* v_unused_2162_; 
v_unused_2162_ = lean_ctor_get(v___x_2111_, 0);
lean_dec(v_unused_2162_);
v___x_2113_ = v___x_2111_;
v_isShared_2114_ = v_isSharedCheck_2161_;
goto v_resetjp_2112_;
}
else
{
lean_dec(v___x_2111_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2161_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; 
v___x_2115_ = lean_unsigned_to_nat(0u);
v___x_2116_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_2117_ = l_Lake_GitRepo_getHeadRevision(v_gitDir_2108_, v___x_2116_);
if (lean_obj_tag(v___x_2117_) == 0)
{
lean_object* v_a_2118_; lean_object* v_a_2119_; lean_object* v___x_2120_; uint8_t v___x_2121_; 
lean_del_object(v___x_2113_);
v_a_2118_ = lean_ctor_get(v___x_2117_, 0);
lean_inc(v_a_2118_);
v_a_2119_ = lean_ctor_get(v___x_2117_, 1);
lean_inc(v_a_2119_);
lean_dec_ref_known(v___x_2117_, 2);
v___x_2120_ = lean_array_get_size(v_a_2119_);
v___x_2121_ = lean_nat_dec_lt(v___x_2115_, v___x_2120_);
if (v___x_2121_ == 0)
{
lean_dec(v_a_2119_);
v___y_2104_ = v___y_2110_;
v_a_2105_ = v_a_2118_;
goto v___jp_2103_;
}
else
{
lean_object* v___x_2122_; size_t v___x_2123_; size_t v___x_2124_; lean_object* v___x_2125_; 
v___x_2122_ = lean_box(0);
v___x_2123_ = ((size_t)0ULL);
v___x_2124_ = lean_usize_of_nat(v___x_2120_);
v___x_2125_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_2119_, v___x_2123_, v___x_2124_, v___x_2122_, v_a_1993_);
lean_dec(v_a_2119_);
if (lean_obj_tag(v___x_2125_) == 0)
{
lean_dec_ref_known(v___x_2125_, 1);
v___y_2104_ = v___y_2110_;
v_a_2105_ = v_a_2118_;
goto v___jp_2103_;
}
else
{
lean_object* v_a_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2133_; 
lean_dec(v_a_2118_);
lean_dec_ref(v___y_2110_);
lean_del_object(v___x_1999_);
lean_dec_ref(v_scope_1997_);
lean_dec(v_name_1996_);
lean_dec(v_subDir_x3f_1992_);
lean_dec(v_inputRev_x3f_1991_);
lean_dec_ref(v_remoteUrl_1990_);
lean_dec_ref(v_relPkgDir_1988_);
lean_dec_ref(v_name_1987_);
lean_dec_ref(v_wsDir_1986_);
v_a_2126_ = lean_ctor_get(v___x_2125_, 0);
v_isSharedCheck_2133_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2133_ == 0)
{
v___x_2128_ = v___x_2125_;
v_isShared_2129_ = v_isSharedCheck_2133_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_a_2126_);
lean_dec(v___x_2125_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2133_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v___x_2131_; 
if (v_isShared_2129_ == 0)
{
v___x_2131_ = v___x_2128_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v_a_2126_);
v___x_2131_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
return v___x_2131_;
}
}
}
}
}
else
{
lean_object* v_a_2134_; lean_object* v___x_2135_; uint8_t v___x_2136_; 
lean_dec_ref(v___y_2110_);
lean_del_object(v___x_1999_);
lean_dec_ref(v_scope_1997_);
lean_dec(v_name_1996_);
lean_dec(v_subDir_x3f_1992_);
lean_dec(v_inputRev_x3f_1991_);
lean_dec_ref(v_remoteUrl_1990_);
lean_dec_ref(v_relPkgDir_1988_);
lean_dec_ref(v_name_1987_);
lean_dec_ref(v_wsDir_1986_);
v_a_2134_ = lean_ctor_get(v___x_2117_, 1);
lean_inc(v_a_2134_);
lean_dec_ref_known(v___x_2117_, 2);
v___x_2135_ = lean_array_get_size(v_a_2134_);
v___x_2136_ = lean_nat_dec_lt(v___x_2115_, v___x_2135_);
if (v___x_2136_ == 0)
{
lean_object* v___x_2137_; lean_object* v___x_2139_; 
lean_dec(v_a_2134_);
v___x_2137_ = lean_box(0);
if (v_isShared_2114_ == 0)
{
lean_ctor_set_tag(v___x_2113_, 1);
lean_ctor_set(v___x_2113_, 0, v___x_2137_);
v___x_2139_ = v___x_2113_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v___x_2137_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
return v___x_2139_;
}
}
else
{
lean_object* v___x_2141_; size_t v___x_2142_; size_t v___x_2143_; lean_object* v___x_2144_; 
lean_del_object(v___x_2113_);
v___x_2141_ = lean_box(0);
v___x_2142_ = ((size_t)0ULL);
v___x_2143_ = lean_usize_of_nat(v___x_2135_);
v___x_2144_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_2134_, v___x_2142_, v___x_2143_, v___x_2141_, v_a_1993_);
lean_dec(v_a_2134_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2151_; 
v_isSharedCheck_2151_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2151_ == 0)
{
lean_object* v_unused_2152_; 
v_unused_2152_ = lean_ctor_get(v___x_2144_, 0);
lean_dec(v_unused_2152_);
v___x_2146_ = v___x_2144_;
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
else
{
lean_dec(v___x_2144_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v___x_2149_; 
if (v_isShared_2147_ == 0)
{
lean_ctor_set_tag(v___x_2146_, 1);
lean_ctor_set(v___x_2146_, 0, v___x_2141_);
v___x_2149_ = v___x_2146_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v___x_2141_);
v___x_2149_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
return v___x_2149_;
}
}
}
else
{
lean_object* v_a_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2160_; 
v_a_2153_ = lean_ctor_get(v___x_2144_, 0);
v_isSharedCheck_2160_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2160_ == 0)
{
v___x_2155_ = v___x_2144_;
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_a_2153_);
lean_dec(v___x_2144_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v___x_2158_; 
if (v_isShared_2156_ == 0)
{
v___x_2158_ = v___x_2155_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_a_2153_);
v___x_2158_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
return v___x_2158_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2163_; lean_object* v___x_2165_; uint8_t v_isShared_2166_; uint8_t v_isSharedCheck_2170_; 
lean_dec_ref(v___y_2110_);
lean_dec_ref(v_gitDir_2108_);
lean_del_object(v___x_1999_);
lean_dec_ref(v_scope_1997_);
lean_dec(v_name_1996_);
lean_dec(v_subDir_x3f_1992_);
lean_dec(v_inputRev_x3f_1991_);
lean_dec_ref(v_remoteUrl_1990_);
lean_dec_ref(v_relPkgDir_1988_);
lean_dec_ref(v_name_1987_);
lean_dec_ref(v_wsDir_1986_);
v_a_2163_ = lean_ctor_get(v___x_2111_, 0);
v_isSharedCheck_2170_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2170_ == 0)
{
v___x_2165_ = v___x_2111_;
v_isShared_2166_ = v_isSharedCheck_2170_;
goto v_resetjp_2164_;
}
else
{
lean_inc(v_a_2163_);
lean_dec(v___x_2111_);
v___x_2165_ = lean_box(0);
v_isShared_2166_ = v_isSharedCheck_2170_;
goto v_resetjp_2164_;
}
v_resetjp_2164_:
{
lean_object* v___x_2168_; 
if (v_isShared_2166_ == 0)
{
v___x_2168_ = v___x_2165_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v_a_2163_);
v___x_2168_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
return v___x_2168_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___boxed(lean_object* v_dep_2177_, lean_object* v_inherited_2178_, lean_object* v_lakeEnv_2179_, lean_object* v_wsDir_2180_, lean_object* v_name_2181_, lean_object* v_relPkgDir_2182_, lean_object* v_gitUrl_2183_, lean_object* v_remoteUrl_2184_, lean_object* v_inputRev_x3f_2185_, lean_object* v_subDir_x3f_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_){
_start:
{
uint8_t v_inherited_boxed_2189_; lean_object* v_res_2190_; 
v_inherited_boxed_2189_ = lean_unbox(v_inherited_2178_);
v_res_2190_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit(v_dep_2177_, v_inherited_boxed_2189_, v_lakeEnv_2179_, v_wsDir_2180_, v_name_2181_, v_relPkgDir_2182_, v_gitUrl_2183_, v_remoteUrl_2184_, v_inputRev_x3f_2185_, v_subDir_x3f_2186_, v_a_2187_);
lean_dec_ref(v_a_2187_);
lean_dec_ref(v_lakeEnv_2179_);
return v_res_2190_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(lean_object* v_a_2191_, lean_object* v_dep_2192_, uint8_t v_inherited_2193_, lean_object* v_lakeEnv_2194_, lean_object* v_wsDir_2195_, lean_object* v_name_2196_, lean_object* v_relPkgDir_2197_, lean_object* v_gitUrl_2198_, lean_object* v_remoteUrl_2199_, lean_object* v_inputRev_x3f_2200_, lean_object* v_subDir_x3f_2201_){
_start:
{
lean_object* v_pkgUrlMap_2203_; lean_object* v_name_2204_; lean_object* v_scope_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2381_; 
v_pkgUrlMap_2203_ = lean_ctor_get(v_lakeEnv_2194_, 5);
v_name_2204_ = lean_ctor_get(v_dep_2192_, 0);
v_scope_2205_ = lean_ctor_get(v_dep_2192_, 1);
v_isSharedCheck_2381_ = !lean_is_exclusive(v_dep_2192_);
if (v_isSharedCheck_2381_ == 0)
{
lean_object* v_unused_2382_; lean_object* v_unused_2383_; lean_object* v_unused_2384_; 
v_unused_2382_ = lean_ctor_get(v_dep_2192_, 4);
lean_dec(v_unused_2382_);
v_unused_2383_ = lean_ctor_get(v_dep_2192_, 3);
lean_dec(v_unused_2383_);
v_unused_2384_ = lean_ctor_get(v_dep_2192_, 2);
lean_dec(v_unused_2384_);
v___x_2207_ = v_dep_2192_;
v_isShared_2208_ = v_isSharedCheck_2381_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_scope_2205_);
lean_inc(v_name_2204_);
lean_dec(v_dep_2192_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2381_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___y_2210_; lean_object* v___y_2211_; lean_object* v___y_2212_; lean_object* v_a_2213_; lean_object* v___y_2222_; lean_object* v___y_2223_; lean_object* v___y_2224_; lean_object* v___y_2225_; lean_object* v___y_2226_; lean_object* v_val_2227_; lean_object* v___y_2243_; lean_object* v___y_2244_; lean_object* v___y_2245_; lean_object* v_a_2246_; lean_object* v___y_2278_; lean_object* v___y_2279_; lean_object* v___y_2280_; lean_object* v___y_2281_; lean_object* v___y_2282_; lean_object* v_val_2283_; lean_object* v___y_2299_; lean_object* v___y_2300_; lean_object* v___y_2301_; lean_object* v___y_2312_; lean_object* v_a_2313_; lean_object* v_gitDir_2316_; lean_object* v___y_2318_; lean_object* v___x_2379_; 
lean_inc_ref(v_relPkgDir_2197_);
lean_inc_ref(v_wsDir_2195_);
v_gitDir_2316_ = l_Lake_joinRelative(v_wsDir_2195_, v_relPkgDir_2197_);
v___x_2379_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgUrlMap_2203_, v_name_2204_);
if (lean_obj_tag(v___x_2379_) == 0)
{
v___y_2318_ = v_gitUrl_2198_;
goto v___jp_2317_;
}
else
{
lean_object* v_val_2380_; 
lean_dec_ref(v_gitUrl_2198_);
v_val_2380_ = lean_ctor_get(v___x_2379_, 0);
lean_inc(v_val_2380_);
lean_dec_ref_known(v___x_2379_, 1);
v___y_2318_ = v_val_2380_;
goto v___jp_2317_;
}
v___jp_2209_:
{
lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2218_; 
v___x_2214_ = l_Lake_defaultConfigFile;
v___x_2215_ = lean_box(0);
v___x_2216_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_2216_, 0, v_name_2204_);
lean_ctor_set(v___x_2216_, 1, v_scope_2205_);
lean_ctor_set(v___x_2216_, 2, v___x_2214_);
lean_ctor_set(v___x_2216_, 3, v___x_2215_);
lean_ctor_set(v___x_2216_, 4, v___y_2212_);
lean_ctor_set_uint8(v___x_2216_, sizeof(void*)*5, v_inherited_2193_);
if (v_isShared_2208_ == 0)
{
lean_ctor_set(v___x_2207_, 4, v___x_2216_);
lean_ctor_set(v___x_2207_, 3, v_a_2213_);
lean_ctor_set(v___x_2207_, 2, v_remoteUrl_2199_);
lean_ctor_set(v___x_2207_, 1, v___y_2210_);
lean_ctor_set(v___x_2207_, 0, v___y_2211_);
v___x_2218_ = v___x_2207_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v___y_2211_);
lean_ctor_set(v_reuseFailAlloc_2220_, 1, v___y_2210_);
lean_ctor_set(v_reuseFailAlloc_2220_, 2, v_remoteUrl_2199_);
lean_ctor_set(v_reuseFailAlloc_2220_, 3, v_a_2213_);
lean_ctor_set(v_reuseFailAlloc_2220_, 4, v___x_2216_);
v___x_2218_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
lean_object* v___x_2219_; 
v___x_2219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2219_, 0, v___x_2218_);
return v___x_2219_;
}
}
v___jp_2221_:
{
lean_object* v___x_2228_; uint8_t v___x_2229_; 
v___x_2228_ = lean_array_get_size(v___y_2224_);
v___x_2229_ = lean_nat_dec_lt(v___y_2223_, v___x_2228_);
if (v___x_2229_ == 0)
{
v___y_2210_ = v___y_2222_;
v___y_2211_ = v___y_2225_;
v___y_2212_ = v___y_2226_;
v_a_2213_ = v_val_2227_;
goto v___jp_2209_;
}
else
{
lean_object* v___x_2230_; size_t v___x_2231_; size_t v___x_2232_; lean_object* v___x_2233_; 
v___x_2230_ = lean_box(0);
v___x_2231_ = ((size_t)0ULL);
v___x_2232_ = lean_usize_of_nat(v___x_2228_);
v___x_2233_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_2224_, v___x_2231_, v___x_2232_, v___x_2230_, v_a_2191_);
if (lean_obj_tag(v___x_2233_) == 0)
{
lean_dec_ref_known(v___x_2233_, 1);
v___y_2210_ = v___y_2222_;
v___y_2211_ = v___y_2225_;
v___y_2212_ = v___y_2226_;
v_a_2213_ = v_val_2227_;
goto v___jp_2209_;
}
else
{
lean_object* v_a_2234_; lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2241_; 
lean_dec_ref(v_val_2227_);
lean_dec_ref(v___y_2226_);
lean_dec_ref(v___y_2225_);
lean_dec_ref(v___y_2222_);
lean_del_object(v___x_2207_);
lean_dec_ref(v_scope_2205_);
lean_dec(v_name_2204_);
lean_dec_ref(v_remoteUrl_2199_);
v_a_2234_ = lean_ctor_get(v___x_2233_, 0);
v_isSharedCheck_2241_ = !lean_is_exclusive(v___x_2233_);
if (v_isSharedCheck_2241_ == 0)
{
v___x_2236_ = v___x_2233_;
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
else
{
lean_inc(v_a_2234_);
lean_dec(v___x_2233_);
v___x_2236_ = lean_box(0);
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
v_resetjp_2235_:
{
lean_object* v___x_2239_; 
if (v_isShared_2237_ == 0)
{
v___x_2239_ = v___x_2236_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v_a_2234_);
v___x_2239_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
return v___x_2239_;
}
}
}
}
}
v___jp_2242_:
{
if (lean_obj_tag(v_a_2246_) == 1)
{
lean_object* v_val_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; 
lean_dec_ref(v___y_2244_);
lean_dec_ref(v_name_2196_);
v_val_2247_ = lean_ctor_get(v_a_2246_, 0);
lean_inc_n(v_val_2247_, 2);
lean_dec_ref_known(v_a_2246_, 1);
v___x_2248_ = l_Lake_defaultManifestFile;
v___x_2249_ = l_Lake_joinRelative(v_val_2247_, v___x_2248_);
v___x_2250_ = lean_unsigned_to_nat(0u);
v___x_2251_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_2252_ = l_Lake_Manifest_load(v___x_2249_);
if (lean_obj_tag(v___x_2252_) == 0)
{
lean_object* v_a_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2260_; 
v_a_2253_ = lean_ctor_get(v___x_2252_, 0);
v_isSharedCheck_2260_ = !lean_is_exclusive(v___x_2252_);
if (v_isSharedCheck_2260_ == 0)
{
v___x_2255_ = v___x_2252_;
v_isShared_2256_ = v_isSharedCheck_2260_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_a_2253_);
lean_dec(v___x_2252_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2260_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
lean_object* v___x_2258_; 
if (v_isShared_2256_ == 0)
{
lean_ctor_set_tag(v___x_2255_, 1);
v___x_2258_ = v___x_2255_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v_a_2253_);
v___x_2258_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2257_;
}
v_reusejp_2257_:
{
v___y_2222_ = v___y_2243_;
v___y_2223_ = v___x_2250_;
v___y_2224_ = v___x_2251_;
v___y_2225_ = v_val_2247_;
v___y_2226_ = v___y_2245_;
v_val_2227_ = v___x_2258_;
goto v___jp_2221_;
}
}
}
else
{
lean_object* v_a_2261_; lean_object* v___x_2263_; uint8_t v_isShared_2264_; uint8_t v_isSharedCheck_2268_; 
v_a_2261_ = lean_ctor_get(v___x_2252_, 0);
v_isSharedCheck_2268_ = !lean_is_exclusive(v___x_2252_);
if (v_isSharedCheck_2268_ == 0)
{
v___x_2263_ = v___x_2252_;
v_isShared_2264_ = v_isSharedCheck_2268_;
goto v_resetjp_2262_;
}
else
{
lean_inc(v_a_2261_);
lean_dec(v___x_2252_);
v___x_2263_ = lean_box(0);
v_isShared_2264_ = v_isSharedCheck_2268_;
goto v_resetjp_2262_;
}
v_resetjp_2262_:
{
lean_object* v___x_2266_; 
if (v_isShared_2264_ == 0)
{
lean_ctor_set_tag(v___x_2263_, 0);
v___x_2266_ = v___x_2263_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v_a_2261_);
v___x_2266_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
v___y_2222_ = v___y_2243_;
v___y_2223_ = v___x_2250_;
v___y_2224_ = v___x_2251_;
v___y_2225_ = v_val_2247_;
v___y_2226_ = v___y_2245_;
v_val_2227_ = v___x_2266_;
goto v___jp_2221_;
}
}
}
}
else
{
lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; uint8_t v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; 
lean_dec(v_a_2246_);
lean_dec_ref(v___y_2245_);
lean_dec_ref(v___y_2243_);
lean_del_object(v___x_2207_);
lean_dec_ref(v_scope_2205_);
lean_dec(v_name_2204_);
lean_dec_ref(v_remoteUrl_2199_);
v___x_2269_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0));
v___x_2270_ = lean_string_append(v_name_2196_, v___x_2269_);
v___x_2271_ = lean_string_append(v___x_2270_, v___y_2244_);
lean_dec_ref(v___y_2244_);
v___x_2272_ = 3;
v___x_2273_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2273_, 0, v___x_2271_);
lean_ctor_set_uint8(v___x_2273_, sizeof(void*)*1, v___x_2272_);
lean_inc_ref(v_a_2191_);
v___x_2274_ = lean_apply_2(v_a_2191_, v___x_2273_, lean_box(0));
v___x_2275_ = lean_box(0);
v___x_2276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2276_, 0, v___x_2275_);
return v___x_2276_;
}
}
v___jp_2277_:
{
lean_object* v___x_2284_; uint8_t v___x_2285_; 
v___x_2284_ = lean_array_get_size(v___y_2281_);
v___x_2285_ = lean_nat_dec_lt(v___y_2279_, v___x_2284_);
if (v___x_2285_ == 0)
{
v___y_2243_ = v___y_2278_;
v___y_2244_ = v___y_2280_;
v___y_2245_ = v___y_2282_;
v_a_2246_ = v_val_2283_;
goto v___jp_2242_;
}
else
{
lean_object* v___x_2286_; size_t v___x_2287_; size_t v___x_2288_; lean_object* v___x_2289_; 
v___x_2286_ = lean_box(0);
v___x_2287_ = ((size_t)0ULL);
v___x_2288_ = lean_usize_of_nat(v___x_2284_);
v___x_2289_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_2281_, v___x_2287_, v___x_2288_, v___x_2286_, v_a_2191_);
if (lean_obj_tag(v___x_2289_) == 0)
{
lean_dec_ref_known(v___x_2289_, 1);
v___y_2243_ = v___y_2278_;
v___y_2244_ = v___y_2280_;
v___y_2245_ = v___y_2282_;
v_a_2246_ = v_val_2283_;
goto v___jp_2242_;
}
else
{
lean_object* v_a_2290_; lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2297_; 
lean_dec(v_val_2283_);
lean_dec_ref(v___y_2282_);
lean_dec_ref(v___y_2280_);
lean_dec_ref(v___y_2278_);
lean_del_object(v___x_2207_);
lean_dec_ref(v_scope_2205_);
lean_dec(v_name_2204_);
lean_dec_ref(v_remoteUrl_2199_);
lean_dec_ref(v_name_2196_);
v_a_2290_ = lean_ctor_get(v___x_2289_, 0);
v_isSharedCheck_2297_ = !lean_is_exclusive(v___x_2289_);
if (v_isSharedCheck_2297_ == 0)
{
v___x_2292_ = v___x_2289_;
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
else
{
lean_inc(v_a_2290_);
lean_dec(v___x_2289_);
v___x_2292_ = lean_box(0);
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
v_resetjp_2291_:
{
lean_object* v___x_2295_; 
if (v_isShared_2293_ == 0)
{
v___x_2295_ = v___x_2292_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v_a_2290_);
v___x_2295_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
return v___x_2295_;
}
}
}
}
}
v___jp_2298_:
{
lean_object* v_pkgDir_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; uint8_t v___x_2308_; 
lean_inc_ref(v___y_2301_);
v_pkgDir_2302_ = l_Lake_joinRelative(v_wsDir_2195_, v___y_2301_);
lean_inc_ref(v_pkgDir_2302_);
v___x_2303_ = l_Lake_resolvePath(v_pkgDir_2302_);
v___x_2304_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2304_, 0, v___y_2299_);
lean_ctor_set(v___x_2304_, 1, v___y_2300_);
lean_ctor_set(v___x_2304_, 2, v_inputRev_x3f_2200_);
lean_ctor_set(v___x_2304_, 3, v_subDir_x3f_2201_);
v___x_2305_ = lean_unsigned_to_nat(0u);
v___x_2306_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_2307_ = lean_string_utf8_byte_size(v___x_2303_);
v___x_2308_ = lean_nat_dec_eq(v___x_2307_, v___x_2305_);
if (v___x_2308_ == 0)
{
lean_object* v___x_2309_; 
v___x_2309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2309_, 0, v___x_2303_);
v___y_2278_ = v___y_2301_;
v___y_2279_ = v___x_2305_;
v___y_2280_ = v_pkgDir_2302_;
v___y_2281_ = v___x_2306_;
v___y_2282_ = v___x_2304_;
v_val_2283_ = v___x_2309_;
goto v___jp_2277_;
}
else
{
lean_object* v___x_2310_; 
lean_dec_ref(v___x_2303_);
v___x_2310_ = lean_box(0);
v___y_2278_ = v___y_2301_;
v___y_2279_ = v___x_2305_;
v___y_2280_ = v_pkgDir_2302_;
v___y_2281_ = v___x_2306_;
v___y_2282_ = v___x_2304_;
v_val_2283_ = v___x_2310_;
goto v___jp_2277_;
}
}
v___jp_2311_:
{
if (lean_obj_tag(v_subDir_x3f_2201_) == 1)
{
lean_object* v_val_2314_; lean_object* v___x_2315_; 
v_val_2314_ = lean_ctor_get(v_subDir_x3f_2201_, 0);
lean_inc(v_val_2314_);
v___x_2315_ = l_Lake_joinRelative(v_relPkgDir_2197_, v_val_2314_);
v___y_2299_ = v___y_2312_;
v___y_2300_ = v_a_2313_;
v___y_2301_ = v___x_2315_;
goto v___jp_2298_;
}
else
{
v___y_2299_ = v___y_2312_;
v___y_2300_ = v_a_2313_;
v___y_2301_ = v_relPkgDir_2197_;
goto v___jp_2298_;
}
}
v___jp_2317_:
{
lean_object* v___x_2319_; 
lean_inc(v_inputRev_x3f_2200_);
lean_inc_ref(v___y_2318_);
lean_inc_ref(v_gitDir_2316_);
lean_inc_ref(v_name_2196_);
v___x_2319_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(v_a_2191_, v_name_2196_, v_gitDir_2316_, v___y_2318_, v_inputRev_x3f_2200_);
if (lean_obj_tag(v___x_2319_) == 0)
{
lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2369_; 
v_isSharedCheck_2369_ = !lean_is_exclusive(v___x_2319_);
if (v_isSharedCheck_2369_ == 0)
{
lean_object* v_unused_2370_; 
v_unused_2370_ = lean_ctor_get(v___x_2319_, 0);
lean_dec(v_unused_2370_);
v___x_2321_ = v___x_2319_;
v_isShared_2322_ = v_isSharedCheck_2369_;
goto v_resetjp_2320_;
}
else
{
lean_dec(v___x_2319_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2369_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; 
v___x_2323_ = lean_unsigned_to_nat(0u);
v___x_2324_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_2325_ = l_Lake_GitRepo_getHeadRevision(v_gitDir_2316_, v___x_2324_);
if (lean_obj_tag(v___x_2325_) == 0)
{
lean_object* v_a_2326_; lean_object* v_a_2327_; lean_object* v___x_2328_; uint8_t v___x_2329_; 
lean_del_object(v___x_2321_);
v_a_2326_ = lean_ctor_get(v___x_2325_, 0);
lean_inc(v_a_2326_);
v_a_2327_ = lean_ctor_get(v___x_2325_, 1);
lean_inc(v_a_2327_);
lean_dec_ref_known(v___x_2325_, 2);
v___x_2328_ = lean_array_get_size(v_a_2327_);
v___x_2329_ = lean_nat_dec_lt(v___x_2323_, v___x_2328_);
if (v___x_2329_ == 0)
{
lean_dec(v_a_2327_);
v___y_2312_ = v___y_2318_;
v_a_2313_ = v_a_2326_;
goto v___jp_2311_;
}
else
{
lean_object* v___x_2330_; size_t v___x_2331_; size_t v___x_2332_; lean_object* v___x_2333_; 
v___x_2330_ = lean_box(0);
v___x_2331_ = ((size_t)0ULL);
v___x_2332_ = lean_usize_of_nat(v___x_2328_);
v___x_2333_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_2327_, v___x_2331_, v___x_2332_, v___x_2330_, v_a_2191_);
lean_dec(v_a_2327_);
if (lean_obj_tag(v___x_2333_) == 0)
{
lean_dec_ref_known(v___x_2333_, 1);
v___y_2312_ = v___y_2318_;
v_a_2313_ = v_a_2326_;
goto v___jp_2311_;
}
else
{
lean_object* v_a_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2341_; 
lean_dec(v_a_2326_);
lean_dec_ref(v___y_2318_);
lean_del_object(v___x_2207_);
lean_dec_ref(v_scope_2205_);
lean_dec(v_name_2204_);
lean_dec(v_subDir_x3f_2201_);
lean_dec(v_inputRev_x3f_2200_);
lean_dec_ref(v_remoteUrl_2199_);
lean_dec_ref(v_relPkgDir_2197_);
lean_dec_ref(v_name_2196_);
lean_dec_ref(v_wsDir_2195_);
v_a_2334_ = lean_ctor_get(v___x_2333_, 0);
v_isSharedCheck_2341_ = !lean_is_exclusive(v___x_2333_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2336_ = v___x_2333_;
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_a_2334_);
lean_dec(v___x_2333_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v___x_2339_; 
if (v_isShared_2337_ == 0)
{
v___x_2339_ = v___x_2336_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_a_2334_);
v___x_2339_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
return v___x_2339_;
}
}
}
}
}
else
{
lean_object* v_a_2342_; lean_object* v___x_2343_; uint8_t v___x_2344_; 
lean_dec_ref(v___y_2318_);
lean_del_object(v___x_2207_);
lean_dec_ref(v_scope_2205_);
lean_dec(v_name_2204_);
lean_dec(v_subDir_x3f_2201_);
lean_dec(v_inputRev_x3f_2200_);
lean_dec_ref(v_remoteUrl_2199_);
lean_dec_ref(v_relPkgDir_2197_);
lean_dec_ref(v_name_2196_);
lean_dec_ref(v_wsDir_2195_);
v_a_2342_ = lean_ctor_get(v___x_2325_, 1);
lean_inc(v_a_2342_);
lean_dec_ref_known(v___x_2325_, 2);
v___x_2343_ = lean_array_get_size(v_a_2342_);
v___x_2344_ = lean_nat_dec_lt(v___x_2323_, v___x_2343_);
if (v___x_2344_ == 0)
{
lean_object* v___x_2345_; lean_object* v___x_2347_; 
lean_dec(v_a_2342_);
v___x_2345_ = lean_box(0);
if (v_isShared_2322_ == 0)
{
lean_ctor_set_tag(v___x_2321_, 1);
lean_ctor_set(v___x_2321_, 0, v___x_2345_);
v___x_2347_ = v___x_2321_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v___x_2345_);
v___x_2347_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
return v___x_2347_;
}
}
else
{
lean_object* v___x_2349_; size_t v___x_2350_; size_t v___x_2351_; lean_object* v___x_2352_; 
lean_del_object(v___x_2321_);
v___x_2349_ = lean_box(0);
v___x_2350_ = ((size_t)0ULL);
v___x_2351_ = lean_usize_of_nat(v___x_2343_);
v___x_2352_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_2342_, v___x_2350_, v___x_2351_, v___x_2349_, v_a_2191_);
lean_dec(v_a_2342_);
if (lean_obj_tag(v___x_2352_) == 0)
{
lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2359_; 
v_isSharedCheck_2359_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2359_ == 0)
{
lean_object* v_unused_2360_; 
v_unused_2360_ = lean_ctor_get(v___x_2352_, 0);
lean_dec(v_unused_2360_);
v___x_2354_ = v___x_2352_;
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
else
{
lean_dec(v___x_2352_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2357_; 
if (v_isShared_2355_ == 0)
{
lean_ctor_set_tag(v___x_2354_, 1);
lean_ctor_set(v___x_2354_, 0, v___x_2349_);
v___x_2357_ = v___x_2354_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v___x_2349_);
v___x_2357_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
return v___x_2357_;
}
}
}
else
{
lean_object* v_a_2361_; lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2368_; 
v_a_2361_ = lean_ctor_get(v___x_2352_, 0);
v_isSharedCheck_2368_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2368_ == 0)
{
v___x_2363_ = v___x_2352_;
v_isShared_2364_ = v_isSharedCheck_2368_;
goto v_resetjp_2362_;
}
else
{
lean_inc(v_a_2361_);
lean_dec(v___x_2352_);
v___x_2363_ = lean_box(0);
v_isShared_2364_ = v_isSharedCheck_2368_;
goto v_resetjp_2362_;
}
v_resetjp_2362_:
{
lean_object* v___x_2366_; 
if (v_isShared_2364_ == 0)
{
v___x_2366_ = v___x_2363_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v_a_2361_);
v___x_2366_ = v_reuseFailAlloc_2367_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
return v___x_2366_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2371_; lean_object* v___x_2373_; uint8_t v_isShared_2374_; uint8_t v_isSharedCheck_2378_; 
lean_dec_ref(v___y_2318_);
lean_dec_ref(v_gitDir_2316_);
lean_del_object(v___x_2207_);
lean_dec_ref(v_scope_2205_);
lean_dec(v_name_2204_);
lean_dec(v_subDir_x3f_2201_);
lean_dec(v_inputRev_x3f_2200_);
lean_dec_ref(v_remoteUrl_2199_);
lean_dec_ref(v_relPkgDir_2197_);
lean_dec_ref(v_name_2196_);
lean_dec_ref(v_wsDir_2195_);
v_a_2371_ = lean_ctor_get(v___x_2319_, 0);
v_isSharedCheck_2378_ = !lean_is_exclusive(v___x_2319_);
if (v_isSharedCheck_2378_ == 0)
{
v___x_2373_ = v___x_2319_;
v_isShared_2374_ = v_isSharedCheck_2378_;
goto v_resetjp_2372_;
}
else
{
lean_inc(v_a_2371_);
lean_dec(v___x_2319_);
v___x_2373_ = lean_box(0);
v_isShared_2374_ = v_isSharedCheck_2378_;
goto v_resetjp_2372_;
}
v_resetjp_2372_:
{
lean_object* v___x_2376_; 
if (v_isShared_2374_ == 0)
{
v___x_2376_ = v___x_2373_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v_a_2371_);
v___x_2376_ = v_reuseFailAlloc_2377_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
return v___x_2376_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0___boxed(lean_object* v_a_2385_, lean_object* v_dep_2386_, lean_object* v_inherited_2387_, lean_object* v_lakeEnv_2388_, lean_object* v_wsDir_2389_, lean_object* v_name_2390_, lean_object* v_relPkgDir_2391_, lean_object* v_gitUrl_2392_, lean_object* v_remoteUrl_2393_, lean_object* v_inputRev_x3f_2394_, lean_object* v_subDir_x3f_2395_, lean_object* v_a_2396_){
_start:
{
uint8_t v_inherited_boxed_2397_; lean_object* v_res_2398_; 
v_inherited_boxed_2397_ = lean_unbox(v_inherited_2387_);
v_res_2398_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(v_a_2385_, v_dep_2386_, v_inherited_boxed_2397_, v_lakeEnv_2388_, v_wsDir_2389_, v_name_2390_, v_relPkgDir_2391_, v_gitUrl_2392_, v_remoteUrl_2393_, v_inputRev_x3f_2394_, v_subDir_x3f_2395_);
lean_dec_ref(v_lakeEnv_2388_);
lean_dec_ref(v_a_2385_);
return v_res_2398_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(lean_object* v_ver_2402_, lean_object* v_as_2403_, size_t v_sz_2404_, size_t v_i_2405_, lean_object* v_b_2406_){
_start:
{
uint8_t v___x_2407_; 
v___x_2407_ = lean_usize_dec_lt(v_i_2405_, v_sz_2404_);
if (v___x_2407_ == 0)
{
lean_inc_ref(v_b_2406_);
return v_b_2406_;
}
else
{
lean_object* v_a_2408_; lean_object* v_version_2409_; lean_object* v___x_2410_; uint8_t v___x_2411_; 
v_a_2408_ = lean_array_uget_borrowed(v_as_2403_, v_i_2405_);
v_version_2409_ = lean_ctor_get(v_a_2408_, 0);
v___x_2410_ = lean_box(0);
v___x_2411_ = l_Lake_VerRange_test(v_ver_2402_, v_version_2409_);
if (v___x_2411_ == 0)
{
lean_object* v___x_2412_; size_t v___x_2413_; size_t v___x_2414_; 
v___x_2412_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___closed__0));
v___x_2413_ = ((size_t)1ULL);
v___x_2414_ = lean_usize_add(v_i_2405_, v___x_2413_);
v_i_2405_ = v___x_2414_;
v_b_2406_ = v___x_2412_;
goto _start;
}
else
{
lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; 
lean_inc(v_a_2408_);
v___x_2416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2416_, 0, v_a_2408_);
v___x_2417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2417_, 0, v___x_2416_);
v___x_2418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2418_, 0, v___x_2417_);
lean_ctor_set(v___x_2418_, 1, v___x_2410_);
return v___x_2418_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___boxed(lean_object* v_ver_2419_, lean_object* v_as_2420_, lean_object* v_sz_2421_, lean_object* v_i_2422_, lean_object* v_b_2423_){
_start:
{
size_t v_sz_boxed_2424_; size_t v_i_boxed_2425_; lean_object* v_res_2426_; 
v_sz_boxed_2424_ = lean_unbox_usize(v_sz_2421_);
lean_dec(v_sz_2421_);
v_i_boxed_2425_ = lean_unbox_usize(v_i_2422_);
lean_dec(v_i_2422_);
v_res_2426_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(v_ver_2419_, v_as_2420_, v_sz_boxed_2424_, v_i_boxed_2425_, v_b_2423_);
lean_dec_ref(v_b_2423_);
lean_dec_ref(v_as_2420_);
lean_dec_ref(v_ver_2419_);
return v_res_2426_;
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize(lean_object* v_dep_2436_, uint8_t v_inherited_2437_, lean_object* v_lakeEnv_2438_, lean_object* v_wsDir_2439_, lean_object* v_relPkgsDir_2440_, lean_object* v_relParentDir_2441_, lean_object* v_a_2442_){
_start:
{
lean_object* v___y_2445_; lean_object* v___y_2446_; lean_object* v___y_2456_; lean_object* v___y_2457_; lean_object* v___y_2458_; lean_object* v___y_2459_; lean_object* v___y_2460_; lean_object* v___y_2461_; lean_object* v___y_2465_; lean_object* v___y_2466_; lean_object* v___y_2467_; lean_object* v___y_2468_; lean_object* v___y_2469_; lean_object* v_a_2470_; lean_object* v_src_x3f_2473_; 
v_src_x3f_2473_ = lean_ctor_get(v_dep_2436_, 3);
lean_inc(v_src_x3f_2473_);
if (lean_obj_tag(v_src_x3f_2473_) == 1)
{
lean_object* v_val_2474_; lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2598_; 
v_val_2474_ = lean_ctor_get(v_src_x3f_2473_, 0);
v_isSharedCheck_2598_ = !lean_is_exclusive(v_src_x3f_2473_);
if (v_isSharedCheck_2598_ == 0)
{
v___x_2476_ = v_src_x3f_2473_;
v_isShared_2477_ = v_isSharedCheck_2598_;
goto v_resetjp_2475_;
}
else
{
lean_inc(v_val_2474_);
lean_dec(v_src_x3f_2473_);
v___x_2476_ = lean_box(0);
v_isShared_2477_ = v_isSharedCheck_2598_;
goto v_resetjp_2475_;
}
v_resetjp_2475_:
{
if (lean_obj_tag(v_val_2474_) == 0)
{
lean_object* v_name_2478_; lean_object* v_scope_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2581_; 
lean_dec_ref(v_relPkgsDir_2440_);
lean_dec_ref(v_lakeEnv_2438_);
v_name_2478_ = lean_ctor_get(v_dep_2436_, 0);
v_scope_2479_ = lean_ctor_get(v_dep_2436_, 1);
v_isSharedCheck_2581_ = !lean_is_exclusive(v_dep_2436_);
if (v_isSharedCheck_2581_ == 0)
{
lean_object* v_unused_2582_; lean_object* v_unused_2583_; lean_object* v_unused_2584_; 
v_unused_2582_ = lean_ctor_get(v_dep_2436_, 4);
lean_dec(v_unused_2582_);
v_unused_2583_ = lean_ctor_get(v_dep_2436_, 3);
lean_dec(v_unused_2583_);
v_unused_2584_ = lean_ctor_get(v_dep_2436_, 2);
lean_dec(v_unused_2584_);
v___x_2481_ = v_dep_2436_;
v_isShared_2482_ = v_isSharedCheck_2581_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_scope_2479_);
lean_inc(v_name_2478_);
lean_dec(v_dep_2436_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2581_;
goto v_resetjp_2480_;
}
v_resetjp_2480_:
{
lean_object* v_dir_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2580_; 
v_dir_2483_ = lean_ctor_get(v_val_2474_, 0);
v_isSharedCheck_2580_ = !lean_is_exclusive(v_val_2474_);
if (v_isSharedCheck_2580_ == 0)
{
v___x_2485_ = v_val_2474_;
v_isShared_2486_ = v_isSharedCheck_2580_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_dir_2483_);
lean_dec(v_val_2474_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2580_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v_relPkgDir_2487_; lean_object* v___x_2489_; 
v_relPkgDir_2487_ = l_Lake_joinRelative(v_relParentDir_2441_, v_dir_2483_);
lean_inc_ref(v_relPkgDir_2487_);
if (v_isShared_2486_ == 0)
{
lean_ctor_set(v___x_2485_, 0, v_relPkgDir_2487_);
v___x_2489_ = v___x_2485_;
goto v_reusejp_2488_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v_relPkgDir_2487_);
v___x_2489_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2488_;
}
v_reusejp_2488_:
{
lean_object* v_pkgDir_2490_; lean_object* v___x_2491_; uint8_t v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___y_2496_; lean_object* v_a_2497_; lean_object* v___y_2506_; lean_object* v___y_2507_; lean_object* v___y_2508_; lean_object* v_val_2509_; lean_object* v_a_2525_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v_val_2559_; lean_object* v___x_2573_; uint8_t v___x_2574_; 
lean_inc_ref(v_relPkgDir_2487_);
v_pkgDir_2490_ = l_Lake_joinRelative(v_wsDir_2439_, v_relPkgDir_2487_);
lean_inc_ref(v_pkgDir_2490_);
v___x_2491_ = l_Lake_resolvePath(v_pkgDir_2490_);
v___x_2492_ = 0;
lean_inc(v_name_2478_);
v___x_2493_ = l_Lean_Name_toString(v_name_2478_, v___x_2492_);
v___x_2494_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___x_2556_ = lean_unsigned_to_nat(0u);
v___x_2557_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_2573_ = lean_string_utf8_byte_size(v___x_2491_);
v___x_2574_ = lean_nat_dec_eq(v___x_2573_, v___x_2556_);
if (v___x_2574_ == 0)
{
lean_object* v___x_2576_; 
if (v_isShared_2477_ == 0)
{
lean_ctor_set(v___x_2476_, 0, v___x_2491_);
v___x_2576_ = v___x_2476_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v___x_2491_);
v___x_2576_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
v_val_2559_ = v___x_2576_;
goto v___jp_2558_;
}
}
else
{
lean_object* v___x_2578_; 
lean_dec_ref(v___x_2491_);
lean_del_object(v___x_2476_);
v___x_2578_ = lean_box(0);
v_val_2559_ = v___x_2578_;
goto v___jp_2558_;
}
v___jp_2495_:
{
lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2502_; 
v___x_2498_ = l_Lake_defaultConfigFile;
v___x_2499_ = lean_box(0);
v___x_2500_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_2500_, 0, v_name_2478_);
lean_ctor_set(v___x_2500_, 1, v_scope_2479_);
lean_ctor_set(v___x_2500_, 2, v___x_2498_);
lean_ctor_set(v___x_2500_, 3, v___x_2499_);
lean_ctor_set(v___x_2500_, 4, v___x_2489_);
lean_ctor_set_uint8(v___x_2500_, sizeof(void*)*5, v_inherited_2437_);
if (v_isShared_2482_ == 0)
{
lean_ctor_set(v___x_2481_, 4, v___x_2500_);
lean_ctor_set(v___x_2481_, 3, v_a_2497_);
lean_ctor_set(v___x_2481_, 2, v___x_2494_);
lean_ctor_set(v___x_2481_, 1, v_relPkgDir_2487_);
lean_ctor_set(v___x_2481_, 0, v___y_2496_);
v___x_2502_ = v___x_2481_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v___y_2496_);
lean_ctor_set(v_reuseFailAlloc_2504_, 1, v_relPkgDir_2487_);
lean_ctor_set(v_reuseFailAlloc_2504_, 2, v___x_2494_);
lean_ctor_set(v_reuseFailAlloc_2504_, 3, v_a_2497_);
lean_ctor_set(v_reuseFailAlloc_2504_, 4, v___x_2500_);
v___x_2502_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
lean_object* v___x_2503_; 
v___x_2503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2503_, 0, v___x_2502_);
return v___x_2503_;
}
}
v___jp_2505_:
{
lean_object* v___x_2510_; uint8_t v___x_2511_; 
v___x_2510_ = lean_array_get_size(v___y_2508_);
v___x_2511_ = lean_nat_dec_lt(v___y_2507_, v___x_2510_);
if (v___x_2511_ == 0)
{
v___y_2496_ = v___y_2506_;
v_a_2497_ = v_val_2509_;
goto v___jp_2495_;
}
else
{
lean_object* v___x_2512_; size_t v___x_2513_; size_t v___x_2514_; lean_object* v___x_2515_; 
v___x_2512_ = lean_box(0);
v___x_2513_ = ((size_t)0ULL);
v___x_2514_ = lean_usize_of_nat(v___x_2510_);
v___x_2515_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_2508_, v___x_2513_, v___x_2514_, v___x_2512_, v_a_2442_);
if (lean_obj_tag(v___x_2515_) == 0)
{
lean_dec_ref_known(v___x_2515_, 1);
v___y_2496_ = v___y_2506_;
v_a_2497_ = v_val_2509_;
goto v___jp_2495_;
}
else
{
lean_object* v_a_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2523_; 
lean_dec_ref(v_val_2509_);
lean_dec_ref(v___y_2506_);
lean_dec_ref(v___x_2489_);
lean_dec_ref(v_relPkgDir_2487_);
lean_del_object(v___x_2481_);
lean_dec_ref(v_scope_2479_);
lean_dec(v_name_2478_);
v_a_2516_ = lean_ctor_get(v___x_2515_, 0);
v_isSharedCheck_2523_ = !lean_is_exclusive(v___x_2515_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2518_ = v___x_2515_;
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_a_2516_);
lean_dec(v___x_2515_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v___x_2521_; 
if (v_isShared_2519_ == 0)
{
v___x_2521_ = v___x_2518_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v_a_2516_);
v___x_2521_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
return v___x_2521_;
}
}
}
}
}
v___jp_2524_:
{
if (lean_obj_tag(v_a_2525_) == 1)
{
lean_object* v_val_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; 
lean_dec_ref(v___x_2493_);
lean_dec_ref(v_pkgDir_2490_);
v_val_2526_ = lean_ctor_get(v_a_2525_, 0);
lean_inc_n(v_val_2526_, 2);
lean_dec_ref_known(v_a_2525_, 1);
v___x_2527_ = l_Lake_defaultManifestFile;
v___x_2528_ = l_Lake_joinRelative(v_val_2526_, v___x_2527_);
v___x_2529_ = lean_unsigned_to_nat(0u);
v___x_2530_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_2531_ = l_Lake_Manifest_load(v___x_2528_);
if (lean_obj_tag(v___x_2531_) == 0)
{
lean_object* v_a_2532_; lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2539_; 
v_a_2532_ = lean_ctor_get(v___x_2531_, 0);
v_isSharedCheck_2539_ = !lean_is_exclusive(v___x_2531_);
if (v_isSharedCheck_2539_ == 0)
{
v___x_2534_ = v___x_2531_;
v_isShared_2535_ = v_isSharedCheck_2539_;
goto v_resetjp_2533_;
}
else
{
lean_inc(v_a_2532_);
lean_dec(v___x_2531_);
v___x_2534_ = lean_box(0);
v_isShared_2535_ = v_isSharedCheck_2539_;
goto v_resetjp_2533_;
}
v_resetjp_2533_:
{
lean_object* v___x_2537_; 
if (v_isShared_2535_ == 0)
{
lean_ctor_set_tag(v___x_2534_, 1);
v___x_2537_ = v___x_2534_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v_a_2532_);
v___x_2537_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
v___y_2506_ = v_val_2526_;
v___y_2507_ = v___x_2529_;
v___y_2508_ = v___x_2530_;
v_val_2509_ = v___x_2537_;
goto v___jp_2505_;
}
}
}
else
{
lean_object* v_a_2540_; lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2547_; 
v_a_2540_ = lean_ctor_get(v___x_2531_, 0);
v_isSharedCheck_2547_ = !lean_is_exclusive(v___x_2531_);
if (v_isSharedCheck_2547_ == 0)
{
v___x_2542_ = v___x_2531_;
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
else
{
lean_inc(v_a_2540_);
lean_dec(v___x_2531_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
lean_object* v___x_2545_; 
if (v_isShared_2543_ == 0)
{
lean_ctor_set_tag(v___x_2542_, 0);
v___x_2545_ = v___x_2542_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v_a_2540_);
v___x_2545_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
v___y_2506_ = v_val_2526_;
v___y_2507_ = v___x_2529_;
v___y_2508_ = v___x_2530_;
v_val_2509_ = v___x_2545_;
goto v___jp_2505_;
}
}
}
}
else
{
lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; uint8_t v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; 
lean_dec(v_a_2525_);
lean_dec_ref(v___x_2489_);
lean_dec_ref(v_relPkgDir_2487_);
lean_del_object(v___x_2481_);
lean_dec_ref(v_scope_2479_);
lean_dec(v_name_2478_);
v___x_2548_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0));
v___x_2549_ = lean_string_append(v___x_2493_, v___x_2548_);
v___x_2550_ = lean_string_append(v___x_2549_, v_pkgDir_2490_);
lean_dec_ref(v_pkgDir_2490_);
v___x_2551_ = 3;
v___x_2552_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2552_, 0, v___x_2550_);
lean_ctor_set_uint8(v___x_2552_, sizeof(void*)*1, v___x_2551_);
lean_inc_ref(v_a_2442_);
v___x_2553_ = lean_apply_2(v_a_2442_, v___x_2552_, lean_box(0));
v___x_2554_ = lean_box(0);
v___x_2555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2555_, 0, v___x_2554_);
return v___x_2555_;
}
}
v___jp_2558_:
{
uint8_t v___x_2560_; 
v___x_2560_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_2560_ == 0)
{
v_a_2525_ = v_val_2559_;
goto v___jp_2524_;
}
else
{
lean_object* v___x_2561_; size_t v___x_2562_; size_t v___x_2563_; lean_object* v___x_2564_; 
v___x_2561_ = lean_box(0);
v___x_2562_ = ((size_t)0ULL);
v___x_2563_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_2564_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_2557_, v___x_2562_, v___x_2563_, v___x_2561_, v_a_2442_);
if (lean_obj_tag(v___x_2564_) == 0)
{
lean_dec_ref_known(v___x_2564_, 1);
v_a_2525_ = v_val_2559_;
goto v___jp_2524_;
}
else
{
lean_object* v_a_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2572_; 
lean_dec(v_val_2559_);
lean_dec_ref(v___x_2493_);
lean_dec_ref(v_pkgDir_2490_);
lean_dec_ref(v___x_2489_);
lean_dec_ref(v_relPkgDir_2487_);
lean_del_object(v___x_2481_);
lean_dec_ref(v_scope_2479_);
lean_dec(v_name_2478_);
v_a_2565_ = lean_ctor_get(v___x_2564_, 0);
v_isSharedCheck_2572_ = !lean_is_exclusive(v___x_2564_);
if (v_isSharedCheck_2572_ == 0)
{
v___x_2567_ = v___x_2564_;
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_a_2565_);
lean_dec(v___x_2564_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2570_; 
if (v_isShared_2568_ == 0)
{
v___x_2570_ = v___x_2567_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v_a_2565_);
v___x_2570_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
return v___x_2570_;
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
lean_object* v_name_2585_; lean_object* v_url_2586_; lean_object* v_rev_2587_; lean_object* v_subDir_2588_; lean_object* v___y_2590_; lean_object* v___x_2595_; 
lean_del_object(v___x_2476_);
lean_dec_ref(v_relParentDir_2441_);
v_name_2585_ = lean_ctor_get(v_dep_2436_, 0);
v_url_2586_ = lean_ctor_get(v_val_2474_, 0);
lean_inc_ref_n(v_url_2586_, 2);
v_rev_2587_ = lean_ctor_get(v_val_2474_, 1);
lean_inc(v_rev_2587_);
v_subDir_2588_ = lean_ctor_get(v_val_2474_, 2);
lean_inc(v_subDir_2588_);
lean_dec_ref_known(v_val_2474_, 3);
v___x_2595_ = l_Lake_Git_filterUrl_x3f(v_url_2586_);
if (lean_obj_tag(v___x_2595_) == 0)
{
lean_object* v___x_2596_; 
v___x_2596_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___y_2590_ = v___x_2596_;
goto v___jp_2589_;
}
else
{
lean_object* v_val_2597_; 
v_val_2597_ = lean_ctor_get(v___x_2595_, 0);
lean_inc(v_val_2597_);
lean_dec_ref_known(v___x_2595_, 1);
v___y_2590_ = v_val_2597_;
goto v___jp_2589_;
}
v___jp_2589_:
{
uint8_t v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; 
v___x_2591_ = 0;
lean_inc(v_name_2585_);
v___x_2592_ = l_Lean_Name_toString(v_name_2585_, v___x_2591_);
lean_inc_ref(v___x_2592_);
v___x_2593_ = l_Lake_joinRelative(v_relPkgsDir_2440_, v___x_2592_);
v___x_2594_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(v_a_2442_, v_dep_2436_, v_inherited_2437_, v_lakeEnv_2438_, v_wsDir_2439_, v___x_2592_, v___x_2593_, v_url_2586_, v___y_2590_, v_rev_2587_, v_subDir_2588_);
lean_dec_ref(v_lakeEnv_2438_);
return v___x_2594_;
}
}
}
}
else
{
lean_object* v_name_2599_; lean_object* v_scope_2600_; lean_object* v_version_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; uint8_t v___x_2604_; 
lean_dec(v_src_x3f_2473_);
lean_dec_ref(v_relParentDir_2441_);
v_name_2599_ = lean_ctor_get(v_dep_2436_, 0);
v_scope_2600_ = lean_ctor_get(v_dep_2436_, 1);
v_version_2601_ = lean_ctor_get(v_dep_2436_, 2);
v___x_2602_ = lean_string_utf8_byte_size(v_scope_2600_);
v___x_2603_ = lean_unsigned_to_nat(0u);
v___x_2604_ = lean_nat_dec_eq(v___x_2602_, v___x_2603_);
if (v___x_2604_ == 0)
{
lean_object* v___x_2605_; lean_object* v___y_2607_; lean_object* v___y_2623_; lean_object* v___y_2624_; lean_object* v___y_2625_; lean_object* v___y_2626_; lean_object* v___y_2627_; lean_object* v___y_2628_; lean_object* v_a_2629_; lean_object* v___y_2673_; lean_object* v___y_2674_; lean_object* v___y_2675_; lean_object* v___y_2676_; lean_object* v___y_2677_; lean_object* v___y_2678_; lean_object* v_fst_2679_; lean_object* v_snd_2680_; lean_object* v_a_2696_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v_fst_2803_; lean_object* v_snd_2804_; 
lean_inc(v_name_2599_);
v___x_2605_ = l_Lean_Name_toString(v_name_2599_, v___x_2604_);
v___x_2800_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v___x_2605_);
lean_inc_ref(v_scope_2600_);
lean_inc_ref(v_lakeEnv_2438_);
v___x_2801_ = l_Lake_Reservoir_fetchPkg_x3f(v_lakeEnv_2438_, v_scope_2600_, v___x_2605_, v___x_2800_);
if (lean_obj_tag(v___x_2801_) == 0)
{
lean_object* v_a_2819_; lean_object* v_a_2820_; lean_object* v___x_2821_; 
v_a_2819_ = lean_ctor_get(v___x_2801_, 0);
lean_inc(v_a_2819_);
v_a_2820_ = lean_ctor_get(v___x_2801_, 1);
lean_inc(v_a_2820_);
lean_dec_ref_known(v___x_2801_, 2);
v___x_2821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2821_, 0, v_a_2819_);
v_fst_2803_ = v___x_2821_;
v_snd_2804_ = v_a_2820_;
goto v___jp_2802_;
}
else
{
lean_object* v_a_2822_; lean_object* v_a_2823_; lean_object* v___x_2824_; 
v_a_2822_ = lean_ctor_get(v___x_2801_, 0);
lean_inc(v_a_2822_);
v_a_2823_ = lean_ctor_get(v___x_2801_, 1);
lean_inc(v_a_2823_);
lean_dec_ref_known(v___x_2801_, 2);
v___x_2824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2824_, 0, v_a_2822_);
v_fst_2803_ = v___x_2824_;
v_snd_2804_ = v_a_2823_;
goto v___jp_2802_;
}
v___jp_2606_:
{
lean_object* v_toString_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; uint8_t v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; 
v_toString_2608_ = lean_ctor_get(v___y_2607_, 0);
lean_inc_ref(v_toString_2608_);
lean_dec_ref(v___y_2607_);
v___x_2609_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
v___x_2610_ = lean_string_append(v_scope_2600_, v___x_2609_);
v___x_2611_ = lean_string_append(v___x_2610_, v___x_2605_);
lean_dec_ref(v___x_2605_);
v___x_2612_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__1));
v___x_2613_ = lean_string_append(v___x_2611_, v___x_2612_);
v___x_2614_ = lean_string_append(v___x_2613_, v_toString_2608_);
lean_dec_ref(v_toString_2608_);
v___x_2615_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__2));
v___x_2616_ = lean_string_append(v___x_2614_, v___x_2615_);
v___x_2617_ = 3;
v___x_2618_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2618_, 0, v___x_2616_);
lean_ctor_set_uint8(v___x_2618_, sizeof(void*)*1, v___x_2617_);
lean_inc_ref(v_a_2442_);
v___x_2619_ = lean_apply_2(v_a_2442_, v___x_2618_, lean_box(0));
v___x_2620_ = lean_box(0);
v___x_2621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2621_, 0, v___x_2620_);
return v___x_2621_;
}
v___jp_2622_:
{
if (lean_obj_tag(v_a_2629_) == 0)
{
lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2645_; 
lean_inc_ref(v_scope_2600_);
lean_dec_ref(v___y_2628_);
lean_dec_ref(v___y_2627_);
lean_dec_ref(v___y_2626_);
lean_dec_ref(v___y_2625_);
lean_dec(v___y_2624_);
lean_dec(v___y_2623_);
lean_dec_ref(v_wsDir_2439_);
lean_dec_ref(v_lakeEnv_2438_);
lean_dec_ref(v_dep_2436_);
v_isSharedCheck_2645_ = !lean_is_exclusive(v_a_2629_);
if (v_isSharedCheck_2645_ == 0)
{
lean_object* v_unused_2646_; 
v_unused_2646_ = lean_ctor_get(v_a_2629_, 0);
lean_dec(v_unused_2646_);
v___x_2631_ = v_a_2629_;
v_isShared_2632_ = v_isSharedCheck_2645_;
goto v_resetjp_2630_;
}
else
{
lean_dec(v_a_2629_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2645_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; uint8_t v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2643_; 
v___x_2633_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
v___x_2634_ = lean_string_append(v_scope_2600_, v___x_2633_);
v___x_2635_ = lean_string_append(v___x_2634_, v___x_2605_);
lean_dec_ref(v___x_2605_);
v___x_2636_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__3));
v___x_2637_ = lean_string_append(v___x_2635_, v___x_2636_);
v___x_2638_ = 3;
v___x_2639_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2639_, 0, v___x_2637_);
lean_ctor_set_uint8(v___x_2639_, sizeof(void*)*1, v___x_2638_);
lean_inc_ref(v_a_2442_);
v___x_2640_ = lean_apply_2(v_a_2442_, v___x_2639_, lean_box(0));
v___x_2641_ = lean_box(0);
if (v_isShared_2632_ == 0)
{
lean_ctor_set_tag(v___x_2631_, 1);
lean_ctor_set(v___x_2631_, 0, v___x_2641_);
v___x_2643_ = v___x_2631_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v___x_2641_);
v___x_2643_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
return v___x_2643_;
}
}
}
else
{
lean_object* v_a_2647_; lean_object* v___x_2648_; size_t v_sz_2649_; size_t v___x_2650_; lean_object* v___x_2651_; lean_object* v_fst_2652_; 
v_a_2647_ = lean_ctor_get(v_a_2629_, 0);
lean_inc(v_a_2647_);
lean_dec_ref_known(v_a_2629_, 1);
v___x_2648_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___closed__0));
v_sz_2649_ = lean_array_size(v_a_2647_);
v___x_2650_ = ((size_t)0ULL);
v___x_2651_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(v___y_2628_, v_a_2647_, v_sz_2649_, v___x_2650_, v___x_2648_);
lean_dec(v_a_2647_);
v_fst_2652_ = lean_ctor_get(v___x_2651_, 0);
lean_inc(v_fst_2652_);
lean_dec_ref(v___x_2651_);
if (lean_obj_tag(v_fst_2652_) == 0)
{
lean_inc_ref(v_scope_2600_);
lean_dec_ref(v___y_2627_);
lean_dec_ref(v___y_2626_);
lean_dec_ref(v___y_2625_);
lean_dec(v___y_2624_);
lean_dec(v___y_2623_);
lean_dec_ref(v_wsDir_2439_);
lean_dec_ref(v_lakeEnv_2438_);
lean_dec_ref(v_dep_2436_);
v___y_2607_ = v___y_2628_;
goto v___jp_2606_;
}
else
{
lean_object* v_val_2653_; 
v_val_2653_ = lean_ctor_get(v_fst_2652_, 0);
lean_inc(v_val_2653_);
lean_dec_ref_known(v_fst_2652_, 1);
if (lean_obj_tag(v_val_2653_) == 1)
{
lean_object* v_val_2654_; lean_object* v_version_2655_; lean_object* v_revision_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; uint8_t v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; 
lean_dec_ref(v___y_2628_);
v_val_2654_ = lean_ctor_get(v_val_2653_, 0);
lean_inc(v_val_2654_);
lean_dec_ref_known(v_val_2653_, 1);
v_version_2655_ = lean_ctor_get(v_val_2654_, 0);
lean_inc_ref(v_version_2655_);
v_revision_2656_ = lean_ctor_get(v_val_2654_, 1);
lean_inc_ref(v_revision_2656_);
lean_dec(v_val_2654_);
v___x_2657_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
lean_inc_ref(v_scope_2600_);
v___x_2658_ = lean_string_append(v_scope_2600_, v___x_2657_);
v___x_2659_ = lean_string_append(v___x_2658_, v___x_2605_);
lean_dec_ref(v___x_2605_);
v___x_2660_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__4));
v___x_2661_ = lean_string_append(v___x_2659_, v___x_2660_);
v___x_2662_ = l_Lake_StdVer_toString(v_version_2655_);
v___x_2663_ = lean_string_append(v___x_2661_, v___x_2662_);
lean_dec_ref(v___x_2662_);
v___x_2664_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__5));
v___x_2665_ = lean_string_append(v___x_2663_, v___x_2664_);
v___x_2666_ = lean_string_append(v___x_2665_, v_revision_2656_);
v___x_2667_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__6));
v___x_2668_ = lean_string_append(v___x_2666_, v___x_2667_);
v___x_2669_ = 1;
v___x_2670_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2670_, 0, v___x_2668_);
lean_ctor_set_uint8(v___x_2670_, sizeof(void*)*1, v___x_2669_);
lean_inc_ref(v_a_2442_);
v___x_2671_ = lean_apply_2(v_a_2442_, v___x_2670_, lean_box(0));
v___y_2465_ = v___y_2624_;
v___y_2466_ = v___y_2623_;
v___y_2467_ = v___y_2625_;
v___y_2468_ = v___y_2626_;
v___y_2469_ = v___y_2627_;
v_a_2470_ = v_revision_2656_;
goto v___jp_2464_;
}
else
{
lean_inc_ref(v_scope_2600_);
lean_dec(v_val_2653_);
lean_dec_ref(v___y_2627_);
lean_dec_ref(v___y_2626_);
lean_dec_ref(v___y_2625_);
lean_dec(v___y_2624_);
lean_dec(v___y_2623_);
lean_dec_ref(v_wsDir_2439_);
lean_dec_ref(v_lakeEnv_2438_);
lean_dec_ref(v_dep_2436_);
v___y_2607_ = v___y_2628_;
goto v___jp_2606_;
}
}
}
}
v___jp_2672_:
{
lean_object* v___x_2681_; uint8_t v___x_2682_; 
v___x_2681_ = lean_array_get_size(v_snd_2680_);
v___x_2682_ = lean_nat_dec_lt(v___x_2603_, v___x_2681_);
if (v___x_2682_ == 0)
{
lean_dec_ref(v_snd_2680_);
v___y_2623_ = v___y_2674_;
v___y_2624_ = v___y_2673_;
v___y_2625_ = v___y_2675_;
v___y_2626_ = v___y_2676_;
v___y_2627_ = v___y_2678_;
v___y_2628_ = v___y_2677_;
v_a_2629_ = v_fst_2679_;
goto v___jp_2622_;
}
else
{
lean_object* v___x_2683_; size_t v___x_2684_; size_t v___x_2685_; lean_object* v___x_2686_; 
v___x_2683_ = lean_box(0);
v___x_2684_ = ((size_t)0ULL);
v___x_2685_ = lean_usize_of_nat(v___x_2681_);
v___x_2686_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_snd_2680_, v___x_2684_, v___x_2685_, v___x_2683_, v_a_2442_);
lean_dec_ref(v_snd_2680_);
if (lean_obj_tag(v___x_2686_) == 0)
{
lean_dec_ref_known(v___x_2686_, 1);
v___y_2623_ = v___y_2674_;
v___y_2624_ = v___y_2673_;
v___y_2625_ = v___y_2675_;
v___y_2626_ = v___y_2676_;
v___y_2627_ = v___y_2678_;
v___y_2628_ = v___y_2677_;
v_a_2629_ = v_fst_2679_;
goto v___jp_2622_;
}
else
{
lean_object* v_a_2687_; lean_object* v___x_2689_; uint8_t v_isShared_2690_; uint8_t v_isSharedCheck_2694_; 
lean_dec_ref(v_fst_2679_);
lean_dec_ref(v___y_2678_);
lean_dec_ref(v___y_2677_);
lean_dec_ref(v___y_2676_);
lean_dec_ref(v___y_2675_);
lean_dec(v___y_2674_);
lean_dec(v___y_2673_);
lean_dec_ref(v___x_2605_);
lean_dec_ref(v_wsDir_2439_);
lean_dec_ref(v_lakeEnv_2438_);
lean_dec_ref(v_dep_2436_);
v_a_2687_ = lean_ctor_get(v___x_2686_, 0);
v_isSharedCheck_2694_ = !lean_is_exclusive(v___x_2686_);
if (v_isSharedCheck_2694_ == 0)
{
v___x_2689_ = v___x_2686_;
v_isShared_2690_ = v_isSharedCheck_2694_;
goto v_resetjp_2688_;
}
else
{
lean_inc(v_a_2687_);
lean_dec(v___x_2686_);
v___x_2689_ = lean_box(0);
v_isShared_2690_ = v_isSharedCheck_2694_;
goto v_resetjp_2688_;
}
v_resetjp_2688_:
{
lean_object* v___x_2692_; 
if (v_isShared_2690_ == 0)
{
v___x_2692_ = v___x_2689_;
goto v_reusejp_2691_;
}
else
{
lean_object* v_reuseFailAlloc_2693_; 
v_reuseFailAlloc_2693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2693_, 0, v_a_2687_);
v___x_2692_ = v_reuseFailAlloc_2693_;
goto v_reusejp_2691_;
}
v_reusejp_2691_:
{
return v___x_2692_;
}
}
}
}
}
v___jp_2695_:
{
if (lean_obj_tag(v_a_2696_) == 0)
{
lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; uint8_t v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; 
lean_inc_ref(v_scope_2600_);
lean_dec_ref_known(v_a_2696_, 1);
lean_dec_ref(v_relPkgsDir_2440_);
lean_dec_ref(v_wsDir_2439_);
lean_dec_ref(v_lakeEnv_2438_);
lean_dec_ref(v_dep_2436_);
v___x_2697_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
v___x_2698_ = lean_string_append(v_scope_2600_, v___x_2697_);
v___x_2699_ = lean_string_append(v___x_2698_, v___x_2605_);
lean_dec_ref(v___x_2605_);
v___x_2700_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__7));
v___x_2701_ = lean_string_append(v___x_2699_, v___x_2700_);
v___x_2702_ = 3;
v___x_2703_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2703_, 0, v___x_2701_);
lean_ctor_set_uint8(v___x_2703_, sizeof(void*)*1, v___x_2702_);
lean_inc_ref(v_a_2442_);
v___x_2704_ = lean_apply_2(v_a_2442_, v___x_2703_, lean_box(0));
v___x_2705_ = lean_box(0);
v___x_2706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2706_, 0, v___x_2705_);
return v___x_2706_;
}
else
{
lean_object* v_a_2707_; lean_object* v___x_2709_; uint8_t v_isShared_2710_; uint8_t v_isSharedCheck_2799_; 
v_a_2707_ = lean_ctor_get(v_a_2696_, 0);
v_isSharedCheck_2799_ = !lean_is_exclusive(v_a_2696_);
if (v_isSharedCheck_2799_ == 0)
{
v___x_2709_ = v_a_2696_;
v_isShared_2710_ = v_isSharedCheck_2799_;
goto v_resetjp_2708_;
}
else
{
lean_inc(v_a_2707_);
lean_dec(v_a_2696_);
v___x_2709_ = lean_box(0);
v_isShared_2710_ = v_isSharedCheck_2799_;
goto v_resetjp_2708_;
}
v_resetjp_2708_:
{
if (lean_obj_tag(v_a_2707_) == 0)
{
lean_object* v___x_2711_; uint8_t v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; 
lean_del_object(v___x_2709_);
lean_dec_ref(v___x_2605_);
lean_dec_ref(v_relPkgsDir_2440_);
lean_dec_ref(v_wsDir_2439_);
lean_dec_ref(v_lakeEnv_2438_);
v___x_2711_ = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed(v_dep_2436_);
v___x_2712_ = 3;
v___x_2713_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2713_, 0, v___x_2711_);
lean_ctor_set_uint8(v___x_2713_, sizeof(void*)*1, v___x_2712_);
lean_inc_ref(v_a_2442_);
v___x_2714_ = lean_apply_2(v_a_2442_, v___x_2713_, lean_box(0));
v___x_2715_ = lean_box(0);
v___x_2716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2716_, 0, v___x_2715_);
return v___x_2716_;
}
else
{
lean_object* v_val_2717_; lean_object* v___x_2718_; 
v_val_2717_ = lean_ctor_get(v_a_2707_, 0);
lean_inc(v_val_2717_);
lean_dec_ref_known(v_a_2707_, 1);
v___x_2718_ = l_Lake_RegistryPkg_gitSrc_x3f(v_val_2717_);
if (lean_obj_tag(v___x_2718_) == 1)
{
lean_object* v_val_2719_; lean_object* v___x_2721_; uint8_t v_isShared_2722_; uint8_t v_isSharedCheck_2798_; 
v_val_2719_ = lean_ctor_get(v___x_2718_, 0);
v_isSharedCheck_2798_ = !lean_is_exclusive(v___x_2718_);
if (v_isSharedCheck_2798_ == 0)
{
v___x_2721_ = v___x_2718_;
v_isShared_2722_ = v_isSharedCheck_2798_;
goto v_resetjp_2720_;
}
else
{
lean_inc(v_val_2719_);
lean_dec(v___x_2718_);
v___x_2721_ = lean_box(0);
v_isShared_2722_ = v_isSharedCheck_2798_;
goto v_resetjp_2720_;
}
v_resetjp_2720_:
{
if (lean_obj_tag(v_val_2719_) == 0)
{
lean_object* v_url_2723_; lean_object* v_githubUrl_x3f_2724_; lean_object* v_defaultBranch_x3f_2725_; lean_object* v_subDir_x3f_2726_; lean_object* v_name_2727_; lean_object* v_fullName_2728_; lean_object* v___x_2729_; 
v_url_2723_ = lean_ctor_get(v_val_2719_, 1);
lean_inc_ref(v_url_2723_);
v_githubUrl_x3f_2724_ = lean_ctor_get(v_val_2719_, 2);
lean_inc(v_githubUrl_x3f_2724_);
v_defaultBranch_x3f_2725_ = lean_ctor_get(v_val_2719_, 3);
lean_inc(v_defaultBranch_x3f_2725_);
v_subDir_x3f_2726_ = lean_ctor_get(v_val_2719_, 4);
lean_inc(v_subDir_x3f_2726_);
lean_dec_ref_known(v_val_2719_, 5);
v_name_2727_ = lean_ctor_get(v_val_2717_, 0);
lean_inc_ref(v_name_2727_);
v_fullName_2728_ = lean_ctor_get(v_val_2717_, 1);
lean_inc_ref(v_fullName_2728_);
lean_dec(v_val_2717_);
v___x_2729_ = l_Lake_joinRelative(v_relPkgsDir_2440_, v_name_2727_);
switch(lean_obj_tag(v_version_2601_))
{
case 0:
{
lean_object* v___x_2730_; 
lean_del_object(v___x_2709_);
lean_dec_ref(v___x_2605_);
v___x_2730_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
if (lean_obj_tag(v_defaultBranch_x3f_2725_) == 0)
{
uint8_t v___x_2731_; 
lean_dec_ref(v___x_2729_);
lean_dec_ref(v_fullName_2728_);
lean_dec(v_subDir_x3f_2726_);
lean_dec(v_githubUrl_x3f_2724_);
lean_dec_ref(v_url_2723_);
lean_dec_ref(v_wsDir_2439_);
lean_dec_ref(v_lakeEnv_2438_);
lean_dec_ref(v_dep_2436_);
v___x_2731_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_2731_ == 0)
{
lean_object* v___x_2732_; lean_object* v___x_2734_; 
v___x_2732_ = lean_box(0);
if (v_isShared_2722_ == 0)
{
lean_ctor_set(v___x_2721_, 0, v___x_2732_);
v___x_2734_ = v___x_2721_;
goto v_reusejp_2733_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v___x_2732_);
v___x_2734_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2733_;
}
v_reusejp_2733_:
{
return v___x_2734_;
}
}
else
{
lean_object* v___x_2736_; size_t v___x_2737_; size_t v___x_2738_; lean_object* v___x_2739_; 
lean_del_object(v___x_2721_);
v___x_2736_ = lean_box(0);
v___x_2737_ = ((size_t)0ULL);
v___x_2738_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_2739_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_2730_, v___x_2737_, v___x_2738_, v___x_2736_, v_a_2442_);
if (lean_obj_tag(v___x_2739_) == 0)
{
lean_object* v___x_2741_; uint8_t v_isShared_2742_; uint8_t v_isSharedCheck_2746_; 
v_isSharedCheck_2746_ = !lean_is_exclusive(v___x_2739_);
if (v_isSharedCheck_2746_ == 0)
{
lean_object* v_unused_2747_; 
v_unused_2747_ = lean_ctor_get(v___x_2739_, 0);
lean_dec(v_unused_2747_);
v___x_2741_ = v___x_2739_;
v_isShared_2742_ = v_isSharedCheck_2746_;
goto v_resetjp_2740_;
}
else
{
lean_dec(v___x_2739_);
v___x_2741_ = lean_box(0);
v_isShared_2742_ = v_isSharedCheck_2746_;
goto v_resetjp_2740_;
}
v_resetjp_2740_:
{
lean_object* v___x_2744_; 
if (v_isShared_2742_ == 0)
{
lean_ctor_set_tag(v___x_2741_, 1);
lean_ctor_set(v___x_2741_, 0, v___x_2736_);
v___x_2744_ = v___x_2741_;
goto v_reusejp_2743_;
}
else
{
lean_object* v_reuseFailAlloc_2745_; 
v_reuseFailAlloc_2745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2745_, 0, v___x_2736_);
v___x_2744_ = v_reuseFailAlloc_2745_;
goto v_reusejp_2743_;
}
v_reusejp_2743_:
{
return v___x_2744_;
}
}
}
else
{
lean_object* v_a_2748_; lean_object* v___x_2750_; uint8_t v_isShared_2751_; uint8_t v_isSharedCheck_2755_; 
v_a_2748_ = lean_ctor_get(v___x_2739_, 0);
v_isSharedCheck_2755_ = !lean_is_exclusive(v___x_2739_);
if (v_isSharedCheck_2755_ == 0)
{
v___x_2750_ = v___x_2739_;
v_isShared_2751_ = v_isSharedCheck_2755_;
goto v_resetjp_2749_;
}
else
{
lean_inc(v_a_2748_);
lean_dec(v___x_2739_);
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
else
{
lean_object* v_val_2756_; uint8_t v___x_2757_; 
lean_del_object(v___x_2721_);
v_val_2756_ = lean_ctor_get(v_defaultBranch_x3f_2725_, 0);
lean_inc(v_val_2756_);
lean_dec_ref_known(v_defaultBranch_x3f_2725_, 1);
v___x_2757_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_2757_ == 0)
{
v___y_2465_ = v_githubUrl_x3f_2724_;
v___y_2466_ = v_subDir_x3f_2726_;
v___y_2467_ = v_url_2723_;
v___y_2468_ = v___x_2729_;
v___y_2469_ = v_fullName_2728_;
v_a_2470_ = v_val_2756_;
goto v___jp_2464_;
}
else
{
lean_object* v___x_2758_; size_t v___x_2759_; size_t v___x_2760_; lean_object* v___x_2761_; 
v___x_2758_ = lean_box(0);
v___x_2759_ = ((size_t)0ULL);
v___x_2760_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_2761_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_2730_, v___x_2759_, v___x_2760_, v___x_2758_, v_a_2442_);
if (lean_obj_tag(v___x_2761_) == 0)
{
lean_dec_ref_known(v___x_2761_, 1);
v___y_2465_ = v_githubUrl_x3f_2724_;
v___y_2466_ = v_subDir_x3f_2726_;
v___y_2467_ = v_url_2723_;
v___y_2468_ = v___x_2729_;
v___y_2469_ = v_fullName_2728_;
v_a_2470_ = v_val_2756_;
goto v___jp_2464_;
}
else
{
lean_object* v_a_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2769_; 
lean_dec(v_val_2756_);
lean_dec_ref(v___x_2729_);
lean_dec_ref(v_fullName_2728_);
lean_dec(v_subDir_x3f_2726_);
lean_dec(v_githubUrl_x3f_2724_);
lean_dec_ref(v_url_2723_);
lean_dec_ref(v_wsDir_2439_);
lean_dec_ref(v_lakeEnv_2438_);
lean_dec_ref(v_dep_2436_);
v_a_2762_ = lean_ctor_get(v___x_2761_, 0);
v_isSharedCheck_2769_ = !lean_is_exclusive(v___x_2761_);
if (v_isSharedCheck_2769_ == 0)
{
v___x_2764_ = v___x_2761_;
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_a_2762_);
lean_dec(v___x_2761_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
lean_object* v___x_2767_; 
if (v_isShared_2765_ == 0)
{
v___x_2767_ = v___x_2764_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v_a_2762_);
v___x_2767_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
return v___x_2767_;
}
}
}
}
}
}
case 1:
{
lean_object* v_rev_2770_; lean_object* v___x_2771_; uint8_t v___x_2772_; 
lean_dec(v_defaultBranch_x3f_2725_);
lean_del_object(v___x_2721_);
lean_del_object(v___x_2709_);
lean_dec_ref(v___x_2605_);
v_rev_2770_ = lean_ctor_get(v_version_2601_, 0);
v___x_2771_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_2772_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_2772_ == 0)
{
lean_inc_ref(v_rev_2770_);
v___y_2465_ = v_githubUrl_x3f_2724_;
v___y_2466_ = v_subDir_x3f_2726_;
v___y_2467_ = v_url_2723_;
v___y_2468_ = v___x_2729_;
v___y_2469_ = v_fullName_2728_;
v_a_2470_ = v_rev_2770_;
goto v___jp_2464_;
}
else
{
lean_object* v___x_2773_; size_t v___x_2774_; size_t v___x_2775_; lean_object* v___x_2776_; 
v___x_2773_ = lean_box(0);
v___x_2774_ = ((size_t)0ULL);
v___x_2775_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_2776_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_2771_, v___x_2774_, v___x_2775_, v___x_2773_, v_a_2442_);
if (lean_obj_tag(v___x_2776_) == 0)
{
lean_dec_ref_known(v___x_2776_, 1);
lean_inc_ref(v_rev_2770_);
v___y_2465_ = v_githubUrl_x3f_2724_;
v___y_2466_ = v_subDir_x3f_2726_;
v___y_2467_ = v_url_2723_;
v___y_2468_ = v___x_2729_;
v___y_2469_ = v_fullName_2728_;
v_a_2470_ = v_rev_2770_;
goto v___jp_2464_;
}
else
{
lean_object* v_a_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2784_; 
lean_dec_ref(v___x_2729_);
lean_dec_ref(v_fullName_2728_);
lean_dec(v_subDir_x3f_2726_);
lean_dec(v_githubUrl_x3f_2724_);
lean_dec_ref(v_url_2723_);
lean_dec_ref(v_wsDir_2439_);
lean_dec_ref(v_lakeEnv_2438_);
lean_dec_ref(v_dep_2436_);
v_a_2777_ = lean_ctor_get(v___x_2776_, 0);
v_isSharedCheck_2784_ = !lean_is_exclusive(v___x_2776_);
if (v_isSharedCheck_2784_ == 0)
{
v___x_2779_ = v___x_2776_;
v_isShared_2780_ = v_isSharedCheck_2784_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_a_2777_);
lean_dec(v___x_2776_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2784_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
lean_object* v___x_2782_; 
if (v_isShared_2780_ == 0)
{
v___x_2782_ = v___x_2779_;
goto v_reusejp_2781_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v_a_2777_);
v___x_2782_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2781_;
}
v_reusejp_2781_:
{
return v___x_2782_;
}
}
}
}
}
default: 
{
lean_object* v_ver_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; 
lean_dec(v_defaultBranch_x3f_2725_);
lean_del_object(v___x_2721_);
v_ver_2785_ = lean_ctor_get(v_version_2601_, 0);
v___x_2786_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v___x_2605_);
lean_inc_ref(v_scope_2600_);
lean_inc_ref(v_lakeEnv_2438_);
v___x_2787_ = l_Lake_Reservoir_fetchPkgVersions(v_lakeEnv_2438_, v_scope_2600_, v___x_2605_, v___x_2786_);
if (lean_obj_tag(v___x_2787_) == 0)
{
lean_object* v_a_2788_; lean_object* v_a_2789_; lean_object* v___x_2791_; 
v_a_2788_ = lean_ctor_get(v___x_2787_, 0);
lean_inc(v_a_2788_);
v_a_2789_ = lean_ctor_get(v___x_2787_, 1);
lean_inc(v_a_2789_);
lean_dec_ref_known(v___x_2787_, 2);
if (v_isShared_2710_ == 0)
{
lean_ctor_set(v___x_2709_, 0, v_a_2788_);
v___x_2791_ = v___x_2709_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v_a_2788_);
v___x_2791_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
lean_inc_ref(v_ver_2785_);
v___y_2673_ = v_githubUrl_x3f_2724_;
v___y_2674_ = v_subDir_x3f_2726_;
v___y_2675_ = v_url_2723_;
v___y_2676_ = v___x_2729_;
v___y_2677_ = v_ver_2785_;
v___y_2678_ = v_fullName_2728_;
v_fst_2679_ = v___x_2791_;
v_snd_2680_ = v_a_2789_;
goto v___jp_2672_;
}
}
else
{
lean_object* v_a_2793_; lean_object* v_a_2794_; lean_object* v___x_2796_; 
v_a_2793_ = lean_ctor_get(v___x_2787_, 0);
lean_inc(v_a_2793_);
v_a_2794_ = lean_ctor_get(v___x_2787_, 1);
lean_inc(v_a_2794_);
lean_dec_ref_known(v___x_2787_, 2);
if (v_isShared_2710_ == 0)
{
lean_ctor_set_tag(v___x_2709_, 0);
lean_ctor_set(v___x_2709_, 0, v_a_2793_);
v___x_2796_ = v___x_2709_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v_a_2793_);
v___x_2796_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
lean_inc_ref(v_ver_2785_);
v___y_2673_ = v_githubUrl_x3f_2724_;
v___y_2674_ = v_subDir_x3f_2726_;
v___y_2675_ = v_url_2723_;
v___y_2676_ = v___x_2729_;
v___y_2677_ = v_ver_2785_;
v___y_2678_ = v_fullName_2728_;
v_fst_2679_ = v___x_2796_;
v_snd_2680_ = v_a_2794_;
goto v___jp_2672_;
}
}
}
}
}
else
{
lean_del_object(v___x_2721_);
lean_dec(v_val_2719_);
lean_del_object(v___x_2709_);
lean_dec_ref(v___x_2605_);
lean_dec_ref(v_relPkgsDir_2440_);
lean_dec_ref(v_wsDir_2439_);
lean_dec_ref(v_lakeEnv_2438_);
lean_dec_ref(v_dep_2436_);
v___y_2445_ = v_val_2717_;
v___y_2446_ = v_a_2442_;
goto v___jp_2444_;
}
}
}
else
{
lean_dec(v___x_2718_);
lean_del_object(v___x_2709_);
lean_dec_ref(v___x_2605_);
lean_dec_ref(v_relPkgsDir_2440_);
lean_dec_ref(v_wsDir_2439_);
lean_dec_ref(v_lakeEnv_2438_);
lean_dec_ref(v_dep_2436_);
v___y_2445_ = v_val_2717_;
v___y_2446_ = v_a_2442_;
goto v___jp_2444_;
}
}
}
}
}
v___jp_2802_:
{
lean_object* v___x_2805_; uint8_t v___x_2806_; 
v___x_2805_ = lean_array_get_size(v_snd_2804_);
v___x_2806_ = lean_nat_dec_lt(v___x_2603_, v___x_2805_);
if (v___x_2806_ == 0)
{
lean_dec_ref(v_snd_2804_);
v_a_2696_ = v_fst_2803_;
goto v___jp_2695_;
}
else
{
lean_object* v___x_2807_; size_t v___x_2808_; size_t v___x_2809_; lean_object* v___x_2810_; 
v___x_2807_ = lean_box(0);
v___x_2808_ = ((size_t)0ULL);
v___x_2809_ = lean_usize_of_nat(v___x_2805_);
v___x_2810_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_snd_2804_, v___x_2808_, v___x_2809_, v___x_2807_, v_a_2442_);
lean_dec_ref(v_snd_2804_);
if (lean_obj_tag(v___x_2810_) == 0)
{
lean_dec_ref_known(v___x_2810_, 1);
v_a_2696_ = v_fst_2803_;
goto v___jp_2695_;
}
else
{
lean_object* v_a_2811_; lean_object* v___x_2813_; uint8_t v_isShared_2814_; uint8_t v_isSharedCheck_2818_; 
lean_dec_ref(v_fst_2803_);
lean_dec_ref(v___x_2605_);
lean_dec_ref(v_relPkgsDir_2440_);
lean_dec_ref(v_wsDir_2439_);
lean_dec_ref(v_lakeEnv_2438_);
lean_dec_ref(v_dep_2436_);
v_a_2811_ = lean_ctor_get(v___x_2810_, 0);
v_isSharedCheck_2818_ = !lean_is_exclusive(v___x_2810_);
if (v_isSharedCheck_2818_ == 0)
{
v___x_2813_ = v___x_2810_;
v_isShared_2814_ = v_isSharedCheck_2818_;
goto v_resetjp_2812_;
}
else
{
lean_inc(v_a_2811_);
lean_dec(v___x_2810_);
v___x_2813_ = lean_box(0);
v_isShared_2814_ = v_isSharedCheck_2818_;
goto v_resetjp_2812_;
}
v_resetjp_2812_:
{
lean_object* v___x_2816_; 
if (v_isShared_2814_ == 0)
{
v___x_2816_ = v___x_2813_;
goto v_reusejp_2815_;
}
else
{
lean_object* v_reuseFailAlloc_2817_; 
v_reuseFailAlloc_2817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2817_, 0, v_a_2811_);
v___x_2816_ = v_reuseFailAlloc_2817_;
goto v_reusejp_2815_;
}
v_reusejp_2815_:
{
return v___x_2816_;
}
}
}
}
}
}
else
{
uint8_t v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; uint8_t v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; 
lean_inc(v_name_2599_);
lean_dec_ref(v_relPkgsDir_2440_);
lean_dec_ref(v_wsDir_2439_);
lean_dec_ref(v_lakeEnv_2438_);
lean_dec_ref(v_dep_2436_);
v___x_2825_ = 0;
v___x_2826_ = l_Lean_Name_toString(v_name_2599_, v___x_2825_);
v___x_2827_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__8));
v___x_2828_ = lean_string_append(v___x_2826_, v___x_2827_);
v___x_2829_ = 3;
v___x_2830_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2830_, 0, v___x_2828_);
lean_ctor_set_uint8(v___x_2830_, sizeof(void*)*1, v___x_2829_);
lean_inc_ref(v_a_2442_);
v___x_2831_ = lean_apply_2(v_a_2442_, v___x_2830_, lean_box(0));
v___x_2832_ = lean_box(0);
v___x_2833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2833_, 0, v___x_2832_);
return v___x_2833_;
}
}
v___jp_2444_:
{
lean_object* v_fullName_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; uint8_t v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; 
v_fullName_2447_ = lean_ctor_get(v___y_2445_, 1);
lean_inc_ref(v_fullName_2447_);
lean_dec_ref(v___y_2445_);
v___x_2448_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__0));
v___x_2449_ = lean_string_append(v_fullName_2447_, v___x_2448_);
v___x_2450_ = 3;
v___x_2451_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2451_, 0, v___x_2449_);
lean_ctor_set_uint8(v___x_2451_, sizeof(void*)*1, v___x_2450_);
lean_inc_ref(v___y_2446_);
v___x_2452_ = lean_apply_2(v___y_2446_, v___x_2451_, lean_box(0));
v___x_2453_ = lean_box(0);
v___x_2454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2454_, 0, v___x_2453_);
return v___x_2454_;
}
v___jp_2455_:
{
lean_object* v___x_2462_; lean_object* v___x_2463_; 
v___x_2462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2462_, 0, v___y_2456_);
v___x_2463_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(v_a_2442_, v_dep_2436_, v_inherited_2437_, v_lakeEnv_2438_, v_wsDir_2439_, v___y_2460_, v___y_2459_, v___y_2458_, v___y_2461_, v___x_2462_, v___y_2457_);
lean_dec_ref(v_lakeEnv_2438_);
return v___x_2463_;
}
v___jp_2464_:
{
if (lean_obj_tag(v___y_2465_) == 0)
{
lean_object* v___x_2471_; 
v___x_2471_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___y_2456_ = v_a_2470_;
v___y_2457_ = v___y_2466_;
v___y_2458_ = v___y_2467_;
v___y_2459_ = v___y_2468_;
v___y_2460_ = v___y_2469_;
v___y_2461_ = v___x_2471_;
goto v___jp_2455_;
}
else
{
lean_object* v_val_2472_; 
v_val_2472_ = lean_ctor_get(v___y_2465_, 0);
lean_inc(v_val_2472_);
lean_dec_ref_known(v___y_2465_, 1);
v___y_2456_ = v_a_2470_;
v___y_2457_ = v___y_2466_;
v___y_2458_ = v___y_2467_;
v___y_2459_ = v___y_2468_;
v___y_2460_ = v___y_2469_;
v___y_2461_ = v_val_2472_;
goto v___jp_2455_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize___boxed(lean_object* v_dep_2834_, lean_object* v_inherited_2835_, lean_object* v_lakeEnv_2836_, lean_object* v_wsDir_2837_, lean_object* v_relPkgsDir_2838_, lean_object* v_relParentDir_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_){
_start:
{
uint8_t v_inherited_boxed_2842_; lean_object* v_res_2843_; 
v_inherited_boxed_2842_ = lean_unbox(v_inherited_2835_);
v_res_2843_ = l_Lake_Dependency_materialize(v_dep_2834_, v_inherited_boxed_2842_, v_lakeEnv_2836_, v_wsDir_2837_, v_relPkgsDir_2838_, v_relParentDir_2839_, v_a_2840_);
lean_dec_ref(v_a_2840_);
return v_res_2843_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep(lean_object* v_manifestEntry_2849_, lean_object* v_wsDir_2850_, lean_object* v_relPkgDir_2851_, lean_object* v_remoteUrl_2852_, lean_object* v_a_2853_){
_start:
{
lean_object* v___y_2856_; lean_object* v_a_2857_; lean_object* v_pkgDir_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___f_2863_; lean_object* v___y_2865_; lean_object* v___y_2866_; lean_object* v___y_2867_; lean_object* v___y_2868_; lean_object* v_val_2869_; lean_object* v_a_2886_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v_val_2926_; lean_object* v___x_2941_; uint8_t v___x_2942_; 
lean_inc_ref(v_relPkgDir_2851_);
v_pkgDir_2860_ = l_Lake_joinRelative(v_wsDir_2850_, v_relPkgDir_2851_);
v___x_2861_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__2, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__2_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__2);
lean_inc_ref(v_pkgDir_2860_);
v___x_2862_ = l_Lake_resolvePath(v_pkgDir_2860_);
v___f_2863_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3));
v___x_2923_ = lean_unsigned_to_nat(0u);
v___x_2924_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_2941_ = lean_string_utf8_byte_size(v___x_2862_);
v___x_2942_ = lean_nat_dec_eq(v___x_2941_, v___x_2923_);
if (v___x_2942_ == 0)
{
lean_object* v___x_2943_; 
v___x_2943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2943_, 0, v___x_2862_);
v_val_2926_ = v___x_2943_;
goto v___jp_2925_;
}
else
{
lean_object* v___x_2944_; 
lean_dec_ref(v___x_2862_);
v___x_2944_ = lean_box(0);
v_val_2926_ = v___x_2944_;
goto v___jp_2925_;
}
v___jp_2855_:
{
lean_object* v___x_2858_; lean_object* v___x_2859_; 
v___x_2858_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2858_, 0, v___y_2856_);
lean_ctor_set(v___x_2858_, 1, v_relPkgDir_2851_);
lean_ctor_set(v___x_2858_, 2, v_remoteUrl_2852_);
lean_ctor_set(v___x_2858_, 3, v_a_2857_);
lean_ctor_set(v___x_2858_, 4, v_manifestEntry_2849_);
v___x_2859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2859_, 0, v___x_2858_);
return v___x_2859_;
}
v___jp_2864_:
{
lean_object* v___x_2870_; uint8_t v___x_2871_; 
v___x_2870_ = lean_array_get_size(v___y_2866_);
v___x_2871_ = lean_nat_dec_lt(v___y_2868_, v___x_2870_);
if (v___x_2871_ == 0)
{
lean_dec_ref(v___y_2865_);
v___y_2856_ = v___y_2867_;
v_a_2857_ = v_val_2869_;
goto v___jp_2855_;
}
else
{
lean_object* v___x_2872_; size_t v___x_2873_; size_t v___x_2874_; lean_object* v___x_1877__overap_2875_; lean_object* v___x_2876_; 
v___x_2872_ = lean_box(0);
v___x_2873_ = ((size_t)0ULL);
v___x_2874_ = lean_usize_of_nat(v___x_2870_);
lean_inc_ref(v___y_2866_);
v___x_1877__overap_2875_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___y_2865_, v___f_2863_, v___y_2866_, v___x_2873_, v___x_2874_, v___x_2872_);
lean_inc_ref(v_a_2853_);
v___x_2876_ = lean_apply_2(v___x_1877__overap_2875_, v_a_2853_, lean_box(0));
if (lean_obj_tag(v___x_2876_) == 0)
{
lean_dec_ref_known(v___x_2876_, 1);
v___y_2856_ = v___y_2867_;
v_a_2857_ = v_val_2869_;
goto v___jp_2855_;
}
else
{
lean_object* v_a_2877_; lean_object* v___x_2879_; uint8_t v_isShared_2880_; uint8_t v_isSharedCheck_2884_; 
lean_dec_ref(v_val_2869_);
lean_dec_ref(v___y_2867_);
lean_dec_ref(v_remoteUrl_2852_);
lean_dec_ref(v_relPkgDir_2851_);
lean_dec_ref(v_manifestEntry_2849_);
v_a_2877_ = lean_ctor_get(v___x_2876_, 0);
v_isSharedCheck_2884_ = !lean_is_exclusive(v___x_2876_);
if (v_isSharedCheck_2884_ == 0)
{
v___x_2879_ = v___x_2876_;
v_isShared_2880_ = v_isSharedCheck_2884_;
goto v_resetjp_2878_;
}
else
{
lean_inc(v_a_2877_);
lean_dec(v___x_2876_);
v___x_2879_ = lean_box(0);
v_isShared_2880_ = v_isSharedCheck_2884_;
goto v_resetjp_2878_;
}
v_resetjp_2878_:
{
lean_object* v___x_2882_; 
if (v_isShared_2880_ == 0)
{
v___x_2882_ = v___x_2879_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2883_; 
v_reuseFailAlloc_2883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2883_, 0, v_a_2877_);
v___x_2882_ = v_reuseFailAlloc_2883_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
return v___x_2882_;
}
}
}
}
}
v___jp_2885_:
{
if (lean_obj_tag(v_a_2886_) == 1)
{
lean_object* v_manifestFile_x3f_2887_; 
lean_dec_ref(v_pkgDir_2860_);
v_manifestFile_x3f_2887_ = lean_ctor_get(v_manifestEntry_2849_, 3);
if (lean_obj_tag(v_manifestFile_x3f_2887_) == 1)
{
lean_object* v_val_2888_; lean_object* v_val_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; 
v_val_2888_ = lean_ctor_get(v_a_2886_, 0);
lean_inc_n(v_val_2888_, 2);
lean_dec_ref_known(v_a_2886_, 1);
v_val_2889_ = lean_ctor_get(v_manifestFile_x3f_2887_, 0);
lean_inc(v_val_2889_);
v___x_2890_ = l_Lake_joinRelative(v_val_2888_, v_val_2889_);
v___x_2891_ = lean_unsigned_to_nat(0u);
v___x_2892_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_2893_ = l_Lake_Manifest_load(v___x_2890_);
if (lean_obj_tag(v___x_2893_) == 0)
{
lean_object* v_a_2894_; lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2901_; 
v_a_2894_ = lean_ctor_get(v___x_2893_, 0);
v_isSharedCheck_2901_ = !lean_is_exclusive(v___x_2893_);
if (v_isSharedCheck_2901_ == 0)
{
v___x_2896_ = v___x_2893_;
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
else
{
lean_inc(v_a_2894_);
lean_dec(v___x_2893_);
v___x_2896_ = lean_box(0);
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
v_resetjp_2895_:
{
lean_object* v___x_2899_; 
if (v_isShared_2897_ == 0)
{
lean_ctor_set_tag(v___x_2896_, 1);
v___x_2899_ = v___x_2896_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v_a_2894_);
v___x_2899_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
v___y_2865_ = v___x_2861_;
v___y_2866_ = v___x_2892_;
v___y_2867_ = v_val_2888_;
v___y_2868_ = v___x_2891_;
v_val_2869_ = v___x_2899_;
goto v___jp_2864_;
}
}
}
else
{
lean_object* v_a_2902_; lean_object* v___x_2904_; uint8_t v_isShared_2905_; uint8_t v_isSharedCheck_2909_; 
v_a_2902_ = lean_ctor_get(v___x_2893_, 0);
v_isSharedCheck_2909_ = !lean_is_exclusive(v___x_2893_);
if (v_isSharedCheck_2909_ == 0)
{
v___x_2904_ = v___x_2893_;
v_isShared_2905_ = v_isSharedCheck_2909_;
goto v_resetjp_2903_;
}
else
{
lean_inc(v_a_2902_);
lean_dec(v___x_2893_);
v___x_2904_ = lean_box(0);
v_isShared_2905_ = v_isSharedCheck_2909_;
goto v_resetjp_2903_;
}
v_resetjp_2903_:
{
lean_object* v___x_2907_; 
if (v_isShared_2905_ == 0)
{
lean_ctor_set_tag(v___x_2904_, 0);
v___x_2907_ = v___x_2904_;
goto v_reusejp_2906_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v_a_2902_);
v___x_2907_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2906_;
}
v_reusejp_2906_:
{
v___y_2865_ = v___x_2861_;
v___y_2866_ = v___x_2892_;
v___y_2867_ = v_val_2888_;
v___y_2868_ = v___x_2891_;
v_val_2869_ = v___x_2907_;
goto v___jp_2864_;
}
}
}
}
else
{
lean_object* v_val_2910_; lean_object* v___x_2911_; 
v_val_2910_ = lean_ctor_get(v_a_2886_, 0);
lean_inc(v_val_2910_);
lean_dec_ref_known(v_a_2886_, 1);
v___x_2911_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1));
v___y_2856_ = v_val_2910_;
v_a_2857_ = v___x_2911_;
goto v___jp_2855_;
}
}
else
{
lean_object* v_name_2912_; uint8_t v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; uint8_t v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; 
lean_dec(v_a_2886_);
lean_dec_ref(v_remoteUrl_2852_);
lean_dec_ref(v_relPkgDir_2851_);
v_name_2912_ = lean_ctor_get(v_manifestEntry_2849_, 0);
lean_inc(v_name_2912_);
lean_dec_ref(v_manifestEntry_2849_);
v___x_2913_ = 0;
v___x_2914_ = l_Lean_Name_toString(v_name_2912_, v___x_2913_);
v___x_2915_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0));
v___x_2916_ = lean_string_append(v___x_2914_, v___x_2915_);
v___x_2917_ = lean_string_append(v___x_2916_, v_pkgDir_2860_);
lean_dec_ref(v_pkgDir_2860_);
v___x_2918_ = 3;
v___x_2919_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2919_, 0, v___x_2917_);
lean_ctor_set_uint8(v___x_2919_, sizeof(void*)*1, v___x_2918_);
lean_inc_ref(v_a_2853_);
v___x_2920_ = lean_apply_2(v_a_2853_, v___x_2919_, lean_box(0));
v___x_2921_ = lean_box(0);
v___x_2922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2922_, 0, v___x_2921_);
return v___x_2922_;
}
}
v___jp_2925_:
{
uint8_t v___x_2927_; 
v___x_2927_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_2927_ == 0)
{
v_a_2886_ = v_val_2926_;
goto v___jp_2885_;
}
else
{
lean_object* v___x_2928_; size_t v___x_2929_; size_t v___x_2930_; lean_object* v___x_1931__overap_2931_; lean_object* v___x_2932_; 
v___x_2928_ = lean_box(0);
v___x_2929_ = ((size_t)0ULL);
v___x_2930_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_1931__overap_2931_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2861_, v___f_2863_, v___x_2924_, v___x_2929_, v___x_2930_, v___x_2928_);
lean_inc_ref(v_a_2853_);
v___x_2932_ = lean_apply_2(v___x_1931__overap_2931_, v_a_2853_, lean_box(0));
if (lean_obj_tag(v___x_2932_) == 0)
{
lean_dec_ref_known(v___x_2932_, 1);
v_a_2886_ = v_val_2926_;
goto v___jp_2885_;
}
else
{
lean_object* v_a_2933_; lean_object* v___x_2935_; uint8_t v_isShared_2936_; uint8_t v_isSharedCheck_2940_; 
lean_dec(v_val_2926_);
lean_dec_ref(v_pkgDir_2860_);
lean_dec_ref(v_remoteUrl_2852_);
lean_dec_ref(v_relPkgDir_2851_);
lean_dec_ref(v_manifestEntry_2849_);
v_a_2933_ = lean_ctor_get(v___x_2932_, 0);
v_isSharedCheck_2940_ = !lean_is_exclusive(v___x_2932_);
if (v_isSharedCheck_2940_ == 0)
{
v___x_2935_ = v___x_2932_;
v_isShared_2936_ = v_isSharedCheck_2940_;
goto v_resetjp_2934_;
}
else
{
lean_inc(v_a_2933_);
lean_dec(v___x_2932_);
v___x_2935_ = lean_box(0);
v_isShared_2936_ = v_isSharedCheck_2940_;
goto v_resetjp_2934_;
}
v_resetjp_2934_:
{
lean_object* v___x_2938_; 
if (v_isShared_2936_ == 0)
{
v___x_2938_ = v___x_2935_;
goto v_reusejp_2937_;
}
else
{
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v_a_2933_);
v___x_2938_ = v_reuseFailAlloc_2939_;
goto v_reusejp_2937_;
}
v_reusejp_2937_:
{
return v___x_2938_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___boxed(lean_object* v_manifestEntry_2945_, lean_object* v_wsDir_2946_, lean_object* v_relPkgDir_2947_, lean_object* v_remoteUrl_2948_, lean_object* v_a_2949_, lean_object* v_a_2950_){
_start:
{
lean_object* v_res_2951_; 
v_res_2951_ = l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep(v_manifestEntry_2945_, v_wsDir_2946_, v_relPkgDir_2947_, v_remoteUrl_2948_, v_a_2949_);
lean_dec_ref(v_a_2949_);
return v_res_2951_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lake_PackageEntry_materialize_spec__0___redArg(lean_object* v_t_2952_, lean_object* v_k_2953_, lean_object* v_fallback_2954_){
_start:
{
if (lean_obj_tag(v_t_2952_) == 0)
{
lean_object* v_k_2955_; lean_object* v_v_2956_; lean_object* v_l_2957_; lean_object* v_r_2958_; uint8_t v___x_2959_; 
v_k_2955_ = lean_ctor_get(v_t_2952_, 1);
v_v_2956_ = lean_ctor_get(v_t_2952_, 2);
v_l_2957_ = lean_ctor_get(v_t_2952_, 3);
v_r_2958_ = lean_ctor_get(v_t_2952_, 4);
v___x_2959_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2953_, v_k_2955_);
switch(v___x_2959_)
{
case 0:
{
v_t_2952_ = v_l_2957_;
goto _start;
}
case 1:
{
lean_inc(v_v_2956_);
return v_v_2956_;
}
default: 
{
v_t_2952_ = v_r_2958_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_2954_);
return v_fallback_2954_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lake_PackageEntry_materialize_spec__0___redArg___boxed(lean_object* v_t_2962_, lean_object* v_k_2963_, lean_object* v_fallback_2964_){
_start:
{
lean_object* v_res_2965_; 
v_res_2965_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lake_PackageEntry_materialize_spec__0___redArg(v_t_2962_, v_k_2963_, v_fallback_2964_);
lean_dec(v_fallback_2964_);
lean_dec(v_k_2963_);
lean_dec(v_t_2962_);
return v_res_2965_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize(lean_object* v_manifestEntry_2966_, lean_object* v_lakeEnv_2967_, lean_object* v_wsDir_2968_, lean_object* v_relPkgsDir_2969_, lean_object* v_a_2970_){
_start:
{
lean_object* v___y_2973_; lean_object* v___y_2974_; lean_object* v___y_2975_; lean_object* v_a_2976_; lean_object* v___y_2980_; lean_object* v___y_2981_; lean_object* v___y_2982_; lean_object* v___y_2983_; lean_object* v___y_2984_; lean_object* v_val_2985_; lean_object* v_src_3000_; 
v_src_3000_ = lean_ctor_get(v_manifestEntry_2966_, 4);
lean_inc_ref(v_src_3000_);
if (lean_obj_tag(v_src_3000_) == 0)
{
lean_object* v_name_3001_; lean_object* v_manifestFile_x3f_3002_; lean_object* v_dir_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3093_; 
lean_dec_ref(v_relPkgsDir_2969_);
v_name_3001_ = lean_ctor_get(v_manifestEntry_2966_, 0);
v_manifestFile_x3f_3002_ = lean_ctor_get(v_manifestEntry_2966_, 3);
v_dir_3003_ = lean_ctor_get(v_src_3000_, 0);
v_isSharedCheck_3093_ = !lean_is_exclusive(v_src_3000_);
if (v_isSharedCheck_3093_ == 0)
{
v___x_3005_ = v_src_3000_;
v_isShared_3006_ = v_isSharedCheck_3093_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_dir_3003_);
lean_dec(v_src_3000_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3093_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
lean_object* v_pkgDir_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___y_3011_; lean_object* v_a_3012_; lean_object* v___y_3018_; lean_object* v___y_3019_; lean_object* v___y_3020_; lean_object* v_val_3021_; lean_object* v_a_3037_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v_val_3075_; lean_object* v___x_3089_; uint8_t v___x_3090_; 
lean_inc_ref(v_dir_3003_);
v_pkgDir_3007_ = l_Lake_joinRelative(v_wsDir_2968_, v_dir_3003_);
lean_inc_ref(v_pkgDir_3007_);
v___x_3008_ = l_Lake_resolvePath(v_pkgDir_3007_);
v___x_3009_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___x_3072_ = lean_unsigned_to_nat(0u);
v___x_3073_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_3089_ = lean_string_utf8_byte_size(v___x_3008_);
v___x_3090_ = lean_nat_dec_eq(v___x_3089_, v___x_3072_);
if (v___x_3090_ == 0)
{
lean_object* v___x_3091_; 
v___x_3091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3091_, 0, v___x_3008_);
v_val_3075_ = v___x_3091_;
goto v___jp_3074_;
}
else
{
lean_object* v___x_3092_; 
lean_dec_ref(v___x_3008_);
v___x_3092_ = lean_box(0);
v_val_3075_ = v___x_3092_;
goto v___jp_3074_;
}
v___jp_3010_:
{
lean_object* v___x_3013_; lean_object* v___x_3015_; 
v___x_3013_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3013_, 0, v___y_3011_);
lean_ctor_set(v___x_3013_, 1, v_dir_3003_);
lean_ctor_set(v___x_3013_, 2, v___x_3009_);
lean_ctor_set(v___x_3013_, 3, v_a_3012_);
lean_ctor_set(v___x_3013_, 4, v_manifestEntry_2966_);
if (v_isShared_3006_ == 0)
{
lean_ctor_set(v___x_3005_, 0, v___x_3013_);
v___x_3015_ = v___x_3005_;
goto v_reusejp_3014_;
}
else
{
lean_object* v_reuseFailAlloc_3016_; 
v_reuseFailAlloc_3016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3016_, 0, v___x_3013_);
v___x_3015_ = v_reuseFailAlloc_3016_;
goto v_reusejp_3014_;
}
v_reusejp_3014_:
{
return v___x_3015_;
}
}
v___jp_3017_:
{
lean_object* v___x_3022_; uint8_t v___x_3023_; 
v___x_3022_ = lean_array_get_size(v___y_3018_);
v___x_3023_ = lean_nat_dec_lt(v___y_3019_, v___x_3022_);
if (v___x_3023_ == 0)
{
v___y_3011_ = v___y_3020_;
v_a_3012_ = v_val_3021_;
goto v___jp_3010_;
}
else
{
lean_object* v___x_3024_; size_t v___x_3025_; size_t v___x_3026_; lean_object* v___x_3027_; 
v___x_3024_ = lean_box(0);
v___x_3025_ = ((size_t)0ULL);
v___x_3026_ = lean_usize_of_nat(v___x_3022_);
v___x_3027_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_3018_, v___x_3025_, v___x_3026_, v___x_3024_, v_a_2970_);
if (lean_obj_tag(v___x_3027_) == 0)
{
lean_dec_ref_known(v___x_3027_, 1);
v___y_3011_ = v___y_3020_;
v_a_3012_ = v_val_3021_;
goto v___jp_3010_;
}
else
{
lean_object* v_a_3028_; lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3035_; 
lean_dec_ref(v_val_3021_);
lean_dec_ref(v___y_3020_);
lean_del_object(v___x_3005_);
lean_dec_ref(v_dir_3003_);
lean_dec_ref(v_manifestEntry_2966_);
v_a_3028_ = lean_ctor_get(v___x_3027_, 0);
v_isSharedCheck_3035_ = !lean_is_exclusive(v___x_3027_);
if (v_isSharedCheck_3035_ == 0)
{
v___x_3030_ = v___x_3027_;
v_isShared_3031_ = v_isSharedCheck_3035_;
goto v_resetjp_3029_;
}
else
{
lean_inc(v_a_3028_);
lean_dec(v___x_3027_);
v___x_3030_ = lean_box(0);
v_isShared_3031_ = v_isSharedCheck_3035_;
goto v_resetjp_3029_;
}
v_resetjp_3029_:
{
lean_object* v___x_3033_; 
if (v_isShared_3031_ == 0)
{
v___x_3033_ = v___x_3030_;
goto v_reusejp_3032_;
}
else
{
lean_object* v_reuseFailAlloc_3034_; 
v_reuseFailAlloc_3034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3034_, 0, v_a_3028_);
v___x_3033_ = v_reuseFailAlloc_3034_;
goto v_reusejp_3032_;
}
v_reusejp_3032_:
{
return v___x_3033_;
}
}
}
}
}
v___jp_3036_:
{
if (lean_obj_tag(v_a_3037_) == 1)
{
lean_dec_ref(v_pkgDir_3007_);
if (lean_obj_tag(v_manifestFile_x3f_3002_) == 1)
{
lean_object* v_val_3038_; lean_object* v_val_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; 
v_val_3038_ = lean_ctor_get(v_a_3037_, 0);
lean_inc_n(v_val_3038_, 2);
lean_dec_ref_known(v_a_3037_, 1);
v_val_3039_ = lean_ctor_get(v_manifestFile_x3f_3002_, 0);
lean_inc(v_val_3039_);
v___x_3040_ = l_Lake_joinRelative(v_val_3038_, v_val_3039_);
v___x_3041_ = lean_unsigned_to_nat(0u);
v___x_3042_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_3043_ = l_Lake_Manifest_load(v___x_3040_);
if (lean_obj_tag(v___x_3043_) == 0)
{
lean_object* v_a_3044_; lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3051_; 
v_a_3044_ = lean_ctor_get(v___x_3043_, 0);
v_isSharedCheck_3051_ = !lean_is_exclusive(v___x_3043_);
if (v_isSharedCheck_3051_ == 0)
{
v___x_3046_ = v___x_3043_;
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
else
{
lean_inc(v_a_3044_);
lean_dec(v___x_3043_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
lean_object* v___x_3049_; 
if (v_isShared_3047_ == 0)
{
lean_ctor_set_tag(v___x_3046_, 1);
v___x_3049_ = v___x_3046_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v_a_3044_);
v___x_3049_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
v___y_3018_ = v___x_3042_;
v___y_3019_ = v___x_3041_;
v___y_3020_ = v_val_3038_;
v_val_3021_ = v___x_3049_;
goto v___jp_3017_;
}
}
}
else
{
lean_object* v_a_3052_; lean_object* v___x_3054_; uint8_t v_isShared_3055_; uint8_t v_isSharedCheck_3059_; 
v_a_3052_ = lean_ctor_get(v___x_3043_, 0);
v_isSharedCheck_3059_ = !lean_is_exclusive(v___x_3043_);
if (v_isSharedCheck_3059_ == 0)
{
v___x_3054_ = v___x_3043_;
v_isShared_3055_ = v_isSharedCheck_3059_;
goto v_resetjp_3053_;
}
else
{
lean_inc(v_a_3052_);
lean_dec(v___x_3043_);
v___x_3054_ = lean_box(0);
v_isShared_3055_ = v_isSharedCheck_3059_;
goto v_resetjp_3053_;
}
v_resetjp_3053_:
{
lean_object* v___x_3057_; 
if (v_isShared_3055_ == 0)
{
lean_ctor_set_tag(v___x_3054_, 0);
v___x_3057_ = v___x_3054_;
goto v_reusejp_3056_;
}
else
{
lean_object* v_reuseFailAlloc_3058_; 
v_reuseFailAlloc_3058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3058_, 0, v_a_3052_);
v___x_3057_ = v_reuseFailAlloc_3058_;
goto v_reusejp_3056_;
}
v_reusejp_3056_:
{
v___y_3018_ = v___x_3042_;
v___y_3019_ = v___x_3041_;
v___y_3020_ = v_val_3038_;
v_val_3021_ = v___x_3057_;
goto v___jp_3017_;
}
}
}
}
else
{
lean_object* v_val_3060_; lean_object* v___x_3061_; 
v_val_3060_ = lean_ctor_get(v_a_3037_, 0);
lean_inc(v_val_3060_);
lean_dec_ref_known(v_a_3037_, 1);
v___x_3061_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1));
v___y_3011_ = v_val_3060_;
v_a_3012_ = v___x_3061_;
goto v___jp_3010_;
}
}
else
{
uint8_t v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; uint8_t v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; 
lean_inc(v_name_3001_);
lean_dec(v_a_3037_);
lean_del_object(v___x_3005_);
lean_dec_ref(v_dir_3003_);
lean_dec_ref(v_manifestEntry_2966_);
v___x_3062_ = 0;
v___x_3063_ = l_Lean_Name_toString(v_name_3001_, v___x_3062_);
v___x_3064_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0));
v___x_3065_ = lean_string_append(v___x_3063_, v___x_3064_);
v___x_3066_ = lean_string_append(v___x_3065_, v_pkgDir_3007_);
lean_dec_ref(v_pkgDir_3007_);
v___x_3067_ = 3;
v___x_3068_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3068_, 0, v___x_3066_);
lean_ctor_set_uint8(v___x_3068_, sizeof(void*)*1, v___x_3067_);
lean_inc_ref(v_a_2970_);
v___x_3069_ = lean_apply_2(v_a_2970_, v___x_3068_, lean_box(0));
v___x_3070_ = lean_box(0);
v___x_3071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3071_, 0, v___x_3070_);
return v___x_3071_;
}
}
v___jp_3074_:
{
uint8_t v___x_3076_; 
v___x_3076_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_3076_ == 0)
{
v_a_3037_ = v_val_3075_;
goto v___jp_3036_;
}
else
{
lean_object* v___x_3077_; size_t v___x_3078_; size_t v___x_3079_; lean_object* v___x_3080_; 
v___x_3077_ = lean_box(0);
v___x_3078_ = ((size_t)0ULL);
v___x_3079_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_3080_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_3073_, v___x_3078_, v___x_3079_, v___x_3077_, v_a_2970_);
if (lean_obj_tag(v___x_3080_) == 0)
{
lean_dec_ref_known(v___x_3080_, 1);
v_a_3037_ = v_val_3075_;
goto v___jp_3036_;
}
else
{
lean_object* v_a_3081_; lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3088_; 
lean_dec(v_val_3075_);
lean_dec_ref(v_pkgDir_3007_);
lean_del_object(v___x_3005_);
lean_dec_ref(v_dir_3003_);
lean_dec_ref(v_manifestEntry_2966_);
v_a_3081_ = lean_ctor_get(v___x_3080_, 0);
v_isSharedCheck_3088_ = !lean_is_exclusive(v___x_3080_);
if (v_isSharedCheck_3088_ == 0)
{
v___x_3083_ = v___x_3080_;
v_isShared_3084_ = v_isSharedCheck_3088_;
goto v_resetjp_3082_;
}
else
{
lean_inc(v_a_3081_);
lean_dec(v___x_3080_);
v___x_3083_ = lean_box(0);
v_isShared_3084_ = v_isSharedCheck_3088_;
goto v_resetjp_3082_;
}
v_resetjp_3082_:
{
lean_object* v___x_3086_; 
if (v_isShared_3084_ == 0)
{
v___x_3086_ = v___x_3083_;
goto v_reusejp_3085_;
}
else
{
lean_object* v_reuseFailAlloc_3087_; 
v_reuseFailAlloc_3087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3087_, 0, v_a_3081_);
v___x_3086_ = v_reuseFailAlloc_3087_;
goto v_reusejp_3085_;
}
v_reusejp_3085_:
{
return v___x_3086_;
}
}
}
}
}
}
}
else
{
lean_object* v_name_3094_; lean_object* v_manifestFile_x3f_3095_; lean_object* v_url_3096_; lean_object* v_rev_3097_; lean_object* v_subDir_x3f_3098_; lean_object* v_pkgUrlMap_3099_; uint8_t v___x_3100_; lean_object* v___x_3101_; lean_object* v___y_3103_; lean_object* v___y_3104_; lean_object* v___y_3105_; lean_object* v_a_3106_; lean_object* v___y_3140_; lean_object* v___y_3141_; lean_object* v___y_3142_; lean_object* v___y_3143_; lean_object* v___y_3144_; lean_object* v_val_3145_; lean_object* v_relGitDir_3160_; lean_object* v_repo_3161_; lean_object* v_url_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; 
v_name_3094_ = lean_ctor_get(v_manifestEntry_2966_, 0);
v_manifestFile_x3f_3095_ = lean_ctor_get(v_manifestEntry_2966_, 3);
v_url_3096_ = lean_ctor_get(v_src_3000_, 0);
lean_inc_ref(v_url_3096_);
v_rev_3097_ = lean_ctor_get(v_src_3000_, 1);
lean_inc_ref(v_rev_3097_);
v_subDir_x3f_3098_ = lean_ctor_get(v_src_3000_, 3);
lean_inc(v_subDir_x3f_3098_);
lean_dec_ref_known(v_src_3000_, 4);
v_pkgUrlMap_3099_ = lean_ctor_get(v_lakeEnv_2967_, 5);
v___x_3100_ = 0;
lean_inc(v_name_3094_);
v___x_3101_ = l_Lean_Name_toString(v_name_3094_, v___x_3100_);
lean_inc_ref_n(v___x_3101_, 2);
v_relGitDir_3160_ = l_Lake_joinRelative(v_relPkgsDir_2969_, v___x_3101_);
lean_inc_ref(v_relGitDir_3160_);
lean_inc_ref(v_wsDir_2968_);
v_repo_3161_ = l_Lake_joinRelative(v_wsDir_2968_, v_relGitDir_3160_);
v_url_3162_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lake_PackageEntry_materialize_spec__0___redArg(v_pkgUrlMap_3099_, v_name_3094_, v_url_3096_);
lean_dec_ref(v_url_3096_);
v___x_3163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3163_, 0, v_rev_3097_);
lean_inc(v_url_3162_);
v___x_3164_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(v_a_2970_, v___x_3101_, v_repo_3161_, v_url_3162_, v___x_3163_);
if (lean_obj_tag(v___x_3164_) == 0)
{
lean_object* v___y_3166_; lean_object* v___y_3167_; lean_object* v___y_3177_; 
lean_dec_ref_known(v___x_3164_, 1);
if (lean_obj_tag(v_subDir_x3f_3098_) == 0)
{
v___y_3177_ = v_relGitDir_3160_;
goto v___jp_3176_;
}
else
{
lean_object* v_val_3181_; lean_object* v___x_3182_; 
v_val_3181_ = lean_ctor_get(v_subDir_x3f_3098_, 0);
lean_inc(v_val_3181_);
lean_dec_ref_known(v_subDir_x3f_3098_, 1);
v___x_3182_ = l_Lake_joinRelative(v_relGitDir_3160_, v_val_3181_);
v___y_3177_ = v___x_3182_;
goto v___jp_3176_;
}
v___jp_3165_:
{
lean_object* v_pkgDir_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; uint8_t v___x_3173_; 
lean_inc_ref(v___y_3166_);
v_pkgDir_3168_ = l_Lake_joinRelative(v_wsDir_2968_, v___y_3166_);
lean_inc_ref(v_pkgDir_3168_);
v___x_3169_ = l_Lake_resolvePath(v_pkgDir_3168_);
v___x_3170_ = lean_unsigned_to_nat(0u);
v___x_3171_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_3172_ = lean_string_utf8_byte_size(v___x_3169_);
v___x_3173_ = lean_nat_dec_eq(v___x_3172_, v___x_3170_);
if (v___x_3173_ == 0)
{
lean_object* v___x_3174_; 
v___x_3174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3174_, 0, v___x_3169_);
v___y_3140_ = v___x_3170_;
v___y_3141_ = v___y_3167_;
v___y_3142_ = v___y_3166_;
v___y_3143_ = v_pkgDir_3168_;
v___y_3144_ = v___x_3171_;
v_val_3145_ = v___x_3174_;
goto v___jp_3139_;
}
else
{
lean_object* v___x_3175_; 
lean_dec_ref(v___x_3169_);
v___x_3175_ = lean_box(0);
v___y_3140_ = v___x_3170_;
v___y_3141_ = v___y_3167_;
v___y_3142_ = v___y_3166_;
v___y_3143_ = v_pkgDir_3168_;
v___y_3144_ = v___x_3171_;
v_val_3145_ = v___x_3175_;
goto v___jp_3139_;
}
}
v___jp_3176_:
{
lean_object* v___x_3178_; 
v___x_3178_ = l_Lake_Git_filterUrl_x3f(v_url_3162_);
if (lean_obj_tag(v___x_3178_) == 0)
{
lean_object* v___x_3179_; 
v___x_3179_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___y_3166_ = v___y_3177_;
v___y_3167_ = v___x_3179_;
goto v___jp_3165_;
}
else
{
lean_object* v_val_3180_; 
v_val_3180_ = lean_ctor_get(v___x_3178_, 0);
lean_inc(v_val_3180_);
lean_dec_ref_known(v___x_3178_, 1);
v___y_3166_ = v___y_3177_;
v___y_3167_ = v_val_3180_;
goto v___jp_3165_;
}
}
}
else
{
lean_object* v_a_3183_; lean_object* v___x_3185_; uint8_t v_isShared_3186_; uint8_t v_isSharedCheck_3190_; 
lean_dec(v_url_3162_);
lean_dec_ref(v_relGitDir_3160_);
lean_dec_ref(v___x_3101_);
lean_dec(v_subDir_x3f_3098_);
lean_dec_ref(v_wsDir_2968_);
lean_dec_ref(v_manifestEntry_2966_);
v_a_3183_ = lean_ctor_get(v___x_3164_, 0);
v_isSharedCheck_3190_ = !lean_is_exclusive(v___x_3164_);
if (v_isSharedCheck_3190_ == 0)
{
v___x_3185_ = v___x_3164_;
v_isShared_3186_ = v_isSharedCheck_3190_;
goto v_resetjp_3184_;
}
else
{
lean_inc(v_a_3183_);
lean_dec(v___x_3164_);
v___x_3185_ = lean_box(0);
v_isShared_3186_ = v_isSharedCheck_3190_;
goto v_resetjp_3184_;
}
v_resetjp_3184_:
{
lean_object* v___x_3188_; 
if (v_isShared_3186_ == 0)
{
v___x_3188_ = v___x_3185_;
goto v_reusejp_3187_;
}
else
{
lean_object* v_reuseFailAlloc_3189_; 
v_reuseFailAlloc_3189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3189_, 0, v_a_3183_);
v___x_3188_ = v_reuseFailAlloc_3189_;
goto v_reusejp_3187_;
}
v_reusejp_3187_:
{
return v___x_3188_;
}
}
}
v___jp_3102_:
{
if (lean_obj_tag(v_a_3106_) == 1)
{
lean_dec_ref(v___y_3105_);
lean_dec_ref(v___x_3101_);
if (lean_obj_tag(v_manifestFile_x3f_3095_) == 1)
{
lean_object* v_val_3107_; lean_object* v_val_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; 
v_val_3107_ = lean_ctor_get(v_a_3106_, 0);
lean_inc_n(v_val_3107_, 2);
lean_dec_ref_known(v_a_3106_, 1);
v_val_3108_ = lean_ctor_get(v_manifestFile_x3f_3095_, 0);
lean_inc(v_val_3108_);
v___x_3109_ = l_Lake_joinRelative(v_val_3107_, v_val_3108_);
v___x_3110_ = lean_unsigned_to_nat(0u);
v___x_3111_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_3112_ = l_Lake_Manifest_load(v___x_3109_);
if (lean_obj_tag(v___x_3112_) == 0)
{
lean_object* v_a_3113_; lean_object* v___x_3115_; uint8_t v_isShared_3116_; uint8_t v_isSharedCheck_3120_; 
v_a_3113_ = lean_ctor_get(v___x_3112_, 0);
v_isSharedCheck_3120_ = !lean_is_exclusive(v___x_3112_);
if (v_isSharedCheck_3120_ == 0)
{
v___x_3115_ = v___x_3112_;
v_isShared_3116_ = v_isSharedCheck_3120_;
goto v_resetjp_3114_;
}
else
{
lean_inc(v_a_3113_);
lean_dec(v___x_3112_);
v___x_3115_ = lean_box(0);
v_isShared_3116_ = v_isSharedCheck_3120_;
goto v_resetjp_3114_;
}
v_resetjp_3114_:
{
lean_object* v___x_3118_; 
if (v_isShared_3116_ == 0)
{
lean_ctor_set_tag(v___x_3115_, 1);
v___x_3118_ = v___x_3115_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3119_; 
v_reuseFailAlloc_3119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3119_, 0, v_a_3113_);
v___x_3118_ = v_reuseFailAlloc_3119_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
v___y_2980_ = v___x_3110_;
v___y_2981_ = v_val_3107_;
v___y_2982_ = v___x_3111_;
v___y_2983_ = v___y_3103_;
v___y_2984_ = v___y_3104_;
v_val_2985_ = v___x_3118_;
goto v___jp_2979_;
}
}
}
else
{
lean_object* v_a_3121_; lean_object* v___x_3123_; uint8_t v_isShared_3124_; uint8_t v_isSharedCheck_3128_; 
v_a_3121_ = lean_ctor_get(v___x_3112_, 0);
v_isSharedCheck_3128_ = !lean_is_exclusive(v___x_3112_);
if (v_isSharedCheck_3128_ == 0)
{
v___x_3123_ = v___x_3112_;
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
else
{
lean_inc(v_a_3121_);
lean_dec(v___x_3112_);
v___x_3123_ = lean_box(0);
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
v_resetjp_3122_:
{
lean_object* v___x_3126_; 
if (v_isShared_3124_ == 0)
{
lean_ctor_set_tag(v___x_3123_, 0);
v___x_3126_ = v___x_3123_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v_a_3121_);
v___x_3126_ = v_reuseFailAlloc_3127_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
v___y_2980_ = v___x_3110_;
v___y_2981_ = v_val_3107_;
v___y_2982_ = v___x_3111_;
v___y_2983_ = v___y_3103_;
v___y_2984_ = v___y_3104_;
v_val_2985_ = v___x_3126_;
goto v___jp_2979_;
}
}
}
}
else
{
lean_object* v_val_3129_; lean_object* v___x_3130_; 
v_val_3129_ = lean_ctor_get(v_a_3106_, 0);
lean_inc(v_val_3129_);
lean_dec_ref_known(v_a_3106_, 1);
v___x_3130_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1));
v___y_2973_ = v_val_3129_;
v___y_2974_ = v___y_3104_;
v___y_2975_ = v___y_3103_;
v_a_2976_ = v___x_3130_;
goto v___jp_2972_;
}
}
else
{
lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; uint8_t v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; 
lean_dec(v_a_3106_);
lean_dec_ref(v___y_3104_);
lean_dec_ref(v___y_3103_);
lean_dec_ref(v_manifestEntry_2966_);
v___x_3131_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0));
v___x_3132_ = lean_string_append(v___x_3101_, v___x_3131_);
v___x_3133_ = lean_string_append(v___x_3132_, v___y_3105_);
lean_dec_ref(v___y_3105_);
v___x_3134_ = 3;
v___x_3135_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3135_, 0, v___x_3133_);
lean_ctor_set_uint8(v___x_3135_, sizeof(void*)*1, v___x_3134_);
lean_inc_ref(v_a_2970_);
v___x_3136_ = lean_apply_2(v_a_2970_, v___x_3135_, lean_box(0));
v___x_3137_ = lean_box(0);
v___x_3138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3138_, 0, v___x_3137_);
return v___x_3138_;
}
}
v___jp_3139_:
{
lean_object* v___x_3146_; uint8_t v___x_3147_; 
v___x_3146_ = lean_array_get_size(v___y_3144_);
v___x_3147_ = lean_nat_dec_lt(v___y_3140_, v___x_3146_);
if (v___x_3147_ == 0)
{
v___y_3103_ = v___y_3142_;
v___y_3104_ = v___y_3141_;
v___y_3105_ = v___y_3143_;
v_a_3106_ = v_val_3145_;
goto v___jp_3102_;
}
else
{
lean_object* v___x_3148_; size_t v___x_3149_; size_t v___x_3150_; lean_object* v___x_3151_; 
v___x_3148_ = lean_box(0);
v___x_3149_ = ((size_t)0ULL);
v___x_3150_ = lean_usize_of_nat(v___x_3146_);
v___x_3151_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_3144_, v___x_3149_, v___x_3150_, v___x_3148_, v_a_2970_);
if (lean_obj_tag(v___x_3151_) == 0)
{
lean_dec_ref_known(v___x_3151_, 1);
v___y_3103_ = v___y_3142_;
v___y_3104_ = v___y_3141_;
v___y_3105_ = v___y_3143_;
v_a_3106_ = v_val_3145_;
goto v___jp_3102_;
}
else
{
lean_object* v_a_3152_; lean_object* v___x_3154_; uint8_t v_isShared_3155_; uint8_t v_isSharedCheck_3159_; 
lean_dec(v_val_3145_);
lean_dec_ref(v___y_3143_);
lean_dec_ref(v___y_3142_);
lean_dec_ref(v___y_3141_);
lean_dec_ref(v___x_3101_);
lean_dec_ref(v_manifestEntry_2966_);
v_a_3152_ = lean_ctor_get(v___x_3151_, 0);
v_isSharedCheck_3159_ = !lean_is_exclusive(v___x_3151_);
if (v_isSharedCheck_3159_ == 0)
{
v___x_3154_ = v___x_3151_;
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
else
{
lean_inc(v_a_3152_);
lean_dec(v___x_3151_);
v___x_3154_ = lean_box(0);
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
v_resetjp_3153_:
{
lean_object* v___x_3157_; 
if (v_isShared_3155_ == 0)
{
v___x_3157_ = v___x_3154_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3158_; 
v_reuseFailAlloc_3158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3158_, 0, v_a_3152_);
v___x_3157_ = v_reuseFailAlloc_3158_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
return v___x_3157_;
}
}
}
}
}
}
v___jp_2972_:
{
lean_object* v___x_2977_; lean_object* v___x_2978_; 
v___x_2977_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2977_, 0, v___y_2973_);
lean_ctor_set(v___x_2977_, 1, v___y_2975_);
lean_ctor_set(v___x_2977_, 2, v___y_2974_);
lean_ctor_set(v___x_2977_, 3, v_a_2976_);
lean_ctor_set(v___x_2977_, 4, v_manifestEntry_2966_);
v___x_2978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2978_, 0, v___x_2977_);
return v___x_2978_;
}
v___jp_2979_:
{
lean_object* v___x_2986_; uint8_t v___x_2987_; 
v___x_2986_ = lean_array_get_size(v___y_2982_);
v___x_2987_ = lean_nat_dec_lt(v___y_2980_, v___x_2986_);
if (v___x_2987_ == 0)
{
v___y_2973_ = v___y_2981_;
v___y_2974_ = v___y_2984_;
v___y_2975_ = v___y_2983_;
v_a_2976_ = v_val_2985_;
goto v___jp_2972_;
}
else
{
lean_object* v___x_2988_; size_t v___x_2989_; size_t v___x_2990_; lean_object* v___x_2991_; 
v___x_2988_ = lean_box(0);
v___x_2989_ = ((size_t)0ULL);
v___x_2990_ = lean_usize_of_nat(v___x_2986_);
v___x_2991_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_2982_, v___x_2989_, v___x_2990_, v___x_2988_, v_a_2970_);
if (lean_obj_tag(v___x_2991_) == 0)
{
lean_dec_ref_known(v___x_2991_, 1);
v___y_2973_ = v___y_2981_;
v___y_2974_ = v___y_2984_;
v___y_2975_ = v___y_2983_;
v_a_2976_ = v_val_2985_;
goto v___jp_2972_;
}
else
{
lean_object* v_a_2992_; lean_object* v___x_2994_; uint8_t v_isShared_2995_; uint8_t v_isSharedCheck_2999_; 
lean_dec_ref(v_val_2985_);
lean_dec_ref(v___y_2984_);
lean_dec_ref(v___y_2983_);
lean_dec_ref(v___y_2981_);
lean_dec_ref(v_manifestEntry_2966_);
v_a_2992_ = lean_ctor_get(v___x_2991_, 0);
v_isSharedCheck_2999_ = !lean_is_exclusive(v___x_2991_);
if (v_isSharedCheck_2999_ == 0)
{
v___x_2994_ = v___x_2991_;
v_isShared_2995_ = v_isSharedCheck_2999_;
goto v_resetjp_2993_;
}
else
{
lean_inc(v_a_2992_);
lean_dec(v___x_2991_);
v___x_2994_ = lean_box(0);
v_isShared_2995_ = v_isSharedCheck_2999_;
goto v_resetjp_2993_;
}
v_resetjp_2993_:
{
lean_object* v___x_2997_; 
if (v_isShared_2995_ == 0)
{
v___x_2997_ = v___x_2994_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v_a_2992_);
v___x_2997_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
return v___x_2997_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize___boxed(lean_object* v_manifestEntry_3191_, lean_object* v_lakeEnv_3192_, lean_object* v_wsDir_3193_, lean_object* v_relPkgsDir_3194_, lean_object* v_a_3195_, lean_object* v_a_3196_){
_start:
{
lean_object* v_res_3197_; 
v_res_3197_ = l_Lake_PackageEntry_materialize(v_manifestEntry_3191_, v_lakeEnv_3192_, v_wsDir_3193_, v_relPkgsDir_3194_, v_a_3195_);
lean_dec_ref(v_a_3195_);
lean_dec_ref(v_lakeEnv_3192_);
return v_res_3197_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lake_PackageEntry_materialize_spec__0(lean_object* v_00_u03b4_3198_, lean_object* v_t_3199_, lean_object* v_k_3200_, lean_object* v_fallback_3201_){
_start:
{
lean_object* v___x_3202_; 
v___x_3202_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lake_PackageEntry_materialize_spec__0___redArg(v_t_3199_, v_k_3200_, v_fallback_3201_);
return v___x_3202_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lake_PackageEntry_materialize_spec__0___boxed(lean_object* v_00_u03b4_3203_, lean_object* v_t_3204_, lean_object* v_k_3205_, lean_object* v_fallback_3206_){
_start:
{
lean_object* v_res_3207_; 
v_res_3207_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lake_PackageEntry_materialize_spec__0(v_00_u03b4_3203_, v_t_3204_, v_k_3205_, v_fallback_3206_);
lean_dec(v_fallback_3206_);
lean_dec(v_k_3205_);
lean_dec(v_t_3204_);
return v_res_3207_;
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

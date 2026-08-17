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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
static uint8_t l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7;
static lean_once_cell_t l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8;
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
static uint8_t _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7(void){
_start:
{
lean_object* v___x_24_; uint8_t v___x_25_; 
v___x_24_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__5, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__5);
v___x_25_ = lean_nat_dec_le(v___x_24_, v___x_24_);
return v___x_25_;
}
}
static size_t _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8(void){
_start:
{
lean_object* v___x_26_; size_t v___x_27_; 
v___x_26_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__5, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__5);
v___x_27_ = lean_usize_of_nat(v___x_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl(lean_object* v_name_28_, lean_object* v_url_29_, lean_object* v_a_30_){
_start:
{
lean_object* v_a_33_; lean_object* v___x_50_; uint8_t v___x_51_; lean_object* v___f_52_; lean_object* v___y_54_; lean_object* v___y_55_; lean_object* v___y_56_; lean_object* v_val_57_; lean_object* v___x_95_; uint8_t v___x_96_; 
v___x_50_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__2, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__2_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__2);
v___x_51_ = l_System_FilePath_pathExists(v_url_29_);
v___f_52_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3));
v___x_95_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_96_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_96_ == 0)
{
goto v___jp_86_;
}
else
{
lean_object* v___x_97_; uint8_t v___x_98_; 
v___x_97_ = lean_box(0);
v___x_98_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
if (v___x_98_ == 0)
{
if (v___x_96_ == 0)
{
goto v___jp_86_;
}
else
{
size_t v___x_99_; size_t v___x_100_; lean_object* v___x_1644__overap_101_; lean_object* v___x_102_; 
v___x_99_ = ((size_t)0ULL);
v___x_100_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8);
v___x_1644__overap_101_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_50_, v___f_52_, v___x_95_, v___x_99_, v___x_100_, v___x_97_);
lean_inc_ref(v_a_30_);
v___x_102_ = lean_apply_2(v___x_1644__overap_101_, v_a_30_, lean_box(0));
if (lean_obj_tag(v___x_102_) == 0)
{
lean_dec_ref_known(v___x_102_, 1);
goto v___jp_86_;
}
else
{
lean_object* v_a_103_; lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_110_; 
lean_dec_ref(v_url_29_);
lean_dec_ref(v_name_28_);
v_a_103_ = lean_ctor_get(v___x_102_, 0);
v_isSharedCheck_110_ = !lean_is_exclusive(v___x_102_);
if (v_isSharedCheck_110_ == 0)
{
v___x_105_ = v___x_102_;
v_isShared_106_ = v_isSharedCheck_110_;
goto v_resetjp_104_;
}
else
{
lean_inc(v_a_103_);
lean_dec(v___x_102_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_110_;
goto v_resetjp_104_;
}
v_resetjp_104_:
{
lean_object* v___x_108_; 
if (v_isShared_106_ == 0)
{
v___x_108_ = v___x_105_;
goto v_reusejp_107_;
}
else
{
lean_object* v_reuseFailAlloc_109_; 
v_reuseFailAlloc_109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_109_, 0, v_a_103_);
v___x_108_ = v_reuseFailAlloc_109_;
goto v_reusejp_107_;
}
v_reusejp_107_:
{
return v___x_108_;
}
}
}
}
}
else
{
size_t v___x_111_; size_t v___x_112_; lean_object* v___x_1654__overap_113_; lean_object* v___x_114_; 
v___x_111_ = ((size_t)0ULL);
v___x_112_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8);
v___x_1654__overap_113_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_50_, v___f_52_, v___x_95_, v___x_111_, v___x_112_, v___x_97_);
lean_inc_ref(v_a_30_);
v___x_114_ = lean_apply_2(v___x_1654__overap_113_, v_a_30_, lean_box(0));
if (lean_obj_tag(v___x_114_) == 0)
{
lean_dec_ref_known(v___x_114_, 1);
goto v___jp_86_;
}
else
{
lean_object* v_a_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_122_; 
lean_dec_ref(v_url_29_);
lean_dec_ref(v_name_28_);
v_a_115_ = lean_ctor_get(v___x_114_, 0);
v_isSharedCheck_122_ = !lean_is_exclusive(v___x_114_);
if (v_isSharedCheck_122_ == 0)
{
v___x_117_ = v___x_114_;
v_isShared_118_ = v_isSharedCheck_122_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_a_115_);
lean_dec(v___x_114_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_122_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v___x_120_; 
if (v_isShared_118_ == 0)
{
v___x_120_ = v___x_117_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v_a_115_);
v___x_120_ = v_reuseFailAlloc_121_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
return v___x_120_;
}
}
}
}
}
v___jp_32_:
{
if (lean_obj_tag(v_a_33_) == 1)
{
lean_object* v_val_34_; lean_object* v___x_36_; uint8_t v_isShared_37_; uint8_t v_isSharedCheck_41_; 
lean_dec_ref(v_url_29_);
lean_dec_ref(v_name_28_);
v_val_34_ = lean_ctor_get(v_a_33_, 0);
v_isSharedCheck_41_ = !lean_is_exclusive(v_a_33_);
if (v_isSharedCheck_41_ == 0)
{
v___x_36_ = v_a_33_;
v_isShared_37_ = v_isSharedCheck_41_;
goto v_resetjp_35_;
}
else
{
lean_inc(v_val_34_);
lean_dec(v_a_33_);
v___x_36_ = lean_box(0);
v_isShared_37_ = v_isSharedCheck_41_;
goto v_resetjp_35_;
}
v_resetjp_35_:
{
lean_object* v___x_39_; 
if (v_isShared_37_ == 0)
{
lean_ctor_set_tag(v___x_36_, 0);
v___x_39_ = v___x_36_;
goto v_reusejp_38_;
}
else
{
lean_object* v_reuseFailAlloc_40_; 
v_reuseFailAlloc_40_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_40_, 0, v_val_34_);
v___x_39_ = v_reuseFailAlloc_40_;
goto v_reusejp_38_;
}
v_reusejp_38_:
{
return v___x_39_;
}
}
}
else
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; uint8_t v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
lean_dec(v_a_33_);
v___x_42_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__0));
v___x_43_ = lean_string_append(v_name_28_, v___x_42_);
v___x_44_ = lean_string_append(v___x_43_, v_url_29_);
lean_dec_ref(v_url_29_);
v___x_45_ = 3;
v___x_46_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_46_, 0, v___x_44_);
lean_ctor_set_uint8(v___x_46_, sizeof(void*)*1, v___x_45_);
lean_inc_ref(v_a_30_);
v___x_47_ = lean_apply_2(v_a_30_, v___x_46_, lean_box(0));
v___x_48_ = lean_box(0);
v___x_49_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_49_, 0, v___x_48_);
return v___x_49_;
}
}
v___jp_53_:
{
lean_object* v___x_58_; uint8_t v___x_59_; 
v___x_58_ = lean_array_get_size(v___y_56_);
v___x_59_ = lean_nat_dec_lt(v___y_54_, v___x_58_);
if (v___x_59_ == 0)
{
lean_dec_ref(v___y_55_);
v_a_33_ = v_val_57_;
goto v___jp_32_;
}
else
{
lean_object* v___x_60_; uint8_t v___x_61_; 
v___x_60_ = lean_box(0);
v___x_61_ = lean_nat_dec_le(v___x_58_, v___x_58_);
if (v___x_61_ == 0)
{
if (v___x_59_ == 0)
{
lean_dec_ref(v___y_55_);
v_a_33_ = v_val_57_;
goto v___jp_32_;
}
else
{
size_t v___x_62_; size_t v___x_63_; lean_object* v___x_2407__overap_64_; lean_object* v___x_65_; 
v___x_62_ = ((size_t)0ULL);
v___x_63_ = lean_usize_of_nat(v___x_58_);
lean_inc_ref(v___y_56_);
v___x_2407__overap_64_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___y_55_, v___f_52_, v___y_56_, v___x_62_, v___x_63_, v___x_60_);
lean_inc_ref(v_a_30_);
v___x_65_ = lean_apply_2(v___x_2407__overap_64_, v_a_30_, lean_box(0));
if (lean_obj_tag(v___x_65_) == 0)
{
lean_dec_ref_known(v___x_65_, 1);
v_a_33_ = v_val_57_;
goto v___jp_32_;
}
else
{
lean_object* v_a_66_; lean_object* v___x_68_; uint8_t v_isShared_69_; uint8_t v_isSharedCheck_73_; 
lean_dec(v_val_57_);
lean_dec_ref(v_url_29_);
lean_dec_ref(v_name_28_);
v_a_66_ = lean_ctor_get(v___x_65_, 0);
v_isSharedCheck_73_ = !lean_is_exclusive(v___x_65_);
if (v_isSharedCheck_73_ == 0)
{
v___x_68_ = v___x_65_;
v_isShared_69_ = v_isSharedCheck_73_;
goto v_resetjp_67_;
}
else
{
lean_inc(v_a_66_);
lean_dec(v___x_65_);
v___x_68_ = lean_box(0);
v_isShared_69_ = v_isSharedCheck_73_;
goto v_resetjp_67_;
}
v_resetjp_67_:
{
lean_object* v___x_71_; 
if (v_isShared_69_ == 0)
{
v___x_71_ = v___x_68_;
goto v_reusejp_70_;
}
else
{
lean_object* v_reuseFailAlloc_72_; 
v_reuseFailAlloc_72_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_72_, 0, v_a_66_);
v___x_71_ = v_reuseFailAlloc_72_;
goto v_reusejp_70_;
}
v_reusejp_70_:
{
return v___x_71_;
}
}
}
}
}
else
{
size_t v___x_74_; size_t v___x_75_; lean_object* v___x_2416__overap_76_; lean_object* v___x_77_; 
v___x_74_ = ((size_t)0ULL);
v___x_75_ = lean_usize_of_nat(v___x_58_);
lean_inc_ref(v___y_56_);
v___x_2416__overap_76_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___y_55_, v___f_52_, v___y_56_, v___x_74_, v___x_75_, v___x_60_);
lean_inc_ref(v_a_30_);
v___x_77_ = lean_apply_2(v___x_2416__overap_76_, v_a_30_, lean_box(0));
if (lean_obj_tag(v___x_77_) == 0)
{
lean_dec_ref_known(v___x_77_, 1);
v_a_33_ = v_val_57_;
goto v___jp_32_;
}
else
{
lean_object* v_a_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_85_; 
lean_dec(v_val_57_);
lean_dec_ref(v_url_29_);
lean_dec_ref(v_name_28_);
v_a_78_ = lean_ctor_get(v___x_77_, 0);
v_isSharedCheck_85_ = !lean_is_exclusive(v___x_77_);
if (v_isSharedCheck_85_ == 0)
{
v___x_80_ = v___x_77_;
v_isShared_81_ = v_isSharedCheck_85_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_a_78_);
lean_dec(v___x_77_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_85_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
lean_object* v___x_83_; 
if (v_isShared_81_ == 0)
{
v___x_83_ = v___x_80_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_84_; 
v_reuseFailAlloc_84_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_84_, 0, v_a_78_);
v___x_83_ = v_reuseFailAlloc_84_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
return v___x_83_;
}
}
}
}
}
}
v___jp_86_:
{
if (v___x_51_ == 0)
{
lean_object* v___x_87_; 
lean_dec_ref(v_name_28_);
v___x_87_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_87_, 0, v_url_29_);
return v___x_87_;
}
else
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; uint8_t v___x_92_; 
lean_inc_ref(v_url_29_);
v___x_88_ = l_Lake_resolvePath(v_url_29_);
v___x_89_ = lean_unsigned_to_nat(0u);
v___x_90_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_91_ = lean_string_utf8_byte_size(v___x_88_);
v___x_92_ = lean_nat_dec_eq(v___x_91_, v___x_89_);
if (v___x_92_ == 0)
{
lean_object* v___x_93_; 
v___x_93_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_93_, 0, v___x_88_);
v___y_54_ = v___x_89_;
v___y_55_ = v___x_50_;
v___y_56_ = v___x_90_;
v_val_57_ = v___x_93_;
goto v___jp_53_;
}
else
{
lean_object* v___x_94_; 
lean_dec_ref(v___x_88_);
v___x_94_ = lean_box(0);
v___y_54_ = v___x_89_;
v___y_55_ = v___x_50_;
v___y_56_ = v___x_90_;
v_val_57_ = v___x_94_;
goto v___jp_53_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___boxed(lean_object* v_name_123_, lean_object* v_url_124_, lean_object* v_a_125_, lean_object* v_a_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl(v_name_123_, v_url_124_, v_a_125_);
lean_dec_ref(v_a_125_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff(lean_object* v_name_129_, lean_object* v_repo_130_, lean_object* v_a_131_){
_start:
{
uint8_t v_a_134_; lean_object* v___x_144_; uint8_t v___x_145_; lean_object* v___f_146_; lean_object* v___x_147_; uint8_t v_val_149_; 
v___x_144_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__2, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__2_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__2);
lean_inc_ref(v_repo_130_);
v___x_145_ = l_Lake_GitRepo_hasNoDiff(v_repo_130_);
v___f_146_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3));
v___x_147_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
if (v___x_145_ == 0)
{
uint8_t v___x_161_; 
v___x_161_ = 1;
v_val_149_ = v___x_161_;
goto v___jp_148_;
}
else
{
uint8_t v___x_162_; 
v___x_162_ = 0;
v_val_149_ = v___x_162_;
goto v___jp_148_;
}
v___jp_133_:
{
if (v_a_134_ == 0)
{
lean_object* v___x_135_; lean_object* v___x_136_; 
lean_dec_ref(v_repo_130_);
lean_dec_ref(v_name_129_);
v___x_135_ = lean_box(0);
v___x_136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_136_, 0, v___x_135_);
return v___x_136_;
}
else
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; uint8_t v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_137_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff___closed__0));
v___x_138_ = lean_string_append(v_name_129_, v___x_137_);
v___x_139_ = lean_string_append(v___x_138_, v_repo_130_);
lean_dec_ref(v_repo_130_);
v___x_140_ = 2;
v___x_141_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_141_, 0, v___x_139_);
lean_ctor_set_uint8(v___x_141_, sizeof(void*)*1, v___x_140_);
lean_inc_ref(v_a_131_);
v___x_142_ = lean_apply_2(v_a_131_, v___x_141_, lean_box(0));
v___x_143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_143_, 0, v___x_142_);
return v___x_143_;
}
}
v___jp_148_:
{
uint8_t v___x_150_; 
v___x_150_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_150_ == 0)
{
v_a_134_ = v_val_149_;
goto v___jp_133_;
}
else
{
lean_object* v___x_151_; uint8_t v___x_152_; 
v___x_151_ = lean_box(0);
v___x_152_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
if (v___x_152_ == 0)
{
if (v___x_150_ == 0)
{
v_a_134_ = v_val_149_;
goto v___jp_133_;
}
else
{
size_t v___x_153_; size_t v___x_154_; lean_object* v___x_1047__overap_155_; lean_object* v___x_156_; 
v___x_153_ = ((size_t)0ULL);
v___x_154_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8);
v___x_1047__overap_155_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_144_, v___f_146_, v___x_147_, v___x_153_, v___x_154_, v___x_151_);
lean_inc_ref(v_a_131_);
v___x_156_ = lean_apply_2(v___x_1047__overap_155_, v_a_131_, lean_box(0));
if (lean_obj_tag(v___x_156_) == 0)
{
lean_dec_ref_known(v___x_156_, 1);
v_a_134_ = v_val_149_;
goto v___jp_133_;
}
else
{
lean_dec_ref(v_repo_130_);
lean_dec_ref(v_name_129_);
return v___x_156_;
}
}
}
else
{
size_t v___x_157_; size_t v___x_158_; lean_object* v___x_1057__overap_159_; lean_object* v___x_160_; 
v___x_157_ = ((size_t)0ULL);
v___x_158_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8);
v___x_1057__overap_159_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_144_, v___f_146_, v___x_147_, v___x_157_, v___x_158_, v___x_151_);
lean_inc_ref(v_a_131_);
v___x_160_ = lean_apply_2(v___x_1057__overap_159_, v_a_131_, lean_box(0));
if (lean_obj_tag(v___x_160_) == 0)
{
lean_dec_ref_known(v___x_160_, 1);
v_a_134_ = v_val_149_;
goto v___jp_133_;
}
else
{
lean_dec_ref(v_repo_130_);
lean_dec_ref(v_name_129_);
return v___x_160_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff___boxed(lean_object* v_name_163_, lean_object* v_repo_164_, lean_object* v_a_165_, lean_object* v_a_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff(v_name_163_, v_repo_164_, v_a_165_);
lean_dec_ref(v_a_165_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout(lean_object* v_name_170_, lean_object* v_repo_171_, lean_object* v_rev_172_, lean_object* v_a_173_){
_start:
{
uint8_t v_a_182_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; uint8_t v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___f_204_; lean_object* v___y_206_; lean_object* v___y_207_; lean_object* v___y_208_; uint8_t v_val_209_; lean_object* v___y_227_; lean_object* v___y_259_; 
v___x_192_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__0));
lean_inc_ref(v_name_170_);
v___x_193_ = lean_string_append(v_name_170_, v___x_192_);
v___x_194_ = lean_string_append(v___x_193_, v_rev_172_);
v___x_195_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__1));
v___x_196_ = lean_string_append(v___x_194_, v___x_195_);
v___x_197_ = 1;
v___x_198_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_198_, 0, v___x_196_);
lean_ctor_set_uint8(v___x_198_, sizeof(void*)*1, v___x_197_);
lean_inc_ref(v_a_173_);
v___x_199_ = lean_apply_2(v_a_173_, v___x_198_, lean_box(0));
v___x_200_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__2, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__2_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__2);
v___x_201_ = lean_unsigned_to_nat(0u);
v___x_202_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_171_);
v___x_203_ = l_Lake_GitRepo_checkoutDetach(v_rev_172_, v_repo_171_, v___x_202_);
v___f_204_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3));
if (lean_obj_tag(v___x_203_) == 0)
{
lean_object* v_a_260_; lean_object* v___x_261_; uint8_t v___x_262_; 
v_a_260_ = lean_ctor_get(v___x_203_, 1);
lean_inc(v_a_260_);
lean_dec_ref_known(v___x_203_, 2);
v___x_261_ = lean_array_get_size(v_a_260_);
v___x_262_ = lean_nat_dec_lt(v___x_201_, v___x_261_);
if (v___x_262_ == 0)
{
lean_dec(v_a_260_);
goto v___jp_228_;
}
else
{
lean_object* v___x_263_; uint8_t v___x_264_; 
v___x_263_ = lean_box(0);
v___x_264_ = lean_nat_dec_le(v___x_261_, v___x_261_);
if (v___x_264_ == 0)
{
if (v___x_262_ == 0)
{
lean_dec(v_a_260_);
goto v___jp_228_;
}
else
{
size_t v___x_265_; size_t v___x_266_; lean_object* v___x_3201__overap_267_; lean_object* v___x_268_; 
v___x_265_ = ((size_t)0ULL);
v___x_266_ = lean_usize_of_nat(v___x_261_);
v___x_3201__overap_267_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_200_, v___f_204_, v_a_260_, v___x_265_, v___x_266_, v___x_263_);
lean_inc_ref(v_a_173_);
v___x_268_ = lean_apply_2(v___x_3201__overap_267_, v_a_173_, lean_box(0));
if (lean_obj_tag(v___x_268_) == 0)
{
lean_dec_ref_known(v___x_268_, 1);
goto v___jp_228_;
}
else
{
v___y_259_ = v___x_268_;
goto v___jp_258_;
}
}
}
else
{
size_t v___x_269_; size_t v___x_270_; lean_object* v___x_3210__overap_271_; lean_object* v___x_272_; 
v___x_269_ = ((size_t)0ULL);
v___x_270_ = lean_usize_of_nat(v___x_261_);
v___x_3210__overap_271_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_200_, v___f_204_, v_a_260_, v___x_269_, v___x_270_, v___x_263_);
lean_inc_ref(v_a_173_);
v___x_272_ = lean_apply_2(v___x_3210__overap_271_, v_a_173_, lean_box(0));
if (lean_obj_tag(v___x_272_) == 0)
{
lean_dec_ref_known(v___x_272_, 1);
goto v___jp_228_;
}
else
{
v___y_259_ = v___x_272_;
goto v___jp_258_;
}
}
}
}
else
{
lean_object* v_a_273_; lean_object* v___x_274_; uint8_t v___x_275_; 
v_a_273_ = lean_ctor_get(v___x_203_, 1);
lean_inc(v_a_273_);
lean_dec_ref_known(v___x_203_, 2);
v___x_274_ = lean_array_get_size(v_a_273_);
v___x_275_ = lean_nat_dec_lt(v___x_201_, v___x_274_);
if (v___x_275_ == 0)
{
lean_object* v___x_276_; lean_object* v___x_277_; 
lean_dec(v_a_273_);
lean_dec_ref(v_repo_171_);
lean_dec_ref(v_name_170_);
v___x_276_ = lean_box(0);
v___x_277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_277_, 0, v___x_276_);
return v___x_277_;
}
else
{
lean_object* v___x_278_; uint8_t v___x_279_; 
v___x_278_ = lean_box(0);
v___x_279_ = lean_nat_dec_le(v___x_274_, v___x_274_);
if (v___x_279_ == 0)
{
if (v___x_275_ == 0)
{
lean_dec(v_a_273_);
lean_dec_ref(v_repo_171_);
lean_dec_ref(v_name_170_);
goto v___jp_175_;
}
else
{
size_t v___x_280_; size_t v___x_281_; lean_object* v___x_3232__overap_282_; lean_object* v___x_283_; 
v___x_280_ = ((size_t)0ULL);
v___x_281_ = lean_usize_of_nat(v___x_274_);
v___x_3232__overap_282_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_200_, v___f_204_, v_a_273_, v___x_280_, v___x_281_, v___x_278_);
lean_inc_ref(v_a_173_);
v___x_283_ = lean_apply_2(v___x_3232__overap_282_, v_a_173_, lean_box(0));
if (lean_obj_tag(v___x_283_) == 0)
{
lean_dec_ref_known(v___x_283_, 1);
lean_dec_ref(v_repo_171_);
lean_dec_ref(v_name_170_);
goto v___jp_175_;
}
else
{
v___y_259_ = v___x_283_;
goto v___jp_258_;
}
}
}
else
{
size_t v___x_284_; size_t v___x_285_; lean_object* v___x_3240__overap_286_; lean_object* v___x_287_; 
v___x_284_ = ((size_t)0ULL);
v___x_285_ = lean_usize_of_nat(v___x_274_);
v___x_3240__overap_286_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_200_, v___f_204_, v_a_273_, v___x_284_, v___x_285_, v___x_278_);
lean_inc_ref(v_a_173_);
v___x_287_ = lean_apply_2(v___x_3240__overap_286_, v_a_173_, lean_box(0));
if (lean_obj_tag(v___x_287_) == 0)
{
lean_dec_ref_known(v___x_287_, 1);
lean_dec_ref(v_repo_171_);
lean_dec_ref(v_name_170_);
goto v___jp_175_;
}
else
{
v___y_259_ = v___x_287_;
goto v___jp_258_;
}
}
}
}
v___jp_175_:
{
lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_176_ = lean_box(0);
v___x_177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_177_, 0, v___x_176_);
return v___x_177_;
}
v___jp_178_:
{
lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_179_ = lean_box(0);
v___x_180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_180_, 0, v___x_179_);
return v___x_180_;
}
v___jp_181_:
{
if (v_a_182_ == 0)
{
lean_object* v___x_183_; lean_object* v___x_184_; 
lean_dec_ref(v_repo_171_);
lean_dec_ref(v_name_170_);
v___x_183_ = lean_box(0);
v___x_184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_184_, 0, v___x_183_);
return v___x_184_;
}
else
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; uint8_t v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_185_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff___closed__0));
v___x_186_ = lean_string_append(v_name_170_, v___x_185_);
v___x_187_ = lean_string_append(v___x_186_, v_repo_171_);
lean_dec_ref(v_repo_171_);
v___x_188_ = 2;
v___x_189_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_189_, 0, v___x_187_);
lean_ctor_set_uint8(v___x_189_, sizeof(void*)*1, v___x_188_);
lean_inc_ref(v_a_173_);
v___x_190_ = lean_apply_2(v_a_173_, v___x_189_, lean_box(0));
v___x_191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_191_, 0, v___x_190_);
return v___x_191_;
}
}
v___jp_205_:
{
lean_object* v___x_210_; uint8_t v___x_211_; 
v___x_210_ = lean_array_get_size(v___y_206_);
v___x_211_ = lean_nat_dec_lt(v___y_207_, v___x_210_);
if (v___x_211_ == 0)
{
lean_dec_ref(v___y_208_);
lean_dec_ref(v___y_206_);
v_a_182_ = v_val_209_;
goto v___jp_181_;
}
else
{
lean_object* v___x_212_; uint8_t v___x_213_; 
v___x_212_ = lean_box(0);
v___x_213_ = lean_nat_dec_le(v___x_210_, v___x_210_);
if (v___x_213_ == 0)
{
if (v___x_211_ == 0)
{
lean_dec_ref(v___y_208_);
lean_dec_ref(v___y_206_);
v_a_182_ = v_val_209_;
goto v___jp_181_;
}
else
{
size_t v___x_214_; size_t v___x_215_; lean_object* v___x_3637__overap_216_; lean_object* v___x_217_; 
v___x_214_ = ((size_t)0ULL);
v___x_215_ = lean_usize_of_nat(v___x_210_);
v___x_3637__overap_216_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___y_208_, v___f_204_, v___y_206_, v___x_214_, v___x_215_, v___x_212_);
lean_inc_ref(v_a_173_);
v___x_217_ = lean_apply_2(v___x_3637__overap_216_, v_a_173_, lean_box(0));
if (lean_obj_tag(v___x_217_) == 0)
{
lean_dec_ref_known(v___x_217_, 1);
v_a_182_ = v_val_209_;
goto v___jp_181_;
}
else
{
lean_dec_ref(v_repo_171_);
lean_dec_ref(v_name_170_);
return v___x_217_;
}
}
}
else
{
size_t v___x_218_; size_t v___x_219_; lean_object* v___x_3645__overap_220_; lean_object* v___x_221_; 
v___x_218_ = ((size_t)0ULL);
v___x_219_ = lean_usize_of_nat(v___x_210_);
v___x_3645__overap_220_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___y_208_, v___f_204_, v___y_206_, v___x_218_, v___x_219_, v___x_212_);
lean_inc_ref(v_a_173_);
v___x_221_ = lean_apply_2(v___x_3645__overap_220_, v_a_173_, lean_box(0));
if (lean_obj_tag(v___x_221_) == 0)
{
lean_dec_ref_known(v___x_221_, 1);
v_a_182_ = v_val_209_;
goto v___jp_181_;
}
else
{
lean_dec_ref(v_repo_171_);
lean_dec_ref(v_name_170_);
return v___x_221_;
}
}
}
}
v___jp_222_:
{
uint8_t v___x_223_; 
lean_inc_ref(v_repo_171_);
v___x_223_ = l_Lake_GitRepo_hasNoDiff(v_repo_171_);
if (v___x_223_ == 0)
{
uint8_t v___x_224_; 
v___x_224_ = 1;
v___y_206_ = v___x_202_;
v___y_207_ = v___x_201_;
v___y_208_ = v___x_200_;
v_val_209_ = v___x_224_;
goto v___jp_205_;
}
else
{
uint8_t v___x_225_; 
v___x_225_ = 0;
v___y_206_ = v___x_202_;
v___y_207_ = v___x_201_;
v___y_208_ = v___x_200_;
v_val_209_ = v___x_225_;
goto v___jp_205_;
}
}
v___jp_226_:
{
if (lean_obj_tag(v___y_227_) == 0)
{
lean_dec_ref_known(v___y_227_, 1);
goto v___jp_222_;
}
else
{
lean_dec_ref(v_repo_171_);
lean_dec_ref(v_name_170_);
return v___y_227_;
}
}
v___jp_228_:
{
lean_object* v___x_229_; 
lean_inc_ref(v_repo_171_);
v___x_229_ = l_Lake_GitRepo_clean(v_repo_171_, v___x_202_);
if (lean_obj_tag(v___x_229_) == 0)
{
lean_object* v_a_230_; lean_object* v___x_231_; uint8_t v___x_232_; 
v_a_230_ = lean_ctor_get(v___x_229_, 1);
lean_inc(v_a_230_);
lean_dec_ref_known(v___x_229_, 2);
v___x_231_ = lean_array_get_size(v_a_230_);
v___x_232_ = lean_nat_dec_lt(v___x_201_, v___x_231_);
if (v___x_232_ == 0)
{
lean_dec(v_a_230_);
goto v___jp_222_;
}
else
{
lean_object* v___x_233_; uint8_t v___x_234_; 
v___x_233_ = lean_box(0);
v___x_234_ = lean_nat_dec_le(v___x_231_, v___x_231_);
if (v___x_234_ == 0)
{
if (v___x_232_ == 0)
{
lean_dec(v_a_230_);
goto v___jp_222_;
}
else
{
size_t v___x_235_; size_t v___x_236_; lean_object* v___x_3688__overap_237_; lean_object* v___x_238_; 
v___x_235_ = ((size_t)0ULL);
v___x_236_ = lean_usize_of_nat(v___x_231_);
v___x_3688__overap_237_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_200_, v___f_204_, v_a_230_, v___x_235_, v___x_236_, v___x_233_);
lean_inc_ref(v_a_173_);
v___x_238_ = lean_apply_2(v___x_3688__overap_237_, v_a_173_, lean_box(0));
if (lean_obj_tag(v___x_238_) == 0)
{
lean_dec_ref_known(v___x_238_, 1);
goto v___jp_222_;
}
else
{
v___y_227_ = v___x_238_;
goto v___jp_226_;
}
}
}
else
{
size_t v___x_239_; size_t v___x_240_; lean_object* v___x_3697__overap_241_; lean_object* v___x_242_; 
v___x_239_ = ((size_t)0ULL);
v___x_240_ = lean_usize_of_nat(v___x_231_);
v___x_3697__overap_241_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_200_, v___f_204_, v_a_230_, v___x_239_, v___x_240_, v___x_233_);
lean_inc_ref(v_a_173_);
v___x_242_ = lean_apply_2(v___x_3697__overap_241_, v_a_173_, lean_box(0));
if (lean_obj_tag(v___x_242_) == 0)
{
lean_dec_ref_known(v___x_242_, 1);
goto v___jp_222_;
}
else
{
v___y_227_ = v___x_242_;
goto v___jp_226_;
}
}
}
}
else
{
lean_object* v_a_243_; lean_object* v___x_244_; uint8_t v___x_245_; 
v_a_243_ = lean_ctor_get(v___x_229_, 1);
lean_inc(v_a_243_);
lean_dec_ref_known(v___x_229_, 2);
v___x_244_ = lean_array_get_size(v_a_243_);
v___x_245_ = lean_nat_dec_lt(v___x_201_, v___x_244_);
if (v___x_245_ == 0)
{
lean_object* v___x_246_; lean_object* v___x_247_; 
lean_dec(v_a_243_);
lean_dec_ref(v_repo_171_);
lean_dec_ref(v_name_170_);
v___x_246_ = lean_box(0);
v___x_247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_247_, 0, v___x_246_);
return v___x_247_;
}
else
{
lean_object* v___x_248_; uint8_t v___x_249_; 
v___x_248_ = lean_box(0);
v___x_249_ = lean_nat_dec_le(v___x_244_, v___x_244_);
if (v___x_249_ == 0)
{
if (v___x_245_ == 0)
{
lean_dec(v_a_243_);
lean_dec_ref(v_repo_171_);
lean_dec_ref(v_name_170_);
goto v___jp_178_;
}
else
{
size_t v___x_250_; size_t v___x_251_; lean_object* v___x_3719__overap_252_; lean_object* v___x_253_; 
v___x_250_ = ((size_t)0ULL);
v___x_251_ = lean_usize_of_nat(v___x_244_);
v___x_3719__overap_252_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_200_, v___f_204_, v_a_243_, v___x_250_, v___x_251_, v___x_248_);
lean_inc_ref(v_a_173_);
v___x_253_ = lean_apply_2(v___x_3719__overap_252_, v_a_173_, lean_box(0));
if (lean_obj_tag(v___x_253_) == 0)
{
lean_dec_ref_known(v___x_253_, 1);
lean_dec_ref(v_repo_171_);
lean_dec_ref(v_name_170_);
goto v___jp_178_;
}
else
{
v___y_227_ = v___x_253_;
goto v___jp_226_;
}
}
}
else
{
size_t v___x_254_; size_t v___x_255_; lean_object* v___x_3727__overap_256_; lean_object* v___x_257_; 
v___x_254_ = ((size_t)0ULL);
v___x_255_ = lean_usize_of_nat(v___x_244_);
v___x_3727__overap_256_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_200_, v___f_204_, v_a_243_, v___x_254_, v___x_255_, v___x_248_);
lean_inc_ref(v_a_173_);
v___x_257_ = lean_apply_2(v___x_3727__overap_256_, v_a_173_, lean_box(0));
if (lean_obj_tag(v___x_257_) == 0)
{
lean_dec_ref_known(v___x_257_, 1);
lean_dec_ref(v_repo_171_);
lean_dec_ref(v_name_170_);
goto v___jp_178_;
}
else
{
v___y_227_ = v___x_257_;
goto v___jp_226_;
}
}
}
}
}
v___jp_258_:
{
if (lean_obj_tag(v___y_259_) == 0)
{
lean_dec_ref_known(v___y_259_, 1);
goto v___jp_228_;
}
else
{
lean_dec_ref(v_repo_171_);
lean_dec_ref(v_name_170_);
return v___y_259_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___boxed(lean_object* v_name_288_, lean_object* v_repo_289_, lean_object* v_rev_290_, lean_object* v_a_291_, lean_object* v_a_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout(v_name_288_, v_repo_289_, v_rev_290_, v_a_291_);
lean_dec_ref(v_a_291_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(lean_object* v_as_294_, size_t v_i_295_, size_t v_stop_296_, lean_object* v_b_297_, lean_object* v___y_298_){
_start:
{
uint8_t v___x_300_; 
v___x_300_ = lean_usize_dec_eq(v_i_295_, v_stop_296_);
if (v___x_300_ == 0)
{
lean_object* v___x_301_; lean_object* v___x_302_; size_t v___x_303_; size_t v___x_304_; 
v___x_301_ = lean_array_uget_borrowed(v_as_294_, v_i_295_);
lean_inc_ref(v___y_298_);
lean_inc(v___x_301_);
v___x_302_ = lean_apply_2(v___y_298_, v___x_301_, lean_box(0));
v___x_303_ = ((size_t)1ULL);
v___x_304_ = lean_usize_add(v_i_295_, v___x_303_);
v_i_295_ = v___x_304_;
v_b_297_ = v___x_302_;
goto _start;
}
else
{
lean_object* v___x_306_; 
v___x_306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_306_, 0, v_b_297_);
return v___x_306_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0___boxed(lean_object* v_as_307_, lean_object* v_i_308_, lean_object* v_stop_309_, lean_object* v_b_310_, lean_object* v___y_311_, lean_object* v___y_312_){
_start:
{
size_t v_i_boxed_313_; size_t v_stop_boxed_314_; lean_object* v_res_315_; 
v_i_boxed_313_ = lean_unbox_usize(v_i_308_);
lean_dec(v_i_308_);
v_stop_boxed_314_ = lean_unbox_usize(v_stop_309_);
lean_dec(v_stop_309_);
v_res_315_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_as_307_, v_i_boxed_313_, v_stop_boxed_314_, v_b_310_, v___y_311_);
lean_dec_ref(v___y_311_);
lean_dec_ref(v_as_307_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo(lean_object* v_name_325_, lean_object* v_repo_326_, lean_object* v_url_327_, lean_object* v_rev_x3f_328_, lean_object* v_a_329_){
_start:
{
lean_object* v___y_341_; lean_object* v___y_352_; lean_object* v___y_375_; lean_object* v___y_380_; uint8_t v_a_381_; lean_object* v___y_389_; lean_object* v___y_437_; lean_object* v___y_438_; lean_object* v___y_440_; lean_object* v___y_441_; lean_object* v___y_470_; lean_object* v___y_471_; uint8_t v_a_472_; lean_object* v___y_480_; lean_object* v___y_481_; lean_object* v___y_482_; lean_object* v___y_484_; lean_object* v___y_485_; lean_object* v___y_486_; lean_object* v___y_487_; uint8_t v_val_488_; lean_object* v___y_500_; lean_object* v___y_501_; lean_object* v___y_508_; lean_object* v___y_509_; lean_object* v___y_510_; lean_object* v___y_512_; lean_object* v___y_513_; lean_object* v___y_542_; lean_object* v___y_543_; lean_object* v___y_544_; lean_object* v___y_546_; lean_object* v___y_547_; lean_object* v___y_548_; uint8_t v_val_549_; lean_object* v___y_561_; lean_object* v___y_562_; lean_object* v___y_563_; lean_object* v___y_564_; lean_object* v_a_565_; lean_object* v___y_608_; lean_object* v___y_609_; lean_object* v___y_610_; lean_object* v___y_611_; lean_object* v_a_612_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_680_; lean_object* v___y_681_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_716_; lean_object* v___y_717_; lean_object* v___y_718_; lean_object* v___y_719_; lean_object* v___y_721_; uint8_t v_a_722_; lean_object* v___y_730_; uint8_t v_a_731_; lean_object* v___y_739_; lean_object* v___y_740_; lean_object* v___y_741_; uint8_t v_val_742_; lean_object* v___y_754_; uint8_t v___y_755_; uint8_t v___y_756_; lean_object* v___y_761_; uint8_t v___y_762_; uint8_t v___y_763_; lean_object* v___y_764_; lean_object* v___y_766_; uint8_t v___y_767_; uint8_t v___y_768_; lean_object* v___y_797_; uint8_t v___y_798_; uint8_t v___y_799_; lean_object* v___y_800_; lean_object* v___y_802_; lean_object* v___y_803_; uint8_t v___y_804_; lean_object* v___y_805_; lean_object* v___y_806_; uint8_t v___y_807_; lean_object* v_a_808_; lean_object* v___y_852_; lean_object* v___y_853_; lean_object* v___y_854_; uint8_t v_val_855_; uint8_t v___y_867_; lean_object* v___y_868_; lean_object* v___y_869_; lean_object* v___y_870_; lean_object* v___y_871_; lean_object* v_a_872_; lean_object* v___y_893_; uint8_t v___y_894_; lean_object* v___y_895_; lean_object* v___y_896_; lean_object* v___y_897_; uint8_t v___y_911_; lean_object* v___y_912_; lean_object* v___y_913_; lean_object* v___y_914_; lean_object* v___y_915_; uint8_t v___y_917_; lean_object* v___y_918_; lean_object* v___y_919_; lean_object* v___y_920_; lean_object* v___y_921_; uint8_t v___y_923_; lean_object* v___y_924_; lean_object* v___y_925_; lean_object* v___y_926_; lean_object* v_a_927_; lean_object* v___y_1000_; lean_object* v___y_1001_; lean_object* v___y_1002_; uint8_t v_a_1003_; lean_object* v___y_1069_; lean_object* v___y_1070_; lean_object* v_a_1071_; lean_object* v___y_1086_; lean_object* v___y_1087_; lean_object* v_a_1088_; lean_object* v___y_1099_; lean_object* v___y_1100_; lean_object* v___y_1101_; lean_object* v___y_1102_; lean_object* v_val_1103_; lean_object* v___y_1115_; lean_object* v___y_1116_; uint8_t v_a_1117_; lean_object* v___y_1126_; 
if (lean_obj_tag(v_rev_x3f_328_) == 0)
{
lean_object* v___x_1139_; 
v___x_1139_ = l_Lake_Git_upstreamBranch;
v___y_1126_ = v___x_1139_;
goto v___jp_1125_;
}
else
{
lean_object* v_val_1140_; 
v_val_1140_ = lean_ctor_get(v_rev_x3f_328_, 0);
lean_inc(v_val_1140_);
lean_dec_ref_known(v_rev_x3f_328_, 1);
v___y_1126_ = v_val_1140_;
goto v___jp_1125_;
}
v___jp_331_:
{
lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_332_ = lean_box(0);
v___x_333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
return v___x_333_;
}
v___jp_334_:
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = lean_box(0);
v___x_336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
return v___x_336_;
}
v___jp_337_:
{
lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_338_ = lean_box(0);
v___x_339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
return v___x_339_;
}
v___jp_340_:
{
if (lean_obj_tag(v___y_341_) == 0)
{
lean_dec_ref_known(v___y_341_, 1);
goto v___jp_337_;
}
else
{
return v___y_341_;
}
}
v___jp_342_:
{
lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_343_ = lean_box(0);
v___x_344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_344_, 0, v___x_343_);
return v___x_344_;
}
v___jp_345_:
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = lean_box(0);
v___x_347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_347_, 0, v___x_346_);
return v___x_347_;
}
v___jp_348_:
{
lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_349_ = lean_box(0);
v___x_350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
return v___x_350_;
}
v___jp_351_:
{
if (lean_obj_tag(v___y_352_) == 0)
{
lean_dec_ref_known(v___y_352_, 1);
goto v___jp_348_;
}
else
{
return v___y_352_;
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
lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_357_ = lean_box(0);
v___x_358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
return v___x_358_;
}
v___jp_359_:
{
lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_360_ = lean_box(0);
v___x_361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_361_, 0, v___x_360_);
return v___x_361_;
}
v___jp_362_:
{
lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_363_ = lean_box(0);
v___x_364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_364_, 0, v___x_363_);
return v___x_364_;
}
v___jp_365_:
{
lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = lean_box(0);
v___x_367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_367_, 0, v___x_366_);
return v___x_367_;
}
v___jp_368_:
{
lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_369_ = lean_box(0);
v___x_370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_370_, 0, v___x_369_);
return v___x_370_;
}
v___jp_371_:
{
lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_372_ = lean_box(0);
v___x_373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_373_, 0, v___x_372_);
return v___x_373_;
}
v___jp_374_:
{
if (lean_obj_tag(v___y_375_) == 0)
{
lean_dec_ref_known(v___y_375_, 1);
goto v___jp_371_;
}
else
{
return v___y_375_;
}
}
v___jp_376_:
{
lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_377_ = lean_box(0);
v___x_378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_378_, 0, v___x_377_);
return v___x_378_;
}
v___jp_379_:
{
if (v_a_381_ == 0)
{
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
goto v___jp_371_;
}
else
{
lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; uint8_t v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_382_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff___closed__0));
v___x_383_ = lean_string_append(v_name_325_, v___x_382_);
v___x_384_ = lean_string_append(v___x_383_, v_repo_326_);
lean_dec_ref(v_repo_326_);
v___x_385_ = 2;
v___x_386_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_386_, 0, v___x_384_);
lean_ctor_set_uint8(v___x_386_, sizeof(void*)*1, v___x_385_);
lean_inc_ref(v___y_380_);
v___x_387_ = lean_apply_2(v___y_380_, v___x_386_, lean_box(0));
goto v___jp_371_;
}
}
v___jp_388_:
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_390_ = lean_unsigned_to_nat(0u);
v___x_391_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_392_ = l_Lake_GitRepo_gcAuto(v_repo_326_, v___x_391_);
if (lean_obj_tag(v___x_392_) == 0)
{
lean_object* v_a_393_; lean_object* v_a_394_; lean_object* v___x_395_; uint8_t v___x_396_; 
v_a_393_ = lean_ctor_get(v___x_392_, 0);
lean_inc(v_a_393_);
v_a_394_ = lean_ctor_get(v___x_392_, 1);
lean_inc(v_a_394_);
lean_dec_ref_known(v___x_392_, 2);
v___x_395_ = lean_array_get_size(v_a_394_);
v___x_396_ = lean_nat_dec_lt(v___x_390_, v___x_395_);
if (v___x_396_ == 0)
{
lean_object* v___x_397_; 
lean_dec(v_a_394_);
v___x_397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_397_, 0, v_a_393_);
return v___x_397_;
}
else
{
lean_object* v___x_398_; uint8_t v___x_399_; 
v___x_398_ = lean_box(0);
v___x_399_ = lean_nat_dec_le(v___x_395_, v___x_395_);
if (v___x_399_ == 0)
{
if (v___x_396_ == 0)
{
lean_object* v___x_400_; 
lean_dec(v_a_394_);
v___x_400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_400_, 0, v_a_393_);
return v___x_400_;
}
else
{
size_t v___x_401_; size_t v___x_402_; lean_object* v___x_403_; 
v___x_401_ = ((size_t)0ULL);
v___x_402_ = lean_usize_of_nat(v___x_395_);
v___x_403_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_394_, v___x_401_, v___x_402_, v___x_398_, v___y_389_);
lean_dec(v_a_394_);
if (lean_obj_tag(v___x_403_) == 0)
{
lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_410_; 
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_410_ == 0)
{
lean_object* v_unused_411_; 
v_unused_411_ = lean_ctor_get(v___x_403_, 0);
lean_dec(v_unused_411_);
v___x_405_ = v___x_403_;
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
else
{
lean_dec(v___x_403_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_408_; 
if (v_isShared_406_ == 0)
{
lean_ctor_set(v___x_405_, 0, v_a_393_);
v___x_408_ = v___x_405_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v_a_393_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
else
{
lean_dec(v_a_393_);
return v___x_403_;
}
}
}
else
{
size_t v___x_412_; size_t v___x_413_; lean_object* v___x_414_; 
v___x_412_ = ((size_t)0ULL);
v___x_413_ = lean_usize_of_nat(v___x_395_);
v___x_414_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_394_, v___x_412_, v___x_413_, v___x_398_, v___y_389_);
lean_dec(v_a_394_);
if (lean_obj_tag(v___x_414_) == 0)
{
lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_421_; 
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_421_ == 0)
{
lean_object* v_unused_422_; 
v_unused_422_ = lean_ctor_get(v___x_414_, 0);
lean_dec(v_unused_422_);
v___x_416_ = v___x_414_;
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
else
{
lean_dec(v___x_414_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_419_; 
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 0, v_a_393_);
v___x_419_ = v___x_416_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_a_393_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
else
{
lean_dec(v_a_393_);
return v___x_414_;
}
}
}
}
else
{
lean_object* v_a_423_; lean_object* v___x_424_; uint8_t v___x_425_; 
v_a_423_ = lean_ctor_get(v___x_392_, 1);
lean_inc(v_a_423_);
lean_dec_ref_known(v___x_392_, 2);
v___x_424_ = lean_array_get_size(v_a_423_);
v___x_425_ = lean_nat_dec_lt(v___x_390_, v___x_424_);
if (v___x_425_ == 0)
{
lean_object* v___x_426_; lean_object* v___x_427_; 
lean_dec(v_a_423_);
v___x_426_ = lean_box(0);
v___x_427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_427_, 0, v___x_426_);
return v___x_427_;
}
else
{
lean_object* v___x_428_; uint8_t v___x_429_; 
v___x_428_ = lean_box(0);
v___x_429_ = lean_nat_dec_le(v___x_424_, v___x_424_);
if (v___x_429_ == 0)
{
if (v___x_425_ == 0)
{
lean_dec(v_a_423_);
goto v___jp_359_;
}
else
{
size_t v___x_430_; size_t v___x_431_; lean_object* v___x_432_; 
v___x_430_ = ((size_t)0ULL);
v___x_431_ = lean_usize_of_nat(v___x_424_);
v___x_432_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_423_, v___x_430_, v___x_431_, v___x_428_, v___y_389_);
lean_dec(v_a_423_);
if (lean_obj_tag(v___x_432_) == 0)
{
lean_dec_ref_known(v___x_432_, 1);
goto v___jp_359_;
}
else
{
return v___x_432_;
}
}
}
else
{
size_t v___x_433_; size_t v___x_434_; lean_object* v___x_435_; 
v___x_433_ = ((size_t)0ULL);
v___x_434_ = lean_usize_of_nat(v___x_424_);
v___x_435_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_423_, v___x_433_, v___x_434_, v___x_428_, v___y_389_);
lean_dec(v_a_423_);
if (lean_obj_tag(v___x_435_) == 0)
{
lean_dec_ref_known(v___x_435_, 1);
goto v___jp_359_;
}
else
{
return v___x_435_;
}
}
}
}
}
v___jp_436_:
{
if (lean_obj_tag(v___y_438_) == 0)
{
lean_dec_ref_known(v___y_438_, 1);
v___y_389_ = v___y_437_;
goto v___jp_388_;
}
else
{
lean_dec_ref(v_repo_326_);
return v___y_438_;
}
}
v___jp_439_:
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_442_ = lean_unsigned_to_nat(0u);
v___x_443_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_326_);
lean_inc_ref(v___y_440_);
v___x_444_ = l_Lake_GitRepo_pruneRemote(v___y_440_, v_repo_326_, v___x_443_);
if (lean_obj_tag(v___x_444_) == 0)
{
lean_object* v_a_445_; lean_object* v___x_446_; uint8_t v___x_447_; 
v_a_445_ = lean_ctor_get(v___x_444_, 1);
lean_inc(v_a_445_);
lean_dec_ref_known(v___x_444_, 2);
v___x_446_ = lean_array_get_size(v_a_445_);
v___x_447_ = lean_nat_dec_lt(v___x_442_, v___x_446_);
if (v___x_447_ == 0)
{
lean_dec(v_a_445_);
v___y_389_ = v___y_441_;
goto v___jp_388_;
}
else
{
lean_object* v___x_448_; uint8_t v___x_449_; 
v___x_448_ = lean_box(0);
v___x_449_ = lean_nat_dec_le(v___x_446_, v___x_446_);
if (v___x_449_ == 0)
{
if (v___x_447_ == 0)
{
lean_dec(v_a_445_);
v___y_389_ = v___y_441_;
goto v___jp_388_;
}
else
{
size_t v___x_450_; size_t v___x_451_; lean_object* v___x_452_; 
v___x_450_ = ((size_t)0ULL);
v___x_451_ = lean_usize_of_nat(v___x_446_);
v___x_452_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_445_, v___x_450_, v___x_451_, v___x_448_, v___y_441_);
lean_dec(v_a_445_);
if (lean_obj_tag(v___x_452_) == 0)
{
lean_dec_ref_known(v___x_452_, 1);
v___y_389_ = v___y_441_;
goto v___jp_388_;
}
else
{
v___y_437_ = v___y_441_;
v___y_438_ = v___x_452_;
goto v___jp_436_;
}
}
}
else
{
size_t v___x_453_; size_t v___x_454_; lean_object* v___x_455_; 
v___x_453_ = ((size_t)0ULL);
v___x_454_ = lean_usize_of_nat(v___x_446_);
v___x_455_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_445_, v___x_453_, v___x_454_, v___x_448_, v___y_441_);
lean_dec(v_a_445_);
if (lean_obj_tag(v___x_455_) == 0)
{
lean_dec_ref_known(v___x_455_, 1);
v___y_389_ = v___y_441_;
goto v___jp_388_;
}
else
{
v___y_437_ = v___y_441_;
v___y_438_ = v___x_455_;
goto v___jp_436_;
}
}
}
}
else
{
lean_object* v_a_456_; lean_object* v___x_457_; uint8_t v___x_458_; 
v_a_456_ = lean_ctor_get(v___x_444_, 1);
lean_inc(v_a_456_);
lean_dec_ref_known(v___x_444_, 2);
v___x_457_ = lean_array_get_size(v_a_456_);
v___x_458_ = lean_nat_dec_lt(v___x_442_, v___x_457_);
if (v___x_458_ == 0)
{
lean_object* v___x_459_; lean_object* v___x_460_; 
lean_dec(v_a_456_);
lean_dec_ref(v_repo_326_);
v___x_459_ = lean_box(0);
v___x_460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_460_, 0, v___x_459_);
return v___x_460_;
}
else
{
lean_object* v___x_461_; uint8_t v___x_462_; 
v___x_461_ = lean_box(0);
v___x_462_ = lean_nat_dec_le(v___x_457_, v___x_457_);
if (v___x_462_ == 0)
{
if (v___x_458_ == 0)
{
lean_dec(v_a_456_);
lean_dec_ref(v_repo_326_);
goto v___jp_362_;
}
else
{
size_t v___x_463_; size_t v___x_464_; lean_object* v___x_465_; 
v___x_463_ = ((size_t)0ULL);
v___x_464_ = lean_usize_of_nat(v___x_457_);
v___x_465_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_456_, v___x_463_, v___x_464_, v___x_461_, v___y_441_);
lean_dec(v_a_456_);
if (lean_obj_tag(v___x_465_) == 0)
{
lean_dec_ref_known(v___x_465_, 1);
lean_dec_ref(v_repo_326_);
goto v___jp_362_;
}
else
{
v___y_437_ = v___y_441_;
v___y_438_ = v___x_465_;
goto v___jp_436_;
}
}
}
else
{
size_t v___x_466_; size_t v___x_467_; lean_object* v___x_468_; 
v___x_466_ = ((size_t)0ULL);
v___x_467_ = lean_usize_of_nat(v___x_457_);
v___x_468_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_456_, v___x_466_, v___x_467_, v___x_461_, v___y_441_);
lean_dec(v_a_456_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_dec_ref_known(v___x_468_, 1);
lean_dec_ref(v_repo_326_);
goto v___jp_362_;
}
else
{
v___y_437_ = v___y_441_;
v___y_438_ = v___x_468_;
goto v___jp_436_;
}
}
}
}
}
v___jp_469_:
{
if (v_a_472_ == 0)
{
lean_dec_ref(v_name_325_);
v___y_440_ = v___y_470_;
v___y_441_ = v___y_471_;
goto v___jp_439_;
}
else
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; uint8_t v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_473_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff___closed__0));
v___x_474_ = lean_string_append(v_name_325_, v___x_473_);
v___x_475_ = lean_string_append(v___x_474_, v_repo_326_);
v___x_476_ = 2;
v___x_477_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_477_, 0, v___x_475_);
lean_ctor_set_uint8(v___x_477_, sizeof(void*)*1, v___x_476_);
lean_inc_ref(v___y_471_);
v___x_478_ = lean_apply_2(v___y_471_, v___x_477_, lean_box(0));
v___y_440_ = v___y_470_;
v___y_441_ = v___y_471_;
goto v___jp_439_;
}
}
v___jp_479_:
{
if (lean_obj_tag(v___y_482_) == 0)
{
lean_dec_ref_known(v___y_482_, 1);
v___y_440_ = v___y_480_;
v___y_441_ = v___y_481_;
goto v___jp_439_;
}
else
{
lean_dec_ref(v_repo_326_);
return v___y_482_;
}
}
v___jp_483_:
{
lean_object* v___x_489_; uint8_t v___x_490_; 
v___x_489_ = lean_array_get_size(v___y_486_);
v___x_490_ = lean_nat_dec_lt(v___y_487_, v___x_489_);
if (v___x_490_ == 0)
{
v___y_470_ = v___y_484_;
v___y_471_ = v___y_485_;
v_a_472_ = v_val_488_;
goto v___jp_469_;
}
else
{
lean_object* v___x_491_; uint8_t v___x_492_; 
v___x_491_ = lean_box(0);
v___x_492_ = lean_nat_dec_le(v___x_489_, v___x_489_);
if (v___x_492_ == 0)
{
if (v___x_490_ == 0)
{
v___y_470_ = v___y_484_;
v___y_471_ = v___y_485_;
v_a_472_ = v_val_488_;
goto v___jp_469_;
}
else
{
size_t v___x_493_; size_t v___x_494_; lean_object* v___x_495_; 
v___x_493_ = ((size_t)0ULL);
v___x_494_ = lean_usize_of_nat(v___x_489_);
v___x_495_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_486_, v___x_493_, v___x_494_, v___x_491_, v___y_485_);
if (lean_obj_tag(v___x_495_) == 0)
{
lean_dec_ref_known(v___x_495_, 1);
v___y_470_ = v___y_484_;
v___y_471_ = v___y_485_;
v_a_472_ = v_val_488_;
goto v___jp_469_;
}
else
{
lean_dec_ref(v_name_325_);
v___y_480_ = v___y_484_;
v___y_481_ = v___y_485_;
v___y_482_ = v___x_495_;
goto v___jp_479_;
}
}
}
else
{
size_t v___x_496_; size_t v___x_497_; lean_object* v___x_498_; 
v___x_496_ = ((size_t)0ULL);
v___x_497_ = lean_usize_of_nat(v___x_489_);
v___x_498_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_486_, v___x_496_, v___x_497_, v___x_491_, v___y_485_);
if (lean_obj_tag(v___x_498_) == 0)
{
lean_dec_ref_known(v___x_498_, 1);
v___y_470_ = v___y_484_;
v___y_471_ = v___y_485_;
v_a_472_ = v_val_488_;
goto v___jp_469_;
}
else
{
lean_dec_ref(v_name_325_);
v___y_480_ = v___y_484_;
v___y_481_ = v___y_485_;
v___y_482_ = v___x_498_;
goto v___jp_479_;
}
}
}
}
v___jp_499_:
{
uint8_t v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
lean_inc_ref(v_repo_326_);
v___x_502_ = l_Lake_GitRepo_hasNoDiff(v_repo_326_);
v___x_503_ = lean_unsigned_to_nat(0u);
v___x_504_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
if (v___x_502_ == 0)
{
uint8_t v___x_505_; 
v___x_505_ = 1;
v___y_484_ = v___y_500_;
v___y_485_ = v___y_501_;
v___y_486_ = v___x_504_;
v___y_487_ = v___x_503_;
v_val_488_ = v___x_505_;
goto v___jp_483_;
}
else
{
uint8_t v___x_506_; 
v___x_506_ = 0;
v___y_484_ = v___y_500_;
v___y_485_ = v___y_501_;
v___y_486_ = v___x_504_;
v___y_487_ = v___x_503_;
v_val_488_ = v___x_506_;
goto v___jp_483_;
}
}
v___jp_507_:
{
if (lean_obj_tag(v___y_510_) == 0)
{
lean_dec_ref_known(v___y_510_, 1);
v___y_500_ = v___y_508_;
v___y_501_ = v___y_509_;
goto v___jp_499_;
}
else
{
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
return v___y_510_;
}
}
v___jp_511_:
{
lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_514_ = lean_unsigned_to_nat(0u);
v___x_515_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_326_);
v___x_516_ = l_Lake_GitRepo_clean(v_repo_326_, v___x_515_);
if (lean_obj_tag(v___x_516_) == 0)
{
lean_object* v_a_517_; lean_object* v___x_518_; uint8_t v___x_519_; 
v_a_517_ = lean_ctor_get(v___x_516_, 1);
lean_inc(v_a_517_);
lean_dec_ref_known(v___x_516_, 2);
v___x_518_ = lean_array_get_size(v_a_517_);
v___x_519_ = lean_nat_dec_lt(v___x_514_, v___x_518_);
if (v___x_519_ == 0)
{
lean_dec(v_a_517_);
v___y_500_ = v___y_512_;
v___y_501_ = v___y_513_;
goto v___jp_499_;
}
else
{
lean_object* v___x_520_; uint8_t v___x_521_; 
v___x_520_ = lean_box(0);
v___x_521_ = lean_nat_dec_le(v___x_518_, v___x_518_);
if (v___x_521_ == 0)
{
if (v___x_519_ == 0)
{
lean_dec(v_a_517_);
v___y_500_ = v___y_512_;
v___y_501_ = v___y_513_;
goto v___jp_499_;
}
else
{
size_t v___x_522_; size_t v___x_523_; lean_object* v___x_524_; 
v___x_522_ = ((size_t)0ULL);
v___x_523_ = lean_usize_of_nat(v___x_518_);
v___x_524_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_517_, v___x_522_, v___x_523_, v___x_520_, v___y_513_);
lean_dec(v_a_517_);
if (lean_obj_tag(v___x_524_) == 0)
{
lean_dec_ref_known(v___x_524_, 1);
v___y_500_ = v___y_512_;
v___y_501_ = v___y_513_;
goto v___jp_499_;
}
else
{
v___y_508_ = v___y_512_;
v___y_509_ = v___y_513_;
v___y_510_ = v___x_524_;
goto v___jp_507_;
}
}
}
else
{
size_t v___x_525_; size_t v___x_526_; lean_object* v___x_527_; 
v___x_525_ = ((size_t)0ULL);
v___x_526_ = lean_usize_of_nat(v___x_518_);
v___x_527_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_517_, v___x_525_, v___x_526_, v___x_520_, v___y_513_);
lean_dec(v_a_517_);
if (lean_obj_tag(v___x_527_) == 0)
{
lean_dec_ref_known(v___x_527_, 1);
v___y_500_ = v___y_512_;
v___y_501_ = v___y_513_;
goto v___jp_499_;
}
else
{
v___y_508_ = v___y_512_;
v___y_509_ = v___y_513_;
v___y_510_ = v___x_527_;
goto v___jp_507_;
}
}
}
}
else
{
lean_object* v_a_528_; lean_object* v___x_529_; uint8_t v___x_530_; 
v_a_528_ = lean_ctor_get(v___x_516_, 1);
lean_inc(v_a_528_);
lean_dec_ref_known(v___x_516_, 2);
v___x_529_ = lean_array_get_size(v_a_528_);
v___x_530_ = lean_nat_dec_lt(v___x_514_, v___x_529_);
if (v___x_530_ == 0)
{
lean_object* v___x_531_; lean_object* v___x_532_; 
lean_dec(v_a_528_);
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
v___x_531_ = lean_box(0);
v___x_532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_532_, 0, v___x_531_);
return v___x_532_;
}
else
{
lean_object* v___x_533_; uint8_t v___x_534_; 
v___x_533_ = lean_box(0);
v___x_534_ = lean_nat_dec_le(v___x_529_, v___x_529_);
if (v___x_534_ == 0)
{
if (v___x_530_ == 0)
{
lean_dec(v_a_528_);
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
goto v___jp_365_;
}
else
{
size_t v___x_535_; size_t v___x_536_; lean_object* v___x_537_; 
v___x_535_ = ((size_t)0ULL);
v___x_536_ = lean_usize_of_nat(v___x_529_);
v___x_537_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_528_, v___x_535_, v___x_536_, v___x_533_, v___y_513_);
lean_dec(v_a_528_);
if (lean_obj_tag(v___x_537_) == 0)
{
lean_dec_ref_known(v___x_537_, 1);
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
goto v___jp_365_;
}
else
{
v___y_508_ = v___y_512_;
v___y_509_ = v___y_513_;
v___y_510_ = v___x_537_;
goto v___jp_507_;
}
}
}
else
{
size_t v___x_538_; size_t v___x_539_; lean_object* v___x_540_; 
v___x_538_ = ((size_t)0ULL);
v___x_539_ = lean_usize_of_nat(v___x_529_);
v___x_540_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_528_, v___x_538_, v___x_539_, v___x_533_, v___y_513_);
lean_dec(v_a_528_);
if (lean_obj_tag(v___x_540_) == 0)
{
lean_dec_ref_known(v___x_540_, 1);
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
goto v___jp_365_;
}
else
{
v___y_508_ = v___y_512_;
v___y_509_ = v___y_513_;
v___y_510_ = v___x_540_;
goto v___jp_507_;
}
}
}
}
}
v___jp_541_:
{
if (lean_obj_tag(v___y_544_) == 0)
{
lean_dec_ref_known(v___y_544_, 1);
v___y_512_ = v___y_542_;
v___y_513_ = v___y_543_;
goto v___jp_511_;
}
else
{
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
return v___y_544_;
}
}
v___jp_545_:
{
lean_object* v___x_550_; uint8_t v___x_551_; 
v___x_550_ = lean_array_get_size(v___y_548_);
v___x_551_ = lean_nat_dec_lt(v___y_547_, v___x_550_);
if (v___x_551_ == 0)
{
v___y_380_ = v___y_546_;
v_a_381_ = v_val_549_;
goto v___jp_379_;
}
else
{
lean_object* v___x_552_; uint8_t v___x_553_; 
v___x_552_ = lean_box(0);
v___x_553_ = lean_nat_dec_le(v___x_550_, v___x_550_);
if (v___x_553_ == 0)
{
if (v___x_551_ == 0)
{
v___y_380_ = v___y_546_;
v_a_381_ = v_val_549_;
goto v___jp_379_;
}
else
{
size_t v___x_554_; size_t v___x_555_; lean_object* v___x_556_; 
v___x_554_ = ((size_t)0ULL);
v___x_555_ = lean_usize_of_nat(v___x_550_);
v___x_556_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_548_, v___x_554_, v___x_555_, v___x_552_, v___y_546_);
if (lean_obj_tag(v___x_556_) == 0)
{
lean_dec_ref_known(v___x_556_, 1);
v___y_380_ = v___y_546_;
v_a_381_ = v_val_549_;
goto v___jp_379_;
}
else
{
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
v___y_375_ = v___x_556_;
goto v___jp_374_;
}
}
}
else
{
size_t v___x_557_; size_t v___x_558_; lean_object* v___x_559_; 
v___x_557_ = ((size_t)0ULL);
v___x_558_ = lean_usize_of_nat(v___x_550_);
v___x_559_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_548_, v___x_557_, v___x_558_, v___x_552_, v___y_546_);
if (lean_obj_tag(v___x_559_) == 0)
{
lean_dec_ref_known(v___x_559_, 1);
v___y_380_ = v___y_546_;
v_a_381_ = v_val_549_;
goto v___jp_379_;
}
else
{
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
v___y_375_ = v___x_559_;
goto v___jp_374_;
}
}
}
}
v___jp_560_:
{
lean_object* v___x_566_; uint8_t v___x_567_; 
v___x_566_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
v___x_567_ = l_Option_instDecidableEq___redArg(v___x_566_, v_a_565_, v___y_564_);
if (v___x_567_ == 0)
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; uint8_t v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_568_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__0));
lean_inc_ref(v_name_325_);
v___x_569_ = lean_string_append(v_name_325_, v___x_568_);
v___x_570_ = lean_string_append(v___x_569_, v___y_561_);
v___x_571_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__1));
v___x_572_ = lean_string_append(v___x_570_, v___x_571_);
v___x_573_ = 1;
v___x_574_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_574_, 0, v___x_572_);
lean_ctor_set_uint8(v___x_574_, sizeof(void*)*1, v___x_573_);
lean_inc_ref(v___y_563_);
v___x_575_ = lean_apply_2(v___y_563_, v___x_574_, lean_box(0));
v___x_576_ = lean_unsigned_to_nat(0u);
v___x_577_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_326_);
v___x_578_ = l_Lake_GitRepo_checkoutDetach(v___y_561_, v_repo_326_, v___x_577_);
if (lean_obj_tag(v___x_578_) == 0)
{
lean_object* v_a_579_; lean_object* v___x_580_; uint8_t v___x_581_; 
v_a_579_ = lean_ctor_get(v___x_578_, 1);
lean_inc(v_a_579_);
lean_dec_ref_known(v___x_578_, 2);
v___x_580_ = lean_array_get_size(v_a_579_);
v___x_581_ = lean_nat_dec_lt(v___x_576_, v___x_580_);
if (v___x_581_ == 0)
{
lean_dec(v_a_579_);
v___y_512_ = v___y_562_;
v___y_513_ = v___y_563_;
goto v___jp_511_;
}
else
{
lean_object* v___x_582_; uint8_t v___x_583_; 
v___x_582_ = lean_box(0);
v___x_583_ = lean_nat_dec_le(v___x_580_, v___x_580_);
if (v___x_583_ == 0)
{
if (v___x_581_ == 0)
{
lean_dec(v_a_579_);
v___y_512_ = v___y_562_;
v___y_513_ = v___y_563_;
goto v___jp_511_;
}
else
{
size_t v___x_584_; size_t v___x_585_; lean_object* v___x_586_; 
v___x_584_ = ((size_t)0ULL);
v___x_585_ = lean_usize_of_nat(v___x_580_);
v___x_586_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_579_, v___x_584_, v___x_585_, v___x_582_, v___y_563_);
lean_dec(v_a_579_);
if (lean_obj_tag(v___x_586_) == 0)
{
lean_dec_ref_known(v___x_586_, 1);
v___y_512_ = v___y_562_;
v___y_513_ = v___y_563_;
goto v___jp_511_;
}
else
{
v___y_542_ = v___y_562_;
v___y_543_ = v___y_563_;
v___y_544_ = v___x_586_;
goto v___jp_541_;
}
}
}
else
{
size_t v___x_587_; size_t v___x_588_; lean_object* v___x_589_; 
v___x_587_ = ((size_t)0ULL);
v___x_588_ = lean_usize_of_nat(v___x_580_);
v___x_589_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_579_, v___x_587_, v___x_588_, v___x_582_, v___y_563_);
lean_dec(v_a_579_);
if (lean_obj_tag(v___x_589_) == 0)
{
lean_dec_ref_known(v___x_589_, 1);
v___y_512_ = v___y_562_;
v___y_513_ = v___y_563_;
goto v___jp_511_;
}
else
{
v___y_542_ = v___y_562_;
v___y_543_ = v___y_563_;
v___y_544_ = v___x_589_;
goto v___jp_541_;
}
}
}
}
else
{
lean_object* v_a_590_; lean_object* v___x_591_; uint8_t v___x_592_; 
v_a_590_ = lean_ctor_get(v___x_578_, 1);
lean_inc(v_a_590_);
lean_dec_ref_known(v___x_578_, 2);
v___x_591_ = lean_array_get_size(v_a_590_);
v___x_592_ = lean_nat_dec_lt(v___x_576_, v___x_591_);
if (v___x_592_ == 0)
{
lean_object* v___x_593_; lean_object* v___x_594_; 
lean_dec(v_a_590_);
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
v___x_593_ = lean_box(0);
v___x_594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_594_, 0, v___x_593_);
return v___x_594_;
}
else
{
lean_object* v___x_595_; uint8_t v___x_596_; 
v___x_595_ = lean_box(0);
v___x_596_ = lean_nat_dec_le(v___x_591_, v___x_591_);
if (v___x_596_ == 0)
{
if (v___x_592_ == 0)
{
lean_dec(v_a_590_);
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
goto v___jp_368_;
}
else
{
size_t v___x_597_; size_t v___x_598_; lean_object* v___x_599_; 
v___x_597_ = ((size_t)0ULL);
v___x_598_ = lean_usize_of_nat(v___x_591_);
v___x_599_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_590_, v___x_597_, v___x_598_, v___x_595_, v___y_563_);
lean_dec(v_a_590_);
if (lean_obj_tag(v___x_599_) == 0)
{
lean_dec_ref_known(v___x_599_, 1);
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
goto v___jp_368_;
}
else
{
v___y_542_ = v___y_562_;
v___y_543_ = v___y_563_;
v___y_544_ = v___x_599_;
goto v___jp_541_;
}
}
}
else
{
size_t v___x_600_; size_t v___x_601_; lean_object* v___x_602_; 
v___x_600_ = ((size_t)0ULL);
v___x_601_ = lean_usize_of_nat(v___x_591_);
v___x_602_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_590_, v___x_600_, v___x_601_, v___x_595_, v___y_563_);
lean_dec(v_a_590_);
if (lean_obj_tag(v___x_602_) == 0)
{
lean_dec_ref_known(v___x_602_, 1);
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
goto v___jp_368_;
}
else
{
v___y_542_ = v___y_562_;
v___y_543_ = v___y_563_;
v___y_544_ = v___x_602_;
goto v___jp_541_;
}
}
}
}
}
else
{
uint8_t v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
lean_dec_ref(v___y_561_);
lean_inc_ref(v_repo_326_);
v___x_603_ = l_Lake_GitRepo_hasNoDiff(v_repo_326_);
v___x_604_ = lean_unsigned_to_nat(0u);
v___x_605_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
if (v___x_603_ == 0)
{
v___y_546_ = v___y_563_;
v___y_547_ = v___x_604_;
v___y_548_ = v___x_605_;
v_val_549_ = v___x_567_;
goto v___jp_545_;
}
else
{
uint8_t v___x_606_; 
v___x_606_ = 0;
v___y_546_ = v___y_563_;
v___y_547_ = v___x_604_;
v___y_548_ = v___x_605_;
v_val_549_ = v___x_606_;
goto v___jp_545_;
}
}
}
v___jp_607_:
{
if (lean_obj_tag(v_a_612_) == 1)
{
lean_object* v_val_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; uint8_t v___x_617_; 
lean_dec_ref(v___y_611_);
lean_dec_ref(v___y_610_);
v_val_613_ = lean_ctor_get(v_a_612_, 0);
lean_inc(v_val_613_);
v___x_614_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__0));
lean_inc_ref(v_repo_326_);
v___x_615_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_614_, v_repo_326_);
v___x_616_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_617_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_617_ == 0)
{
v___y_561_ = v_val_613_;
v___y_562_ = v___y_608_;
v___y_563_ = v___y_609_;
v___y_564_ = v_a_612_;
v_a_565_ = v___x_615_;
goto v___jp_560_;
}
else
{
lean_object* v___x_618_; uint8_t v___x_619_; 
v___x_618_ = lean_box(0);
v___x_619_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
if (v___x_619_ == 0)
{
if (v___x_617_ == 0)
{
v___y_561_ = v_val_613_;
v___y_562_ = v___y_608_;
v___y_563_ = v___y_609_;
v___y_564_ = v_a_612_;
v_a_565_ = v___x_615_;
goto v___jp_560_;
}
else
{
size_t v___x_620_; size_t v___x_621_; lean_object* v___x_622_; 
v___x_620_ = ((size_t)0ULL);
v___x_621_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8);
v___x_622_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_616_, v___x_620_, v___x_621_, v___x_618_, v___y_609_);
if (lean_obj_tag(v___x_622_) == 0)
{
lean_dec_ref_known(v___x_622_, 1);
v___y_561_ = v_val_613_;
v___y_562_ = v___y_608_;
v___y_563_ = v___y_609_;
v___y_564_ = v_a_612_;
v_a_565_ = v___x_615_;
goto v___jp_560_;
}
else
{
lean_dec(v___x_615_);
lean_dec_ref_known(v_a_612_, 1);
lean_dec(v_val_613_);
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
return v___x_622_;
}
}
}
else
{
size_t v___x_623_; size_t v___x_624_; lean_object* v___x_625_; 
v___x_623_ = ((size_t)0ULL);
v___x_624_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8);
v___x_625_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_616_, v___x_623_, v___x_624_, v___x_618_, v___y_609_);
if (lean_obj_tag(v___x_625_) == 0)
{
lean_dec_ref_known(v___x_625_, 1);
v___y_561_ = v_val_613_;
v___y_562_ = v___y_608_;
v___y_563_ = v___y_609_;
v___y_564_ = v_a_612_;
v_a_565_ = v___x_615_;
goto v___jp_560_;
}
else
{
lean_dec(v___x_615_);
lean_dec_ref_known(v_a_612_, 1);
lean_dec(v_val_613_);
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
return v___x_625_;
}
}
}
}
else
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; uint8_t v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
lean_dec(v_a_612_);
lean_dec_ref(v_repo_326_);
v___x_626_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__1));
v___x_627_ = lean_string_append(v_name_325_, v___x_626_);
v___x_628_ = lean_string_append(v___x_627_, v___y_611_);
lean_dec_ref(v___y_611_);
v___x_629_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__2));
v___x_630_ = lean_string_append(v___x_628_, v___x_629_);
v___x_631_ = lean_string_append(v___x_630_, v___y_610_);
lean_dec_ref(v___y_610_);
v___x_632_ = 3;
v___x_633_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_633_, 0, v___x_631_);
lean_ctor_set_uint8(v___x_633_, sizeof(void*)*1, v___x_632_);
lean_inc_ref(v___y_609_);
v___x_634_ = lean_apply_2(v___y_609_, v___x_633_, lean_box(0));
v___x_635_ = lean_box(0);
v___x_636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_636_, 0, v___x_635_);
return v___x_636_;
}
}
v___jp_637_:
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; uint8_t v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_642_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__3));
lean_inc_ref(v_name_325_);
v___x_643_ = lean_string_append(v_name_325_, v___x_642_);
v___x_644_ = lean_string_append(v___x_643_, v___y_640_);
v___x_645_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__4));
v___x_646_ = lean_string_append(v___x_644_, v___x_645_);
v___x_647_ = lean_string_append(v___x_646_, v___y_639_);
v___x_648_ = 1;
v___x_649_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_649_, 0, v___x_647_);
lean_ctor_set_uint8(v___x_649_, sizeof(void*)*1, v___x_648_);
lean_inc_ref(v___y_641_);
v___x_650_ = lean_apply_2(v___y_641_, v___x_649_, lean_box(0));
v___x_651_ = lean_unsigned_to_nat(0u);
v___x_652_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v___y_640_);
lean_inc_ref(v___y_638_);
lean_inc_ref(v_repo_326_);
v___x_653_ = l_Lake_GitRepo_fetchRevision_x3f(v_repo_326_, v___y_638_, v___y_640_, v___x_652_);
if (lean_obj_tag(v___x_653_) == 0)
{
lean_object* v_a_654_; lean_object* v_a_655_; lean_object* v___x_656_; uint8_t v___x_657_; 
v_a_654_ = lean_ctor_get(v___x_653_, 0);
lean_inc(v_a_654_);
v_a_655_ = lean_ctor_get(v___x_653_, 1);
lean_inc(v_a_655_);
lean_dec_ref_known(v___x_653_, 2);
v___x_656_ = lean_array_get_size(v_a_655_);
v___x_657_ = lean_nat_dec_lt(v___x_651_, v___x_656_);
if (v___x_657_ == 0)
{
lean_dec(v_a_655_);
v___y_608_ = v___y_638_;
v___y_609_ = v___y_641_;
v___y_610_ = v___y_639_;
v___y_611_ = v___y_640_;
v_a_612_ = v_a_654_;
goto v___jp_607_;
}
else
{
lean_object* v___x_658_; uint8_t v___x_659_; 
v___x_658_ = lean_box(0);
v___x_659_ = lean_nat_dec_le(v___x_656_, v___x_656_);
if (v___x_659_ == 0)
{
if (v___x_657_ == 0)
{
lean_dec(v_a_655_);
v___y_608_ = v___y_638_;
v___y_609_ = v___y_641_;
v___y_610_ = v___y_639_;
v___y_611_ = v___y_640_;
v_a_612_ = v_a_654_;
goto v___jp_607_;
}
else
{
size_t v___x_660_; size_t v___x_661_; lean_object* v___x_662_; 
v___x_660_ = ((size_t)0ULL);
v___x_661_ = lean_usize_of_nat(v___x_656_);
v___x_662_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_655_, v___x_660_, v___x_661_, v___x_658_, v___y_641_);
lean_dec(v_a_655_);
if (lean_obj_tag(v___x_662_) == 0)
{
lean_dec_ref_known(v___x_662_, 1);
v___y_608_ = v___y_638_;
v___y_609_ = v___y_641_;
v___y_610_ = v___y_639_;
v___y_611_ = v___y_640_;
v_a_612_ = v_a_654_;
goto v___jp_607_;
}
else
{
lean_dec(v_a_654_);
lean_dec_ref(v___y_640_);
lean_dec_ref(v___y_639_);
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
return v___x_662_;
}
}
}
else
{
size_t v___x_663_; size_t v___x_664_; lean_object* v___x_665_; 
v___x_663_ = ((size_t)0ULL);
v___x_664_ = lean_usize_of_nat(v___x_656_);
v___x_665_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_655_, v___x_663_, v___x_664_, v___x_658_, v___y_641_);
lean_dec(v_a_655_);
if (lean_obj_tag(v___x_665_) == 0)
{
lean_dec_ref_known(v___x_665_, 1);
v___y_608_ = v___y_638_;
v___y_609_ = v___y_641_;
v___y_610_ = v___y_639_;
v___y_611_ = v___y_640_;
v_a_612_ = v_a_654_;
goto v___jp_607_;
}
else
{
lean_dec(v_a_654_);
lean_dec_ref(v___y_640_);
lean_dec_ref(v___y_639_);
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
return v___x_665_;
}
}
}
}
else
{
lean_object* v_a_666_; lean_object* v___x_667_; uint8_t v___x_668_; 
lean_dec_ref(v___y_640_);
lean_dec_ref(v___y_639_);
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
v_a_666_ = lean_ctor_get(v___x_653_, 1);
lean_inc(v_a_666_);
lean_dec_ref_known(v___x_653_, 2);
v___x_667_ = lean_array_get_size(v_a_666_);
v___x_668_ = lean_nat_dec_lt(v___x_651_, v___x_667_);
if (v___x_668_ == 0)
{
lean_object* v___x_669_; lean_object* v___x_670_; 
lean_dec(v_a_666_);
v___x_669_ = lean_box(0);
v___x_670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_670_, 0, v___x_669_);
return v___x_670_;
}
else
{
lean_object* v___x_671_; uint8_t v___x_672_; 
v___x_671_ = lean_box(0);
v___x_672_ = lean_nat_dec_le(v___x_667_, v___x_667_);
if (v___x_672_ == 0)
{
if (v___x_668_ == 0)
{
lean_dec(v_a_666_);
goto v___jp_376_;
}
else
{
size_t v___x_673_; size_t v___x_674_; lean_object* v___x_675_; 
v___x_673_ = ((size_t)0ULL);
v___x_674_ = lean_usize_of_nat(v___x_667_);
v___x_675_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_666_, v___x_673_, v___x_674_, v___x_671_, v___y_641_);
lean_dec(v_a_666_);
if (lean_obj_tag(v___x_675_) == 0)
{
lean_dec_ref_known(v___x_675_, 1);
goto v___jp_376_;
}
else
{
return v___x_675_;
}
}
}
else
{
size_t v___x_676_; size_t v___x_677_; lean_object* v___x_678_; 
v___x_676_ = ((size_t)0ULL);
v___x_677_ = lean_usize_of_nat(v___x_667_);
v___x_678_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_666_, v___x_676_, v___x_677_, v___x_671_, v___y_641_);
lean_dec(v_a_666_);
if (lean_obj_tag(v___x_678_) == 0)
{
lean_dec_ref_known(v___x_678_, 1);
goto v___jp_376_;
}
else
{
return v___x_678_;
}
}
}
}
}
v___jp_679_:
{
if (lean_obj_tag(v___y_683_) == 0)
{
lean_dec_ref_known(v___y_683_, 1);
v___y_638_ = v___y_680_;
v___y_639_ = v___y_681_;
v___y_640_ = v___y_682_;
v___y_641_ = v_a_329_;
goto v___jp_637_;
}
else
{
lean_dec_ref(v___y_682_);
lean_dec_ref(v___y_681_);
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
return v___y_683_;
}
}
v___jp_684_:
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_688_ = lean_unsigned_to_nat(0u);
v___x_689_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_326_);
lean_inc_ref(v___y_686_);
lean_inc_ref(v___y_685_);
v___x_690_ = l_Lake_GitRepo_addRemote(v___y_685_, v___y_686_, v_repo_326_, v___x_689_);
if (lean_obj_tag(v___x_690_) == 0)
{
lean_object* v_a_691_; lean_object* v___x_692_; uint8_t v___x_693_; 
v_a_691_ = lean_ctor_get(v___x_690_, 1);
lean_inc(v_a_691_);
lean_dec_ref_known(v___x_690_, 2);
v___x_692_ = lean_array_get_size(v_a_691_);
v___x_693_ = lean_nat_dec_lt(v___x_688_, v___x_692_);
if (v___x_693_ == 0)
{
lean_dec(v_a_691_);
v___y_638_ = v___y_685_;
v___y_639_ = v___y_686_;
v___y_640_ = v___y_687_;
v___y_641_ = v_a_329_;
goto v___jp_637_;
}
else
{
lean_object* v___x_694_; uint8_t v___x_695_; 
v___x_694_ = lean_box(0);
v___x_695_ = lean_nat_dec_le(v___x_692_, v___x_692_);
if (v___x_695_ == 0)
{
if (v___x_693_ == 0)
{
lean_dec(v_a_691_);
v___y_638_ = v___y_685_;
v___y_639_ = v___y_686_;
v___y_640_ = v___y_687_;
v___y_641_ = v_a_329_;
goto v___jp_637_;
}
else
{
size_t v___x_696_; size_t v___x_697_; lean_object* v___x_698_; 
v___x_696_ = ((size_t)0ULL);
v___x_697_ = lean_usize_of_nat(v___x_692_);
v___x_698_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_691_, v___x_696_, v___x_697_, v___x_694_, v_a_329_);
lean_dec(v_a_691_);
if (lean_obj_tag(v___x_698_) == 0)
{
lean_dec_ref_known(v___x_698_, 1);
v___y_638_ = v___y_685_;
v___y_639_ = v___y_686_;
v___y_640_ = v___y_687_;
v___y_641_ = v_a_329_;
goto v___jp_637_;
}
else
{
v___y_680_ = v___y_685_;
v___y_681_ = v___y_686_;
v___y_682_ = v___y_687_;
v___y_683_ = v___x_698_;
goto v___jp_679_;
}
}
}
else
{
size_t v___x_699_; size_t v___x_700_; lean_object* v___x_701_; 
v___x_699_ = ((size_t)0ULL);
v___x_700_ = lean_usize_of_nat(v___x_692_);
v___x_701_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_691_, v___x_699_, v___x_700_, v___x_694_, v_a_329_);
lean_dec(v_a_691_);
if (lean_obj_tag(v___x_701_) == 0)
{
lean_dec_ref_known(v___x_701_, 1);
v___y_638_ = v___y_685_;
v___y_639_ = v___y_686_;
v___y_640_ = v___y_687_;
v___y_641_ = v_a_329_;
goto v___jp_637_;
}
else
{
v___y_680_ = v___y_685_;
v___y_681_ = v___y_686_;
v___y_682_ = v___y_687_;
v___y_683_ = v___x_701_;
goto v___jp_679_;
}
}
}
}
else
{
lean_object* v_a_702_; lean_object* v___x_703_; uint8_t v___x_704_; 
v_a_702_ = lean_ctor_get(v___x_690_, 1);
lean_inc(v_a_702_);
lean_dec_ref_known(v___x_690_, 2);
v___x_703_ = lean_array_get_size(v_a_702_);
v___x_704_ = lean_nat_dec_lt(v___x_688_, v___x_703_);
if (v___x_704_ == 0)
{
lean_object* v___x_705_; lean_object* v___x_706_; 
lean_dec(v_a_702_);
lean_dec_ref(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
v___x_705_ = lean_box(0);
v___x_706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_706_, 0, v___x_705_);
return v___x_706_;
}
else
{
lean_object* v___x_707_; uint8_t v___x_708_; 
v___x_707_ = lean_box(0);
v___x_708_ = lean_nat_dec_le(v___x_703_, v___x_703_);
if (v___x_708_ == 0)
{
if (v___x_704_ == 0)
{
lean_dec(v_a_702_);
lean_dec_ref(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
goto v___jp_356_;
}
else
{
size_t v___x_709_; size_t v___x_710_; lean_object* v___x_711_; 
v___x_709_ = ((size_t)0ULL);
v___x_710_ = lean_usize_of_nat(v___x_703_);
v___x_711_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_702_, v___x_709_, v___x_710_, v___x_707_, v_a_329_);
lean_dec(v_a_702_);
if (lean_obj_tag(v___x_711_) == 0)
{
lean_dec_ref_known(v___x_711_, 1);
lean_dec_ref(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
goto v___jp_356_;
}
else
{
v___y_680_ = v___y_685_;
v___y_681_ = v___y_686_;
v___y_682_ = v___y_687_;
v___y_683_ = v___x_711_;
goto v___jp_679_;
}
}
}
else
{
size_t v___x_712_; size_t v___x_713_; lean_object* v___x_714_; 
v___x_712_ = ((size_t)0ULL);
v___x_713_ = lean_usize_of_nat(v___x_703_);
v___x_714_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_702_, v___x_712_, v___x_713_, v___x_707_, v_a_329_);
lean_dec(v_a_702_);
if (lean_obj_tag(v___x_714_) == 0)
{
lean_dec_ref_known(v___x_714_, 1);
lean_dec_ref(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
goto v___jp_356_;
}
else
{
v___y_680_ = v___y_685_;
v___y_681_ = v___y_686_;
v___y_682_ = v___y_687_;
v___y_683_ = v___x_714_;
goto v___jp_679_;
}
}
}
}
}
v___jp_715_:
{
if (lean_obj_tag(v___y_719_) == 0)
{
lean_dec_ref_known(v___y_719_, 1);
v___y_685_ = v___y_716_;
v___y_686_ = v___y_717_;
v___y_687_ = v___y_718_;
goto v___jp_684_;
}
else
{
lean_dec_ref(v___y_718_);
lean_dec_ref(v___y_717_);
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
return v___y_719_;
}
}
v___jp_720_:
{
if (v_a_722_ == 0)
{
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
goto v___jp_348_;
}
else
{
lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; uint8_t v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_723_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff___closed__0));
v___x_724_ = lean_string_append(v_name_325_, v___x_723_);
v___x_725_ = lean_string_append(v___x_724_, v_repo_326_);
lean_dec_ref(v_repo_326_);
v___x_726_ = 2;
v___x_727_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_727_, 0, v___x_725_);
lean_ctor_set_uint8(v___x_727_, sizeof(void*)*1, v___x_726_);
lean_inc_ref(v___y_721_);
v___x_728_ = lean_apply_2(v___y_721_, v___x_727_, lean_box(0));
goto v___jp_348_;
}
}
v___jp_729_:
{
if (v_a_731_ == 0)
{
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
goto v___jp_337_;
}
else
{
lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; uint8_t v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_732_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff___closed__0));
v___x_733_ = lean_string_append(v_name_325_, v___x_732_);
v___x_734_ = lean_string_append(v___x_733_, v_repo_326_);
lean_dec_ref(v_repo_326_);
v___x_735_ = 2;
v___x_736_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_736_, 0, v___x_734_);
lean_ctor_set_uint8(v___x_736_, sizeof(void*)*1, v___x_735_);
lean_inc_ref(v___y_730_);
v___x_737_ = lean_apply_2(v___y_730_, v___x_736_, lean_box(0));
goto v___jp_337_;
}
}
v___jp_738_:
{
lean_object* v___x_743_; uint8_t v___x_744_; 
v___x_743_ = lean_array_get_size(v___y_740_);
v___x_744_ = lean_nat_dec_lt(v___y_741_, v___x_743_);
if (v___x_744_ == 0)
{
v___y_721_ = v___y_739_;
v_a_722_ = v_val_742_;
goto v___jp_720_;
}
else
{
lean_object* v___x_745_; uint8_t v___x_746_; 
v___x_745_ = lean_box(0);
v___x_746_ = lean_nat_dec_le(v___x_743_, v___x_743_);
if (v___x_746_ == 0)
{
if (v___x_744_ == 0)
{
v___y_721_ = v___y_739_;
v_a_722_ = v_val_742_;
goto v___jp_720_;
}
else
{
size_t v___x_747_; size_t v___x_748_; lean_object* v___x_749_; 
v___x_747_ = ((size_t)0ULL);
v___x_748_ = lean_usize_of_nat(v___x_743_);
v___x_749_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_740_, v___x_747_, v___x_748_, v___x_745_, v___y_739_);
if (lean_obj_tag(v___x_749_) == 0)
{
lean_dec_ref_known(v___x_749_, 1);
v___y_721_ = v___y_739_;
v_a_722_ = v_val_742_;
goto v___jp_720_;
}
else
{
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
v___y_352_ = v___x_749_;
goto v___jp_351_;
}
}
}
else
{
size_t v___x_750_; size_t v___x_751_; lean_object* v___x_752_; 
v___x_750_ = ((size_t)0ULL);
v___x_751_ = lean_usize_of_nat(v___x_743_);
v___x_752_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_740_, v___x_750_, v___x_751_, v___x_745_, v___y_739_);
if (lean_obj_tag(v___x_752_) == 0)
{
lean_dec_ref_known(v___x_752_, 1);
v___y_721_ = v___y_739_;
v_a_722_ = v_val_742_;
goto v___jp_720_;
}
else
{
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
v___y_352_ = v___x_752_;
goto v___jp_351_;
}
}
}
}
v___jp_753_:
{
uint8_t v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
lean_inc_ref(v_repo_326_);
v___x_757_ = l_Lake_GitRepo_hasNoDiff(v_repo_326_);
v___x_758_ = lean_unsigned_to_nat(0u);
v___x_759_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
if (v___x_757_ == 0)
{
v___y_739_ = v___y_754_;
v___y_740_ = v___x_759_;
v___y_741_ = v___x_758_;
v_val_742_ = v___y_755_;
goto v___jp_738_;
}
else
{
v___y_739_ = v___y_754_;
v___y_740_ = v___x_759_;
v___y_741_ = v___x_758_;
v_val_742_ = v___y_756_;
goto v___jp_738_;
}
}
v___jp_760_:
{
if (lean_obj_tag(v___y_764_) == 0)
{
lean_dec_ref_known(v___y_764_, 1);
v___y_754_ = v___y_761_;
v___y_755_ = v___y_762_;
v___y_756_ = v___y_763_;
goto v___jp_753_;
}
else
{
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
return v___y_764_;
}
}
v___jp_765_:
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_769_ = lean_unsigned_to_nat(0u);
v___x_770_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_326_);
v___x_771_ = l_Lake_GitRepo_clean(v_repo_326_, v___x_770_);
if (lean_obj_tag(v___x_771_) == 0)
{
lean_object* v_a_772_; lean_object* v___x_773_; uint8_t v___x_774_; 
v_a_772_ = lean_ctor_get(v___x_771_, 1);
lean_inc(v_a_772_);
lean_dec_ref_known(v___x_771_, 2);
v___x_773_ = lean_array_get_size(v_a_772_);
v___x_774_ = lean_nat_dec_lt(v___x_769_, v___x_773_);
if (v___x_774_ == 0)
{
lean_dec(v_a_772_);
v___y_754_ = v___y_766_;
v___y_755_ = v___y_767_;
v___y_756_ = v___y_768_;
goto v___jp_753_;
}
else
{
lean_object* v___x_775_; uint8_t v___x_776_; 
v___x_775_ = lean_box(0);
v___x_776_ = lean_nat_dec_le(v___x_773_, v___x_773_);
if (v___x_776_ == 0)
{
if (v___x_774_ == 0)
{
lean_dec(v_a_772_);
v___y_754_ = v___y_766_;
v___y_755_ = v___y_767_;
v___y_756_ = v___y_768_;
goto v___jp_753_;
}
else
{
size_t v___x_777_; size_t v___x_778_; lean_object* v___x_779_; 
v___x_777_ = ((size_t)0ULL);
v___x_778_ = lean_usize_of_nat(v___x_773_);
v___x_779_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_772_, v___x_777_, v___x_778_, v___x_775_, v___y_766_);
lean_dec(v_a_772_);
if (lean_obj_tag(v___x_779_) == 0)
{
lean_dec_ref_known(v___x_779_, 1);
v___y_754_ = v___y_766_;
v___y_755_ = v___y_767_;
v___y_756_ = v___y_768_;
goto v___jp_753_;
}
else
{
v___y_761_ = v___y_766_;
v___y_762_ = v___y_767_;
v___y_763_ = v___y_768_;
v___y_764_ = v___x_779_;
goto v___jp_760_;
}
}
}
else
{
size_t v___x_780_; size_t v___x_781_; lean_object* v___x_782_; 
v___x_780_ = ((size_t)0ULL);
v___x_781_ = lean_usize_of_nat(v___x_773_);
v___x_782_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_772_, v___x_780_, v___x_781_, v___x_775_, v___y_766_);
lean_dec(v_a_772_);
if (lean_obj_tag(v___x_782_) == 0)
{
lean_dec_ref_known(v___x_782_, 1);
v___y_754_ = v___y_766_;
v___y_755_ = v___y_767_;
v___y_756_ = v___y_768_;
goto v___jp_753_;
}
else
{
v___y_761_ = v___y_766_;
v___y_762_ = v___y_767_;
v___y_763_ = v___y_768_;
v___y_764_ = v___x_782_;
goto v___jp_760_;
}
}
}
}
else
{
lean_object* v_a_783_; lean_object* v___x_784_; uint8_t v___x_785_; 
v_a_783_ = lean_ctor_get(v___x_771_, 1);
lean_inc(v_a_783_);
lean_dec_ref_known(v___x_771_, 2);
v___x_784_ = lean_array_get_size(v_a_783_);
v___x_785_ = lean_nat_dec_lt(v___x_769_, v___x_784_);
if (v___x_785_ == 0)
{
lean_object* v___x_786_; lean_object* v___x_787_; 
lean_dec(v_a_783_);
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
v___x_786_ = lean_box(0);
v___x_787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_787_, 0, v___x_786_);
return v___x_787_;
}
else
{
lean_object* v___x_788_; uint8_t v___x_789_; 
v___x_788_ = lean_box(0);
v___x_789_ = lean_nat_dec_le(v___x_784_, v___x_784_);
if (v___x_789_ == 0)
{
if (v___x_785_ == 0)
{
lean_dec(v_a_783_);
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
goto v___jp_345_;
}
else
{
size_t v___x_790_; size_t v___x_791_; lean_object* v___x_792_; 
v___x_790_ = ((size_t)0ULL);
v___x_791_ = lean_usize_of_nat(v___x_784_);
v___x_792_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_783_, v___x_790_, v___x_791_, v___x_788_, v___y_766_);
lean_dec(v_a_783_);
if (lean_obj_tag(v___x_792_) == 0)
{
lean_dec_ref_known(v___x_792_, 1);
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
goto v___jp_345_;
}
else
{
v___y_761_ = v___y_766_;
v___y_762_ = v___y_767_;
v___y_763_ = v___y_768_;
v___y_764_ = v___x_792_;
goto v___jp_760_;
}
}
}
else
{
size_t v___x_793_; size_t v___x_794_; lean_object* v___x_795_; 
v___x_793_ = ((size_t)0ULL);
v___x_794_ = lean_usize_of_nat(v___x_784_);
v___x_795_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_783_, v___x_793_, v___x_794_, v___x_788_, v___y_766_);
lean_dec(v_a_783_);
if (lean_obj_tag(v___x_795_) == 0)
{
lean_dec_ref_known(v___x_795_, 1);
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
goto v___jp_345_;
}
else
{
v___y_761_ = v___y_766_;
v___y_762_ = v___y_767_;
v___y_763_ = v___y_768_;
v___y_764_ = v___x_795_;
goto v___jp_760_;
}
}
}
}
}
v___jp_796_:
{
if (lean_obj_tag(v___y_800_) == 0)
{
lean_dec_ref_known(v___y_800_, 1);
v___y_766_ = v___y_797_;
v___y_767_ = v___y_798_;
v___y_768_ = v___y_799_;
goto v___jp_765_;
}
else
{
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
return v___y_800_;
}
}
v___jp_801_:
{
if (lean_obj_tag(v_a_808_) == 0)
{
v___y_638_ = v___y_802_;
v___y_639_ = v___y_805_;
v___y_640_ = v___y_806_;
v___y_641_ = v___y_803_;
goto v___jp_637_;
}
else
{
lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_849_; 
v_isSharedCheck_849_ = !lean_is_exclusive(v_a_808_);
if (v_isSharedCheck_849_ == 0)
{
lean_object* v_unused_850_; 
v_unused_850_ = lean_ctor_get(v_a_808_, 0);
lean_dec(v_unused_850_);
v___x_810_ = v_a_808_;
v_isShared_811_ = v_isSharedCheck_849_;
goto v_resetjp_809_;
}
else
{
lean_dec(v_a_808_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_849_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
if (v___y_804_ == 0)
{
lean_del_object(v___x_810_);
v___y_638_ = v___y_802_;
v___y_639_ = v___y_805_;
v___y_640_ = v___y_806_;
v___y_641_ = v___y_803_;
goto v___jp_637_;
}
else
{
lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; uint8_t v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
lean_dec_ref(v___y_805_);
v___x_812_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__0));
lean_inc_ref(v_name_325_);
v___x_813_ = lean_string_append(v_name_325_, v___x_812_);
v___x_814_ = lean_string_append(v___x_813_, v___y_806_);
v___x_815_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__1));
v___x_816_ = lean_string_append(v___x_814_, v___x_815_);
v___x_817_ = 1;
v___x_818_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_818_, 0, v___x_816_);
lean_ctor_set_uint8(v___x_818_, sizeof(void*)*1, v___x_817_);
lean_inc_ref(v___y_803_);
v___x_819_ = lean_apply_2(v___y_803_, v___x_818_, lean_box(0));
v___x_820_ = lean_unsigned_to_nat(0u);
v___x_821_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_326_);
v___x_822_ = l_Lake_GitRepo_checkoutDetach(v___y_806_, v_repo_326_, v___x_821_);
if (lean_obj_tag(v___x_822_) == 0)
{
lean_object* v_a_823_; lean_object* v___x_824_; uint8_t v___x_825_; 
lean_del_object(v___x_810_);
v_a_823_ = lean_ctor_get(v___x_822_, 1);
lean_inc(v_a_823_);
lean_dec_ref_known(v___x_822_, 2);
v___x_824_ = lean_array_get_size(v_a_823_);
v___x_825_ = lean_nat_dec_lt(v___x_820_, v___x_824_);
if (v___x_825_ == 0)
{
lean_dec(v_a_823_);
v___y_766_ = v___y_803_;
v___y_767_ = v___y_804_;
v___y_768_ = v___y_807_;
goto v___jp_765_;
}
else
{
lean_object* v___x_826_; uint8_t v___x_827_; 
v___x_826_ = lean_box(0);
v___x_827_ = lean_nat_dec_le(v___x_824_, v___x_824_);
if (v___x_827_ == 0)
{
if (v___x_825_ == 0)
{
lean_dec(v_a_823_);
v___y_766_ = v___y_803_;
v___y_767_ = v___y_804_;
v___y_768_ = v___y_807_;
goto v___jp_765_;
}
else
{
size_t v___x_828_; size_t v___x_829_; lean_object* v___x_830_; 
v___x_828_ = ((size_t)0ULL);
v___x_829_ = lean_usize_of_nat(v___x_824_);
v___x_830_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_823_, v___x_828_, v___x_829_, v___x_826_, v___y_803_);
lean_dec(v_a_823_);
if (lean_obj_tag(v___x_830_) == 0)
{
lean_dec_ref_known(v___x_830_, 1);
v___y_766_ = v___y_803_;
v___y_767_ = v___y_804_;
v___y_768_ = v___y_807_;
goto v___jp_765_;
}
else
{
v___y_797_ = v___y_803_;
v___y_798_ = v___y_804_;
v___y_799_ = v___y_807_;
v___y_800_ = v___x_830_;
goto v___jp_796_;
}
}
}
else
{
size_t v___x_831_; size_t v___x_832_; lean_object* v___x_833_; 
v___x_831_ = ((size_t)0ULL);
v___x_832_ = lean_usize_of_nat(v___x_824_);
v___x_833_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_823_, v___x_831_, v___x_832_, v___x_826_, v___y_803_);
lean_dec(v_a_823_);
if (lean_obj_tag(v___x_833_) == 0)
{
lean_dec_ref_known(v___x_833_, 1);
v___y_766_ = v___y_803_;
v___y_767_ = v___y_804_;
v___y_768_ = v___y_807_;
goto v___jp_765_;
}
else
{
v___y_797_ = v___y_803_;
v___y_798_ = v___y_804_;
v___y_799_ = v___y_807_;
v___y_800_ = v___x_833_;
goto v___jp_796_;
}
}
}
}
else
{
lean_object* v_a_834_; lean_object* v___x_835_; uint8_t v___x_836_; 
v_a_834_ = lean_ctor_get(v___x_822_, 1);
lean_inc(v_a_834_);
lean_dec_ref_known(v___x_822_, 2);
v___x_835_ = lean_array_get_size(v_a_834_);
v___x_836_ = lean_nat_dec_lt(v___x_820_, v___x_835_);
if (v___x_836_ == 0)
{
lean_object* v___x_837_; lean_object* v___x_839_; 
lean_dec(v_a_834_);
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
v___x_837_ = lean_box(0);
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 0, v___x_837_);
v___x_839_ = v___x_810_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v___x_837_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
else
{
lean_object* v___x_841_; uint8_t v___x_842_; 
lean_del_object(v___x_810_);
v___x_841_ = lean_box(0);
v___x_842_ = lean_nat_dec_le(v___x_835_, v___x_835_);
if (v___x_842_ == 0)
{
if (v___x_836_ == 0)
{
lean_dec(v_a_834_);
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
goto v___jp_342_;
}
else
{
size_t v___x_843_; size_t v___x_844_; lean_object* v___x_845_; 
v___x_843_ = ((size_t)0ULL);
v___x_844_ = lean_usize_of_nat(v___x_835_);
v___x_845_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_834_, v___x_843_, v___x_844_, v___x_841_, v___y_803_);
lean_dec(v_a_834_);
if (lean_obj_tag(v___x_845_) == 0)
{
lean_dec_ref_known(v___x_845_, 1);
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
goto v___jp_342_;
}
else
{
v___y_797_ = v___y_803_;
v___y_798_ = v___y_804_;
v___y_799_ = v___y_807_;
v___y_800_ = v___x_845_;
goto v___jp_796_;
}
}
}
else
{
size_t v___x_846_; size_t v___x_847_; lean_object* v___x_848_; 
v___x_846_ = ((size_t)0ULL);
v___x_847_ = lean_usize_of_nat(v___x_835_);
v___x_848_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_834_, v___x_846_, v___x_847_, v___x_841_, v___y_803_);
lean_dec(v_a_834_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_dec_ref_known(v___x_848_, 1);
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
goto v___jp_342_;
}
else
{
v___y_797_ = v___y_803_;
v___y_798_ = v___y_804_;
v___y_799_ = v___y_807_;
v___y_800_ = v___x_848_;
goto v___jp_796_;
}
}
}
}
}
}
}
}
v___jp_851_:
{
lean_object* v___x_856_; uint8_t v___x_857_; 
v___x_856_ = lean_array_get_size(v___y_853_);
v___x_857_ = lean_nat_dec_lt(v___y_854_, v___x_856_);
if (v___x_857_ == 0)
{
v___y_730_ = v___y_852_;
v_a_731_ = v_val_855_;
goto v___jp_729_;
}
else
{
lean_object* v___x_858_; uint8_t v___x_859_; 
v___x_858_ = lean_box(0);
v___x_859_ = lean_nat_dec_le(v___x_856_, v___x_856_);
if (v___x_859_ == 0)
{
if (v___x_857_ == 0)
{
v___y_730_ = v___y_852_;
v_a_731_ = v_val_855_;
goto v___jp_729_;
}
else
{
size_t v___x_860_; size_t v___x_861_; lean_object* v___x_862_; 
v___x_860_ = ((size_t)0ULL);
v___x_861_ = lean_usize_of_nat(v___x_856_);
v___x_862_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_853_, v___x_860_, v___x_861_, v___x_858_, v___y_852_);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_dec_ref_known(v___x_862_, 1);
v___y_730_ = v___y_852_;
v_a_731_ = v_val_855_;
goto v___jp_729_;
}
else
{
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
v___y_341_ = v___x_862_;
goto v___jp_340_;
}
}
}
else
{
size_t v___x_863_; size_t v___x_864_; lean_object* v___x_865_; 
v___x_863_ = ((size_t)0ULL);
v___x_864_ = lean_usize_of_nat(v___x_856_);
v___x_865_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_853_, v___x_863_, v___x_864_, v___x_858_, v___y_852_);
if (lean_obj_tag(v___x_865_) == 0)
{
lean_dec_ref_known(v___x_865_, 1);
v___y_730_ = v___y_852_;
v_a_731_ = v_val_855_;
goto v___jp_729_;
}
else
{
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
v___y_341_ = v___x_865_;
goto v___jp_340_;
}
}
}
}
v___jp_866_:
{
lean_object* v___x_873_; lean_object* v___x_874_; uint8_t v___x_875_; 
v___x_873_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
lean_inc_ref(v___y_871_);
v___x_874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_874_, 0, v___y_871_);
v___x_875_ = l_Option_instDecidableEq___redArg(v___x_873_, v_a_872_, v___x_874_);
if (v___x_875_ == 0)
{
uint8_t v___x_876_; 
v___x_876_ = l_Lake_GitRev_isFullSha1(v___y_871_);
if (v___x_876_ == 0)
{
v___y_638_ = v___y_868_;
v___y_639_ = v___y_870_;
v___y_640_ = v___y_871_;
v___y_641_ = v___y_869_;
goto v___jp_637_;
}
else
{
lean_object* v___x_877_; lean_object* v___x_878_; uint8_t v___x_879_; 
lean_inc_ref(v_repo_326_);
lean_inc_ref(v___y_871_);
v___x_877_ = l_Lake_GitRepo_findCommit_x3f(v___y_871_, v_repo_326_);
v___x_878_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_879_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_879_ == 0)
{
v___y_802_ = v___y_868_;
v___y_803_ = v___y_869_;
v___y_804_ = v___x_876_;
v___y_805_ = v___y_870_;
v___y_806_ = v___y_871_;
v___y_807_ = v___x_875_;
v_a_808_ = v___x_877_;
goto v___jp_801_;
}
else
{
lean_object* v___x_880_; uint8_t v___x_881_; 
v___x_880_ = lean_box(0);
v___x_881_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
if (v___x_881_ == 0)
{
if (v___x_879_ == 0)
{
v___y_802_ = v___y_868_;
v___y_803_ = v___y_869_;
v___y_804_ = v___x_876_;
v___y_805_ = v___y_870_;
v___y_806_ = v___y_871_;
v___y_807_ = v___x_875_;
v_a_808_ = v___x_877_;
goto v___jp_801_;
}
else
{
size_t v___x_882_; size_t v___x_883_; lean_object* v___x_884_; 
v___x_882_ = ((size_t)0ULL);
v___x_883_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8);
v___x_884_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_878_, v___x_882_, v___x_883_, v___x_880_, v___y_869_);
if (lean_obj_tag(v___x_884_) == 0)
{
lean_dec_ref_known(v___x_884_, 1);
v___y_802_ = v___y_868_;
v___y_803_ = v___y_869_;
v___y_804_ = v___x_876_;
v___y_805_ = v___y_870_;
v___y_806_ = v___y_871_;
v___y_807_ = v___x_875_;
v_a_808_ = v___x_877_;
goto v___jp_801_;
}
else
{
lean_dec(v___x_877_);
lean_dec_ref(v___y_871_);
lean_dec_ref(v___y_870_);
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
return v___x_884_;
}
}
}
else
{
size_t v___x_885_; size_t v___x_886_; lean_object* v___x_887_; 
v___x_885_ = ((size_t)0ULL);
v___x_886_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8);
v___x_887_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_878_, v___x_885_, v___x_886_, v___x_880_, v___y_869_);
if (lean_obj_tag(v___x_887_) == 0)
{
lean_dec_ref_known(v___x_887_, 1);
v___y_802_ = v___y_868_;
v___y_803_ = v___y_869_;
v___y_804_ = v___x_876_;
v___y_805_ = v___y_870_;
v___y_806_ = v___y_871_;
v___y_807_ = v___x_875_;
v_a_808_ = v___x_877_;
goto v___jp_801_;
}
else
{
lean_dec(v___x_877_);
lean_dec_ref(v___y_871_);
lean_dec_ref(v___y_870_);
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
return v___x_887_;
}
}
}
}
}
else
{
uint8_t v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
lean_dec_ref(v___y_871_);
lean_dec_ref(v___y_870_);
lean_inc_ref(v_repo_326_);
v___x_888_ = l_Lake_GitRepo_hasNoDiff(v_repo_326_);
v___x_889_ = lean_unsigned_to_nat(0u);
v___x_890_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
if (v___x_888_ == 0)
{
v___y_852_ = v___y_869_;
v___y_853_ = v___x_890_;
v___y_854_ = v___x_889_;
v_val_855_ = v___y_867_;
goto v___jp_851_;
}
else
{
uint8_t v___x_891_; 
v___x_891_ = 0;
v___y_852_ = v___y_869_;
v___y_853_ = v___x_890_;
v___y_854_ = v___x_889_;
v_val_855_ = v___x_891_;
goto v___jp_851_;
}
}
}
v___jp_892_:
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; uint8_t v___x_901_; 
v___x_898_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__0));
lean_inc_ref(v_repo_326_);
v___x_899_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_898_, v_repo_326_);
v___x_900_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_901_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_901_ == 0)
{
v___y_867_ = v___y_894_;
v___y_868_ = v___y_893_;
v___y_869_ = v___y_897_;
v___y_870_ = v___y_895_;
v___y_871_ = v___y_896_;
v_a_872_ = v___x_899_;
goto v___jp_866_;
}
else
{
lean_object* v___x_902_; uint8_t v___x_903_; 
v___x_902_ = lean_box(0);
v___x_903_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
if (v___x_903_ == 0)
{
if (v___x_901_ == 0)
{
v___y_867_ = v___y_894_;
v___y_868_ = v___y_893_;
v___y_869_ = v___y_897_;
v___y_870_ = v___y_895_;
v___y_871_ = v___y_896_;
v_a_872_ = v___x_899_;
goto v___jp_866_;
}
else
{
size_t v___x_904_; size_t v___x_905_; lean_object* v___x_906_; 
v___x_904_ = ((size_t)0ULL);
v___x_905_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8);
v___x_906_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_900_, v___x_904_, v___x_905_, v___x_902_, v___y_897_);
if (lean_obj_tag(v___x_906_) == 0)
{
lean_dec_ref_known(v___x_906_, 1);
v___y_867_ = v___y_894_;
v___y_868_ = v___y_893_;
v___y_869_ = v___y_897_;
v___y_870_ = v___y_895_;
v___y_871_ = v___y_896_;
v_a_872_ = v___x_899_;
goto v___jp_866_;
}
else
{
lean_dec(v___x_899_);
lean_dec_ref(v___y_896_);
lean_dec_ref(v___y_895_);
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
return v___x_906_;
}
}
}
else
{
size_t v___x_907_; size_t v___x_908_; lean_object* v___x_909_; 
v___x_907_ = ((size_t)0ULL);
v___x_908_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8);
v___x_909_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_900_, v___x_907_, v___x_908_, v___x_902_, v___y_897_);
if (lean_obj_tag(v___x_909_) == 0)
{
lean_dec_ref_known(v___x_909_, 1);
v___y_867_ = v___y_894_;
v___y_868_ = v___y_893_;
v___y_869_ = v___y_897_;
v___y_870_ = v___y_895_;
v___y_871_ = v___y_896_;
v_a_872_ = v___x_899_;
goto v___jp_866_;
}
else
{
lean_dec(v___x_899_);
lean_dec_ref(v___y_896_);
lean_dec_ref(v___y_895_);
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
return v___x_909_;
}
}
}
}
v___jp_910_:
{
if (lean_obj_tag(v___y_915_) == 0)
{
lean_dec_ref_known(v___y_915_, 1);
v___y_893_ = v___y_912_;
v___y_894_ = v___y_911_;
v___y_895_ = v___y_913_;
v___y_896_ = v___y_914_;
v___y_897_ = v_a_329_;
goto v___jp_892_;
}
else
{
lean_dec_ref(v___y_914_);
lean_dec_ref(v___y_913_);
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
return v___y_915_;
}
}
v___jp_916_:
{
if (lean_obj_tag(v___y_921_) == 0)
{
lean_dec_ref_known(v___y_921_, 1);
v___y_893_ = v___y_918_;
v___y_894_ = v___y_917_;
v___y_895_ = v___y_919_;
v___y_896_ = v___y_920_;
v___y_897_ = v_a_329_;
goto v___jp_892_;
}
else
{
lean_dec_ref(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
return v___y_921_;
}
}
v___jp_922_:
{
if (lean_obj_tag(v_a_927_) == 1)
{
lean_object* v_val_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_971_; 
v_val_928_ = lean_ctor_get(v_a_927_, 0);
v_isSharedCheck_971_ = !lean_is_exclusive(v_a_927_);
if (v_isSharedCheck_971_ == 0)
{
v___x_930_ = v_a_927_;
v_isShared_931_ = v_isSharedCheck_971_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_val_928_);
lean_dec(v_a_927_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_971_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
uint8_t v___x_932_; 
v___x_932_ = lean_string_dec_eq(v_val_928_, v___y_925_);
if (v___x_932_ == 0)
{
lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; uint8_t v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_933_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__5));
lean_inc_ref(v_name_325_);
v___x_934_ = lean_string_append(v_name_325_, v___x_933_);
v___x_935_ = lean_string_append(v___x_934_, v_val_928_);
lean_dec(v_val_928_);
v___x_936_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__6));
v___x_937_ = lean_string_append(v___x_935_, v___x_936_);
v___x_938_ = lean_string_append(v___x_937_, v___y_925_);
v___x_939_ = 1;
v___x_940_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_940_, 0, v___x_938_);
lean_ctor_set_uint8(v___x_940_, sizeof(void*)*1, v___x_939_);
lean_inc_ref(v_a_329_);
v___x_941_ = lean_apply_2(v_a_329_, v___x_940_, lean_box(0));
v___x_942_ = lean_unsigned_to_nat(0u);
v___x_943_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_326_);
lean_inc_ref(v___y_925_);
lean_inc_ref(v___y_924_);
v___x_944_ = l_Lake_GitRepo_setRemoteUrl(v___y_924_, v___y_925_, v_repo_326_, v___x_943_);
if (lean_obj_tag(v___x_944_) == 0)
{
lean_object* v_a_945_; lean_object* v___x_946_; uint8_t v___x_947_; 
lean_del_object(v___x_930_);
v_a_945_ = lean_ctor_get(v___x_944_, 1);
lean_inc(v_a_945_);
lean_dec_ref_known(v___x_944_, 2);
v___x_946_ = lean_array_get_size(v_a_945_);
v___x_947_ = lean_nat_dec_lt(v___x_942_, v___x_946_);
if (v___x_947_ == 0)
{
lean_dec(v_a_945_);
v___y_893_ = v___y_924_;
v___y_894_ = v___y_923_;
v___y_895_ = v___y_925_;
v___y_896_ = v___y_926_;
v___y_897_ = v_a_329_;
goto v___jp_892_;
}
else
{
lean_object* v___x_948_; uint8_t v___x_949_; 
v___x_948_ = lean_box(0);
v___x_949_ = lean_nat_dec_le(v___x_946_, v___x_946_);
if (v___x_949_ == 0)
{
if (v___x_947_ == 0)
{
lean_dec(v_a_945_);
v___y_893_ = v___y_924_;
v___y_894_ = v___y_923_;
v___y_895_ = v___y_925_;
v___y_896_ = v___y_926_;
v___y_897_ = v_a_329_;
goto v___jp_892_;
}
else
{
size_t v___x_950_; size_t v___x_951_; lean_object* v___x_952_; 
v___x_950_ = ((size_t)0ULL);
v___x_951_ = lean_usize_of_nat(v___x_946_);
v___x_952_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_945_, v___x_950_, v___x_951_, v___x_948_, v_a_329_);
lean_dec(v_a_945_);
if (lean_obj_tag(v___x_952_) == 0)
{
lean_dec_ref_known(v___x_952_, 1);
v___y_893_ = v___y_924_;
v___y_894_ = v___y_923_;
v___y_895_ = v___y_925_;
v___y_896_ = v___y_926_;
v___y_897_ = v_a_329_;
goto v___jp_892_;
}
else
{
v___y_911_ = v___y_923_;
v___y_912_ = v___y_924_;
v___y_913_ = v___y_925_;
v___y_914_ = v___y_926_;
v___y_915_ = v___x_952_;
goto v___jp_910_;
}
}
}
else
{
size_t v___x_953_; size_t v___x_954_; lean_object* v___x_955_; 
v___x_953_ = ((size_t)0ULL);
v___x_954_ = lean_usize_of_nat(v___x_946_);
v___x_955_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_945_, v___x_953_, v___x_954_, v___x_948_, v_a_329_);
lean_dec(v_a_945_);
if (lean_obj_tag(v___x_955_) == 0)
{
lean_dec_ref_known(v___x_955_, 1);
v___y_893_ = v___y_924_;
v___y_894_ = v___y_923_;
v___y_895_ = v___y_925_;
v___y_896_ = v___y_926_;
v___y_897_ = v_a_329_;
goto v___jp_892_;
}
else
{
v___y_911_ = v___y_923_;
v___y_912_ = v___y_924_;
v___y_913_ = v___y_925_;
v___y_914_ = v___y_926_;
v___y_915_ = v___x_955_;
goto v___jp_910_;
}
}
}
}
else
{
lean_object* v_a_956_; lean_object* v___x_957_; uint8_t v___x_958_; 
v_a_956_ = lean_ctor_get(v___x_944_, 1);
lean_inc(v_a_956_);
lean_dec_ref_known(v___x_944_, 2);
v___x_957_ = lean_array_get_size(v_a_956_);
v___x_958_ = lean_nat_dec_lt(v___x_942_, v___x_957_);
if (v___x_958_ == 0)
{
lean_object* v___x_959_; lean_object* v___x_961_; 
lean_dec(v_a_956_);
lean_dec_ref(v___y_926_);
lean_dec_ref(v___y_925_);
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
v___x_959_ = lean_box(0);
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 0, v___x_959_);
v___x_961_ = v___x_930_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v___x_959_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
else
{
lean_object* v___x_963_; uint8_t v___x_964_; 
lean_del_object(v___x_930_);
v___x_963_ = lean_box(0);
v___x_964_ = lean_nat_dec_le(v___x_957_, v___x_957_);
if (v___x_964_ == 0)
{
if (v___x_958_ == 0)
{
lean_dec(v_a_956_);
lean_dec_ref(v___y_926_);
lean_dec_ref(v___y_925_);
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
goto v___jp_334_;
}
else
{
size_t v___x_965_; size_t v___x_966_; lean_object* v___x_967_; 
v___x_965_ = ((size_t)0ULL);
v___x_966_ = lean_usize_of_nat(v___x_957_);
v___x_967_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_956_, v___x_965_, v___x_966_, v___x_963_, v_a_329_);
lean_dec(v_a_956_);
if (lean_obj_tag(v___x_967_) == 0)
{
lean_dec_ref_known(v___x_967_, 1);
lean_dec_ref(v___y_926_);
lean_dec_ref(v___y_925_);
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
goto v___jp_334_;
}
else
{
v___y_911_ = v___y_923_;
v___y_912_ = v___y_924_;
v___y_913_ = v___y_925_;
v___y_914_ = v___y_926_;
v___y_915_ = v___x_967_;
goto v___jp_910_;
}
}
}
else
{
size_t v___x_968_; size_t v___x_969_; lean_object* v___x_970_; 
v___x_968_ = ((size_t)0ULL);
v___x_969_ = lean_usize_of_nat(v___x_957_);
v___x_970_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_956_, v___x_968_, v___x_969_, v___x_963_, v_a_329_);
lean_dec(v_a_956_);
if (lean_obj_tag(v___x_970_) == 0)
{
lean_dec_ref_known(v___x_970_, 1);
lean_dec_ref(v___y_926_);
lean_dec_ref(v___y_925_);
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
goto v___jp_334_;
}
else
{
v___y_911_ = v___y_923_;
v___y_912_ = v___y_924_;
v___y_913_ = v___y_925_;
v___y_914_ = v___y_926_;
v___y_915_ = v___x_970_;
goto v___jp_910_;
}
}
}
}
}
else
{
lean_del_object(v___x_930_);
lean_dec(v_val_928_);
v___y_893_ = v___y_924_;
v___y_894_ = v___y_923_;
v___y_895_ = v___y_925_;
v___y_896_ = v___y_926_;
v___y_897_ = v_a_329_;
goto v___jp_892_;
}
}
}
else
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
lean_dec(v_a_927_);
v___x_972_ = lean_unsigned_to_nat(0u);
v___x_973_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_326_);
lean_inc_ref(v___y_925_);
lean_inc_ref(v___y_924_);
v___x_974_ = l_Lake_GitRepo_addRemote(v___y_924_, v___y_925_, v_repo_326_, v___x_973_);
if (lean_obj_tag(v___x_974_) == 0)
{
lean_object* v_a_975_; lean_object* v___x_976_; uint8_t v___x_977_; 
v_a_975_ = lean_ctor_get(v___x_974_, 1);
lean_inc(v_a_975_);
lean_dec_ref_known(v___x_974_, 2);
v___x_976_ = lean_array_get_size(v_a_975_);
v___x_977_ = lean_nat_dec_lt(v___x_972_, v___x_976_);
if (v___x_977_ == 0)
{
lean_dec(v_a_975_);
v___y_893_ = v___y_924_;
v___y_894_ = v___y_923_;
v___y_895_ = v___y_925_;
v___y_896_ = v___y_926_;
v___y_897_ = v_a_329_;
goto v___jp_892_;
}
else
{
lean_object* v___x_978_; uint8_t v___x_979_; 
v___x_978_ = lean_box(0);
v___x_979_ = lean_nat_dec_le(v___x_976_, v___x_976_);
if (v___x_979_ == 0)
{
if (v___x_977_ == 0)
{
lean_dec(v_a_975_);
v___y_893_ = v___y_924_;
v___y_894_ = v___y_923_;
v___y_895_ = v___y_925_;
v___y_896_ = v___y_926_;
v___y_897_ = v_a_329_;
goto v___jp_892_;
}
else
{
size_t v___x_980_; size_t v___x_981_; lean_object* v___x_982_; 
v___x_980_ = ((size_t)0ULL);
v___x_981_ = lean_usize_of_nat(v___x_976_);
v___x_982_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_975_, v___x_980_, v___x_981_, v___x_978_, v_a_329_);
lean_dec(v_a_975_);
if (lean_obj_tag(v___x_982_) == 0)
{
lean_dec_ref_known(v___x_982_, 1);
v___y_893_ = v___y_924_;
v___y_894_ = v___y_923_;
v___y_895_ = v___y_925_;
v___y_896_ = v___y_926_;
v___y_897_ = v_a_329_;
goto v___jp_892_;
}
else
{
v___y_917_ = v___y_923_;
v___y_918_ = v___y_924_;
v___y_919_ = v___y_925_;
v___y_920_ = v___y_926_;
v___y_921_ = v___x_982_;
goto v___jp_916_;
}
}
}
else
{
size_t v___x_983_; size_t v___x_984_; lean_object* v___x_985_; 
v___x_983_ = ((size_t)0ULL);
v___x_984_ = lean_usize_of_nat(v___x_976_);
v___x_985_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_975_, v___x_983_, v___x_984_, v___x_978_, v_a_329_);
lean_dec(v_a_975_);
if (lean_obj_tag(v___x_985_) == 0)
{
lean_dec_ref_known(v___x_985_, 1);
v___y_893_ = v___y_924_;
v___y_894_ = v___y_923_;
v___y_895_ = v___y_925_;
v___y_896_ = v___y_926_;
v___y_897_ = v_a_329_;
goto v___jp_892_;
}
else
{
v___y_917_ = v___y_923_;
v___y_918_ = v___y_924_;
v___y_919_ = v___y_925_;
v___y_920_ = v___y_926_;
v___y_921_ = v___x_985_;
goto v___jp_916_;
}
}
}
}
else
{
lean_object* v_a_986_; lean_object* v___x_987_; uint8_t v___x_988_; 
v_a_986_ = lean_ctor_get(v___x_974_, 1);
lean_inc(v_a_986_);
lean_dec_ref_known(v___x_974_, 2);
v___x_987_ = lean_array_get_size(v_a_986_);
v___x_988_ = lean_nat_dec_lt(v___x_972_, v___x_987_);
if (v___x_988_ == 0)
{
lean_object* v___x_989_; lean_object* v___x_990_; 
lean_dec(v_a_986_);
lean_dec_ref(v___y_926_);
lean_dec_ref(v___y_925_);
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
v___x_989_ = lean_box(0);
v___x_990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_990_, 0, v___x_989_);
return v___x_990_;
}
else
{
lean_object* v___x_991_; uint8_t v___x_992_; 
v___x_991_ = lean_box(0);
v___x_992_ = lean_nat_dec_le(v___x_987_, v___x_987_);
if (v___x_992_ == 0)
{
if (v___x_988_ == 0)
{
lean_dec(v_a_986_);
lean_dec_ref(v___y_926_);
lean_dec_ref(v___y_925_);
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
goto v___jp_331_;
}
else
{
size_t v___x_993_; size_t v___x_994_; lean_object* v___x_995_; 
v___x_993_ = ((size_t)0ULL);
v___x_994_ = lean_usize_of_nat(v___x_987_);
v___x_995_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_986_, v___x_993_, v___x_994_, v___x_991_, v_a_329_);
lean_dec(v_a_986_);
if (lean_obj_tag(v___x_995_) == 0)
{
lean_dec_ref_known(v___x_995_, 1);
lean_dec_ref(v___y_926_);
lean_dec_ref(v___y_925_);
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
goto v___jp_331_;
}
else
{
v___y_917_ = v___y_923_;
v___y_918_ = v___y_924_;
v___y_919_ = v___y_925_;
v___y_920_ = v___y_926_;
v___y_921_ = v___x_995_;
goto v___jp_916_;
}
}
}
else
{
size_t v___x_996_; size_t v___x_997_; lean_object* v___x_998_; 
v___x_996_ = ((size_t)0ULL);
v___x_997_ = lean_usize_of_nat(v___x_987_);
v___x_998_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_986_, v___x_996_, v___x_997_, v___x_991_, v_a_329_);
lean_dec(v_a_986_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_dec_ref_known(v___x_998_, 1);
lean_dec_ref(v___y_926_);
lean_dec_ref(v___y_925_);
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
goto v___jp_331_;
}
else
{
v___y_917_ = v___y_923_;
v___y_918_ = v___y_924_;
v___y_919_ = v___y_925_;
v___y_920_ = v___y_926_;
v___y_921_ = v___x_998_;
goto v___jp_916_;
}
}
}
}
}
}
v___jp_999_:
{
if (v_a_1003_ == 0)
{
lean_object* v___x_1004_; lean_object* v___x_1005_; uint8_t v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1004_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__7));
lean_inc_ref(v_name_325_);
v___x_1005_ = lean_string_append(v_name_325_, v___x_1004_);
v___x_1006_ = 1;
v___x_1007_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1007_, 0, v___x_1005_);
lean_ctor_set_uint8(v___x_1007_, sizeof(void*)*1, v___x_1006_);
lean_inc_ref(v_a_329_);
v___x_1008_ = lean_apply_2(v_a_329_, v___x_1007_, lean_box(0));
lean_inc_ref(v_repo_326_);
v___x_1009_ = l_IO_FS_createDirAll(v_repo_326_);
if (lean_obj_tag(v___x_1009_) == 0)
{
lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1042_; 
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1042_ == 0)
{
lean_object* v_unused_1043_; 
v_unused_1043_ = lean_ctor_get(v___x_1009_, 0);
lean_dec(v_unused_1043_);
v___x_1011_ = v___x_1009_;
v_isShared_1012_ = v_isSharedCheck_1042_;
goto v_resetjp_1010_;
}
else
{
lean_dec(v___x_1009_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1042_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1013_ = lean_unsigned_to_nat(0u);
v___x_1014_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_326_);
v___x_1015_ = l_Lake_GitRepo_quietInit(v_repo_326_, v___x_1014_);
if (lean_obj_tag(v___x_1015_) == 0)
{
lean_object* v_a_1016_; lean_object* v___x_1017_; uint8_t v___x_1018_; 
lean_del_object(v___x_1011_);
v_a_1016_ = lean_ctor_get(v___x_1015_, 1);
lean_inc(v_a_1016_);
lean_dec_ref_known(v___x_1015_, 2);
v___x_1017_ = lean_array_get_size(v_a_1016_);
v___x_1018_ = lean_nat_dec_lt(v___x_1013_, v___x_1017_);
if (v___x_1018_ == 0)
{
lean_dec(v_a_1016_);
v___y_685_ = v___y_1000_;
v___y_686_ = v___y_1001_;
v___y_687_ = v___y_1002_;
goto v___jp_684_;
}
else
{
lean_object* v___x_1019_; uint8_t v___x_1020_; 
v___x_1019_ = lean_box(0);
v___x_1020_ = lean_nat_dec_le(v___x_1017_, v___x_1017_);
if (v___x_1020_ == 0)
{
if (v___x_1018_ == 0)
{
lean_dec(v_a_1016_);
v___y_685_ = v___y_1000_;
v___y_686_ = v___y_1001_;
v___y_687_ = v___y_1002_;
goto v___jp_684_;
}
else
{
size_t v___x_1021_; size_t v___x_1022_; lean_object* v___x_1023_; 
v___x_1021_ = ((size_t)0ULL);
v___x_1022_ = lean_usize_of_nat(v___x_1017_);
v___x_1023_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1016_, v___x_1021_, v___x_1022_, v___x_1019_, v_a_329_);
lean_dec(v_a_1016_);
if (lean_obj_tag(v___x_1023_) == 0)
{
lean_dec_ref_known(v___x_1023_, 1);
v___y_685_ = v___y_1000_;
v___y_686_ = v___y_1001_;
v___y_687_ = v___y_1002_;
goto v___jp_684_;
}
else
{
v___y_716_ = v___y_1000_;
v___y_717_ = v___y_1001_;
v___y_718_ = v___y_1002_;
v___y_719_ = v___x_1023_;
goto v___jp_715_;
}
}
}
else
{
size_t v___x_1024_; size_t v___x_1025_; lean_object* v___x_1026_; 
v___x_1024_ = ((size_t)0ULL);
v___x_1025_ = lean_usize_of_nat(v___x_1017_);
v___x_1026_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1016_, v___x_1024_, v___x_1025_, v___x_1019_, v_a_329_);
lean_dec(v_a_1016_);
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_dec_ref_known(v___x_1026_, 1);
v___y_685_ = v___y_1000_;
v___y_686_ = v___y_1001_;
v___y_687_ = v___y_1002_;
goto v___jp_684_;
}
else
{
v___y_716_ = v___y_1000_;
v___y_717_ = v___y_1001_;
v___y_718_ = v___y_1002_;
v___y_719_ = v___x_1026_;
goto v___jp_715_;
}
}
}
}
else
{
lean_object* v_a_1027_; lean_object* v___x_1028_; uint8_t v___x_1029_; 
v_a_1027_ = lean_ctor_get(v___x_1015_, 1);
lean_inc(v_a_1027_);
lean_dec_ref_known(v___x_1015_, 2);
v___x_1028_ = lean_array_get_size(v_a_1027_);
v___x_1029_ = lean_nat_dec_lt(v___x_1013_, v___x_1028_);
if (v___x_1029_ == 0)
{
lean_object* v___x_1030_; lean_object* v___x_1032_; 
lean_dec(v_a_1027_);
lean_dec_ref(v___y_1002_);
lean_dec_ref(v___y_1001_);
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
v___x_1030_ = lean_box(0);
if (v_isShared_1012_ == 0)
{
lean_ctor_set_tag(v___x_1011_, 1);
lean_ctor_set(v___x_1011_, 0, v___x_1030_);
v___x_1032_ = v___x_1011_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v___x_1030_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
else
{
lean_object* v___x_1034_; uint8_t v___x_1035_; 
lean_del_object(v___x_1011_);
v___x_1034_ = lean_box(0);
v___x_1035_ = lean_nat_dec_le(v___x_1028_, v___x_1028_);
if (v___x_1035_ == 0)
{
if (v___x_1029_ == 0)
{
lean_dec(v_a_1027_);
lean_dec_ref(v___y_1002_);
lean_dec_ref(v___y_1001_);
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
goto v___jp_353_;
}
else
{
size_t v___x_1036_; size_t v___x_1037_; lean_object* v___x_1038_; 
v___x_1036_ = ((size_t)0ULL);
v___x_1037_ = lean_usize_of_nat(v___x_1028_);
v___x_1038_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1027_, v___x_1036_, v___x_1037_, v___x_1034_, v_a_329_);
lean_dec(v_a_1027_);
if (lean_obj_tag(v___x_1038_) == 0)
{
lean_dec_ref_known(v___x_1038_, 1);
lean_dec_ref(v___y_1002_);
lean_dec_ref(v___y_1001_);
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
goto v___jp_353_;
}
else
{
v___y_716_ = v___y_1000_;
v___y_717_ = v___y_1001_;
v___y_718_ = v___y_1002_;
v___y_719_ = v___x_1038_;
goto v___jp_715_;
}
}
}
else
{
size_t v___x_1039_; size_t v___x_1040_; lean_object* v___x_1041_; 
v___x_1039_ = ((size_t)0ULL);
v___x_1040_ = lean_usize_of_nat(v___x_1028_);
v___x_1041_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1027_, v___x_1039_, v___x_1040_, v___x_1034_, v_a_329_);
lean_dec(v_a_1027_);
if (lean_obj_tag(v___x_1041_) == 0)
{
lean_dec_ref_known(v___x_1041_, 1);
lean_dec_ref(v___y_1002_);
lean_dec_ref(v___y_1001_);
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
goto v___jp_353_;
}
else
{
v___y_716_ = v___y_1000_;
v___y_717_ = v___y_1001_;
v___y_718_ = v___y_1002_;
v___y_719_ = v___x_1041_;
goto v___jp_715_;
}
}
}
}
}
}
else
{
lean_object* v_a_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1056_; 
lean_dec_ref(v___y_1002_);
lean_dec_ref(v___y_1001_);
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
v_a_1044_ = lean_ctor_get(v___x_1009_, 0);
v_isSharedCheck_1056_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1046_ = v___x_1009_;
v_isShared_1047_ = v_isSharedCheck_1056_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_a_1044_);
lean_dec(v___x_1009_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1056_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1048_; uint8_t v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1054_; 
v___x_1048_ = lean_io_error_to_string(v_a_1044_);
v___x_1049_ = 3;
v___x_1050_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1050_, 0, v___x_1048_);
lean_ctor_set_uint8(v___x_1050_, sizeof(void*)*1, v___x_1049_);
lean_inc_ref(v_a_329_);
v___x_1051_ = lean_apply_2(v_a_329_, v___x_1050_, lean_box(0));
v___x_1052_ = lean_box(0);
if (v_isShared_1047_ == 0)
{
lean_ctor_set(v___x_1046_, 0, v___x_1052_);
v___x_1054_ = v___x_1046_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v___x_1052_);
v___x_1054_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
return v___x_1054_;
}
}
}
}
else
{
lean_object* v___x_1057_; lean_object* v___x_1058_; uint8_t v___x_1059_; 
lean_inc_ref(v_repo_326_);
lean_inc_ref(v___y_1000_);
v___x_1057_ = l_Lake_GitRepo_getRemoteUrl_x3f(v___y_1000_, v_repo_326_);
v___x_1058_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_1059_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_1059_ == 0)
{
v___y_923_ = v_a_1003_;
v___y_924_ = v___y_1000_;
v___y_925_ = v___y_1001_;
v___y_926_ = v___y_1002_;
v_a_927_ = v___x_1057_;
goto v___jp_922_;
}
else
{
lean_object* v___x_1060_; uint8_t v___x_1061_; 
v___x_1060_ = lean_box(0);
v___x_1061_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
if (v___x_1061_ == 0)
{
if (v___x_1059_ == 0)
{
v___y_923_ = v_a_1003_;
v___y_924_ = v___y_1000_;
v___y_925_ = v___y_1001_;
v___y_926_ = v___y_1002_;
v_a_927_ = v___x_1057_;
goto v___jp_922_;
}
else
{
size_t v___x_1062_; size_t v___x_1063_; lean_object* v___x_1064_; 
v___x_1062_ = ((size_t)0ULL);
v___x_1063_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8);
v___x_1064_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_1058_, v___x_1062_, v___x_1063_, v___x_1060_, v_a_329_);
if (lean_obj_tag(v___x_1064_) == 0)
{
lean_dec_ref_known(v___x_1064_, 1);
v___y_923_ = v_a_1003_;
v___y_924_ = v___y_1000_;
v___y_925_ = v___y_1001_;
v___y_926_ = v___y_1002_;
v_a_927_ = v___x_1057_;
goto v___jp_922_;
}
else
{
lean_dec(v___x_1057_);
lean_dec_ref(v___y_1002_);
lean_dec_ref(v___y_1001_);
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
return v___x_1064_;
}
}
}
else
{
size_t v___x_1065_; size_t v___x_1066_; lean_object* v___x_1067_; 
v___x_1065_ = ((size_t)0ULL);
v___x_1066_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8);
v___x_1067_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_1058_, v___x_1065_, v___x_1066_, v___x_1060_, v_a_329_);
if (lean_obj_tag(v___x_1067_) == 0)
{
lean_dec_ref_known(v___x_1067_, 1);
v___y_923_ = v_a_1003_;
v___y_924_ = v___y_1000_;
v___y_925_ = v___y_1001_;
v___y_926_ = v___y_1002_;
v_a_927_ = v___x_1057_;
goto v___jp_922_;
}
else
{
lean_dec(v___x_1057_);
lean_dec_ref(v___y_1002_);
lean_dec_ref(v___y_1001_);
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
return v___x_1067_;
}
}
}
}
}
v___jp_1068_:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; uint8_t v___x_1074_; lean_object* v___x_1075_; uint8_t v___x_1076_; 
v___x_1072_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__8));
lean_inc_ref(v_repo_326_);
v___x_1073_ = l_System_FilePath_join(v_repo_326_, v___x_1072_);
v___x_1074_ = l_System_FilePath_pathExists(v___x_1073_);
lean_dec_ref(v___x_1073_);
v___x_1075_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_1076_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_1076_ == 0)
{
v___y_1000_ = v___y_1069_;
v___y_1001_ = v_a_1071_;
v___y_1002_ = v___y_1070_;
v_a_1003_ = v___x_1074_;
goto v___jp_999_;
}
else
{
lean_object* v___x_1077_; uint8_t v___x_1078_; 
v___x_1077_ = lean_box(0);
v___x_1078_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
if (v___x_1078_ == 0)
{
if (v___x_1076_ == 0)
{
v___y_1000_ = v___y_1069_;
v___y_1001_ = v_a_1071_;
v___y_1002_ = v___y_1070_;
v_a_1003_ = v___x_1074_;
goto v___jp_999_;
}
else
{
size_t v___x_1079_; size_t v___x_1080_; lean_object* v___x_1081_; 
v___x_1079_ = ((size_t)0ULL);
v___x_1080_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8);
v___x_1081_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_1075_, v___x_1079_, v___x_1080_, v___x_1077_, v_a_329_);
if (lean_obj_tag(v___x_1081_) == 0)
{
lean_dec_ref_known(v___x_1081_, 1);
v___y_1000_ = v___y_1069_;
v___y_1001_ = v_a_1071_;
v___y_1002_ = v___y_1070_;
v_a_1003_ = v___x_1074_;
goto v___jp_999_;
}
else
{
lean_dec_ref(v_a_1071_);
lean_dec_ref(v___y_1070_);
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
return v___x_1081_;
}
}
}
else
{
size_t v___x_1082_; size_t v___x_1083_; lean_object* v___x_1084_; 
v___x_1082_ = ((size_t)0ULL);
v___x_1083_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8);
v___x_1084_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_1075_, v___x_1082_, v___x_1083_, v___x_1077_, v_a_329_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_dec_ref_known(v___x_1084_, 1);
v___y_1000_ = v___y_1069_;
v___y_1001_ = v_a_1071_;
v___y_1002_ = v___y_1070_;
v_a_1003_ = v___x_1074_;
goto v___jp_999_;
}
else
{
lean_dec_ref(v_a_1071_);
lean_dec_ref(v___y_1070_);
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
return v___x_1084_;
}
}
}
}
v___jp_1085_:
{
if (lean_obj_tag(v_a_1088_) == 1)
{
lean_object* v_val_1089_; 
lean_dec_ref(v_url_327_);
v_val_1089_ = lean_ctor_get(v_a_1088_, 0);
lean_inc(v_val_1089_);
lean_dec_ref_known(v_a_1088_, 1);
v___y_1069_ = v___y_1086_;
v___y_1070_ = v___y_1087_;
v_a_1071_ = v_val_1089_;
goto v___jp_1068_;
}
else
{
lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; uint8_t v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
lean_dec(v_a_1088_);
lean_dec_ref(v___y_1087_);
lean_dec_ref(v_repo_326_);
v___x_1090_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__0));
v___x_1091_ = lean_string_append(v_name_325_, v___x_1090_);
v___x_1092_ = lean_string_append(v___x_1091_, v_url_327_);
lean_dec_ref(v_url_327_);
v___x_1093_ = 3;
v___x_1094_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1094_, 0, v___x_1092_);
lean_ctor_set_uint8(v___x_1094_, sizeof(void*)*1, v___x_1093_);
lean_inc_ref(v_a_329_);
v___x_1095_ = lean_apply_2(v_a_329_, v___x_1094_, lean_box(0));
v___x_1096_ = lean_box(0);
v___x_1097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1096_);
return v___x_1097_;
}
}
v___jp_1098_:
{
lean_object* v___x_1104_; uint8_t v___x_1105_; 
v___x_1104_ = lean_array_get_size(v___y_1102_);
v___x_1105_ = lean_nat_dec_lt(v___y_1099_, v___x_1104_);
if (v___x_1105_ == 0)
{
v___y_1086_ = v___y_1100_;
v___y_1087_ = v___y_1101_;
v_a_1088_ = v_val_1103_;
goto v___jp_1085_;
}
else
{
lean_object* v___x_1106_; uint8_t v___x_1107_; 
v___x_1106_ = lean_box(0);
v___x_1107_ = lean_nat_dec_le(v___x_1104_, v___x_1104_);
if (v___x_1107_ == 0)
{
if (v___x_1105_ == 0)
{
v___y_1086_ = v___y_1100_;
v___y_1087_ = v___y_1101_;
v_a_1088_ = v_val_1103_;
goto v___jp_1085_;
}
else
{
size_t v___x_1108_; size_t v___x_1109_; lean_object* v___x_1110_; 
v___x_1108_ = ((size_t)0ULL);
v___x_1109_ = lean_usize_of_nat(v___x_1104_);
v___x_1110_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_1102_, v___x_1108_, v___x_1109_, v___x_1106_, v_a_329_);
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_dec_ref_known(v___x_1110_, 1);
v___y_1086_ = v___y_1100_;
v___y_1087_ = v___y_1101_;
v_a_1088_ = v_val_1103_;
goto v___jp_1085_;
}
else
{
lean_dec(v_val_1103_);
lean_dec_ref(v___y_1101_);
lean_dec_ref(v_url_327_);
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
return v___x_1110_;
}
}
}
else
{
size_t v___x_1111_; size_t v___x_1112_; lean_object* v___x_1113_; 
v___x_1111_ = ((size_t)0ULL);
v___x_1112_ = lean_usize_of_nat(v___x_1104_);
v___x_1113_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_1102_, v___x_1111_, v___x_1112_, v___x_1106_, v_a_329_);
if (lean_obj_tag(v___x_1113_) == 0)
{
lean_dec_ref_known(v___x_1113_, 1);
v___y_1086_ = v___y_1100_;
v___y_1087_ = v___y_1101_;
v_a_1088_ = v_val_1103_;
goto v___jp_1085_;
}
else
{
lean_dec(v_val_1103_);
lean_dec_ref(v___y_1101_);
lean_dec_ref(v_url_327_);
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
return v___x_1113_;
}
}
}
}
v___jp_1114_:
{
if (v_a_1117_ == 0)
{
v___y_1069_ = v___y_1115_;
v___y_1070_ = v___y_1116_;
v_a_1071_ = v_url_327_;
goto v___jp_1068_;
}
else
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; uint8_t v___x_1122_; 
lean_inc_ref(v_url_327_);
v___x_1118_ = l_Lake_resolvePath(v_url_327_);
v___x_1119_ = lean_unsigned_to_nat(0u);
v___x_1120_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_1121_ = lean_string_utf8_byte_size(v___x_1118_);
v___x_1122_ = lean_nat_dec_eq(v___x_1121_, v___x_1119_);
if (v___x_1122_ == 0)
{
lean_object* v___x_1123_; 
v___x_1123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1123_, 0, v___x_1118_);
v___y_1099_ = v___x_1119_;
v___y_1100_ = v___y_1115_;
v___y_1101_ = v___y_1116_;
v___y_1102_ = v___x_1120_;
v_val_1103_ = v___x_1123_;
goto v___jp_1098_;
}
else
{
lean_object* v___x_1124_; 
lean_dec_ref(v___x_1118_);
v___x_1124_ = lean_box(0);
v___y_1099_ = v___x_1119_;
v___y_1100_ = v___y_1115_;
v___y_1101_ = v___y_1116_;
v___y_1102_ = v___x_1120_;
v_val_1103_ = v___x_1124_;
goto v___jp_1098_;
}
}
}
v___jp_1125_:
{
uint8_t v___x_1127_; lean_object* v_remote_1128_; lean_object* v___x_1129_; uint8_t v___x_1130_; 
v___x_1127_ = l_System_FilePath_pathExists(v_url_327_);
v_remote_1128_ = l_Lake_Git_defaultRemote;
v___x_1129_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_1130_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_1130_ == 0)
{
v___y_1115_ = v_remote_1128_;
v___y_1116_ = v___y_1126_;
v_a_1117_ = v___x_1127_;
goto v___jp_1114_;
}
else
{
lean_object* v___x_1131_; uint8_t v___x_1132_; 
v___x_1131_ = lean_box(0);
v___x_1132_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
if (v___x_1132_ == 0)
{
if (v___x_1130_ == 0)
{
v___y_1115_ = v_remote_1128_;
v___y_1116_ = v___y_1126_;
v_a_1117_ = v___x_1127_;
goto v___jp_1114_;
}
else
{
size_t v___x_1133_; size_t v___x_1134_; lean_object* v___x_1135_; 
v___x_1133_ = ((size_t)0ULL);
v___x_1134_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8);
v___x_1135_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_1129_, v___x_1133_, v___x_1134_, v___x_1131_, v_a_329_);
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_dec_ref_known(v___x_1135_, 1);
v___y_1115_ = v_remote_1128_;
v___y_1116_ = v___y_1126_;
v_a_1117_ = v___x_1127_;
goto v___jp_1114_;
}
else
{
lean_dec_ref(v___y_1126_);
lean_dec_ref(v_url_327_);
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
return v___x_1135_;
}
}
}
else
{
size_t v___x_1136_; size_t v___x_1137_; lean_object* v___x_1138_; 
v___x_1136_ = ((size_t)0ULL);
v___x_1137_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8);
v___x_1138_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_1129_, v___x_1136_, v___x_1137_, v___x_1131_, v_a_329_);
if (lean_obj_tag(v___x_1138_) == 0)
{
lean_dec_ref_known(v___x_1138_, 1);
v___y_1115_ = v_remote_1128_;
v___y_1116_ = v___y_1126_;
v_a_1117_ = v___x_1127_;
goto v___jp_1114_;
}
else
{
lean_dec_ref(v___y_1126_);
lean_dec_ref(v_url_327_);
lean_dec_ref(v_repo_326_);
lean_dec_ref(v_name_325_);
return v___x_1138_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___boxed(lean_object* v_name_1141_, lean_object* v_repo_1142_, lean_object* v_url_1143_, lean_object* v_rev_x3f_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_){
_start:
{
lean_object* v_res_1147_; 
v_res_1147_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo(v_name_1141_, v_repo_1142_, v_url_1143_, v_rev_x3f_1144_, v_a_1145_);
lean_dec_ref(v_a_1145_);
return v_res_1147_;
}
}
static lean_object* _init_l_Lake_instInhabitedMaterializedDep_default___closed__4(void){
_start:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1154_ = l_Lake_instInhabitedPackageEntry_default;
v___x_1155_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__3));
v___x_1156_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___x_1157_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1156_);
lean_ctor_set(v___x_1157_, 1, v___x_1156_);
lean_ctor_set(v___x_1157_, 2, v___x_1156_);
lean_ctor_set(v___x_1157_, 3, v___x_1155_);
lean_ctor_set(v___x_1157_, 4, v___x_1154_);
return v___x_1157_;
}
}
static lean_object* _init_l_Lake_instInhabitedMaterializedDep_default(void){
_start:
{
lean_object* v___x_1158_; 
v___x_1158_ = lean_obj_once(&l_Lake_instInhabitedMaterializedDep_default___closed__4, &l_Lake_instInhabitedMaterializedDep_default___closed__4_once, _init_l_Lake_instInhabitedMaterializedDep_default___closed__4);
return v___x_1158_;
}
}
static lean_object* _init_l_Lake_instInhabitedMaterializedDep(void){
_start:
{
lean_object* v___x_1159_; 
v___x_1159_ = l_Lake_instInhabitedMaterializedDep_default;
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_name(lean_object* v_self_1160_){
_start:
{
lean_object* v_manifestEntry_1161_; lean_object* v_name_1162_; 
v_manifestEntry_1161_ = lean_ctor_get(v_self_1160_, 4);
v_name_1162_ = lean_ctor_get(v_manifestEntry_1161_, 0);
lean_inc(v_name_1162_);
return v_name_1162_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_name___boxed(lean_object* v_self_1163_){
_start:
{
lean_object* v_res_1164_; 
v_res_1164_ = l_Lake_MaterializedDep_name(v_self_1163_);
lean_dec_ref(v_self_1163_);
return v_res_1164_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_prettyName(lean_object* v_self_1165_){
_start:
{
lean_object* v_manifestEntry_1166_; lean_object* v_name_1167_; uint8_t v___x_1168_; lean_object* v___x_1169_; 
v_manifestEntry_1166_ = lean_ctor_get(v_self_1165_, 4);
lean_inc_ref(v_manifestEntry_1166_);
lean_dec_ref(v_self_1165_);
v_name_1167_ = lean_ctor_get(v_manifestEntry_1166_, 0);
lean_inc(v_name_1167_);
lean_dec_ref(v_manifestEntry_1166_);
v___x_1168_ = 0;
v___x_1169_ = l_Lean_Name_toString(v_name_1167_, v___x_1168_);
return v___x_1169_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_scope(lean_object* v_self_1170_){
_start:
{
lean_object* v_manifestEntry_1171_; lean_object* v_scope_1172_; 
v_manifestEntry_1171_ = lean_ctor_get(v_self_1170_, 4);
v_scope_1172_ = lean_ctor_get(v_manifestEntry_1171_, 1);
lean_inc_ref(v_scope_1172_);
return v_scope_1172_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_scope___boxed(lean_object* v_self_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l_Lake_MaterializedDep_scope(v_self_1173_);
lean_dec_ref(v_self_1173_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relManifestFile_x3f(lean_object* v_self_1175_){
_start:
{
lean_object* v_manifestEntry_1176_; lean_object* v_manifestFile_x3f_1177_; 
v_manifestEntry_1176_ = lean_ctor_get(v_self_1175_, 4);
v_manifestFile_x3f_1177_ = lean_ctor_get(v_manifestEntry_1176_, 3);
lean_inc(v_manifestFile_x3f_1177_);
return v_manifestFile_x3f_1177_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relManifestFile_x3f___boxed(lean_object* v_self_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l_Lake_MaterializedDep_relManifestFile_x3f(v_self_1178_);
lean_dec_ref(v_self_1178_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relManifestFile(lean_object* v_self_1180_){
_start:
{
lean_object* v_manifestEntry_1181_; lean_object* v_manifestFile_x3f_1182_; 
v_manifestEntry_1181_ = lean_ctor_get(v_self_1180_, 4);
v_manifestFile_x3f_1182_ = lean_ctor_get(v_manifestEntry_1181_, 3);
if (lean_obj_tag(v_manifestFile_x3f_1182_) == 0)
{
lean_object* v___x_1183_; 
v___x_1183_ = l_Lake_defaultManifestFile;
return v___x_1183_;
}
else
{
lean_object* v_val_1184_; 
v_val_1184_ = lean_ctor_get(v_manifestFile_x3f_1182_, 0);
lean_inc(v_val_1184_);
return v_val_1184_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relManifestFile___boxed(lean_object* v_self_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l_Lake_MaterializedDep_relManifestFile(v_self_1185_);
lean_dec_ref(v_self_1185_);
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_manifestFile(lean_object* v_self_1187_){
_start:
{
lean_object* v_manifestEntry_1188_; lean_object* v_manifestFile_x3f_1189_; 
v_manifestEntry_1188_ = lean_ctor_get(v_self_1187_, 4);
v_manifestFile_x3f_1189_ = lean_ctor_get(v_manifestEntry_1188_, 3);
if (lean_obj_tag(v_manifestFile_x3f_1189_) == 0)
{
lean_object* v_pkgDir_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; 
v_pkgDir_1190_ = lean_ctor_get(v_self_1187_, 0);
lean_inc_ref(v_pkgDir_1190_);
lean_dec_ref(v_self_1187_);
v___x_1191_ = l_Lake_defaultManifestFile;
v___x_1192_ = l_Lake_joinRelative(v_pkgDir_1190_, v___x_1191_);
return v___x_1192_;
}
else
{
lean_object* v_pkgDir_1193_; lean_object* v_val_1194_; lean_object* v___x_1195_; 
lean_inc_ref(v_manifestFile_x3f_1189_);
v_pkgDir_1193_ = lean_ctor_get(v_self_1187_, 0);
lean_inc_ref(v_pkgDir_1193_);
lean_dec_ref(v_self_1187_);
v_val_1194_ = lean_ctor_get(v_manifestFile_x3f_1189_, 0);
lean_inc(v_val_1194_);
lean_dec_ref_known(v_manifestFile_x3f_1189_, 1);
v___x_1195_ = l_Lake_joinRelative(v_pkgDir_1193_, v_val_1194_);
return v___x_1195_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relConfigFile(lean_object* v_self_1196_){
_start:
{
lean_object* v_manifestEntry_1197_; lean_object* v_configFile_1198_; 
v_manifestEntry_1197_ = lean_ctor_get(v_self_1196_, 4);
v_configFile_1198_ = lean_ctor_get(v_manifestEntry_1197_, 2);
lean_inc_ref(v_configFile_1198_);
return v_configFile_1198_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relConfigFile___boxed(lean_object* v_self_1199_){
_start:
{
lean_object* v_res_1200_; 
v_res_1200_ = l_Lake_MaterializedDep_relConfigFile(v_self_1199_);
lean_dec_ref(v_self_1199_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_configFile(lean_object* v_self_1201_){
_start:
{
lean_object* v_manifestEntry_1202_; lean_object* v_pkgDir_1203_; lean_object* v_configFile_1204_; lean_object* v___x_1205_; 
v_manifestEntry_1202_ = lean_ctor_get(v_self_1201_, 4);
lean_inc_ref(v_manifestEntry_1202_);
v_pkgDir_1203_ = lean_ctor_get(v_self_1201_, 0);
lean_inc_ref(v_pkgDir_1203_);
lean_dec_ref(v_self_1201_);
v_configFile_1204_ = lean_ctor_get(v_manifestEntry_1202_, 2);
lean_inc_ref(v_configFile_1204_);
lean_dec_ref(v_manifestEntry_1202_);
v___x_1205_ = l_Lake_joinRelative(v_pkgDir_1203_, v_configFile_1204_);
return v___x_1205_;
}
}
LEAN_EXPORT uint8_t l_Lake_MaterializedDep_fixedToolchain(lean_object* v_self_1206_){
_start:
{
lean_object* v_manifest_x3f_1207_; 
v_manifest_x3f_1207_ = lean_ctor_get(v_self_1206_, 3);
if (lean_obj_tag(v_manifest_x3f_1207_) == 1)
{
lean_object* v_a_1208_; uint8_t v_fixedToolchain_1209_; 
v_a_1208_ = lean_ctor_get(v_manifest_x3f_1207_, 0);
v_fixedToolchain_1209_ = lean_ctor_get_uint8(v_a_1208_, sizeof(void*)*4);
return v_fixedToolchain_1209_;
}
else
{
uint8_t v___x_1210_; 
v___x_1210_ = 0;
return v___x_1210_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_fixedToolchain___boxed(lean_object* v_self_1211_){
_start:
{
uint8_t v_res_1212_; lean_object* v_r_1213_; 
v_res_1212_ = l_Lake_MaterializedDep_fixedToolchain(v_self_1211_);
lean_dec_ref(v_self_1211_);
v_r_1213_ = lean_box(v_res_1212_);
return v_r_1213_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed(lean_object* v_dep_1222_){
_start:
{
lean_object* v_name_1223_; lean_object* v_scope_1224_; lean_object* v_version_1225_; lean_object* v_fst_1227_; lean_object* v_snd_1228_; 
v_name_1223_ = lean_ctor_get(v_dep_1222_, 0);
lean_inc(v_name_1223_);
v_scope_1224_ = lean_ctor_get(v_dep_1222_, 1);
lean_inc_ref(v_scope_1224_);
v_version_1225_ = lean_ctor_get(v_dep_1222_, 2);
lean_inc(v_version_1225_);
lean_dec_ref(v_dep_1222_);
switch(lean_obj_tag(v_version_1225_))
{
case 0:
{
lean_object* v___x_1251_; 
v___x_1251_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v_fst_1227_ = v___x_1251_;
v_snd_1228_ = v___x_1251_;
goto v___jp_1226_;
}
case 1:
{
lean_object* v_rev_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1267_; 
v_rev_1252_ = lean_ctor_get(v_version_1225_, 0);
v_isSharedCheck_1267_ = !lean_is_exclusive(v_version_1225_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1254_ = v_version_1225_;
v_isShared_1255_ = v_isSharedCheck_1267_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_rev_1252_);
lean_dec(v_version_1225_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1267_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1259_; 
v___x_1256_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__5));
v___x_1257_ = l_String_quote(v_rev_1252_);
if (v_isShared_1255_ == 0)
{
lean_ctor_set_tag(v___x_1254_, 3);
lean_ctor_set(v___x_1254_, 0, v___x_1257_);
v___x_1259_ = v___x_1254_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v___x_1257_);
v___x_1259_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1260_ = l_Std_Format_defWidth;
v___x_1261_ = lean_unsigned_to_nat(0u);
v___x_1262_ = l_Std_Format_pretty(v___x_1259_, v___x_1260_, v___x_1261_, v___x_1261_);
v___x_1263_ = lean_string_append(v___x_1256_, v___x_1262_);
v___x_1264_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__6));
v___x_1265_ = lean_string_append(v___x_1264_, v___x_1262_);
lean_dec_ref(v___x_1262_);
v_fst_1227_ = v___x_1263_;
v_snd_1228_ = v___x_1265_;
goto v___jp_1226_;
}
}
}
default: 
{
lean_object* v_ver_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1284_; 
v_ver_1268_ = lean_ctor_get(v_version_1225_, 0);
v_isSharedCheck_1284_ = !lean_is_exclusive(v_version_1225_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1270_ = v_version_1225_;
v_isShared_1271_ = v_isSharedCheck_1284_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_ver_1268_);
lean_dec(v_version_1225_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1284_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v_toString_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1276_; 
v_toString_1272_ = lean_ctor_get(v_ver_1268_, 0);
lean_inc_ref(v_toString_1272_);
lean_dec_ref(v_ver_1268_);
v___x_1273_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__5));
v___x_1274_ = l_String_quote(v_toString_1272_);
if (v_isShared_1271_ == 0)
{
lean_ctor_set_tag(v___x_1270_, 3);
lean_ctor_set(v___x_1270_, 0, v___x_1274_);
v___x_1276_ = v___x_1270_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v___x_1274_);
v___x_1276_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1277_ = l_Std_Format_defWidth;
v___x_1278_ = lean_unsigned_to_nat(0u);
v___x_1279_ = l_Std_Format_pretty(v___x_1276_, v___x_1277_, v___x_1278_, v___x_1278_);
v___x_1280_ = lean_string_append(v___x_1273_, v___x_1279_);
v___x_1281_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__7));
v___x_1282_ = lean_string_append(v___x_1281_, v___x_1279_);
lean_dec_ref(v___x_1279_);
v_fst_1227_ = v___x_1280_;
v_snd_1228_ = v___x_1282_;
goto v___jp_1226_;
}
}
}
}
v___jp_1226_:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; uint8_t v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1229_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
lean_inc_ref(v_scope_1224_);
v___x_1230_ = lean_string_append(v_scope_1224_, v___x_1229_);
v___x_1231_ = 0;
v___x_1232_ = l_Lean_Name_toString(v_name_1223_, v___x_1231_);
v___x_1233_ = lean_string_append(v___x_1230_, v___x_1232_);
v___x_1234_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__1));
v___x_1235_ = lean_string_append(v___x_1233_, v___x_1234_);
v___x_1236_ = lean_string_append(v___x_1235_, v_scope_1224_);
v___x_1237_ = lean_string_append(v___x_1236_, v___x_1229_);
v___x_1238_ = lean_string_append(v___x_1237_, v___x_1232_);
v___x_1239_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__2));
v___x_1240_ = lean_string_append(v___x_1238_, v___x_1239_);
v___x_1241_ = lean_string_append(v___x_1240_, v_fst_1227_);
lean_dec_ref(v_fst_1227_);
v___x_1242_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__3));
v___x_1243_ = lean_string_append(v___x_1241_, v___x_1242_);
v___x_1244_ = lean_string_append(v___x_1243_, v_scope_1224_);
lean_dec_ref(v_scope_1224_);
v___x_1245_ = lean_string_append(v___x_1244_, v___x_1229_);
v___x_1246_ = lean_string_append(v___x_1245_, v___x_1232_);
lean_dec_ref(v___x_1232_);
v___x_1247_ = lean_string_append(v___x_1246_, v___x_1239_);
v___x_1248_ = lean_string_append(v___x_1247_, v_snd_1228_);
lean_dec_ref(v_snd_1228_);
v___x_1249_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__4));
v___x_1250_ = lean_string_append(v___x_1248_, v___x_1249_);
return v___x_1250_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep(lean_object* v_dep_1286_, uint8_t v_inherited_1287_, lean_object* v_wsDir_1288_, lean_object* v_name_1289_, lean_object* v_relPkgDir_1290_, lean_object* v_remoteUrl_1291_, lean_object* v_src_1292_, lean_object* v_a_1293_){
_start:
{
lean_object* v___y_1296_; lean_object* v_a_1297_; lean_object* v_pkgDir_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___f_1317_; lean_object* v___y_1319_; lean_object* v___y_1320_; lean_object* v___y_1321_; lean_object* v___y_1322_; lean_object* v_val_1323_; lean_object* v_a_1353_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v_val_1387_; lean_object* v___x_1415_; uint8_t v___x_1416_; 
lean_inc_ref(v_relPkgDir_1290_);
v_pkgDir_1314_ = l_Lake_joinRelative(v_wsDir_1288_, v_relPkgDir_1290_);
v___x_1315_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__2, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__2_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__2);
lean_inc_ref(v_pkgDir_1314_);
v___x_1316_ = l_Lake_resolvePath(v_pkgDir_1314_);
v___f_1317_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3));
v___x_1384_ = lean_unsigned_to_nat(0u);
v___x_1385_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_1415_ = lean_string_utf8_byte_size(v___x_1316_);
v___x_1416_ = lean_nat_dec_eq(v___x_1415_, v___x_1384_);
if (v___x_1416_ == 0)
{
lean_object* v___x_1417_; 
v___x_1417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1417_, 0, v___x_1316_);
v_val_1387_ = v___x_1417_;
goto v___jp_1386_;
}
else
{
lean_object* v___x_1418_; 
lean_dec_ref(v___x_1316_);
v___x_1418_ = lean_box(0);
v_val_1387_ = v___x_1418_;
goto v___jp_1386_;
}
v___jp_1295_:
{
lean_object* v_name_1298_; lean_object* v_scope_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1310_; 
v_name_1298_ = lean_ctor_get(v_dep_1286_, 0);
v_scope_1299_ = lean_ctor_get(v_dep_1286_, 1);
v_isSharedCheck_1310_ = !lean_is_exclusive(v_dep_1286_);
if (v_isSharedCheck_1310_ == 0)
{
lean_object* v_unused_1311_; lean_object* v_unused_1312_; lean_object* v_unused_1313_; 
v_unused_1311_ = lean_ctor_get(v_dep_1286_, 4);
lean_dec(v_unused_1311_);
v_unused_1312_ = lean_ctor_get(v_dep_1286_, 3);
lean_dec(v_unused_1312_);
v_unused_1313_ = lean_ctor_get(v_dep_1286_, 2);
lean_dec(v_unused_1313_);
v___x_1301_ = v_dep_1286_;
v_isShared_1302_ = v_isSharedCheck_1310_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_scope_1299_);
lean_inc(v_name_1298_);
lean_dec(v_dep_1286_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1310_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1307_; 
v___x_1303_ = l_Lake_defaultConfigFile;
v___x_1304_ = lean_box(0);
v___x_1305_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1305_, 0, v_name_1298_);
lean_ctor_set(v___x_1305_, 1, v_scope_1299_);
lean_ctor_set(v___x_1305_, 2, v___x_1303_);
lean_ctor_set(v___x_1305_, 3, v___x_1304_);
lean_ctor_set(v___x_1305_, 4, v_src_1292_);
lean_ctor_set_uint8(v___x_1305_, sizeof(void*)*5, v_inherited_1287_);
if (v_isShared_1302_ == 0)
{
lean_ctor_set(v___x_1301_, 4, v___x_1305_);
lean_ctor_set(v___x_1301_, 3, v_a_1297_);
lean_ctor_set(v___x_1301_, 2, v_remoteUrl_1291_);
lean_ctor_set(v___x_1301_, 1, v_relPkgDir_1290_);
lean_ctor_set(v___x_1301_, 0, v___y_1296_);
v___x_1307_ = v___x_1301_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v___y_1296_);
lean_ctor_set(v_reuseFailAlloc_1309_, 1, v_relPkgDir_1290_);
lean_ctor_set(v_reuseFailAlloc_1309_, 2, v_remoteUrl_1291_);
lean_ctor_set(v_reuseFailAlloc_1309_, 3, v_a_1297_);
lean_ctor_set(v_reuseFailAlloc_1309_, 4, v___x_1305_);
v___x_1307_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
lean_object* v___x_1308_; 
v___x_1308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1307_);
return v___x_1308_;
}
}
}
v___jp_1318_:
{
lean_object* v___x_1324_; uint8_t v___x_1325_; 
v___x_1324_ = lean_array_get_size(v___y_1320_);
v___x_1325_ = lean_nat_dec_lt(v___y_1322_, v___x_1324_);
if (v___x_1325_ == 0)
{
lean_dec_ref(v___y_1321_);
v___y_1296_ = v___y_1319_;
v_a_1297_ = v_val_1323_;
goto v___jp_1295_;
}
else
{
lean_object* v___x_1326_; uint8_t v___x_1327_; 
v___x_1326_ = lean_box(0);
v___x_1327_ = lean_nat_dec_le(v___x_1324_, v___x_1324_);
if (v___x_1327_ == 0)
{
if (v___x_1325_ == 0)
{
lean_dec_ref(v___y_1321_);
v___y_1296_ = v___y_1319_;
v_a_1297_ = v_val_1323_;
goto v___jp_1295_;
}
else
{
size_t v___x_1328_; size_t v___x_1329_; lean_object* v___x_2388__overap_1330_; lean_object* v___x_1331_; 
v___x_1328_ = ((size_t)0ULL);
v___x_1329_ = lean_usize_of_nat(v___x_1324_);
lean_inc_ref(v___y_1320_);
v___x_2388__overap_1330_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___y_1321_, v___f_1317_, v___y_1320_, v___x_1328_, v___x_1329_, v___x_1326_);
lean_inc_ref(v_a_1293_);
v___x_1331_ = lean_apply_2(v___x_2388__overap_1330_, v_a_1293_, lean_box(0));
if (lean_obj_tag(v___x_1331_) == 0)
{
lean_dec_ref_known(v___x_1331_, 1);
v___y_1296_ = v___y_1319_;
v_a_1297_ = v_val_1323_;
goto v___jp_1295_;
}
else
{
lean_object* v_a_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1339_; 
lean_dec_ref(v_val_1323_);
lean_dec_ref(v___y_1319_);
lean_dec_ref(v_src_1292_);
lean_dec_ref(v_remoteUrl_1291_);
lean_dec_ref(v_relPkgDir_1290_);
lean_dec_ref(v_dep_1286_);
v_a_1332_ = lean_ctor_get(v___x_1331_, 0);
v_isSharedCheck_1339_ = !lean_is_exclusive(v___x_1331_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1334_ = v___x_1331_;
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_a_1332_);
lean_dec(v___x_1331_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1337_; 
if (v_isShared_1335_ == 0)
{
v___x_1337_ = v___x_1334_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v_a_1332_);
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
}
else
{
size_t v___x_1340_; size_t v___x_1341_; lean_object* v___x_2398__overap_1342_; lean_object* v___x_1343_; 
v___x_1340_ = ((size_t)0ULL);
v___x_1341_ = lean_usize_of_nat(v___x_1324_);
lean_inc_ref(v___y_1320_);
v___x_2398__overap_1342_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___y_1321_, v___f_1317_, v___y_1320_, v___x_1340_, v___x_1341_, v___x_1326_);
lean_inc_ref(v_a_1293_);
v___x_1343_ = lean_apply_2(v___x_2398__overap_1342_, v_a_1293_, lean_box(0));
if (lean_obj_tag(v___x_1343_) == 0)
{
lean_dec_ref_known(v___x_1343_, 1);
v___y_1296_ = v___y_1319_;
v_a_1297_ = v_val_1323_;
goto v___jp_1295_;
}
else
{
lean_object* v_a_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1351_; 
lean_dec_ref(v_val_1323_);
lean_dec_ref(v___y_1319_);
lean_dec_ref(v_src_1292_);
lean_dec_ref(v_remoteUrl_1291_);
lean_dec_ref(v_relPkgDir_1290_);
lean_dec_ref(v_dep_1286_);
v_a_1344_ = lean_ctor_get(v___x_1343_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v___x_1343_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1346_ = v___x_1343_;
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_a_1344_);
lean_dec(v___x_1343_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1349_; 
if (v_isShared_1347_ == 0)
{
v___x_1349_ = v___x_1346_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_a_1344_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
return v___x_1349_;
}
}
}
}
}
}
v___jp_1352_:
{
if (lean_obj_tag(v_a_1353_) == 1)
{
lean_object* v_val_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; 
lean_dec_ref(v_pkgDir_1314_);
lean_dec_ref(v_name_1289_);
v_val_1354_ = lean_ctor_get(v_a_1353_, 0);
lean_inc_n(v_val_1354_, 2);
lean_dec_ref_known(v_a_1353_, 1);
v___x_1355_ = l_Lake_defaultManifestFile;
v___x_1356_ = l_Lake_joinRelative(v_val_1354_, v___x_1355_);
v___x_1357_ = lean_unsigned_to_nat(0u);
v___x_1358_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_1359_ = l_Lake_Manifest_load(v___x_1356_);
if (lean_obj_tag(v___x_1359_) == 0)
{
lean_object* v_a_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1367_; 
v_a_1360_ = lean_ctor_get(v___x_1359_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1362_ = v___x_1359_;
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_a_1360_);
lean_dec(v___x_1359_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1365_; 
if (v_isShared_1363_ == 0)
{
lean_ctor_set_tag(v___x_1362_, 1);
v___x_1365_ = v___x_1362_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_a_1360_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
v___y_1319_ = v_val_1354_;
v___y_1320_ = v___x_1358_;
v___y_1321_ = v___x_1315_;
v___y_1322_ = v___x_1357_;
v_val_1323_ = v___x_1365_;
goto v___jp_1318_;
}
}
}
else
{
lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1375_; 
v_a_1368_ = lean_ctor_get(v___x_1359_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1370_ = v___x_1359_;
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_dec(v___x_1359_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1373_; 
if (v_isShared_1371_ == 0)
{
lean_ctor_set_tag(v___x_1370_, 0);
v___x_1373_ = v___x_1370_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_a_1368_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
v___y_1319_ = v_val_1354_;
v___y_1320_ = v___x_1358_;
v___y_1321_ = v___x_1315_;
v___y_1322_ = v___x_1357_;
v_val_1323_ = v___x_1373_;
goto v___jp_1318_;
}
}
}
}
else
{
lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; uint8_t v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
lean_dec(v_a_1353_);
lean_dec_ref(v_src_1292_);
lean_dec_ref(v_remoteUrl_1291_);
lean_dec_ref(v_relPkgDir_1290_);
lean_dec_ref(v_dep_1286_);
v___x_1376_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0));
v___x_1377_ = lean_string_append(v_name_1289_, v___x_1376_);
v___x_1378_ = lean_string_append(v___x_1377_, v_pkgDir_1314_);
lean_dec_ref(v_pkgDir_1314_);
v___x_1379_ = 3;
v___x_1380_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1380_, 0, v___x_1378_);
lean_ctor_set_uint8(v___x_1380_, sizeof(void*)*1, v___x_1379_);
lean_inc_ref(v_a_1293_);
v___x_1381_ = lean_apply_2(v_a_1293_, v___x_1380_, lean_box(0));
v___x_1382_ = lean_box(0);
v___x_1383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1382_);
return v___x_1383_;
}
}
v___jp_1386_:
{
uint8_t v___x_1388_; 
v___x_1388_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_1388_ == 0)
{
v_a_1353_ = v_val_1387_;
goto v___jp_1352_;
}
else
{
lean_object* v___x_1389_; uint8_t v___x_1390_; 
v___x_1389_ = lean_box(0);
v___x_1390_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
if (v___x_1390_ == 0)
{
if (v___x_1388_ == 0)
{
v_a_1353_ = v_val_1387_;
goto v___jp_1352_;
}
else
{
size_t v___x_1391_; size_t v___x_1392_; lean_object* v___x_2450__overap_1393_; lean_object* v___x_1394_; 
v___x_1391_ = ((size_t)0ULL);
v___x_1392_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8);
v___x_2450__overap_1393_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1315_, v___f_1317_, v___x_1385_, v___x_1391_, v___x_1392_, v___x_1389_);
lean_inc_ref(v_a_1293_);
v___x_1394_ = lean_apply_2(v___x_2450__overap_1393_, v_a_1293_, lean_box(0));
if (lean_obj_tag(v___x_1394_) == 0)
{
lean_dec_ref_known(v___x_1394_, 1);
v_a_1353_ = v_val_1387_;
goto v___jp_1352_;
}
else
{
lean_object* v_a_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1402_; 
lean_dec(v_val_1387_);
lean_dec_ref(v_pkgDir_1314_);
lean_dec_ref(v_src_1292_);
lean_dec_ref(v_remoteUrl_1291_);
lean_dec_ref(v_relPkgDir_1290_);
lean_dec_ref(v_name_1289_);
lean_dec_ref(v_dep_1286_);
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
size_t v___x_1403_; size_t v___x_1404_; lean_object* v___x_2460__overap_1405_; lean_object* v___x_1406_; 
v___x_1403_ = ((size_t)0ULL);
v___x_1404_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8);
v___x_2460__overap_1405_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1315_, v___f_1317_, v___x_1385_, v___x_1403_, v___x_1404_, v___x_1389_);
lean_inc_ref(v_a_1293_);
v___x_1406_ = lean_apply_2(v___x_2460__overap_1405_, v_a_1293_, lean_box(0));
if (lean_obj_tag(v___x_1406_) == 0)
{
lean_dec_ref_known(v___x_1406_, 1);
v_a_1353_ = v_val_1387_;
goto v___jp_1352_;
}
else
{
lean_object* v_a_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1414_; 
lean_dec(v_val_1387_);
lean_dec_ref(v_pkgDir_1314_);
lean_dec_ref(v_src_1292_);
lean_dec_ref(v_remoteUrl_1291_);
lean_dec_ref(v_relPkgDir_1290_);
lean_dec_ref(v_name_1289_);
lean_dec_ref(v_dep_1286_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___boxed(lean_object* v_dep_1419_, lean_object* v_inherited_1420_, lean_object* v_wsDir_1421_, lean_object* v_name_1422_, lean_object* v_relPkgDir_1423_, lean_object* v_remoteUrl_1424_, lean_object* v_src_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_){
_start:
{
uint8_t v_inherited_boxed_1428_; lean_object* v_res_1429_; 
v_inherited_boxed_1428_ = lean_unbox(v_inherited_1420_);
v_res_1429_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep(v_dep_1419_, v_inherited_boxed_1428_, v_wsDir_1421_, v_name_1422_, v_relPkgDir_1423_, v_remoteUrl_1424_, v_src_1425_, v_a_1426_);
lean_dec_ref(v_a_1426_);
return v_res_1429_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(lean_object* v_a_1430_, lean_object* v_name_1431_, lean_object* v_repo_1432_, lean_object* v_url_1433_, lean_object* v_rev_x3f_1434_){
_start:
{
lean_object* v___y_1446_; lean_object* v___y_1457_; lean_object* v___y_1480_; lean_object* v___y_1485_; uint8_t v_a_1486_; lean_object* v___y_1494_; lean_object* v___y_1542_; lean_object* v___y_1543_; lean_object* v___y_1545_; lean_object* v___y_1546_; lean_object* v___y_1575_; lean_object* v___y_1576_; uint8_t v_a_1577_; lean_object* v___y_1585_; lean_object* v___y_1586_; lean_object* v___y_1587_; lean_object* v___y_1589_; lean_object* v___y_1590_; lean_object* v___y_1591_; lean_object* v___y_1592_; uint8_t v_val_1593_; lean_object* v___y_1605_; lean_object* v___y_1606_; lean_object* v___y_1613_; lean_object* v___y_1614_; lean_object* v___y_1615_; lean_object* v___y_1617_; lean_object* v___y_1618_; lean_object* v___y_1647_; lean_object* v___y_1648_; lean_object* v___y_1649_; lean_object* v___y_1651_; lean_object* v___y_1652_; lean_object* v___y_1653_; uint8_t v_val_1654_; lean_object* v___y_1666_; lean_object* v___y_1667_; lean_object* v___y_1668_; lean_object* v___y_1669_; lean_object* v_a_1670_; lean_object* v___y_1713_; lean_object* v___y_1714_; lean_object* v___y_1715_; lean_object* v___y_1716_; lean_object* v_a_1717_; lean_object* v___y_1743_; lean_object* v___y_1744_; lean_object* v___y_1745_; lean_object* v___y_1746_; lean_object* v___y_1785_; lean_object* v___y_1786_; lean_object* v___y_1787_; lean_object* v___y_1788_; lean_object* v___y_1790_; lean_object* v___y_1791_; lean_object* v___y_1792_; lean_object* v___y_1821_; lean_object* v___y_1822_; lean_object* v___y_1823_; lean_object* v___y_1824_; lean_object* v___y_1826_; uint8_t v_a_1827_; lean_object* v___y_1835_; uint8_t v_a_1836_; lean_object* v___y_1844_; lean_object* v___y_1845_; lean_object* v___y_1846_; uint8_t v_val_1847_; uint8_t v___y_1859_; lean_object* v___y_1860_; uint8_t v___y_1861_; uint8_t v___y_1866_; lean_object* v___y_1867_; uint8_t v___y_1868_; lean_object* v___y_1869_; uint8_t v___y_1871_; lean_object* v___y_1872_; uint8_t v___y_1873_; uint8_t v___y_1902_; lean_object* v___y_1903_; uint8_t v___y_1904_; lean_object* v___y_1905_; lean_object* v___y_1907_; uint8_t v___y_1908_; lean_object* v___y_1909_; lean_object* v___y_1910_; uint8_t v___y_1911_; lean_object* v___y_1912_; lean_object* v_a_1913_; lean_object* v___y_1957_; lean_object* v___y_1958_; lean_object* v___y_1959_; uint8_t v_val_1960_; lean_object* v___y_1972_; uint8_t v___y_1973_; lean_object* v___y_1974_; lean_object* v___y_1975_; lean_object* v___y_1976_; lean_object* v_a_1977_; lean_object* v___y_1998_; lean_object* v___y_1999_; uint8_t v___y_2000_; lean_object* v___y_2001_; lean_object* v___y_2002_; lean_object* v___y_2016_; uint8_t v___y_2017_; lean_object* v___y_2018_; lean_object* v___y_2019_; lean_object* v___y_2020_; lean_object* v___y_2022_; uint8_t v___y_2023_; lean_object* v___y_2024_; lean_object* v___y_2025_; lean_object* v___y_2026_; lean_object* v___y_2028_; uint8_t v___y_2029_; lean_object* v___y_2030_; lean_object* v___y_2031_; lean_object* v_a_2032_; lean_object* v___y_2105_; lean_object* v___y_2106_; lean_object* v___y_2107_; uint8_t v_a_2108_; lean_object* v___y_2174_; lean_object* v___y_2175_; lean_object* v_a_2176_; lean_object* v___y_2191_; lean_object* v___y_2192_; lean_object* v_a_2193_; lean_object* v___y_2204_; lean_object* v___y_2205_; lean_object* v___y_2206_; lean_object* v___y_2207_; lean_object* v_val_2208_; lean_object* v___y_2220_; lean_object* v___y_2221_; uint8_t v_a_2222_; lean_object* v___y_2231_; 
if (lean_obj_tag(v_rev_x3f_1434_) == 0)
{
lean_object* v___x_2244_; 
v___x_2244_ = l_Lake_Git_upstreamBranch;
v___y_2231_ = v___x_2244_;
goto v___jp_2230_;
}
else
{
lean_object* v_val_2245_; 
v_val_2245_ = lean_ctor_get(v_rev_x3f_1434_, 0);
lean_inc(v_val_2245_);
lean_dec_ref_known(v_rev_x3f_1434_, 1);
v___y_2231_ = v_val_2245_;
goto v___jp_2230_;
}
v___jp_1436_:
{
lean_object* v___x_1437_; lean_object* v___x_1438_; 
v___x_1437_ = lean_box(0);
v___x_1438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1438_, 0, v___x_1437_);
return v___x_1438_;
}
v___jp_1439_:
{
lean_object* v___x_1440_; lean_object* v___x_1441_; 
v___x_1440_ = lean_box(0);
v___x_1441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1441_, 0, v___x_1440_);
return v___x_1441_;
}
v___jp_1442_:
{
lean_object* v___x_1443_; lean_object* v___x_1444_; 
v___x_1443_ = lean_box(0);
v___x_1444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1444_, 0, v___x_1443_);
return v___x_1444_;
}
v___jp_1445_:
{
if (lean_obj_tag(v___y_1446_) == 0)
{
lean_dec_ref_known(v___y_1446_, 1);
goto v___jp_1442_;
}
else
{
return v___y_1446_;
}
}
v___jp_1447_:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1448_ = lean_box(0);
v___x_1449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1448_);
return v___x_1449_;
}
v___jp_1450_:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; 
v___x_1451_ = lean_box(0);
v___x_1452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1452_, 0, v___x_1451_);
return v___x_1452_;
}
v___jp_1453_:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1454_ = lean_box(0);
v___x_1455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1455_, 0, v___x_1454_);
return v___x_1455_;
}
v___jp_1456_:
{
if (lean_obj_tag(v___y_1457_) == 0)
{
lean_dec_ref_known(v___y_1457_, 1);
goto v___jp_1453_;
}
else
{
return v___y_1457_;
}
}
v___jp_1458_:
{
lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1459_ = lean_box(0);
v___x_1460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1460_, 0, v___x_1459_);
return v___x_1460_;
}
v___jp_1461_:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1462_ = lean_box(0);
v___x_1463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1463_, 0, v___x_1462_);
return v___x_1463_;
}
v___jp_1464_:
{
lean_object* v___x_1465_; lean_object* v___x_1466_; 
v___x_1465_ = lean_box(0);
v___x_1466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1466_, 0, v___x_1465_);
return v___x_1466_;
}
v___jp_1467_:
{
lean_object* v___x_1468_; lean_object* v___x_1469_; 
v___x_1468_ = lean_box(0);
v___x_1469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1468_);
return v___x_1469_;
}
v___jp_1470_:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; 
v___x_1471_ = lean_box(0);
v___x_1472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1472_, 0, v___x_1471_);
return v___x_1472_;
}
v___jp_1473_:
{
lean_object* v___x_1474_; lean_object* v___x_1475_; 
v___x_1474_ = lean_box(0);
v___x_1475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1475_, 0, v___x_1474_);
return v___x_1475_;
}
v___jp_1476_:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1477_ = lean_box(0);
v___x_1478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1478_, 0, v___x_1477_);
return v___x_1478_;
}
v___jp_1479_:
{
if (lean_obj_tag(v___y_1480_) == 0)
{
lean_dec_ref_known(v___y_1480_, 1);
goto v___jp_1476_;
}
else
{
return v___y_1480_;
}
}
v___jp_1481_:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; 
v___x_1482_ = lean_box(0);
v___x_1483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1483_, 0, v___x_1482_);
return v___x_1483_;
}
v___jp_1484_:
{
if (v_a_1486_ == 0)
{
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
goto v___jp_1476_;
}
else
{
lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; uint8_t v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1487_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff___closed__0));
v___x_1488_ = lean_string_append(v_name_1431_, v___x_1487_);
v___x_1489_ = lean_string_append(v___x_1488_, v_repo_1432_);
lean_dec_ref(v_repo_1432_);
v___x_1490_ = 2;
v___x_1491_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1491_, 0, v___x_1489_);
lean_ctor_set_uint8(v___x_1491_, sizeof(void*)*1, v___x_1490_);
lean_inc_ref(v___y_1485_);
v___x_1492_ = lean_apply_2(v___y_1485_, v___x_1491_, lean_box(0));
goto v___jp_1476_;
}
}
v___jp_1493_:
{
lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___x_1495_ = lean_unsigned_to_nat(0u);
v___x_1496_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_1497_ = l_Lake_GitRepo_gcAuto(v_repo_1432_, v___x_1496_);
if (lean_obj_tag(v___x_1497_) == 0)
{
lean_object* v_a_1498_; lean_object* v_a_1499_; lean_object* v___x_1500_; uint8_t v___x_1501_; 
v_a_1498_ = lean_ctor_get(v___x_1497_, 0);
lean_inc(v_a_1498_);
v_a_1499_ = lean_ctor_get(v___x_1497_, 1);
lean_inc(v_a_1499_);
lean_dec_ref_known(v___x_1497_, 2);
v___x_1500_ = lean_array_get_size(v_a_1499_);
v___x_1501_ = lean_nat_dec_lt(v___x_1495_, v___x_1500_);
if (v___x_1501_ == 0)
{
lean_object* v___x_1502_; 
lean_dec(v_a_1499_);
v___x_1502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1502_, 0, v_a_1498_);
return v___x_1502_;
}
else
{
lean_object* v___x_1503_; uint8_t v___x_1504_; 
v___x_1503_ = lean_box(0);
v___x_1504_ = lean_nat_dec_le(v___x_1500_, v___x_1500_);
if (v___x_1504_ == 0)
{
if (v___x_1501_ == 0)
{
lean_object* v___x_1505_; 
lean_dec(v_a_1499_);
v___x_1505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1505_, 0, v_a_1498_);
return v___x_1505_;
}
else
{
size_t v___x_1506_; size_t v___x_1507_; lean_object* v___x_1508_; 
v___x_1506_ = ((size_t)0ULL);
v___x_1507_ = lean_usize_of_nat(v___x_1500_);
v___x_1508_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1499_, v___x_1506_, v___x_1507_, v___x_1503_, v___y_1494_);
lean_dec(v_a_1499_);
if (lean_obj_tag(v___x_1508_) == 0)
{
lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1515_; 
v_isSharedCheck_1515_ = !lean_is_exclusive(v___x_1508_);
if (v_isSharedCheck_1515_ == 0)
{
lean_object* v_unused_1516_; 
v_unused_1516_ = lean_ctor_get(v___x_1508_, 0);
lean_dec(v_unused_1516_);
v___x_1510_ = v___x_1508_;
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
else
{
lean_dec(v___x_1508_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1513_; 
if (v_isShared_1511_ == 0)
{
lean_ctor_set(v___x_1510_, 0, v_a_1498_);
v___x_1513_ = v___x_1510_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_a_1498_);
v___x_1513_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
return v___x_1513_;
}
}
}
else
{
lean_dec(v_a_1498_);
return v___x_1508_;
}
}
}
else
{
size_t v___x_1517_; size_t v___x_1518_; lean_object* v___x_1519_; 
v___x_1517_ = ((size_t)0ULL);
v___x_1518_ = lean_usize_of_nat(v___x_1500_);
v___x_1519_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1499_, v___x_1517_, v___x_1518_, v___x_1503_, v___y_1494_);
lean_dec(v_a_1499_);
if (lean_obj_tag(v___x_1519_) == 0)
{
lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1526_; 
v_isSharedCheck_1526_ = !lean_is_exclusive(v___x_1519_);
if (v_isSharedCheck_1526_ == 0)
{
lean_object* v_unused_1527_; 
v_unused_1527_ = lean_ctor_get(v___x_1519_, 0);
lean_dec(v_unused_1527_);
v___x_1521_ = v___x_1519_;
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
else
{
lean_dec(v___x_1519_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1524_; 
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 0, v_a_1498_);
v___x_1524_ = v___x_1521_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_a_1498_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
return v___x_1524_;
}
}
}
else
{
lean_dec(v_a_1498_);
return v___x_1519_;
}
}
}
}
else
{
lean_object* v_a_1528_; lean_object* v___x_1529_; uint8_t v___x_1530_; 
v_a_1528_ = lean_ctor_get(v___x_1497_, 1);
lean_inc(v_a_1528_);
lean_dec_ref_known(v___x_1497_, 2);
v___x_1529_ = lean_array_get_size(v_a_1528_);
v___x_1530_ = lean_nat_dec_lt(v___x_1495_, v___x_1529_);
if (v___x_1530_ == 0)
{
lean_object* v___x_1531_; lean_object* v___x_1532_; 
lean_dec(v_a_1528_);
v___x_1531_ = lean_box(0);
v___x_1532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1531_);
return v___x_1532_;
}
else
{
lean_object* v___x_1533_; uint8_t v___x_1534_; 
v___x_1533_ = lean_box(0);
v___x_1534_ = lean_nat_dec_le(v___x_1529_, v___x_1529_);
if (v___x_1534_ == 0)
{
if (v___x_1530_ == 0)
{
lean_dec(v_a_1528_);
goto v___jp_1464_;
}
else
{
size_t v___x_1535_; size_t v___x_1536_; lean_object* v___x_1537_; 
v___x_1535_ = ((size_t)0ULL);
v___x_1536_ = lean_usize_of_nat(v___x_1529_);
v___x_1537_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1528_, v___x_1535_, v___x_1536_, v___x_1533_, v___y_1494_);
lean_dec(v_a_1528_);
if (lean_obj_tag(v___x_1537_) == 0)
{
lean_dec_ref_known(v___x_1537_, 1);
goto v___jp_1464_;
}
else
{
return v___x_1537_;
}
}
}
else
{
size_t v___x_1538_; size_t v___x_1539_; lean_object* v___x_1540_; 
v___x_1538_ = ((size_t)0ULL);
v___x_1539_ = lean_usize_of_nat(v___x_1529_);
v___x_1540_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1528_, v___x_1538_, v___x_1539_, v___x_1533_, v___y_1494_);
lean_dec(v_a_1528_);
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_dec_ref_known(v___x_1540_, 1);
goto v___jp_1464_;
}
else
{
return v___x_1540_;
}
}
}
}
}
v___jp_1541_:
{
if (lean_obj_tag(v___y_1543_) == 0)
{
lean_dec_ref_known(v___y_1543_, 1);
v___y_1494_ = v___y_1542_;
goto v___jp_1493_;
}
else
{
lean_dec_ref(v_repo_1432_);
return v___y_1543_;
}
}
v___jp_1544_:
{
lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1547_ = lean_unsigned_to_nat(0u);
v___x_1548_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1432_);
lean_inc_ref(v___y_1546_);
v___x_1549_ = l_Lake_GitRepo_pruneRemote(v___y_1546_, v_repo_1432_, v___x_1548_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v_a_1550_; lean_object* v___x_1551_; uint8_t v___x_1552_; 
v_a_1550_ = lean_ctor_get(v___x_1549_, 1);
lean_inc(v_a_1550_);
lean_dec_ref_known(v___x_1549_, 2);
v___x_1551_ = lean_array_get_size(v_a_1550_);
v___x_1552_ = lean_nat_dec_lt(v___x_1547_, v___x_1551_);
if (v___x_1552_ == 0)
{
lean_dec(v_a_1550_);
v___y_1494_ = v___y_1545_;
goto v___jp_1493_;
}
else
{
lean_object* v___x_1553_; uint8_t v___x_1554_; 
v___x_1553_ = lean_box(0);
v___x_1554_ = lean_nat_dec_le(v___x_1551_, v___x_1551_);
if (v___x_1554_ == 0)
{
if (v___x_1552_ == 0)
{
lean_dec(v_a_1550_);
v___y_1494_ = v___y_1545_;
goto v___jp_1493_;
}
else
{
size_t v___x_1555_; size_t v___x_1556_; lean_object* v___x_1557_; 
v___x_1555_ = ((size_t)0ULL);
v___x_1556_ = lean_usize_of_nat(v___x_1551_);
v___x_1557_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1550_, v___x_1555_, v___x_1556_, v___x_1553_, v___y_1545_);
lean_dec(v_a_1550_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_dec_ref_known(v___x_1557_, 1);
v___y_1494_ = v___y_1545_;
goto v___jp_1493_;
}
else
{
v___y_1542_ = v___y_1545_;
v___y_1543_ = v___x_1557_;
goto v___jp_1541_;
}
}
}
else
{
size_t v___x_1558_; size_t v___x_1559_; lean_object* v___x_1560_; 
v___x_1558_ = ((size_t)0ULL);
v___x_1559_ = lean_usize_of_nat(v___x_1551_);
v___x_1560_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1550_, v___x_1558_, v___x_1559_, v___x_1553_, v___y_1545_);
lean_dec(v_a_1550_);
if (lean_obj_tag(v___x_1560_) == 0)
{
lean_dec_ref_known(v___x_1560_, 1);
v___y_1494_ = v___y_1545_;
goto v___jp_1493_;
}
else
{
v___y_1542_ = v___y_1545_;
v___y_1543_ = v___x_1560_;
goto v___jp_1541_;
}
}
}
}
else
{
lean_object* v_a_1561_; lean_object* v___x_1562_; uint8_t v___x_1563_; 
v_a_1561_ = lean_ctor_get(v___x_1549_, 1);
lean_inc(v_a_1561_);
lean_dec_ref_known(v___x_1549_, 2);
v___x_1562_ = lean_array_get_size(v_a_1561_);
v___x_1563_ = lean_nat_dec_lt(v___x_1547_, v___x_1562_);
if (v___x_1563_ == 0)
{
lean_object* v___x_1564_; lean_object* v___x_1565_; 
lean_dec(v_a_1561_);
lean_dec_ref(v_repo_1432_);
v___x_1564_ = lean_box(0);
v___x_1565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1564_);
return v___x_1565_;
}
else
{
lean_object* v___x_1566_; uint8_t v___x_1567_; 
v___x_1566_ = lean_box(0);
v___x_1567_ = lean_nat_dec_le(v___x_1562_, v___x_1562_);
if (v___x_1567_ == 0)
{
if (v___x_1563_ == 0)
{
lean_dec(v_a_1561_);
lean_dec_ref(v_repo_1432_);
goto v___jp_1467_;
}
else
{
size_t v___x_1568_; size_t v___x_1569_; lean_object* v___x_1570_; 
v___x_1568_ = ((size_t)0ULL);
v___x_1569_ = lean_usize_of_nat(v___x_1562_);
v___x_1570_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1561_, v___x_1568_, v___x_1569_, v___x_1566_, v___y_1545_);
lean_dec(v_a_1561_);
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_dec_ref_known(v___x_1570_, 1);
lean_dec_ref(v_repo_1432_);
goto v___jp_1467_;
}
else
{
v___y_1542_ = v___y_1545_;
v___y_1543_ = v___x_1570_;
goto v___jp_1541_;
}
}
}
else
{
size_t v___x_1571_; size_t v___x_1572_; lean_object* v___x_1573_; 
v___x_1571_ = ((size_t)0ULL);
v___x_1572_ = lean_usize_of_nat(v___x_1562_);
v___x_1573_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1561_, v___x_1571_, v___x_1572_, v___x_1566_, v___y_1545_);
lean_dec(v_a_1561_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_dec_ref_known(v___x_1573_, 1);
lean_dec_ref(v_repo_1432_);
goto v___jp_1467_;
}
else
{
v___y_1542_ = v___y_1545_;
v___y_1543_ = v___x_1573_;
goto v___jp_1541_;
}
}
}
}
}
v___jp_1574_:
{
if (v_a_1577_ == 0)
{
lean_dec_ref(v_name_1431_);
v___y_1545_ = v___y_1576_;
v___y_1546_ = v___y_1575_;
goto v___jp_1544_;
}
else
{
lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; uint8_t v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; 
v___x_1578_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff___closed__0));
v___x_1579_ = lean_string_append(v_name_1431_, v___x_1578_);
v___x_1580_ = lean_string_append(v___x_1579_, v_repo_1432_);
v___x_1581_ = 2;
v___x_1582_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1582_, 0, v___x_1580_);
lean_ctor_set_uint8(v___x_1582_, sizeof(void*)*1, v___x_1581_);
lean_inc_ref(v___y_1576_);
v___x_1583_ = lean_apply_2(v___y_1576_, v___x_1582_, lean_box(0));
v___y_1545_ = v___y_1576_;
v___y_1546_ = v___y_1575_;
goto v___jp_1544_;
}
}
v___jp_1584_:
{
if (lean_obj_tag(v___y_1587_) == 0)
{
lean_dec_ref_known(v___y_1587_, 1);
v___y_1545_ = v___y_1586_;
v___y_1546_ = v___y_1585_;
goto v___jp_1544_;
}
else
{
lean_dec_ref(v_repo_1432_);
return v___y_1587_;
}
}
v___jp_1588_:
{
lean_object* v___x_1594_; uint8_t v___x_1595_; 
v___x_1594_ = lean_array_get_size(v___y_1592_);
v___x_1595_ = lean_nat_dec_lt(v___y_1591_, v___x_1594_);
if (v___x_1595_ == 0)
{
v___y_1575_ = v___y_1590_;
v___y_1576_ = v___y_1589_;
v_a_1577_ = v_val_1593_;
goto v___jp_1574_;
}
else
{
lean_object* v___x_1596_; uint8_t v___x_1597_; 
v___x_1596_ = lean_box(0);
v___x_1597_ = lean_nat_dec_le(v___x_1594_, v___x_1594_);
if (v___x_1597_ == 0)
{
if (v___x_1595_ == 0)
{
v___y_1575_ = v___y_1590_;
v___y_1576_ = v___y_1589_;
v_a_1577_ = v_val_1593_;
goto v___jp_1574_;
}
else
{
size_t v___x_1598_; size_t v___x_1599_; lean_object* v___x_1600_; 
v___x_1598_ = ((size_t)0ULL);
v___x_1599_ = lean_usize_of_nat(v___x_1594_);
v___x_1600_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_1592_, v___x_1598_, v___x_1599_, v___x_1596_, v___y_1589_);
if (lean_obj_tag(v___x_1600_) == 0)
{
lean_dec_ref_known(v___x_1600_, 1);
v___y_1575_ = v___y_1590_;
v___y_1576_ = v___y_1589_;
v_a_1577_ = v_val_1593_;
goto v___jp_1574_;
}
else
{
lean_dec_ref(v_name_1431_);
v___y_1585_ = v___y_1590_;
v___y_1586_ = v___y_1589_;
v___y_1587_ = v___x_1600_;
goto v___jp_1584_;
}
}
}
else
{
size_t v___x_1601_; size_t v___x_1602_; lean_object* v___x_1603_; 
v___x_1601_ = ((size_t)0ULL);
v___x_1602_ = lean_usize_of_nat(v___x_1594_);
v___x_1603_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_1592_, v___x_1601_, v___x_1602_, v___x_1596_, v___y_1589_);
if (lean_obj_tag(v___x_1603_) == 0)
{
lean_dec_ref_known(v___x_1603_, 1);
v___y_1575_ = v___y_1590_;
v___y_1576_ = v___y_1589_;
v_a_1577_ = v_val_1593_;
goto v___jp_1574_;
}
else
{
lean_dec_ref(v_name_1431_);
v___y_1585_ = v___y_1590_;
v___y_1586_ = v___y_1589_;
v___y_1587_ = v___x_1603_;
goto v___jp_1584_;
}
}
}
}
v___jp_1604_:
{
uint8_t v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; 
lean_inc_ref(v_repo_1432_);
v___x_1607_ = l_Lake_GitRepo_hasNoDiff(v_repo_1432_);
v___x_1608_ = lean_unsigned_to_nat(0u);
v___x_1609_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
if (v___x_1607_ == 0)
{
uint8_t v___x_1610_; 
v___x_1610_ = 1;
v___y_1589_ = v___y_1606_;
v___y_1590_ = v___y_1605_;
v___y_1591_ = v___x_1608_;
v___y_1592_ = v___x_1609_;
v_val_1593_ = v___x_1610_;
goto v___jp_1588_;
}
else
{
uint8_t v___x_1611_; 
v___x_1611_ = 0;
v___y_1589_ = v___y_1606_;
v___y_1590_ = v___y_1605_;
v___y_1591_ = v___x_1608_;
v___y_1592_ = v___x_1609_;
v_val_1593_ = v___x_1611_;
goto v___jp_1588_;
}
}
v___jp_1612_:
{
if (lean_obj_tag(v___y_1615_) == 0)
{
lean_dec_ref_known(v___y_1615_, 1);
v___y_1605_ = v___y_1614_;
v___y_1606_ = v___y_1613_;
goto v___jp_1604_;
}
else
{
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
return v___y_1615_;
}
}
v___jp_1616_:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; 
v___x_1619_ = lean_unsigned_to_nat(0u);
v___x_1620_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1432_);
v___x_1621_ = l_Lake_GitRepo_clean(v_repo_1432_, v___x_1620_);
if (lean_obj_tag(v___x_1621_) == 0)
{
lean_object* v_a_1622_; lean_object* v___x_1623_; uint8_t v___x_1624_; 
v_a_1622_ = lean_ctor_get(v___x_1621_, 1);
lean_inc(v_a_1622_);
lean_dec_ref_known(v___x_1621_, 2);
v___x_1623_ = lean_array_get_size(v_a_1622_);
v___x_1624_ = lean_nat_dec_lt(v___x_1619_, v___x_1623_);
if (v___x_1624_ == 0)
{
lean_dec(v_a_1622_);
v___y_1605_ = v___y_1618_;
v___y_1606_ = v___y_1617_;
goto v___jp_1604_;
}
else
{
lean_object* v___x_1625_; uint8_t v___x_1626_; 
v___x_1625_ = lean_box(0);
v___x_1626_ = lean_nat_dec_le(v___x_1623_, v___x_1623_);
if (v___x_1626_ == 0)
{
if (v___x_1624_ == 0)
{
lean_dec(v_a_1622_);
v___y_1605_ = v___y_1618_;
v___y_1606_ = v___y_1617_;
goto v___jp_1604_;
}
else
{
size_t v___x_1627_; size_t v___x_1628_; lean_object* v___x_1629_; 
v___x_1627_ = ((size_t)0ULL);
v___x_1628_ = lean_usize_of_nat(v___x_1623_);
v___x_1629_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1622_, v___x_1627_, v___x_1628_, v___x_1625_, v___y_1617_);
lean_dec(v_a_1622_);
if (lean_obj_tag(v___x_1629_) == 0)
{
lean_dec_ref_known(v___x_1629_, 1);
v___y_1605_ = v___y_1618_;
v___y_1606_ = v___y_1617_;
goto v___jp_1604_;
}
else
{
v___y_1613_ = v___y_1617_;
v___y_1614_ = v___y_1618_;
v___y_1615_ = v___x_1629_;
goto v___jp_1612_;
}
}
}
else
{
size_t v___x_1630_; size_t v___x_1631_; lean_object* v___x_1632_; 
v___x_1630_ = ((size_t)0ULL);
v___x_1631_ = lean_usize_of_nat(v___x_1623_);
v___x_1632_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1622_, v___x_1630_, v___x_1631_, v___x_1625_, v___y_1617_);
lean_dec(v_a_1622_);
if (lean_obj_tag(v___x_1632_) == 0)
{
lean_dec_ref_known(v___x_1632_, 1);
v___y_1605_ = v___y_1618_;
v___y_1606_ = v___y_1617_;
goto v___jp_1604_;
}
else
{
v___y_1613_ = v___y_1617_;
v___y_1614_ = v___y_1618_;
v___y_1615_ = v___x_1632_;
goto v___jp_1612_;
}
}
}
}
else
{
lean_object* v_a_1633_; lean_object* v___x_1634_; uint8_t v___x_1635_; 
v_a_1633_ = lean_ctor_get(v___x_1621_, 1);
lean_inc(v_a_1633_);
lean_dec_ref_known(v___x_1621_, 2);
v___x_1634_ = lean_array_get_size(v_a_1633_);
v___x_1635_ = lean_nat_dec_lt(v___x_1619_, v___x_1634_);
if (v___x_1635_ == 0)
{
lean_object* v___x_1636_; lean_object* v___x_1637_; 
lean_dec(v_a_1633_);
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
v___x_1636_ = lean_box(0);
v___x_1637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1637_, 0, v___x_1636_);
return v___x_1637_;
}
else
{
lean_object* v___x_1638_; uint8_t v___x_1639_; 
v___x_1638_ = lean_box(0);
v___x_1639_ = lean_nat_dec_le(v___x_1634_, v___x_1634_);
if (v___x_1639_ == 0)
{
if (v___x_1635_ == 0)
{
lean_dec(v_a_1633_);
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
goto v___jp_1470_;
}
else
{
size_t v___x_1640_; size_t v___x_1641_; lean_object* v___x_1642_; 
v___x_1640_ = ((size_t)0ULL);
v___x_1641_ = lean_usize_of_nat(v___x_1634_);
v___x_1642_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1633_, v___x_1640_, v___x_1641_, v___x_1638_, v___y_1617_);
lean_dec(v_a_1633_);
if (lean_obj_tag(v___x_1642_) == 0)
{
lean_dec_ref_known(v___x_1642_, 1);
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
goto v___jp_1470_;
}
else
{
v___y_1613_ = v___y_1617_;
v___y_1614_ = v___y_1618_;
v___y_1615_ = v___x_1642_;
goto v___jp_1612_;
}
}
}
else
{
size_t v___x_1643_; size_t v___x_1644_; lean_object* v___x_1645_; 
v___x_1643_ = ((size_t)0ULL);
v___x_1644_ = lean_usize_of_nat(v___x_1634_);
v___x_1645_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1633_, v___x_1643_, v___x_1644_, v___x_1638_, v___y_1617_);
lean_dec(v_a_1633_);
if (lean_obj_tag(v___x_1645_) == 0)
{
lean_dec_ref_known(v___x_1645_, 1);
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
goto v___jp_1470_;
}
else
{
v___y_1613_ = v___y_1617_;
v___y_1614_ = v___y_1618_;
v___y_1615_ = v___x_1645_;
goto v___jp_1612_;
}
}
}
}
}
v___jp_1646_:
{
if (lean_obj_tag(v___y_1649_) == 0)
{
lean_dec_ref_known(v___y_1649_, 1);
v___y_1617_ = v___y_1648_;
v___y_1618_ = v___y_1647_;
goto v___jp_1616_;
}
else
{
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
return v___y_1649_;
}
}
v___jp_1650_:
{
lean_object* v___x_1655_; uint8_t v___x_1656_; 
v___x_1655_ = lean_array_get_size(v___y_1652_);
v___x_1656_ = lean_nat_dec_lt(v___y_1651_, v___x_1655_);
if (v___x_1656_ == 0)
{
v___y_1485_ = v___y_1653_;
v_a_1486_ = v_val_1654_;
goto v___jp_1484_;
}
else
{
lean_object* v___x_1657_; uint8_t v___x_1658_; 
v___x_1657_ = lean_box(0);
v___x_1658_ = lean_nat_dec_le(v___x_1655_, v___x_1655_);
if (v___x_1658_ == 0)
{
if (v___x_1656_ == 0)
{
v___y_1485_ = v___y_1653_;
v_a_1486_ = v_val_1654_;
goto v___jp_1484_;
}
else
{
size_t v___x_1659_; size_t v___x_1660_; lean_object* v___x_1661_; 
v___x_1659_ = ((size_t)0ULL);
v___x_1660_ = lean_usize_of_nat(v___x_1655_);
v___x_1661_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_1652_, v___x_1659_, v___x_1660_, v___x_1657_, v___y_1653_);
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_dec_ref_known(v___x_1661_, 1);
v___y_1485_ = v___y_1653_;
v_a_1486_ = v_val_1654_;
goto v___jp_1484_;
}
else
{
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
v___y_1480_ = v___x_1661_;
goto v___jp_1479_;
}
}
}
else
{
size_t v___x_1662_; size_t v___x_1663_; lean_object* v___x_1664_; 
v___x_1662_ = ((size_t)0ULL);
v___x_1663_ = lean_usize_of_nat(v___x_1655_);
v___x_1664_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_1652_, v___x_1662_, v___x_1663_, v___x_1657_, v___y_1653_);
if (lean_obj_tag(v___x_1664_) == 0)
{
lean_dec_ref_known(v___x_1664_, 1);
v___y_1485_ = v___y_1653_;
v_a_1486_ = v_val_1654_;
goto v___jp_1484_;
}
else
{
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
v___y_1480_ = v___x_1664_;
goto v___jp_1479_;
}
}
}
}
v___jp_1665_:
{
lean_object* v___x_1671_; uint8_t v___x_1672_; 
v___x_1671_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
v___x_1672_ = l_Option_instDecidableEq___redArg(v___x_1671_, v_a_1670_, v___y_1667_);
if (v___x_1672_ == 0)
{
lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; uint8_t v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1673_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__0));
lean_inc_ref(v_name_1431_);
v___x_1674_ = lean_string_append(v_name_1431_, v___x_1673_);
v___x_1675_ = lean_string_append(v___x_1674_, v___y_1666_);
v___x_1676_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__1));
v___x_1677_ = lean_string_append(v___x_1675_, v___x_1676_);
v___x_1678_ = 1;
v___x_1679_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1679_, 0, v___x_1677_);
lean_ctor_set_uint8(v___x_1679_, sizeof(void*)*1, v___x_1678_);
lean_inc_ref(v___y_1669_);
v___x_1680_ = lean_apply_2(v___y_1669_, v___x_1679_, lean_box(0));
v___x_1681_ = lean_unsigned_to_nat(0u);
v___x_1682_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1432_);
v___x_1683_ = l_Lake_GitRepo_checkoutDetach(v___y_1666_, v_repo_1432_, v___x_1682_);
if (lean_obj_tag(v___x_1683_) == 0)
{
lean_object* v_a_1684_; lean_object* v___x_1685_; uint8_t v___x_1686_; 
v_a_1684_ = lean_ctor_get(v___x_1683_, 1);
lean_inc(v_a_1684_);
lean_dec_ref_known(v___x_1683_, 2);
v___x_1685_ = lean_array_get_size(v_a_1684_);
v___x_1686_ = lean_nat_dec_lt(v___x_1681_, v___x_1685_);
if (v___x_1686_ == 0)
{
lean_dec(v_a_1684_);
v___y_1617_ = v___y_1669_;
v___y_1618_ = v___y_1668_;
goto v___jp_1616_;
}
else
{
lean_object* v___x_1687_; uint8_t v___x_1688_; 
v___x_1687_ = lean_box(0);
v___x_1688_ = lean_nat_dec_le(v___x_1685_, v___x_1685_);
if (v___x_1688_ == 0)
{
if (v___x_1686_ == 0)
{
lean_dec(v_a_1684_);
v___y_1617_ = v___y_1669_;
v___y_1618_ = v___y_1668_;
goto v___jp_1616_;
}
else
{
size_t v___x_1689_; size_t v___x_1690_; lean_object* v___x_1691_; 
v___x_1689_ = ((size_t)0ULL);
v___x_1690_ = lean_usize_of_nat(v___x_1685_);
v___x_1691_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1684_, v___x_1689_, v___x_1690_, v___x_1687_, v___y_1669_);
lean_dec(v_a_1684_);
if (lean_obj_tag(v___x_1691_) == 0)
{
lean_dec_ref_known(v___x_1691_, 1);
v___y_1617_ = v___y_1669_;
v___y_1618_ = v___y_1668_;
goto v___jp_1616_;
}
else
{
v___y_1647_ = v___y_1668_;
v___y_1648_ = v___y_1669_;
v___y_1649_ = v___x_1691_;
goto v___jp_1646_;
}
}
}
else
{
size_t v___x_1692_; size_t v___x_1693_; lean_object* v___x_1694_; 
v___x_1692_ = ((size_t)0ULL);
v___x_1693_ = lean_usize_of_nat(v___x_1685_);
v___x_1694_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1684_, v___x_1692_, v___x_1693_, v___x_1687_, v___y_1669_);
lean_dec(v_a_1684_);
if (lean_obj_tag(v___x_1694_) == 0)
{
lean_dec_ref_known(v___x_1694_, 1);
v___y_1617_ = v___y_1669_;
v___y_1618_ = v___y_1668_;
goto v___jp_1616_;
}
else
{
v___y_1647_ = v___y_1668_;
v___y_1648_ = v___y_1669_;
v___y_1649_ = v___x_1694_;
goto v___jp_1646_;
}
}
}
}
else
{
lean_object* v_a_1695_; lean_object* v___x_1696_; uint8_t v___x_1697_; 
v_a_1695_ = lean_ctor_get(v___x_1683_, 1);
lean_inc(v_a_1695_);
lean_dec_ref_known(v___x_1683_, 2);
v___x_1696_ = lean_array_get_size(v_a_1695_);
v___x_1697_ = lean_nat_dec_lt(v___x_1681_, v___x_1696_);
if (v___x_1697_ == 0)
{
lean_object* v___x_1698_; lean_object* v___x_1699_; 
lean_dec(v_a_1695_);
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
v___x_1698_ = lean_box(0);
v___x_1699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1699_, 0, v___x_1698_);
return v___x_1699_;
}
else
{
lean_object* v___x_1700_; uint8_t v___x_1701_; 
v___x_1700_ = lean_box(0);
v___x_1701_ = lean_nat_dec_le(v___x_1696_, v___x_1696_);
if (v___x_1701_ == 0)
{
if (v___x_1697_ == 0)
{
lean_dec(v_a_1695_);
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
goto v___jp_1473_;
}
else
{
size_t v___x_1702_; size_t v___x_1703_; lean_object* v___x_1704_; 
v___x_1702_ = ((size_t)0ULL);
v___x_1703_ = lean_usize_of_nat(v___x_1696_);
v___x_1704_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1695_, v___x_1702_, v___x_1703_, v___x_1700_, v___y_1669_);
lean_dec(v_a_1695_);
if (lean_obj_tag(v___x_1704_) == 0)
{
lean_dec_ref_known(v___x_1704_, 1);
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
goto v___jp_1473_;
}
else
{
v___y_1647_ = v___y_1668_;
v___y_1648_ = v___y_1669_;
v___y_1649_ = v___x_1704_;
goto v___jp_1646_;
}
}
}
else
{
size_t v___x_1705_; size_t v___x_1706_; lean_object* v___x_1707_; 
v___x_1705_ = ((size_t)0ULL);
v___x_1706_ = lean_usize_of_nat(v___x_1696_);
v___x_1707_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1695_, v___x_1705_, v___x_1706_, v___x_1700_, v___y_1669_);
lean_dec(v_a_1695_);
if (lean_obj_tag(v___x_1707_) == 0)
{
lean_dec_ref_known(v___x_1707_, 1);
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
goto v___jp_1473_;
}
else
{
v___y_1647_ = v___y_1668_;
v___y_1648_ = v___y_1669_;
v___y_1649_ = v___x_1707_;
goto v___jp_1646_;
}
}
}
}
}
else
{
uint8_t v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; 
lean_dec_ref(v___y_1666_);
lean_inc_ref(v_repo_1432_);
v___x_1708_ = l_Lake_GitRepo_hasNoDiff(v_repo_1432_);
v___x_1709_ = lean_unsigned_to_nat(0u);
v___x_1710_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
if (v___x_1708_ == 0)
{
v___y_1651_ = v___x_1709_;
v___y_1652_ = v___x_1710_;
v___y_1653_ = v___y_1669_;
v_val_1654_ = v___x_1672_;
goto v___jp_1650_;
}
else
{
uint8_t v___x_1711_; 
v___x_1711_ = 0;
v___y_1651_ = v___x_1709_;
v___y_1652_ = v___x_1710_;
v___y_1653_ = v___y_1669_;
v_val_1654_ = v___x_1711_;
goto v___jp_1650_;
}
}
}
v___jp_1712_:
{
if (lean_obj_tag(v_a_1717_) == 1)
{
lean_object* v_val_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; uint8_t v___x_1722_; 
lean_dec_ref(v___y_1714_);
lean_dec_ref(v___y_1713_);
v_val_1718_ = lean_ctor_get(v_a_1717_, 0);
lean_inc(v_val_1718_);
v___x_1719_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__0));
lean_inc_ref(v_repo_1432_);
v___x_1720_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_1719_, v_repo_1432_);
v___x_1721_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_1722_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_1722_ == 0)
{
v___y_1666_ = v_val_1718_;
v___y_1667_ = v_a_1717_;
v___y_1668_ = v___y_1716_;
v___y_1669_ = v___y_1715_;
v_a_1670_ = v___x_1720_;
goto v___jp_1665_;
}
else
{
lean_object* v___x_1723_; uint8_t v___x_1724_; 
v___x_1723_ = lean_box(0);
v___x_1724_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
if (v___x_1724_ == 0)
{
if (v___x_1722_ == 0)
{
v___y_1666_ = v_val_1718_;
v___y_1667_ = v_a_1717_;
v___y_1668_ = v___y_1716_;
v___y_1669_ = v___y_1715_;
v_a_1670_ = v___x_1720_;
goto v___jp_1665_;
}
else
{
size_t v___x_1725_; size_t v___x_1726_; lean_object* v___x_1727_; 
v___x_1725_ = ((size_t)0ULL);
v___x_1726_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8);
v___x_1727_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_1721_, v___x_1725_, v___x_1726_, v___x_1723_, v___y_1715_);
if (lean_obj_tag(v___x_1727_) == 0)
{
lean_dec_ref_known(v___x_1727_, 1);
v___y_1666_ = v_val_1718_;
v___y_1667_ = v_a_1717_;
v___y_1668_ = v___y_1716_;
v___y_1669_ = v___y_1715_;
v_a_1670_ = v___x_1720_;
goto v___jp_1665_;
}
else
{
lean_dec(v___x_1720_);
lean_dec_ref_known(v_a_1717_, 1);
lean_dec(v_val_1718_);
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
return v___x_1727_;
}
}
}
else
{
size_t v___x_1728_; size_t v___x_1729_; lean_object* v___x_1730_; 
v___x_1728_ = ((size_t)0ULL);
v___x_1729_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8);
v___x_1730_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_1721_, v___x_1728_, v___x_1729_, v___x_1723_, v___y_1715_);
if (lean_obj_tag(v___x_1730_) == 0)
{
lean_dec_ref_known(v___x_1730_, 1);
v___y_1666_ = v_val_1718_;
v___y_1667_ = v_a_1717_;
v___y_1668_ = v___y_1716_;
v___y_1669_ = v___y_1715_;
v_a_1670_ = v___x_1720_;
goto v___jp_1665_;
}
else
{
lean_dec(v___x_1720_);
lean_dec_ref_known(v_a_1717_, 1);
lean_dec(v_val_1718_);
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
return v___x_1730_;
}
}
}
}
else
{
lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; uint8_t v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; 
lean_dec(v_a_1717_);
lean_dec_ref(v_repo_1432_);
v___x_1731_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__1));
v___x_1732_ = lean_string_append(v_name_1431_, v___x_1731_);
v___x_1733_ = lean_string_append(v___x_1732_, v___y_1713_);
lean_dec_ref(v___y_1713_);
v___x_1734_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__2));
v___x_1735_ = lean_string_append(v___x_1733_, v___x_1734_);
v___x_1736_ = lean_string_append(v___x_1735_, v___y_1714_);
lean_dec_ref(v___y_1714_);
v___x_1737_ = 3;
v___x_1738_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1738_, 0, v___x_1736_);
lean_ctor_set_uint8(v___x_1738_, sizeof(void*)*1, v___x_1737_);
lean_inc_ref(v___y_1715_);
v___x_1739_ = lean_apply_2(v___y_1715_, v___x_1738_, lean_box(0));
v___x_1740_ = lean_box(0);
v___x_1741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1741_, 0, v___x_1740_);
return v___x_1741_;
}
}
v___jp_1742_:
{
lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; uint8_t v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; 
v___x_1747_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__3));
lean_inc_ref(v_name_1431_);
v___x_1748_ = lean_string_append(v_name_1431_, v___x_1747_);
v___x_1749_ = lean_string_append(v___x_1748_, v___y_1743_);
v___x_1750_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__4));
v___x_1751_ = lean_string_append(v___x_1749_, v___x_1750_);
v___x_1752_ = lean_string_append(v___x_1751_, v___y_1744_);
v___x_1753_ = 1;
v___x_1754_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1754_, 0, v___x_1752_);
lean_ctor_set_uint8(v___x_1754_, sizeof(void*)*1, v___x_1753_);
lean_inc_ref(v___y_1746_);
v___x_1755_ = lean_apply_2(v___y_1746_, v___x_1754_, lean_box(0));
v___x_1756_ = lean_unsigned_to_nat(0u);
v___x_1757_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v___y_1743_);
lean_inc_ref(v___y_1745_);
lean_inc_ref(v_repo_1432_);
v___x_1758_ = l_Lake_GitRepo_fetchRevision_x3f(v_repo_1432_, v___y_1745_, v___y_1743_, v___x_1757_);
if (lean_obj_tag(v___x_1758_) == 0)
{
lean_object* v_a_1759_; lean_object* v_a_1760_; lean_object* v___x_1761_; uint8_t v___x_1762_; 
v_a_1759_ = lean_ctor_get(v___x_1758_, 0);
lean_inc(v_a_1759_);
v_a_1760_ = lean_ctor_get(v___x_1758_, 1);
lean_inc(v_a_1760_);
lean_dec_ref_known(v___x_1758_, 2);
v___x_1761_ = lean_array_get_size(v_a_1760_);
v___x_1762_ = lean_nat_dec_lt(v___x_1756_, v___x_1761_);
if (v___x_1762_ == 0)
{
lean_dec(v_a_1760_);
v___y_1713_ = v___y_1743_;
v___y_1714_ = v___y_1744_;
v___y_1715_ = v___y_1746_;
v___y_1716_ = v___y_1745_;
v_a_1717_ = v_a_1759_;
goto v___jp_1712_;
}
else
{
lean_object* v___x_1763_; uint8_t v___x_1764_; 
v___x_1763_ = lean_box(0);
v___x_1764_ = lean_nat_dec_le(v___x_1761_, v___x_1761_);
if (v___x_1764_ == 0)
{
if (v___x_1762_ == 0)
{
lean_dec(v_a_1760_);
v___y_1713_ = v___y_1743_;
v___y_1714_ = v___y_1744_;
v___y_1715_ = v___y_1746_;
v___y_1716_ = v___y_1745_;
v_a_1717_ = v_a_1759_;
goto v___jp_1712_;
}
else
{
size_t v___x_1765_; size_t v___x_1766_; lean_object* v___x_1767_; 
v___x_1765_ = ((size_t)0ULL);
v___x_1766_ = lean_usize_of_nat(v___x_1761_);
v___x_1767_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1760_, v___x_1765_, v___x_1766_, v___x_1763_, v___y_1746_);
lean_dec(v_a_1760_);
if (lean_obj_tag(v___x_1767_) == 0)
{
lean_dec_ref_known(v___x_1767_, 1);
v___y_1713_ = v___y_1743_;
v___y_1714_ = v___y_1744_;
v___y_1715_ = v___y_1746_;
v___y_1716_ = v___y_1745_;
v_a_1717_ = v_a_1759_;
goto v___jp_1712_;
}
else
{
lean_dec(v_a_1759_);
lean_dec_ref(v___y_1744_);
lean_dec_ref(v___y_1743_);
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
return v___x_1767_;
}
}
}
else
{
size_t v___x_1768_; size_t v___x_1769_; lean_object* v___x_1770_; 
v___x_1768_ = ((size_t)0ULL);
v___x_1769_ = lean_usize_of_nat(v___x_1761_);
v___x_1770_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1760_, v___x_1768_, v___x_1769_, v___x_1763_, v___y_1746_);
lean_dec(v_a_1760_);
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_dec_ref_known(v___x_1770_, 1);
v___y_1713_ = v___y_1743_;
v___y_1714_ = v___y_1744_;
v___y_1715_ = v___y_1746_;
v___y_1716_ = v___y_1745_;
v_a_1717_ = v_a_1759_;
goto v___jp_1712_;
}
else
{
lean_dec(v_a_1759_);
lean_dec_ref(v___y_1744_);
lean_dec_ref(v___y_1743_);
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
return v___x_1770_;
}
}
}
}
else
{
lean_object* v_a_1771_; lean_object* v___x_1772_; uint8_t v___x_1773_; 
lean_dec_ref(v___y_1744_);
lean_dec_ref(v___y_1743_);
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
v_a_1771_ = lean_ctor_get(v___x_1758_, 1);
lean_inc(v_a_1771_);
lean_dec_ref_known(v___x_1758_, 2);
v___x_1772_ = lean_array_get_size(v_a_1771_);
v___x_1773_ = lean_nat_dec_lt(v___x_1756_, v___x_1772_);
if (v___x_1773_ == 0)
{
lean_object* v___x_1774_; lean_object* v___x_1775_; 
lean_dec(v_a_1771_);
v___x_1774_ = lean_box(0);
v___x_1775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1774_);
return v___x_1775_;
}
else
{
lean_object* v___x_1776_; uint8_t v___x_1777_; 
v___x_1776_ = lean_box(0);
v___x_1777_ = lean_nat_dec_le(v___x_1772_, v___x_1772_);
if (v___x_1777_ == 0)
{
if (v___x_1773_ == 0)
{
lean_dec(v_a_1771_);
goto v___jp_1481_;
}
else
{
size_t v___x_1778_; size_t v___x_1779_; lean_object* v___x_1780_; 
v___x_1778_ = ((size_t)0ULL);
v___x_1779_ = lean_usize_of_nat(v___x_1772_);
v___x_1780_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1771_, v___x_1778_, v___x_1779_, v___x_1776_, v___y_1746_);
lean_dec(v_a_1771_);
if (lean_obj_tag(v___x_1780_) == 0)
{
lean_dec_ref_known(v___x_1780_, 1);
goto v___jp_1481_;
}
else
{
return v___x_1780_;
}
}
}
else
{
size_t v___x_1781_; size_t v___x_1782_; lean_object* v___x_1783_; 
v___x_1781_ = ((size_t)0ULL);
v___x_1782_ = lean_usize_of_nat(v___x_1772_);
v___x_1783_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1771_, v___x_1781_, v___x_1782_, v___x_1776_, v___y_1746_);
lean_dec(v_a_1771_);
if (lean_obj_tag(v___x_1783_) == 0)
{
lean_dec_ref_known(v___x_1783_, 1);
goto v___jp_1481_;
}
else
{
return v___x_1783_;
}
}
}
}
}
v___jp_1784_:
{
if (lean_obj_tag(v___y_1788_) == 0)
{
lean_dec_ref_known(v___y_1788_, 1);
v___y_1743_ = v___y_1785_;
v___y_1744_ = v___y_1786_;
v___y_1745_ = v___y_1787_;
v___y_1746_ = v_a_1430_;
goto v___jp_1742_;
}
else
{
lean_dec_ref(v___y_1786_);
lean_dec_ref(v___y_1785_);
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
return v___y_1788_;
}
}
v___jp_1789_:
{
lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; 
v___x_1793_ = lean_unsigned_to_nat(0u);
v___x_1794_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1432_);
lean_inc_ref(v___y_1791_);
lean_inc_ref(v___y_1792_);
v___x_1795_ = l_Lake_GitRepo_addRemote(v___y_1792_, v___y_1791_, v_repo_1432_, v___x_1794_);
if (lean_obj_tag(v___x_1795_) == 0)
{
lean_object* v_a_1796_; lean_object* v___x_1797_; uint8_t v___x_1798_; 
v_a_1796_ = lean_ctor_get(v___x_1795_, 1);
lean_inc(v_a_1796_);
lean_dec_ref_known(v___x_1795_, 2);
v___x_1797_ = lean_array_get_size(v_a_1796_);
v___x_1798_ = lean_nat_dec_lt(v___x_1793_, v___x_1797_);
if (v___x_1798_ == 0)
{
lean_dec(v_a_1796_);
v___y_1743_ = v___y_1790_;
v___y_1744_ = v___y_1791_;
v___y_1745_ = v___y_1792_;
v___y_1746_ = v_a_1430_;
goto v___jp_1742_;
}
else
{
lean_object* v___x_1799_; uint8_t v___x_1800_; 
v___x_1799_ = lean_box(0);
v___x_1800_ = lean_nat_dec_le(v___x_1797_, v___x_1797_);
if (v___x_1800_ == 0)
{
if (v___x_1798_ == 0)
{
lean_dec(v_a_1796_);
v___y_1743_ = v___y_1790_;
v___y_1744_ = v___y_1791_;
v___y_1745_ = v___y_1792_;
v___y_1746_ = v_a_1430_;
goto v___jp_1742_;
}
else
{
size_t v___x_1801_; size_t v___x_1802_; lean_object* v___x_1803_; 
v___x_1801_ = ((size_t)0ULL);
v___x_1802_ = lean_usize_of_nat(v___x_1797_);
v___x_1803_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1796_, v___x_1801_, v___x_1802_, v___x_1799_, v_a_1430_);
lean_dec(v_a_1796_);
if (lean_obj_tag(v___x_1803_) == 0)
{
lean_dec_ref_known(v___x_1803_, 1);
v___y_1743_ = v___y_1790_;
v___y_1744_ = v___y_1791_;
v___y_1745_ = v___y_1792_;
v___y_1746_ = v_a_1430_;
goto v___jp_1742_;
}
else
{
v___y_1785_ = v___y_1790_;
v___y_1786_ = v___y_1791_;
v___y_1787_ = v___y_1792_;
v___y_1788_ = v___x_1803_;
goto v___jp_1784_;
}
}
}
else
{
size_t v___x_1804_; size_t v___x_1805_; lean_object* v___x_1806_; 
v___x_1804_ = ((size_t)0ULL);
v___x_1805_ = lean_usize_of_nat(v___x_1797_);
v___x_1806_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1796_, v___x_1804_, v___x_1805_, v___x_1799_, v_a_1430_);
lean_dec(v_a_1796_);
if (lean_obj_tag(v___x_1806_) == 0)
{
lean_dec_ref_known(v___x_1806_, 1);
v___y_1743_ = v___y_1790_;
v___y_1744_ = v___y_1791_;
v___y_1745_ = v___y_1792_;
v___y_1746_ = v_a_1430_;
goto v___jp_1742_;
}
else
{
v___y_1785_ = v___y_1790_;
v___y_1786_ = v___y_1791_;
v___y_1787_ = v___y_1792_;
v___y_1788_ = v___x_1806_;
goto v___jp_1784_;
}
}
}
}
else
{
lean_object* v_a_1807_; lean_object* v___x_1808_; uint8_t v___x_1809_; 
v_a_1807_ = lean_ctor_get(v___x_1795_, 1);
lean_inc(v_a_1807_);
lean_dec_ref_known(v___x_1795_, 2);
v___x_1808_ = lean_array_get_size(v_a_1807_);
v___x_1809_ = lean_nat_dec_lt(v___x_1793_, v___x_1808_);
if (v___x_1809_ == 0)
{
lean_object* v___x_1810_; lean_object* v___x_1811_; 
lean_dec(v_a_1807_);
lean_dec_ref(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
v___x_1810_ = lean_box(0);
v___x_1811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1811_, 0, v___x_1810_);
return v___x_1811_;
}
else
{
lean_object* v___x_1812_; uint8_t v___x_1813_; 
v___x_1812_ = lean_box(0);
v___x_1813_ = lean_nat_dec_le(v___x_1808_, v___x_1808_);
if (v___x_1813_ == 0)
{
if (v___x_1809_ == 0)
{
lean_dec(v_a_1807_);
lean_dec_ref(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
goto v___jp_1461_;
}
else
{
size_t v___x_1814_; size_t v___x_1815_; lean_object* v___x_1816_; 
v___x_1814_ = ((size_t)0ULL);
v___x_1815_ = lean_usize_of_nat(v___x_1808_);
v___x_1816_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1807_, v___x_1814_, v___x_1815_, v___x_1812_, v_a_1430_);
lean_dec(v_a_1807_);
if (lean_obj_tag(v___x_1816_) == 0)
{
lean_dec_ref_known(v___x_1816_, 1);
lean_dec_ref(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
goto v___jp_1461_;
}
else
{
v___y_1785_ = v___y_1790_;
v___y_1786_ = v___y_1791_;
v___y_1787_ = v___y_1792_;
v___y_1788_ = v___x_1816_;
goto v___jp_1784_;
}
}
}
else
{
size_t v___x_1817_; size_t v___x_1818_; lean_object* v___x_1819_; 
v___x_1817_ = ((size_t)0ULL);
v___x_1818_ = lean_usize_of_nat(v___x_1808_);
v___x_1819_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1807_, v___x_1817_, v___x_1818_, v___x_1812_, v_a_1430_);
lean_dec(v_a_1807_);
if (lean_obj_tag(v___x_1819_) == 0)
{
lean_dec_ref_known(v___x_1819_, 1);
lean_dec_ref(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
goto v___jp_1461_;
}
else
{
v___y_1785_ = v___y_1790_;
v___y_1786_ = v___y_1791_;
v___y_1787_ = v___y_1792_;
v___y_1788_ = v___x_1819_;
goto v___jp_1784_;
}
}
}
}
}
v___jp_1820_:
{
if (lean_obj_tag(v___y_1824_) == 0)
{
lean_dec_ref_known(v___y_1824_, 1);
v___y_1790_ = v___y_1821_;
v___y_1791_ = v___y_1822_;
v___y_1792_ = v___y_1823_;
goto v___jp_1789_;
}
else
{
lean_dec_ref(v___y_1822_);
lean_dec_ref(v___y_1821_);
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
return v___y_1824_;
}
}
v___jp_1825_:
{
if (v_a_1827_ == 0)
{
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
goto v___jp_1453_;
}
else
{
lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; uint8_t v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; 
v___x_1828_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff___closed__0));
v___x_1829_ = lean_string_append(v_name_1431_, v___x_1828_);
v___x_1830_ = lean_string_append(v___x_1829_, v_repo_1432_);
lean_dec_ref(v_repo_1432_);
v___x_1831_ = 2;
v___x_1832_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1832_, 0, v___x_1830_);
lean_ctor_set_uint8(v___x_1832_, sizeof(void*)*1, v___x_1831_);
lean_inc_ref(v___y_1826_);
v___x_1833_ = lean_apply_2(v___y_1826_, v___x_1832_, lean_box(0));
goto v___jp_1453_;
}
}
v___jp_1834_:
{
if (v_a_1836_ == 0)
{
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
goto v___jp_1442_;
}
else
{
lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; uint8_t v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1837_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff___closed__0));
v___x_1838_ = lean_string_append(v_name_1431_, v___x_1837_);
v___x_1839_ = lean_string_append(v___x_1838_, v_repo_1432_);
lean_dec_ref(v_repo_1432_);
v___x_1840_ = 2;
v___x_1841_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1841_, 0, v___x_1839_);
lean_ctor_set_uint8(v___x_1841_, sizeof(void*)*1, v___x_1840_);
lean_inc_ref(v___y_1835_);
v___x_1842_ = lean_apply_2(v___y_1835_, v___x_1841_, lean_box(0));
goto v___jp_1442_;
}
}
v___jp_1843_:
{
lean_object* v___x_1848_; uint8_t v___x_1849_; 
v___x_1848_ = lean_array_get_size(v___y_1846_);
v___x_1849_ = lean_nat_dec_lt(v___y_1845_, v___x_1848_);
if (v___x_1849_ == 0)
{
v___y_1826_ = v___y_1844_;
v_a_1827_ = v_val_1847_;
goto v___jp_1825_;
}
else
{
lean_object* v___x_1850_; uint8_t v___x_1851_; 
v___x_1850_ = lean_box(0);
v___x_1851_ = lean_nat_dec_le(v___x_1848_, v___x_1848_);
if (v___x_1851_ == 0)
{
if (v___x_1849_ == 0)
{
v___y_1826_ = v___y_1844_;
v_a_1827_ = v_val_1847_;
goto v___jp_1825_;
}
else
{
size_t v___x_1852_; size_t v___x_1853_; lean_object* v___x_1854_; 
v___x_1852_ = ((size_t)0ULL);
v___x_1853_ = lean_usize_of_nat(v___x_1848_);
v___x_1854_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_1846_, v___x_1852_, v___x_1853_, v___x_1850_, v___y_1844_);
if (lean_obj_tag(v___x_1854_) == 0)
{
lean_dec_ref_known(v___x_1854_, 1);
v___y_1826_ = v___y_1844_;
v_a_1827_ = v_val_1847_;
goto v___jp_1825_;
}
else
{
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
v___y_1457_ = v___x_1854_;
goto v___jp_1456_;
}
}
}
else
{
size_t v___x_1855_; size_t v___x_1856_; lean_object* v___x_1857_; 
v___x_1855_ = ((size_t)0ULL);
v___x_1856_ = lean_usize_of_nat(v___x_1848_);
v___x_1857_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_1846_, v___x_1855_, v___x_1856_, v___x_1850_, v___y_1844_);
if (lean_obj_tag(v___x_1857_) == 0)
{
lean_dec_ref_known(v___x_1857_, 1);
v___y_1826_ = v___y_1844_;
v_a_1827_ = v_val_1847_;
goto v___jp_1825_;
}
else
{
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
v___y_1457_ = v___x_1857_;
goto v___jp_1456_;
}
}
}
}
v___jp_1858_:
{
uint8_t v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; 
lean_inc_ref(v_repo_1432_);
v___x_1862_ = l_Lake_GitRepo_hasNoDiff(v_repo_1432_);
v___x_1863_ = lean_unsigned_to_nat(0u);
v___x_1864_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
if (v___x_1862_ == 0)
{
v___y_1844_ = v___y_1860_;
v___y_1845_ = v___x_1863_;
v___y_1846_ = v___x_1864_;
v_val_1847_ = v___y_1861_;
goto v___jp_1843_;
}
else
{
v___y_1844_ = v___y_1860_;
v___y_1845_ = v___x_1863_;
v___y_1846_ = v___x_1864_;
v_val_1847_ = v___y_1859_;
goto v___jp_1843_;
}
}
v___jp_1865_:
{
if (lean_obj_tag(v___y_1869_) == 0)
{
lean_dec_ref_known(v___y_1869_, 1);
v___y_1859_ = v___y_1866_;
v___y_1860_ = v___y_1867_;
v___y_1861_ = v___y_1868_;
goto v___jp_1858_;
}
else
{
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
return v___y_1869_;
}
}
v___jp_1870_:
{
lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; 
v___x_1874_ = lean_unsigned_to_nat(0u);
v___x_1875_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1432_);
v___x_1876_ = l_Lake_GitRepo_clean(v_repo_1432_, v___x_1875_);
if (lean_obj_tag(v___x_1876_) == 0)
{
lean_object* v_a_1877_; lean_object* v___x_1878_; uint8_t v___x_1879_; 
v_a_1877_ = lean_ctor_get(v___x_1876_, 1);
lean_inc(v_a_1877_);
lean_dec_ref_known(v___x_1876_, 2);
v___x_1878_ = lean_array_get_size(v_a_1877_);
v___x_1879_ = lean_nat_dec_lt(v___x_1874_, v___x_1878_);
if (v___x_1879_ == 0)
{
lean_dec(v_a_1877_);
v___y_1859_ = v___y_1871_;
v___y_1860_ = v___y_1872_;
v___y_1861_ = v___y_1873_;
goto v___jp_1858_;
}
else
{
lean_object* v___x_1880_; uint8_t v___x_1881_; 
v___x_1880_ = lean_box(0);
v___x_1881_ = lean_nat_dec_le(v___x_1878_, v___x_1878_);
if (v___x_1881_ == 0)
{
if (v___x_1879_ == 0)
{
lean_dec(v_a_1877_);
v___y_1859_ = v___y_1871_;
v___y_1860_ = v___y_1872_;
v___y_1861_ = v___y_1873_;
goto v___jp_1858_;
}
else
{
size_t v___x_1882_; size_t v___x_1883_; lean_object* v___x_1884_; 
v___x_1882_ = ((size_t)0ULL);
v___x_1883_ = lean_usize_of_nat(v___x_1878_);
v___x_1884_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1877_, v___x_1882_, v___x_1883_, v___x_1880_, v___y_1872_);
lean_dec(v_a_1877_);
if (lean_obj_tag(v___x_1884_) == 0)
{
lean_dec_ref_known(v___x_1884_, 1);
v___y_1859_ = v___y_1871_;
v___y_1860_ = v___y_1872_;
v___y_1861_ = v___y_1873_;
goto v___jp_1858_;
}
else
{
v___y_1866_ = v___y_1871_;
v___y_1867_ = v___y_1872_;
v___y_1868_ = v___y_1873_;
v___y_1869_ = v___x_1884_;
goto v___jp_1865_;
}
}
}
else
{
size_t v___x_1885_; size_t v___x_1886_; lean_object* v___x_1887_; 
v___x_1885_ = ((size_t)0ULL);
v___x_1886_ = lean_usize_of_nat(v___x_1878_);
v___x_1887_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1877_, v___x_1885_, v___x_1886_, v___x_1880_, v___y_1872_);
lean_dec(v_a_1877_);
if (lean_obj_tag(v___x_1887_) == 0)
{
lean_dec_ref_known(v___x_1887_, 1);
v___y_1859_ = v___y_1871_;
v___y_1860_ = v___y_1872_;
v___y_1861_ = v___y_1873_;
goto v___jp_1858_;
}
else
{
v___y_1866_ = v___y_1871_;
v___y_1867_ = v___y_1872_;
v___y_1868_ = v___y_1873_;
v___y_1869_ = v___x_1887_;
goto v___jp_1865_;
}
}
}
}
else
{
lean_object* v_a_1888_; lean_object* v___x_1889_; uint8_t v___x_1890_; 
v_a_1888_ = lean_ctor_get(v___x_1876_, 1);
lean_inc(v_a_1888_);
lean_dec_ref_known(v___x_1876_, 2);
v___x_1889_ = lean_array_get_size(v_a_1888_);
v___x_1890_ = lean_nat_dec_lt(v___x_1874_, v___x_1889_);
if (v___x_1890_ == 0)
{
lean_object* v___x_1891_; lean_object* v___x_1892_; 
lean_dec(v_a_1888_);
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
v___x_1891_ = lean_box(0);
v___x_1892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1892_, 0, v___x_1891_);
return v___x_1892_;
}
else
{
lean_object* v___x_1893_; uint8_t v___x_1894_; 
v___x_1893_ = lean_box(0);
v___x_1894_ = lean_nat_dec_le(v___x_1889_, v___x_1889_);
if (v___x_1894_ == 0)
{
if (v___x_1890_ == 0)
{
lean_dec(v_a_1888_);
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
goto v___jp_1450_;
}
else
{
size_t v___x_1895_; size_t v___x_1896_; lean_object* v___x_1897_; 
v___x_1895_ = ((size_t)0ULL);
v___x_1896_ = lean_usize_of_nat(v___x_1889_);
v___x_1897_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1888_, v___x_1895_, v___x_1896_, v___x_1893_, v___y_1872_);
lean_dec(v_a_1888_);
if (lean_obj_tag(v___x_1897_) == 0)
{
lean_dec_ref_known(v___x_1897_, 1);
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
goto v___jp_1450_;
}
else
{
v___y_1866_ = v___y_1871_;
v___y_1867_ = v___y_1872_;
v___y_1868_ = v___y_1873_;
v___y_1869_ = v___x_1897_;
goto v___jp_1865_;
}
}
}
else
{
size_t v___x_1898_; size_t v___x_1899_; lean_object* v___x_1900_; 
v___x_1898_ = ((size_t)0ULL);
v___x_1899_ = lean_usize_of_nat(v___x_1889_);
v___x_1900_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1888_, v___x_1898_, v___x_1899_, v___x_1893_, v___y_1872_);
lean_dec(v_a_1888_);
if (lean_obj_tag(v___x_1900_) == 0)
{
lean_dec_ref_known(v___x_1900_, 1);
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
goto v___jp_1450_;
}
else
{
v___y_1866_ = v___y_1871_;
v___y_1867_ = v___y_1872_;
v___y_1868_ = v___y_1873_;
v___y_1869_ = v___x_1900_;
goto v___jp_1865_;
}
}
}
}
}
v___jp_1901_:
{
if (lean_obj_tag(v___y_1905_) == 0)
{
lean_dec_ref_known(v___y_1905_, 1);
v___y_1871_ = v___y_1902_;
v___y_1872_ = v___y_1903_;
v___y_1873_ = v___y_1904_;
goto v___jp_1870_;
}
else
{
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
return v___y_1905_;
}
}
v___jp_1906_:
{
if (lean_obj_tag(v_a_1913_) == 0)
{
v___y_1743_ = v___y_1907_;
v___y_1744_ = v___y_1909_;
v___y_1745_ = v___y_1912_;
v___y_1746_ = v___y_1910_;
goto v___jp_1742_;
}
else
{
lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1954_; 
v_isSharedCheck_1954_ = !lean_is_exclusive(v_a_1913_);
if (v_isSharedCheck_1954_ == 0)
{
lean_object* v_unused_1955_; 
v_unused_1955_ = lean_ctor_get(v_a_1913_, 0);
lean_dec(v_unused_1955_);
v___x_1915_ = v_a_1913_;
v_isShared_1916_ = v_isSharedCheck_1954_;
goto v_resetjp_1914_;
}
else
{
lean_dec(v_a_1913_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1954_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
if (v___y_1911_ == 0)
{
lean_del_object(v___x_1915_);
v___y_1743_ = v___y_1907_;
v___y_1744_ = v___y_1909_;
v___y_1745_ = v___y_1912_;
v___y_1746_ = v___y_1910_;
goto v___jp_1742_;
}
else
{
lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; uint8_t v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; 
lean_dec_ref(v___y_1909_);
v___x_1917_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__0));
lean_inc_ref(v_name_1431_);
v___x_1918_ = lean_string_append(v_name_1431_, v___x_1917_);
v___x_1919_ = lean_string_append(v___x_1918_, v___y_1907_);
v___x_1920_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__1));
v___x_1921_ = lean_string_append(v___x_1919_, v___x_1920_);
v___x_1922_ = 1;
v___x_1923_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1923_, 0, v___x_1921_);
lean_ctor_set_uint8(v___x_1923_, sizeof(void*)*1, v___x_1922_);
lean_inc_ref(v___y_1910_);
v___x_1924_ = lean_apply_2(v___y_1910_, v___x_1923_, lean_box(0));
v___x_1925_ = lean_unsigned_to_nat(0u);
v___x_1926_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1432_);
v___x_1927_ = l_Lake_GitRepo_checkoutDetach(v___y_1907_, v_repo_1432_, v___x_1926_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_object* v_a_1928_; lean_object* v___x_1929_; uint8_t v___x_1930_; 
lean_del_object(v___x_1915_);
v_a_1928_ = lean_ctor_get(v___x_1927_, 1);
lean_inc(v_a_1928_);
lean_dec_ref_known(v___x_1927_, 2);
v___x_1929_ = lean_array_get_size(v_a_1928_);
v___x_1930_ = lean_nat_dec_lt(v___x_1925_, v___x_1929_);
if (v___x_1930_ == 0)
{
lean_dec(v_a_1928_);
v___y_1871_ = v___y_1908_;
v___y_1872_ = v___y_1910_;
v___y_1873_ = v___y_1911_;
goto v___jp_1870_;
}
else
{
lean_object* v___x_1931_; uint8_t v___x_1932_; 
v___x_1931_ = lean_box(0);
v___x_1932_ = lean_nat_dec_le(v___x_1929_, v___x_1929_);
if (v___x_1932_ == 0)
{
if (v___x_1930_ == 0)
{
lean_dec(v_a_1928_);
v___y_1871_ = v___y_1908_;
v___y_1872_ = v___y_1910_;
v___y_1873_ = v___y_1911_;
goto v___jp_1870_;
}
else
{
size_t v___x_1933_; size_t v___x_1934_; lean_object* v___x_1935_; 
v___x_1933_ = ((size_t)0ULL);
v___x_1934_ = lean_usize_of_nat(v___x_1929_);
v___x_1935_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1928_, v___x_1933_, v___x_1934_, v___x_1931_, v___y_1910_);
lean_dec(v_a_1928_);
if (lean_obj_tag(v___x_1935_) == 0)
{
lean_dec_ref_known(v___x_1935_, 1);
v___y_1871_ = v___y_1908_;
v___y_1872_ = v___y_1910_;
v___y_1873_ = v___y_1911_;
goto v___jp_1870_;
}
else
{
v___y_1902_ = v___y_1908_;
v___y_1903_ = v___y_1910_;
v___y_1904_ = v___y_1911_;
v___y_1905_ = v___x_1935_;
goto v___jp_1901_;
}
}
}
else
{
size_t v___x_1936_; size_t v___x_1937_; lean_object* v___x_1938_; 
v___x_1936_ = ((size_t)0ULL);
v___x_1937_ = lean_usize_of_nat(v___x_1929_);
v___x_1938_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1928_, v___x_1936_, v___x_1937_, v___x_1931_, v___y_1910_);
lean_dec(v_a_1928_);
if (lean_obj_tag(v___x_1938_) == 0)
{
lean_dec_ref_known(v___x_1938_, 1);
v___y_1871_ = v___y_1908_;
v___y_1872_ = v___y_1910_;
v___y_1873_ = v___y_1911_;
goto v___jp_1870_;
}
else
{
v___y_1902_ = v___y_1908_;
v___y_1903_ = v___y_1910_;
v___y_1904_ = v___y_1911_;
v___y_1905_ = v___x_1938_;
goto v___jp_1901_;
}
}
}
}
else
{
lean_object* v_a_1939_; lean_object* v___x_1940_; uint8_t v___x_1941_; 
v_a_1939_ = lean_ctor_get(v___x_1927_, 1);
lean_inc(v_a_1939_);
lean_dec_ref_known(v___x_1927_, 2);
v___x_1940_ = lean_array_get_size(v_a_1939_);
v___x_1941_ = lean_nat_dec_lt(v___x_1925_, v___x_1940_);
if (v___x_1941_ == 0)
{
lean_object* v___x_1942_; lean_object* v___x_1944_; 
lean_dec(v_a_1939_);
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
v___x_1942_ = lean_box(0);
if (v_isShared_1916_ == 0)
{
lean_ctor_set(v___x_1915_, 0, v___x_1942_);
v___x_1944_ = v___x_1915_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v___x_1942_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
return v___x_1944_;
}
}
else
{
lean_object* v___x_1946_; uint8_t v___x_1947_; 
lean_del_object(v___x_1915_);
v___x_1946_ = lean_box(0);
v___x_1947_ = lean_nat_dec_le(v___x_1940_, v___x_1940_);
if (v___x_1947_ == 0)
{
if (v___x_1941_ == 0)
{
lean_dec(v_a_1939_);
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
goto v___jp_1447_;
}
else
{
size_t v___x_1948_; size_t v___x_1949_; lean_object* v___x_1950_; 
v___x_1948_ = ((size_t)0ULL);
v___x_1949_ = lean_usize_of_nat(v___x_1940_);
v___x_1950_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1939_, v___x_1948_, v___x_1949_, v___x_1946_, v___y_1910_);
lean_dec(v_a_1939_);
if (lean_obj_tag(v___x_1950_) == 0)
{
lean_dec_ref_known(v___x_1950_, 1);
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
goto v___jp_1447_;
}
else
{
v___y_1902_ = v___y_1908_;
v___y_1903_ = v___y_1910_;
v___y_1904_ = v___y_1911_;
v___y_1905_ = v___x_1950_;
goto v___jp_1901_;
}
}
}
else
{
size_t v___x_1951_; size_t v___x_1952_; lean_object* v___x_1953_; 
v___x_1951_ = ((size_t)0ULL);
v___x_1952_ = lean_usize_of_nat(v___x_1940_);
v___x_1953_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1939_, v___x_1951_, v___x_1952_, v___x_1946_, v___y_1910_);
lean_dec(v_a_1939_);
if (lean_obj_tag(v___x_1953_) == 0)
{
lean_dec_ref_known(v___x_1953_, 1);
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
goto v___jp_1447_;
}
else
{
v___y_1902_ = v___y_1908_;
v___y_1903_ = v___y_1910_;
v___y_1904_ = v___y_1911_;
v___y_1905_ = v___x_1953_;
goto v___jp_1901_;
}
}
}
}
}
}
}
}
v___jp_1956_:
{
lean_object* v___x_1961_; uint8_t v___x_1962_; 
v___x_1961_ = lean_array_get_size(v___y_1959_);
v___x_1962_ = lean_nat_dec_lt(v___y_1957_, v___x_1961_);
if (v___x_1962_ == 0)
{
v___y_1835_ = v___y_1958_;
v_a_1836_ = v_val_1960_;
goto v___jp_1834_;
}
else
{
lean_object* v___x_1963_; uint8_t v___x_1964_; 
v___x_1963_ = lean_box(0);
v___x_1964_ = lean_nat_dec_le(v___x_1961_, v___x_1961_);
if (v___x_1964_ == 0)
{
if (v___x_1962_ == 0)
{
v___y_1835_ = v___y_1958_;
v_a_1836_ = v_val_1960_;
goto v___jp_1834_;
}
else
{
size_t v___x_1965_; size_t v___x_1966_; lean_object* v___x_1967_; 
v___x_1965_ = ((size_t)0ULL);
v___x_1966_ = lean_usize_of_nat(v___x_1961_);
v___x_1967_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_1959_, v___x_1965_, v___x_1966_, v___x_1963_, v___y_1958_);
if (lean_obj_tag(v___x_1967_) == 0)
{
lean_dec_ref_known(v___x_1967_, 1);
v___y_1835_ = v___y_1958_;
v_a_1836_ = v_val_1960_;
goto v___jp_1834_;
}
else
{
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
v___y_1446_ = v___x_1967_;
goto v___jp_1445_;
}
}
}
else
{
size_t v___x_1968_; size_t v___x_1969_; lean_object* v___x_1970_; 
v___x_1968_ = ((size_t)0ULL);
v___x_1969_ = lean_usize_of_nat(v___x_1961_);
v___x_1970_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_1959_, v___x_1968_, v___x_1969_, v___x_1963_, v___y_1958_);
if (lean_obj_tag(v___x_1970_) == 0)
{
lean_dec_ref_known(v___x_1970_, 1);
v___y_1835_ = v___y_1958_;
v_a_1836_ = v_val_1960_;
goto v___jp_1834_;
}
else
{
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
v___y_1446_ = v___x_1970_;
goto v___jp_1445_;
}
}
}
}
v___jp_1971_:
{
lean_object* v___x_1978_; lean_object* v___x_1979_; uint8_t v___x_1980_; 
v___x_1978_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
lean_inc_ref(v___y_1972_);
v___x_1979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1979_, 0, v___y_1972_);
v___x_1980_ = l_Option_instDecidableEq___redArg(v___x_1978_, v_a_1977_, v___x_1979_);
if (v___x_1980_ == 0)
{
uint8_t v___x_1981_; 
v___x_1981_ = l_Lake_GitRev_isFullSha1(v___y_1972_);
if (v___x_1981_ == 0)
{
v___y_1743_ = v___y_1972_;
v___y_1744_ = v___y_1974_;
v___y_1745_ = v___y_1976_;
v___y_1746_ = v___y_1975_;
goto v___jp_1742_;
}
else
{
lean_object* v___x_1982_; lean_object* v___x_1983_; uint8_t v___x_1984_; 
lean_inc_ref(v_repo_1432_);
lean_inc_ref(v___y_1972_);
v___x_1982_ = l_Lake_GitRepo_findCommit_x3f(v___y_1972_, v_repo_1432_);
v___x_1983_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_1984_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_1984_ == 0)
{
v___y_1907_ = v___y_1972_;
v___y_1908_ = v___x_1980_;
v___y_1909_ = v___y_1974_;
v___y_1910_ = v___y_1975_;
v___y_1911_ = v___x_1981_;
v___y_1912_ = v___y_1976_;
v_a_1913_ = v___x_1982_;
goto v___jp_1906_;
}
else
{
lean_object* v___x_1985_; uint8_t v___x_1986_; 
v___x_1985_ = lean_box(0);
v___x_1986_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
if (v___x_1986_ == 0)
{
if (v___x_1984_ == 0)
{
v___y_1907_ = v___y_1972_;
v___y_1908_ = v___x_1980_;
v___y_1909_ = v___y_1974_;
v___y_1910_ = v___y_1975_;
v___y_1911_ = v___x_1981_;
v___y_1912_ = v___y_1976_;
v_a_1913_ = v___x_1982_;
goto v___jp_1906_;
}
else
{
size_t v___x_1987_; size_t v___x_1988_; lean_object* v___x_1989_; 
v___x_1987_ = ((size_t)0ULL);
v___x_1988_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8);
v___x_1989_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_1983_, v___x_1987_, v___x_1988_, v___x_1985_, v___y_1975_);
if (lean_obj_tag(v___x_1989_) == 0)
{
lean_dec_ref_known(v___x_1989_, 1);
v___y_1907_ = v___y_1972_;
v___y_1908_ = v___x_1980_;
v___y_1909_ = v___y_1974_;
v___y_1910_ = v___y_1975_;
v___y_1911_ = v___x_1981_;
v___y_1912_ = v___y_1976_;
v_a_1913_ = v___x_1982_;
goto v___jp_1906_;
}
else
{
lean_dec(v___x_1982_);
lean_dec_ref(v___y_1974_);
lean_dec_ref(v___y_1972_);
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
return v___x_1989_;
}
}
}
else
{
size_t v___x_1990_; size_t v___x_1991_; lean_object* v___x_1992_; 
v___x_1990_ = ((size_t)0ULL);
v___x_1991_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8);
v___x_1992_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_1983_, v___x_1990_, v___x_1991_, v___x_1985_, v___y_1975_);
if (lean_obj_tag(v___x_1992_) == 0)
{
lean_dec_ref_known(v___x_1992_, 1);
v___y_1907_ = v___y_1972_;
v___y_1908_ = v___x_1980_;
v___y_1909_ = v___y_1974_;
v___y_1910_ = v___y_1975_;
v___y_1911_ = v___x_1981_;
v___y_1912_ = v___y_1976_;
v_a_1913_ = v___x_1982_;
goto v___jp_1906_;
}
else
{
lean_dec(v___x_1982_);
lean_dec_ref(v___y_1974_);
lean_dec_ref(v___y_1972_);
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
return v___x_1992_;
}
}
}
}
}
else
{
uint8_t v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; 
lean_dec_ref(v___y_1974_);
lean_dec_ref(v___y_1972_);
lean_inc_ref(v_repo_1432_);
v___x_1993_ = l_Lake_GitRepo_hasNoDiff(v_repo_1432_);
v___x_1994_ = lean_unsigned_to_nat(0u);
v___x_1995_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
if (v___x_1993_ == 0)
{
v___y_1957_ = v___x_1994_;
v___y_1958_ = v___y_1975_;
v___y_1959_ = v___x_1995_;
v_val_1960_ = v___y_1973_;
goto v___jp_1956_;
}
else
{
uint8_t v___x_1996_; 
v___x_1996_ = 0;
v___y_1957_ = v___x_1994_;
v___y_1958_ = v___y_1975_;
v___y_1959_ = v___x_1995_;
v_val_1960_ = v___x_1996_;
goto v___jp_1956_;
}
}
}
v___jp_1997_:
{
lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; uint8_t v___x_2006_; 
v___x_2003_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__0));
lean_inc_ref(v_repo_1432_);
v___x_2004_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_2003_, v_repo_1432_);
v___x_2005_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_2006_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_2006_ == 0)
{
v___y_1972_ = v___y_1998_;
v___y_1973_ = v___y_2000_;
v___y_1974_ = v___y_1999_;
v___y_1975_ = v___y_2002_;
v___y_1976_ = v___y_2001_;
v_a_1977_ = v___x_2004_;
goto v___jp_1971_;
}
else
{
lean_object* v___x_2007_; uint8_t v___x_2008_; 
v___x_2007_ = lean_box(0);
v___x_2008_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
if (v___x_2008_ == 0)
{
if (v___x_2006_ == 0)
{
v___y_1972_ = v___y_1998_;
v___y_1973_ = v___y_2000_;
v___y_1974_ = v___y_1999_;
v___y_1975_ = v___y_2002_;
v___y_1976_ = v___y_2001_;
v_a_1977_ = v___x_2004_;
goto v___jp_1971_;
}
else
{
size_t v___x_2009_; size_t v___x_2010_; lean_object* v___x_2011_; 
v___x_2009_ = ((size_t)0ULL);
v___x_2010_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8);
v___x_2011_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_2005_, v___x_2009_, v___x_2010_, v___x_2007_, v___y_2002_);
if (lean_obj_tag(v___x_2011_) == 0)
{
lean_dec_ref_known(v___x_2011_, 1);
v___y_1972_ = v___y_1998_;
v___y_1973_ = v___y_2000_;
v___y_1974_ = v___y_1999_;
v___y_1975_ = v___y_2002_;
v___y_1976_ = v___y_2001_;
v_a_1977_ = v___x_2004_;
goto v___jp_1971_;
}
else
{
lean_dec(v___x_2004_);
lean_dec_ref(v___y_1999_);
lean_dec_ref(v___y_1998_);
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
return v___x_2011_;
}
}
}
else
{
size_t v___x_2012_; size_t v___x_2013_; lean_object* v___x_2014_; 
v___x_2012_ = ((size_t)0ULL);
v___x_2013_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8);
v___x_2014_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_2005_, v___x_2012_, v___x_2013_, v___x_2007_, v___y_2002_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_dec_ref_known(v___x_2014_, 1);
v___y_1972_ = v___y_1998_;
v___y_1973_ = v___y_2000_;
v___y_1974_ = v___y_1999_;
v___y_1975_ = v___y_2002_;
v___y_1976_ = v___y_2001_;
v_a_1977_ = v___x_2004_;
goto v___jp_1971_;
}
else
{
lean_dec(v___x_2004_);
lean_dec_ref(v___y_1999_);
lean_dec_ref(v___y_1998_);
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
return v___x_2014_;
}
}
}
}
v___jp_2015_:
{
if (lean_obj_tag(v___y_2020_) == 0)
{
lean_dec_ref_known(v___y_2020_, 1);
v___y_1998_ = v___y_2016_;
v___y_1999_ = v___y_2018_;
v___y_2000_ = v___y_2017_;
v___y_2001_ = v___y_2019_;
v___y_2002_ = v_a_1430_;
goto v___jp_1997_;
}
else
{
lean_dec_ref(v___y_2018_);
lean_dec_ref(v___y_2016_);
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
return v___y_2020_;
}
}
v___jp_2021_:
{
if (lean_obj_tag(v___y_2026_) == 0)
{
lean_dec_ref_known(v___y_2026_, 1);
v___y_1998_ = v___y_2022_;
v___y_1999_ = v___y_2024_;
v___y_2000_ = v___y_2023_;
v___y_2001_ = v___y_2025_;
v___y_2002_ = v_a_1430_;
goto v___jp_1997_;
}
else
{
lean_dec_ref(v___y_2024_);
lean_dec_ref(v___y_2022_);
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
return v___y_2026_;
}
}
v___jp_2027_:
{
if (lean_obj_tag(v_a_2032_) == 1)
{
lean_object* v_val_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2076_; 
v_val_2033_ = lean_ctor_get(v_a_2032_, 0);
v_isSharedCheck_2076_ = !lean_is_exclusive(v_a_2032_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2035_ = v_a_2032_;
v_isShared_2036_ = v_isSharedCheck_2076_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_val_2033_);
lean_dec(v_a_2032_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2076_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
uint8_t v___x_2037_; 
v___x_2037_ = lean_string_dec_eq(v_val_2033_, v___y_2030_);
if (v___x_2037_ == 0)
{
lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; uint8_t v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; 
v___x_2038_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__5));
lean_inc_ref(v_name_1431_);
v___x_2039_ = lean_string_append(v_name_1431_, v___x_2038_);
v___x_2040_ = lean_string_append(v___x_2039_, v_val_2033_);
lean_dec(v_val_2033_);
v___x_2041_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__6));
v___x_2042_ = lean_string_append(v___x_2040_, v___x_2041_);
v___x_2043_ = lean_string_append(v___x_2042_, v___y_2030_);
v___x_2044_ = 1;
v___x_2045_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2045_, 0, v___x_2043_);
lean_ctor_set_uint8(v___x_2045_, sizeof(void*)*1, v___x_2044_);
lean_inc_ref(v_a_1430_);
v___x_2046_ = lean_apply_2(v_a_1430_, v___x_2045_, lean_box(0));
v___x_2047_ = lean_unsigned_to_nat(0u);
v___x_2048_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1432_);
lean_inc_ref(v___y_2030_);
lean_inc_ref(v___y_2031_);
v___x_2049_ = l_Lake_GitRepo_setRemoteUrl(v___y_2031_, v___y_2030_, v_repo_1432_, v___x_2048_);
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_object* v_a_2050_; lean_object* v___x_2051_; uint8_t v___x_2052_; 
lean_del_object(v___x_2035_);
v_a_2050_ = lean_ctor_get(v___x_2049_, 1);
lean_inc(v_a_2050_);
lean_dec_ref_known(v___x_2049_, 2);
v___x_2051_ = lean_array_get_size(v_a_2050_);
v___x_2052_ = lean_nat_dec_lt(v___x_2047_, v___x_2051_);
if (v___x_2052_ == 0)
{
lean_dec(v_a_2050_);
v___y_1998_ = v___y_2028_;
v___y_1999_ = v___y_2030_;
v___y_2000_ = v___y_2029_;
v___y_2001_ = v___y_2031_;
v___y_2002_ = v_a_1430_;
goto v___jp_1997_;
}
else
{
lean_object* v___x_2053_; uint8_t v___x_2054_; 
v___x_2053_ = lean_box(0);
v___x_2054_ = lean_nat_dec_le(v___x_2051_, v___x_2051_);
if (v___x_2054_ == 0)
{
if (v___x_2052_ == 0)
{
lean_dec(v_a_2050_);
v___y_1998_ = v___y_2028_;
v___y_1999_ = v___y_2030_;
v___y_2000_ = v___y_2029_;
v___y_2001_ = v___y_2031_;
v___y_2002_ = v_a_1430_;
goto v___jp_1997_;
}
else
{
size_t v___x_2055_; size_t v___x_2056_; lean_object* v___x_2057_; 
v___x_2055_ = ((size_t)0ULL);
v___x_2056_ = lean_usize_of_nat(v___x_2051_);
v___x_2057_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_2050_, v___x_2055_, v___x_2056_, v___x_2053_, v_a_1430_);
lean_dec(v_a_2050_);
if (lean_obj_tag(v___x_2057_) == 0)
{
lean_dec_ref_known(v___x_2057_, 1);
v___y_1998_ = v___y_2028_;
v___y_1999_ = v___y_2030_;
v___y_2000_ = v___y_2029_;
v___y_2001_ = v___y_2031_;
v___y_2002_ = v_a_1430_;
goto v___jp_1997_;
}
else
{
v___y_2016_ = v___y_2028_;
v___y_2017_ = v___y_2029_;
v___y_2018_ = v___y_2030_;
v___y_2019_ = v___y_2031_;
v___y_2020_ = v___x_2057_;
goto v___jp_2015_;
}
}
}
else
{
size_t v___x_2058_; size_t v___x_2059_; lean_object* v___x_2060_; 
v___x_2058_ = ((size_t)0ULL);
v___x_2059_ = lean_usize_of_nat(v___x_2051_);
v___x_2060_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_2050_, v___x_2058_, v___x_2059_, v___x_2053_, v_a_1430_);
lean_dec(v_a_2050_);
if (lean_obj_tag(v___x_2060_) == 0)
{
lean_dec_ref_known(v___x_2060_, 1);
v___y_1998_ = v___y_2028_;
v___y_1999_ = v___y_2030_;
v___y_2000_ = v___y_2029_;
v___y_2001_ = v___y_2031_;
v___y_2002_ = v_a_1430_;
goto v___jp_1997_;
}
else
{
v___y_2016_ = v___y_2028_;
v___y_2017_ = v___y_2029_;
v___y_2018_ = v___y_2030_;
v___y_2019_ = v___y_2031_;
v___y_2020_ = v___x_2060_;
goto v___jp_2015_;
}
}
}
}
else
{
lean_object* v_a_2061_; lean_object* v___x_2062_; uint8_t v___x_2063_; 
v_a_2061_ = lean_ctor_get(v___x_2049_, 1);
lean_inc(v_a_2061_);
lean_dec_ref_known(v___x_2049_, 2);
v___x_2062_ = lean_array_get_size(v_a_2061_);
v___x_2063_ = lean_nat_dec_lt(v___x_2047_, v___x_2062_);
if (v___x_2063_ == 0)
{
lean_object* v___x_2064_; lean_object* v___x_2066_; 
lean_dec(v_a_2061_);
lean_dec_ref(v___y_2030_);
lean_dec_ref(v___y_2028_);
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
v___x_2064_ = lean_box(0);
if (v_isShared_2036_ == 0)
{
lean_ctor_set(v___x_2035_, 0, v___x_2064_);
v___x_2066_ = v___x_2035_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v___x_2064_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
}
}
else
{
lean_object* v___x_2068_; uint8_t v___x_2069_; 
lean_del_object(v___x_2035_);
v___x_2068_ = lean_box(0);
v___x_2069_ = lean_nat_dec_le(v___x_2062_, v___x_2062_);
if (v___x_2069_ == 0)
{
if (v___x_2063_ == 0)
{
lean_dec(v_a_2061_);
lean_dec_ref(v___y_2030_);
lean_dec_ref(v___y_2028_);
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
goto v___jp_1439_;
}
else
{
size_t v___x_2070_; size_t v___x_2071_; lean_object* v___x_2072_; 
v___x_2070_ = ((size_t)0ULL);
v___x_2071_ = lean_usize_of_nat(v___x_2062_);
v___x_2072_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_2061_, v___x_2070_, v___x_2071_, v___x_2068_, v_a_1430_);
lean_dec(v_a_2061_);
if (lean_obj_tag(v___x_2072_) == 0)
{
lean_dec_ref_known(v___x_2072_, 1);
lean_dec_ref(v___y_2030_);
lean_dec_ref(v___y_2028_);
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
goto v___jp_1439_;
}
else
{
v___y_2016_ = v___y_2028_;
v___y_2017_ = v___y_2029_;
v___y_2018_ = v___y_2030_;
v___y_2019_ = v___y_2031_;
v___y_2020_ = v___x_2072_;
goto v___jp_2015_;
}
}
}
else
{
size_t v___x_2073_; size_t v___x_2074_; lean_object* v___x_2075_; 
v___x_2073_ = ((size_t)0ULL);
v___x_2074_ = lean_usize_of_nat(v___x_2062_);
v___x_2075_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_2061_, v___x_2073_, v___x_2074_, v___x_2068_, v_a_1430_);
lean_dec(v_a_2061_);
if (lean_obj_tag(v___x_2075_) == 0)
{
lean_dec_ref_known(v___x_2075_, 1);
lean_dec_ref(v___y_2030_);
lean_dec_ref(v___y_2028_);
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
goto v___jp_1439_;
}
else
{
v___y_2016_ = v___y_2028_;
v___y_2017_ = v___y_2029_;
v___y_2018_ = v___y_2030_;
v___y_2019_ = v___y_2031_;
v___y_2020_ = v___x_2075_;
goto v___jp_2015_;
}
}
}
}
}
else
{
lean_del_object(v___x_2035_);
lean_dec(v_val_2033_);
v___y_1998_ = v___y_2028_;
v___y_1999_ = v___y_2030_;
v___y_2000_ = v___y_2029_;
v___y_2001_ = v___y_2031_;
v___y_2002_ = v_a_1430_;
goto v___jp_1997_;
}
}
}
else
{
lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; 
lean_dec(v_a_2032_);
v___x_2077_ = lean_unsigned_to_nat(0u);
v___x_2078_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1432_);
lean_inc_ref(v___y_2030_);
lean_inc_ref(v___y_2031_);
v___x_2079_ = l_Lake_GitRepo_addRemote(v___y_2031_, v___y_2030_, v_repo_1432_, v___x_2078_);
if (lean_obj_tag(v___x_2079_) == 0)
{
lean_object* v_a_2080_; lean_object* v___x_2081_; uint8_t v___x_2082_; 
v_a_2080_ = lean_ctor_get(v___x_2079_, 1);
lean_inc(v_a_2080_);
lean_dec_ref_known(v___x_2079_, 2);
v___x_2081_ = lean_array_get_size(v_a_2080_);
v___x_2082_ = lean_nat_dec_lt(v___x_2077_, v___x_2081_);
if (v___x_2082_ == 0)
{
lean_dec(v_a_2080_);
v___y_1998_ = v___y_2028_;
v___y_1999_ = v___y_2030_;
v___y_2000_ = v___y_2029_;
v___y_2001_ = v___y_2031_;
v___y_2002_ = v_a_1430_;
goto v___jp_1997_;
}
else
{
lean_object* v___x_2083_; uint8_t v___x_2084_; 
v___x_2083_ = lean_box(0);
v___x_2084_ = lean_nat_dec_le(v___x_2081_, v___x_2081_);
if (v___x_2084_ == 0)
{
if (v___x_2082_ == 0)
{
lean_dec(v_a_2080_);
v___y_1998_ = v___y_2028_;
v___y_1999_ = v___y_2030_;
v___y_2000_ = v___y_2029_;
v___y_2001_ = v___y_2031_;
v___y_2002_ = v_a_1430_;
goto v___jp_1997_;
}
else
{
size_t v___x_2085_; size_t v___x_2086_; lean_object* v___x_2087_; 
v___x_2085_ = ((size_t)0ULL);
v___x_2086_ = lean_usize_of_nat(v___x_2081_);
v___x_2087_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_2080_, v___x_2085_, v___x_2086_, v___x_2083_, v_a_1430_);
lean_dec(v_a_2080_);
if (lean_obj_tag(v___x_2087_) == 0)
{
lean_dec_ref_known(v___x_2087_, 1);
v___y_1998_ = v___y_2028_;
v___y_1999_ = v___y_2030_;
v___y_2000_ = v___y_2029_;
v___y_2001_ = v___y_2031_;
v___y_2002_ = v_a_1430_;
goto v___jp_1997_;
}
else
{
v___y_2022_ = v___y_2028_;
v___y_2023_ = v___y_2029_;
v___y_2024_ = v___y_2030_;
v___y_2025_ = v___y_2031_;
v___y_2026_ = v___x_2087_;
goto v___jp_2021_;
}
}
}
else
{
size_t v___x_2088_; size_t v___x_2089_; lean_object* v___x_2090_; 
v___x_2088_ = ((size_t)0ULL);
v___x_2089_ = lean_usize_of_nat(v___x_2081_);
v___x_2090_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_2080_, v___x_2088_, v___x_2089_, v___x_2083_, v_a_1430_);
lean_dec(v_a_2080_);
if (lean_obj_tag(v___x_2090_) == 0)
{
lean_dec_ref_known(v___x_2090_, 1);
v___y_1998_ = v___y_2028_;
v___y_1999_ = v___y_2030_;
v___y_2000_ = v___y_2029_;
v___y_2001_ = v___y_2031_;
v___y_2002_ = v_a_1430_;
goto v___jp_1997_;
}
else
{
v___y_2022_ = v___y_2028_;
v___y_2023_ = v___y_2029_;
v___y_2024_ = v___y_2030_;
v___y_2025_ = v___y_2031_;
v___y_2026_ = v___x_2090_;
goto v___jp_2021_;
}
}
}
}
else
{
lean_object* v_a_2091_; lean_object* v___x_2092_; uint8_t v___x_2093_; 
v_a_2091_ = lean_ctor_get(v___x_2079_, 1);
lean_inc(v_a_2091_);
lean_dec_ref_known(v___x_2079_, 2);
v___x_2092_ = lean_array_get_size(v_a_2091_);
v___x_2093_ = lean_nat_dec_lt(v___x_2077_, v___x_2092_);
if (v___x_2093_ == 0)
{
lean_object* v___x_2094_; lean_object* v___x_2095_; 
lean_dec(v_a_2091_);
lean_dec_ref(v___y_2030_);
lean_dec_ref(v___y_2028_);
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
v___x_2094_ = lean_box(0);
v___x_2095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2095_, 0, v___x_2094_);
return v___x_2095_;
}
else
{
lean_object* v___x_2096_; uint8_t v___x_2097_; 
v___x_2096_ = lean_box(0);
v___x_2097_ = lean_nat_dec_le(v___x_2092_, v___x_2092_);
if (v___x_2097_ == 0)
{
if (v___x_2093_ == 0)
{
lean_dec(v_a_2091_);
lean_dec_ref(v___y_2030_);
lean_dec_ref(v___y_2028_);
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
goto v___jp_1436_;
}
else
{
size_t v___x_2098_; size_t v___x_2099_; lean_object* v___x_2100_; 
v___x_2098_ = ((size_t)0ULL);
v___x_2099_ = lean_usize_of_nat(v___x_2092_);
v___x_2100_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_2091_, v___x_2098_, v___x_2099_, v___x_2096_, v_a_1430_);
lean_dec(v_a_2091_);
if (lean_obj_tag(v___x_2100_) == 0)
{
lean_dec_ref_known(v___x_2100_, 1);
lean_dec_ref(v___y_2030_);
lean_dec_ref(v___y_2028_);
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
goto v___jp_1436_;
}
else
{
v___y_2022_ = v___y_2028_;
v___y_2023_ = v___y_2029_;
v___y_2024_ = v___y_2030_;
v___y_2025_ = v___y_2031_;
v___y_2026_ = v___x_2100_;
goto v___jp_2021_;
}
}
}
else
{
size_t v___x_2101_; size_t v___x_2102_; lean_object* v___x_2103_; 
v___x_2101_ = ((size_t)0ULL);
v___x_2102_ = lean_usize_of_nat(v___x_2092_);
v___x_2103_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_2091_, v___x_2101_, v___x_2102_, v___x_2096_, v_a_1430_);
lean_dec(v_a_2091_);
if (lean_obj_tag(v___x_2103_) == 0)
{
lean_dec_ref_known(v___x_2103_, 1);
lean_dec_ref(v___y_2030_);
lean_dec_ref(v___y_2028_);
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
goto v___jp_1436_;
}
else
{
v___y_2022_ = v___y_2028_;
v___y_2023_ = v___y_2029_;
v___y_2024_ = v___y_2030_;
v___y_2025_ = v___y_2031_;
v___y_2026_ = v___x_2103_;
goto v___jp_2021_;
}
}
}
}
}
}
v___jp_2104_:
{
if (v_a_2108_ == 0)
{
lean_object* v___x_2109_; lean_object* v___x_2110_; uint8_t v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; 
v___x_2109_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__7));
lean_inc_ref(v_name_1431_);
v___x_2110_ = lean_string_append(v_name_1431_, v___x_2109_);
v___x_2111_ = 1;
v___x_2112_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2112_, 0, v___x_2110_);
lean_ctor_set_uint8(v___x_2112_, sizeof(void*)*1, v___x_2111_);
lean_inc_ref(v_a_1430_);
v___x_2113_ = lean_apply_2(v_a_1430_, v___x_2112_, lean_box(0));
lean_inc_ref(v_repo_1432_);
v___x_2114_ = l_IO_FS_createDirAll(v_repo_1432_);
if (lean_obj_tag(v___x_2114_) == 0)
{
lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2147_; 
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2114_);
if (v_isSharedCheck_2147_ == 0)
{
lean_object* v_unused_2148_; 
v_unused_2148_ = lean_ctor_get(v___x_2114_, 0);
lean_dec(v_unused_2148_);
v___x_2116_ = v___x_2114_;
v_isShared_2117_ = v_isSharedCheck_2147_;
goto v_resetjp_2115_;
}
else
{
lean_dec(v___x_2114_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2147_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2118_ = lean_unsigned_to_nat(0u);
v___x_2119_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1432_);
v___x_2120_ = l_Lake_GitRepo_quietInit(v_repo_1432_, v___x_2119_);
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_object* v_a_2121_; lean_object* v___x_2122_; uint8_t v___x_2123_; 
lean_del_object(v___x_2116_);
v_a_2121_ = lean_ctor_get(v___x_2120_, 1);
lean_inc(v_a_2121_);
lean_dec_ref_known(v___x_2120_, 2);
v___x_2122_ = lean_array_get_size(v_a_2121_);
v___x_2123_ = lean_nat_dec_lt(v___x_2118_, v___x_2122_);
if (v___x_2123_ == 0)
{
lean_dec(v_a_2121_);
v___y_1790_ = v___y_2105_;
v___y_1791_ = v___y_2106_;
v___y_1792_ = v___y_2107_;
goto v___jp_1789_;
}
else
{
lean_object* v___x_2124_; uint8_t v___x_2125_; 
v___x_2124_ = lean_box(0);
v___x_2125_ = lean_nat_dec_le(v___x_2122_, v___x_2122_);
if (v___x_2125_ == 0)
{
if (v___x_2123_ == 0)
{
lean_dec(v_a_2121_);
v___y_1790_ = v___y_2105_;
v___y_1791_ = v___y_2106_;
v___y_1792_ = v___y_2107_;
goto v___jp_1789_;
}
else
{
size_t v___x_2126_; size_t v___x_2127_; lean_object* v___x_2128_; 
v___x_2126_ = ((size_t)0ULL);
v___x_2127_ = lean_usize_of_nat(v___x_2122_);
v___x_2128_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_2121_, v___x_2126_, v___x_2127_, v___x_2124_, v_a_1430_);
lean_dec(v_a_2121_);
if (lean_obj_tag(v___x_2128_) == 0)
{
lean_dec_ref_known(v___x_2128_, 1);
v___y_1790_ = v___y_2105_;
v___y_1791_ = v___y_2106_;
v___y_1792_ = v___y_2107_;
goto v___jp_1789_;
}
else
{
v___y_1821_ = v___y_2105_;
v___y_1822_ = v___y_2106_;
v___y_1823_ = v___y_2107_;
v___y_1824_ = v___x_2128_;
goto v___jp_1820_;
}
}
}
else
{
size_t v___x_2129_; size_t v___x_2130_; lean_object* v___x_2131_; 
v___x_2129_ = ((size_t)0ULL);
v___x_2130_ = lean_usize_of_nat(v___x_2122_);
v___x_2131_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_2121_, v___x_2129_, v___x_2130_, v___x_2124_, v_a_1430_);
lean_dec(v_a_2121_);
if (lean_obj_tag(v___x_2131_) == 0)
{
lean_dec_ref_known(v___x_2131_, 1);
v___y_1790_ = v___y_2105_;
v___y_1791_ = v___y_2106_;
v___y_1792_ = v___y_2107_;
goto v___jp_1789_;
}
else
{
v___y_1821_ = v___y_2105_;
v___y_1822_ = v___y_2106_;
v___y_1823_ = v___y_2107_;
v___y_1824_ = v___x_2131_;
goto v___jp_1820_;
}
}
}
}
else
{
lean_object* v_a_2132_; lean_object* v___x_2133_; uint8_t v___x_2134_; 
v_a_2132_ = lean_ctor_get(v___x_2120_, 1);
lean_inc(v_a_2132_);
lean_dec_ref_known(v___x_2120_, 2);
v___x_2133_ = lean_array_get_size(v_a_2132_);
v___x_2134_ = lean_nat_dec_lt(v___x_2118_, v___x_2133_);
if (v___x_2134_ == 0)
{
lean_object* v___x_2135_; lean_object* v___x_2137_; 
lean_dec(v_a_2132_);
lean_dec_ref(v___y_2106_);
lean_dec_ref(v___y_2105_);
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
v___x_2135_ = lean_box(0);
if (v_isShared_2117_ == 0)
{
lean_ctor_set_tag(v___x_2116_, 1);
lean_ctor_set(v___x_2116_, 0, v___x_2135_);
v___x_2137_ = v___x_2116_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v___x_2135_);
v___x_2137_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
return v___x_2137_;
}
}
else
{
lean_object* v___x_2139_; uint8_t v___x_2140_; 
lean_del_object(v___x_2116_);
v___x_2139_ = lean_box(0);
v___x_2140_ = lean_nat_dec_le(v___x_2133_, v___x_2133_);
if (v___x_2140_ == 0)
{
if (v___x_2134_ == 0)
{
lean_dec(v_a_2132_);
lean_dec_ref(v___y_2106_);
lean_dec_ref(v___y_2105_);
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
goto v___jp_1458_;
}
else
{
size_t v___x_2141_; size_t v___x_2142_; lean_object* v___x_2143_; 
v___x_2141_ = ((size_t)0ULL);
v___x_2142_ = lean_usize_of_nat(v___x_2133_);
v___x_2143_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_2132_, v___x_2141_, v___x_2142_, v___x_2139_, v_a_1430_);
lean_dec(v_a_2132_);
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_dec_ref_known(v___x_2143_, 1);
lean_dec_ref(v___y_2106_);
lean_dec_ref(v___y_2105_);
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
goto v___jp_1458_;
}
else
{
v___y_1821_ = v___y_2105_;
v___y_1822_ = v___y_2106_;
v___y_1823_ = v___y_2107_;
v___y_1824_ = v___x_2143_;
goto v___jp_1820_;
}
}
}
else
{
size_t v___x_2144_; size_t v___x_2145_; lean_object* v___x_2146_; 
v___x_2144_ = ((size_t)0ULL);
v___x_2145_ = lean_usize_of_nat(v___x_2133_);
v___x_2146_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_2132_, v___x_2144_, v___x_2145_, v___x_2139_, v_a_1430_);
lean_dec(v_a_2132_);
if (lean_obj_tag(v___x_2146_) == 0)
{
lean_dec_ref_known(v___x_2146_, 1);
lean_dec_ref(v___y_2106_);
lean_dec_ref(v___y_2105_);
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
goto v___jp_1458_;
}
else
{
v___y_1821_ = v___y_2105_;
v___y_1822_ = v___y_2106_;
v___y_1823_ = v___y_2107_;
v___y_1824_ = v___x_2146_;
goto v___jp_1820_;
}
}
}
}
}
}
else
{
lean_object* v_a_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2161_; 
lean_dec_ref(v___y_2106_);
lean_dec_ref(v___y_2105_);
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
v_a_2149_ = lean_ctor_get(v___x_2114_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2114_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2151_ = v___x_2114_;
v_isShared_2152_ = v_isSharedCheck_2161_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_a_2149_);
lean_dec(v___x_2114_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2161_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v___x_2153_; uint8_t v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2159_; 
v___x_2153_ = lean_io_error_to_string(v_a_2149_);
v___x_2154_ = 3;
v___x_2155_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2155_, 0, v___x_2153_);
lean_ctor_set_uint8(v___x_2155_, sizeof(void*)*1, v___x_2154_);
lean_inc_ref(v_a_1430_);
v___x_2156_ = lean_apply_2(v_a_1430_, v___x_2155_, lean_box(0));
v___x_2157_ = lean_box(0);
if (v_isShared_2152_ == 0)
{
lean_ctor_set(v___x_2151_, 0, v___x_2157_);
v___x_2159_ = v___x_2151_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v___x_2157_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
}
}
else
{
lean_object* v___x_2162_; lean_object* v___x_2163_; uint8_t v___x_2164_; 
lean_inc_ref(v_repo_1432_);
lean_inc_ref(v___y_2107_);
v___x_2162_ = l_Lake_GitRepo_getRemoteUrl_x3f(v___y_2107_, v_repo_1432_);
v___x_2163_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_2164_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_2164_ == 0)
{
v___y_2028_ = v___y_2105_;
v___y_2029_ = v_a_2108_;
v___y_2030_ = v___y_2106_;
v___y_2031_ = v___y_2107_;
v_a_2032_ = v___x_2162_;
goto v___jp_2027_;
}
else
{
lean_object* v___x_2165_; uint8_t v___x_2166_; 
v___x_2165_ = lean_box(0);
v___x_2166_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
if (v___x_2166_ == 0)
{
if (v___x_2164_ == 0)
{
v___y_2028_ = v___y_2105_;
v___y_2029_ = v_a_2108_;
v___y_2030_ = v___y_2106_;
v___y_2031_ = v___y_2107_;
v_a_2032_ = v___x_2162_;
goto v___jp_2027_;
}
else
{
size_t v___x_2167_; size_t v___x_2168_; lean_object* v___x_2169_; 
v___x_2167_ = ((size_t)0ULL);
v___x_2168_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8);
v___x_2169_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_2163_, v___x_2167_, v___x_2168_, v___x_2165_, v_a_1430_);
if (lean_obj_tag(v___x_2169_) == 0)
{
lean_dec_ref_known(v___x_2169_, 1);
v___y_2028_ = v___y_2105_;
v___y_2029_ = v_a_2108_;
v___y_2030_ = v___y_2106_;
v___y_2031_ = v___y_2107_;
v_a_2032_ = v___x_2162_;
goto v___jp_2027_;
}
else
{
lean_dec(v___x_2162_);
lean_dec_ref(v___y_2106_);
lean_dec_ref(v___y_2105_);
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
return v___x_2169_;
}
}
}
else
{
size_t v___x_2170_; size_t v___x_2171_; lean_object* v___x_2172_; 
v___x_2170_ = ((size_t)0ULL);
v___x_2171_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8);
v___x_2172_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_2163_, v___x_2170_, v___x_2171_, v___x_2165_, v_a_1430_);
if (lean_obj_tag(v___x_2172_) == 0)
{
lean_dec_ref_known(v___x_2172_, 1);
v___y_2028_ = v___y_2105_;
v___y_2029_ = v_a_2108_;
v___y_2030_ = v___y_2106_;
v___y_2031_ = v___y_2107_;
v_a_2032_ = v___x_2162_;
goto v___jp_2027_;
}
else
{
lean_dec(v___x_2162_);
lean_dec_ref(v___y_2106_);
lean_dec_ref(v___y_2105_);
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
return v___x_2172_;
}
}
}
}
}
v___jp_2173_:
{
lean_object* v___x_2177_; lean_object* v___x_2178_; uint8_t v___x_2179_; lean_object* v___x_2180_; uint8_t v___x_2181_; 
v___x_2177_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__8));
lean_inc_ref(v_repo_1432_);
v___x_2178_ = l_System_FilePath_join(v_repo_1432_, v___x_2177_);
v___x_2179_ = l_System_FilePath_pathExists(v___x_2178_);
lean_dec_ref(v___x_2178_);
v___x_2180_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_2181_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_2181_ == 0)
{
v___y_2105_ = v___y_2174_;
v___y_2106_ = v_a_2176_;
v___y_2107_ = v___y_2175_;
v_a_2108_ = v___x_2179_;
goto v___jp_2104_;
}
else
{
lean_object* v___x_2182_; uint8_t v___x_2183_; 
v___x_2182_ = lean_box(0);
v___x_2183_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
if (v___x_2183_ == 0)
{
if (v___x_2181_ == 0)
{
v___y_2105_ = v___y_2174_;
v___y_2106_ = v_a_2176_;
v___y_2107_ = v___y_2175_;
v_a_2108_ = v___x_2179_;
goto v___jp_2104_;
}
else
{
size_t v___x_2184_; size_t v___x_2185_; lean_object* v___x_2186_; 
v___x_2184_ = ((size_t)0ULL);
v___x_2185_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8);
v___x_2186_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_2180_, v___x_2184_, v___x_2185_, v___x_2182_, v_a_1430_);
if (lean_obj_tag(v___x_2186_) == 0)
{
lean_dec_ref_known(v___x_2186_, 1);
v___y_2105_ = v___y_2174_;
v___y_2106_ = v_a_2176_;
v___y_2107_ = v___y_2175_;
v_a_2108_ = v___x_2179_;
goto v___jp_2104_;
}
else
{
lean_dec_ref(v_a_2176_);
lean_dec_ref(v___y_2174_);
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
return v___x_2186_;
}
}
}
else
{
size_t v___x_2187_; size_t v___x_2188_; lean_object* v___x_2189_; 
v___x_2187_ = ((size_t)0ULL);
v___x_2188_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8);
v___x_2189_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_2180_, v___x_2187_, v___x_2188_, v___x_2182_, v_a_1430_);
if (lean_obj_tag(v___x_2189_) == 0)
{
lean_dec_ref_known(v___x_2189_, 1);
v___y_2105_ = v___y_2174_;
v___y_2106_ = v_a_2176_;
v___y_2107_ = v___y_2175_;
v_a_2108_ = v___x_2179_;
goto v___jp_2104_;
}
else
{
lean_dec_ref(v_a_2176_);
lean_dec_ref(v___y_2174_);
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
return v___x_2189_;
}
}
}
}
v___jp_2190_:
{
if (lean_obj_tag(v_a_2193_) == 1)
{
lean_object* v_val_2194_; 
lean_dec_ref(v_url_1433_);
v_val_2194_ = lean_ctor_get(v_a_2193_, 0);
lean_inc(v_val_2194_);
lean_dec_ref_known(v_a_2193_, 1);
v___y_2174_ = v___y_2191_;
v___y_2175_ = v___y_2192_;
v_a_2176_ = v_val_2194_;
goto v___jp_2173_;
}
else
{
lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; uint8_t v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; 
lean_dec(v_a_2193_);
lean_dec_ref(v___y_2191_);
lean_dec_ref(v_repo_1432_);
v___x_2195_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__0));
v___x_2196_ = lean_string_append(v_name_1431_, v___x_2195_);
v___x_2197_ = lean_string_append(v___x_2196_, v_url_1433_);
lean_dec_ref(v_url_1433_);
v___x_2198_ = 3;
v___x_2199_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2199_, 0, v___x_2197_);
lean_ctor_set_uint8(v___x_2199_, sizeof(void*)*1, v___x_2198_);
lean_inc_ref(v_a_1430_);
v___x_2200_ = lean_apply_2(v_a_1430_, v___x_2199_, lean_box(0));
v___x_2201_ = lean_box(0);
v___x_2202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2201_);
return v___x_2202_;
}
}
v___jp_2203_:
{
lean_object* v___x_2209_; uint8_t v___x_2210_; 
v___x_2209_ = lean_array_get_size(v___y_2205_);
v___x_2210_ = lean_nat_dec_lt(v___y_2206_, v___x_2209_);
if (v___x_2210_ == 0)
{
v___y_2191_ = v___y_2204_;
v___y_2192_ = v___y_2207_;
v_a_2193_ = v_val_2208_;
goto v___jp_2190_;
}
else
{
lean_object* v___x_2211_; uint8_t v___x_2212_; 
v___x_2211_ = lean_box(0);
v___x_2212_ = lean_nat_dec_le(v___x_2209_, v___x_2209_);
if (v___x_2212_ == 0)
{
if (v___x_2210_ == 0)
{
v___y_2191_ = v___y_2204_;
v___y_2192_ = v___y_2207_;
v_a_2193_ = v_val_2208_;
goto v___jp_2190_;
}
else
{
size_t v___x_2213_; size_t v___x_2214_; lean_object* v___x_2215_; 
v___x_2213_ = ((size_t)0ULL);
v___x_2214_ = lean_usize_of_nat(v___x_2209_);
v___x_2215_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_2205_, v___x_2213_, v___x_2214_, v___x_2211_, v_a_1430_);
if (lean_obj_tag(v___x_2215_) == 0)
{
lean_dec_ref_known(v___x_2215_, 1);
v___y_2191_ = v___y_2204_;
v___y_2192_ = v___y_2207_;
v_a_2193_ = v_val_2208_;
goto v___jp_2190_;
}
else
{
lean_dec(v_val_2208_);
lean_dec_ref(v___y_2204_);
lean_dec_ref(v_url_1433_);
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
return v___x_2215_;
}
}
}
else
{
size_t v___x_2216_; size_t v___x_2217_; lean_object* v___x_2218_; 
v___x_2216_ = ((size_t)0ULL);
v___x_2217_ = lean_usize_of_nat(v___x_2209_);
v___x_2218_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_2205_, v___x_2216_, v___x_2217_, v___x_2211_, v_a_1430_);
if (lean_obj_tag(v___x_2218_) == 0)
{
lean_dec_ref_known(v___x_2218_, 1);
v___y_2191_ = v___y_2204_;
v___y_2192_ = v___y_2207_;
v_a_2193_ = v_val_2208_;
goto v___jp_2190_;
}
else
{
lean_dec(v_val_2208_);
lean_dec_ref(v___y_2204_);
lean_dec_ref(v_url_1433_);
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
return v___x_2218_;
}
}
}
}
v___jp_2219_:
{
if (v_a_2222_ == 0)
{
v___y_2174_ = v___y_2220_;
v___y_2175_ = v___y_2221_;
v_a_2176_ = v_url_1433_;
goto v___jp_2173_;
}
else
{
lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; uint8_t v___x_2227_; 
lean_inc_ref(v_url_1433_);
v___x_2223_ = l_Lake_resolvePath(v_url_1433_);
v___x_2224_ = lean_unsigned_to_nat(0u);
v___x_2225_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_2226_ = lean_string_utf8_byte_size(v___x_2223_);
v___x_2227_ = lean_nat_dec_eq(v___x_2226_, v___x_2224_);
if (v___x_2227_ == 0)
{
lean_object* v___x_2228_; 
v___x_2228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2228_, 0, v___x_2223_);
v___y_2204_ = v___y_2220_;
v___y_2205_ = v___x_2225_;
v___y_2206_ = v___x_2224_;
v___y_2207_ = v___y_2221_;
v_val_2208_ = v___x_2228_;
goto v___jp_2203_;
}
else
{
lean_object* v___x_2229_; 
lean_dec_ref(v___x_2223_);
v___x_2229_ = lean_box(0);
v___y_2204_ = v___y_2220_;
v___y_2205_ = v___x_2225_;
v___y_2206_ = v___x_2224_;
v___y_2207_ = v___y_2221_;
v_val_2208_ = v___x_2229_;
goto v___jp_2203_;
}
}
}
v___jp_2230_:
{
uint8_t v___x_2232_; lean_object* v_remote_2233_; lean_object* v___x_2234_; uint8_t v___x_2235_; 
v___x_2232_ = l_System_FilePath_pathExists(v_url_1433_);
v_remote_2233_ = l_Lake_Git_defaultRemote;
v___x_2234_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_2235_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_2235_ == 0)
{
v___y_2220_ = v___y_2231_;
v___y_2221_ = v_remote_2233_;
v_a_2222_ = v___x_2232_;
goto v___jp_2219_;
}
else
{
lean_object* v___x_2236_; uint8_t v___x_2237_; 
v___x_2236_ = lean_box(0);
v___x_2237_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
if (v___x_2237_ == 0)
{
if (v___x_2235_ == 0)
{
v___y_2220_ = v___y_2231_;
v___y_2221_ = v_remote_2233_;
v_a_2222_ = v___x_2232_;
goto v___jp_2219_;
}
else
{
size_t v___x_2238_; size_t v___x_2239_; lean_object* v___x_2240_; 
v___x_2238_ = ((size_t)0ULL);
v___x_2239_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8);
v___x_2240_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_2234_, v___x_2238_, v___x_2239_, v___x_2236_, v_a_1430_);
if (lean_obj_tag(v___x_2240_) == 0)
{
lean_dec_ref_known(v___x_2240_, 1);
v___y_2220_ = v___y_2231_;
v___y_2221_ = v_remote_2233_;
v_a_2222_ = v___x_2232_;
goto v___jp_2219_;
}
else
{
lean_dec_ref(v___y_2231_);
lean_dec_ref(v_url_1433_);
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
return v___x_2240_;
}
}
}
else
{
size_t v___x_2241_; size_t v___x_2242_; lean_object* v___x_2243_; 
v___x_2241_ = ((size_t)0ULL);
v___x_2242_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8);
v___x_2243_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_2234_, v___x_2241_, v___x_2242_, v___x_2236_, v_a_1430_);
if (lean_obj_tag(v___x_2243_) == 0)
{
lean_dec_ref_known(v___x_2243_, 1);
v___y_2220_ = v___y_2231_;
v___y_2221_ = v_remote_2233_;
v_a_2222_ = v___x_2232_;
goto v___jp_2219_;
}
else
{
lean_dec_ref(v___y_2231_);
lean_dec_ref(v_url_1433_);
lean_dec_ref(v_repo_1432_);
lean_dec_ref(v_name_1431_);
return v___x_2243_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0___boxed(lean_object* v_a_2246_, lean_object* v_name_2247_, lean_object* v_repo_2248_, lean_object* v_url_2249_, lean_object* v_rev_x3f_2250_, lean_object* v_a_2251_){
_start:
{
lean_object* v_res_2252_; 
v_res_2252_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(v_a_2246_, v_name_2247_, v_repo_2248_, v_url_2249_, v_rev_x3f_2250_);
lean_dec_ref(v_a_2246_);
return v_res_2252_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit(lean_object* v_dep_2253_, uint8_t v_inherited_2254_, lean_object* v_lakeEnv_2255_, lean_object* v_wsDir_2256_, lean_object* v_name_2257_, lean_object* v_relPkgDir_2258_, lean_object* v_gitUrl_2259_, lean_object* v_remoteUrl_2260_, lean_object* v_inputRev_x3f_2261_, lean_object* v_subDir_x3f_2262_, lean_object* v_a_2263_){
_start:
{
lean_object* v_pkgUrlMap_2268_; lean_object* v_name_2269_; lean_object* v_scope_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2486_; 
v_pkgUrlMap_2268_ = lean_ctor_get(v_lakeEnv_2255_, 5);
v_name_2269_ = lean_ctor_get(v_dep_2253_, 0);
v_scope_2270_ = lean_ctor_get(v_dep_2253_, 1);
v_isSharedCheck_2486_ = !lean_is_exclusive(v_dep_2253_);
if (v_isSharedCheck_2486_ == 0)
{
lean_object* v_unused_2487_; lean_object* v_unused_2488_; lean_object* v_unused_2489_; 
v_unused_2487_ = lean_ctor_get(v_dep_2253_, 4);
lean_dec(v_unused_2487_);
v_unused_2488_ = lean_ctor_get(v_dep_2253_, 3);
lean_dec(v_unused_2488_);
v_unused_2489_ = lean_ctor_get(v_dep_2253_, 2);
lean_dec(v_unused_2489_);
v___x_2272_ = v_dep_2253_;
v_isShared_2273_ = v_isSharedCheck_2486_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_scope_2270_);
lean_inc(v_name_2269_);
lean_dec(v_dep_2253_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2486_;
goto v_resetjp_2271_;
}
v___jp_2265_:
{
lean_object* v___x_2266_; lean_object* v___x_2267_; 
v___x_2266_ = lean_box(0);
v___x_2267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2267_, 0, v___x_2266_);
return v___x_2267_;
}
v_resetjp_2271_:
{
lean_object* v___y_2275_; lean_object* v___y_2276_; lean_object* v___y_2277_; lean_object* v_a_2278_; lean_object* v___y_2287_; lean_object* v___y_2288_; lean_object* v___y_2289_; lean_object* v___y_2290_; lean_object* v___y_2291_; lean_object* v_val_2292_; lean_object* v___y_2320_; lean_object* v___y_2321_; lean_object* v___y_2322_; lean_object* v_a_2323_; lean_object* v___y_2355_; lean_object* v___y_2356_; lean_object* v___y_2357_; lean_object* v___y_2358_; lean_object* v___y_2359_; lean_object* v_val_2360_; lean_object* v___y_2388_; lean_object* v___y_2389_; lean_object* v___y_2390_; lean_object* v___y_2401_; lean_object* v_a_2402_; lean_object* v_gitDir_2405_; lean_object* v___y_2407_; lean_object* v___x_2484_; 
lean_inc_ref(v_relPkgDir_2258_);
lean_inc_ref(v_wsDir_2256_);
v_gitDir_2405_ = l_Lake_joinRelative(v_wsDir_2256_, v_relPkgDir_2258_);
v___x_2484_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgUrlMap_2268_, v_name_2269_);
if (lean_obj_tag(v___x_2484_) == 0)
{
v___y_2407_ = v_gitUrl_2259_;
goto v___jp_2406_;
}
else
{
lean_object* v_val_2485_; 
lean_dec_ref(v_gitUrl_2259_);
v_val_2485_ = lean_ctor_get(v___x_2484_, 0);
lean_inc(v_val_2485_);
lean_dec_ref_known(v___x_2484_, 1);
v___y_2407_ = v_val_2485_;
goto v___jp_2406_;
}
v___jp_2274_:
{
lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2283_; 
v___x_2279_ = l_Lake_defaultConfigFile;
v___x_2280_ = lean_box(0);
v___x_2281_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_2281_, 0, v_name_2269_);
lean_ctor_set(v___x_2281_, 1, v_scope_2270_);
lean_ctor_set(v___x_2281_, 2, v___x_2279_);
lean_ctor_set(v___x_2281_, 3, v___x_2280_);
lean_ctor_set(v___x_2281_, 4, v___y_2276_);
lean_ctor_set_uint8(v___x_2281_, sizeof(void*)*5, v_inherited_2254_);
if (v_isShared_2273_ == 0)
{
lean_ctor_set(v___x_2272_, 4, v___x_2281_);
lean_ctor_set(v___x_2272_, 3, v_a_2278_);
lean_ctor_set(v___x_2272_, 2, v_remoteUrl_2260_);
lean_ctor_set(v___x_2272_, 1, v___y_2275_);
lean_ctor_set(v___x_2272_, 0, v___y_2277_);
v___x_2283_ = v___x_2272_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2285_; 
v_reuseFailAlloc_2285_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2285_, 0, v___y_2277_);
lean_ctor_set(v_reuseFailAlloc_2285_, 1, v___y_2275_);
lean_ctor_set(v_reuseFailAlloc_2285_, 2, v_remoteUrl_2260_);
lean_ctor_set(v_reuseFailAlloc_2285_, 3, v_a_2278_);
lean_ctor_set(v_reuseFailAlloc_2285_, 4, v___x_2281_);
v___x_2283_ = v_reuseFailAlloc_2285_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
lean_object* v___x_2284_; 
v___x_2284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2284_, 0, v___x_2283_);
return v___x_2284_;
}
}
v___jp_2286_:
{
lean_object* v___x_2293_; uint8_t v___x_2294_; 
v___x_2293_ = lean_array_get_size(v___y_2290_);
v___x_2294_ = lean_nat_dec_lt(v___y_2287_, v___x_2293_);
if (v___x_2294_ == 0)
{
v___y_2275_ = v___y_2289_;
v___y_2276_ = v___y_2288_;
v___y_2277_ = v___y_2291_;
v_a_2278_ = v_val_2292_;
goto v___jp_2274_;
}
else
{
lean_object* v___x_2295_; uint8_t v___x_2296_; 
v___x_2295_ = lean_box(0);
v___x_2296_ = lean_nat_dec_le(v___x_2293_, v___x_2293_);
if (v___x_2296_ == 0)
{
if (v___x_2294_ == 0)
{
v___y_2275_ = v___y_2289_;
v___y_2276_ = v___y_2288_;
v___y_2277_ = v___y_2291_;
v_a_2278_ = v_val_2292_;
goto v___jp_2274_;
}
else
{
size_t v___x_2297_; size_t v___x_2298_; lean_object* v___x_2299_; 
v___x_2297_ = ((size_t)0ULL);
v___x_2298_ = lean_usize_of_nat(v___x_2293_);
v___x_2299_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_2290_, v___x_2297_, v___x_2298_, v___x_2295_, v_a_2263_);
if (lean_obj_tag(v___x_2299_) == 0)
{
lean_dec_ref_known(v___x_2299_, 1);
v___y_2275_ = v___y_2289_;
v___y_2276_ = v___y_2288_;
v___y_2277_ = v___y_2291_;
v_a_2278_ = v_val_2292_;
goto v___jp_2274_;
}
else
{
lean_object* v_a_2300_; lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2307_; 
lean_dec_ref(v_val_2292_);
lean_dec_ref(v___y_2291_);
lean_dec_ref(v___y_2289_);
lean_dec_ref(v___y_2288_);
lean_del_object(v___x_2272_);
lean_dec_ref(v_scope_2270_);
lean_dec(v_name_2269_);
lean_dec_ref(v_remoteUrl_2260_);
v_a_2300_ = lean_ctor_get(v___x_2299_, 0);
v_isSharedCheck_2307_ = !lean_is_exclusive(v___x_2299_);
if (v_isSharedCheck_2307_ == 0)
{
v___x_2302_ = v___x_2299_;
v_isShared_2303_ = v_isSharedCheck_2307_;
goto v_resetjp_2301_;
}
else
{
lean_inc(v_a_2300_);
lean_dec(v___x_2299_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2307_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
lean_object* v___x_2305_; 
if (v_isShared_2303_ == 0)
{
v___x_2305_ = v___x_2302_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v_a_2300_);
v___x_2305_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
return v___x_2305_;
}
}
}
}
}
else
{
size_t v___x_2308_; size_t v___x_2309_; lean_object* v___x_2310_; 
v___x_2308_ = ((size_t)0ULL);
v___x_2309_ = lean_usize_of_nat(v___x_2293_);
v___x_2310_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_2290_, v___x_2308_, v___x_2309_, v___x_2295_, v_a_2263_);
if (lean_obj_tag(v___x_2310_) == 0)
{
lean_dec_ref_known(v___x_2310_, 1);
v___y_2275_ = v___y_2289_;
v___y_2276_ = v___y_2288_;
v___y_2277_ = v___y_2291_;
v_a_2278_ = v_val_2292_;
goto v___jp_2274_;
}
else
{
lean_object* v_a_2311_; lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2318_; 
lean_dec_ref(v_val_2292_);
lean_dec_ref(v___y_2291_);
lean_dec_ref(v___y_2289_);
lean_dec_ref(v___y_2288_);
lean_del_object(v___x_2272_);
lean_dec_ref(v_scope_2270_);
lean_dec(v_name_2269_);
lean_dec_ref(v_remoteUrl_2260_);
v_a_2311_ = lean_ctor_get(v___x_2310_, 0);
v_isSharedCheck_2318_ = !lean_is_exclusive(v___x_2310_);
if (v_isSharedCheck_2318_ == 0)
{
v___x_2313_ = v___x_2310_;
v_isShared_2314_ = v_isSharedCheck_2318_;
goto v_resetjp_2312_;
}
else
{
lean_inc(v_a_2311_);
lean_dec(v___x_2310_);
v___x_2313_ = lean_box(0);
v_isShared_2314_ = v_isSharedCheck_2318_;
goto v_resetjp_2312_;
}
v_resetjp_2312_:
{
lean_object* v___x_2316_; 
if (v_isShared_2314_ == 0)
{
v___x_2316_ = v___x_2313_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v_a_2311_);
v___x_2316_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
return v___x_2316_;
}
}
}
}
}
}
v___jp_2319_:
{
if (lean_obj_tag(v_a_2323_) == 1)
{
lean_object* v_val_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; 
lean_dec_ref(v___y_2322_);
lean_dec_ref(v_name_2257_);
v_val_2324_ = lean_ctor_get(v_a_2323_, 0);
lean_inc_n(v_val_2324_, 2);
lean_dec_ref_known(v_a_2323_, 1);
v___x_2325_ = l_Lake_defaultManifestFile;
v___x_2326_ = l_Lake_joinRelative(v_val_2324_, v___x_2325_);
v___x_2327_ = lean_unsigned_to_nat(0u);
v___x_2328_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_2329_ = l_Lake_Manifest_load(v___x_2326_);
if (lean_obj_tag(v___x_2329_) == 0)
{
lean_object* v_a_2330_; lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2337_; 
v_a_2330_ = lean_ctor_get(v___x_2329_, 0);
v_isSharedCheck_2337_ = !lean_is_exclusive(v___x_2329_);
if (v_isSharedCheck_2337_ == 0)
{
v___x_2332_ = v___x_2329_;
v_isShared_2333_ = v_isSharedCheck_2337_;
goto v_resetjp_2331_;
}
else
{
lean_inc(v_a_2330_);
lean_dec(v___x_2329_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2337_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
lean_object* v___x_2335_; 
if (v_isShared_2333_ == 0)
{
lean_ctor_set_tag(v___x_2332_, 1);
v___x_2335_ = v___x_2332_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v_a_2330_);
v___x_2335_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
v___y_2287_ = v___x_2327_;
v___y_2288_ = v___y_2320_;
v___y_2289_ = v___y_2321_;
v___y_2290_ = v___x_2328_;
v___y_2291_ = v_val_2324_;
v_val_2292_ = v___x_2335_;
goto v___jp_2286_;
}
}
}
else
{
lean_object* v_a_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2345_; 
v_a_2338_ = lean_ctor_get(v___x_2329_, 0);
v_isSharedCheck_2345_ = !lean_is_exclusive(v___x_2329_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2340_ = v___x_2329_;
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
else
{
lean_inc(v_a_2338_);
lean_dec(v___x_2329_);
v___x_2340_ = lean_box(0);
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
v_resetjp_2339_:
{
lean_object* v___x_2343_; 
if (v_isShared_2341_ == 0)
{
lean_ctor_set_tag(v___x_2340_, 0);
v___x_2343_ = v___x_2340_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v_a_2338_);
v___x_2343_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
v___y_2287_ = v___x_2327_;
v___y_2288_ = v___y_2320_;
v___y_2289_ = v___y_2321_;
v___y_2290_ = v___x_2328_;
v___y_2291_ = v_val_2324_;
v_val_2292_ = v___x_2343_;
goto v___jp_2286_;
}
}
}
}
else
{
lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; uint8_t v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; 
lean_dec(v_a_2323_);
lean_dec_ref(v___y_2321_);
lean_dec_ref(v___y_2320_);
lean_del_object(v___x_2272_);
lean_dec_ref(v_scope_2270_);
lean_dec(v_name_2269_);
lean_dec_ref(v_remoteUrl_2260_);
v___x_2346_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0));
v___x_2347_ = lean_string_append(v_name_2257_, v___x_2346_);
v___x_2348_ = lean_string_append(v___x_2347_, v___y_2322_);
lean_dec_ref(v___y_2322_);
v___x_2349_ = 3;
v___x_2350_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2350_, 0, v___x_2348_);
lean_ctor_set_uint8(v___x_2350_, sizeof(void*)*1, v___x_2349_);
lean_inc_ref(v_a_2263_);
v___x_2351_ = lean_apply_2(v_a_2263_, v___x_2350_, lean_box(0));
v___x_2352_ = lean_box(0);
v___x_2353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2353_, 0, v___x_2352_);
return v___x_2353_;
}
}
v___jp_2354_:
{
lean_object* v___x_2361_; uint8_t v___x_2362_; 
v___x_2361_ = lean_array_get_size(v___y_2359_);
v___x_2362_ = lean_nat_dec_lt(v___y_2357_, v___x_2361_);
if (v___x_2362_ == 0)
{
v___y_2320_ = v___y_2356_;
v___y_2321_ = v___y_2355_;
v___y_2322_ = v___y_2358_;
v_a_2323_ = v_val_2360_;
goto v___jp_2319_;
}
else
{
lean_object* v___x_2363_; uint8_t v___x_2364_; 
v___x_2363_ = lean_box(0);
v___x_2364_ = lean_nat_dec_le(v___x_2361_, v___x_2361_);
if (v___x_2364_ == 0)
{
if (v___x_2362_ == 0)
{
v___y_2320_ = v___y_2356_;
v___y_2321_ = v___y_2355_;
v___y_2322_ = v___y_2358_;
v_a_2323_ = v_val_2360_;
goto v___jp_2319_;
}
else
{
size_t v___x_2365_; size_t v___x_2366_; lean_object* v___x_2367_; 
v___x_2365_ = ((size_t)0ULL);
v___x_2366_ = lean_usize_of_nat(v___x_2361_);
v___x_2367_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_2359_, v___x_2365_, v___x_2366_, v___x_2363_, v_a_2263_);
if (lean_obj_tag(v___x_2367_) == 0)
{
lean_dec_ref_known(v___x_2367_, 1);
v___y_2320_ = v___y_2356_;
v___y_2321_ = v___y_2355_;
v___y_2322_ = v___y_2358_;
v_a_2323_ = v_val_2360_;
goto v___jp_2319_;
}
else
{
lean_object* v_a_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2375_; 
lean_dec(v_val_2360_);
lean_dec_ref(v___y_2358_);
lean_dec_ref(v___y_2356_);
lean_dec_ref(v___y_2355_);
lean_del_object(v___x_2272_);
lean_dec_ref(v_scope_2270_);
lean_dec(v_name_2269_);
lean_dec_ref(v_remoteUrl_2260_);
lean_dec_ref(v_name_2257_);
v_a_2368_ = lean_ctor_get(v___x_2367_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2367_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2370_ = v___x_2367_;
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_a_2368_);
lean_dec(v___x_2367_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v___x_2373_; 
if (v_isShared_2371_ == 0)
{
v___x_2373_ = v___x_2370_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v_a_2368_);
v___x_2373_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
return v___x_2373_;
}
}
}
}
}
else
{
size_t v___x_2376_; size_t v___x_2377_; lean_object* v___x_2378_; 
v___x_2376_ = ((size_t)0ULL);
v___x_2377_ = lean_usize_of_nat(v___x_2361_);
v___x_2378_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_2359_, v___x_2376_, v___x_2377_, v___x_2363_, v_a_2263_);
if (lean_obj_tag(v___x_2378_) == 0)
{
lean_dec_ref_known(v___x_2378_, 1);
v___y_2320_ = v___y_2356_;
v___y_2321_ = v___y_2355_;
v___y_2322_ = v___y_2358_;
v_a_2323_ = v_val_2360_;
goto v___jp_2319_;
}
else
{
lean_object* v_a_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2386_; 
lean_dec(v_val_2360_);
lean_dec_ref(v___y_2358_);
lean_dec_ref(v___y_2356_);
lean_dec_ref(v___y_2355_);
lean_del_object(v___x_2272_);
lean_dec_ref(v_scope_2270_);
lean_dec(v_name_2269_);
lean_dec_ref(v_remoteUrl_2260_);
lean_dec_ref(v_name_2257_);
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
}
v___jp_2387_:
{
lean_object* v_pkgDir_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; uint8_t v___x_2397_; 
lean_inc_ref(v___y_2390_);
v_pkgDir_2391_ = l_Lake_joinRelative(v_wsDir_2256_, v___y_2390_);
lean_inc_ref(v_pkgDir_2391_);
v___x_2392_ = l_Lake_resolvePath(v_pkgDir_2391_);
v___x_2393_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2393_, 0, v___y_2389_);
lean_ctor_set(v___x_2393_, 1, v___y_2388_);
lean_ctor_set(v___x_2393_, 2, v_inputRev_x3f_2261_);
lean_ctor_set(v___x_2393_, 3, v_subDir_x3f_2262_);
v___x_2394_ = lean_unsigned_to_nat(0u);
v___x_2395_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_2396_ = lean_string_utf8_byte_size(v___x_2392_);
v___x_2397_ = lean_nat_dec_eq(v___x_2396_, v___x_2394_);
if (v___x_2397_ == 0)
{
lean_object* v___x_2398_; 
v___x_2398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2398_, 0, v___x_2392_);
v___y_2355_ = v___y_2390_;
v___y_2356_ = v___x_2393_;
v___y_2357_ = v___x_2394_;
v___y_2358_ = v_pkgDir_2391_;
v___y_2359_ = v___x_2395_;
v_val_2360_ = v___x_2398_;
goto v___jp_2354_;
}
else
{
lean_object* v___x_2399_; 
lean_dec_ref(v___x_2392_);
v___x_2399_ = lean_box(0);
v___y_2355_ = v___y_2390_;
v___y_2356_ = v___x_2393_;
v___y_2357_ = v___x_2394_;
v___y_2358_ = v_pkgDir_2391_;
v___y_2359_ = v___x_2395_;
v_val_2360_ = v___x_2399_;
goto v___jp_2354_;
}
}
v___jp_2400_:
{
if (lean_obj_tag(v_subDir_x3f_2262_) == 1)
{
lean_object* v_val_2403_; lean_object* v___x_2404_; 
v_val_2403_ = lean_ctor_get(v_subDir_x3f_2262_, 0);
lean_inc(v_val_2403_);
v___x_2404_ = l_Lake_joinRelative(v_relPkgDir_2258_, v_val_2403_);
v___y_2388_ = v_a_2402_;
v___y_2389_ = v___y_2401_;
v___y_2390_ = v___x_2404_;
goto v___jp_2387_;
}
else
{
v___y_2388_ = v_a_2402_;
v___y_2389_ = v___y_2401_;
v___y_2390_ = v_relPkgDir_2258_;
goto v___jp_2387_;
}
}
v___jp_2406_:
{
lean_object* v___x_2408_; 
lean_inc(v_inputRev_x3f_2261_);
lean_inc_ref(v___y_2407_);
lean_inc_ref(v_gitDir_2405_);
lean_inc_ref(v_name_2257_);
v___x_2408_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(v_a_2263_, v_name_2257_, v_gitDir_2405_, v___y_2407_, v_inputRev_x3f_2261_);
if (lean_obj_tag(v___x_2408_) == 0)
{
lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2474_; 
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2408_);
if (v_isSharedCheck_2474_ == 0)
{
lean_object* v_unused_2475_; 
v_unused_2475_ = lean_ctor_get(v___x_2408_, 0);
lean_dec(v_unused_2475_);
v___x_2410_ = v___x_2408_;
v_isShared_2411_ = v_isSharedCheck_2474_;
goto v_resetjp_2409_;
}
else
{
lean_dec(v___x_2408_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2474_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; 
v___x_2412_ = lean_unsigned_to_nat(0u);
v___x_2413_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_2414_ = l_Lake_GitRepo_getHeadRevision(v_gitDir_2405_, v___x_2413_);
if (lean_obj_tag(v___x_2414_) == 0)
{
lean_object* v_a_2415_; lean_object* v_a_2416_; lean_object* v___x_2417_; uint8_t v___x_2418_; 
lean_del_object(v___x_2410_);
v_a_2415_ = lean_ctor_get(v___x_2414_, 0);
lean_inc(v_a_2415_);
v_a_2416_ = lean_ctor_get(v___x_2414_, 1);
lean_inc(v_a_2416_);
lean_dec_ref_known(v___x_2414_, 2);
v___x_2417_ = lean_array_get_size(v_a_2416_);
v___x_2418_ = lean_nat_dec_lt(v___x_2412_, v___x_2417_);
if (v___x_2418_ == 0)
{
lean_dec(v_a_2416_);
v___y_2401_ = v___y_2407_;
v_a_2402_ = v_a_2415_;
goto v___jp_2400_;
}
else
{
lean_object* v___x_2419_; uint8_t v___x_2420_; 
v___x_2419_ = lean_box(0);
v___x_2420_ = lean_nat_dec_le(v___x_2417_, v___x_2417_);
if (v___x_2420_ == 0)
{
if (v___x_2418_ == 0)
{
lean_dec(v_a_2416_);
v___y_2401_ = v___y_2407_;
v_a_2402_ = v_a_2415_;
goto v___jp_2400_;
}
else
{
size_t v___x_2421_; size_t v___x_2422_; lean_object* v___x_2423_; 
v___x_2421_ = ((size_t)0ULL);
v___x_2422_ = lean_usize_of_nat(v___x_2417_);
v___x_2423_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_2416_, v___x_2421_, v___x_2422_, v___x_2419_, v_a_2263_);
lean_dec(v_a_2416_);
if (lean_obj_tag(v___x_2423_) == 0)
{
lean_dec_ref_known(v___x_2423_, 1);
v___y_2401_ = v___y_2407_;
v_a_2402_ = v_a_2415_;
goto v___jp_2400_;
}
else
{
lean_object* v_a_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2431_; 
lean_dec(v_a_2415_);
lean_dec_ref(v___y_2407_);
lean_del_object(v___x_2272_);
lean_dec_ref(v_scope_2270_);
lean_dec(v_name_2269_);
lean_dec(v_subDir_x3f_2262_);
lean_dec(v_inputRev_x3f_2261_);
lean_dec_ref(v_remoteUrl_2260_);
lean_dec_ref(v_relPkgDir_2258_);
lean_dec_ref(v_name_2257_);
lean_dec_ref(v_wsDir_2256_);
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
else
{
size_t v___x_2432_; size_t v___x_2433_; lean_object* v___x_2434_; 
v___x_2432_ = ((size_t)0ULL);
v___x_2433_ = lean_usize_of_nat(v___x_2417_);
v___x_2434_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_2416_, v___x_2432_, v___x_2433_, v___x_2419_, v_a_2263_);
lean_dec(v_a_2416_);
if (lean_obj_tag(v___x_2434_) == 0)
{
lean_dec_ref_known(v___x_2434_, 1);
v___y_2401_ = v___y_2407_;
v_a_2402_ = v_a_2415_;
goto v___jp_2400_;
}
else
{
lean_object* v_a_2435_; lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2442_; 
lean_dec(v_a_2415_);
lean_dec_ref(v___y_2407_);
lean_del_object(v___x_2272_);
lean_dec_ref(v_scope_2270_);
lean_dec(v_name_2269_);
lean_dec(v_subDir_x3f_2262_);
lean_dec(v_inputRev_x3f_2261_);
lean_dec_ref(v_remoteUrl_2260_);
lean_dec_ref(v_relPkgDir_2258_);
lean_dec_ref(v_name_2257_);
lean_dec_ref(v_wsDir_2256_);
v_a_2435_ = lean_ctor_get(v___x_2434_, 0);
v_isSharedCheck_2442_ = !lean_is_exclusive(v___x_2434_);
if (v_isSharedCheck_2442_ == 0)
{
v___x_2437_ = v___x_2434_;
v_isShared_2438_ = v_isSharedCheck_2442_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_a_2435_);
lean_dec(v___x_2434_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2442_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
lean_object* v___x_2440_; 
if (v_isShared_2438_ == 0)
{
v___x_2440_ = v___x_2437_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v_a_2435_);
v___x_2440_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
return v___x_2440_;
}
}
}
}
}
}
else
{
lean_object* v_a_2443_; lean_object* v___x_2444_; uint8_t v___x_2445_; 
lean_dec_ref(v___y_2407_);
lean_del_object(v___x_2272_);
lean_dec_ref(v_scope_2270_);
lean_dec(v_name_2269_);
lean_dec(v_subDir_x3f_2262_);
lean_dec(v_inputRev_x3f_2261_);
lean_dec_ref(v_remoteUrl_2260_);
lean_dec_ref(v_relPkgDir_2258_);
lean_dec_ref(v_name_2257_);
lean_dec_ref(v_wsDir_2256_);
v_a_2443_ = lean_ctor_get(v___x_2414_, 1);
lean_inc(v_a_2443_);
lean_dec_ref_known(v___x_2414_, 2);
v___x_2444_ = lean_array_get_size(v_a_2443_);
v___x_2445_ = lean_nat_dec_lt(v___x_2412_, v___x_2444_);
if (v___x_2445_ == 0)
{
lean_object* v___x_2446_; lean_object* v___x_2448_; 
lean_dec(v_a_2443_);
v___x_2446_ = lean_box(0);
if (v_isShared_2411_ == 0)
{
lean_ctor_set_tag(v___x_2410_, 1);
lean_ctor_set(v___x_2410_, 0, v___x_2446_);
v___x_2448_ = v___x_2410_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v___x_2446_);
v___x_2448_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
return v___x_2448_;
}
}
else
{
lean_object* v___x_2450_; uint8_t v___x_2451_; 
lean_del_object(v___x_2410_);
v___x_2450_ = lean_box(0);
v___x_2451_ = lean_nat_dec_le(v___x_2444_, v___x_2444_);
if (v___x_2451_ == 0)
{
if (v___x_2445_ == 0)
{
lean_dec(v_a_2443_);
goto v___jp_2265_;
}
else
{
size_t v___x_2452_; size_t v___x_2453_; lean_object* v___x_2454_; 
v___x_2452_ = ((size_t)0ULL);
v___x_2453_ = lean_usize_of_nat(v___x_2444_);
v___x_2454_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_2443_, v___x_2452_, v___x_2453_, v___x_2450_, v_a_2263_);
lean_dec(v_a_2443_);
if (lean_obj_tag(v___x_2454_) == 0)
{
lean_dec_ref_known(v___x_2454_, 1);
goto v___jp_2265_;
}
else
{
lean_object* v_a_2455_; lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2462_; 
v_a_2455_ = lean_ctor_get(v___x_2454_, 0);
v_isSharedCheck_2462_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2462_ == 0)
{
v___x_2457_ = v___x_2454_;
v_isShared_2458_ = v_isSharedCheck_2462_;
goto v_resetjp_2456_;
}
else
{
lean_inc(v_a_2455_);
lean_dec(v___x_2454_);
v___x_2457_ = lean_box(0);
v_isShared_2458_ = v_isSharedCheck_2462_;
goto v_resetjp_2456_;
}
v_resetjp_2456_:
{
lean_object* v___x_2460_; 
if (v_isShared_2458_ == 0)
{
v___x_2460_ = v___x_2457_;
goto v_reusejp_2459_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v_a_2455_);
v___x_2460_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2459_;
}
v_reusejp_2459_:
{
return v___x_2460_;
}
}
}
}
}
else
{
size_t v___x_2463_; size_t v___x_2464_; lean_object* v___x_2465_; 
v___x_2463_ = ((size_t)0ULL);
v___x_2464_ = lean_usize_of_nat(v___x_2444_);
v___x_2465_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_2443_, v___x_2463_, v___x_2464_, v___x_2450_, v_a_2263_);
lean_dec(v_a_2443_);
if (lean_obj_tag(v___x_2465_) == 0)
{
lean_dec_ref_known(v___x_2465_, 1);
goto v___jp_2265_;
}
else
{
lean_object* v_a_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2473_; 
v_a_2466_ = lean_ctor_get(v___x_2465_, 0);
v_isSharedCheck_2473_ = !lean_is_exclusive(v___x_2465_);
if (v_isSharedCheck_2473_ == 0)
{
v___x_2468_ = v___x_2465_;
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_a_2466_);
lean_dec(v___x_2465_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
lean_object* v___x_2471_; 
if (v_isShared_2469_ == 0)
{
v___x_2471_ = v___x_2468_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v_a_2466_);
v___x_2471_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
return v___x_2471_;
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
lean_object* v_a_2476_; lean_object* v___x_2478_; uint8_t v_isShared_2479_; uint8_t v_isSharedCheck_2483_; 
lean_dec_ref(v___y_2407_);
lean_dec_ref(v_gitDir_2405_);
lean_del_object(v___x_2272_);
lean_dec_ref(v_scope_2270_);
lean_dec(v_name_2269_);
lean_dec(v_subDir_x3f_2262_);
lean_dec(v_inputRev_x3f_2261_);
lean_dec_ref(v_remoteUrl_2260_);
lean_dec_ref(v_relPkgDir_2258_);
lean_dec_ref(v_name_2257_);
lean_dec_ref(v_wsDir_2256_);
v_a_2476_ = lean_ctor_get(v___x_2408_, 0);
v_isSharedCheck_2483_ = !lean_is_exclusive(v___x_2408_);
if (v_isSharedCheck_2483_ == 0)
{
v___x_2478_ = v___x_2408_;
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
else
{
lean_inc(v_a_2476_);
lean_dec(v___x_2408_);
v___x_2478_ = lean_box(0);
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
v_resetjp_2477_:
{
lean_object* v___x_2481_; 
if (v_isShared_2479_ == 0)
{
v___x_2481_ = v___x_2478_;
goto v_reusejp_2480_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v_a_2476_);
v___x_2481_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2480_;
}
v_reusejp_2480_:
{
return v___x_2481_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___boxed(lean_object* v_dep_2490_, lean_object* v_inherited_2491_, lean_object* v_lakeEnv_2492_, lean_object* v_wsDir_2493_, lean_object* v_name_2494_, lean_object* v_relPkgDir_2495_, lean_object* v_gitUrl_2496_, lean_object* v_remoteUrl_2497_, lean_object* v_inputRev_x3f_2498_, lean_object* v_subDir_x3f_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_){
_start:
{
uint8_t v_inherited_boxed_2502_; lean_object* v_res_2503_; 
v_inherited_boxed_2502_ = lean_unbox(v_inherited_2491_);
v_res_2503_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit(v_dep_2490_, v_inherited_boxed_2502_, v_lakeEnv_2492_, v_wsDir_2493_, v_name_2494_, v_relPkgDir_2495_, v_gitUrl_2496_, v_remoteUrl_2497_, v_inputRev_x3f_2498_, v_subDir_x3f_2499_, v_a_2500_);
lean_dec_ref(v_a_2500_);
lean_dec_ref(v_lakeEnv_2492_);
return v_res_2503_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(lean_object* v_a_2504_, lean_object* v_dep_2505_, uint8_t v_inherited_2506_, lean_object* v_lakeEnv_2507_, lean_object* v_wsDir_2508_, lean_object* v_name_2509_, lean_object* v_relPkgDir_2510_, lean_object* v_gitUrl_2511_, lean_object* v_remoteUrl_2512_, lean_object* v_inputRev_x3f_2513_, lean_object* v_subDir_x3f_2514_){
_start:
{
lean_object* v_pkgUrlMap_2519_; lean_object* v_name_2520_; lean_object* v_scope_2521_; lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2737_; 
v_pkgUrlMap_2519_ = lean_ctor_get(v_lakeEnv_2507_, 5);
v_name_2520_ = lean_ctor_get(v_dep_2505_, 0);
v_scope_2521_ = lean_ctor_get(v_dep_2505_, 1);
v_isSharedCheck_2737_ = !lean_is_exclusive(v_dep_2505_);
if (v_isSharedCheck_2737_ == 0)
{
lean_object* v_unused_2738_; lean_object* v_unused_2739_; lean_object* v_unused_2740_; 
v_unused_2738_ = lean_ctor_get(v_dep_2505_, 4);
lean_dec(v_unused_2738_);
v_unused_2739_ = lean_ctor_get(v_dep_2505_, 3);
lean_dec(v_unused_2739_);
v_unused_2740_ = lean_ctor_get(v_dep_2505_, 2);
lean_dec(v_unused_2740_);
v___x_2523_ = v_dep_2505_;
v_isShared_2524_ = v_isSharedCheck_2737_;
goto v_resetjp_2522_;
}
else
{
lean_inc(v_scope_2521_);
lean_inc(v_name_2520_);
lean_dec(v_dep_2505_);
v___x_2523_ = lean_box(0);
v_isShared_2524_ = v_isSharedCheck_2737_;
goto v_resetjp_2522_;
}
v___jp_2516_:
{
lean_object* v___x_2517_; lean_object* v___x_2518_; 
v___x_2517_ = lean_box(0);
v___x_2518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2518_, 0, v___x_2517_);
return v___x_2518_;
}
v_resetjp_2522_:
{
lean_object* v___y_2526_; lean_object* v___y_2527_; lean_object* v___y_2528_; lean_object* v_a_2529_; lean_object* v___y_2538_; lean_object* v___y_2539_; lean_object* v___y_2540_; lean_object* v___y_2541_; lean_object* v___y_2542_; lean_object* v_val_2543_; lean_object* v___y_2571_; lean_object* v___y_2572_; lean_object* v___y_2573_; lean_object* v_a_2574_; lean_object* v___y_2606_; lean_object* v___y_2607_; lean_object* v___y_2608_; lean_object* v___y_2609_; lean_object* v___y_2610_; lean_object* v_val_2611_; lean_object* v___y_2639_; lean_object* v___y_2640_; lean_object* v___y_2641_; lean_object* v___y_2652_; lean_object* v_a_2653_; lean_object* v_gitDir_2656_; lean_object* v___y_2658_; lean_object* v___x_2735_; 
lean_inc_ref(v_relPkgDir_2510_);
lean_inc_ref(v_wsDir_2508_);
v_gitDir_2656_ = l_Lake_joinRelative(v_wsDir_2508_, v_relPkgDir_2510_);
v___x_2735_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgUrlMap_2519_, v_name_2520_);
if (lean_obj_tag(v___x_2735_) == 0)
{
v___y_2658_ = v_gitUrl_2511_;
goto v___jp_2657_;
}
else
{
lean_object* v_val_2736_; 
lean_dec_ref(v_gitUrl_2511_);
v_val_2736_ = lean_ctor_get(v___x_2735_, 0);
lean_inc(v_val_2736_);
lean_dec_ref_known(v___x_2735_, 1);
v___y_2658_ = v_val_2736_;
goto v___jp_2657_;
}
v___jp_2525_:
{
lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2534_; 
v___x_2530_ = l_Lake_defaultConfigFile;
v___x_2531_ = lean_box(0);
v___x_2532_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_2532_, 0, v_name_2520_);
lean_ctor_set(v___x_2532_, 1, v_scope_2521_);
lean_ctor_set(v___x_2532_, 2, v___x_2530_);
lean_ctor_set(v___x_2532_, 3, v___x_2531_);
lean_ctor_set(v___x_2532_, 4, v___y_2526_);
lean_ctor_set_uint8(v___x_2532_, sizeof(void*)*5, v_inherited_2506_);
if (v_isShared_2524_ == 0)
{
lean_ctor_set(v___x_2523_, 4, v___x_2532_);
lean_ctor_set(v___x_2523_, 3, v_a_2529_);
lean_ctor_set(v___x_2523_, 2, v_remoteUrl_2512_);
lean_ctor_set(v___x_2523_, 1, v___y_2528_);
lean_ctor_set(v___x_2523_, 0, v___y_2527_);
v___x_2534_ = v___x_2523_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v___y_2527_);
lean_ctor_set(v_reuseFailAlloc_2536_, 1, v___y_2528_);
lean_ctor_set(v_reuseFailAlloc_2536_, 2, v_remoteUrl_2512_);
lean_ctor_set(v_reuseFailAlloc_2536_, 3, v_a_2529_);
lean_ctor_set(v_reuseFailAlloc_2536_, 4, v___x_2532_);
v___x_2534_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
lean_object* v___x_2535_; 
v___x_2535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2535_, 0, v___x_2534_);
return v___x_2535_;
}
}
v___jp_2537_:
{
lean_object* v___x_2544_; uint8_t v___x_2545_; 
v___x_2544_ = lean_array_get_size(v___y_2540_);
v___x_2545_ = lean_nat_dec_lt(v___y_2541_, v___x_2544_);
if (v___x_2545_ == 0)
{
v___y_2526_ = v___y_2538_;
v___y_2527_ = v___y_2539_;
v___y_2528_ = v___y_2542_;
v_a_2529_ = v_val_2543_;
goto v___jp_2525_;
}
else
{
lean_object* v___x_2546_; uint8_t v___x_2547_; 
v___x_2546_ = lean_box(0);
v___x_2547_ = lean_nat_dec_le(v___x_2544_, v___x_2544_);
if (v___x_2547_ == 0)
{
if (v___x_2545_ == 0)
{
v___y_2526_ = v___y_2538_;
v___y_2527_ = v___y_2539_;
v___y_2528_ = v___y_2542_;
v_a_2529_ = v_val_2543_;
goto v___jp_2525_;
}
else
{
size_t v___x_2548_; size_t v___x_2549_; lean_object* v___x_2550_; 
v___x_2548_ = ((size_t)0ULL);
v___x_2549_ = lean_usize_of_nat(v___x_2544_);
v___x_2550_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_2540_, v___x_2548_, v___x_2549_, v___x_2546_, v_a_2504_);
if (lean_obj_tag(v___x_2550_) == 0)
{
lean_dec_ref_known(v___x_2550_, 1);
v___y_2526_ = v___y_2538_;
v___y_2527_ = v___y_2539_;
v___y_2528_ = v___y_2542_;
v_a_2529_ = v_val_2543_;
goto v___jp_2525_;
}
else
{
lean_object* v_a_2551_; lean_object* v___x_2553_; uint8_t v_isShared_2554_; uint8_t v_isSharedCheck_2558_; 
lean_dec_ref(v_val_2543_);
lean_dec_ref(v___y_2542_);
lean_dec_ref(v___y_2539_);
lean_dec_ref(v___y_2538_);
lean_del_object(v___x_2523_);
lean_dec_ref(v_scope_2521_);
lean_dec(v_name_2520_);
lean_dec_ref(v_remoteUrl_2512_);
v_a_2551_ = lean_ctor_get(v___x_2550_, 0);
v_isSharedCheck_2558_ = !lean_is_exclusive(v___x_2550_);
if (v_isSharedCheck_2558_ == 0)
{
v___x_2553_ = v___x_2550_;
v_isShared_2554_ = v_isSharedCheck_2558_;
goto v_resetjp_2552_;
}
else
{
lean_inc(v_a_2551_);
lean_dec(v___x_2550_);
v___x_2553_ = lean_box(0);
v_isShared_2554_ = v_isSharedCheck_2558_;
goto v_resetjp_2552_;
}
v_resetjp_2552_:
{
lean_object* v___x_2556_; 
if (v_isShared_2554_ == 0)
{
v___x_2556_ = v___x_2553_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v_a_2551_);
v___x_2556_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
return v___x_2556_;
}
}
}
}
}
else
{
size_t v___x_2559_; size_t v___x_2560_; lean_object* v___x_2561_; 
v___x_2559_ = ((size_t)0ULL);
v___x_2560_ = lean_usize_of_nat(v___x_2544_);
v___x_2561_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_2540_, v___x_2559_, v___x_2560_, v___x_2546_, v_a_2504_);
if (lean_obj_tag(v___x_2561_) == 0)
{
lean_dec_ref_known(v___x_2561_, 1);
v___y_2526_ = v___y_2538_;
v___y_2527_ = v___y_2539_;
v___y_2528_ = v___y_2542_;
v_a_2529_ = v_val_2543_;
goto v___jp_2525_;
}
else
{
lean_object* v_a_2562_; lean_object* v___x_2564_; uint8_t v_isShared_2565_; uint8_t v_isSharedCheck_2569_; 
lean_dec_ref(v_val_2543_);
lean_dec_ref(v___y_2542_);
lean_dec_ref(v___y_2539_);
lean_dec_ref(v___y_2538_);
lean_del_object(v___x_2523_);
lean_dec_ref(v_scope_2521_);
lean_dec(v_name_2520_);
lean_dec_ref(v_remoteUrl_2512_);
v_a_2562_ = lean_ctor_get(v___x_2561_, 0);
v_isSharedCheck_2569_ = !lean_is_exclusive(v___x_2561_);
if (v_isSharedCheck_2569_ == 0)
{
v___x_2564_ = v___x_2561_;
v_isShared_2565_ = v_isSharedCheck_2569_;
goto v_resetjp_2563_;
}
else
{
lean_inc(v_a_2562_);
lean_dec(v___x_2561_);
v___x_2564_ = lean_box(0);
v_isShared_2565_ = v_isSharedCheck_2569_;
goto v_resetjp_2563_;
}
v_resetjp_2563_:
{
lean_object* v___x_2567_; 
if (v_isShared_2565_ == 0)
{
v___x_2567_ = v___x_2564_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v_a_2562_);
v___x_2567_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
return v___x_2567_;
}
}
}
}
}
}
v___jp_2570_:
{
if (lean_obj_tag(v_a_2574_) == 1)
{
lean_object* v_val_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; 
lean_dec_ref(v___y_2572_);
lean_dec_ref(v_name_2509_);
v_val_2575_ = lean_ctor_get(v_a_2574_, 0);
lean_inc_n(v_val_2575_, 2);
lean_dec_ref_known(v_a_2574_, 1);
v___x_2576_ = l_Lake_defaultManifestFile;
v___x_2577_ = l_Lake_joinRelative(v_val_2575_, v___x_2576_);
v___x_2578_ = lean_unsigned_to_nat(0u);
v___x_2579_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
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
v___y_2538_ = v___y_2571_;
v___y_2539_ = v_val_2575_;
v___y_2540_ = v___x_2579_;
v___y_2541_ = v___x_2578_;
v___y_2542_ = v___y_2573_;
v_val_2543_ = v___x_2586_;
goto v___jp_2537_;
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
v___y_2538_ = v___y_2571_;
v___y_2539_ = v_val_2575_;
v___y_2540_ = v___x_2579_;
v___y_2541_ = v___x_2578_;
v___y_2542_ = v___y_2573_;
v_val_2543_ = v___x_2594_;
goto v___jp_2537_;
}
}
}
}
else
{
lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; uint8_t v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; 
lean_dec(v_a_2574_);
lean_dec_ref(v___y_2573_);
lean_dec_ref(v___y_2571_);
lean_del_object(v___x_2523_);
lean_dec_ref(v_scope_2521_);
lean_dec(v_name_2520_);
lean_dec_ref(v_remoteUrl_2512_);
v___x_2597_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0));
v___x_2598_ = lean_string_append(v_name_2509_, v___x_2597_);
v___x_2599_ = lean_string_append(v___x_2598_, v___y_2572_);
lean_dec_ref(v___y_2572_);
v___x_2600_ = 3;
v___x_2601_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2601_, 0, v___x_2599_);
lean_ctor_set_uint8(v___x_2601_, sizeof(void*)*1, v___x_2600_);
lean_inc_ref(v_a_2504_);
v___x_2602_ = lean_apply_2(v_a_2504_, v___x_2601_, lean_box(0));
v___x_2603_ = lean_box(0);
v___x_2604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2604_, 0, v___x_2603_);
return v___x_2604_;
}
}
v___jp_2605_:
{
lean_object* v___x_2612_; uint8_t v___x_2613_; 
v___x_2612_ = lean_array_get_size(v___y_2609_);
v___x_2613_ = lean_nat_dec_lt(v___y_2607_, v___x_2612_);
if (v___x_2613_ == 0)
{
v___y_2571_ = v___y_2606_;
v___y_2572_ = v___y_2608_;
v___y_2573_ = v___y_2610_;
v_a_2574_ = v_val_2611_;
goto v___jp_2570_;
}
else
{
lean_object* v___x_2614_; uint8_t v___x_2615_; 
v___x_2614_ = lean_box(0);
v___x_2615_ = lean_nat_dec_le(v___x_2612_, v___x_2612_);
if (v___x_2615_ == 0)
{
if (v___x_2613_ == 0)
{
v___y_2571_ = v___y_2606_;
v___y_2572_ = v___y_2608_;
v___y_2573_ = v___y_2610_;
v_a_2574_ = v_val_2611_;
goto v___jp_2570_;
}
else
{
size_t v___x_2616_; size_t v___x_2617_; lean_object* v___x_2618_; 
v___x_2616_ = ((size_t)0ULL);
v___x_2617_ = lean_usize_of_nat(v___x_2612_);
v___x_2618_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_2609_, v___x_2616_, v___x_2617_, v___x_2614_, v_a_2504_);
if (lean_obj_tag(v___x_2618_) == 0)
{
lean_dec_ref_known(v___x_2618_, 1);
v___y_2571_ = v___y_2606_;
v___y_2572_ = v___y_2608_;
v___y_2573_ = v___y_2610_;
v_a_2574_ = v_val_2611_;
goto v___jp_2570_;
}
else
{
lean_object* v_a_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2626_; 
lean_dec(v_val_2611_);
lean_dec_ref(v___y_2610_);
lean_dec_ref(v___y_2608_);
lean_dec_ref(v___y_2606_);
lean_del_object(v___x_2523_);
lean_dec_ref(v_scope_2521_);
lean_dec(v_name_2520_);
lean_dec_ref(v_remoteUrl_2512_);
lean_dec_ref(v_name_2509_);
v_a_2619_ = lean_ctor_get(v___x_2618_, 0);
v_isSharedCheck_2626_ = !lean_is_exclusive(v___x_2618_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2621_ = v___x_2618_;
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_a_2619_);
lean_dec(v___x_2618_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
lean_object* v___x_2624_; 
if (v_isShared_2622_ == 0)
{
v___x_2624_ = v___x_2621_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v_a_2619_);
v___x_2624_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
return v___x_2624_;
}
}
}
}
}
else
{
size_t v___x_2627_; size_t v___x_2628_; lean_object* v___x_2629_; 
v___x_2627_ = ((size_t)0ULL);
v___x_2628_ = lean_usize_of_nat(v___x_2612_);
v___x_2629_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_2609_, v___x_2627_, v___x_2628_, v___x_2614_, v_a_2504_);
if (lean_obj_tag(v___x_2629_) == 0)
{
lean_dec_ref_known(v___x_2629_, 1);
v___y_2571_ = v___y_2606_;
v___y_2572_ = v___y_2608_;
v___y_2573_ = v___y_2610_;
v_a_2574_ = v_val_2611_;
goto v___jp_2570_;
}
else
{
lean_object* v_a_2630_; lean_object* v___x_2632_; uint8_t v_isShared_2633_; uint8_t v_isSharedCheck_2637_; 
lean_dec(v_val_2611_);
lean_dec_ref(v___y_2610_);
lean_dec_ref(v___y_2608_);
lean_dec_ref(v___y_2606_);
lean_del_object(v___x_2523_);
lean_dec_ref(v_scope_2521_);
lean_dec(v_name_2520_);
lean_dec_ref(v_remoteUrl_2512_);
lean_dec_ref(v_name_2509_);
v_a_2630_ = lean_ctor_get(v___x_2629_, 0);
v_isSharedCheck_2637_ = !lean_is_exclusive(v___x_2629_);
if (v_isSharedCheck_2637_ == 0)
{
v___x_2632_ = v___x_2629_;
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
else
{
lean_inc(v_a_2630_);
lean_dec(v___x_2629_);
v___x_2632_ = lean_box(0);
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
v_resetjp_2631_:
{
lean_object* v___x_2635_; 
if (v_isShared_2633_ == 0)
{
v___x_2635_ = v___x_2632_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v_a_2630_);
v___x_2635_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
return v___x_2635_;
}
}
}
}
}
}
v___jp_2638_:
{
lean_object* v_pkgDir_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; uint8_t v___x_2648_; 
lean_inc_ref(v___y_2641_);
v_pkgDir_2642_ = l_Lake_joinRelative(v_wsDir_2508_, v___y_2641_);
lean_inc_ref(v_pkgDir_2642_);
v___x_2643_ = l_Lake_resolvePath(v_pkgDir_2642_);
v___x_2644_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2644_, 0, v___y_2640_);
lean_ctor_set(v___x_2644_, 1, v___y_2639_);
lean_ctor_set(v___x_2644_, 2, v_inputRev_x3f_2513_);
lean_ctor_set(v___x_2644_, 3, v_subDir_x3f_2514_);
v___x_2645_ = lean_unsigned_to_nat(0u);
v___x_2646_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_2647_ = lean_string_utf8_byte_size(v___x_2643_);
v___x_2648_ = lean_nat_dec_eq(v___x_2647_, v___x_2645_);
if (v___x_2648_ == 0)
{
lean_object* v___x_2649_; 
v___x_2649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2649_, 0, v___x_2643_);
v___y_2606_ = v___x_2644_;
v___y_2607_ = v___x_2645_;
v___y_2608_ = v_pkgDir_2642_;
v___y_2609_ = v___x_2646_;
v___y_2610_ = v___y_2641_;
v_val_2611_ = v___x_2649_;
goto v___jp_2605_;
}
else
{
lean_object* v___x_2650_; 
lean_dec_ref(v___x_2643_);
v___x_2650_ = lean_box(0);
v___y_2606_ = v___x_2644_;
v___y_2607_ = v___x_2645_;
v___y_2608_ = v_pkgDir_2642_;
v___y_2609_ = v___x_2646_;
v___y_2610_ = v___y_2641_;
v_val_2611_ = v___x_2650_;
goto v___jp_2605_;
}
}
v___jp_2651_:
{
if (lean_obj_tag(v_subDir_x3f_2514_) == 1)
{
lean_object* v_val_2654_; lean_object* v___x_2655_; 
v_val_2654_ = lean_ctor_get(v_subDir_x3f_2514_, 0);
lean_inc(v_val_2654_);
v___x_2655_ = l_Lake_joinRelative(v_relPkgDir_2510_, v_val_2654_);
v___y_2639_ = v_a_2653_;
v___y_2640_ = v___y_2652_;
v___y_2641_ = v___x_2655_;
goto v___jp_2638_;
}
else
{
v___y_2639_ = v_a_2653_;
v___y_2640_ = v___y_2652_;
v___y_2641_ = v_relPkgDir_2510_;
goto v___jp_2638_;
}
}
v___jp_2657_:
{
lean_object* v___x_2659_; 
lean_inc(v_inputRev_x3f_2513_);
lean_inc_ref(v___y_2658_);
lean_inc_ref(v_gitDir_2656_);
lean_inc_ref(v_name_2509_);
v___x_2659_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(v_a_2504_, v_name_2509_, v_gitDir_2656_, v___y_2658_, v_inputRev_x3f_2513_);
if (lean_obj_tag(v___x_2659_) == 0)
{
lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2725_; 
v_isSharedCheck_2725_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_2725_ == 0)
{
lean_object* v_unused_2726_; 
v_unused_2726_ = lean_ctor_get(v___x_2659_, 0);
lean_dec(v_unused_2726_);
v___x_2661_ = v___x_2659_;
v_isShared_2662_ = v_isSharedCheck_2725_;
goto v_resetjp_2660_;
}
else
{
lean_dec(v___x_2659_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2725_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; 
v___x_2663_ = lean_unsigned_to_nat(0u);
v___x_2664_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_2665_ = l_Lake_GitRepo_getHeadRevision(v_gitDir_2656_, v___x_2664_);
if (lean_obj_tag(v___x_2665_) == 0)
{
lean_object* v_a_2666_; lean_object* v_a_2667_; lean_object* v___x_2668_; uint8_t v___x_2669_; 
lean_del_object(v___x_2661_);
v_a_2666_ = lean_ctor_get(v___x_2665_, 0);
lean_inc(v_a_2666_);
v_a_2667_ = lean_ctor_get(v___x_2665_, 1);
lean_inc(v_a_2667_);
lean_dec_ref_known(v___x_2665_, 2);
v___x_2668_ = lean_array_get_size(v_a_2667_);
v___x_2669_ = lean_nat_dec_lt(v___x_2663_, v___x_2668_);
if (v___x_2669_ == 0)
{
lean_dec(v_a_2667_);
v___y_2652_ = v___y_2658_;
v_a_2653_ = v_a_2666_;
goto v___jp_2651_;
}
else
{
lean_object* v___x_2670_; uint8_t v___x_2671_; 
v___x_2670_ = lean_box(0);
v___x_2671_ = lean_nat_dec_le(v___x_2668_, v___x_2668_);
if (v___x_2671_ == 0)
{
if (v___x_2669_ == 0)
{
lean_dec(v_a_2667_);
v___y_2652_ = v___y_2658_;
v_a_2653_ = v_a_2666_;
goto v___jp_2651_;
}
else
{
size_t v___x_2672_; size_t v___x_2673_; lean_object* v___x_2674_; 
v___x_2672_ = ((size_t)0ULL);
v___x_2673_ = lean_usize_of_nat(v___x_2668_);
v___x_2674_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_2667_, v___x_2672_, v___x_2673_, v___x_2670_, v_a_2504_);
lean_dec(v_a_2667_);
if (lean_obj_tag(v___x_2674_) == 0)
{
lean_dec_ref_known(v___x_2674_, 1);
v___y_2652_ = v___y_2658_;
v_a_2653_ = v_a_2666_;
goto v___jp_2651_;
}
else
{
lean_object* v_a_2675_; lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2682_; 
lean_dec(v_a_2666_);
lean_dec_ref(v___y_2658_);
lean_del_object(v___x_2523_);
lean_dec_ref(v_scope_2521_);
lean_dec(v_name_2520_);
lean_dec(v_subDir_x3f_2514_);
lean_dec(v_inputRev_x3f_2513_);
lean_dec_ref(v_remoteUrl_2512_);
lean_dec_ref(v_relPkgDir_2510_);
lean_dec_ref(v_name_2509_);
lean_dec_ref(v_wsDir_2508_);
v_a_2675_ = lean_ctor_get(v___x_2674_, 0);
v_isSharedCheck_2682_ = !lean_is_exclusive(v___x_2674_);
if (v_isSharedCheck_2682_ == 0)
{
v___x_2677_ = v___x_2674_;
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
else
{
lean_inc(v_a_2675_);
lean_dec(v___x_2674_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v___x_2680_; 
if (v_isShared_2678_ == 0)
{
v___x_2680_ = v___x_2677_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v_a_2675_);
v___x_2680_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
return v___x_2680_;
}
}
}
}
}
else
{
size_t v___x_2683_; size_t v___x_2684_; lean_object* v___x_2685_; 
v___x_2683_ = ((size_t)0ULL);
v___x_2684_ = lean_usize_of_nat(v___x_2668_);
v___x_2685_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_2667_, v___x_2683_, v___x_2684_, v___x_2670_, v_a_2504_);
lean_dec(v_a_2667_);
if (lean_obj_tag(v___x_2685_) == 0)
{
lean_dec_ref_known(v___x_2685_, 1);
v___y_2652_ = v___y_2658_;
v_a_2653_ = v_a_2666_;
goto v___jp_2651_;
}
else
{
lean_object* v_a_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2693_; 
lean_dec(v_a_2666_);
lean_dec_ref(v___y_2658_);
lean_del_object(v___x_2523_);
lean_dec_ref(v_scope_2521_);
lean_dec(v_name_2520_);
lean_dec(v_subDir_x3f_2514_);
lean_dec(v_inputRev_x3f_2513_);
lean_dec_ref(v_remoteUrl_2512_);
lean_dec_ref(v_relPkgDir_2510_);
lean_dec_ref(v_name_2509_);
lean_dec_ref(v_wsDir_2508_);
v_a_2686_ = lean_ctor_get(v___x_2685_, 0);
v_isSharedCheck_2693_ = !lean_is_exclusive(v___x_2685_);
if (v_isSharedCheck_2693_ == 0)
{
v___x_2688_ = v___x_2685_;
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
else
{
lean_inc(v_a_2686_);
lean_dec(v___x_2685_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v___x_2691_; 
if (v_isShared_2689_ == 0)
{
v___x_2691_ = v___x_2688_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_a_2686_);
v___x_2691_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
return v___x_2691_;
}
}
}
}
}
}
else
{
lean_object* v_a_2694_; lean_object* v___x_2695_; uint8_t v___x_2696_; 
lean_dec_ref(v___y_2658_);
lean_del_object(v___x_2523_);
lean_dec_ref(v_scope_2521_);
lean_dec(v_name_2520_);
lean_dec(v_subDir_x3f_2514_);
lean_dec(v_inputRev_x3f_2513_);
lean_dec_ref(v_remoteUrl_2512_);
lean_dec_ref(v_relPkgDir_2510_);
lean_dec_ref(v_name_2509_);
lean_dec_ref(v_wsDir_2508_);
v_a_2694_ = lean_ctor_get(v___x_2665_, 1);
lean_inc(v_a_2694_);
lean_dec_ref_known(v___x_2665_, 2);
v___x_2695_ = lean_array_get_size(v_a_2694_);
v___x_2696_ = lean_nat_dec_lt(v___x_2663_, v___x_2695_);
if (v___x_2696_ == 0)
{
lean_object* v___x_2697_; lean_object* v___x_2699_; 
lean_dec(v_a_2694_);
v___x_2697_ = lean_box(0);
if (v_isShared_2662_ == 0)
{
lean_ctor_set_tag(v___x_2661_, 1);
lean_ctor_set(v___x_2661_, 0, v___x_2697_);
v___x_2699_ = v___x_2661_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v___x_2697_);
v___x_2699_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
return v___x_2699_;
}
}
else
{
lean_object* v___x_2701_; uint8_t v___x_2702_; 
lean_del_object(v___x_2661_);
v___x_2701_ = lean_box(0);
v___x_2702_ = lean_nat_dec_le(v___x_2695_, v___x_2695_);
if (v___x_2702_ == 0)
{
if (v___x_2696_ == 0)
{
lean_dec(v_a_2694_);
goto v___jp_2516_;
}
else
{
size_t v___x_2703_; size_t v___x_2704_; lean_object* v___x_2705_; 
v___x_2703_ = ((size_t)0ULL);
v___x_2704_ = lean_usize_of_nat(v___x_2695_);
v___x_2705_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_2694_, v___x_2703_, v___x_2704_, v___x_2701_, v_a_2504_);
lean_dec(v_a_2694_);
if (lean_obj_tag(v___x_2705_) == 0)
{
lean_dec_ref_known(v___x_2705_, 1);
goto v___jp_2516_;
}
else
{
lean_object* v_a_2706_; lean_object* v___x_2708_; uint8_t v_isShared_2709_; uint8_t v_isSharedCheck_2713_; 
v_a_2706_ = lean_ctor_get(v___x_2705_, 0);
v_isSharedCheck_2713_ = !lean_is_exclusive(v___x_2705_);
if (v_isSharedCheck_2713_ == 0)
{
v___x_2708_ = v___x_2705_;
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
else
{
lean_inc(v_a_2706_);
lean_dec(v___x_2705_);
v___x_2708_ = lean_box(0);
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
v_resetjp_2707_:
{
lean_object* v___x_2711_; 
if (v_isShared_2709_ == 0)
{
v___x_2711_ = v___x_2708_;
goto v_reusejp_2710_;
}
else
{
lean_object* v_reuseFailAlloc_2712_; 
v_reuseFailAlloc_2712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2712_, 0, v_a_2706_);
v___x_2711_ = v_reuseFailAlloc_2712_;
goto v_reusejp_2710_;
}
v_reusejp_2710_:
{
return v___x_2711_;
}
}
}
}
}
else
{
size_t v___x_2714_; size_t v___x_2715_; lean_object* v___x_2716_; 
v___x_2714_ = ((size_t)0ULL);
v___x_2715_ = lean_usize_of_nat(v___x_2695_);
v___x_2716_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_2694_, v___x_2714_, v___x_2715_, v___x_2701_, v_a_2504_);
lean_dec(v_a_2694_);
if (lean_obj_tag(v___x_2716_) == 0)
{
lean_dec_ref_known(v___x_2716_, 1);
goto v___jp_2516_;
}
else
{
lean_object* v_a_2717_; lean_object* v___x_2719_; uint8_t v_isShared_2720_; uint8_t v_isSharedCheck_2724_; 
v_a_2717_ = lean_ctor_get(v___x_2716_, 0);
v_isSharedCheck_2724_ = !lean_is_exclusive(v___x_2716_);
if (v_isSharedCheck_2724_ == 0)
{
v___x_2719_ = v___x_2716_;
v_isShared_2720_ = v_isSharedCheck_2724_;
goto v_resetjp_2718_;
}
else
{
lean_inc(v_a_2717_);
lean_dec(v___x_2716_);
v___x_2719_ = lean_box(0);
v_isShared_2720_ = v_isSharedCheck_2724_;
goto v_resetjp_2718_;
}
v_resetjp_2718_:
{
lean_object* v___x_2722_; 
if (v_isShared_2720_ == 0)
{
v___x_2722_ = v___x_2719_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v_a_2717_);
v___x_2722_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
return v___x_2722_;
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
lean_object* v_a_2727_; lean_object* v___x_2729_; uint8_t v_isShared_2730_; uint8_t v_isSharedCheck_2734_; 
lean_dec_ref(v___y_2658_);
lean_dec_ref(v_gitDir_2656_);
lean_del_object(v___x_2523_);
lean_dec_ref(v_scope_2521_);
lean_dec(v_name_2520_);
lean_dec(v_subDir_x3f_2514_);
lean_dec(v_inputRev_x3f_2513_);
lean_dec_ref(v_remoteUrl_2512_);
lean_dec_ref(v_relPkgDir_2510_);
lean_dec_ref(v_name_2509_);
lean_dec_ref(v_wsDir_2508_);
v_a_2727_ = lean_ctor_get(v___x_2659_, 0);
v_isSharedCheck_2734_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_2734_ == 0)
{
v___x_2729_ = v___x_2659_;
v_isShared_2730_ = v_isSharedCheck_2734_;
goto v_resetjp_2728_;
}
else
{
lean_inc(v_a_2727_);
lean_dec(v___x_2659_);
v___x_2729_ = lean_box(0);
v_isShared_2730_ = v_isSharedCheck_2734_;
goto v_resetjp_2728_;
}
v_resetjp_2728_:
{
lean_object* v___x_2732_; 
if (v_isShared_2730_ == 0)
{
v___x_2732_ = v___x_2729_;
goto v_reusejp_2731_;
}
else
{
lean_object* v_reuseFailAlloc_2733_; 
v_reuseFailAlloc_2733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2733_, 0, v_a_2727_);
v___x_2732_ = v_reuseFailAlloc_2733_;
goto v_reusejp_2731_;
}
v_reusejp_2731_:
{
return v___x_2732_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0___boxed(lean_object* v_a_2741_, lean_object* v_dep_2742_, lean_object* v_inherited_2743_, lean_object* v_lakeEnv_2744_, lean_object* v_wsDir_2745_, lean_object* v_name_2746_, lean_object* v_relPkgDir_2747_, lean_object* v_gitUrl_2748_, lean_object* v_remoteUrl_2749_, lean_object* v_inputRev_x3f_2750_, lean_object* v_subDir_x3f_2751_, lean_object* v_a_2752_){
_start:
{
uint8_t v_inherited_boxed_2753_; lean_object* v_res_2754_; 
v_inherited_boxed_2753_ = lean_unbox(v_inherited_2743_);
v_res_2754_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(v_a_2741_, v_dep_2742_, v_inherited_boxed_2753_, v_lakeEnv_2744_, v_wsDir_2745_, v_name_2746_, v_relPkgDir_2747_, v_gitUrl_2748_, v_remoteUrl_2749_, v_inputRev_x3f_2750_, v_subDir_x3f_2751_);
lean_dec_ref(v_lakeEnv_2744_);
lean_dec_ref(v_a_2741_);
return v_res_2754_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(lean_object* v_ver_2758_, lean_object* v_as_2759_, size_t v_sz_2760_, size_t v_i_2761_, lean_object* v_b_2762_){
_start:
{
uint8_t v___x_2763_; 
v___x_2763_ = lean_usize_dec_lt(v_i_2761_, v_sz_2760_);
if (v___x_2763_ == 0)
{
lean_inc_ref(v_b_2762_);
return v_b_2762_;
}
else
{
lean_object* v_a_2764_; lean_object* v_version_2765_; lean_object* v___x_2766_; uint8_t v___x_2767_; 
v_a_2764_ = lean_array_uget_borrowed(v_as_2759_, v_i_2761_);
v_version_2765_ = lean_ctor_get(v_a_2764_, 0);
v___x_2766_ = lean_box(0);
v___x_2767_ = l_Lake_VerRange_test(v_ver_2758_, v_version_2765_);
if (v___x_2767_ == 0)
{
lean_object* v___x_2768_; size_t v___x_2769_; size_t v___x_2770_; 
v___x_2768_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___closed__0));
v___x_2769_ = ((size_t)1ULL);
v___x_2770_ = lean_usize_add(v_i_2761_, v___x_2769_);
v_i_2761_ = v___x_2770_;
v_b_2762_ = v___x_2768_;
goto _start;
}
else
{
lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; 
lean_inc(v_a_2764_);
v___x_2772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2772_, 0, v_a_2764_);
v___x_2773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2773_, 0, v___x_2772_);
v___x_2774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2774_, 0, v___x_2773_);
lean_ctor_set(v___x_2774_, 1, v___x_2766_);
return v___x_2774_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___boxed(lean_object* v_ver_2775_, lean_object* v_as_2776_, lean_object* v_sz_2777_, lean_object* v_i_2778_, lean_object* v_b_2779_){
_start:
{
size_t v_sz_boxed_2780_; size_t v_i_boxed_2781_; lean_object* v_res_2782_; 
v_sz_boxed_2780_ = lean_unbox_usize(v_sz_2777_);
lean_dec(v_sz_2777_);
v_i_boxed_2781_ = lean_unbox_usize(v_i_2778_);
lean_dec(v_i_2778_);
v_res_2782_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(v_ver_2775_, v_as_2776_, v_sz_boxed_2780_, v_i_boxed_2781_, v_b_2779_);
lean_dec_ref(v_b_2779_);
lean_dec_ref(v_as_2776_);
lean_dec_ref(v_ver_2775_);
return v_res_2782_;
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize(lean_object* v_dep_2792_, uint8_t v_inherited_2793_, lean_object* v_lakeEnv_2794_, lean_object* v_wsDir_2795_, lean_object* v_relPkgsDir_2796_, lean_object* v_relParentDir_2797_, lean_object* v_a_2798_){
_start:
{
lean_object* v___y_2804_; lean_object* v___y_2805_; lean_object* v___y_2815_; lean_object* v___y_2816_; lean_object* v___y_2817_; lean_object* v___y_2818_; lean_object* v___y_2819_; lean_object* v___y_2820_; lean_object* v___y_2824_; lean_object* v___y_2825_; lean_object* v___y_2826_; lean_object* v___y_2827_; lean_object* v___y_2828_; lean_object* v_a_2829_; lean_object* v_src_x3f_2832_; 
v_src_x3f_2832_ = lean_ctor_get(v_dep_2792_, 3);
lean_inc(v_src_x3f_2832_);
if (lean_obj_tag(v_src_x3f_2832_) == 1)
{
lean_object* v_val_2833_; lean_object* v___x_2835_; uint8_t v_isShared_2836_; uint8_t v_isSharedCheck_2981_; 
v_val_2833_ = lean_ctor_get(v_src_x3f_2832_, 0);
v_isSharedCheck_2981_ = !lean_is_exclusive(v_src_x3f_2832_);
if (v_isSharedCheck_2981_ == 0)
{
v___x_2835_ = v_src_x3f_2832_;
v_isShared_2836_ = v_isSharedCheck_2981_;
goto v_resetjp_2834_;
}
else
{
lean_inc(v_val_2833_);
lean_dec(v_src_x3f_2832_);
v___x_2835_ = lean_box(0);
v_isShared_2836_ = v_isSharedCheck_2981_;
goto v_resetjp_2834_;
}
v_resetjp_2834_:
{
if (lean_obj_tag(v_val_2833_) == 0)
{
lean_object* v_name_2837_; lean_object* v_scope_2838_; lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2964_; 
lean_dec_ref(v_relPkgsDir_2796_);
lean_dec_ref(v_lakeEnv_2794_);
v_name_2837_ = lean_ctor_get(v_dep_2792_, 0);
v_scope_2838_ = lean_ctor_get(v_dep_2792_, 1);
v_isSharedCheck_2964_ = !lean_is_exclusive(v_dep_2792_);
if (v_isSharedCheck_2964_ == 0)
{
lean_object* v_unused_2965_; lean_object* v_unused_2966_; lean_object* v_unused_2967_; 
v_unused_2965_ = lean_ctor_get(v_dep_2792_, 4);
lean_dec(v_unused_2965_);
v_unused_2966_ = lean_ctor_get(v_dep_2792_, 3);
lean_dec(v_unused_2966_);
v_unused_2967_ = lean_ctor_get(v_dep_2792_, 2);
lean_dec(v_unused_2967_);
v___x_2840_ = v_dep_2792_;
v_isShared_2841_ = v_isSharedCheck_2964_;
goto v_resetjp_2839_;
}
else
{
lean_inc(v_scope_2838_);
lean_inc(v_name_2837_);
lean_dec(v_dep_2792_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_2964_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
lean_object* v_dir_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2963_; 
v_dir_2842_ = lean_ctor_get(v_val_2833_, 0);
v_isSharedCheck_2963_ = !lean_is_exclusive(v_val_2833_);
if (v_isSharedCheck_2963_ == 0)
{
v___x_2844_ = v_val_2833_;
v_isShared_2845_ = v_isSharedCheck_2963_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_dir_2842_);
lean_dec(v_val_2833_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_2963_;
goto v_resetjp_2843_;
}
v_resetjp_2843_:
{
lean_object* v_relPkgDir_2846_; lean_object* v___x_2848_; 
v_relPkgDir_2846_ = l_Lake_joinRelative(v_relParentDir_2797_, v_dir_2842_);
lean_inc_ref(v_relPkgDir_2846_);
if (v_isShared_2845_ == 0)
{
lean_ctor_set(v___x_2844_, 0, v_relPkgDir_2846_);
v___x_2848_ = v___x_2844_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2962_; 
v_reuseFailAlloc_2962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2962_, 0, v_relPkgDir_2846_);
v___x_2848_ = v_reuseFailAlloc_2962_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
lean_object* v_pkgDir_2849_; lean_object* v___x_2850_; uint8_t v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___y_2855_; lean_object* v_a_2856_; lean_object* v___y_2865_; lean_object* v___y_2866_; lean_object* v___y_2867_; lean_object* v_val_2868_; lean_object* v_a_2896_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v_val_2930_; lean_object* v___x_2956_; uint8_t v___x_2957_; 
lean_inc_ref(v_relPkgDir_2846_);
v_pkgDir_2849_ = l_Lake_joinRelative(v_wsDir_2795_, v_relPkgDir_2846_);
lean_inc_ref(v_pkgDir_2849_);
v___x_2850_ = l_Lake_resolvePath(v_pkgDir_2849_);
v___x_2851_ = 0;
lean_inc(v_name_2837_);
v___x_2852_ = l_Lean_Name_toString(v_name_2837_, v___x_2851_);
v___x_2853_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___x_2927_ = lean_unsigned_to_nat(0u);
v___x_2928_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_2956_ = lean_string_utf8_byte_size(v___x_2850_);
v___x_2957_ = lean_nat_dec_eq(v___x_2956_, v___x_2927_);
if (v___x_2957_ == 0)
{
lean_object* v___x_2959_; 
if (v_isShared_2836_ == 0)
{
lean_ctor_set(v___x_2835_, 0, v___x_2850_);
v___x_2959_ = v___x_2835_;
goto v_reusejp_2958_;
}
else
{
lean_object* v_reuseFailAlloc_2960_; 
v_reuseFailAlloc_2960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2960_, 0, v___x_2850_);
v___x_2959_ = v_reuseFailAlloc_2960_;
goto v_reusejp_2958_;
}
v_reusejp_2958_:
{
v_val_2930_ = v___x_2959_;
goto v___jp_2929_;
}
}
else
{
lean_object* v___x_2961_; 
lean_dec_ref(v___x_2850_);
lean_del_object(v___x_2835_);
v___x_2961_ = lean_box(0);
v_val_2930_ = v___x_2961_;
goto v___jp_2929_;
}
v___jp_2854_:
{
lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2861_; 
v___x_2857_ = l_Lake_defaultConfigFile;
v___x_2858_ = lean_box(0);
v___x_2859_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_2859_, 0, v_name_2837_);
lean_ctor_set(v___x_2859_, 1, v_scope_2838_);
lean_ctor_set(v___x_2859_, 2, v___x_2857_);
lean_ctor_set(v___x_2859_, 3, v___x_2858_);
lean_ctor_set(v___x_2859_, 4, v___x_2848_);
lean_ctor_set_uint8(v___x_2859_, sizeof(void*)*5, v_inherited_2793_);
if (v_isShared_2841_ == 0)
{
lean_ctor_set(v___x_2840_, 4, v___x_2859_);
lean_ctor_set(v___x_2840_, 3, v_a_2856_);
lean_ctor_set(v___x_2840_, 2, v___x_2853_);
lean_ctor_set(v___x_2840_, 1, v_relPkgDir_2846_);
lean_ctor_set(v___x_2840_, 0, v___y_2855_);
v___x_2861_ = v___x_2840_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2863_; 
v_reuseFailAlloc_2863_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2863_, 0, v___y_2855_);
lean_ctor_set(v_reuseFailAlloc_2863_, 1, v_relPkgDir_2846_);
lean_ctor_set(v_reuseFailAlloc_2863_, 2, v___x_2853_);
lean_ctor_set(v_reuseFailAlloc_2863_, 3, v_a_2856_);
lean_ctor_set(v_reuseFailAlloc_2863_, 4, v___x_2859_);
v___x_2861_ = v_reuseFailAlloc_2863_;
goto v_reusejp_2860_;
}
v_reusejp_2860_:
{
lean_object* v___x_2862_; 
v___x_2862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2862_, 0, v___x_2861_);
return v___x_2862_;
}
}
v___jp_2864_:
{
lean_object* v___x_2869_; uint8_t v___x_2870_; 
v___x_2869_ = lean_array_get_size(v___y_2867_);
v___x_2870_ = lean_nat_dec_lt(v___y_2865_, v___x_2869_);
if (v___x_2870_ == 0)
{
v___y_2855_ = v___y_2866_;
v_a_2856_ = v_val_2868_;
goto v___jp_2854_;
}
else
{
lean_object* v___x_2871_; uint8_t v___x_2872_; 
v___x_2871_ = lean_box(0);
v___x_2872_ = lean_nat_dec_le(v___x_2869_, v___x_2869_);
if (v___x_2872_ == 0)
{
if (v___x_2870_ == 0)
{
v___y_2855_ = v___y_2866_;
v_a_2856_ = v_val_2868_;
goto v___jp_2854_;
}
else
{
size_t v___x_2873_; size_t v___x_2874_; lean_object* v___x_2875_; 
v___x_2873_ = ((size_t)0ULL);
v___x_2874_ = lean_usize_of_nat(v___x_2869_);
v___x_2875_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_2867_, v___x_2873_, v___x_2874_, v___x_2871_, v_a_2798_);
if (lean_obj_tag(v___x_2875_) == 0)
{
lean_dec_ref_known(v___x_2875_, 1);
v___y_2855_ = v___y_2866_;
v_a_2856_ = v_val_2868_;
goto v___jp_2854_;
}
else
{
lean_object* v_a_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2883_; 
lean_dec_ref(v_val_2868_);
lean_dec_ref(v___y_2866_);
lean_dec_ref(v___x_2848_);
lean_dec_ref(v_relPkgDir_2846_);
lean_del_object(v___x_2840_);
lean_dec_ref(v_scope_2838_);
lean_dec(v_name_2837_);
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
else
{
size_t v___x_2884_; size_t v___x_2885_; lean_object* v___x_2886_; 
v___x_2884_ = ((size_t)0ULL);
v___x_2885_ = lean_usize_of_nat(v___x_2869_);
v___x_2886_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_2867_, v___x_2884_, v___x_2885_, v___x_2871_, v_a_2798_);
if (lean_obj_tag(v___x_2886_) == 0)
{
lean_dec_ref_known(v___x_2886_, 1);
v___y_2855_ = v___y_2866_;
v_a_2856_ = v_val_2868_;
goto v___jp_2854_;
}
else
{
lean_object* v_a_2887_; lean_object* v___x_2889_; uint8_t v_isShared_2890_; uint8_t v_isSharedCheck_2894_; 
lean_dec_ref(v_val_2868_);
lean_dec_ref(v___y_2866_);
lean_dec_ref(v___x_2848_);
lean_dec_ref(v_relPkgDir_2846_);
lean_del_object(v___x_2840_);
lean_dec_ref(v_scope_2838_);
lean_dec(v_name_2837_);
v_a_2887_ = lean_ctor_get(v___x_2886_, 0);
v_isSharedCheck_2894_ = !lean_is_exclusive(v___x_2886_);
if (v_isSharedCheck_2894_ == 0)
{
v___x_2889_ = v___x_2886_;
v_isShared_2890_ = v_isSharedCheck_2894_;
goto v_resetjp_2888_;
}
else
{
lean_inc(v_a_2887_);
lean_dec(v___x_2886_);
v___x_2889_ = lean_box(0);
v_isShared_2890_ = v_isSharedCheck_2894_;
goto v_resetjp_2888_;
}
v_resetjp_2888_:
{
lean_object* v___x_2892_; 
if (v_isShared_2890_ == 0)
{
v___x_2892_ = v___x_2889_;
goto v_reusejp_2891_;
}
else
{
lean_object* v_reuseFailAlloc_2893_; 
v_reuseFailAlloc_2893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2893_, 0, v_a_2887_);
v___x_2892_ = v_reuseFailAlloc_2893_;
goto v_reusejp_2891_;
}
v_reusejp_2891_:
{
return v___x_2892_;
}
}
}
}
}
}
v___jp_2895_:
{
if (lean_obj_tag(v_a_2896_) == 1)
{
lean_object* v_val_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; 
lean_dec_ref(v___x_2852_);
lean_dec_ref(v_pkgDir_2849_);
v_val_2897_ = lean_ctor_get(v_a_2896_, 0);
lean_inc_n(v_val_2897_, 2);
lean_dec_ref_known(v_a_2896_, 1);
v___x_2898_ = l_Lake_defaultManifestFile;
v___x_2899_ = l_Lake_joinRelative(v_val_2897_, v___x_2898_);
v___x_2900_ = lean_unsigned_to_nat(0u);
v___x_2901_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_2902_ = l_Lake_Manifest_load(v___x_2899_);
if (lean_obj_tag(v___x_2902_) == 0)
{
lean_object* v_a_2903_; lean_object* v___x_2905_; uint8_t v_isShared_2906_; uint8_t v_isSharedCheck_2910_; 
v_a_2903_ = lean_ctor_get(v___x_2902_, 0);
v_isSharedCheck_2910_ = !lean_is_exclusive(v___x_2902_);
if (v_isSharedCheck_2910_ == 0)
{
v___x_2905_ = v___x_2902_;
v_isShared_2906_ = v_isSharedCheck_2910_;
goto v_resetjp_2904_;
}
else
{
lean_inc(v_a_2903_);
lean_dec(v___x_2902_);
v___x_2905_ = lean_box(0);
v_isShared_2906_ = v_isSharedCheck_2910_;
goto v_resetjp_2904_;
}
v_resetjp_2904_:
{
lean_object* v___x_2908_; 
if (v_isShared_2906_ == 0)
{
lean_ctor_set_tag(v___x_2905_, 1);
v___x_2908_ = v___x_2905_;
goto v_reusejp_2907_;
}
else
{
lean_object* v_reuseFailAlloc_2909_; 
v_reuseFailAlloc_2909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2909_, 0, v_a_2903_);
v___x_2908_ = v_reuseFailAlloc_2909_;
goto v_reusejp_2907_;
}
v_reusejp_2907_:
{
v___y_2865_ = v___x_2900_;
v___y_2866_ = v_val_2897_;
v___y_2867_ = v___x_2901_;
v_val_2868_ = v___x_2908_;
goto v___jp_2864_;
}
}
}
else
{
lean_object* v_a_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2918_; 
v_a_2911_ = lean_ctor_get(v___x_2902_, 0);
v_isSharedCheck_2918_ = !lean_is_exclusive(v___x_2902_);
if (v_isSharedCheck_2918_ == 0)
{
v___x_2913_ = v___x_2902_;
v_isShared_2914_ = v_isSharedCheck_2918_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_a_2911_);
lean_dec(v___x_2902_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_2918_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
lean_object* v___x_2916_; 
if (v_isShared_2914_ == 0)
{
lean_ctor_set_tag(v___x_2913_, 0);
v___x_2916_ = v___x_2913_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v_a_2911_);
v___x_2916_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
v___y_2865_ = v___x_2900_;
v___y_2866_ = v_val_2897_;
v___y_2867_ = v___x_2901_;
v_val_2868_ = v___x_2916_;
goto v___jp_2864_;
}
}
}
}
else
{
lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; uint8_t v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; 
lean_dec(v_a_2896_);
lean_dec_ref(v___x_2848_);
lean_dec_ref(v_relPkgDir_2846_);
lean_del_object(v___x_2840_);
lean_dec_ref(v_scope_2838_);
lean_dec(v_name_2837_);
v___x_2919_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0));
v___x_2920_ = lean_string_append(v___x_2852_, v___x_2919_);
v___x_2921_ = lean_string_append(v___x_2920_, v_pkgDir_2849_);
lean_dec_ref(v_pkgDir_2849_);
v___x_2922_ = 3;
v___x_2923_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2923_, 0, v___x_2921_);
lean_ctor_set_uint8(v___x_2923_, sizeof(void*)*1, v___x_2922_);
lean_inc_ref(v_a_2798_);
v___x_2924_ = lean_apply_2(v_a_2798_, v___x_2923_, lean_box(0));
v___x_2925_ = lean_box(0);
v___x_2926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2926_, 0, v___x_2925_);
return v___x_2926_;
}
}
v___jp_2929_:
{
uint8_t v___x_2931_; 
v___x_2931_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_2931_ == 0)
{
v_a_2896_ = v_val_2930_;
goto v___jp_2895_;
}
else
{
lean_object* v___x_2932_; uint8_t v___x_2933_; 
v___x_2932_ = lean_box(0);
v___x_2933_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
if (v___x_2933_ == 0)
{
if (v___x_2931_ == 0)
{
v_a_2896_ = v_val_2930_;
goto v___jp_2895_;
}
else
{
size_t v___x_2934_; size_t v___x_2935_; lean_object* v___x_2936_; 
v___x_2934_ = ((size_t)0ULL);
v___x_2935_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8);
v___x_2936_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_2928_, v___x_2934_, v___x_2935_, v___x_2932_, v_a_2798_);
if (lean_obj_tag(v___x_2936_) == 0)
{
lean_dec_ref_known(v___x_2936_, 1);
v_a_2896_ = v_val_2930_;
goto v___jp_2895_;
}
else
{
lean_object* v_a_2937_; lean_object* v___x_2939_; uint8_t v_isShared_2940_; uint8_t v_isSharedCheck_2944_; 
lean_dec(v_val_2930_);
lean_dec_ref(v___x_2852_);
lean_dec_ref(v_pkgDir_2849_);
lean_dec_ref(v___x_2848_);
lean_dec_ref(v_relPkgDir_2846_);
lean_del_object(v___x_2840_);
lean_dec_ref(v_scope_2838_);
lean_dec(v_name_2837_);
v_a_2937_ = lean_ctor_get(v___x_2936_, 0);
v_isSharedCheck_2944_ = !lean_is_exclusive(v___x_2936_);
if (v_isSharedCheck_2944_ == 0)
{
v___x_2939_ = v___x_2936_;
v_isShared_2940_ = v_isSharedCheck_2944_;
goto v_resetjp_2938_;
}
else
{
lean_inc(v_a_2937_);
lean_dec(v___x_2936_);
v___x_2939_ = lean_box(0);
v_isShared_2940_ = v_isSharedCheck_2944_;
goto v_resetjp_2938_;
}
v_resetjp_2938_:
{
lean_object* v___x_2942_; 
if (v_isShared_2940_ == 0)
{
v___x_2942_ = v___x_2939_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v_a_2937_);
v___x_2942_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
return v___x_2942_;
}
}
}
}
}
else
{
size_t v___x_2945_; size_t v___x_2946_; lean_object* v___x_2947_; 
v___x_2945_ = ((size_t)0ULL);
v___x_2946_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8);
v___x_2947_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_2928_, v___x_2945_, v___x_2946_, v___x_2932_, v_a_2798_);
if (lean_obj_tag(v___x_2947_) == 0)
{
lean_dec_ref_known(v___x_2947_, 1);
v_a_2896_ = v_val_2930_;
goto v___jp_2895_;
}
else
{
lean_object* v_a_2948_; lean_object* v___x_2950_; uint8_t v_isShared_2951_; uint8_t v_isSharedCheck_2955_; 
lean_dec(v_val_2930_);
lean_dec_ref(v___x_2852_);
lean_dec_ref(v_pkgDir_2849_);
lean_dec_ref(v___x_2848_);
lean_dec_ref(v_relPkgDir_2846_);
lean_del_object(v___x_2840_);
lean_dec_ref(v_scope_2838_);
lean_dec(v_name_2837_);
v_a_2948_ = lean_ctor_get(v___x_2947_, 0);
v_isSharedCheck_2955_ = !lean_is_exclusive(v___x_2947_);
if (v_isSharedCheck_2955_ == 0)
{
v___x_2950_ = v___x_2947_;
v_isShared_2951_ = v_isSharedCheck_2955_;
goto v_resetjp_2949_;
}
else
{
lean_inc(v_a_2948_);
lean_dec(v___x_2947_);
v___x_2950_ = lean_box(0);
v_isShared_2951_ = v_isSharedCheck_2955_;
goto v_resetjp_2949_;
}
v_resetjp_2949_:
{
lean_object* v___x_2953_; 
if (v_isShared_2951_ == 0)
{
v___x_2953_ = v___x_2950_;
goto v_reusejp_2952_;
}
else
{
lean_object* v_reuseFailAlloc_2954_; 
v_reuseFailAlloc_2954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2954_, 0, v_a_2948_);
v___x_2953_ = v_reuseFailAlloc_2954_;
goto v_reusejp_2952_;
}
v_reusejp_2952_:
{
return v___x_2953_;
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
lean_object* v_name_2968_; lean_object* v_url_2969_; lean_object* v_rev_2970_; lean_object* v_subDir_2971_; lean_object* v___y_2973_; lean_object* v___x_2978_; 
lean_del_object(v___x_2835_);
lean_dec_ref(v_relParentDir_2797_);
v_name_2968_ = lean_ctor_get(v_dep_2792_, 0);
v_url_2969_ = lean_ctor_get(v_val_2833_, 0);
lean_inc_ref_n(v_url_2969_, 2);
v_rev_2970_ = lean_ctor_get(v_val_2833_, 1);
lean_inc(v_rev_2970_);
v_subDir_2971_ = lean_ctor_get(v_val_2833_, 2);
lean_inc(v_subDir_2971_);
lean_dec_ref_known(v_val_2833_, 3);
v___x_2978_ = l_Lake_Git_filterUrl_x3f(v_url_2969_);
if (lean_obj_tag(v___x_2978_) == 0)
{
lean_object* v___x_2979_; 
v___x_2979_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___y_2973_ = v___x_2979_;
goto v___jp_2972_;
}
else
{
lean_object* v_val_2980_; 
v_val_2980_ = lean_ctor_get(v___x_2978_, 0);
lean_inc(v_val_2980_);
lean_dec_ref_known(v___x_2978_, 1);
v___y_2973_ = v_val_2980_;
goto v___jp_2972_;
}
v___jp_2972_:
{
uint8_t v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; 
v___x_2974_ = 0;
lean_inc(v_name_2968_);
v___x_2975_ = l_Lean_Name_toString(v_name_2968_, v___x_2974_);
lean_inc_ref(v___x_2975_);
v___x_2976_ = l_Lake_joinRelative(v_relPkgsDir_2796_, v___x_2975_);
v___x_2977_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(v_a_2798_, v_dep_2792_, v_inherited_2793_, v_lakeEnv_2794_, v_wsDir_2795_, v___x_2975_, v___x_2976_, v_url_2969_, v___y_2973_, v_rev_2970_, v_subDir_2971_);
lean_dec_ref(v_lakeEnv_2794_);
return v___x_2977_;
}
}
}
}
else
{
lean_object* v_name_2982_; lean_object* v_scope_2983_; lean_object* v_version_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; uint8_t v___x_2987_; 
lean_dec(v_src_x3f_2832_);
lean_dec_ref(v_relParentDir_2797_);
v_name_2982_ = lean_ctor_get(v_dep_2792_, 0);
v_scope_2983_ = lean_ctor_get(v_dep_2792_, 1);
v_version_2984_ = lean_ctor_get(v_dep_2792_, 2);
v___x_2985_ = lean_string_utf8_byte_size(v_scope_2983_);
v___x_2986_ = lean_unsigned_to_nat(0u);
v___x_2987_ = lean_nat_dec_eq(v___x_2985_, v___x_2986_);
if (v___x_2987_ == 0)
{
lean_object* v___x_2988_; lean_object* v___y_2990_; lean_object* v___y_3006_; lean_object* v___y_3007_; lean_object* v___y_3008_; lean_object* v___y_3009_; lean_object* v___y_3010_; lean_object* v___y_3011_; lean_object* v_a_3012_; lean_object* v___y_3056_; lean_object* v___y_3057_; lean_object* v___y_3058_; lean_object* v___y_3059_; lean_object* v___y_3060_; lean_object* v___y_3061_; lean_object* v_fst_3062_; lean_object* v_snd_3063_; lean_object* v_a_3091_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v_fst_3226_; lean_object* v_snd_3227_; 
lean_inc(v_name_2982_);
v___x_2988_ = l_Lean_Name_toString(v_name_2982_, v___x_2987_);
v___x_3223_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v___x_2988_);
lean_inc_ref(v_scope_2983_);
lean_inc_ref(v_lakeEnv_2794_);
v___x_3224_ = l_Lake_Reservoir_fetchPkg_x3f(v_lakeEnv_2794_, v_scope_2983_, v___x_2988_, v___x_3223_);
if (lean_obj_tag(v___x_3224_) == 0)
{
lean_object* v_a_3254_; lean_object* v_a_3255_; lean_object* v___x_3256_; 
v_a_3254_ = lean_ctor_get(v___x_3224_, 0);
lean_inc(v_a_3254_);
v_a_3255_ = lean_ctor_get(v___x_3224_, 1);
lean_inc(v_a_3255_);
lean_dec_ref_known(v___x_3224_, 2);
v___x_3256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3256_, 0, v_a_3254_);
v_fst_3226_ = v___x_3256_;
v_snd_3227_ = v_a_3255_;
goto v___jp_3225_;
}
else
{
lean_object* v_a_3257_; lean_object* v_a_3258_; lean_object* v___x_3259_; 
v_a_3257_ = lean_ctor_get(v___x_3224_, 0);
lean_inc(v_a_3257_);
v_a_3258_ = lean_ctor_get(v___x_3224_, 1);
lean_inc(v_a_3258_);
lean_dec_ref_known(v___x_3224_, 2);
v___x_3259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3259_, 0, v_a_3257_);
v_fst_3226_ = v___x_3259_;
v_snd_3227_ = v_a_3258_;
goto v___jp_3225_;
}
v___jp_2989_:
{
lean_object* v_toString_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; uint8_t v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; 
v_toString_2991_ = lean_ctor_get(v___y_2990_, 0);
lean_inc_ref(v_toString_2991_);
lean_dec_ref(v___y_2990_);
v___x_2992_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
v___x_2993_ = lean_string_append(v_scope_2983_, v___x_2992_);
v___x_2994_ = lean_string_append(v___x_2993_, v___x_2988_);
lean_dec_ref(v___x_2988_);
v___x_2995_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__1));
v___x_2996_ = lean_string_append(v___x_2994_, v___x_2995_);
v___x_2997_ = lean_string_append(v___x_2996_, v_toString_2991_);
lean_dec_ref(v_toString_2991_);
v___x_2998_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__2));
v___x_2999_ = lean_string_append(v___x_2997_, v___x_2998_);
v___x_3000_ = 3;
v___x_3001_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3001_, 0, v___x_2999_);
lean_ctor_set_uint8(v___x_3001_, sizeof(void*)*1, v___x_3000_);
lean_inc_ref(v_a_2798_);
v___x_3002_ = lean_apply_2(v_a_2798_, v___x_3001_, lean_box(0));
v___x_3003_ = lean_box(0);
v___x_3004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3004_, 0, v___x_3003_);
return v___x_3004_;
}
v___jp_3005_:
{
if (lean_obj_tag(v_a_3012_) == 0)
{
lean_object* v___x_3014_; uint8_t v_isShared_3015_; uint8_t v_isSharedCheck_3028_; 
lean_inc_ref(v_scope_2983_);
lean_dec(v___y_3011_);
lean_dec_ref(v___y_3010_);
lean_dec_ref(v___y_3009_);
lean_dec(v___y_3008_);
lean_dec_ref(v___y_3007_);
lean_dec_ref(v___y_3006_);
lean_dec_ref(v_wsDir_2795_);
lean_dec_ref(v_lakeEnv_2794_);
lean_dec_ref(v_dep_2792_);
v_isSharedCheck_3028_ = !lean_is_exclusive(v_a_3012_);
if (v_isSharedCheck_3028_ == 0)
{
lean_object* v_unused_3029_; 
v_unused_3029_ = lean_ctor_get(v_a_3012_, 0);
lean_dec(v_unused_3029_);
v___x_3014_ = v_a_3012_;
v_isShared_3015_ = v_isSharedCheck_3028_;
goto v_resetjp_3013_;
}
else
{
lean_dec(v_a_3012_);
v___x_3014_ = lean_box(0);
v_isShared_3015_ = v_isSharedCheck_3028_;
goto v_resetjp_3013_;
}
v_resetjp_3013_:
{
lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; uint8_t v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3026_; 
v___x_3016_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
v___x_3017_ = lean_string_append(v_scope_2983_, v___x_3016_);
v___x_3018_ = lean_string_append(v___x_3017_, v___x_2988_);
lean_dec_ref(v___x_2988_);
v___x_3019_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__3));
v___x_3020_ = lean_string_append(v___x_3018_, v___x_3019_);
v___x_3021_ = 3;
v___x_3022_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3022_, 0, v___x_3020_);
lean_ctor_set_uint8(v___x_3022_, sizeof(void*)*1, v___x_3021_);
lean_inc_ref(v_a_2798_);
v___x_3023_ = lean_apply_2(v_a_2798_, v___x_3022_, lean_box(0));
v___x_3024_ = lean_box(0);
if (v_isShared_3015_ == 0)
{
lean_ctor_set_tag(v___x_3014_, 1);
lean_ctor_set(v___x_3014_, 0, v___x_3024_);
v___x_3026_ = v___x_3014_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3027_; 
v_reuseFailAlloc_3027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3027_, 0, v___x_3024_);
v___x_3026_ = v_reuseFailAlloc_3027_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
return v___x_3026_;
}
}
}
else
{
lean_object* v_a_3030_; lean_object* v___x_3031_; size_t v_sz_3032_; size_t v___x_3033_; lean_object* v___x_3034_; lean_object* v_fst_3035_; 
v_a_3030_ = lean_ctor_get(v_a_3012_, 0);
lean_inc(v_a_3030_);
lean_dec_ref_known(v_a_3012_, 1);
v___x_3031_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___closed__0));
v_sz_3032_ = lean_array_size(v_a_3030_);
v___x_3033_ = ((size_t)0ULL);
v___x_3034_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(v___y_3007_, v_a_3030_, v_sz_3032_, v___x_3033_, v___x_3031_);
lean_dec(v_a_3030_);
v_fst_3035_ = lean_ctor_get(v___x_3034_, 0);
lean_inc(v_fst_3035_);
lean_dec_ref(v___x_3034_);
if (lean_obj_tag(v_fst_3035_) == 0)
{
lean_inc_ref(v_scope_2983_);
lean_dec(v___y_3011_);
lean_dec_ref(v___y_3010_);
lean_dec_ref(v___y_3009_);
lean_dec(v___y_3008_);
lean_dec_ref(v___y_3006_);
lean_dec_ref(v_wsDir_2795_);
lean_dec_ref(v_lakeEnv_2794_);
lean_dec_ref(v_dep_2792_);
v___y_2990_ = v___y_3007_;
goto v___jp_2989_;
}
else
{
lean_object* v_val_3036_; 
v_val_3036_ = lean_ctor_get(v_fst_3035_, 0);
lean_inc(v_val_3036_);
lean_dec_ref_known(v_fst_3035_, 1);
if (lean_obj_tag(v_val_3036_) == 1)
{
lean_object* v_val_3037_; lean_object* v_version_3038_; lean_object* v_revision_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; uint8_t v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; 
lean_dec_ref(v___y_3007_);
v_val_3037_ = lean_ctor_get(v_val_3036_, 0);
lean_inc(v_val_3037_);
lean_dec_ref_known(v_val_3036_, 1);
v_version_3038_ = lean_ctor_get(v_val_3037_, 0);
lean_inc_ref(v_version_3038_);
v_revision_3039_ = lean_ctor_get(v_val_3037_, 1);
lean_inc_ref(v_revision_3039_);
lean_dec(v_val_3037_);
v___x_3040_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
lean_inc_ref(v_scope_2983_);
v___x_3041_ = lean_string_append(v_scope_2983_, v___x_3040_);
v___x_3042_ = lean_string_append(v___x_3041_, v___x_2988_);
lean_dec_ref(v___x_2988_);
v___x_3043_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__4));
v___x_3044_ = lean_string_append(v___x_3042_, v___x_3043_);
v___x_3045_ = l_Lake_StdVer_toString(v_version_3038_);
v___x_3046_ = lean_string_append(v___x_3044_, v___x_3045_);
lean_dec_ref(v___x_3045_);
v___x_3047_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__5));
v___x_3048_ = lean_string_append(v___x_3046_, v___x_3047_);
v___x_3049_ = lean_string_append(v___x_3048_, v_revision_3039_);
v___x_3050_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__6));
v___x_3051_ = lean_string_append(v___x_3049_, v___x_3050_);
v___x_3052_ = 1;
v___x_3053_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3053_, 0, v___x_3051_);
lean_ctor_set_uint8(v___x_3053_, sizeof(void*)*1, v___x_3052_);
lean_inc_ref(v_a_2798_);
v___x_3054_ = lean_apply_2(v_a_2798_, v___x_3053_, lean_box(0));
v___y_2824_ = v___y_3006_;
v___y_2825_ = v___y_3008_;
v___y_2826_ = v___y_3009_;
v___y_2827_ = v___y_3010_;
v___y_2828_ = v___y_3011_;
v_a_2829_ = v_revision_3039_;
goto v___jp_2823_;
}
else
{
lean_inc_ref(v_scope_2983_);
lean_dec(v_val_3036_);
lean_dec(v___y_3011_);
lean_dec_ref(v___y_3010_);
lean_dec_ref(v___y_3009_);
lean_dec(v___y_3008_);
lean_dec_ref(v___y_3006_);
lean_dec_ref(v_wsDir_2795_);
lean_dec_ref(v_lakeEnv_2794_);
lean_dec_ref(v_dep_2792_);
v___y_2990_ = v___y_3007_;
goto v___jp_2989_;
}
}
}
}
v___jp_3055_:
{
lean_object* v___x_3064_; uint8_t v___x_3065_; 
v___x_3064_ = lean_array_get_size(v_snd_3063_);
v___x_3065_ = lean_nat_dec_lt(v___x_2986_, v___x_3064_);
if (v___x_3065_ == 0)
{
lean_dec_ref(v_snd_3063_);
v___y_3006_ = v___y_3057_;
v___y_3007_ = v___y_3056_;
v___y_3008_ = v___y_3058_;
v___y_3009_ = v___y_3059_;
v___y_3010_ = v___y_3060_;
v___y_3011_ = v___y_3061_;
v_a_3012_ = v_fst_3062_;
goto v___jp_3005_;
}
else
{
lean_object* v___x_3066_; uint8_t v___x_3067_; 
v___x_3066_ = lean_box(0);
v___x_3067_ = lean_nat_dec_le(v___x_3064_, v___x_3064_);
if (v___x_3067_ == 0)
{
if (v___x_3065_ == 0)
{
lean_dec_ref(v_snd_3063_);
v___y_3006_ = v___y_3057_;
v___y_3007_ = v___y_3056_;
v___y_3008_ = v___y_3058_;
v___y_3009_ = v___y_3059_;
v___y_3010_ = v___y_3060_;
v___y_3011_ = v___y_3061_;
v_a_3012_ = v_fst_3062_;
goto v___jp_3005_;
}
else
{
size_t v___x_3068_; size_t v___x_3069_; lean_object* v___x_3070_; 
v___x_3068_ = ((size_t)0ULL);
v___x_3069_ = lean_usize_of_nat(v___x_3064_);
v___x_3070_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_snd_3063_, v___x_3068_, v___x_3069_, v___x_3066_, v_a_2798_);
lean_dec_ref(v_snd_3063_);
if (lean_obj_tag(v___x_3070_) == 0)
{
lean_dec_ref_known(v___x_3070_, 1);
v___y_3006_ = v___y_3057_;
v___y_3007_ = v___y_3056_;
v___y_3008_ = v___y_3058_;
v___y_3009_ = v___y_3059_;
v___y_3010_ = v___y_3060_;
v___y_3011_ = v___y_3061_;
v_a_3012_ = v_fst_3062_;
goto v___jp_3005_;
}
else
{
lean_object* v_a_3071_; lean_object* v___x_3073_; uint8_t v_isShared_3074_; uint8_t v_isSharedCheck_3078_; 
lean_dec_ref(v_fst_3062_);
lean_dec(v___y_3061_);
lean_dec_ref(v___y_3060_);
lean_dec_ref(v___y_3059_);
lean_dec(v___y_3058_);
lean_dec_ref(v___y_3057_);
lean_dec_ref(v___y_3056_);
lean_dec_ref(v___x_2988_);
lean_dec_ref(v_wsDir_2795_);
lean_dec_ref(v_lakeEnv_2794_);
lean_dec_ref(v_dep_2792_);
v_a_3071_ = lean_ctor_get(v___x_3070_, 0);
v_isSharedCheck_3078_ = !lean_is_exclusive(v___x_3070_);
if (v_isSharedCheck_3078_ == 0)
{
v___x_3073_ = v___x_3070_;
v_isShared_3074_ = v_isSharedCheck_3078_;
goto v_resetjp_3072_;
}
else
{
lean_inc(v_a_3071_);
lean_dec(v___x_3070_);
v___x_3073_ = lean_box(0);
v_isShared_3074_ = v_isSharedCheck_3078_;
goto v_resetjp_3072_;
}
v_resetjp_3072_:
{
lean_object* v___x_3076_; 
if (v_isShared_3074_ == 0)
{
v___x_3076_ = v___x_3073_;
goto v_reusejp_3075_;
}
else
{
lean_object* v_reuseFailAlloc_3077_; 
v_reuseFailAlloc_3077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3077_, 0, v_a_3071_);
v___x_3076_ = v_reuseFailAlloc_3077_;
goto v_reusejp_3075_;
}
v_reusejp_3075_:
{
return v___x_3076_;
}
}
}
}
}
else
{
size_t v___x_3079_; size_t v___x_3080_; lean_object* v___x_3081_; 
v___x_3079_ = ((size_t)0ULL);
v___x_3080_ = lean_usize_of_nat(v___x_3064_);
v___x_3081_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_snd_3063_, v___x_3079_, v___x_3080_, v___x_3066_, v_a_2798_);
lean_dec_ref(v_snd_3063_);
if (lean_obj_tag(v___x_3081_) == 0)
{
lean_dec_ref_known(v___x_3081_, 1);
v___y_3006_ = v___y_3057_;
v___y_3007_ = v___y_3056_;
v___y_3008_ = v___y_3058_;
v___y_3009_ = v___y_3059_;
v___y_3010_ = v___y_3060_;
v___y_3011_ = v___y_3061_;
v_a_3012_ = v_fst_3062_;
goto v___jp_3005_;
}
else
{
lean_object* v_a_3082_; lean_object* v___x_3084_; uint8_t v_isShared_3085_; uint8_t v_isSharedCheck_3089_; 
lean_dec_ref(v_fst_3062_);
lean_dec(v___y_3061_);
lean_dec_ref(v___y_3060_);
lean_dec_ref(v___y_3059_);
lean_dec(v___y_3058_);
lean_dec_ref(v___y_3057_);
lean_dec_ref(v___y_3056_);
lean_dec_ref(v___x_2988_);
lean_dec_ref(v_wsDir_2795_);
lean_dec_ref(v_lakeEnv_2794_);
lean_dec_ref(v_dep_2792_);
v_a_3082_ = lean_ctor_get(v___x_3081_, 0);
v_isSharedCheck_3089_ = !lean_is_exclusive(v___x_3081_);
if (v_isSharedCheck_3089_ == 0)
{
v___x_3084_ = v___x_3081_;
v_isShared_3085_ = v_isSharedCheck_3089_;
goto v_resetjp_3083_;
}
else
{
lean_inc(v_a_3082_);
lean_dec(v___x_3081_);
v___x_3084_ = lean_box(0);
v_isShared_3085_ = v_isSharedCheck_3089_;
goto v_resetjp_3083_;
}
v_resetjp_3083_:
{
lean_object* v___x_3087_; 
if (v_isShared_3085_ == 0)
{
v___x_3087_ = v___x_3084_;
goto v_reusejp_3086_;
}
else
{
lean_object* v_reuseFailAlloc_3088_; 
v_reuseFailAlloc_3088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3088_, 0, v_a_3082_);
v___x_3087_ = v_reuseFailAlloc_3088_;
goto v_reusejp_3086_;
}
v_reusejp_3086_:
{
return v___x_3087_;
}
}
}
}
}
}
v___jp_3090_:
{
if (lean_obj_tag(v_a_3091_) == 0)
{
lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; uint8_t v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; 
lean_inc_ref(v_scope_2983_);
lean_dec_ref_known(v_a_3091_, 1);
lean_dec_ref(v_relPkgsDir_2796_);
lean_dec_ref(v_wsDir_2795_);
lean_dec_ref(v_lakeEnv_2794_);
lean_dec_ref(v_dep_2792_);
v___x_3092_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
v___x_3093_ = lean_string_append(v_scope_2983_, v___x_3092_);
v___x_3094_ = lean_string_append(v___x_3093_, v___x_2988_);
lean_dec_ref(v___x_2988_);
v___x_3095_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__7));
v___x_3096_ = lean_string_append(v___x_3094_, v___x_3095_);
v___x_3097_ = 3;
v___x_3098_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3098_, 0, v___x_3096_);
lean_ctor_set_uint8(v___x_3098_, sizeof(void*)*1, v___x_3097_);
lean_inc_ref(v_a_2798_);
v___x_3099_ = lean_apply_2(v_a_2798_, v___x_3098_, lean_box(0));
v___x_3100_ = lean_box(0);
v___x_3101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3101_, 0, v___x_3100_);
return v___x_3101_;
}
else
{
lean_object* v_a_3102_; lean_object* v___x_3104_; uint8_t v_isShared_3105_; uint8_t v_isSharedCheck_3222_; 
v_a_3102_ = lean_ctor_get(v_a_3091_, 0);
v_isSharedCheck_3222_ = !lean_is_exclusive(v_a_3091_);
if (v_isSharedCheck_3222_ == 0)
{
v___x_3104_ = v_a_3091_;
v_isShared_3105_ = v_isSharedCheck_3222_;
goto v_resetjp_3103_;
}
else
{
lean_inc(v_a_3102_);
lean_dec(v_a_3091_);
v___x_3104_ = lean_box(0);
v_isShared_3105_ = v_isSharedCheck_3222_;
goto v_resetjp_3103_;
}
v_resetjp_3103_:
{
if (lean_obj_tag(v_a_3102_) == 0)
{
lean_object* v___x_3106_; uint8_t v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; 
lean_del_object(v___x_3104_);
lean_dec_ref(v___x_2988_);
lean_dec_ref(v_relPkgsDir_2796_);
lean_dec_ref(v_wsDir_2795_);
lean_dec_ref(v_lakeEnv_2794_);
v___x_3106_ = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed(v_dep_2792_);
v___x_3107_ = 3;
v___x_3108_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3108_, 0, v___x_3106_);
lean_ctor_set_uint8(v___x_3108_, sizeof(void*)*1, v___x_3107_);
lean_inc_ref(v_a_2798_);
v___x_3109_ = lean_apply_2(v_a_2798_, v___x_3108_, lean_box(0));
v___x_3110_ = lean_box(0);
v___x_3111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3111_, 0, v___x_3110_);
return v___x_3111_;
}
else
{
lean_object* v_val_3112_; lean_object* v___x_3113_; 
v_val_3112_ = lean_ctor_get(v_a_3102_, 0);
lean_inc(v_val_3112_);
lean_dec_ref_known(v_a_3102_, 1);
v___x_3113_ = l_Lake_RegistryPkg_gitSrc_x3f(v_val_3112_);
if (lean_obj_tag(v___x_3113_) == 1)
{
lean_object* v_val_3114_; lean_object* v___x_3116_; uint8_t v_isShared_3117_; uint8_t v_isSharedCheck_3221_; 
v_val_3114_ = lean_ctor_get(v___x_3113_, 0);
v_isSharedCheck_3221_ = !lean_is_exclusive(v___x_3113_);
if (v_isSharedCheck_3221_ == 0)
{
v___x_3116_ = v___x_3113_;
v_isShared_3117_ = v_isSharedCheck_3221_;
goto v_resetjp_3115_;
}
else
{
lean_inc(v_val_3114_);
lean_dec(v___x_3113_);
v___x_3116_ = lean_box(0);
v_isShared_3117_ = v_isSharedCheck_3221_;
goto v_resetjp_3115_;
}
v_resetjp_3115_:
{
if (lean_obj_tag(v_val_3114_) == 0)
{
lean_object* v_url_3118_; lean_object* v_githubUrl_x3f_3119_; lean_object* v_defaultBranch_x3f_3120_; lean_object* v_subDir_x3f_3121_; lean_object* v_name_3122_; lean_object* v_fullName_3123_; lean_object* v___x_3124_; 
v_url_3118_ = lean_ctor_get(v_val_3114_, 1);
lean_inc_ref(v_url_3118_);
v_githubUrl_x3f_3119_ = lean_ctor_get(v_val_3114_, 2);
lean_inc(v_githubUrl_x3f_3119_);
v_defaultBranch_x3f_3120_ = lean_ctor_get(v_val_3114_, 3);
lean_inc(v_defaultBranch_x3f_3120_);
v_subDir_x3f_3121_ = lean_ctor_get(v_val_3114_, 4);
lean_inc(v_subDir_x3f_3121_);
lean_dec_ref_known(v_val_3114_, 5);
v_name_3122_ = lean_ctor_get(v_val_3112_, 0);
lean_inc_ref(v_name_3122_);
v_fullName_3123_ = lean_ctor_get(v_val_3112_, 1);
lean_inc_ref(v_fullName_3123_);
lean_dec(v_val_3112_);
v___x_3124_ = l_Lake_joinRelative(v_relPkgsDir_2796_, v_name_3122_);
switch(lean_obj_tag(v_version_2984_))
{
case 0:
{
lean_object* v___x_3125_; 
lean_del_object(v___x_3104_);
lean_dec_ref(v___x_2988_);
v___x_3125_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
if (lean_obj_tag(v_defaultBranch_x3f_3120_) == 0)
{
uint8_t v___x_3126_; 
lean_dec_ref(v___x_3124_);
lean_dec_ref(v_fullName_3123_);
lean_dec(v_subDir_x3f_3121_);
lean_dec(v_githubUrl_x3f_3119_);
lean_dec_ref(v_url_3118_);
lean_dec_ref(v_wsDir_2795_);
lean_dec_ref(v_lakeEnv_2794_);
lean_dec_ref(v_dep_2792_);
v___x_3126_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_3126_ == 0)
{
lean_object* v___x_3127_; lean_object* v___x_3129_; 
v___x_3127_ = lean_box(0);
if (v_isShared_3117_ == 0)
{
lean_ctor_set(v___x_3116_, 0, v___x_3127_);
v___x_3129_ = v___x_3116_;
goto v_reusejp_3128_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v___x_3127_);
v___x_3129_ = v_reuseFailAlloc_3130_;
goto v_reusejp_3128_;
}
v_reusejp_3128_:
{
return v___x_3129_;
}
}
else
{
lean_object* v___x_3131_; uint8_t v___x_3132_; 
lean_del_object(v___x_3116_);
v___x_3131_ = lean_box(0);
v___x_3132_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
if (v___x_3132_ == 0)
{
if (v___x_3126_ == 0)
{
goto v___jp_2800_;
}
else
{
size_t v___x_3133_; size_t v___x_3134_; lean_object* v___x_3135_; 
v___x_3133_ = ((size_t)0ULL);
v___x_3134_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8);
v___x_3135_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_3125_, v___x_3133_, v___x_3134_, v___x_3131_, v_a_2798_);
if (lean_obj_tag(v___x_3135_) == 0)
{
lean_dec_ref_known(v___x_3135_, 1);
goto v___jp_2800_;
}
else
{
lean_object* v_a_3136_; lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3143_; 
v_a_3136_ = lean_ctor_get(v___x_3135_, 0);
v_isSharedCheck_3143_ = !lean_is_exclusive(v___x_3135_);
if (v_isSharedCheck_3143_ == 0)
{
v___x_3138_ = v___x_3135_;
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
else
{
lean_inc(v_a_3136_);
lean_dec(v___x_3135_);
v___x_3138_ = lean_box(0);
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
v_resetjp_3137_:
{
lean_object* v___x_3141_; 
if (v_isShared_3139_ == 0)
{
v___x_3141_ = v___x_3138_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v_a_3136_);
v___x_3141_ = v_reuseFailAlloc_3142_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
return v___x_3141_;
}
}
}
}
}
else
{
size_t v___x_3144_; size_t v___x_3145_; lean_object* v___x_3146_; 
v___x_3144_ = ((size_t)0ULL);
v___x_3145_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8);
v___x_3146_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_3125_, v___x_3144_, v___x_3145_, v___x_3131_, v_a_2798_);
if (lean_obj_tag(v___x_3146_) == 0)
{
lean_dec_ref_known(v___x_3146_, 1);
goto v___jp_2800_;
}
else
{
lean_object* v_a_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3154_; 
v_a_3147_ = lean_ctor_get(v___x_3146_, 0);
v_isSharedCheck_3154_ = !lean_is_exclusive(v___x_3146_);
if (v_isSharedCheck_3154_ == 0)
{
v___x_3149_ = v___x_3146_;
v_isShared_3150_ = v_isSharedCheck_3154_;
goto v_resetjp_3148_;
}
else
{
lean_inc(v_a_3147_);
lean_dec(v___x_3146_);
v___x_3149_ = lean_box(0);
v_isShared_3150_ = v_isSharedCheck_3154_;
goto v_resetjp_3148_;
}
v_resetjp_3148_:
{
lean_object* v___x_3152_; 
if (v_isShared_3150_ == 0)
{
v___x_3152_ = v___x_3149_;
goto v_reusejp_3151_;
}
else
{
lean_object* v_reuseFailAlloc_3153_; 
v_reuseFailAlloc_3153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3153_, 0, v_a_3147_);
v___x_3152_ = v_reuseFailAlloc_3153_;
goto v_reusejp_3151_;
}
v_reusejp_3151_:
{
return v___x_3152_;
}
}
}
}
}
}
else
{
lean_object* v_val_3155_; uint8_t v___x_3156_; 
lean_del_object(v___x_3116_);
v_val_3155_ = lean_ctor_get(v_defaultBranch_x3f_3120_, 0);
lean_inc(v_val_3155_);
lean_dec_ref_known(v_defaultBranch_x3f_3120_, 1);
v___x_3156_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_3156_ == 0)
{
v___y_2824_ = v_fullName_3123_;
v___y_2825_ = v_githubUrl_x3f_3119_;
v___y_2826_ = v_url_3118_;
v___y_2827_ = v___x_3124_;
v___y_2828_ = v_subDir_x3f_3121_;
v_a_2829_ = v_val_3155_;
goto v___jp_2823_;
}
else
{
lean_object* v___x_3157_; uint8_t v___x_3158_; 
v___x_3157_ = lean_box(0);
v___x_3158_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
if (v___x_3158_ == 0)
{
if (v___x_3156_ == 0)
{
v___y_2824_ = v_fullName_3123_;
v___y_2825_ = v_githubUrl_x3f_3119_;
v___y_2826_ = v_url_3118_;
v___y_2827_ = v___x_3124_;
v___y_2828_ = v_subDir_x3f_3121_;
v_a_2829_ = v_val_3155_;
goto v___jp_2823_;
}
else
{
size_t v___x_3159_; size_t v___x_3160_; lean_object* v___x_3161_; 
v___x_3159_ = ((size_t)0ULL);
v___x_3160_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8);
v___x_3161_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_3125_, v___x_3159_, v___x_3160_, v___x_3157_, v_a_2798_);
if (lean_obj_tag(v___x_3161_) == 0)
{
lean_dec_ref_known(v___x_3161_, 1);
v___y_2824_ = v_fullName_3123_;
v___y_2825_ = v_githubUrl_x3f_3119_;
v___y_2826_ = v_url_3118_;
v___y_2827_ = v___x_3124_;
v___y_2828_ = v_subDir_x3f_3121_;
v_a_2829_ = v_val_3155_;
goto v___jp_2823_;
}
else
{
lean_object* v_a_3162_; lean_object* v___x_3164_; uint8_t v_isShared_3165_; uint8_t v_isSharedCheck_3169_; 
lean_dec(v_val_3155_);
lean_dec_ref(v___x_3124_);
lean_dec_ref(v_fullName_3123_);
lean_dec(v_subDir_x3f_3121_);
lean_dec(v_githubUrl_x3f_3119_);
lean_dec_ref(v_url_3118_);
lean_dec_ref(v_wsDir_2795_);
lean_dec_ref(v_lakeEnv_2794_);
lean_dec_ref(v_dep_2792_);
v_a_3162_ = lean_ctor_get(v___x_3161_, 0);
v_isSharedCheck_3169_ = !lean_is_exclusive(v___x_3161_);
if (v_isSharedCheck_3169_ == 0)
{
v___x_3164_ = v___x_3161_;
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
else
{
lean_inc(v_a_3162_);
lean_dec(v___x_3161_);
v___x_3164_ = lean_box(0);
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
v_resetjp_3163_:
{
lean_object* v___x_3167_; 
if (v_isShared_3165_ == 0)
{
v___x_3167_ = v___x_3164_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3168_; 
v_reuseFailAlloc_3168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3168_, 0, v_a_3162_);
v___x_3167_ = v_reuseFailAlloc_3168_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
return v___x_3167_;
}
}
}
}
}
else
{
size_t v___x_3170_; size_t v___x_3171_; lean_object* v___x_3172_; 
v___x_3170_ = ((size_t)0ULL);
v___x_3171_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8);
v___x_3172_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_3125_, v___x_3170_, v___x_3171_, v___x_3157_, v_a_2798_);
if (lean_obj_tag(v___x_3172_) == 0)
{
lean_dec_ref_known(v___x_3172_, 1);
v___y_2824_ = v_fullName_3123_;
v___y_2825_ = v_githubUrl_x3f_3119_;
v___y_2826_ = v_url_3118_;
v___y_2827_ = v___x_3124_;
v___y_2828_ = v_subDir_x3f_3121_;
v_a_2829_ = v_val_3155_;
goto v___jp_2823_;
}
else
{
lean_object* v_a_3173_; lean_object* v___x_3175_; uint8_t v_isShared_3176_; uint8_t v_isSharedCheck_3180_; 
lean_dec(v_val_3155_);
lean_dec_ref(v___x_3124_);
lean_dec_ref(v_fullName_3123_);
lean_dec(v_subDir_x3f_3121_);
lean_dec(v_githubUrl_x3f_3119_);
lean_dec_ref(v_url_3118_);
lean_dec_ref(v_wsDir_2795_);
lean_dec_ref(v_lakeEnv_2794_);
lean_dec_ref(v_dep_2792_);
v_a_3173_ = lean_ctor_get(v___x_3172_, 0);
v_isSharedCheck_3180_ = !lean_is_exclusive(v___x_3172_);
if (v_isSharedCheck_3180_ == 0)
{
v___x_3175_ = v___x_3172_;
v_isShared_3176_ = v_isSharedCheck_3180_;
goto v_resetjp_3174_;
}
else
{
lean_inc(v_a_3173_);
lean_dec(v___x_3172_);
v___x_3175_ = lean_box(0);
v_isShared_3176_ = v_isSharedCheck_3180_;
goto v_resetjp_3174_;
}
v_resetjp_3174_:
{
lean_object* v___x_3178_; 
if (v_isShared_3176_ == 0)
{
v___x_3178_ = v___x_3175_;
goto v_reusejp_3177_;
}
else
{
lean_object* v_reuseFailAlloc_3179_; 
v_reuseFailAlloc_3179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3179_, 0, v_a_3173_);
v___x_3178_ = v_reuseFailAlloc_3179_;
goto v_reusejp_3177_;
}
v_reusejp_3177_:
{
return v___x_3178_;
}
}
}
}
}
}
}
case 1:
{
lean_object* v_rev_3181_; lean_object* v___x_3182_; uint8_t v___x_3183_; 
lean_dec(v_defaultBranch_x3f_3120_);
lean_del_object(v___x_3116_);
lean_del_object(v___x_3104_);
lean_dec_ref(v___x_2988_);
v_rev_3181_ = lean_ctor_get(v_version_2984_, 0);
v___x_3182_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_3183_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_3183_ == 0)
{
lean_inc_ref(v_rev_3181_);
v___y_2824_ = v_fullName_3123_;
v___y_2825_ = v_githubUrl_x3f_3119_;
v___y_2826_ = v_url_3118_;
v___y_2827_ = v___x_3124_;
v___y_2828_ = v_subDir_x3f_3121_;
v_a_2829_ = v_rev_3181_;
goto v___jp_2823_;
}
else
{
lean_object* v___x_3184_; uint8_t v___x_3185_; 
v___x_3184_ = lean_box(0);
v___x_3185_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
if (v___x_3185_ == 0)
{
if (v___x_3183_ == 0)
{
lean_inc_ref(v_rev_3181_);
v___y_2824_ = v_fullName_3123_;
v___y_2825_ = v_githubUrl_x3f_3119_;
v___y_2826_ = v_url_3118_;
v___y_2827_ = v___x_3124_;
v___y_2828_ = v_subDir_x3f_3121_;
v_a_2829_ = v_rev_3181_;
goto v___jp_2823_;
}
else
{
size_t v___x_3186_; size_t v___x_3187_; lean_object* v___x_3188_; 
v___x_3186_ = ((size_t)0ULL);
v___x_3187_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8);
v___x_3188_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_3182_, v___x_3186_, v___x_3187_, v___x_3184_, v_a_2798_);
if (lean_obj_tag(v___x_3188_) == 0)
{
lean_dec_ref_known(v___x_3188_, 1);
lean_inc_ref(v_rev_3181_);
v___y_2824_ = v_fullName_3123_;
v___y_2825_ = v_githubUrl_x3f_3119_;
v___y_2826_ = v_url_3118_;
v___y_2827_ = v___x_3124_;
v___y_2828_ = v_subDir_x3f_3121_;
v_a_2829_ = v_rev_3181_;
goto v___jp_2823_;
}
else
{
lean_object* v_a_3189_; lean_object* v___x_3191_; uint8_t v_isShared_3192_; uint8_t v_isSharedCheck_3196_; 
lean_dec_ref(v___x_3124_);
lean_dec_ref(v_fullName_3123_);
lean_dec(v_subDir_x3f_3121_);
lean_dec(v_githubUrl_x3f_3119_);
lean_dec_ref(v_url_3118_);
lean_dec_ref(v_wsDir_2795_);
lean_dec_ref(v_lakeEnv_2794_);
lean_dec_ref(v_dep_2792_);
v_a_3189_ = lean_ctor_get(v___x_3188_, 0);
v_isSharedCheck_3196_ = !lean_is_exclusive(v___x_3188_);
if (v_isSharedCheck_3196_ == 0)
{
v___x_3191_ = v___x_3188_;
v_isShared_3192_ = v_isSharedCheck_3196_;
goto v_resetjp_3190_;
}
else
{
lean_inc(v_a_3189_);
lean_dec(v___x_3188_);
v___x_3191_ = lean_box(0);
v_isShared_3192_ = v_isSharedCheck_3196_;
goto v_resetjp_3190_;
}
v_resetjp_3190_:
{
lean_object* v___x_3194_; 
if (v_isShared_3192_ == 0)
{
v___x_3194_ = v___x_3191_;
goto v_reusejp_3193_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v_a_3189_);
v___x_3194_ = v_reuseFailAlloc_3195_;
goto v_reusejp_3193_;
}
v_reusejp_3193_:
{
return v___x_3194_;
}
}
}
}
}
else
{
size_t v___x_3197_; size_t v___x_3198_; lean_object* v___x_3199_; 
v___x_3197_ = ((size_t)0ULL);
v___x_3198_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8);
v___x_3199_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_3182_, v___x_3197_, v___x_3198_, v___x_3184_, v_a_2798_);
if (lean_obj_tag(v___x_3199_) == 0)
{
lean_dec_ref_known(v___x_3199_, 1);
lean_inc_ref(v_rev_3181_);
v___y_2824_ = v_fullName_3123_;
v___y_2825_ = v_githubUrl_x3f_3119_;
v___y_2826_ = v_url_3118_;
v___y_2827_ = v___x_3124_;
v___y_2828_ = v_subDir_x3f_3121_;
v_a_2829_ = v_rev_3181_;
goto v___jp_2823_;
}
else
{
lean_object* v_a_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3207_; 
lean_dec_ref(v___x_3124_);
lean_dec_ref(v_fullName_3123_);
lean_dec(v_subDir_x3f_3121_);
lean_dec(v_githubUrl_x3f_3119_);
lean_dec_ref(v_url_3118_);
lean_dec_ref(v_wsDir_2795_);
lean_dec_ref(v_lakeEnv_2794_);
lean_dec_ref(v_dep_2792_);
v_a_3200_ = lean_ctor_get(v___x_3199_, 0);
v_isSharedCheck_3207_ = !lean_is_exclusive(v___x_3199_);
if (v_isSharedCheck_3207_ == 0)
{
v___x_3202_ = v___x_3199_;
v_isShared_3203_ = v_isSharedCheck_3207_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_a_3200_);
lean_dec(v___x_3199_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3207_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
lean_object* v___x_3205_; 
if (v_isShared_3203_ == 0)
{
v___x_3205_ = v___x_3202_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v_a_3200_);
v___x_3205_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
return v___x_3205_;
}
}
}
}
}
}
default: 
{
lean_object* v_ver_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; 
lean_dec(v_defaultBranch_x3f_3120_);
lean_del_object(v___x_3116_);
v_ver_3208_ = lean_ctor_get(v_version_2984_, 0);
v___x_3209_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v___x_2988_);
lean_inc_ref(v_scope_2983_);
lean_inc_ref(v_lakeEnv_2794_);
v___x_3210_ = l_Lake_Reservoir_fetchPkgVersions(v_lakeEnv_2794_, v_scope_2983_, v___x_2988_, v___x_3209_);
if (lean_obj_tag(v___x_3210_) == 0)
{
lean_object* v_a_3211_; lean_object* v_a_3212_; lean_object* v___x_3214_; 
v_a_3211_ = lean_ctor_get(v___x_3210_, 0);
lean_inc(v_a_3211_);
v_a_3212_ = lean_ctor_get(v___x_3210_, 1);
lean_inc(v_a_3212_);
lean_dec_ref_known(v___x_3210_, 2);
if (v_isShared_3105_ == 0)
{
lean_ctor_set(v___x_3104_, 0, v_a_3211_);
v___x_3214_ = v___x_3104_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v_a_3211_);
v___x_3214_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
lean_inc_ref(v_ver_3208_);
v___y_3056_ = v_ver_3208_;
v___y_3057_ = v_fullName_3123_;
v___y_3058_ = v_githubUrl_x3f_3119_;
v___y_3059_ = v_url_3118_;
v___y_3060_ = v___x_3124_;
v___y_3061_ = v_subDir_x3f_3121_;
v_fst_3062_ = v___x_3214_;
v_snd_3063_ = v_a_3212_;
goto v___jp_3055_;
}
}
else
{
lean_object* v_a_3216_; lean_object* v_a_3217_; lean_object* v___x_3219_; 
v_a_3216_ = lean_ctor_get(v___x_3210_, 0);
lean_inc(v_a_3216_);
v_a_3217_ = lean_ctor_get(v___x_3210_, 1);
lean_inc(v_a_3217_);
lean_dec_ref_known(v___x_3210_, 2);
if (v_isShared_3105_ == 0)
{
lean_ctor_set_tag(v___x_3104_, 0);
lean_ctor_set(v___x_3104_, 0, v_a_3216_);
v___x_3219_ = v___x_3104_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3220_; 
v_reuseFailAlloc_3220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3220_, 0, v_a_3216_);
v___x_3219_ = v_reuseFailAlloc_3220_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
lean_inc_ref(v_ver_3208_);
v___y_3056_ = v_ver_3208_;
v___y_3057_ = v_fullName_3123_;
v___y_3058_ = v_githubUrl_x3f_3119_;
v___y_3059_ = v_url_3118_;
v___y_3060_ = v___x_3124_;
v___y_3061_ = v_subDir_x3f_3121_;
v_fst_3062_ = v___x_3219_;
v_snd_3063_ = v_a_3217_;
goto v___jp_3055_;
}
}
}
}
}
else
{
lean_del_object(v___x_3116_);
lean_dec(v_val_3114_);
lean_del_object(v___x_3104_);
lean_dec_ref(v___x_2988_);
lean_dec_ref(v_relPkgsDir_2796_);
lean_dec_ref(v_wsDir_2795_);
lean_dec_ref(v_lakeEnv_2794_);
lean_dec_ref(v_dep_2792_);
v___y_2804_ = v_val_3112_;
v___y_2805_ = v_a_2798_;
goto v___jp_2803_;
}
}
}
else
{
lean_dec(v___x_3113_);
lean_del_object(v___x_3104_);
lean_dec_ref(v___x_2988_);
lean_dec_ref(v_relPkgsDir_2796_);
lean_dec_ref(v_wsDir_2795_);
lean_dec_ref(v_lakeEnv_2794_);
lean_dec_ref(v_dep_2792_);
v___y_2804_ = v_val_3112_;
v___y_2805_ = v_a_2798_;
goto v___jp_2803_;
}
}
}
}
}
v___jp_3225_:
{
lean_object* v___x_3228_; uint8_t v___x_3229_; 
v___x_3228_ = lean_array_get_size(v_snd_3227_);
v___x_3229_ = lean_nat_dec_lt(v___x_2986_, v___x_3228_);
if (v___x_3229_ == 0)
{
lean_dec_ref(v_snd_3227_);
v_a_3091_ = v_fst_3226_;
goto v___jp_3090_;
}
else
{
lean_object* v___x_3230_; uint8_t v___x_3231_; 
v___x_3230_ = lean_box(0);
v___x_3231_ = lean_nat_dec_le(v___x_3228_, v___x_3228_);
if (v___x_3231_ == 0)
{
if (v___x_3229_ == 0)
{
lean_dec_ref(v_snd_3227_);
v_a_3091_ = v_fst_3226_;
goto v___jp_3090_;
}
else
{
size_t v___x_3232_; size_t v___x_3233_; lean_object* v___x_3234_; 
v___x_3232_ = ((size_t)0ULL);
v___x_3233_ = lean_usize_of_nat(v___x_3228_);
v___x_3234_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_snd_3227_, v___x_3232_, v___x_3233_, v___x_3230_, v_a_2798_);
lean_dec_ref(v_snd_3227_);
if (lean_obj_tag(v___x_3234_) == 0)
{
lean_dec_ref_known(v___x_3234_, 1);
v_a_3091_ = v_fst_3226_;
goto v___jp_3090_;
}
else
{
lean_object* v_a_3235_; lean_object* v___x_3237_; uint8_t v_isShared_3238_; uint8_t v_isSharedCheck_3242_; 
lean_dec_ref(v_fst_3226_);
lean_dec_ref(v___x_2988_);
lean_dec_ref(v_relPkgsDir_2796_);
lean_dec_ref(v_wsDir_2795_);
lean_dec_ref(v_lakeEnv_2794_);
lean_dec_ref(v_dep_2792_);
v_a_3235_ = lean_ctor_get(v___x_3234_, 0);
v_isSharedCheck_3242_ = !lean_is_exclusive(v___x_3234_);
if (v_isSharedCheck_3242_ == 0)
{
v___x_3237_ = v___x_3234_;
v_isShared_3238_ = v_isSharedCheck_3242_;
goto v_resetjp_3236_;
}
else
{
lean_inc(v_a_3235_);
lean_dec(v___x_3234_);
v___x_3237_ = lean_box(0);
v_isShared_3238_ = v_isSharedCheck_3242_;
goto v_resetjp_3236_;
}
v_resetjp_3236_:
{
lean_object* v___x_3240_; 
if (v_isShared_3238_ == 0)
{
v___x_3240_ = v___x_3237_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3241_; 
v_reuseFailAlloc_3241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3241_, 0, v_a_3235_);
v___x_3240_ = v_reuseFailAlloc_3241_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
return v___x_3240_;
}
}
}
}
}
else
{
size_t v___x_3243_; size_t v___x_3244_; lean_object* v___x_3245_; 
v___x_3243_ = ((size_t)0ULL);
v___x_3244_ = lean_usize_of_nat(v___x_3228_);
v___x_3245_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_snd_3227_, v___x_3243_, v___x_3244_, v___x_3230_, v_a_2798_);
lean_dec_ref(v_snd_3227_);
if (lean_obj_tag(v___x_3245_) == 0)
{
lean_dec_ref_known(v___x_3245_, 1);
v_a_3091_ = v_fst_3226_;
goto v___jp_3090_;
}
else
{
lean_object* v_a_3246_; lean_object* v___x_3248_; uint8_t v_isShared_3249_; uint8_t v_isSharedCheck_3253_; 
lean_dec_ref(v_fst_3226_);
lean_dec_ref(v___x_2988_);
lean_dec_ref(v_relPkgsDir_2796_);
lean_dec_ref(v_wsDir_2795_);
lean_dec_ref(v_lakeEnv_2794_);
lean_dec_ref(v_dep_2792_);
v_a_3246_ = lean_ctor_get(v___x_3245_, 0);
v_isSharedCheck_3253_ = !lean_is_exclusive(v___x_3245_);
if (v_isSharedCheck_3253_ == 0)
{
v___x_3248_ = v___x_3245_;
v_isShared_3249_ = v_isSharedCheck_3253_;
goto v_resetjp_3247_;
}
else
{
lean_inc(v_a_3246_);
lean_dec(v___x_3245_);
v___x_3248_ = lean_box(0);
v_isShared_3249_ = v_isSharedCheck_3253_;
goto v_resetjp_3247_;
}
v_resetjp_3247_:
{
lean_object* v___x_3251_; 
if (v_isShared_3249_ == 0)
{
v___x_3251_ = v___x_3248_;
goto v_reusejp_3250_;
}
else
{
lean_object* v_reuseFailAlloc_3252_; 
v_reuseFailAlloc_3252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3252_, 0, v_a_3246_);
v___x_3251_ = v_reuseFailAlloc_3252_;
goto v_reusejp_3250_;
}
v_reusejp_3250_:
{
return v___x_3251_;
}
}
}
}
}
}
}
else
{
uint8_t v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; uint8_t v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; 
lean_inc(v_name_2982_);
lean_dec_ref(v_relPkgsDir_2796_);
lean_dec_ref(v_wsDir_2795_);
lean_dec_ref(v_lakeEnv_2794_);
lean_dec_ref(v_dep_2792_);
v___x_3260_ = 0;
v___x_3261_ = l_Lean_Name_toString(v_name_2982_, v___x_3260_);
v___x_3262_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__8));
v___x_3263_ = lean_string_append(v___x_3261_, v___x_3262_);
v___x_3264_ = 3;
v___x_3265_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3265_, 0, v___x_3263_);
lean_ctor_set_uint8(v___x_3265_, sizeof(void*)*1, v___x_3264_);
lean_inc_ref(v_a_2798_);
v___x_3266_ = lean_apply_2(v_a_2798_, v___x_3265_, lean_box(0));
v___x_3267_ = lean_box(0);
v___x_3268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3268_, 0, v___x_3267_);
return v___x_3268_;
}
}
v___jp_2800_:
{
lean_object* v___x_2801_; lean_object* v___x_2802_; 
v___x_2801_ = lean_box(0);
v___x_2802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2802_, 0, v___x_2801_);
return v___x_2802_;
}
v___jp_2803_:
{
lean_object* v_fullName_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; uint8_t v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; 
v_fullName_2806_ = lean_ctor_get(v___y_2804_, 1);
lean_inc_ref(v_fullName_2806_);
lean_dec_ref(v___y_2804_);
v___x_2807_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__0));
v___x_2808_ = lean_string_append(v_fullName_2806_, v___x_2807_);
v___x_2809_ = 3;
v___x_2810_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2810_, 0, v___x_2808_);
lean_ctor_set_uint8(v___x_2810_, sizeof(void*)*1, v___x_2809_);
lean_inc_ref(v___y_2805_);
v___x_2811_ = lean_apply_2(v___y_2805_, v___x_2810_, lean_box(0));
v___x_2812_ = lean_box(0);
v___x_2813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2813_, 0, v___x_2812_);
return v___x_2813_;
}
v___jp_2814_:
{
lean_object* v___x_2821_; lean_object* v___x_2822_; 
v___x_2821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2821_, 0, v___y_2817_);
v___x_2822_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(v_a_2798_, v_dep_2792_, v_inherited_2793_, v_lakeEnv_2794_, v_wsDir_2795_, v___y_2815_, v___y_2818_, v___y_2816_, v___y_2820_, v___x_2821_, v___y_2819_);
lean_dec_ref(v_lakeEnv_2794_);
return v___x_2822_;
}
v___jp_2823_:
{
if (lean_obj_tag(v___y_2825_) == 0)
{
lean_object* v___x_2830_; 
v___x_2830_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___y_2815_ = v___y_2824_;
v___y_2816_ = v___y_2826_;
v___y_2817_ = v_a_2829_;
v___y_2818_ = v___y_2827_;
v___y_2819_ = v___y_2828_;
v___y_2820_ = v___x_2830_;
goto v___jp_2814_;
}
else
{
lean_object* v_val_2831_; 
v_val_2831_ = lean_ctor_get(v___y_2825_, 0);
lean_inc(v_val_2831_);
lean_dec_ref_known(v___y_2825_, 1);
v___y_2815_ = v___y_2824_;
v___y_2816_ = v___y_2826_;
v___y_2817_ = v_a_2829_;
v___y_2818_ = v___y_2827_;
v___y_2819_ = v___y_2828_;
v___y_2820_ = v_val_2831_;
goto v___jp_2814_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize___boxed(lean_object* v_dep_3269_, lean_object* v_inherited_3270_, lean_object* v_lakeEnv_3271_, lean_object* v_wsDir_3272_, lean_object* v_relPkgsDir_3273_, lean_object* v_relParentDir_3274_, lean_object* v_a_3275_, lean_object* v_a_3276_){
_start:
{
uint8_t v_inherited_boxed_3277_; lean_object* v_res_3278_; 
v_inherited_boxed_3277_ = lean_unbox(v_inherited_3270_);
v_res_3278_ = l_Lake_Dependency_materialize(v_dep_3269_, v_inherited_boxed_3277_, v_lakeEnv_3271_, v_wsDir_3272_, v_relPkgsDir_3273_, v_relParentDir_3274_, v_a_3275_);
lean_dec_ref(v_a_3275_);
return v_res_3278_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep(lean_object* v_manifestEntry_3284_, lean_object* v_wsDir_3285_, lean_object* v_relPkgDir_3286_, lean_object* v_remoteUrl_3287_, lean_object* v_a_3288_){
_start:
{
lean_object* v___y_3291_; lean_object* v_a_3292_; lean_object* v_pkgDir_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___f_3298_; lean_object* v___y_3300_; lean_object* v___y_3301_; lean_object* v___y_3302_; lean_object* v___y_3303_; lean_object* v_val_3304_; lean_object* v_a_3334_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v_val_3374_; lean_object* v___x_3402_; uint8_t v___x_3403_; 
lean_inc_ref(v_relPkgDir_3286_);
v_pkgDir_3295_ = l_Lake_joinRelative(v_wsDir_3285_, v_relPkgDir_3286_);
v___x_3296_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__2, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__2_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__2);
lean_inc_ref(v_pkgDir_3295_);
v___x_3297_ = l_Lake_resolvePath(v_pkgDir_3295_);
v___f_3298_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3));
v___x_3371_ = lean_unsigned_to_nat(0u);
v___x_3372_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_3402_ = lean_string_utf8_byte_size(v___x_3297_);
v___x_3403_ = lean_nat_dec_eq(v___x_3402_, v___x_3371_);
if (v___x_3403_ == 0)
{
lean_object* v___x_3404_; 
v___x_3404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3404_, 0, v___x_3297_);
v_val_3374_ = v___x_3404_;
goto v___jp_3373_;
}
else
{
lean_object* v___x_3405_; 
lean_dec_ref(v___x_3297_);
v___x_3405_ = lean_box(0);
v_val_3374_ = v___x_3405_;
goto v___jp_3373_;
}
v___jp_3290_:
{
lean_object* v___x_3293_; lean_object* v___x_3294_; 
v___x_3293_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3293_, 0, v___y_3291_);
lean_ctor_set(v___x_3293_, 1, v_relPkgDir_3286_);
lean_ctor_set(v___x_3293_, 2, v_remoteUrl_3287_);
lean_ctor_set(v___x_3293_, 3, v_a_3292_);
lean_ctor_set(v___x_3293_, 4, v_manifestEntry_3284_);
v___x_3294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3294_, 0, v___x_3293_);
return v___x_3294_;
}
v___jp_3299_:
{
lean_object* v___x_3305_; uint8_t v___x_3306_; 
v___x_3305_ = lean_array_get_size(v___y_3301_);
v___x_3306_ = lean_nat_dec_lt(v___y_3300_, v___x_3305_);
if (v___x_3306_ == 0)
{
lean_dec_ref(v___y_3302_);
v___y_3291_ = v___y_3303_;
v_a_3292_ = v_val_3304_;
goto v___jp_3290_;
}
else
{
lean_object* v___x_3307_; uint8_t v___x_3308_; 
v___x_3307_ = lean_box(0);
v___x_3308_ = lean_nat_dec_le(v___x_3305_, v___x_3305_);
if (v___x_3308_ == 0)
{
if (v___x_3306_ == 0)
{
lean_dec_ref(v___y_3302_);
v___y_3291_ = v___y_3303_;
v_a_3292_ = v_val_3304_;
goto v___jp_3290_;
}
else
{
size_t v___x_3309_; size_t v___x_3310_; lean_object* v___x_2400__overap_3311_; lean_object* v___x_3312_; 
v___x_3309_ = ((size_t)0ULL);
v___x_3310_ = lean_usize_of_nat(v___x_3305_);
lean_inc_ref(v___y_3301_);
v___x_2400__overap_3311_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___y_3302_, v___f_3298_, v___y_3301_, v___x_3309_, v___x_3310_, v___x_3307_);
lean_inc_ref(v_a_3288_);
v___x_3312_ = lean_apply_2(v___x_2400__overap_3311_, v_a_3288_, lean_box(0));
if (lean_obj_tag(v___x_3312_) == 0)
{
lean_dec_ref_known(v___x_3312_, 1);
v___y_3291_ = v___y_3303_;
v_a_3292_ = v_val_3304_;
goto v___jp_3290_;
}
else
{
lean_object* v_a_3313_; lean_object* v___x_3315_; uint8_t v_isShared_3316_; uint8_t v_isSharedCheck_3320_; 
lean_dec_ref(v_val_3304_);
lean_dec_ref(v___y_3303_);
lean_dec_ref(v_remoteUrl_3287_);
lean_dec_ref(v_relPkgDir_3286_);
lean_dec_ref(v_manifestEntry_3284_);
v_a_3313_ = lean_ctor_get(v___x_3312_, 0);
v_isSharedCheck_3320_ = !lean_is_exclusive(v___x_3312_);
if (v_isSharedCheck_3320_ == 0)
{
v___x_3315_ = v___x_3312_;
v_isShared_3316_ = v_isSharedCheck_3320_;
goto v_resetjp_3314_;
}
else
{
lean_inc(v_a_3313_);
lean_dec(v___x_3312_);
v___x_3315_ = lean_box(0);
v_isShared_3316_ = v_isSharedCheck_3320_;
goto v_resetjp_3314_;
}
v_resetjp_3314_:
{
lean_object* v___x_3318_; 
if (v_isShared_3316_ == 0)
{
v___x_3318_ = v___x_3315_;
goto v_reusejp_3317_;
}
else
{
lean_object* v_reuseFailAlloc_3319_; 
v_reuseFailAlloc_3319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3319_, 0, v_a_3313_);
v___x_3318_ = v_reuseFailAlloc_3319_;
goto v_reusejp_3317_;
}
v_reusejp_3317_:
{
return v___x_3318_;
}
}
}
}
}
else
{
size_t v___x_3321_; size_t v___x_3322_; lean_object* v___x_2410__overap_3323_; lean_object* v___x_3324_; 
v___x_3321_ = ((size_t)0ULL);
v___x_3322_ = lean_usize_of_nat(v___x_3305_);
lean_inc_ref(v___y_3301_);
v___x_2410__overap_3323_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___y_3302_, v___f_3298_, v___y_3301_, v___x_3321_, v___x_3322_, v___x_3307_);
lean_inc_ref(v_a_3288_);
v___x_3324_ = lean_apply_2(v___x_2410__overap_3323_, v_a_3288_, lean_box(0));
if (lean_obj_tag(v___x_3324_) == 0)
{
lean_dec_ref_known(v___x_3324_, 1);
v___y_3291_ = v___y_3303_;
v_a_3292_ = v_val_3304_;
goto v___jp_3290_;
}
else
{
lean_object* v_a_3325_; lean_object* v___x_3327_; uint8_t v_isShared_3328_; uint8_t v_isSharedCheck_3332_; 
lean_dec_ref(v_val_3304_);
lean_dec_ref(v___y_3303_);
lean_dec_ref(v_remoteUrl_3287_);
lean_dec_ref(v_relPkgDir_3286_);
lean_dec_ref(v_manifestEntry_3284_);
v_a_3325_ = lean_ctor_get(v___x_3324_, 0);
v_isSharedCheck_3332_ = !lean_is_exclusive(v___x_3324_);
if (v_isSharedCheck_3332_ == 0)
{
v___x_3327_ = v___x_3324_;
v_isShared_3328_ = v_isSharedCheck_3332_;
goto v_resetjp_3326_;
}
else
{
lean_inc(v_a_3325_);
lean_dec(v___x_3324_);
v___x_3327_ = lean_box(0);
v_isShared_3328_ = v_isSharedCheck_3332_;
goto v_resetjp_3326_;
}
v_resetjp_3326_:
{
lean_object* v___x_3330_; 
if (v_isShared_3328_ == 0)
{
v___x_3330_ = v___x_3327_;
goto v_reusejp_3329_;
}
else
{
lean_object* v_reuseFailAlloc_3331_; 
v_reuseFailAlloc_3331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3331_, 0, v_a_3325_);
v___x_3330_ = v_reuseFailAlloc_3331_;
goto v_reusejp_3329_;
}
v_reusejp_3329_:
{
return v___x_3330_;
}
}
}
}
}
}
v___jp_3333_:
{
if (lean_obj_tag(v_a_3334_) == 1)
{
lean_object* v_manifestFile_x3f_3335_; 
lean_dec_ref(v_pkgDir_3295_);
v_manifestFile_x3f_3335_ = lean_ctor_get(v_manifestEntry_3284_, 3);
if (lean_obj_tag(v_manifestFile_x3f_3335_) == 1)
{
lean_object* v_val_3336_; lean_object* v_val_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; 
v_val_3336_ = lean_ctor_get(v_a_3334_, 0);
lean_inc_n(v_val_3336_, 2);
lean_dec_ref_known(v_a_3334_, 1);
v_val_3337_ = lean_ctor_get(v_manifestFile_x3f_3335_, 0);
lean_inc(v_val_3337_);
v___x_3338_ = l_Lake_joinRelative(v_val_3336_, v_val_3337_);
v___x_3339_ = lean_unsigned_to_nat(0u);
v___x_3340_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_3341_ = l_Lake_Manifest_load(v___x_3338_);
if (lean_obj_tag(v___x_3341_) == 0)
{
lean_object* v_a_3342_; lean_object* v___x_3344_; uint8_t v_isShared_3345_; uint8_t v_isSharedCheck_3349_; 
v_a_3342_ = lean_ctor_get(v___x_3341_, 0);
v_isSharedCheck_3349_ = !lean_is_exclusive(v___x_3341_);
if (v_isSharedCheck_3349_ == 0)
{
v___x_3344_ = v___x_3341_;
v_isShared_3345_ = v_isSharedCheck_3349_;
goto v_resetjp_3343_;
}
else
{
lean_inc(v_a_3342_);
lean_dec(v___x_3341_);
v___x_3344_ = lean_box(0);
v_isShared_3345_ = v_isSharedCheck_3349_;
goto v_resetjp_3343_;
}
v_resetjp_3343_:
{
lean_object* v___x_3347_; 
if (v_isShared_3345_ == 0)
{
lean_ctor_set_tag(v___x_3344_, 1);
v___x_3347_ = v___x_3344_;
goto v_reusejp_3346_;
}
else
{
lean_object* v_reuseFailAlloc_3348_; 
v_reuseFailAlloc_3348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3348_, 0, v_a_3342_);
v___x_3347_ = v_reuseFailAlloc_3348_;
goto v_reusejp_3346_;
}
v_reusejp_3346_:
{
v___y_3300_ = v___x_3339_;
v___y_3301_ = v___x_3340_;
v___y_3302_ = v___x_3296_;
v___y_3303_ = v_val_3336_;
v_val_3304_ = v___x_3347_;
goto v___jp_3299_;
}
}
}
else
{
lean_object* v_a_3350_; lean_object* v___x_3352_; uint8_t v_isShared_3353_; uint8_t v_isSharedCheck_3357_; 
v_a_3350_ = lean_ctor_get(v___x_3341_, 0);
v_isSharedCheck_3357_ = !lean_is_exclusive(v___x_3341_);
if (v_isSharedCheck_3357_ == 0)
{
v___x_3352_ = v___x_3341_;
v_isShared_3353_ = v_isSharedCheck_3357_;
goto v_resetjp_3351_;
}
else
{
lean_inc(v_a_3350_);
lean_dec(v___x_3341_);
v___x_3352_ = lean_box(0);
v_isShared_3353_ = v_isSharedCheck_3357_;
goto v_resetjp_3351_;
}
v_resetjp_3351_:
{
lean_object* v___x_3355_; 
if (v_isShared_3353_ == 0)
{
lean_ctor_set_tag(v___x_3352_, 0);
v___x_3355_ = v___x_3352_;
goto v_reusejp_3354_;
}
else
{
lean_object* v_reuseFailAlloc_3356_; 
v_reuseFailAlloc_3356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3356_, 0, v_a_3350_);
v___x_3355_ = v_reuseFailAlloc_3356_;
goto v_reusejp_3354_;
}
v_reusejp_3354_:
{
v___y_3300_ = v___x_3339_;
v___y_3301_ = v___x_3340_;
v___y_3302_ = v___x_3296_;
v___y_3303_ = v_val_3336_;
v_val_3304_ = v___x_3355_;
goto v___jp_3299_;
}
}
}
}
else
{
lean_object* v_val_3358_; lean_object* v___x_3359_; 
v_val_3358_ = lean_ctor_get(v_a_3334_, 0);
lean_inc(v_val_3358_);
lean_dec_ref_known(v_a_3334_, 1);
v___x_3359_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1));
v___y_3291_ = v_val_3358_;
v_a_3292_ = v___x_3359_;
goto v___jp_3290_;
}
}
else
{
lean_object* v_name_3360_; uint8_t v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; uint8_t v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; 
lean_dec(v_a_3334_);
lean_dec_ref(v_remoteUrl_3287_);
lean_dec_ref(v_relPkgDir_3286_);
v_name_3360_ = lean_ctor_get(v_manifestEntry_3284_, 0);
lean_inc(v_name_3360_);
lean_dec_ref(v_manifestEntry_3284_);
v___x_3361_ = 0;
v___x_3362_ = l_Lean_Name_toString(v_name_3360_, v___x_3361_);
v___x_3363_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0));
v___x_3364_ = lean_string_append(v___x_3362_, v___x_3363_);
v___x_3365_ = lean_string_append(v___x_3364_, v_pkgDir_3295_);
lean_dec_ref(v_pkgDir_3295_);
v___x_3366_ = 3;
v___x_3367_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3367_, 0, v___x_3365_);
lean_ctor_set_uint8(v___x_3367_, sizeof(void*)*1, v___x_3366_);
lean_inc_ref(v_a_3288_);
v___x_3368_ = lean_apply_2(v_a_3288_, v___x_3367_, lean_box(0));
v___x_3369_ = lean_box(0);
v___x_3370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3370_, 0, v___x_3369_);
return v___x_3370_;
}
}
v___jp_3373_:
{
uint8_t v___x_3375_; 
v___x_3375_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_3375_ == 0)
{
v_a_3334_ = v_val_3374_;
goto v___jp_3333_;
}
else
{
lean_object* v___x_3376_; uint8_t v___x_3377_; 
v___x_3376_ = lean_box(0);
v___x_3377_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
if (v___x_3377_ == 0)
{
if (v___x_3375_ == 0)
{
v_a_3334_ = v_val_3374_;
goto v___jp_3333_;
}
else
{
size_t v___x_3378_; size_t v___x_3379_; lean_object* v___x_2466__overap_3380_; lean_object* v___x_3381_; 
v___x_3378_ = ((size_t)0ULL);
v___x_3379_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8);
v___x_2466__overap_3380_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3296_, v___f_3298_, v___x_3372_, v___x_3378_, v___x_3379_, v___x_3376_);
lean_inc_ref(v_a_3288_);
v___x_3381_ = lean_apply_2(v___x_2466__overap_3380_, v_a_3288_, lean_box(0));
if (lean_obj_tag(v___x_3381_) == 0)
{
lean_dec_ref_known(v___x_3381_, 1);
v_a_3334_ = v_val_3374_;
goto v___jp_3333_;
}
else
{
lean_object* v_a_3382_; lean_object* v___x_3384_; uint8_t v_isShared_3385_; uint8_t v_isSharedCheck_3389_; 
lean_dec(v_val_3374_);
lean_dec_ref(v_pkgDir_3295_);
lean_dec_ref(v_remoteUrl_3287_);
lean_dec_ref(v_relPkgDir_3286_);
lean_dec_ref(v_manifestEntry_3284_);
v_a_3382_ = lean_ctor_get(v___x_3381_, 0);
v_isSharedCheck_3389_ = !lean_is_exclusive(v___x_3381_);
if (v_isSharedCheck_3389_ == 0)
{
v___x_3384_ = v___x_3381_;
v_isShared_3385_ = v_isSharedCheck_3389_;
goto v_resetjp_3383_;
}
else
{
lean_inc(v_a_3382_);
lean_dec(v___x_3381_);
v___x_3384_ = lean_box(0);
v_isShared_3385_ = v_isSharedCheck_3389_;
goto v_resetjp_3383_;
}
v_resetjp_3383_:
{
lean_object* v___x_3387_; 
if (v_isShared_3385_ == 0)
{
v___x_3387_ = v___x_3384_;
goto v_reusejp_3386_;
}
else
{
lean_object* v_reuseFailAlloc_3388_; 
v_reuseFailAlloc_3388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3388_, 0, v_a_3382_);
v___x_3387_ = v_reuseFailAlloc_3388_;
goto v_reusejp_3386_;
}
v_reusejp_3386_:
{
return v___x_3387_;
}
}
}
}
}
else
{
size_t v___x_3390_; size_t v___x_3391_; lean_object* v___x_2476__overap_3392_; lean_object* v___x_3393_; 
v___x_3390_ = ((size_t)0ULL);
v___x_3391_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8);
v___x_2476__overap_3392_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3296_, v___f_3298_, v___x_3372_, v___x_3390_, v___x_3391_, v___x_3376_);
lean_inc_ref(v_a_3288_);
v___x_3393_ = lean_apply_2(v___x_2476__overap_3392_, v_a_3288_, lean_box(0));
if (lean_obj_tag(v___x_3393_) == 0)
{
lean_dec_ref_known(v___x_3393_, 1);
v_a_3334_ = v_val_3374_;
goto v___jp_3333_;
}
else
{
lean_object* v_a_3394_; lean_object* v___x_3396_; uint8_t v_isShared_3397_; uint8_t v_isSharedCheck_3401_; 
lean_dec(v_val_3374_);
lean_dec_ref(v_pkgDir_3295_);
lean_dec_ref(v_remoteUrl_3287_);
lean_dec_ref(v_relPkgDir_3286_);
lean_dec_ref(v_manifestEntry_3284_);
v_a_3394_ = lean_ctor_get(v___x_3393_, 0);
v_isSharedCheck_3401_ = !lean_is_exclusive(v___x_3393_);
if (v_isSharedCheck_3401_ == 0)
{
v___x_3396_ = v___x_3393_;
v_isShared_3397_ = v_isSharedCheck_3401_;
goto v_resetjp_3395_;
}
else
{
lean_inc(v_a_3394_);
lean_dec(v___x_3393_);
v___x_3396_ = lean_box(0);
v_isShared_3397_ = v_isSharedCheck_3401_;
goto v_resetjp_3395_;
}
v_resetjp_3395_:
{
lean_object* v___x_3399_; 
if (v_isShared_3397_ == 0)
{
v___x_3399_ = v___x_3396_;
goto v_reusejp_3398_;
}
else
{
lean_object* v_reuseFailAlloc_3400_; 
v_reuseFailAlloc_3400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3400_, 0, v_a_3394_);
v___x_3399_ = v_reuseFailAlloc_3400_;
goto v_reusejp_3398_;
}
v_reusejp_3398_:
{
return v___x_3399_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___boxed(lean_object* v_manifestEntry_3406_, lean_object* v_wsDir_3407_, lean_object* v_relPkgDir_3408_, lean_object* v_remoteUrl_3409_, lean_object* v_a_3410_, lean_object* v_a_3411_){
_start:
{
lean_object* v_res_3412_; 
v_res_3412_ = l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep(v_manifestEntry_3406_, v_wsDir_3407_, v_relPkgDir_3408_, v_remoteUrl_3409_, v_a_3410_);
lean_dec_ref(v_a_3410_);
return v_res_3412_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lake_PackageEntry_materialize_spec__0___redArg(lean_object* v_t_3413_, lean_object* v_k_3414_, lean_object* v_fallback_3415_){
_start:
{
if (lean_obj_tag(v_t_3413_) == 0)
{
lean_object* v_k_3416_; lean_object* v_v_3417_; lean_object* v_l_3418_; lean_object* v_r_3419_; uint8_t v___x_3420_; 
v_k_3416_ = lean_ctor_get(v_t_3413_, 1);
v_v_3417_ = lean_ctor_get(v_t_3413_, 2);
v_l_3418_ = lean_ctor_get(v_t_3413_, 3);
v_r_3419_ = lean_ctor_get(v_t_3413_, 4);
v___x_3420_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3414_, v_k_3416_);
switch(v___x_3420_)
{
case 0:
{
v_t_3413_ = v_l_3418_;
goto _start;
}
case 1:
{
lean_inc(v_v_3417_);
return v_v_3417_;
}
default: 
{
v_t_3413_ = v_r_3419_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_3415_);
return v_fallback_3415_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lake_PackageEntry_materialize_spec__0___redArg___boxed(lean_object* v_t_3423_, lean_object* v_k_3424_, lean_object* v_fallback_3425_){
_start:
{
lean_object* v_res_3426_; 
v_res_3426_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lake_PackageEntry_materialize_spec__0___redArg(v_t_3423_, v_k_3424_, v_fallback_3425_);
lean_dec(v_fallback_3425_);
lean_dec(v_k_3424_);
lean_dec(v_t_3423_);
return v_res_3426_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize(lean_object* v_manifestEntry_3427_, lean_object* v_lakeEnv_3428_, lean_object* v_wsDir_3429_, lean_object* v_relPkgsDir_3430_, lean_object* v_a_3431_){
_start:
{
lean_object* v___y_3434_; lean_object* v___y_3435_; lean_object* v___y_3436_; lean_object* v_a_3437_; lean_object* v___y_3441_; lean_object* v___y_3442_; lean_object* v___y_3443_; lean_object* v___y_3444_; lean_object* v___y_3445_; lean_object* v_val_3446_; lean_object* v_src_3473_; 
v_src_3473_ = lean_ctor_get(v_manifestEntry_3427_, 4);
lean_inc_ref(v_src_3473_);
if (lean_obj_tag(v_src_3473_) == 0)
{
lean_object* v_name_3474_; lean_object* v_manifestFile_x3f_3475_; lean_object* v_dir_3476_; lean_object* v___x_3478_; uint8_t v_isShared_3479_; uint8_t v_isSharedCheck_3590_; 
lean_dec_ref(v_relPkgsDir_3430_);
v_name_3474_ = lean_ctor_get(v_manifestEntry_3427_, 0);
v_manifestFile_x3f_3475_ = lean_ctor_get(v_manifestEntry_3427_, 3);
v_dir_3476_ = lean_ctor_get(v_src_3473_, 0);
v_isSharedCheck_3590_ = !lean_is_exclusive(v_src_3473_);
if (v_isSharedCheck_3590_ == 0)
{
v___x_3478_ = v_src_3473_;
v_isShared_3479_ = v_isSharedCheck_3590_;
goto v_resetjp_3477_;
}
else
{
lean_inc(v_dir_3476_);
lean_dec(v_src_3473_);
v___x_3478_ = lean_box(0);
v_isShared_3479_ = v_isSharedCheck_3590_;
goto v_resetjp_3477_;
}
v_resetjp_3477_:
{
lean_object* v_pkgDir_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___y_3484_; lean_object* v_a_3485_; lean_object* v___y_3491_; lean_object* v___y_3492_; lean_object* v___y_3493_; lean_object* v_val_3494_; lean_object* v_a_3522_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v_val_3560_; lean_object* v___x_3586_; uint8_t v___x_3587_; 
lean_inc_ref(v_dir_3476_);
v_pkgDir_3480_ = l_Lake_joinRelative(v_wsDir_3429_, v_dir_3476_);
lean_inc_ref(v_pkgDir_3480_);
v___x_3481_ = l_Lake_resolvePath(v_pkgDir_3480_);
v___x_3482_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___x_3557_ = lean_unsigned_to_nat(0u);
v___x_3558_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_3586_ = lean_string_utf8_byte_size(v___x_3481_);
v___x_3587_ = lean_nat_dec_eq(v___x_3586_, v___x_3557_);
if (v___x_3587_ == 0)
{
lean_object* v___x_3588_; 
v___x_3588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3588_, 0, v___x_3481_);
v_val_3560_ = v___x_3588_;
goto v___jp_3559_;
}
else
{
lean_object* v___x_3589_; 
lean_dec_ref(v___x_3481_);
v___x_3589_ = lean_box(0);
v_val_3560_ = v___x_3589_;
goto v___jp_3559_;
}
v___jp_3483_:
{
lean_object* v___x_3486_; lean_object* v___x_3488_; 
v___x_3486_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3486_, 0, v___y_3484_);
lean_ctor_set(v___x_3486_, 1, v_dir_3476_);
lean_ctor_set(v___x_3486_, 2, v___x_3482_);
lean_ctor_set(v___x_3486_, 3, v_a_3485_);
lean_ctor_set(v___x_3486_, 4, v_manifestEntry_3427_);
if (v_isShared_3479_ == 0)
{
lean_ctor_set(v___x_3478_, 0, v___x_3486_);
v___x_3488_ = v___x_3478_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v___x_3486_);
v___x_3488_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
return v___x_3488_;
}
}
v___jp_3490_:
{
lean_object* v___x_3495_; uint8_t v___x_3496_; 
v___x_3495_ = lean_array_get_size(v___y_3491_);
v___x_3496_ = lean_nat_dec_lt(v___y_3492_, v___x_3495_);
if (v___x_3496_ == 0)
{
v___y_3484_ = v___y_3493_;
v_a_3485_ = v_val_3494_;
goto v___jp_3483_;
}
else
{
lean_object* v___x_3497_; uint8_t v___x_3498_; 
v___x_3497_ = lean_box(0);
v___x_3498_ = lean_nat_dec_le(v___x_3495_, v___x_3495_);
if (v___x_3498_ == 0)
{
if (v___x_3496_ == 0)
{
v___y_3484_ = v___y_3493_;
v_a_3485_ = v_val_3494_;
goto v___jp_3483_;
}
else
{
size_t v___x_3499_; size_t v___x_3500_; lean_object* v___x_3501_; 
v___x_3499_ = ((size_t)0ULL);
v___x_3500_ = lean_usize_of_nat(v___x_3495_);
v___x_3501_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_3491_, v___x_3499_, v___x_3500_, v___x_3497_, v_a_3431_);
if (lean_obj_tag(v___x_3501_) == 0)
{
lean_dec_ref_known(v___x_3501_, 1);
v___y_3484_ = v___y_3493_;
v_a_3485_ = v_val_3494_;
goto v___jp_3483_;
}
else
{
lean_object* v_a_3502_; lean_object* v___x_3504_; uint8_t v_isShared_3505_; uint8_t v_isSharedCheck_3509_; 
lean_dec_ref(v_val_3494_);
lean_dec_ref(v___y_3493_);
lean_del_object(v___x_3478_);
lean_dec_ref(v_dir_3476_);
lean_dec_ref(v_manifestEntry_3427_);
v_a_3502_ = lean_ctor_get(v___x_3501_, 0);
v_isSharedCheck_3509_ = !lean_is_exclusive(v___x_3501_);
if (v_isSharedCheck_3509_ == 0)
{
v___x_3504_ = v___x_3501_;
v_isShared_3505_ = v_isSharedCheck_3509_;
goto v_resetjp_3503_;
}
else
{
lean_inc(v_a_3502_);
lean_dec(v___x_3501_);
v___x_3504_ = lean_box(0);
v_isShared_3505_ = v_isSharedCheck_3509_;
goto v_resetjp_3503_;
}
v_resetjp_3503_:
{
lean_object* v___x_3507_; 
if (v_isShared_3505_ == 0)
{
v___x_3507_ = v___x_3504_;
goto v_reusejp_3506_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v_a_3502_);
v___x_3507_ = v_reuseFailAlloc_3508_;
goto v_reusejp_3506_;
}
v_reusejp_3506_:
{
return v___x_3507_;
}
}
}
}
}
else
{
size_t v___x_3510_; size_t v___x_3511_; lean_object* v___x_3512_; 
v___x_3510_ = ((size_t)0ULL);
v___x_3511_ = lean_usize_of_nat(v___x_3495_);
v___x_3512_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_3491_, v___x_3510_, v___x_3511_, v___x_3497_, v_a_3431_);
if (lean_obj_tag(v___x_3512_) == 0)
{
lean_dec_ref_known(v___x_3512_, 1);
v___y_3484_ = v___y_3493_;
v_a_3485_ = v_val_3494_;
goto v___jp_3483_;
}
else
{
lean_object* v_a_3513_; lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3520_; 
lean_dec_ref(v_val_3494_);
lean_dec_ref(v___y_3493_);
lean_del_object(v___x_3478_);
lean_dec_ref(v_dir_3476_);
lean_dec_ref(v_manifestEntry_3427_);
v_a_3513_ = lean_ctor_get(v___x_3512_, 0);
v_isSharedCheck_3520_ = !lean_is_exclusive(v___x_3512_);
if (v_isSharedCheck_3520_ == 0)
{
v___x_3515_ = v___x_3512_;
v_isShared_3516_ = v_isSharedCheck_3520_;
goto v_resetjp_3514_;
}
else
{
lean_inc(v_a_3513_);
lean_dec(v___x_3512_);
v___x_3515_ = lean_box(0);
v_isShared_3516_ = v_isSharedCheck_3520_;
goto v_resetjp_3514_;
}
v_resetjp_3514_:
{
lean_object* v___x_3518_; 
if (v_isShared_3516_ == 0)
{
v___x_3518_ = v___x_3515_;
goto v_reusejp_3517_;
}
else
{
lean_object* v_reuseFailAlloc_3519_; 
v_reuseFailAlloc_3519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3519_, 0, v_a_3513_);
v___x_3518_ = v_reuseFailAlloc_3519_;
goto v_reusejp_3517_;
}
v_reusejp_3517_:
{
return v___x_3518_;
}
}
}
}
}
}
v___jp_3521_:
{
if (lean_obj_tag(v_a_3522_) == 1)
{
lean_dec_ref(v_pkgDir_3480_);
if (lean_obj_tag(v_manifestFile_x3f_3475_) == 1)
{
lean_object* v_val_3523_; lean_object* v_val_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; 
v_val_3523_ = lean_ctor_get(v_a_3522_, 0);
lean_inc_n(v_val_3523_, 2);
lean_dec_ref_known(v_a_3522_, 1);
v_val_3524_ = lean_ctor_get(v_manifestFile_x3f_3475_, 0);
lean_inc(v_val_3524_);
v___x_3525_ = l_Lake_joinRelative(v_val_3523_, v_val_3524_);
v___x_3526_ = lean_unsigned_to_nat(0u);
v___x_3527_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_3528_ = l_Lake_Manifest_load(v___x_3525_);
if (lean_obj_tag(v___x_3528_) == 0)
{
lean_object* v_a_3529_; lean_object* v___x_3531_; uint8_t v_isShared_3532_; uint8_t v_isSharedCheck_3536_; 
v_a_3529_ = lean_ctor_get(v___x_3528_, 0);
v_isSharedCheck_3536_ = !lean_is_exclusive(v___x_3528_);
if (v_isSharedCheck_3536_ == 0)
{
v___x_3531_ = v___x_3528_;
v_isShared_3532_ = v_isSharedCheck_3536_;
goto v_resetjp_3530_;
}
else
{
lean_inc(v_a_3529_);
lean_dec(v___x_3528_);
v___x_3531_ = lean_box(0);
v_isShared_3532_ = v_isSharedCheck_3536_;
goto v_resetjp_3530_;
}
v_resetjp_3530_:
{
lean_object* v___x_3534_; 
if (v_isShared_3532_ == 0)
{
lean_ctor_set_tag(v___x_3531_, 1);
v___x_3534_ = v___x_3531_;
goto v_reusejp_3533_;
}
else
{
lean_object* v_reuseFailAlloc_3535_; 
v_reuseFailAlloc_3535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3535_, 0, v_a_3529_);
v___x_3534_ = v_reuseFailAlloc_3535_;
goto v_reusejp_3533_;
}
v_reusejp_3533_:
{
v___y_3491_ = v___x_3527_;
v___y_3492_ = v___x_3526_;
v___y_3493_ = v_val_3523_;
v_val_3494_ = v___x_3534_;
goto v___jp_3490_;
}
}
}
else
{
lean_object* v_a_3537_; lean_object* v___x_3539_; uint8_t v_isShared_3540_; uint8_t v_isSharedCheck_3544_; 
v_a_3537_ = lean_ctor_get(v___x_3528_, 0);
v_isSharedCheck_3544_ = !lean_is_exclusive(v___x_3528_);
if (v_isSharedCheck_3544_ == 0)
{
v___x_3539_ = v___x_3528_;
v_isShared_3540_ = v_isSharedCheck_3544_;
goto v_resetjp_3538_;
}
else
{
lean_inc(v_a_3537_);
lean_dec(v___x_3528_);
v___x_3539_ = lean_box(0);
v_isShared_3540_ = v_isSharedCheck_3544_;
goto v_resetjp_3538_;
}
v_resetjp_3538_:
{
lean_object* v___x_3542_; 
if (v_isShared_3540_ == 0)
{
lean_ctor_set_tag(v___x_3539_, 0);
v___x_3542_ = v___x_3539_;
goto v_reusejp_3541_;
}
else
{
lean_object* v_reuseFailAlloc_3543_; 
v_reuseFailAlloc_3543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3543_, 0, v_a_3537_);
v___x_3542_ = v_reuseFailAlloc_3543_;
goto v_reusejp_3541_;
}
v_reusejp_3541_:
{
v___y_3491_ = v___x_3527_;
v___y_3492_ = v___x_3526_;
v___y_3493_ = v_val_3523_;
v_val_3494_ = v___x_3542_;
goto v___jp_3490_;
}
}
}
}
else
{
lean_object* v_val_3545_; lean_object* v___x_3546_; 
v_val_3545_ = lean_ctor_get(v_a_3522_, 0);
lean_inc(v_val_3545_);
lean_dec_ref_known(v_a_3522_, 1);
v___x_3546_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1));
v___y_3484_ = v_val_3545_;
v_a_3485_ = v___x_3546_;
goto v___jp_3483_;
}
}
else
{
uint8_t v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; uint8_t v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; 
lean_inc(v_name_3474_);
lean_dec(v_a_3522_);
lean_del_object(v___x_3478_);
lean_dec_ref(v_dir_3476_);
lean_dec_ref(v_manifestEntry_3427_);
v___x_3547_ = 0;
v___x_3548_ = l_Lean_Name_toString(v_name_3474_, v___x_3547_);
v___x_3549_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0));
v___x_3550_ = lean_string_append(v___x_3548_, v___x_3549_);
v___x_3551_ = lean_string_append(v___x_3550_, v_pkgDir_3480_);
lean_dec_ref(v_pkgDir_3480_);
v___x_3552_ = 3;
v___x_3553_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3553_, 0, v___x_3551_);
lean_ctor_set_uint8(v___x_3553_, sizeof(void*)*1, v___x_3552_);
lean_inc_ref(v_a_3431_);
v___x_3554_ = lean_apply_2(v_a_3431_, v___x_3553_, lean_box(0));
v___x_3555_ = lean_box(0);
v___x_3556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3556_, 0, v___x_3555_);
return v___x_3556_;
}
}
v___jp_3559_:
{
uint8_t v___x_3561_; 
v___x_3561_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_3561_ == 0)
{
v_a_3522_ = v_val_3560_;
goto v___jp_3521_;
}
else
{
lean_object* v___x_3562_; uint8_t v___x_3563_; 
v___x_3562_ = lean_box(0);
v___x_3563_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
if (v___x_3563_ == 0)
{
if (v___x_3561_ == 0)
{
v_a_3522_ = v_val_3560_;
goto v___jp_3521_;
}
else
{
size_t v___x_3564_; size_t v___x_3565_; lean_object* v___x_3566_; 
v___x_3564_ = ((size_t)0ULL);
v___x_3565_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8);
v___x_3566_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_3558_, v___x_3564_, v___x_3565_, v___x_3562_, v_a_3431_);
if (lean_obj_tag(v___x_3566_) == 0)
{
lean_dec_ref_known(v___x_3566_, 1);
v_a_3522_ = v_val_3560_;
goto v___jp_3521_;
}
else
{
lean_object* v_a_3567_; lean_object* v___x_3569_; uint8_t v_isShared_3570_; uint8_t v_isSharedCheck_3574_; 
lean_dec(v_val_3560_);
lean_dec_ref(v_pkgDir_3480_);
lean_del_object(v___x_3478_);
lean_dec_ref(v_dir_3476_);
lean_dec_ref(v_manifestEntry_3427_);
v_a_3567_ = lean_ctor_get(v___x_3566_, 0);
v_isSharedCheck_3574_ = !lean_is_exclusive(v___x_3566_);
if (v_isSharedCheck_3574_ == 0)
{
v___x_3569_ = v___x_3566_;
v_isShared_3570_ = v_isSharedCheck_3574_;
goto v_resetjp_3568_;
}
else
{
lean_inc(v_a_3567_);
lean_dec(v___x_3566_);
v___x_3569_ = lean_box(0);
v_isShared_3570_ = v_isSharedCheck_3574_;
goto v_resetjp_3568_;
}
v_resetjp_3568_:
{
lean_object* v___x_3572_; 
if (v_isShared_3570_ == 0)
{
v___x_3572_ = v___x_3569_;
goto v_reusejp_3571_;
}
else
{
lean_object* v_reuseFailAlloc_3573_; 
v_reuseFailAlloc_3573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3573_, 0, v_a_3567_);
v___x_3572_ = v_reuseFailAlloc_3573_;
goto v_reusejp_3571_;
}
v_reusejp_3571_:
{
return v___x_3572_;
}
}
}
}
}
else
{
size_t v___x_3575_; size_t v___x_3576_; lean_object* v___x_3577_; 
v___x_3575_ = ((size_t)0ULL);
v___x_3576_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__8);
v___x_3577_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_3558_, v___x_3575_, v___x_3576_, v___x_3562_, v_a_3431_);
if (lean_obj_tag(v___x_3577_) == 0)
{
lean_dec_ref_known(v___x_3577_, 1);
v_a_3522_ = v_val_3560_;
goto v___jp_3521_;
}
else
{
lean_object* v_a_3578_; lean_object* v___x_3580_; uint8_t v_isShared_3581_; uint8_t v_isSharedCheck_3585_; 
lean_dec(v_val_3560_);
lean_dec_ref(v_pkgDir_3480_);
lean_del_object(v___x_3478_);
lean_dec_ref(v_dir_3476_);
lean_dec_ref(v_manifestEntry_3427_);
v_a_3578_ = lean_ctor_get(v___x_3577_, 0);
v_isSharedCheck_3585_ = !lean_is_exclusive(v___x_3577_);
if (v_isSharedCheck_3585_ == 0)
{
v___x_3580_ = v___x_3577_;
v_isShared_3581_ = v_isSharedCheck_3585_;
goto v_resetjp_3579_;
}
else
{
lean_inc(v_a_3578_);
lean_dec(v___x_3577_);
v___x_3580_ = lean_box(0);
v_isShared_3581_ = v_isSharedCheck_3585_;
goto v_resetjp_3579_;
}
v_resetjp_3579_:
{
lean_object* v___x_3583_; 
if (v_isShared_3581_ == 0)
{
v___x_3583_ = v___x_3580_;
goto v_reusejp_3582_;
}
else
{
lean_object* v_reuseFailAlloc_3584_; 
v_reuseFailAlloc_3584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3584_, 0, v_a_3578_);
v___x_3583_ = v_reuseFailAlloc_3584_;
goto v_reusejp_3582_;
}
v_reusejp_3582_:
{
return v___x_3583_;
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
lean_object* v_name_3591_; lean_object* v_manifestFile_x3f_3592_; lean_object* v_url_3593_; lean_object* v_rev_3594_; lean_object* v_subDir_x3f_3595_; lean_object* v_pkgUrlMap_3596_; uint8_t v___x_3597_; lean_object* v___x_3598_; lean_object* v___y_3600_; lean_object* v___y_3601_; lean_object* v___y_3602_; lean_object* v_a_3603_; lean_object* v___y_3637_; lean_object* v___y_3638_; lean_object* v___y_3639_; lean_object* v___y_3640_; lean_object* v___y_3641_; lean_object* v_val_3642_; lean_object* v_relGitDir_3669_; lean_object* v_repo_3670_; lean_object* v_url_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; 
v_name_3591_ = lean_ctor_get(v_manifestEntry_3427_, 0);
v_manifestFile_x3f_3592_ = lean_ctor_get(v_manifestEntry_3427_, 3);
v_url_3593_ = lean_ctor_get(v_src_3473_, 0);
lean_inc_ref(v_url_3593_);
v_rev_3594_ = lean_ctor_get(v_src_3473_, 1);
lean_inc_ref(v_rev_3594_);
v_subDir_x3f_3595_ = lean_ctor_get(v_src_3473_, 3);
lean_inc(v_subDir_x3f_3595_);
lean_dec_ref_known(v_src_3473_, 4);
v_pkgUrlMap_3596_ = lean_ctor_get(v_lakeEnv_3428_, 5);
v___x_3597_ = 0;
lean_inc(v_name_3591_);
v___x_3598_ = l_Lean_Name_toString(v_name_3591_, v___x_3597_);
lean_inc_ref_n(v___x_3598_, 2);
v_relGitDir_3669_ = l_Lake_joinRelative(v_relPkgsDir_3430_, v___x_3598_);
lean_inc_ref(v_relGitDir_3669_);
lean_inc_ref(v_wsDir_3429_);
v_repo_3670_ = l_Lake_joinRelative(v_wsDir_3429_, v_relGitDir_3669_);
v_url_3671_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lake_PackageEntry_materialize_spec__0___redArg(v_pkgUrlMap_3596_, v_name_3591_, v_url_3593_);
lean_dec_ref(v_url_3593_);
v___x_3672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3672_, 0, v_rev_3594_);
lean_inc(v_url_3671_);
v___x_3673_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(v_a_3431_, v___x_3598_, v_repo_3670_, v_url_3671_, v___x_3672_);
if (lean_obj_tag(v___x_3673_) == 0)
{
lean_object* v___y_3675_; lean_object* v___y_3676_; lean_object* v___y_3686_; 
lean_dec_ref_known(v___x_3673_, 1);
if (lean_obj_tag(v_subDir_x3f_3595_) == 0)
{
v___y_3686_ = v_relGitDir_3669_;
goto v___jp_3685_;
}
else
{
lean_object* v_val_3690_; lean_object* v___x_3691_; 
v_val_3690_ = lean_ctor_get(v_subDir_x3f_3595_, 0);
lean_inc(v_val_3690_);
lean_dec_ref_known(v_subDir_x3f_3595_, 1);
v___x_3691_ = l_Lake_joinRelative(v_relGitDir_3669_, v_val_3690_);
v___y_3686_ = v___x_3691_;
goto v___jp_3685_;
}
v___jp_3674_:
{
lean_object* v_pkgDir_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; uint8_t v___x_3682_; 
lean_inc_ref(v___y_3675_);
v_pkgDir_3677_ = l_Lake_joinRelative(v_wsDir_3429_, v___y_3675_);
lean_inc_ref(v_pkgDir_3677_);
v___x_3678_ = l_Lake_resolvePath(v_pkgDir_3677_);
v___x_3679_ = lean_unsigned_to_nat(0u);
v___x_3680_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_3681_ = lean_string_utf8_byte_size(v___x_3678_);
v___x_3682_ = lean_nat_dec_eq(v___x_3681_, v___x_3679_);
if (v___x_3682_ == 0)
{
lean_object* v___x_3683_; 
v___x_3683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3683_, 0, v___x_3678_);
v___y_3637_ = v___x_3680_;
v___y_3638_ = v___y_3676_;
v___y_3639_ = v___y_3675_;
v___y_3640_ = v_pkgDir_3677_;
v___y_3641_ = v___x_3679_;
v_val_3642_ = v___x_3683_;
goto v___jp_3636_;
}
else
{
lean_object* v___x_3684_; 
lean_dec_ref(v___x_3678_);
v___x_3684_ = lean_box(0);
v___y_3637_ = v___x_3680_;
v___y_3638_ = v___y_3676_;
v___y_3639_ = v___y_3675_;
v___y_3640_ = v_pkgDir_3677_;
v___y_3641_ = v___x_3679_;
v_val_3642_ = v___x_3684_;
goto v___jp_3636_;
}
}
v___jp_3685_:
{
lean_object* v___x_3687_; 
v___x_3687_ = l_Lake_Git_filterUrl_x3f(v_url_3671_);
if (lean_obj_tag(v___x_3687_) == 0)
{
lean_object* v___x_3688_; 
v___x_3688_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___y_3675_ = v___y_3686_;
v___y_3676_ = v___x_3688_;
goto v___jp_3674_;
}
else
{
lean_object* v_val_3689_; 
v_val_3689_ = lean_ctor_get(v___x_3687_, 0);
lean_inc(v_val_3689_);
lean_dec_ref_known(v___x_3687_, 1);
v___y_3675_ = v___y_3686_;
v___y_3676_ = v_val_3689_;
goto v___jp_3674_;
}
}
}
else
{
lean_object* v_a_3692_; lean_object* v___x_3694_; uint8_t v_isShared_3695_; uint8_t v_isSharedCheck_3699_; 
lean_dec(v_url_3671_);
lean_dec_ref(v_relGitDir_3669_);
lean_dec_ref(v___x_3598_);
lean_dec(v_subDir_x3f_3595_);
lean_dec_ref(v_wsDir_3429_);
lean_dec_ref(v_manifestEntry_3427_);
v_a_3692_ = lean_ctor_get(v___x_3673_, 0);
v_isSharedCheck_3699_ = !lean_is_exclusive(v___x_3673_);
if (v_isSharedCheck_3699_ == 0)
{
v___x_3694_ = v___x_3673_;
v_isShared_3695_ = v_isSharedCheck_3699_;
goto v_resetjp_3693_;
}
else
{
lean_inc(v_a_3692_);
lean_dec(v___x_3673_);
v___x_3694_ = lean_box(0);
v_isShared_3695_ = v_isSharedCheck_3699_;
goto v_resetjp_3693_;
}
v_resetjp_3693_:
{
lean_object* v___x_3697_; 
if (v_isShared_3695_ == 0)
{
v___x_3697_ = v___x_3694_;
goto v_reusejp_3696_;
}
else
{
lean_object* v_reuseFailAlloc_3698_; 
v_reuseFailAlloc_3698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3698_, 0, v_a_3692_);
v___x_3697_ = v_reuseFailAlloc_3698_;
goto v_reusejp_3696_;
}
v_reusejp_3696_:
{
return v___x_3697_;
}
}
}
v___jp_3599_:
{
if (lean_obj_tag(v_a_3603_) == 1)
{
lean_dec_ref(v___y_3601_);
lean_dec_ref(v___x_3598_);
if (lean_obj_tag(v_manifestFile_x3f_3592_) == 1)
{
lean_object* v_val_3604_; lean_object* v_val_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; 
v_val_3604_ = lean_ctor_get(v_a_3603_, 0);
lean_inc_n(v_val_3604_, 2);
lean_dec_ref_known(v_a_3603_, 1);
v_val_3605_ = lean_ctor_get(v_manifestFile_x3f_3592_, 0);
lean_inc(v_val_3605_);
v___x_3606_ = l_Lake_joinRelative(v_val_3604_, v_val_3605_);
v___x_3607_ = lean_unsigned_to_nat(0u);
v___x_3608_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_3609_ = l_Lake_Manifest_load(v___x_3606_);
if (lean_obj_tag(v___x_3609_) == 0)
{
lean_object* v_a_3610_; lean_object* v___x_3612_; uint8_t v_isShared_3613_; uint8_t v_isSharedCheck_3617_; 
v_a_3610_ = lean_ctor_get(v___x_3609_, 0);
v_isSharedCheck_3617_ = !lean_is_exclusive(v___x_3609_);
if (v_isSharedCheck_3617_ == 0)
{
v___x_3612_ = v___x_3609_;
v_isShared_3613_ = v_isSharedCheck_3617_;
goto v_resetjp_3611_;
}
else
{
lean_inc(v_a_3610_);
lean_dec(v___x_3609_);
v___x_3612_ = lean_box(0);
v_isShared_3613_ = v_isSharedCheck_3617_;
goto v_resetjp_3611_;
}
v_resetjp_3611_:
{
lean_object* v___x_3615_; 
if (v_isShared_3613_ == 0)
{
lean_ctor_set_tag(v___x_3612_, 1);
v___x_3615_ = v___x_3612_;
goto v_reusejp_3614_;
}
else
{
lean_object* v_reuseFailAlloc_3616_; 
v_reuseFailAlloc_3616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3616_, 0, v_a_3610_);
v___x_3615_ = v_reuseFailAlloc_3616_;
goto v_reusejp_3614_;
}
v_reusejp_3614_:
{
v___y_3441_ = v___x_3607_;
v___y_3442_ = v___y_3600_;
v___y_3443_ = v_val_3604_;
v___y_3444_ = v___y_3602_;
v___y_3445_ = v___x_3608_;
v_val_3446_ = v___x_3615_;
goto v___jp_3440_;
}
}
}
else
{
lean_object* v_a_3618_; lean_object* v___x_3620_; uint8_t v_isShared_3621_; uint8_t v_isSharedCheck_3625_; 
v_a_3618_ = lean_ctor_get(v___x_3609_, 0);
v_isSharedCheck_3625_ = !lean_is_exclusive(v___x_3609_);
if (v_isSharedCheck_3625_ == 0)
{
v___x_3620_ = v___x_3609_;
v_isShared_3621_ = v_isSharedCheck_3625_;
goto v_resetjp_3619_;
}
else
{
lean_inc(v_a_3618_);
lean_dec(v___x_3609_);
v___x_3620_ = lean_box(0);
v_isShared_3621_ = v_isSharedCheck_3625_;
goto v_resetjp_3619_;
}
v_resetjp_3619_:
{
lean_object* v___x_3623_; 
if (v_isShared_3621_ == 0)
{
lean_ctor_set_tag(v___x_3620_, 0);
v___x_3623_ = v___x_3620_;
goto v_reusejp_3622_;
}
else
{
lean_object* v_reuseFailAlloc_3624_; 
v_reuseFailAlloc_3624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3624_, 0, v_a_3618_);
v___x_3623_ = v_reuseFailAlloc_3624_;
goto v_reusejp_3622_;
}
v_reusejp_3622_:
{
v___y_3441_ = v___x_3607_;
v___y_3442_ = v___y_3600_;
v___y_3443_ = v_val_3604_;
v___y_3444_ = v___y_3602_;
v___y_3445_ = v___x_3608_;
v_val_3446_ = v___x_3623_;
goto v___jp_3440_;
}
}
}
}
else
{
lean_object* v_val_3626_; lean_object* v___x_3627_; 
v_val_3626_ = lean_ctor_get(v_a_3603_, 0);
lean_inc(v_val_3626_);
lean_dec_ref_known(v_a_3603_, 1);
v___x_3627_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1));
v___y_3434_ = v___y_3600_;
v___y_3435_ = v___y_3602_;
v___y_3436_ = v_val_3626_;
v_a_3437_ = v___x_3627_;
goto v___jp_3433_;
}
}
else
{
lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; uint8_t v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; 
lean_dec(v_a_3603_);
lean_dec_ref(v___y_3602_);
lean_dec_ref(v___y_3600_);
lean_dec_ref(v_manifestEntry_3427_);
v___x_3628_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0));
v___x_3629_ = lean_string_append(v___x_3598_, v___x_3628_);
v___x_3630_ = lean_string_append(v___x_3629_, v___y_3601_);
lean_dec_ref(v___y_3601_);
v___x_3631_ = 3;
v___x_3632_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3632_, 0, v___x_3630_);
lean_ctor_set_uint8(v___x_3632_, sizeof(void*)*1, v___x_3631_);
lean_inc_ref(v_a_3431_);
v___x_3633_ = lean_apply_2(v_a_3431_, v___x_3632_, lean_box(0));
v___x_3634_ = lean_box(0);
v___x_3635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3635_, 0, v___x_3634_);
return v___x_3635_;
}
}
v___jp_3636_:
{
lean_object* v___x_3643_; uint8_t v___x_3644_; 
v___x_3643_ = lean_array_get_size(v___y_3637_);
v___x_3644_ = lean_nat_dec_lt(v___y_3641_, v___x_3643_);
if (v___x_3644_ == 0)
{
v___y_3600_ = v___y_3638_;
v___y_3601_ = v___y_3640_;
v___y_3602_ = v___y_3639_;
v_a_3603_ = v_val_3642_;
goto v___jp_3599_;
}
else
{
lean_object* v___x_3645_; uint8_t v___x_3646_; 
v___x_3645_ = lean_box(0);
v___x_3646_ = lean_nat_dec_le(v___x_3643_, v___x_3643_);
if (v___x_3646_ == 0)
{
if (v___x_3644_ == 0)
{
v___y_3600_ = v___y_3638_;
v___y_3601_ = v___y_3640_;
v___y_3602_ = v___y_3639_;
v_a_3603_ = v_val_3642_;
goto v___jp_3599_;
}
else
{
size_t v___x_3647_; size_t v___x_3648_; lean_object* v___x_3649_; 
v___x_3647_ = ((size_t)0ULL);
v___x_3648_ = lean_usize_of_nat(v___x_3643_);
v___x_3649_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_3637_, v___x_3647_, v___x_3648_, v___x_3645_, v_a_3431_);
if (lean_obj_tag(v___x_3649_) == 0)
{
lean_dec_ref_known(v___x_3649_, 1);
v___y_3600_ = v___y_3638_;
v___y_3601_ = v___y_3640_;
v___y_3602_ = v___y_3639_;
v_a_3603_ = v_val_3642_;
goto v___jp_3599_;
}
else
{
lean_object* v_a_3650_; lean_object* v___x_3652_; uint8_t v_isShared_3653_; uint8_t v_isSharedCheck_3657_; 
lean_dec(v_val_3642_);
lean_dec_ref(v___y_3640_);
lean_dec_ref(v___y_3639_);
lean_dec_ref(v___y_3638_);
lean_dec_ref(v___x_3598_);
lean_dec_ref(v_manifestEntry_3427_);
v_a_3650_ = lean_ctor_get(v___x_3649_, 0);
v_isSharedCheck_3657_ = !lean_is_exclusive(v___x_3649_);
if (v_isSharedCheck_3657_ == 0)
{
v___x_3652_ = v___x_3649_;
v_isShared_3653_ = v_isSharedCheck_3657_;
goto v_resetjp_3651_;
}
else
{
lean_inc(v_a_3650_);
lean_dec(v___x_3649_);
v___x_3652_ = lean_box(0);
v_isShared_3653_ = v_isSharedCheck_3657_;
goto v_resetjp_3651_;
}
v_resetjp_3651_:
{
lean_object* v___x_3655_; 
if (v_isShared_3653_ == 0)
{
v___x_3655_ = v___x_3652_;
goto v_reusejp_3654_;
}
else
{
lean_object* v_reuseFailAlloc_3656_; 
v_reuseFailAlloc_3656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3656_, 0, v_a_3650_);
v___x_3655_ = v_reuseFailAlloc_3656_;
goto v_reusejp_3654_;
}
v_reusejp_3654_:
{
return v___x_3655_;
}
}
}
}
}
else
{
size_t v___x_3658_; size_t v___x_3659_; lean_object* v___x_3660_; 
v___x_3658_ = ((size_t)0ULL);
v___x_3659_ = lean_usize_of_nat(v___x_3643_);
v___x_3660_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_3637_, v___x_3658_, v___x_3659_, v___x_3645_, v_a_3431_);
if (lean_obj_tag(v___x_3660_) == 0)
{
lean_dec_ref_known(v___x_3660_, 1);
v___y_3600_ = v___y_3638_;
v___y_3601_ = v___y_3640_;
v___y_3602_ = v___y_3639_;
v_a_3603_ = v_val_3642_;
goto v___jp_3599_;
}
else
{
lean_object* v_a_3661_; lean_object* v___x_3663_; uint8_t v_isShared_3664_; uint8_t v_isSharedCheck_3668_; 
lean_dec(v_val_3642_);
lean_dec_ref(v___y_3640_);
lean_dec_ref(v___y_3639_);
lean_dec_ref(v___y_3638_);
lean_dec_ref(v___x_3598_);
lean_dec_ref(v_manifestEntry_3427_);
v_a_3661_ = lean_ctor_get(v___x_3660_, 0);
v_isSharedCheck_3668_ = !lean_is_exclusive(v___x_3660_);
if (v_isSharedCheck_3668_ == 0)
{
v___x_3663_ = v___x_3660_;
v_isShared_3664_ = v_isSharedCheck_3668_;
goto v_resetjp_3662_;
}
else
{
lean_inc(v_a_3661_);
lean_dec(v___x_3660_);
v___x_3663_ = lean_box(0);
v_isShared_3664_ = v_isSharedCheck_3668_;
goto v_resetjp_3662_;
}
v_resetjp_3662_:
{
lean_object* v___x_3666_; 
if (v_isShared_3664_ == 0)
{
v___x_3666_ = v___x_3663_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v_a_3661_);
v___x_3666_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
return v___x_3666_;
}
}
}
}
}
}
}
v___jp_3433_:
{
lean_object* v___x_3438_; lean_object* v___x_3439_; 
v___x_3438_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3438_, 0, v___y_3436_);
lean_ctor_set(v___x_3438_, 1, v___y_3435_);
lean_ctor_set(v___x_3438_, 2, v___y_3434_);
lean_ctor_set(v___x_3438_, 3, v_a_3437_);
lean_ctor_set(v___x_3438_, 4, v_manifestEntry_3427_);
v___x_3439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3439_, 0, v___x_3438_);
return v___x_3439_;
}
v___jp_3440_:
{
lean_object* v___x_3447_; uint8_t v___x_3448_; 
v___x_3447_ = lean_array_get_size(v___y_3445_);
v___x_3448_ = lean_nat_dec_lt(v___y_3441_, v___x_3447_);
if (v___x_3448_ == 0)
{
v___y_3434_ = v___y_3442_;
v___y_3435_ = v___y_3444_;
v___y_3436_ = v___y_3443_;
v_a_3437_ = v_val_3446_;
goto v___jp_3433_;
}
else
{
lean_object* v___x_3449_; uint8_t v___x_3450_; 
v___x_3449_ = lean_box(0);
v___x_3450_ = lean_nat_dec_le(v___x_3447_, v___x_3447_);
if (v___x_3450_ == 0)
{
if (v___x_3448_ == 0)
{
v___y_3434_ = v___y_3442_;
v___y_3435_ = v___y_3444_;
v___y_3436_ = v___y_3443_;
v_a_3437_ = v_val_3446_;
goto v___jp_3433_;
}
else
{
size_t v___x_3451_; size_t v___x_3452_; lean_object* v___x_3453_; 
v___x_3451_ = ((size_t)0ULL);
v___x_3452_ = lean_usize_of_nat(v___x_3447_);
v___x_3453_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_3445_, v___x_3451_, v___x_3452_, v___x_3449_, v_a_3431_);
if (lean_obj_tag(v___x_3453_) == 0)
{
lean_dec_ref_known(v___x_3453_, 1);
v___y_3434_ = v___y_3442_;
v___y_3435_ = v___y_3444_;
v___y_3436_ = v___y_3443_;
v_a_3437_ = v_val_3446_;
goto v___jp_3433_;
}
else
{
lean_object* v_a_3454_; lean_object* v___x_3456_; uint8_t v_isShared_3457_; uint8_t v_isSharedCheck_3461_; 
lean_dec_ref(v_val_3446_);
lean_dec_ref(v___y_3444_);
lean_dec_ref(v___y_3443_);
lean_dec_ref(v___y_3442_);
lean_dec_ref(v_manifestEntry_3427_);
v_a_3454_ = lean_ctor_get(v___x_3453_, 0);
v_isSharedCheck_3461_ = !lean_is_exclusive(v___x_3453_);
if (v_isSharedCheck_3461_ == 0)
{
v___x_3456_ = v___x_3453_;
v_isShared_3457_ = v_isSharedCheck_3461_;
goto v_resetjp_3455_;
}
else
{
lean_inc(v_a_3454_);
lean_dec(v___x_3453_);
v___x_3456_ = lean_box(0);
v_isShared_3457_ = v_isSharedCheck_3461_;
goto v_resetjp_3455_;
}
v_resetjp_3455_:
{
lean_object* v___x_3459_; 
if (v_isShared_3457_ == 0)
{
v___x_3459_ = v___x_3456_;
goto v_reusejp_3458_;
}
else
{
lean_object* v_reuseFailAlloc_3460_; 
v_reuseFailAlloc_3460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3460_, 0, v_a_3454_);
v___x_3459_ = v_reuseFailAlloc_3460_;
goto v_reusejp_3458_;
}
v_reusejp_3458_:
{
return v___x_3459_;
}
}
}
}
}
else
{
size_t v___x_3462_; size_t v___x_3463_; lean_object* v___x_3464_; 
v___x_3462_ = ((size_t)0ULL);
v___x_3463_ = lean_usize_of_nat(v___x_3447_);
v___x_3464_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_3445_, v___x_3462_, v___x_3463_, v___x_3449_, v_a_3431_);
if (lean_obj_tag(v___x_3464_) == 0)
{
lean_dec_ref_known(v___x_3464_, 1);
v___y_3434_ = v___y_3442_;
v___y_3435_ = v___y_3444_;
v___y_3436_ = v___y_3443_;
v_a_3437_ = v_val_3446_;
goto v___jp_3433_;
}
else
{
lean_object* v_a_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3472_; 
lean_dec_ref(v_val_3446_);
lean_dec_ref(v___y_3444_);
lean_dec_ref(v___y_3443_);
lean_dec_ref(v___y_3442_);
lean_dec_ref(v_manifestEntry_3427_);
v_a_3465_ = lean_ctor_get(v___x_3464_, 0);
v_isSharedCheck_3472_ = !lean_is_exclusive(v___x_3464_);
if (v_isSharedCheck_3472_ == 0)
{
v___x_3467_ = v___x_3464_;
v_isShared_3468_ = v_isSharedCheck_3472_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_a_3465_);
lean_dec(v___x_3464_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3472_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
lean_object* v___x_3470_; 
if (v_isShared_3468_ == 0)
{
v___x_3470_ = v___x_3467_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v_a_3465_);
v___x_3470_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3469_;
}
v_reusejp_3469_:
{
return v___x_3470_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize___boxed(lean_object* v_manifestEntry_3700_, lean_object* v_lakeEnv_3701_, lean_object* v_wsDir_3702_, lean_object* v_relPkgsDir_3703_, lean_object* v_a_3704_, lean_object* v_a_3705_){
_start:
{
lean_object* v_res_3706_; 
v_res_3706_ = l_Lake_PackageEntry_materialize(v_manifestEntry_3700_, v_lakeEnv_3701_, v_wsDir_3702_, v_relPkgsDir_3703_, v_a_3704_);
lean_dec_ref(v_a_3704_);
lean_dec_ref(v_lakeEnv_3701_);
return v_res_3706_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lake_PackageEntry_materialize_spec__0(lean_object* v_00_u03b4_3707_, lean_object* v_t_3708_, lean_object* v_k_3709_, lean_object* v_fallback_3710_){
_start:
{
lean_object* v___x_3711_; 
v___x_3711_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lake_PackageEntry_materialize_spec__0___redArg(v_t_3708_, v_k_3709_, v_fallback_3710_);
return v___x_3711_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lake_PackageEntry_materialize_spec__0___boxed(lean_object* v_00_u03b4_3712_, lean_object* v_t_3713_, lean_object* v_k_3714_, lean_object* v_fallback_3715_){
_start:
{
lean_object* v_res_3716_; 
v_res_3716_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lake_PackageEntry_materialize_spec__0(v_00_u03b4_3712_, v_t_3713_, v_k_3714_, v_fallback_3715_);
lean_dec(v_fallback_3715_);
lean_dec(v_k_3714_);
lean_dec(v_t_3713_);
return v_res_3716_;
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

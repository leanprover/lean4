// Lean compiler output
// Module: Lake.Load.Materialize
// Imports: public import Lake.Config.Env public import Lake.Load.Manifest public import Lake.Config.Package import Lake.Util.Git import Lake.Config.Dependency import Lake.Reservoir
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
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_configFile(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorIdx___boxed(lean_object*);
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__1;
extern lean_object* l_System_instInhabitedFilePath_default;
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_none_elim___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
static lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__3;
lean_object* l_Lake_Reservoir_fetchPkgVersions(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__1;
static lean_object* l_Lake_Dependency_materialize___closed__3;
lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__3;
lean_object* l_String_quote(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__2;
static lean_object* l_Lake_Dependency_materialize___closed__6;
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_name(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint8_t l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6;
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Dependency_materialize___closed__5;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedMaterializedDep_default;
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1_spec__1___redArg(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
extern lean_object* l_Lake_instInhabitedPackageEntry_default;
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_resolveRemoteRevision(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lake_Dependency_materialize___closed__8;
static lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Dependency_materialize___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_System_FilePath_isDir(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_git_elim(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_StdVer_toString(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__6;
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_configFile___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ver_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_name___boxed(lean_object*);
static lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0;
uint8_t l_Option_instDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_none_elim(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_removeDirAll(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_manifestFile_x3f___boxed(lean_object*);
lean_object* l_Lake_Git_filterUrl_x3f(lean_object*);
lean_object* l_Lake_GitRepo_clone(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_resolveRevision_x3f(lean_object*, lean_object*);
static lean_object* l_Lake_Dependency_materialize___closed__9;
static lean_object* l_Lake_Dependency_materialize___closed__11;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep(lean_object*, lean_object*, lean_object*);
static lean_object* l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg(lean_object*);
lean_object* l_Lake_GitRepo_findRemoteRevision(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_GitRepo_hasNoDiff(lean_object*);
lean_object* l_Lake_GitRepo_getHeadRevision(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_manifestFile_x3f(lean_object*);
extern lean_object* l_Std_Format_defWidth;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_Git_defaultRemote;
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instInhabitedMaterializedDep_default___closed__1;
lean_object* l_Lake_Reservoir_fetchPkg_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Dependency_materialize___closed__10;
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__5;
static lean_object* l_Lake_PackageEntry_materialize___closed__0;
lean_object* l_Lake_GitRepo_checkoutDetach(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1;
static lean_object* l_Lake_Dependency_materialize___closed__7;
static lean_object* l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___closed__0;
static lean_object* l_Lake_Dependency_materialize___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_git_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__7;
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l_Lake_VerRange_test(lean_object*, lean_object*);
static lean_object* l_Lake_instInhabitedMaterializedDep_default___closed__0;
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_scope(lean_object*);
static lean_object* l_Lake_Dependency_materialize___closed__4;
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_RegistryPkg_gitSrc_x3f(lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
static lean_object* l_Lake_Dependency_materialize___closed__2;
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_scope___boxed(lean_object*);
lean_object* lean_io_realpath(lean_object*);
static lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3;
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__2;
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__4;
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__0;
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___boxed(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static size_t l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
extern lean_object* l_Lake_defaultConfigFile;
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_getRemoteUrl_x3f(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint8_t l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ver_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4;
lean_object* l___private_Lake_Util_Version_0__Lake_runVerParse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorIdx(lean_object*);
extern uint8_t l_System_Platform_isWindows;
LEAN_EXPORT lean_object* l_Lake_instInhabitedMaterializedDep;
static lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0;
lean_object* l_instDecidableEqString___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
x_8 = lean_array_uget(x_1, x_2);
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
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": repository '", 14, 14);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' has local changes", 19, 19);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": checking out revision '", 25, 25);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_6; lean_object* x_7; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_35; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_92; lean_object* x_96; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_100 = l_Lake_Git_defaultRemote;
x_101 = lean_unsigned_to_nat(0u);
x_102 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
lean_inc_ref(x_2);
x_103 = l_Lake_GitRepo_findRemoteRevision(x_2, x_3, x_100, x_102);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_134; uint8_t x_135; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec_ref(x_103);
x_134 = lean_array_get_size(x_105);
x_135 = lean_nat_dec_lt(x_101, x_134);
if (x_135 == 0)
{
lean_dec(x_105);
x_106 = lean_box(0);
goto block_133;
}
else
{
lean_object* x_136; uint8_t x_137; 
x_136 = lean_box(0);
x_137 = lean_nat_dec_le(x_134, x_134);
if (x_137 == 0)
{
if (x_135 == 0)
{
lean_dec(x_105);
x_106 = lean_box(0);
goto block_133;
}
else
{
size_t x_138; size_t x_139; lean_object* x_140; 
x_138 = 0;
x_139 = lean_usize_of_nat(x_134);
lean_inc_ref(x_4);
x_140 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_105, x_138, x_139, x_136, x_4);
lean_dec(x_105);
if (lean_obj_tag(x_140) == 0)
{
lean_dec_ref(x_140);
x_106 = lean_box(0);
goto block_133;
}
else
{
lean_dec(x_104);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_140;
}
}
}
else
{
size_t x_141; size_t x_142; lean_object* x_143; 
x_141 = 0;
x_142 = lean_usize_of_nat(x_134);
lean_inc_ref(x_4);
x_143 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_105, x_141, x_142, x_136, x_4);
lean_dec(x_105);
if (lean_obj_tag(x_143) == 0)
{
lean_dec_ref(x_143);
x_106 = lean_box(0);
goto block_133;
}
else
{
lean_dec(x_104);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_143;
}
}
}
block_133:
{
lean_object* x_107; 
lean_inc_ref(x_2);
x_107 = l_Lake_GitRepo_getHeadRevision(x_2, x_102);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec_ref(x_107);
x_110 = lean_array_get_size(x_109);
x_111 = lean_nat_dec_lt(x_101, x_110);
if (x_111 == 0)
{
lean_dec(x_109);
x_39 = x_104;
x_40 = x_108;
x_41 = lean_box(0);
goto block_91;
}
else
{
lean_object* x_112; uint8_t x_113; 
x_112 = lean_box(0);
x_113 = lean_nat_dec_le(x_110, x_110);
if (x_113 == 0)
{
if (x_111 == 0)
{
lean_dec(x_109);
x_39 = x_104;
x_40 = x_108;
x_41 = lean_box(0);
goto block_91;
}
else
{
size_t x_114; size_t x_115; lean_object* x_116; 
x_114 = 0;
x_115 = lean_usize_of_nat(x_110);
lean_inc_ref(x_4);
x_116 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_109, x_114, x_115, x_112, x_4);
lean_dec(x_109);
if (lean_obj_tag(x_116) == 0)
{
lean_dec_ref(x_116);
x_39 = x_104;
x_40 = x_108;
x_41 = lean_box(0);
goto block_91;
}
else
{
lean_dec(x_108);
lean_dec(x_104);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_116;
}
}
}
else
{
size_t x_117; size_t x_118; lean_object* x_119; 
x_117 = 0;
x_118 = lean_usize_of_nat(x_110);
lean_inc_ref(x_4);
x_119 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_109, x_117, x_118, x_112, x_4);
lean_dec(x_109);
if (lean_obj_tag(x_119) == 0)
{
lean_dec_ref(x_119);
x_39 = x_104;
x_40 = x_108;
x_41 = lean_box(0);
goto block_91;
}
else
{
lean_dec(x_108);
lean_dec(x_104);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_119;
}
}
}
}
else
{
lean_object* x_120; lean_object* x_121; uint8_t x_122; 
lean_dec(x_104);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_120 = lean_ctor_get(x_107, 1);
lean_inc(x_120);
lean_dec_ref(x_107);
x_121 = lean_array_get_size(x_120);
x_122 = lean_nat_dec_lt(x_101, x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; 
lean_dec(x_120);
lean_dec_ref(x_4);
x_123 = lean_box(0);
x_124 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_124, 0, x_123);
return x_124;
}
else
{
lean_object* x_125; uint8_t x_126; 
x_125 = lean_box(0);
x_126 = lean_nat_dec_le(x_121, x_121);
if (x_126 == 0)
{
if (x_122 == 0)
{
lean_dec(x_120);
lean_dec_ref(x_4);
x_92 = lean_box(0);
goto block_95;
}
else
{
size_t x_127; size_t x_128; lean_object* x_129; 
x_127 = 0;
x_128 = lean_usize_of_nat(x_121);
x_129 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_120, x_127, x_128, x_125, x_4);
lean_dec(x_120);
if (lean_obj_tag(x_129) == 0)
{
lean_dec_ref(x_129);
x_92 = lean_box(0);
goto block_95;
}
else
{
return x_129;
}
}
}
else
{
size_t x_130; size_t x_131; lean_object* x_132; 
x_130 = 0;
x_131 = lean_usize_of_nat(x_121);
x_132 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_120, x_130, x_131, x_125, x_4);
lean_dec(x_120);
if (lean_obj_tag(x_132) == 0)
{
lean_dec_ref(x_132);
x_92 = lean_box(0);
goto block_95;
}
else
{
return x_132;
}
}
}
}
}
}
else
{
lean_object* x_144; lean_object* x_145; uint8_t x_146; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_144 = lean_ctor_get(x_103, 1);
lean_inc(x_144);
lean_dec_ref(x_103);
x_145 = lean_array_get_size(x_144);
x_146 = lean_nat_dec_lt(x_101, x_145);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; 
lean_dec(x_144);
lean_dec_ref(x_4);
x_147 = lean_box(0);
x_148 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_148, 0, x_147);
return x_148;
}
else
{
lean_object* x_149; uint8_t x_150; 
x_149 = lean_box(0);
x_150 = lean_nat_dec_le(x_145, x_145);
if (x_150 == 0)
{
if (x_146 == 0)
{
lean_dec(x_144);
lean_dec_ref(x_4);
x_96 = lean_box(0);
goto block_99;
}
else
{
size_t x_151; size_t x_152; lean_object* x_153; 
x_151 = 0;
x_152 = lean_usize_of_nat(x_145);
x_153 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_144, x_151, x_152, x_149, x_4);
lean_dec(x_144);
if (lean_obj_tag(x_153) == 0)
{
lean_dec_ref(x_153);
x_96 = lean_box(0);
goto block_99;
}
else
{
return x_153;
}
}
}
else
{
size_t x_154; size_t x_155; lean_object* x_156; 
x_154 = 0;
x_155 = lean_usize_of_nat(x_145);
x_156 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_144, x_154, x_155, x_149, x_4);
lean_dec(x_144);
if (lean_obj_tag(x_156) == 0)
{
lean_dec_ref(x_156);
x_96 = lean_box(0);
goto block_99;
}
else
{
return x_156;
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
x_10 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0;
x_11 = lean_string_append(x_1, x_10);
x_12 = lean_string_append(x_11, x_2);
lean_dec_ref(x_2);
x_13 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1;
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
x_24 = lean_array_get_size(x_20);
x_25 = lean_nat_dec_lt(x_21, x_24);
if (x_25 == 0)
{
lean_dec_ref(x_20);
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
lean_dec_ref(x_20);
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
x_30 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_20, x_28, x_29, x_26, x_4);
lean_dec_ref(x_20);
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
x_33 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_20, x_31, x_32, x_26, x_4);
lean_dec_ref(x_20);
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
block_91:
{
uint8_t x_42; 
x_42 = lean_string_dec_eq(x_40, x_39);
lean_dec_ref(x_40);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_43 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
x_44 = lean_string_append(x_1, x_43);
x_45 = lean_string_append(x_44, x_39);
x_46 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3;
x_47 = lean_string_append(x_45, x_46);
x_48 = 1;
x_49 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set_uint8(x_49, sizeof(void*)*1, x_48);
lean_inc_ref(x_4);
x_50 = lean_apply_2(x_4, x_49, lean_box(0));
x_51 = lean_unsigned_to_nat(0u);
x_52 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
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
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_64, 0);
lean_dec(x_66);
lean_ctor_set(x_64, 0, x_54);
return x_64;
}
else
{
lean_object* x_67; 
lean_dec(x_64);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_54);
return x_67;
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
size_t x_68; size_t x_69; lean_object* x_70; 
x_68 = 0;
x_69 = lean_usize_of_nat(x_56);
x_70 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_55, x_68, x_69, x_59, x_4);
lean_dec(x_55);
if (lean_obj_tag(x_70) == 0)
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_70, 0);
lean_dec(x_72);
lean_ctor_set(x_70, 0, x_54);
return x_70;
}
else
{
lean_object* x_73; 
lean_dec(x_70);
x_73 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_73, 0, x_54);
return x_73;
}
}
else
{
lean_dec(x_54);
return x_70;
}
}
}
}
else
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_74 = lean_ctor_get(x_53, 1);
lean_inc(x_74);
lean_dec_ref(x_53);
x_75 = lean_array_get_size(x_74);
x_76 = lean_nat_dec_lt(x_51, x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
lean_dec(x_74);
lean_dec_ref(x_4);
x_77 = lean_box(0);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
else
{
lean_object* x_79; uint8_t x_80; 
x_79 = lean_box(0);
x_80 = lean_nat_dec_le(x_75, x_75);
if (x_80 == 0)
{
if (x_76 == 0)
{
lean_dec(x_74);
lean_dec_ref(x_4);
x_35 = lean_box(0);
goto block_38;
}
else
{
size_t x_81; size_t x_82; lean_object* x_83; 
x_81 = 0;
x_82 = lean_usize_of_nat(x_75);
x_83 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_74, x_81, x_82, x_79, x_4);
lean_dec(x_74);
if (lean_obj_tag(x_83) == 0)
{
lean_dec_ref(x_83);
x_35 = lean_box(0);
goto block_38;
}
else
{
return x_83;
}
}
}
else
{
size_t x_84; size_t x_85; lean_object* x_86; 
x_84 = 0;
x_85 = lean_usize_of_nat(x_75);
x_86 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_74, x_84, x_85, x_79, x_4);
lean_dec(x_74);
if (lean_obj_tag(x_86) == 0)
{
lean_dec_ref(x_86);
x_35 = lean_box(0);
goto block_38;
}
else
{
return x_86;
}
}
}
}
}
else
{
uint8_t x_87; lean_object* x_88; lean_object* x_89; 
lean_dec_ref(x_39);
lean_inc_ref(x_2);
x_87 = l_Lake_GitRepo_hasNoDiff(x_2);
x_88 = lean_unsigned_to_nat(0u);
x_89 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
if (x_87 == 0)
{
x_20 = x_89;
x_21 = x_88;
x_22 = x_42;
x_23 = lean_box(0);
goto block_34;
}
else
{
uint8_t x_90; 
x_90 = 0;
x_20 = x_89;
x_21 = x_88;
x_22 = x_90;
x_23 = lean_box(0);
goto block_34;
}
}
}
block_95:
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_box(0);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_93);
return x_94;
}
block_99:
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_box(0);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_97);
return x_98;
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
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": cloning ", 10, 10);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_11; lean_object* x_12; lean_object* x_58; lean_object* x_62; lean_object* x_126; lean_object* x_128; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_132 = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___closed__0;
lean_inc_ref(x_1);
x_133 = lean_string_append(x_1, x_132);
x_134 = lean_string_append(x_133, x_3);
x_135 = 1;
x_136 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set_uint8(x_136, sizeof(void*)*1, x_135);
lean_inc_ref(x_5);
x_137 = lean_apply_2(x_5, x_136, lean_box(0));
x_138 = lean_unsigned_to_nat(0u);
x_139 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
lean_inc_ref(x_2);
x_140 = l_Lake_GitRepo_clone(x_3, x_2, x_139);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_141 = lean_ctor_get(x_140, 1);
lean_inc(x_141);
lean_dec_ref(x_140);
x_142 = lean_array_get_size(x_141);
x_143 = lean_nat_dec_lt(x_138, x_142);
if (x_143 == 0)
{
lean_dec(x_141);
x_62 = lean_box(0);
goto block_125;
}
else
{
lean_object* x_144; uint8_t x_145; 
x_144 = lean_box(0);
x_145 = lean_nat_dec_le(x_142, x_142);
if (x_145 == 0)
{
if (x_143 == 0)
{
lean_dec(x_141);
x_62 = lean_box(0);
goto block_125;
}
else
{
size_t x_146; size_t x_147; lean_object* x_148; 
x_146 = 0;
x_147 = lean_usize_of_nat(x_142);
lean_inc_ref(x_5);
x_148 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_141, x_146, x_147, x_144, x_5);
lean_dec(x_141);
if (lean_obj_tag(x_148) == 0)
{
lean_dec_ref(x_148);
x_62 = lean_box(0);
goto block_125;
}
else
{
x_126 = x_148;
goto block_127;
}
}
}
else
{
size_t x_149; size_t x_150; lean_object* x_151; 
x_149 = 0;
x_150 = lean_usize_of_nat(x_142);
lean_inc_ref(x_5);
x_151 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_141, x_149, x_150, x_144, x_5);
lean_dec(x_141);
if (lean_obj_tag(x_151) == 0)
{
lean_dec_ref(x_151);
x_62 = lean_box(0);
goto block_125;
}
else
{
x_126 = x_151;
goto block_127;
}
}
}
}
else
{
lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_152 = lean_ctor_get(x_140, 1);
lean_inc(x_152);
lean_dec_ref(x_140);
x_153 = lean_array_get_size(x_152);
x_154 = lean_nat_dec_lt(x_138, x_153);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; 
lean_dec(x_152);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_155 = lean_box(0);
x_156 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_156, 0, x_155);
return x_156;
}
else
{
lean_object* x_157; uint8_t x_158; 
x_157 = lean_box(0);
x_158 = lean_nat_dec_le(x_153, x_153);
if (x_158 == 0)
{
if (x_154 == 0)
{
lean_dec(x_152);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_128 = lean_box(0);
goto block_131;
}
else
{
size_t x_159; size_t x_160; lean_object* x_161; 
x_159 = 0;
x_160 = lean_usize_of_nat(x_153);
lean_inc_ref(x_5);
x_161 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_152, x_159, x_160, x_157, x_5);
lean_dec(x_152);
if (lean_obj_tag(x_161) == 0)
{
lean_dec_ref(x_161);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_128 = lean_box(0);
goto block_131;
}
else
{
x_126 = x_161;
goto block_127;
}
}
}
else
{
size_t x_162; size_t x_163; lean_object* x_164; 
x_162 = 0;
x_163 = lean_usize_of_nat(x_153);
lean_inc_ref(x_5);
x_164 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_152, x_162, x_163, x_157, x_5);
lean_dec(x_152);
if (lean_obj_tag(x_164) == 0)
{
lean_dec_ref(x_164);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_128 = lean_box(0);
goto block_131;
}
else
{
x_126 = x_164;
goto block_127;
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
block_57:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_13 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
x_14 = lean_string_append(x_1, x_13);
x_15 = lean_string_append(x_14, x_11);
x_16 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3;
x_17 = lean_string_append(x_15, x_16);
x_18 = 1;
x_19 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_18);
lean_inc_ref(x_5);
x_20 = lean_apply_2(x_5, x_19, lean_box(0));
x_21 = lean_unsigned_to_nat(0u);
x_22 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
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
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
lean_ctor_set(x_34, 0, x_24);
return x_34;
}
else
{
lean_object* x_37; 
lean_dec(x_34);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_24);
return x_37;
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
size_t x_38; size_t x_39; lean_object* x_40; 
x_38 = 0;
x_39 = lean_usize_of_nat(x_26);
x_40 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_25, x_38, x_39, x_29, x_5);
lean_dec(x_25);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
lean_ctor_set(x_40, 0, x_24);
return x_40;
}
else
{
lean_object* x_43; 
lean_dec(x_40);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_24);
return x_43;
}
}
else
{
lean_dec(x_24);
return x_40;
}
}
}
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_23, 1);
lean_inc(x_44);
lean_dec_ref(x_23);
x_45 = lean_array_get_size(x_44);
x_46 = lean_nat_dec_lt(x_21, x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_44);
lean_dec_ref(x_5);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
else
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_box(0);
x_50 = lean_nat_dec_le(x_45, x_45);
if (x_50 == 0)
{
if (x_46 == 0)
{
lean_dec(x_44);
lean_dec_ref(x_5);
x_7 = lean_box(0);
goto block_10;
}
else
{
size_t x_51; size_t x_52; lean_object* x_53; 
x_51 = 0;
x_52 = lean_usize_of_nat(x_45);
x_53 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_44, x_51, x_52, x_49, x_5);
lean_dec(x_44);
if (lean_obj_tag(x_53) == 0)
{
lean_dec_ref(x_53);
x_7 = lean_box(0);
goto block_10;
}
else
{
return x_53;
}
}
}
else
{
size_t x_54; size_t x_55; lean_object* x_56; 
x_54 = 0;
x_55 = lean_usize_of_nat(x_45);
x_56 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_44, x_54, x_55, x_49, x_5);
lean_dec(x_44);
if (lean_obj_tag(x_56) == 0)
{
lean_dec_ref(x_56);
x_7 = lean_box(0);
goto block_10;
}
else
{
return x_56;
}
}
}
}
}
block_61:
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
return x_60;
}
block_125:
{
if (lean_obj_tag(x_4) == 1)
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_4);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_4, 0);
x_65 = l_Lake_Git_defaultRemote;
x_66 = lean_unsigned_to_nat(0u);
x_67 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
lean_inc_ref(x_2);
x_68 = l_Lake_GitRepo_resolveRemoteRevision(x_64, x_65, x_2, x_67);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
lean_free_object(x_4);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec_ref(x_68);
x_71 = lean_array_get_size(x_70);
x_72 = lean_nat_dec_lt(x_66, x_71);
if (x_72 == 0)
{
lean_dec(x_70);
x_11 = x_69;
x_12 = lean_box(0);
goto block_57;
}
else
{
lean_object* x_73; uint8_t x_74; 
x_73 = lean_box(0);
x_74 = lean_nat_dec_le(x_71, x_71);
if (x_74 == 0)
{
if (x_72 == 0)
{
lean_dec(x_70);
x_11 = x_69;
x_12 = lean_box(0);
goto block_57;
}
else
{
size_t x_75; size_t x_76; lean_object* x_77; 
x_75 = 0;
x_76 = lean_usize_of_nat(x_71);
lean_inc_ref(x_5);
x_77 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_70, x_75, x_76, x_73, x_5);
lean_dec(x_70);
if (lean_obj_tag(x_77) == 0)
{
lean_dec_ref(x_77);
x_11 = x_69;
x_12 = lean_box(0);
goto block_57;
}
else
{
lean_dec(x_69);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_77;
}
}
}
else
{
size_t x_78; size_t x_79; lean_object* x_80; 
x_78 = 0;
x_79 = lean_usize_of_nat(x_71);
lean_inc_ref(x_5);
x_80 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_70, x_78, x_79, x_73, x_5);
lean_dec(x_70);
if (lean_obj_tag(x_80) == 0)
{
lean_dec_ref(x_80);
x_11 = x_69;
x_12 = lean_box(0);
goto block_57;
}
else
{
lean_dec(x_69);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_80;
}
}
}
}
else
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_81 = lean_ctor_get(x_68, 1);
lean_inc(x_81);
lean_dec_ref(x_68);
x_82 = lean_array_get_size(x_81);
x_83 = lean_nat_dec_lt(x_66, x_82);
if (x_83 == 0)
{
lean_object* x_84; 
lean_dec(x_81);
lean_dec_ref(x_5);
x_84 = lean_box(0);
lean_ctor_set(x_4, 0, x_84);
return x_4;
}
else
{
lean_object* x_85; uint8_t x_86; 
lean_free_object(x_4);
x_85 = lean_box(0);
x_86 = lean_nat_dec_le(x_82, x_82);
if (x_86 == 0)
{
if (x_83 == 0)
{
lean_dec(x_81);
lean_dec_ref(x_5);
x_58 = lean_box(0);
goto block_61;
}
else
{
size_t x_87; size_t x_88; lean_object* x_89; 
x_87 = 0;
x_88 = lean_usize_of_nat(x_82);
x_89 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_81, x_87, x_88, x_85, x_5);
lean_dec(x_81);
if (lean_obj_tag(x_89) == 0)
{
lean_dec_ref(x_89);
x_58 = lean_box(0);
goto block_61;
}
else
{
return x_89;
}
}
}
else
{
size_t x_90; size_t x_91; lean_object* x_92; 
x_90 = 0;
x_91 = lean_usize_of_nat(x_82);
x_92 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_81, x_90, x_91, x_85, x_5);
lean_dec(x_81);
if (lean_obj_tag(x_92) == 0)
{
lean_dec_ref(x_92);
x_58 = lean_box(0);
goto block_61;
}
else
{
return x_92;
}
}
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_93 = lean_ctor_get(x_4, 0);
lean_inc(x_93);
lean_dec(x_4);
x_94 = l_Lake_Git_defaultRemote;
x_95 = lean_unsigned_to_nat(0u);
x_96 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
lean_inc_ref(x_2);
x_97 = l_Lake_GitRepo_resolveRemoteRevision(x_93, x_94, x_2, x_96);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec_ref(x_97);
x_100 = lean_array_get_size(x_99);
x_101 = lean_nat_dec_lt(x_95, x_100);
if (x_101 == 0)
{
lean_dec(x_99);
x_11 = x_98;
x_12 = lean_box(0);
goto block_57;
}
else
{
lean_object* x_102; uint8_t x_103; 
x_102 = lean_box(0);
x_103 = lean_nat_dec_le(x_100, x_100);
if (x_103 == 0)
{
if (x_101 == 0)
{
lean_dec(x_99);
x_11 = x_98;
x_12 = lean_box(0);
goto block_57;
}
else
{
size_t x_104; size_t x_105; lean_object* x_106; 
x_104 = 0;
x_105 = lean_usize_of_nat(x_100);
lean_inc_ref(x_5);
x_106 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_99, x_104, x_105, x_102, x_5);
lean_dec(x_99);
if (lean_obj_tag(x_106) == 0)
{
lean_dec_ref(x_106);
x_11 = x_98;
x_12 = lean_box(0);
goto block_57;
}
else
{
lean_dec(x_98);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_106;
}
}
}
else
{
size_t x_107; size_t x_108; lean_object* x_109; 
x_107 = 0;
x_108 = lean_usize_of_nat(x_100);
lean_inc_ref(x_5);
x_109 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_99, x_107, x_108, x_102, x_5);
lean_dec(x_99);
if (lean_obj_tag(x_109) == 0)
{
lean_dec_ref(x_109);
x_11 = x_98;
x_12 = lean_box(0);
goto block_57;
}
else
{
lean_dec(x_98);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_109;
}
}
}
}
else
{
lean_object* x_110; lean_object* x_111; uint8_t x_112; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_110 = lean_ctor_get(x_97, 1);
lean_inc(x_110);
lean_dec_ref(x_97);
x_111 = lean_array_get_size(x_110);
x_112 = lean_nat_dec_lt(x_95, x_111);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; 
lean_dec(x_110);
lean_dec_ref(x_5);
x_113 = lean_box(0);
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_113);
return x_114;
}
else
{
lean_object* x_115; uint8_t x_116; 
x_115 = lean_box(0);
x_116 = lean_nat_dec_le(x_111, x_111);
if (x_116 == 0)
{
if (x_112 == 0)
{
lean_dec(x_110);
lean_dec_ref(x_5);
x_58 = lean_box(0);
goto block_61;
}
else
{
size_t x_117; size_t x_118; lean_object* x_119; 
x_117 = 0;
x_118 = lean_usize_of_nat(x_111);
x_119 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_110, x_117, x_118, x_115, x_5);
lean_dec(x_110);
if (lean_obj_tag(x_119) == 0)
{
lean_dec_ref(x_119);
x_58 = lean_box(0);
goto block_61;
}
else
{
return x_119;
}
}
}
else
{
size_t x_120; size_t x_121; lean_object* x_122; 
x_120 = 0;
x_121 = lean_usize_of_nat(x_111);
x_122 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_110, x_120, x_121, x_115, x_5);
lean_dec(x_110);
if (lean_obj_tag(x_122) == 0)
{
lean_dec_ref(x_122);
x_58 = lean_box(0);
goto block_61;
}
else
{
return x_122;
}
}
}
}
}
}
else
{
lean_object* x_123; lean_object* x_124; 
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_123 = lean_box(0);
x_124 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_124, 0, x_123);
return x_124;
}
}
block_127:
{
if (lean_obj_tag(x_126) == 0)
{
lean_dec_ref(x_126);
x_62 = lean_box(0);
goto block_125;
}
else
{
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_126;
}
}
block_131:
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_box(0);
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_129);
return x_130;
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
lean_object* x_7; lean_object* x_11; lean_object* x_12; lean_object* x_58; lean_object* x_62; lean_object* x_126; lean_object* x_128; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_132 = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___closed__0;
lean_inc_ref(x_2);
x_133 = lean_string_append(x_2, x_132);
x_134 = lean_string_append(x_133, x_4);
x_135 = 1;
x_136 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set_uint8(x_136, sizeof(void*)*1, x_135);
lean_inc_ref(x_1);
x_137 = lean_apply_2(x_1, x_136, lean_box(0));
x_138 = lean_unsigned_to_nat(0u);
x_139 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
lean_inc_ref(x_3);
x_140 = l_Lake_GitRepo_clone(x_4, x_3, x_139);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_141 = lean_ctor_get(x_140, 1);
lean_inc(x_141);
lean_dec_ref(x_140);
x_142 = lean_array_get_size(x_141);
x_143 = lean_nat_dec_lt(x_138, x_142);
if (x_143 == 0)
{
lean_dec(x_141);
x_62 = lean_box(0);
goto block_125;
}
else
{
lean_object* x_144; uint8_t x_145; 
x_144 = lean_box(0);
x_145 = lean_nat_dec_le(x_142, x_142);
if (x_145 == 0)
{
if (x_143 == 0)
{
lean_dec(x_141);
x_62 = lean_box(0);
goto block_125;
}
else
{
size_t x_146; size_t x_147; lean_object* x_148; 
x_146 = 0;
x_147 = lean_usize_of_nat(x_142);
lean_inc_ref(x_1);
x_148 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_141, x_146, x_147, x_144, x_1);
lean_dec(x_141);
if (lean_obj_tag(x_148) == 0)
{
lean_dec_ref(x_148);
x_62 = lean_box(0);
goto block_125;
}
else
{
x_126 = x_148;
goto block_127;
}
}
}
else
{
size_t x_149; size_t x_150; lean_object* x_151; 
x_149 = 0;
x_150 = lean_usize_of_nat(x_142);
lean_inc_ref(x_1);
x_151 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_141, x_149, x_150, x_144, x_1);
lean_dec(x_141);
if (lean_obj_tag(x_151) == 0)
{
lean_dec_ref(x_151);
x_62 = lean_box(0);
goto block_125;
}
else
{
x_126 = x_151;
goto block_127;
}
}
}
}
else
{
lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_152 = lean_ctor_get(x_140, 1);
lean_inc(x_152);
lean_dec_ref(x_140);
x_153 = lean_array_get_size(x_152);
x_154 = lean_nat_dec_lt(x_138, x_153);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; 
lean_dec(x_152);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_155 = lean_box(0);
x_156 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_156, 0, x_155);
return x_156;
}
else
{
lean_object* x_157; uint8_t x_158; 
x_157 = lean_box(0);
x_158 = lean_nat_dec_le(x_153, x_153);
if (x_158 == 0)
{
if (x_154 == 0)
{
lean_dec(x_152);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_128 = lean_box(0);
goto block_131;
}
else
{
size_t x_159; size_t x_160; lean_object* x_161; 
x_159 = 0;
x_160 = lean_usize_of_nat(x_153);
lean_inc_ref(x_1);
x_161 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_152, x_159, x_160, x_157, x_1);
lean_dec(x_152);
if (lean_obj_tag(x_161) == 0)
{
lean_dec_ref(x_161);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_128 = lean_box(0);
goto block_131;
}
else
{
x_126 = x_161;
goto block_127;
}
}
}
else
{
size_t x_162; size_t x_163; lean_object* x_164; 
x_162 = 0;
x_163 = lean_usize_of_nat(x_153);
lean_inc_ref(x_1);
x_164 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_152, x_162, x_163, x_157, x_1);
lean_dec(x_152);
if (lean_obj_tag(x_164) == 0)
{
lean_dec_ref(x_164);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_128 = lean_box(0);
goto block_131;
}
else
{
x_126 = x_164;
goto block_127;
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
block_57:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_13 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
x_14 = lean_string_append(x_2, x_13);
x_15 = lean_string_append(x_14, x_11);
x_16 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3;
x_17 = lean_string_append(x_15, x_16);
x_18 = 1;
x_19 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_18);
lean_inc_ref(x_1);
x_20 = lean_apply_2(x_1, x_19, lean_box(0));
x_21 = lean_unsigned_to_nat(0u);
x_22 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
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
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
lean_ctor_set(x_34, 0, x_24);
return x_34;
}
else
{
lean_object* x_37; 
lean_dec(x_34);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_24);
return x_37;
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
size_t x_38; size_t x_39; lean_object* x_40; 
x_38 = 0;
x_39 = lean_usize_of_nat(x_26);
x_40 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_25, x_38, x_39, x_29, x_1);
lean_dec(x_25);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
lean_ctor_set(x_40, 0, x_24);
return x_40;
}
else
{
lean_object* x_43; 
lean_dec(x_40);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_24);
return x_43;
}
}
else
{
lean_dec(x_24);
return x_40;
}
}
}
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_23, 1);
lean_inc(x_44);
lean_dec_ref(x_23);
x_45 = lean_array_get_size(x_44);
x_46 = lean_nat_dec_lt(x_21, x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_44);
lean_dec_ref(x_1);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
else
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_box(0);
x_50 = lean_nat_dec_le(x_45, x_45);
if (x_50 == 0)
{
if (x_46 == 0)
{
lean_dec(x_44);
lean_dec_ref(x_1);
x_7 = lean_box(0);
goto block_10;
}
else
{
size_t x_51; size_t x_52; lean_object* x_53; 
x_51 = 0;
x_52 = lean_usize_of_nat(x_45);
x_53 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_44, x_51, x_52, x_49, x_1);
lean_dec(x_44);
if (lean_obj_tag(x_53) == 0)
{
lean_dec_ref(x_53);
x_7 = lean_box(0);
goto block_10;
}
else
{
return x_53;
}
}
}
else
{
size_t x_54; size_t x_55; lean_object* x_56; 
x_54 = 0;
x_55 = lean_usize_of_nat(x_45);
x_56 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_44, x_54, x_55, x_49, x_1);
lean_dec(x_44);
if (lean_obj_tag(x_56) == 0)
{
lean_dec_ref(x_56);
x_7 = lean_box(0);
goto block_10;
}
else
{
return x_56;
}
}
}
}
}
block_61:
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
return x_60;
}
block_125:
{
if (lean_obj_tag(x_5) == 1)
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_5);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_5, 0);
x_65 = l_Lake_Git_defaultRemote;
x_66 = lean_unsigned_to_nat(0u);
x_67 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
lean_inc_ref(x_3);
x_68 = l_Lake_GitRepo_resolveRemoteRevision(x_64, x_65, x_3, x_67);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
lean_free_object(x_5);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec_ref(x_68);
x_71 = lean_array_get_size(x_70);
x_72 = lean_nat_dec_lt(x_66, x_71);
if (x_72 == 0)
{
lean_dec(x_70);
x_11 = x_69;
x_12 = lean_box(0);
goto block_57;
}
else
{
lean_object* x_73; uint8_t x_74; 
x_73 = lean_box(0);
x_74 = lean_nat_dec_le(x_71, x_71);
if (x_74 == 0)
{
if (x_72 == 0)
{
lean_dec(x_70);
x_11 = x_69;
x_12 = lean_box(0);
goto block_57;
}
else
{
size_t x_75; size_t x_76; lean_object* x_77; 
x_75 = 0;
x_76 = lean_usize_of_nat(x_71);
lean_inc_ref(x_1);
x_77 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_70, x_75, x_76, x_73, x_1);
lean_dec(x_70);
if (lean_obj_tag(x_77) == 0)
{
lean_dec_ref(x_77);
x_11 = x_69;
x_12 = lean_box(0);
goto block_57;
}
else
{
lean_dec(x_69);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_77;
}
}
}
else
{
size_t x_78; size_t x_79; lean_object* x_80; 
x_78 = 0;
x_79 = lean_usize_of_nat(x_71);
lean_inc_ref(x_1);
x_80 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_70, x_78, x_79, x_73, x_1);
lean_dec(x_70);
if (lean_obj_tag(x_80) == 0)
{
lean_dec_ref(x_80);
x_11 = x_69;
x_12 = lean_box(0);
goto block_57;
}
else
{
lean_dec(x_69);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_80;
}
}
}
}
else
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_81 = lean_ctor_get(x_68, 1);
lean_inc(x_81);
lean_dec_ref(x_68);
x_82 = lean_array_get_size(x_81);
x_83 = lean_nat_dec_lt(x_66, x_82);
if (x_83 == 0)
{
lean_object* x_84; 
lean_dec(x_81);
lean_dec_ref(x_1);
x_84 = lean_box(0);
lean_ctor_set(x_5, 0, x_84);
return x_5;
}
else
{
lean_object* x_85; uint8_t x_86; 
lean_free_object(x_5);
x_85 = lean_box(0);
x_86 = lean_nat_dec_le(x_82, x_82);
if (x_86 == 0)
{
if (x_83 == 0)
{
lean_dec(x_81);
lean_dec_ref(x_1);
x_58 = lean_box(0);
goto block_61;
}
else
{
size_t x_87; size_t x_88; lean_object* x_89; 
x_87 = 0;
x_88 = lean_usize_of_nat(x_82);
x_89 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_81, x_87, x_88, x_85, x_1);
lean_dec(x_81);
if (lean_obj_tag(x_89) == 0)
{
lean_dec_ref(x_89);
x_58 = lean_box(0);
goto block_61;
}
else
{
return x_89;
}
}
}
else
{
size_t x_90; size_t x_91; lean_object* x_92; 
x_90 = 0;
x_91 = lean_usize_of_nat(x_82);
x_92 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_81, x_90, x_91, x_85, x_1);
lean_dec(x_81);
if (lean_obj_tag(x_92) == 0)
{
lean_dec_ref(x_92);
x_58 = lean_box(0);
goto block_61;
}
else
{
return x_92;
}
}
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_93 = lean_ctor_get(x_5, 0);
lean_inc(x_93);
lean_dec(x_5);
x_94 = l_Lake_Git_defaultRemote;
x_95 = lean_unsigned_to_nat(0u);
x_96 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
lean_inc_ref(x_3);
x_97 = l_Lake_GitRepo_resolveRemoteRevision(x_93, x_94, x_3, x_96);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec_ref(x_97);
x_100 = lean_array_get_size(x_99);
x_101 = lean_nat_dec_lt(x_95, x_100);
if (x_101 == 0)
{
lean_dec(x_99);
x_11 = x_98;
x_12 = lean_box(0);
goto block_57;
}
else
{
lean_object* x_102; uint8_t x_103; 
x_102 = lean_box(0);
x_103 = lean_nat_dec_le(x_100, x_100);
if (x_103 == 0)
{
if (x_101 == 0)
{
lean_dec(x_99);
x_11 = x_98;
x_12 = lean_box(0);
goto block_57;
}
else
{
size_t x_104; size_t x_105; lean_object* x_106; 
x_104 = 0;
x_105 = lean_usize_of_nat(x_100);
lean_inc_ref(x_1);
x_106 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_99, x_104, x_105, x_102, x_1);
lean_dec(x_99);
if (lean_obj_tag(x_106) == 0)
{
lean_dec_ref(x_106);
x_11 = x_98;
x_12 = lean_box(0);
goto block_57;
}
else
{
lean_dec(x_98);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_106;
}
}
}
else
{
size_t x_107; size_t x_108; lean_object* x_109; 
x_107 = 0;
x_108 = lean_usize_of_nat(x_100);
lean_inc_ref(x_1);
x_109 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_99, x_107, x_108, x_102, x_1);
lean_dec(x_99);
if (lean_obj_tag(x_109) == 0)
{
lean_dec_ref(x_109);
x_11 = x_98;
x_12 = lean_box(0);
goto block_57;
}
else
{
lean_dec(x_98);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_109;
}
}
}
}
else
{
lean_object* x_110; lean_object* x_111; uint8_t x_112; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_110 = lean_ctor_get(x_97, 1);
lean_inc(x_110);
lean_dec_ref(x_97);
x_111 = lean_array_get_size(x_110);
x_112 = lean_nat_dec_lt(x_95, x_111);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; 
lean_dec(x_110);
lean_dec_ref(x_1);
x_113 = lean_box(0);
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_113);
return x_114;
}
else
{
lean_object* x_115; uint8_t x_116; 
x_115 = lean_box(0);
x_116 = lean_nat_dec_le(x_111, x_111);
if (x_116 == 0)
{
if (x_112 == 0)
{
lean_dec(x_110);
lean_dec_ref(x_1);
x_58 = lean_box(0);
goto block_61;
}
else
{
size_t x_117; size_t x_118; lean_object* x_119; 
x_117 = 0;
x_118 = lean_usize_of_nat(x_111);
x_119 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_110, x_117, x_118, x_115, x_1);
lean_dec(x_110);
if (lean_obj_tag(x_119) == 0)
{
lean_dec_ref(x_119);
x_58 = lean_box(0);
goto block_61;
}
else
{
return x_119;
}
}
}
else
{
size_t x_120; size_t x_121; lean_object* x_122; 
x_120 = 0;
x_121 = lean_usize_of_nat(x_111);
x_122 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_110, x_120, x_121, x_115, x_1);
lean_dec(x_110);
if (lean_obj_tag(x_122) == 0)
{
lean_dec_ref(x_122);
x_58 = lean_box(0);
goto block_61;
}
else
{
return x_122;
}
}
}
}
}
}
else
{
lean_object* x_123; lean_object* x_124; 
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_123 = lean_box(0);
x_124 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_124, 0, x_123);
return x_124;
}
}
block_127:
{
if (lean_obj_tag(x_126) == 0)
{
lean_dec_ref(x_126);
x_62 = lean_box(0);
goto block_125;
}
else
{
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_126;
}
}
block_131:
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_box(0);
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_129);
return x_130;
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
uint8_t x_6; lean_object* x_7; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_35; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_92; lean_object* x_96; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_100 = l_Lake_Git_defaultRemote;
x_101 = lean_unsigned_to_nat(0u);
x_102 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
lean_inc_ref(x_3);
x_103 = l_Lake_GitRepo_findRemoteRevision(x_3, x_4, x_100, x_102);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_134; uint8_t x_135; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec_ref(x_103);
x_134 = lean_array_get_size(x_105);
x_135 = lean_nat_dec_lt(x_101, x_134);
if (x_135 == 0)
{
lean_dec(x_105);
x_106 = lean_box(0);
goto block_133;
}
else
{
lean_object* x_136; uint8_t x_137; 
x_136 = lean_box(0);
x_137 = lean_nat_dec_le(x_134, x_134);
if (x_137 == 0)
{
if (x_135 == 0)
{
lean_dec(x_105);
x_106 = lean_box(0);
goto block_133;
}
else
{
size_t x_138; size_t x_139; lean_object* x_140; 
x_138 = 0;
x_139 = lean_usize_of_nat(x_134);
lean_inc_ref(x_1);
x_140 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_105, x_138, x_139, x_136, x_1);
lean_dec(x_105);
if (lean_obj_tag(x_140) == 0)
{
lean_dec_ref(x_140);
x_106 = lean_box(0);
goto block_133;
}
else
{
lean_dec(x_104);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_140;
}
}
}
else
{
size_t x_141; size_t x_142; lean_object* x_143; 
x_141 = 0;
x_142 = lean_usize_of_nat(x_134);
lean_inc_ref(x_1);
x_143 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_105, x_141, x_142, x_136, x_1);
lean_dec(x_105);
if (lean_obj_tag(x_143) == 0)
{
lean_dec_ref(x_143);
x_106 = lean_box(0);
goto block_133;
}
else
{
lean_dec(x_104);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_143;
}
}
}
block_133:
{
lean_object* x_107; 
lean_inc_ref(x_3);
x_107 = l_Lake_GitRepo_getHeadRevision(x_3, x_102);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec_ref(x_107);
x_110 = lean_array_get_size(x_109);
x_111 = lean_nat_dec_lt(x_101, x_110);
if (x_111 == 0)
{
lean_dec(x_109);
x_39 = x_104;
x_40 = x_108;
x_41 = lean_box(0);
goto block_91;
}
else
{
lean_object* x_112; uint8_t x_113; 
x_112 = lean_box(0);
x_113 = lean_nat_dec_le(x_110, x_110);
if (x_113 == 0)
{
if (x_111 == 0)
{
lean_dec(x_109);
x_39 = x_104;
x_40 = x_108;
x_41 = lean_box(0);
goto block_91;
}
else
{
size_t x_114; size_t x_115; lean_object* x_116; 
x_114 = 0;
x_115 = lean_usize_of_nat(x_110);
lean_inc_ref(x_1);
x_116 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_109, x_114, x_115, x_112, x_1);
lean_dec(x_109);
if (lean_obj_tag(x_116) == 0)
{
lean_dec_ref(x_116);
x_39 = x_104;
x_40 = x_108;
x_41 = lean_box(0);
goto block_91;
}
else
{
lean_dec(x_108);
lean_dec(x_104);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_116;
}
}
}
else
{
size_t x_117; size_t x_118; lean_object* x_119; 
x_117 = 0;
x_118 = lean_usize_of_nat(x_110);
lean_inc_ref(x_1);
x_119 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_109, x_117, x_118, x_112, x_1);
lean_dec(x_109);
if (lean_obj_tag(x_119) == 0)
{
lean_dec_ref(x_119);
x_39 = x_104;
x_40 = x_108;
x_41 = lean_box(0);
goto block_91;
}
else
{
lean_dec(x_108);
lean_dec(x_104);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_119;
}
}
}
}
else
{
lean_object* x_120; lean_object* x_121; uint8_t x_122; 
lean_dec(x_104);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_120 = lean_ctor_get(x_107, 1);
lean_inc(x_120);
lean_dec_ref(x_107);
x_121 = lean_array_get_size(x_120);
x_122 = lean_nat_dec_lt(x_101, x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; 
lean_dec(x_120);
lean_dec_ref(x_1);
x_123 = lean_box(0);
x_124 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_124, 0, x_123);
return x_124;
}
else
{
lean_object* x_125; uint8_t x_126; 
x_125 = lean_box(0);
x_126 = lean_nat_dec_le(x_121, x_121);
if (x_126 == 0)
{
if (x_122 == 0)
{
lean_dec(x_120);
lean_dec_ref(x_1);
x_92 = lean_box(0);
goto block_95;
}
else
{
size_t x_127; size_t x_128; lean_object* x_129; 
x_127 = 0;
x_128 = lean_usize_of_nat(x_121);
x_129 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_120, x_127, x_128, x_125, x_1);
lean_dec(x_120);
if (lean_obj_tag(x_129) == 0)
{
lean_dec_ref(x_129);
x_92 = lean_box(0);
goto block_95;
}
else
{
return x_129;
}
}
}
else
{
size_t x_130; size_t x_131; lean_object* x_132; 
x_130 = 0;
x_131 = lean_usize_of_nat(x_121);
x_132 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_120, x_130, x_131, x_125, x_1);
lean_dec(x_120);
if (lean_obj_tag(x_132) == 0)
{
lean_dec_ref(x_132);
x_92 = lean_box(0);
goto block_95;
}
else
{
return x_132;
}
}
}
}
}
}
else
{
lean_object* x_144; lean_object* x_145; uint8_t x_146; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_144 = lean_ctor_get(x_103, 1);
lean_inc(x_144);
lean_dec_ref(x_103);
x_145 = lean_array_get_size(x_144);
x_146 = lean_nat_dec_lt(x_101, x_145);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; 
lean_dec(x_144);
lean_dec_ref(x_1);
x_147 = lean_box(0);
x_148 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_148, 0, x_147);
return x_148;
}
else
{
lean_object* x_149; uint8_t x_150; 
x_149 = lean_box(0);
x_150 = lean_nat_dec_le(x_145, x_145);
if (x_150 == 0)
{
if (x_146 == 0)
{
lean_dec(x_144);
lean_dec_ref(x_1);
x_96 = lean_box(0);
goto block_99;
}
else
{
size_t x_151; size_t x_152; lean_object* x_153; 
x_151 = 0;
x_152 = lean_usize_of_nat(x_145);
x_153 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_144, x_151, x_152, x_149, x_1);
lean_dec(x_144);
if (lean_obj_tag(x_153) == 0)
{
lean_dec_ref(x_153);
x_96 = lean_box(0);
goto block_99;
}
else
{
return x_153;
}
}
}
else
{
size_t x_154; size_t x_155; lean_object* x_156; 
x_154 = 0;
x_155 = lean_usize_of_nat(x_145);
x_156 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_144, x_154, x_155, x_149, x_1);
lean_dec(x_144);
if (lean_obj_tag(x_156) == 0)
{
lean_dec_ref(x_156);
x_96 = lean_box(0);
goto block_99;
}
else
{
return x_156;
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
x_10 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0;
x_11 = lean_string_append(x_2, x_10);
x_12 = lean_string_append(x_11, x_3);
lean_dec_ref(x_3);
x_13 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1;
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
block_91:
{
uint8_t x_42; 
x_42 = lean_string_dec_eq(x_40, x_39);
lean_dec_ref(x_40);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_43 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
x_44 = lean_string_append(x_2, x_43);
x_45 = lean_string_append(x_44, x_39);
x_46 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3;
x_47 = lean_string_append(x_45, x_46);
x_48 = 1;
x_49 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set_uint8(x_49, sizeof(void*)*1, x_48);
lean_inc_ref(x_1);
x_50 = lean_apply_2(x_1, x_49, lean_box(0));
x_51 = lean_unsigned_to_nat(0u);
x_52 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
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
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_64, 0);
lean_dec(x_66);
lean_ctor_set(x_64, 0, x_54);
return x_64;
}
else
{
lean_object* x_67; 
lean_dec(x_64);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_54);
return x_67;
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
size_t x_68; size_t x_69; lean_object* x_70; 
x_68 = 0;
x_69 = lean_usize_of_nat(x_56);
x_70 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_55, x_68, x_69, x_59, x_1);
lean_dec(x_55);
if (lean_obj_tag(x_70) == 0)
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_70, 0);
lean_dec(x_72);
lean_ctor_set(x_70, 0, x_54);
return x_70;
}
else
{
lean_object* x_73; 
lean_dec(x_70);
x_73 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_73, 0, x_54);
return x_73;
}
}
else
{
lean_dec(x_54);
return x_70;
}
}
}
}
else
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_74 = lean_ctor_get(x_53, 1);
lean_inc(x_74);
lean_dec_ref(x_53);
x_75 = lean_array_get_size(x_74);
x_76 = lean_nat_dec_lt(x_51, x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
lean_dec(x_74);
lean_dec_ref(x_1);
x_77 = lean_box(0);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
else
{
lean_object* x_79; uint8_t x_80; 
x_79 = lean_box(0);
x_80 = lean_nat_dec_le(x_75, x_75);
if (x_80 == 0)
{
if (x_76 == 0)
{
lean_dec(x_74);
lean_dec_ref(x_1);
x_35 = lean_box(0);
goto block_38;
}
else
{
size_t x_81; size_t x_82; lean_object* x_83; 
x_81 = 0;
x_82 = lean_usize_of_nat(x_75);
x_83 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_74, x_81, x_82, x_79, x_1);
lean_dec(x_74);
if (lean_obj_tag(x_83) == 0)
{
lean_dec_ref(x_83);
x_35 = lean_box(0);
goto block_38;
}
else
{
return x_83;
}
}
}
else
{
size_t x_84; size_t x_85; lean_object* x_86; 
x_84 = 0;
x_85 = lean_usize_of_nat(x_75);
x_86 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_74, x_84, x_85, x_79, x_1);
lean_dec(x_74);
if (lean_obj_tag(x_86) == 0)
{
lean_dec_ref(x_86);
x_35 = lean_box(0);
goto block_38;
}
else
{
return x_86;
}
}
}
}
}
else
{
uint8_t x_87; lean_object* x_88; lean_object* x_89; 
lean_dec_ref(x_39);
lean_inc_ref(x_3);
x_87 = l_Lake_GitRepo_hasNoDiff(x_3);
x_88 = lean_unsigned_to_nat(0u);
x_89 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
if (x_87 == 0)
{
x_20 = x_88;
x_21 = x_89;
x_22 = x_42;
x_23 = lean_box(0);
goto block_34;
}
else
{
uint8_t x_90; 
x_90 = 0;
x_20 = x_88;
x_21 = x_89;
x_22 = x_90;
x_23 = lean_box(0);
goto block_34;
}
}
}
block_95:
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_box(0);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_93);
return x_94;
}
block_99:
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_box(0);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_97);
return x_98;
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
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": URL has changed; deleting '", 29, 29);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' and cloning again", 19, 19);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": URL has changed; you might need to delete '", 45, 45);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' manually", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
x_2 = lean_array_get_size(x_1);
return x_2;
}
}
static uint8_t _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_lt(x_2, x_1);
return x_3;
}
}
static uint8_t _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4;
x_2 = lean_nat_dec_le(x_1, x_1);
return x_2;
}
}
static size_t _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4;
x_2 = lean_usize_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; lean_object* x_8; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; 
x_45 = l_Lake_Git_defaultRemote;
lean_inc_ref(x_2);
x_46 = l_Lake_GitRepo_getRemoteUrl_x3f(x_45, x_2);
x_47 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
if (lean_obj_tag(x_46) == 1)
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_ctor_get(x_46, 0);
lean_inc(x_60);
lean_dec_ref(x_46);
x_61 = lean_string_dec_eq(x_60, x_3);
if (x_61 == 0)
{
lean_object* x_62; 
x_62 = lean_io_realpath(x_60);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
lean_dec_ref(x_62);
lean_inc_ref(x_3);
x_64 = lean_io_realpath(x_3);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
lean_dec_ref(x_64);
x_66 = lean_string_dec_eq(x_63, x_65);
lean_dec(x_65);
lean_dec(x_63);
x_48 = x_66;
x_49 = lean_box(0);
goto block_59;
}
else
{
lean_dec_ref(x_64);
lean_dec(x_63);
x_48 = x_61;
x_49 = lean_box(0);
goto block_59;
}
}
else
{
lean_dec_ref(x_62);
x_48 = x_61;
x_49 = lean_box(0);
goto block_59;
}
}
else
{
lean_dec(x_60);
x_48 = x_61;
x_49 = lean_box(0);
goto block_59;
}
}
else
{
uint8_t x_67; 
lean_dec(x_46);
x_67 = 0;
x_48 = x_67;
x_49 = lean_box(0);
goto block_59;
}
block_44:
{
if (x_7 == 0)
{
uint8_t x_9; 
x_9 = l_System_Platform_isWindows;
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__0;
lean_inc_ref(x_1);
x_11 = lean_string_append(x_1, x_10);
x_12 = lean_string_append(x_11, x_2);
x_13 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__1;
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
uint8_t x_20; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_18, 0);
x_22 = lean_io_error_to_string(x_21);
x_23 = 3;
x_24 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_23);
x_25 = lean_apply_2(x_5, x_24, lean_box(0));
x_26 = lean_box(0);
lean_ctor_set(x_18, 0, x_26);
return x_18;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
lean_dec(x_18);
x_28 = lean_io_error_to_string(x_27);
x_29 = 3;
x_30 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*1, x_29);
x_31 = lean_apply_2(x_5, x_30, lean_box(0));
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec_ref(x_3);
x_34 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__2;
lean_inc_ref(x_1);
x_35 = lean_string_append(x_1, x_34);
x_36 = lean_string_append(x_35, x_2);
x_37 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__3;
x_38 = lean_string_append(x_36, x_37);
x_39 = 1;
x_40 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*1, x_39);
lean_inc_ref(x_5);
x_41 = lean_apply_2(x_5, x_40, lean_box(0));
x_42 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(x_5, x_1, x_2, x_4);
return x_42;
}
}
else
{
lean_object* x_43; 
lean_dec_ref(x_3);
x_43 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(x_5, x_1, x_2, x_4);
return x_43;
}
}
block_59:
{
uint8_t x_50; 
x_50 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5;
if (x_50 == 0)
{
x_7 = x_48;
x_8 = lean_box(0);
goto block_44;
}
else
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_box(0);
x_52 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6;
if (x_52 == 0)
{
if (x_50 == 0)
{
x_7 = x_48;
x_8 = lean_box(0);
goto block_44;
}
else
{
size_t x_53; size_t x_54; lean_object* x_55; 
x_53 = 0;
x_54 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
lean_inc_ref(x_5);
x_55 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_47, x_53, x_54, x_51, x_5);
if (lean_obj_tag(x_55) == 0)
{
lean_dec_ref(x_55);
x_7 = x_48;
x_8 = lean_box(0);
goto block_44;
}
else
{
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_55;
}
}
}
else
{
size_t x_56; size_t x_57; lean_object* x_58; 
x_56 = 0;
x_57 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
lean_inc_ref(x_5);
x_58 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_47, x_56, x_57, x_51, x_5);
if (lean_obj_tag(x_58) == 0)
{
lean_dec_ref(x_58);
x_7 = x_48;
x_8 = lean_box(0);
goto block_44;
}
else
{
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_58;
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
uint8_t x_7; lean_object* x_8; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; 
x_45 = l_Lake_Git_defaultRemote;
lean_inc_ref(x_3);
x_46 = l_Lake_GitRepo_getRemoteUrl_x3f(x_45, x_3);
x_47 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
if (lean_obj_tag(x_46) == 1)
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_ctor_get(x_46, 0);
lean_inc(x_60);
lean_dec_ref(x_46);
x_61 = lean_string_dec_eq(x_60, x_4);
if (x_61 == 0)
{
lean_object* x_62; 
x_62 = lean_io_realpath(x_60);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
lean_dec_ref(x_62);
lean_inc_ref(x_4);
x_64 = lean_io_realpath(x_4);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
lean_dec_ref(x_64);
x_66 = lean_string_dec_eq(x_63, x_65);
lean_dec(x_65);
lean_dec(x_63);
x_48 = x_66;
x_49 = lean_box(0);
goto block_59;
}
else
{
lean_dec_ref(x_64);
lean_dec(x_63);
x_48 = x_61;
x_49 = lean_box(0);
goto block_59;
}
}
else
{
lean_dec_ref(x_62);
x_48 = x_61;
x_49 = lean_box(0);
goto block_59;
}
}
else
{
lean_dec(x_60);
x_48 = x_61;
x_49 = lean_box(0);
goto block_59;
}
}
else
{
uint8_t x_67; 
lean_dec(x_46);
x_67 = 0;
x_48 = x_67;
x_49 = lean_box(0);
goto block_59;
}
block_44:
{
if (x_7 == 0)
{
uint8_t x_9; 
x_9 = l_System_Platform_isWindows;
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__0;
lean_inc_ref(x_2);
x_11 = lean_string_append(x_2, x_10);
x_12 = lean_string_append(x_11, x_3);
x_13 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__1;
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
uint8_t x_20; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_18, 0);
x_22 = lean_io_error_to_string(x_21);
x_23 = 3;
x_24 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_23);
x_25 = lean_apply_2(x_1, x_24, lean_box(0));
x_26 = lean_box(0);
lean_ctor_set(x_18, 0, x_26);
return x_18;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
lean_dec(x_18);
x_28 = lean_io_error_to_string(x_27);
x_29 = 3;
x_30 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*1, x_29);
x_31 = lean_apply_2(x_1, x_30, lean_box(0));
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec_ref(x_4);
x_34 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__2;
lean_inc_ref(x_2);
x_35 = lean_string_append(x_2, x_34);
x_36 = lean_string_append(x_35, x_3);
x_37 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__3;
x_38 = lean_string_append(x_36, x_37);
x_39 = 1;
x_40 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*1, x_39);
lean_inc_ref(x_1);
x_41 = lean_apply_2(x_1, x_40, lean_box(0));
x_42 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(x_1, x_2, x_3, x_5);
return x_42;
}
}
else
{
lean_object* x_43; 
lean_dec_ref(x_4);
x_43 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(x_1, x_2, x_3, x_5);
return x_43;
}
}
block_59:
{
uint8_t x_50; 
x_50 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5;
if (x_50 == 0)
{
x_7 = x_48;
x_8 = lean_box(0);
goto block_44;
}
else
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_box(0);
x_52 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6;
if (x_52 == 0)
{
if (x_50 == 0)
{
x_7 = x_48;
x_8 = lean_box(0);
goto block_44;
}
else
{
size_t x_53; size_t x_54; lean_object* x_55; 
x_53 = 0;
x_54 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
lean_inc_ref(x_1);
x_55 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_47, x_53, x_54, x_51, x_1);
if (lean_obj_tag(x_55) == 0)
{
lean_dec_ref(x_55);
x_7 = x_48;
x_8 = lean_box(0);
goto block_44;
}
else
{
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_55;
}
}
}
else
{
size_t x_56; size_t x_57; lean_object* x_58; 
x_56 = 0;
x_57 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
lean_inc_ref(x_1);
x_58 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_47, x_56, x_57, x_51, x_1);
if (lean_obj_tag(x_58) == 0)
{
lean_dec_ref(x_58);
x_7 = x_48;
x_8 = lean_box(0);
goto block_44;
}
else
{
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_58;
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
x_12 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
x_13 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5;
if (x_13 == 0)
{
x_8 = lean_box(0);
goto block_11;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_box(0);
x_15 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6;
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
x_17 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
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
x_20 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
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
static lean_object* _init_l_Lake_instInhabitedMaterializedDep_default___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedMaterializedDep_default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_instInhabitedPackageEntry_default;
x_2 = l_Lake_instInhabitedMaterializedDep_default___closed__0;
x_3 = l_System_instInhabitedFilePath_default;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_instInhabitedMaterializedDep_default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instInhabitedMaterializedDep_default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedMaterializedDep() {
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
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("/", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": package not found on Reservoir.\n\n  If the package is on GitHub, you can add a Git source. For example:\n\n    require ...\n      from git \"https://github.com/", 157, 157);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\"", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n\n  or, if using TOML:\n\n    [[require]]\n    git = \"https://github.com/", 70, 70);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n    ...\n", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" @ ", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n    rev = ", 11, 11);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n    version = ", 15, 15);
return x_1;
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
x_27 = l_Lake_instInhabitedMaterializedDep_default___closed__0;
x_4 = x_27;
x_5 = x_27;
goto block_26;
}
case 1:
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_3);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_3, 0);
x_30 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__5;
x_31 = l_String_quote(x_29);
lean_ctor_set_tag(x_3, 3);
lean_ctor_set(x_3, 0, x_31);
x_32 = l_Std_Format_defWidth;
x_33 = lean_unsigned_to_nat(0u);
x_34 = l_Std_Format_pretty(x_3, x_32, x_33, x_33);
x_35 = lean_string_append(x_30, x_34);
x_36 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__6;
x_37 = lean_string_append(x_36, x_34);
lean_dec_ref(x_34);
x_4 = x_35;
x_5 = x_37;
goto block_26;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_38 = lean_ctor_get(x_3, 0);
lean_inc(x_38);
lean_dec(x_3);
x_39 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__5;
x_40 = l_String_quote(x_38);
x_41 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = l_Std_Format_defWidth;
x_43 = lean_unsigned_to_nat(0u);
x_44 = l_Std_Format_pretty(x_41, x_42, x_43, x_43);
x_45 = lean_string_append(x_39, x_44);
x_46 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__6;
x_47 = lean_string_append(x_46, x_44);
lean_dec_ref(x_44);
x_4 = x_45;
x_5 = x_47;
goto block_26;
}
}
default: 
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_3);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_49 = lean_ctor_get(x_3, 0);
x_50 = lean_ctor_get(x_49, 0);
lean_inc_ref(x_50);
lean_dec_ref(x_49);
x_51 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__5;
x_52 = l_String_quote(x_50);
lean_ctor_set_tag(x_3, 3);
lean_ctor_set(x_3, 0, x_52);
x_53 = l_Std_Format_defWidth;
x_54 = lean_unsigned_to_nat(0u);
x_55 = l_Std_Format_pretty(x_3, x_53, x_54, x_54);
x_56 = lean_string_append(x_51, x_55);
x_57 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__7;
x_58 = lean_string_append(x_57, x_55);
lean_dec_ref(x_55);
x_4 = x_56;
x_5 = x_58;
goto block_26;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_59 = lean_ctor_get(x_3, 0);
lean_inc(x_59);
lean_dec(x_3);
x_60 = lean_ctor_get(x_59, 0);
lean_inc_ref(x_60);
lean_dec_ref(x_59);
x_61 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__5;
x_62 = l_String_quote(x_60);
x_63 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_63, 0, x_62);
x_64 = l_Std_Format_defWidth;
x_65 = lean_unsigned_to_nat(0u);
x_66 = l_Std_Format_pretty(x_63, x_64, x_65, x_65);
x_67 = lean_string_append(x_61, x_66);
x_68 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__7;
x_69 = lean_string_append(x_68, x_66);
lean_dec_ref(x_66);
x_4 = x_67;
x_5 = x_69;
goto block_26;
}
}
}
block_26:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_6 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0;
lean_inc_ref(x_1);
x_7 = lean_string_append(x_1, x_6);
x_8 = lean_string_append(x_7, x_2);
x_9 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__1;
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_string_append(x_10, x_1);
x_12 = lean_string_append(x_11, x_6);
x_13 = lean_string_append(x_12, x_2);
x_14 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__2;
x_15 = lean_string_append(x_13, x_14);
x_16 = lean_string_append(x_15, x_4);
lean_dec_ref(x_4);
x_17 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__3;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_string_append(x_18, x_1);
lean_dec_ref(x_1);
x_20 = lean_string_append(x_19, x_6);
x_21 = lean_string_append(x_20, x_2);
x_22 = lean_string_append(x_21, x_14);
x_23 = lean_string_append(x_22, x_5);
lean_dec_ref(x_5);
x_24 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__4;
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
x_12 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
x_13 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5;
if (x_13 == 0)
{
x_8 = lean_box(0);
goto block_11;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_box(0);
x_15 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6;
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
x_17 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
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
x_20 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
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
lean_object* x_13; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_37; lean_object* x_38; lean_object* x_125; 
x_17 = lean_ctor_get(x_3, 5);
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_6);
x_37 = l_Lake_joinRelative(x_4, x_6);
x_125 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_17, x_18);
if (lean_obj_tag(x_125) == 0)
{
x_38 = x_7;
goto block_124;
}
else
{
lean_object* x_126; 
lean_dec_ref(x_7);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
lean_dec_ref(x_125);
x_38 = x_126;
goto block_124;
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
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_22);
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
x_20 = lean_box(0);
x_21 = x_31;
x_22 = x_32;
x_23 = x_35;
goto block_30;
}
else
{
x_20 = lean_box(0);
x_21 = x_31;
x_22 = x_32;
x_23 = x_6;
goto block_30;
}
}
block_124:
{
lean_object* x_39; 
lean_inc(x_9);
lean_inc_ref(x_38);
lean_inc_ref(x_37);
lean_inc_ref(x_11);
x_39 = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(x_11, x_5, x_37, x_38, x_9);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
x_42 = lean_unsigned_to_nat(0u);
x_43 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
x_44 = l_Lake_GitRepo_getHeadRevision(x_37, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
lean_free_object(x_39);
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
uint8_t x_54; 
lean_dec(x_45);
lean_dec_ref(x_38);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
return x_53;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
}
}
else
{
size_t x_57; size_t x_58; lean_object* x_59; 
x_57 = 0;
x_58 = lean_usize_of_nat(x_47);
x_59 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_46, x_57, x_58, x_49, x_11);
lean_dec(x_46);
if (lean_obj_tag(x_59) == 0)
{
lean_dec_ref(x_59);
x_31 = x_38;
x_32 = x_45;
x_33 = lean_box(0);
goto block_36;
}
else
{
uint8_t x_60; 
lean_dec(x_45);
lean_dec_ref(x_38);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
return x_59;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_59, 0);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
return x_62;
}
}
}
}
}
else
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; 
lean_dec_ref(x_38);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
x_63 = lean_ctor_get(x_44, 1);
lean_inc(x_63);
lean_dec_ref(x_44);
x_64 = lean_array_get_size(x_63);
x_65 = lean_nat_dec_lt(x_42, x_64);
if (x_65 == 0)
{
lean_object* x_66; 
lean_dec(x_63);
lean_dec_ref(x_11);
x_66 = lean_box(0);
lean_ctor_set_tag(x_39, 1);
lean_ctor_set(x_39, 0, x_66);
return x_39;
}
else
{
lean_object* x_67; uint8_t x_68; 
lean_free_object(x_39);
x_67 = lean_box(0);
x_68 = lean_nat_dec_le(x_64, x_64);
if (x_68 == 0)
{
if (x_65 == 0)
{
lean_dec(x_63);
lean_dec_ref(x_11);
x_13 = lean_box(0);
goto block_16;
}
else
{
size_t x_69; size_t x_70; lean_object* x_71; 
x_69 = 0;
x_70 = lean_usize_of_nat(x_64);
x_71 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_63, x_69, x_70, x_67, x_11);
lean_dec(x_63);
if (lean_obj_tag(x_71) == 0)
{
lean_dec_ref(x_71);
x_13 = lean_box(0);
goto block_16;
}
else
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
return x_71;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_71, 0);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_73);
return x_74;
}
}
}
}
else
{
size_t x_75; size_t x_76; lean_object* x_77; 
x_75 = 0;
x_76 = lean_usize_of_nat(x_64);
x_77 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_63, x_75, x_76, x_67, x_11);
lean_dec(x_63);
if (lean_obj_tag(x_77) == 0)
{
lean_dec_ref(x_77);
x_13 = lean_box(0);
goto block_16;
}
else
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
return x_77;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_77, 0);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
return x_80;
}
}
}
}
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_39);
x_81 = lean_unsigned_to_nat(0u);
x_82 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
x_83 = l_Lake_GitRepo_getHeadRevision(x_37, x_82);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec_ref(x_83);
x_86 = lean_array_get_size(x_85);
x_87 = lean_nat_dec_lt(x_81, x_86);
if (x_87 == 0)
{
lean_dec(x_85);
lean_dec_ref(x_11);
x_31 = x_38;
x_32 = x_84;
x_33 = lean_box(0);
goto block_36;
}
else
{
lean_object* x_88; uint8_t x_89; 
x_88 = lean_box(0);
x_89 = lean_nat_dec_le(x_86, x_86);
if (x_89 == 0)
{
if (x_87 == 0)
{
lean_dec(x_85);
lean_dec_ref(x_11);
x_31 = x_38;
x_32 = x_84;
x_33 = lean_box(0);
goto block_36;
}
else
{
size_t x_90; size_t x_91; lean_object* x_92; 
x_90 = 0;
x_91 = lean_usize_of_nat(x_86);
x_92 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_85, x_90, x_91, x_88, x_11);
lean_dec(x_85);
if (lean_obj_tag(x_92) == 0)
{
lean_dec_ref(x_92);
x_31 = x_38;
x_32 = x_84;
x_33 = lean_box(0);
goto block_36;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_84);
lean_dec_ref(x_38);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 x_94 = x_92;
} else {
 lean_dec_ref(x_92);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 1, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_93);
return x_95;
}
}
}
else
{
size_t x_96; size_t x_97; lean_object* x_98; 
x_96 = 0;
x_97 = lean_usize_of_nat(x_86);
x_98 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_85, x_96, x_97, x_88, x_11);
lean_dec(x_85);
if (lean_obj_tag(x_98) == 0)
{
lean_dec_ref(x_98);
x_31 = x_38;
x_32 = x_84;
x_33 = lean_box(0);
goto block_36;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_84);
lean_dec_ref(x_38);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 x_100 = x_98;
} else {
 lean_dec_ref(x_98);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(1, 1, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_99);
return x_101;
}
}
}
}
else
{
lean_object* x_102; lean_object* x_103; uint8_t x_104; 
lean_dec_ref(x_38);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
x_102 = lean_ctor_get(x_83, 1);
lean_inc(x_102);
lean_dec_ref(x_83);
x_103 = lean_array_get_size(x_102);
x_104 = lean_nat_dec_lt(x_81, x_103);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; 
lean_dec(x_102);
lean_dec_ref(x_11);
x_105 = lean_box(0);
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_105);
return x_106;
}
else
{
lean_object* x_107; uint8_t x_108; 
x_107 = lean_box(0);
x_108 = lean_nat_dec_le(x_103, x_103);
if (x_108 == 0)
{
if (x_104 == 0)
{
lean_dec(x_102);
lean_dec_ref(x_11);
x_13 = lean_box(0);
goto block_16;
}
else
{
size_t x_109; size_t x_110; lean_object* x_111; 
x_109 = 0;
x_110 = lean_usize_of_nat(x_103);
x_111 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_102, x_109, x_110, x_107, x_11);
lean_dec(x_102);
if (lean_obj_tag(x_111) == 0)
{
lean_dec_ref(x_111);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 x_113 = x_111;
} else {
 lean_dec_ref(x_111);
 x_113 = lean_box(0);
}
if (lean_is_scalar(x_113)) {
 x_114 = lean_alloc_ctor(1, 1, 0);
} else {
 x_114 = x_113;
}
lean_ctor_set(x_114, 0, x_112);
return x_114;
}
}
}
else
{
size_t x_115; size_t x_116; lean_object* x_117; 
x_115 = 0;
x_116 = lean_usize_of_nat(x_103);
x_117 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_102, x_115, x_116, x_107, x_11);
lean_dec(x_102);
if (lean_obj_tag(x_117) == 0)
{
lean_dec_ref(x_117);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 x_119 = x_117;
} else {
 lean_dec_ref(x_117);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(1, 1, 0);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_118);
return x_120;
}
}
}
}
}
}
else
{
uint8_t x_121; 
lean_dec_ref(x_38);
lean_dec_ref(x_37);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
x_121 = !lean_is_exclusive(x_39);
if (x_121 == 0)
{
return x_39;
}
else
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_39, 0);
lean_inc(x_122);
lean_dec(x_39);
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_122);
return x_123;
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
lean_object* x_13; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_37; lean_object* x_38; lean_object* x_125; 
x_17 = lean_ctor_get(x_4, 5);
x_18 = lean_ctor_get(x_2, 0);
x_19 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_7);
x_37 = l_Lake_joinRelative(x_5, x_7);
x_125 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_17, x_18);
if (lean_obj_tag(x_125) == 0)
{
x_38 = x_8;
goto block_124;
}
else
{
lean_object* x_126; 
lean_dec_ref(x_8);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
lean_dec_ref(x_125);
x_38 = x_126;
goto block_124;
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
block_124:
{
lean_object* x_39; 
lean_inc(x_10);
lean_inc_ref(x_38);
lean_inc_ref(x_37);
lean_inc_ref(x_1);
x_39 = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(x_1, x_6, x_37, x_38, x_10);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
x_42 = lean_unsigned_to_nat(0u);
x_43 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
x_44 = l_Lake_GitRepo_getHeadRevision(x_37, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
lean_free_object(x_39);
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
uint8_t x_54; 
lean_dec(x_45);
lean_dec_ref(x_38);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
return x_53;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
}
}
else
{
size_t x_57; size_t x_58; lean_object* x_59; 
x_57 = 0;
x_58 = lean_usize_of_nat(x_47);
x_59 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_46, x_57, x_58, x_49, x_1);
lean_dec(x_46);
if (lean_obj_tag(x_59) == 0)
{
lean_dec_ref(x_59);
x_31 = x_38;
x_32 = x_45;
x_33 = lean_box(0);
goto block_36;
}
else
{
uint8_t x_60; 
lean_dec(x_45);
lean_dec_ref(x_38);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
return x_59;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_59, 0);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
return x_62;
}
}
}
}
}
else
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; 
lean_dec_ref(x_38);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
x_63 = lean_ctor_get(x_44, 1);
lean_inc(x_63);
lean_dec_ref(x_44);
x_64 = lean_array_get_size(x_63);
x_65 = lean_nat_dec_lt(x_42, x_64);
if (x_65 == 0)
{
lean_object* x_66; 
lean_dec(x_63);
lean_dec_ref(x_1);
x_66 = lean_box(0);
lean_ctor_set_tag(x_39, 1);
lean_ctor_set(x_39, 0, x_66);
return x_39;
}
else
{
lean_object* x_67; uint8_t x_68; 
lean_free_object(x_39);
x_67 = lean_box(0);
x_68 = lean_nat_dec_le(x_64, x_64);
if (x_68 == 0)
{
if (x_65 == 0)
{
lean_dec(x_63);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
size_t x_69; size_t x_70; lean_object* x_71; 
x_69 = 0;
x_70 = lean_usize_of_nat(x_64);
x_71 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_63, x_69, x_70, x_67, x_1);
lean_dec(x_63);
if (lean_obj_tag(x_71) == 0)
{
lean_dec_ref(x_71);
x_13 = lean_box(0);
goto block_16;
}
else
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
return x_71;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_71, 0);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_73);
return x_74;
}
}
}
}
else
{
size_t x_75; size_t x_76; lean_object* x_77; 
x_75 = 0;
x_76 = lean_usize_of_nat(x_64);
x_77 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_63, x_75, x_76, x_67, x_1);
lean_dec(x_63);
if (lean_obj_tag(x_77) == 0)
{
lean_dec_ref(x_77);
x_13 = lean_box(0);
goto block_16;
}
else
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
return x_77;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_77, 0);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
return x_80;
}
}
}
}
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_39);
x_81 = lean_unsigned_to_nat(0u);
x_82 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
x_83 = l_Lake_GitRepo_getHeadRevision(x_37, x_82);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec_ref(x_83);
x_86 = lean_array_get_size(x_85);
x_87 = lean_nat_dec_lt(x_81, x_86);
if (x_87 == 0)
{
lean_dec(x_85);
lean_dec_ref(x_1);
x_31 = x_38;
x_32 = x_84;
x_33 = lean_box(0);
goto block_36;
}
else
{
lean_object* x_88; uint8_t x_89; 
x_88 = lean_box(0);
x_89 = lean_nat_dec_le(x_86, x_86);
if (x_89 == 0)
{
if (x_87 == 0)
{
lean_dec(x_85);
lean_dec_ref(x_1);
x_31 = x_38;
x_32 = x_84;
x_33 = lean_box(0);
goto block_36;
}
else
{
size_t x_90; size_t x_91; lean_object* x_92; 
x_90 = 0;
x_91 = lean_usize_of_nat(x_86);
x_92 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_85, x_90, x_91, x_88, x_1);
lean_dec(x_85);
if (lean_obj_tag(x_92) == 0)
{
lean_dec_ref(x_92);
x_31 = x_38;
x_32 = x_84;
x_33 = lean_box(0);
goto block_36;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_84);
lean_dec_ref(x_38);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 x_94 = x_92;
} else {
 lean_dec_ref(x_92);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 1, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_93);
return x_95;
}
}
}
else
{
size_t x_96; size_t x_97; lean_object* x_98; 
x_96 = 0;
x_97 = lean_usize_of_nat(x_86);
x_98 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_85, x_96, x_97, x_88, x_1);
lean_dec(x_85);
if (lean_obj_tag(x_98) == 0)
{
lean_dec_ref(x_98);
x_31 = x_38;
x_32 = x_84;
x_33 = lean_box(0);
goto block_36;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_84);
lean_dec_ref(x_38);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 x_100 = x_98;
} else {
 lean_dec_ref(x_98);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(1, 1, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_99);
return x_101;
}
}
}
}
else
{
lean_object* x_102; lean_object* x_103; uint8_t x_104; 
lean_dec_ref(x_38);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
x_102 = lean_ctor_get(x_83, 1);
lean_inc(x_102);
lean_dec_ref(x_83);
x_103 = lean_array_get_size(x_102);
x_104 = lean_nat_dec_lt(x_81, x_103);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; 
lean_dec(x_102);
lean_dec_ref(x_1);
x_105 = lean_box(0);
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_105);
return x_106;
}
else
{
lean_object* x_107; uint8_t x_108; 
x_107 = lean_box(0);
x_108 = lean_nat_dec_le(x_103, x_103);
if (x_108 == 0)
{
if (x_104 == 0)
{
lean_dec(x_102);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
size_t x_109; size_t x_110; lean_object* x_111; 
x_109 = 0;
x_110 = lean_usize_of_nat(x_103);
x_111 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_102, x_109, x_110, x_107, x_1);
lean_dec(x_102);
if (lean_obj_tag(x_111) == 0)
{
lean_dec_ref(x_111);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 x_113 = x_111;
} else {
 lean_dec_ref(x_111);
 x_113 = lean_box(0);
}
if (lean_is_scalar(x_113)) {
 x_114 = lean_alloc_ctor(1, 1, 0);
} else {
 x_114 = x_113;
}
lean_ctor_set(x_114, 0, x_112);
return x_114;
}
}
}
else
{
size_t x_115; size_t x_116; lean_object* x_117; 
x_115 = 0;
x_116 = lean_usize_of_nat(x_103);
x_117 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_102, x_115, x_116, x_107, x_1);
lean_dec(x_102);
if (lean_obj_tag(x_117) == 0)
{
lean_dec_ref(x_117);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 x_119 = x_117;
} else {
 lean_dec_ref(x_117);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(1, 1, 0);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_118);
return x_120;
}
}
}
}
}
}
else
{
uint8_t x_121; 
lean_dec_ref(x_38);
lean_dec_ref(x_37);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_121 = !lean_is_exclusive(x_39);
if (x_121 == 0)
{
return x_39;
}
else
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_39, 0);
lean_inc(x_122);
lean_dec(x_39);
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_122);
return x_123;
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
static lean_object* _init_l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("git#", 4, 4);
return x_1;
}
}
static lean_object* _init_l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__0;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__0;
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__1;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_6, x_5);
if (x_8 == 0)
{
lean_inc_ref(x_7);
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_array_uget(x_4, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
x_11 = l_Lake_VerRange_test(x_1, x_10);
lean_dec_ref(x_10);
if (x_11 == 0)
{
size_t x_12; size_t x_13; 
lean_dec(x_9);
x_12 = 1;
x_13 = lean_usize_add(x_6, x_12);
{
size_t _tmp_5 = x_13;
lean_object* _tmp_6 = x_2;
x_6 = _tmp_5;
x_7 = _tmp_6;
}
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_9);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_3);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
static lean_object* _init_l_Lake_Dependency_materialize___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": Git source not found on Reservoir", 35, 35);
return x_1;
}
}
static lean_object* _init_l_Lake_Dependency_materialize___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": version `", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lake_Dependency_materialize___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` not found on Reservoir", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lake_Dependency_materialize___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": could not fetch package versions: this may be a transient error or a bug in Lake or Reservoir", 95, 95);
return x_1;
}
}
static lean_object* _init_l_Lake_Dependency_materialize___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Dependency_materialize___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": using version `", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lake_Dependency_materialize___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` at revision `", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lake_Dependency_materialize___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_Dependency_materialize___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": could not materialize package: this may be a transient error or a bug in Lake or Reservoir", 92, 92);
return x_1;
}
}
static lean_object* _init_l_Lake_Dependency_materialize___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Dependency_materialize___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": invalid dependency version range: ", 36, 36);
return x_1;
}
}
static lean_object* _init_l_Lake_Dependency_materialize___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": ill-formed dependency: dependency is missing a source and is missing a scope for Reservoir", 92, 92);
return x_1;
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
uint8_t x_126; 
x_126 = !lean_is_exclusive(x_50);
if (x_126 == 0)
{
lean_object* x_127; 
x_127 = lean_ctor_get(x_50, 0);
if (lean_obj_tag(x_127) == 0)
{
uint8_t x_128; 
lean_inc_ref(x_48);
lean_inc(x_47);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_128 = !lean_is_exclusive(x_127);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_129 = lean_ctor_get(x_127, 0);
x_130 = l_Lake_joinRelative(x_6, x_129);
x_131 = l_Lake_instInhabitedMaterializedDep_default___closed__0;
lean_inc_ref(x_130);
lean_ctor_set(x_127, 0, x_130);
x_132 = l_Lake_defaultConfigFile;
x_133 = lean_box(0);
x_134 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_134, 0, x_47);
lean_ctor_set(x_134, 1, x_48);
lean_ctor_set(x_134, 2, x_132);
lean_ctor_set(x_134, 3, x_133);
lean_ctor_set(x_134, 4, x_127);
lean_ctor_set_uint8(x_134, sizeof(void*)*5, x_2);
x_135 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_135, 0, x_130);
lean_ctor_set(x_135, 1, x_131);
lean_ctor_set(x_135, 2, x_134);
lean_ctor_set_tag(x_50, 0);
lean_ctor_set(x_50, 0, x_135);
return x_50;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_136 = lean_ctor_get(x_127, 0);
lean_inc(x_136);
lean_dec(x_127);
x_137 = l_Lake_joinRelative(x_6, x_136);
x_138 = l_Lake_instInhabitedMaterializedDep_default___closed__0;
lean_inc_ref(x_137);
x_139 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_139, 0, x_137);
x_140 = l_Lake_defaultConfigFile;
x_141 = lean_box(0);
x_142 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_142, 0, x_47);
lean_ctor_set(x_142, 1, x_48);
lean_ctor_set(x_142, 2, x_140);
lean_ctor_set(x_142, 3, x_141);
lean_ctor_set(x_142, 4, x_139);
lean_ctor_set_uint8(x_142, sizeof(void*)*5, x_2);
x_143 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_143, 0, x_137);
lean_ctor_set(x_143, 1, x_138);
lean_ctor_set(x_143, 2, x_142);
lean_ctor_set_tag(x_50, 0);
lean_ctor_set(x_50, 0, x_143);
return x_50;
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; lean_object* x_153; 
lean_free_object(x_50);
lean_dec_ref(x_6);
x_144 = lean_ctor_get(x_127, 0);
lean_inc_ref(x_144);
x_145 = lean_ctor_get(x_127, 1);
lean_inc(x_145);
x_146 = lean_ctor_get(x_127, 2);
lean_inc(x_146);
lean_dec_ref(x_127);
x_147 = 0;
lean_inc(x_47);
x_148 = l_Lean_Name_toString(x_47, x_147);
lean_inc_ref(x_144);
x_153 = l_Lake_Git_filterUrl_x3f(x_144);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; 
x_154 = l_Lake_instInhabitedMaterializedDep_default___closed__0;
x_149 = x_154;
goto block_152;
}
else
{
lean_object* x_155; 
x_155 = lean_ctor_get(x_153, 0);
lean_inc(x_155);
lean_dec_ref(x_153);
x_149 = x_155;
goto block_152;
}
block_152:
{
lean_object* x_150; lean_object* x_151; 
lean_inc_ref(x_148);
x_150 = l_Lake_joinRelative(x_5, x_148);
x_151 = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(x_7, x_1, x_2, x_3, x_4, x_148, x_150, x_144, x_149, x_145, x_146);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_151;
}
}
}
else
{
lean_object* x_156; 
x_156 = lean_ctor_get(x_50, 0);
lean_inc(x_156);
lean_dec(x_50);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_inc_ref(x_48);
lean_inc(x_47);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_157 = lean_ctor_get(x_156, 0);
lean_inc_ref(x_157);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 x_158 = x_156;
} else {
 lean_dec_ref(x_156);
 x_158 = lean_box(0);
}
x_159 = l_Lake_joinRelative(x_6, x_157);
x_160 = l_Lake_instInhabitedMaterializedDep_default___closed__0;
lean_inc_ref(x_159);
if (lean_is_scalar(x_158)) {
 x_161 = lean_alloc_ctor(0, 1, 0);
} else {
 x_161 = x_158;
}
lean_ctor_set(x_161, 0, x_159);
x_162 = l_Lake_defaultConfigFile;
x_163 = lean_box(0);
x_164 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_164, 0, x_47);
lean_ctor_set(x_164, 1, x_48);
lean_ctor_set(x_164, 2, x_162);
lean_ctor_set(x_164, 3, x_163);
lean_ctor_set(x_164, 4, x_161);
lean_ctor_set_uint8(x_164, sizeof(void*)*5, x_2);
x_165 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_165, 0, x_159);
lean_ctor_set(x_165, 1, x_160);
lean_ctor_set(x_165, 2, x_164);
x_166 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_166, 0, x_165);
return x_166;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; lean_object* x_171; lean_object* x_172; lean_object* x_176; 
lean_dec_ref(x_6);
x_167 = lean_ctor_get(x_156, 0);
lean_inc_ref(x_167);
x_168 = lean_ctor_get(x_156, 1);
lean_inc(x_168);
x_169 = lean_ctor_get(x_156, 2);
lean_inc(x_169);
lean_dec_ref(x_156);
x_170 = 0;
lean_inc(x_47);
x_171 = l_Lean_Name_toString(x_47, x_170);
lean_inc_ref(x_167);
x_176 = l_Lake_Git_filterUrl_x3f(x_167);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; 
x_177 = l_Lake_instInhabitedMaterializedDep_default___closed__0;
x_172 = x_177;
goto block_175;
}
else
{
lean_object* x_178; 
x_178 = lean_ctor_get(x_176, 0);
lean_inc(x_178);
lean_dec_ref(x_176);
x_172 = x_178;
goto block_175;
}
block_175:
{
lean_object* x_173; lean_object* x_174; 
lean_inc_ref(x_171);
x_173 = l_Lake_joinRelative(x_5, x_171);
x_174 = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(x_7, x_1, x_2, x_3, x_4, x_171, x_173, x_167, x_172, x_168, x_169);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_174;
}
}
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; uint8_t x_465; lean_object* x_466; lean_object* x_467; 
lean_dec(x_50);
lean_dec_ref(x_6);
x_179 = lean_string_utf8_byte_size(x_48);
x_180 = lean_unsigned_to_nat(0u);
x_465 = lean_nat_dec_eq(x_179, x_180);
if (x_465 == 0)
{
if (lean_obj_tag(x_49) == 1)
{
lean_object* x_478; lean_object* x_479; 
x_478 = lean_ctor_get(x_49, 0);
lean_inc(x_478);
x_479 = l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg(x_478);
if (lean_obj_tag(x_479) == 1)
{
uint8_t x_480; 
x_480 = !lean_is_exclusive(x_479);
if (x_480 == 0)
{
lean_object* x_481; lean_object* x_482; 
x_481 = lean_ctor_get(x_479, 0);
x_482 = l_String_Slice_toString(x_481);
lean_dec(x_481);
lean_ctor_set(x_479, 0, x_482);
x_466 = x_479;
x_467 = lean_box(0);
goto block_477;
}
else
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; 
x_483 = lean_ctor_get(x_479, 0);
lean_inc(x_483);
lean_dec(x_479);
x_484 = l_String_Slice_toString(x_483);
lean_dec(x_483);
x_485 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_485, 0, x_484);
x_466 = x_485;
x_467 = lean_box(0);
goto block_477;
}
}
else
{
lean_object* x_486; lean_object* x_487; lean_object* x_488; 
lean_dec(x_479);
x_486 = l_Lake_Dependency_materialize___closed__9;
x_487 = lean_string_utf8_byte_size(x_478);
lean_inc(x_478);
x_488 = l___private_Lake_Util_Version_0__Lake_runVerParse(lean_box(0), x_478, x_486, x_180, x_487);
if (lean_obj_tag(x_488) == 0)
{
uint8_t x_489; 
lean_inc(x_47);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_489 = !lean_is_exclusive(x_488);
if (x_489 == 0)
{
lean_object* x_490; uint8_t x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; uint8_t x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; 
x_490 = lean_ctor_get(x_488, 0);
x_491 = 1;
x_492 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_47, x_491);
x_493 = l_Lake_Dependency_materialize___closed__10;
x_494 = lean_string_append(x_492, x_493);
x_495 = lean_string_append(x_494, x_490);
lean_dec(x_490);
x_496 = 3;
x_497 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_497, 0, x_495);
lean_ctor_set_uint8(x_497, sizeof(void*)*1, x_496);
x_498 = lean_apply_2(x_7, x_497, lean_box(0));
x_499 = lean_box(0);
lean_ctor_set_tag(x_488, 1);
lean_ctor_set(x_488, 0, x_499);
return x_488;
}
else
{
lean_object* x_500; uint8_t x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; uint8_t x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; 
x_500 = lean_ctor_get(x_488, 0);
lean_inc(x_500);
lean_dec(x_488);
x_501 = 1;
x_502 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_47, x_501);
x_503 = l_Lake_Dependency_materialize___closed__10;
x_504 = lean_string_append(x_502, x_503);
x_505 = lean_string_append(x_504, x_500);
lean_dec(x_500);
x_506 = 3;
x_507 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_507, 0, x_505);
lean_ctor_set_uint8(x_507, sizeof(void*)*1, x_506);
x_508 = lean_apply_2(x_7, x_507, lean_box(0));
x_509 = lean_box(0);
x_510 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_510, 0, x_509);
return x_510;
}
}
else
{
uint8_t x_511; 
x_511 = !lean_is_exclusive(x_488);
if (x_511 == 0)
{
lean_ctor_set_tag(x_488, 2);
x_466 = x_488;
x_467 = lean_box(0);
goto block_477;
}
else
{
lean_object* x_512; lean_object* x_513; 
x_512 = lean_ctor_get(x_488, 0);
lean_inc(x_512);
lean_dec(x_488);
x_513 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_513, 0, x_512);
x_466 = x_513;
x_467 = lean_box(0);
goto block_477;
}
}
}
}
else
{
lean_object* x_514; 
x_514 = lean_box(0);
x_466 = x_514;
x_467 = lean_box(0);
goto block_477;
}
}
else
{
lean_object* x_515; lean_object* x_516; lean_object* x_517; uint8_t x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; 
lean_inc(x_47);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_515 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_47, x_465);
x_516 = l_Lake_Dependency_materialize___closed__11;
x_517 = lean_string_append(x_515, x_516);
x_518 = 3;
x_519 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_519, 0, x_517);
lean_ctor_set_uint8(x_519, sizeof(void*)*1, x_518);
x_520 = lean_apply_2(x_7, x_519, lean_box(0));
x_521 = lean_box(0);
x_522 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_522, 0, x_521);
return x_522;
}
block_207:
{
lean_object* x_191; uint8_t x_192; 
x_191 = lean_array_get_size(x_189);
x_192 = lean_nat_dec_lt(x_180, x_191);
if (x_192 == 0)
{
lean_dec_ref(x_189);
x_69 = x_182;
x_70 = x_181;
x_71 = x_183;
x_72 = x_184;
x_73 = x_185;
x_74 = x_186;
x_75 = x_187;
x_76 = x_188;
x_77 = lean_box(0);
goto block_125;
}
else
{
lean_object* x_193; uint8_t x_194; 
x_193 = lean_box(0);
x_194 = lean_nat_dec_le(x_191, x_191);
if (x_194 == 0)
{
if (x_192 == 0)
{
lean_dec_ref(x_189);
x_69 = x_182;
x_70 = x_181;
x_71 = x_183;
x_72 = x_184;
x_73 = x_185;
x_74 = x_186;
x_75 = x_187;
x_76 = x_188;
x_77 = lean_box(0);
goto block_125;
}
else
{
size_t x_195; size_t x_196; lean_object* x_197; 
x_195 = 0;
x_196 = lean_usize_of_nat(x_191);
lean_inc_ref(x_7);
x_197 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_189, x_195, x_196, x_193, x_7);
lean_dec_ref(x_189);
if (lean_obj_tag(x_197) == 0)
{
lean_dec_ref(x_197);
x_69 = x_182;
x_70 = x_181;
x_71 = x_183;
x_72 = x_184;
x_73 = x_185;
x_74 = x_186;
x_75 = x_187;
x_76 = x_188;
x_77 = lean_box(0);
goto block_125;
}
else
{
uint8_t x_198; 
lean_dec_ref(x_188);
lean_dec_ref(x_187);
lean_dec_ref(x_186);
lean_dec(x_185);
lean_dec_ref(x_184);
lean_dec_ref(x_183);
lean_dec(x_182);
lean_dec_ref(x_181);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_198 = !lean_is_exclusive(x_197);
if (x_198 == 0)
{
return x_197;
}
else
{
lean_object* x_199; lean_object* x_200; 
x_199 = lean_ctor_get(x_197, 0);
lean_inc(x_199);
lean_dec(x_197);
x_200 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_200, 0, x_199);
return x_200;
}
}
}
}
else
{
size_t x_201; size_t x_202; lean_object* x_203; 
x_201 = 0;
x_202 = lean_usize_of_nat(x_191);
lean_inc_ref(x_7);
x_203 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_189, x_201, x_202, x_193, x_7);
lean_dec_ref(x_189);
if (lean_obj_tag(x_203) == 0)
{
lean_dec_ref(x_203);
x_69 = x_182;
x_70 = x_181;
x_71 = x_183;
x_72 = x_184;
x_73 = x_185;
x_74 = x_186;
x_75 = x_187;
x_76 = x_188;
x_77 = lean_box(0);
goto block_125;
}
else
{
uint8_t x_204; 
lean_dec_ref(x_188);
lean_dec_ref(x_187);
lean_dec_ref(x_186);
lean_dec(x_185);
lean_dec_ref(x_184);
lean_dec_ref(x_183);
lean_dec(x_182);
lean_dec_ref(x_181);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_204 = !lean_is_exclusive(x_203);
if (x_204 == 0)
{
return x_203;
}
else
{
lean_object* x_205; lean_object* x_206; 
x_205 = lean_ctor_get(x_203, 0);
lean_inc(x_205);
lean_dec(x_203);
x_206 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_206, 0, x_205);
return x_206;
}
}
}
}
}
block_442:
{
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
lean_dec_ref(x_210);
lean_dec(x_208);
lean_inc_ref(x_48);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_212 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0;
x_213 = lean_string_append(x_48, x_212);
x_214 = lean_string_append(x_213, x_209);
lean_dec_ref(x_209);
x_215 = l_Lake_Dependency_materialize___closed__8;
x_216 = lean_string_append(x_214, x_215);
x_217 = 3;
x_218 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set_uint8(x_218, sizeof(void*)*1, x_217);
x_219 = lean_apply_2(x_7, x_218, lean_box(0));
x_220 = lean_box(0);
x_221 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_221, 0, x_220);
return x_221;
}
else
{
uint8_t x_222; 
x_222 = !lean_is_exclusive(x_210);
if (x_222 == 0)
{
lean_object* x_223; 
x_223 = lean_ctor_get(x_210, 0);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; uint8_t x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
lean_free_object(x_210);
lean_inc_ref(x_48);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_224 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed(x_48, x_209, x_208);
lean_dec_ref(x_209);
x_225 = 3;
x_226 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_226, 0, x_224);
lean_ctor_set_uint8(x_226, sizeof(void*)*1, x_225);
x_227 = lean_apply_2(x_7, x_226, lean_box(0));
x_228 = lean_box(0);
x_229 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_229, 0, x_228);
return x_229;
}
else
{
lean_object* x_230; lean_object* x_231; 
x_230 = lean_ctor_get(x_223, 0);
lean_inc(x_230);
lean_dec_ref(x_223);
x_231 = l_Lake_RegistryPkg_gitSrc_x3f(x_230);
if (lean_obj_tag(x_231) == 1)
{
uint8_t x_232; 
x_232 = !lean_is_exclusive(x_231);
if (x_232 == 0)
{
lean_object* x_233; 
x_233 = lean_ctor_get(x_231, 0);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_234 = lean_ctor_get(x_233, 1);
lean_inc_ref(x_234);
x_235 = lean_ctor_get(x_233, 2);
lean_inc(x_235);
x_236 = lean_ctor_get(x_233, 3);
lean_inc(x_236);
x_237 = lean_ctor_get(x_233, 4);
lean_inc(x_237);
lean_dec_ref(x_233);
x_238 = lean_ctor_get(x_230, 0);
lean_inc_ref(x_238);
x_239 = lean_ctor_get(x_230, 1);
lean_inc_ref(x_239);
lean_dec(x_230);
x_240 = l_Lake_joinRelative(x_5, x_238);
switch (lean_obj_tag(x_208)) {
case 0:
{
lean_object* x_241; 
lean_free_object(x_210);
lean_dec_ref(x_209);
x_241 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
if (lean_obj_tag(x_236) == 0)
{
uint8_t x_242; 
lean_dec_ref(x_240);
lean_dec_ref(x_239);
lean_dec(x_237);
lean_dec(x_235);
lean_dec_ref(x_234);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_242 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5;
if (x_242 == 0)
{
lean_object* x_243; 
lean_dec_ref(x_7);
x_243 = lean_box(0);
lean_ctor_set(x_231, 0, x_243);
return x_231;
}
else
{
lean_object* x_244; uint8_t x_245; 
lean_free_object(x_231);
x_244 = lean_box(0);
x_245 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6;
if (x_245 == 0)
{
if (x_242 == 0)
{
lean_dec_ref(x_7);
x_9 = lean_box(0);
goto block_12;
}
else
{
size_t x_246; size_t x_247; lean_object* x_248; 
x_246 = 0;
x_247 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
x_248 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_241, x_246, x_247, x_244, x_7);
if (lean_obj_tag(x_248) == 0)
{
lean_dec_ref(x_248);
x_9 = lean_box(0);
goto block_12;
}
else
{
uint8_t x_249; 
x_249 = !lean_is_exclusive(x_248);
if (x_249 == 0)
{
return x_248;
}
else
{
lean_object* x_250; lean_object* x_251; 
x_250 = lean_ctor_get(x_248, 0);
lean_inc(x_250);
lean_dec(x_248);
x_251 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_251, 0, x_250);
return x_251;
}
}
}
}
else
{
size_t x_252; size_t x_253; lean_object* x_254; 
x_252 = 0;
x_253 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
x_254 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_241, x_252, x_253, x_244, x_7);
if (lean_obj_tag(x_254) == 0)
{
lean_dec_ref(x_254);
x_9 = lean_box(0);
goto block_12;
}
else
{
uint8_t x_255; 
x_255 = !lean_is_exclusive(x_254);
if (x_255 == 0)
{
return x_254;
}
else
{
lean_object* x_256; lean_object* x_257; 
x_256 = lean_ctor_get(x_254, 0);
lean_inc(x_256);
lean_dec(x_254);
x_257 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_257, 0, x_256);
return x_257;
}
}
}
}
}
else
{
lean_object* x_258; uint8_t x_259; 
lean_free_object(x_231);
x_258 = lean_ctor_get(x_236, 0);
lean_inc(x_258);
lean_dec_ref(x_236);
x_259 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5;
if (x_259 == 0)
{
x_36 = x_237;
x_37 = x_234;
x_38 = x_240;
x_39 = x_235;
x_40 = x_239;
x_41 = x_258;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
else
{
lean_object* x_260; uint8_t x_261; 
x_260 = lean_box(0);
x_261 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6;
if (x_261 == 0)
{
if (x_259 == 0)
{
x_36 = x_237;
x_37 = x_234;
x_38 = x_240;
x_39 = x_235;
x_40 = x_239;
x_41 = x_258;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
else
{
size_t x_262; size_t x_263; lean_object* x_264; 
x_262 = 0;
x_263 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
lean_inc_ref(x_7);
x_264 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_241, x_262, x_263, x_260, x_7);
if (lean_obj_tag(x_264) == 0)
{
lean_dec_ref(x_264);
x_36 = x_237;
x_37 = x_234;
x_38 = x_240;
x_39 = x_235;
x_40 = x_239;
x_41 = x_258;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
else
{
uint8_t x_265; 
lean_dec(x_258);
lean_dec_ref(x_240);
lean_dec_ref(x_239);
lean_dec(x_237);
lean_dec(x_235);
lean_dec_ref(x_234);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_265 = !lean_is_exclusive(x_264);
if (x_265 == 0)
{
return x_264;
}
else
{
lean_object* x_266; lean_object* x_267; 
x_266 = lean_ctor_get(x_264, 0);
lean_inc(x_266);
lean_dec(x_264);
x_267 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_267, 0, x_266);
return x_267;
}
}
}
}
else
{
size_t x_268; size_t x_269; lean_object* x_270; 
x_268 = 0;
x_269 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
lean_inc_ref(x_7);
x_270 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_241, x_268, x_269, x_260, x_7);
if (lean_obj_tag(x_270) == 0)
{
lean_dec_ref(x_270);
x_36 = x_237;
x_37 = x_234;
x_38 = x_240;
x_39 = x_235;
x_40 = x_239;
x_41 = x_258;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
else
{
uint8_t x_271; 
lean_dec(x_258);
lean_dec_ref(x_240);
lean_dec_ref(x_239);
lean_dec(x_237);
lean_dec(x_235);
lean_dec_ref(x_234);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_271 = !lean_is_exclusive(x_270);
if (x_271 == 0)
{
return x_270;
}
else
{
lean_object* x_272; lean_object* x_273; 
x_272 = lean_ctor_get(x_270, 0);
lean_inc(x_272);
lean_dec(x_270);
x_273 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_273, 0, x_272);
return x_273;
}
}
}
}
}
}
case 1:
{
lean_object* x_274; lean_object* x_275; uint8_t x_276; 
lean_dec(x_236);
lean_free_object(x_231);
lean_free_object(x_210);
lean_dec_ref(x_209);
x_274 = lean_ctor_get(x_208, 0);
lean_inc_ref(x_274);
lean_dec_ref(x_208);
x_275 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
x_276 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5;
if (x_276 == 0)
{
x_36 = x_237;
x_37 = x_234;
x_38 = x_240;
x_39 = x_235;
x_40 = x_239;
x_41 = x_274;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
else
{
lean_object* x_277; uint8_t x_278; 
x_277 = lean_box(0);
x_278 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6;
if (x_278 == 0)
{
if (x_276 == 0)
{
x_36 = x_237;
x_37 = x_234;
x_38 = x_240;
x_39 = x_235;
x_40 = x_239;
x_41 = x_274;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
else
{
size_t x_279; size_t x_280; lean_object* x_281; 
x_279 = 0;
x_280 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
lean_inc_ref(x_7);
x_281 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_275, x_279, x_280, x_277, x_7);
if (lean_obj_tag(x_281) == 0)
{
lean_dec_ref(x_281);
x_36 = x_237;
x_37 = x_234;
x_38 = x_240;
x_39 = x_235;
x_40 = x_239;
x_41 = x_274;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
else
{
uint8_t x_282; 
lean_dec_ref(x_274);
lean_dec_ref(x_240);
lean_dec_ref(x_239);
lean_dec(x_237);
lean_dec(x_235);
lean_dec_ref(x_234);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_282 = !lean_is_exclusive(x_281);
if (x_282 == 0)
{
return x_281;
}
else
{
lean_object* x_283; lean_object* x_284; 
x_283 = lean_ctor_get(x_281, 0);
lean_inc(x_283);
lean_dec(x_281);
x_284 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_284, 0, x_283);
return x_284;
}
}
}
}
else
{
size_t x_285; size_t x_286; lean_object* x_287; 
x_285 = 0;
x_286 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
lean_inc_ref(x_7);
x_287 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_275, x_285, x_286, x_277, x_7);
if (lean_obj_tag(x_287) == 0)
{
lean_dec_ref(x_287);
x_36 = x_237;
x_37 = x_234;
x_38 = x_240;
x_39 = x_235;
x_40 = x_239;
x_41 = x_274;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
else
{
uint8_t x_288; 
lean_dec_ref(x_274);
lean_dec_ref(x_240);
lean_dec_ref(x_239);
lean_dec(x_237);
lean_dec(x_235);
lean_dec_ref(x_234);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_288 = !lean_is_exclusive(x_287);
if (x_288 == 0)
{
return x_287;
}
else
{
lean_object* x_289; lean_object* x_290; 
x_289 = lean_ctor_get(x_287, 0);
lean_inc(x_289);
lean_dec(x_287);
x_290 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_290, 0, x_289);
return x_290;
}
}
}
}
}
default: 
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; 
lean_dec(x_236);
lean_free_object(x_231);
x_291 = lean_ctor_get(x_208, 0);
lean_inc_ref(x_291);
lean_dec_ref(x_208);
x_292 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
lean_inc_ref(x_209);
lean_inc_ref(x_48);
lean_inc_ref(x_3);
x_293 = l_Lake_Reservoir_fetchPkgVersions(x_3, x_48, x_209, x_292);
if (lean_obj_tag(x_293) == 0)
{
lean_object* x_294; lean_object* x_295; 
x_294 = lean_ctor_get(x_293, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_293, 1);
lean_inc(x_295);
lean_dec_ref(x_293);
lean_ctor_set(x_210, 0, x_294);
x_181 = x_209;
x_182 = x_237;
x_183 = x_234;
x_184 = x_240;
x_185 = x_235;
x_186 = x_291;
x_187 = x_239;
x_188 = x_210;
x_189 = x_295;
x_190 = lean_box(0);
goto block_207;
}
else
{
lean_object* x_296; lean_object* x_297; 
x_296 = lean_ctor_get(x_293, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_293, 1);
lean_inc(x_297);
lean_dec_ref(x_293);
lean_ctor_set_tag(x_210, 0);
lean_ctor_set(x_210, 0, x_296);
x_181 = x_209;
x_182 = x_237;
x_183 = x_234;
x_184 = x_240;
x_185 = x_235;
x_186 = x_291;
x_187 = x_239;
x_188 = x_210;
x_189 = x_297;
x_190 = lean_box(0);
goto block_207;
}
}
}
}
else
{
lean_free_object(x_231);
lean_dec(x_233);
lean_free_object(x_210);
lean_dec_ref(x_209);
lean_dec(x_208);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_13 = x_230;
x_14 = x_7;
x_15 = lean_box(0);
goto block_24;
}
}
else
{
lean_object* x_298; 
x_298 = lean_ctor_get(x_231, 0);
lean_inc(x_298);
lean_dec(x_231);
if (lean_obj_tag(x_298) == 0)
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_299 = lean_ctor_get(x_298, 1);
lean_inc_ref(x_299);
x_300 = lean_ctor_get(x_298, 2);
lean_inc(x_300);
x_301 = lean_ctor_get(x_298, 3);
lean_inc(x_301);
x_302 = lean_ctor_get(x_298, 4);
lean_inc(x_302);
lean_dec_ref(x_298);
x_303 = lean_ctor_get(x_230, 0);
lean_inc_ref(x_303);
x_304 = lean_ctor_get(x_230, 1);
lean_inc_ref(x_304);
lean_dec(x_230);
x_305 = l_Lake_joinRelative(x_5, x_303);
switch (lean_obj_tag(x_208)) {
case 0:
{
lean_object* x_306; 
lean_free_object(x_210);
lean_dec_ref(x_209);
x_306 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
if (lean_obj_tag(x_301) == 0)
{
uint8_t x_307; 
lean_dec_ref(x_305);
lean_dec_ref(x_304);
lean_dec(x_302);
lean_dec(x_300);
lean_dec_ref(x_299);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_307 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5;
if (x_307 == 0)
{
lean_object* x_308; lean_object* x_309; 
lean_dec_ref(x_7);
x_308 = lean_box(0);
x_309 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_309, 0, x_308);
return x_309;
}
else
{
lean_object* x_310; uint8_t x_311; 
x_310 = lean_box(0);
x_311 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6;
if (x_311 == 0)
{
if (x_307 == 0)
{
lean_dec_ref(x_7);
x_9 = lean_box(0);
goto block_12;
}
else
{
size_t x_312; size_t x_313; lean_object* x_314; 
x_312 = 0;
x_313 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
x_314 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_306, x_312, x_313, x_310, x_7);
if (lean_obj_tag(x_314) == 0)
{
lean_dec_ref(x_314);
x_9 = lean_box(0);
goto block_12;
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
if (lean_is_exclusive(x_314)) {
 lean_ctor_release(x_314, 0);
 x_316 = x_314;
} else {
 lean_dec_ref(x_314);
 x_316 = lean_box(0);
}
if (lean_is_scalar(x_316)) {
 x_317 = lean_alloc_ctor(1, 1, 0);
} else {
 x_317 = x_316;
}
lean_ctor_set(x_317, 0, x_315);
return x_317;
}
}
}
else
{
size_t x_318; size_t x_319; lean_object* x_320; 
x_318 = 0;
x_319 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
x_320 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_306, x_318, x_319, x_310, x_7);
if (lean_obj_tag(x_320) == 0)
{
lean_dec_ref(x_320);
x_9 = lean_box(0);
goto block_12;
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_321 = lean_ctor_get(x_320, 0);
lean_inc(x_321);
if (lean_is_exclusive(x_320)) {
 lean_ctor_release(x_320, 0);
 x_322 = x_320;
} else {
 lean_dec_ref(x_320);
 x_322 = lean_box(0);
}
if (lean_is_scalar(x_322)) {
 x_323 = lean_alloc_ctor(1, 1, 0);
} else {
 x_323 = x_322;
}
lean_ctor_set(x_323, 0, x_321);
return x_323;
}
}
}
}
else
{
lean_object* x_324; uint8_t x_325; 
x_324 = lean_ctor_get(x_301, 0);
lean_inc(x_324);
lean_dec_ref(x_301);
x_325 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5;
if (x_325 == 0)
{
x_36 = x_302;
x_37 = x_299;
x_38 = x_305;
x_39 = x_300;
x_40 = x_304;
x_41 = x_324;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
else
{
lean_object* x_326; uint8_t x_327; 
x_326 = lean_box(0);
x_327 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6;
if (x_327 == 0)
{
if (x_325 == 0)
{
x_36 = x_302;
x_37 = x_299;
x_38 = x_305;
x_39 = x_300;
x_40 = x_304;
x_41 = x_324;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
else
{
size_t x_328; size_t x_329; lean_object* x_330; 
x_328 = 0;
x_329 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
lean_inc_ref(x_7);
x_330 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_306, x_328, x_329, x_326, x_7);
if (lean_obj_tag(x_330) == 0)
{
lean_dec_ref(x_330);
x_36 = x_302;
x_37 = x_299;
x_38 = x_305;
x_39 = x_300;
x_40 = x_304;
x_41 = x_324;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; 
lean_dec(x_324);
lean_dec_ref(x_305);
lean_dec_ref(x_304);
lean_dec(x_302);
lean_dec(x_300);
lean_dec_ref(x_299);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_331 = lean_ctor_get(x_330, 0);
lean_inc(x_331);
if (lean_is_exclusive(x_330)) {
 lean_ctor_release(x_330, 0);
 x_332 = x_330;
} else {
 lean_dec_ref(x_330);
 x_332 = lean_box(0);
}
if (lean_is_scalar(x_332)) {
 x_333 = lean_alloc_ctor(1, 1, 0);
} else {
 x_333 = x_332;
}
lean_ctor_set(x_333, 0, x_331);
return x_333;
}
}
}
else
{
size_t x_334; size_t x_335; lean_object* x_336; 
x_334 = 0;
x_335 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
lean_inc_ref(x_7);
x_336 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_306, x_334, x_335, x_326, x_7);
if (lean_obj_tag(x_336) == 0)
{
lean_dec_ref(x_336);
x_36 = x_302;
x_37 = x_299;
x_38 = x_305;
x_39 = x_300;
x_40 = x_304;
x_41 = x_324;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; 
lean_dec(x_324);
lean_dec_ref(x_305);
lean_dec_ref(x_304);
lean_dec(x_302);
lean_dec(x_300);
lean_dec_ref(x_299);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_337 = lean_ctor_get(x_336, 0);
lean_inc(x_337);
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 x_338 = x_336;
} else {
 lean_dec_ref(x_336);
 x_338 = lean_box(0);
}
if (lean_is_scalar(x_338)) {
 x_339 = lean_alloc_ctor(1, 1, 0);
} else {
 x_339 = x_338;
}
lean_ctor_set(x_339, 0, x_337);
return x_339;
}
}
}
}
}
case 1:
{
lean_object* x_340; lean_object* x_341; uint8_t x_342; 
lean_dec(x_301);
lean_free_object(x_210);
lean_dec_ref(x_209);
x_340 = lean_ctor_get(x_208, 0);
lean_inc_ref(x_340);
lean_dec_ref(x_208);
x_341 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
x_342 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5;
if (x_342 == 0)
{
x_36 = x_302;
x_37 = x_299;
x_38 = x_305;
x_39 = x_300;
x_40 = x_304;
x_41 = x_340;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
else
{
lean_object* x_343; uint8_t x_344; 
x_343 = lean_box(0);
x_344 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6;
if (x_344 == 0)
{
if (x_342 == 0)
{
x_36 = x_302;
x_37 = x_299;
x_38 = x_305;
x_39 = x_300;
x_40 = x_304;
x_41 = x_340;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
else
{
size_t x_345; size_t x_346; lean_object* x_347; 
x_345 = 0;
x_346 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
lean_inc_ref(x_7);
x_347 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_341, x_345, x_346, x_343, x_7);
if (lean_obj_tag(x_347) == 0)
{
lean_dec_ref(x_347);
x_36 = x_302;
x_37 = x_299;
x_38 = x_305;
x_39 = x_300;
x_40 = x_304;
x_41 = x_340;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
else
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; 
lean_dec_ref(x_340);
lean_dec_ref(x_305);
lean_dec_ref(x_304);
lean_dec(x_302);
lean_dec(x_300);
lean_dec_ref(x_299);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_348 = lean_ctor_get(x_347, 0);
lean_inc(x_348);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 x_349 = x_347;
} else {
 lean_dec_ref(x_347);
 x_349 = lean_box(0);
}
if (lean_is_scalar(x_349)) {
 x_350 = lean_alloc_ctor(1, 1, 0);
} else {
 x_350 = x_349;
}
lean_ctor_set(x_350, 0, x_348);
return x_350;
}
}
}
else
{
size_t x_351; size_t x_352; lean_object* x_353; 
x_351 = 0;
x_352 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
lean_inc_ref(x_7);
x_353 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_341, x_351, x_352, x_343, x_7);
if (lean_obj_tag(x_353) == 0)
{
lean_dec_ref(x_353);
x_36 = x_302;
x_37 = x_299;
x_38 = x_305;
x_39 = x_300;
x_40 = x_304;
x_41 = x_340;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; 
lean_dec_ref(x_340);
lean_dec_ref(x_305);
lean_dec_ref(x_304);
lean_dec(x_302);
lean_dec(x_300);
lean_dec_ref(x_299);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_354 = lean_ctor_get(x_353, 0);
lean_inc(x_354);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 x_355 = x_353;
} else {
 lean_dec_ref(x_353);
 x_355 = lean_box(0);
}
if (lean_is_scalar(x_355)) {
 x_356 = lean_alloc_ctor(1, 1, 0);
} else {
 x_356 = x_355;
}
lean_ctor_set(x_356, 0, x_354);
return x_356;
}
}
}
}
default: 
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; 
lean_dec(x_301);
x_357 = lean_ctor_get(x_208, 0);
lean_inc_ref(x_357);
lean_dec_ref(x_208);
x_358 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
lean_inc_ref(x_209);
lean_inc_ref(x_48);
lean_inc_ref(x_3);
x_359 = l_Lake_Reservoir_fetchPkgVersions(x_3, x_48, x_209, x_358);
if (lean_obj_tag(x_359) == 0)
{
lean_object* x_360; lean_object* x_361; 
x_360 = lean_ctor_get(x_359, 0);
lean_inc(x_360);
x_361 = lean_ctor_get(x_359, 1);
lean_inc(x_361);
lean_dec_ref(x_359);
lean_ctor_set(x_210, 0, x_360);
x_181 = x_209;
x_182 = x_302;
x_183 = x_299;
x_184 = x_305;
x_185 = x_300;
x_186 = x_357;
x_187 = x_304;
x_188 = x_210;
x_189 = x_361;
x_190 = lean_box(0);
goto block_207;
}
else
{
lean_object* x_362; lean_object* x_363; 
x_362 = lean_ctor_get(x_359, 0);
lean_inc(x_362);
x_363 = lean_ctor_get(x_359, 1);
lean_inc(x_363);
lean_dec_ref(x_359);
lean_ctor_set_tag(x_210, 0);
lean_ctor_set(x_210, 0, x_362);
x_181 = x_209;
x_182 = x_302;
x_183 = x_299;
x_184 = x_305;
x_185 = x_300;
x_186 = x_357;
x_187 = x_304;
x_188 = x_210;
x_189 = x_363;
x_190 = lean_box(0);
goto block_207;
}
}
}
}
else
{
lean_dec(x_298);
lean_free_object(x_210);
lean_dec_ref(x_209);
lean_dec(x_208);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_13 = x_230;
x_14 = x_7;
x_15 = lean_box(0);
goto block_24;
}
}
}
else
{
lean_dec(x_231);
lean_free_object(x_210);
lean_dec_ref(x_209);
lean_dec(x_208);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_13 = x_230;
x_14 = x_7;
x_15 = lean_box(0);
goto block_24;
}
}
}
else
{
lean_object* x_364; 
x_364 = lean_ctor_get(x_210, 0);
lean_inc(x_364);
lean_dec(x_210);
if (lean_obj_tag(x_364) == 0)
{
lean_object* x_365; uint8_t x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; 
lean_inc_ref(x_48);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_365 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed(x_48, x_209, x_208);
lean_dec_ref(x_209);
x_366 = 3;
x_367 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_367, 0, x_365);
lean_ctor_set_uint8(x_367, sizeof(void*)*1, x_366);
x_368 = lean_apply_2(x_7, x_367, lean_box(0));
x_369 = lean_box(0);
x_370 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_370, 0, x_369);
return x_370;
}
else
{
lean_object* x_371; lean_object* x_372; 
x_371 = lean_ctor_get(x_364, 0);
lean_inc(x_371);
lean_dec_ref(x_364);
x_372 = l_Lake_RegistryPkg_gitSrc_x3f(x_371);
if (lean_obj_tag(x_372) == 1)
{
lean_object* x_373; lean_object* x_374; 
x_373 = lean_ctor_get(x_372, 0);
lean_inc(x_373);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 x_374 = x_372;
} else {
 lean_dec_ref(x_372);
 x_374 = lean_box(0);
}
if (lean_obj_tag(x_373) == 0)
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_375 = lean_ctor_get(x_373, 1);
lean_inc_ref(x_375);
x_376 = lean_ctor_get(x_373, 2);
lean_inc(x_376);
x_377 = lean_ctor_get(x_373, 3);
lean_inc(x_377);
x_378 = lean_ctor_get(x_373, 4);
lean_inc(x_378);
lean_dec_ref(x_373);
x_379 = lean_ctor_get(x_371, 0);
lean_inc_ref(x_379);
x_380 = lean_ctor_get(x_371, 1);
lean_inc_ref(x_380);
lean_dec(x_371);
x_381 = l_Lake_joinRelative(x_5, x_379);
switch (lean_obj_tag(x_208)) {
case 0:
{
lean_object* x_382; 
lean_dec_ref(x_209);
x_382 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
if (lean_obj_tag(x_377) == 0)
{
uint8_t x_383; 
lean_dec_ref(x_381);
lean_dec_ref(x_380);
lean_dec(x_378);
lean_dec(x_376);
lean_dec_ref(x_375);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_383 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5;
if (x_383 == 0)
{
lean_object* x_384; lean_object* x_385; 
lean_dec_ref(x_7);
x_384 = lean_box(0);
if (lean_is_scalar(x_374)) {
 x_385 = lean_alloc_ctor(1, 1, 0);
} else {
 x_385 = x_374;
}
lean_ctor_set(x_385, 0, x_384);
return x_385;
}
else
{
lean_object* x_386; uint8_t x_387; 
lean_dec(x_374);
x_386 = lean_box(0);
x_387 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6;
if (x_387 == 0)
{
if (x_383 == 0)
{
lean_dec_ref(x_7);
x_9 = lean_box(0);
goto block_12;
}
else
{
size_t x_388; size_t x_389; lean_object* x_390; 
x_388 = 0;
x_389 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
x_390 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_382, x_388, x_389, x_386, x_7);
if (lean_obj_tag(x_390) == 0)
{
lean_dec_ref(x_390);
x_9 = lean_box(0);
goto block_12;
}
else
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; 
x_391 = lean_ctor_get(x_390, 0);
lean_inc(x_391);
if (lean_is_exclusive(x_390)) {
 lean_ctor_release(x_390, 0);
 x_392 = x_390;
} else {
 lean_dec_ref(x_390);
 x_392 = lean_box(0);
}
if (lean_is_scalar(x_392)) {
 x_393 = lean_alloc_ctor(1, 1, 0);
} else {
 x_393 = x_392;
}
lean_ctor_set(x_393, 0, x_391);
return x_393;
}
}
}
else
{
size_t x_394; size_t x_395; lean_object* x_396; 
x_394 = 0;
x_395 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
x_396 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_382, x_394, x_395, x_386, x_7);
if (lean_obj_tag(x_396) == 0)
{
lean_dec_ref(x_396);
x_9 = lean_box(0);
goto block_12;
}
else
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; 
x_397 = lean_ctor_get(x_396, 0);
lean_inc(x_397);
if (lean_is_exclusive(x_396)) {
 lean_ctor_release(x_396, 0);
 x_398 = x_396;
} else {
 lean_dec_ref(x_396);
 x_398 = lean_box(0);
}
if (lean_is_scalar(x_398)) {
 x_399 = lean_alloc_ctor(1, 1, 0);
} else {
 x_399 = x_398;
}
lean_ctor_set(x_399, 0, x_397);
return x_399;
}
}
}
}
else
{
lean_object* x_400; uint8_t x_401; 
lean_dec(x_374);
x_400 = lean_ctor_get(x_377, 0);
lean_inc(x_400);
lean_dec_ref(x_377);
x_401 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5;
if (x_401 == 0)
{
x_36 = x_378;
x_37 = x_375;
x_38 = x_381;
x_39 = x_376;
x_40 = x_380;
x_41 = x_400;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
else
{
lean_object* x_402; uint8_t x_403; 
x_402 = lean_box(0);
x_403 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6;
if (x_403 == 0)
{
if (x_401 == 0)
{
x_36 = x_378;
x_37 = x_375;
x_38 = x_381;
x_39 = x_376;
x_40 = x_380;
x_41 = x_400;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
else
{
size_t x_404; size_t x_405; lean_object* x_406; 
x_404 = 0;
x_405 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
lean_inc_ref(x_7);
x_406 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_382, x_404, x_405, x_402, x_7);
if (lean_obj_tag(x_406) == 0)
{
lean_dec_ref(x_406);
x_36 = x_378;
x_37 = x_375;
x_38 = x_381;
x_39 = x_376;
x_40 = x_380;
x_41 = x_400;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
else
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; 
lean_dec(x_400);
lean_dec_ref(x_381);
lean_dec_ref(x_380);
lean_dec(x_378);
lean_dec(x_376);
lean_dec_ref(x_375);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_407 = lean_ctor_get(x_406, 0);
lean_inc(x_407);
if (lean_is_exclusive(x_406)) {
 lean_ctor_release(x_406, 0);
 x_408 = x_406;
} else {
 lean_dec_ref(x_406);
 x_408 = lean_box(0);
}
if (lean_is_scalar(x_408)) {
 x_409 = lean_alloc_ctor(1, 1, 0);
} else {
 x_409 = x_408;
}
lean_ctor_set(x_409, 0, x_407);
return x_409;
}
}
}
else
{
size_t x_410; size_t x_411; lean_object* x_412; 
x_410 = 0;
x_411 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
lean_inc_ref(x_7);
x_412 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_382, x_410, x_411, x_402, x_7);
if (lean_obj_tag(x_412) == 0)
{
lean_dec_ref(x_412);
x_36 = x_378;
x_37 = x_375;
x_38 = x_381;
x_39 = x_376;
x_40 = x_380;
x_41 = x_400;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
else
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; 
lean_dec(x_400);
lean_dec_ref(x_381);
lean_dec_ref(x_380);
lean_dec(x_378);
lean_dec(x_376);
lean_dec_ref(x_375);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_413 = lean_ctor_get(x_412, 0);
lean_inc(x_413);
if (lean_is_exclusive(x_412)) {
 lean_ctor_release(x_412, 0);
 x_414 = x_412;
} else {
 lean_dec_ref(x_412);
 x_414 = lean_box(0);
}
if (lean_is_scalar(x_414)) {
 x_415 = lean_alloc_ctor(1, 1, 0);
} else {
 x_415 = x_414;
}
lean_ctor_set(x_415, 0, x_413);
return x_415;
}
}
}
}
}
case 1:
{
lean_object* x_416; lean_object* x_417; uint8_t x_418; 
lean_dec(x_377);
lean_dec(x_374);
lean_dec_ref(x_209);
x_416 = lean_ctor_get(x_208, 0);
lean_inc_ref(x_416);
lean_dec_ref(x_208);
x_417 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
x_418 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5;
if (x_418 == 0)
{
x_36 = x_378;
x_37 = x_375;
x_38 = x_381;
x_39 = x_376;
x_40 = x_380;
x_41 = x_416;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
else
{
lean_object* x_419; uint8_t x_420; 
x_419 = lean_box(0);
x_420 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6;
if (x_420 == 0)
{
if (x_418 == 0)
{
x_36 = x_378;
x_37 = x_375;
x_38 = x_381;
x_39 = x_376;
x_40 = x_380;
x_41 = x_416;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
else
{
size_t x_421; size_t x_422; lean_object* x_423; 
x_421 = 0;
x_422 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
lean_inc_ref(x_7);
x_423 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_417, x_421, x_422, x_419, x_7);
if (lean_obj_tag(x_423) == 0)
{
lean_dec_ref(x_423);
x_36 = x_378;
x_37 = x_375;
x_38 = x_381;
x_39 = x_376;
x_40 = x_380;
x_41 = x_416;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
else
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; 
lean_dec_ref(x_416);
lean_dec_ref(x_381);
lean_dec_ref(x_380);
lean_dec(x_378);
lean_dec(x_376);
lean_dec_ref(x_375);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_424 = lean_ctor_get(x_423, 0);
lean_inc(x_424);
if (lean_is_exclusive(x_423)) {
 lean_ctor_release(x_423, 0);
 x_425 = x_423;
} else {
 lean_dec_ref(x_423);
 x_425 = lean_box(0);
}
if (lean_is_scalar(x_425)) {
 x_426 = lean_alloc_ctor(1, 1, 0);
} else {
 x_426 = x_425;
}
lean_ctor_set(x_426, 0, x_424);
return x_426;
}
}
}
else
{
size_t x_427; size_t x_428; lean_object* x_429; 
x_427 = 0;
x_428 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
lean_inc_ref(x_7);
x_429 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_417, x_427, x_428, x_419, x_7);
if (lean_obj_tag(x_429) == 0)
{
lean_dec_ref(x_429);
x_36 = x_378;
x_37 = x_375;
x_38 = x_381;
x_39 = x_376;
x_40 = x_380;
x_41 = x_416;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
else
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; 
lean_dec_ref(x_416);
lean_dec_ref(x_381);
lean_dec_ref(x_380);
lean_dec(x_378);
lean_dec(x_376);
lean_dec_ref(x_375);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_430 = lean_ctor_get(x_429, 0);
lean_inc(x_430);
if (lean_is_exclusive(x_429)) {
 lean_ctor_release(x_429, 0);
 x_431 = x_429;
} else {
 lean_dec_ref(x_429);
 x_431 = lean_box(0);
}
if (lean_is_scalar(x_431)) {
 x_432 = lean_alloc_ctor(1, 1, 0);
} else {
 x_432 = x_431;
}
lean_ctor_set(x_432, 0, x_430);
return x_432;
}
}
}
}
default: 
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; 
lean_dec(x_377);
lean_dec(x_374);
x_433 = lean_ctor_get(x_208, 0);
lean_inc_ref(x_433);
lean_dec_ref(x_208);
x_434 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
lean_inc_ref(x_209);
lean_inc_ref(x_48);
lean_inc_ref(x_3);
x_435 = l_Lake_Reservoir_fetchPkgVersions(x_3, x_48, x_209, x_434);
if (lean_obj_tag(x_435) == 0)
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; 
x_436 = lean_ctor_get(x_435, 0);
lean_inc(x_436);
x_437 = lean_ctor_get(x_435, 1);
lean_inc(x_437);
lean_dec_ref(x_435);
x_438 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_438, 0, x_436);
x_181 = x_209;
x_182 = x_378;
x_183 = x_375;
x_184 = x_381;
x_185 = x_376;
x_186 = x_433;
x_187 = x_380;
x_188 = x_438;
x_189 = x_437;
x_190 = lean_box(0);
goto block_207;
}
else
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; 
x_439 = lean_ctor_get(x_435, 0);
lean_inc(x_439);
x_440 = lean_ctor_get(x_435, 1);
lean_inc(x_440);
lean_dec_ref(x_435);
x_441 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_441, 0, x_439);
x_181 = x_209;
x_182 = x_378;
x_183 = x_375;
x_184 = x_381;
x_185 = x_376;
x_186 = x_433;
x_187 = x_380;
x_188 = x_441;
x_189 = x_440;
x_190 = lean_box(0);
goto block_207;
}
}
}
}
else
{
lean_dec(x_374);
lean_dec(x_373);
lean_dec_ref(x_209);
lean_dec(x_208);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_13 = x_371;
x_14 = x_7;
x_15 = lean_box(0);
goto block_24;
}
}
else
{
lean_dec(x_372);
lean_dec_ref(x_209);
lean_dec(x_208);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_13 = x_371;
x_14 = x_7;
x_15 = lean_box(0);
goto block_24;
}
}
}
}
}
block_464:
{
lean_object* x_448; uint8_t x_449; 
x_448 = lean_array_get_size(x_446);
x_449 = lean_nat_dec_lt(x_180, x_448);
if (x_449 == 0)
{
lean_dec_ref(x_446);
x_208 = x_443;
x_209 = x_444;
x_210 = x_445;
x_211 = lean_box(0);
goto block_442;
}
else
{
lean_object* x_450; uint8_t x_451; 
x_450 = lean_box(0);
x_451 = lean_nat_dec_le(x_448, x_448);
if (x_451 == 0)
{
if (x_449 == 0)
{
lean_dec_ref(x_446);
x_208 = x_443;
x_209 = x_444;
x_210 = x_445;
x_211 = lean_box(0);
goto block_442;
}
else
{
size_t x_452; size_t x_453; lean_object* x_454; 
x_452 = 0;
x_453 = lean_usize_of_nat(x_448);
lean_inc_ref(x_7);
x_454 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_446, x_452, x_453, x_450, x_7);
lean_dec_ref(x_446);
if (lean_obj_tag(x_454) == 0)
{
lean_dec_ref(x_454);
x_208 = x_443;
x_209 = x_444;
x_210 = x_445;
x_211 = lean_box(0);
goto block_442;
}
else
{
uint8_t x_455; 
lean_dec_ref(x_445);
lean_dec_ref(x_444);
lean_dec(x_443);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_455 = !lean_is_exclusive(x_454);
if (x_455 == 0)
{
return x_454;
}
else
{
lean_object* x_456; lean_object* x_457; 
x_456 = lean_ctor_get(x_454, 0);
lean_inc(x_456);
lean_dec(x_454);
x_457 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_457, 0, x_456);
return x_457;
}
}
}
}
else
{
size_t x_458; size_t x_459; lean_object* x_460; 
x_458 = 0;
x_459 = lean_usize_of_nat(x_448);
lean_inc_ref(x_7);
x_460 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_446, x_458, x_459, x_450, x_7);
lean_dec_ref(x_446);
if (lean_obj_tag(x_460) == 0)
{
lean_dec_ref(x_460);
x_208 = x_443;
x_209 = x_444;
x_210 = x_445;
x_211 = lean_box(0);
goto block_442;
}
else
{
uint8_t x_461; 
lean_dec_ref(x_445);
lean_dec_ref(x_444);
lean_dec(x_443);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_461 = !lean_is_exclusive(x_460);
if (x_461 == 0)
{
return x_460;
}
else
{
lean_object* x_462; lean_object* x_463; 
x_462 = lean_ctor_get(x_460, 0);
lean_inc(x_462);
lean_dec(x_460);
x_463 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_463, 0, x_462);
return x_463;
}
}
}
}
}
block_477:
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; 
lean_inc(x_47);
x_468 = l_Lean_Name_toString(x_47, x_465);
x_469 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
lean_inc_ref(x_468);
lean_inc_ref(x_48);
lean_inc_ref(x_3);
x_470 = l_Lake_Reservoir_fetchPkg_x3f(x_3, x_48, x_468, x_469);
if (lean_obj_tag(x_470) == 0)
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; 
x_471 = lean_ctor_get(x_470, 0);
lean_inc(x_471);
x_472 = lean_ctor_get(x_470, 1);
lean_inc(x_472);
lean_dec_ref(x_470);
x_473 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_473, 0, x_471);
x_443 = x_466;
x_444 = x_468;
x_445 = x_473;
x_446 = x_472;
x_447 = lean_box(0);
goto block_464;
}
else
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; 
x_474 = lean_ctor_get(x_470, 0);
lean_inc(x_474);
x_475 = lean_ctor_get(x_470, 1);
lean_inc(x_475);
lean_dec_ref(x_470);
x_476 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_476, 0, x_474);
x_443 = x_466;
x_444 = x_468;
x_445 = x_476;
x_446 = x_475;
x_447 = lean_box(0);
goto block_464;
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
x_17 = l_Lake_Dependency_materialize___closed__0;
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
lean_ctor_set(x_33, 0, x_27);
x_34 = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit(x_1, x_2, x_3, x_4, x_31, x_29, x_28, x_32, x_33, x_25, x_26);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_34;
}
block_46:
{
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_44; 
x_44 = l_Lake_instInhabitedMaterializedDep_default___closed__0;
x_25 = x_36;
x_26 = x_42;
x_27 = x_41;
x_28 = x_37;
x_29 = x_38;
x_30 = lean_box(0);
x_31 = x_40;
x_32 = x_44;
goto block_35;
}
else
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_39, 0);
lean_inc(x_45);
lean_dec_ref(x_39);
x_25 = x_36;
x_26 = x_42;
x_27 = x_41;
x_28 = x_37;
x_29 = x_38;
x_30 = lean_box(0);
x_31 = x_40;
x_32 = x_45;
goto block_35;
}
}
block_68:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc_ref(x_54);
lean_dec_ref(x_53);
x_55 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0;
x_56 = lean_string_append(x_48, x_55);
x_57 = lean_string_append(x_56, x_51);
lean_dec_ref(x_51);
x_58 = l_Lake_Dependency_materialize___closed__1;
x_59 = lean_string_append(x_57, x_58);
x_60 = lean_string_append(x_59, x_54);
lean_dec_ref(x_54);
x_61 = l_Lake_Dependency_materialize___closed__2;
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
block_125:
{
if (lean_obj_tag(x_76) == 0)
{
uint8_t x_78; 
lean_dec_ref(x_75);
lean_dec_ref(x_74);
lean_dec(x_73);
lean_dec_ref(x_72);
lean_dec_ref(x_71);
lean_dec(x_69);
lean_inc_ref(x_48);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_78 = !lean_is_exclusive(x_76);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_79 = lean_ctor_get(x_76, 0);
lean_dec(x_79);
x_80 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0;
x_81 = lean_string_append(x_48, x_80);
x_82 = lean_string_append(x_81, x_70);
lean_dec_ref(x_70);
x_83 = l_Lake_Dependency_materialize___closed__3;
x_84 = lean_string_append(x_82, x_83);
x_85 = 3;
x_86 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set_uint8(x_86, sizeof(void*)*1, x_85);
x_87 = lean_apply_2(x_7, x_86, lean_box(0));
x_88 = lean_box(0);
lean_ctor_set_tag(x_76, 1);
lean_ctor_set(x_76, 0, x_88);
return x_76;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_76);
x_89 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0;
x_90 = lean_string_append(x_48, x_89);
x_91 = lean_string_append(x_90, x_70);
lean_dec_ref(x_70);
x_92 = l_Lake_Dependency_materialize___closed__3;
x_93 = lean_string_append(x_91, x_92);
x_94 = 3;
x_95 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set_uint8(x_95, sizeof(void*)*1, x_94);
x_96 = lean_apply_2(x_7, x_95, lean_box(0));
x_97 = lean_box(0);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_97);
return x_98;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; size_t x_102; size_t x_103; lean_object* x_104; lean_object* x_105; 
x_99 = lean_ctor_get(x_76, 0);
lean_inc(x_99);
lean_dec_ref(x_76);
x_100 = lean_box(0);
x_101 = l_Lake_Dependency_materialize___closed__4;
x_102 = lean_array_size(x_99);
x_103 = 0;
x_104 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(x_74, x_101, x_100, x_99, x_102, x_103, x_101);
lean_dec(x_99);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
lean_dec_ref(x_104);
if (lean_obj_tag(x_105) == 0)
{
lean_dec_ref(x_75);
lean_dec(x_73);
lean_dec_ref(x_72);
lean_dec_ref(x_71);
lean_dec(x_69);
lean_inc_ref(x_48);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_51 = x_70;
x_52 = lean_box(0);
x_53 = x_74;
goto block_68;
}
else
{
lean_object* x_106; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
lean_dec_ref(x_105);
if (lean_obj_tag(x_106) == 1)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; lean_object* x_123; lean_object* x_124; 
lean_dec_ref(x_74);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
lean_dec_ref(x_106);
x_108 = lean_ctor_get(x_107, 0);
lean_inc_ref(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc_ref(x_109);
lean_dec(x_107);
x_110 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0;
lean_inc_ref(x_48);
x_111 = lean_string_append(x_48, x_110);
x_112 = lean_string_append(x_111, x_70);
lean_dec_ref(x_70);
x_113 = l_Lake_Dependency_materialize___closed__5;
x_114 = lean_string_append(x_112, x_113);
x_115 = l_Lake_StdVer_toString(x_108);
x_116 = lean_string_append(x_114, x_115);
lean_dec_ref(x_115);
x_117 = l_Lake_Dependency_materialize___closed__6;
x_118 = lean_string_append(x_116, x_117);
x_119 = lean_string_append(x_118, x_109);
x_120 = l_Lake_Dependency_materialize___closed__7;
x_121 = lean_string_append(x_119, x_120);
x_122 = 1;
x_123 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set_uint8(x_123, sizeof(void*)*1, x_122);
lean_inc_ref(x_7);
x_124 = lean_apply_2(x_7, x_123, lean_box(0));
x_36 = x_69;
x_37 = x_71;
x_38 = x_72;
x_39 = x_73;
x_40 = x_75;
x_41 = x_109;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
else
{
lean_dec(x_106);
lean_dec_ref(x_75);
lean_dec(x_73);
lean_dec_ref(x_72);
lean_dec_ref(x_71);
lean_dec(x_69);
lean_inc_ref(x_48);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_51 = x_70;
x_52 = lean_box(0);
x_53 = x_74;
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
static lean_object* _init_l_Lake_PackageEntry_materialize___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HEAD", 4, 4);
return x_1;
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
uint8_t x_14; 
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = l_Lake_instInhabitedMaterializedDep_default___closed__0;
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_17, 2, x_1);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
lean_dec(x_13);
x_19 = l_Lake_instInhabitedMaterializedDep_default___closed__0;
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_1);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_48; lean_object* x_49; uint8_t x_56; lean_object* x_57; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; uint8_t x_88; lean_object* x_89; lean_object* x_90; uint8_t x_101; lean_object* x_102; lean_object* x_125; uint8_t x_126; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_23);
x_24 = lean_ctor_get(x_13, 1);
lean_inc_ref(x_24);
x_25 = lean_ctor_get(x_13, 3);
lean_inc(x_25);
lean_dec_ref(x_13);
x_32 = 0;
lean_inc(x_22);
x_33 = l_Lean_Name_toString(x_22, x_32);
lean_inc_ref(x_33);
x_34 = l_Lake_joinRelative(x_4, x_33);
lean_inc_ref(x_34);
x_39 = l_Lake_joinRelative(x_3, x_34);
x_101 = l_System_FilePath_isDir(x_39);
x_125 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
x_126 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5;
if (x_126 == 0)
{
x_102 = lean_box(0);
goto block_124;
}
else
{
lean_object* x_127; uint8_t x_128; 
x_127 = lean_box(0);
x_128 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6;
if (x_128 == 0)
{
if (x_126 == 0)
{
x_102 = lean_box(0);
goto block_124;
}
else
{
size_t x_129; size_t x_130; lean_object* x_131; 
x_129 = 0;
x_130 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
lean_inc_ref(x_5);
x_131 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_125, x_129, x_130, x_127, x_5);
if (lean_obj_tag(x_131) == 0)
{
lean_dec_ref(x_131);
x_102 = lean_box(0);
goto block_124;
}
else
{
uint8_t x_132; 
lean_dec_ref(x_39);
lean_dec_ref(x_34);
lean_dec_ref(x_33);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_132 = !lean_is_exclusive(x_131);
if (x_132 == 0)
{
return x_131;
}
else
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_ctor_get(x_131, 0);
lean_inc(x_133);
lean_dec(x_131);
x_134 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_134, 0, x_133);
return x_134;
}
}
}
}
else
{
size_t x_135; size_t x_136; lean_object* x_137; 
x_135 = 0;
x_136 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
lean_inc_ref(x_5);
x_137 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_125, x_135, x_136, x_127, x_5);
if (lean_obj_tag(x_137) == 0)
{
lean_dec_ref(x_137);
x_102 = lean_box(0);
goto block_124;
}
else
{
uint8_t x_138; 
lean_dec_ref(x_39);
lean_dec_ref(x_34);
lean_dec_ref(x_33);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_138 = !lean_is_exclusive(x_137);
if (x_138 == 0)
{
return x_137;
}
else
{
lean_object* x_139; lean_object* x_140; 
x_139 = lean_ctor_get(x_137, 0);
lean_inc(x_139);
lean_dec(x_137);
x_140 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_140, 0, x_139);
return x_140;
}
}
}
}
block_31:
{
lean_object* x_28; 
x_28 = l_Lake_Git_filterUrl_x3f(x_23);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
x_29 = l_Lake_instInhabitedMaterializedDep_default___closed__0;
x_7 = lean_box(0);
x_8 = x_27;
x_9 = x_29;
goto block_12;
}
else
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
lean_dec_ref(x_28);
x_7 = lean_box(0);
x_8 = x_27;
x_9 = x_30;
goto block_12;
}
}
block_38:
{
if (lean_obj_tag(x_25) == 0)
{
x_26 = lean_box(0);
x_27 = x_34;
goto block_31;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_25, 0);
lean_inc(x_36);
lean_dec_ref(x_25);
x_37 = l_Lake_joinRelative(x_34, x_36);
x_26 = lean_box(0);
x_27 = x_37;
goto block_31;
}
}
block_47:
{
lean_object* x_43; 
x_43 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(x_5, x_33, x_39, x_42, x_41);
if (lean_obj_tag(x_43) == 0)
{
lean_dec_ref(x_43);
x_35 = lean_box(0);
goto block_38;
}
else
{
uint8_t x_44; 
lean_dec_ref(x_34);
lean_dec(x_25);
lean_dec_ref(x_23);
lean_dec_ref(x_1);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
return x_43;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
}
block_55:
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_24);
x_51 = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(x_5, x_33, x_39, x_49, x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_dec_ref(x_51);
x_35 = lean_box(0);
goto block_38;
}
else
{
uint8_t x_52; 
lean_dec_ref(x_34);
lean_dec(x_25);
lean_dec_ref(x_23);
lean_dec_ref(x_1);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
return x_51;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
return x_54;
}
}
}
block_66:
{
if (x_56 == 0)
{
lean_dec_ref(x_39);
lean_dec_ref(x_33);
lean_dec_ref(x_5);
x_35 = lean_box(0);
goto block_38;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; 
x_58 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0;
x_59 = lean_string_append(x_33, x_58);
x_60 = lean_string_append(x_59, x_39);
lean_dec_ref(x_39);
x_61 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1;
x_62 = lean_string_append(x_60, x_61);
x_63 = 2;
x_64 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set_uint8(x_64, sizeof(void*)*1, x_63);
x_65 = lean_apply_2(x_5, x_64, lean_box(0));
x_35 = lean_box(0);
goto block_38;
}
}
block_87:
{
lean_object* x_71; uint8_t x_72; 
x_71 = lean_array_get_size(x_67);
x_72 = lean_nat_dec_lt(x_68, x_71);
if (x_72 == 0)
{
lean_dec_ref(x_67);
x_56 = x_69;
x_57 = lean_box(0);
goto block_66;
}
else
{
lean_object* x_73; uint8_t x_74; 
x_73 = lean_box(0);
x_74 = lean_nat_dec_le(x_71, x_71);
if (x_74 == 0)
{
if (x_72 == 0)
{
lean_dec_ref(x_67);
x_56 = x_69;
x_57 = lean_box(0);
goto block_66;
}
else
{
size_t x_75; size_t x_76; lean_object* x_77; 
x_75 = 0;
x_76 = lean_usize_of_nat(x_71);
lean_inc_ref(x_5);
x_77 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_67, x_75, x_76, x_73, x_5);
lean_dec_ref(x_67);
if (lean_obj_tag(x_77) == 0)
{
lean_dec_ref(x_77);
x_56 = x_69;
x_57 = lean_box(0);
goto block_66;
}
else
{
uint8_t x_78; 
lean_dec_ref(x_39);
lean_dec_ref(x_34);
lean_dec_ref(x_33);
lean_dec(x_25);
lean_dec_ref(x_23);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
return x_77;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_77, 0);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
return x_80;
}
}
}
}
else
{
size_t x_81; size_t x_82; lean_object* x_83; 
x_81 = 0;
x_82 = lean_usize_of_nat(x_71);
lean_inc_ref(x_5);
x_83 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_67, x_81, x_82, x_73, x_5);
lean_dec_ref(x_67);
if (lean_obj_tag(x_83) == 0)
{
lean_dec_ref(x_83);
x_56 = x_69;
x_57 = lean_box(0);
goto block_66;
}
else
{
uint8_t x_84; 
lean_dec_ref(x_39);
lean_dec_ref(x_34);
lean_dec_ref(x_33);
lean_dec(x_25);
lean_dec_ref(x_23);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_84 = !lean_is_exclusive(x_83);
if (x_84 == 0)
{
return x_83;
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_83, 0);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_85);
return x_86;
}
}
}
}
}
block_100:
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_91 = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_24);
lean_inc_ref(x_92);
x_93 = l_Option_instDecidableEq___redArg(x_91, x_89, x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_2, 5);
x_95 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_94, x_22);
if (lean_obj_tag(x_95) == 0)
{
lean_inc_ref(x_23);
x_40 = lean_box(0);
x_41 = x_92;
x_42 = x_23;
goto block_47;
}
else
{
lean_object* x_96; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
lean_dec_ref(x_95);
x_40 = lean_box(0);
x_41 = x_92;
x_42 = x_96;
goto block_47;
}
}
else
{
uint8_t x_97; lean_object* x_98; lean_object* x_99; 
lean_dec_ref(x_92);
lean_inc_ref(x_39);
x_97 = l_Lake_GitRepo_hasNoDiff(x_39);
x_98 = lean_unsigned_to_nat(0u);
x_99 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
if (x_97 == 0)
{
x_67 = x_99;
x_68 = x_98;
x_69 = x_88;
x_70 = lean_box(0);
goto block_87;
}
else
{
x_67 = x_99;
x_68 = x_98;
x_69 = x_32;
x_70 = lean_box(0);
goto block_87;
}
}
}
block_124:
{
if (x_101 == 0)
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_2, 5);
x_104 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_103, x_22);
if (lean_obj_tag(x_104) == 0)
{
lean_inc_ref(x_23);
x_48 = lean_box(0);
x_49 = x_23;
goto block_55;
}
else
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
lean_dec_ref(x_104);
x_48 = lean_box(0);
x_49 = x_105;
goto block_55;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_106 = l_Lake_PackageEntry_materialize___closed__0;
lean_inc_ref(x_39);
x_107 = l_Lake_GitRepo_resolveRevision_x3f(x_106, x_39);
x_108 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
x_109 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5;
if (x_109 == 0)
{
x_88 = x_101;
x_89 = x_107;
x_90 = lean_box(0);
goto block_100;
}
else
{
lean_object* x_110; uint8_t x_111; 
x_110 = lean_box(0);
x_111 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6;
if (x_111 == 0)
{
if (x_109 == 0)
{
x_88 = x_101;
x_89 = x_107;
x_90 = lean_box(0);
goto block_100;
}
else
{
size_t x_112; size_t x_113; lean_object* x_114; 
x_112 = 0;
x_113 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
lean_inc_ref(x_5);
x_114 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_108, x_112, x_113, x_110, x_5);
if (lean_obj_tag(x_114) == 0)
{
lean_dec_ref(x_114);
x_88 = x_101;
x_89 = x_107;
x_90 = lean_box(0);
goto block_100;
}
else
{
uint8_t x_115; 
lean_dec(x_107);
lean_dec_ref(x_39);
lean_dec_ref(x_34);
lean_dec_ref(x_33);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_115 = !lean_is_exclusive(x_114);
if (x_115 == 0)
{
return x_114;
}
else
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_114, 0);
lean_inc(x_116);
lean_dec(x_114);
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_116);
return x_117;
}
}
}
}
else
{
size_t x_118; size_t x_119; lean_object* x_120; 
x_118 = 0;
x_119 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
lean_inc_ref(x_5);
x_120 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_108, x_118, x_119, x_110, x_5);
if (lean_obj_tag(x_120) == 0)
{
lean_dec_ref(x_120);
x_88 = x_101;
x_89 = x_107;
x_90 = lean_box(0);
goto block_100;
}
else
{
uint8_t x_121; 
lean_dec(x_107);
lean_dec_ref(x_39);
lean_dec_ref(x_34);
lean_dec_ref(x_33);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_121 = !lean_is_exclusive(x_120);
if (x_121 == 0)
{
return x_120;
}
else
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_120, 0);
lean_inc(x_122);
lean_dec(x_120);
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_122);
return x_123;
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
lean_ctor_set(x_10, 0, x_8);
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
lean_object* initialize_Lake_Config_Env(uint8_t builtin);
lean_object* initialize_Lake_Load_Manifest(uint8_t builtin);
lean_object* initialize_Lake_Config_Package(uint8_t builtin);
lean_object* initialize_Lake_Util_Git(uint8_t builtin);
lean_object* initialize_Lake_Config_Dependency(uint8_t builtin);
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
res = initialize_Lake_Config_Dependency(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Reservoir(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0 = _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0();
lean_mark_persistent(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0);
l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1 = _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1();
lean_mark_persistent(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1);
l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2 = _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2();
lean_mark_persistent(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2);
l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3 = _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3();
lean_mark_persistent(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3);
l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4 = _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4();
lean_mark_persistent(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4);
l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___closed__0 = _init_l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___closed__0();
lean_mark_persistent(l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___closed__0);
l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__0 = _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__0();
lean_mark_persistent(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__0);
l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__1 = _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__1();
lean_mark_persistent(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__1);
l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__2 = _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__2();
lean_mark_persistent(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__2);
l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__3 = _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__3();
lean_mark_persistent(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__3);
l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4 = _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4();
lean_mark_persistent(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4);
l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5 = _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5();
l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6 = _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6();
l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7 = _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7();
l_Lake_instInhabitedMaterializedDep_default___closed__0 = _init_l_Lake_instInhabitedMaterializedDep_default___closed__0();
lean_mark_persistent(l_Lake_instInhabitedMaterializedDep_default___closed__0);
l_Lake_instInhabitedMaterializedDep_default___closed__1 = _init_l_Lake_instInhabitedMaterializedDep_default___closed__1();
lean_mark_persistent(l_Lake_instInhabitedMaterializedDep_default___closed__1);
l_Lake_instInhabitedMaterializedDep_default = _init_l_Lake_instInhabitedMaterializedDep_default();
lean_mark_persistent(l_Lake_instInhabitedMaterializedDep_default);
l_Lake_instInhabitedMaterializedDep = _init_l_Lake_instInhabitedMaterializedDep();
lean_mark_persistent(l_Lake_instInhabitedMaterializedDep);
l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0 = _init_l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0();
lean_mark_persistent(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0);
l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__1 = _init_l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__1();
lean_mark_persistent(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__1);
l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__2 = _init_l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__2();
lean_mark_persistent(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__2);
l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__3 = _init_l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__3();
lean_mark_persistent(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__3);
l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__4 = _init_l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__4();
lean_mark_persistent(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__4);
l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__5 = _init_l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__5();
lean_mark_persistent(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__5);
l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__6 = _init_l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__6();
lean_mark_persistent(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__6);
l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__7 = _init_l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__7();
lean_mark_persistent(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__7);
l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__0 = _init_l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__0();
lean_mark_persistent(l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__0);
l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__1 = _init_l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__1();
lean_mark_persistent(l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__1);
l_Lake_Dependency_materialize___closed__0 = _init_l_Lake_Dependency_materialize___closed__0();
lean_mark_persistent(l_Lake_Dependency_materialize___closed__0);
l_Lake_Dependency_materialize___closed__1 = _init_l_Lake_Dependency_materialize___closed__1();
lean_mark_persistent(l_Lake_Dependency_materialize___closed__1);
l_Lake_Dependency_materialize___closed__2 = _init_l_Lake_Dependency_materialize___closed__2();
lean_mark_persistent(l_Lake_Dependency_materialize___closed__2);
l_Lake_Dependency_materialize___closed__3 = _init_l_Lake_Dependency_materialize___closed__3();
lean_mark_persistent(l_Lake_Dependency_materialize___closed__3);
l_Lake_Dependency_materialize___closed__4 = _init_l_Lake_Dependency_materialize___closed__4();
lean_mark_persistent(l_Lake_Dependency_materialize___closed__4);
l_Lake_Dependency_materialize___closed__5 = _init_l_Lake_Dependency_materialize___closed__5();
lean_mark_persistent(l_Lake_Dependency_materialize___closed__5);
l_Lake_Dependency_materialize___closed__6 = _init_l_Lake_Dependency_materialize___closed__6();
lean_mark_persistent(l_Lake_Dependency_materialize___closed__6);
l_Lake_Dependency_materialize___closed__7 = _init_l_Lake_Dependency_materialize___closed__7();
lean_mark_persistent(l_Lake_Dependency_materialize___closed__7);
l_Lake_Dependency_materialize___closed__8 = _init_l_Lake_Dependency_materialize___closed__8();
lean_mark_persistent(l_Lake_Dependency_materialize___closed__8);
l_Lake_Dependency_materialize___closed__9 = _init_l_Lake_Dependency_materialize___closed__9();
lean_mark_persistent(l_Lake_Dependency_materialize___closed__9);
l_Lake_Dependency_materialize___closed__10 = _init_l_Lake_Dependency_materialize___closed__10();
lean_mark_persistent(l_Lake_Dependency_materialize___closed__10);
l_Lake_Dependency_materialize___closed__11 = _init_l_Lake_Dependency_materialize___closed__11();
lean_mark_persistent(l_Lake_Dependency_materialize___closed__11);
l_Lake_PackageEntry_materialize___closed__0 = _init_l_Lake_PackageEntry_materialize___closed__0();
lean_mark_persistent(l_Lake_PackageEntry_materialize___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

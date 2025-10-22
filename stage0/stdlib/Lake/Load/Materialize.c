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
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_configFile(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorIdx___boxed(lean_object*);
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__1;
extern lean_object* l_System_instInhabitedFilePath_default;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_none_elim___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
static lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__3;
static lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__5;
lean_object* l_Lake_Reservoir_fetchPkgVersions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__1;
static lean_object* l_Lake_Dependency_materialize___closed__3;
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___Lake_Dependency_materialize_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__3;
lean_object* l_String_quote(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__2;
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Dependency_materialize___closed__6;
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_name(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint8_t l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6;
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at_____private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at_____private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Dependency_materialize___closed__5;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedMaterializedDep_default;
lean_object* lean_string_utf8_byte_size(lean_object*);
extern lean_object* l_Lake_instInhabitedPackageEntry_default;
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_String_dropPrefix_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_ctorIdx___boxed(lean_object*);
lean_object* l_Lake_GitRepo_resolveRemoteRevision(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lake_Dependency_materialize___closed__8;
static lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Dependency_materialize___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lake_Dependency_materialize_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_isDir(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_git_elim(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_StdVer_toString(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__6;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lake_Dependency_materialize_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_configFile___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at_____private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_name___boxed(lean_object*);
static lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0;
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_none_elim(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_removeDirAll(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_manifestFile_x3f___boxed(lean_object*);
lean_object* l_Lake_Git_filterUrl_x3f(lean_object*);
lean_object* l_Lake_GitRepo_clone(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_resolveRevision_x3f(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Dependency_materialize___closed__9;
static lean_object* l_Lake_Dependency_materialize___closed__11;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_std_elim___redArg(lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_findRemoteRevision(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_hasNoDiff(lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_getHeadRevision(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_manifestFile_x3f(lean_object*);
extern lean_object* l_Std_Format_defWidth;
extern lean_object* l_Lake_Git_defaultRemote;
static lean_object* l_Lake_instInhabitedMaterializedDep_default___closed__1;
lean_object* l_Lake_Reservoir_fetchPkg_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Dependency_materialize___closed__10;
lean_object* l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(lean_object*, uint8_t);
static lean_object* l_Lake_instInhabitedMaterializedDep_default___closed__2;
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___Lake_Dependency_materialize_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__5;
static lean_object* l_Lake_PackageEntry_materialize___closed__0;
lean_object* l_Lake_GitRepo_checkoutDetach(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1;
static lean_object* l_Lake_Dependency_materialize___closed__7;
static lean_object* l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___closed__0;
static lean_object* l_Lake_Dependency_materialize___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_git_elim___redArg(lean_object*, lean_object*);
lean_object* l_Lake_StdVer_parse(lean_object*);
static lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__7;
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lake_instInhabitedMaterializedDep_default___closed__0;
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_scope(lean_object*);
static lean_object* l_Lake_Dependency_materialize___closed__4;
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_RegistryPkg_gitSrc_x3f(lean_object*);
static lean_object* l_Lake_Dependency_materialize___closed__2;
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_scope___boxed(lean_object*);
lean_object* lean_io_realpath(lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3;
uint8_t l_Lake_instDecidableEqStdVer_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_std_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__2;
static lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__4;
static lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0;
static uint8_t l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__0;
static uint8_t l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
extern lean_object* l_Lake_defaultConfigFile;
static size_t l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__8;
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at_____private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_getRemoteUrl_x3f(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t l_Option_instDecidableEq_decEq___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__9;
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4;
static lean_object* l_Lake_instInhabitedMaterializedDep_default___closed__3;
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorIdx(lean_object*);
static lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__8;
extern uint8_t l_System_Platform_isWindows;
LEAN_EXPORT lean_object* l_Lake_instInhabitedMaterializedDep;
static lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0;
lean_object* l_instDecidableEqString___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_apply_2(x_2, x_1, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_apply_2(x_1, x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0_spec__0___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_8 = lean_array_uget(x_1, x_2);
lean_inc_ref(x_5);
x_9 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0_spec__0___redArg(x_5, x_8, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_2 = x_13;
x_4 = x_10;
x_6 = x_11;
goto _start;
}
else
{
lean_object* x_15; 
lean_dec_ref(x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_6);
return x_15;
}
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
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Git_defaultRemote;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_36; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_118; lean_object* x_122; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_126 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__5;
x_127 = lean_unsigned_to_nat(0u);
x_128 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
lean_inc_ref(x_2);
x_129 = l_Lake_GitRepo_findRemoteRevision(x_2, x_3, x_126, x_128, x_5);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_173; uint8_t x_174; 
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec_ref(x_129);
x_132 = lean_ctor_get(x_130, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_130, 1);
lean_inc(x_133);
lean_dec_ref(x_130);
x_173 = lean_array_get_size(x_133);
x_174 = lean_nat_dec_lt(x_127, x_173);
if (x_174 == 0)
{
lean_dec(x_173);
lean_dec(x_133);
x_134 = x_131;
goto block_172;
}
else
{
uint8_t x_175; 
x_175 = lean_nat_dec_le(x_173, x_173);
if (x_175 == 0)
{
lean_dec(x_173);
lean_dec(x_133);
x_134 = x_131;
goto block_172;
}
else
{
lean_object* x_176; size_t x_177; size_t x_178; lean_object* x_179; lean_object* x_180; 
x_176 = lean_box(0);
x_177 = 0;
x_178 = lean_usize_of_nat(x_173);
lean_dec(x_173);
lean_inc_ref(x_4);
x_179 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_133, x_177, x_178, x_176, x_4, x_131);
lean_dec(x_133);
x_180 = lean_ctor_get(x_179, 1);
lean_inc(x_180);
lean_dec_ref(x_179);
x_134 = x_180;
goto block_172;
}
}
block_172:
{
lean_object* x_135; lean_object* x_136; 
lean_inc_ref(x_2);
x_135 = l_Lake_GitRepo_getHeadRevision(x_2, x_128, x_134);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; 
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec_ref(x_135);
x_138 = lean_ctor_get(x_136, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_136, 1);
lean_inc(x_139);
lean_dec_ref(x_136);
x_140 = lean_array_get_size(x_139);
x_141 = lean_nat_dec_lt(x_127, x_140);
if (x_141 == 0)
{
lean_dec(x_140);
lean_dec(x_139);
x_40 = x_132;
x_41 = x_138;
x_42 = x_137;
goto block_117;
}
else
{
uint8_t x_142; 
x_142 = lean_nat_dec_le(x_140, x_140);
if (x_142 == 0)
{
lean_dec(x_140);
lean_dec(x_139);
x_40 = x_132;
x_41 = x_138;
x_42 = x_137;
goto block_117;
}
else
{
lean_object* x_143; size_t x_144; size_t x_145; lean_object* x_146; lean_object* x_147; 
x_143 = lean_box(0);
x_144 = 0;
x_145 = lean_usize_of_nat(x_140);
lean_dec(x_140);
lean_inc_ref(x_4);
x_146 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_139, x_144, x_145, x_143, x_4, x_137);
lean_dec(x_139);
x_147 = lean_ctor_get(x_146, 1);
lean_inc(x_147);
lean_dec_ref(x_146);
x_40 = x_132;
x_41 = x_138;
x_42 = x_147;
goto block_117;
}
}
}
else
{
lean_object* x_148; uint8_t x_149; 
lean_dec(x_132);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_148 = lean_ctor_get(x_135, 1);
lean_inc(x_148);
lean_dec_ref(x_135);
x_149 = !lean_is_exclusive(x_136);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; 
x_150 = lean_ctor_get(x_136, 1);
x_151 = lean_ctor_get(x_136, 0);
lean_dec(x_151);
x_152 = lean_array_get_size(x_150);
x_153 = lean_nat_dec_lt(x_127, x_152);
if (x_153 == 0)
{
lean_object* x_154; 
lean_dec(x_152);
lean_dec(x_150);
lean_dec_ref(x_4);
x_154 = lean_box(0);
lean_ctor_set(x_136, 1, x_148);
lean_ctor_set(x_136, 0, x_154);
return x_136;
}
else
{
uint8_t x_155; 
lean_free_object(x_136);
x_155 = lean_nat_dec_le(x_152, x_152);
if (x_155 == 0)
{
lean_dec(x_152);
lean_dec(x_150);
lean_dec_ref(x_4);
x_118 = x_148;
goto block_121;
}
else
{
lean_object* x_156; size_t x_157; size_t x_158; lean_object* x_159; lean_object* x_160; 
x_156 = lean_box(0);
x_157 = 0;
x_158 = lean_usize_of_nat(x_152);
lean_dec(x_152);
x_159 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_150, x_157, x_158, x_156, x_4, x_148);
lean_dec(x_150);
x_160 = lean_ctor_get(x_159, 1);
lean_inc(x_160);
lean_dec_ref(x_159);
x_118 = x_160;
goto block_121;
}
}
}
else
{
lean_object* x_161; lean_object* x_162; uint8_t x_163; 
x_161 = lean_ctor_get(x_136, 1);
lean_inc(x_161);
lean_dec(x_136);
x_162 = lean_array_get_size(x_161);
x_163 = lean_nat_dec_lt(x_127, x_162);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; 
lean_dec(x_162);
lean_dec(x_161);
lean_dec_ref(x_4);
x_164 = lean_box(0);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_148);
return x_165;
}
else
{
uint8_t x_166; 
x_166 = lean_nat_dec_le(x_162, x_162);
if (x_166 == 0)
{
lean_dec(x_162);
lean_dec(x_161);
lean_dec_ref(x_4);
x_118 = x_148;
goto block_121;
}
else
{
lean_object* x_167; size_t x_168; size_t x_169; lean_object* x_170; lean_object* x_171; 
x_167 = lean_box(0);
x_168 = 0;
x_169 = lean_usize_of_nat(x_162);
lean_dec(x_162);
x_170 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_161, x_168, x_169, x_167, x_4, x_148);
lean_dec(x_161);
x_171 = lean_ctor_get(x_170, 1);
lean_inc(x_171);
lean_dec_ref(x_170);
x_118 = x_171;
goto block_121;
}
}
}
}
}
}
else
{
lean_object* x_181; uint8_t x_182; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_181 = lean_ctor_get(x_129, 1);
lean_inc(x_181);
lean_dec_ref(x_129);
x_182 = !lean_is_exclusive(x_130);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; 
x_183 = lean_ctor_get(x_130, 1);
x_184 = lean_ctor_get(x_130, 0);
lean_dec(x_184);
x_185 = lean_array_get_size(x_183);
x_186 = lean_nat_dec_lt(x_127, x_185);
if (x_186 == 0)
{
lean_object* x_187; 
lean_dec(x_185);
lean_dec(x_183);
lean_dec_ref(x_4);
x_187 = lean_box(0);
lean_ctor_set(x_130, 1, x_181);
lean_ctor_set(x_130, 0, x_187);
return x_130;
}
else
{
uint8_t x_188; 
lean_free_object(x_130);
x_188 = lean_nat_dec_le(x_185, x_185);
if (x_188 == 0)
{
lean_dec(x_185);
lean_dec(x_183);
lean_dec_ref(x_4);
x_122 = x_181;
goto block_125;
}
else
{
lean_object* x_189; size_t x_190; size_t x_191; lean_object* x_192; lean_object* x_193; 
x_189 = lean_box(0);
x_190 = 0;
x_191 = lean_usize_of_nat(x_185);
lean_dec(x_185);
x_192 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_183, x_190, x_191, x_189, x_4, x_181);
lean_dec(x_183);
x_193 = lean_ctor_get(x_192, 1);
lean_inc(x_193);
lean_dec_ref(x_192);
x_122 = x_193;
goto block_125;
}
}
}
else
{
lean_object* x_194; lean_object* x_195; uint8_t x_196; 
x_194 = lean_ctor_get(x_130, 1);
lean_inc(x_194);
lean_dec(x_130);
x_195 = lean_array_get_size(x_194);
x_196 = lean_nat_dec_lt(x_127, x_195);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; 
lean_dec(x_195);
lean_dec(x_194);
lean_dec_ref(x_4);
x_197 = lean_box(0);
x_198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_181);
return x_198;
}
else
{
uint8_t x_199; 
x_199 = lean_nat_dec_le(x_195, x_195);
if (x_199 == 0)
{
lean_dec(x_195);
lean_dec(x_194);
lean_dec_ref(x_4);
x_122 = x_181;
goto block_125;
}
else
{
lean_object* x_200; size_t x_201; size_t x_202; lean_object* x_203; lean_object* x_204; 
x_200 = lean_box(0);
x_201 = 0;
x_202 = lean_usize_of_nat(x_195);
lean_dec(x_195);
x_203 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_194, x_201, x_202, x_200, x_4, x_181);
lean_dec(x_194);
x_204 = lean_ctor_get(x_203, 1);
lean_inc(x_204);
lean_dec_ref(x_203);
x_122 = x_204;
goto block_125;
}
}
}
}
block_22:
{
if (x_6 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
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
x_17 = lean_apply_2(x_4, x_16, x_7);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
block_35:
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_array_get_size(x_23);
x_28 = lean_nat_dec_lt(x_24, x_27);
if (x_28 == 0)
{
lean_dec(x_27);
lean_dec_ref(x_23);
x_6 = x_25;
x_7 = x_26;
goto block_22;
}
else
{
uint8_t x_29; 
x_29 = lean_nat_dec_le(x_27, x_27);
if (x_29 == 0)
{
lean_dec(x_27);
lean_dec_ref(x_23);
x_6 = x_25;
x_7 = x_26;
goto block_22;
}
else
{
lean_object* x_30; size_t x_31; size_t x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_box(0);
x_31 = 0;
x_32 = lean_usize_of_nat(x_27);
lean_dec(x_27);
lean_inc_ref(x_4);
x_33 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_23, x_31, x_32, x_30, x_4, x_26);
lean_dec_ref(x_23);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec_ref(x_33);
x_6 = x_25;
x_7 = x_34;
goto block_22;
}
}
}
block_39:
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
block_117:
{
uint8_t x_43; 
x_43 = lean_string_dec_eq(x_41, x_40);
lean_dec_ref(x_41);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_44 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
x_45 = lean_string_append(x_1, x_44);
x_46 = lean_string_append(x_45, x_40);
x_47 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3;
x_48 = lean_string_append(x_46, x_47);
x_49 = 1;
x_50 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set_uint8(x_50, sizeof(void*)*1, x_49);
lean_inc_ref(x_4);
x_51 = lean_apply_2(x_4, x_50, x_42);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec_ref(x_51);
x_53 = lean_unsigned_to_nat(0u);
x_54 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
x_55 = l_Lake_GitRepo_checkoutDetach(x_40, x_2, x_54, x_52);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec_ref(x_55);
x_58 = !lean_is_exclusive(x_56);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_59 = lean_ctor_get(x_56, 0);
x_60 = lean_ctor_get(x_56, 1);
x_61 = lean_array_get_size(x_60);
x_62 = lean_nat_dec_lt(x_53, x_61);
if (x_62 == 0)
{
lean_dec(x_61);
lean_dec(x_60);
lean_dec_ref(x_4);
lean_ctor_set(x_56, 1, x_57);
return x_56;
}
else
{
uint8_t x_63; 
x_63 = lean_nat_dec_le(x_61, x_61);
if (x_63 == 0)
{
lean_dec(x_61);
lean_dec(x_60);
lean_dec_ref(x_4);
lean_ctor_set(x_56, 1, x_57);
return x_56;
}
else
{
lean_object* x_64; size_t x_65; size_t x_66; lean_object* x_67; uint8_t x_68; 
lean_free_object(x_56);
x_64 = lean_box(0);
x_65 = 0;
x_66 = lean_usize_of_nat(x_61);
lean_dec(x_61);
x_67 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_60, x_65, x_66, x_64, x_4, x_57);
lean_dec(x_60);
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_67, 0);
lean_dec(x_69);
lean_ctor_set(x_67, 0, x_59);
return x_67;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
lean_dec(x_67);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_59);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_72 = lean_ctor_get(x_56, 0);
x_73 = lean_ctor_get(x_56, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_56);
x_74 = lean_array_get_size(x_73);
x_75 = lean_nat_dec_lt(x_53, x_74);
if (x_75 == 0)
{
lean_object* x_76; 
lean_dec(x_74);
lean_dec(x_73);
lean_dec_ref(x_4);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_72);
lean_ctor_set(x_76, 1, x_57);
return x_76;
}
else
{
uint8_t x_77; 
x_77 = lean_nat_dec_le(x_74, x_74);
if (x_77 == 0)
{
lean_object* x_78; 
lean_dec(x_74);
lean_dec(x_73);
lean_dec_ref(x_4);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_72);
lean_ctor_set(x_78, 1, x_57);
return x_78;
}
else
{
lean_object* x_79; size_t x_80; size_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_79 = lean_box(0);
x_80 = 0;
x_81 = lean_usize_of_nat(x_74);
lean_dec(x_74);
x_82 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_73, x_80, x_81, x_79, x_4, x_57);
lean_dec(x_73);
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_84 = x_82;
} else {
 lean_dec_ref(x_82);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_72);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
}
}
}
else
{
lean_object* x_86; uint8_t x_87; 
x_86 = lean_ctor_get(x_55, 1);
lean_inc(x_86);
lean_dec_ref(x_55);
x_87 = !lean_is_exclusive(x_56);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_88 = lean_ctor_get(x_56, 1);
x_89 = lean_ctor_get(x_56, 0);
lean_dec(x_89);
x_90 = lean_array_get_size(x_88);
x_91 = lean_nat_dec_lt(x_53, x_90);
if (x_91 == 0)
{
lean_object* x_92; 
lean_dec(x_90);
lean_dec(x_88);
lean_dec_ref(x_4);
x_92 = lean_box(0);
lean_ctor_set(x_56, 1, x_86);
lean_ctor_set(x_56, 0, x_92);
return x_56;
}
else
{
uint8_t x_93; 
lean_free_object(x_56);
x_93 = lean_nat_dec_le(x_90, x_90);
if (x_93 == 0)
{
lean_dec(x_90);
lean_dec(x_88);
lean_dec_ref(x_4);
x_36 = x_86;
goto block_39;
}
else
{
lean_object* x_94; size_t x_95; size_t x_96; lean_object* x_97; lean_object* x_98; 
x_94 = lean_box(0);
x_95 = 0;
x_96 = lean_usize_of_nat(x_90);
lean_dec(x_90);
x_97 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_88, x_95, x_96, x_94, x_4, x_86);
lean_dec(x_88);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec_ref(x_97);
x_36 = x_98;
goto block_39;
}
}
}
else
{
lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_99 = lean_ctor_get(x_56, 1);
lean_inc(x_99);
lean_dec(x_56);
x_100 = lean_array_get_size(x_99);
x_101 = lean_nat_dec_lt(x_53, x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_100);
lean_dec(x_99);
lean_dec_ref(x_4);
x_102 = lean_box(0);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_86);
return x_103;
}
else
{
uint8_t x_104; 
x_104 = lean_nat_dec_le(x_100, x_100);
if (x_104 == 0)
{
lean_dec(x_100);
lean_dec(x_99);
lean_dec_ref(x_4);
x_36 = x_86;
goto block_39;
}
else
{
lean_object* x_105; size_t x_106; size_t x_107; lean_object* x_108; lean_object* x_109; 
x_105 = lean_box(0);
x_106 = 0;
x_107 = lean_usize_of_nat(x_100);
lean_dec(x_100);
x_108 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_99, x_106, x_107, x_105, x_4, x_86);
lean_dec(x_99);
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
lean_dec_ref(x_108);
x_36 = x_109;
goto block_39;
}
}
}
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
lean_dec_ref(x_40);
lean_inc_ref(x_2);
x_110 = l_Lake_GitRepo_hasNoDiff(x_2, x_42);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec_ref(x_110);
x_113 = lean_unsigned_to_nat(0u);
x_114 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
x_115 = lean_unbox(x_111);
lean_dec(x_111);
if (x_115 == 0)
{
x_23 = x_114;
x_24 = x_113;
x_25 = x_43;
x_26 = x_112;
goto block_35;
}
else
{
uint8_t x_116; 
x_116 = 0;
x_23 = x_114;
x_24 = x_113;
x_25 = x_116;
x_26 = x_112;
goto block_35;
}
}
}
block_121:
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_box(0);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_118);
return x_120;
}
block_125:
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_box(0);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_122);
return x_124;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec_ref(x_1);
return x_9;
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
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_11; lean_object* x_12; lean_object* x_80; lean_object* x_84; lean_object* x_129; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_133 = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___closed__0;
lean_inc_ref(x_1);
x_134 = lean_string_append(x_1, x_133);
x_135 = lean_string_append(x_134, x_3);
x_136 = 1;
x_137 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set_uint8(x_137, sizeof(void*)*1, x_136);
lean_inc_ref(x_5);
x_138 = lean_apply_2(x_5, x_137, x_6);
x_139 = lean_ctor_get(x_138, 1);
lean_inc(x_139);
lean_dec_ref(x_138);
x_140 = lean_unsigned_to_nat(0u);
x_141 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
lean_inc_ref(x_2);
x_142 = l_Lake_GitRepo_clone(x_3, x_2, x_141, x_139);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec_ref(x_142);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec_ref(x_143);
x_146 = lean_array_get_size(x_145);
x_147 = lean_nat_dec_lt(x_140, x_146);
if (x_147 == 0)
{
lean_dec(x_146);
lean_dec(x_145);
x_84 = x_144;
goto block_128;
}
else
{
uint8_t x_148; 
x_148 = lean_nat_dec_le(x_146, x_146);
if (x_148 == 0)
{
lean_dec(x_146);
lean_dec(x_145);
x_84 = x_144;
goto block_128;
}
else
{
lean_object* x_149; size_t x_150; size_t x_151; lean_object* x_152; lean_object* x_153; 
x_149 = lean_box(0);
x_150 = 0;
x_151 = lean_usize_of_nat(x_146);
lean_dec(x_146);
lean_inc_ref(x_5);
x_152 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_145, x_150, x_151, x_149, x_5, x_144);
lean_dec(x_145);
x_153 = lean_ctor_get(x_152, 1);
lean_inc(x_153);
lean_dec_ref(x_152);
x_84 = x_153;
goto block_128;
}
}
}
else
{
lean_object* x_154; uint8_t x_155; 
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_154 = lean_ctor_get(x_142, 1);
lean_inc(x_154);
lean_dec_ref(x_142);
x_155 = !lean_is_exclusive(x_143);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; 
x_156 = lean_ctor_get(x_143, 1);
x_157 = lean_ctor_get(x_143, 0);
lean_dec(x_157);
x_158 = lean_array_get_size(x_156);
x_159 = lean_nat_dec_lt(x_140, x_158);
if (x_159 == 0)
{
lean_object* x_160; 
lean_dec(x_158);
lean_dec(x_156);
lean_dec_ref(x_5);
x_160 = lean_box(0);
lean_ctor_set(x_143, 1, x_154);
lean_ctor_set(x_143, 0, x_160);
return x_143;
}
else
{
uint8_t x_161; 
lean_free_object(x_143);
x_161 = lean_nat_dec_le(x_158, x_158);
if (x_161 == 0)
{
lean_dec(x_158);
lean_dec(x_156);
lean_dec_ref(x_5);
x_129 = x_154;
goto block_132;
}
else
{
lean_object* x_162; size_t x_163; size_t x_164; lean_object* x_165; lean_object* x_166; 
x_162 = lean_box(0);
x_163 = 0;
x_164 = lean_usize_of_nat(x_158);
lean_dec(x_158);
x_165 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_156, x_163, x_164, x_162, x_5, x_154);
lean_dec(x_156);
x_166 = lean_ctor_get(x_165, 1);
lean_inc(x_166);
lean_dec_ref(x_165);
x_129 = x_166;
goto block_132;
}
}
}
else
{
lean_object* x_167; lean_object* x_168; uint8_t x_169; 
x_167 = lean_ctor_get(x_143, 1);
lean_inc(x_167);
lean_dec(x_143);
x_168 = lean_array_get_size(x_167);
x_169 = lean_nat_dec_lt(x_140, x_168);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; 
lean_dec(x_168);
lean_dec(x_167);
lean_dec_ref(x_5);
x_170 = lean_box(0);
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_154);
return x_171;
}
else
{
uint8_t x_172; 
x_172 = lean_nat_dec_le(x_168, x_168);
if (x_172 == 0)
{
lean_dec(x_168);
lean_dec(x_167);
lean_dec_ref(x_5);
x_129 = x_154;
goto block_132;
}
else
{
lean_object* x_173; size_t x_174; size_t x_175; lean_object* x_176; lean_object* x_177; 
x_173 = lean_box(0);
x_174 = 0;
x_175 = lean_usize_of_nat(x_168);
lean_dec(x_168);
x_176 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_167, x_174, x_175, x_173, x_5, x_154);
lean_dec(x_167);
x_177 = lean_ctor_get(x_176, 1);
lean_inc(x_177);
lean_dec_ref(x_176);
x_129 = x_177;
goto block_132;
}
}
}
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
block_79:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
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
x_20 = lean_apply_2(x_5, x_19, x_12);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
x_24 = l_Lake_GitRepo_checkoutDetach(x_11, x_2, x_23, x_21);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec_ref(x_24);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_25, 0);
x_29 = lean_ctor_get(x_25, 1);
x_30 = lean_array_get_size(x_29);
x_31 = lean_nat_dec_lt(x_22, x_30);
if (x_31 == 0)
{
lean_dec(x_30);
lean_dec(x_29);
lean_dec_ref(x_5);
lean_ctor_set(x_25, 1, x_26);
return x_25;
}
else
{
uint8_t x_32; 
x_32 = lean_nat_dec_le(x_30, x_30);
if (x_32 == 0)
{
lean_dec(x_30);
lean_dec(x_29);
lean_dec_ref(x_5);
lean_ctor_set(x_25, 1, x_26);
return x_25;
}
else
{
lean_object* x_33; size_t x_34; size_t x_35; lean_object* x_36; uint8_t x_37; 
lean_free_object(x_25);
x_33 = lean_box(0);
x_34 = 0;
x_35 = lean_usize_of_nat(x_30);
lean_dec(x_30);
x_36 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_29, x_34, x_35, x_33, x_5, x_26);
lean_dec(x_29);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 0);
lean_dec(x_38);
lean_ctor_set(x_36, 0, x_28);
return x_36;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_28);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_41 = lean_ctor_get(x_25, 0);
x_42 = lean_ctor_get(x_25, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_25);
x_43 = lean_array_get_size(x_42);
x_44 = lean_nat_dec_lt(x_22, x_43);
if (x_44 == 0)
{
lean_object* x_45; 
lean_dec(x_43);
lean_dec(x_42);
lean_dec_ref(x_5);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_41);
lean_ctor_set(x_45, 1, x_26);
return x_45;
}
else
{
uint8_t x_46; 
x_46 = lean_nat_dec_le(x_43, x_43);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec(x_43);
lean_dec(x_42);
lean_dec_ref(x_5);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_41);
lean_ctor_set(x_47, 1, x_26);
return x_47;
}
else
{
lean_object* x_48; size_t x_49; size_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_48 = lean_box(0);
x_49 = 0;
x_50 = lean_usize_of_nat(x_43);
lean_dec(x_43);
x_51 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_42, x_49, x_50, x_48, x_5, x_26);
lean_dec(x_42);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_53 = x_51;
} else {
 lean_dec_ref(x_51);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_41);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
}
}
else
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_24, 1);
lean_inc(x_55);
lean_dec_ref(x_24);
x_56 = !lean_is_exclusive(x_25);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_57 = lean_ctor_get(x_25, 1);
x_58 = lean_ctor_get(x_25, 0);
lean_dec(x_58);
x_59 = lean_array_get_size(x_57);
x_60 = lean_nat_dec_lt(x_22, x_59);
if (x_60 == 0)
{
lean_object* x_61; 
lean_dec(x_59);
lean_dec(x_57);
lean_dec_ref(x_5);
x_61 = lean_box(0);
lean_ctor_set(x_25, 1, x_55);
lean_ctor_set(x_25, 0, x_61);
return x_25;
}
else
{
uint8_t x_62; 
lean_free_object(x_25);
x_62 = lean_nat_dec_le(x_59, x_59);
if (x_62 == 0)
{
lean_dec(x_59);
lean_dec(x_57);
lean_dec_ref(x_5);
x_7 = x_55;
goto block_10;
}
else
{
lean_object* x_63; size_t x_64; size_t x_65; lean_object* x_66; lean_object* x_67; 
x_63 = lean_box(0);
x_64 = 0;
x_65 = lean_usize_of_nat(x_59);
lean_dec(x_59);
x_66 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_57, x_64, x_65, x_63, x_5, x_55);
lean_dec(x_57);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec_ref(x_66);
x_7 = x_67;
goto block_10;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_68 = lean_ctor_get(x_25, 1);
lean_inc(x_68);
lean_dec(x_25);
x_69 = lean_array_get_size(x_68);
x_70 = lean_nat_dec_lt(x_22, x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_69);
lean_dec(x_68);
lean_dec_ref(x_5);
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_55);
return x_72;
}
else
{
uint8_t x_73; 
x_73 = lean_nat_dec_le(x_69, x_69);
if (x_73 == 0)
{
lean_dec(x_69);
lean_dec(x_68);
lean_dec_ref(x_5);
x_7 = x_55;
goto block_10;
}
else
{
lean_object* x_74; size_t x_75; size_t x_76; lean_object* x_77; lean_object* x_78; 
x_74 = lean_box(0);
x_75 = 0;
x_76 = lean_usize_of_nat(x_69);
lean_dec(x_69);
x_77 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_68, x_75, x_76, x_74, x_5, x_55);
lean_dec(x_68);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec_ref(x_77);
x_7 = x_78;
goto block_10;
}
}
}
}
}
block_83:
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_box(0);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
block_128:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_85; lean_object* x_86; 
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_85 = lean_box(0);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_87 = lean_ctor_get(x_4, 0);
lean_inc(x_87);
lean_dec_ref(x_4);
x_88 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__5;
x_89 = lean_unsigned_to_nat(0u);
x_90 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
lean_inc_ref(x_2);
x_91 = l_Lake_GitRepo_resolveRemoteRevision(x_87, x_88, x_2, x_90, x_84);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec_ref(x_91);
x_94 = lean_ctor_get(x_92, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_92, 1);
lean_inc(x_95);
lean_dec_ref(x_92);
x_96 = lean_array_get_size(x_95);
x_97 = lean_nat_dec_lt(x_89, x_96);
if (x_97 == 0)
{
lean_dec(x_96);
lean_dec(x_95);
x_11 = x_94;
x_12 = x_93;
goto block_79;
}
else
{
uint8_t x_98; 
x_98 = lean_nat_dec_le(x_96, x_96);
if (x_98 == 0)
{
lean_dec(x_96);
lean_dec(x_95);
x_11 = x_94;
x_12 = x_93;
goto block_79;
}
else
{
lean_object* x_99; size_t x_100; size_t x_101; lean_object* x_102; lean_object* x_103; 
x_99 = lean_box(0);
x_100 = 0;
x_101 = lean_usize_of_nat(x_96);
lean_dec(x_96);
lean_inc_ref(x_5);
x_102 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_95, x_100, x_101, x_99, x_5, x_93);
lean_dec(x_95);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
lean_dec_ref(x_102);
x_11 = x_94;
x_12 = x_103;
goto block_79;
}
}
}
else
{
lean_object* x_104; uint8_t x_105; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_104 = lean_ctor_get(x_91, 1);
lean_inc(x_104);
lean_dec_ref(x_91);
x_105 = !lean_is_exclusive(x_92);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_106 = lean_ctor_get(x_92, 1);
x_107 = lean_ctor_get(x_92, 0);
lean_dec(x_107);
x_108 = lean_array_get_size(x_106);
x_109 = lean_nat_dec_lt(x_89, x_108);
if (x_109 == 0)
{
lean_object* x_110; 
lean_dec(x_108);
lean_dec(x_106);
lean_dec_ref(x_5);
x_110 = lean_box(0);
lean_ctor_set(x_92, 1, x_104);
lean_ctor_set(x_92, 0, x_110);
return x_92;
}
else
{
uint8_t x_111; 
lean_free_object(x_92);
x_111 = lean_nat_dec_le(x_108, x_108);
if (x_111 == 0)
{
lean_dec(x_108);
lean_dec(x_106);
lean_dec_ref(x_5);
x_80 = x_104;
goto block_83;
}
else
{
lean_object* x_112; size_t x_113; size_t x_114; lean_object* x_115; lean_object* x_116; 
x_112 = lean_box(0);
x_113 = 0;
x_114 = lean_usize_of_nat(x_108);
lean_dec(x_108);
x_115 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_106, x_113, x_114, x_112, x_5, x_104);
lean_dec(x_106);
x_116 = lean_ctor_get(x_115, 1);
lean_inc(x_116);
lean_dec_ref(x_115);
x_80 = x_116;
goto block_83;
}
}
}
else
{
lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_117 = lean_ctor_get(x_92, 1);
lean_inc(x_117);
lean_dec(x_92);
x_118 = lean_array_get_size(x_117);
x_119 = lean_nat_dec_lt(x_89, x_118);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; 
lean_dec(x_118);
lean_dec(x_117);
lean_dec_ref(x_5);
x_120 = lean_box(0);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_104);
return x_121;
}
else
{
uint8_t x_122; 
x_122 = lean_nat_dec_le(x_118, x_118);
if (x_122 == 0)
{
lean_dec(x_118);
lean_dec(x_117);
lean_dec_ref(x_5);
x_80 = x_104;
goto block_83;
}
else
{
lean_object* x_123; size_t x_124; size_t x_125; lean_object* x_126; lean_object* x_127; 
x_123 = lean_box(0);
x_124 = 0;
x_125 = lean_usize_of_nat(x_118);
lean_dec(x_118);
x_126 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_117, x_124, x_125, x_123, x_5, x_104);
lean_dec(x_117);
x_127 = lean_ctor_get(x_126, 1);
lean_inc(x_127);
lean_dec_ref(x_126);
x_80 = x_127;
goto block_83;
}
}
}
}
}
}
block_132:
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_box(0);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_129);
return x_131;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at_____private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_11; lean_object* x_12; lean_object* x_80; lean_object* x_84; lean_object* x_129; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_133 = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___closed__0;
lean_inc_ref(x_2);
x_134 = lean_string_append(x_2, x_133);
x_135 = lean_string_append(x_134, x_4);
x_136 = 1;
x_137 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set_uint8(x_137, sizeof(void*)*1, x_136);
lean_inc_ref(x_1);
x_138 = lean_apply_2(x_1, x_137, x_6);
x_139 = lean_ctor_get(x_138, 1);
lean_inc(x_139);
lean_dec_ref(x_138);
x_140 = lean_unsigned_to_nat(0u);
x_141 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
lean_inc_ref(x_3);
x_142 = l_Lake_GitRepo_clone(x_4, x_3, x_141, x_139);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec_ref(x_142);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec_ref(x_143);
x_146 = lean_array_get_size(x_145);
x_147 = lean_nat_dec_lt(x_140, x_146);
if (x_147 == 0)
{
lean_dec(x_146);
lean_dec(x_145);
x_84 = x_144;
goto block_128;
}
else
{
uint8_t x_148; 
x_148 = lean_nat_dec_le(x_146, x_146);
if (x_148 == 0)
{
lean_dec(x_146);
lean_dec(x_145);
x_84 = x_144;
goto block_128;
}
else
{
lean_object* x_149; size_t x_150; size_t x_151; lean_object* x_152; lean_object* x_153; 
x_149 = lean_box(0);
x_150 = 0;
x_151 = lean_usize_of_nat(x_146);
lean_dec(x_146);
lean_inc_ref(x_1);
x_152 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_145, x_150, x_151, x_149, x_1, x_144);
lean_dec(x_145);
x_153 = lean_ctor_get(x_152, 1);
lean_inc(x_153);
lean_dec_ref(x_152);
x_84 = x_153;
goto block_128;
}
}
}
else
{
lean_object* x_154; uint8_t x_155; 
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_154 = lean_ctor_get(x_142, 1);
lean_inc(x_154);
lean_dec_ref(x_142);
x_155 = !lean_is_exclusive(x_143);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; 
x_156 = lean_ctor_get(x_143, 1);
x_157 = lean_ctor_get(x_143, 0);
lean_dec(x_157);
x_158 = lean_array_get_size(x_156);
x_159 = lean_nat_dec_lt(x_140, x_158);
if (x_159 == 0)
{
lean_object* x_160; 
lean_dec(x_158);
lean_dec(x_156);
lean_dec_ref(x_1);
x_160 = lean_box(0);
lean_ctor_set(x_143, 1, x_154);
lean_ctor_set(x_143, 0, x_160);
return x_143;
}
else
{
uint8_t x_161; 
lean_free_object(x_143);
x_161 = lean_nat_dec_le(x_158, x_158);
if (x_161 == 0)
{
lean_dec(x_158);
lean_dec(x_156);
lean_dec_ref(x_1);
x_129 = x_154;
goto block_132;
}
else
{
lean_object* x_162; size_t x_163; size_t x_164; lean_object* x_165; lean_object* x_166; 
x_162 = lean_box(0);
x_163 = 0;
x_164 = lean_usize_of_nat(x_158);
lean_dec(x_158);
x_165 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_156, x_163, x_164, x_162, x_1, x_154);
lean_dec(x_156);
x_166 = lean_ctor_get(x_165, 1);
lean_inc(x_166);
lean_dec_ref(x_165);
x_129 = x_166;
goto block_132;
}
}
}
else
{
lean_object* x_167; lean_object* x_168; uint8_t x_169; 
x_167 = lean_ctor_get(x_143, 1);
lean_inc(x_167);
lean_dec(x_143);
x_168 = lean_array_get_size(x_167);
x_169 = lean_nat_dec_lt(x_140, x_168);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; 
lean_dec(x_168);
lean_dec(x_167);
lean_dec_ref(x_1);
x_170 = lean_box(0);
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_154);
return x_171;
}
else
{
uint8_t x_172; 
x_172 = lean_nat_dec_le(x_168, x_168);
if (x_172 == 0)
{
lean_dec(x_168);
lean_dec(x_167);
lean_dec_ref(x_1);
x_129 = x_154;
goto block_132;
}
else
{
lean_object* x_173; size_t x_174; size_t x_175; lean_object* x_176; lean_object* x_177; 
x_173 = lean_box(0);
x_174 = 0;
x_175 = lean_usize_of_nat(x_168);
lean_dec(x_168);
x_176 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_167, x_174, x_175, x_173, x_1, x_154);
lean_dec(x_167);
x_177 = lean_ctor_get(x_176, 1);
lean_inc(x_177);
lean_dec_ref(x_176);
x_129 = x_177;
goto block_132;
}
}
}
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
block_79:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
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
x_20 = lean_apply_2(x_1, x_19, x_12);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
x_24 = l_Lake_GitRepo_checkoutDetach(x_11, x_3, x_23, x_21);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec_ref(x_24);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_25, 0);
x_29 = lean_ctor_get(x_25, 1);
x_30 = lean_array_get_size(x_29);
x_31 = lean_nat_dec_lt(x_22, x_30);
if (x_31 == 0)
{
lean_dec(x_30);
lean_dec(x_29);
lean_dec_ref(x_1);
lean_ctor_set(x_25, 1, x_26);
return x_25;
}
else
{
uint8_t x_32; 
x_32 = lean_nat_dec_le(x_30, x_30);
if (x_32 == 0)
{
lean_dec(x_30);
lean_dec(x_29);
lean_dec_ref(x_1);
lean_ctor_set(x_25, 1, x_26);
return x_25;
}
else
{
lean_object* x_33; size_t x_34; size_t x_35; lean_object* x_36; uint8_t x_37; 
lean_free_object(x_25);
x_33 = lean_box(0);
x_34 = 0;
x_35 = lean_usize_of_nat(x_30);
lean_dec(x_30);
x_36 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_29, x_34, x_35, x_33, x_1, x_26);
lean_dec(x_29);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 0);
lean_dec(x_38);
lean_ctor_set(x_36, 0, x_28);
return x_36;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_28);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_41 = lean_ctor_get(x_25, 0);
x_42 = lean_ctor_get(x_25, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_25);
x_43 = lean_array_get_size(x_42);
x_44 = lean_nat_dec_lt(x_22, x_43);
if (x_44 == 0)
{
lean_object* x_45; 
lean_dec(x_43);
lean_dec(x_42);
lean_dec_ref(x_1);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_41);
lean_ctor_set(x_45, 1, x_26);
return x_45;
}
else
{
uint8_t x_46; 
x_46 = lean_nat_dec_le(x_43, x_43);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec(x_43);
lean_dec(x_42);
lean_dec_ref(x_1);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_41);
lean_ctor_set(x_47, 1, x_26);
return x_47;
}
else
{
lean_object* x_48; size_t x_49; size_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_48 = lean_box(0);
x_49 = 0;
x_50 = lean_usize_of_nat(x_43);
lean_dec(x_43);
x_51 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_42, x_49, x_50, x_48, x_1, x_26);
lean_dec(x_42);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_53 = x_51;
} else {
 lean_dec_ref(x_51);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_41);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
}
}
else
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_24, 1);
lean_inc(x_55);
lean_dec_ref(x_24);
x_56 = !lean_is_exclusive(x_25);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_57 = lean_ctor_get(x_25, 1);
x_58 = lean_ctor_get(x_25, 0);
lean_dec(x_58);
x_59 = lean_array_get_size(x_57);
x_60 = lean_nat_dec_lt(x_22, x_59);
if (x_60 == 0)
{
lean_object* x_61; 
lean_dec(x_59);
lean_dec(x_57);
lean_dec_ref(x_1);
x_61 = lean_box(0);
lean_ctor_set(x_25, 1, x_55);
lean_ctor_set(x_25, 0, x_61);
return x_25;
}
else
{
uint8_t x_62; 
lean_free_object(x_25);
x_62 = lean_nat_dec_le(x_59, x_59);
if (x_62 == 0)
{
lean_dec(x_59);
lean_dec(x_57);
lean_dec_ref(x_1);
x_7 = x_55;
goto block_10;
}
else
{
lean_object* x_63; size_t x_64; size_t x_65; lean_object* x_66; lean_object* x_67; 
x_63 = lean_box(0);
x_64 = 0;
x_65 = lean_usize_of_nat(x_59);
lean_dec(x_59);
x_66 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_57, x_64, x_65, x_63, x_1, x_55);
lean_dec(x_57);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec_ref(x_66);
x_7 = x_67;
goto block_10;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_68 = lean_ctor_get(x_25, 1);
lean_inc(x_68);
lean_dec(x_25);
x_69 = lean_array_get_size(x_68);
x_70 = lean_nat_dec_lt(x_22, x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_69);
lean_dec(x_68);
lean_dec_ref(x_1);
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_55);
return x_72;
}
else
{
uint8_t x_73; 
x_73 = lean_nat_dec_le(x_69, x_69);
if (x_73 == 0)
{
lean_dec(x_69);
lean_dec(x_68);
lean_dec_ref(x_1);
x_7 = x_55;
goto block_10;
}
else
{
lean_object* x_74; size_t x_75; size_t x_76; lean_object* x_77; lean_object* x_78; 
x_74 = lean_box(0);
x_75 = 0;
x_76 = lean_usize_of_nat(x_69);
lean_dec(x_69);
x_77 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_68, x_75, x_76, x_74, x_1, x_55);
lean_dec(x_68);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec_ref(x_77);
x_7 = x_78;
goto block_10;
}
}
}
}
}
block_83:
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_box(0);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
block_128:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_85; lean_object* x_86; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_85 = lean_box(0);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_87 = lean_ctor_get(x_5, 0);
lean_inc(x_87);
lean_dec_ref(x_5);
x_88 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__5;
x_89 = lean_unsigned_to_nat(0u);
x_90 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
lean_inc_ref(x_3);
x_91 = l_Lake_GitRepo_resolveRemoteRevision(x_87, x_88, x_3, x_90, x_84);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec_ref(x_91);
x_94 = lean_ctor_get(x_92, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_92, 1);
lean_inc(x_95);
lean_dec_ref(x_92);
x_96 = lean_array_get_size(x_95);
x_97 = lean_nat_dec_lt(x_89, x_96);
if (x_97 == 0)
{
lean_dec(x_96);
lean_dec(x_95);
x_11 = x_94;
x_12 = x_93;
goto block_79;
}
else
{
uint8_t x_98; 
x_98 = lean_nat_dec_le(x_96, x_96);
if (x_98 == 0)
{
lean_dec(x_96);
lean_dec(x_95);
x_11 = x_94;
x_12 = x_93;
goto block_79;
}
else
{
lean_object* x_99; size_t x_100; size_t x_101; lean_object* x_102; lean_object* x_103; 
x_99 = lean_box(0);
x_100 = 0;
x_101 = lean_usize_of_nat(x_96);
lean_dec(x_96);
lean_inc_ref(x_1);
x_102 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_95, x_100, x_101, x_99, x_1, x_93);
lean_dec(x_95);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
lean_dec_ref(x_102);
x_11 = x_94;
x_12 = x_103;
goto block_79;
}
}
}
else
{
lean_object* x_104; uint8_t x_105; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_104 = lean_ctor_get(x_91, 1);
lean_inc(x_104);
lean_dec_ref(x_91);
x_105 = !lean_is_exclusive(x_92);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_106 = lean_ctor_get(x_92, 1);
x_107 = lean_ctor_get(x_92, 0);
lean_dec(x_107);
x_108 = lean_array_get_size(x_106);
x_109 = lean_nat_dec_lt(x_89, x_108);
if (x_109 == 0)
{
lean_object* x_110; 
lean_dec(x_108);
lean_dec(x_106);
lean_dec_ref(x_1);
x_110 = lean_box(0);
lean_ctor_set(x_92, 1, x_104);
lean_ctor_set(x_92, 0, x_110);
return x_92;
}
else
{
uint8_t x_111; 
lean_free_object(x_92);
x_111 = lean_nat_dec_le(x_108, x_108);
if (x_111 == 0)
{
lean_dec(x_108);
lean_dec(x_106);
lean_dec_ref(x_1);
x_80 = x_104;
goto block_83;
}
else
{
lean_object* x_112; size_t x_113; size_t x_114; lean_object* x_115; lean_object* x_116; 
x_112 = lean_box(0);
x_113 = 0;
x_114 = lean_usize_of_nat(x_108);
lean_dec(x_108);
x_115 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_106, x_113, x_114, x_112, x_1, x_104);
lean_dec(x_106);
x_116 = lean_ctor_get(x_115, 1);
lean_inc(x_116);
lean_dec_ref(x_115);
x_80 = x_116;
goto block_83;
}
}
}
else
{
lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_117 = lean_ctor_get(x_92, 1);
lean_inc(x_117);
lean_dec(x_92);
x_118 = lean_array_get_size(x_117);
x_119 = lean_nat_dec_lt(x_89, x_118);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; 
lean_dec(x_118);
lean_dec(x_117);
lean_dec_ref(x_1);
x_120 = lean_box(0);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_104);
return x_121;
}
else
{
uint8_t x_122; 
x_122 = lean_nat_dec_le(x_118, x_118);
if (x_122 == 0)
{
lean_dec(x_118);
lean_dec(x_117);
lean_dec_ref(x_1);
x_80 = x_104;
goto block_83;
}
else
{
lean_object* x_123; size_t x_124; size_t x_125; lean_object* x_126; lean_object* x_127; 
x_123 = lean_box(0);
x_124 = 0;
x_125 = lean_usize_of_nat(x_118);
lean_dec(x_118);
x_126 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_117, x_124, x_125, x_123, x_1, x_104);
lean_dec(x_117);
x_127 = lean_ctor_get(x_126, 1);
lean_inc(x_127);
lean_dec_ref(x_126);
x_80 = x_127;
goto block_83;
}
}
}
}
}
}
block_132:
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_box(0);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_129);
return x_131;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at_____private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_36; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_118; lean_object* x_122; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_126 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__5;
x_127 = lean_unsigned_to_nat(0u);
x_128 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
lean_inc_ref(x_3);
x_129 = l_Lake_GitRepo_findRemoteRevision(x_3, x_4, x_126, x_128, x_5);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_173; uint8_t x_174; 
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec_ref(x_129);
x_132 = lean_ctor_get(x_130, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_130, 1);
lean_inc(x_133);
lean_dec_ref(x_130);
x_173 = lean_array_get_size(x_133);
x_174 = lean_nat_dec_lt(x_127, x_173);
if (x_174 == 0)
{
lean_dec(x_173);
lean_dec(x_133);
x_134 = x_131;
goto block_172;
}
else
{
uint8_t x_175; 
x_175 = lean_nat_dec_le(x_173, x_173);
if (x_175 == 0)
{
lean_dec(x_173);
lean_dec(x_133);
x_134 = x_131;
goto block_172;
}
else
{
lean_object* x_176; size_t x_177; size_t x_178; lean_object* x_179; lean_object* x_180; 
x_176 = lean_box(0);
x_177 = 0;
x_178 = lean_usize_of_nat(x_173);
lean_dec(x_173);
lean_inc_ref(x_1);
x_179 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_133, x_177, x_178, x_176, x_1, x_131);
lean_dec(x_133);
x_180 = lean_ctor_get(x_179, 1);
lean_inc(x_180);
lean_dec_ref(x_179);
x_134 = x_180;
goto block_172;
}
}
block_172:
{
lean_object* x_135; lean_object* x_136; 
lean_inc_ref(x_3);
x_135 = l_Lake_GitRepo_getHeadRevision(x_3, x_128, x_134);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; 
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec_ref(x_135);
x_138 = lean_ctor_get(x_136, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_136, 1);
lean_inc(x_139);
lean_dec_ref(x_136);
x_140 = lean_array_get_size(x_139);
x_141 = lean_nat_dec_lt(x_127, x_140);
if (x_141 == 0)
{
lean_dec(x_140);
lean_dec(x_139);
x_40 = x_132;
x_41 = x_138;
x_42 = x_137;
goto block_117;
}
else
{
uint8_t x_142; 
x_142 = lean_nat_dec_le(x_140, x_140);
if (x_142 == 0)
{
lean_dec(x_140);
lean_dec(x_139);
x_40 = x_132;
x_41 = x_138;
x_42 = x_137;
goto block_117;
}
else
{
lean_object* x_143; size_t x_144; size_t x_145; lean_object* x_146; lean_object* x_147; 
x_143 = lean_box(0);
x_144 = 0;
x_145 = lean_usize_of_nat(x_140);
lean_dec(x_140);
lean_inc_ref(x_1);
x_146 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_139, x_144, x_145, x_143, x_1, x_137);
lean_dec(x_139);
x_147 = lean_ctor_get(x_146, 1);
lean_inc(x_147);
lean_dec_ref(x_146);
x_40 = x_132;
x_41 = x_138;
x_42 = x_147;
goto block_117;
}
}
}
else
{
lean_object* x_148; uint8_t x_149; 
lean_dec(x_132);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_148 = lean_ctor_get(x_135, 1);
lean_inc(x_148);
lean_dec_ref(x_135);
x_149 = !lean_is_exclusive(x_136);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; 
x_150 = lean_ctor_get(x_136, 1);
x_151 = lean_ctor_get(x_136, 0);
lean_dec(x_151);
x_152 = lean_array_get_size(x_150);
x_153 = lean_nat_dec_lt(x_127, x_152);
if (x_153 == 0)
{
lean_object* x_154; 
lean_dec(x_152);
lean_dec(x_150);
lean_dec_ref(x_1);
x_154 = lean_box(0);
lean_ctor_set(x_136, 1, x_148);
lean_ctor_set(x_136, 0, x_154);
return x_136;
}
else
{
uint8_t x_155; 
lean_free_object(x_136);
x_155 = lean_nat_dec_le(x_152, x_152);
if (x_155 == 0)
{
lean_dec(x_152);
lean_dec(x_150);
lean_dec_ref(x_1);
x_118 = x_148;
goto block_121;
}
else
{
lean_object* x_156; size_t x_157; size_t x_158; lean_object* x_159; lean_object* x_160; 
x_156 = lean_box(0);
x_157 = 0;
x_158 = lean_usize_of_nat(x_152);
lean_dec(x_152);
x_159 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_150, x_157, x_158, x_156, x_1, x_148);
lean_dec(x_150);
x_160 = lean_ctor_get(x_159, 1);
lean_inc(x_160);
lean_dec_ref(x_159);
x_118 = x_160;
goto block_121;
}
}
}
else
{
lean_object* x_161; lean_object* x_162; uint8_t x_163; 
x_161 = lean_ctor_get(x_136, 1);
lean_inc(x_161);
lean_dec(x_136);
x_162 = lean_array_get_size(x_161);
x_163 = lean_nat_dec_lt(x_127, x_162);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; 
lean_dec(x_162);
lean_dec(x_161);
lean_dec_ref(x_1);
x_164 = lean_box(0);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_148);
return x_165;
}
else
{
uint8_t x_166; 
x_166 = lean_nat_dec_le(x_162, x_162);
if (x_166 == 0)
{
lean_dec(x_162);
lean_dec(x_161);
lean_dec_ref(x_1);
x_118 = x_148;
goto block_121;
}
else
{
lean_object* x_167; size_t x_168; size_t x_169; lean_object* x_170; lean_object* x_171; 
x_167 = lean_box(0);
x_168 = 0;
x_169 = lean_usize_of_nat(x_162);
lean_dec(x_162);
x_170 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_161, x_168, x_169, x_167, x_1, x_148);
lean_dec(x_161);
x_171 = lean_ctor_get(x_170, 1);
lean_inc(x_171);
lean_dec_ref(x_170);
x_118 = x_171;
goto block_121;
}
}
}
}
}
}
else
{
lean_object* x_181; uint8_t x_182; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_181 = lean_ctor_get(x_129, 1);
lean_inc(x_181);
lean_dec_ref(x_129);
x_182 = !lean_is_exclusive(x_130);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; 
x_183 = lean_ctor_get(x_130, 1);
x_184 = lean_ctor_get(x_130, 0);
lean_dec(x_184);
x_185 = lean_array_get_size(x_183);
x_186 = lean_nat_dec_lt(x_127, x_185);
if (x_186 == 0)
{
lean_object* x_187; 
lean_dec(x_185);
lean_dec(x_183);
lean_dec_ref(x_1);
x_187 = lean_box(0);
lean_ctor_set(x_130, 1, x_181);
lean_ctor_set(x_130, 0, x_187);
return x_130;
}
else
{
uint8_t x_188; 
lean_free_object(x_130);
x_188 = lean_nat_dec_le(x_185, x_185);
if (x_188 == 0)
{
lean_dec(x_185);
lean_dec(x_183);
lean_dec_ref(x_1);
x_122 = x_181;
goto block_125;
}
else
{
lean_object* x_189; size_t x_190; size_t x_191; lean_object* x_192; lean_object* x_193; 
x_189 = lean_box(0);
x_190 = 0;
x_191 = lean_usize_of_nat(x_185);
lean_dec(x_185);
x_192 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_183, x_190, x_191, x_189, x_1, x_181);
lean_dec(x_183);
x_193 = lean_ctor_get(x_192, 1);
lean_inc(x_193);
lean_dec_ref(x_192);
x_122 = x_193;
goto block_125;
}
}
}
else
{
lean_object* x_194; lean_object* x_195; uint8_t x_196; 
x_194 = lean_ctor_get(x_130, 1);
lean_inc(x_194);
lean_dec(x_130);
x_195 = lean_array_get_size(x_194);
x_196 = lean_nat_dec_lt(x_127, x_195);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; 
lean_dec(x_195);
lean_dec(x_194);
lean_dec_ref(x_1);
x_197 = lean_box(0);
x_198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_181);
return x_198;
}
else
{
uint8_t x_199; 
x_199 = lean_nat_dec_le(x_195, x_195);
if (x_199 == 0)
{
lean_dec(x_195);
lean_dec(x_194);
lean_dec_ref(x_1);
x_122 = x_181;
goto block_125;
}
else
{
lean_object* x_200; size_t x_201; size_t x_202; lean_object* x_203; lean_object* x_204; 
x_200 = lean_box(0);
x_201 = 0;
x_202 = lean_usize_of_nat(x_195);
lean_dec(x_195);
x_203 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_194, x_201, x_202, x_200, x_1, x_181);
lean_dec(x_194);
x_204 = lean_ctor_get(x_203, 1);
lean_inc(x_204);
lean_dec_ref(x_203);
x_122 = x_204;
goto block_125;
}
}
}
}
block_22:
{
if (x_6 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
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
x_17 = lean_apply_2(x_1, x_16, x_7);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
block_35:
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_array_get_size(x_24);
x_28 = lean_nat_dec_lt(x_23, x_27);
if (x_28 == 0)
{
lean_dec(x_27);
lean_dec_ref(x_24);
x_6 = x_25;
x_7 = x_26;
goto block_22;
}
else
{
uint8_t x_29; 
x_29 = lean_nat_dec_le(x_27, x_27);
if (x_29 == 0)
{
lean_dec(x_27);
lean_dec_ref(x_24);
x_6 = x_25;
x_7 = x_26;
goto block_22;
}
else
{
lean_object* x_30; size_t x_31; size_t x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_box(0);
x_31 = 0;
x_32 = lean_usize_of_nat(x_27);
lean_dec(x_27);
lean_inc_ref(x_1);
x_33 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_24, x_31, x_32, x_30, x_1, x_26);
lean_dec_ref(x_24);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec_ref(x_33);
x_6 = x_25;
x_7 = x_34;
goto block_22;
}
}
}
block_39:
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
block_117:
{
uint8_t x_43; 
x_43 = lean_string_dec_eq(x_41, x_40);
lean_dec_ref(x_41);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_44 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
x_45 = lean_string_append(x_2, x_44);
x_46 = lean_string_append(x_45, x_40);
x_47 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3;
x_48 = lean_string_append(x_46, x_47);
x_49 = 1;
x_50 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set_uint8(x_50, sizeof(void*)*1, x_49);
lean_inc_ref(x_1);
x_51 = lean_apply_2(x_1, x_50, x_42);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec_ref(x_51);
x_53 = lean_unsigned_to_nat(0u);
x_54 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
x_55 = l_Lake_GitRepo_checkoutDetach(x_40, x_3, x_54, x_52);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec_ref(x_55);
x_58 = !lean_is_exclusive(x_56);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_59 = lean_ctor_get(x_56, 0);
x_60 = lean_ctor_get(x_56, 1);
x_61 = lean_array_get_size(x_60);
x_62 = lean_nat_dec_lt(x_53, x_61);
if (x_62 == 0)
{
lean_dec(x_61);
lean_dec(x_60);
lean_dec_ref(x_1);
lean_ctor_set(x_56, 1, x_57);
return x_56;
}
else
{
uint8_t x_63; 
x_63 = lean_nat_dec_le(x_61, x_61);
if (x_63 == 0)
{
lean_dec(x_61);
lean_dec(x_60);
lean_dec_ref(x_1);
lean_ctor_set(x_56, 1, x_57);
return x_56;
}
else
{
lean_object* x_64; size_t x_65; size_t x_66; lean_object* x_67; uint8_t x_68; 
lean_free_object(x_56);
x_64 = lean_box(0);
x_65 = 0;
x_66 = lean_usize_of_nat(x_61);
lean_dec(x_61);
x_67 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_60, x_65, x_66, x_64, x_1, x_57);
lean_dec(x_60);
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_67, 0);
lean_dec(x_69);
lean_ctor_set(x_67, 0, x_59);
return x_67;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
lean_dec(x_67);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_59);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_72 = lean_ctor_get(x_56, 0);
x_73 = lean_ctor_get(x_56, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_56);
x_74 = lean_array_get_size(x_73);
x_75 = lean_nat_dec_lt(x_53, x_74);
if (x_75 == 0)
{
lean_object* x_76; 
lean_dec(x_74);
lean_dec(x_73);
lean_dec_ref(x_1);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_72);
lean_ctor_set(x_76, 1, x_57);
return x_76;
}
else
{
uint8_t x_77; 
x_77 = lean_nat_dec_le(x_74, x_74);
if (x_77 == 0)
{
lean_object* x_78; 
lean_dec(x_74);
lean_dec(x_73);
lean_dec_ref(x_1);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_72);
lean_ctor_set(x_78, 1, x_57);
return x_78;
}
else
{
lean_object* x_79; size_t x_80; size_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_79 = lean_box(0);
x_80 = 0;
x_81 = lean_usize_of_nat(x_74);
lean_dec(x_74);
x_82 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_73, x_80, x_81, x_79, x_1, x_57);
lean_dec(x_73);
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_84 = x_82;
} else {
 lean_dec_ref(x_82);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_72);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
}
}
}
else
{
lean_object* x_86; uint8_t x_87; 
x_86 = lean_ctor_get(x_55, 1);
lean_inc(x_86);
lean_dec_ref(x_55);
x_87 = !lean_is_exclusive(x_56);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_88 = lean_ctor_get(x_56, 1);
x_89 = lean_ctor_get(x_56, 0);
lean_dec(x_89);
x_90 = lean_array_get_size(x_88);
x_91 = lean_nat_dec_lt(x_53, x_90);
if (x_91 == 0)
{
lean_object* x_92; 
lean_dec(x_90);
lean_dec(x_88);
lean_dec_ref(x_1);
x_92 = lean_box(0);
lean_ctor_set(x_56, 1, x_86);
lean_ctor_set(x_56, 0, x_92);
return x_56;
}
else
{
uint8_t x_93; 
lean_free_object(x_56);
x_93 = lean_nat_dec_le(x_90, x_90);
if (x_93 == 0)
{
lean_dec(x_90);
lean_dec(x_88);
lean_dec_ref(x_1);
x_36 = x_86;
goto block_39;
}
else
{
lean_object* x_94; size_t x_95; size_t x_96; lean_object* x_97; lean_object* x_98; 
x_94 = lean_box(0);
x_95 = 0;
x_96 = lean_usize_of_nat(x_90);
lean_dec(x_90);
x_97 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_88, x_95, x_96, x_94, x_1, x_86);
lean_dec(x_88);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec_ref(x_97);
x_36 = x_98;
goto block_39;
}
}
}
else
{
lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_99 = lean_ctor_get(x_56, 1);
lean_inc(x_99);
lean_dec(x_56);
x_100 = lean_array_get_size(x_99);
x_101 = lean_nat_dec_lt(x_53, x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_100);
lean_dec(x_99);
lean_dec_ref(x_1);
x_102 = lean_box(0);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_86);
return x_103;
}
else
{
uint8_t x_104; 
x_104 = lean_nat_dec_le(x_100, x_100);
if (x_104 == 0)
{
lean_dec(x_100);
lean_dec(x_99);
lean_dec_ref(x_1);
x_36 = x_86;
goto block_39;
}
else
{
lean_object* x_105; size_t x_106; size_t x_107; lean_object* x_108; lean_object* x_109; 
x_105 = lean_box(0);
x_106 = 0;
x_107 = lean_usize_of_nat(x_100);
lean_dec(x_100);
x_108 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_99, x_106, x_107, x_105, x_1, x_86);
lean_dec(x_99);
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
lean_dec_ref(x_108);
x_36 = x_109;
goto block_39;
}
}
}
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
lean_dec_ref(x_40);
lean_inc_ref(x_3);
x_110 = l_Lake_GitRepo_hasNoDiff(x_3, x_42);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec_ref(x_110);
x_113 = lean_unsigned_to_nat(0u);
x_114 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
x_115 = lean_unbox(x_111);
lean_dec(x_111);
if (x_115 == 0)
{
x_23 = x_113;
x_24 = x_114;
x_25 = x_43;
x_26 = x_112;
goto block_35;
}
else
{
uint8_t x_116; 
x_116 = 0;
x_23 = x_113;
x_24 = x_114;
x_25 = x_116;
x_26 = x_112;
goto block_35;
}
}
}
block_121:
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_box(0);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_118);
return x_120;
}
block_125:
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_box(0);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_122);
return x_124;
}
}
}
static uint8_t _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__0() {
_start:
{
uint8_t x_1; 
x_1 = l_System_Platform_isWindows;
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": URL has changed; deleting '", 29, 29);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' and cloning again", 19, 19);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": URL has changed; you might need to delete '", 45, 45);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' manually", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
x_2 = lean_array_get_size(x_1);
return x_2;
}
}
static uint8_t _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_lt(x_2, x_1);
return x_3;
}
}
static uint8_t _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5;
x_2 = lean_nat_dec_le(x_1, x_1);
return x_2;
}
}
static size_t _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__8() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5;
x_2 = lean_usize_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; 
x_52 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__5;
lean_inc_ref(x_2);
x_53 = l_Lake_GitRepo_getRemoteUrl_x3f(x_52, x_2, x_6);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec_ref(x_53);
x_56 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
if (lean_obj_tag(x_54) == 0)
{
uint8_t x_67; 
x_67 = 0;
x_57 = x_67;
x_58 = x_55;
goto block_66;
}
else
{
lean_object* x_68; uint8_t x_69; 
x_68 = lean_ctor_get(x_54, 0);
lean_inc(x_68);
lean_dec_ref(x_54);
x_69 = lean_string_dec_eq(x_68, x_3);
if (x_69 == 0)
{
lean_object* x_70; 
x_70 = lean_io_realpath(x_68, x_55);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec_ref(x_70);
lean_inc_ref(x_3);
x_73 = lean_io_realpath(x_3, x_72);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec_ref(x_73);
x_76 = lean_string_dec_eq(x_71, x_74);
lean_dec(x_74);
lean_dec(x_71);
x_57 = x_76;
x_58 = x_75;
goto block_66;
}
else
{
lean_object* x_77; 
lean_dec(x_71);
x_77 = lean_ctor_get(x_73, 1);
lean_inc(x_77);
lean_dec_ref(x_73);
x_57 = x_69;
x_58 = x_77;
goto block_66;
}
}
else
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_70, 1);
lean_inc(x_78);
lean_dec_ref(x_70);
x_57 = x_69;
x_58 = x_78;
goto block_66;
}
}
else
{
lean_dec(x_68);
x_57 = x_69;
x_58 = x_55;
goto block_66;
}
}
block_51:
{
if (x_7 == 0)
{
uint8_t x_9; 
x_9 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__0;
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_10 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__1;
lean_inc_ref(x_1);
x_11 = lean_string_append(x_1, x_10);
x_12 = lean_string_append(x_11, x_2);
x_13 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__2;
x_14 = lean_string_append(x_12, x_13);
x_15 = 1;
x_16 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_15);
lean_inc_ref(x_5);
x_17 = lean_apply_2(x_5, x_16, x_8);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = l_IO_FS_removeDirAll(x_2, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at_____private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(x_5, x_1, x_2, x_3, x_4, x_20);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_19, 0);
x_24 = lean_ctor_get(x_19, 1);
x_25 = lean_io_error_to_string(x_23);
x_26 = 3;
x_27 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_26);
x_28 = lean_apply_2(x_5, x_27, x_24);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = lean_box(0);
lean_ctor_set(x_19, 1, x_29);
lean_ctor_set(x_19, 0, x_30);
return x_19;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_31 = lean_ctor_get(x_19, 0);
x_32 = lean_ctor_get(x_19, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_19);
x_33 = lean_io_error_to_string(x_31);
x_34 = 3;
x_35 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_34);
x_36 = lean_apply_2(x_5, x_35, x_32);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec_ref(x_36);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec_ref(x_3);
x_40 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__3;
lean_inc_ref(x_1);
x_41 = lean_string_append(x_1, x_40);
x_42 = lean_string_append(x_41, x_2);
x_43 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4;
x_44 = lean_string_append(x_42, x_43);
x_45 = 1;
x_46 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set_uint8(x_46, sizeof(void*)*1, x_45);
lean_inc_ref(x_5);
x_47 = lean_apply_2(x_5, x_46, x_8);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec_ref(x_47);
x_49 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at_____private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(x_5, x_1, x_2, x_4, x_48);
return x_49;
}
}
else
{
lean_object* x_50; 
lean_dec_ref(x_3);
x_50 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at_____private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(x_5, x_1, x_2, x_4, x_8);
return x_50;
}
}
block_66:
{
uint8_t x_59; 
x_59 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6;
if (x_59 == 0)
{
x_7 = x_57;
x_8 = x_58;
goto block_51;
}
else
{
uint8_t x_60; 
x_60 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
if (x_60 == 0)
{
x_7 = x_57;
x_8 = x_58;
goto block_51;
}
else
{
lean_object* x_61; size_t x_62; size_t x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_box(0);
x_62 = 0;
x_63 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__8;
lean_inc_ref(x_5);
x_64 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_56, x_62, x_63, x_61, x_5, x_58);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec_ref(x_64);
x_7 = x_57;
x_8 = x_65;
goto block_51;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at_____private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; 
x_52 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__5;
lean_inc_ref(x_3);
x_53 = l_Lake_GitRepo_getRemoteUrl_x3f(x_52, x_3, x_6);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec_ref(x_53);
x_56 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
if (lean_obj_tag(x_54) == 0)
{
uint8_t x_67; 
x_67 = 0;
x_57 = x_67;
x_58 = x_55;
goto block_66;
}
else
{
lean_object* x_68; uint8_t x_69; 
x_68 = lean_ctor_get(x_54, 0);
lean_inc(x_68);
lean_dec_ref(x_54);
x_69 = lean_string_dec_eq(x_68, x_4);
if (x_69 == 0)
{
lean_object* x_70; 
x_70 = lean_io_realpath(x_68, x_55);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec_ref(x_70);
lean_inc_ref(x_4);
x_73 = lean_io_realpath(x_4, x_72);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec_ref(x_73);
x_76 = lean_string_dec_eq(x_71, x_74);
lean_dec(x_74);
lean_dec(x_71);
x_57 = x_76;
x_58 = x_75;
goto block_66;
}
else
{
lean_object* x_77; 
lean_dec(x_71);
x_77 = lean_ctor_get(x_73, 1);
lean_inc(x_77);
lean_dec_ref(x_73);
x_57 = x_69;
x_58 = x_77;
goto block_66;
}
}
else
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_70, 1);
lean_inc(x_78);
lean_dec_ref(x_70);
x_57 = x_69;
x_58 = x_78;
goto block_66;
}
}
else
{
lean_dec(x_68);
x_57 = x_69;
x_58 = x_55;
goto block_66;
}
}
block_51:
{
if (x_7 == 0)
{
uint8_t x_9; 
x_9 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__0;
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_10 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__1;
lean_inc_ref(x_2);
x_11 = lean_string_append(x_2, x_10);
x_12 = lean_string_append(x_11, x_3);
x_13 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__2;
x_14 = lean_string_append(x_12, x_13);
x_15 = 1;
x_16 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_15);
lean_inc_ref(x_1);
x_17 = lean_apply_2(x_1, x_16, x_8);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = l_IO_FS_removeDirAll(x_3, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at_____private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(x_1, x_2, x_3, x_4, x_5, x_20);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_19, 0);
x_24 = lean_ctor_get(x_19, 1);
x_25 = lean_io_error_to_string(x_23);
x_26 = 3;
x_27 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_26);
x_28 = lean_apply_2(x_1, x_27, x_24);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = lean_box(0);
lean_ctor_set(x_19, 1, x_29);
lean_ctor_set(x_19, 0, x_30);
return x_19;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_31 = lean_ctor_get(x_19, 0);
x_32 = lean_ctor_get(x_19, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_19);
x_33 = lean_io_error_to_string(x_31);
x_34 = 3;
x_35 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_34);
x_36 = lean_apply_2(x_1, x_35, x_32);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec_ref(x_36);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec_ref(x_4);
x_40 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__3;
lean_inc_ref(x_2);
x_41 = lean_string_append(x_2, x_40);
x_42 = lean_string_append(x_41, x_3);
x_43 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4;
x_44 = lean_string_append(x_42, x_43);
x_45 = 1;
x_46 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set_uint8(x_46, sizeof(void*)*1, x_45);
lean_inc_ref(x_1);
x_47 = lean_apply_2(x_1, x_46, x_8);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec_ref(x_47);
x_49 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at_____private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(x_1, x_2, x_3, x_5, x_48);
return x_49;
}
}
else
{
lean_object* x_50; 
lean_dec_ref(x_4);
x_50 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at_____private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(x_1, x_2, x_3, x_5, x_8);
return x_50;
}
}
block_66:
{
uint8_t x_59; 
x_59 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6;
if (x_59 == 0)
{
x_7 = x_57;
x_8 = x_58;
goto block_51;
}
else
{
uint8_t x_60; 
x_60 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
if (x_60 == 0)
{
x_7 = x_57;
x_8 = x_58;
goto block_51;
}
else
{
lean_object* x_61; size_t x_62; size_t x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_box(0);
x_62 = 0;
x_63 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__8;
lean_inc_ref(x_1);
x_64 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_56, x_62, x_63, x_61, x_1, x_58);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec_ref(x_64);
x_7 = x_57;
x_8 = x_65;
goto block_51;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_15; uint8_t x_16; 
x_7 = l_System_FilePath_isDir(x_2, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
x_15 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
x_16 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6;
if (x_16 == 0)
{
x_10 = x_9;
goto block_14;
}
else
{
uint8_t x_17; 
x_17 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
if (x_17 == 0)
{
x_10 = x_9;
goto block_14;
}
else
{
lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_box(0);
x_19 = 0;
x_20 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__8;
lean_inc_ref(x_5);
x_21 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_15, x_19, x_20, x_18, x_5, x_9);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec_ref(x_21);
x_10 = x_22;
goto block_14;
}
}
block_14:
{
uint8_t x_11; 
x_11 = lean_unbox(x_8);
lean_dec(x_8);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at_____private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(x_5, x_1, x_2, x_3, x_4, x_10);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at_____private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(x_5, x_1, x_2, x_3, x_4, x_10);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_MaterializedDep_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instInhabitedMaterializedDep_default___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_System_instInhabitedFilePath_default;
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedMaterializedDep_default___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedMaterializedDep_default___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instInhabitedPackageEntry_default;
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedMaterializedDep_default___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_instInhabitedMaterializedDep_default___closed__2;
x_2 = l_Lake_instInhabitedMaterializedDep_default___closed__1;
x_3 = l_Lake_instInhabitedMaterializedDep_default___closed__0;
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
x_1 = l_Lake_instInhabitedMaterializedDep_default___closed__3;
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
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_std_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_std_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_1 = lean_mk_string_unchecked(" @ git ", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Format_defWidth;
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n    rev = ", 11, 11);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" @ ", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__9() {
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
x_27 = l_Lake_instInhabitedMaterializedDep_default___closed__1;
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
x_32 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__6;
x_33 = lean_unsigned_to_nat(0u);
x_34 = l_Std_Format_pretty(x_3, x_32, x_33, x_33);
x_35 = lean_string_append(x_30, x_34);
x_36 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__7;
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
x_42 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__6;
x_43 = lean_unsigned_to_nat(0u);
x_44 = l_Std_Format_pretty(x_41, x_42, x_43, x_43);
x_45 = lean_string_append(x_39, x_44);
x_46 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__7;
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
x_50 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__8;
x_51 = l_Lake_StdVer_toString(x_49);
x_52 = l_String_quote(x_51);
lean_ctor_set_tag(x_3, 3);
lean_ctor_set(x_3, 0, x_52);
x_53 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__6;
x_54 = lean_unsigned_to_nat(0u);
x_55 = l_Std_Format_pretty(x_3, x_53, x_54, x_54);
x_56 = lean_string_append(x_50, x_55);
x_57 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__9;
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
x_60 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__8;
x_61 = l_Lake_StdVer_toString(x_59);
x_62 = l_String_quote(x_61);
x_63 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_63, 0, x_62);
x_64 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__6;
x_65 = lean_unsigned_to_nat(0u);
x_66 = l_Std_Format_pretty(x_63, x_64, x_65, x_65);
x_67 = lean_string_append(x_60, x_66);
x_68 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__9;
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
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_defaultConfigFile;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0;
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
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at_____private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_15; uint8_t x_16; 
x_7 = l_System_FilePath_isDir(x_3, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
x_15 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
x_16 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6;
if (x_16 == 0)
{
x_10 = x_9;
goto block_14;
}
else
{
uint8_t x_17; 
x_17 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
if (x_17 == 0)
{
x_10 = x_9;
goto block_14;
}
else
{
lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_box(0);
x_19 = 0;
x_20 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__8;
lean_inc_ref(x_1);
x_21 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_15, x_19, x_20, x_18, x_1, x_9);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec_ref(x_21);
x_10 = x_22;
goto block_14;
}
}
block_14:
{
uint8_t x_11; 
x_11 = lean_unbox(x_8);
lean_dec(x_8);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at_____private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(x_1, x_2, x_3, x_4, x_5, x_10);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at_____private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(x_1, x_2, x_3, x_4, x_5, x_10);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_37; lean_object* x_38; lean_object* x_102; 
x_17 = lean_ctor_get(x_3, 5);
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_1, 1);
x_37 = l_Lake_joinRelative(x_4, x_6);
x_102 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lean_NameMap_find_x3f_spec__0___redArg(x_17, x_18);
if (lean_obj_tag(x_102) == 0)
{
x_38 = x_7;
goto block_101;
}
else
{
lean_object* x_103; 
lean_dec_ref(x_7);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
lean_dec_ref(x_102);
x_38 = x_103;
goto block_101;
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
block_30:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_9);
lean_ctor_set(x_24, 3, x_10);
x_25 = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0;
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
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_20);
return x_29;
}
block_36:
{
if (lean_obj_tag(x_10) == 0)
{
x_20 = x_33;
x_21 = x_32;
x_22 = x_31;
x_23 = x_6;
goto block_30;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_10, 0);
x_35 = l_Lake_joinRelative(x_6, x_34);
x_20 = x_33;
x_21 = x_32;
x_22 = x_31;
x_23 = x_35;
goto block_30;
}
}
block_101:
{
lean_object* x_39; 
lean_inc(x_9);
lean_inc_ref(x_38);
lean_inc_ref(x_37);
lean_inc_ref(x_11);
x_39 = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at_____private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(x_11, x_5, x_37, x_38, x_9, x_12);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_39, 1);
x_42 = lean_ctor_get(x_39, 0);
lean_dec(x_42);
x_43 = lean_unsigned_to_nat(0u);
x_44 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
x_45 = l_Lake_GitRepo_getHeadRevision(x_37, x_44, x_41);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
lean_free_object(x_39);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec_ref(x_45);
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec_ref(x_46);
x_50 = lean_array_get_size(x_49);
x_51 = lean_nat_dec_lt(x_43, x_50);
if (x_51 == 0)
{
lean_dec(x_50);
lean_dec(x_49);
lean_dec_ref(x_11);
x_31 = x_38;
x_32 = x_48;
x_33 = x_47;
goto block_36;
}
else
{
uint8_t x_52; 
x_52 = lean_nat_dec_le(x_50, x_50);
if (x_52 == 0)
{
lean_dec(x_50);
lean_dec(x_49);
lean_dec_ref(x_11);
x_31 = x_38;
x_32 = x_48;
x_33 = x_47;
goto block_36;
}
else
{
lean_object* x_53; size_t x_54; size_t x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_box(0);
x_54 = 0;
x_55 = lean_usize_of_nat(x_50);
lean_dec(x_50);
x_56 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_49, x_54, x_55, x_53, x_11, x_47);
lean_dec(x_49);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec_ref(x_56);
x_31 = x_38;
x_32 = x_48;
x_33 = x_57;
goto block_36;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
lean_dec_ref(x_38);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
x_58 = lean_ctor_get(x_45, 1);
lean_inc(x_58);
lean_dec_ref(x_45);
x_59 = lean_ctor_get(x_46, 1);
lean_inc(x_59);
lean_dec_ref(x_46);
x_60 = lean_array_get_size(x_59);
x_61 = lean_nat_dec_lt(x_43, x_60);
if (x_61 == 0)
{
lean_object* x_62; 
lean_dec(x_60);
lean_dec(x_59);
lean_dec_ref(x_11);
x_62 = lean_box(0);
lean_ctor_set_tag(x_39, 1);
lean_ctor_set(x_39, 1, x_58);
lean_ctor_set(x_39, 0, x_62);
return x_39;
}
else
{
uint8_t x_63; 
lean_free_object(x_39);
x_63 = lean_nat_dec_le(x_60, x_60);
if (x_63 == 0)
{
lean_dec(x_60);
lean_dec(x_59);
lean_dec_ref(x_11);
x_13 = x_58;
goto block_16;
}
else
{
lean_object* x_64; size_t x_65; size_t x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_box(0);
x_65 = 0;
x_66 = lean_usize_of_nat(x_60);
lean_dec(x_60);
x_67 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_59, x_65, x_66, x_64, x_11, x_58);
lean_dec(x_59);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec_ref(x_67);
x_13 = x_68;
goto block_16;
}
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_69 = lean_ctor_get(x_39, 1);
lean_inc(x_69);
lean_dec(x_39);
x_70 = lean_unsigned_to_nat(0u);
x_71 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
x_72 = l_Lake_GitRepo_getHeadRevision(x_37, x_71, x_69);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec_ref(x_72);
x_75 = lean_ctor_get(x_73, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_dec_ref(x_73);
x_77 = lean_array_get_size(x_76);
x_78 = lean_nat_dec_lt(x_70, x_77);
if (x_78 == 0)
{
lean_dec(x_77);
lean_dec(x_76);
lean_dec_ref(x_11);
x_31 = x_38;
x_32 = x_75;
x_33 = x_74;
goto block_36;
}
else
{
uint8_t x_79; 
x_79 = lean_nat_dec_le(x_77, x_77);
if (x_79 == 0)
{
lean_dec(x_77);
lean_dec(x_76);
lean_dec_ref(x_11);
x_31 = x_38;
x_32 = x_75;
x_33 = x_74;
goto block_36;
}
else
{
lean_object* x_80; size_t x_81; size_t x_82; lean_object* x_83; lean_object* x_84; 
x_80 = lean_box(0);
x_81 = 0;
x_82 = lean_usize_of_nat(x_77);
lean_dec(x_77);
x_83 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_76, x_81, x_82, x_80, x_11, x_74);
lean_dec(x_76);
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
lean_dec_ref(x_83);
x_31 = x_38;
x_32 = x_75;
x_33 = x_84;
goto block_36;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
lean_dec_ref(x_38);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
x_85 = lean_ctor_get(x_72, 1);
lean_inc(x_85);
lean_dec_ref(x_72);
x_86 = lean_ctor_get(x_73, 1);
lean_inc(x_86);
lean_dec_ref(x_73);
x_87 = lean_array_get_size(x_86);
x_88 = lean_nat_dec_lt(x_70, x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
lean_dec(x_87);
lean_dec(x_86);
lean_dec_ref(x_11);
x_89 = lean_box(0);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_85);
return x_90;
}
else
{
uint8_t x_91; 
x_91 = lean_nat_dec_le(x_87, x_87);
if (x_91 == 0)
{
lean_dec(x_87);
lean_dec(x_86);
lean_dec_ref(x_11);
x_13 = x_85;
goto block_16;
}
else
{
lean_object* x_92; size_t x_93; size_t x_94; lean_object* x_95; lean_object* x_96; 
x_92 = lean_box(0);
x_93 = 0;
x_94 = lean_usize_of_nat(x_87);
lean_dec(x_87);
x_95 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_86, x_93, x_94, x_92, x_11, x_85);
lean_dec(x_86);
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
lean_dec_ref(x_95);
x_13 = x_96;
goto block_16;
}
}
}
}
}
else
{
uint8_t x_97; 
lean_dec_ref(x_38);
lean_dec_ref(x_37);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
x_97 = !lean_is_exclusive(x_39);
if (x_97 == 0)
{
return x_39;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_39, 0);
x_99 = lean_ctor_get(x_39, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_39);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
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
x_14 = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lake_Dependency_materialize_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
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
x_11 = l_Lake_instDecidableEqStdVer_decEq(x_10, x_1);
lean_dec_ref(x_10);
if (x_11 == 0)
{
size_t x_12; size_t x_13; 
lean_dec_ref(x_9);
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
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___Lake_Dependency_materialize_spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_37; lean_object* x_38; lean_object* x_102; 
x_17 = lean_ctor_get(x_4, 5);
x_18 = lean_ctor_get(x_2, 0);
x_19 = lean_ctor_get(x_2, 1);
x_37 = l_Lake_joinRelative(x_5, x_7);
x_102 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lean_NameMap_find_x3f_spec__0___redArg(x_17, x_18);
if (lean_obj_tag(x_102) == 0)
{
x_38 = x_8;
goto block_101;
}
else
{
lean_object* x_103; 
lean_dec_ref(x_8);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
lean_dec_ref(x_102);
x_38 = x_103;
goto block_101;
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
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
x_25 = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0;
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
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_22);
return x_29;
}
block_36:
{
if (lean_obj_tag(x_11) == 0)
{
x_20 = x_31;
x_21 = x_32;
x_22 = x_33;
x_23 = x_7;
goto block_30;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_11, 0);
x_35 = l_Lake_joinRelative(x_7, x_34);
x_20 = x_31;
x_21 = x_32;
x_22 = x_33;
x_23 = x_35;
goto block_30;
}
}
block_101:
{
lean_object* x_39; 
lean_inc(x_10);
lean_inc_ref(x_38);
lean_inc_ref(x_37);
lean_inc_ref(x_1);
x_39 = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at_____private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(x_1, x_6, x_37, x_38, x_10, x_12);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_39, 1);
x_42 = lean_ctor_get(x_39, 0);
lean_dec(x_42);
x_43 = lean_unsigned_to_nat(0u);
x_44 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
x_45 = l_Lake_GitRepo_getHeadRevision(x_37, x_44, x_41);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
lean_free_object(x_39);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec_ref(x_45);
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec_ref(x_46);
x_50 = lean_array_get_size(x_49);
x_51 = lean_nat_dec_lt(x_43, x_50);
if (x_51 == 0)
{
lean_dec(x_50);
lean_dec(x_49);
lean_dec_ref(x_1);
x_31 = x_38;
x_32 = x_48;
x_33 = x_47;
goto block_36;
}
else
{
uint8_t x_52; 
x_52 = lean_nat_dec_le(x_50, x_50);
if (x_52 == 0)
{
lean_dec(x_50);
lean_dec(x_49);
lean_dec_ref(x_1);
x_31 = x_38;
x_32 = x_48;
x_33 = x_47;
goto block_36;
}
else
{
lean_object* x_53; size_t x_54; size_t x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_box(0);
x_54 = 0;
x_55 = lean_usize_of_nat(x_50);
lean_dec(x_50);
x_56 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_49, x_54, x_55, x_53, x_1, x_47);
lean_dec(x_49);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec_ref(x_56);
x_31 = x_38;
x_32 = x_48;
x_33 = x_57;
goto block_36;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
lean_dec_ref(x_38);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
x_58 = lean_ctor_get(x_45, 1);
lean_inc(x_58);
lean_dec_ref(x_45);
x_59 = lean_ctor_get(x_46, 1);
lean_inc(x_59);
lean_dec_ref(x_46);
x_60 = lean_array_get_size(x_59);
x_61 = lean_nat_dec_lt(x_43, x_60);
if (x_61 == 0)
{
lean_object* x_62; 
lean_dec(x_60);
lean_dec(x_59);
lean_dec_ref(x_1);
x_62 = lean_box(0);
lean_ctor_set_tag(x_39, 1);
lean_ctor_set(x_39, 1, x_58);
lean_ctor_set(x_39, 0, x_62);
return x_39;
}
else
{
uint8_t x_63; 
lean_free_object(x_39);
x_63 = lean_nat_dec_le(x_60, x_60);
if (x_63 == 0)
{
lean_dec(x_60);
lean_dec(x_59);
lean_dec_ref(x_1);
x_13 = x_58;
goto block_16;
}
else
{
lean_object* x_64; size_t x_65; size_t x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_box(0);
x_65 = 0;
x_66 = lean_usize_of_nat(x_60);
lean_dec(x_60);
x_67 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_59, x_65, x_66, x_64, x_1, x_58);
lean_dec(x_59);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec_ref(x_67);
x_13 = x_68;
goto block_16;
}
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_69 = lean_ctor_get(x_39, 1);
lean_inc(x_69);
lean_dec(x_39);
x_70 = lean_unsigned_to_nat(0u);
x_71 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
x_72 = l_Lake_GitRepo_getHeadRevision(x_37, x_71, x_69);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec_ref(x_72);
x_75 = lean_ctor_get(x_73, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_dec_ref(x_73);
x_77 = lean_array_get_size(x_76);
x_78 = lean_nat_dec_lt(x_70, x_77);
if (x_78 == 0)
{
lean_dec(x_77);
lean_dec(x_76);
lean_dec_ref(x_1);
x_31 = x_38;
x_32 = x_75;
x_33 = x_74;
goto block_36;
}
else
{
uint8_t x_79; 
x_79 = lean_nat_dec_le(x_77, x_77);
if (x_79 == 0)
{
lean_dec(x_77);
lean_dec(x_76);
lean_dec_ref(x_1);
x_31 = x_38;
x_32 = x_75;
x_33 = x_74;
goto block_36;
}
else
{
lean_object* x_80; size_t x_81; size_t x_82; lean_object* x_83; lean_object* x_84; 
x_80 = lean_box(0);
x_81 = 0;
x_82 = lean_usize_of_nat(x_77);
lean_dec(x_77);
x_83 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_76, x_81, x_82, x_80, x_1, x_74);
lean_dec(x_76);
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
lean_dec_ref(x_83);
x_31 = x_38;
x_32 = x_75;
x_33 = x_84;
goto block_36;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
lean_dec_ref(x_38);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
x_85 = lean_ctor_get(x_72, 1);
lean_inc(x_85);
lean_dec_ref(x_72);
x_86 = lean_ctor_get(x_73, 1);
lean_inc(x_86);
lean_dec_ref(x_73);
x_87 = lean_array_get_size(x_86);
x_88 = lean_nat_dec_lt(x_70, x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
lean_dec(x_87);
lean_dec(x_86);
lean_dec_ref(x_1);
x_89 = lean_box(0);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_85);
return x_90;
}
else
{
uint8_t x_91; 
x_91 = lean_nat_dec_le(x_87, x_87);
if (x_91 == 0)
{
lean_dec(x_87);
lean_dec(x_86);
lean_dec_ref(x_1);
x_13 = x_85;
goto block_16;
}
else
{
lean_object* x_92; size_t x_93; size_t x_94; lean_object* x_95; lean_object* x_96; 
x_92 = lean_box(0);
x_93 = 0;
x_94 = lean_usize_of_nat(x_87);
lean_dec(x_87);
x_95 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_86, x_93, x_94, x_92, x_1, x_85);
lean_dec(x_86);
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
lean_dec_ref(x_95);
x_13 = x_96;
goto block_16;
}
}
}
}
}
else
{
uint8_t x_97; 
lean_dec_ref(x_38);
lean_dec_ref(x_37);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_97 = !lean_is_exclusive(x_39);
if (x_97 == 0)
{
return x_39;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_39, 0);
x_99 = lean_ctor_get(x_39, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_39);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
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
x_1 = lean_mk_string_unchecked("git#", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_Dependency_materialize___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": unsupported dependency version format '", 41, 41);
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
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_51 = lean_ctor_get(x_1, 0);
x_52 = lean_ctor_get(x_1, 1);
x_53 = lean_ctor_get(x_1, 2);
x_54 = lean_ctor_get(x_1, 3);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; uint8_t x_299; lean_object* x_300; lean_object* x_301; 
lean_dec_ref(x_6);
x_128 = lean_string_utf8_byte_size(x_52);
x_129 = lean_unsigned_to_nat(0u);
x_299 = lean_nat_dec_eq(x_128, x_129);
lean_dec(x_128);
if (x_299 == 0)
{
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_315; 
x_315 = lean_box(0);
x_300 = x_315;
x_301 = x_8;
goto block_314;
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_316 = lean_ctor_get(x_53, 0);
x_317 = l_Lake_Dependency_materialize___closed__9;
lean_inc(x_316);
x_318 = l_String_dropPrefix_x3f(x_316, x_317);
if (lean_obj_tag(x_318) == 0)
{
lean_object* x_319; 
x_319 = l_Lake_StdVer_parse(x_316);
if (lean_obj_tag(x_319) == 0)
{
uint8_t x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; uint8_t x_327; lean_object* x_328; lean_object* x_329; uint8_t x_330; 
lean_dec_ref(x_319);
lean_inc(x_316);
lean_inc(x_51);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_320 = 1;
x_321 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_51, x_320);
x_322 = l_Lake_Dependency_materialize___closed__10;
x_323 = lean_string_append(x_321, x_322);
x_324 = lean_string_append(x_323, x_316);
lean_dec(x_316);
x_325 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3;
x_326 = lean_string_append(x_324, x_325);
x_327 = 3;
x_328 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_328, 0, x_326);
lean_ctor_set_uint8(x_328, sizeof(void*)*1, x_327);
x_329 = lean_apply_2(x_7, x_328, x_8);
x_330 = !lean_is_exclusive(x_329);
if (x_330 == 0)
{
lean_object* x_331; lean_object* x_332; 
x_331 = lean_ctor_get(x_329, 0);
lean_dec(x_331);
x_332 = lean_box(0);
lean_ctor_set_tag(x_329, 1);
lean_ctor_set(x_329, 0, x_332);
return x_329;
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_333 = lean_ctor_get(x_329, 1);
lean_inc(x_333);
lean_dec(x_329);
x_334 = lean_box(0);
x_335 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_335, 0, x_334);
lean_ctor_set(x_335, 1, x_333);
return x_335;
}
}
else
{
uint8_t x_336; 
x_336 = !lean_is_exclusive(x_319);
if (x_336 == 0)
{
lean_ctor_set_tag(x_319, 2);
x_300 = x_319;
x_301 = x_8;
goto block_314;
}
else
{
lean_object* x_337; lean_object* x_338; 
x_337 = lean_ctor_get(x_319, 0);
lean_inc(x_337);
lean_dec(x_319);
x_338 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_338, 0, x_337);
x_300 = x_338;
x_301 = x_8;
goto block_314;
}
}
}
else
{
uint8_t x_339; 
x_339 = !lean_is_exclusive(x_318);
if (x_339 == 0)
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; 
x_340 = lean_ctor_get(x_318, 0);
x_341 = lean_ctor_get(x_340, 0);
lean_inc_ref(x_341);
x_342 = lean_ctor_get(x_340, 1);
lean_inc(x_342);
x_343 = lean_ctor_get(x_340, 2);
lean_inc(x_343);
lean_dec(x_340);
x_344 = lean_string_utf8_extract(x_341, x_342, x_343);
lean_dec(x_343);
lean_dec(x_342);
lean_dec_ref(x_341);
lean_ctor_set(x_318, 0, x_344);
x_300 = x_318;
x_301 = x_8;
goto block_314;
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; 
x_345 = lean_ctor_get(x_318, 0);
lean_inc(x_345);
lean_dec(x_318);
x_346 = lean_ctor_get(x_345, 0);
lean_inc_ref(x_346);
x_347 = lean_ctor_get(x_345, 1);
lean_inc(x_347);
x_348 = lean_ctor_get(x_345, 2);
lean_inc(x_348);
lean_dec(x_345);
x_349 = lean_string_utf8_extract(x_346, x_347, x_348);
lean_dec(x_348);
lean_dec(x_347);
lean_dec_ref(x_346);
x_350 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_350, 0, x_349);
x_300 = x_350;
x_301 = x_8;
goto block_314;
}
}
}
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; uint8_t x_354; lean_object* x_355; lean_object* x_356; uint8_t x_357; 
lean_inc(x_51);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_351 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_51, x_299);
x_352 = l_Lake_Dependency_materialize___closed__11;
x_353 = lean_string_append(x_351, x_352);
x_354 = 3;
x_355 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_355, 0, x_353);
lean_ctor_set_uint8(x_355, sizeof(void*)*1, x_354);
x_356 = lean_apply_2(x_7, x_355, x_8);
x_357 = !lean_is_exclusive(x_356);
if (x_357 == 0)
{
lean_object* x_358; lean_object* x_359; 
x_358 = lean_ctor_get(x_356, 0);
lean_dec(x_358);
x_359 = lean_box(0);
lean_ctor_set_tag(x_356, 1);
lean_ctor_set(x_356, 0, x_359);
return x_356;
}
else
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_360 = lean_ctor_get(x_356, 1);
lean_inc(x_360);
lean_dec(x_356);
x_361 = lean_box(0);
x_362 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_362, 0, x_361);
lean_ctor_set(x_362, 1, x_360);
return x_362;
}
}
block_148:
{
lean_object* x_140; uint8_t x_141; 
x_140 = lean_array_get_size(x_138);
x_141 = lean_nat_dec_lt(x_129, x_140);
if (x_141 == 0)
{
lean_dec(x_140);
lean_dec_ref(x_138);
x_77 = x_130;
x_78 = x_131;
x_79 = x_132;
x_80 = x_133;
x_81 = x_134;
x_82 = x_136;
x_83 = x_135;
x_84 = x_137;
x_85 = x_139;
goto block_127;
}
else
{
uint8_t x_142; 
x_142 = lean_nat_dec_le(x_140, x_140);
if (x_142 == 0)
{
lean_dec(x_140);
lean_dec_ref(x_138);
x_77 = x_130;
x_78 = x_131;
x_79 = x_132;
x_80 = x_133;
x_81 = x_134;
x_82 = x_136;
x_83 = x_135;
x_84 = x_137;
x_85 = x_139;
goto block_127;
}
else
{
lean_object* x_143; size_t x_144; size_t x_145; lean_object* x_146; lean_object* x_147; 
x_143 = lean_box(0);
x_144 = 0;
x_145 = lean_usize_of_nat(x_140);
lean_dec(x_140);
lean_inc_ref(x_7);
x_146 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_138, x_144, x_145, x_143, x_7, x_139);
lean_dec_ref(x_138);
x_147 = lean_ctor_get(x_146, 1);
lean_inc(x_147);
lean_dec_ref(x_146);
x_77 = x_130;
x_78 = x_131;
x_79 = x_132;
x_80 = x_133;
x_81 = x_134;
x_82 = x_136;
x_83 = x_135;
x_84 = x_137;
x_85 = x_147;
goto block_127;
}
}
}
block_284:
{
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; 
lean_dec_ref(x_151);
lean_dec(x_149);
lean_inc_ref(x_52);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_153 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0;
x_154 = lean_string_append(x_52, x_153);
x_155 = lean_string_append(x_154, x_150);
lean_dec_ref(x_150);
x_156 = l_Lake_Dependency_materialize___closed__8;
x_157 = lean_string_append(x_155, x_156);
x_158 = 3;
x_159 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set_uint8(x_159, sizeof(void*)*1, x_158);
x_160 = lean_apply_2(x_7, x_159, x_152);
x_161 = !lean_is_exclusive(x_160);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; 
x_162 = lean_ctor_get(x_160, 0);
lean_dec(x_162);
x_163 = lean_box(0);
lean_ctor_set_tag(x_160, 1);
lean_ctor_set(x_160, 0, x_163);
return x_160;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_160, 1);
lean_inc(x_164);
lean_dec(x_160);
x_165 = lean_box(0);
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_164);
return x_166;
}
}
else
{
uint8_t x_167; 
x_167 = !lean_is_exclusive(x_151);
if (x_167 == 0)
{
lean_object* x_168; 
x_168 = lean_ctor_get(x_151, 0);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; uint8_t x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; 
lean_free_object(x_151);
lean_inc_ref(x_52);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_169 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed(x_52, x_150, x_149);
lean_dec_ref(x_150);
x_170 = 3;
x_171 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set_uint8(x_171, sizeof(void*)*1, x_170);
x_172 = lean_apply_2(x_7, x_171, x_152);
x_173 = !lean_is_exclusive(x_172);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; 
x_174 = lean_ctor_get(x_172, 0);
lean_dec(x_174);
x_175 = lean_box(0);
lean_ctor_set_tag(x_172, 1);
lean_ctor_set(x_172, 0, x_175);
return x_172;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_172, 1);
lean_inc(x_176);
lean_dec(x_172);
x_177 = lean_box(0);
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_176);
return x_178;
}
}
else
{
lean_object* x_179; lean_object* x_180; 
x_179 = lean_ctor_get(x_168, 0);
lean_inc(x_179);
lean_dec_ref(x_168);
x_180 = l_Lake_RegistryPkg_gitSrc_x3f(x_179);
if (lean_obj_tag(x_180) == 0)
{
lean_free_object(x_151);
lean_dec_ref(x_150);
lean_dec(x_149);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_13 = x_179;
x_14 = x_7;
x_15 = x_152;
goto block_28;
}
else
{
lean_object* x_181; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
lean_dec_ref(x_180);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_182 = lean_ctor_get(x_181, 1);
lean_inc_ref(x_182);
x_183 = lean_ctor_get(x_181, 2);
lean_inc(x_183);
x_184 = lean_ctor_get(x_181, 3);
lean_inc(x_184);
x_185 = lean_ctor_get(x_181, 4);
lean_inc(x_185);
lean_dec_ref(x_181);
x_186 = lean_ctor_get(x_179, 0);
lean_inc_ref(x_186);
x_187 = lean_ctor_get(x_179, 1);
lean_inc_ref(x_187);
lean_dec(x_179);
x_188 = l_Lake_joinRelative(x_5, x_186);
lean_dec_ref(x_186);
switch (lean_obj_tag(x_149)) {
case 0:
{
lean_object* x_189; 
lean_free_object(x_151);
lean_dec_ref(x_150);
x_189 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
if (lean_obj_tag(x_184) == 0)
{
uint8_t x_190; 
lean_dec_ref(x_188);
lean_dec_ref(x_187);
lean_dec(x_185);
lean_dec(x_183);
lean_dec_ref(x_182);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_190 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6;
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; 
lean_dec_ref(x_7);
x_191 = lean_box(0);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_152);
return x_192;
}
else
{
uint8_t x_193; 
x_193 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
if (x_193 == 0)
{
lean_dec_ref(x_7);
x_9 = x_152;
goto block_12;
}
else
{
lean_object* x_194; size_t x_195; size_t x_196; lean_object* x_197; lean_object* x_198; 
x_194 = lean_box(0);
x_195 = 0;
x_196 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__8;
x_197 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_189, x_195, x_196, x_194, x_7, x_152);
x_198 = lean_ctor_get(x_197, 1);
lean_inc(x_198);
lean_dec_ref(x_197);
x_9 = x_198;
goto block_12;
}
}
}
else
{
lean_object* x_199; uint8_t x_200; 
x_199 = lean_ctor_get(x_184, 0);
lean_inc(x_199);
lean_dec_ref(x_184);
x_200 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6;
if (x_200 == 0)
{
x_40 = x_183;
x_41 = x_187;
x_42 = x_182;
x_43 = x_188;
x_44 = x_185;
x_45 = x_199;
x_46 = x_7;
x_47 = x_152;
goto block_50;
}
else
{
uint8_t x_201; 
x_201 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
if (x_201 == 0)
{
x_40 = x_183;
x_41 = x_187;
x_42 = x_182;
x_43 = x_188;
x_44 = x_185;
x_45 = x_199;
x_46 = x_7;
x_47 = x_152;
goto block_50;
}
else
{
lean_object* x_202; size_t x_203; size_t x_204; lean_object* x_205; lean_object* x_206; 
x_202 = lean_box(0);
x_203 = 0;
x_204 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__8;
lean_inc_ref(x_7);
x_205 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_189, x_203, x_204, x_202, x_7, x_152);
x_206 = lean_ctor_get(x_205, 1);
lean_inc(x_206);
lean_dec_ref(x_205);
x_40 = x_183;
x_41 = x_187;
x_42 = x_182;
x_43 = x_188;
x_44 = x_185;
x_45 = x_199;
x_46 = x_7;
x_47 = x_206;
goto block_50;
}
}
}
}
case 1:
{
lean_object* x_207; lean_object* x_208; uint8_t x_209; 
lean_dec(x_184);
lean_free_object(x_151);
lean_dec_ref(x_150);
x_207 = lean_ctor_get(x_149, 0);
lean_inc_ref(x_207);
lean_dec_ref(x_149);
x_208 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
x_209 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6;
if (x_209 == 0)
{
x_40 = x_183;
x_41 = x_187;
x_42 = x_182;
x_43 = x_188;
x_44 = x_185;
x_45 = x_207;
x_46 = x_7;
x_47 = x_152;
goto block_50;
}
else
{
uint8_t x_210; 
x_210 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
if (x_210 == 0)
{
x_40 = x_183;
x_41 = x_187;
x_42 = x_182;
x_43 = x_188;
x_44 = x_185;
x_45 = x_207;
x_46 = x_7;
x_47 = x_152;
goto block_50;
}
else
{
lean_object* x_211; size_t x_212; size_t x_213; lean_object* x_214; lean_object* x_215; 
x_211 = lean_box(0);
x_212 = 0;
x_213 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__8;
lean_inc_ref(x_7);
x_214 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_208, x_212, x_213, x_211, x_7, x_152);
x_215 = lean_ctor_get(x_214, 1);
lean_inc(x_215);
lean_dec_ref(x_214);
x_40 = x_183;
x_41 = x_187;
x_42 = x_182;
x_43 = x_188;
x_44 = x_185;
x_45 = x_207;
x_46 = x_7;
x_47 = x_215;
goto block_50;
}
}
}
default: 
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec(x_184);
x_216 = lean_ctor_get(x_149, 0);
lean_inc_ref(x_216);
lean_dec_ref(x_149);
x_217 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
lean_inc_ref(x_52);
lean_inc_ref(x_3);
x_218 = l_Lake_Reservoir_fetchPkgVersions(x_3, x_52, x_150, x_217, x_152);
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_220 = lean_ctor_get(x_218, 1);
lean_inc(x_220);
lean_dec_ref(x_218);
x_221 = lean_ctor_get(x_219, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_219, 1);
lean_inc(x_222);
lean_dec_ref(x_219);
lean_ctor_set(x_151, 0, x_221);
x_130 = x_183;
x_131 = x_187;
x_132 = x_216;
x_133 = x_182;
x_134 = x_188;
x_135 = x_150;
x_136 = x_185;
x_137 = x_151;
x_138 = x_222;
x_139 = x_220;
goto block_148;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_223 = lean_ctor_get(x_218, 1);
lean_inc(x_223);
lean_dec_ref(x_218);
x_224 = lean_ctor_get(x_219, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_219, 1);
lean_inc(x_225);
lean_dec_ref(x_219);
lean_ctor_set_tag(x_151, 0);
lean_ctor_set(x_151, 0, x_224);
x_130 = x_183;
x_131 = x_187;
x_132 = x_216;
x_133 = x_182;
x_134 = x_188;
x_135 = x_150;
x_136 = x_185;
x_137 = x_151;
x_138 = x_225;
x_139 = x_223;
goto block_148;
}
}
}
}
else
{
lean_dec_ref(x_181);
lean_free_object(x_151);
lean_dec_ref(x_150);
lean_dec(x_149);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_13 = x_179;
x_14 = x_7;
x_15 = x_152;
goto block_28;
}
}
}
}
else
{
lean_object* x_226; 
x_226 = lean_ctor_get(x_151, 0);
lean_inc(x_226);
lean_dec(x_151);
if (lean_obj_tag(x_226) == 0)
{
lean_object* x_227; uint8_t x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
lean_inc_ref(x_52);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_227 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed(x_52, x_150, x_149);
lean_dec_ref(x_150);
x_228 = 3;
x_229 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_229, 0, x_227);
lean_ctor_set_uint8(x_229, sizeof(void*)*1, x_228);
x_230 = lean_apply_2(x_7, x_229, x_152);
x_231 = lean_ctor_get(x_230, 1);
lean_inc(x_231);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 x_232 = x_230;
} else {
 lean_dec_ref(x_230);
 x_232 = lean_box(0);
}
x_233 = lean_box(0);
if (lean_is_scalar(x_232)) {
 x_234 = lean_alloc_ctor(1, 2, 0);
} else {
 x_234 = x_232;
 lean_ctor_set_tag(x_234, 1);
}
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set(x_234, 1, x_231);
return x_234;
}
else
{
lean_object* x_235; lean_object* x_236; 
x_235 = lean_ctor_get(x_226, 0);
lean_inc(x_235);
lean_dec_ref(x_226);
x_236 = l_Lake_RegistryPkg_gitSrc_x3f(x_235);
if (lean_obj_tag(x_236) == 0)
{
lean_dec_ref(x_150);
lean_dec(x_149);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_13 = x_235;
x_14 = x_7;
x_15 = x_152;
goto block_28;
}
else
{
lean_object* x_237; 
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
lean_dec_ref(x_236);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_238 = lean_ctor_get(x_237, 1);
lean_inc_ref(x_238);
x_239 = lean_ctor_get(x_237, 2);
lean_inc(x_239);
x_240 = lean_ctor_get(x_237, 3);
lean_inc(x_240);
x_241 = lean_ctor_get(x_237, 4);
lean_inc(x_241);
lean_dec_ref(x_237);
x_242 = lean_ctor_get(x_235, 0);
lean_inc_ref(x_242);
x_243 = lean_ctor_get(x_235, 1);
lean_inc_ref(x_243);
lean_dec(x_235);
x_244 = l_Lake_joinRelative(x_5, x_242);
lean_dec_ref(x_242);
switch (lean_obj_tag(x_149)) {
case 0:
{
lean_object* x_245; 
lean_dec_ref(x_150);
x_245 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
if (lean_obj_tag(x_240) == 0)
{
uint8_t x_246; 
lean_dec_ref(x_244);
lean_dec_ref(x_243);
lean_dec(x_241);
lean_dec(x_239);
lean_dec_ref(x_238);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_246 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6;
if (x_246 == 0)
{
lean_object* x_247; lean_object* x_248; 
lean_dec_ref(x_7);
x_247 = lean_box(0);
x_248 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set(x_248, 1, x_152);
return x_248;
}
else
{
uint8_t x_249; 
x_249 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
if (x_249 == 0)
{
lean_dec_ref(x_7);
x_9 = x_152;
goto block_12;
}
else
{
lean_object* x_250; size_t x_251; size_t x_252; lean_object* x_253; lean_object* x_254; 
x_250 = lean_box(0);
x_251 = 0;
x_252 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__8;
x_253 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_245, x_251, x_252, x_250, x_7, x_152);
x_254 = lean_ctor_get(x_253, 1);
lean_inc(x_254);
lean_dec_ref(x_253);
x_9 = x_254;
goto block_12;
}
}
}
else
{
lean_object* x_255; uint8_t x_256; 
x_255 = lean_ctor_get(x_240, 0);
lean_inc(x_255);
lean_dec_ref(x_240);
x_256 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6;
if (x_256 == 0)
{
x_40 = x_239;
x_41 = x_243;
x_42 = x_238;
x_43 = x_244;
x_44 = x_241;
x_45 = x_255;
x_46 = x_7;
x_47 = x_152;
goto block_50;
}
else
{
uint8_t x_257; 
x_257 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
if (x_257 == 0)
{
x_40 = x_239;
x_41 = x_243;
x_42 = x_238;
x_43 = x_244;
x_44 = x_241;
x_45 = x_255;
x_46 = x_7;
x_47 = x_152;
goto block_50;
}
else
{
lean_object* x_258; size_t x_259; size_t x_260; lean_object* x_261; lean_object* x_262; 
x_258 = lean_box(0);
x_259 = 0;
x_260 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__8;
lean_inc_ref(x_7);
x_261 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_245, x_259, x_260, x_258, x_7, x_152);
x_262 = lean_ctor_get(x_261, 1);
lean_inc(x_262);
lean_dec_ref(x_261);
x_40 = x_239;
x_41 = x_243;
x_42 = x_238;
x_43 = x_244;
x_44 = x_241;
x_45 = x_255;
x_46 = x_7;
x_47 = x_262;
goto block_50;
}
}
}
}
case 1:
{
lean_object* x_263; lean_object* x_264; uint8_t x_265; 
lean_dec(x_240);
lean_dec_ref(x_150);
x_263 = lean_ctor_get(x_149, 0);
lean_inc_ref(x_263);
lean_dec_ref(x_149);
x_264 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
x_265 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6;
if (x_265 == 0)
{
x_40 = x_239;
x_41 = x_243;
x_42 = x_238;
x_43 = x_244;
x_44 = x_241;
x_45 = x_263;
x_46 = x_7;
x_47 = x_152;
goto block_50;
}
else
{
uint8_t x_266; 
x_266 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
if (x_266 == 0)
{
x_40 = x_239;
x_41 = x_243;
x_42 = x_238;
x_43 = x_244;
x_44 = x_241;
x_45 = x_263;
x_46 = x_7;
x_47 = x_152;
goto block_50;
}
else
{
lean_object* x_267; size_t x_268; size_t x_269; lean_object* x_270; lean_object* x_271; 
x_267 = lean_box(0);
x_268 = 0;
x_269 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__8;
lean_inc_ref(x_7);
x_270 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_264, x_268, x_269, x_267, x_7, x_152);
x_271 = lean_ctor_get(x_270, 1);
lean_inc(x_271);
lean_dec_ref(x_270);
x_40 = x_239;
x_41 = x_243;
x_42 = x_238;
x_43 = x_244;
x_44 = x_241;
x_45 = x_263;
x_46 = x_7;
x_47 = x_271;
goto block_50;
}
}
}
default: 
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
lean_dec(x_240);
x_272 = lean_ctor_get(x_149, 0);
lean_inc_ref(x_272);
lean_dec_ref(x_149);
x_273 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
lean_inc_ref(x_52);
lean_inc_ref(x_3);
x_274 = l_Lake_Reservoir_fetchPkgVersions(x_3, x_52, x_150, x_273, x_152);
x_275 = lean_ctor_get(x_274, 0);
lean_inc(x_275);
if (lean_obj_tag(x_275) == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_276 = lean_ctor_get(x_274, 1);
lean_inc(x_276);
lean_dec_ref(x_274);
x_277 = lean_ctor_get(x_275, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_275, 1);
lean_inc(x_278);
lean_dec_ref(x_275);
x_279 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_279, 0, x_277);
x_130 = x_239;
x_131 = x_243;
x_132 = x_272;
x_133 = x_238;
x_134 = x_244;
x_135 = x_150;
x_136 = x_241;
x_137 = x_279;
x_138 = x_278;
x_139 = x_276;
goto block_148;
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_280 = lean_ctor_get(x_274, 1);
lean_inc(x_280);
lean_dec_ref(x_274);
x_281 = lean_ctor_get(x_275, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_275, 1);
lean_inc(x_282);
lean_dec_ref(x_275);
x_283 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_283, 0, x_281);
x_130 = x_239;
x_131 = x_243;
x_132 = x_272;
x_133 = x_238;
x_134 = x_244;
x_135 = x_150;
x_136 = x_241;
x_137 = x_283;
x_138 = x_282;
x_139 = x_280;
goto block_148;
}
}
}
}
else
{
lean_dec_ref(x_237);
lean_dec_ref(x_150);
lean_dec(x_149);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_13 = x_235;
x_14 = x_7;
x_15 = x_152;
goto block_28;
}
}
}
}
}
}
block_298:
{
lean_object* x_290; uint8_t x_291; 
x_290 = lean_array_get_size(x_288);
x_291 = lean_nat_dec_lt(x_129, x_290);
if (x_291 == 0)
{
lean_dec(x_290);
lean_dec_ref(x_288);
x_149 = x_285;
x_150 = x_286;
x_151 = x_287;
x_152 = x_289;
goto block_284;
}
else
{
uint8_t x_292; 
x_292 = lean_nat_dec_le(x_290, x_290);
if (x_292 == 0)
{
lean_dec(x_290);
lean_dec_ref(x_288);
x_149 = x_285;
x_150 = x_286;
x_151 = x_287;
x_152 = x_289;
goto block_284;
}
else
{
lean_object* x_293; size_t x_294; size_t x_295; lean_object* x_296; lean_object* x_297; 
x_293 = lean_box(0);
x_294 = 0;
x_295 = lean_usize_of_nat(x_290);
lean_dec(x_290);
lean_inc_ref(x_7);
x_296 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_288, x_294, x_295, x_293, x_7, x_289);
lean_dec_ref(x_288);
x_297 = lean_ctor_get(x_296, 1);
lean_inc(x_297);
lean_dec_ref(x_296);
x_149 = x_285;
x_150 = x_286;
x_151 = x_287;
x_152 = x_297;
goto block_284;
}
}
}
block_314:
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; 
lean_inc(x_51);
x_302 = l_Lean_Name_toString(x_51, x_299);
x_303 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
lean_inc_ref(x_52);
lean_inc_ref(x_3);
x_304 = l_Lake_Reservoir_fetchPkg_x3f(x_3, x_52, x_302, x_303, x_301);
x_305 = lean_ctor_get(x_304, 0);
lean_inc(x_305);
if (lean_obj_tag(x_305) == 0)
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_306 = lean_ctor_get(x_304, 1);
lean_inc(x_306);
lean_dec_ref(x_304);
x_307 = lean_ctor_get(x_305, 0);
lean_inc(x_307);
x_308 = lean_ctor_get(x_305, 1);
lean_inc(x_308);
lean_dec_ref(x_305);
x_309 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_309, 0, x_307);
x_285 = x_300;
x_286 = x_302;
x_287 = x_309;
x_288 = x_308;
x_289 = x_306;
goto block_298;
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_310 = lean_ctor_get(x_304, 1);
lean_inc(x_310);
lean_dec_ref(x_304);
x_311 = lean_ctor_get(x_305, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_305, 1);
lean_inc(x_312);
lean_dec_ref(x_305);
x_313 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_313, 0, x_311);
x_285 = x_300;
x_286 = x_302;
x_287 = x_313;
x_288 = x_312;
x_289 = x_310;
goto block_298;
}
}
}
else
{
lean_object* x_363; 
x_363 = lean_ctor_get(x_54, 0);
lean_inc(x_363);
if (lean_obj_tag(x_363) == 0)
{
uint8_t x_364; 
lean_inc_ref(x_52);
lean_inc(x_51);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_364 = !lean_is_exclusive(x_363);
if (x_364 == 0)
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; 
x_365 = lean_ctor_get(x_363, 0);
x_366 = l_Lake_joinRelative(x_6, x_365);
lean_dec_ref(x_365);
x_367 = l_Lake_instInhabitedMaterializedDep_default___closed__1;
lean_inc_ref(x_366);
lean_ctor_set(x_363, 0, x_366);
x_368 = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0;
x_369 = lean_box(0);
x_370 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_370, 0, x_51);
lean_ctor_set(x_370, 1, x_52);
lean_ctor_set(x_370, 2, x_368);
lean_ctor_set(x_370, 3, x_369);
lean_ctor_set(x_370, 4, x_363);
lean_ctor_set_uint8(x_370, sizeof(void*)*5, x_2);
x_371 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_371, 0, x_366);
lean_ctor_set(x_371, 1, x_367);
lean_ctor_set(x_371, 2, x_370);
x_372 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_372, 0, x_371);
lean_ctor_set(x_372, 1, x_8);
return x_372;
}
else
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_373 = lean_ctor_get(x_363, 0);
lean_inc(x_373);
lean_dec(x_363);
x_374 = l_Lake_joinRelative(x_6, x_373);
lean_dec_ref(x_373);
x_375 = l_Lake_instInhabitedMaterializedDep_default___closed__1;
lean_inc_ref(x_374);
x_376 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_376, 0, x_374);
x_377 = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0;
x_378 = lean_box(0);
x_379 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_379, 0, x_51);
lean_ctor_set(x_379, 1, x_52);
lean_ctor_set(x_379, 2, x_377);
lean_ctor_set(x_379, 3, x_378);
lean_ctor_set(x_379, 4, x_376);
lean_ctor_set_uint8(x_379, sizeof(void*)*5, x_2);
x_380 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_380, 0, x_374);
lean_ctor_set(x_380, 1, x_375);
lean_ctor_set(x_380, 2, x_379);
x_381 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_381, 0, x_380);
lean_ctor_set(x_381, 1, x_8);
return x_381;
}
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; uint8_t x_385; lean_object* x_386; lean_object* x_387; lean_object* x_391; 
lean_dec_ref(x_6);
x_382 = lean_ctor_get(x_363, 0);
lean_inc_ref(x_382);
x_383 = lean_ctor_get(x_363, 1);
lean_inc(x_383);
x_384 = lean_ctor_get(x_363, 2);
lean_inc(x_384);
lean_dec_ref(x_363);
x_385 = 0;
lean_inc(x_51);
x_386 = l_Lean_Name_toString(x_51, x_385);
lean_inc_ref(x_382);
x_391 = l_Lake_Git_filterUrl_x3f(x_382);
if (lean_obj_tag(x_391) == 0)
{
lean_object* x_392; 
x_392 = l_Lake_instInhabitedMaterializedDep_default___closed__1;
x_387 = x_392;
goto block_390;
}
else
{
lean_object* x_393; 
x_393 = lean_ctor_get(x_391, 0);
lean_inc(x_393);
lean_dec_ref(x_391);
x_387 = x_393;
goto block_390;
}
block_390:
{
lean_object* x_388; lean_object* x_389; 
x_388 = l_Lake_joinRelative(x_5, x_386);
x_389 = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___Lake_Dependency_materialize_spec__1(x_7, x_1, x_2, x_3, x_4, x_386, x_388, x_382, x_387, x_383, x_384, x_8);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_389;
}
}
}
block_12:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
block_28:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc_ref(x_16);
lean_dec_ref(x_13);
x_17 = l_Lake_Dependency_materialize___closed__0;
x_18 = lean_string_append(x_16, x_17);
x_19 = 3;
x_20 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*1, x_19);
x_21 = lean_apply_2(x_14, x_20, x_15);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
x_24 = lean_box(0);
lean_ctor_set_tag(x_21, 1);
lean_ctor_set(x_21, 0, x_24);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
block_39:
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_33);
x_38 = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit(x_1, x_2, x_3, x_4, x_30, x_32, x_31, x_36, x_37, x_35, x_29, x_34);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_38;
}
block_50:
{
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_48; 
x_48 = l_Lake_instInhabitedMaterializedDep_default___closed__1;
x_29 = x_46;
x_30 = x_41;
x_31 = x_42;
x_32 = x_43;
x_33 = x_45;
x_34 = x_47;
x_35 = x_44;
x_36 = x_48;
goto block_39;
}
else
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_40, 0);
lean_inc(x_49);
lean_dec_ref(x_40);
x_29 = x_46;
x_30 = x_41;
x_31 = x_42;
x_32 = x_43;
x_33 = x_45;
x_34 = x_47;
x_35 = x_44;
x_36 = x_49;
goto block_39;
}
}
block_76:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_58 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0;
x_59 = lean_string_append(x_52, x_58);
x_60 = lean_string_append(x_59, x_57);
lean_dec_ref(x_57);
x_61 = l_Lake_Dependency_materialize___closed__1;
x_62 = lean_string_append(x_60, x_61);
x_63 = l_Lake_StdVer_toString(x_56);
x_64 = lean_string_append(x_62, x_63);
lean_dec_ref(x_63);
x_65 = l_Lake_Dependency_materialize___closed__2;
x_66 = lean_string_append(x_64, x_65);
x_67 = 3;
x_68 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set_uint8(x_68, sizeof(void*)*1, x_67);
x_69 = lean_apply_2(x_7, x_68, x_55);
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_69, 0);
lean_dec(x_71);
x_72 = lean_box(0);
lean_ctor_set_tag(x_69, 1);
lean_ctor_set(x_69, 0, x_72);
return x_69;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_69, 1);
lean_inc(x_73);
lean_dec(x_69);
x_74 = lean_box(0);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
block_127:
{
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
lean_dec_ref(x_84);
lean_dec(x_82);
lean_dec_ref(x_81);
lean_dec_ref(x_80);
lean_dec_ref(x_79);
lean_dec_ref(x_78);
lean_dec(x_77);
lean_inc_ref(x_52);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_86 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0;
x_87 = lean_string_append(x_52, x_86);
x_88 = lean_string_append(x_87, x_83);
lean_dec_ref(x_83);
x_89 = l_Lake_Dependency_materialize___closed__3;
x_90 = lean_string_append(x_88, x_89);
x_91 = 3;
x_92 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set_uint8(x_92, sizeof(void*)*1, x_91);
x_93 = lean_apply_2(x_7, x_92, x_85);
x_94 = !lean_is_exclusive(x_93);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_93, 0);
lean_dec(x_95);
x_96 = lean_box(0);
lean_ctor_set_tag(x_93, 1);
lean_ctor_set(x_93, 0, x_96);
return x_93;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_93, 1);
lean_inc(x_97);
lean_dec(x_93);
x_98 = lean_box(0);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_97);
return x_99;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; size_t x_103; size_t x_104; lean_object* x_105; lean_object* x_106; 
x_100 = lean_ctor_get(x_84, 0);
lean_inc(x_100);
lean_dec_ref(x_84);
x_101 = lean_box(0);
x_102 = l_Lake_Dependency_materialize___closed__4;
x_103 = lean_array_size(x_100);
x_104 = 0;
x_105 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lake_Dependency_materialize_spec__0(x_79, x_102, x_101, x_100, x_103, x_104, x_102);
lean_dec(x_100);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
lean_dec_ref(x_105);
if (lean_obj_tag(x_106) == 0)
{
lean_dec(x_82);
lean_dec_ref(x_81);
lean_dec_ref(x_80);
lean_dec_ref(x_78);
lean_dec(x_77);
lean_inc_ref(x_52);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_55 = x_85;
x_56 = x_79;
x_57 = x_83;
goto block_76;
}
else
{
lean_object* x_107; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
lean_dec_ref(x_106);
if (lean_obj_tag(x_107) == 0)
{
lean_dec(x_82);
lean_dec_ref(x_81);
lean_dec_ref(x_80);
lean_dec_ref(x_78);
lean_dec(x_77);
lean_inc_ref(x_52);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_55 = x_85;
x_56 = x_79;
x_57 = x_83;
goto block_76;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec_ref(x_79);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
lean_dec_ref(x_107);
x_109 = lean_ctor_get(x_108, 0);
lean_inc_ref(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc_ref(x_110);
lean_dec(x_108);
x_111 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0;
lean_inc_ref(x_52);
x_112 = lean_string_append(x_52, x_111);
x_113 = lean_string_append(x_112, x_83);
lean_dec_ref(x_83);
x_114 = l_Lake_Dependency_materialize___closed__5;
x_115 = lean_string_append(x_113, x_114);
x_116 = l_Lake_StdVer_toString(x_109);
x_117 = lean_string_append(x_115, x_116);
lean_dec_ref(x_116);
x_118 = l_Lake_Dependency_materialize___closed__6;
x_119 = lean_string_append(x_117, x_118);
x_120 = lean_string_append(x_119, x_110);
x_121 = l_Lake_Dependency_materialize___closed__7;
x_122 = lean_string_append(x_120, x_121);
x_123 = 1;
x_124 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set_uint8(x_124, sizeof(void*)*1, x_123);
lean_inc_ref(x_7);
x_125 = lean_apply_2(x_7, x_124, x_85);
x_126 = lean_ctor_get(x_125, 1);
lean_inc(x_126);
lean_dec_ref(x_125);
x_40 = x_77;
x_41 = x_78;
x_42 = x_80;
x_43 = x_81;
x_44 = x_82;
x_45 = x_110;
x_46 = x_7;
x_47 = x_126;
goto block_50;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lake_Dependency_materialize_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lake_Dependency_materialize_spec__0(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___Lake_Dependency_materialize_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
x_14 = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___Lake_Dependency_materialize_spec__1(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l_Lake_Dependency_materialize(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_13; 
x_13 = lean_ctor_get(x_1, 4);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_14 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_14);
x_15 = l_Lake_instInhabitedMaterializedDep_default___closed__1;
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_16, 2, x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_6);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_46; lean_object* x_47; uint8_t x_56; lean_object* x_57; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_121; uint8_t x_122; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
x_21 = lean_ctor_get(x_13, 3);
x_28 = 0;
lean_inc(x_18);
x_29 = l_Lean_Name_toString(x_18, x_28);
x_30 = l_Lake_joinRelative(x_4, x_29);
x_35 = l_Lake_joinRelative(x_3, x_30);
x_97 = l_System_FilePath_isDir(x_35, x_6);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec_ref(x_97);
x_121 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
x_122 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6;
if (x_122 == 0)
{
x_100 = x_99;
goto block_120;
}
else
{
uint8_t x_123; 
x_123 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
if (x_123 == 0)
{
x_100 = x_99;
goto block_120;
}
else
{
lean_object* x_124; size_t x_125; size_t x_126; lean_object* x_127; lean_object* x_128; 
x_124 = lean_box(0);
x_125 = 0;
x_126 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__8;
lean_inc_ref(x_5);
x_127 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_121, x_125, x_126, x_124, x_5, x_99);
x_128 = lean_ctor_get(x_127, 1);
lean_inc(x_128);
lean_dec_ref(x_127);
x_100 = x_128;
goto block_120;
}
}
block_27:
{
lean_object* x_24; 
lean_inc_ref(x_19);
x_24 = l_Lake_Git_filterUrl_x3f(x_19);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = l_Lake_instInhabitedMaterializedDep_default___closed__1;
x_7 = x_22;
x_8 = x_23;
x_9 = x_25;
goto block_12;
}
else
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec_ref(x_24);
x_7 = x_22;
x_8 = x_23;
x_9 = x_26;
goto block_12;
}
}
block_34:
{
if (lean_obj_tag(x_21) == 0)
{
x_22 = x_31;
x_23 = x_30;
goto block_27;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_21, 0);
x_33 = l_Lake_joinRelative(x_30, x_32);
x_22 = x_31;
x_23 = x_33;
goto block_27;
}
}
block_45:
{
lean_object* x_39; 
x_39 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at_____private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(x_5, x_29, x_35, x_38, x_36, x_37);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec_ref(x_39);
x_31 = x_40;
goto block_34;
}
else
{
uint8_t x_41; 
lean_dec_ref(x_30);
lean_dec_ref(x_1);
x_41 = !lean_is_exclusive(x_39);
if (x_41 == 0)
{
return x_39;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_39, 0);
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_39);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
block_55:
{
lean_object* x_48; lean_object* x_49; 
lean_inc_ref(x_20);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_20);
x_49 = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at_____private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(x_5, x_29, x_35, x_47, x_48, x_46);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec_ref(x_49);
x_31 = x_50;
goto block_34;
}
else
{
uint8_t x_51; 
lean_dec_ref(x_30);
lean_dec_ref(x_1);
x_51 = !lean_is_exclusive(x_49);
if (x_51 == 0)
{
return x_49;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_49, 0);
x_53 = lean_ctor_get(x_49, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_49);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
block_67:
{
if (x_56 == 0)
{
lean_dec_ref(x_35);
lean_dec_ref(x_29);
lean_dec_ref(x_5);
x_31 = x_57;
goto block_34;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_58 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0;
x_59 = lean_string_append(x_29, x_58);
x_60 = lean_string_append(x_59, x_35);
lean_dec_ref(x_35);
x_61 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1;
x_62 = lean_string_append(x_60, x_61);
x_63 = 2;
x_64 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set_uint8(x_64, sizeof(void*)*1, x_63);
x_65 = lean_apply_2(x_5, x_64, x_57);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec_ref(x_65);
x_31 = x_66;
goto block_34;
}
}
block_80:
{
lean_object* x_72; uint8_t x_73; 
x_72 = lean_array_get_size(x_69);
x_73 = lean_nat_dec_lt(x_68, x_72);
if (x_73 == 0)
{
lean_dec(x_72);
lean_dec_ref(x_69);
x_56 = x_70;
x_57 = x_71;
goto block_67;
}
else
{
uint8_t x_74; 
x_74 = lean_nat_dec_le(x_72, x_72);
if (x_74 == 0)
{
lean_dec(x_72);
lean_dec_ref(x_69);
x_56 = x_70;
x_57 = x_71;
goto block_67;
}
else
{
lean_object* x_75; size_t x_76; size_t x_77; lean_object* x_78; lean_object* x_79; 
x_75 = lean_box(0);
x_76 = 0;
x_77 = lean_usize_of_nat(x_72);
lean_dec(x_72);
lean_inc_ref(x_5);
x_78 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_69, x_76, x_77, x_75, x_5, x_71);
lean_dec_ref(x_69);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec_ref(x_78);
x_56 = x_70;
x_57 = x_79;
goto block_67;
}
}
}
block_96:
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_84 = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
lean_inc_ref(x_20);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_20);
lean_inc_ref(x_85);
x_86 = l_Option_instDecidableEq_decEq___redArg(x_84, x_82, x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_2, 5);
x_88 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lean_NameMap_find_x3f_spec__0___redArg(x_87, x_18);
if (lean_obj_tag(x_88) == 0)
{
lean_inc_ref(x_19);
x_36 = x_85;
x_37 = x_83;
x_38 = x_19;
goto block_45;
}
else
{
lean_object* x_89; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
lean_dec_ref(x_88);
x_36 = x_85;
x_37 = x_83;
x_38 = x_89;
goto block_45;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
lean_dec_ref(x_85);
lean_inc_ref(x_35);
x_90 = l_Lake_GitRepo_hasNoDiff(x_35, x_83);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec_ref(x_90);
x_93 = lean_unsigned_to_nat(0u);
x_94 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
x_95 = lean_unbox(x_91);
lean_dec(x_91);
if (x_95 == 0)
{
x_68 = x_93;
x_69 = x_94;
x_70 = x_81;
x_71 = x_92;
goto block_80;
}
else
{
x_68 = x_93;
x_69 = x_94;
x_70 = x_28;
x_71 = x_92;
goto block_80;
}
}
}
block_120:
{
uint8_t x_101; 
x_101 = lean_unbox(x_98);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_98);
x_102 = lean_ctor_get(x_2, 5);
x_103 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lean_NameMap_find_x3f_spec__0___redArg(x_102, x_18);
if (lean_obj_tag(x_103) == 0)
{
lean_inc_ref(x_19);
x_46 = x_100;
x_47 = x_19;
goto block_55;
}
else
{
lean_object* x_104; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
lean_dec_ref(x_103);
x_46 = x_100;
x_47 = x_104;
goto block_55;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_105 = l_Lake_PackageEntry_materialize___closed__0;
lean_inc_ref(x_35);
x_106 = l_Lake_GitRepo_resolveRevision_x3f(x_105, x_35, x_100);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec_ref(x_106);
x_109 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
x_110 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6;
if (x_110 == 0)
{
uint8_t x_111; 
x_111 = lean_unbox(x_98);
lean_dec(x_98);
x_81 = x_111;
x_82 = x_107;
x_83 = x_108;
goto block_96;
}
else
{
uint8_t x_112; 
x_112 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
if (x_112 == 0)
{
uint8_t x_113; 
x_113 = lean_unbox(x_98);
lean_dec(x_98);
x_81 = x_113;
x_82 = x_107;
x_83 = x_108;
goto block_96;
}
else
{
lean_object* x_114; size_t x_115; size_t x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_114 = lean_box(0);
x_115 = 0;
x_116 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__8;
lean_inc_ref(x_5);
x_117 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_109, x_115, x_116, x_114, x_5, x_108);
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
lean_dec_ref(x_117);
x_119 = lean_unbox(x_98);
lean_dec(x_98);
x_81 = x_119;
x_82 = x_107;
x_83 = x_118;
goto block_96;
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
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_PackageEntry_materialize(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_2);
return x_7;
}
}
lean_object* initialize_Lake_Config_Env(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Load_Manifest(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_Package(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Git(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_Dependency(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Reservoir(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Load_Materialize(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Config_Env(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Manifest(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Package(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Git(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Dependency(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Reservoir(builtin, lean_io_mk_world());
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
l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__5 = _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__5();
lean_mark_persistent(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__5);
l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___closed__0 = _init_l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___closed__0();
lean_mark_persistent(l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___closed__0);
l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__0 = _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__0();
l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__1 = _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__1();
lean_mark_persistent(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__1);
l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__2 = _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__2();
lean_mark_persistent(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__2);
l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__3 = _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__3();
lean_mark_persistent(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__3);
l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4 = _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4();
lean_mark_persistent(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4);
l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5 = _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5();
lean_mark_persistent(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6 = _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6();
l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7 = _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7();
l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__8 = _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__8();
l_Lake_instInhabitedMaterializedDep_default___closed__0 = _init_l_Lake_instInhabitedMaterializedDep_default___closed__0();
lean_mark_persistent(l_Lake_instInhabitedMaterializedDep_default___closed__0);
l_Lake_instInhabitedMaterializedDep_default___closed__1 = _init_l_Lake_instInhabitedMaterializedDep_default___closed__1();
lean_mark_persistent(l_Lake_instInhabitedMaterializedDep_default___closed__1);
l_Lake_instInhabitedMaterializedDep_default___closed__2 = _init_l_Lake_instInhabitedMaterializedDep_default___closed__2();
lean_mark_persistent(l_Lake_instInhabitedMaterializedDep_default___closed__2);
l_Lake_instInhabitedMaterializedDep_default___closed__3 = _init_l_Lake_instInhabitedMaterializedDep_default___closed__3();
lean_mark_persistent(l_Lake_instInhabitedMaterializedDep_default___closed__3);
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
l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__8 = _init_l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__8();
lean_mark_persistent(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__8);
l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__9 = _init_l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__9();
lean_mark_persistent(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__9);
l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0 = _init_l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0();
lean_mark_persistent(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0);
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

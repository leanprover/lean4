// Lean compiler output
// Module: Lake.CLI.Translate.Toml
// Imports: Init Lake.Toml.Encode Lake.Config.Package
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Toml_encodeLeanOptions___spec__1(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lake_Dependency_toToml___closed__9;
LEAN_EXPORT lean_object* l_Lake_instToTomlBuildType(uint8_t);
static lean_object* l_Lake_Package_mkTomlConfig___closed__14;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lake_LeanConfig_toToml___closed__15;
LEAN_EXPORT lean_object* l_Lake_instToTomlBuildType___boxed(lean_object*);
static lean_object* l_Lake_Package_mkTomlConfig___closed__9;
static lean_object* l_Lake_LeanLibConfig_toToml___closed__2;
static lean_object* l_Lake_PackageConfig_toToml___closed__12;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Package_mkTomlConfig___spec__3(size_t, size_t, lean_object*);
static lean_object* l_Lake_Package_mkTomlConfig___closed__15;
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toToml(lean_object*, lean_object*);
extern lean_object* l_Lake_defaultBuildDir;
lean_object* l_System_FilePath_normalize(lean_object*);
static lean_object* l_Lake_PackageConfig_toToml___closed__17;
static lean_object* l_Lake_LeanLibConfig_toToml___closed__4;
LEAN_EXPORT lean_object* l_Lake_Dependency_toToml(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToTomlBackend(uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_instBEqFilePath__lake___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_LeanConfig_toToml___closed__3;
static lean_object* l_Lake_Dependency_toToml___closed__3;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lake_Dependency_toToml___closed__4;
static lean_object* l_Lake_Package_mkTomlConfig___closed__2;
static lean_object* l_Lake_PackageConfig_toToml___closed__28;
extern lean_object* l_Lake_defaultPackagesDir;
LEAN_EXPORT lean_object* l_Lake_instToTomlBackend___boxed(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Lake_PackageConfig_toToml___closed__24;
LEAN_EXPORT lean_object* l_Lake_instSmartInsertBackend___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Toml_RBDict_empty___rarg(lean_object*);
static lean_object* l_Lake_PackageConfig_toToml___closed__34;
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at_Lake_LeanLibConfig_toToml___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_PackageConfig_toToml___closed__19;
static lean_object* l_Lake_LeanLibConfig_toToml___closed__3;
LEAN_EXPORT lean_object* l_Lake_Toml_leanOptionsEncoder___elambda__1___boxed(lean_object*);
static lean_object* l_Lake_PackageConfig_toToml___closed__22;
static lean_object* l_Lake_LeanLibConfig_toToml___closed__11;
static lean_object* l_Lake_LeanLibConfig_toToml___closed__1;
static lean_object* l_Lake_PackageConfig_toToml___closed__9;
LEAN_EXPORT lean_object* l_Lake_Toml_encodeLeanOptions___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToTomlGlob(lean_object*);
static lean_object* l_Lake_PackageConfig_toToml___closed__3;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lake_PackageConfig_toToml___closed__29;
LEAN_EXPORT lean_object* l_Lake_Toml_encodeLeanOptionValue(lean_object*);
static lean_object* l_Lake_LeanConfig_toToml___closed__12;
static lean_object* l_Lake_Package_mkTomlConfig___closed__11;
static lean_object* l_Lake_LeanExeConfig_toToml___closed__4;
LEAN_EXPORT lean_object* l_Array_isEqvAux___at_Lake_LeanLibConfig_toToml___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at_Lake_LeanLibConfig_toToml___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instSmartInsertBackend___closed__1;
static lean_object* l_Lake_LeanConfig_toToml___closed__19;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Package_mkTomlConfig___spec__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_PackageConfig_toToml___closed__13;
static lean_object* l_Lake_LeanConfig_toToml___closed__22;
LEAN_EXPORT lean_object* l_Array_isEqvAux___at_Lake_LeanLibConfig_toToml___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToTomlDependency(lean_object*);
static lean_object* l_Lake_LeanConfig_toToml___closed__5;
static lean_object* l_Lake_PackageConfig_toToml___closed__2;
static lean_object* l_Lake_LeanConfig_toToml___closed__20;
static lean_object* l_Lake_LeanExeConfig_toToml___closed__6;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanConfig_toToml___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanConfig_toToml___closed__4;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanLibConfig_toToml___spec__4(size_t, size_t, lean_object*);
static lean_object* l_Lake_LeanConfig_toToml___closed__21;
size_t lean_usize_of_nat(lean_object*);
uint8_t l_String_isEmpty(lean_object*);
static lean_object* l_Lake_Dependency_toToml___closed__7;
lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanLibConfig_globs___default___spec__1(size_t, size_t, lean_object*);
static lean_object* l_Lake_LeanLibConfig_toToml___closed__9;
static lean_object* l_Lake_Package_mkTomlConfig___closed__8;
static lean_object* l_Lake_PackageConfig_toToml___closed__18;
static lean_object* l_Lake_Package_mkTomlConfig___closed__7;
static lean_object* l_Lake_Dependency_toToml___closed__12;
uint8_t l_Lake_instDecidableEqBuildType(uint8_t, uint8_t);
static lean_object* l_Lake_Package_mkTomlConfig___closed__13;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Package_mkTomlConfig___spec__2(size_t, size_t, lean_object*);
static lean_object* l_Lake_LeanExeConfig_toToml___closed__1;
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Name_quickCmp___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_PackageConfig_toToml___closed__20;
static lean_object* l_Lake_LeanExeConfig_toToml___closed__2;
static lean_object* l_Lake_Package_mkTomlConfig___closed__4;
static lean_object* l_Lake_Toml_leanOptionsEncoder___closed__1;
LEAN_EXPORT lean_object* l_Lake_LeanConfig_toToml(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at_Lake_LeanLibConfig_toToml___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanLibConfig_toToml___closed__13;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Package_mkTomlConfig___spec__1(size_t, size_t, lean_object*);
static lean_object* l_Lake_LeanConfig_toToml___closed__11;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanConfig_toToml___spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_CLI_Translate_Toml_0__Lake_instBEqFilePath__lake(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToTomlLeanExeConfig(lean_object*);
static lean_object* l_Lake_LeanLibConfig_toToml___closed__12;
static lean_object* l_Lake_Dependency_toToml___closed__6;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanLibConfig_toToml___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_PackageConfig_toToml___closed__7;
static lean_object* l_Lake_Toml_encodeLeanOptions___closed__1;
static lean_object* l_Lake_WorkspaceConfig_toToml___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanLibConfig_toToml___spec__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Glob_toString(lean_object*);
static lean_object* l_Lake_Dependency_toToml___closed__10;
LEAN_EXPORT lean_object* l_Lake_instToTomlLeanOptionValue;
LEAN_EXPORT lean_object* l_Array_isEqvAux___at_Lake_LeanLibConfig_toToml___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lake_Dependency_toToml___closed__2;
static lean_object* l_Lake_PackageConfig_toToml___closed__16;
static lean_object* l_Lake_LeanConfig_toToml___closed__10;
LEAN_EXPORT lean_object* l_Lake_Toml_leanOptionsEncoder___elambda__1(lean_object*);
static lean_object* l_Lake_LeanConfig_toToml___closed__2;
static lean_object* l_Lake_PackageConfig_toToml___closed__30;
static lean_object* l_Lake_LeanConfig_toToml___closed__13;
static lean_object* l_Lake_Dependency_toToml___closed__1;
static lean_object* l_Lake_LeanExeConfig_toToml___closed__3;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toToml(lean_object*, lean_object*);
static lean_object* l_Lake_WorkspaceConfig_toToml___closed__3;
static lean_object* l_Lake_PackageConfig_toToml___closed__23;
LEAN_EXPORT lean_object* l_Lake_Toml_leanOptionsEncoder;
lean_object* l_Lake_BuildType_toString(uint8_t);
static lean_object* l_Lake_PackageConfig_toToml___closed__6;
static lean_object* l_Lake_PackageConfig_toToml___closed__21;
static lean_object* l_Lake_PackageConfig_toToml___closed__10;
static lean_object* l_Lake_Dependency_toToml___closed__5;
static lean_object* l_Lake_PackageConfig_toToml___closed__14;
static lean_object* l_Lake_LeanConfig_toToml___closed__7;
LEAN_EXPORT uint8_t l_Array_isEqvAux___at_Lake_LeanLibConfig_toToml___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Toml_RBDict_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_encodeLeanOptions(lean_object*);
static lean_object* l_Lake_LeanExeConfig_toToml___closed__5;
static lean_object* l_Lake_PackageConfig_toToml___closed__32;
static lean_object* l_Lake_LeanConfig_toToml___closed__9;
LEAN_EXPORT lean_object* l_Array_isEqvAux___at_Lake_LeanLibConfig_toToml___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_PackageConfig_toToml___closed__33;
static lean_object* l_Lake_Package_mkTomlConfig___closed__3;
static lean_object* l_Lake_LeanConfig_toToml___closed__8;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lake_Dependency_toToml___closed__11;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lake_Dependency_toToml___closed__14;
LEAN_EXPORT uint8_t l_Array_isEqvAux___at_Lake_LeanLibConfig_toToml___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_mkTomlConfig___closed__5;
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lake_Dependency_toToml___spec__1(lean_object*, lean_object*);
static lean_object* l_Lake_Package_mkTomlConfig___closed__6;
static lean_object* l_Lake_Package_mkTomlConfig___closed__12;
static lean_object* l_Lake_Dependency_toToml___closed__8;
LEAN_EXPORT lean_object* l_Lake_WorkspaceConfig_toToml(lean_object*, lean_object*);
static lean_object* l_Lake_WorkspaceConfig_toToml___closed__1;
static lean_object* l_Lake_PackageConfig_toToml___closed__31;
static lean_object* l_Lake_LeanLibConfig_toToml___closed__5;
static lean_object* l_Lake_PackageConfig_toToml___closed__26;
static lean_object* l_Lake_Package_mkTomlConfig___closed__1;
static lean_object* l_Lake_Package_mkTomlConfig___closed__16;
static lean_object* l_Lake_instToTomlLeanOptionValue___closed__1;
static lean_object* l_Lake_LeanLibConfig_toToml___closed__10;
static lean_object* l_Lake_PackageConfig_toToml___closed__4;
static lean_object* l_Lake_LeanConfig_toToml___closed__6;
lean_object* l_Lake_mkRelPathString(lean_object*);
static lean_object* l_Lake_Dependency_toToml___closed__13;
extern lean_object* l_Lake_defaultNativeLibDir;
static lean_object* l_Lake_PackageConfig_toToml___closed__5;
LEAN_EXPORT lean_object* l_Lake_Package_mkTomlConfig(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Package_mkTomlConfig___spec__2___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lake_Config_Glob_0__Lake_decEqGlob____x40_Lake_Config_Glob___hyg_196_(lean_object*, lean_object*);
static lean_object* l_Lake_PackageConfig_toToml___closed__15;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanLibConfig_toToml___spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToTomlLeanConfig(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToTomlLeanLibConfig(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanExeConfig_toToml(lean_object*, lean_object*);
static lean_object* l_Lake_LeanConfig_toToml___closed__17;
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lake_PackageConfig_toToml___closed__25;
lean_object* l_Lake_Backend_toString(uint8_t);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at_Lake_LeanLibConfig_toToml___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lake_LeanLibConfig_toToml___closed__7;
size_t lean_array_size(lean_object*);
static lean_object* l_Lake_Package_mkTomlConfig___closed__10;
static lean_object* l_Lake_PackageConfig_toToml___closed__27;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Package_mkTomlConfig___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Toml_encodeLeanOptions___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lake_PackageConfig_toToml___closed__1;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lake_PackageConfig_toToml___closed__8;
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Name_toStringWithSep(lean_object*, uint8_t, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lake_defaultBinDir;
static lean_object* l_Lake_LeanConfig_toToml___closed__1;
static lean_object* l_Lake_LeanLibConfig_toToml___closed__6;
extern lean_object* l_Lake_defaultIrDir;
static lean_object* l_Lake_LeanLibConfig_toToml___closed__8;
extern lean_object* l_System_Platform_target;
static lean_object* l_Lake_LeanConfig_toToml___closed__16;
LEAN_EXPORT lean_object* l_Lake_instSmartInsertBackend(lean_object*, uint8_t, lean_object*);
static lean_object* l_Lake_PackageConfig_toToml___closed__11;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToTomlPackageConfig(lean_object*);
static lean_object* l_Lake_LeanConfig_toToml___closed__14;
extern lean_object* l_Lake_defaultLeanLibDir;
static lean_object* l_Lake_LeanConfig_toToml___closed__18;
LEAN_EXPORT lean_object* l_Lake_instToTomlWorkspaceConfig(lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_CLI_Translate_Toml_0__Lake_instBEqFilePath__lake(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_System_FilePath_normalize(x_1);
x_4 = l_System_FilePath_normalize(x_2);
x_5 = lean_string_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_instBEqFilePath__lake___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lake_CLI_Translate_Toml_0__Lake_instBEqFilePath__lake(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTomlBackend(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lake_Backend_toString(x_1);
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTomlBackend___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lake_instToTomlBackend(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instSmartInsertBackend___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_quickCmp___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instSmartInsertBackend(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_box(x_2);
if (lean_obj_tag(x_4) == 2)
{
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_5 = l_Lake_Backend_toString(x_2);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = l_Lake_instSmartInsertBackend___closed__1;
x_9 = l_Lake_Toml_RBDict_insert___rarg(x_8, x_1, x_7, x_3);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instSmartInsertBackend___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lake_instSmartInsertBackend(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTomlBuildType(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lake_BuildType_toString(x_1);
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTomlBuildType___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lake_instToTomlBuildType(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_encodeLeanOptionValue(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
case 1:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get_uint8(x_1, 0);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(3, 1, 1);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_5);
return x_7;
}
default: 
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_nat_to_int(x_8);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
}
}
static lean_object* _init_l_Lake_instToTomlLeanOptionValue___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Toml_encodeLeanOptionValue), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instToTomlLeanOptionValue() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instToTomlLeanOptionValue___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Toml_encodeLeanOptions___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = 1;
x_8 = lean_usize_add(x_2, x_7);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_dec(x_6);
x_11 = l_Lake_Toml_encodeLeanOptionValue(x_10);
x_12 = l_Lake_instSmartInsertBackend___closed__1;
x_13 = l_Lake_Toml_RBDict_insert___rarg(x_12, x_9, x_11, x_4);
x_2 = x_8;
x_4 = x_13;
goto _start;
}
else
{
return x_4;
}
}
}
static lean_object* _init_l_Lake_Toml_encodeLeanOptions___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instSmartInsertBackend___closed__1;
x_2 = l_Lake_Toml_RBDict_empty___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_encodeLeanOptions(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_lt(x_3, x_2);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = l_Lake_Toml_encodeLeanOptions___closed__1;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_2, x_2);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = l_Lake_Toml_encodeLeanOptions___closed__1;
return x_7;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_2);
lean_dec(x_2);
x_10 = l_Lake_Toml_encodeLeanOptions___closed__1;
x_11 = l_Array_foldlMUnsafe_fold___at_Lake_Toml_encodeLeanOptions___spec__1(x_1, x_8, x_9, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Toml_encodeLeanOptions___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lake_Toml_encodeLeanOptions___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_encodeLeanOptions___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Toml_encodeLeanOptions(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_leanOptionsEncoder___elambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lake_Toml_encodeLeanOptions(x_1);
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_Toml_leanOptionsEncoder___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Toml_leanOptionsEncoder___elambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_leanOptionsEncoder() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Toml_leanOptionsEncoder___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_leanOptionsEncoder___elambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Toml_leanOptionsEncoder___elambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_WorkspaceConfig_toToml___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("packagesDir", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lake_WorkspaceConfig_toToml___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_WorkspaceConfig_toToml___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_WorkspaceConfig_toToml___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_defaultPackagesDir;
x_2 = l_System_FilePath_normalize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_WorkspaceConfig_toToml(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
lean_inc(x_1);
x_3 = l_System_FilePath_normalize(x_1);
x_4 = l_Lake_WorkspaceConfig_toToml___closed__3;
x_5 = lean_string_dec_eq(x_3, x_4);
lean_dec(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = l_Lake_mkRelPathString(x_1);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
x_9 = l_Lake_instSmartInsertBackend___closed__1;
x_10 = l_Lake_WorkspaceConfig_toToml___closed__2;
x_11 = l_Lake_Toml_RBDict_insert___rarg(x_9, x_10, x_8, x_2);
return x_11;
}
else
{
lean_dec(x_1);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instToTomlWorkspaceConfig(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lake_Toml_encodeLeanOptions___closed__1;
x_3 = l_Lake_WorkspaceConfig_toToml(x_1, x_2);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanConfig_toToml___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_array_uset(x_7, x_2, x_9);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
}
}
static lean_object* _init_l_Lake_LeanConfig_toToml___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("weakLinkArgs", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanConfig_toToml___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanConfig_toToml___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanConfig_toToml___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("moreLinkArgs", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanConfig_toToml___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanConfig_toToml___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanConfig_toToml___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("weakLeancArgs", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanConfig_toToml___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanConfig_toToml___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanConfig_toToml___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("moreLeancArgs", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanConfig_toToml___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanConfig_toToml___closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanConfig_toToml___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("weakLeanArgs", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanConfig_toToml___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanConfig_toToml___closed__9;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanConfig_toToml___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("moreLeanArgs", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanConfig_toToml___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanConfig_toToml___closed__11;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanConfig_toToml___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("moreServerOptions", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanConfig_toToml___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanConfig_toToml___closed__13;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanConfig_toToml___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("leanOptions", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanConfig_toToml___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanConfig_toToml___closed__15;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanConfig_toToml___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("platformIndependent", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanConfig_toToml___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanConfig_toToml___closed__17;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanConfig_toToml___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("backend", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanConfig_toToml___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanConfig_toToml___closed__19;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanConfig_toToml___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("buildType", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanConfig_toToml___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanConfig_toToml___closed__21;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_toToml(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; lean_object* x_49; lean_object* x_72; lean_object* x_97; lean_object* x_120; lean_object* x_133; uint8_t x_134; 
x_3 = lean_ctor_get(x_1, 7);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 6);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 5);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 4);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 8);
lean_inc(x_11);
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*9 + 1);
x_13 = lean_ctor_get_uint8(x_1, sizeof(void*)*9);
lean_dec(x_1);
x_14 = 3;
x_15 = l_Lake_instDecidableEqBuildType(x_13, x_14);
x_16 = l_Array_isEmpty___rarg(x_10);
x_17 = l_Array_isEmpty___rarg(x_9);
x_18 = l_Array_isEmpty___rarg(x_8);
x_19 = l_Array_isEmpty___rarg(x_7);
x_20 = l_Array_isEmpty___rarg(x_6);
x_21 = l_Array_isEmpty___rarg(x_5);
x_22 = l_Array_isEmpty___rarg(x_4);
x_23 = l_Array_isEmpty___rarg(x_3);
if (x_15 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_150 = l_Lake_BuildType_toString(x_13);
x_151 = lean_box(0);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_150);
x_153 = l_Lake_instSmartInsertBackend___closed__1;
x_154 = l_Lake_LeanConfig_toToml___closed__22;
x_155 = l_Lake_Toml_RBDict_insert___rarg(x_153, x_154, x_152, x_2);
x_156 = lean_box(x_12);
if (lean_obj_tag(x_156) == 2)
{
if (lean_obj_tag(x_11) == 0)
{
x_120 = x_155;
goto block_132;
}
else
{
lean_object* x_157; uint8_t x_158; 
x_157 = lean_ctor_get(x_11, 0);
lean_inc(x_157);
lean_dec(x_11);
x_158 = lean_unbox(x_157);
lean_dec(x_157);
x_133 = x_155;
x_134 = x_158;
goto block_149;
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_156);
x_159 = l_Lake_Backend_toString(x_12);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_151);
lean_ctor_set(x_160, 1, x_159);
x_161 = l_Lake_LeanConfig_toToml___closed__20;
x_162 = l_Lake_Toml_RBDict_insert___rarg(x_153, x_161, x_160, x_155);
if (lean_obj_tag(x_11) == 0)
{
x_120 = x_162;
goto block_132;
}
else
{
lean_object* x_163; uint8_t x_164; 
x_163 = lean_ctor_get(x_11, 0);
lean_inc(x_163);
lean_dec(x_11);
x_164 = lean_unbox(x_163);
lean_dec(x_163);
x_133 = x_162;
x_134 = x_164;
goto block_149;
}
}
}
else
{
lean_object* x_165; 
x_165 = lean_box(x_12);
if (lean_obj_tag(x_165) == 2)
{
if (lean_obj_tag(x_11) == 0)
{
x_120 = x_2;
goto block_132;
}
else
{
lean_object* x_166; uint8_t x_167; 
x_166 = lean_ctor_get(x_11, 0);
lean_inc(x_166);
lean_dec(x_11);
x_167 = lean_unbox(x_166);
lean_dec(x_166);
x_133 = x_2;
x_134 = x_167;
goto block_149;
}
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_165);
x_168 = l_Lake_Backend_toString(x_12);
x_169 = lean_box(0);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_168);
x_171 = l_Lake_instSmartInsertBackend___closed__1;
x_172 = l_Lake_LeanConfig_toToml___closed__20;
x_173 = l_Lake_Toml_RBDict_insert___rarg(x_171, x_172, x_170, x_2);
if (lean_obj_tag(x_11) == 0)
{
x_120 = x_173;
goto block_132;
}
else
{
lean_object* x_174; uint8_t x_175; 
x_174 = lean_ctor_get(x_11, 0);
lean_inc(x_174);
lean_dec(x_11);
x_175 = lean_unbox(x_174);
lean_dec(x_174);
x_133 = x_173;
x_134 = x_175;
goto block_149;
}
}
}
block_48:
{
size_t x_25; size_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_25 = lean_array_size(x_5);
x_26 = 0;
x_27 = l_Array_mapMUnsafe_map___at_Lake_LeanConfig_toToml___spec__1(x_25, x_26, x_5);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l_Lake_instSmartInsertBackend___closed__1;
x_31 = l_Lake_LeanConfig_toToml___closed__6;
x_32 = l_Lake_Toml_RBDict_insert___rarg(x_30, x_31, x_29, x_24);
if (x_22 == 0)
{
size_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_array_size(x_4);
x_34 = l_Array_mapMUnsafe_map___at_Lake_LeanConfig_toToml___spec__1(x_33, x_26, x_4);
x_35 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_35, 0, x_28);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lake_LeanConfig_toToml___closed__4;
x_37 = l_Lake_Toml_RBDict_insert___rarg(x_30, x_36, x_35, x_32);
if (x_23 == 0)
{
size_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_array_size(x_3);
x_39 = l_Array_mapMUnsafe_map___at_Lake_LeanConfig_toToml___spec__1(x_38, x_26, x_3);
x_40 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_40, 0, x_28);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lake_LeanConfig_toToml___closed__2;
x_42 = l_Lake_Toml_RBDict_insert___rarg(x_30, x_41, x_40, x_37);
return x_42;
}
else
{
lean_dec(x_3);
return x_37;
}
}
else
{
lean_dec(x_4);
if (x_23 == 0)
{
size_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_array_size(x_3);
x_44 = l_Array_mapMUnsafe_map___at_Lake_LeanConfig_toToml___spec__1(x_43, x_26, x_3);
x_45 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_45, 0, x_28);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lake_LeanConfig_toToml___closed__2;
x_47 = l_Lake_Toml_RBDict_insert___rarg(x_30, x_46, x_45, x_32);
return x_47;
}
else
{
lean_dec(x_3);
return x_32;
}
}
}
block_71:
{
if (x_22 == 0)
{
size_t x_50; size_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_50 = lean_array_size(x_4);
x_51 = 0;
x_52 = l_Array_mapMUnsafe_map___at_Lake_LeanConfig_toToml___spec__1(x_50, x_51, x_4);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
x_55 = l_Lake_instSmartInsertBackend___closed__1;
x_56 = l_Lake_LeanConfig_toToml___closed__4;
x_57 = l_Lake_Toml_RBDict_insert___rarg(x_55, x_56, x_54, x_49);
if (x_23 == 0)
{
size_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_58 = lean_array_size(x_3);
x_59 = l_Array_mapMUnsafe_map___at_Lake_LeanConfig_toToml___spec__1(x_58, x_51, x_3);
x_60 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_60, 0, x_53);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Lake_LeanConfig_toToml___closed__2;
x_62 = l_Lake_Toml_RBDict_insert___rarg(x_55, x_61, x_60, x_57);
return x_62;
}
else
{
lean_dec(x_3);
return x_57;
}
}
else
{
lean_dec(x_4);
if (x_23 == 0)
{
size_t x_63; size_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_63 = lean_array_size(x_3);
x_64 = 0;
x_65 = l_Array_mapMUnsafe_map___at_Lake_LeanConfig_toToml___spec__1(x_63, x_64, x_3);
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
x_68 = l_Lake_instSmartInsertBackend___closed__1;
x_69 = l_Lake_LeanConfig_toToml___closed__2;
x_70 = l_Lake_Toml_RBDict_insert___rarg(x_68, x_69, x_67, x_49);
return x_70;
}
else
{
lean_dec(x_3);
return x_49;
}
}
}
block_96:
{
size_t x_73; size_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_73 = lean_array_size(x_8);
x_74 = 0;
x_75 = l_Array_mapMUnsafe_map___at_Lake_LeanConfig_toToml___spec__1(x_73, x_74, x_8);
x_76 = lean_box(0);
x_77 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = l_Lake_instSmartInsertBackend___closed__1;
x_79 = l_Lake_LeanConfig_toToml___closed__12;
x_80 = l_Lake_Toml_RBDict_insert___rarg(x_78, x_79, x_77, x_72);
if (x_19 == 0)
{
size_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_81 = lean_array_size(x_7);
x_82 = l_Array_mapMUnsafe_map___at_Lake_LeanConfig_toToml___spec__1(x_81, x_74, x_7);
x_83 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_83, 0, x_76);
lean_ctor_set(x_83, 1, x_82);
x_84 = l_Lake_LeanConfig_toToml___closed__10;
x_85 = l_Lake_Toml_RBDict_insert___rarg(x_78, x_84, x_83, x_80);
if (x_20 == 0)
{
size_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_86 = lean_array_size(x_6);
x_87 = l_Array_mapMUnsafe_map___at_Lake_LeanConfig_toToml___spec__1(x_86, x_74, x_6);
x_88 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_88, 0, x_76);
lean_ctor_set(x_88, 1, x_87);
x_89 = l_Lake_LeanConfig_toToml___closed__8;
x_90 = l_Lake_Toml_RBDict_insert___rarg(x_78, x_89, x_88, x_85);
if (x_21 == 0)
{
x_24 = x_90;
goto block_48;
}
else
{
lean_dec(x_5);
x_49 = x_90;
goto block_71;
}
}
else
{
lean_dec(x_6);
if (x_21 == 0)
{
x_24 = x_85;
goto block_48;
}
else
{
lean_dec(x_5);
x_49 = x_85;
goto block_71;
}
}
}
else
{
lean_dec(x_7);
if (x_20 == 0)
{
size_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_91 = lean_array_size(x_6);
x_92 = l_Array_mapMUnsafe_map___at_Lake_LeanConfig_toToml___spec__1(x_91, x_74, x_6);
x_93 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_93, 0, x_76);
lean_ctor_set(x_93, 1, x_92);
x_94 = l_Lake_LeanConfig_toToml___closed__8;
x_95 = l_Lake_Toml_RBDict_insert___rarg(x_78, x_94, x_93, x_80);
if (x_21 == 0)
{
x_24 = x_95;
goto block_48;
}
else
{
lean_dec(x_5);
x_49 = x_95;
goto block_71;
}
}
else
{
lean_dec(x_6);
if (x_21 == 0)
{
x_24 = x_80;
goto block_48;
}
else
{
lean_dec(x_5);
x_49 = x_80;
goto block_71;
}
}
}
}
block_119:
{
if (x_19 == 0)
{
size_t x_98; size_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_98 = lean_array_size(x_7);
x_99 = 0;
x_100 = l_Array_mapMUnsafe_map___at_Lake_LeanConfig_toToml___spec__1(x_98, x_99, x_7);
x_101 = lean_box(0);
x_102 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_100);
x_103 = l_Lake_instSmartInsertBackend___closed__1;
x_104 = l_Lake_LeanConfig_toToml___closed__10;
x_105 = l_Lake_Toml_RBDict_insert___rarg(x_103, x_104, x_102, x_97);
if (x_20 == 0)
{
size_t x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_106 = lean_array_size(x_6);
x_107 = l_Array_mapMUnsafe_map___at_Lake_LeanConfig_toToml___spec__1(x_106, x_99, x_6);
x_108 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_108, 0, x_101);
lean_ctor_set(x_108, 1, x_107);
x_109 = l_Lake_LeanConfig_toToml___closed__8;
x_110 = l_Lake_Toml_RBDict_insert___rarg(x_103, x_109, x_108, x_105);
if (x_21 == 0)
{
x_24 = x_110;
goto block_48;
}
else
{
lean_dec(x_5);
x_49 = x_110;
goto block_71;
}
}
else
{
lean_dec(x_6);
if (x_21 == 0)
{
x_24 = x_105;
goto block_48;
}
else
{
lean_dec(x_5);
x_49 = x_105;
goto block_71;
}
}
}
else
{
lean_dec(x_7);
if (x_20 == 0)
{
size_t x_111; size_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_111 = lean_array_size(x_6);
x_112 = 0;
x_113 = l_Array_mapMUnsafe_map___at_Lake_LeanConfig_toToml___spec__1(x_111, x_112, x_6);
x_114 = lean_box(0);
x_115 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_113);
x_116 = l_Lake_instSmartInsertBackend___closed__1;
x_117 = l_Lake_LeanConfig_toToml___closed__8;
x_118 = l_Lake_Toml_RBDict_insert___rarg(x_116, x_117, x_115, x_97);
if (x_21 == 0)
{
x_24 = x_118;
goto block_48;
}
else
{
lean_dec(x_5);
x_49 = x_118;
goto block_71;
}
}
else
{
lean_dec(x_6);
if (x_21 == 0)
{
x_24 = x_97;
goto block_48;
}
else
{
lean_dec(x_5);
x_49 = x_97;
goto block_71;
}
}
}
}
block_132:
{
if (x_16 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_121 = l_Lake_Toml_leanOptionsEncoder___elambda__1(x_10);
lean_dec(x_10);
x_122 = l_Lake_instSmartInsertBackend___closed__1;
x_123 = l_Lake_LeanConfig_toToml___closed__16;
x_124 = l_Lake_Toml_RBDict_insert___rarg(x_122, x_123, x_121, x_120);
if (x_17 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = l_Lake_Toml_leanOptionsEncoder___elambda__1(x_9);
lean_dec(x_9);
x_126 = l_Lake_LeanConfig_toToml___closed__14;
x_127 = l_Lake_Toml_RBDict_insert___rarg(x_122, x_126, x_125, x_124);
if (x_18 == 0)
{
x_72 = x_127;
goto block_96;
}
else
{
lean_dec(x_8);
x_97 = x_127;
goto block_119;
}
}
else
{
lean_dec(x_9);
if (x_18 == 0)
{
x_72 = x_124;
goto block_96;
}
else
{
lean_dec(x_8);
x_97 = x_124;
goto block_119;
}
}
}
else
{
lean_dec(x_10);
if (x_17 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_128 = l_Lake_Toml_leanOptionsEncoder___elambda__1(x_9);
lean_dec(x_9);
x_129 = l_Lake_instSmartInsertBackend___closed__1;
x_130 = l_Lake_LeanConfig_toToml___closed__14;
x_131 = l_Lake_Toml_RBDict_insert___rarg(x_129, x_130, x_128, x_120);
if (x_18 == 0)
{
x_72 = x_131;
goto block_96;
}
else
{
lean_dec(x_8);
x_97 = x_131;
goto block_119;
}
}
else
{
lean_dec(x_9);
if (x_18 == 0)
{
x_72 = x_120;
goto block_96;
}
else
{
lean_dec(x_8);
x_97 = x_120;
goto block_119;
}
}
}
}
block_149:
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_135 = lean_box(0);
x_136 = lean_alloc_ctor(3, 1, 1);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set_uint8(x_136, sizeof(void*)*1, x_134);
x_137 = l_Lake_instSmartInsertBackend___closed__1;
x_138 = l_Lake_LeanConfig_toToml___closed__18;
x_139 = l_Lake_Toml_RBDict_insert___rarg(x_137, x_138, x_136, x_133);
if (x_16 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = l_Lake_Toml_leanOptionsEncoder___elambda__1(x_10);
lean_dec(x_10);
x_141 = l_Lake_LeanConfig_toToml___closed__16;
x_142 = l_Lake_Toml_RBDict_insert___rarg(x_137, x_141, x_140, x_139);
if (x_17 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = l_Lake_Toml_leanOptionsEncoder___elambda__1(x_9);
lean_dec(x_9);
x_144 = l_Lake_LeanConfig_toToml___closed__14;
x_145 = l_Lake_Toml_RBDict_insert___rarg(x_137, x_144, x_143, x_142);
if (x_18 == 0)
{
x_72 = x_145;
goto block_96;
}
else
{
lean_dec(x_8);
x_97 = x_145;
goto block_119;
}
}
else
{
lean_dec(x_9);
if (x_18 == 0)
{
x_72 = x_142;
goto block_96;
}
else
{
lean_dec(x_8);
x_97 = x_142;
goto block_119;
}
}
}
else
{
lean_dec(x_10);
if (x_17 == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = l_Lake_Toml_leanOptionsEncoder___elambda__1(x_9);
lean_dec(x_9);
x_147 = l_Lake_LeanConfig_toToml___closed__14;
x_148 = l_Lake_Toml_RBDict_insert___rarg(x_137, x_147, x_146, x_139);
if (x_18 == 0)
{
x_72 = x_148;
goto block_96;
}
else
{
lean_dec(x_8);
x_97 = x_148;
goto block_119;
}
}
else
{
lean_dec(x_9);
if (x_18 == 0)
{
x_72 = x_139;
goto block_96;
}
else
{
lean_dec(x_8);
x_97 = x_139;
goto block_119;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanConfig_toToml___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lake_LeanConfig_toToml___spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTomlLeanConfig(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lake_Toml_encodeLeanOptions___closed__1;
x_3 = l_Lake_LeanConfig_toToml(x_1, x_2);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
static lean_object* _init_l_Lake_PackageConfig_toToml___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("preferReleaseBuild", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_toToml___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_PackageConfig_toToml___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig_toToml___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("buildArchive", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_toToml___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_PackageConfig_toToml___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig_toToml___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_toToml___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_toToml___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".tar.gz", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_toToml___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("releaseRepo", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_toToml___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_PackageConfig_toToml___closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig_toToml___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("irDir", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_toToml___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_PackageConfig_toToml___closed__10;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig_toToml___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("binDir", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_toToml___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_PackageConfig_toToml___closed__12;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig_toToml___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("nativeLibDir", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_toToml___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_PackageConfig_toToml___closed__14;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig_toToml___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("leanLibDir", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_toToml___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_PackageConfig_toToml___closed__16;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig_toToml___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("buildDir", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_toToml___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_PackageConfig_toToml___closed__18;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig_toToml___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("srcDir", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_toToml___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_PackageConfig_toToml___closed__20;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig_toToml___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("moreGlobalServerArgs", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_toToml___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_PackageConfig_toToml___closed__22;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig_toToml___closed__24() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("precompileModules", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_toToml___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_PackageConfig_toToml___closed__24;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig_toToml___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("name", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_toToml___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_PackageConfig_toToml___closed__26;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig_toToml___closed__28() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_toToml___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_PackageConfig_toToml___closed__28;
x_2 = l_System_FilePath_normalize(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_PackageConfig_toToml___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_defaultBuildDir;
x_2 = l_System_FilePath_normalize(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_PackageConfig_toToml___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_defaultLeanLibDir;
x_2 = l_System_FilePath_normalize(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_PackageConfig_toToml___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_defaultNativeLibDir;
x_2 = l_System_FilePath_normalize(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_PackageConfig_toToml___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_defaultBinDir;
x_2 = l_System_FilePath_normalize(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_PackageConfig_toToml___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_defaultIrDir;
x_2 = l_System_FilePath_normalize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toToml(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*21 + 1);
x_6 = lean_ctor_get(x_1, 15);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = 0;
lean_inc(x_7);
x_9 = l_Lean_Name_toString(x_7, x_8);
x_10 = l_Lake_PackageConfig_toToml___closed__5;
x_11 = lean_string_append(x_10, x_9);
lean_dec(x_9);
x_12 = l_Lake_PackageConfig_toToml___closed__6;
x_13 = lean_string_append(x_11, x_12);
x_14 = l_System_Platform_target;
x_15 = lean_string_append(x_13, x_14);
x_16 = l_Lake_PackageConfig_toToml___closed__7;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_ctor_get(x_1, 14);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 12);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 11);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 10);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 9);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 8);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 7);
lean_inc(x_24);
x_25 = lean_ctor_get(x_1, 6);
lean_inc(x_25);
x_26 = lean_ctor_get_uint8(x_1, sizeof(void*)*21);
x_27 = 1;
x_28 = l_Lean_Name_toString(x_7, x_27);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l_Lake_instSmartInsertBackend___closed__1;
x_32 = l_Lake_PackageConfig_toToml___closed__27;
x_33 = l_Lake_Toml_RBDict_insert___rarg(x_31, x_32, x_30, x_2);
x_34 = l_Array_isEmpty___rarg(x_25);
lean_inc(x_24);
x_35 = l_System_FilePath_normalize(x_24);
x_36 = l_Lake_PackageConfig_toToml___closed__29;
x_37 = lean_string_dec_eq(x_35, x_36);
lean_dec(x_35);
lean_inc(x_23);
x_38 = l_System_FilePath_normalize(x_23);
x_39 = l_Lake_PackageConfig_toToml___closed__30;
x_40 = lean_string_dec_eq(x_38, x_39);
lean_dec(x_38);
lean_inc(x_22);
x_41 = l_System_FilePath_normalize(x_22);
x_42 = l_Lake_PackageConfig_toToml___closed__31;
x_43 = lean_string_dec_eq(x_41, x_42);
lean_dec(x_41);
lean_inc(x_21);
x_44 = l_System_FilePath_normalize(x_21);
x_45 = l_Lake_PackageConfig_toToml___closed__32;
x_46 = lean_string_dec_eq(x_44, x_45);
lean_dec(x_44);
lean_inc(x_20);
x_47 = l_System_FilePath_normalize(x_20);
x_48 = l_Lake_PackageConfig_toToml___closed__33;
x_49 = lean_string_dec_eq(x_47, x_48);
lean_dec(x_47);
lean_inc(x_19);
x_50 = l_System_FilePath_normalize(x_19);
x_51 = l_Lake_PackageConfig_toToml___closed__34;
x_52 = lean_string_dec_eq(x_50, x_51);
lean_dec(x_50);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_215; 
x_215 = lean_ctor_get(x_1, 16);
lean_inc(x_215);
x_53 = x_215;
goto block_214;
}
else
{
lean_object* x_216; 
x_216 = lean_ctor_get(x_6, 0);
lean_inc(x_216);
lean_dec(x_6);
x_53 = x_216;
goto block_214;
}
block_214:
{
uint8_t x_54; lean_object* x_55; 
x_54 = lean_string_dec_eq(x_53, x_17);
lean_dec(x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_210; 
x_210 = lean_ctor_get(x_1, 13);
lean_inc(x_210);
lean_dec(x_1);
x_55 = x_210;
goto block_209;
}
else
{
uint8_t x_211; 
lean_dec(x_1);
x_211 = !lean_is_exclusive(x_18);
if (x_211 == 0)
{
x_55 = x_18;
goto block_209;
}
else
{
lean_object* x_212; lean_object* x_213; 
x_212 = lean_ctor_get(x_18, 0);
lean_inc(x_212);
lean_dec(x_18);
x_213 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_213, 0, x_212);
x_55 = x_213;
goto block_209;
}
}
block_209:
{
lean_object* x_56; lean_object* x_100; lean_object* x_140; lean_object* x_158; lean_object* x_172; lean_object* x_192; 
if (x_26 == 0)
{
if (x_34 == 0)
{
x_172 = x_33;
goto block_191;
}
else
{
lean_dec(x_25);
x_192 = x_33;
goto block_205;
}
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_206 = lean_alloc_ctor(3, 1, 1);
lean_ctor_set(x_206, 0, x_29);
lean_ctor_set_uint8(x_206, sizeof(void*)*1, x_26);
x_207 = l_Lake_PackageConfig_toToml___closed__25;
x_208 = l_Lake_Toml_RBDict_insert___rarg(x_31, x_207, x_206, x_33);
if (x_34 == 0)
{
x_172 = x_208;
goto block_191;
}
else
{
lean_dec(x_25);
x_192 = x_208;
goto block_205;
}
}
block_99:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = l_Lake_mkRelPathString(x_19);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_29);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lake_PackageConfig_toToml___closed__11;
x_60 = l_Lake_Toml_RBDict_insert___rarg(x_31, x_59, x_58, x_56);
if (lean_obj_tag(x_55) == 0)
{
if (x_54 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_29);
lean_ctor_set(x_61, 1, x_53);
x_62 = l_Lake_PackageConfig_toToml___closed__4;
x_63 = l_Lake_Toml_RBDict_insert___rarg(x_31, x_62, x_61, x_60);
if (x_5 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = l_Lake_WorkspaceConfig_toToml(x_4, x_63);
x_65 = l_Lake_LeanConfig_toToml(x_3, x_64);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = lean_alloc_ctor(3, 1, 1);
lean_ctor_set(x_66, 0, x_29);
lean_ctor_set_uint8(x_66, sizeof(void*)*1, x_5);
x_67 = l_Lake_PackageConfig_toToml___closed__2;
x_68 = l_Lake_Toml_RBDict_insert___rarg(x_31, x_67, x_66, x_63);
x_69 = l_Lake_WorkspaceConfig_toToml(x_4, x_68);
x_70 = l_Lake_LeanConfig_toToml(x_3, x_69);
return x_70;
}
}
else
{
lean_dec(x_53);
if (x_5 == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = l_Lake_WorkspaceConfig_toToml(x_4, x_60);
x_72 = l_Lake_LeanConfig_toToml(x_3, x_71);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_73 = lean_alloc_ctor(3, 1, 1);
lean_ctor_set(x_73, 0, x_29);
lean_ctor_set_uint8(x_73, sizeof(void*)*1, x_5);
x_74 = l_Lake_PackageConfig_toToml___closed__2;
x_75 = l_Lake_Toml_RBDict_insert___rarg(x_31, x_74, x_73, x_60);
x_76 = l_Lake_WorkspaceConfig_toToml(x_4, x_75);
x_77 = l_Lake_LeanConfig_toToml(x_3, x_76);
return x_77;
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_55, 0);
lean_inc(x_78);
lean_dec(x_55);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_29);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_Lake_PackageConfig_toToml___closed__9;
x_81 = l_Lake_Toml_RBDict_insert___rarg(x_31, x_80, x_79, x_60);
if (x_54 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_29);
lean_ctor_set(x_82, 1, x_53);
x_83 = l_Lake_PackageConfig_toToml___closed__4;
x_84 = l_Lake_Toml_RBDict_insert___rarg(x_31, x_83, x_82, x_81);
if (x_5 == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = l_Lake_WorkspaceConfig_toToml(x_4, x_84);
x_86 = l_Lake_LeanConfig_toToml(x_3, x_85);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_87 = lean_alloc_ctor(3, 1, 1);
lean_ctor_set(x_87, 0, x_29);
lean_ctor_set_uint8(x_87, sizeof(void*)*1, x_5);
x_88 = l_Lake_PackageConfig_toToml___closed__2;
x_89 = l_Lake_Toml_RBDict_insert___rarg(x_31, x_88, x_87, x_84);
x_90 = l_Lake_WorkspaceConfig_toToml(x_4, x_89);
x_91 = l_Lake_LeanConfig_toToml(x_3, x_90);
return x_91;
}
}
else
{
lean_dec(x_53);
if (x_5 == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = l_Lake_WorkspaceConfig_toToml(x_4, x_81);
x_93 = l_Lake_LeanConfig_toToml(x_3, x_92);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_94 = lean_alloc_ctor(3, 1, 1);
lean_ctor_set(x_94, 0, x_29);
lean_ctor_set_uint8(x_94, sizeof(void*)*1, x_5);
x_95 = l_Lake_PackageConfig_toToml___closed__2;
x_96 = l_Lake_Toml_RBDict_insert___rarg(x_31, x_95, x_94, x_81);
x_97 = l_Lake_WorkspaceConfig_toToml(x_4, x_96);
x_98 = l_Lake_LeanConfig_toToml(x_3, x_97);
return x_98;
}
}
}
}
block_139:
{
if (lean_obj_tag(x_55) == 0)
{
if (x_54 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_29);
lean_ctor_set(x_101, 1, x_53);
x_102 = l_Lake_PackageConfig_toToml___closed__4;
x_103 = l_Lake_Toml_RBDict_insert___rarg(x_31, x_102, x_101, x_100);
if (x_5 == 0)
{
lean_object* x_104; lean_object* x_105; 
x_104 = l_Lake_WorkspaceConfig_toToml(x_4, x_103);
x_105 = l_Lake_LeanConfig_toToml(x_3, x_104);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_106 = lean_alloc_ctor(3, 1, 1);
lean_ctor_set(x_106, 0, x_29);
lean_ctor_set_uint8(x_106, sizeof(void*)*1, x_5);
x_107 = l_Lake_PackageConfig_toToml___closed__2;
x_108 = l_Lake_Toml_RBDict_insert___rarg(x_31, x_107, x_106, x_103);
x_109 = l_Lake_WorkspaceConfig_toToml(x_4, x_108);
x_110 = l_Lake_LeanConfig_toToml(x_3, x_109);
return x_110;
}
}
else
{
lean_dec(x_53);
if (x_5 == 0)
{
lean_object* x_111; lean_object* x_112; 
x_111 = l_Lake_WorkspaceConfig_toToml(x_4, x_100);
x_112 = l_Lake_LeanConfig_toToml(x_3, x_111);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_113 = lean_alloc_ctor(3, 1, 1);
lean_ctor_set(x_113, 0, x_29);
lean_ctor_set_uint8(x_113, sizeof(void*)*1, x_5);
x_114 = l_Lake_PackageConfig_toToml___closed__2;
x_115 = l_Lake_Toml_RBDict_insert___rarg(x_31, x_114, x_113, x_100);
x_116 = l_Lake_WorkspaceConfig_toToml(x_4, x_115);
x_117 = l_Lake_LeanConfig_toToml(x_3, x_116);
return x_117;
}
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_118 = lean_ctor_get(x_55, 0);
lean_inc(x_118);
lean_dec(x_55);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_29);
lean_ctor_set(x_119, 1, x_118);
x_120 = l_Lake_PackageConfig_toToml___closed__9;
x_121 = l_Lake_Toml_RBDict_insert___rarg(x_31, x_120, x_119, x_100);
if (x_54 == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_29);
lean_ctor_set(x_122, 1, x_53);
x_123 = l_Lake_PackageConfig_toToml___closed__4;
x_124 = l_Lake_Toml_RBDict_insert___rarg(x_31, x_123, x_122, x_121);
if (x_5 == 0)
{
lean_object* x_125; lean_object* x_126; 
x_125 = l_Lake_WorkspaceConfig_toToml(x_4, x_124);
x_126 = l_Lake_LeanConfig_toToml(x_3, x_125);
return x_126;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_127 = lean_alloc_ctor(3, 1, 1);
lean_ctor_set(x_127, 0, x_29);
lean_ctor_set_uint8(x_127, sizeof(void*)*1, x_5);
x_128 = l_Lake_PackageConfig_toToml___closed__2;
x_129 = l_Lake_Toml_RBDict_insert___rarg(x_31, x_128, x_127, x_124);
x_130 = l_Lake_WorkspaceConfig_toToml(x_4, x_129);
x_131 = l_Lake_LeanConfig_toToml(x_3, x_130);
return x_131;
}
}
else
{
lean_dec(x_53);
if (x_5 == 0)
{
lean_object* x_132; lean_object* x_133; 
x_132 = l_Lake_WorkspaceConfig_toToml(x_4, x_121);
x_133 = l_Lake_LeanConfig_toToml(x_3, x_132);
return x_133;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_134 = lean_alloc_ctor(3, 1, 1);
lean_ctor_set(x_134, 0, x_29);
lean_ctor_set_uint8(x_134, sizeof(void*)*1, x_5);
x_135 = l_Lake_PackageConfig_toToml___closed__2;
x_136 = l_Lake_Toml_RBDict_insert___rarg(x_31, x_135, x_134, x_121);
x_137 = l_Lake_WorkspaceConfig_toToml(x_4, x_136);
x_138 = l_Lake_LeanConfig_toToml(x_3, x_137);
return x_138;
}
}
}
}
block_157:
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_141 = l_Lake_mkRelPathString(x_22);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_29);
lean_ctor_set(x_142, 1, x_141);
x_143 = l_Lake_PackageConfig_toToml___closed__17;
x_144 = l_Lake_Toml_RBDict_insert___rarg(x_31, x_143, x_142, x_140);
if (x_46 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_145 = l_Lake_mkRelPathString(x_21);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_29);
lean_ctor_set(x_146, 1, x_145);
x_147 = l_Lake_PackageConfig_toToml___closed__15;
x_148 = l_Lake_Toml_RBDict_insert___rarg(x_31, x_147, x_146, x_144);
if (x_49 == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_149 = l_Lake_mkRelPathString(x_20);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_29);
lean_ctor_set(x_150, 1, x_149);
x_151 = l_Lake_PackageConfig_toToml___closed__13;
x_152 = l_Lake_Toml_RBDict_insert___rarg(x_31, x_151, x_150, x_148);
if (x_52 == 0)
{
x_56 = x_152;
goto block_99;
}
else
{
lean_dec(x_19);
x_100 = x_152;
goto block_139;
}
}
else
{
lean_dec(x_20);
if (x_52 == 0)
{
x_56 = x_148;
goto block_99;
}
else
{
lean_dec(x_19);
x_100 = x_148;
goto block_139;
}
}
}
else
{
lean_dec(x_21);
if (x_49 == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_153 = l_Lake_mkRelPathString(x_20);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_29);
lean_ctor_set(x_154, 1, x_153);
x_155 = l_Lake_PackageConfig_toToml___closed__13;
x_156 = l_Lake_Toml_RBDict_insert___rarg(x_31, x_155, x_154, x_144);
if (x_52 == 0)
{
x_56 = x_156;
goto block_99;
}
else
{
lean_dec(x_19);
x_100 = x_156;
goto block_139;
}
}
else
{
lean_dec(x_20);
if (x_52 == 0)
{
x_56 = x_144;
goto block_99;
}
else
{
lean_dec(x_19);
x_100 = x_144;
goto block_139;
}
}
}
}
block_171:
{
if (x_46 == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_159 = l_Lake_mkRelPathString(x_21);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_29);
lean_ctor_set(x_160, 1, x_159);
x_161 = l_Lake_PackageConfig_toToml___closed__15;
x_162 = l_Lake_Toml_RBDict_insert___rarg(x_31, x_161, x_160, x_158);
if (x_49 == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_163 = l_Lake_mkRelPathString(x_20);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_29);
lean_ctor_set(x_164, 1, x_163);
x_165 = l_Lake_PackageConfig_toToml___closed__13;
x_166 = l_Lake_Toml_RBDict_insert___rarg(x_31, x_165, x_164, x_162);
if (x_52 == 0)
{
x_56 = x_166;
goto block_99;
}
else
{
lean_dec(x_19);
x_100 = x_166;
goto block_139;
}
}
else
{
lean_dec(x_20);
if (x_52 == 0)
{
x_56 = x_162;
goto block_99;
}
else
{
lean_dec(x_19);
x_100 = x_162;
goto block_139;
}
}
}
else
{
lean_dec(x_21);
if (x_49 == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_167 = l_Lake_mkRelPathString(x_20);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_29);
lean_ctor_set(x_168, 1, x_167);
x_169 = l_Lake_PackageConfig_toToml___closed__13;
x_170 = l_Lake_Toml_RBDict_insert___rarg(x_31, x_169, x_168, x_158);
if (x_52 == 0)
{
x_56 = x_170;
goto block_99;
}
else
{
lean_dec(x_19);
x_100 = x_170;
goto block_139;
}
}
else
{
lean_dec(x_20);
if (x_52 == 0)
{
x_56 = x_158;
goto block_99;
}
else
{
lean_dec(x_19);
x_100 = x_158;
goto block_139;
}
}
}
}
block_191:
{
size_t x_173; size_t x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_173 = lean_array_size(x_25);
x_174 = 0;
x_175 = l_Array_mapMUnsafe_map___at_Lake_LeanConfig_toToml___spec__1(x_173, x_174, x_25);
x_176 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_176, 0, x_29);
lean_ctor_set(x_176, 1, x_175);
x_177 = l_Lake_PackageConfig_toToml___closed__23;
x_178 = l_Lake_Toml_RBDict_insert___rarg(x_31, x_177, x_176, x_172);
if (x_37 == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_179 = l_Lake_mkRelPathString(x_24);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_29);
lean_ctor_set(x_180, 1, x_179);
x_181 = l_Lake_PackageConfig_toToml___closed__21;
x_182 = l_Lake_Toml_RBDict_insert___rarg(x_31, x_181, x_180, x_178);
if (x_40 == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_183 = l_Lake_mkRelPathString(x_23);
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_29);
lean_ctor_set(x_184, 1, x_183);
x_185 = l_Lake_PackageConfig_toToml___closed__19;
x_186 = l_Lake_Toml_RBDict_insert___rarg(x_31, x_185, x_184, x_182);
if (x_43 == 0)
{
x_140 = x_186;
goto block_157;
}
else
{
lean_dec(x_22);
x_158 = x_186;
goto block_171;
}
}
else
{
lean_dec(x_23);
if (x_43 == 0)
{
x_140 = x_182;
goto block_157;
}
else
{
lean_dec(x_22);
x_158 = x_182;
goto block_171;
}
}
}
else
{
lean_dec(x_24);
if (x_40 == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_187 = l_Lake_mkRelPathString(x_23);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_29);
lean_ctor_set(x_188, 1, x_187);
x_189 = l_Lake_PackageConfig_toToml___closed__19;
x_190 = l_Lake_Toml_RBDict_insert___rarg(x_31, x_189, x_188, x_178);
if (x_43 == 0)
{
x_140 = x_190;
goto block_157;
}
else
{
lean_dec(x_22);
x_158 = x_190;
goto block_171;
}
}
else
{
lean_dec(x_23);
if (x_43 == 0)
{
x_140 = x_178;
goto block_157;
}
else
{
lean_dec(x_22);
x_158 = x_178;
goto block_171;
}
}
}
}
block_205:
{
if (x_37 == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_193 = l_Lake_mkRelPathString(x_24);
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_29);
lean_ctor_set(x_194, 1, x_193);
x_195 = l_Lake_PackageConfig_toToml___closed__21;
x_196 = l_Lake_Toml_RBDict_insert___rarg(x_31, x_195, x_194, x_192);
if (x_40 == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_197 = l_Lake_mkRelPathString(x_23);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_29);
lean_ctor_set(x_198, 1, x_197);
x_199 = l_Lake_PackageConfig_toToml___closed__19;
x_200 = l_Lake_Toml_RBDict_insert___rarg(x_31, x_199, x_198, x_196);
if (x_43 == 0)
{
x_140 = x_200;
goto block_157;
}
else
{
lean_dec(x_22);
x_158 = x_200;
goto block_171;
}
}
else
{
lean_dec(x_23);
if (x_43 == 0)
{
x_140 = x_196;
goto block_157;
}
else
{
lean_dec(x_22);
x_158 = x_196;
goto block_171;
}
}
}
else
{
lean_dec(x_24);
if (x_40 == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_201 = l_Lake_mkRelPathString(x_23);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_29);
lean_ctor_set(x_202, 1, x_201);
x_203 = l_Lake_PackageConfig_toToml___closed__19;
x_204 = l_Lake_Toml_RBDict_insert___rarg(x_31, x_203, x_202, x_192);
if (x_43 == 0)
{
x_140 = x_204;
goto block_157;
}
else
{
lean_dec(x_22);
x_158 = x_204;
goto block_171;
}
}
else
{
lean_dec(x_23);
if (x_43 == 0)
{
x_140 = x_192;
goto block_157;
}
else
{
lean_dec(x_22);
x_158 = x_192;
goto block_171;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instToTomlPackageConfig(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lake_Toml_encodeLeanOptions___closed__1;
x_3 = l_Lake_PackageConfig_toToml(x_1, x_2);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTomlGlob(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lake_Glob_toString(x_1);
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanLibConfig_toToml___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = 1;
x_9 = l_Lean_Name_toString(x_5, x_8);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_14 = lean_array_uset(x_7, x_2, x_11);
x_2 = x_13;
x_3 = x_14;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at_Lake_LeanLibConfig_toToml___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_5, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_5);
x_8 = 1;
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_array_fget(x_3, x_5);
x_10 = lean_array_fget(x_4, x_5);
x_11 = lean_name_eq(x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_5);
x_12 = 0;
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_2 = lean_box(0);
x_5 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at_Lake_LeanLibConfig_toToml___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_5, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_5);
x_8 = 1;
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_array_fget(x_3, x_5);
x_10 = lean_array_fget(x_4, x_5);
x_11 = lean_name_eq(x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_5);
x_12 = 0;
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_2 = lean_box(0);
x_5 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanLibConfig_toToml___spec__4(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lake_Glob_toString(x_5);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_13 = lean_array_uset(x_7, x_2, x_10);
x_2 = x_12;
x_3 = x_13;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at_Lake_LeanLibConfig_toToml___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_5, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_5);
x_8 = 1;
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_array_fget(x_3, x_5);
x_10 = lean_array_fget(x_4, x_5);
x_11 = l___private_Lake_Config_Glob_0__Lake_decEqGlob____x40_Lake_Config_Glob___hyg_196_(x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_5);
x_12 = 0;
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_2 = lean_box(0);
x_5 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at_Lake_LeanLibConfig_toToml___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_5, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_5);
x_8 = 1;
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_array_fget(x_3, x_5);
x_10 = lean_array_fget(x_4, x_5);
x_11 = lean_name_eq(x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_5);
x_12 = 0;
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_2 = lean_box(0);
x_5 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at_Lake_LeanLibConfig_toToml___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_5, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_5);
x_8 = 1;
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_array_fget(x_3, x_5);
x_10 = lean_array_fget(x_4, x_5);
x_11 = l___private_Lake_Config_Glob_0__Lake_decEqGlob____x40_Lake_Config_Glob___hyg_196_(x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_5);
x_12 = 0;
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_2 = lean_box(0);
x_5 = x_14;
goto _start;
}
}
}
}
static lean_object* _init_l_Lake_LeanLibConfig_toToml___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("defaultFacets", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_toToml___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanLibConfig_toToml___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_toToml___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("leanArts", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_toToml___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanLibConfig_toToml___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_toToml___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_toToml___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_LeanLibConfig_toToml___closed__5;
x_2 = l_Lake_LeanLibConfig_toToml___closed__4;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_toToml___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("libName", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_toToml___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanLibConfig_toToml___closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_toToml___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("globs", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_toToml___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanLibConfig_toToml___closed__9;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_toToml___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("roots", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_toToml___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanLibConfig_toToml___closed__11;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_toToml___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_LeanLibConfig_toToml___closed__6;
x_2 = lean_array_get_size(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toToml(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_77; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 7);
lean_inc(x_4);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*9);
x_6 = lean_ctor_get(x_1, 5);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = 0;
lean_inc(x_7);
x_9 = l_Lean_Name_toString(x_7, x_8);
x_10 = lean_ctor_get(x_1, 4);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
x_12 = lean_array_size(x_11);
x_13 = 0;
lean_inc(x_11);
x_14 = l_Array_mapMUnsafe_map___at_Lake_LeanLibConfig_globs___default___spec__1(x_12, x_13, x_11);
x_15 = l_Lake_LeanLibConfig_toToml___closed__5;
lean_inc(x_7);
x_16 = lean_array_push(x_15, x_7);
x_17 = lean_ctor_get(x_1, 2);
lean_inc(x_17);
x_18 = 1;
x_19 = l_Lean_Name_toString(x_7, x_18);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = l_Lake_instSmartInsertBackend___closed__1;
x_23 = l_Lake_PackageConfig_toToml___closed__27;
x_24 = l_Lake_Toml_RBDict_insert___rarg(x_22, x_23, x_21, x_2);
lean_inc(x_17);
x_25 = l_System_FilePath_normalize(x_17);
x_26 = l_Lake_PackageConfig_toToml___closed__29;
x_27 = lean_string_dec_eq(x_25, x_26);
lean_dec(x_25);
x_28 = lean_array_get_size(x_11);
x_29 = lean_array_get_size(x_16);
x_30 = lean_nat_dec_eq(x_28, x_29);
lean_dec(x_29);
lean_dec(x_28);
x_31 = lean_array_get_size(x_10);
x_32 = lean_array_get_size(x_14);
x_33 = lean_nat_dec_eq(x_31, x_32);
lean_dec(x_32);
lean_dec(x_31);
x_34 = lean_string_dec_eq(x_6, x_9);
lean_dec(x_9);
x_35 = lean_array_get_size(x_4);
x_36 = l_Lake_LeanLibConfig_toToml___closed__13;
x_37 = lean_nat_dec_eq(x_35, x_36);
lean_dec(x_35);
if (x_27 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_130 = l_Lake_mkRelPathString(x_17);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_20);
lean_ctor_set(x_131, 1, x_130);
x_132 = l_Lake_PackageConfig_toToml___closed__21;
x_133 = l_Lake_Toml_RBDict_insert___rarg(x_22, x_132, x_131, x_24);
x_77 = x_133;
goto block_129;
}
else
{
lean_dec(x_17);
x_77 = x_24;
goto block_129;
}
block_76:
{
uint8_t x_39; 
if (x_5 == 0)
{
x_39 = x_18;
goto block_75;
}
else
{
x_39 = x_8;
goto block_75;
}
block_75:
{
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_alloc_ctor(3, 1, 1);
lean_ctor_set(x_40, 0, x_20);
lean_ctor_set_uint8(x_40, sizeof(void*)*1, x_5);
x_41 = l_Lake_PackageConfig_toToml___closed__25;
x_42 = l_Lake_Toml_RBDict_insert___rarg(x_22, x_41, x_40, x_38);
if (x_37 == 0)
{
size_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_1);
x_43 = lean_array_size(x_4);
x_44 = l_Array_mapMUnsafe_map___at_Lake_LeanLibConfig_toToml___spec__1(x_43, x_13, x_4);
x_45 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_45, 0, x_20);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lake_LeanLibConfig_toToml___closed__2;
x_47 = l_Lake_Toml_RBDict_insert___rarg(x_22, x_46, x_45, x_42);
x_48 = l_Lake_LeanConfig_toToml(x_3, x_47);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_49 = l_Lake_LeanLibConfig_toToml___closed__6;
x_50 = lean_unsigned_to_nat(0u);
x_51 = l_Array_isEqvAux___at_Lake_LeanLibConfig_toToml___spec__2(x_1, lean_box(0), x_4, x_49, x_50);
lean_dec(x_1);
if (x_51 == 0)
{
size_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_52 = lean_array_size(x_4);
x_53 = l_Array_mapMUnsafe_map___at_Lake_LeanLibConfig_toToml___spec__1(x_52, x_13, x_4);
x_54 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_54, 0, x_20);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Lake_LeanLibConfig_toToml___closed__2;
x_56 = l_Lake_Toml_RBDict_insert___rarg(x_22, x_55, x_54, x_42);
x_57 = l_Lake_LeanConfig_toToml(x_3, x_56);
return x_57;
}
else
{
lean_object* x_58; 
lean_dec(x_4);
x_58 = l_Lake_LeanConfig_toToml(x_3, x_42);
return x_58;
}
}
}
else
{
if (x_37 == 0)
{
size_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_1);
x_59 = lean_array_size(x_4);
x_60 = l_Array_mapMUnsafe_map___at_Lake_LeanLibConfig_toToml___spec__1(x_59, x_13, x_4);
x_61 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_61, 0, x_20);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lake_LeanLibConfig_toToml___closed__2;
x_63 = l_Lake_Toml_RBDict_insert___rarg(x_22, x_62, x_61, x_38);
x_64 = l_Lake_LeanConfig_toToml(x_3, x_63);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_65 = l_Lake_LeanLibConfig_toToml___closed__6;
x_66 = lean_unsigned_to_nat(0u);
x_67 = l_Array_isEqvAux___at_Lake_LeanLibConfig_toToml___spec__3(x_1, lean_box(0), x_4, x_65, x_66);
lean_dec(x_1);
if (x_67 == 0)
{
size_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_68 = lean_array_size(x_4);
x_69 = l_Array_mapMUnsafe_map___at_Lake_LeanLibConfig_toToml___spec__1(x_68, x_13, x_4);
x_70 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_70, 0, x_20);
lean_ctor_set(x_70, 1, x_69);
x_71 = l_Lake_LeanLibConfig_toToml___closed__2;
x_72 = l_Lake_Toml_RBDict_insert___rarg(x_22, x_71, x_70, x_38);
x_73 = l_Lake_LeanConfig_toToml(x_3, x_72);
return x_73;
}
else
{
lean_object* x_74; 
lean_dec(x_4);
x_74 = l_Lake_LeanConfig_toToml(x_3, x_38);
return x_74;
}
}
}
}
}
block_129:
{
lean_object* x_78; 
if (x_30 == 0)
{
lean_object* x_105; 
lean_dec(x_16);
x_105 = lean_box(0);
x_78 = x_105;
goto block_104;
}
else
{
lean_object* x_106; uint8_t x_107; 
x_106 = lean_unsigned_to_nat(0u);
x_107 = l_Array_isEqvAux___at_Lake_LeanLibConfig_toToml___spec__6(x_1, lean_box(0), x_11, x_16, x_106);
lean_dec(x_16);
if (x_107 == 0)
{
lean_object* x_108; 
x_108 = lean_box(0);
x_78 = x_108;
goto block_104;
}
else
{
lean_dec(x_11);
if (x_33 == 0)
{
size_t x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_14);
x_109 = lean_array_size(x_10);
x_110 = l_Array_mapMUnsafe_map___at_Lake_LeanLibConfig_toToml___spec__4(x_109, x_13, x_10);
x_111 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_111, 0, x_20);
lean_ctor_set(x_111, 1, x_110);
x_112 = l_Lake_LeanLibConfig_toToml___closed__10;
x_113 = l_Lake_Toml_RBDict_insert___rarg(x_22, x_112, x_111, x_77);
if (x_34 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_20);
lean_ctor_set(x_114, 1, x_6);
x_115 = l_Lake_LeanLibConfig_toToml___closed__8;
x_116 = l_Lake_Toml_RBDict_insert___rarg(x_22, x_115, x_114, x_113);
x_38 = x_116;
goto block_76;
}
else
{
lean_dec(x_6);
x_38 = x_113;
goto block_76;
}
}
else
{
uint8_t x_117; 
x_117 = l_Array_isEqvAux___at_Lake_LeanLibConfig_toToml___spec__7(x_1, lean_box(0), x_10, x_14, x_106);
lean_dec(x_14);
if (x_117 == 0)
{
size_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_118 = lean_array_size(x_10);
x_119 = l_Array_mapMUnsafe_map___at_Lake_LeanLibConfig_toToml___spec__4(x_118, x_13, x_10);
x_120 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_120, 0, x_20);
lean_ctor_set(x_120, 1, x_119);
x_121 = l_Lake_LeanLibConfig_toToml___closed__10;
x_122 = l_Lake_Toml_RBDict_insert___rarg(x_22, x_121, x_120, x_77);
if (x_34 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_20);
lean_ctor_set(x_123, 1, x_6);
x_124 = l_Lake_LeanLibConfig_toToml___closed__8;
x_125 = l_Lake_Toml_RBDict_insert___rarg(x_22, x_124, x_123, x_122);
x_38 = x_125;
goto block_76;
}
else
{
lean_dec(x_6);
x_38 = x_122;
goto block_76;
}
}
else
{
lean_dec(x_10);
if (x_34 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_20);
lean_ctor_set(x_126, 1, x_6);
x_127 = l_Lake_LeanLibConfig_toToml___closed__8;
x_128 = l_Lake_Toml_RBDict_insert___rarg(x_22, x_127, x_126, x_77);
x_38 = x_128;
goto block_76;
}
else
{
lean_dec(x_6);
x_38 = x_77;
goto block_76;
}
}
}
}
}
block_104:
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_78);
x_79 = l_Array_mapMUnsafe_map___at_Lake_LeanLibConfig_toToml___spec__1(x_12, x_13, x_11);
x_80 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_80, 0, x_20);
lean_ctor_set(x_80, 1, x_79);
x_81 = l_Lake_LeanLibConfig_toToml___closed__12;
x_82 = l_Lake_Toml_RBDict_insert___rarg(x_22, x_81, x_80, x_77);
if (x_33 == 0)
{
size_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_14);
x_83 = lean_array_size(x_10);
x_84 = l_Array_mapMUnsafe_map___at_Lake_LeanLibConfig_toToml___spec__4(x_83, x_13, x_10);
x_85 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_85, 0, x_20);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lake_LeanLibConfig_toToml___closed__10;
x_87 = l_Lake_Toml_RBDict_insert___rarg(x_22, x_86, x_85, x_82);
if (x_34 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_20);
lean_ctor_set(x_88, 1, x_6);
x_89 = l_Lake_LeanLibConfig_toToml___closed__8;
x_90 = l_Lake_Toml_RBDict_insert___rarg(x_22, x_89, x_88, x_87);
x_38 = x_90;
goto block_76;
}
else
{
lean_dec(x_6);
x_38 = x_87;
goto block_76;
}
}
else
{
lean_object* x_91; uint8_t x_92; 
x_91 = lean_unsigned_to_nat(0u);
x_92 = l_Array_isEqvAux___at_Lake_LeanLibConfig_toToml___spec__5(x_1, lean_box(0), x_10, x_14, x_91);
lean_dec(x_14);
if (x_92 == 0)
{
size_t x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_93 = lean_array_size(x_10);
x_94 = l_Array_mapMUnsafe_map___at_Lake_LeanLibConfig_toToml___spec__4(x_93, x_13, x_10);
x_95 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_95, 0, x_20);
lean_ctor_set(x_95, 1, x_94);
x_96 = l_Lake_LeanLibConfig_toToml___closed__10;
x_97 = l_Lake_Toml_RBDict_insert___rarg(x_22, x_96, x_95, x_82);
if (x_34 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_20);
lean_ctor_set(x_98, 1, x_6);
x_99 = l_Lake_LeanLibConfig_toToml___closed__8;
x_100 = l_Lake_Toml_RBDict_insert___rarg(x_22, x_99, x_98, x_97);
x_38 = x_100;
goto block_76;
}
else
{
lean_dec(x_6);
x_38 = x_97;
goto block_76;
}
}
else
{
lean_dec(x_10);
if (x_34 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_20);
lean_ctor_set(x_101, 1, x_6);
x_102 = l_Lake_LeanLibConfig_toToml___closed__8;
x_103 = l_Lake_Toml_RBDict_insert___rarg(x_22, x_102, x_101, x_82);
x_38 = x_103;
goto block_76;
}
else
{
lean_dec(x_6);
x_38 = x_82;
goto block_76;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanLibConfig_toToml___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lake_LeanLibConfig_toToml___spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at_Lake_LeanLibConfig_toToml___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_isEqvAux___at_Lake_LeanLibConfig_toToml___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at_Lake_LeanLibConfig_toToml___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_isEqvAux___at_Lake_LeanLibConfig_toToml___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanLibConfig_toToml___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lake_LeanLibConfig_toToml___spec__4(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at_Lake_LeanLibConfig_toToml___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_isEqvAux___at_Lake_LeanLibConfig_toToml___spec__5(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at_Lake_LeanLibConfig_toToml___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_isEqvAux___at_Lake_LeanLibConfig_toToml___spec__6(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at_Lake_LeanLibConfig_toToml___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_isEqvAux___at_Lake_LeanLibConfig_toToml___spec__7(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTomlLeanLibConfig(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lake_Toml_encodeLeanOptions___closed__1;
x_3 = l_Lake_LeanLibConfig_toToml(x_1, x_2);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
static lean_object* _init_l_Lake_LeanExeConfig_toToml___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("supportInterpreter", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanExeConfig_toToml___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanExeConfig_toToml___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanExeConfig_toToml___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("exeName", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanExeConfig_toToml___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanExeConfig_toToml___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanExeConfig_toToml___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("root", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanExeConfig_toToml___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanExeConfig_toToml___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExeConfig_toToml(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*7);
x_5 = lean_ctor_get(x_1, 4);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = l_Lake_PackageConfig_toToml___closed__6;
x_8 = 0;
lean_inc(x_6);
x_9 = l_Lean_Name_toStringWithSep(x_7, x_8, x_6);
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
lean_dec(x_1);
x_12 = 1;
lean_inc(x_6);
x_13 = l_Lean_Name_toString(x_6, x_12);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l_Lake_instSmartInsertBackend___closed__1;
x_17 = l_Lake_PackageConfig_toToml___closed__27;
x_18 = l_Lake_Toml_RBDict_insert___rarg(x_16, x_17, x_15, x_2);
lean_inc(x_11);
x_19 = l_System_FilePath_normalize(x_11);
x_20 = l_Lake_PackageConfig_toToml___closed__29;
x_21 = lean_string_dec_eq(x_19, x_20);
lean_dec(x_19);
x_22 = lean_name_eq(x_10, x_6);
lean_dec(x_6);
x_23 = lean_string_dec_eq(x_5, x_9);
lean_dec(x_9);
if (x_21 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = l_Lake_mkRelPathString(x_11);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_14);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lake_PackageConfig_toToml___closed__21;
x_27 = l_Lake_Toml_RBDict_insert___rarg(x_16, x_26, x_25, x_18);
if (x_22 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = l_Lean_Name_toString(x_10, x_12);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_14);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lake_LeanExeConfig_toToml___closed__6;
x_31 = l_Lake_Toml_RBDict_insert___rarg(x_16, x_30, x_29, x_27);
if (x_23 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_14);
lean_ctor_set(x_32, 1, x_5);
x_33 = l_Lake_LeanExeConfig_toToml___closed__4;
x_34 = l_Lake_Toml_RBDict_insert___rarg(x_16, x_33, x_32, x_31);
if (x_4 == 0)
{
lean_object* x_35; 
x_35 = l_Lake_LeanConfig_toToml(x_3, x_34);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_alloc_ctor(3, 1, 1);
lean_ctor_set(x_36, 0, x_14);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_4);
x_37 = l_Lake_LeanExeConfig_toToml___closed__2;
x_38 = l_Lake_Toml_RBDict_insert___rarg(x_16, x_37, x_36, x_34);
x_39 = l_Lake_LeanConfig_toToml(x_3, x_38);
return x_39;
}
}
else
{
lean_dec(x_5);
if (x_4 == 0)
{
lean_object* x_40; 
x_40 = l_Lake_LeanConfig_toToml(x_3, x_31);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_alloc_ctor(3, 1, 1);
lean_ctor_set(x_41, 0, x_14);
lean_ctor_set_uint8(x_41, sizeof(void*)*1, x_4);
x_42 = l_Lake_LeanExeConfig_toToml___closed__2;
x_43 = l_Lake_Toml_RBDict_insert___rarg(x_16, x_42, x_41, x_31);
x_44 = l_Lake_LeanConfig_toToml(x_3, x_43);
return x_44;
}
}
}
else
{
lean_dec(x_10);
if (x_23 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_14);
lean_ctor_set(x_45, 1, x_5);
x_46 = l_Lake_LeanExeConfig_toToml___closed__4;
x_47 = l_Lake_Toml_RBDict_insert___rarg(x_16, x_46, x_45, x_27);
if (x_4 == 0)
{
lean_object* x_48; 
x_48 = l_Lake_LeanConfig_toToml(x_3, x_47);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_alloc_ctor(3, 1, 1);
lean_ctor_set(x_49, 0, x_14);
lean_ctor_set_uint8(x_49, sizeof(void*)*1, x_4);
x_50 = l_Lake_LeanExeConfig_toToml___closed__2;
x_51 = l_Lake_Toml_RBDict_insert___rarg(x_16, x_50, x_49, x_47);
x_52 = l_Lake_LeanConfig_toToml(x_3, x_51);
return x_52;
}
}
else
{
lean_dec(x_5);
if (x_4 == 0)
{
lean_object* x_53; 
x_53 = l_Lake_LeanConfig_toToml(x_3, x_27);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_alloc_ctor(3, 1, 1);
lean_ctor_set(x_54, 0, x_14);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_4);
x_55 = l_Lake_LeanExeConfig_toToml___closed__2;
x_56 = l_Lake_Toml_RBDict_insert___rarg(x_16, x_55, x_54, x_27);
x_57 = l_Lake_LeanConfig_toToml(x_3, x_56);
return x_57;
}
}
}
}
else
{
lean_dec(x_11);
if (x_22 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = l_Lean_Name_toString(x_10, x_12);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_14);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lake_LeanExeConfig_toToml___closed__6;
x_61 = l_Lake_Toml_RBDict_insert___rarg(x_16, x_60, x_59, x_18);
if (x_23 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_14);
lean_ctor_set(x_62, 1, x_5);
x_63 = l_Lake_LeanExeConfig_toToml___closed__4;
x_64 = l_Lake_Toml_RBDict_insert___rarg(x_16, x_63, x_62, x_61);
if (x_4 == 0)
{
lean_object* x_65; 
x_65 = l_Lake_LeanConfig_toToml(x_3, x_64);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_alloc_ctor(3, 1, 1);
lean_ctor_set(x_66, 0, x_14);
lean_ctor_set_uint8(x_66, sizeof(void*)*1, x_4);
x_67 = l_Lake_LeanExeConfig_toToml___closed__2;
x_68 = l_Lake_Toml_RBDict_insert___rarg(x_16, x_67, x_66, x_64);
x_69 = l_Lake_LeanConfig_toToml(x_3, x_68);
return x_69;
}
}
else
{
lean_dec(x_5);
if (x_4 == 0)
{
lean_object* x_70; 
x_70 = l_Lake_LeanConfig_toToml(x_3, x_61);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_alloc_ctor(3, 1, 1);
lean_ctor_set(x_71, 0, x_14);
lean_ctor_set_uint8(x_71, sizeof(void*)*1, x_4);
x_72 = l_Lake_LeanExeConfig_toToml___closed__2;
x_73 = l_Lake_Toml_RBDict_insert___rarg(x_16, x_72, x_71, x_61);
x_74 = l_Lake_LeanConfig_toToml(x_3, x_73);
return x_74;
}
}
}
else
{
lean_dec(x_10);
if (x_23 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_14);
lean_ctor_set(x_75, 1, x_5);
x_76 = l_Lake_LeanExeConfig_toToml___closed__4;
x_77 = l_Lake_Toml_RBDict_insert___rarg(x_16, x_76, x_75, x_18);
if (x_4 == 0)
{
lean_object* x_78; 
x_78 = l_Lake_LeanConfig_toToml(x_3, x_77);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_alloc_ctor(3, 1, 1);
lean_ctor_set(x_79, 0, x_14);
lean_ctor_set_uint8(x_79, sizeof(void*)*1, x_4);
x_80 = l_Lake_LeanExeConfig_toToml___closed__2;
x_81 = l_Lake_Toml_RBDict_insert___rarg(x_16, x_80, x_79, x_77);
x_82 = l_Lake_LeanConfig_toToml(x_3, x_81);
return x_82;
}
}
else
{
lean_dec(x_5);
if (x_4 == 0)
{
lean_object* x_83; 
x_83 = l_Lake_LeanConfig_toToml(x_3, x_18);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_alloc_ctor(3, 1, 1);
lean_ctor_set(x_84, 0, x_14);
lean_ctor_set_uint8(x_84, sizeof(void*)*1, x_4);
x_85 = l_Lake_LeanExeConfig_toToml___closed__2;
x_86 = l_Lake_Toml_RBDict_insert___rarg(x_16, x_85, x_84, x_18);
x_87 = l_Lake_LeanConfig_toToml(x_3, x_86);
return x_87;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instToTomlLeanExeConfig(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lake_Toml_encodeLeanOptions___closed__1;
x_3 = l_Lake_LeanExeConfig_toToml(x_1, x_2);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lake_Dependency_toToml___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 3);
lean_inc(x_6);
lean_dec(x_2);
x_7 = l_Lean_RBNode_fold___at_Lake_Dependency_toToml___spec__1(x_1, x_3);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
x_10 = l_Lake_instSmartInsertBackend___closed__1;
x_11 = l_Lake_Toml_RBDict_insert___rarg(x_10, x_4, x_9, x_7);
x_1 = x_11;
x_2 = x_6;
goto _start;
}
}
}
static lean_object* _init_l_Lake_Dependency_toToml___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("version", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_Dependency_toToml___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Dependency_toToml___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Dependency_toToml___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("scope", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_Dependency_toToml___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Dependency_toToml___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Dependency_toToml___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("options", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_Dependency_toToml___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Dependency_toToml___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Dependency_toToml___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("path", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_Dependency_toToml___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Dependency_toToml___closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Dependency_toToml___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("subDir", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_Dependency_toToml___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Dependency_toToml___closed__9;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Dependency_toToml___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rev", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_Dependency_toToml___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Dependency_toToml___closed__11;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Dependency_toToml___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("git", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_Dependency_toToml___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Dependency_toToml___closed__13;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_toToml(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_27; lean_object* x_28; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 4);
lean_inc(x_7);
lean_dec(x_1);
x_8 = 1;
x_9 = l_Lean_Name_toString(x_3, x_8);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l_Lake_instSmartInsertBackend___closed__1;
x_13 = l_Lake_PackageConfig_toToml___closed__27;
x_14 = l_Lake_Toml_RBDict_insert___rarg(x_12, x_13, x_11, x_2);
x_15 = l_Lake_PackageConfig_toToml___closed__5;
x_16 = lean_string_dec_eq(x_4, x_15);
if (x_16 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_10);
lean_ctor_set(x_55, 1, x_4);
x_56 = l_Lake_Dependency_toToml___closed__4;
x_57 = l_Lake_Toml_RBDict_insert___rarg(x_12, x_56, x_55, x_14);
if (lean_obj_tag(x_5) == 0)
{
if (lean_obj_tag(x_6) == 0)
{
x_17 = x_57;
x_18 = x_7;
goto block_26;
}
else
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_6, 0);
lean_inc(x_58);
lean_dec(x_6);
x_27 = x_57;
x_28 = x_58;
goto block_54;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_5, 0);
lean_inc(x_59);
lean_dec(x_5);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_10);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Lake_Dependency_toToml___closed__2;
x_62 = l_Lake_Toml_RBDict_insert___rarg(x_12, x_61, x_60, x_57);
if (lean_obj_tag(x_6) == 0)
{
x_17 = x_62;
x_18 = x_7;
goto block_26;
}
else
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_6, 0);
lean_inc(x_63);
lean_dec(x_6);
x_27 = x_62;
x_28 = x_63;
goto block_54;
}
}
}
else
{
lean_dec(x_4);
if (lean_obj_tag(x_5) == 0)
{
if (lean_obj_tag(x_6) == 0)
{
x_17 = x_14;
x_18 = x_7;
goto block_26;
}
else
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_6, 0);
lean_inc(x_64);
lean_dec(x_6);
x_27 = x_14;
x_28 = x_64;
goto block_54;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_5, 0);
lean_inc(x_65);
lean_dec(x_5);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_10);
lean_ctor_set(x_66, 1, x_65);
x_67 = l_Lake_Dependency_toToml___closed__2;
x_68 = l_Lake_Toml_RBDict_insert___rarg(x_12, x_67, x_66, x_14);
if (lean_obj_tag(x_6) == 0)
{
x_17 = x_68;
x_18 = x_7;
goto block_26;
}
else
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_6, 0);
lean_inc(x_69);
lean_dec(x_6);
x_27 = x_68;
x_28 = x_69;
goto block_54;
}
}
}
block_26:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = l_Lake_Toml_encodeLeanOptions___closed__1;
x_20 = l_Lean_RBNode_fold___at_Lake_Dependency_toToml___spec__1(x_19, x_18);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = l_Array_isEmpty___rarg(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_23, 0, x_10);
lean_ctor_set(x_23, 1, x_20);
x_24 = l_Lake_Dependency_toToml___closed__6;
x_25 = l_Lake_Toml_RBDict_insert___rarg(x_12, x_24, x_23, x_17);
return x_25;
}
else
{
lean_dec(x_20);
return x_17;
}
}
block_54:
{
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lake_mkRelPathString(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_10);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lake_Dependency_toToml___closed__8;
x_33 = l_Lake_Toml_RBDict_insert___rarg(x_12, x_32, x_31, x_27);
x_17 = x_33;
x_18 = x_7;
goto block_26;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_28, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_28, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_28, 2);
lean_inc(x_36);
lean_dec(x_28);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_10);
lean_ctor_set(x_37, 1, x_34);
x_38 = l_Lake_Dependency_toToml___closed__14;
x_39 = l_Lake_Toml_RBDict_insert___rarg(x_12, x_38, x_37, x_27);
if (lean_obj_tag(x_35) == 0)
{
if (lean_obj_tag(x_36) == 0)
{
x_17 = x_39;
x_18 = x_7;
goto block_26;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_36, 0);
lean_inc(x_40);
lean_dec(x_36);
x_41 = l_Lake_mkRelPathString(x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_10);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lake_Dependency_toToml___closed__10;
x_44 = l_Lake_Toml_RBDict_insert___rarg(x_12, x_43, x_42, x_39);
x_17 = x_44;
x_18 = x_7;
goto block_26;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_35, 0);
lean_inc(x_45);
lean_dec(x_35);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_10);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lake_Dependency_toToml___closed__12;
x_48 = l_Lake_Toml_RBDict_insert___rarg(x_12, x_47, x_46, x_39);
if (lean_obj_tag(x_36) == 0)
{
x_17 = x_48;
x_18 = x_7;
goto block_26;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_36, 0);
lean_inc(x_49);
lean_dec(x_36);
x_50 = l_Lake_mkRelPathString(x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_10);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lake_Dependency_toToml___closed__10;
x_53 = l_Lake_Toml_RBDict_insert___rarg(x_12, x_52, x_51, x_48);
x_17 = x_53;
x_18 = x_7;
goto block_26;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instToTomlDependency(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lake_Toml_encodeLeanOptions___closed__1;
x_3 = l_Lake_Dependency_toToml(x_1, x_2);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Package_mkTomlConfig___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lake_Toml_encodeLeanOptions___closed__1;
x_9 = l_Lake_Dependency_toToml(x_5, x_8);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_14 = lean_array_uset(x_7, x_2, x_11);
x_2 = x_13;
x_3 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Package_mkTomlConfig___spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lake_Toml_encodeLeanOptions___closed__1;
x_9 = l_Lake_LeanLibConfig_toToml(x_5, x_8);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_14 = lean_array_uset(x_7, x_2, x_11);
x_2 = x_13;
x_3 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Package_mkTomlConfig___spec__3(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lake_Toml_encodeLeanOptions___closed__1;
x_9 = l_Lake_LeanExeConfig_toToml(x_5, x_8);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_14 = lean_array_uset(x_7, x_2, x_11);
x_2 = x_13;
x_3 = x_14;
goto _start;
}
}
}
static lean_object* _init_l_Lake_Package_mkTomlConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_exe", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_mkTomlConfig___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Package_mkTomlConfig___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_mkTomlConfig___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_lib", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_mkTomlConfig___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Package_mkTomlConfig___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_mkTomlConfig___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("require", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_mkTomlConfig___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Package_mkTomlConfig___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_mkTomlConfig___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("defaultTargets", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_mkTomlConfig___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Package_mkTomlConfig___closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_mkTomlConfig___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lintDriverArgs", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_mkTomlConfig___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Package_mkTomlConfig___closed__9;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_mkTomlConfig___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lintDriver", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_mkTomlConfig___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Package_mkTomlConfig___closed__11;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_mkTomlConfig___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("testDriverArgs", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_mkTomlConfig___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Package_mkTomlConfig___closed__13;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_mkTomlConfig___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("testDriver", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_mkTomlConfig___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Package_mkTomlConfig___closed__15;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_mkTomlConfig(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; lean_object* x_48; lean_object* x_71; lean_object* x_95; 
x_3 = lean_ctor_get(x_1, 9);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 8);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_1, 7);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 12);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 20);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 17);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 18);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 16);
lean_inc(x_13);
lean_dec(x_1);
x_14 = l_Lake_PackageConfig_toToml(x_9, x_2);
x_15 = l_String_isEmpty(x_13);
x_16 = l_Array_isEmpty___rarg(x_12);
x_17 = l_String_isEmpty(x_11);
x_18 = l_Array_isEmpty___rarg(x_10);
x_19 = l_Array_isEmpty___rarg(x_8);
x_20 = l_Array_isEmpty___rarg(x_7);
x_21 = l_Array_isEmpty___rarg(x_6);
x_22 = l_Array_isEmpty___rarg(x_4);
if (x_15 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_118 = lean_box(0);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_13);
x_120 = l_Lake_instSmartInsertBackend___closed__1;
x_121 = l_Lake_Package_mkTomlConfig___closed__16;
x_122 = l_Lake_Toml_RBDict_insert___rarg(x_120, x_121, x_119, x_14);
if (x_16 == 0)
{
size_t x_123; size_t x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_123 = lean_array_size(x_12);
x_124 = 0;
x_125 = l_Array_mapMUnsafe_map___at_Lake_LeanConfig_toToml___spec__1(x_123, x_124, x_12);
x_126 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_126, 0, x_118);
lean_ctor_set(x_126, 1, x_125);
x_127 = l_Lake_Package_mkTomlConfig___closed__14;
x_128 = l_Lake_Toml_RBDict_insert___rarg(x_120, x_127, x_126, x_122);
if (x_17 == 0)
{
x_71 = x_128;
goto block_94;
}
else
{
lean_dec(x_11);
x_95 = x_128;
goto block_117;
}
}
else
{
lean_dec(x_12);
if (x_17 == 0)
{
x_71 = x_122;
goto block_94;
}
else
{
lean_dec(x_11);
x_95 = x_122;
goto block_117;
}
}
}
else
{
lean_dec(x_13);
if (x_16 == 0)
{
size_t x_129; size_t x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_129 = lean_array_size(x_12);
x_130 = 0;
x_131 = l_Array_mapMUnsafe_map___at_Lake_LeanConfig_toToml___spec__1(x_129, x_130, x_12);
x_132 = lean_box(0);
x_133 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_131);
x_134 = l_Lake_instSmartInsertBackend___closed__1;
x_135 = l_Lake_Package_mkTomlConfig___closed__14;
x_136 = l_Lake_Toml_RBDict_insert___rarg(x_134, x_135, x_133, x_14);
if (x_17 == 0)
{
x_71 = x_136;
goto block_94;
}
else
{
lean_dec(x_11);
x_95 = x_136;
goto block_117;
}
}
else
{
lean_dec(x_12);
if (x_17 == 0)
{
x_71 = x_14;
goto block_94;
}
else
{
lean_dec(x_11);
x_95 = x_14;
goto block_117;
}
}
}
block_47:
{
size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_24 = lean_array_size(x_7);
x_25 = 0;
x_26 = l_Array_mapMUnsafe_map___at_Lake_Package_mkTomlConfig___spec__1(x_24, x_25, x_7);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = l_Lake_instSmartInsertBackend___closed__1;
x_30 = l_Lake_Package_mkTomlConfig___closed__6;
x_31 = l_Lake_Toml_RBDict_insert___rarg(x_29, x_30, x_28, x_23);
if (x_21 == 0)
{
size_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_array_size(x_6);
x_33 = l_Array_mapMUnsafe_map___at_Lake_Package_mkTomlConfig___spec__2(x_32, x_25, x_6);
x_34 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_34, 0, x_27);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lake_Package_mkTomlConfig___closed__4;
x_36 = l_Lake_Toml_RBDict_insert___rarg(x_29, x_35, x_34, x_31);
if (x_22 == 0)
{
size_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_array_size(x_4);
x_38 = l_Array_mapMUnsafe_map___at_Lake_Package_mkTomlConfig___spec__3(x_37, x_25, x_4);
x_39 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_39, 0, x_27);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lake_Package_mkTomlConfig___closed__2;
x_41 = l_Lake_Toml_RBDict_insert___rarg(x_29, x_40, x_39, x_36);
return x_41;
}
else
{
lean_dec(x_4);
return x_36;
}
}
else
{
lean_dec(x_6);
if (x_22 == 0)
{
size_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_array_size(x_4);
x_43 = l_Array_mapMUnsafe_map___at_Lake_Package_mkTomlConfig___spec__3(x_42, x_25, x_4);
x_44 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_44, 0, x_27);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lake_Package_mkTomlConfig___closed__2;
x_46 = l_Lake_Toml_RBDict_insert___rarg(x_29, x_45, x_44, x_31);
return x_46;
}
else
{
lean_dec(x_4);
return x_31;
}
}
}
block_70:
{
if (x_21 == 0)
{
size_t x_49; size_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_49 = lean_array_size(x_6);
x_50 = 0;
x_51 = l_Array_mapMUnsafe_map___at_Lake_Package_mkTomlConfig___spec__2(x_49, x_50, x_6);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
x_54 = l_Lake_instSmartInsertBackend___closed__1;
x_55 = l_Lake_Package_mkTomlConfig___closed__4;
x_56 = l_Lake_Toml_RBDict_insert___rarg(x_54, x_55, x_53, x_48);
if (x_22 == 0)
{
size_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_57 = lean_array_size(x_4);
x_58 = l_Array_mapMUnsafe_map___at_Lake_Package_mkTomlConfig___spec__3(x_57, x_50, x_4);
x_59 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_59, 0, x_52);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lake_Package_mkTomlConfig___closed__2;
x_61 = l_Lake_Toml_RBDict_insert___rarg(x_54, x_60, x_59, x_56);
return x_61;
}
else
{
lean_dec(x_4);
return x_56;
}
}
else
{
lean_dec(x_6);
if (x_22 == 0)
{
size_t x_62; size_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_62 = lean_array_size(x_4);
x_63 = 0;
x_64 = l_Array_mapMUnsafe_map___at_Lake_Package_mkTomlConfig___spec__3(x_62, x_63, x_4);
x_65 = lean_box(0);
x_66 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
x_67 = l_Lake_instSmartInsertBackend___closed__1;
x_68 = l_Lake_Package_mkTomlConfig___closed__2;
x_69 = l_Lake_Toml_RBDict_insert___rarg(x_67, x_68, x_66, x_48);
return x_69;
}
else
{
lean_dec(x_4);
return x_48;
}
}
}
block_94:
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_11);
x_74 = l_Lake_instSmartInsertBackend___closed__1;
x_75 = l_Lake_Package_mkTomlConfig___closed__12;
x_76 = l_Lake_Toml_RBDict_insert___rarg(x_74, x_75, x_73, x_71);
if (x_18 == 0)
{
size_t x_77; size_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_77 = lean_array_size(x_10);
x_78 = 0;
x_79 = l_Array_mapMUnsafe_map___at_Lake_LeanConfig_toToml___spec__1(x_77, x_78, x_10);
x_80 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_80, 0, x_72);
lean_ctor_set(x_80, 1, x_79);
x_81 = l_Lake_Package_mkTomlConfig___closed__10;
x_82 = l_Lake_Toml_RBDict_insert___rarg(x_74, x_81, x_80, x_76);
if (x_19 == 0)
{
size_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_83 = lean_array_size(x_8);
x_84 = l_Array_mapMUnsafe_map___at_Lake_LeanLibConfig_toToml___spec__1(x_83, x_78, x_8);
x_85 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_85, 0, x_72);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lake_Package_mkTomlConfig___closed__8;
x_87 = l_Lake_Toml_RBDict_insert___rarg(x_74, x_86, x_85, x_82);
if (x_20 == 0)
{
x_23 = x_87;
goto block_47;
}
else
{
lean_dec(x_7);
x_48 = x_87;
goto block_70;
}
}
else
{
lean_dec(x_8);
if (x_20 == 0)
{
x_23 = x_82;
goto block_47;
}
else
{
lean_dec(x_7);
x_48 = x_82;
goto block_70;
}
}
}
else
{
lean_dec(x_10);
if (x_19 == 0)
{
size_t x_88; size_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_88 = lean_array_size(x_8);
x_89 = 0;
x_90 = l_Array_mapMUnsafe_map___at_Lake_LeanLibConfig_toToml___spec__1(x_88, x_89, x_8);
x_91 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_91, 0, x_72);
lean_ctor_set(x_91, 1, x_90);
x_92 = l_Lake_Package_mkTomlConfig___closed__8;
x_93 = l_Lake_Toml_RBDict_insert___rarg(x_74, x_92, x_91, x_76);
if (x_20 == 0)
{
x_23 = x_93;
goto block_47;
}
else
{
lean_dec(x_7);
x_48 = x_93;
goto block_70;
}
}
else
{
lean_dec(x_8);
if (x_20 == 0)
{
x_23 = x_76;
goto block_47;
}
else
{
lean_dec(x_7);
x_48 = x_76;
goto block_70;
}
}
}
}
block_117:
{
if (x_18 == 0)
{
size_t x_96; size_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_96 = lean_array_size(x_10);
x_97 = 0;
x_98 = l_Array_mapMUnsafe_map___at_Lake_LeanConfig_toToml___spec__1(x_96, x_97, x_10);
x_99 = lean_box(0);
x_100 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_98);
x_101 = l_Lake_instSmartInsertBackend___closed__1;
x_102 = l_Lake_Package_mkTomlConfig___closed__10;
x_103 = l_Lake_Toml_RBDict_insert___rarg(x_101, x_102, x_100, x_95);
if (x_19 == 0)
{
size_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_104 = lean_array_size(x_8);
x_105 = l_Array_mapMUnsafe_map___at_Lake_LeanLibConfig_toToml___spec__1(x_104, x_97, x_8);
x_106 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_106, 0, x_99);
lean_ctor_set(x_106, 1, x_105);
x_107 = l_Lake_Package_mkTomlConfig___closed__8;
x_108 = l_Lake_Toml_RBDict_insert___rarg(x_101, x_107, x_106, x_103);
if (x_20 == 0)
{
x_23 = x_108;
goto block_47;
}
else
{
lean_dec(x_7);
x_48 = x_108;
goto block_70;
}
}
else
{
lean_dec(x_8);
if (x_20 == 0)
{
x_23 = x_103;
goto block_47;
}
else
{
lean_dec(x_7);
x_48 = x_103;
goto block_70;
}
}
}
else
{
lean_dec(x_10);
if (x_19 == 0)
{
size_t x_109; size_t x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_109 = lean_array_size(x_8);
x_110 = 0;
x_111 = l_Array_mapMUnsafe_map___at_Lake_LeanLibConfig_toToml___spec__1(x_109, x_110, x_8);
x_112 = lean_box(0);
x_113 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_111);
x_114 = l_Lake_instSmartInsertBackend___closed__1;
x_115 = l_Lake_Package_mkTomlConfig___closed__8;
x_116 = l_Lake_Toml_RBDict_insert___rarg(x_114, x_115, x_113, x_95);
if (x_20 == 0)
{
x_23 = x_116;
goto block_47;
}
else
{
lean_dec(x_7);
x_48 = x_116;
goto block_70;
}
}
else
{
lean_dec(x_8);
if (x_20 == 0)
{
x_23 = x_95;
goto block_47;
}
else
{
lean_dec(x_7);
x_48 = x_95;
goto block_70;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Package_mkTomlConfig___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lake_Package_mkTomlConfig___spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Package_mkTomlConfig___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lake_Package_mkTomlConfig___spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Package_mkTomlConfig___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lake_Package_mkTomlConfig___spec__3(x_4, x_5, x_3);
return x_6;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Toml_Encode(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_Package(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_CLI_Translate_Toml(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Toml_Encode(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Package(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instSmartInsertBackend___closed__1 = _init_l_Lake_instSmartInsertBackend___closed__1();
lean_mark_persistent(l_Lake_instSmartInsertBackend___closed__1);
l_Lake_instToTomlLeanOptionValue___closed__1 = _init_l_Lake_instToTomlLeanOptionValue___closed__1();
lean_mark_persistent(l_Lake_instToTomlLeanOptionValue___closed__1);
l_Lake_instToTomlLeanOptionValue = _init_l_Lake_instToTomlLeanOptionValue();
lean_mark_persistent(l_Lake_instToTomlLeanOptionValue);
l_Lake_Toml_encodeLeanOptions___closed__1 = _init_l_Lake_Toml_encodeLeanOptions___closed__1();
lean_mark_persistent(l_Lake_Toml_encodeLeanOptions___closed__1);
l_Lake_Toml_leanOptionsEncoder___closed__1 = _init_l_Lake_Toml_leanOptionsEncoder___closed__1();
lean_mark_persistent(l_Lake_Toml_leanOptionsEncoder___closed__1);
l_Lake_Toml_leanOptionsEncoder = _init_l_Lake_Toml_leanOptionsEncoder();
lean_mark_persistent(l_Lake_Toml_leanOptionsEncoder);
l_Lake_WorkspaceConfig_toToml___closed__1 = _init_l_Lake_WorkspaceConfig_toToml___closed__1();
lean_mark_persistent(l_Lake_WorkspaceConfig_toToml___closed__1);
l_Lake_WorkspaceConfig_toToml___closed__2 = _init_l_Lake_WorkspaceConfig_toToml___closed__2();
lean_mark_persistent(l_Lake_WorkspaceConfig_toToml___closed__2);
l_Lake_WorkspaceConfig_toToml___closed__3 = _init_l_Lake_WorkspaceConfig_toToml___closed__3();
lean_mark_persistent(l_Lake_WorkspaceConfig_toToml___closed__3);
l_Lake_LeanConfig_toToml___closed__1 = _init_l_Lake_LeanConfig_toToml___closed__1();
lean_mark_persistent(l_Lake_LeanConfig_toToml___closed__1);
l_Lake_LeanConfig_toToml___closed__2 = _init_l_Lake_LeanConfig_toToml___closed__2();
lean_mark_persistent(l_Lake_LeanConfig_toToml___closed__2);
l_Lake_LeanConfig_toToml___closed__3 = _init_l_Lake_LeanConfig_toToml___closed__3();
lean_mark_persistent(l_Lake_LeanConfig_toToml___closed__3);
l_Lake_LeanConfig_toToml___closed__4 = _init_l_Lake_LeanConfig_toToml___closed__4();
lean_mark_persistent(l_Lake_LeanConfig_toToml___closed__4);
l_Lake_LeanConfig_toToml___closed__5 = _init_l_Lake_LeanConfig_toToml___closed__5();
lean_mark_persistent(l_Lake_LeanConfig_toToml___closed__5);
l_Lake_LeanConfig_toToml___closed__6 = _init_l_Lake_LeanConfig_toToml___closed__6();
lean_mark_persistent(l_Lake_LeanConfig_toToml___closed__6);
l_Lake_LeanConfig_toToml___closed__7 = _init_l_Lake_LeanConfig_toToml___closed__7();
lean_mark_persistent(l_Lake_LeanConfig_toToml___closed__7);
l_Lake_LeanConfig_toToml___closed__8 = _init_l_Lake_LeanConfig_toToml___closed__8();
lean_mark_persistent(l_Lake_LeanConfig_toToml___closed__8);
l_Lake_LeanConfig_toToml___closed__9 = _init_l_Lake_LeanConfig_toToml___closed__9();
lean_mark_persistent(l_Lake_LeanConfig_toToml___closed__9);
l_Lake_LeanConfig_toToml___closed__10 = _init_l_Lake_LeanConfig_toToml___closed__10();
lean_mark_persistent(l_Lake_LeanConfig_toToml___closed__10);
l_Lake_LeanConfig_toToml___closed__11 = _init_l_Lake_LeanConfig_toToml___closed__11();
lean_mark_persistent(l_Lake_LeanConfig_toToml___closed__11);
l_Lake_LeanConfig_toToml___closed__12 = _init_l_Lake_LeanConfig_toToml___closed__12();
lean_mark_persistent(l_Lake_LeanConfig_toToml___closed__12);
l_Lake_LeanConfig_toToml___closed__13 = _init_l_Lake_LeanConfig_toToml___closed__13();
lean_mark_persistent(l_Lake_LeanConfig_toToml___closed__13);
l_Lake_LeanConfig_toToml___closed__14 = _init_l_Lake_LeanConfig_toToml___closed__14();
lean_mark_persistent(l_Lake_LeanConfig_toToml___closed__14);
l_Lake_LeanConfig_toToml___closed__15 = _init_l_Lake_LeanConfig_toToml___closed__15();
lean_mark_persistent(l_Lake_LeanConfig_toToml___closed__15);
l_Lake_LeanConfig_toToml___closed__16 = _init_l_Lake_LeanConfig_toToml___closed__16();
lean_mark_persistent(l_Lake_LeanConfig_toToml___closed__16);
l_Lake_LeanConfig_toToml___closed__17 = _init_l_Lake_LeanConfig_toToml___closed__17();
lean_mark_persistent(l_Lake_LeanConfig_toToml___closed__17);
l_Lake_LeanConfig_toToml___closed__18 = _init_l_Lake_LeanConfig_toToml___closed__18();
lean_mark_persistent(l_Lake_LeanConfig_toToml___closed__18);
l_Lake_LeanConfig_toToml___closed__19 = _init_l_Lake_LeanConfig_toToml___closed__19();
lean_mark_persistent(l_Lake_LeanConfig_toToml___closed__19);
l_Lake_LeanConfig_toToml___closed__20 = _init_l_Lake_LeanConfig_toToml___closed__20();
lean_mark_persistent(l_Lake_LeanConfig_toToml___closed__20);
l_Lake_LeanConfig_toToml___closed__21 = _init_l_Lake_LeanConfig_toToml___closed__21();
lean_mark_persistent(l_Lake_LeanConfig_toToml___closed__21);
l_Lake_LeanConfig_toToml___closed__22 = _init_l_Lake_LeanConfig_toToml___closed__22();
lean_mark_persistent(l_Lake_LeanConfig_toToml___closed__22);
l_Lake_PackageConfig_toToml___closed__1 = _init_l_Lake_PackageConfig_toToml___closed__1();
lean_mark_persistent(l_Lake_PackageConfig_toToml___closed__1);
l_Lake_PackageConfig_toToml___closed__2 = _init_l_Lake_PackageConfig_toToml___closed__2();
lean_mark_persistent(l_Lake_PackageConfig_toToml___closed__2);
l_Lake_PackageConfig_toToml___closed__3 = _init_l_Lake_PackageConfig_toToml___closed__3();
lean_mark_persistent(l_Lake_PackageConfig_toToml___closed__3);
l_Lake_PackageConfig_toToml___closed__4 = _init_l_Lake_PackageConfig_toToml___closed__4();
lean_mark_persistent(l_Lake_PackageConfig_toToml___closed__4);
l_Lake_PackageConfig_toToml___closed__5 = _init_l_Lake_PackageConfig_toToml___closed__5();
lean_mark_persistent(l_Lake_PackageConfig_toToml___closed__5);
l_Lake_PackageConfig_toToml___closed__6 = _init_l_Lake_PackageConfig_toToml___closed__6();
lean_mark_persistent(l_Lake_PackageConfig_toToml___closed__6);
l_Lake_PackageConfig_toToml___closed__7 = _init_l_Lake_PackageConfig_toToml___closed__7();
lean_mark_persistent(l_Lake_PackageConfig_toToml___closed__7);
l_Lake_PackageConfig_toToml___closed__8 = _init_l_Lake_PackageConfig_toToml___closed__8();
lean_mark_persistent(l_Lake_PackageConfig_toToml___closed__8);
l_Lake_PackageConfig_toToml___closed__9 = _init_l_Lake_PackageConfig_toToml___closed__9();
lean_mark_persistent(l_Lake_PackageConfig_toToml___closed__9);
l_Lake_PackageConfig_toToml___closed__10 = _init_l_Lake_PackageConfig_toToml___closed__10();
lean_mark_persistent(l_Lake_PackageConfig_toToml___closed__10);
l_Lake_PackageConfig_toToml___closed__11 = _init_l_Lake_PackageConfig_toToml___closed__11();
lean_mark_persistent(l_Lake_PackageConfig_toToml___closed__11);
l_Lake_PackageConfig_toToml___closed__12 = _init_l_Lake_PackageConfig_toToml___closed__12();
lean_mark_persistent(l_Lake_PackageConfig_toToml___closed__12);
l_Lake_PackageConfig_toToml___closed__13 = _init_l_Lake_PackageConfig_toToml___closed__13();
lean_mark_persistent(l_Lake_PackageConfig_toToml___closed__13);
l_Lake_PackageConfig_toToml___closed__14 = _init_l_Lake_PackageConfig_toToml___closed__14();
lean_mark_persistent(l_Lake_PackageConfig_toToml___closed__14);
l_Lake_PackageConfig_toToml___closed__15 = _init_l_Lake_PackageConfig_toToml___closed__15();
lean_mark_persistent(l_Lake_PackageConfig_toToml___closed__15);
l_Lake_PackageConfig_toToml___closed__16 = _init_l_Lake_PackageConfig_toToml___closed__16();
lean_mark_persistent(l_Lake_PackageConfig_toToml___closed__16);
l_Lake_PackageConfig_toToml___closed__17 = _init_l_Lake_PackageConfig_toToml___closed__17();
lean_mark_persistent(l_Lake_PackageConfig_toToml___closed__17);
l_Lake_PackageConfig_toToml___closed__18 = _init_l_Lake_PackageConfig_toToml___closed__18();
lean_mark_persistent(l_Lake_PackageConfig_toToml___closed__18);
l_Lake_PackageConfig_toToml___closed__19 = _init_l_Lake_PackageConfig_toToml___closed__19();
lean_mark_persistent(l_Lake_PackageConfig_toToml___closed__19);
l_Lake_PackageConfig_toToml___closed__20 = _init_l_Lake_PackageConfig_toToml___closed__20();
lean_mark_persistent(l_Lake_PackageConfig_toToml___closed__20);
l_Lake_PackageConfig_toToml___closed__21 = _init_l_Lake_PackageConfig_toToml___closed__21();
lean_mark_persistent(l_Lake_PackageConfig_toToml___closed__21);
l_Lake_PackageConfig_toToml___closed__22 = _init_l_Lake_PackageConfig_toToml___closed__22();
lean_mark_persistent(l_Lake_PackageConfig_toToml___closed__22);
l_Lake_PackageConfig_toToml___closed__23 = _init_l_Lake_PackageConfig_toToml___closed__23();
lean_mark_persistent(l_Lake_PackageConfig_toToml___closed__23);
l_Lake_PackageConfig_toToml___closed__24 = _init_l_Lake_PackageConfig_toToml___closed__24();
lean_mark_persistent(l_Lake_PackageConfig_toToml___closed__24);
l_Lake_PackageConfig_toToml___closed__25 = _init_l_Lake_PackageConfig_toToml___closed__25();
lean_mark_persistent(l_Lake_PackageConfig_toToml___closed__25);
l_Lake_PackageConfig_toToml___closed__26 = _init_l_Lake_PackageConfig_toToml___closed__26();
lean_mark_persistent(l_Lake_PackageConfig_toToml___closed__26);
l_Lake_PackageConfig_toToml___closed__27 = _init_l_Lake_PackageConfig_toToml___closed__27();
lean_mark_persistent(l_Lake_PackageConfig_toToml___closed__27);
l_Lake_PackageConfig_toToml___closed__28 = _init_l_Lake_PackageConfig_toToml___closed__28();
lean_mark_persistent(l_Lake_PackageConfig_toToml___closed__28);
l_Lake_PackageConfig_toToml___closed__29 = _init_l_Lake_PackageConfig_toToml___closed__29();
lean_mark_persistent(l_Lake_PackageConfig_toToml___closed__29);
l_Lake_PackageConfig_toToml___closed__30 = _init_l_Lake_PackageConfig_toToml___closed__30();
lean_mark_persistent(l_Lake_PackageConfig_toToml___closed__30);
l_Lake_PackageConfig_toToml___closed__31 = _init_l_Lake_PackageConfig_toToml___closed__31();
lean_mark_persistent(l_Lake_PackageConfig_toToml___closed__31);
l_Lake_PackageConfig_toToml___closed__32 = _init_l_Lake_PackageConfig_toToml___closed__32();
lean_mark_persistent(l_Lake_PackageConfig_toToml___closed__32);
l_Lake_PackageConfig_toToml___closed__33 = _init_l_Lake_PackageConfig_toToml___closed__33();
lean_mark_persistent(l_Lake_PackageConfig_toToml___closed__33);
l_Lake_PackageConfig_toToml___closed__34 = _init_l_Lake_PackageConfig_toToml___closed__34();
lean_mark_persistent(l_Lake_PackageConfig_toToml___closed__34);
l_Lake_LeanLibConfig_toToml___closed__1 = _init_l_Lake_LeanLibConfig_toToml___closed__1();
lean_mark_persistent(l_Lake_LeanLibConfig_toToml___closed__1);
l_Lake_LeanLibConfig_toToml___closed__2 = _init_l_Lake_LeanLibConfig_toToml___closed__2();
lean_mark_persistent(l_Lake_LeanLibConfig_toToml___closed__2);
l_Lake_LeanLibConfig_toToml___closed__3 = _init_l_Lake_LeanLibConfig_toToml___closed__3();
lean_mark_persistent(l_Lake_LeanLibConfig_toToml___closed__3);
l_Lake_LeanLibConfig_toToml___closed__4 = _init_l_Lake_LeanLibConfig_toToml___closed__4();
lean_mark_persistent(l_Lake_LeanLibConfig_toToml___closed__4);
l_Lake_LeanLibConfig_toToml___closed__5 = _init_l_Lake_LeanLibConfig_toToml___closed__5();
lean_mark_persistent(l_Lake_LeanLibConfig_toToml___closed__5);
l_Lake_LeanLibConfig_toToml___closed__6 = _init_l_Lake_LeanLibConfig_toToml___closed__6();
lean_mark_persistent(l_Lake_LeanLibConfig_toToml___closed__6);
l_Lake_LeanLibConfig_toToml___closed__7 = _init_l_Lake_LeanLibConfig_toToml___closed__7();
lean_mark_persistent(l_Lake_LeanLibConfig_toToml___closed__7);
l_Lake_LeanLibConfig_toToml___closed__8 = _init_l_Lake_LeanLibConfig_toToml___closed__8();
lean_mark_persistent(l_Lake_LeanLibConfig_toToml___closed__8);
l_Lake_LeanLibConfig_toToml___closed__9 = _init_l_Lake_LeanLibConfig_toToml___closed__9();
lean_mark_persistent(l_Lake_LeanLibConfig_toToml___closed__9);
l_Lake_LeanLibConfig_toToml___closed__10 = _init_l_Lake_LeanLibConfig_toToml___closed__10();
lean_mark_persistent(l_Lake_LeanLibConfig_toToml___closed__10);
l_Lake_LeanLibConfig_toToml___closed__11 = _init_l_Lake_LeanLibConfig_toToml___closed__11();
lean_mark_persistent(l_Lake_LeanLibConfig_toToml___closed__11);
l_Lake_LeanLibConfig_toToml___closed__12 = _init_l_Lake_LeanLibConfig_toToml___closed__12();
lean_mark_persistent(l_Lake_LeanLibConfig_toToml___closed__12);
l_Lake_LeanLibConfig_toToml___closed__13 = _init_l_Lake_LeanLibConfig_toToml___closed__13();
lean_mark_persistent(l_Lake_LeanLibConfig_toToml___closed__13);
l_Lake_LeanExeConfig_toToml___closed__1 = _init_l_Lake_LeanExeConfig_toToml___closed__1();
lean_mark_persistent(l_Lake_LeanExeConfig_toToml___closed__1);
l_Lake_LeanExeConfig_toToml___closed__2 = _init_l_Lake_LeanExeConfig_toToml___closed__2();
lean_mark_persistent(l_Lake_LeanExeConfig_toToml___closed__2);
l_Lake_LeanExeConfig_toToml___closed__3 = _init_l_Lake_LeanExeConfig_toToml___closed__3();
lean_mark_persistent(l_Lake_LeanExeConfig_toToml___closed__3);
l_Lake_LeanExeConfig_toToml___closed__4 = _init_l_Lake_LeanExeConfig_toToml___closed__4();
lean_mark_persistent(l_Lake_LeanExeConfig_toToml___closed__4);
l_Lake_LeanExeConfig_toToml___closed__5 = _init_l_Lake_LeanExeConfig_toToml___closed__5();
lean_mark_persistent(l_Lake_LeanExeConfig_toToml___closed__5);
l_Lake_LeanExeConfig_toToml___closed__6 = _init_l_Lake_LeanExeConfig_toToml___closed__6();
lean_mark_persistent(l_Lake_LeanExeConfig_toToml___closed__6);
l_Lake_Dependency_toToml___closed__1 = _init_l_Lake_Dependency_toToml___closed__1();
lean_mark_persistent(l_Lake_Dependency_toToml___closed__1);
l_Lake_Dependency_toToml___closed__2 = _init_l_Lake_Dependency_toToml___closed__2();
lean_mark_persistent(l_Lake_Dependency_toToml___closed__2);
l_Lake_Dependency_toToml___closed__3 = _init_l_Lake_Dependency_toToml___closed__3();
lean_mark_persistent(l_Lake_Dependency_toToml___closed__3);
l_Lake_Dependency_toToml___closed__4 = _init_l_Lake_Dependency_toToml___closed__4();
lean_mark_persistent(l_Lake_Dependency_toToml___closed__4);
l_Lake_Dependency_toToml___closed__5 = _init_l_Lake_Dependency_toToml___closed__5();
lean_mark_persistent(l_Lake_Dependency_toToml___closed__5);
l_Lake_Dependency_toToml___closed__6 = _init_l_Lake_Dependency_toToml___closed__6();
lean_mark_persistent(l_Lake_Dependency_toToml___closed__6);
l_Lake_Dependency_toToml___closed__7 = _init_l_Lake_Dependency_toToml___closed__7();
lean_mark_persistent(l_Lake_Dependency_toToml___closed__7);
l_Lake_Dependency_toToml___closed__8 = _init_l_Lake_Dependency_toToml___closed__8();
lean_mark_persistent(l_Lake_Dependency_toToml___closed__8);
l_Lake_Dependency_toToml___closed__9 = _init_l_Lake_Dependency_toToml___closed__9();
lean_mark_persistent(l_Lake_Dependency_toToml___closed__9);
l_Lake_Dependency_toToml___closed__10 = _init_l_Lake_Dependency_toToml___closed__10();
lean_mark_persistent(l_Lake_Dependency_toToml___closed__10);
l_Lake_Dependency_toToml___closed__11 = _init_l_Lake_Dependency_toToml___closed__11();
lean_mark_persistent(l_Lake_Dependency_toToml___closed__11);
l_Lake_Dependency_toToml___closed__12 = _init_l_Lake_Dependency_toToml___closed__12();
lean_mark_persistent(l_Lake_Dependency_toToml___closed__12);
l_Lake_Dependency_toToml___closed__13 = _init_l_Lake_Dependency_toToml___closed__13();
lean_mark_persistent(l_Lake_Dependency_toToml___closed__13);
l_Lake_Dependency_toToml___closed__14 = _init_l_Lake_Dependency_toToml___closed__14();
lean_mark_persistent(l_Lake_Dependency_toToml___closed__14);
l_Lake_Package_mkTomlConfig___closed__1 = _init_l_Lake_Package_mkTomlConfig___closed__1();
lean_mark_persistent(l_Lake_Package_mkTomlConfig___closed__1);
l_Lake_Package_mkTomlConfig___closed__2 = _init_l_Lake_Package_mkTomlConfig___closed__2();
lean_mark_persistent(l_Lake_Package_mkTomlConfig___closed__2);
l_Lake_Package_mkTomlConfig___closed__3 = _init_l_Lake_Package_mkTomlConfig___closed__3();
lean_mark_persistent(l_Lake_Package_mkTomlConfig___closed__3);
l_Lake_Package_mkTomlConfig___closed__4 = _init_l_Lake_Package_mkTomlConfig___closed__4();
lean_mark_persistent(l_Lake_Package_mkTomlConfig___closed__4);
l_Lake_Package_mkTomlConfig___closed__5 = _init_l_Lake_Package_mkTomlConfig___closed__5();
lean_mark_persistent(l_Lake_Package_mkTomlConfig___closed__5);
l_Lake_Package_mkTomlConfig___closed__6 = _init_l_Lake_Package_mkTomlConfig___closed__6();
lean_mark_persistent(l_Lake_Package_mkTomlConfig___closed__6);
l_Lake_Package_mkTomlConfig___closed__7 = _init_l_Lake_Package_mkTomlConfig___closed__7();
lean_mark_persistent(l_Lake_Package_mkTomlConfig___closed__7);
l_Lake_Package_mkTomlConfig___closed__8 = _init_l_Lake_Package_mkTomlConfig___closed__8();
lean_mark_persistent(l_Lake_Package_mkTomlConfig___closed__8);
l_Lake_Package_mkTomlConfig___closed__9 = _init_l_Lake_Package_mkTomlConfig___closed__9();
lean_mark_persistent(l_Lake_Package_mkTomlConfig___closed__9);
l_Lake_Package_mkTomlConfig___closed__10 = _init_l_Lake_Package_mkTomlConfig___closed__10();
lean_mark_persistent(l_Lake_Package_mkTomlConfig___closed__10);
l_Lake_Package_mkTomlConfig___closed__11 = _init_l_Lake_Package_mkTomlConfig___closed__11();
lean_mark_persistent(l_Lake_Package_mkTomlConfig___closed__11);
l_Lake_Package_mkTomlConfig___closed__12 = _init_l_Lake_Package_mkTomlConfig___closed__12();
lean_mark_persistent(l_Lake_Package_mkTomlConfig___closed__12);
l_Lake_Package_mkTomlConfig___closed__13 = _init_l_Lake_Package_mkTomlConfig___closed__13();
lean_mark_persistent(l_Lake_Package_mkTomlConfig___closed__13);
l_Lake_Package_mkTomlConfig___closed__14 = _init_l_Lake_Package_mkTomlConfig___closed__14();
lean_mark_persistent(l_Lake_Package_mkTomlConfig___closed__14);
l_Lake_Package_mkTomlConfig___closed__15 = _init_l_Lake_Package_mkTomlConfig___closed__15();
lean_mark_persistent(l_Lake_Package_mkTomlConfig___closed__15);
l_Lake_Package_mkTomlConfig___closed__16 = _init_l_Lake_Package_mkTomlConfig___closed__16();
lean_mark_persistent(l_Lake_Package_mkTomlConfig___closed__16);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

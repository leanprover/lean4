// Lean compiler output
// Module: Lake.Config.Module
// Imports: Init Lake.Build.Trace Lake.Config.LeanLib Lake.Util.OrdHashSet
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
extern lean_object* l_Lake_MTime_instOrd;
LEAN_EXPORT lean_object* l_Lake_Module_bcFile_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_ileanFile(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_pkg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_findModule_x3f(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_getModuleArray___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lake_Package_findModule_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_filePath(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_findModule_x3f___closed__1;
extern lean_object* l_Lake_instOrdBuildType;
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
lean_object* l_Lake_nameToSharedLib(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_rootModules___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instBEqModule___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_leancArgs___boxed(lean_object*);
static lean_object* l_Lake_Module_instCheckExists___closed__1;
LEAN_EXPORT uint8_t l_Lake_Module_dynlibName___lambda__1(lean_object*);
static lean_object* l_Lake_ModuleSet_empty___closed__3;
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lake_Package_findModule_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_instBEqModule(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_irPath___boxed(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_getModuleArray(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_System_FilePath_extension(lean_object*);
lean_object* lean_io_metadata(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_leanLibPath___boxed(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_platformIndependent(lean_object*);
lean_object* l_System_FilePath_withExtension(lean_object*, lean_object*);
static lean_object* l_Lake_Module_traceFile___closed__1;
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___at_Lake_LeanLib_getModuleArray___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_coNoExportFile___closed__1;
lean_object* l_IO_FS_DirEntry_path(lean_object*);
lean_object* l_Nat_nextPowerOfTwo_go(lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_pathExists(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_instGetMTime;
LEAN_EXPORT lean_object* l_Lake_Module_weakLeancArgs(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_getModuleArray___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___at_Lake_LeanLib_getModuleArray___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdModuleSet_empty;
LEAN_EXPORT lean_object* l_Lake_ModuleSet_empty;
static lean_object* l_Lake_ModuleSet_empty___closed__1;
LEAN_EXPORT lean_object* l_Lake_Module_leancArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_weakLinkArgs(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_rootModules___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instHashableModule___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_leanFile(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_getMTime(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lake_LeanLib_rootModules___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_checkExists(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_getModuleArray___spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_isDir(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_coExportFile(lean_object*);
static lean_object* l_Lake_Module_bcFile___closed__1;
LEAN_EXPORT lean_object* l_Lake_Module_filePath___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_rootModules(lean_object*);
static lean_object* l_Lake_OrdHashSet_empty___at_Lake_OrdModuleSet_empty___spec__1___closed__4;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_getModuleArray___spec__2___closed__1;
static lean_object* l_Lake_OrdHashSet_empty___at_Lake_OrdModuleSet_empty___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Package_findModule_x3f___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lake_Package_findModule_x3f___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_weakLeanArgs(lean_object*);
static lean_object* l_Lake_Module_dynlibName___closed__1;
LEAN_EXPORT lean_object* l_Lake_Module_rootDir(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_checkExists___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lake_Package_findModule_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_findModule_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_nativeFacets___boxed(lean_object*, lean_object*);
uint8_t l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lean_forEachModuleInDir___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
static lean_object* l_Lake_Module_bcoFile___closed__1;
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lake_LeanLib_rootModules___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_getModuleArray___spec__2___closed__2;
LEAN_EXPORT lean_object* l_Lake_Module_oleanFile(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lake_OrdHashSet_empty___at_Lake_OrdModuleSet_empty___spec__1___closed__3;
static lean_object* l_Lake_ModuleSet_empty___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Package_findModule_x3f___spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_srcPath___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_traceFile(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ModuleMap_empty(lean_object*);
LEAN_EXPORT uint8_t l_Lake_Module_shouldPrecompile(lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
static lean_object* l_Lake_Module_dynlibName___closed__2;
LEAN_EXPORT lean_object* l_Lake_Module_leanArgs(lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_getModuleArray___spec__2___closed__4;
LEAN_EXPORT lean_object* l_Lake_Module_nativeFacets(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_Module_srcPath(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_pkg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_coNoExportFile(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_getModuleArray___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_oleanFile___closed__1;
LEAN_EXPORT uint8_t l_Lake_Module_backend(lean_object*);
static lean_object* l_Lake_Module_cFile___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_empty___at_Lake_OrdModuleSet_empty___spec__1;
static uint8_t l_Lake_Module_bcFile_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lake_Module_dynlibName___lambda__1___boxed(lean_object*);
uint8_t l_Lake_Backend_orPreferLeft(uint8_t, uint8_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_checkExists___lambda__1(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_instCheckExists;
LEAN_EXPORT lean_object* l_Lake_Module_cFile(lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
uint8_t l_instDecidableRelLe___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_bcFile(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_dynlibSuffix;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_backend___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_buildType___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_dynlibFile(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_getModuleArray___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_findModule_x3f___closed__2;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_getModuleArray___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_read_dir(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_leanLibPath(lean_object*, lean_object*);
uint8_t lean_internal_has_llvm_backend(lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_Module_irPath(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lake_Package_findModule_x3f___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT uint64_t l_Lake_instHashableModule(lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_bcoFile(lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lake_Package_findModule_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_dynlibSuffix___closed__1;
uint8_t l_Lake_LeanLibConfig_isBuildableModule(lean_object*, lean_object*);
static lean_object* l_Lake_OrdHashSet_empty___at_Lake_OrdModuleSet_empty___spec__1___closed__2;
lean_object* l_Lean_modToFilePath(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_getModuleArray___spec__2___closed__3;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Name_toStringWithSep(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lake_BuildType_leancArgs(uint8_t);
static lean_object* l_Lake_Module_instGetMTime___closed__1;
static lean_object* l_Lake_Module_coExportFile___closed__1;
static lean_object* l_Lake_Module_ileanFile___closed__1;
LEAN_EXPORT lean_object* l_Lake_Module_linkArgs(lean_object*);
LEAN_EXPORT uint8_t l_Lake_Module_buildType(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lake_Package_moreLeanArgs___spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_dynlibName(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_serverOptions(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_shouldPrecompile___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Lake_instHashableModule(lean_object* x_1) {
_start:
{
lean_object* x_2; uint64_t x_3; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = l_Lean_Name_hash___override(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instHashableModule___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lake_instHashableModule(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lake_instBEqModule(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 2);
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_name_eq(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_instBEqModule___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lake_instBEqModule(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_ModuleSet_empty___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Nat_nextPowerOfTwo_go(x_1, x_2, lean_box(0));
return x_3;
}
}
static lean_object* _init_l_Lake_ModuleSet_empty___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_ModuleSet_empty___closed__1;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_ModuleSet_empty___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lake_ModuleSet_empty___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_ModuleSet_empty() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_ModuleSet_empty___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at_Lake_OrdModuleSet_empty___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at_Lake_OrdModuleSet_empty___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instHashableModule___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at_Lake_OrdModuleSet_empty___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instBEqModule___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at_Lake_OrdModuleSet_empty___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_ModuleSet_empty___closed__3;
x_2 = l_Lake_OrdHashSet_empty___at_Lake_OrdModuleSet_empty___spec__1___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at_Lake_OrdModuleSet_empty___spec__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_OrdHashSet_empty___at_Lake_OrdModuleSet_empty___spec__1___closed__4;
return x_1;
}
}
static lean_object* _init_l_Lake_OrdModuleSet_empty() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_OrdHashSet_empty___at_Lake_OrdModuleSet_empty___spec__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_ModuleMap_empty(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_findModule_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = l_Lake_LeanLibConfig_isBuildableModule(x_1, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_inc(x_1);
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_1);
lean_ctor_set(x_6, 2, x_1);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lake_Package_findModule_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_3, x_7);
lean_dec(x_3);
x_9 = lean_array_fget(x_2, x_8);
lean_inc(x_1);
x_10 = l_Lake_LeanLib_findModule_x3f(x_1, x_9);
if (lean_obj_tag(x_10) == 0)
{
x_3 = x_8;
x_4 = lean_box(0);
goto _start;
}
else
{
lean_dec(x_8);
lean_dec(x_1);
return x_10;
}
}
else
{
lean_object* x_12; 
lean_dec(x_3);
lean_dec(x_1);
x_12 = lean_box(0);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lake_Package_findModule_x3f___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_3, x_7);
lean_dec(x_3);
x_9 = lean_array_fget(x_2, x_8);
lean_inc(x_1);
x_10 = l_Lake_LeanLib_findModule_x3f(x_1, x_9);
if (lean_obj_tag(x_10) == 0)
{
x_3 = x_8;
x_4 = lean_box(0);
goto _start;
}
else
{
lean_dec(x_8);
lean_dec(x_1);
return x_10;
}
}
else
{
lean_object* x_12; 
lean_dec(x_3);
lean_dec(x_1);
x_12 = lean_box(0);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Package_findModule_x3f___spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_array_push(x_5, x_8);
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_3 = x_11;
x_5 = x_9;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lake_Package_findModule_x3f___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_3, x_7);
lean_dec(x_3);
x_9 = lean_array_fget(x_2, x_8);
lean_inc(x_1);
x_10 = l_Lake_LeanLib_findModule_x3f(x_1, x_9);
if (lean_obj_tag(x_10) == 0)
{
x_3 = x_8;
x_4 = lean_box(0);
goto _start;
}
else
{
lean_dec(x_8);
lean_dec(x_1);
return x_10;
}
}
else
{
lean_object* x_12; 
lean_dec(x_3);
lean_dec(x_1);
x_12 = lean_box(0);
return x_12;
}
}
}
static lean_object* _init_l_Lake_Package_findModule_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_findModule_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Package_findModule_x3f___closed__1;
x_2 = lean_array_get_size(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_findModule_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_2, 8);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_8 = l_Lake_Package_findModule_x3f___closed__1;
x_9 = l_Lake_Package_findModule_x3f___closed__2;
x_10 = l_Array_findSomeRevM_x3f_find___at_Lake_Package_findModule_x3f___spec__1(x_1, x_8, x_9, lean_box(0));
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_nat_dec_le(x_5, x_5);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_12 = l_Lake_Package_findModule_x3f___closed__1;
x_13 = l_Lake_Package_findModule_x3f___closed__2;
x_14 = l_Array_findSomeRevM_x3f_find___at_Lake_Package_findModule_x3f___spec__2(x_1, x_12, x_13, lean_box(0));
return x_14;
}
else
{
size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = 0;
x_16 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_17 = l_Lake_Package_findModule_x3f___closed__1;
x_18 = l_Array_foldlMUnsafe_fold___at_Lake_Package_findModule_x3f___spec__3(x_2, x_4, x_15, x_16, x_17);
lean_dec(x_4);
x_19 = lean_array_get_size(x_18);
x_20 = l_Array_findSomeRevM_x3f_find___at_Lake_Package_findModule_x3f___spec__4(x_1, x_18, x_19, lean_box(0));
lean_dec(x_18);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lake_Package_findModule_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_findSomeRevM_x3f_find___at_Lake_Package_findModule_x3f___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lake_Package_findModule_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_findSomeRevM_x3f_find___at_Lake_Package_findModule_x3f___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Package_findModule_x3f___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lake_Package_findModule_x3f___spec__3(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lake_Package_findModule_x3f___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_findSomeRevM_x3f_find___at_Lake_Package_findModule_x3f___spec__4(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_getModuleArray___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_Name_append(x_1, x_3);
x_7 = lean_apply_3(x_2, x_6, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_getModuleArray___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_getModuleArray___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_getModuleArray___spec__2___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_getModuleArray___spec__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_getModuleArray___spec__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_getModuleArray___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_19; 
x_19 = lean_usize_dec_lt(x_6, x_5);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_7);
lean_ctor_set(x_20, 1, x_8);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_9);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_dec(x_7);
x_22 = lean_array_uget(x_4, x_6);
lean_inc(x_22);
x_23 = l_IO_FS_DirEntry_path(x_22);
x_24 = l_System_FilePath_isDir(x_23, x_9);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_24);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_24, 1);
x_29 = lean_ctor_get(x_24, 0);
lean_dec(x_29);
x_30 = l_System_FilePath_extension(x_23);
x_31 = l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_getModuleArray___spec__2___closed__2;
x_32 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lean_forEachModuleInDir___spec__1(x_30, x_31);
lean_dec(x_30);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_22);
x_33 = l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_getModuleArray___spec__2___closed__3;
lean_ctor_set(x_24, 1, x_8);
lean_ctor_set(x_24, 0, x_33);
x_10 = x_24;
x_11 = x_28;
goto block_18;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_free_object(x_24);
x_34 = lean_ctor_get(x_22, 1);
lean_inc(x_34);
lean_dec(x_22);
x_35 = l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_getModuleArray___spec__2___closed__4;
x_36 = l_System_FilePath_withExtension(x_34, x_35);
x_37 = lean_box(0);
x_38 = l_Lean_Name_str___override(x_37, x_36);
lean_inc(x_1);
x_39 = lean_apply_3(x_1, x_38, x_8, x_28);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = !lean_is_exclusive(x_40);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_40, 0);
lean_dec(x_43);
x_44 = l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_getModuleArray___spec__2___closed__3;
lean_ctor_set(x_40, 0, x_44);
x_10 = x_40;
x_11 = x_41;
goto block_18;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_40, 1);
lean_inc(x_45);
lean_dec(x_40);
x_46 = l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_getModuleArray___spec__2___closed__3;
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_10 = x_47;
x_11 = x_41;
goto block_18;
}
}
else
{
uint8_t x_48; 
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_39);
if (x_48 == 0)
{
return x_39;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_39, 0);
x_50 = lean_ctor_get(x_39, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_39);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_52 = lean_ctor_get(x_24, 1);
lean_inc(x_52);
lean_dec(x_24);
x_53 = l_System_FilePath_extension(x_23);
x_54 = l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_getModuleArray___spec__2___closed__2;
x_55 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lean_forEachModuleInDir___spec__1(x_53, x_54);
lean_dec(x_53);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_22);
x_56 = l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_getModuleArray___spec__2___closed__3;
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_8);
x_10 = x_57;
x_11 = x_52;
goto block_18;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_58 = lean_ctor_get(x_22, 1);
lean_inc(x_58);
lean_dec(x_22);
x_59 = l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_getModuleArray___spec__2___closed__4;
x_60 = l_System_FilePath_withExtension(x_58, x_59);
x_61 = lean_box(0);
x_62 = l_Lean_Name_str___override(x_61, x_60);
lean_inc(x_1);
x_63 = lean_apply_3(x_1, x_62, x_8, x_52);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_67 = x_64;
} else {
 lean_dec_ref(x_64);
 x_67 = lean_box(0);
}
x_68 = l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_getModuleArray___spec__2___closed__3;
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_67;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_66);
x_10 = x_69;
x_11 = x_65;
goto block_18;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_1);
x_70 = lean_ctor_get(x_63, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_63, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_72 = x_63;
} else {
 lean_dec_ref(x_63);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_74 = lean_ctor_get(x_24, 1);
lean_inc(x_74);
lean_dec(x_24);
x_75 = lean_ctor_get(x_22, 1);
lean_inc(x_75);
lean_dec(x_22);
x_76 = lean_box(0);
x_77 = l_Lean_Name_str___override(x_76, x_75);
lean_inc(x_1);
x_78 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_getModuleArray___spec__2___lambda__1), 5, 2);
lean_closure_set(x_78, 0, x_77);
lean_closure_set(x_78, 1, x_1);
x_79 = l_Lean_forEachModuleInDir___at_Lake_LeanLib_getModuleArray___spec__1(x_23, x_78, x_8, x_74);
lean_dec(x_23);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = !lean_is_exclusive(x_80);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_80, 0);
lean_dec(x_83);
x_84 = l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_getModuleArray___spec__2___closed__3;
lean_ctor_set(x_80, 0, x_84);
x_10 = x_80;
x_11 = x_81;
goto block_18;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_80, 1);
lean_inc(x_85);
lean_dec(x_80);
x_86 = l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_getModuleArray___spec__2___closed__3;
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_85);
x_10 = x_87;
x_11 = x_81;
goto block_18;
}
}
else
{
uint8_t x_88; 
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_79);
if (x_88 == 0)
{
return x_79;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_79, 0);
x_90 = lean_ctor_get(x_79, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_79);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
}
block_18:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = 1;
x_16 = lean_usize_add(x_6, x_15);
x_6 = x_16;
x_7 = x_14;
x_8 = x_13;
x_9 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___at_Lake_LeanLib_getModuleArray___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_io_read_dir(x_1, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_box(0);
x_9 = lean_array_size(x_6);
x_10 = 0;
x_11 = lean_box(0);
x_12 = l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_getModuleArray___spec__2(x_2, x_6, x_8, x_6, x_9, x_10, x_11, x_3, x_7);
lean_dec(x_6);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_11);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_12, 0, x_18);
return x_12;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_12);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_22 = x_19;
} else {
 lean_dec_ref(x_19);
 x_22 = lean_box(0);
}
if (lean_is_scalar(x_22)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_22;
}
lean_ctor_set(x_23, 0, x_11);
lean_ctor_set(x_23, 1, x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_20);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_12);
if (x_25 == 0)
{
return x_12;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_12, 0);
x_27 = lean_ctor_get(x_12, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_12);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_3);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_5);
if (x_29 == 0)
{
return x_5;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_5, 0);
x_31 = lean_ctor_get(x_5, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_5);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_getModuleArray___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = l_Lean_Name_append(x_1, x_3);
lean_inc(x_6);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
lean_ctor_set(x_7, 2, x_6);
x_8 = lean_array_push(x_4, x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_getModuleArray___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_eq(x_4, x_5);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_6);
x_10 = lean_array_uget(x_3, x_4);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 2);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_13, 7);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_System_FilePath_join(x_12, x_14);
lean_dec(x_14);
x_16 = lean_ctor_get(x_2, 2);
x_17 = l_System_FilePath_join(x_15, x_16);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
lean_dec(x_17);
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
lean_dec(x_10);
lean_inc(x_18);
lean_inc(x_1);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_array_push(x_7, x_19);
x_21 = 1;
x_22 = lean_usize_add(x_4, x_21);
x_23 = lean_box(0);
x_4 = x_22;
x_6 = x_23;
x_7 = x_20;
goto _start;
}
case 1:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_10, 0);
lean_inc(x_25);
lean_dec(x_10);
x_26 = l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_getModuleArray___spec__2___closed__4;
x_27 = l_Lean_modToFilePath(x_17, x_25, x_26);
lean_dec(x_17);
lean_inc(x_1);
x_28 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_getModuleArray___spec__3___lambda__1), 5, 2);
lean_closure_set(x_28, 0, x_25);
lean_closure_set(x_28, 1, x_1);
x_29 = l_Lean_forEachModuleInDir___at_Lake_LeanLib_getModuleArray___spec__1(x_27, x_28, x_7, x_8);
lean_dec(x_27);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; size_t x_34; size_t x_35; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = 1;
x_35 = lean_usize_add(x_4, x_34);
x_4 = x_35;
x_6 = x_32;
x_7 = x_33;
x_8 = x_31;
goto _start;
}
else
{
uint8_t x_37; 
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_29);
if (x_37 == 0)
{
return x_29;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_29, 0);
x_39 = lean_ctor_get(x_29, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_29);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
default: 
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_41 = lean_ctor_get(x_10, 0);
lean_inc(x_41);
lean_dec(x_10);
lean_inc_n(x_41, 2);
lean_inc(x_1);
x_42 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_42, 0, x_1);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_42, 2, x_41);
x_43 = lean_array_push(x_7, x_42);
x_44 = l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_getModuleArray___spec__2___closed__4;
x_45 = l_Lean_modToFilePath(x_17, x_41, x_44);
lean_dec(x_17);
lean_inc(x_1);
x_46 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_getModuleArray___spec__3___lambda__1), 5, 2);
lean_closure_set(x_46, 0, x_41);
lean_closure_set(x_46, 1, x_1);
x_47 = l_Lean_forEachModuleInDir___at_Lake_LeanLib_getModuleArray___spec__1(x_45, x_46, x_43, x_8);
lean_dec(x_45);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; size_t x_52; size_t x_53; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
x_52 = 1;
x_53 = lean_usize_add(x_4, x_52);
x_4 = x_53;
x_6 = x_50;
x_7 = x_51;
x_8 = x_49;
goto _start;
}
else
{
uint8_t x_55; 
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_47);
if (x_55 == 0)
{
return x_47;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_47, 0);
x_57 = lean_ctor_get(x_47, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_47);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_1);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_6);
lean_ctor_set(x_59, 1, x_7);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_8);
return x_60;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_getModuleArray(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 4);
lean_inc(x_4);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_8 = l_Lake_Package_findModule_x3f___closed__1;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_2);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = lean_nat_dec_le(x_5, x_5);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_11 = l_Lake_Package_findModule_x3f___closed__1;
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
return x_12;
}
else
{
size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = 0;
x_14 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_15 = lean_box(0);
x_16 = l_Lake_Package_findModule_x3f___closed__1;
x_17 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_getModuleArray___spec__3(x_1, x_3, x_4, x_13, x_14, x_15, x_16, x_2);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_17);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_17);
if (x_25 == 0)
{
return x_17;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_17, 0);
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_17);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_getModuleArray___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_12 = l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_getModuleArray___spec__2(x_1, x_2, x_3, x_4, x_10, x_11, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___at_Lake_LeanLib_getModuleArray___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_forEachModuleInDir___at_Lake_LeanLib_getModuleArray___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_getModuleArray___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_getModuleArray___spec__3(x_1, x_2, x_3, x_9, x_10, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_rootModules___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = l_Lake_LeanLib_findModule_x3f(x_7, x_1);
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
if (lean_obj_tag(x_8) == 0)
{
x_3 = x_10;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_array_push(x_5, x_12);
x_3 = x_10;
x_5 = x_13;
goto _start;
}
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lake_LeanLib_rootModules___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_1);
x_6 = l_Lake_Package_findModule_x3f___closed__1;
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_le(x_4, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = l_Lake_Package_findModule_x3f___closed__1;
return x_9;
}
else
{
size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_usize_of_nat(x_3);
x_11 = lean_usize_of_nat(x_4);
x_12 = l_Lake_Package_findModule_x3f___closed__1;
x_13 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_rootModules___spec__2(x_1, x_2, x_10, x_11, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_rootModules(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = lean_ctor_get(x_2, 3);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_filterMapM___at_Lake_LeanLib_rootModules___spec__1(x_1, x_3, x_5, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_rootModules___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_rootModules___spec__2(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lake_LeanLib_rootModules___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_filterMapM___at_Lake_LeanLib_rootModules___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_pkg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_pkg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Module_pkg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_rootDir(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 2);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_5, 7);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_System_FilePath_join(x_4, x_6);
lean_dec(x_6);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_System_FilePath_join(x_7, x_9);
lean_dec(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_filePath(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 1);
x_5 = l_Lean_modToFilePath(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_filePath___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_Module_filePath(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_srcPath(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 2);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_6, 7);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_System_FilePath_join(x_5, x_7);
lean_dec(x_7);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_ctor_get(x_9, 2);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_System_FilePath_join(x_8, x_10);
lean_dec(x_10);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec(x_2);
x_13 = l_Lean_modToFilePath(x_11, x_12, x_1);
lean_dec(x_12);
lean_dec(x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_srcPath___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Module_srcPath(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanFile(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 2);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_5, 7);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_System_FilePath_join(x_4, x_6);
lean_dec(x_6);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_System_FilePath_join(x_7, x_9);
lean_dec(x_9);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_getModuleArray___spec__2___closed__1;
x_13 = l_Lean_modToFilePath(x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanLibPath(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 2);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_6, 8);
lean_inc(x_7);
x_8 = l_System_FilePath_join(x_5, x_7);
lean_dec(x_7);
x_9 = lean_ctor_get(x_6, 9);
lean_inc(x_9);
lean_dec(x_6);
x_10 = l_System_FilePath_join(x_8, x_9);
lean_dec(x_9);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec(x_2);
x_12 = l_Lean_modToFilePath(x_10, x_11, x_1);
lean_dec(x_11);
lean_dec(x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanLibPath___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Module_leanLibPath(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Module_oleanFile___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("olean", 5, 5);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_oleanFile(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 2);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_5, 8);
lean_inc(x_6);
x_7 = l_System_FilePath_join(x_4, x_6);
lean_dec(x_6);
x_8 = lean_ctor_get(x_5, 9);
lean_inc(x_8);
lean_dec(x_5);
x_9 = l_System_FilePath_join(x_7, x_8);
lean_dec(x_8);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l_Lake_Module_oleanFile___closed__1;
x_12 = l_Lean_modToFilePath(x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_12;
}
}
static lean_object* _init_l_Lake_Module_ileanFile___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ilean", 5, 5);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_ileanFile(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 2);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_5, 8);
lean_inc(x_6);
x_7 = l_System_FilePath_join(x_4, x_6);
lean_dec(x_6);
x_8 = lean_ctor_get(x_5, 9);
lean_inc(x_8);
lean_dec(x_5);
x_9 = l_System_FilePath_join(x_7, x_8);
lean_dec(x_8);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l_Lake_Module_ileanFile___closed__1;
x_12 = l_Lean_modToFilePath(x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_12;
}
}
static lean_object* _init_l_Lake_Module_traceFile___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("trace", 5, 5);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_traceFile(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 2);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_5, 8);
lean_inc(x_6);
x_7 = l_System_FilePath_join(x_4, x_6);
lean_dec(x_6);
x_8 = lean_ctor_get(x_5, 9);
lean_inc(x_8);
lean_dec(x_5);
x_9 = l_System_FilePath_join(x_7, x_8);
lean_dec(x_8);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l_Lake_Module_traceFile___closed__1;
x_12 = l_Lean_modToFilePath(x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_irPath(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 2);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_6, 8);
lean_inc(x_7);
x_8 = l_System_FilePath_join(x_5, x_7);
lean_dec(x_7);
x_9 = lean_ctor_get(x_6, 12);
lean_inc(x_9);
lean_dec(x_6);
x_10 = l_System_FilePath_join(x_8, x_9);
lean_dec(x_9);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec(x_2);
x_12 = l_Lean_modToFilePath(x_10, x_11, x_1);
lean_dec(x_11);
lean_dec(x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_irPath___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Module_irPath(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Module_cFile___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("c", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_cFile(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 2);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_5, 8);
lean_inc(x_6);
x_7 = l_System_FilePath_join(x_4, x_6);
lean_dec(x_6);
x_8 = lean_ctor_get(x_5, 12);
lean_inc(x_8);
lean_dec(x_5);
x_9 = l_System_FilePath_join(x_7, x_8);
lean_dec(x_8);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l_Lake_Module_cFile___closed__1;
x_12 = l_Lean_modToFilePath(x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_12;
}
}
static lean_object* _init_l_Lake_Module_coExportFile___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("c.o.export", 10, 10);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_coExportFile(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 2);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_5, 8);
lean_inc(x_6);
x_7 = l_System_FilePath_join(x_4, x_6);
lean_dec(x_6);
x_8 = lean_ctor_get(x_5, 12);
lean_inc(x_8);
lean_dec(x_5);
x_9 = l_System_FilePath_join(x_7, x_8);
lean_dec(x_8);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l_Lake_Module_coExportFile___closed__1;
x_12 = l_Lean_modToFilePath(x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_12;
}
}
static lean_object* _init_l_Lake_Module_coNoExportFile___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("c.o.noexport", 12, 12);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_coNoExportFile(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 2);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_5, 8);
lean_inc(x_6);
x_7 = l_System_FilePath_join(x_4, x_6);
lean_dec(x_6);
x_8 = lean_ctor_get(x_5, 12);
lean_inc(x_8);
lean_dec(x_5);
x_9 = l_System_FilePath_join(x_7, x_8);
lean_dec(x_8);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l_Lake_Module_coNoExportFile___closed__1;
x_12 = l_Lean_modToFilePath(x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_12;
}
}
static lean_object* _init_l_Lake_Module_bcFile___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("bc", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_bcFile(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 2);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_5, 8);
lean_inc(x_6);
x_7 = l_System_FilePath_join(x_4, x_6);
lean_dec(x_6);
x_8 = lean_ctor_get(x_5, 12);
lean_inc(x_8);
lean_dec(x_5);
x_9 = l_System_FilePath_join(x_7, x_8);
lean_dec(x_8);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l_Lake_Module_bcFile___closed__1;
x_12 = l_Lean_modToFilePath(x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_12;
}
}
static uint8_t _init_l_Lake_Module_bcFile_x3f___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_box(0);
x_2 = lean_internal_has_llvm_backend(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_bcFile_x3f(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lake_Module_bcFile_x3f___closed__1;
if (x_2 == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 2);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_7, 8);
lean_inc(x_8);
x_9 = l_System_FilePath_join(x_6, x_8);
lean_dec(x_8);
x_10 = lean_ctor_get(x_7, 12);
lean_inc(x_10);
lean_dec(x_7);
x_11 = l_System_FilePath_join(x_9, x_10);
lean_dec(x_10);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = l_Lake_Module_bcFile___closed__1;
x_14 = l_Lean_modToFilePath(x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
static lean_object* _init_l_Lake_Module_bcoFile___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("bc.o", 4, 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_bcoFile(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 2);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_5, 8);
lean_inc(x_6);
x_7 = l_System_FilePath_join(x_4, x_6);
lean_dec(x_6);
x_8 = lean_ctor_get(x_5, 12);
lean_inc(x_8);
lean_dec(x_5);
x_9 = l_System_FilePath_join(x_7, x_8);
lean_dec(x_8);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l_Lake_Module_bcoFile___closed__1;
x_12 = l_Lean_modToFilePath(x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_12;
}
}
static lean_object* _init_l_Lake_Module_dynlibSuffix___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-1", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_dynlibSuffix() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Module_dynlibSuffix___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lake_Module_dynlibName___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l_Lake_Module_dynlibName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_dynlibName___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Module_dynlibName___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_dynlibName(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_Lake_Module_dynlibName___closed__1;
x_4 = 1;
x_5 = l_Lake_Module_dynlibName___closed__2;
x_6 = l_Lean_Name_toStringWithSep(x_3, x_4, x_2, x_5);
x_7 = l_Lake_Module_dynlibSuffix;
x_8 = lean_string_append(x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_dynlibName___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_Module_dynlibName___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_dynlibFile(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 2);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_5, 8);
lean_inc(x_6);
x_7 = l_System_FilePath_join(x_4, x_6);
lean_dec(x_6);
x_8 = lean_ctor_get(x_5, 10);
lean_inc(x_8);
lean_dec(x_5);
x_9 = l_System_FilePath_join(x_7, x_8);
lean_dec(x_8);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l_Lake_Module_dynlibName___closed__1;
x_12 = 1;
x_13 = l_Lake_Module_dynlibName___closed__2;
x_14 = l_Lean_Name_toStringWithSep(x_11, x_12, x_10, x_13);
x_15 = l_Lake_Module_dynlibSuffix;
x_16 = lean_string_append(x_14, x_15);
x_17 = l_Lake_nameToSharedLib(x_16);
lean_dec(x_16);
x_18 = l_System_FilePath_join(x_9, x_17);
lean_dec(x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_serverOptions(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 2);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 4);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Array_append___rarg(x_6, x_7);
lean_dec(x_7);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = l_Array_append___rarg(x_8, x_11);
lean_dec(x_11);
x_13 = lean_ctor_get(x_10, 4);
lean_inc(x_13);
lean_dec(x_10);
x_14 = l_Array_append___rarg(x_12, x_13);
lean_dec(x_13);
return x_14;
}
}
LEAN_EXPORT uint8_t l_Lake_Module_buildType(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_3, 2);
x_5 = lean_ctor_get(x_4, 1);
x_6 = lean_ctor_get_uint8(x_5, sizeof(void*)*9);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_7, 0);
x_9 = lean_ctor_get_uint8(x_8, sizeof(void*)*9);
x_10 = l_Lake_instOrdBuildType;
x_11 = lean_box(x_6);
x_12 = lean_box(x_9);
x_13 = l_instDecidableRelLe___rarg(x_10, x_11, x_12);
if (x_13 == 0)
{
return x_9;
}
else
{
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_buildType___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_Module_buildType(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lake_Module_backend(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*9 + 1);
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_6, 2);
x_8 = lean_ctor_get(x_7, 1);
x_9 = lean_ctor_get_uint8(x_8, sizeof(void*)*9 + 1);
x_10 = l_Lake_Backend_orPreferLeft(x_5, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_backend___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_Module_backend(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanArgs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 2);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_array_size(x_6);
x_8 = 0;
x_9 = l_Array_mapMUnsafe_map___at_Lake_Package_moreLeanArgs___spec__1(x_7, x_8, x_6);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = l_Array_append___rarg(x_9, x_10);
lean_dec(x_10);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_array_size(x_14);
x_16 = l_Array_mapMUnsafe_map___at_Lake_Package_moreLeanArgs___spec__1(x_15, x_8, x_14);
x_17 = l_Array_append___rarg(x_11, x_16);
lean_dec(x_16);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = l_Array_append___rarg(x_17, x_18);
lean_dec(x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_weakLeanArgs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 2);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Array_append___rarg(x_6, x_9);
lean_dec(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leancArgs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_3, 2);
x_5 = lean_ctor_get(x_4, 1);
x_6 = lean_ctor_get_uint8(x_5, sizeof(void*)*9);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_7, 0);
x_9 = lean_ctor_get_uint8(x_8, sizeof(void*)*9);
x_10 = l_Lake_instOrdBuildType;
x_11 = lean_box(x_6);
x_12 = lean_box(x_9);
x_13 = l_instDecidableRelLe___rarg(x_10, x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_5, 3);
x_15 = lean_ctor_get(x_8, 3);
x_16 = l_Lake_BuildType_leancArgs(x_9);
x_17 = l_Array_append___rarg(x_16, x_14);
x_18 = l_Array_append___rarg(x_17, x_15);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_5, 3);
x_20 = lean_ctor_get(x_8, 3);
x_21 = l_Lake_BuildType_leancArgs(x_6);
x_22 = l_Array_append___rarg(x_21, x_19);
x_23 = l_Array_append___rarg(x_22, x_20);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leancArgs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Module_leancArgs(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_weakLeancArgs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 2);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 5);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_8, 5);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Array_append___rarg(x_6, x_9);
lean_dec(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_linkArgs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 2);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 6);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_8, 6);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Array_append___rarg(x_6, x_9);
lean_dec(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_weakLinkArgs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 2);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 7);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_8, 7);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Array_append___rarg(x_6, x_9);
lean_dec(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_platformIndependent(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 8);
lean_inc(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_8, 8);
lean_inc(x_9);
lean_dec(x_8);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_2);
x_10 = !lean_is_exclusive(x_5);
if (x_10 == 0)
{
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
lean_dec(x_5);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_Module_shouldPrecompile(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_3, 2);
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*29);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get_uint8(x_6, sizeof(void*)*9);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_shouldPrecompile___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_Module_shouldPrecompile(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_nativeFacets(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 8);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_box(x_2);
x_7 = lean_apply_1(x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_nativeFacets___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lake_Module_nativeFacets(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_getMTime(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 2);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_6, 8);
lean_inc(x_7);
x_8 = l_System_FilePath_join(x_5, x_7);
lean_dec(x_7);
x_9 = lean_ctor_get(x_6, 9);
lean_inc(x_9);
lean_inc(x_8);
x_10 = l_System_FilePath_join(x_8, x_9);
lean_dec(x_9);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l_Lake_Module_oleanFile___closed__1;
x_13 = l_Lean_modToFilePath(x_10, x_11, x_12);
x_14 = lean_io_metadata(x_13, x_2);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lake_Module_ileanFile___closed__1;
x_19 = l_Lean_modToFilePath(x_10, x_11, x_18);
lean_dec(x_10);
x_20 = lean_io_metadata(x_19, x_16);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_6, 12);
lean_inc(x_24);
lean_dec(x_6);
x_25 = l_System_FilePath_join(x_8, x_24);
lean_dec(x_24);
x_26 = l_Lake_Module_cFile___closed__1;
x_27 = l_Lean_modToFilePath(x_25, x_11, x_26);
lean_dec(x_11);
lean_dec(x_25);
x_28 = lean_io_metadata(x_27, x_22);
lean_dec(x_27);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = l_Lake_MTime_instOrd;
lean_inc(x_23);
lean_inc(x_17);
x_33 = l_instDecidableRelLe___rarg(x_32, x_17, x_23);
if (x_33 == 0)
{
uint8_t x_34; 
lean_dec(x_23);
lean_inc(x_31);
lean_inc(x_17);
x_34 = l_instDecidableRelLe___rarg(x_32, x_17, x_31);
if (x_34 == 0)
{
lean_dec(x_31);
lean_ctor_set(x_28, 0, x_17);
return x_28;
}
else
{
lean_dec(x_17);
lean_ctor_set(x_28, 0, x_31);
return x_28;
}
}
else
{
uint8_t x_35; 
lean_dec(x_17);
lean_inc(x_31);
lean_inc(x_23);
x_35 = l_instDecidableRelLe___rarg(x_32, x_23, x_31);
if (x_35 == 0)
{
lean_dec(x_31);
lean_ctor_set(x_28, 0, x_23);
return x_28;
}
else
{
lean_dec(x_23);
lean_ctor_set(x_28, 0, x_31);
return x_28;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_36 = lean_ctor_get(x_28, 0);
x_37 = lean_ctor_get(x_28, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_28);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lake_MTime_instOrd;
lean_inc(x_23);
lean_inc(x_17);
x_40 = l_instDecidableRelLe___rarg(x_39, x_17, x_23);
if (x_40 == 0)
{
uint8_t x_41; 
lean_dec(x_23);
lean_inc(x_38);
lean_inc(x_17);
x_41 = l_instDecidableRelLe___rarg(x_39, x_17, x_38);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_38);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_17);
lean_ctor_set(x_42, 1, x_37);
return x_42;
}
else
{
lean_object* x_43; 
lean_dec(x_17);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_38);
lean_ctor_set(x_43, 1, x_37);
return x_43;
}
}
else
{
uint8_t x_44; 
lean_dec(x_17);
lean_inc(x_38);
lean_inc(x_23);
x_44 = l_instDecidableRelLe___rarg(x_39, x_23, x_38);
if (x_44 == 0)
{
lean_object* x_45; 
lean_dec(x_38);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_23);
lean_ctor_set(x_45, 1, x_37);
return x_45;
}
else
{
lean_object* x_46; 
lean_dec(x_23);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_38);
lean_ctor_set(x_46, 1, x_37);
return x_46;
}
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_23);
lean_dec(x_17);
x_47 = !lean_is_exclusive(x_28);
if (x_47 == 0)
{
return x_28;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_28, 0);
x_49 = lean_ctor_get(x_28, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_28);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
x_51 = !lean_is_exclusive(x_20);
if (x_51 == 0)
{
return x_20;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_20, 0);
x_53 = lean_ctor_get(x_20, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_20);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
x_55 = !lean_is_exclusive(x_14);
if (x_55 == 0)
{
return x_14;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_14, 0);
x_57 = lean_ctor_get(x_14, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_14);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
static lean_object* _init_l_Lake_Module_instGetMTime___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Module_getMTime), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_instGetMTime() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Module_instGetMTime___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_checkExists___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 2);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_7, 8);
lean_inc(x_8);
x_9 = l_System_FilePath_join(x_6, x_8);
lean_dec(x_8);
x_10 = lean_ctor_get(x_7, 9);
lean_inc(x_10);
lean_inc(x_9);
x_11 = l_System_FilePath_join(x_9, x_10);
lean_dec(x_10);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = l_Lake_Module_oleanFile___closed__1;
x_14 = l_Lean_modToFilePath(x_11, x_12, x_13);
x_15 = l_System_FilePath_pathExists(x_14, x_3);
lean_dec(x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lake_Module_ileanFile___closed__1;
x_19 = l_Lean_modToFilePath(x_11, x_12, x_18);
lean_dec(x_11);
x_20 = l_System_FilePath_pathExists(x_19, x_17);
lean_dec(x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_7, 12);
lean_inc(x_23);
lean_dec(x_7);
x_24 = l_System_FilePath_join(x_9, x_23);
lean_dec(x_23);
x_25 = l_Lake_Module_cFile___closed__1;
x_26 = l_Lean_modToFilePath(x_24, x_12, x_25);
lean_dec(x_12);
lean_dec(x_24);
x_27 = l_System_FilePath_pathExists(x_26, x_22);
lean_dec(x_26);
x_28 = lean_unbox(x_16);
lean_dec(x_16);
if (x_28 == 0)
{
uint8_t x_29; 
lean_dec(x_21);
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_27, 0);
lean_dec(x_30);
x_31 = 0;
x_32 = lean_box(x_31);
lean_ctor_set(x_27, 0, x_32);
return x_27;
}
else
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_dec(x_27);
x_34 = 0;
x_35 = lean_box(x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
}
else
{
uint8_t x_37; 
x_37 = lean_unbox(x_21);
lean_dec(x_21);
if (x_37 == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_27);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_27, 0);
lean_dec(x_39);
x_40 = 0;
x_41 = lean_box(x_40);
lean_ctor_set(x_27, 0, x_41);
return x_27;
}
else
{
lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_27, 1);
lean_inc(x_42);
lean_dec(x_27);
x_43 = 0;
x_44 = lean_box(x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_42);
return x_45;
}
}
else
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_27, 0);
lean_inc(x_46);
x_47 = lean_unbox(x_46);
lean_dec(x_46);
if (x_47 == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_27);
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_27, 0);
lean_dec(x_49);
x_50 = 0;
x_51 = lean_box(x_50);
lean_ctor_set(x_27, 0, x_51);
return x_27;
}
else
{
lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_27, 1);
lean_inc(x_52);
lean_dec(x_27);
x_53 = 0;
x_54 = lean_box(x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_52);
return x_55;
}
}
else
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_27);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_27, 0);
lean_dec(x_57);
x_58 = lean_box(x_2);
lean_ctor_set(x_27, 0, x_58);
return x_27;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_27, 1);
lean_inc(x_59);
lean_dec(x_27);
x_60 = lean_box(x_2);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_checkExists(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lake_Module_bcFile_x3f___closed__1;
if (x_3 == 0)
{
uint8_t x_4; lean_object* x_5; 
x_4 = 1;
x_5 = l_Lake_Module_checkExists___lambda__1(x_1, x_4, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 2);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_9, 8);
lean_inc(x_10);
x_11 = l_System_FilePath_join(x_8, x_10);
lean_dec(x_10);
x_12 = lean_ctor_get(x_9, 12);
lean_inc(x_12);
lean_dec(x_9);
x_13 = l_System_FilePath_join(x_11, x_12);
lean_dec(x_12);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
x_15 = l_Lake_Module_bcFile___closed__1;
x_16 = l_Lean_modToFilePath(x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
x_17 = l_System_FilePath_pathExists(x_16, x_2);
lean_dec(x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_unbox(x_18);
lean_dec(x_18);
x_21 = l_Lake_Module_checkExists___lambda__1(x_1, x_20, x_19);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_checkExists___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lake_Module_checkExists___lambda__1(x_1, x_4, x_3);
return x_5;
}
}
static lean_object* _init_l_Lake_Module_instCheckExists___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Module_checkExists), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_instCheckExists() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Module_instCheckExists___closed__1;
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Trace(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_LeanLib(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_OrdHashSet(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_Module(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Trace(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_LeanLib(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_OrdHashSet(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_ModuleSet_empty___closed__1 = _init_l_Lake_ModuleSet_empty___closed__1();
lean_mark_persistent(l_Lake_ModuleSet_empty___closed__1);
l_Lake_ModuleSet_empty___closed__2 = _init_l_Lake_ModuleSet_empty___closed__2();
lean_mark_persistent(l_Lake_ModuleSet_empty___closed__2);
l_Lake_ModuleSet_empty___closed__3 = _init_l_Lake_ModuleSet_empty___closed__3();
lean_mark_persistent(l_Lake_ModuleSet_empty___closed__3);
l_Lake_ModuleSet_empty = _init_l_Lake_ModuleSet_empty();
lean_mark_persistent(l_Lake_ModuleSet_empty);
l_Lake_OrdHashSet_empty___at_Lake_OrdModuleSet_empty___spec__1___closed__1 = _init_l_Lake_OrdHashSet_empty___at_Lake_OrdModuleSet_empty___spec__1___closed__1();
lean_mark_persistent(l_Lake_OrdHashSet_empty___at_Lake_OrdModuleSet_empty___spec__1___closed__1);
l_Lake_OrdHashSet_empty___at_Lake_OrdModuleSet_empty___spec__1___closed__2 = _init_l_Lake_OrdHashSet_empty___at_Lake_OrdModuleSet_empty___spec__1___closed__2();
lean_mark_persistent(l_Lake_OrdHashSet_empty___at_Lake_OrdModuleSet_empty___spec__1___closed__2);
l_Lake_OrdHashSet_empty___at_Lake_OrdModuleSet_empty___spec__1___closed__3 = _init_l_Lake_OrdHashSet_empty___at_Lake_OrdModuleSet_empty___spec__1___closed__3();
lean_mark_persistent(l_Lake_OrdHashSet_empty___at_Lake_OrdModuleSet_empty___spec__1___closed__3);
l_Lake_OrdHashSet_empty___at_Lake_OrdModuleSet_empty___spec__1___closed__4 = _init_l_Lake_OrdHashSet_empty___at_Lake_OrdModuleSet_empty___spec__1___closed__4();
lean_mark_persistent(l_Lake_OrdHashSet_empty___at_Lake_OrdModuleSet_empty___spec__1___closed__4);
l_Lake_OrdHashSet_empty___at_Lake_OrdModuleSet_empty___spec__1 = _init_l_Lake_OrdHashSet_empty___at_Lake_OrdModuleSet_empty___spec__1();
lean_mark_persistent(l_Lake_OrdHashSet_empty___at_Lake_OrdModuleSet_empty___spec__1);
l_Lake_OrdModuleSet_empty = _init_l_Lake_OrdModuleSet_empty();
lean_mark_persistent(l_Lake_OrdModuleSet_empty);
l_Lake_Package_findModule_x3f___closed__1 = _init_l_Lake_Package_findModule_x3f___closed__1();
lean_mark_persistent(l_Lake_Package_findModule_x3f___closed__1);
l_Lake_Package_findModule_x3f___closed__2 = _init_l_Lake_Package_findModule_x3f___closed__2();
lean_mark_persistent(l_Lake_Package_findModule_x3f___closed__2);
l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_getModuleArray___spec__2___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_getModuleArray___spec__2___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_getModuleArray___spec__2___closed__1);
l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_getModuleArray___spec__2___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_getModuleArray___spec__2___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_getModuleArray___spec__2___closed__2);
l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_getModuleArray___spec__2___closed__3 = _init_l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_getModuleArray___spec__2___closed__3();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_getModuleArray___spec__2___closed__3);
l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_getModuleArray___spec__2___closed__4 = _init_l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_getModuleArray___spec__2___closed__4();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_getModuleArray___spec__2___closed__4);
l_Lake_Module_oleanFile___closed__1 = _init_l_Lake_Module_oleanFile___closed__1();
lean_mark_persistent(l_Lake_Module_oleanFile___closed__1);
l_Lake_Module_ileanFile___closed__1 = _init_l_Lake_Module_ileanFile___closed__1();
lean_mark_persistent(l_Lake_Module_ileanFile___closed__1);
l_Lake_Module_traceFile___closed__1 = _init_l_Lake_Module_traceFile___closed__1();
lean_mark_persistent(l_Lake_Module_traceFile___closed__1);
l_Lake_Module_cFile___closed__1 = _init_l_Lake_Module_cFile___closed__1();
lean_mark_persistent(l_Lake_Module_cFile___closed__1);
l_Lake_Module_coExportFile___closed__1 = _init_l_Lake_Module_coExportFile___closed__1();
lean_mark_persistent(l_Lake_Module_coExportFile___closed__1);
l_Lake_Module_coNoExportFile___closed__1 = _init_l_Lake_Module_coNoExportFile___closed__1();
lean_mark_persistent(l_Lake_Module_coNoExportFile___closed__1);
l_Lake_Module_bcFile___closed__1 = _init_l_Lake_Module_bcFile___closed__1();
lean_mark_persistent(l_Lake_Module_bcFile___closed__1);
l_Lake_Module_bcFile_x3f___closed__1 = _init_l_Lake_Module_bcFile_x3f___closed__1();
l_Lake_Module_bcoFile___closed__1 = _init_l_Lake_Module_bcoFile___closed__1();
lean_mark_persistent(l_Lake_Module_bcoFile___closed__1);
l_Lake_Module_dynlibSuffix___closed__1 = _init_l_Lake_Module_dynlibSuffix___closed__1();
lean_mark_persistent(l_Lake_Module_dynlibSuffix___closed__1);
l_Lake_Module_dynlibSuffix = _init_l_Lake_Module_dynlibSuffix();
lean_mark_persistent(l_Lake_Module_dynlibSuffix);
l_Lake_Module_dynlibName___closed__1 = _init_l_Lake_Module_dynlibName___closed__1();
lean_mark_persistent(l_Lake_Module_dynlibName___closed__1);
l_Lake_Module_dynlibName___closed__2 = _init_l_Lake_Module_dynlibName___closed__2();
lean_mark_persistent(l_Lake_Module_dynlibName___closed__2);
l_Lake_Module_instGetMTime___closed__1 = _init_l_Lake_Module_instGetMTime___closed__1();
lean_mark_persistent(l_Lake_Module_instGetMTime___closed__1);
l_Lake_Module_instGetMTime = _init_l_Lake_Module_instGetMTime();
lean_mark_persistent(l_Lake_Module_instGetMTime);
l_Lake_Module_instCheckExists___closed__1 = _init_l_Lake_Module_instCheckExists___closed__1();
lean_mark_persistent(l_Lake_Module_instCheckExists___closed__1);
l_Lake_Module_instCheckExists = _init_l_Lake_Module_instCheckExists();
lean_mark_persistent(l_Lake_Module_instCheckExists);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

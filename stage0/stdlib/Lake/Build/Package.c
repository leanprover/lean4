// Lean compiler output
// Module: Lake.Build.Package
// Imports: Init Lake.Util.Git Lake.Util.Sugar Lake.Build.Common Lake.Build.Targets
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
static lean_object* l_Lake_Package_recBuildExtraDepTargets___closed__1;
lean_object* l_Lake_GitRepo_getFilteredRemoteUrl_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Package_fetchTargetJob(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_fetchRelease___lambda__2___closed__11;
uint8_t lean_uint32_to_uint8(uint32_t);
static lean_object* l_Lake_Package_depsFacetConfig___closed__2;
LEAN_EXPORT lean_object* l_Lake_initPackageFacetConfigs;
LEAN_EXPORT lean_object* l_Functor_discard___at_Lake_Package_extraDepFacetConfig___spec__1(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_Package_recBuildExtraDepTargets___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
static lean_object* l_Lake_Package_fetchRelease___lambda__2___closed__16;
static lean_object* l_Functor_discard___at_Lake_Package_extraDepFacetConfig___spec__1___closed__1;
lean_object* l_Lake_BuildJob_add___rarg(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__4(lean_object*, lean_object*, lean_object*);
size_t lean_hashset_mk_idx(lean_object*, uint64_t);
lean_object* lean_io_as_task(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
static lean_object* l_Lake_Package_fetchRelease___lambda__2___closed__13;
static lean_object* l_Lake_Package_fetchRelease___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_recBuildExtraDepTargets___closed__3;
static lean_object* l_Lake_Package_depsFacetConfig___closed__1;
static lean_object* l_Lake_Package_fetchRelease___lambda__2___closed__6;
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_HashSetImp_contains___at_Lake_Package_recComputeDeps___spec__2(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at_Lake_Package_recComputeDeps___spec__3(lean_object*, lean_object*);
static lean_object* l_Lake_Package_fetchRelease___lambda__2___closed__10;
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Lake_Package_fetchRelease___lambda__2___closed__12;
lean_object* l_Lake_download(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_fetchRelease___lambda__2___closed__3;
static lean_object* l_Lake_Package_fetchRelease___lambda__2___closed__15;
LEAN_EXPORT lean_object* l_Lake_Package_releaseFacetConfig___elambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_string_hash(lean_object*);
static lean_object* l_Functor_discard___at_Lake_Package_extraDepFacetConfig___spec__1___closed__2;
static lean_object* l_Lake_Package_fetchRelease___lambda__2___closed__9;
LEAN_EXPORT lean_object* l_Lean_HashSetImp_contains___at_Lake_Package_recComputeDeps___spec__2___boxed(lean_object*, lean_object*);
extern lean_object* l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1;
lean_object* l_System_FilePath_pathExists(lean_object*, lean_object*);
static lean_object* l_Lake_initPackageFacetConfigs___closed__3;
static lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__4___closed__2;
lean_object* l_IO_FS_createDirAll(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_afterReleaseSync___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_fetchRelease___closed__3;
lean_object* l_Lake_BuildTrace_checkUpToDate___at_Lake_buildFileUnlessUpToDate___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_fetchRelease___lambda__2___closed__8;
LEAN_EXPORT lean_object* l_Lake_Package_fetchRelease___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_task_pure(lean_object*);
uint8_t l_instDecidableNot___rarg(uint8_t);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__11___closed__2;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lake_captureProc_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_replace___at_Lake_Package_recComputeDeps___spec__9(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_Lake_Package_recBuildExtraDepTargets___closed__5;
static lean_object* l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeDeps___spec__1___closed__2;
static lean_object* l_Lake_Package_fetchRelease___lambda__2___closed__24;
static lean_object* l_Lake_Package_fetchRelease___lambda__2___closed__7;
lean_object* lean_uint64_to_nat(uint64_t);
lean_object* l_Function_const___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_afterReleaseAsync(lean_object*);
static lean_object* l_Lake_initPackageFacetConfigs___closed__2;
LEAN_EXPORT lean_object* l_Lake_Package_afterReleaseSync___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_afterReleaseAsync___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_fetchRelease___lambda__2___closed__21;
static lean_object* l_Lake_Package_recBuildExtraDepTargets___closed__6;
LEAN_EXPORT lean_object* l_Lake_Package_afterReleaseSync(lean_object*);
static lean_object* l_Lake_Package_releaseFacetConfig___closed__1;
lean_object* lean_io_map_task(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_System_FilePath_parent(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_fetchRelease___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Task_Priority_default;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Lake_Package_recComputeDeps___spec__7___at_Lake_Package_recComputeDeps___spec__8(lean_object*, lean_object*);
lean_object* l_Lake_BuildJob_mix___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_fetchRelease___lambda__2___closed__4;
extern lean_object* l_Lake_BuildTrace_nil;
static lean_object* l_Lake_Package_fetchRelease___lambda__2___closed__22;
static lean_object* l_Lake_Package_fetchRelease___lambda__2___closed__14;
LEAN_EXPORT lean_object* l_Lake_Package_afterReleaseAsync___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_Lake_EResult_map___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_Package_recBuildExtraDepTargets___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lake_Package_recBuildExtraDepTargets___spec__1___closed__1;
extern lean_object* l_Lake_defaultLakeDir;
static lean_object* l_Array_forInUnsafe_loop___at_Lake_Package_recBuildExtraDepTargets___spec__1___closed__2;
lean_object* l_Lake_untar(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lake_Package_fetchRelease___lambda__2___closed__19;
static uint8_t l_Lake_Package_fetchRelease___lambda__2___closed__23;
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
extern lean_object* l_Lake_Git_defaultRemote;
LEAN_EXPORT lean_object* l_Lake_Package_releaseFacetConfig;
static lean_object* l_Lake_Package_fetchRelease___closed__1;
static lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__2___closed__1;
static lean_object* l_Lake_Package_recComputeDeps___closed__1;
LEAN_EXPORT lean_object* l_Lake_Package_fetchRelease___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lake_Package_deps___spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_depsFacetConfig;
static lean_object* l_Lake_Package_fetchRelease___closed__4;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__10(lean_object*, size_t, size_t, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lake_Package_extraDepFacetConfig___closed__2;
static lean_object* l_Lake_Package_extraDepFacetConfig___closed__3;
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeDeps___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_releaseFacetConfig___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_releaseFacetConfig___closed__2;
static lean_object* l_Lake_Package_extraDepFacetConfig___closed__4;
uint64_t l_Lean_Name_hash___override(lean_object*);
lean_object* lean_io_exit(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_fetchRelease___lambda__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_extraDepFacetConfig;
lean_object* l_Lake_instHashablePackage___boxed(lean_object*);
static lean_object* l_Lake_Package_fetchRelease___lambda__2___closed__18;
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Lake_Package_recComputeDeps___spec__7(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_io_bind_task(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Functor_discard___at_Lake_Package_extraDepFacetConfig___spec__1___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_afterReleaseAsync___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_fetchRelease___lambda__2___closed__17;
LEAN_EXPORT lean_object* l_List_elem___at_Lake_Package_recComputeDeps___spec__3___boxed(lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__11___closed__1;
static lean_object* l_Lake_Package_recBuildExtraDepTargets___closed__2;
static lean_object* l_Lake_Package_recBuildExtraDepTargets___closed__4;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_Package_recBuildExtraDepTargets___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_insert___at_Lake_Package_recComputeDeps___spec__4(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_io_error_to_string(lean_object*);
static lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__4___closed__1;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_fetchRelease(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_fetchRelease___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__11(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_insert___at_Lake_Workspace_addPackageFacetConfig___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_instBEqPackage___boxed(lean_object*, lean_object*);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
extern uint32_t l_Lake_noBuildCode;
LEAN_EXPORT lean_object* l_Lean_HashSetImp_moveEntries___at_Lake_Package_recComputeDeps___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lake_Package_extraDepFacetConfig___closed__1;
static lean_object* l_Lake_initPackageFacetConfigs___closed__1;
LEAN_EXPORT lean_object* l_Lean_HashSetImp_expand___at_Lake_Package_recComputeDeps___spec__5(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lake_Package_fetchRelease___lambda__2___closed__20;
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__2(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_fetchRelease___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_Package_recBuildExtraDepTargets___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_fetchRelease___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lake_Package_recComputeDeps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeDeps___spec__1___closed__1;
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__1(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_replace___at_Lake_Package_recComputeDeps___spec__9___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_fetchRelease___lambda__2___closed__5;
uint8_t l_Array_isEmpty___rarg(lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at_Lake_Package_recComputeDeps___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_6, 2);
x_8 = lean_ctor_get(x_4, 2);
x_9 = lean_ctor_get(x_8, 2);
x_10 = lean_name_eq(x_7, x_9);
if (x_10 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_12; 
x_12 = 1;
return x_12;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_HashSetImp_contains___at_Lake_Package_recComputeDeps___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; lean_object* x_9; uint8_t x_10; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Name_hash___override(x_6);
lean_dec(x_6);
x_8 = lean_hashset_mk_idx(x_4, x_7);
x_9 = lean_array_uget(x_3, x_8);
lean_dec(x_3);
x_10 = l_List_elem___at_Lake_Package_recComputeDeps___spec__3(x_2, x_9);
lean_dec(x_9);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lake_Package_recComputeDeps___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_5);
x_8 = lean_apply_1(x_1, x_5);
x_9 = lean_unbox_uint64(x_8);
lean_dec(x_8);
x_10 = lean_hashset_mk_idx(x_7, x_9);
x_11 = lean_array_uget(x_2, x_10);
lean_ctor_set(x_3, 1, x_11);
x_12 = lean_array_uset(x_2, x_10, x_3);
x_2 = x_12;
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint64_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_3);
x_16 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_14);
x_17 = lean_apply_1(x_1, x_14);
x_18 = lean_unbox_uint64(x_17);
lean_dec(x_17);
x_19 = lean_hashset_mk_idx(x_16, x_18);
x_20 = lean_array_uget(x_2, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_array_uset(x_2, x_19, x_21);
x_2 = x_22;
x_3 = x_15;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lake_Package_recComputeDeps___spec__7___at_Lake_Package_recComputeDeps___spec__8(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_array_get_size(x_1);
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Name_hash___override(x_8);
lean_dec(x_8);
x_10 = lean_hashset_mk_idx(x_6, x_9);
x_11 = lean_array_uget(x_1, x_10);
lean_ctor_set(x_2, 1, x_11);
x_12 = lean_array_uset(x_1, x_10, x_2);
x_1 = x_12;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint64_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_2);
x_16 = lean_array_get_size(x_1);
x_17 = lean_ctor_get(x_14, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 2);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Lean_Name_hash___override(x_18);
lean_dec(x_18);
x_20 = lean_hashset_mk_idx(x_16, x_19);
x_21 = lean_array_uget(x_1, x_20);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_array_uset(x_1, x_20, x_22);
x_1 = x_23;
x_2 = x_15;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_moveEntries___at_Lake_Package_recComputeDeps___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_List_foldl___at_Lake_Package_recComputeDeps___spec__7___at_Lake_Package_recComputeDeps___spec__8(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_expand___at_Lake_Package_recComputeDeps___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_mul(x_3, x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_5, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_HashSetImp_moveEntries___at_Lake_Package_recComputeDeps___spec__6(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_replace___at_Lake_Package_recComputeDeps___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_3);
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_6, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_2, 2);
x_11 = lean_ctor_get(x_10, 2);
x_12 = lean_name_eq(x_9, x_11);
lean_dec(x_9);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = l_List_replace___at_Lake_Package_recComputeDeps___spec__9(x_7, x_2, x_3);
lean_ctor_set(x_1, 1, x_13);
return x_1;
}
else
{
lean_dec(x_6);
lean_ctor_set(x_1, 0, x_3);
return x_1;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_1);
x_16 = lean_ctor_get(x_14, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 2);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_2, 2);
x_19 = lean_ctor_get(x_18, 2);
x_20 = lean_name_eq(x_17, x_19);
lean_dec(x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_List_replace___at_Lake_Package_recComputeDeps___spec__9(x_15, x_2, x_3);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
else
{
lean_object* x_23; 
lean_dec(x_14);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_3);
lean_ctor_set(x_23, 1, x_15);
return x_23;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_insert___at_Lake_Package_recComputeDeps___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; size_t x_10; lean_object* x_11; uint8_t x_12; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_array_get_size(x_5);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Name_hash___override(x_8);
lean_dec(x_8);
lean_inc(x_6);
x_10 = lean_hashset_mk_idx(x_6, x_9);
x_11 = lean_array_uget(x_5, x_10);
x_12 = l_List_elem___at_Lake_Package_recComputeDeps___spec__3(x_2, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_4, x_13);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_11);
x_16 = lean_array_uset(x_5, x_10, x_15);
x_17 = lean_nat_dec_le(x_14, x_6);
lean_dec(x_6);
if (x_17 == 0)
{
lean_object* x_18; 
lean_free_object(x_1);
x_18 = l_Lean_HashSetImp_expand___at_Lake_Package_recComputeDeps___spec__5(x_14, x_16);
return x_18;
}
else
{
lean_ctor_set(x_1, 1, x_16);
lean_ctor_set(x_1, 0, x_14);
return x_1;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
lean_inc(x_2);
x_19 = l_List_replace___at_Lake_Package_recComputeDeps___spec__9(x_11, x_2, x_2);
lean_dec(x_2);
x_20 = lean_array_uset(x_5, x_10, x_19);
lean_ctor_set(x_1, 1, x_20);
return x_1;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; size_t x_27; lean_object* x_28; uint8_t x_29; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_1);
x_23 = lean_array_get_size(x_22);
x_24 = lean_ctor_get(x_2, 2);
lean_inc(x_24);
x_25 = lean_ctor_get(x_24, 2);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_Lean_Name_hash___override(x_25);
lean_dec(x_25);
lean_inc(x_23);
x_27 = lean_hashset_mk_idx(x_23, x_26);
x_28 = lean_array_uget(x_22, x_27);
x_29 = l_List_elem___at_Lake_Package_recComputeDeps___spec__3(x_2, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_21, x_30);
lean_dec(x_21);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_32, 1, x_28);
x_33 = lean_array_uset(x_22, x_27, x_32);
x_34 = lean_nat_dec_le(x_31, x_23);
lean_dec(x_23);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = l_Lean_HashSetImp_expand___at_Lake_Package_recComputeDeps___spec__5(x_31, x_33);
return x_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_23);
lean_inc(x_2);
x_37 = l_List_replace___at_Lake_Package_recComputeDeps___spec__9(x_28, x_2, x_2);
lean_dec(x_2);
x_38 = lean_array_uset(x_22, x_27, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_21);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
static lean_object* _init_l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeDeps___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instHashablePackage___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeDeps___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instBEqPackage___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeDeps___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_3);
x_4 = l_Lean_HashSetImp_contains___at_Lake_Package_recComputeDeps___spec__2(x_3, x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
lean_inc(x_2);
x_6 = lean_array_push(x_5, x_2);
x_7 = l_Lean_HashSetImp_insert___at_Lake_Package_recComputeDeps___spec__4(x_3, x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__10(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeDeps___spec__1(x_4, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__11___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("deps", 4);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__11___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__11___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__11(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_27; 
x_27 = lean_usize_dec_eq(x_2, x_3);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_array_uget(x_1, x_2);
x_29 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__11___closed__2;
lean_inc(x_28);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
lean_inc(x_5);
lean_inc(x_8);
lean_inc(x_6);
x_31 = lean_apply_6(x_5, x_30, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = !lean_is_exclusive(x_32);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_32, 0);
lean_dec(x_36);
x_37 = !lean_is_exclusive(x_33);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_33, 0);
x_39 = lean_array_get_size(x_38);
x_40 = lean_unsigned_to_nat(0u);
x_41 = lean_nat_dec_lt(x_40, x_39);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_39);
lean_dec(x_38);
x_42 = l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeDeps___spec__1(x_4, x_28);
lean_ctor_set(x_33, 0, x_42);
x_11 = x_32;
x_12 = x_34;
goto block_26;
}
else
{
uint8_t x_43; 
x_43 = lean_nat_dec_le(x_39, x_39);
if (x_43 == 0)
{
lean_object* x_44; 
lean_dec(x_39);
lean_dec(x_38);
x_44 = l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeDeps___spec__1(x_4, x_28);
lean_ctor_set(x_33, 0, x_44);
x_11 = x_32;
x_12 = x_34;
goto block_26;
}
else
{
size_t x_45; size_t x_46; lean_object* x_47; lean_object* x_48; 
x_45 = 0;
x_46 = lean_usize_of_nat(x_39);
lean_dec(x_39);
x_47 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__10(x_38, x_45, x_46, x_4);
lean_dec(x_38);
x_48 = l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeDeps___spec__1(x_47, x_28);
lean_ctor_set(x_33, 0, x_48);
x_11 = x_32;
x_12 = x_34;
goto block_26;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_49 = lean_ctor_get(x_33, 0);
x_50 = lean_ctor_get(x_33, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_33);
x_51 = lean_array_get_size(x_49);
x_52 = lean_unsigned_to_nat(0u);
x_53 = lean_nat_dec_lt(x_52, x_51);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_51);
lean_dec(x_49);
x_54 = l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeDeps___spec__1(x_4, x_28);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_50);
lean_ctor_set(x_32, 0, x_55);
x_11 = x_32;
x_12 = x_34;
goto block_26;
}
else
{
uint8_t x_56; 
x_56 = lean_nat_dec_le(x_51, x_51);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_51);
lean_dec(x_49);
x_57 = l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeDeps___spec__1(x_4, x_28);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_50);
lean_ctor_set(x_32, 0, x_58);
x_11 = x_32;
x_12 = x_34;
goto block_26;
}
else
{
size_t x_59; size_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = 0;
x_60 = lean_usize_of_nat(x_51);
lean_dec(x_51);
x_61 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__10(x_49, x_59, x_60, x_4);
lean_dec(x_49);
x_62 = l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeDeps___spec__1(x_61, x_28);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_50);
lean_ctor_set(x_32, 0, x_63);
x_11 = x_32;
x_12 = x_34;
goto block_26;
}
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_64 = lean_ctor_get(x_32, 1);
lean_inc(x_64);
lean_dec(x_32);
x_65 = lean_ctor_get(x_33, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_33, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_67 = x_33;
} else {
 lean_dec_ref(x_33);
 x_67 = lean_box(0);
}
x_68 = lean_array_get_size(x_65);
x_69 = lean_unsigned_to_nat(0u);
x_70 = lean_nat_dec_lt(x_69, x_68);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_68);
lean_dec(x_65);
x_71 = l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeDeps___spec__1(x_4, x_28);
if (lean_is_scalar(x_67)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_67;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_66);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_64);
x_11 = x_73;
x_12 = x_34;
goto block_26;
}
else
{
uint8_t x_74; 
x_74 = lean_nat_dec_le(x_68, x_68);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_68);
lean_dec(x_65);
x_75 = l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeDeps___spec__1(x_4, x_28);
if (lean_is_scalar(x_67)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_67;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_66);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_64);
x_11 = x_77;
x_12 = x_34;
goto block_26;
}
else
{
size_t x_78; size_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_78 = 0;
x_79 = lean_usize_of_nat(x_68);
lean_dec(x_68);
x_80 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__10(x_65, x_78, x_79, x_4);
lean_dec(x_65);
x_81 = l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeDeps___spec__1(x_80, x_28);
if (lean_is_scalar(x_67)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_67;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_66);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_64);
x_11 = x_83;
x_12 = x_34;
goto block_26;
}
}
}
}
else
{
lean_object* x_84; uint8_t x_85; 
lean_dec(x_28);
lean_dec(x_4);
x_84 = lean_ctor_get(x_31, 1);
lean_inc(x_84);
lean_dec(x_31);
x_85 = !lean_is_exclusive(x_32);
if (x_85 == 0)
{
x_11 = x_32;
x_12 = x_84;
goto block_26;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_32, 0);
x_87 = lean_ctor_get(x_32, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_32);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
x_11 = x_88;
x_12 = x_84;
goto block_26;
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_28);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_89 = !lean_is_exclusive(x_31);
if (x_89 == 0)
{
return x_31;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_31, 0);
x_91 = lean_ctor_get(x_31, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_31);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_4);
lean_ctor_set(x_93, 1, x_7);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_9);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_10);
return x_95;
}
block_26:
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = 1;
x_18 = lean_usize_add(x_2, x_17);
x_2 = x_18;
x_4 = x_15;
x_7 = x_16;
x_9 = x_14;
x_10 = x_12;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_12);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_11, 0);
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_11);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_12);
return x_25;
}
}
}
}
}
static lean_object* _init_l_Lake_Package_recComputeDeps___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_recComputeDeps(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_8 = lean_ctor_get(x_1, 6);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_array_get_size(x_8);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = 0;
x_12 = l_Array_mapMUnsafe_map___at_Lake_Package_deps___spec__1(x_10, x_11, x_8);
x_13 = lean_array_get_size(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_lt(x_14, x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_16 = l_Lake_Package_recComputeDeps___closed__1;
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_4);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_6);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_7);
return x_19;
}
else
{
uint8_t x_20; 
x_20 = lean_nat_dec_le(x_13, x_13);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_21 = l_Lake_Package_recComputeDeps___closed__1;
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_4);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_6);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_7);
return x_24;
}
else
{
size_t x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_26 = l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1;
x_27 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__11(x_12, x_11, x_25, x_26, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_12);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = !lean_is_exclusive(x_27);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_27, 0);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_28);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_28, 0);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_29);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_29, 0);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
lean_ctor_set(x_29, 0, x_36);
return x_27;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_29, 0);
x_38 = lean_ctor_get(x_29, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_29);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
lean_ctor_set(x_28, 0, x_40);
return x_27;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_41 = lean_ctor_get(x_28, 1);
lean_inc(x_41);
lean_dec(x_28);
x_42 = lean_ctor_get(x_29, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_29, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_44 = x_29;
} else {
 lean_dec_ref(x_29);
 x_44 = lean_box(0);
}
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
if (lean_is_scalar(x_44)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_44;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_43);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_41);
lean_ctor_set(x_27, 0, x_47);
return x_27;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_48 = lean_ctor_get(x_27, 1);
lean_inc(x_48);
lean_dec(x_27);
x_49 = lean_ctor_get(x_28, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_50 = x_28;
} else {
 lean_dec_ref(x_28);
 x_50 = lean_box(0);
}
x_51 = lean_ctor_get(x_29, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_29, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_53 = x_29;
} else {
 lean_dec_ref(x_29);
 x_53 = lean_box(0);
}
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
if (lean_is_scalar(x_53)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_53;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_52);
if (lean_is_scalar(x_50)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_50;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_49);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_48);
return x_57;
}
}
else
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_27);
if (x_58 == 0)
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_27, 0);
lean_dec(x_59);
x_60 = !lean_is_exclusive(x_28);
if (x_60 == 0)
{
return x_27;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_28, 0);
x_62 = lean_ctor_get(x_28, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_28);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set(x_27, 0, x_63);
return x_27;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_64 = lean_ctor_get(x_27, 1);
lean_inc(x_64);
lean_dec(x_27);
x_65 = lean_ctor_get(x_28, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_28, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_67 = x_28;
} else {
 lean_dec_ref(x_28);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_64);
return x_69;
}
}
}
else
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_27);
if (x_70 == 0)
{
return x_27;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_27, 0);
x_72 = lean_ctor_get(x_27, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_27);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at_Lake_Package_recComputeDeps___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_elem___at_Lake_Package_recComputeDeps___spec__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_contains___at_Lake_Package_recComputeDeps___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_HashSetImp_contains___at_Lake_Package_recComputeDeps___spec__2(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_replace___at_Lake_Package_recComputeDeps___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_replace___at_Lake_Package_recComputeDeps___spec__9(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__10(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__11(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_13;
}
}
static lean_object* _init_l_Lake_Package_depsFacetConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Package_recComputeDeps), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_depsFacetConfig___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Package_depsFacetConfig___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_depsFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Package_depsFacetConfig___closed__2;
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lake_Package_recBuildExtraDepTargets___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("extraDep", 8);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lake_Package_recBuildExtraDepTargets___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_forInUnsafe_loop___at_Lake_Package_recBuildExtraDepTargets___spec__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_Package_recBuildExtraDepTargets___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_45; 
x_45 = lean_usize_dec_lt(x_3, x_2);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_7);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_9);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_10);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_array_uget(x_1, x_3);
x_50 = l_Array_forInUnsafe_loop___at_Lake_Package_recBuildExtraDepTargets___spec__1___closed__2;
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
lean_inc(x_5);
lean_inc(x_8);
lean_inc(x_6);
x_52 = lean_apply_6(x_5, x_51, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = !lean_is_exclusive(x_53);
if (x_56 == 0)
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_53, 0);
lean_dec(x_57);
x_58 = !lean_is_exclusive(x_54);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_54, 0);
x_60 = l_Lake_BuildJob_mix___rarg(x_4, x_59, x_55);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_54, 0, x_63);
x_11 = x_53;
x_12 = x_62;
goto block_44;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_64 = lean_ctor_get(x_54, 0);
x_65 = lean_ctor_get(x_54, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_54);
x_66 = l_Lake_BuildJob_mix___rarg(x_4, x_64, x_55);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_67);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_65);
lean_ctor_set(x_53, 0, x_70);
x_11 = x_53;
x_12 = x_68;
goto block_44;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_71 = lean_ctor_get(x_53, 1);
lean_inc(x_71);
lean_dec(x_53);
x_72 = lean_ctor_get(x_54, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_54, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_74 = x_54;
} else {
 lean_dec_ref(x_54);
 x_74 = lean_box(0);
}
x_75 = l_Lake_BuildJob_mix___rarg(x_4, x_72, x_55);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_76);
if (lean_is_scalar(x_74)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_74;
}
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_73);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_71);
x_11 = x_80;
x_12 = x_77;
goto block_44;
}
}
else
{
lean_object* x_81; uint8_t x_82; 
lean_dec(x_4);
x_81 = lean_ctor_get(x_52, 1);
lean_inc(x_81);
lean_dec(x_52);
x_82 = !lean_is_exclusive(x_53);
if (x_82 == 0)
{
x_11 = x_53;
x_12 = x_81;
goto block_44;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_53, 0);
x_84 = lean_ctor_get(x_53, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_53);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
x_11 = x_85;
x_12 = x_81;
goto block_44;
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_86 = !lean_is_exclusive(x_52);
if (x_86 == 0)
{
return x_52;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_52, 0);
x_88 = lean_ctor_get(x_52, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_52);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
block_44:
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_11, 0);
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec(x_14);
lean_ctor_set(x_13, 0, x_19);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_11);
lean_ctor_set(x_20, 1, x_12);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_11, 0, x_23);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_11);
lean_ctor_set(x_24, 1, x_12);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_11, 1);
lean_inc(x_25);
lean_dec(x_11);
x_26 = lean_ctor_get(x_13, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_27 = x_13;
} else {
 lean_dec_ref(x_13);
 x_27 = lean_box(0);
}
x_28 = lean_ctor_get(x_14, 0);
lean_inc(x_28);
lean_dec(x_14);
if (lean_is_scalar(x_27)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_27;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_25);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_12);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; size_t x_35; size_t x_36; 
x_32 = lean_ctor_get(x_11, 1);
lean_inc(x_32);
lean_dec(x_11);
x_33 = lean_ctor_get(x_13, 1);
lean_inc(x_33);
lean_dec(x_13);
x_34 = lean_ctor_get(x_14, 0);
lean_inc(x_34);
lean_dec(x_14);
x_35 = 1;
x_36 = lean_usize_add(x_3, x_35);
x_3 = x_36;
x_4 = x_34;
x_7 = x_33;
x_9 = x_32;
x_10 = x_12;
goto _start;
}
}
else
{
uint8_t x_38; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_38 = !lean_is_exclusive(x_11);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_11);
lean_ctor_set(x_39, 1, x_12);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_11, 0);
x_41 = lean_ctor_get(x_11, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_11);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_12);
return x_43;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_Package_recBuildExtraDepTargets___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_46; 
x_46 = lean_usize_dec_lt(x_4, x_3);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_5);
lean_ctor_set(x_47, 1, x_8);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_10);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_11);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_array_uget(x_2, x_4);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_51 = l_Lake_Package_fetchTargetJob(x_1, x_50, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
x_55 = !lean_is_exclusive(x_52);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = lean_ctor_get(x_52, 0);
lean_dec(x_56);
x_57 = !lean_is_exclusive(x_53);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_58 = lean_ctor_get(x_53, 0);
x_59 = l_Lake_BuildJob_mix___rarg(x_5, x_58, x_54);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_53, 0, x_62);
x_12 = x_52;
x_13 = x_61;
goto block_45;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_63 = lean_ctor_get(x_53, 0);
x_64 = lean_ctor_get(x_53, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_53);
x_65 = l_Lake_BuildJob_mix___rarg(x_5, x_63, x_54);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_66);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_64);
lean_ctor_set(x_52, 0, x_69);
x_12 = x_52;
x_13 = x_67;
goto block_45;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_70 = lean_ctor_get(x_52, 1);
lean_inc(x_70);
lean_dec(x_52);
x_71 = lean_ctor_get(x_53, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_53, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_73 = x_53;
} else {
 lean_dec_ref(x_53);
 x_73 = lean_box(0);
}
x_74 = l_Lake_BuildJob_mix___rarg(x_5, x_71, x_54);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_75);
if (lean_is_scalar(x_73)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_73;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_72);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_70);
x_12 = x_79;
x_13 = x_76;
goto block_45;
}
}
else
{
lean_object* x_80; uint8_t x_81; 
lean_dec(x_5);
x_80 = lean_ctor_get(x_51, 1);
lean_inc(x_80);
lean_dec(x_51);
x_81 = !lean_is_exclusive(x_52);
if (x_81 == 0)
{
x_12 = x_52;
x_13 = x_80;
goto block_45;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_52, 0);
x_83 = lean_ctor_get(x_52, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_52);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_12 = x_84;
x_13 = x_80;
goto block_45;
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_85 = !lean_is_exclusive(x_51);
if (x_85 == 0)
{
return x_51;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_51, 0);
x_87 = lean_ctor_get(x_51, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_51);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
block_45:
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_12, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 0);
lean_dec(x_19);
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
lean_dec(x_15);
lean_ctor_set(x_14, 0, x_20);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_12);
lean_ctor_set(x_21, 1, x_13);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_ctor_get(x_15, 0);
lean_inc(x_23);
lean_dec(x_15);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_12, 0, x_24);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_12);
lean_ctor_set(x_25, 1, x_13);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_12, 1);
lean_inc(x_26);
lean_dec(x_12);
x_27 = lean_ctor_get(x_14, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_28 = x_14;
} else {
 lean_dec_ref(x_14);
 x_28 = lean_box(0);
}
x_29 = lean_ctor_get(x_15, 0);
lean_inc(x_29);
lean_dec(x_15);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_13);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; 
x_33 = lean_ctor_get(x_12, 1);
lean_inc(x_33);
lean_dec(x_12);
x_34 = lean_ctor_get(x_14, 1);
lean_inc(x_34);
lean_dec(x_14);
x_35 = lean_ctor_get(x_15, 0);
lean_inc(x_35);
lean_dec(x_15);
x_36 = 1;
x_37 = lean_usize_add(x_4, x_36);
x_4 = x_37;
x_5 = x_35;
x_8 = x_34;
x_10 = x_33;
x_11 = x_13;
goto _start;
}
}
else
{
uint8_t x_39; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_12);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_12);
lean_ctor_set(x_40, 1, x_13);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_12, 0);
x_42 = lean_ctor_get(x_12, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_12);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_13);
return x_44;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__1(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 4);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_array_get_size(x_12);
x_14 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_15 = l_Array_forInUnsafe_loop___at_Lake_Package_recBuildExtraDepTargets___spec__2(x_1, x_12, x_14, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_15, 0);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_16, 0);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_17);
if (x_22 == 0)
{
return x_15;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_17, 0);
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_17);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_16, 0, x_25);
return x_15;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_dec(x_16);
x_27 = lean_ctor_get(x_17, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_17, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_29 = x_17;
} else {
 lean_dec_ref(x_17);
 x_29 = lean_box(0);
}
if (lean_is_scalar(x_29)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_29;
}
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_28);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_26);
lean_ctor_set(x_15, 0, x_31);
return x_15;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
lean_dec(x_15);
x_33 = lean_ctor_get(x_16, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_34 = x_16;
} else {
 lean_dec_ref(x_16);
 x_34 = lean_box(0);
}
x_35 = lean_ctor_get(x_17, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_17, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_37 = x_17;
} else {
 lean_dec_ref(x_17);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
if (lean_is_scalar(x_34)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_34;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_33);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_32);
return x_40;
}
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_15);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_15, 0);
lean_dec(x_42);
x_43 = !lean_is_exclusive(x_16);
if (x_43 == 0)
{
return x_15;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_16, 0);
x_45 = lean_ctor_get(x_16, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_16);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_15, 0, x_46);
return x_15;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_15, 1);
lean_inc(x_47);
lean_dec(x_15);
x_48 = lean_ctor_get(x_16, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_16, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_50 = x_16;
} else {
 lean_dec_ref(x_16);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(1, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_49);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_47);
return x_52;
}
}
}
else
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_15);
if (x_53 == 0)
{
return x_15;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_15, 0);
x_55 = lean_ctor_get(x_15, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_15);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
static lean_object* _init_l_Lake_Package_recBuildExtraDepTargets___lambda__2___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = l_Lake_BuildTrace_nil;
x_3 = lean_box(x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__2(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
lean_dec(x_5);
x_6 = 1;
x_7 = lean_box(x_6);
lean_ctor_set(x_3, 0, x_7);
return x_1;
}
else
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec(x_3);
x_9 = 1;
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
lean_ctor_set(x_1, 0, x_11);
return x_1;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_15 = x_12;
} else {
 lean_dec_ref(x_12);
 x_15 = lean_box(0);
}
x_16 = 1;
x_17 = lean_box(x_16);
if (lean_is_scalar(x_15)) {
 x_18 = lean_alloc_ctor(0, 2, 0);
} else {
 x_18 = x_15;
}
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_14);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_13);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_1);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_1, 0);
lean_dec(x_21);
x_22 = l_Lake_Package_recBuildExtraDepTargets___lambda__2___closed__1;
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 0, x_22);
return x_1;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_dec(x_1);
x_24 = l_Lake_Package_recBuildExtraDepTargets___lambda__2___closed__1;
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
}
static lean_object* _init_l_Lake_Package_recBuildExtraDepTargets___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("fetching cloud release failed; falling back to local build", 58);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_recBuildExtraDepTargets___lambda__4___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 2;
x_2 = l_Lake_Package_recBuildExtraDepTargets___lambda__4___closed__1;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_unbox(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec(x_4);
x_9 = l_Lake_Package_recBuildExtraDepTargets___lambda__4___closed__2;
x_10 = lean_array_push(x_7, x_9);
x_11 = lean_box(0);
x_12 = l_Lake_Package_recBuildExtraDepTargets___lambda__3(x_8, x_11, x_1, x_10, x_3);
lean_dec(x_1);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_dec(x_4);
x_15 = lean_box(0);
x_16 = l_Lake_Package_recBuildExtraDepTargets___lambda__3(x_14, x_15, x_1, x_13, x_3);
lean_dec(x_1);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_2);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_3);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_2, 0);
x_20 = lean_ctor_get(x_2, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_2);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_3);
return x_22;
}
}
}
}
static lean_object* _init_l_Lake_Package_recBuildExtraDepTargets___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_BuildTrace_nil;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_recBuildExtraDepTargets___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_recBuildExtraDepTargets___closed__1;
x_2 = l_Lake_Package_recComputeDeps___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_recBuildExtraDepTargets___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Package_recBuildExtraDepTargets___closed__2;
x_2 = lean_task_pure(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_recBuildExtraDepTargets___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("release", 7);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_recBuildExtraDepTargets___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Package_recBuildExtraDepTargets___closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_recBuildExtraDepTargets___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Package_recBuildExtraDepTargets___lambda__2), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; size_t x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_ctor_get(x_1, 6);
lean_inc(x_8);
x_9 = lean_array_get_size(x_8);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = 0;
x_12 = l_Array_mapMUnsafe_map___at_Lake_Package_deps___spec__1(x_10, x_11, x_8);
x_13 = lean_array_get_size(x_12);
x_14 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_15 = l_Lake_Package_recBuildExtraDepTargets___closed__3;
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
x_16 = l_Array_forInUnsafe_loop___at_Lake_Package_recBuildExtraDepTargets___spec__1(x_12, x_14, x_11, x_15, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_30; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_ctor_get(x_5, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 2);
lean_inc(x_24);
x_25 = lean_ctor_get(x_24, 2);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_ctor_get(x_26, 2);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_ctor_get(x_27, 2);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_name_eq(x_25, x_28);
lean_dec(x_28);
lean_dec(x_25);
x_30 = l_instDecidableNot___rarg(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_24);
x_31 = lean_box(0);
x_32 = l_Lake_Package_recBuildExtraDepTargets___lambda__1(x_1, x_11, x_21, x_31, x_2, x_3, x_22, x_5, x_20, x_19);
return x_32;
}
else
{
uint8_t x_33; 
x_33 = lean_ctor_get_uint8(x_24, sizeof(void*)*17 + 1);
lean_dec(x_24);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_box(0);
x_35 = l_Lake_Package_recBuildExtraDepTargets___lambda__1(x_1, x_11, x_21, x_34, x_2, x_3, x_22, x_5, x_20, x_19);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = l_Lake_Package_recBuildExtraDepTargets___closed__5;
lean_inc(x_1);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_1);
lean_ctor_set(x_37, 1, x_36);
lean_inc(x_2);
lean_inc(x_5);
lean_inc(x_3);
x_38 = lean_apply_6(x_2, x_37, x_3, x_22, x_5, x_20, x_19);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = lean_ctor_get(x_40, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
lean_dec(x_40);
x_45 = l_Lake_Package_recBuildExtraDepTargets___closed__6;
x_46 = l_Task_Priority_default;
x_47 = 0;
x_48 = lean_task_map(x_45, x_43, x_46, x_47);
lean_inc(x_5);
x_49 = lean_alloc_closure((void*)(l_Lake_Package_recBuildExtraDepTargets___lambda__4), 3, 1);
lean_closure_set(x_49, 0, x_5);
x_50 = lean_io_map_task(x_49, x_48, x_46, x_47, x_41);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = l_Lake_BuildJob_add___rarg(x_21, x_51, x_52);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_box(0);
x_57 = l_Lake_Package_recBuildExtraDepTargets___lambda__1(x_1, x_11, x_54, x_56, x_2, x_3, x_44, x_5, x_42, x_55);
return x_57;
}
else
{
uint8_t x_58; 
lean_dec(x_21);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_38);
if (x_58 == 0)
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_38, 0);
lean_dec(x_59);
x_60 = !lean_is_exclusive(x_39);
if (x_60 == 0)
{
return x_38;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_39, 0);
x_62 = lean_ctor_get(x_39, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_39);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set(x_38, 0, x_63);
return x_38;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_64 = lean_ctor_get(x_38, 1);
lean_inc(x_64);
lean_dec(x_38);
x_65 = lean_ctor_get(x_39, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_39, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_67 = x_39;
} else {
 lean_dec_ref(x_39);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_64);
return x_69;
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_21);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_38);
if (x_70 == 0)
{
return x_38;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_38, 0);
x_72 = lean_ctor_get(x_38, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_38);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_16);
if (x_74 == 0)
{
lean_object* x_75; uint8_t x_76; 
x_75 = lean_ctor_get(x_16, 0);
lean_dec(x_75);
x_76 = !lean_is_exclusive(x_17);
if (x_76 == 0)
{
return x_16;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_17, 0);
x_78 = lean_ctor_get(x_17, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_17);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
lean_ctor_set(x_16, 0, x_79);
return x_16;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_80 = lean_ctor_get(x_16, 1);
lean_inc(x_80);
lean_dec(x_16);
x_81 = lean_ctor_get(x_17, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_17, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_83 = x_17;
} else {
 lean_dec_ref(x_17);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_82);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_80);
return x_85;
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_16);
if (x_86 == 0)
{
return x_16;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_16, 0);
x_88 = lean_ctor_get(x_16, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_16);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_Package_recBuildExtraDepTargets___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_forInUnsafe_loop___at_Lake_Package_recBuildExtraDepTargets___spec__1(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_Package_recBuildExtraDepTargets___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_forInUnsafe_loop___at_Lake_Package_recBuildExtraDepTargets___spec__2(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; lean_object* x_12; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = l_Lake_Package_recBuildExtraDepTargets___lambda__1(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Package_recBuildExtraDepTargets___lambda__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Functor_discard___at_Lake_Package_extraDepFacetConfig___spec__1___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_dec(x_3);
x_4 = lean_box(0);
lean_ctor_set(x_1, 0, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
}
static lean_object* _init_l_Functor_discard___at_Lake_Package_extraDepFacetConfig___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Functor_discard___at_Lake_Package_extraDepFacetConfig___spec__1___lambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Functor_discard___at_Lake_Package_extraDepFacetConfig___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Functor_discard___at_Lake_Package_extraDepFacetConfig___spec__1___closed__1;
x_2 = lean_alloc_closure((void*)(l_Lake_EResult_map___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Functor_discard___at_Lake_Package_extraDepFacetConfig___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_2 = l_Functor_discard___at_Lake_Package_extraDepFacetConfig___spec__1___closed__2;
x_3 = l_Task_Priority_default;
x_4 = 0;
x_5 = lean_task_map(x_2, x_1, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_Package_extraDepFacetConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Functor_discard___at_Lake_Package_extraDepFacetConfig___spec__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_extraDepFacetConfig___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Package_extraDepFacetConfig___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_extraDepFacetConfig___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Package_recBuildExtraDepTargets), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_extraDepFacetConfig___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_extraDepFacetConfig___closed__3;
x_2 = l_Lake_Package_extraDepFacetConfig___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_extraDepFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Package_extraDepFacetConfig___closed__4;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_fetchRelease___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lake_Package_recBuildExtraDepTargets___closed__1;
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
}
static lean_object* _init_l_Lake_Package_fetchRelease___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_fetchRelease___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("describe", 8);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_fetchRelease___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_fetchRelease___lambda__2___closed__1;
x_2 = l_Lake_Package_fetchRelease___lambda__2___closed__2;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_fetchRelease___lambda__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("--tags", 6);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_fetchRelease___lambda__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_fetchRelease___lambda__2___closed__3;
x_2 = l_Lake_Package_fetchRelease___lambda__2___closed__4;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_fetchRelease___lambda__2___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("--exact-match", 13);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_fetchRelease___lambda__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_fetchRelease___lambda__2___closed__5;
x_2 = l_Lake_Package_fetchRelease___lambda__2___closed__6;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_fetchRelease___lambda__2___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("HEAD", 4);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_fetchRelease___lambda__2___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_fetchRelease___lambda__2___closed__7;
x_2 = l_Lake_Package_fetchRelease___lambda__2___closed__8;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_fetchRelease___lambda__2___closed__10() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_2, 0, x_1);
lean_ctor_set_uint8(x_2, 1, x_1);
lean_ctor_set_uint8(x_2, 2, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_fetchRelease___lambda__2___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("git", 3);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_fetchRelease___lambda__2___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_fetchRelease___lambda__2___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(": wanted prebuilt release, ", 27);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_fetchRelease___lambda__2___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("but could not find an associated tag for the package's revision", 63);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_fetchRelease___lambda__2___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("/releases/download/", 19);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_fetchRelease___lambda__2___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("/", 1);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_fetchRelease___lambda__2___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Package_fetchRelease___lambda__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_fetchRelease___lambda__2___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unpacking ", 10);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_fetchRelease___lambda__2___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(".trace", 6);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_fetchRelease___lambda__2___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_fetchRelease___lambda__2___closed__21() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = l_Lake_Package_fetchRelease___lambda__2___closed__20;
x_3 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint32(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_fetchRelease___lambda__2___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("downloading ", 12);
return x_1;
}
}
static uint8_t _init_l_Lake_Package_fetchRelease___lambda__2___closed__23() {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = l_Lake_noBuildCode;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_fetchRelease___lambda__2___closed__24() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("but package's repository URL was not known; it may need to set `releaseRepo\?`", 77);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_fetchRelease___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = l_Lake_Git_defaultRemote;
lean_inc(x_1);
x_9 = l_Lake_GitRepo_getFilteredRemoteUrl_x3f(x_8, x_1, x_7);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
if (lean_obj_tag(x_6) == 0)
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; uint8_t x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_249 = l_Lake_Package_fetchRelease___lambda__2___closed__12;
x_250 = lean_string_append(x_249, x_3);
x_251 = l_Lake_Package_fetchRelease___lambda__2___closed__13;
x_252 = lean_string_append(x_250, x_251);
x_253 = l_Lake_Package_fetchRelease___lambda__2___closed__24;
x_254 = lean_string_append(x_252, x_253);
x_255 = 3;
x_256 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_256, 0, x_254);
lean_ctor_set_uint8(x_256, sizeof(void*)*1, x_255);
x_257 = lean_array_get_size(x_2);
x_258 = lean_array_push(x_2, x_256);
x_259 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_259, 0, x_257);
lean_ctor_set(x_259, 1, x_258);
lean_ctor_set(x_9, 0, x_259);
return x_9;
}
else
{
lean_object* x_260; 
lean_free_object(x_9);
x_260 = lean_ctor_get(x_11, 0);
lean_inc(x_260);
lean_dec(x_11);
x_13 = x_260;
goto block_248;
}
}
else
{
lean_object* x_261; 
lean_free_object(x_9);
lean_dec(x_11);
x_261 = lean_ctor_get(x_6, 0);
lean_inc(x_261);
lean_dec(x_6);
x_13 = x_261;
goto block_248;
}
block_248:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_inc(x_1);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_1);
x_15 = l_Lake_Package_fetchRelease___lambda__2___closed__10;
x_16 = l_Lake_Package_fetchRelease___lambda__2___closed__11;
x_17 = l_Lake_Package_fetchRelease___lambda__2___closed__9;
x_18 = 0;
lean_inc(x_2);
x_19 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_16);
lean_ctor_set(x_19, 2, x_17);
lean_ctor_set(x_19, 3, x_14);
lean_ctor_set(x_19, 4, x_2);
lean_ctor_set_uint8(x_19, sizeof(void*)*5, x_18);
x_20 = l_Lake_captureProc_x3f(x_19, x_12);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = l_Lake_Package_fetchRelease___lambda__2___closed__12;
x_25 = lean_string_append(x_24, x_3);
x_26 = l_Lake_Package_fetchRelease___lambda__2___closed__13;
x_27 = lean_string_append(x_25, x_26);
x_28 = l_Lake_Package_fetchRelease___lambda__2___closed__14;
x_29 = lean_string_append(x_27, x_28);
x_30 = 3;
x_31 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*1, x_30);
x_32 = lean_array_get_size(x_2);
x_33 = lean_array_push(x_2, x_31);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_20, 0, x_34);
return x_20;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_35 = lean_ctor_get(x_20, 1);
lean_inc(x_35);
lean_dec(x_20);
x_36 = l_Lake_Package_fetchRelease___lambda__2___closed__12;
x_37 = lean_string_append(x_36, x_3);
x_38 = l_Lake_Package_fetchRelease___lambda__2___closed__13;
x_39 = lean_string_append(x_37, x_38);
x_40 = l_Lake_Package_fetchRelease___lambda__2___closed__14;
x_41 = lean_string_append(x_39, x_40);
x_42 = 3;
x_43 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set_uint8(x_43, sizeof(void*)*1, x_42);
x_44 = lean_array_get_size(x_2);
x_45 = lean_array_push(x_2, x_43);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_35);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint64_t x_67; uint64_t x_68; uint64_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
x_48 = lean_ctor_get(x_20, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_49 = x_20;
} else {
 lean_dec_ref(x_20);
 x_49 = lean_box(0);
}
x_50 = lean_ctor_get(x_21, 0);
lean_inc(x_50);
lean_dec(x_21);
x_51 = l_Lake_Package_fetchRelease___lambda__2___closed__12;
x_52 = lean_string_append(x_51, x_13);
lean_dec(x_13);
x_53 = l_Lake_Package_fetchRelease___lambda__2___closed__15;
x_54 = lean_string_append(x_52, x_53);
x_55 = lean_string_append(x_54, x_50);
x_56 = l_Lake_Package_fetchRelease___lambda__2___closed__16;
x_57 = lean_string_append(x_55, x_56);
x_58 = lean_ctor_get(x_4, 16);
lean_inc(x_58);
x_59 = lean_string_append(x_57, x_58);
x_60 = lean_string_append(x_59, x_51);
x_61 = lean_string_append(x_51, x_3);
x_62 = lean_string_append(x_61, x_56);
x_63 = lean_string_append(x_62, x_50);
lean_dec(x_50);
x_64 = lean_string_append(x_63, x_56);
x_65 = lean_string_append(x_64, x_58);
x_66 = lean_string_append(x_65, x_51);
x_67 = lean_string_hash(x_60);
x_68 = 1723;
x_69 = lean_uint64_mix_hash(x_68, x_67);
x_70 = l_Lake_defaultLakeDir;
lean_inc(x_1);
x_71 = l_System_FilePath_join(x_1, x_70);
x_72 = l_System_FilePath_join(x_71, x_58);
x_144 = l_Lake_Package_fetchRelease___lambda__2___closed__19;
lean_inc(x_72);
x_145 = lean_string_append(x_72, x_144);
x_146 = l_Lake_Package_fetchRelease___lambda__2___closed__21;
x_147 = lean_box_uint64(x_69);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_146);
x_149 = l_Lake_Package_fetchRelease___lambda__2___closed__22;
x_150 = lean_string_append(x_149, x_66);
x_151 = lean_string_append(x_150, x_51);
x_152 = 0;
x_153 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set_uint8(x_153, sizeof(void*)*1, x_152);
x_154 = l_Lake_BuildTrace_checkUpToDate___at_Lake_buildFileUnlessUpToDate___spec__1(x_72, x_148, x_145, x_5, x_2, x_48);
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_unbox(x_156);
lean_dec(x_156);
if (x_157 == 0)
{
lean_object* x_158; uint8_t x_159; 
x_158 = lean_ctor_get(x_5, 0);
lean_inc(x_158);
x_159 = lean_ctor_get_uint8(x_158, 2);
lean_dec(x_158);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_160 = lean_ctor_get(x_154, 1);
lean_inc(x_160);
lean_dec(x_154);
x_161 = lean_ctor_get(x_155, 1);
lean_inc(x_161);
lean_dec(x_155);
x_162 = lean_array_push(x_161, x_153);
lean_inc(x_72);
x_163 = l_Lake_download(x_60, x_72, x_162, x_160);
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_180; 
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_167 = x_164;
} else {
 lean_dec_ref(x_164);
 x_167 = lean_box(0);
}
lean_inc(x_145);
x_180 = l_System_FilePath_parent(x_145);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_uint64_to_nat(x_69);
x_182 = l___private_Init_Data_Repr_0__Nat_reprFast(x_181);
x_183 = l_IO_FS_writeFile(x_145, x_182, x_165);
lean_dec(x_182);
lean_dec(x_145);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
lean_dec(x_183);
x_186 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_186, 0, x_184);
x_168 = x_186;
x_169 = x_185;
goto block_179;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_183, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_183, 1);
lean_inc(x_188);
lean_dec(x_183);
x_189 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_189, 0, x_187);
x_168 = x_189;
x_169 = x_188;
goto block_179;
}
}
else
{
lean_object* x_190; lean_object* x_191; 
x_190 = lean_ctor_get(x_180, 0);
lean_inc(x_190);
lean_dec(x_180);
x_191 = l_IO_FS_createDirAll(x_190, x_165);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_192 = lean_ctor_get(x_191, 1);
lean_inc(x_192);
lean_dec(x_191);
x_193 = lean_uint64_to_nat(x_69);
x_194 = l___private_Init_Data_Repr_0__Nat_reprFast(x_193);
x_195 = l_IO_FS_writeFile(x_145, x_194, x_192);
lean_dec(x_194);
lean_dec(x_145);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
lean_dec(x_195);
x_198 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_198, 0, x_196);
x_168 = x_198;
x_169 = x_197;
goto block_179;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_195, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_195, 1);
lean_inc(x_200);
lean_dec(x_195);
x_201 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_201, 0, x_199);
x_168 = x_201;
x_169 = x_200;
goto block_179;
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_145);
x_202 = lean_ctor_get(x_191, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_191, 1);
lean_inc(x_203);
lean_dec(x_191);
x_204 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_204, 0, x_202);
x_168 = x_204;
x_169 = x_203;
goto block_179;
}
}
block_179:
{
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_170; lean_object* x_171; uint8_t x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_170 = lean_ctor_get(x_168, 0);
lean_inc(x_170);
lean_dec(x_168);
x_171 = lean_io_error_to_string(x_170);
x_172 = 3;
x_173 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set_uint8(x_173, sizeof(void*)*1, x_172);
x_174 = lean_array_get_size(x_166);
x_175 = lean_array_push(x_166, x_173);
if (lean_is_scalar(x_167)) {
 x_176 = lean_alloc_ctor(1, 2, 0);
} else {
 x_176 = x_167;
 lean_ctor_set_tag(x_176, 1);
}
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_175);
x_73 = x_176;
x_74 = x_169;
goto block_143;
}
else
{
lean_object* x_177; lean_object* x_178; 
lean_dec(x_168);
x_177 = lean_box(x_18);
if (lean_is_scalar(x_167)) {
 x_178 = lean_alloc_ctor(0, 2, 0);
} else {
 x_178 = x_167;
}
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_166);
x_73 = x_178;
x_74 = x_169;
goto block_143;
}
}
}
else
{
lean_object* x_205; uint8_t x_206; 
lean_dec(x_145);
x_205 = lean_ctor_get(x_163, 1);
lean_inc(x_205);
lean_dec(x_163);
x_206 = !lean_is_exclusive(x_164);
if (x_206 == 0)
{
x_73 = x_164;
x_74 = x_205;
goto block_143;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_164, 0);
x_208 = lean_ctor_get(x_164, 1);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_164);
x_209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
x_73 = x_209;
x_74 = x_205;
goto block_143;
}
}
}
else
{
lean_object* x_210; uint8_t x_211; 
lean_dec(x_153);
lean_dec(x_145);
lean_dec(x_60);
x_210 = lean_ctor_get(x_154, 1);
lean_inc(x_210);
lean_dec(x_154);
x_211 = !lean_is_exclusive(x_155);
if (x_211 == 0)
{
lean_object* x_212; lean_object* x_213; uint8_t x_214; lean_object* x_215; 
x_212 = lean_ctor_get(x_155, 1);
x_213 = lean_ctor_get(x_155, 0);
lean_dec(x_213);
x_214 = l_Lake_Package_fetchRelease___lambda__2___closed__23;
x_215 = lean_io_exit(x_214, x_210);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; 
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_215, 1);
lean_inc(x_217);
lean_dec(x_215);
lean_ctor_set(x_155, 0, x_216);
x_73 = x_155;
x_74 = x_217;
goto block_143;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_218 = lean_ctor_get(x_215, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_215, 1);
lean_inc(x_219);
lean_dec(x_215);
x_220 = lean_io_error_to_string(x_218);
x_221 = 3;
x_222 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_222, 0, x_220);
lean_ctor_set_uint8(x_222, sizeof(void*)*1, x_221);
x_223 = lean_array_get_size(x_212);
x_224 = lean_array_push(x_212, x_222);
lean_ctor_set_tag(x_155, 1);
lean_ctor_set(x_155, 1, x_224);
lean_ctor_set(x_155, 0, x_223);
x_73 = x_155;
x_74 = x_219;
goto block_143;
}
}
else
{
lean_object* x_225; uint8_t x_226; lean_object* x_227; 
x_225 = lean_ctor_get(x_155, 1);
lean_inc(x_225);
lean_dec(x_155);
x_226 = l_Lake_Package_fetchRelease___lambda__2___closed__23;
x_227 = lean_io_exit(x_226, x_210);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_227, 1);
lean_inc(x_229);
lean_dec(x_227);
x_230 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_230, 0, x_228);
lean_ctor_set(x_230, 1, x_225);
x_73 = x_230;
x_74 = x_229;
goto block_143;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; uint8_t x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_231 = lean_ctor_get(x_227, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_227, 1);
lean_inc(x_232);
lean_dec(x_227);
x_233 = lean_io_error_to_string(x_231);
x_234 = 3;
x_235 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_235, 0, x_233);
lean_ctor_set_uint8(x_235, sizeof(void*)*1, x_234);
x_236 = lean_array_get_size(x_225);
x_237 = lean_array_push(x_225, x_235);
x_238 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_238, 0, x_236);
lean_ctor_set(x_238, 1, x_237);
x_73 = x_238;
x_74 = x_232;
goto block_143;
}
}
}
}
else
{
lean_object* x_239; uint8_t x_240; 
lean_dec(x_153);
lean_dec(x_145);
lean_dec(x_60);
x_239 = lean_ctor_get(x_154, 1);
lean_inc(x_239);
lean_dec(x_154);
x_240 = !lean_is_exclusive(x_155);
if (x_240 == 0)
{
lean_object* x_241; uint8_t x_242; lean_object* x_243; 
x_241 = lean_ctor_get(x_155, 0);
lean_dec(x_241);
x_242 = 1;
x_243 = lean_box(x_242);
lean_ctor_set(x_155, 0, x_243);
x_73 = x_155;
x_74 = x_239;
goto block_143;
}
else
{
lean_object* x_244; uint8_t x_245; lean_object* x_246; lean_object* x_247; 
x_244 = lean_ctor_get(x_155, 1);
lean_inc(x_244);
lean_dec(x_155);
x_245 = 1;
x_246 = lean_box(x_245);
x_247 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_244);
x_73 = x_247;
x_74 = x_239;
goto block_143;
}
}
block_143:
{
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
lean_dec(x_49);
x_75 = lean_ctor_get(x_73, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_dec(x_73);
x_77 = lean_ctor_get(x_4, 8);
lean_inc(x_77);
lean_dec(x_4);
x_78 = l_System_FilePath_join(x_1, x_77);
x_79 = l_System_FilePath_pathExists(x_78, x_74);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = l_Lake_Package_fetchRelease___lambda__2___closed__17;
x_83 = lean_unbox(x_75);
lean_dec(x_75);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_80);
x_84 = l_Lake_Package_fetchRelease___lambda__2___closed__18;
x_85 = lean_string_append(x_84, x_66);
lean_dec(x_66);
x_86 = lean_string_append(x_85, x_51);
x_87 = 0;
x_88 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set_uint8(x_88, sizeof(void*)*1, x_87);
x_89 = lean_array_push(x_76, x_88);
x_90 = 1;
x_91 = l_Lake_untar(x_72, x_78, x_90, x_89, x_81);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_ctor_get(x_92, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_92, 1);
lean_inc(x_95);
lean_dec(x_92);
x_96 = lean_apply_4(x_82, x_94, x_5, x_95, x_93);
return x_96;
}
else
{
uint8_t x_97; 
lean_dec(x_5);
x_97 = !lean_is_exclusive(x_91);
if (x_97 == 0)
{
lean_object* x_98; uint8_t x_99; 
x_98 = lean_ctor_get(x_91, 0);
lean_dec(x_98);
x_99 = !lean_is_exclusive(x_92);
if (x_99 == 0)
{
return x_91;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_92, 0);
x_101 = lean_ctor_get(x_92, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_92);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
lean_ctor_set(x_91, 0, x_102);
return x_91;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_103 = lean_ctor_get(x_91, 1);
lean_inc(x_103);
lean_dec(x_91);
x_104 = lean_ctor_get(x_92, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_92, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_106 = x_92;
} else {
 lean_dec_ref(x_92);
 x_106 = lean_box(0);
}
if (lean_is_scalar(x_106)) {
 x_107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_107 = x_106;
}
lean_ctor_set(x_107, 0, x_104);
lean_ctor_set(x_107, 1, x_105);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_103);
return x_108;
}
}
}
else
{
uint8_t x_109; 
x_109 = lean_unbox(x_80);
lean_dec(x_80);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; 
x_110 = l_Lake_Package_fetchRelease___lambda__2___closed__18;
x_111 = lean_string_append(x_110, x_66);
lean_dec(x_66);
x_112 = lean_string_append(x_111, x_51);
x_113 = 0;
x_114 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set_uint8(x_114, sizeof(void*)*1, x_113);
x_115 = lean_array_push(x_76, x_114);
x_116 = 1;
x_117 = l_Lake_untar(x_72, x_78, x_116, x_115, x_81);
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
x_120 = lean_ctor_get(x_118, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_118, 1);
lean_inc(x_121);
lean_dec(x_118);
x_122 = lean_apply_4(x_82, x_120, x_5, x_121, x_119);
return x_122;
}
else
{
uint8_t x_123; 
lean_dec(x_5);
x_123 = !lean_is_exclusive(x_117);
if (x_123 == 0)
{
lean_object* x_124; uint8_t x_125; 
x_124 = lean_ctor_get(x_117, 0);
lean_dec(x_124);
x_125 = !lean_is_exclusive(x_118);
if (x_125 == 0)
{
return x_117;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_118, 0);
x_127 = lean_ctor_get(x_118, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_118);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
lean_ctor_set(x_117, 0, x_128);
return x_117;
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_129 = lean_ctor_get(x_117, 1);
lean_inc(x_129);
lean_dec(x_117);
x_130 = lean_ctor_get(x_118, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_118, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_132 = x_118;
} else {
 lean_dec_ref(x_118);
 x_132 = lean_box(0);
}
if (lean_is_scalar(x_132)) {
 x_133 = lean_alloc_ctor(1, 2, 0);
} else {
 x_133 = x_132;
}
lean_ctor_set(x_133, 0, x_130);
lean_ctor_set(x_133, 1, x_131);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_129);
return x_134;
}
}
}
else
{
lean_object* x_135; lean_object* x_136; 
lean_dec(x_78);
lean_dec(x_72);
lean_dec(x_66);
x_135 = lean_box(0);
x_136 = lean_apply_4(x_82, x_135, x_5, x_76, x_81);
return x_136;
}
}
}
else
{
uint8_t x_137; 
lean_dec(x_72);
lean_dec(x_66);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_137 = !lean_is_exclusive(x_73);
if (x_137 == 0)
{
lean_object* x_138; 
if (lean_is_scalar(x_49)) {
 x_138 = lean_alloc_ctor(0, 2, 0);
} else {
 x_138 = x_49;
}
lean_ctor_set(x_138, 0, x_73);
lean_ctor_set(x_138, 1, x_74);
return x_138;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_139 = lean_ctor_get(x_73, 0);
x_140 = lean_ctor_get(x_73, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_73);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
if (lean_is_scalar(x_49)) {
 x_142 = lean_alloc_ctor(0, 2, 0);
} else {
 x_142 = x_49;
}
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_74);
return x_142;
}
}
}
}
}
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_262 = lean_ctor_get(x_9, 0);
x_263 = lean_ctor_get(x_9, 1);
lean_inc(x_263);
lean_inc(x_262);
lean_dec(x_9);
if (lean_obj_tag(x_6) == 0)
{
if (lean_obj_tag(x_262) == 0)
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; uint8_t x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_461 = l_Lake_Package_fetchRelease___lambda__2___closed__12;
x_462 = lean_string_append(x_461, x_3);
x_463 = l_Lake_Package_fetchRelease___lambda__2___closed__13;
x_464 = lean_string_append(x_462, x_463);
x_465 = l_Lake_Package_fetchRelease___lambda__2___closed__24;
x_466 = lean_string_append(x_464, x_465);
x_467 = 3;
x_468 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_468, 0, x_466);
lean_ctor_set_uint8(x_468, sizeof(void*)*1, x_467);
x_469 = lean_array_get_size(x_2);
x_470 = lean_array_push(x_2, x_468);
x_471 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_471, 0, x_469);
lean_ctor_set(x_471, 1, x_470);
x_472 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_472, 0, x_471);
lean_ctor_set(x_472, 1, x_263);
return x_472;
}
else
{
lean_object* x_473; 
x_473 = lean_ctor_get(x_262, 0);
lean_inc(x_473);
lean_dec(x_262);
x_264 = x_473;
goto block_460;
}
}
else
{
lean_object* x_474; 
lean_dec(x_262);
x_474 = lean_ctor_get(x_6, 0);
lean_inc(x_474);
lean_dec(x_6);
x_264 = x_474;
goto block_460;
}
block_460:
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; uint8_t x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
lean_inc(x_1);
x_265 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_265, 0, x_1);
x_266 = l_Lake_Package_fetchRelease___lambda__2___closed__10;
x_267 = l_Lake_Package_fetchRelease___lambda__2___closed__11;
x_268 = l_Lake_Package_fetchRelease___lambda__2___closed__9;
x_269 = 0;
lean_inc(x_2);
x_270 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_270, 0, x_266);
lean_ctor_set(x_270, 1, x_267);
lean_ctor_set(x_270, 2, x_268);
lean_ctor_set(x_270, 3, x_265);
lean_ctor_set(x_270, 4, x_2);
lean_ctor_set_uint8(x_270, sizeof(void*)*5, x_269);
x_271 = l_Lake_captureProc_x3f(x_270, x_263);
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; uint8_t x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
lean_dec(x_264);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_273 = lean_ctor_get(x_271, 1);
lean_inc(x_273);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 x_274 = x_271;
} else {
 lean_dec_ref(x_271);
 x_274 = lean_box(0);
}
x_275 = l_Lake_Package_fetchRelease___lambda__2___closed__12;
x_276 = lean_string_append(x_275, x_3);
x_277 = l_Lake_Package_fetchRelease___lambda__2___closed__13;
x_278 = lean_string_append(x_276, x_277);
x_279 = l_Lake_Package_fetchRelease___lambda__2___closed__14;
x_280 = lean_string_append(x_278, x_279);
x_281 = 3;
x_282 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_282, 0, x_280);
lean_ctor_set_uint8(x_282, sizeof(void*)*1, x_281);
x_283 = lean_array_get_size(x_2);
x_284 = lean_array_push(x_2, x_282);
x_285 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_285, 0, x_283);
lean_ctor_set(x_285, 1, x_284);
if (lean_is_scalar(x_274)) {
 x_286 = lean_alloc_ctor(0, 2, 0);
} else {
 x_286 = x_274;
}
lean_ctor_set(x_286, 0, x_285);
lean_ctor_set(x_286, 1, x_273);
return x_286;
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; uint64_t x_306; uint64_t x_307; uint64_t x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; uint8_t x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; uint8_t x_385; 
x_287 = lean_ctor_get(x_271, 1);
lean_inc(x_287);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 x_288 = x_271;
} else {
 lean_dec_ref(x_271);
 x_288 = lean_box(0);
}
x_289 = lean_ctor_get(x_272, 0);
lean_inc(x_289);
lean_dec(x_272);
x_290 = l_Lake_Package_fetchRelease___lambda__2___closed__12;
x_291 = lean_string_append(x_290, x_264);
lean_dec(x_264);
x_292 = l_Lake_Package_fetchRelease___lambda__2___closed__15;
x_293 = lean_string_append(x_291, x_292);
x_294 = lean_string_append(x_293, x_289);
x_295 = l_Lake_Package_fetchRelease___lambda__2___closed__16;
x_296 = lean_string_append(x_294, x_295);
x_297 = lean_ctor_get(x_4, 16);
lean_inc(x_297);
x_298 = lean_string_append(x_296, x_297);
x_299 = lean_string_append(x_298, x_290);
x_300 = lean_string_append(x_290, x_3);
x_301 = lean_string_append(x_300, x_295);
x_302 = lean_string_append(x_301, x_289);
lean_dec(x_289);
x_303 = lean_string_append(x_302, x_295);
x_304 = lean_string_append(x_303, x_297);
x_305 = lean_string_append(x_304, x_290);
x_306 = lean_string_hash(x_299);
x_307 = 1723;
x_308 = lean_uint64_mix_hash(x_307, x_306);
x_309 = l_Lake_defaultLakeDir;
lean_inc(x_1);
x_310 = l_System_FilePath_join(x_1, x_309);
x_311 = l_System_FilePath_join(x_310, x_297);
x_372 = l_Lake_Package_fetchRelease___lambda__2___closed__19;
lean_inc(x_311);
x_373 = lean_string_append(x_311, x_372);
x_374 = l_Lake_Package_fetchRelease___lambda__2___closed__21;
x_375 = lean_box_uint64(x_308);
x_376 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_376, 0, x_375);
lean_ctor_set(x_376, 1, x_374);
x_377 = l_Lake_Package_fetchRelease___lambda__2___closed__22;
x_378 = lean_string_append(x_377, x_305);
x_379 = lean_string_append(x_378, x_290);
x_380 = 0;
x_381 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_381, 0, x_379);
lean_ctor_set_uint8(x_381, sizeof(void*)*1, x_380);
x_382 = l_Lake_BuildTrace_checkUpToDate___at_Lake_buildFileUnlessUpToDate___spec__1(x_311, x_376, x_373, x_5, x_2, x_287);
x_383 = lean_ctor_get(x_382, 0);
lean_inc(x_383);
x_384 = lean_ctor_get(x_383, 0);
lean_inc(x_384);
x_385 = lean_unbox(x_384);
lean_dec(x_384);
if (x_385 == 0)
{
lean_object* x_386; uint8_t x_387; 
x_386 = lean_ctor_get(x_5, 0);
lean_inc(x_386);
x_387 = lean_ctor_get_uint8(x_386, 2);
lean_dec(x_386);
if (x_387 == 0)
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; 
x_388 = lean_ctor_get(x_382, 1);
lean_inc(x_388);
lean_dec(x_382);
x_389 = lean_ctor_get(x_383, 1);
lean_inc(x_389);
lean_dec(x_383);
x_390 = lean_array_push(x_389, x_381);
lean_inc(x_311);
x_391 = l_Lake_download(x_299, x_311, x_390, x_388);
x_392 = lean_ctor_get(x_391, 0);
lean_inc(x_392);
if (lean_obj_tag(x_392) == 0)
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_408; 
x_393 = lean_ctor_get(x_391, 1);
lean_inc(x_393);
lean_dec(x_391);
x_394 = lean_ctor_get(x_392, 1);
lean_inc(x_394);
if (lean_is_exclusive(x_392)) {
 lean_ctor_release(x_392, 0);
 lean_ctor_release(x_392, 1);
 x_395 = x_392;
} else {
 lean_dec_ref(x_392);
 x_395 = lean_box(0);
}
lean_inc(x_373);
x_408 = l_System_FilePath_parent(x_373);
if (lean_obj_tag(x_408) == 0)
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; 
x_409 = lean_uint64_to_nat(x_308);
x_410 = l___private_Init_Data_Repr_0__Nat_reprFast(x_409);
x_411 = l_IO_FS_writeFile(x_373, x_410, x_393);
lean_dec(x_410);
lean_dec(x_373);
if (lean_obj_tag(x_411) == 0)
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; 
x_412 = lean_ctor_get(x_411, 0);
lean_inc(x_412);
x_413 = lean_ctor_get(x_411, 1);
lean_inc(x_413);
lean_dec(x_411);
x_414 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_414, 0, x_412);
x_396 = x_414;
x_397 = x_413;
goto block_407;
}
else
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; 
x_415 = lean_ctor_get(x_411, 0);
lean_inc(x_415);
x_416 = lean_ctor_get(x_411, 1);
lean_inc(x_416);
lean_dec(x_411);
x_417 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_417, 0, x_415);
x_396 = x_417;
x_397 = x_416;
goto block_407;
}
}
else
{
lean_object* x_418; lean_object* x_419; 
x_418 = lean_ctor_get(x_408, 0);
lean_inc(x_418);
lean_dec(x_408);
x_419 = l_IO_FS_createDirAll(x_418, x_393);
if (lean_obj_tag(x_419) == 0)
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; 
x_420 = lean_ctor_get(x_419, 1);
lean_inc(x_420);
lean_dec(x_419);
x_421 = lean_uint64_to_nat(x_308);
x_422 = l___private_Init_Data_Repr_0__Nat_reprFast(x_421);
x_423 = l_IO_FS_writeFile(x_373, x_422, x_420);
lean_dec(x_422);
lean_dec(x_373);
if (lean_obj_tag(x_423) == 0)
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; 
x_424 = lean_ctor_get(x_423, 0);
lean_inc(x_424);
x_425 = lean_ctor_get(x_423, 1);
lean_inc(x_425);
lean_dec(x_423);
x_426 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_426, 0, x_424);
x_396 = x_426;
x_397 = x_425;
goto block_407;
}
else
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; 
x_427 = lean_ctor_get(x_423, 0);
lean_inc(x_427);
x_428 = lean_ctor_get(x_423, 1);
lean_inc(x_428);
lean_dec(x_423);
x_429 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_429, 0, x_427);
x_396 = x_429;
x_397 = x_428;
goto block_407;
}
}
else
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; 
lean_dec(x_373);
x_430 = lean_ctor_get(x_419, 0);
lean_inc(x_430);
x_431 = lean_ctor_get(x_419, 1);
lean_inc(x_431);
lean_dec(x_419);
x_432 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_432, 0, x_430);
x_396 = x_432;
x_397 = x_431;
goto block_407;
}
}
block_407:
{
if (lean_obj_tag(x_396) == 0)
{
lean_object* x_398; lean_object* x_399; uint8_t x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; 
x_398 = lean_ctor_get(x_396, 0);
lean_inc(x_398);
lean_dec(x_396);
x_399 = lean_io_error_to_string(x_398);
x_400 = 3;
x_401 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_401, 0, x_399);
lean_ctor_set_uint8(x_401, sizeof(void*)*1, x_400);
x_402 = lean_array_get_size(x_394);
x_403 = lean_array_push(x_394, x_401);
if (lean_is_scalar(x_395)) {
 x_404 = lean_alloc_ctor(1, 2, 0);
} else {
 x_404 = x_395;
 lean_ctor_set_tag(x_404, 1);
}
lean_ctor_set(x_404, 0, x_402);
lean_ctor_set(x_404, 1, x_403);
x_312 = x_404;
x_313 = x_397;
goto block_371;
}
else
{
lean_object* x_405; lean_object* x_406; 
lean_dec(x_396);
x_405 = lean_box(x_269);
if (lean_is_scalar(x_395)) {
 x_406 = lean_alloc_ctor(0, 2, 0);
} else {
 x_406 = x_395;
}
lean_ctor_set(x_406, 0, x_405);
lean_ctor_set(x_406, 1, x_394);
x_312 = x_406;
x_313 = x_397;
goto block_371;
}
}
}
else
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; 
lean_dec(x_373);
x_433 = lean_ctor_get(x_391, 1);
lean_inc(x_433);
lean_dec(x_391);
x_434 = lean_ctor_get(x_392, 0);
lean_inc(x_434);
x_435 = lean_ctor_get(x_392, 1);
lean_inc(x_435);
if (lean_is_exclusive(x_392)) {
 lean_ctor_release(x_392, 0);
 lean_ctor_release(x_392, 1);
 x_436 = x_392;
} else {
 lean_dec_ref(x_392);
 x_436 = lean_box(0);
}
if (lean_is_scalar(x_436)) {
 x_437 = lean_alloc_ctor(1, 2, 0);
} else {
 x_437 = x_436;
}
lean_ctor_set(x_437, 0, x_434);
lean_ctor_set(x_437, 1, x_435);
x_312 = x_437;
x_313 = x_433;
goto block_371;
}
}
else
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; uint8_t x_441; lean_object* x_442; 
lean_dec(x_381);
lean_dec(x_373);
lean_dec(x_299);
x_438 = lean_ctor_get(x_382, 1);
lean_inc(x_438);
lean_dec(x_382);
x_439 = lean_ctor_get(x_383, 1);
lean_inc(x_439);
if (lean_is_exclusive(x_383)) {
 lean_ctor_release(x_383, 0);
 lean_ctor_release(x_383, 1);
 x_440 = x_383;
} else {
 lean_dec_ref(x_383);
 x_440 = lean_box(0);
}
x_441 = l_Lake_Package_fetchRelease___lambda__2___closed__23;
x_442 = lean_io_exit(x_441, x_438);
if (lean_obj_tag(x_442) == 0)
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; 
x_443 = lean_ctor_get(x_442, 0);
lean_inc(x_443);
x_444 = lean_ctor_get(x_442, 1);
lean_inc(x_444);
lean_dec(x_442);
if (lean_is_scalar(x_440)) {
 x_445 = lean_alloc_ctor(0, 2, 0);
} else {
 x_445 = x_440;
}
lean_ctor_set(x_445, 0, x_443);
lean_ctor_set(x_445, 1, x_439);
x_312 = x_445;
x_313 = x_444;
goto block_371;
}
else
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; uint8_t x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; 
x_446 = lean_ctor_get(x_442, 0);
lean_inc(x_446);
x_447 = lean_ctor_get(x_442, 1);
lean_inc(x_447);
lean_dec(x_442);
x_448 = lean_io_error_to_string(x_446);
x_449 = 3;
x_450 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_450, 0, x_448);
lean_ctor_set_uint8(x_450, sizeof(void*)*1, x_449);
x_451 = lean_array_get_size(x_439);
x_452 = lean_array_push(x_439, x_450);
if (lean_is_scalar(x_440)) {
 x_453 = lean_alloc_ctor(1, 2, 0);
} else {
 x_453 = x_440;
 lean_ctor_set_tag(x_453, 1);
}
lean_ctor_set(x_453, 0, x_451);
lean_ctor_set(x_453, 1, x_452);
x_312 = x_453;
x_313 = x_447;
goto block_371;
}
}
}
else
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; uint8_t x_457; lean_object* x_458; lean_object* x_459; 
lean_dec(x_381);
lean_dec(x_373);
lean_dec(x_299);
x_454 = lean_ctor_get(x_382, 1);
lean_inc(x_454);
lean_dec(x_382);
x_455 = lean_ctor_get(x_383, 1);
lean_inc(x_455);
if (lean_is_exclusive(x_383)) {
 lean_ctor_release(x_383, 0);
 lean_ctor_release(x_383, 1);
 x_456 = x_383;
} else {
 lean_dec_ref(x_383);
 x_456 = lean_box(0);
}
x_457 = 1;
x_458 = lean_box(x_457);
if (lean_is_scalar(x_456)) {
 x_459 = lean_alloc_ctor(0, 2, 0);
} else {
 x_459 = x_456;
}
lean_ctor_set(x_459, 0, x_458);
lean_ctor_set(x_459, 1, x_455);
x_312 = x_459;
x_313 = x_454;
goto block_371;
}
block_371:
{
if (lean_obj_tag(x_312) == 0)
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; uint8_t x_322; 
lean_dec(x_288);
x_314 = lean_ctor_get(x_312, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_312, 1);
lean_inc(x_315);
lean_dec(x_312);
x_316 = lean_ctor_get(x_4, 8);
lean_inc(x_316);
lean_dec(x_4);
x_317 = l_System_FilePath_join(x_1, x_316);
x_318 = l_System_FilePath_pathExists(x_317, x_313);
x_319 = lean_ctor_get(x_318, 0);
lean_inc(x_319);
x_320 = lean_ctor_get(x_318, 1);
lean_inc(x_320);
lean_dec(x_318);
x_321 = l_Lake_Package_fetchRelease___lambda__2___closed__17;
x_322 = lean_unbox(x_314);
lean_dec(x_314);
if (x_322 == 0)
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; uint8_t x_326; lean_object* x_327; lean_object* x_328; uint8_t x_329; lean_object* x_330; lean_object* x_331; 
lean_dec(x_319);
x_323 = l_Lake_Package_fetchRelease___lambda__2___closed__18;
x_324 = lean_string_append(x_323, x_305);
lean_dec(x_305);
x_325 = lean_string_append(x_324, x_290);
x_326 = 0;
x_327 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_327, 0, x_325);
lean_ctor_set_uint8(x_327, sizeof(void*)*1, x_326);
x_328 = lean_array_push(x_315, x_327);
x_329 = 1;
x_330 = l_Lake_untar(x_311, x_317, x_329, x_328, x_320);
x_331 = lean_ctor_get(x_330, 0);
lean_inc(x_331);
if (lean_obj_tag(x_331) == 0)
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_332 = lean_ctor_get(x_330, 1);
lean_inc(x_332);
lean_dec(x_330);
x_333 = lean_ctor_get(x_331, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_331, 1);
lean_inc(x_334);
lean_dec(x_331);
x_335 = lean_apply_4(x_321, x_333, x_5, x_334, x_332);
return x_335;
}
else
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; 
lean_dec(x_5);
x_336 = lean_ctor_get(x_330, 1);
lean_inc(x_336);
if (lean_is_exclusive(x_330)) {
 lean_ctor_release(x_330, 0);
 lean_ctor_release(x_330, 1);
 x_337 = x_330;
} else {
 lean_dec_ref(x_330);
 x_337 = lean_box(0);
}
x_338 = lean_ctor_get(x_331, 0);
lean_inc(x_338);
x_339 = lean_ctor_get(x_331, 1);
lean_inc(x_339);
if (lean_is_exclusive(x_331)) {
 lean_ctor_release(x_331, 0);
 lean_ctor_release(x_331, 1);
 x_340 = x_331;
} else {
 lean_dec_ref(x_331);
 x_340 = lean_box(0);
}
if (lean_is_scalar(x_340)) {
 x_341 = lean_alloc_ctor(1, 2, 0);
} else {
 x_341 = x_340;
}
lean_ctor_set(x_341, 0, x_338);
lean_ctor_set(x_341, 1, x_339);
if (lean_is_scalar(x_337)) {
 x_342 = lean_alloc_ctor(0, 2, 0);
} else {
 x_342 = x_337;
}
lean_ctor_set(x_342, 0, x_341);
lean_ctor_set(x_342, 1, x_336);
return x_342;
}
}
else
{
uint8_t x_343; 
x_343 = lean_unbox(x_319);
lean_dec(x_319);
if (x_343 == 0)
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; uint8_t x_347; lean_object* x_348; lean_object* x_349; uint8_t x_350; lean_object* x_351; lean_object* x_352; 
x_344 = l_Lake_Package_fetchRelease___lambda__2___closed__18;
x_345 = lean_string_append(x_344, x_305);
lean_dec(x_305);
x_346 = lean_string_append(x_345, x_290);
x_347 = 0;
x_348 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_348, 0, x_346);
lean_ctor_set_uint8(x_348, sizeof(void*)*1, x_347);
x_349 = lean_array_push(x_315, x_348);
x_350 = 1;
x_351 = l_Lake_untar(x_311, x_317, x_350, x_349, x_320);
x_352 = lean_ctor_get(x_351, 0);
lean_inc(x_352);
if (lean_obj_tag(x_352) == 0)
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; 
x_353 = lean_ctor_get(x_351, 1);
lean_inc(x_353);
lean_dec(x_351);
x_354 = lean_ctor_get(x_352, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_352, 1);
lean_inc(x_355);
lean_dec(x_352);
x_356 = lean_apply_4(x_321, x_354, x_5, x_355, x_353);
return x_356;
}
else
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; 
lean_dec(x_5);
x_357 = lean_ctor_get(x_351, 1);
lean_inc(x_357);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 lean_ctor_release(x_351, 1);
 x_358 = x_351;
} else {
 lean_dec_ref(x_351);
 x_358 = lean_box(0);
}
x_359 = lean_ctor_get(x_352, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_352, 1);
lean_inc(x_360);
if (lean_is_exclusive(x_352)) {
 lean_ctor_release(x_352, 0);
 lean_ctor_release(x_352, 1);
 x_361 = x_352;
} else {
 lean_dec_ref(x_352);
 x_361 = lean_box(0);
}
if (lean_is_scalar(x_361)) {
 x_362 = lean_alloc_ctor(1, 2, 0);
} else {
 x_362 = x_361;
}
lean_ctor_set(x_362, 0, x_359);
lean_ctor_set(x_362, 1, x_360);
if (lean_is_scalar(x_358)) {
 x_363 = lean_alloc_ctor(0, 2, 0);
} else {
 x_363 = x_358;
}
lean_ctor_set(x_363, 0, x_362);
lean_ctor_set(x_363, 1, x_357);
return x_363;
}
}
else
{
lean_object* x_364; lean_object* x_365; 
lean_dec(x_317);
lean_dec(x_311);
lean_dec(x_305);
x_364 = lean_box(0);
x_365 = lean_apply_4(x_321, x_364, x_5, x_315, x_320);
return x_365;
}
}
}
else
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; 
lean_dec(x_311);
lean_dec(x_305);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_366 = lean_ctor_get(x_312, 0);
lean_inc(x_366);
x_367 = lean_ctor_get(x_312, 1);
lean_inc(x_367);
if (lean_is_exclusive(x_312)) {
 lean_ctor_release(x_312, 0);
 lean_ctor_release(x_312, 1);
 x_368 = x_312;
} else {
 lean_dec_ref(x_312);
 x_368 = lean_box(0);
}
if (lean_is_scalar(x_368)) {
 x_369 = lean_alloc_ctor(1, 2, 0);
} else {
 x_369 = x_368;
}
lean_ctor_set(x_369, 0, x_366);
lean_ctor_set(x_369, 1, x_367);
if (lean_is_scalar(x_288)) {
 x_370 = lean_alloc_ctor(0, 2, 0);
} else {
 x_370 = x_288;
}
lean_ctor_set(x_370, 0, x_369);
lean_ctor_set(x_370, 1, x_313);
return x_370;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_fetchRelease___lambda__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 1);
lean_dec(x_4);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_1);
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_2, 1);
lean_dec(x_8);
x_9 = lean_ctor_get(x_2, 0);
lean_dec(x_9);
x_10 = lean_unsigned_to_nat(0u);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 0, x_10);
return x_2;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_1);
return x_12;
}
}
}
}
static lean_object* _init_l_Lake_Package_fetchRelease___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Fetching ", 9);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_fetchRelease___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" cloud release", 14);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_fetchRelease___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_closure((void*)(l_Function_const___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_fetchRelease___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Package_fetchRelease___closed__3;
x_2 = lean_alloc_closure((void*)(l_Lake_EResult_map___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_fetchRelease(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 5);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_5, 2);
lean_inc(x_7);
x_8 = 1;
x_9 = l_Lean_Name_toString(x_7, x_8);
x_10 = l_Lake_Package_fetchRelease___closed__1;
x_11 = lean_string_append(x_10, x_9);
x_12 = l_Lake_Package_fetchRelease___closed__2;
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_ctor_get(x_5, 14);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_5, 13);
lean_inc(x_53);
if (lean_obj_tag(x_53) == 0)
{
x_15 = x_6;
goto block_52;
}
else
{
uint8_t x_54; 
lean_dec(x_6);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
x_15 = x_53;
goto block_52;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_15 = x_56;
goto block_52;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_6);
x_57 = !lean_is_exclusive(x_14);
if (x_57 == 0)
{
x_15 = x_14;
goto block_52;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_14, 0);
lean_inc(x_58);
lean_dec(x_14);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_15 = x_59;
goto block_52;
}
}
block_52:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = l_Lake_Package_recComputeDeps___closed__1;
lean_inc(x_2);
x_17 = lean_alloc_closure((void*)(l_Lake_Package_fetchRelease___lambda__2___boxed), 7, 6);
lean_closure_set(x_17, 0, x_4);
lean_closure_set(x_17, 1, x_16);
lean_closure_set(x_17, 2, x_9);
lean_closure_set(x_17, 3, x_5);
lean_closure_set(x_17, 4, x_2);
lean_closure_set(x_17, 5, x_15);
x_18 = l_Task_Priority_default;
x_19 = lean_io_as_task(x_17, x_18, x_3);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_2, 3);
lean_inc(x_22);
lean_dec(x_2);
x_23 = lean_st_ref_take(x_22, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lake_Package_fetchRelease___closed__4;
x_27 = 0;
lean_inc(x_20);
x_28 = lean_task_map(x_26, x_20, x_18, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_13);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_array_push(x_24, x_29);
x_31 = lean_st_ref_set(x_22, x_30, x_25);
lean_dec(x_22);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
x_34 = lean_alloc_closure((void*)(l_Lake_Package_fetchRelease___lambda__3), 2, 1);
lean_closure_set(x_34, 0, x_16);
x_35 = lean_task_map(x_34, x_20, x_18, x_8);
lean_ctor_set(x_31, 0, x_35);
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
x_37 = lean_alloc_closure((void*)(l_Lake_Package_fetchRelease___lambda__3), 2, 1);
lean_closure_set(x_37, 0, x_16);
x_38 = lean_task_map(x_37, x_20, x_18, x_8);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_20);
x_40 = !lean_is_exclusive(x_31);
if (x_40 == 0)
{
return x_31;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_31, 0);
x_42 = lean_ctor_get(x_31, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_31);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_13);
x_44 = !lean_is_exclusive(x_23);
if (x_44 == 0)
{
return x_23;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_23, 0);
x_46 = lean_ctor_get(x_23, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_23);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_13);
lean_dec(x_2);
x_48 = !lean_is_exclusive(x_19);
if (x_48 == 0)
{
return x_19;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_19, 0);
x_50 = lean_ctor_get(x_19, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_19);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_fetchRelease___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_Package_fetchRelease___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_fetchRelease___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_Package_fetchRelease___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_releaseFacetConfig___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lake_Package_fetchRelease(x_1, x_5, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
lean_ctor_set(x_8, 0, x_12);
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_8);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_4);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_6);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
}
}
static lean_object* _init_l_Lake_Package_releaseFacetConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Package_releaseFacetConfig___elambda__1___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_releaseFacetConfig___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_releaseFacetConfig___closed__1;
x_2 = l_Lake_Package_extraDepFacetConfig___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_releaseFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Package_releaseFacetConfig___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_releaseFacetConfig___elambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_Package_releaseFacetConfig___elambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterReleaseAsync___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Array_append___rarg(x_1, x_4);
lean_ctor_set(x_2, 1, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_8 = l_Array_append___rarg(x_1, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
x_13 = lean_array_get_size(x_1);
x_14 = lean_nat_add(x_13, x_11);
lean_dec(x_11);
lean_dec(x_13);
x_15 = l_Array_append___rarg(x_1, x_12);
lean_ctor_set(x_2, 1, x_15);
lean_ctor_set(x_2, 0, x_14);
return x_2;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_2, 0);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_2);
x_18 = lean_array_get_size(x_1);
x_19 = lean_nat_add(x_18, x_16);
lean_dec(x_16);
lean_dec(x_18);
x_20 = l_Array_append___rarg(x_1, x_17);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterReleaseAsync___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_apply_2(x_1, x_2, x_4);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = l_Array_isEmpty___rarg(x_5);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_alloc_closure((void*)(l_Lake_Package_afterReleaseAsync___rarg___lambda__1), 2, 1);
lean_closure_set(x_10, 0, x_5);
x_11 = l_Task_Priority_default;
x_12 = 1;
x_13 = lean_task_map(x_10, x_8, x_11, x_12);
lean_ctor_set(x_6, 0, x_13);
return x_6;
}
else
{
lean_dec(x_5);
return x_6;
}
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_6);
x_16 = l_Array_isEmpty___rarg(x_5);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_alloc_closure((void*)(l_Lake_Package_afterReleaseAsync___rarg___lambda__1), 2, 1);
lean_closure_set(x_17, 0, x_5);
x_18 = l_Task_Priority_default;
x_19 = 1;
x_20 = lean_task_map(x_17, x_14, x_18, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_15);
return x_21;
}
else
{
lean_object* x_22; 
lean_dec(x_5);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_15);
return x_22;
}
}
}
else
{
uint8_t x_23; 
lean_dec(x_5);
x_23 = !lean_is_exclusive(x_6);
if (x_23 == 0)
{
return x_6;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_6, 0);
x_25 = lean_ctor_get(x_6, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_6);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_3);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_task_pure(x_3);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_4);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_3, 0);
x_31 = lean_ctor_get(x_3, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_3);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_task_pure(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_4);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterReleaseAsync___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
x_10 = lean_ctor_get_uint8(x_9, sizeof(void*)*17 + 1);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_11 = lean_apply_2(x_2, x_6, x_8);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_7);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_5);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_7);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; 
x_21 = lean_ctor_get(x_6, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_ctor_get(x_9, 2);
lean_inc(x_23);
lean_dec(x_9);
x_24 = lean_ctor_get(x_22, 2);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_24, 2);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_name_eq(x_23, x_25);
lean_dec(x_25);
lean_dec(x_23);
x_27 = l_instDecidableNot___rarg(x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_28 = lean_apply_2(x_2, x_6, x_8);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_5);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_7);
lean_ctor_set(x_28, 0, x_32);
return x_28;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_28, 0);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_28);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_5);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_7);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = l_Lake_Package_recBuildExtraDepTargets___closed__5;
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_1);
lean_ctor_set(x_39, 1, x_38);
lean_inc(x_6);
x_40 = lean_apply_6(x_3, x_39, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = !lean_is_exclusive(x_41);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_41, 0);
lean_dec(x_45);
x_46 = !lean_is_exclusive(x_42);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; uint8_t x_52; 
x_47 = lean_ctor_get(x_42, 0);
x_48 = lean_alloc_closure((void*)(l_Lake_Package_afterReleaseAsync___rarg___lambda__2), 4, 2);
lean_closure_set(x_48, 0, x_2);
lean_closure_set(x_48, 1, x_6);
x_49 = l_Task_Priority_default;
x_50 = 0;
x_51 = lean_io_bind_task(x_47, x_48, x_49, x_50, x_43);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_51, 0);
lean_ctor_set(x_42, 0, x_53);
lean_ctor_set(x_51, 0, x_41);
return x_51;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_51, 0);
x_55 = lean_ctor_get(x_51, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_51);
lean_ctor_set(x_42, 0, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_41);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_57 = lean_ctor_get(x_42, 0);
x_58 = lean_ctor_get(x_42, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_42);
x_59 = lean_alloc_closure((void*)(l_Lake_Package_afterReleaseAsync___rarg___lambda__2), 4, 2);
lean_closure_set(x_59, 0, x_2);
lean_closure_set(x_59, 1, x_6);
x_60 = l_Task_Priority_default;
x_61 = 0;
x_62 = lean_io_bind_task(x_57, x_59, x_60, x_61, x_43);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_65 = x_62;
} else {
 lean_dec_ref(x_62);
 x_65 = lean_box(0);
}
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_58);
lean_ctor_set(x_41, 0, x_66);
if (lean_is_scalar(x_65)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_65;
}
lean_ctor_set(x_67, 0, x_41);
lean_ctor_set(x_67, 1, x_64);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_68 = lean_ctor_get(x_41, 1);
lean_inc(x_68);
lean_dec(x_41);
x_69 = lean_ctor_get(x_42, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_42, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_71 = x_42;
} else {
 lean_dec_ref(x_42);
 x_71 = lean_box(0);
}
x_72 = lean_alloc_closure((void*)(l_Lake_Package_afterReleaseAsync___rarg___lambda__2), 4, 2);
lean_closure_set(x_72, 0, x_2);
lean_closure_set(x_72, 1, x_6);
x_73 = l_Task_Priority_default;
x_74 = 0;
x_75 = lean_io_bind_task(x_69, x_72, x_73, x_74, x_43);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_78 = x_75;
} else {
 lean_dec_ref(x_75);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_71;
}
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_70);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_68);
if (lean_is_scalar(x_78)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_78;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_77);
return x_81;
}
}
else
{
uint8_t x_82; 
lean_dec(x_6);
lean_dec(x_2);
x_82 = !lean_is_exclusive(x_40);
if (x_82 == 0)
{
lean_object* x_83; uint8_t x_84; 
x_83 = lean_ctor_get(x_40, 0);
lean_dec(x_83);
x_84 = !lean_is_exclusive(x_41);
if (x_84 == 0)
{
return x_40;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_41, 0);
x_86 = lean_ctor_get(x_41, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_41);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
lean_ctor_set(x_40, 0, x_87);
return x_40;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_88 = lean_ctor_get(x_40, 1);
lean_inc(x_88);
lean_dec(x_40);
x_89 = lean_ctor_get(x_41, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_41, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_91 = x_41;
} else {
 lean_dec_ref(x_41);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(1, 2, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_90);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_88);
return x_93;
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_6);
lean_dec(x_2);
x_94 = !lean_is_exclusive(x_40);
if (x_94 == 0)
{
return x_40;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_40, 0);
x_96 = lean_ctor_get(x_40, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_40);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterReleaseAsync(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_Package_afterReleaseAsync___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterReleaseSync___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_apply_3(x_1, x_2, x_5, x_4);
return x_6;
}
else
{
uint8_t x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_4);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterReleaseSync___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
x_10 = lean_ctor_get_uint8(x_9, sizeof(void*)*17 + 1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_11 = l_Lake_Package_recComputeDeps___closed__1;
x_12 = lean_apply_2(x_2, x_6, x_11);
x_13 = l_Task_Priority_default;
x_14 = lean_io_as_task(x_12, x_13, x_8);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_5);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_7);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_14);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_5);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_7);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_30; 
x_24 = lean_ctor_get(x_6, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_ctor_get(x_9, 2);
lean_inc(x_26);
lean_dec(x_9);
x_27 = lean_ctor_get(x_25, 2);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_27, 2);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_name_eq(x_26, x_28);
lean_dec(x_28);
lean_dec(x_26);
x_30 = l_instDecidableNot___rarg(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_31 = l_Lake_Package_recComputeDeps___closed__1;
x_32 = lean_apply_2(x_2, x_6, x_31);
x_33 = l_Task_Priority_default;
x_34 = lean_io_as_task(x_32, x_33, x_8);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_5);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_7);
lean_ctor_set(x_34, 0, x_38);
return x_34;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_34, 0);
x_40 = lean_ctor_get(x_34, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_34);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_5);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_7);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_40);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = l_Lake_Package_recBuildExtraDepTargets___closed__5;
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_1);
lean_ctor_set(x_45, 1, x_44);
lean_inc(x_6);
x_46 = lean_apply_6(x_3, x_45, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
x_50 = !lean_is_exclusive(x_47);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_47, 0);
lean_dec(x_51);
x_52 = !lean_is_exclusive(x_48);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; uint8_t x_58; 
x_53 = lean_ctor_get(x_48, 0);
x_54 = lean_alloc_closure((void*)(l_Lake_Package_afterReleaseSync___rarg___lambda__1), 4, 2);
lean_closure_set(x_54, 0, x_2);
lean_closure_set(x_54, 1, x_6);
x_55 = l_Task_Priority_default;
x_56 = 0;
x_57 = lean_io_map_task(x_54, x_53, x_55, x_56, x_49);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_57, 0);
lean_ctor_set(x_48, 0, x_59);
lean_ctor_set(x_57, 0, x_47);
return x_57;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_57, 0);
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_57);
lean_ctor_set(x_48, 0, x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_47);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_63 = lean_ctor_get(x_48, 0);
x_64 = lean_ctor_get(x_48, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_48);
x_65 = lean_alloc_closure((void*)(l_Lake_Package_afterReleaseSync___rarg___lambda__1), 4, 2);
lean_closure_set(x_65, 0, x_2);
lean_closure_set(x_65, 1, x_6);
x_66 = l_Task_Priority_default;
x_67 = 0;
x_68 = lean_io_map_task(x_65, x_63, x_66, x_67, x_49);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_71 = x_68;
} else {
 lean_dec_ref(x_68);
 x_71 = lean_box(0);
}
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_64);
lean_ctor_set(x_47, 0, x_72);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_47);
lean_ctor_set(x_73, 1, x_70);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_74 = lean_ctor_get(x_47, 1);
lean_inc(x_74);
lean_dec(x_47);
x_75 = lean_ctor_get(x_48, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_48, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_77 = x_48;
} else {
 lean_dec_ref(x_48);
 x_77 = lean_box(0);
}
x_78 = lean_alloc_closure((void*)(l_Lake_Package_afterReleaseSync___rarg___lambda__1), 4, 2);
lean_closure_set(x_78, 0, x_2);
lean_closure_set(x_78, 1, x_6);
x_79 = l_Task_Priority_default;
x_80 = 0;
x_81 = lean_io_map_task(x_78, x_75, x_79, x_80, x_49);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_84 = x_81;
} else {
 lean_dec_ref(x_81);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_77;
}
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_76);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_74);
if (lean_is_scalar(x_84)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_84;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_83);
return x_87;
}
}
else
{
uint8_t x_88; 
lean_dec(x_6);
lean_dec(x_2);
x_88 = !lean_is_exclusive(x_46);
if (x_88 == 0)
{
lean_object* x_89; uint8_t x_90; 
x_89 = lean_ctor_get(x_46, 0);
lean_dec(x_89);
x_90 = !lean_is_exclusive(x_47);
if (x_90 == 0)
{
return x_46;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_47, 0);
x_92 = lean_ctor_get(x_47, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_47);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
lean_ctor_set(x_46, 0, x_93);
return x_46;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_94 = lean_ctor_get(x_46, 1);
lean_inc(x_94);
lean_dec(x_46);
x_95 = lean_ctor_get(x_47, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_47, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_97 = x_47;
} else {
 lean_dec_ref(x_47);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(1, 2, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_96);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_94);
return x_99;
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_6);
lean_dec(x_2);
x_100 = !lean_is_exclusive(x_46);
if (x_100 == 0)
{
return x_46;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_46, 0);
x_102 = lean_ctor_get(x_46, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_46);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterReleaseSync(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_Package_afterReleaseSync___rarg), 8, 0);
return x_2;
}
}
static lean_object* _init_l_Lake_initPackageFacetConfigs___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__11___closed__2;
x_3 = l_Lake_Package_depsFacetConfig;
x_4 = l_Lean_RBNode_insert___at_Lake_Workspace_addPackageFacetConfig___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_initPackageFacetConfigs___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_initPackageFacetConfigs___closed__1;
x_2 = l_Array_forInUnsafe_loop___at_Lake_Package_recBuildExtraDepTargets___spec__1___closed__2;
x_3 = l_Lake_Package_extraDepFacetConfig;
x_4 = l_Lean_RBNode_insert___at_Lake_Workspace_addPackageFacetConfig___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_initPackageFacetConfigs___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_initPackageFacetConfigs___closed__2;
x_2 = l_Lake_Package_recBuildExtraDepTargets___closed__5;
x_3 = l_Lake_Package_releaseFacetConfig;
x_4 = l_Lean_RBNode_insert___at_Lake_Workspace_addPackageFacetConfig___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_initPackageFacetConfigs() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_initPackageFacetConfigs___closed__3;
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Git(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Sugar(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Common(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Targets(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Package(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Git(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Sugar(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Common(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Targets(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeDeps___spec__1___closed__1 = _init_l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeDeps___spec__1___closed__1();
lean_mark_persistent(l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeDeps___spec__1___closed__1);
l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeDeps___spec__1___closed__2 = _init_l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeDeps___spec__1___closed__2();
lean_mark_persistent(l_Lake_OrdHashSet_insert___at_Lake_Package_recComputeDeps___spec__1___closed__2);
l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__11___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__11___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__11___closed__1);
l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__11___closed__2 = _init_l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__11___closed__2();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_Package_recComputeDeps___spec__11___closed__2);
l_Lake_Package_recComputeDeps___closed__1 = _init_l_Lake_Package_recComputeDeps___closed__1();
lean_mark_persistent(l_Lake_Package_recComputeDeps___closed__1);
l_Lake_Package_depsFacetConfig___closed__1 = _init_l_Lake_Package_depsFacetConfig___closed__1();
lean_mark_persistent(l_Lake_Package_depsFacetConfig___closed__1);
l_Lake_Package_depsFacetConfig___closed__2 = _init_l_Lake_Package_depsFacetConfig___closed__2();
lean_mark_persistent(l_Lake_Package_depsFacetConfig___closed__2);
l_Lake_Package_depsFacetConfig = _init_l_Lake_Package_depsFacetConfig();
lean_mark_persistent(l_Lake_Package_depsFacetConfig);
l_Array_forInUnsafe_loop___at_Lake_Package_recBuildExtraDepTargets___spec__1___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lake_Package_recBuildExtraDepTargets___spec__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lake_Package_recBuildExtraDepTargets___spec__1___closed__1);
l_Array_forInUnsafe_loop___at_Lake_Package_recBuildExtraDepTargets___spec__1___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lake_Package_recBuildExtraDepTargets___spec__1___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lake_Package_recBuildExtraDepTargets___spec__1___closed__2);
l_Lake_Package_recBuildExtraDepTargets___lambda__2___closed__1 = _init_l_Lake_Package_recBuildExtraDepTargets___lambda__2___closed__1();
lean_mark_persistent(l_Lake_Package_recBuildExtraDepTargets___lambda__2___closed__1);
l_Lake_Package_recBuildExtraDepTargets___lambda__4___closed__1 = _init_l_Lake_Package_recBuildExtraDepTargets___lambda__4___closed__1();
lean_mark_persistent(l_Lake_Package_recBuildExtraDepTargets___lambda__4___closed__1);
l_Lake_Package_recBuildExtraDepTargets___lambda__4___closed__2 = _init_l_Lake_Package_recBuildExtraDepTargets___lambda__4___closed__2();
lean_mark_persistent(l_Lake_Package_recBuildExtraDepTargets___lambda__4___closed__2);
l_Lake_Package_recBuildExtraDepTargets___closed__1 = _init_l_Lake_Package_recBuildExtraDepTargets___closed__1();
lean_mark_persistent(l_Lake_Package_recBuildExtraDepTargets___closed__1);
l_Lake_Package_recBuildExtraDepTargets___closed__2 = _init_l_Lake_Package_recBuildExtraDepTargets___closed__2();
lean_mark_persistent(l_Lake_Package_recBuildExtraDepTargets___closed__2);
l_Lake_Package_recBuildExtraDepTargets___closed__3 = _init_l_Lake_Package_recBuildExtraDepTargets___closed__3();
lean_mark_persistent(l_Lake_Package_recBuildExtraDepTargets___closed__3);
l_Lake_Package_recBuildExtraDepTargets___closed__4 = _init_l_Lake_Package_recBuildExtraDepTargets___closed__4();
lean_mark_persistent(l_Lake_Package_recBuildExtraDepTargets___closed__4);
l_Lake_Package_recBuildExtraDepTargets___closed__5 = _init_l_Lake_Package_recBuildExtraDepTargets___closed__5();
lean_mark_persistent(l_Lake_Package_recBuildExtraDepTargets___closed__5);
l_Lake_Package_recBuildExtraDepTargets___closed__6 = _init_l_Lake_Package_recBuildExtraDepTargets___closed__6();
lean_mark_persistent(l_Lake_Package_recBuildExtraDepTargets___closed__6);
l_Functor_discard___at_Lake_Package_extraDepFacetConfig___spec__1___closed__1 = _init_l_Functor_discard___at_Lake_Package_extraDepFacetConfig___spec__1___closed__1();
lean_mark_persistent(l_Functor_discard___at_Lake_Package_extraDepFacetConfig___spec__1___closed__1);
l_Functor_discard___at_Lake_Package_extraDepFacetConfig___spec__1___closed__2 = _init_l_Functor_discard___at_Lake_Package_extraDepFacetConfig___spec__1___closed__2();
lean_mark_persistent(l_Functor_discard___at_Lake_Package_extraDepFacetConfig___spec__1___closed__2);
l_Lake_Package_extraDepFacetConfig___closed__1 = _init_l_Lake_Package_extraDepFacetConfig___closed__1();
lean_mark_persistent(l_Lake_Package_extraDepFacetConfig___closed__1);
l_Lake_Package_extraDepFacetConfig___closed__2 = _init_l_Lake_Package_extraDepFacetConfig___closed__2();
lean_mark_persistent(l_Lake_Package_extraDepFacetConfig___closed__2);
l_Lake_Package_extraDepFacetConfig___closed__3 = _init_l_Lake_Package_extraDepFacetConfig___closed__3();
lean_mark_persistent(l_Lake_Package_extraDepFacetConfig___closed__3);
l_Lake_Package_extraDepFacetConfig___closed__4 = _init_l_Lake_Package_extraDepFacetConfig___closed__4();
lean_mark_persistent(l_Lake_Package_extraDepFacetConfig___closed__4);
l_Lake_Package_extraDepFacetConfig = _init_l_Lake_Package_extraDepFacetConfig();
lean_mark_persistent(l_Lake_Package_extraDepFacetConfig);
l_Lake_Package_fetchRelease___lambda__2___closed__1 = _init_l_Lake_Package_fetchRelease___lambda__2___closed__1();
lean_mark_persistent(l_Lake_Package_fetchRelease___lambda__2___closed__1);
l_Lake_Package_fetchRelease___lambda__2___closed__2 = _init_l_Lake_Package_fetchRelease___lambda__2___closed__2();
lean_mark_persistent(l_Lake_Package_fetchRelease___lambda__2___closed__2);
l_Lake_Package_fetchRelease___lambda__2___closed__3 = _init_l_Lake_Package_fetchRelease___lambda__2___closed__3();
lean_mark_persistent(l_Lake_Package_fetchRelease___lambda__2___closed__3);
l_Lake_Package_fetchRelease___lambda__2___closed__4 = _init_l_Lake_Package_fetchRelease___lambda__2___closed__4();
lean_mark_persistent(l_Lake_Package_fetchRelease___lambda__2___closed__4);
l_Lake_Package_fetchRelease___lambda__2___closed__5 = _init_l_Lake_Package_fetchRelease___lambda__2___closed__5();
lean_mark_persistent(l_Lake_Package_fetchRelease___lambda__2___closed__5);
l_Lake_Package_fetchRelease___lambda__2___closed__6 = _init_l_Lake_Package_fetchRelease___lambda__2___closed__6();
lean_mark_persistent(l_Lake_Package_fetchRelease___lambda__2___closed__6);
l_Lake_Package_fetchRelease___lambda__2___closed__7 = _init_l_Lake_Package_fetchRelease___lambda__2___closed__7();
lean_mark_persistent(l_Lake_Package_fetchRelease___lambda__2___closed__7);
l_Lake_Package_fetchRelease___lambda__2___closed__8 = _init_l_Lake_Package_fetchRelease___lambda__2___closed__8();
lean_mark_persistent(l_Lake_Package_fetchRelease___lambda__2___closed__8);
l_Lake_Package_fetchRelease___lambda__2___closed__9 = _init_l_Lake_Package_fetchRelease___lambda__2___closed__9();
lean_mark_persistent(l_Lake_Package_fetchRelease___lambda__2___closed__9);
l_Lake_Package_fetchRelease___lambda__2___closed__10 = _init_l_Lake_Package_fetchRelease___lambda__2___closed__10();
lean_mark_persistent(l_Lake_Package_fetchRelease___lambda__2___closed__10);
l_Lake_Package_fetchRelease___lambda__2___closed__11 = _init_l_Lake_Package_fetchRelease___lambda__2___closed__11();
lean_mark_persistent(l_Lake_Package_fetchRelease___lambda__2___closed__11);
l_Lake_Package_fetchRelease___lambda__2___closed__12 = _init_l_Lake_Package_fetchRelease___lambda__2___closed__12();
lean_mark_persistent(l_Lake_Package_fetchRelease___lambda__2___closed__12);
l_Lake_Package_fetchRelease___lambda__2___closed__13 = _init_l_Lake_Package_fetchRelease___lambda__2___closed__13();
lean_mark_persistent(l_Lake_Package_fetchRelease___lambda__2___closed__13);
l_Lake_Package_fetchRelease___lambda__2___closed__14 = _init_l_Lake_Package_fetchRelease___lambda__2___closed__14();
lean_mark_persistent(l_Lake_Package_fetchRelease___lambda__2___closed__14);
l_Lake_Package_fetchRelease___lambda__2___closed__15 = _init_l_Lake_Package_fetchRelease___lambda__2___closed__15();
lean_mark_persistent(l_Lake_Package_fetchRelease___lambda__2___closed__15);
l_Lake_Package_fetchRelease___lambda__2___closed__16 = _init_l_Lake_Package_fetchRelease___lambda__2___closed__16();
lean_mark_persistent(l_Lake_Package_fetchRelease___lambda__2___closed__16);
l_Lake_Package_fetchRelease___lambda__2___closed__17 = _init_l_Lake_Package_fetchRelease___lambda__2___closed__17();
lean_mark_persistent(l_Lake_Package_fetchRelease___lambda__2___closed__17);
l_Lake_Package_fetchRelease___lambda__2___closed__18 = _init_l_Lake_Package_fetchRelease___lambda__2___closed__18();
lean_mark_persistent(l_Lake_Package_fetchRelease___lambda__2___closed__18);
l_Lake_Package_fetchRelease___lambda__2___closed__19 = _init_l_Lake_Package_fetchRelease___lambda__2___closed__19();
lean_mark_persistent(l_Lake_Package_fetchRelease___lambda__2___closed__19);
l_Lake_Package_fetchRelease___lambda__2___closed__20 = _init_l_Lake_Package_fetchRelease___lambda__2___closed__20();
lean_mark_persistent(l_Lake_Package_fetchRelease___lambda__2___closed__20);
l_Lake_Package_fetchRelease___lambda__2___closed__21 = _init_l_Lake_Package_fetchRelease___lambda__2___closed__21();
lean_mark_persistent(l_Lake_Package_fetchRelease___lambda__2___closed__21);
l_Lake_Package_fetchRelease___lambda__2___closed__22 = _init_l_Lake_Package_fetchRelease___lambda__2___closed__22();
lean_mark_persistent(l_Lake_Package_fetchRelease___lambda__2___closed__22);
l_Lake_Package_fetchRelease___lambda__2___closed__23 = _init_l_Lake_Package_fetchRelease___lambda__2___closed__23();
l_Lake_Package_fetchRelease___lambda__2___closed__24 = _init_l_Lake_Package_fetchRelease___lambda__2___closed__24();
lean_mark_persistent(l_Lake_Package_fetchRelease___lambda__2___closed__24);
l_Lake_Package_fetchRelease___closed__1 = _init_l_Lake_Package_fetchRelease___closed__1();
lean_mark_persistent(l_Lake_Package_fetchRelease___closed__1);
l_Lake_Package_fetchRelease___closed__2 = _init_l_Lake_Package_fetchRelease___closed__2();
lean_mark_persistent(l_Lake_Package_fetchRelease___closed__2);
l_Lake_Package_fetchRelease___closed__3 = _init_l_Lake_Package_fetchRelease___closed__3();
lean_mark_persistent(l_Lake_Package_fetchRelease___closed__3);
l_Lake_Package_fetchRelease___closed__4 = _init_l_Lake_Package_fetchRelease___closed__4();
lean_mark_persistent(l_Lake_Package_fetchRelease___closed__4);
l_Lake_Package_releaseFacetConfig___closed__1 = _init_l_Lake_Package_releaseFacetConfig___closed__1();
lean_mark_persistent(l_Lake_Package_releaseFacetConfig___closed__1);
l_Lake_Package_releaseFacetConfig___closed__2 = _init_l_Lake_Package_releaseFacetConfig___closed__2();
lean_mark_persistent(l_Lake_Package_releaseFacetConfig___closed__2);
l_Lake_Package_releaseFacetConfig = _init_l_Lake_Package_releaseFacetConfig();
lean_mark_persistent(l_Lake_Package_releaseFacetConfig);
l_Lake_initPackageFacetConfigs___closed__1 = _init_l_Lake_initPackageFacetConfigs___closed__1();
lean_mark_persistent(l_Lake_initPackageFacetConfigs___closed__1);
l_Lake_initPackageFacetConfigs___closed__2 = _init_l_Lake_initPackageFacetConfigs___closed__2();
lean_mark_persistent(l_Lake_initPackageFacetConfigs___closed__2);
l_Lake_initPackageFacetConfigs___closed__3 = _init_l_Lake_initPackageFacetConfigs___closed__3();
lean_mark_persistent(l_Lake_initPackageFacetConfigs___closed__3);
l_Lake_initPackageFacetConfigs = _init_l_Lake_initPackageFacetConfigs();
lean_mark_persistent(l_Lake_initPackageFacetConfigs);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

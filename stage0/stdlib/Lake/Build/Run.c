// Lean compiler output
// Module: Lake.Build.Run
// Imports: Init Lake.Util.Lock Lake.Build.Index
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
LEAN_EXPORT lean_object* l_Lake_mkBuildContext(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lake_instOrdLogLevel;
uint8_t l_Lake_Log_hasVisibleEntries(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lake_Workspace_runFetchM___spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* lean_get_set_stdout(lean_object*, lean_object*);
static lean_object* l_Lake_mkBuildContext___closed__1;
static lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__1;
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__2;
lean_object* l___private_Init_GetElem_0__outOfBounds___rarg(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_Workspace_runFetchM___spec__6(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lake_mkBuildContext___closed__2;
static lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__12(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__2(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___closed__4;
uint64_t lean_string_hash(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_Workspace_runFetchM___spec__5___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___closed__6;
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___lambda__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___closed__2;
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_Workspace_runFetchM___spec__2___rarg(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_validate_utf8(lean_object*);
extern lean_object* l_instInhabitedPUnit;
lean_object* lean_get_stdout(lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t l_String_isEmpty(lean_object*);
static lean_object* l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___closed__1;
static lean_object* l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___lambda__2___closed__1;
static lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__1;
static lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__1;
static lean_object* l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___closed__3;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lake_Workspace_runFetchM___spec__14(uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
extern lean_object* l_ByteArray_empty;
static lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__2;
lean_object* l_Lake_recFetch___at_Lake_FetchM_run___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_logToStream(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1(lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__3;
static lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__4;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg(lean_object*, uint8_t, lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__7___closed__2;
lean_object* l_panic___at_String_fromUTF8_x21___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_Workspace_runFetchM___spec__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_get_stderr(lean_object*);
extern lean_object* l_String_instInhabited;
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_Workspace_runFetchM___spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_runBuild(lean_object*);
lean_object* l_IO_FS_Stream_ofBuffer(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__7(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at_Lake_Workspace_runFetchM___spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lake_Workspace_runFetchM___spec__9(uint8_t, lean_object*, size_t, size_t);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_set_stderr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10(lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_from_utf8(lean_object*);
static lean_object* l_Lake_mkBuildContext___closed__3;
static lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__6;
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__4;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__4___closed__1;
static lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__5;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__11(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
uint8_t l_Lake_instDecidableEqVerbosity(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Job_instInhabited___rarg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__7___closed__1;
lean_object* l_Lake_Env_leanGithash(lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___lambda__3(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lake_Workspace_runFetchM___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__7___closed__3;
uint8_t l_instDecidableRelLe___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___closed__5;
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__5(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_set_stdin(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___lambda__2(uint8_t, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__11___closed__1;
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__13(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__6(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_runBuild___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_Workspace_runFetchM___spec__5(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at_Lake_Workspace_runFetchM___spec__4___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_io_wait(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_Workspace_runFetchM___spec__6___rarg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild(lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__5;
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_Workspace_runFetchM___spec__2(lean_object*);
static lean_object* l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___lambda__1___closed__1;
uint8_t l_Array_isEmpty___rarg(lean_object*);
static lean_object* _init_l_Lake_mkBuildContext___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_mkBuildContext___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_mkBuildContext___closed__3() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = l_Lake_mkBuildContext___closed__2;
x_3 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint32(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_mkBuildContext(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lake_mkBuildContext___closed__1;
x_5 = lean_st_mk_ref(x_4, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = l_Lake_Env_leanGithash(x_8);
lean_dec(x_8);
x_10 = lean_string_hash(x_9);
lean_dec(x_9);
x_11 = 1723;
x_12 = lean_uint64_mix_hash(x_11, x_10);
x_13 = l_Lake_mkBuildContext___closed__3;
x_14 = lean_box_uint64(x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_1);
lean_ctor_set(x_16, 2, x_15);
lean_ctor_set(x_16, 3, x_7);
lean_ctor_set(x_5, 0, x_16);
return x_5;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_17 = lean_ctor_get(x_5, 0);
x_18 = lean_ctor_get(x_5, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_5);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
x_20 = l_Lake_Env_leanGithash(x_19);
lean_dec(x_19);
x_21 = lean_string_hash(x_20);
lean_dec(x_20);
x_22 = 1723;
x_23 = lean_uint64_mix_hash(x_22, x_21);
x_24 = l_Lake_mkBuildContext___closed__3;
x_25 = lean_box_uint64(x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_2);
lean_ctor_set(x_27, 1, x_1);
lean_ctor_set(x_27, 2, x_26);
lean_ctor_set(x_27, 3, x_17);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_18);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_2);
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_Workspace_runFetchM___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_get_set_stdout(x_1, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_apply_1(x_2, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_get_set_stdout(x_5, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_8);
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_dec(x_7);
x_17 = lean_get_set_stdout(x_5, x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_15);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_Workspace_runFetchM___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_Workspace_runFetchM___spec__2___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_Workspace_runFetchM___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_get_set_stdin(x_1, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_apply_1(x_2, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_get_set_stdin(x_5, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_8);
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_dec(x_7);
x_17 = lean_get_set_stdin(x_5, x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_15);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_Workspace_runFetchM___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_withStdin___at_Lake_Workspace_runFetchM___spec__3___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at_Lake_Workspace_runFetchM___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_get_set_stderr(x_1, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_apply_1(x_2, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_get_set_stderr(x_5, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_8);
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_dec(x_7);
x_17 = lean_get_set_stderr(x_5, x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_15);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at_Lake_Workspace_runFetchM___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_withStderr___at_Lake_Workspace_runFetchM___spec__4___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_Workspace_runFetchM___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_get_set_stdout(x_1, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_apply_1(x_2, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_get_set_stdout(x_5, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_8);
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_dec(x_7);
x_17 = lean_get_set_stdout(x_5, x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_15);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_Workspace_runFetchM___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_Workspace_runFetchM___spec__5___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_Workspace_runFetchM___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_get_set_stdin(x_1, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_apply_1(x_2, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_get_set_stdin(x_5, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_8);
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_dec(x_7);
x_17 = lean_get_set_stdin(x_5, x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_15);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_Workspace_runFetchM___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_withStdin___at_Lake_Workspace_runFetchM___spec__6___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_ByteArray_empty;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Init.Data.String.Extra", 22);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("String.fromUTF8!", 16);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid UTF-8 string", 20);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__2;
x_2 = l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__3;
x_3 = lean_unsigned_to_nat(92u);
x_4 = lean_unsigned_to_nat(47u);
x_5 = l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__4;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__1;
x_5 = lean_st_mk_ref(x_4, x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_st_mk_ref(x_4, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_IO_FS_Stream_ofBuffer(x_6);
lean_inc(x_9);
x_12 = l_IO_FS_Stream_ofBuffer(x_9);
if (x_2 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_Workspace_runFetchM___spec__2___rarg), 3, 2);
lean_closure_set(x_13, 0, x_12);
lean_closure_set(x_13, 1, x_1);
x_14 = l_IO_withStdin___at_Lake_Workspace_runFetchM___spec__3___rarg(x_11, x_13, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_st_ref_get(x_9, x_16);
lean_dec(x_9);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_string_validate_utf8(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_20);
x_22 = l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__5;
x_23 = l_panic___at_String_fromUTF8_x21___spec__1(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_15);
lean_ctor_set(x_17, 0, x_24);
return x_17;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_string_from_utf8(x_20);
lean_dec(x_20);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_15);
lean_ctor_set(x_17, 0, x_26);
return x_17;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_17, 0);
x_28 = lean_ctor_get(x_17, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_17);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_string_validate_utf8(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_29);
x_31 = l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__5;
x_32 = l_panic___at_String_fromUTF8_x21___spec__1(x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_15);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_28);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_string_from_utf8(x_29);
lean_dec(x_29);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_15);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_28);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_9);
x_38 = !lean_is_exclusive(x_14);
if (x_38 == 0)
{
return x_14;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_14, 0);
x_40 = lean_ctor_get(x_14, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_14);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_inc(x_12);
x_42 = lean_alloc_closure((void*)(l_IO_withStderr___at_Lake_Workspace_runFetchM___spec__4___rarg), 3, 2);
lean_closure_set(x_42, 0, x_12);
lean_closure_set(x_42, 1, x_1);
x_43 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_Workspace_runFetchM___spec__5___rarg), 3, 2);
lean_closure_set(x_43, 0, x_12);
lean_closure_set(x_43, 1, x_42);
x_44 = l_IO_withStdin___at_Lake_Workspace_runFetchM___spec__6___rarg(x_11, x_43, x_10);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_st_ref_get(x_9, x_46);
lean_dec(x_9);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec(x_49);
x_51 = lean_string_validate_utf8(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_50);
x_52 = l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__5;
x_53 = l_panic___at_String_fromUTF8_x21___spec__1(x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_45);
lean_ctor_set(x_47, 0, x_54);
return x_47;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_string_from_utf8(x_50);
lean_dec(x_50);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_45);
lean_ctor_set(x_47, 0, x_56);
return x_47;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_57 = lean_ctor_get(x_47, 0);
x_58 = lean_ctor_get(x_47, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_47);
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_string_validate_utf8(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_59);
x_61 = l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__5;
x_62 = l_panic___at_String_fromUTF8_x21___spec__1(x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_45);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_58);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_string_from_utf8(x_59);
lean_dec(x_59);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_45);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_58);
return x_67;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_9);
x_68 = !lean_is_exclusive(x_44);
if (x_68 == 0)
{
return x_44;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_44, 0);
x_70 = lean_ctor_get(x_44, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_44);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__7(lean_object* x_1, uint8_t x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_eq(x_4, x_5);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; 
lean_dec(x_6);
x_10 = lean_array_uget(x_3, x_4);
lean_inc(x_1);
x_11 = l_Lake_logToStream(x_10, x_1, x_2, x_8);
lean_dec(x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = 1;
x_15 = lean_usize_add(x_4, x_14);
x_4 = x_15;
x_6 = x_12;
x_8 = x_13;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_7);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_8);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__8(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_3, x_4);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; 
lean_dec(x_5);
x_9 = lean_array_uget(x_2, x_3);
x_10 = 2;
lean_inc(x_1);
x_11 = l_Lake_logToStream(x_9, x_1, x_10, x_7);
lean_dec(x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = 1;
x_15 = lean_usize_add(x_3, x_14);
x_3 = x_15;
x_5 = x_12;
x_7 = x_13;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_6);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_7);
return x_18;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lake_Workspace_runFetchM___spec__9(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
lean_dec(x_6);
x_8 = l_Lake_instOrdLogLevel;
x_9 = lean_box(x_1);
x_10 = lean_box(x_7);
x_11 = l_instDecidableRelLe___rarg(x_8, x_9, x_10);
if (x_11 == 0)
{
size_t x_12; size_t x_13; 
x_12 = 1;
x_13 = lean_usize_add(x_3, x_12);
x_3 = x_13;
goto _start;
}
else
{
uint8_t x_15; 
x_15 = 1;
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
}
}
static lean_object* _init_l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\n", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
x_9 = l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___lambda__1___closed__1;
x_10 = lean_apply_2(x_8, x_9, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_array_get_size(x_2);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_12);
if (x_3 == 0)
{
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_apply_1(x_15, x_11);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_6);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_16);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_6);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_6);
x_24 = !lean_is_exclusive(x_16);
if (x_24 == 0)
{
return x_16;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_16, 0);
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_16);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
uint8_t x_28; 
x_28 = lean_nat_dec_le(x_12, x_12);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_12);
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
lean_dec(x_1);
x_30 = lean_apply_1(x_29, x_11);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_6);
lean_ctor_set(x_30, 0, x_33);
return x_30;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_30, 0);
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_30);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_6);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_6);
x_38 = !lean_is_exclusive(x_30);
if (x_38 == 0)
{
return x_30;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_30, 0);
x_40 = lean_ctor_get(x_30, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_30);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
size_t x_42; size_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_42 = 0;
x_43 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_44 = lean_box(0);
lean_inc(x_1);
x_45 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__7(x_1, x_4, x_2, x_42, x_43, x_44, x_6, x_11);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = !lean_is_exclusive(x_46);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_46, 1);
x_50 = lean_ctor_get(x_46, 0);
lean_dec(x_50);
x_51 = lean_ctor_get(x_1, 0);
lean_inc(x_51);
lean_dec(x_1);
x_52 = lean_apply_1(x_51, x_47);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_52, 0);
lean_ctor_set(x_46, 0, x_54);
lean_ctor_set(x_52, 0, x_46);
return x_52;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_52, 0);
x_56 = lean_ctor_get(x_52, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_52);
lean_ctor_set(x_46, 0, x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_46);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
else
{
uint8_t x_58; 
lean_free_object(x_46);
lean_dec(x_49);
x_58 = !lean_is_exclusive(x_52);
if (x_58 == 0)
{
return x_52;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_52, 0);
x_60 = lean_ctor_get(x_52, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_52);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_46, 1);
lean_inc(x_62);
lean_dec(x_46);
x_63 = lean_ctor_get(x_1, 0);
lean_inc(x_63);
lean_dec(x_1);
x_64 = lean_apply_1(x_63, x_47);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
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
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_62);
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_67;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_66);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_62);
x_70 = lean_ctor_get(x_64, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_64, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_72 = x_64;
} else {
 lean_dec_ref(x_64);
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
}
else
{
if (x_14 == 0)
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_12);
x_74 = lean_ctor_get(x_1, 0);
lean_inc(x_74);
lean_dec(x_1);
x_75 = lean_apply_1(x_74, x_11);
if (lean_obj_tag(x_75) == 0)
{
uint8_t x_76; 
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_75, 0);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_6);
lean_ctor_set(x_75, 0, x_78);
return x_75;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_75, 0);
x_80 = lean_ctor_get(x_75, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_75);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_6);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
else
{
uint8_t x_83; 
lean_dec(x_6);
x_83 = !lean_is_exclusive(x_75);
if (x_83 == 0)
{
return x_75;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_75, 0);
x_85 = lean_ctor_get(x_75, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_75);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
uint8_t x_87; 
x_87 = lean_nat_dec_le(x_12, x_12);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_12);
x_88 = lean_ctor_get(x_1, 0);
lean_inc(x_88);
lean_dec(x_1);
x_89 = lean_apply_1(x_88, x_11);
if (lean_obj_tag(x_89) == 0)
{
uint8_t x_90; 
x_90 = !lean_is_exclusive(x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_89, 0);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_6);
lean_ctor_set(x_89, 0, x_92);
return x_89;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_89, 0);
x_94 = lean_ctor_get(x_89, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_89);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_6);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
else
{
uint8_t x_97; 
lean_dec(x_6);
x_97 = !lean_is_exclusive(x_89);
if (x_97 == 0)
{
return x_89;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_89, 0);
x_99 = lean_ctor_get(x_89, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_89);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
else
{
size_t x_101; size_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_101 = 0;
x_102 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_103 = lean_box(0);
lean_inc(x_1);
x_104 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__8(x_1, x_2, x_101, x_102, x_103, x_6, x_11);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = !lean_is_exclusive(x_105);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_108 = lean_ctor_get(x_105, 1);
x_109 = lean_ctor_get(x_105, 0);
lean_dec(x_109);
x_110 = lean_ctor_get(x_1, 0);
lean_inc(x_110);
lean_dec(x_1);
x_111 = lean_apply_1(x_110, x_106);
if (lean_obj_tag(x_111) == 0)
{
uint8_t x_112; 
x_112 = !lean_is_exclusive(x_111);
if (x_112 == 0)
{
lean_object* x_113; 
x_113 = lean_ctor_get(x_111, 0);
lean_ctor_set(x_105, 0, x_113);
lean_ctor_set(x_111, 0, x_105);
return x_111;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_111, 0);
x_115 = lean_ctor_get(x_111, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_111);
lean_ctor_set(x_105, 0, x_114);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_105);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
else
{
uint8_t x_117; 
lean_free_object(x_105);
lean_dec(x_108);
x_117 = !lean_is_exclusive(x_111);
if (x_117 == 0)
{
return x_111;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_111, 0);
x_119 = lean_ctor_get(x_111, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_111);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_105, 1);
lean_inc(x_121);
lean_dec(x_105);
x_122 = lean_ctor_get(x_1, 0);
lean_inc(x_122);
lean_dec(x_1);
x_123 = lean_apply_1(x_122, x_106);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_126 = x_123;
} else {
 lean_dec_ref(x_123);
 x_126 = lean_box(0);
}
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_124);
lean_ctor_set(x_127, 1, x_121);
if (lean_is_scalar(x_126)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_126;
}
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_125);
return x_128;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_121);
x_129 = lean_ctor_get(x_123, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_123, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_131 = x_123;
} else {
 lean_dec_ref(x_123);
 x_131 = lean_box(0);
}
if (lean_is_scalar(x_131)) {
 x_132 = lean_alloc_ctor(1, 2, 0);
} else {
 x_132 = x_131;
}
lean_ctor_set(x_132, 0, x_129);
lean_ctor_set(x_132, 1, x_130);
return x_132;
}
}
}
}
}
}
else
{
uint8_t x_133; 
lean_dec(x_6);
lean_dec(x_1);
x_133 = !lean_is_exclusive(x_10);
if (x_133 == 0)
{
return x_10;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_10, 0);
x_135 = lean_ctor_get(x_10, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_10);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
}
}
}
static lean_object* _init_l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\x1b[2K\r", 5);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___lambda__2(uint8_t x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (x_1 == 0)
{
uint8_t x_11; 
lean_inc(x_2);
x_11 = l_Lake_Log_hasVisibleEntries(x_2, x_3);
if (x_11 == 0)
{
lean_dec(x_7);
lean_dec(x_2);
if (x_4 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
if (x_5 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_6, 4);
lean_inc(x_15);
lean_dec(x_6);
x_16 = l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___lambda__1___closed__1;
x_17 = lean_apply_2(x_15, x_16, x_10);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_9);
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
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_9);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_9);
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
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_6, 4);
lean_inc(x_29);
lean_dec(x_6);
x_30 = l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___lambda__2___closed__1;
x_31 = lean_apply_2(x_29, x_30, x_10);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_9);
lean_ctor_set(x_31, 0, x_34);
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_31, 0);
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_31);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_9);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_9);
x_39 = !lean_is_exclusive(x_31);
if (x_39 == 0)
{
return x_31;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_31, 0);
x_41 = lean_ctor_get(x_31, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_31);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
}
else
{
if (x_4 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_6, 4);
lean_inc(x_43);
x_44 = lean_apply_2(x_43, x_7, x_10);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___lambda__1(x_6, x_2, x_1, x_3, x_45, x_9, x_46);
lean_dec(x_45);
lean_dec(x_2);
return x_47;
}
else
{
uint8_t x_48; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_2);
x_48 = !lean_is_exclusive(x_44);
if (x_48 == 0)
{
return x_44;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_44, 0);
x_50 = lean_ctor_get(x_44, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_44);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_7);
x_52 = lean_box(0);
x_53 = l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___lambda__1(x_6, x_2, x_1, x_3, x_52, x_9, x_10);
lean_dec(x_2);
return x_53;
}
}
}
else
{
if (x_4 == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_6, 4);
lean_inc(x_54);
x_55 = lean_apply_2(x_54, x_7, x_10);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___lambda__1(x_6, x_2, x_1, x_3, x_56, x_9, x_57);
lean_dec(x_56);
lean_dec(x_2);
return x_58;
}
else
{
uint8_t x_59; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_2);
x_59 = !lean_is_exclusive(x_55);
if (x_59 == 0)
{
return x_55;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_55, 0);
x_61 = lean_ctor_get(x_55, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_55);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_7);
x_63 = lean_box(0);
x_64 = l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___lambda__1(x_6, x_2, x_1, x_3, x_63, x_9, x_10);
lean_dec(x_2);
return x_64;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___lambda__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_31; 
lean_dec(x_9);
x_12 = lean_io_wait(x_1, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_31 = lean_ctor_get(x_13, 1);
lean_inc(x_31);
lean_dec(x_13);
x_15 = x_31;
goto block_30;
block_30:
{
uint8_t x_16; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_array_get_size(x_15);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_nat_dec_lt(x_24, x_23);
if (x_25 == 0)
{
uint8_t x_26; 
lean_dec(x_23);
x_26 = 0;
x_16 = x_26;
goto block_22;
}
else
{
size_t x_27; size_t x_28; uint8_t x_29; 
x_27 = 0;
x_28 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_29 = l_Array_anyMUnsafe_any___at_Lake_Workspace_runFetchM___spec__9(x_8, x_15, x_27, x_28);
x_16 = x_29;
goto block_22;
}
block_22:
{
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_7);
x_17 = lean_box(0);
x_18 = l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___lambda__2(x_16, x_15, x_3, x_4, x_5, x_2, x_6, x_17, x_10, x_14);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_array_push(x_10, x_7);
x_20 = lean_box(0);
x_21 = l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___lambda__2(x_16, x_15, x_3, x_4, x_5, x_2, x_6, x_20, x_19, x_14);
return x_21;
}
}
}
}
}
static lean_object* _init_l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("[", 1);
return x_1;
}
}
static lean_object* _init_l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("/", 1);
return x_1;
}
}
static lean_object* _init_l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("] ", 2);
return x_1;
}
}
static lean_object* _init_l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instInhabitedPUnit;
x_2 = l_Lake_Job_instInhabited___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_String_instInhabited;
x_2 = l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10(lean_object* x_1, uint8_t x_2, uint8_t x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_9, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_68; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_9, x_14);
lean_dec(x_9);
x_16 = lean_nat_sub(x_8, x_15);
x_17 = lean_nat_sub(x_16, x_14);
lean_dec(x_16);
x_68 = lean_nat_dec_lt(x_17, x_7);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___closed__6;
x_70 = l___private_Init_GetElem_0__outOfBounds___rarg(x_69);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_18 = x_71;
x_19 = x_72;
goto block_67;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_array_fget(x_6, x_17);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_18 = x_74;
x_19 = x_75;
goto block_67;
}
block_67:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_20 = lean_nat_add(x_17, x_14);
lean_dec(x_17);
x_21 = l___private_Init_Data_Repr_0__Nat_reprFast(x_20);
x_22 = l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___closed__1;
x_23 = lean_string_append(x_22, x_21);
lean_dec(x_21);
x_24 = l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___closed__2;
x_25 = lean_string_append(x_23, x_24);
lean_inc(x_7);
x_26 = l___private_Init_Data_Repr_0__Nat_reprFast(x_7);
x_27 = lean_string_append(x_25, x_26);
lean_dec(x_26);
x_28 = l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___closed__3;
x_29 = lean_string_append(x_27, x_28);
x_30 = lean_string_append(x_29, x_18);
x_31 = l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___closed__4;
x_32 = lean_string_append(x_30, x_31);
if (x_4 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_box(0);
lean_inc(x_1);
x_34 = l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___lambda__3(x_19, x_1, x_3, x_4, x_2, x_32, x_18, x_5, x_33, x_10, x_11);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_9 = x_15;
x_10 = x_37;
x_11 = x_36;
goto _start;
}
else
{
uint8_t x_39; 
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_34);
if (x_39 == 0)
{
return x_34;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_34, 0);
x_41 = lean_ctor_get(x_34, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_34);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_1, 4);
lean_inc(x_43);
lean_inc(x_32);
x_44 = lean_apply_2(x_43, x_32, x_11);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_ctor_get(x_1, 0);
lean_inc(x_46);
x_47 = lean_apply_1(x_46, x_45);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
lean_inc(x_1);
x_50 = l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___lambda__3(x_19, x_1, x_3, x_4, x_2, x_32, x_18, x_5, x_48, x_10, x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_9 = x_15;
x_10 = x_53;
x_11 = x_52;
goto _start;
}
else
{
uint8_t x_55; 
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_50);
if (x_55 == 0)
{
return x_50;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_50, 0);
x_57 = lean_ctor_get(x_50, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_50);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_32);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_47);
if (x_59 == 0)
{
return x_47;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_47, 0);
x_61 = lean_ctor_get(x_47, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_47);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_32);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_44);
if (x_63 == 0)
{
return x_44;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_44, 0);
x_65 = lean_ctor_get(x_44, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_44);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
}
}
else
{
lean_object* x_76; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_1);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_10);
lean_ctor_set(x_76, 1, x_11);
return x_76;
}
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__11___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("- ", 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__11(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_3, x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
x_8 = lean_array_uget(x_2, x_3);
x_9 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__11___closed__1;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___lambda__1___closed__1;
x_12 = lean_string_append(x_10, x_11);
lean_inc(x_1);
x_13 = lean_apply_2(x_1, x_12, x_6);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 1;
x_17 = lean_usize_add(x_3, x_16);
x_3 = x_17;
x_5 = x_14;
x_6 = x_15;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
return x_13;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_13, 0);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_13);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; 
lean_dec(x_1);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_6);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__12(lean_object* x_1, uint8_t x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_4, x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; 
lean_dec(x_6);
x_9 = lean_array_uget(x_3, x_4);
lean_inc(x_1);
x_10 = l_Lake_logToStream(x_9, x_1, x_2, x_7);
lean_dec(x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = 1;
x_14 = lean_usize_add(x_4, x_13);
x_4 = x_14;
x_6 = x_11;
x_7 = x_12;
goto _start;
}
else
{
lean_object* x_16; 
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_7);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__13(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_3, x_4);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; 
lean_dec(x_5);
x_8 = lean_array_uget(x_2, x_3);
x_9 = 2;
lean_inc(x_1);
x_10 = l_Lake_logToStream(x_8, x_1, x_9, x_6);
lean_dec(x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = 1;
x_14 = lean_usize_add(x_3, x_13);
x_3 = x_14;
x_5 = x_11;
x_6 = x_12;
goto _start;
}
else
{
lean_object* x_16; 
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_5);
lean_ctor_set(x_16, 1, x_6);
return x_16;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lake_Workspace_runFetchM___spec__14(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
lean_dec(x_6);
x_8 = l_Lake_instOrdLogLevel;
x_9 = lean_box(x_1);
x_10 = lean_box(x_7);
x_11 = l_instDecidableRelLe___rarg(x_8, x_9, x_10);
if (x_11 == 0)
{
size_t x_12; size_t x_13; 
x_12 = 1;
x_13 = lean_usize_add(x_3, x_12);
x_3 = x_13;
goto _start;
}
else
{
uint8_t x_15; 
x_15 = 1;
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_recFetch___at_Lake_FetchM_run___spec__7), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_box(0);
x_6 = lean_box(0);
x_7 = l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__1;
x_8 = lean_apply_6(x_1, x_7, x_5, x_6, x_2, x_3, x_4);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_8, 0);
lean_dec(x_12);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_10, 1);
lean_dec(x_16);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_10, 1, x_13);
lean_ctor_set(x_10, 0, x_17);
lean_ctor_set(x_8, 0, x_10);
return x_8;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
lean_dec(x_10);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_13);
lean_ctor_set(x_8, 0, x_20);
return x_8;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_8, 1);
lean_inc(x_21);
lean_dec(x_8);
x_22 = lean_ctor_get(x_9, 1);
lean_inc(x_22);
lean_dec(x_9);
x_23 = lean_ctor_get(x_10, 0);
lean_inc(x_23);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_24 = x_10;
} else {
 lean_dec_ref(x_10);
 x_24 = lean_box(0);
}
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_23);
if (lean_is_scalar(x_24)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_24;
}
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_22);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_21);
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_8);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_8, 0);
lean_dec(x_29);
x_30 = lean_ctor_get(x_9, 1);
lean_inc(x_30);
lean_dec(x_9);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_8, 0, x_32);
return x_8;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_8, 1);
lean_inc(x_33);
lean_dec(x_8);
x_34 = lean_ctor_get(x_9, 1);
lean_inc(x_34);
lean_dec(x_9);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_33);
return x_37;
}
}
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Some build steps logged failures:\n", 34);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("build failed", 12);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__2;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Computing build jobs", 20);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__4;
x_2 = l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_1, 3);
x_13 = lean_st_ref_get(x_12, x_11);
if (x_8 == 0)
{
x_14 = x_9;
goto block_116;
}
else
{
lean_object* x_117; 
lean_dec(x_9);
x_117 = l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__6;
x_14 = x_117;
goto block_116;
}
block_116:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_array_get_size(x_15);
lean_inc_n(x_17, 2);
lean_inc(x_2);
x_18 = l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10(x_2, x_3, x_4, x_5, x_6, x_15, x_17, x_17, x_17, x_14, x_16);
lean_dec(x_17);
lean_dec(x_15);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = l_Array_isEmpty___rarg(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_free_object(x_18);
x_23 = lean_ctor_get(x_2, 4);
lean_inc(x_23);
lean_dec(x_2);
x_24 = l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__1;
lean_inc(x_23);
x_25 = lean_apply_2(x_23, x_24, x_21);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_25, 1);
x_28 = lean_ctor_get(x_25, 0);
lean_dec(x_28);
x_29 = lean_array_get_size(x_20);
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_nat_dec_lt(x_30, x_29);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_29);
lean_dec(x_23);
lean_dec(x_20);
x_32 = l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__3;
lean_ctor_set_tag(x_25, 1);
lean_ctor_set(x_25, 0, x_32);
return x_25;
}
else
{
uint8_t x_33; 
x_33 = lean_nat_dec_le(x_29, x_29);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_29);
lean_dec(x_23);
lean_dec(x_20);
x_34 = l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__3;
lean_ctor_set_tag(x_25, 1);
lean_ctor_set(x_25, 0, x_34);
return x_25;
}
else
{
size_t x_35; size_t x_36; lean_object* x_37; lean_object* x_38; 
lean_free_object(x_25);
x_35 = 0;
x_36 = lean_usize_of_nat(x_29);
lean_dec(x_29);
x_37 = lean_box(0);
x_38 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__11(x_23, x_20, x_35, x_36, x_37, x_27);
lean_dec(x_20);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
x_41 = l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__3;
lean_ctor_set_tag(x_38, 1);
lean_ctor_set(x_38, 0, x_41);
return x_38;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
lean_dec(x_38);
x_43 = l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__3;
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_38);
if (x_45 == 0)
{
return x_38;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_38, 0);
x_47 = lean_ctor_get(x_38, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_38);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_25, 1);
lean_inc(x_49);
lean_dec(x_25);
x_50 = lean_array_get_size(x_20);
x_51 = lean_unsigned_to_nat(0u);
x_52 = lean_nat_dec_lt(x_51, x_50);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_50);
lean_dec(x_23);
lean_dec(x_20);
x_53 = l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__3;
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_49);
return x_54;
}
else
{
uint8_t x_55; 
x_55 = lean_nat_dec_le(x_50, x_50);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_50);
lean_dec(x_23);
lean_dec(x_20);
x_56 = l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__3;
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_49);
return x_57;
}
else
{
size_t x_58; size_t x_59; lean_object* x_60; lean_object* x_61; 
x_58 = 0;
x_59 = lean_usize_of_nat(x_50);
lean_dec(x_50);
x_60 = lean_box(0);
x_61 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__11(x_23, x_20, x_58, x_59, x_60, x_49);
lean_dec(x_20);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_63 = x_61;
} else {
 lean_dec_ref(x_61);
 x_63 = lean_box(0);
}
x_64 = l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__3;
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(1, 2, 0);
} else {
 x_65 = x_63;
 lean_ctor_set_tag(x_65, 1);
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_62);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_61, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_61, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_68 = x_61;
} else {
 lean_dec_ref(x_61);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(1, 2, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_23);
lean_dec(x_20);
x_70 = !lean_is_exclusive(x_25);
if (x_70 == 0)
{
return x_25;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_25, 0);
x_72 = lean_ctor_get(x_25, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_25);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
lean_dec(x_20);
lean_dec(x_2);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_74; 
x_74 = l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__3;
lean_ctor_set_tag(x_18, 1);
lean_ctor_set(x_18, 0, x_74);
return x_18;
}
else
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_7, 0);
lean_inc(x_75);
lean_ctor_set(x_18, 0, x_75);
return x_18;
}
}
}
else
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_76 = lean_ctor_get(x_18, 0);
x_77 = lean_ctor_get(x_18, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_18);
x_78 = l_Array_isEmpty___rarg(x_76);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_2, 4);
lean_inc(x_79);
lean_dec(x_2);
x_80 = l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__1;
lean_inc(x_79);
x_81 = lean_apply_2(x_79, x_80, x_77);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_83 = x_81;
} else {
 lean_dec_ref(x_81);
 x_83 = lean_box(0);
}
x_84 = lean_array_get_size(x_76);
x_85 = lean_unsigned_to_nat(0u);
x_86 = lean_nat_dec_lt(x_85, x_84);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_84);
lean_dec(x_79);
lean_dec(x_76);
x_87 = l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__3;
if (lean_is_scalar(x_83)) {
 x_88 = lean_alloc_ctor(1, 2, 0);
} else {
 x_88 = x_83;
 lean_ctor_set_tag(x_88, 1);
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_82);
return x_88;
}
else
{
uint8_t x_89; 
x_89 = lean_nat_dec_le(x_84, x_84);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_84);
lean_dec(x_79);
lean_dec(x_76);
x_90 = l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__3;
if (lean_is_scalar(x_83)) {
 x_91 = lean_alloc_ctor(1, 2, 0);
} else {
 x_91 = x_83;
 lean_ctor_set_tag(x_91, 1);
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_82);
return x_91;
}
else
{
size_t x_92; size_t x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_83);
x_92 = 0;
x_93 = lean_usize_of_nat(x_84);
lean_dec(x_84);
x_94 = lean_box(0);
x_95 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__11(x_79, x_76, x_92, x_93, x_94, x_82);
lean_dec(x_76);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_97 = x_95;
} else {
 lean_dec_ref(x_95);
 x_97 = lean_box(0);
}
x_98 = l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__3;
if (lean_is_scalar(x_97)) {
 x_99 = lean_alloc_ctor(1, 2, 0);
} else {
 x_99 = x_97;
 lean_ctor_set_tag(x_99, 1);
}
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_96);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_100 = lean_ctor_get(x_95, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_95, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_102 = x_95;
} else {
 lean_dec_ref(x_95);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(1, 2, 0);
} else {
 x_103 = x_102;
}
lean_ctor_set(x_103, 0, x_100);
lean_ctor_set(x_103, 1, x_101);
return x_103;
}
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_79);
lean_dec(x_76);
x_104 = lean_ctor_get(x_81, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_81, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_106 = x_81;
} else {
 lean_dec_ref(x_81);
 x_106 = lean_box(0);
}
if (lean_is_scalar(x_106)) {
 x_107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_107 = x_106;
}
lean_ctor_set(x_107, 0, x_104);
lean_ctor_set(x_107, 1, x_105);
return x_107;
}
}
else
{
lean_dec(x_76);
lean_dec(x_2);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_108; lean_object* x_109; 
x_108 = l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__3;
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_77);
return x_109;
}
else
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_7, 0);
lean_inc(x_110);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_77);
return x_111;
}
}
}
}
else
{
uint8_t x_112; 
lean_dec(x_2);
x_112 = !lean_is_exclusive(x_18);
if (x_112 == 0)
{
return x_18;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_18, 0);
x_114 = lean_ctor_get(x_18, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_18);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_5, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_apply_2(x_2, x_7, x_8);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_2);
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_6);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___rarg___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("stdout/stderr:\n", 15);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_String_isEmpty(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lake_Workspace_runFetchM___rarg___lambda__4___closed__1;
lean_inc(x_4);
x_9 = lean_apply_2(x_4, x_8, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_apply_2(x_4, x_3, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lake_Workspace_runFetchM___rarg___lambda__3(x_1, x_2, x_12, x_13);
lean_dec(x_12);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_2);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
else
{
uint8_t x_19; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_9);
if (x_19 == 0)
{
return x_9;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_9, 0);
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_9);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_4);
lean_dec(x_3);
x_23 = lean_box(0);
x_24 = l_Lake_Workspace_runFetchM___rarg___lambda__3(x_1, x_2, x_23, x_6);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_1, 4);
lean_inc(x_11);
x_12 = l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___lambda__1___closed__1;
lean_inc(x_11);
x_13 = lean_apply_2(x_11, x_12, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
if (x_4 == 0)
{
uint8_t x_41; 
lean_inc(x_8);
x_41 = l_Lake_Log_hasVisibleEntries(x_8, x_7);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_8);
lean_dec(x_6);
x_42 = lean_box(0);
x_43 = l_Lake_Workspace_runFetchM___rarg___lambda__4(x_1, x_2, x_3, x_11, x_42, x_14);
return x_43;
}
else
{
lean_object* x_44; 
x_44 = lean_box(0);
x_15 = x_44;
goto block_40;
}
}
else
{
lean_object* x_45; 
x_45 = lean_box(0);
x_15 = x_45;
goto block_40;
}
block_40:
{
lean_dec(x_15);
if (x_4 == 0)
{
if (x_5 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_8);
lean_dec(x_6);
x_16 = lean_box(0);
x_17 = l_Lake_Workspace_runFetchM___rarg___lambda__4(x_1, x_2, x_3, x_11, x_16, x_14);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_le(x_6, x_6);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_8);
lean_dec(x_6);
x_19 = lean_box(0);
x_20 = l_Lake_Workspace_runFetchM___rarg___lambda__4(x_1, x_2, x_3, x_11, x_19, x_14);
return x_20;
}
else
{
size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = 0;
x_22 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_23 = lean_box(0);
lean_inc(x_1);
x_24 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__12(x_1, x_7, x_8, x_21, x_22, x_23, x_14);
lean_dec(x_8);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lake_Workspace_runFetchM___rarg___lambda__4(x_1, x_2, x_3, x_11, x_25, x_26);
lean_dec(x_25);
return x_27;
}
}
}
else
{
if (x_5 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_8);
lean_dec(x_6);
x_28 = lean_box(0);
x_29 = l_Lake_Workspace_runFetchM___rarg___lambda__4(x_1, x_2, x_3, x_11, x_28, x_14);
return x_29;
}
else
{
uint8_t x_30; 
x_30 = lean_nat_dec_le(x_6, x_6);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_8);
lean_dec(x_6);
x_31 = lean_box(0);
x_32 = l_Lake_Workspace_runFetchM___rarg___lambda__4(x_1, x_2, x_3, x_11, x_31, x_14);
return x_32;
}
else
{
size_t x_33; size_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_33 = 0;
x_34 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_35 = lean_box(0);
lean_inc(x_1);
x_36 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__13(x_1, x_8, x_33, x_34, x_35, x_14);
lean_dec(x_8);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lake_Workspace_runFetchM___rarg___lambda__4(x_1, x_2, x_3, x_11, x_37, x_38);
lean_dec(x_37);
return x_39;
}
}
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_13);
if (x_46 == 0)
{
return x_13;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_13, 0);
x_48 = lean_ctor_get(x_13, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_13);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
lean_dec(x_8);
x_10 = l_Lake_mkBuildContext___closed__1;
lean_inc(x_2);
x_11 = lean_alloc_closure((void*)(l_Lake_Workspace_runFetchM___rarg___lambda__1), 4, 3);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_10);
x_12 = 1;
x_13 = l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg(x_11, x_12, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_ctor_get(x_2, 0);
lean_inc(x_20);
x_21 = lean_ctor_get_uint8(x_20, 4);
lean_dec(x_20);
x_22 = lean_array_get_size(x_19);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_nat_dec_lt(x_23, x_22);
if (x_21 == 0)
{
uint8_t x_79; 
x_79 = 3;
x_25 = x_79;
goto block_78;
}
else
{
uint8_t x_80; 
x_80 = 2;
x_25 = x_80;
goto block_78;
}
block_78:
{
uint8_t x_26; 
if (x_24 == 0)
{
uint8_t x_74; 
x_74 = 0;
x_26 = x_74;
goto block_73;
}
else
{
size_t x_75; size_t x_76; uint8_t x_77; 
x_75 = 0;
x_76 = lean_usize_of_nat(x_22);
x_77 = l_Array_anyMUnsafe_any___at_Lake_Workspace_runFetchM___spec__14(x_25, x_19, x_75, x_76);
x_26 = x_77;
goto block_73;
}
block_73:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_27 = lean_box(x_4);
x_28 = lean_box(x_5);
x_29 = lean_box(x_6);
x_30 = lean_box(x_25);
x_31 = lean_box(x_26);
lean_inc(x_18);
lean_inc(x_3);
lean_inc(x_2);
x_32 = lean_alloc_closure((void*)(l_Lake_Workspace_runFetchM___rarg___lambda__2___boxed), 11, 9);
lean_closure_set(x_32, 0, x_2);
lean_closure_set(x_32, 1, x_3);
lean_closure_set(x_32, 2, x_27);
lean_closure_set(x_32, 3, x_28);
lean_closure_set(x_32, 4, x_29);
lean_closure_set(x_32, 5, x_30);
lean_closure_set(x_32, 6, x_18);
lean_closure_set(x_32, 7, x_31);
lean_closure_set(x_32, 8, x_10);
if (x_26 == 0)
{
uint8_t x_46; 
x_46 = l_String_isEmpty(x_17);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec(x_18);
lean_dec(x_2);
x_47 = lean_box(0);
x_33 = x_47;
goto block_45;
}
else
{
uint8_t x_48; 
lean_inc(x_19);
x_48 = l_Lake_Log_hasVisibleEntries(x_19, x_5);
if (x_48 == 0)
{
lean_dec(x_32);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_7);
if (x_6 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_box(0);
x_50 = l_Lake_Workspace_runFetchM___rarg___lambda__2(x_2, x_3, x_4, x_5, x_6, x_25, x_18, x_26, x_10, x_49, x_16);
lean_dec(x_18);
lean_dec(x_2);
return x_50;
}
else
{
if (x_4 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_3, 4);
lean_inc(x_51);
x_52 = l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___lambda__1___closed__1;
x_53 = lean_apply_2(x_51, x_52, x_16);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = l_Lake_Workspace_runFetchM___rarg___lambda__2(x_2, x_3, x_4, x_5, x_6, x_25, x_18, x_26, x_10, x_54, x_55);
lean_dec(x_54);
lean_dec(x_18);
lean_dec(x_2);
return x_56;
}
else
{
uint8_t x_57; 
lean_dec(x_18);
lean_dec(x_3);
lean_dec(x_2);
x_57 = !lean_is_exclusive(x_53);
if (x_57 == 0)
{
return x_53;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_53, 0);
x_59 = lean_ctor_get(x_53, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_53);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_3, 4);
lean_inc(x_61);
x_62 = l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___lambda__2___closed__1;
x_63 = lean_apply_2(x_61, x_62, x_16);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = l_Lake_Workspace_runFetchM___rarg___lambda__2(x_2, x_3, x_4, x_5, x_6, x_25, x_18, x_26, x_10, x_64, x_65);
lean_dec(x_64);
lean_dec(x_18);
lean_dec(x_2);
return x_66;
}
else
{
uint8_t x_67; 
lean_dec(x_18);
lean_dec(x_3);
lean_dec(x_2);
x_67 = !lean_is_exclusive(x_63);
if (x_67 == 0)
{
return x_63;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_63, 0);
x_69 = lean_ctor_get(x_63, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_63);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
}
else
{
lean_object* x_71; 
lean_dec(x_18);
lean_dec(x_2);
x_71 = lean_box(0);
x_33 = x_71;
goto block_45;
}
}
}
else
{
lean_object* x_72; 
lean_dec(x_18);
lean_dec(x_2);
x_72 = lean_box(0);
x_33 = x_72;
goto block_45;
}
block_45:
{
lean_dec(x_33);
if (x_6 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_3, 4);
lean_inc(x_34);
x_35 = lean_apply_2(x_34, x_7, x_16);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lake_Workspace_runFetchM___rarg___lambda__5(x_3, x_32, x_17, x_26, x_24, x_22, x_5, x_19, x_36, x_37);
lean_dec(x_36);
return x_38;
}
else
{
uint8_t x_39; 
lean_dec(x_32);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_3);
x_39 = !lean_is_exclusive(x_35);
if (x_39 == 0)
{
return x_35;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_35, 0);
x_41 = lean_ctor_get(x_35, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_35);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_7);
x_43 = lean_box(0);
x_44 = l_Lake_Workspace_runFetchM___rarg___lambda__5(x_3, x_32, x_17, x_26, x_24, x_22, x_5, x_19, x_43, x_16);
return x_44;
}
}
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_81 = !lean_is_exclusive(x_13);
if (x_81 == 0)
{
return x_13;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_13, 0);
x_83 = lean_ctor_get(x_13, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_13);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___rarg___lambda__7___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("[\?/\?] ", 6);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___rarg___lambda__7___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Workspace_runFetchM___rarg___lambda__7___closed__1;
x_2 = l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__5;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___rarg___lambda__7___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Workspace_runFetchM___rarg___lambda__7___closed__2;
x_2 = l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; 
x_6 = lean_ctor_get(x_4, 5);
lean_inc(x_6);
x_7 = lean_apply_1(x_6, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get_uint8(x_1, 3);
x_11 = lean_ctor_get_uint8(x_1, 2);
lean_dec(x_1);
if (x_11 == 0)
{
uint8_t x_36; uint8_t x_37; 
x_36 = 0;
x_37 = l_Lake_instDecidableEqVerbosity(x_10, x_36);
if (x_37 == 0)
{
uint8_t x_38; 
x_38 = 1;
x_12 = x_38;
goto block_35;
}
else
{
uint8_t x_39; 
x_39 = 0;
x_12 = x_39;
goto block_35;
}
}
else
{
uint8_t x_40; uint8_t x_41; 
x_40 = 2;
x_41 = l_Lake_instDecidableEqVerbosity(x_10, x_40);
if (x_41 == 0)
{
uint8_t x_42; uint8_t x_43; 
x_42 = 0;
x_43 = l_Lake_instDecidableEqVerbosity(x_10, x_42);
if (x_43 == 0)
{
uint8_t x_44; 
x_44 = 1;
x_12 = x_44;
goto block_35;
}
else
{
uint8_t x_45; 
x_45 = 0;
x_12 = x_45;
goto block_35;
}
}
else
{
uint8_t x_46; 
x_46 = 1;
x_12 = x_46;
goto block_35;
}
}
block_35:
{
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_13 = l_Lake_Workspace_runFetchM___rarg___lambda__7___closed__3;
x_14 = lean_box(0);
x_15 = lean_unbox(x_8);
lean_dec(x_8);
x_16 = l_Lake_Workspace_runFetchM___rarg___lambda__6(x_2, x_3, x_4, x_15, x_10, x_12, x_13, x_14, x_9);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_4, 4);
lean_inc(x_17);
x_18 = l_Lake_Workspace_runFetchM___rarg___lambda__7___closed__3;
x_19 = lean_apply_2(x_17, x_18, x_9);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_4, 0);
lean_inc(x_21);
x_22 = lean_apply_1(x_21, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_unbox(x_8);
lean_dec(x_8);
x_26 = l_Lake_Workspace_runFetchM___rarg___lambda__6(x_2, x_3, x_4, x_25, x_10, x_12, x_18, x_23, x_24);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_22);
if (x_27 == 0)
{
return x_22;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_22, 0);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_22);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_19);
if (x_31 == 0)
{
return x_19;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_19, 0);
x_33 = lean_ctor_get(x_19, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_19);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
lean_inc(x_3);
x_5 = l_Lake_mkBuildContext(x_1, x_3, x_4);
x_6 = lean_ctor_get_uint8(x_3, 5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_get_stderr(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lake_Workspace_runFetchM___rarg___lambda__7(x_3, x_2, x_7, x_10, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_5, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
lean_dec(x_5);
x_15 = lean_get_stdout(x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lake_Workspace_runFetchM___rarg___lambda__7(x_3, x_2, x_13, x_16, x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_Workspace_runFetchM___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__7(x_1, x_9, x_3, x_10, x_11, x_6, x_7, x_8);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__8(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lake_Workspace_runFetchM___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_anyMUnsafe_any___at_Lake_Workspace_runFetchM___spec__9(x_5, x_2, x_6, x_7);
lean_dec(x_2);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_3);
lean_dec(x_3);
x_9 = lean_unbox(x_4);
lean_dec(x_4);
x_10 = l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___lambda__1(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = lean_unbox(x_4);
lean_dec(x_4);
x_14 = lean_unbox(x_5);
lean_dec(x_5);
x_15 = l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___lambda__2(x_11, x_2, x_12, x_13, x_14, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = lean_unbox(x_4);
lean_dec(x_4);
x_14 = lean_unbox(x_5);
lean_dec(x_5);
x_15 = lean_unbox(x_8);
lean_dec(x_8);
x_16 = l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___lambda__3(x_1, x_2, x_12, x_13, x_14, x_6, x_7, x_15, x_9, x_10, x_11);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = lean_unbox(x_5);
lean_dec(x_5);
x_16 = l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10(x_1, x_12, x_13, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_8);
lean_dec(x_6);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__11(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__12(x_1, x_8, x_3, x_9, x_10, x_6, x_7);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__13(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lake_Workspace_runFetchM___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_anyMUnsafe_any___at_Lake_Workspace_runFetchM___spec__14(x_5, x_2, x_6, x_7);
lean_dec(x_2);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = lean_unbox(x_4);
lean_dec(x_4);
x_14 = lean_unbox(x_5);
lean_dec(x_5);
x_15 = lean_unbox(x_6);
lean_dec(x_6);
x_16 = lean_unbox(x_8);
lean_dec(x_8);
x_17 = l_Lake_Workspace_runFetchM___rarg___lambda__2(x_1, x_2, x_12, x_13, x_14, x_15, x_7, x_16, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_Workspace_runFetchM___rarg___lambda__3(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_Workspace_runFetchM___rarg___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = lean_unbox(x_7);
lean_dec(x_7);
x_14 = l_Lake_Workspace_runFetchM___rarg___lambda__5(x_1, x_2, x_3, x_11, x_12, x_6, x_13, x_8, x_9, x_10);
lean_dec(x_9);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = lean_unbox(x_5);
lean_dec(x_5);
x_12 = lean_unbox(x_6);
lean_dec(x_6);
x_13 = l_Lake_Workspace_runFetchM___rarg___lambda__6(x_1, x_2, x_3, x_10, x_11, x_12, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_Workspace_runFetchM___rarg(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_io_wait(x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_8, 0);
lean_dec(x_12);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
lean_ctor_set(x_8, 0, x_13);
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_dec(x_8);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_9);
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_8, 0);
lean_dec(x_18);
x_19 = l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__3;
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_19);
return x_8;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_8, 1);
lean_inc(x_20);
lean_dec(x_8);
x_21 = l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__3;
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_5);
if (x_23 == 0)
{
return x_5;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_5, 0);
x_25 = lean_ctor_get(x_5, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_5);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_Workspace_runBuild___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_runBuild___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_Workspace_runFetchM___rarg(x_3, x_1, x_2, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_io_wait(x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_8, 0);
lean_dec(x_12);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
lean_ctor_set(x_8, 0, x_13);
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_dec(x_8);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_9);
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_8, 0);
lean_dec(x_18);
x_19 = l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__3;
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_19);
return x_8;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_8, 1);
lean_inc(x_20);
lean_dec(x_8);
x_21 = l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__3;
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_5);
if (x_23 == 0)
{
return x_5;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_5, 0);
x_25 = lean_ctor_get(x_5, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_5);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_runBuild(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_runBuild___rarg), 4, 0);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Lock(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Index(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Run(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Lock(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Index(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_mkBuildContext___closed__1 = _init_l_Lake_mkBuildContext___closed__1();
lean_mark_persistent(l_Lake_mkBuildContext___closed__1);
l_Lake_mkBuildContext___closed__2 = _init_l_Lake_mkBuildContext___closed__2();
lean_mark_persistent(l_Lake_mkBuildContext___closed__2);
l_Lake_mkBuildContext___closed__3 = _init_l_Lake_mkBuildContext___closed__3();
lean_mark_persistent(l_Lake_mkBuildContext___closed__3);
l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__1 = _init_l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__1();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__1);
l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__2 = _init_l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__2();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__2);
l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__3 = _init_l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__3();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__3);
l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__4 = _init_l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__4();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__4);
l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__5 = _init_l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__5();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__5);
l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___lambda__1___closed__1 = _init_l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___lambda__1___closed__1();
lean_mark_persistent(l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___lambda__1___closed__1);
l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___lambda__2___closed__1 = _init_l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___lambda__2___closed__1();
lean_mark_persistent(l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___lambda__2___closed__1);
l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___closed__1 = _init_l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___closed__1();
lean_mark_persistent(l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___closed__1);
l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___closed__2 = _init_l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___closed__2();
lean_mark_persistent(l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___closed__2);
l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___closed__3 = _init_l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___closed__3();
lean_mark_persistent(l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___closed__3);
l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___closed__4 = _init_l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___closed__4();
lean_mark_persistent(l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___closed__4);
l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___closed__5 = _init_l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___closed__5();
lean_mark_persistent(l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___closed__5);
l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___closed__6 = _init_l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___closed__6();
lean_mark_persistent(l_Nat_foldM_loop___at_Lake_Workspace_runFetchM___spec__10___closed__6);
l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__11___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__11___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__11___closed__1);
l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__1 = _init_l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__1);
l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__1 = _init_l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__1();
lean_mark_persistent(l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__1);
l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__2 = _init_l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__2();
lean_mark_persistent(l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__2);
l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__3 = _init_l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__3();
lean_mark_persistent(l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__3);
l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__4 = _init_l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__4();
lean_mark_persistent(l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__4);
l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__5 = _init_l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__5();
lean_mark_persistent(l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__5);
l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__6 = _init_l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__6();
lean_mark_persistent(l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__6);
l_Lake_Workspace_runFetchM___rarg___lambda__4___closed__1 = _init_l_Lake_Workspace_runFetchM___rarg___lambda__4___closed__1();
lean_mark_persistent(l_Lake_Workspace_runFetchM___rarg___lambda__4___closed__1);
l_Lake_Workspace_runFetchM___rarg___lambda__7___closed__1 = _init_l_Lake_Workspace_runFetchM___rarg___lambda__7___closed__1();
lean_mark_persistent(l_Lake_Workspace_runFetchM___rarg___lambda__7___closed__1);
l_Lake_Workspace_runFetchM___rarg___lambda__7___closed__2 = _init_l_Lake_Workspace_runFetchM___rarg___lambda__7___closed__2();
lean_mark_persistent(l_Lake_Workspace_runFetchM___rarg___lambda__7___closed__2);
l_Lake_Workspace_runFetchM___rarg___lambda__7___closed__3 = _init_l_Lake_Workspace_runFetchM___rarg___lambda__7___closed__3();
lean_mark_persistent(l_Lake_Workspace_runFetchM___rarg___lambda__7___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

// Lean compiler output
// Module: Lake.Config.Cache
// Imports: Lake.Util.Log Lake.Config.Artifact Lake.Build.Trace
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lake_CacheMap_save_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_insertCore___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_lock(lean_object*, uint8_t, lean_object*);
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__2;
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_save(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0;
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
static lean_object* l_Lake_Cache_getArtifact_x3f___closed__1;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lake_CacheMap_save_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_CacheMap_save_spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__1(lean_object*, uint64_t, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_fromJson_x3f___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__0(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_metadata(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lake_CacheMap_get_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_artifactDir(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_save___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_insertCore(uint64_t, lean_object*, lean_object*);
static lean_object* l_Lake_instInhabitedCache___closed__0;
lean_object* l_System_FilePath_pathExists(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__1;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_insert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheRef_get_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lake_CacheMap_save_spec__3___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__4;
LEAN_EXPORT lean_object* l_Lake_instInhabitedCache;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_UInt64_fromJson_x3f(lean_object*);
lean_object* l_Lake_createParentDirs(lean_object*, lean_object*);
lean_object* l_Lake_instHashableHash___lam__0___boxed(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop___closed__1;
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_IO_FS_Handle_putStrLn(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
static lean_object* l_Lake_Cache_inputsDir___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_get_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_CacheMap_save_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_CacheMap_save___closed__0;
lean_object* lean_uint64_to_nat(uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_CacheMap_save_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Cache_isDisabled(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifact_x3f(lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lake_CacheMap_get_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_get_x3f(uint64_t, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__1___redArg(uint64_t, lean_object*);
static lean_object* l_Lake_Cache_artifactDir___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_toJson___at___Lake_CacheMap_save_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lake_CacheMap_get_x3f_spec__0___redArg(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_artifactPath___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t, lean_object*);
static lean_object* l_Lake_CacheMap_load___closed__0;
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifact_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_insert___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_get_line(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lake_Cache_inputsFile___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lake_CacheMap_save___closed__1;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Prod_fromJson_x3f___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__0___closed__0;
static lean_object* l_Lake_Cache_artifactPath___closed__0;
LEAN_EXPORT lean_object* l_Lake_CacheRef_insert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_CacheMap_save_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lake_CacheMap_get_x3f_spec__0(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__2_spec__2_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheRef_insert___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheRef_insert(lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__5(lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_insert___redArg(lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_inputsFile(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_load(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_bignumToJson(lean_object*);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__2_spec__2_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__5___redArg(uint64_t, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Prod_fromJson_x3f___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__0___closed__1;
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lake_Cache_getArtifact_x3f___closed__0;
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Prod_toJson___at___Lake_CacheMap_save_spec__0___closed__0;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop___closed__0;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheRef_get_x3f(uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lake_CacheMap_save_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_artifactPath(lean_object*, uint64_t, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__3;
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_isDisabled___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lake_CacheMap_save_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lake_beqHash____x40_Lake_Build_Trace___hyg_476____boxed(lean_object*, lean_object*);
lean_object* lean_io_prim_handle_rewind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_inputsDir(lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_CacheMap_insert(lean_object*, lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheRef_insert___redArg(lean_object*, uint64_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lake_instInhabitedCache___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedCache() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instInhabitedCache___closed__0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lake_Cache_isDisabled(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_string_utf8_byte_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_isDisabled___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_Cache_isDisabled(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Cache_artifactDir___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("artifacts", 9, 9);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_artifactDir(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lake_Cache_artifactDir___closed__0;
x_3 = l_System_FilePath_join(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Cache_artifactPath___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_artifactPath(lean_object* x_1, uint64_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = l_Lake_Cache_artifactDir___closed__0;
x_5 = l_System_FilePath_join(x_1, x_4);
x_6 = lean_string_utf8_byte_size(x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_6, x_7);
lean_dec(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_uint64_to_nat(x_2);
x_10 = l_Nat_reprFast(x_9);
x_11 = l_Lake_Cache_artifactPath___closed__0;
x_12 = lean_string_append(x_10, x_11);
x_13 = lean_string_append(x_12, x_3);
x_14 = l_System_FilePath_join(x_5, x_13);
lean_dec_ref(x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_uint64_to_nat(x_2);
x_16 = l_Nat_reprFast(x_15);
x_17 = l_System_FilePath_join(x_5, x_16);
lean_dec_ref(x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_artifactPath___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l_Lake_Cache_artifactPath(x_1, x_4, x_3);
lean_dec_ref(x_3);
return x_5;
}
}
static lean_object* _init_l_Lake_Cache_getArtifact_x3f___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Cache_getArtifact_x3f___closed__1() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = l_Lake_Cache_getArtifact_x3f___closed__0;
x_3 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint32(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifact_x3f(lean_object* x_1, uint64_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lake_Cache_artifactPath(x_1, x_2, x_3);
x_6 = lean_io_metadata(x_5, x_4);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_8, 1);
lean_inc_ref(x_9);
lean_dec(x_8);
lean_inc_ref(x_5);
x_10 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_5);
lean_ctor_set(x_10, 2, x_9);
lean_ctor_set_uint64(x_10, sizeof(void*)*3, x_2);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_6, 0, x_11);
return x_6;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_6);
x_14 = lean_ctor_get(x_12, 1);
lean_inc_ref(x_14);
lean_dec(x_12);
lean_inc_ref(x_5);
x_15 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 2, x_14);
lean_ctor_set_uint64(x_15, sizeof(void*)*3, x_2);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_13);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_6, 1);
lean_inc(x_18);
lean_dec_ref(x_6);
x_19 = l_System_FilePath_pathExists(x_5, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
uint8_t x_22; 
lean_dec_ref(x_5);
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_19, 0);
lean_dec(x_23);
x_24 = lean_box(0);
lean_ctor_set(x_19, 0, x_24);
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_dec(x_19);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_19);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_19, 0);
lean_dec(x_29);
x_30 = l_Lake_Cache_getArtifact_x3f___closed__1;
lean_inc_ref(x_5);
x_31 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_31, 0, x_5);
lean_ctor_set(x_31, 1, x_5);
lean_ctor_set(x_31, 2, x_30);
lean_ctor_set_uint64(x_31, sizeof(void*)*3, x_2);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_19, 0, x_32);
return x_19;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_19, 1);
lean_inc(x_33);
lean_dec(x_19);
x_34 = l_Lake_Cache_getArtifact_x3f___closed__1;
lean_inc_ref(x_5);
x_35 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_35, 0, x_5);
lean_ctor_set(x_35, 1, x_5);
lean_ctor_set(x_35, 2, x_34);
lean_ctor_set_uint64(x_35, sizeof(void*)*3, x_2);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_33);
return x_37;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifact_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_6 = l_Lake_Cache_getArtifact_x3f(x_1, x_5, x_3, x_4);
lean_dec_ref(x_3);
return x_6;
}
}
static lean_object* _init_l_Lake_Cache_inputsDir___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("inputs", 6, 6);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_inputsDir(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lake_Cache_inputsDir___closed__0;
x_3 = l_System_FilePath_join(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Cache_inputsFile___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".jsonl", 6, 6);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_inputsFile(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_Lake_Cache_inputsDir___closed__0;
x_4 = l_System_FilePath_join(x_2, x_3);
x_5 = l_Lake_Cache_inputsFile___closed__0;
x_6 = lean_string_append(x_1, x_5);
x_7 = l_System_FilePath_join(x_4, x_6);
lean_dec_ref(x_6);
return x_7;
}
}
static lean_object* _init_l_Prod_fromJson_x3f___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected pair, got '", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Prod_fromJson_x3f___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Prod_fromJson_x3f___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_11);
x_12 = lean_array_get_size(x_11);
x_13 = lean_unsigned_to_nat(2u);
x_14 = lean_nat_dec_eq(x_12, x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_dec_ref(x_11);
x_2 = x_1;
goto block_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec_ref(x_1);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_fget(x_11, x_15);
x_17 = l_UInt64_fromJson_x3f(x_16);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec_ref(x_11);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_17);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_17, 0);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_array_fget(x_11, x_23);
lean_dec_ref(x_11);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_17, 0, x_25);
return x_17;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_17, 0);
lean_inc(x_26);
lean_dec(x_17);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_array_fget(x_11, x_27);
lean_dec_ref(x_11);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
}
}
else
{
x_2 = x_1;
goto block_10;
}
block_10:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = l_Prod_fromJson_x3f___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__0___closed__0;
x_4 = lean_unsigned_to_nat(80u);
x_5 = l_Lean_Json_pretty(x_2, x_4);
x_6 = lean_string_append(x_3, x_5);
lean_dec_ref(x_5);
x_7 = l_Prod_fromJson_x3f___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__0___closed__1;
x_8 = lean_string_append(x_6, x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__1___redArg(uint64_t x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; uint64_t x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_unbox_uint64(x_4);
x_7 = lean_uint64_dec_eq(x_6, x_1);
if (x_7 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_7;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__1(lean_object* x_1, uint64_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__2_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = 32;
x_8 = lean_unbox_uint64(x_4);
x_9 = lean_uint64_shift_right(x_8, x_7);
x_10 = lean_unbox_uint64(x_4);
x_11 = lean_uint64_xor(x_10, x_9);
x_12 = 16;
x_13 = lean_uint64_shift_right(x_11, x_12);
x_14 = lean_uint64_xor(x_11, x_13);
x_15 = lean_uint64_to_usize(x_14);
x_16 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_17 = 1;
x_18 = lean_usize_sub(x_16, x_17);
x_19 = lean_usize_land(x_15, x_18);
x_20 = lean_array_uget(x_1, x_19);
lean_ctor_set(x_2, 2, x_20);
x_21 = lean_array_uset(x_1, x_19, x_2);
x_1 = x_21;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; size_t x_35; size_t x_36; size_t x_37; size_t x_38; size_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_23 = lean_ctor_get(x_2, 0);
x_24 = lean_ctor_get(x_2, 1);
x_25 = lean_ctor_get(x_2, 2);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_2);
x_26 = lean_array_get_size(x_1);
x_27 = 32;
x_28 = lean_unbox_uint64(x_23);
x_29 = lean_uint64_shift_right(x_28, x_27);
x_30 = lean_unbox_uint64(x_23);
x_31 = lean_uint64_xor(x_30, x_29);
x_32 = 16;
x_33 = lean_uint64_shift_right(x_31, x_32);
x_34 = lean_uint64_xor(x_31, x_33);
x_35 = lean_uint64_to_usize(x_34);
x_36 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_37 = 1;
x_38 = lean_usize_sub(x_36, x_37);
x_39 = lean_usize_land(x_35, x_38);
x_40 = lean_array_uget(x_1, x_39);
x_41 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_41, 0, x_23);
lean_ctor_set(x_41, 1, x_24);
lean_ctor_set(x_41, 2, x_40);
x_42 = lean_array_uset(x_1, x_39, x_41);
x_1 = x_42;
x_2 = x_25;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__2_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__2_spec__2_spec__2___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__2_spec__2_spec__2___redArg(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__2_spec__2___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__2___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
lean_dec(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__2_spec__2___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__2___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__5___redArg(uint64_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_unbox_uint64(x_5);
x_9 = lean_uint64_dec_eq(x_8, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__5___redArg(x_1, x_2, x_7);
lean_ctor_set(x_3, 2, x_10);
return x_3;
}
else
{
lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
x_11 = lean_box_uint64(x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_11);
return x_3;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint64_t x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
x_14 = lean_ctor_get(x_3, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_15 = lean_unbox_uint64(x_12);
x_16 = lean_uint64_dec_eq(x_15, x_1);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__5___redArg(x_1, x_2, x_14);
x_18 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_13);
lean_ctor_set(x_18, 2, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_13);
lean_dec(x_12);
x_19 = lean_box_uint64(x_1);
x_20 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_2);
lean_ctor_set(x_20, 2, x_14);
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__5(lean_object* x_1, uint64_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__5___redArg(x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": invalid JSON on line ", 23, 23);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": ", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_io_prim_handle_get_line(x_1, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_26 = lean_string_utf8_byte_size(x_9);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_nat_dec_eq(x_26, x_27);
lean_dec(x_26);
if (x_28 == 0)
{
lean_object* x_29; 
lean_free_object(x_7);
x_29 = l_Lean_Json_parse(x_9);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_11 = x_30;
goto block_25;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
lean_dec_ref(x_29);
x_32 = l_Prod_fromJson_x3f___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__0(x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_11 = x_33;
goto block_25;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec_ref(x_32);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = !lean_is_exclusive(x_4);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; uint64_t x_46; uint64_t x_47; uint64_t x_48; uint64_t x_49; uint64_t x_50; size_t x_51; size_t x_52; size_t x_53; size_t x_54; size_t x_55; lean_object* x_56; uint64_t x_57; uint8_t x_58; 
x_38 = lean_ctor_get(x_4, 0);
x_39 = lean_ctor_get(x_4, 1);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_add(x_3, x_40);
lean_dec(x_3);
x_42 = lean_array_get_size(x_39);
x_43 = 32;
x_44 = lean_unbox_uint64(x_35);
x_45 = lean_uint64_shift_right(x_44, x_43);
x_46 = lean_unbox_uint64(x_35);
x_47 = lean_uint64_xor(x_46, x_45);
x_48 = 16;
x_49 = lean_uint64_shift_right(x_47, x_48);
x_50 = lean_uint64_xor(x_47, x_49);
x_51 = lean_uint64_to_usize(x_50);
x_52 = lean_usize_of_nat(x_42);
lean_dec(x_42);
x_53 = 1;
x_54 = lean_usize_sub(x_52, x_53);
x_55 = lean_usize_land(x_51, x_54);
x_56 = lean_array_uget(x_39, x_55);
x_57 = lean_unbox_uint64(x_35);
x_58 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__1___redArg(x_57, x_56);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_59 = lean_nat_add(x_38, x_40);
lean_dec(x_38);
x_60 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_60, 0, x_35);
lean_ctor_set(x_60, 1, x_36);
lean_ctor_set(x_60, 2, x_56);
x_61 = lean_array_uset(x_39, x_55, x_60);
x_62 = lean_unsigned_to_nat(4u);
x_63 = lean_nat_mul(x_59, x_62);
x_64 = lean_unsigned_to_nat(3u);
x_65 = lean_nat_div(x_63, x_64);
lean_dec(x_63);
x_66 = lean_array_get_size(x_61);
x_67 = lean_nat_dec_le(x_65, x_66);
lean_dec(x_66);
lean_dec(x_65);
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__2___redArg(x_61);
lean_ctor_set(x_4, 1, x_68);
lean_ctor_set(x_4, 0, x_59);
x_3 = x_41;
x_6 = x_10;
goto _start;
}
else
{
lean_ctor_set(x_4, 1, x_61);
lean_ctor_set(x_4, 0, x_59);
x_3 = x_41;
x_6 = x_10;
goto _start;
}
}
else
{
lean_object* x_71; lean_object* x_72; uint64_t x_73; lean_object* x_74; lean_object* x_75; 
x_71 = lean_box(0);
x_72 = lean_array_uset(x_39, x_55, x_71);
x_73 = lean_unbox_uint64(x_35);
lean_dec(x_35);
x_74 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__5___redArg(x_73, x_36, x_56);
x_75 = lean_array_uset(x_72, x_55, x_74);
lean_ctor_set(x_4, 1, x_75);
x_3 = x_41;
x_6 = x_10;
goto _start;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint64_t x_82; uint64_t x_83; uint64_t x_84; uint64_t x_85; uint64_t x_86; uint64_t x_87; uint64_t x_88; uint64_t x_89; size_t x_90; size_t x_91; size_t x_92; size_t x_93; size_t x_94; lean_object* x_95; uint64_t x_96; uint8_t x_97; 
x_77 = lean_ctor_get(x_4, 0);
x_78 = lean_ctor_get(x_4, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_4);
x_79 = lean_unsigned_to_nat(1u);
x_80 = lean_nat_add(x_3, x_79);
lean_dec(x_3);
x_81 = lean_array_get_size(x_78);
x_82 = 32;
x_83 = lean_unbox_uint64(x_35);
x_84 = lean_uint64_shift_right(x_83, x_82);
x_85 = lean_unbox_uint64(x_35);
x_86 = lean_uint64_xor(x_85, x_84);
x_87 = 16;
x_88 = lean_uint64_shift_right(x_86, x_87);
x_89 = lean_uint64_xor(x_86, x_88);
x_90 = lean_uint64_to_usize(x_89);
x_91 = lean_usize_of_nat(x_81);
lean_dec(x_81);
x_92 = 1;
x_93 = lean_usize_sub(x_91, x_92);
x_94 = lean_usize_land(x_90, x_93);
x_95 = lean_array_uget(x_78, x_94);
x_96 = lean_unbox_uint64(x_35);
x_97 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__1___redArg(x_96, x_95);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_98 = lean_nat_add(x_77, x_79);
lean_dec(x_77);
x_99 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_99, 0, x_35);
lean_ctor_set(x_99, 1, x_36);
lean_ctor_set(x_99, 2, x_95);
x_100 = lean_array_uset(x_78, x_94, x_99);
x_101 = lean_unsigned_to_nat(4u);
x_102 = lean_nat_mul(x_98, x_101);
x_103 = lean_unsigned_to_nat(3u);
x_104 = lean_nat_div(x_102, x_103);
lean_dec(x_102);
x_105 = lean_array_get_size(x_100);
x_106 = lean_nat_dec_le(x_104, x_105);
lean_dec(x_105);
lean_dec(x_104);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; 
x_107 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__2___redArg(x_100);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_98);
lean_ctor_set(x_108, 1, x_107);
x_3 = x_80;
x_4 = x_108;
x_6 = x_10;
goto _start;
}
else
{
lean_object* x_110; 
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_98);
lean_ctor_set(x_110, 1, x_100);
x_3 = x_80;
x_4 = x_110;
x_6 = x_10;
goto _start;
}
}
else
{
lean_object* x_112; lean_object* x_113; uint64_t x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_112 = lean_box(0);
x_113 = lean_array_uset(x_78, x_94, x_112);
x_114 = lean_unbox_uint64(x_35);
lean_dec(x_35);
x_115 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__5___redArg(x_114, x_36, x_95);
x_116 = lean_array_uset(x_113, x_94, x_115);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_77);
lean_ctor_set(x_117, 1, x_116);
x_3 = x_80;
x_4 = x_117;
x_6 = x_10;
goto _start;
}
}
}
}
}
else
{
lean_object* x_119; 
lean_dec(x_9);
lean_dec(x_3);
lean_dec_ref(x_2);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_4);
lean_ctor_set(x_119, 1, x_5);
lean_ctor_set(x_7, 0, x_119);
return x_7;
}
block_25:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_12 = l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop___closed__0;
lean_inc_ref(x_2);
x_13 = lean_string_append(x_2, x_12);
lean_inc(x_3);
x_14 = l_Nat_reprFast(x_3);
x_15 = lean_string_append(x_13, x_14);
lean_dec_ref(x_14);
x_16 = l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop___closed__1;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_string_append(x_17, x_11);
lean_dec_ref(x_11);
x_19 = 2;
x_20 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*1, x_19);
x_21 = lean_array_push(x_5, x_20);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_3, x_22);
lean_dec(x_3);
x_3 = x_23;
x_5 = x_21;
x_6 = x_10;
goto _start;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_120 = lean_ctor_get(x_7, 0);
x_121 = lean_ctor_get(x_7, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_7);
x_137 = lean_string_utf8_byte_size(x_120);
x_138 = lean_unsigned_to_nat(0u);
x_139 = lean_nat_dec_eq(x_137, x_138);
lean_dec(x_137);
if (x_139 == 0)
{
lean_object* x_140; 
x_140 = l_Lean_Json_parse(x_120);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
lean_dec_ref(x_140);
x_122 = x_141;
goto block_136;
}
else
{
lean_object* x_142; lean_object* x_143; 
x_142 = lean_ctor_get(x_140, 0);
lean_inc(x_142);
lean_dec_ref(x_140);
x_143 = l_Prod_fromJson_x3f___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__0(x_142);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
lean_dec_ref(x_143);
x_122 = x_144;
goto block_136;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint64_t x_154; uint64_t x_155; uint64_t x_156; uint64_t x_157; uint64_t x_158; uint64_t x_159; uint64_t x_160; uint64_t x_161; size_t x_162; size_t x_163; size_t x_164; size_t x_165; size_t x_166; lean_object* x_167; uint64_t x_168; uint8_t x_169; 
x_145 = lean_ctor_get(x_143, 0);
lean_inc(x_145);
lean_dec_ref(x_143);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec(x_145);
x_148 = lean_ctor_get(x_4, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_149);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_150 = x_4;
} else {
 lean_dec_ref(x_4);
 x_150 = lean_box(0);
}
x_151 = lean_unsigned_to_nat(1u);
x_152 = lean_nat_add(x_3, x_151);
lean_dec(x_3);
x_153 = lean_array_get_size(x_149);
x_154 = 32;
x_155 = lean_unbox_uint64(x_146);
x_156 = lean_uint64_shift_right(x_155, x_154);
x_157 = lean_unbox_uint64(x_146);
x_158 = lean_uint64_xor(x_157, x_156);
x_159 = 16;
x_160 = lean_uint64_shift_right(x_158, x_159);
x_161 = lean_uint64_xor(x_158, x_160);
x_162 = lean_uint64_to_usize(x_161);
x_163 = lean_usize_of_nat(x_153);
lean_dec(x_153);
x_164 = 1;
x_165 = lean_usize_sub(x_163, x_164);
x_166 = lean_usize_land(x_162, x_165);
x_167 = lean_array_uget(x_149, x_166);
x_168 = lean_unbox_uint64(x_146);
x_169 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__1___redArg(x_168, x_167);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_170 = lean_nat_add(x_148, x_151);
lean_dec(x_148);
x_171 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_171, 0, x_146);
lean_ctor_set(x_171, 1, x_147);
lean_ctor_set(x_171, 2, x_167);
x_172 = lean_array_uset(x_149, x_166, x_171);
x_173 = lean_unsigned_to_nat(4u);
x_174 = lean_nat_mul(x_170, x_173);
x_175 = lean_unsigned_to_nat(3u);
x_176 = lean_nat_div(x_174, x_175);
lean_dec(x_174);
x_177 = lean_array_get_size(x_172);
x_178 = lean_nat_dec_le(x_176, x_177);
lean_dec(x_177);
lean_dec(x_176);
if (x_178 == 0)
{
lean_object* x_179; lean_object* x_180; 
x_179 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__2___redArg(x_172);
if (lean_is_scalar(x_150)) {
 x_180 = lean_alloc_ctor(0, 2, 0);
} else {
 x_180 = x_150;
}
lean_ctor_set(x_180, 0, x_170);
lean_ctor_set(x_180, 1, x_179);
x_3 = x_152;
x_4 = x_180;
x_6 = x_121;
goto _start;
}
else
{
lean_object* x_182; 
if (lean_is_scalar(x_150)) {
 x_182 = lean_alloc_ctor(0, 2, 0);
} else {
 x_182 = x_150;
}
lean_ctor_set(x_182, 0, x_170);
lean_ctor_set(x_182, 1, x_172);
x_3 = x_152;
x_4 = x_182;
x_6 = x_121;
goto _start;
}
}
else
{
lean_object* x_184; lean_object* x_185; uint64_t x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_184 = lean_box(0);
x_185 = lean_array_uset(x_149, x_166, x_184);
x_186 = lean_unbox_uint64(x_146);
lean_dec(x_146);
x_187 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__5___redArg(x_186, x_147, x_167);
x_188 = lean_array_uset(x_185, x_166, x_187);
if (lean_is_scalar(x_150)) {
 x_189 = lean_alloc_ctor(0, 2, 0);
} else {
 x_189 = x_150;
}
lean_ctor_set(x_189, 0, x_148);
lean_ctor_set(x_189, 1, x_188);
x_3 = x_152;
x_4 = x_189;
x_6 = x_121;
goto _start;
}
}
}
}
else
{
lean_object* x_191; lean_object* x_192; 
lean_dec(x_120);
lean_dec(x_3);
lean_dec_ref(x_2);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_4);
lean_ctor_set(x_191, 1, x_5);
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_121);
return x_192;
}
block_136:
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_123 = l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop___closed__0;
lean_inc_ref(x_2);
x_124 = lean_string_append(x_2, x_123);
lean_inc(x_3);
x_125 = l_Nat_reprFast(x_3);
x_126 = lean_string_append(x_124, x_125);
lean_dec_ref(x_125);
x_127 = l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop___closed__1;
x_128 = lean_string_append(x_126, x_127);
x_129 = lean_string_append(x_128, x_122);
lean_dec_ref(x_122);
x_130 = 2;
x_131 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set_uint8(x_131, sizeof(void*)*1, x_130);
x_132 = lean_array_push(x_5, x_131);
x_133 = lean_unsigned_to_nat(1u);
x_134 = lean_nat_add(x_3, x_133);
lean_dec(x_3);
x_3 = x_134;
x_5 = x_132;
x_6 = x_121;
goto _start;
}
}
}
else
{
uint8_t x_193; 
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_193 = !lean_is_exclusive(x_7);
if (x_193 == 0)
{
lean_object* x_194; lean_object* x_195; uint8_t x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_194 = lean_ctor_get(x_7, 0);
x_195 = lean_io_error_to_string(x_194);
x_196 = 3;
x_197 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set_uint8(x_197, sizeof(void*)*1, x_196);
x_198 = lean_array_get_size(x_5);
x_199 = lean_array_push(x_5, x_197);
x_200 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_199);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 0, x_200);
return x_7;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_201 = lean_ctor_get(x_7, 0);
x_202 = lean_ctor_get(x_7, 1);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_7);
x_203 = lean_io_error_to_string(x_201);
x_204 = 3;
x_205 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_205, 0, x_203);
lean_ctor_set_uint8(x_205, sizeof(void*)*1, x_204);
x_206 = lean_array_get_size(x_5);
x_207 = lean_array_push(x_5, x_205);
x_208 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_207);
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_202);
return x_209;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__1___redArg(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__1(x_1, x_4, x_3);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__5___redArg(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_6 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__5(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__1;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__2;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__4;
x_7 = l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop(x_1, x_2, x_5, x_6, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l_Lake_CacheMap_load___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": failed to open file: ", 23, 23);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_load(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = 0;
x_5 = lean_io_prim_handle_mk(x_1, x_4, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = 0;
x_9 = lean_io_prim_handle_lock(x_6, x_8, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__4;
x_13 = l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop(x_6, x_1, x_11, x_12, x_2, x_10);
lean_dec(x_6);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_6);
lean_dec_ref(x_1);
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_io_error_to_string(x_15);
x_17 = 3;
x_18 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_17);
x_19 = lean_array_get_size(x_2);
x_20 = lean_array_push(x_2, x_18);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set_tag(x_9, 0);
lean_ctor_set(x_9, 0, x_21);
return x_9;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_22 = lean_ctor_get(x_9, 0);
x_23 = lean_ctor_get(x_9, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_9);
x_24 = lean_io_error_to_string(x_22);
x_25 = 3;
x_26 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_25);
x_27 = lean_array_get_size(x_2);
x_28 = lean_array_push(x_2, x_26);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_23);
return x_30;
}
}
}
else
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_5, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 11)
{
uint8_t x_32; 
lean_dec_ref(x_31);
lean_dec_ref(x_1);
x_32 = !lean_is_exclusive(x_5);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_5, 0);
lean_dec(x_33);
x_34 = l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__4;
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_2);
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 0, x_35);
return x_5;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_5, 1);
lean_inc(x_36);
lean_dec(x_5);
x_37 = l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__4;
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_2);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_5);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_41 = lean_ctor_get(x_5, 0);
lean_dec(x_41);
x_42 = l_Lake_CacheMap_load___closed__0;
x_43 = lean_string_append(x_1, x_42);
x_44 = lean_io_error_to_string(x_31);
x_45 = lean_string_append(x_43, x_44);
lean_dec_ref(x_44);
x_46 = 3;
x_47 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set_uint8(x_47, sizeof(void*)*1, x_46);
x_48 = lean_array_get_size(x_2);
x_49 = lean_array_push(x_2, x_47);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 0, x_50);
return x_5;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_51 = lean_ctor_get(x_5, 1);
lean_inc(x_51);
lean_dec(x_5);
x_52 = l_Lake_CacheMap_load___closed__0;
x_53 = lean_string_append(x_1, x_52);
x_54 = lean_io_error_to_string(x_31);
x_55 = lean_string_append(x_53, x_54);
lean_dec_ref(x_54);
x_56 = 3;
x_57 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set_uint8(x_57, sizeof(void*)*1, x_56);
x_58 = lean_array_get_size(x_2);
x_59 = lean_array_push(x_2, x_57);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_51);
return x_61;
}
}
}
}
}
static lean_object* _init_l_Prod_toJson___at___Lake_CacheMap_save_spec__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Prod_toJson___at___Lake_CacheMap_save_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint64_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = lean_uint64_to_nat(x_4);
x_6 = l_Lean_bignumToJson(x_5);
x_7 = l_Prod_toJson___at___Lake_CacheMap_save_spec__0___closed__0;
x_8 = lean_array_push(x_7, x_6);
x_9 = lean_array_push(x_8, x_3);
x_10 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lake_CacheMap_save_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_4);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
x_10 = lean_ctor_get(x_3, 2);
lean_inc(x_9);
lean_inc(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_9);
x_12 = l_Prod_toJson___at___Lake_CacheMap_save_spec__0(x_11);
x_13 = l_Lean_Json_compress(x_12);
x_14 = l_IO_FS_Handle_putStrLn(x_1, x_13, x_5);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_2 = x_15;
x_3 = x_10;
x_5 = x_16;
goto _start;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_io_error_to_string(x_19);
x_21 = 3;
x_22 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*1, x_21);
x_23 = lean_array_get_size(x_4);
x_24 = lean_array_push(x_4, x_22);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set_tag(x_14, 0);
lean_ctor_set(x_14, 0, x_25);
return x_14;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_26 = lean_ctor_get(x_14, 0);
x_27 = lean_ctor_get(x_14, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_14);
x_28 = lean_io_error_to_string(x_26);
x_29 = 3;
x_30 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*1, x_29);
x_31 = lean_array_get_size(x_4);
x_32 = lean_array_push(x_4, x_30);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_27);
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_CacheMap_save_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_3, x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_array_uget(x_2, x_3);
x_10 = lean_box(0);
x_11 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Lake_CacheMap_save_spec__1(x_1, x_10, x_9, x_6, x_7);
lean_dec(x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec_ref(x_12);
x_16 = 1;
x_17 = lean_usize_add(x_3, x_16);
x_3 = x_17;
x_5 = x_14;
x_6 = x_15;
x_7 = x_13;
goto _start;
}
else
{
lean_dec_ref(x_12);
return x_11;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_5);
lean_ctor_set(x_19, 1, x_6);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_7);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lake_CacheMap_save_spec__3___redArg(lean_object* x_1, lean_object* x_2) {
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
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; size_t x_19; size_t x_20; size_t x_21; size_t x_22; size_t x_23; lean_object* x_24; uint64_t x_25; uint8_t x_26; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_array_get_size(x_9);
x_11 = 32;
x_12 = lean_unbox_uint64(x_5);
x_13 = lean_uint64_shift_right(x_12, x_11);
x_14 = lean_unbox_uint64(x_5);
x_15 = lean_uint64_xor(x_14, x_13);
x_16 = 16;
x_17 = lean_uint64_shift_right(x_15, x_16);
x_18 = lean_uint64_xor(x_15, x_17);
x_19 = lean_uint64_to_usize(x_18);
x_20 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_21 = 1;
x_22 = lean_usize_sub(x_20, x_21);
x_23 = lean_usize_land(x_19, x_22);
x_24 = lean_array_uget(x_9, x_23);
x_25 = lean_unbox_uint64(x_5);
x_26 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__1___redArg(x_25, x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_8, x_27);
lean_dec(x_8);
lean_ctor_set(x_2, 2, x_24);
x_29 = lean_array_uset(x_9, x_23, x_2);
x_30 = lean_unsigned_to_nat(4u);
x_31 = lean_nat_mul(x_28, x_30);
x_32 = lean_unsigned_to_nat(3u);
x_33 = lean_nat_div(x_31, x_32);
lean_dec(x_31);
x_34 = lean_array_get_size(x_29);
x_35 = lean_nat_dec_le(x_33, x_34);
lean_dec(x_34);
lean_dec(x_33);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__2___redArg(x_29);
lean_ctor_set(x_1, 1, x_36);
lean_ctor_set(x_1, 0, x_28);
x_2 = x_7;
goto _start;
}
else
{
lean_ctor_set(x_1, 1, x_29);
lean_ctor_set(x_1, 0, x_28);
x_2 = x_7;
goto _start;
}
}
else
{
lean_object* x_39; lean_object* x_40; uint64_t x_41; lean_object* x_42; lean_object* x_43; 
lean_free_object(x_2);
x_39 = lean_box(0);
x_40 = lean_array_uset(x_9, x_23, x_39);
x_41 = lean_unbox_uint64(x_5);
lean_dec(x_5);
x_42 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__5___redArg(x_41, x_6, x_24);
x_43 = lean_array_uset(x_40, x_23, x_42);
lean_ctor_set(x_1, 1, x_43);
x_2 = x_7;
goto _start;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint64_t x_51; uint64_t x_52; uint64_t x_53; uint64_t x_54; uint64_t x_55; uint64_t x_56; uint64_t x_57; uint64_t x_58; size_t x_59; size_t x_60; size_t x_61; size_t x_62; size_t x_63; lean_object* x_64; uint64_t x_65; uint8_t x_66; 
x_45 = lean_ctor_get(x_2, 0);
x_46 = lean_ctor_get(x_2, 1);
x_47 = lean_ctor_get(x_2, 2);
x_48 = lean_ctor_get(x_1, 0);
x_49 = lean_ctor_get(x_1, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_1);
x_50 = lean_array_get_size(x_49);
x_51 = 32;
x_52 = lean_unbox_uint64(x_45);
x_53 = lean_uint64_shift_right(x_52, x_51);
x_54 = lean_unbox_uint64(x_45);
x_55 = lean_uint64_xor(x_54, x_53);
x_56 = 16;
x_57 = lean_uint64_shift_right(x_55, x_56);
x_58 = lean_uint64_xor(x_55, x_57);
x_59 = lean_uint64_to_usize(x_58);
x_60 = lean_usize_of_nat(x_50);
lean_dec(x_50);
x_61 = 1;
x_62 = lean_usize_sub(x_60, x_61);
x_63 = lean_usize_land(x_59, x_62);
x_64 = lean_array_uget(x_49, x_63);
x_65 = lean_unbox_uint64(x_45);
x_66 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__1___redArg(x_65, x_64);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_67 = lean_unsigned_to_nat(1u);
x_68 = lean_nat_add(x_48, x_67);
lean_dec(x_48);
lean_ctor_set(x_2, 2, x_64);
x_69 = lean_array_uset(x_49, x_63, x_2);
x_70 = lean_unsigned_to_nat(4u);
x_71 = lean_nat_mul(x_68, x_70);
x_72 = lean_unsigned_to_nat(3u);
x_73 = lean_nat_div(x_71, x_72);
lean_dec(x_71);
x_74 = lean_array_get_size(x_69);
x_75 = lean_nat_dec_le(x_73, x_74);
lean_dec(x_74);
lean_dec(x_73);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__2___redArg(x_69);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_68);
lean_ctor_set(x_77, 1, x_76);
x_1 = x_77;
x_2 = x_47;
goto _start;
}
else
{
lean_object* x_79; 
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_68);
lean_ctor_set(x_79, 1, x_69);
x_1 = x_79;
x_2 = x_47;
goto _start;
}
}
else
{
lean_object* x_81; lean_object* x_82; uint64_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_free_object(x_2);
x_81 = lean_box(0);
x_82 = lean_array_uset(x_49, x_63, x_81);
x_83 = lean_unbox_uint64(x_45);
lean_dec(x_45);
x_84 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__5___redArg(x_83, x_46, x_64);
x_85 = lean_array_uset(x_82, x_63, x_84);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_48);
lean_ctor_set(x_86, 1, x_85);
x_1 = x_86;
x_2 = x_47;
goto _start;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint64_t x_95; uint64_t x_96; uint64_t x_97; uint64_t x_98; uint64_t x_99; uint64_t x_100; uint64_t x_101; uint64_t x_102; size_t x_103; size_t x_104; size_t x_105; size_t x_106; size_t x_107; lean_object* x_108; uint64_t x_109; uint8_t x_110; 
x_88 = lean_ctor_get(x_2, 0);
x_89 = lean_ctor_get(x_2, 1);
x_90 = lean_ctor_get(x_2, 2);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_2);
x_91 = lean_ctor_get(x_1, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_92);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_93 = x_1;
} else {
 lean_dec_ref(x_1);
 x_93 = lean_box(0);
}
x_94 = lean_array_get_size(x_92);
x_95 = 32;
x_96 = lean_unbox_uint64(x_88);
x_97 = lean_uint64_shift_right(x_96, x_95);
x_98 = lean_unbox_uint64(x_88);
x_99 = lean_uint64_xor(x_98, x_97);
x_100 = 16;
x_101 = lean_uint64_shift_right(x_99, x_100);
x_102 = lean_uint64_xor(x_99, x_101);
x_103 = lean_uint64_to_usize(x_102);
x_104 = lean_usize_of_nat(x_94);
lean_dec(x_94);
x_105 = 1;
x_106 = lean_usize_sub(x_104, x_105);
x_107 = lean_usize_land(x_103, x_106);
x_108 = lean_array_uget(x_92, x_107);
x_109 = lean_unbox_uint64(x_88);
x_110 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__1___redArg(x_109, x_108);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_111 = lean_unsigned_to_nat(1u);
x_112 = lean_nat_add(x_91, x_111);
lean_dec(x_91);
x_113 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_113, 0, x_88);
lean_ctor_set(x_113, 1, x_89);
lean_ctor_set(x_113, 2, x_108);
x_114 = lean_array_uset(x_92, x_107, x_113);
x_115 = lean_unsigned_to_nat(4u);
x_116 = lean_nat_mul(x_112, x_115);
x_117 = lean_unsigned_to_nat(3u);
x_118 = lean_nat_div(x_116, x_117);
lean_dec(x_116);
x_119 = lean_array_get_size(x_114);
x_120 = lean_nat_dec_le(x_118, x_119);
lean_dec(x_119);
lean_dec(x_118);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; 
x_121 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__2___redArg(x_114);
if (lean_is_scalar(x_93)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_93;
}
lean_ctor_set(x_122, 0, x_112);
lean_ctor_set(x_122, 1, x_121);
x_1 = x_122;
x_2 = x_90;
goto _start;
}
else
{
lean_object* x_124; 
if (lean_is_scalar(x_93)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_93;
}
lean_ctor_set(x_124, 0, x_112);
lean_ctor_set(x_124, 1, x_114);
x_1 = x_124;
x_2 = x_90;
goto _start;
}
}
else
{
lean_object* x_126; lean_object* x_127; uint64_t x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_126 = lean_box(0);
x_127 = lean_array_uset(x_92, x_107, x_126);
x_128 = lean_unbox_uint64(x_88);
lean_dec(x_88);
x_129 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__5___redArg(x_128, x_89, x_108);
x_130 = lean_array_uset(x_127, x_107, x_129);
if (lean_is_scalar(x_93)) {
 x_131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_131 = x_93;
}
lean_ctor_set(x_131, 0, x_91);
lean_ctor_set(x_131, 1, x_130);
x_1 = x_131;
x_2 = x_90;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lake_CacheMap_save_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Lake_CacheMap_save_spec__3___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_CacheMap_save_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_4, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_8 = lean_array_uget(x_3, x_4);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Lake_CacheMap_save_spec__3___redArg(x_6, x_8);
x_10 = 1;
x_11 = lean_usize_add(x_4, x_10);
x_4 = x_11;
x_6 = x_9;
goto _start;
}
else
{
return x_6;
}
}
}
static lean_object* _init_l_Lake_CacheMap_save___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_beqHash____x40_Lake_Build_Trace___hyg_476____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_CacheMap_save___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instHashableHash___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_save(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_createParentDirs(x_1, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = 4;
x_8 = lean_io_prim_handle_mk(x_1, x_7, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = 3;
x_11 = lean_io_prim_handle_mk(x_1, x_10, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = 1;
x_15 = lean_io_prim_handle_lock(x_12, x_14, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__4;
x_20 = l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop(x_12, x_1, x_17, x_19, x_3, x_16);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec_ref(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_25 = x_21;
} else {
 lean_dec_ref(x_21);
 x_25 = lean_box(0);
}
x_72 = lean_ctor_get(x_2, 1);
x_73 = lean_array_get_size(x_72);
x_74 = lean_nat_dec_lt(x_18, x_73);
if (x_74 == 0)
{
lean_dec(x_73);
x_26 = x_23;
goto block_71;
}
else
{
uint8_t x_75; 
x_75 = lean_nat_dec_le(x_73, x_73);
if (x_75 == 0)
{
lean_dec(x_73);
x_26 = x_23;
goto block_71;
}
else
{
lean_object* x_76; lean_object* x_77; size_t x_78; size_t x_79; lean_object* x_80; 
x_76 = l_Lake_CacheMap_save___closed__0;
x_77 = l_Lake_CacheMap_save___closed__1;
x_78 = 0;
x_79 = lean_usize_of_nat(x_73);
lean_dec(x_73);
x_80 = l_Array_foldlMUnsafe_fold___at___Lake_CacheMap_save_spec__4(x_76, x_77, x_72, x_78, x_79, x_23);
x_26 = x_80;
goto block_71;
}
}
block_71:
{
lean_object* x_27; 
x_27 = lean_io_prim_handle_rewind(x_12, x_22);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_29 = lean_ctor_get(x_27, 1);
x_30 = lean_ctor_get(x_27, 0);
lean_dec(x_30);
x_31 = lean_ctor_get(x_26, 1);
lean_inc_ref(x_31);
lean_dec_ref(x_26);
x_32 = lean_array_get_size(x_31);
x_33 = lean_box(0);
x_34 = lean_nat_dec_lt(x_18, x_32);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_12);
if (lean_is_scalar(x_25)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_25;
}
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_24);
lean_ctor_set(x_27, 0, x_35);
return x_27;
}
else
{
uint8_t x_36; 
x_36 = lean_nat_dec_le(x_32, x_32);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_12);
if (lean_is_scalar(x_25)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_25;
}
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_24);
lean_ctor_set(x_27, 0, x_37);
return x_27;
}
else
{
size_t x_38; size_t x_39; lean_object* x_40; 
lean_free_object(x_27);
lean_dec(x_25);
x_38 = 0;
x_39 = lean_usize_of_nat(x_32);
lean_dec(x_32);
x_40 = l_Array_foldlMUnsafe_fold___at___Lake_CacheMap_save_spec__2(x_12, x_31, x_38, x_39, x_33, x_24, x_29);
lean_dec_ref(x_31);
lean_dec(x_12);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_41 = lean_ctor_get(x_27, 1);
lean_inc(x_41);
lean_dec(x_27);
x_42 = lean_ctor_get(x_26, 1);
lean_inc_ref(x_42);
lean_dec_ref(x_26);
x_43 = lean_array_get_size(x_42);
x_44 = lean_box(0);
x_45 = lean_nat_dec_lt(x_18, x_43);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_43);
lean_dec_ref(x_42);
lean_dec(x_12);
if (lean_is_scalar(x_25)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_25;
}
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_24);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_41);
return x_47;
}
else
{
uint8_t x_48; 
x_48 = lean_nat_dec_le(x_43, x_43);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_43);
lean_dec_ref(x_42);
lean_dec(x_12);
if (lean_is_scalar(x_25)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_25;
}
lean_ctor_set(x_49, 0, x_44);
lean_ctor_set(x_49, 1, x_24);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_41);
return x_50;
}
else
{
size_t x_51; size_t x_52; lean_object* x_53; 
lean_dec(x_25);
x_51 = 0;
x_52 = lean_usize_of_nat(x_43);
lean_dec(x_43);
x_53 = l_Array_foldlMUnsafe_fold___at___Lake_CacheMap_save_spec__2(x_12, x_42, x_51, x_52, x_44, x_24, x_41);
lean_dec_ref(x_42);
lean_dec(x_12);
return x_53;
}
}
}
}
else
{
uint8_t x_54; 
lean_dec_ref(x_26);
lean_dec(x_12);
x_54 = !lean_is_exclusive(x_27);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_55 = lean_ctor_get(x_27, 0);
x_56 = lean_io_error_to_string(x_55);
x_57 = 3;
x_58 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set_uint8(x_58, sizeof(void*)*1, x_57);
x_59 = lean_array_get_size(x_24);
x_60 = lean_array_push(x_24, x_58);
if (lean_is_scalar(x_25)) {
 x_61 = lean_alloc_ctor(1, 2, 0);
} else {
 x_61 = x_25;
 lean_ctor_set_tag(x_61, 1);
}
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
lean_ctor_set_tag(x_27, 0);
lean_ctor_set(x_27, 0, x_61);
return x_27;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_62 = lean_ctor_get(x_27, 0);
x_63 = lean_ctor_get(x_27, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_27);
x_64 = lean_io_error_to_string(x_62);
x_65 = 3;
x_66 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set_uint8(x_66, sizeof(void*)*1, x_65);
x_67 = lean_array_get_size(x_24);
x_68 = lean_array_push(x_24, x_66);
if (lean_is_scalar(x_25)) {
 x_69 = lean_alloc_ctor(1, 2, 0);
} else {
 x_69 = x_25;
 lean_ctor_set_tag(x_69, 1);
}
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_63);
return x_70;
}
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_12);
x_81 = !lean_is_exclusive(x_20);
if (x_81 == 0)
{
lean_object* x_82; uint8_t x_83; 
x_82 = lean_ctor_get(x_20, 0);
lean_dec(x_82);
x_83 = !lean_is_exclusive(x_21);
if (x_83 == 0)
{
return x_20;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_21, 0);
x_85 = lean_ctor_get(x_21, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_21);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
lean_ctor_set(x_20, 0, x_86);
return x_20;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_87 = lean_ctor_get(x_20, 1);
lean_inc(x_87);
lean_dec(x_20);
x_88 = lean_ctor_get(x_21, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_21, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_90 = x_21;
} else {
 lean_dec_ref(x_21);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(1, 2, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_89);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_87);
return x_92;
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_12);
lean_dec_ref(x_1);
x_93 = !lean_is_exclusive(x_15);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_94 = lean_ctor_get(x_15, 0);
x_95 = lean_io_error_to_string(x_94);
x_96 = 3;
x_97 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set_uint8(x_97, sizeof(void*)*1, x_96);
x_98 = lean_array_get_size(x_3);
x_99 = lean_array_push(x_3, x_97);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
lean_ctor_set_tag(x_15, 0);
lean_ctor_set(x_15, 0, x_100);
return x_15;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_101 = lean_ctor_get(x_15, 0);
x_102 = lean_ctor_get(x_15, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_15);
x_103 = lean_io_error_to_string(x_101);
x_104 = 3;
x_105 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set_uint8(x_105, sizeof(void*)*1, x_104);
x_106 = lean_array_get_size(x_3);
x_107 = lean_array_push(x_3, x_105);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_102);
return x_109;
}
}
}
else
{
uint8_t x_110; 
x_110 = !lean_is_exclusive(x_11);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_111 = lean_ctor_get(x_11, 0);
x_112 = l_Lake_CacheMap_load___closed__0;
x_113 = lean_string_append(x_1, x_112);
x_114 = lean_io_error_to_string(x_111);
x_115 = lean_string_append(x_113, x_114);
lean_dec_ref(x_114);
x_116 = 3;
x_117 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set_uint8(x_117, sizeof(void*)*1, x_116);
x_118 = lean_array_get_size(x_3);
x_119 = lean_array_push(x_3, x_117);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
lean_ctor_set_tag(x_11, 0);
lean_ctor_set(x_11, 0, x_120);
return x_11;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_121 = lean_ctor_get(x_11, 0);
x_122 = lean_ctor_get(x_11, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_11);
x_123 = l_Lake_CacheMap_load___closed__0;
x_124 = lean_string_append(x_1, x_123);
x_125 = lean_io_error_to_string(x_121);
x_126 = lean_string_append(x_124, x_125);
lean_dec_ref(x_125);
x_127 = 3;
x_128 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set_uint8(x_128, sizeof(void*)*1, x_127);
x_129 = lean_array_get_size(x_3);
x_130 = lean_array_push(x_3, x_128);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_122);
return x_132;
}
}
}
else
{
uint8_t x_133; 
lean_dec_ref(x_1);
x_133 = !lean_is_exclusive(x_8);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; uint8_t x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_134 = lean_ctor_get(x_8, 0);
x_135 = lean_io_error_to_string(x_134);
x_136 = 3;
x_137 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set_uint8(x_137, sizeof(void*)*1, x_136);
x_138 = lean_array_get_size(x_3);
x_139 = lean_array_push(x_3, x_137);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
lean_ctor_set_tag(x_8, 0);
lean_ctor_set(x_8, 0, x_140);
return x_8;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_141 = lean_ctor_get(x_8, 0);
x_142 = lean_ctor_get(x_8, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_8);
x_143 = lean_io_error_to_string(x_141);
x_144 = 3;
x_145 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set_uint8(x_145, sizeof(void*)*1, x_144);
x_146 = lean_array_get_size(x_3);
x_147 = lean_array_push(x_3, x_145);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_142);
return x_149;
}
}
}
else
{
uint8_t x_150; 
lean_dec_ref(x_1);
x_150 = !lean_is_exclusive(x_5);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; uint8_t x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_151 = lean_ctor_get(x_5, 0);
x_152 = lean_io_error_to_string(x_151);
x_153 = 3;
x_154 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set_uint8(x_154, sizeof(void*)*1, x_153);
x_155 = lean_array_get_size(x_3);
x_156 = lean_array_push(x_3, x_154);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 0, x_157);
return x_5;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_158 = lean_ctor_get(x_5, 0);
x_159 = lean_ctor_get(x_5, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_5);
x_160 = lean_io_error_to_string(x_158);
x_161 = 3;
x_162 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set_uint8(x_162, sizeof(void*)*1, x_161);
x_163 = lean_array_get_size(x_3);
x_164 = lean_array_push(x_3, x_162);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_159);
return x_166;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lake_CacheMap_save_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Lake_CacheMap_save_spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_CacheMap_save_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at___Lake_CacheMap_save_spec__2(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lake_CacheMap_save_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Lake_CacheMap_save_spec__3(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_CacheMap_save_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at___Lake_CacheMap_save_spec__4(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_save___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_CacheMap_save(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lake_CacheMap_get_x3f_spec__0___redArg(uint64_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_unbox_uint64(x_4);
x_8 = lean_uint64_dec_eq(x_7, x_1);
if (x_8 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_10; 
lean_inc(x_5);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_5);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lake_CacheMap_get_x3f_spec__0(lean_object* x_1, uint64_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lake_CacheMap_get_x3f_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_get_x3f(uint64_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_array_get_size(x_3);
x_5 = 32;
x_6 = lean_uint64_shift_right(x_1, x_5);
x_7 = lean_uint64_xor(x_1, x_6);
x_8 = 16;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = lean_uint64_to_usize(x_10);
x_12 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_13 = 1;
x_14 = lean_usize_sub(x_12, x_13);
x_15 = lean_usize_land(x_11, x_14);
x_16 = lean_array_uget(x_3, x_15);
x_17 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lake_CacheMap_get_x3f_spec__0___redArg(x_1, x_16);
lean_dec(x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lake_CacheMap_get_x3f_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lake_CacheMap_get_x3f_spec__0___redArg(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lake_CacheMap_get_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lake_CacheMap_get_x3f_spec__0(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_get_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = l_Lake_CacheMap_get_x3f(x_3, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_insertCore(uint64_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; uint8_t x_20; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_array_get_size(x_6);
x_8 = 32;
x_9 = lean_uint64_shift_right(x_1, x_8);
x_10 = lean_uint64_xor(x_1, x_9);
x_11 = 16;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_16 = 1;
x_17 = lean_usize_sub(x_15, x_16);
x_18 = lean_usize_land(x_14, x_17);
x_19 = lean_array_uget(x_6, x_18);
x_20 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__1___redArg(x_1, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_5, x_21);
lean_dec(x_5);
x_23 = lean_box_uint64(x_1);
x_24 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_2);
lean_ctor_set(x_24, 2, x_19);
x_25 = lean_array_uset(x_6, x_18, x_24);
x_26 = lean_unsigned_to_nat(4u);
x_27 = lean_nat_mul(x_22, x_26);
x_28 = lean_unsigned_to_nat(3u);
x_29 = lean_nat_div(x_27, x_28);
lean_dec(x_27);
x_30 = lean_array_get_size(x_25);
x_31 = lean_nat_dec_le(x_29, x_30);
lean_dec(x_30);
lean_dec(x_29);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__2___redArg(x_25);
lean_ctor_set(x_3, 1, x_32);
lean_ctor_set(x_3, 0, x_22);
return x_3;
}
else
{
lean_ctor_set(x_3, 1, x_25);
lean_ctor_set(x_3, 0, x_22);
return x_3;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_box(0);
x_34 = lean_array_uset(x_6, x_18, x_33);
x_35 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__5___redArg(x_1, x_2, x_19);
x_36 = lean_array_uset(x_34, x_18, x_35);
lean_ctor_set(x_3, 1, x_36);
return x_3;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; size_t x_46; size_t x_47; size_t x_48; size_t x_49; size_t x_50; lean_object* x_51; uint8_t x_52; 
x_37 = lean_ctor_get(x_3, 0);
x_38 = lean_ctor_get(x_3, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_3);
x_39 = lean_array_get_size(x_38);
x_40 = 32;
x_41 = lean_uint64_shift_right(x_1, x_40);
x_42 = lean_uint64_xor(x_1, x_41);
x_43 = 16;
x_44 = lean_uint64_shift_right(x_42, x_43);
x_45 = lean_uint64_xor(x_42, x_44);
x_46 = lean_uint64_to_usize(x_45);
x_47 = lean_usize_of_nat(x_39);
lean_dec(x_39);
x_48 = 1;
x_49 = lean_usize_sub(x_47, x_48);
x_50 = lean_usize_land(x_46, x_49);
x_51 = lean_array_uget(x_38, x_50);
x_52 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__1___redArg(x_1, x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_nat_add(x_37, x_53);
lean_dec(x_37);
x_55 = lean_box_uint64(x_1);
x_56 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_2);
lean_ctor_set(x_56, 2, x_51);
x_57 = lean_array_uset(x_38, x_50, x_56);
x_58 = lean_unsigned_to_nat(4u);
x_59 = lean_nat_mul(x_54, x_58);
x_60 = lean_unsigned_to_nat(3u);
x_61 = lean_nat_div(x_59, x_60);
lean_dec(x_59);
x_62 = lean_array_get_size(x_57);
x_63 = lean_nat_dec_le(x_61, x_62);
lean_dec(x_62);
lean_dec(x_61);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__2___redArg(x_57);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_54);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_54);
lean_ctor_set(x_66, 1, x_57);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_67 = lean_box(0);
x_68 = lean_array_uset(x_38, x_50, x_67);
x_69 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__5___redArg(x_1, x_2, x_51);
x_70 = lean_array_uset(x_68, x_50, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_37);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_insertCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_5 = l_Lake_CacheMap_insertCore(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_insert___redArg(lean_object* x_1, uint64_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_apply_1(x_1, x_3);
x_6 = l_Lake_CacheMap_insertCore(x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_insert(lean_object* x_1, lean_object* x_2, uint64_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_apply_1(x_2, x_4);
x_7 = l_Lake_CacheMap_insertCore(x_3, x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_insert___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_6 = l_Lake_CacheMap_insert___redArg(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_insert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint64_t x_6; lean_object* x_7; 
x_6 = lean_unbox_uint64(x_3);
lean_dec(x_3);
x_7 = l_Lake_CacheMap_insert(x_1, x_2, x_6, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_get_x3f(uint64_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_st_ref_take(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
lean_inc(x_5);
x_7 = lean_st_ref_set(x_2, x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_dec(x_9);
x_10 = l_Lake_CacheMap_get_x3f(x_1, x_5);
lean_dec(x_5);
lean_ctor_set(x_7, 0, x_10);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_dec(x_7);
x_12 = l_Lake_CacheMap_get_x3f(x_1, x_5);
lean_dec(x_5);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_get_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_5 = l_Lake_CacheRef_get_x3f(x_4, x_2, x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_insert___redArg(lean_object* x_1, uint64_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_st_ref_take(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_apply_1(x_1, x_3);
x_10 = l_Lake_CacheMap_insertCore(x_2, x_9, x_7);
x_11 = lean_st_ref_set(x_4, x_10, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_insert(lean_object* x_1, lean_object* x_2, uint64_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_st_ref_take(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = lean_apply_1(x_2, x_4);
x_11 = l_Lake_CacheMap_insertCore(x_3, x_10, x_8);
x_12 = lean_st_ref_set(x_5, x_11, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_insert___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint64_t x_6; lean_object* x_7; 
x_6 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_7 = l_Lake_CacheRef_insert___redArg(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_insert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint64_t x_7; lean_object* x_8; 
x_7 = lean_unbox_uint64(x_3);
lean_dec(x_3);
x_8 = l_Lake_CacheRef_insert(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_5);
return x_8;
}
}
lean_object* initialize_Lake_Util_Log(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_Artifact(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Trace(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_Cache(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Util_Log(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Artifact(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Trace(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instInhabitedCache___closed__0 = _init_l_Lake_instInhabitedCache___closed__0();
lean_mark_persistent(l_Lake_instInhabitedCache___closed__0);
l_Lake_instInhabitedCache = _init_l_Lake_instInhabitedCache();
lean_mark_persistent(l_Lake_instInhabitedCache);
l_Lake_Cache_artifactDir___closed__0 = _init_l_Lake_Cache_artifactDir___closed__0();
lean_mark_persistent(l_Lake_Cache_artifactDir___closed__0);
l_Lake_Cache_artifactPath___closed__0 = _init_l_Lake_Cache_artifactPath___closed__0();
lean_mark_persistent(l_Lake_Cache_artifactPath___closed__0);
l_Lake_Cache_getArtifact_x3f___closed__0 = _init_l_Lake_Cache_getArtifact_x3f___closed__0();
lean_mark_persistent(l_Lake_Cache_getArtifact_x3f___closed__0);
l_Lake_Cache_getArtifact_x3f___closed__1 = _init_l_Lake_Cache_getArtifact_x3f___closed__1();
lean_mark_persistent(l_Lake_Cache_getArtifact_x3f___closed__1);
l_Lake_Cache_inputsDir___closed__0 = _init_l_Lake_Cache_inputsDir___closed__0();
lean_mark_persistent(l_Lake_Cache_inputsDir___closed__0);
l_Lake_Cache_inputsFile___closed__0 = _init_l_Lake_Cache_inputsFile___closed__0();
lean_mark_persistent(l_Lake_Cache_inputsFile___closed__0);
l_Prod_fromJson_x3f___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__0___closed__0 = _init_l_Prod_fromJson_x3f___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__0___closed__0();
lean_mark_persistent(l_Prod_fromJson_x3f___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__0___closed__0);
l_Prod_fromJson_x3f___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__0___closed__1 = _init_l_Prod_fromJson_x3f___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__0___closed__1();
lean_mark_persistent(l_Prod_fromJson_x3f___at_____private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__0___closed__1);
l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop___closed__0 = _init_l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop___closed__0();
lean_mark_persistent(l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop___closed__0);
l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop___closed__1 = _init_l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop___closed__1();
lean_mark_persistent(l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop___closed__1);
l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0 = _init_l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0();
lean_mark_persistent(l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0);
l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__1 = _init_l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__1();
lean_mark_persistent(l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__1);
l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__2 = _init_l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__2();
lean_mark_persistent(l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__2);
l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__3 = _init_l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__3();
lean_mark_persistent(l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__3);
l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__4 = _init_l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__4();
lean_mark_persistent(l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__4);
l_Lake_CacheMap_load___closed__0 = _init_l_Lake_CacheMap_load___closed__0();
lean_mark_persistent(l_Lake_CacheMap_load___closed__0);
l_Prod_toJson___at___Lake_CacheMap_save_spec__0___closed__0 = _init_l_Prod_toJson___at___Lake_CacheMap_save_spec__0___closed__0();
lean_mark_persistent(l_Prod_toJson___at___Lake_CacheMap_save_spec__0___closed__0);
l_Lake_CacheMap_save___closed__0 = _init_l_Lake_CacheMap_save___closed__0();
lean_mark_persistent(l_Lake_CacheMap_save___closed__0);
l_Lake_CacheMap_save___closed__1 = _init_l_Lake_CacheMap_save___closed__1();
lean_mark_persistent(l_Lake_CacheMap_save___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

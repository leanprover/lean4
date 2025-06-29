// Lean compiler output
// Module: Lake.Build.ModuleArtifacts
// Imports: Lake.Build.Trace Lake.Config.Artifact Lake.Util.JsonObject
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
lean_object* l_Lean_Json_getObj_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_fromJson_x3f___at___Lake_ModuleOutputHashes_fromJson_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Array_fromJson_x3f___at___Lake_ModuleOutputHashes_fromJson_x3f_spec__0___closed__1;
static lean_object* l_Lake_ModuleOutputHashes_toJson___closed__0;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lake_ModuleOutputHashes_fromJson_x3f___closed__5;
static lean_object* l_Lake_ModuleOutputHashes_toJson___closed__1;
static lean_object* l_Lake_instToJsonModuleOutputHashes___closed__0;
static lean_object* l_Lake_ModuleOutputHashes_fromJson_x3f___closed__2;
static lean_object* l_Lake_ModuleOutputHashes_fromJson_x3f___closed__7;
LEAN_EXPORT lean_object* l_Array_toJson___at___Lake_ModuleOutputHashes_toJson_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ModuleOutputHashes_oleanHashes(lean_object*);
static lean_object* l_Lake_ModuleOutputHashes_fromJson_x3f___closed__1;
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___Lake_ModuleOutputHashes_fromJson_x3f_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ModuleOutputHashes_fromJson_x3f(lean_object*);
static lean_object* l_Lake_ModuleOutputHashes_fromJson_x3f___closed__11;
lean_object* l_UInt64_fromJson_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_toJson___at___Lake_ModuleOutputHashes_toJson_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToJsonModuleOutputHashes;
lean_object* lean_uint64_to_nat(uint64_t);
static lean_object* l_Array_fromJson_x3f___at___Lake_ModuleOutputHashes_fromJson_x3f_spec__0___closed__0;
static lean_object* l_Lake_ModuleOutputHashes_toJson___closed__3;
static lean_object* l_Lake_instFromJsonModuleOutputHashes___closed__0;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___Lake_ModuleOutputHashes_fromJson_x3f_spec__2(lean_object*);
static lean_object* l_Lake_ModuleOutputHashes_fromJson_x3f___closed__6;
static lean_object* l_Lake_ModuleOutputHashes_oleanHashes___closed__0;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_toJson___at___Lake_ModuleOutputHashes_toJson_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Option_fromJson_x3f___at___Lake_ModuleOutputHashes_fromJson_x3f_spec__2___closed__0;
LEAN_EXPORT lean_object* l_Lake_ModuleOutputArtifacts_hashes(lean_object*);
static lean_object* l_Lake_ModuleOutputHashes_fromJson_x3f___closed__0;
static lean_object* l_Lake_ModuleOutputHashes_fromJson_x3f___closed__4;
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lake_ModuleOutputHashes_fromJson_x3f___closed__3;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_fromJson_x3f___at___Lake_ModuleOutputHashes_fromJson_x3f_spec__0_spec__0(size_t, size_t, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lake_ModuleOutputHashes_fromJson_x3f___closed__8;
static lean_object* l_Lake_ModuleOutputHashes_toJson___closed__2;
static lean_object* l_Lake_ModuleOutputHashes_fromJson_x3f___closed__10;
lean_object* l_Lean_bignumToJson(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instFromJsonModuleOutputHashes;
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_RBNode_find___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1___redArg(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
static lean_object* l_Lake_ModuleOutputHashes_fromJson_x3f___closed__9;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lake_ModuleOutputHashes_fromJson_x3f___closed__12;
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ModuleOutputHashes_toJson(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* _init_l_Lake_ModuleOutputHashes_oleanHashes___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_ModuleOutputHashes_oleanHashes(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_9; lean_object* x_10; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
lean_dec(x_1);
x_9 = l_Lake_ModuleOutputHashes_oleanHashes___closed__0;
x_10 = lean_array_push(x_9, x_2);
if (lean_obj_tag(x_3) == 0)
{
x_5 = x_10;
goto block_8;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_dec(x_3);
x_12 = lean_array_push(x_10, x_11);
x_5 = x_12;
goto block_8;
}
block_8:
{
if (lean_obj_tag(x_4) == 0)
{
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_array_push(x_5, x_6);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_toJson___at___Lake_ModuleOutputHashes_toJson_spec__0_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_box(0);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_unbox_uint64(x_5);
lean_dec(x_5);
x_9 = lean_uint64_to_nat(x_8);
x_10 = l_Lean_bignumToJson(x_9);
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_13 = lean_array_uset(x_7, x_2, x_10);
x_2 = x_12;
x_3 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___Lake_ModuleOutputHashes_toJson_spec__0(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_array_size(x_1);
x_3 = 0;
x_4 = l_Array_mapMUnsafe_map___at___Array_toJson___at___Lake_ModuleOutputHashes_toJson_spec__0_spec__0(x_2, x_3, x_1);
x_5 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_ModuleOutputHashes_toJson___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("o", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_ModuleOutputHashes_toJson___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("i", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_ModuleOutputHashes_toJson___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("c", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_ModuleOutputHashes_toJson___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("bc", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_ModuleOutputHashes_toJson(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint64_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint64_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 4);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 5);
lean_inc(x_4);
x_5 = lean_box(0);
x_6 = l_Lake_ModuleOutputHashes_toJson___closed__0;
x_7 = l_Lake_ModuleOutputHashes_oleanHashes(x_1);
x_8 = l_Array_toJson___at___Lake_ModuleOutputHashes_toJson_spec__0(x_7);
x_9 = l_Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0___redArg(x_5, x_6, x_8);
x_10 = l_Lake_ModuleOutputHashes_toJson___closed__1;
x_11 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_12 = lean_uint64_to_nat(x_11);
x_13 = l_Lean_bignumToJson(x_12);
x_14 = l_Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0___redArg(x_9, x_10, x_13);
x_15 = l_Lake_ModuleOutputHashes_toJson___closed__2;
x_16 = lean_unbox_uint64(x_3);
lean_dec(x_3);
x_17 = lean_uint64_to_nat(x_16);
x_18 = l_Lean_bignumToJson(x_17);
x_19 = l_Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0___redArg(x_14, x_15, x_18);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_4);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint64_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_4, 0);
x_23 = l_Lake_ModuleOutputHashes_toJson___closed__3;
x_24 = lean_unbox_uint64(x_22);
lean_dec(x_22);
x_25 = lean_uint64_to_nat(x_24);
x_26 = l_Lean_bignumToJson(x_25);
x_27 = l_Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0___redArg(x_19, x_23, x_26);
lean_ctor_set_tag(x_4, 5);
lean_ctor_set(x_4, 0, x_27);
return x_4;
}
else
{
lean_object* x_28; lean_object* x_29; uint64_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_4, 0);
lean_inc(x_28);
lean_dec(x_4);
x_29 = l_Lake_ModuleOutputHashes_toJson___closed__3;
x_30 = lean_unbox_uint64(x_28);
lean_dec(x_28);
x_31 = lean_uint64_to_nat(x_30);
x_32 = l_Lean_bignumToJson(x_31);
x_33 = l_Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0___redArg(x_19, x_29, x_32);
x_34 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_toJson___at___Lake_ModuleOutputHashes_toJson_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Array_toJson___at___Lake_ModuleOutputHashes_toJson_spec__0_spec__0(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l_Lake_instToJsonModuleOutputHashes___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_ModuleOutputHashes_toJson), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instToJsonModuleOutputHashes() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instToJsonModuleOutputHashes___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_fromJson_x3f___at___Lake_ModuleOutputHashes_fromJson_x3f_spec__0_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = l_UInt64_fromJson_x3f(x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_3);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_box(0);
x_13 = lean_array_uset(x_3, x_2, x_12);
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_16 = lean_array_uset(x_13, x_2, x_11);
x_2 = x_15;
x_3 = x_16;
goto _start;
}
}
}
}
static lean_object* _init_l_Array_fromJson_x3f___at___Lake_ModuleOutputHashes_fromJson_x3f_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected JSON array, got '", 26, 26);
return x_1;
}
}
static lean_object* _init_l_Array_fromJson_x3f___at___Lake_ModuleOutputHashes_fromJson_x3f_spec__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___Lake_ModuleOutputHashes_fromJson_x3f_spec__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_2; size_t x_3; size_t x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_array_size(x_2);
x_4 = 0;
x_5 = l_Array_mapMUnsafe_map___at___Array_fromJson_x3f___at___Lake_ModuleOutputHashes_fromJson_x3f_spec__0_spec__0(x_3, x_4, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = l_Array_fromJson_x3f___at___Lake_ModuleOutputHashes_fromJson_x3f_spec__0___closed__0;
x_7 = lean_unsigned_to_nat(80u);
x_8 = l_Lean_Json_pretty(x_1, x_7);
x_9 = lean_string_append(x_6, x_8);
lean_dec(x_8);
x_10 = l_Array_fromJson_x3f___at___Lake_ModuleOutputHashes_fromJson_x3f_spec__0___closed__1;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
static lean_object* _init_l_Option_fromJson_x3f___at___Lake_ModuleOutputHashes_fromJson_x3f_spec__2___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___Lake_ModuleOutputHashes_fromJson_x3f_spec__2(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Option_fromJson_x3f___at___Lake_ModuleOutputHashes_fromJson_x3f_spec__2___closed__0;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_UInt64_fromJson_x3f(x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
}
}
static lean_object* _init_l_Lake_ModuleOutputHashes_fromJson_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("property not found: o", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lake_ModuleOutputHashes_fromJson_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_ModuleOutputHashes_fromJson_x3f___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_ModuleOutputHashes_fromJson_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("o: ", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_ModuleOutputHashes_fromJson_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected a least one 'o' (OLean) hash", 37, 37);
return x_1;
}
}
static lean_object* _init_l_Lake_ModuleOutputHashes_fromJson_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_ModuleOutputHashes_fromJson_x3f___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_ModuleOutputHashes_fromJson_x3f___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("property not found: i", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lake_ModuleOutputHashes_fromJson_x3f___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_ModuleOutputHashes_fromJson_x3f___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_ModuleOutputHashes_fromJson_x3f___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("i: ", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_ModuleOutputHashes_fromJson_x3f___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("property not found: c", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lake_ModuleOutputHashes_fromJson_x3f___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_ModuleOutputHashes_fromJson_x3f___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_ModuleOutputHashes_fromJson_x3f___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("c: ", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_ModuleOutputHashes_fromJson_x3f___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("b", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_ModuleOutputHashes_fromJson_x3f___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("b: ", 3, 3);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_ModuleOutputHashes_fromJson_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Json_getObj_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = l_Lake_ModuleOutputHashes_toJson___closed__0;
x_8 = l_Lean_RBNode_find___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1___redArg(x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
lean_dec(x_6);
x_9 = l_Lake_ModuleOutputHashes_fromJson_x3f___closed__1;
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Array_fromJson_x3f___at___Lake_ModuleOutputHashes_fromJson_x3f_spec__0(x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_6);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = l_Lake_ModuleOutputHashes_fromJson_x3f___closed__2;
x_15 = lean_string_append(x_14, x_13);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
x_17 = l_Lake_ModuleOutputHashes_fromJson_x3f___closed__2;
x_18 = lean_string_append(x_17, x_16);
lean_dec(x_16);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
else
{
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_20; 
lean_dec(x_6);
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
lean_ctor_set_tag(x_11, 0);
return x_11;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_11, 0);
lean_inc(x_21);
lean_dec(x_11);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_11, 0);
lean_inc(x_23);
lean_dec(x_11);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_array_get_size(x_23);
x_26 = lean_nat_dec_lt(x_24, x_25);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_6);
x_27 = l_Lake_ModuleOutputHashes_fromJson_x3f___closed__4;
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = l_Lake_ModuleOutputHashes_toJson___closed__1;
x_29 = l_Lean_RBNode_find___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1___redArg(x_6, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_6);
x_30 = l_Lake_ModuleOutputHashes_fromJson_x3f___closed__6;
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 x_32 = x_29;
} else {
 lean_dec_ref(x_29);
 x_32 = lean_box(0);
}
x_33 = l_UInt64_fromJson_x3f(x_31);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
lean_dec(x_32);
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_6);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = l_Lake_ModuleOutputHashes_fromJson_x3f___closed__7;
x_37 = lean_string_append(x_36, x_35);
lean_dec(x_35);
lean_ctor_set(x_33, 0, x_37);
return x_33;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_33, 0);
lean_inc(x_38);
lean_dec(x_33);
x_39 = l_Lake_ModuleOutputHashes_fromJson_x3f___closed__7;
x_40 = lean_string_append(x_39, x_38);
lean_dec(x_38);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_33, 0);
lean_inc(x_42);
lean_dec(x_33);
x_43 = l_Lake_ModuleOutputHashes_toJson___closed__2;
x_44 = l_Lean_RBNode_find___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1___redArg(x_6, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
lean_dec(x_42);
lean_dec(x_32);
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_6);
x_45 = l_Lake_ModuleOutputHashes_fromJson_x3f___closed__9;
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 x_47 = x_44;
} else {
 lean_dec_ref(x_44);
 x_47 = lean_box(0);
}
x_48 = l_UInt64_fromJson_x3f(x_46);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
lean_dec(x_47);
lean_dec(x_42);
lean_dec(x_32);
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_6);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = l_Lake_ModuleOutputHashes_fromJson_x3f___closed__10;
x_52 = lean_string_append(x_51, x_50);
lean_dec(x_50);
lean_ctor_set(x_48, 0, x_52);
return x_48;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_48, 0);
lean_inc(x_53);
lean_dec(x_48);
x_54 = l_Lake_ModuleOutputHashes_fromJson_x3f___closed__10;
x_55 = lean_string_append(x_54, x_53);
lean_dec(x_53);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint64_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_68; lean_object* x_69; lean_object* x_78; lean_object* x_87; lean_object* x_88; 
x_57 = lean_ctor_get(x_48, 0);
lean_inc(x_57);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 x_58 = x_48;
} else {
 lean_dec_ref(x_48);
 x_58 = lean_box(0);
}
x_59 = lean_array_fget(x_23, x_24);
x_60 = lean_unbox_uint64(x_59);
lean_dec(x_59);
x_87 = l_Lake_ModuleOutputHashes_fromJson_x3f___closed__11;
x_88 = l_Lean_RBNode_find___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1___redArg(x_6, x_87);
lean_dec(x_6);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; 
x_89 = lean_box(0);
x_78 = x_89;
goto block_86;
}
else
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_88, 0);
lean_inc(x_90);
lean_dec(x_88);
x_91 = l_Option_fromJson_x3f___at___Lake_ModuleOutputHashes_fromJson_x3f_spec__2(x_90);
if (lean_obj_tag(x_91) == 0)
{
uint8_t x_92; 
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_47);
lean_dec(x_42);
lean_dec(x_32);
lean_dec(x_25);
lean_dec(x_23);
x_92 = !lean_is_exclusive(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_91, 0);
x_94 = l_Lake_ModuleOutputHashes_fromJson_x3f___closed__12;
x_95 = lean_string_append(x_94, x_93);
lean_dec(x_93);
lean_ctor_set(x_91, 0, x_95);
return x_91;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_91, 0);
lean_inc(x_96);
lean_dec(x_91);
x_97 = l_Lake_ModuleOutputHashes_fromJson_x3f___closed__12;
x_98 = lean_string_append(x_97, x_96);
lean_dec(x_96);
x_99 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_99, 0, x_98);
return x_99;
}
}
else
{
if (lean_obj_tag(x_91) == 0)
{
uint8_t x_100; 
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_47);
lean_dec(x_42);
lean_dec(x_32);
lean_dec(x_25);
lean_dec(x_23);
x_100 = !lean_is_exclusive(x_91);
if (x_100 == 0)
{
lean_ctor_set_tag(x_91, 0);
return x_91;
}
else
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_91, 0);
lean_inc(x_101);
lean_dec(x_91);
x_102 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_102, 0, x_101);
return x_102;
}
}
else
{
lean_object* x_103; 
x_103 = lean_ctor_get(x_91, 0);
lean_inc(x_103);
lean_dec(x_91);
x_78 = x_103;
goto block_86;
}
}
}
block_67:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_box_uint64(x_60);
x_65 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_61);
lean_ctor_set(x_65, 2, x_63);
lean_ctor_set(x_65, 3, x_42);
lean_ctor_set(x_65, 4, x_57);
lean_ctor_set(x_65, 5, x_62);
if (lean_is_scalar(x_58)) {
 x_66 = lean_alloc_ctor(1, 1, 0);
} else {
 x_66 = x_58;
}
lean_ctor_set(x_66, 0, x_65);
return x_66;
}
block_77:
{
lean_object* x_70; uint8_t x_71; 
x_70 = lean_unsigned_to_nat(2u);
x_71 = lean_nat_dec_lt(x_70, x_25);
lean_dec(x_25);
if (x_71 == 0)
{
lean_object* x_72; 
lean_dec(x_47);
lean_dec(x_23);
x_72 = lean_box(0);
x_61 = x_69;
x_62 = x_68;
x_63 = x_72;
goto block_67;
}
else
{
lean_object* x_73; uint64_t x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_array_fget(x_23, x_70);
lean_dec(x_23);
x_74 = lean_unbox_uint64(x_73);
lean_dec(x_73);
x_75 = lean_box_uint64(x_74);
if (lean_is_scalar(x_47)) {
 x_76 = lean_alloc_ctor(1, 1, 0);
} else {
 x_76 = x_47;
}
lean_ctor_set(x_76, 0, x_75);
x_61 = x_69;
x_62 = x_68;
x_63 = x_76;
goto block_67;
}
}
block_86:
{
lean_object* x_79; uint8_t x_80; 
x_79 = lean_unsigned_to_nat(1u);
x_80 = lean_nat_dec_lt(x_79, x_25);
if (x_80 == 0)
{
lean_object* x_81; 
lean_dec(x_32);
x_81 = lean_box(0);
x_68 = x_78;
x_69 = x_81;
goto block_77;
}
else
{
lean_object* x_82; uint64_t x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_array_fget(x_23, x_79);
x_83 = lean_unbox_uint64(x_82);
lean_dec(x_82);
x_84 = lean_box_uint64(x_83);
if (lean_is_scalar(x_32)) {
 x_85 = lean_alloc_ctor(1, 1, 0);
} else {
 x_85 = x_32;
}
lean_ctor_set(x_85, 0, x_84);
x_68 = x_78;
x_69 = x_85;
goto block_77;
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
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_fromJson_x3f___at___Lake_ModuleOutputHashes_fromJson_x3f_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Array_fromJson_x3f___at___Lake_ModuleOutputHashes_fromJson_x3f_spec__0_spec__0(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l_Lake_instFromJsonModuleOutputHashes___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_ModuleOutputHashes_fromJson_x3f), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instFromJsonModuleOutputHashes() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instFromJsonModuleOutputHashes___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_ModuleOutputArtifacts_hashes(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_29; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 3);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 4);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 5);
lean_inc(x_7);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 x_8 = x_1;
} else {
 lean_dec_ref(x_1);
 x_8 = lean_box(0);
}
x_9 = lean_ctor_get(x_2, 3);
lean_inc(x_9);
lean_dec(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_38; 
x_38 = lean_box(0);
x_29 = x_38;
goto block_37;
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_3);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_3, 0);
x_41 = lean_ctor_get(x_40, 3);
lean_inc(x_41);
lean_dec(x_40);
lean_ctor_set(x_3, 0, x_41);
x_29 = x_3;
goto block_37;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_3, 0);
lean_inc(x_42);
lean_dec(x_3);
x_43 = lean_ctor_get(x_42, 3);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_29 = x_44;
goto block_37;
}
}
block_28:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_5, 3);
lean_inc(x_12);
lean_dec(x_5);
x_13 = lean_ctor_get(x_6, 3);
lean_inc(x_13);
lean_dec(x_6);
x_14 = lean_box(0);
if (lean_is_scalar(x_8)) {
 x_15 = lean_alloc_ctor(0, 6, 0);
} else {
 x_15 = x_8;
}
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_10);
lean_ctor_set(x_15, 2, x_11);
lean_ctor_set(x_15, 3, x_12);
lean_ctor_set(x_15, 4, x_13);
lean_ctor_set(x_15, 5, x_14);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_7);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_7, 0);
x_18 = lean_ctor_get(x_5, 3);
lean_inc(x_18);
lean_dec(x_5);
x_19 = lean_ctor_get(x_6, 3);
lean_inc(x_19);
lean_dec(x_6);
x_20 = lean_ctor_get(x_17, 3);
lean_inc(x_20);
lean_dec(x_17);
lean_ctor_set(x_7, 0, x_20);
if (lean_is_scalar(x_8)) {
 x_21 = lean_alloc_ctor(0, 6, 0);
} else {
 x_21 = x_8;
}
lean_ctor_set(x_21, 0, x_9);
lean_ctor_set(x_21, 1, x_10);
lean_ctor_set(x_21, 2, x_11);
lean_ctor_set(x_21, 3, x_18);
lean_ctor_set(x_21, 4, x_19);
lean_ctor_set(x_21, 5, x_7);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_7, 0);
lean_inc(x_22);
lean_dec(x_7);
x_23 = lean_ctor_get(x_5, 3);
lean_inc(x_23);
lean_dec(x_5);
x_24 = lean_ctor_get(x_6, 3);
lean_inc(x_24);
lean_dec(x_6);
x_25 = lean_ctor_get(x_22, 3);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
if (lean_is_scalar(x_8)) {
 x_27 = lean_alloc_ctor(0, 6, 0);
} else {
 x_27 = x_8;
}
lean_ctor_set(x_27, 0, x_9);
lean_ctor_set(x_27, 1, x_10);
lean_ctor_set(x_27, 2, x_11);
lean_ctor_set(x_27, 3, x_23);
lean_ctor_set(x_27, 4, x_24);
lean_ctor_set(x_27, 5, x_26);
return x_27;
}
}
}
block_37:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_30; 
x_30 = lean_box(0);
x_10 = x_29;
x_11 = x_30;
goto block_28;
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_4);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_4, 0);
x_33 = lean_ctor_get(x_32, 3);
lean_inc(x_33);
lean_dec(x_32);
lean_ctor_set(x_4, 0, x_33);
x_10 = x_29;
x_11 = x_4;
goto block_28;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_4, 0);
lean_inc(x_34);
lean_dec(x_4);
x_35 = lean_ctor_get(x_34, 3);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_10 = x_29;
x_11 = x_36;
goto block_28;
}
}
}
}
}
lean_object* initialize_Lake_Build_Trace(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_Artifact(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_JsonObject(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_ModuleArtifacts(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Build_Trace(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Artifact(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_JsonObject(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_ModuleOutputHashes_oleanHashes___closed__0 = _init_l_Lake_ModuleOutputHashes_oleanHashes___closed__0();
lean_mark_persistent(l_Lake_ModuleOutputHashes_oleanHashes___closed__0);
l_Lake_ModuleOutputHashes_toJson___closed__0 = _init_l_Lake_ModuleOutputHashes_toJson___closed__0();
lean_mark_persistent(l_Lake_ModuleOutputHashes_toJson___closed__0);
l_Lake_ModuleOutputHashes_toJson___closed__1 = _init_l_Lake_ModuleOutputHashes_toJson___closed__1();
lean_mark_persistent(l_Lake_ModuleOutputHashes_toJson___closed__1);
l_Lake_ModuleOutputHashes_toJson___closed__2 = _init_l_Lake_ModuleOutputHashes_toJson___closed__2();
lean_mark_persistent(l_Lake_ModuleOutputHashes_toJson___closed__2);
l_Lake_ModuleOutputHashes_toJson___closed__3 = _init_l_Lake_ModuleOutputHashes_toJson___closed__3();
lean_mark_persistent(l_Lake_ModuleOutputHashes_toJson___closed__3);
l_Lake_instToJsonModuleOutputHashes___closed__0 = _init_l_Lake_instToJsonModuleOutputHashes___closed__0();
lean_mark_persistent(l_Lake_instToJsonModuleOutputHashes___closed__0);
l_Lake_instToJsonModuleOutputHashes = _init_l_Lake_instToJsonModuleOutputHashes();
lean_mark_persistent(l_Lake_instToJsonModuleOutputHashes);
l_Array_fromJson_x3f___at___Lake_ModuleOutputHashes_fromJson_x3f_spec__0___closed__0 = _init_l_Array_fromJson_x3f___at___Lake_ModuleOutputHashes_fromJson_x3f_spec__0___closed__0();
lean_mark_persistent(l_Array_fromJson_x3f___at___Lake_ModuleOutputHashes_fromJson_x3f_spec__0___closed__0);
l_Array_fromJson_x3f___at___Lake_ModuleOutputHashes_fromJson_x3f_spec__0___closed__1 = _init_l_Array_fromJson_x3f___at___Lake_ModuleOutputHashes_fromJson_x3f_spec__0___closed__1();
lean_mark_persistent(l_Array_fromJson_x3f___at___Lake_ModuleOutputHashes_fromJson_x3f_spec__0___closed__1);
l_Option_fromJson_x3f___at___Lake_ModuleOutputHashes_fromJson_x3f_spec__2___closed__0 = _init_l_Option_fromJson_x3f___at___Lake_ModuleOutputHashes_fromJson_x3f_spec__2___closed__0();
lean_mark_persistent(l_Option_fromJson_x3f___at___Lake_ModuleOutputHashes_fromJson_x3f_spec__2___closed__0);
l_Lake_ModuleOutputHashes_fromJson_x3f___closed__0 = _init_l_Lake_ModuleOutputHashes_fromJson_x3f___closed__0();
lean_mark_persistent(l_Lake_ModuleOutputHashes_fromJson_x3f___closed__0);
l_Lake_ModuleOutputHashes_fromJson_x3f___closed__1 = _init_l_Lake_ModuleOutputHashes_fromJson_x3f___closed__1();
lean_mark_persistent(l_Lake_ModuleOutputHashes_fromJson_x3f___closed__1);
l_Lake_ModuleOutputHashes_fromJson_x3f___closed__2 = _init_l_Lake_ModuleOutputHashes_fromJson_x3f___closed__2();
lean_mark_persistent(l_Lake_ModuleOutputHashes_fromJson_x3f___closed__2);
l_Lake_ModuleOutputHashes_fromJson_x3f___closed__3 = _init_l_Lake_ModuleOutputHashes_fromJson_x3f___closed__3();
lean_mark_persistent(l_Lake_ModuleOutputHashes_fromJson_x3f___closed__3);
l_Lake_ModuleOutputHashes_fromJson_x3f___closed__4 = _init_l_Lake_ModuleOutputHashes_fromJson_x3f___closed__4();
lean_mark_persistent(l_Lake_ModuleOutputHashes_fromJson_x3f___closed__4);
l_Lake_ModuleOutputHashes_fromJson_x3f___closed__5 = _init_l_Lake_ModuleOutputHashes_fromJson_x3f___closed__5();
lean_mark_persistent(l_Lake_ModuleOutputHashes_fromJson_x3f___closed__5);
l_Lake_ModuleOutputHashes_fromJson_x3f___closed__6 = _init_l_Lake_ModuleOutputHashes_fromJson_x3f___closed__6();
lean_mark_persistent(l_Lake_ModuleOutputHashes_fromJson_x3f___closed__6);
l_Lake_ModuleOutputHashes_fromJson_x3f___closed__7 = _init_l_Lake_ModuleOutputHashes_fromJson_x3f___closed__7();
lean_mark_persistent(l_Lake_ModuleOutputHashes_fromJson_x3f___closed__7);
l_Lake_ModuleOutputHashes_fromJson_x3f___closed__8 = _init_l_Lake_ModuleOutputHashes_fromJson_x3f___closed__8();
lean_mark_persistent(l_Lake_ModuleOutputHashes_fromJson_x3f___closed__8);
l_Lake_ModuleOutputHashes_fromJson_x3f___closed__9 = _init_l_Lake_ModuleOutputHashes_fromJson_x3f___closed__9();
lean_mark_persistent(l_Lake_ModuleOutputHashes_fromJson_x3f___closed__9);
l_Lake_ModuleOutputHashes_fromJson_x3f___closed__10 = _init_l_Lake_ModuleOutputHashes_fromJson_x3f___closed__10();
lean_mark_persistent(l_Lake_ModuleOutputHashes_fromJson_x3f___closed__10);
l_Lake_ModuleOutputHashes_fromJson_x3f___closed__11 = _init_l_Lake_ModuleOutputHashes_fromJson_x3f___closed__11();
lean_mark_persistent(l_Lake_ModuleOutputHashes_fromJson_x3f___closed__11);
l_Lake_ModuleOutputHashes_fromJson_x3f___closed__12 = _init_l_Lake_ModuleOutputHashes_fromJson_x3f___closed__12();
lean_mark_persistent(l_Lake_ModuleOutputHashes_fromJson_x3f___closed__12);
l_Lake_instFromJsonModuleOutputHashes___closed__0 = _init_l_Lake_instFromJsonModuleOutputHashes___closed__0();
lean_mark_persistent(l_Lake_instFromJsonModuleOutputHashes___closed__0);
l_Lake_instFromJsonModuleOutputHashes = _init_l_Lake_instFromJsonModuleOutputHashes();
lean_mark_persistent(l_Lake_instFromJsonModuleOutputHashes);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

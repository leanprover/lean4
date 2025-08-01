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
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___redArg(lean_object*, lean_object*);
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
static lean_object* l_Lake_ModuleOutputHashes_toJson___closed__4;
static lean_object* l_Lake_ModuleOutputHashes_fromJson_x3f___closed__3;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_fromJson_x3f___at___Lake_ModuleOutputHashes_fromJson_x3f_spec__0_spec__0(size_t, size_t, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lake_ModuleOutputHashes_fromJson_x3f___closed__8;
lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___Lean_Json_Parser_objectCore_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_ModuleOutputHashes_toJson___closed__2;
static lean_object* l_Lake_ModuleOutputHashes_fromJson_x3f___closed__10;
lean_object* l_Lean_bignumToJson(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instFromJsonModuleOutputHashes;
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
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
uint64_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec_ref(x_1);
x_9 = l_Lake_ModuleOutputHashes_oleanHashes___closed__0;
x_10 = lean_box_uint64(x_2);
x_11 = lean_array_push(x_9, x_10);
if (lean_obj_tag(x_3) == 0)
{
x_5 = x_11;
goto block_8;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_dec_ref(x_3);
x_13 = lean_array_push(x_11, x_12);
x_5 = x_13;
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
lean_dec_ref(x_4);
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
x_6 = lean_unsigned_to_nat(0u);
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
x_1 = lean_mk_string_unchecked("c", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_ModuleOutputHashes_toJson___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("b", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_ModuleOutputHashes_toJson___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("o", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_ModuleOutputHashes_toJson___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("i", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_ModuleOutputHashes_toJson___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("r", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_ModuleOutputHashes_toJson(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; uint64_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_2 = lean_ctor_get_uint64(x_1, sizeof(void*)*4 + 8);
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
x_4 = lean_ctor_get_uint64(x_1, sizeof(void*)*4 + 16);
x_5 = lean_ctor_get(x_1, 3);
lean_inc(x_5);
x_27 = lean_box(1);
x_28 = l_Lake_ModuleOutputHashes_toJson___closed__2;
x_29 = l_Lake_ModuleOutputHashes_oleanHashes(x_1);
x_30 = l_Array_toJson___at___Lake_ModuleOutputHashes_toJson_spec__0(x_29);
x_31 = l_Std_DTreeMap_Internal_Impl_insert_x21___at___Lean_Json_Parser_objectCore_spec__0___redArg(x_28, x_30, x_27);
x_32 = l_Lake_ModuleOutputHashes_toJson___closed__3;
x_33 = lean_uint64_to_nat(x_2);
x_34 = l_Lean_bignumToJson(x_33);
x_35 = l_Std_DTreeMap_Internal_Impl_insert_x21___at___Lean_Json_Parser_objectCore_spec__0___redArg(x_32, x_34, x_31);
if (lean_obj_tag(x_3) == 0)
{
x_6 = x_35;
goto block_26;
}
else
{
lean_object* x_36; lean_object* x_37; uint64_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_3, 0);
lean_inc(x_36);
lean_dec_ref(x_3);
x_37 = l_Lake_ModuleOutputHashes_toJson___closed__4;
x_38 = lean_unbox_uint64(x_36);
lean_dec(x_36);
x_39 = lean_uint64_to_nat(x_38);
x_40 = l_Lean_bignumToJson(x_39);
x_41 = l_Std_DTreeMap_Internal_Impl_insert_x21___at___Lean_Json_Parser_objectCore_spec__0___redArg(x_37, x_40, x_35);
x_6 = x_41;
goto block_26;
}
block_26:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lake_ModuleOutputHashes_toJson___closed__0;
x_8 = lean_uint64_to_nat(x_4);
x_9 = l_Lean_bignumToJson(x_8);
x_10 = l_Std_DTreeMap_Internal_Impl_insert_x21___at___Lean_Json_Parser_objectCore_spec__0___redArg(x_7, x_9, x_6);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_5);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint64_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_5, 0);
x_14 = l_Lake_ModuleOutputHashes_toJson___closed__1;
x_15 = lean_unbox_uint64(x_13);
lean_dec(x_13);
x_16 = lean_uint64_to_nat(x_15);
x_17 = l_Lean_bignumToJson(x_16);
x_18 = l_Std_DTreeMap_Internal_Impl_insert_x21___at___Lean_Json_Parser_objectCore_spec__0___redArg(x_14, x_17, x_10);
lean_ctor_set_tag(x_5, 5);
lean_ctor_set(x_5, 0, x_18);
return x_5;
}
else
{
lean_object* x_19; lean_object* x_20; uint64_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_5, 0);
lean_inc(x_19);
lean_dec(x_5);
x_20 = l_Lake_ModuleOutputHashes_toJson___closed__1;
x_21 = lean_unbox_uint64(x_19);
lean_dec(x_19);
x_22 = lean_uint64_to_nat(x_21);
x_23 = l_Lean_bignumToJson(x_22);
x_24 = l_Std_DTreeMap_Internal_Impl_insert_x21___at___Lean_Json_Parser_objectCore_spec__0___redArg(x_20, x_23, x_10);
x_25 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
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
lean_dec_ref(x_3);
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
lean_dec_ref(x_7);
x_12 = lean_unsigned_to_nat(0u);
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
lean_inc_ref(x_2);
lean_dec_ref(x_1);
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
lean_dec_ref(x_8);
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
x_1 = lean_mk_string_unchecked("b: ", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_ModuleOutputHashes_fromJson_x3f___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("r: ", 3, 3);
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
lean_dec_ref(x_2);
x_7 = l_Lake_ModuleOutputHashes_toJson___closed__2;
x_8 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___redArg(x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
lean_dec(x_6);
x_9 = l_Lake_ModuleOutputHashes_fromJson_x3f___closed__1;
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 x_11 = x_8;
} else {
 lean_dec_ref(x_8);
 x_11 = lean_box(0);
}
x_12 = l_Array_fromJson_x3f___at___Lake_ModuleOutputHashes_fromJson_x3f_spec__0(x_10);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_11);
lean_dec(x_6);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = l_Lake_ModuleOutputHashes_fromJson_x3f___closed__2;
x_16 = lean_string_append(x_15, x_14);
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
lean_dec(x_12);
x_18 = l_Lake_ModuleOutputHashes_fromJson_x3f___closed__2;
x_19 = lean_string_append(x_18, x_17);
lean_dec(x_17);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
else
{
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_21; 
lean_dec(x_11);
lean_dec(x_6);
x_21 = !lean_is_exclusive(x_12);
if (x_21 == 0)
{
lean_ctor_set_tag(x_12, 0);
return x_12;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_12, 0);
lean_inc(x_22);
lean_dec(x_12);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_12, 0);
lean_inc(x_24);
lean_dec_ref(x_12);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_array_get_size(x_24);
x_27 = lean_nat_dec_lt(x_25, x_26);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_11);
lean_dec(x_6);
x_28 = l_Lake_ModuleOutputHashes_fromJson_x3f___closed__4;
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = l_Lake_ModuleOutputHashes_toJson___closed__3;
x_30 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___redArg(x_6, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_11);
lean_dec(x_6);
x_31 = l_Lake_ModuleOutputHashes_fromJson_x3f___closed__6;
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_33 = x_30;
} else {
 lean_dec_ref(x_30);
 x_33 = lean_box(0);
}
x_34 = l_UInt64_fromJson_x3f(x_32);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
lean_dec(x_33);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_11);
lean_dec(x_6);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = l_Lake_ModuleOutputHashes_fromJson_x3f___closed__7;
x_38 = lean_string_append(x_37, x_36);
lean_dec(x_36);
lean_ctor_set(x_34, 0, x_38);
return x_34;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_34, 0);
lean_inc(x_39);
lean_dec(x_34);
x_40 = l_Lake_ModuleOutputHashes_fromJson_x3f___closed__7;
x_41 = lean_string_append(x_40, x_39);
lean_dec(x_39);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint64_t x_46; lean_object* x_47; lean_object* x_48; uint64_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_56; lean_object* x_57; uint64_t x_58; lean_object* x_59; lean_object* x_68; uint64_t x_69; lean_object* x_70; lean_object* x_79; lean_object* x_114; lean_object* x_115; 
x_43 = lean_ctor_get(x_34, 0);
lean_inc(x_43);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 x_44 = x_34;
} else {
 lean_dec_ref(x_34);
 x_44 = lean_box(0);
}
x_45 = lean_array_fget(x_24, x_25);
x_46 = lean_unbox_uint64(x_45);
lean_dec(x_45);
x_114 = l_Lake_ModuleOutputHashes_toJson___closed__4;
x_115 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___redArg(x_6, x_114);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; 
x_116 = lean_box(0);
x_79 = x_116;
goto block_113;
}
else
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_ctor_get(x_115, 0);
lean_inc(x_117);
lean_dec_ref(x_115);
x_118 = l_Option_fromJson_x3f___at___Lake_ModuleOutputHashes_fromJson_x3f_spec__2(x_117);
if (lean_obj_tag(x_118) == 0)
{
uint8_t x_119; 
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_33);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_11);
lean_dec(x_6);
x_119 = !lean_is_exclusive(x_118);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_118, 0);
x_121 = l_Lake_ModuleOutputHashes_fromJson_x3f___closed__12;
x_122 = lean_string_append(x_121, x_120);
lean_dec(x_120);
lean_ctor_set(x_118, 0, x_122);
return x_118;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_123 = lean_ctor_get(x_118, 0);
lean_inc(x_123);
lean_dec(x_118);
x_124 = l_Lake_ModuleOutputHashes_fromJson_x3f___closed__12;
x_125 = lean_string_append(x_124, x_123);
lean_dec(x_123);
x_126 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_126, 0, x_125);
return x_126;
}
}
else
{
if (lean_obj_tag(x_118) == 0)
{
uint8_t x_127; 
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_33);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_11);
lean_dec(x_6);
x_127 = !lean_is_exclusive(x_118);
if (x_127 == 0)
{
lean_ctor_set_tag(x_118, 0);
return x_118;
}
else
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_118, 0);
lean_inc(x_128);
lean_dec(x_118);
x_129 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_129, 0, x_128);
return x_129;
}
}
else
{
lean_object* x_130; 
x_130 = lean_ctor_get(x_118, 0);
lean_inc(x_130);
lean_dec_ref(x_118);
x_79 = x_130;
goto block_113;
}
}
}
block_55:
{
lean_object* x_52; uint64_t x_53; lean_object* x_54; 
x_52 = lean_alloc_ctor(0, 4, 24);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_52, 2, x_47);
lean_ctor_set(x_52, 3, x_48);
lean_ctor_set_uint64(x_52, sizeof(void*)*4, x_46);
x_53 = lean_unbox_uint64(x_43);
lean_dec(x_43);
lean_ctor_set_uint64(x_52, sizeof(void*)*4 + 8, x_53);
lean_ctor_set_uint64(x_52, sizeof(void*)*4 + 16, x_49);
if (lean_is_scalar(x_44)) {
 x_54 = lean_alloc_ctor(1, 1, 0);
} else {
 x_54 = x_44;
}
lean_ctor_set(x_54, 0, x_52);
return x_54;
}
block_67:
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_unsigned_to_nat(2u);
x_61 = lean_nat_dec_lt(x_60, x_26);
lean_dec(x_26);
if (x_61 == 0)
{
lean_object* x_62; 
lean_dec(x_33);
lean_dec(x_24);
x_62 = lean_box(0);
x_47 = x_56;
x_48 = x_57;
x_49 = x_58;
x_50 = x_59;
x_51 = x_62;
goto block_55;
}
else
{
lean_object* x_63; uint64_t x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_array_fget(x_24, x_60);
lean_dec(x_24);
x_64 = lean_unbox_uint64(x_63);
lean_dec(x_63);
x_65 = lean_box_uint64(x_64);
if (lean_is_scalar(x_33)) {
 x_66 = lean_alloc_ctor(1, 1, 0);
} else {
 x_66 = x_33;
}
lean_ctor_set(x_66, 0, x_65);
x_47 = x_56;
x_48 = x_57;
x_49 = x_58;
x_50 = x_59;
x_51 = x_66;
goto block_55;
}
}
block_78:
{
lean_object* x_71; uint8_t x_72; 
x_71 = lean_unsigned_to_nat(1u);
x_72 = lean_nat_dec_lt(x_71, x_26);
if (x_72 == 0)
{
lean_object* x_73; 
lean_dec(x_11);
x_73 = lean_box(0);
x_56 = x_68;
x_57 = x_70;
x_58 = x_69;
x_59 = x_73;
goto block_67;
}
else
{
lean_object* x_74; uint64_t x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_array_fget(x_24, x_71);
x_75 = lean_unbox_uint64(x_74);
lean_dec(x_74);
x_76 = lean_box_uint64(x_75);
if (lean_is_scalar(x_11)) {
 x_77 = lean_alloc_ctor(1, 1, 0);
} else {
 x_77 = x_11;
}
lean_ctor_set(x_77, 0, x_76);
x_56 = x_68;
x_57 = x_70;
x_58 = x_69;
x_59 = x_77;
goto block_67;
}
}
block_113:
{
lean_object* x_80; lean_object* x_81; 
x_80 = l_Lake_ModuleOutputHashes_toJson___closed__0;
x_81 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___redArg(x_6, x_80);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; 
lean_dec(x_79);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_33);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_11);
lean_dec(x_6);
x_82 = l_Lake_ModuleOutputHashes_fromJson_x3f___closed__9;
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_81, 0);
lean_inc(x_83);
lean_dec_ref(x_81);
x_84 = l_UInt64_fromJson_x3f(x_83);
if (lean_obj_tag(x_84) == 0)
{
uint8_t x_85; 
lean_dec(x_79);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_33);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_11);
lean_dec(x_6);
x_85 = !lean_is_exclusive(x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_84, 0);
x_87 = l_Lake_ModuleOutputHashes_fromJson_x3f___closed__10;
x_88 = lean_string_append(x_87, x_86);
lean_dec(x_86);
lean_ctor_set(x_84, 0, x_88);
return x_84;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_84, 0);
lean_inc(x_89);
lean_dec(x_84);
x_90 = l_Lake_ModuleOutputHashes_fromJson_x3f___closed__10;
x_91 = lean_string_append(x_90, x_89);
lean_dec(x_89);
x_92 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_92, 0, x_91);
return x_92;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_84, 0);
lean_inc(x_93);
lean_dec_ref(x_84);
x_94 = l_Lake_ModuleOutputHashes_toJson___closed__1;
x_95 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___redArg(x_6, x_94);
lean_dec(x_6);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; uint64_t x_97; 
x_96 = lean_box(0);
x_97 = lean_unbox_uint64(x_93);
lean_dec(x_93);
x_68 = x_79;
x_69 = x_97;
x_70 = x_96;
goto block_78;
}
else
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_95, 0);
lean_inc(x_98);
lean_dec_ref(x_95);
x_99 = l_Option_fromJson_x3f___at___Lake_ModuleOutputHashes_fromJson_x3f_spec__2(x_98);
if (lean_obj_tag(x_99) == 0)
{
uint8_t x_100; 
lean_dec(x_93);
lean_dec(x_79);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_33);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_11);
x_100 = !lean_is_exclusive(x_99);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_99, 0);
x_102 = l_Lake_ModuleOutputHashes_fromJson_x3f___closed__11;
x_103 = lean_string_append(x_102, x_101);
lean_dec(x_101);
lean_ctor_set(x_99, 0, x_103);
return x_99;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_104 = lean_ctor_get(x_99, 0);
lean_inc(x_104);
lean_dec(x_99);
x_105 = l_Lake_ModuleOutputHashes_fromJson_x3f___closed__11;
x_106 = lean_string_append(x_105, x_104);
lean_dec(x_104);
x_107 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_107, 0, x_106);
return x_107;
}
}
else
{
if (lean_obj_tag(x_99) == 0)
{
uint8_t x_108; 
lean_dec(x_93);
lean_dec(x_79);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_33);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_11);
x_108 = !lean_is_exclusive(x_99);
if (x_108 == 0)
{
lean_ctor_set_tag(x_99, 0);
return x_99;
}
else
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_99, 0);
lean_inc(x_109);
lean_dec(x_99);
x_110 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_110, 0, x_109);
return x_110;
}
}
else
{
lean_object* x_111; uint64_t x_112; 
x_111 = lean_ctor_get(x_99, 0);
lean_inc(x_111);
lean_dec_ref(x_99);
x_112 = lean_unbox_uint64(x_93);
lean_dec(x_93);
x_68 = x_79;
x_69 = x_112;
x_70 = x_111;
goto block_78;
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
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; lean_object* x_10; lean_object* x_11; uint64_t x_12; lean_object* x_13; lean_object* x_30; lean_object* x_31; lean_object* x_45; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 4);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 5);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_1, 6);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
lean_dec_ref(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_56; 
x_56 = lean_box(0);
x_45 = x_56;
goto block_55;
}
else
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_3);
if (x_57 == 0)
{
lean_object* x_58; uint64_t x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_3, 0);
x_59 = lean_ctor_get_uint64(x_58, sizeof(void*)*3);
lean_dec(x_58);
x_60 = lean_box_uint64(x_59);
lean_ctor_set(x_3, 0, x_60);
x_45 = x_3;
goto block_55;
}
else
{
lean_object* x_61; uint64_t x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_3, 0);
lean_inc(x_61);
lean_dec(x_3);
x_62 = lean_ctor_get_uint64(x_61, sizeof(void*)*3);
lean_dec(x_61);
x_63 = lean_box_uint64(x_62);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_45 = x_64;
goto block_55;
}
}
block_29:
{
if (lean_obj_tag(x_8) == 0)
{
uint64_t x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get_uint64(x_7, sizeof(void*)*3);
lean_dec_ref(x_7);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 4, 24);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 2, x_13);
lean_ctor_set(x_16, 3, x_15);
lean_ctor_set_uint64(x_16, sizeof(void*)*4, x_9);
lean_ctor_set_uint64(x_16, sizeof(void*)*4 + 8, x_12);
lean_ctor_set_uint64(x_16, sizeof(void*)*4 + 16, x_14);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
lean_object* x_18; uint64_t x_19; uint64_t x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_8, 0);
x_19 = lean_ctor_get_uint64(x_7, sizeof(void*)*3);
lean_dec_ref(x_7);
x_20 = lean_ctor_get_uint64(x_18, sizeof(void*)*3);
lean_dec(x_18);
x_21 = lean_box_uint64(x_20);
lean_ctor_set(x_8, 0, x_21);
x_22 = lean_alloc_ctor(0, 4, 24);
lean_ctor_set(x_22, 0, x_10);
lean_ctor_set(x_22, 1, x_11);
lean_ctor_set(x_22, 2, x_13);
lean_ctor_set(x_22, 3, x_8);
lean_ctor_set_uint64(x_22, sizeof(void*)*4, x_9);
lean_ctor_set_uint64(x_22, sizeof(void*)*4 + 8, x_12);
lean_ctor_set_uint64(x_22, sizeof(void*)*4 + 16, x_19);
return x_22;
}
else
{
lean_object* x_23; uint64_t x_24; uint64_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_8, 0);
lean_inc(x_23);
lean_dec(x_8);
x_24 = lean_ctor_get_uint64(x_7, sizeof(void*)*3);
lean_dec_ref(x_7);
x_25 = lean_ctor_get_uint64(x_23, sizeof(void*)*3);
lean_dec(x_23);
x_26 = lean_box_uint64(x_25);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(0, 4, 24);
lean_ctor_set(x_28, 0, x_10);
lean_ctor_set(x_28, 1, x_11);
lean_ctor_set(x_28, 2, x_13);
lean_ctor_set(x_28, 3, x_27);
lean_ctor_set_uint64(x_28, sizeof(void*)*4, x_9);
lean_ctor_set_uint64(x_28, sizeof(void*)*4 + 8, x_12);
lean_ctor_set_uint64(x_28, sizeof(void*)*4 + 16, x_24);
return x_28;
}
}
}
block_44:
{
if (lean_obj_tag(x_6) == 0)
{
uint64_t x_32; lean_object* x_33; 
x_32 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_dec_ref(x_5);
x_33 = lean_box(0);
x_10 = x_30;
x_11 = x_31;
x_12 = x_32;
x_13 = x_33;
goto block_29;
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_6);
if (x_34 == 0)
{
lean_object* x_35; uint64_t x_36; uint64_t x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_6, 0);
x_36 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_dec_ref(x_5);
x_37 = lean_ctor_get_uint64(x_35, sizeof(void*)*3);
lean_dec(x_35);
x_38 = lean_box_uint64(x_37);
lean_ctor_set(x_6, 0, x_38);
x_10 = x_30;
x_11 = x_31;
x_12 = x_36;
x_13 = x_6;
goto block_29;
}
else
{
lean_object* x_39; uint64_t x_40; uint64_t x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_6, 0);
lean_inc(x_39);
lean_dec(x_6);
x_40 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_dec_ref(x_5);
x_41 = lean_ctor_get_uint64(x_39, sizeof(void*)*3);
lean_dec(x_39);
x_42 = lean_box_uint64(x_41);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_10 = x_30;
x_11 = x_31;
x_12 = x_40;
x_13 = x_43;
goto block_29;
}
}
}
block_55:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_46; 
x_46 = lean_box(0);
x_30 = x_45;
x_31 = x_46;
goto block_44;
}
else
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_4);
if (x_47 == 0)
{
lean_object* x_48; uint64_t x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_4, 0);
x_49 = lean_ctor_get_uint64(x_48, sizeof(void*)*3);
lean_dec(x_48);
x_50 = lean_box_uint64(x_49);
lean_ctor_set(x_4, 0, x_50);
x_30 = x_45;
x_31 = x_4;
goto block_44;
}
else
{
lean_object* x_51; uint64_t x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_4, 0);
lean_inc(x_51);
lean_dec(x_4);
x_52 = lean_ctor_get_uint64(x_51, sizeof(void*)*3);
lean_dec(x_51);
x_53 = lean_box_uint64(x_52);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_30 = x_45;
x_31 = x_54;
goto block_44;
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
l_Lake_ModuleOutputHashes_toJson___closed__4 = _init_l_Lake_ModuleOutputHashes_toJson___closed__4();
lean_mark_persistent(l_Lake_ModuleOutputHashes_toJson___closed__4);
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

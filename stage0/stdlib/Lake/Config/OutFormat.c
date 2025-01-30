// Lean compiler output
// Module: Lake.Config.OutFormat
// Imports: Lean.Data.Json Lake.Build.Job.Basic
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
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
static lean_object* l_Lake_instToTextArray___rarg___closed__5;
static lean_object* l_Lake_instToTextArray___rarg___closed__3;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_instToTextArray___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToTextOfToString___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToTextOfToString(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_OutFormat_noConfusion(lean_object*);
static lean_object* l_Lake_instToTextArray___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lake_OutFormat_noConfusion___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Lake_instToTextList___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToTextList___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instFormatQueryOfToTextOfToJson(lean_object*);
LEAN_EXPORT lean_object* l_Lake_stdFormat___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutFormat_noConfusion___rarg___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutFormat_noConfusion___rarg(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instFormatQueryUnit;
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instFormatQuery(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToTextArray___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_nullFormat___rarg(uint8_t, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_stdFormat(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Lake_instToTextList___spec__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToTextJson;
LEAN_EXPORT lean_object* l_Lake_instToTextOfToString___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_nullFormat___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instFormatQueryOfToTextOfToJson___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutFormat_noConfusion___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_nullFormat___rarg___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_instToTextArray___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_nullFormat(lean_object*);
static lean_object* l_Lake_instToTextJson___closed__1;
static lean_object* l_Lake_instToTextArray___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lake_stdFormat___rarg(lean_object*, lean_object*, uint8_t, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToTextList(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_instToTextArray___spec__1___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_List_foldl___at_Lake_instToTextList___spec__1___rarg___closed__2;
static lean_object* l_Lake_instToTextArray___rarg___closed__4;
lean_object* l_Substring_prevn(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToTextArray___rarg___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_instFormatQuery___closed__1;
LEAN_EXPORT lean_object* l_Lake_instToTextArray(lean_object*);
static lean_object* l_List_foldl___at_Lake_instToTextList___spec__1___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lake_OutFormat_toCtorIdx___boxed(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lake_OutFormat_toCtorIdx(uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lake_OutFormat_noConfusion___rarg___closed__1;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lake_instToTextArray___rarg___closed__6;
LEAN_EXPORT lean_object* l_Lake_OutFormat_toCtorIdx(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OutFormat_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lake_OutFormat_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_OutFormat_noConfusion___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Lake_OutFormat_noConfusion___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_OutFormat_noConfusion___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_OutFormat_noConfusion___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_OutFormat_noConfusion___rarg___closed__1;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_OutFormat_noConfusion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_OutFormat_noConfusion___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_OutFormat_noConfusion___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_OutFormat_noConfusion___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_OutFormat_noConfusion___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lake_OutFormat_noConfusion___rarg(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTextOfToString___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTextOfToString(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_instToTextOfToString___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTextOfToString___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_instToTextOfToString___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instToTextJson___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Json_compress), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instToTextJson() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instToTextJson___closed__1;
return x_1;
}
}
static lean_object* _init_l_List_foldl___at_Lake_instToTextList___spec__1___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_List_foldl___at_Lake_instToTextList___spec__1___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lake_instToTextList___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_List_foldl___at_Lake_instToTextList___spec__1___rarg___closed__1;
x_7 = lean_string_append(x_6, x_2);
lean_dec(x_2);
x_8 = lean_string_append(x_7, x_6);
lean_inc(x_1);
x_9 = lean_apply_1(x_1, x_4);
x_10 = lean_string_append(x_8, x_9);
lean_dec(x_9);
x_11 = l_List_foldl___at_Lake_instToTextList___spec__1___rarg___closed__2;
x_12 = lean_string_append(x_10, x_11);
x_2 = x_12;
x_3 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lake_instToTextList___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_foldl___at_Lake_instToTextList___spec__1___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTextList___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_3 = l_List_foldl___at_Lake_instToTextList___spec__1___rarg___closed__1;
x_4 = l_List_foldl___at_Lake_instToTextList___spec__1___rarg(x_1, x_3, x_2);
x_5 = lean_string_utf8_byte_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
lean_inc(x_5);
lean_inc(x_4);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
lean_ctor_set(x_7, 2, x_5);
x_8 = lean_nat_sub(x_5, x_6);
lean_dec(x_5);
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Substring_prevn(x_7, x_9, x_8);
lean_dec(x_7);
x_11 = lean_nat_add(x_6, x_10);
lean_dec(x_10);
x_12 = lean_string_utf8_extract(x_4, x_6, x_11);
lean_dec(x_11);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTextList(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_instToTextList___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_instToTextArray___spec__1___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = l_List_foldl___at_Lake_instToTextList___spec__1___rarg___closed__1;
x_9 = lean_string_append(x_8, x_5);
lean_dec(x_5);
x_10 = lean_string_append(x_9, x_8);
lean_inc(x_1);
x_11 = lean_apply_1(x_1, x_7);
x_12 = lean_string_append(x_10, x_11);
lean_dec(x_11);
x_13 = l_List_foldl___at_Lake_instToTextList___spec__1___rarg___closed__2;
x_14 = lean_string_append(x_12, x_13);
x_15 = 1;
x_16 = lean_usize_add(x_3, x_15);
x_3 = x_16;
x_5 = x_14;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_instToTextArray___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lake_instToTextArray___spec__1___rarg___boxed), 5, 0);
return x_2;
}
}
static lean_object* _init_l_Lake_instToTextArray___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldl___at_Lake_instToTextList___spec__1___rarg___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instToTextArray___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_List_foldl___at_Lake_instToTextList___spec__1___rarg___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lake_instToTextArray___rarg___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_instToTextArray___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_instToTextArray___rarg___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_sub(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instToTextArray___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_instToTextArray___rarg___closed__2;
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Lake_instToTextArray___rarg___closed__3;
x_4 = l_Substring_prevn(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_instToTextArray___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lake_instToTextArray___rarg___closed__4;
x_3 = lean_nat_add(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instToTextArray___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_List_foldl___at_Lake_instToTextList___spec__1___rarg___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lake_instToTextArray___rarg___closed__5;
x_4 = lean_string_utf8_extract(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTextArray___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_1);
x_6 = l_Lake_instToTextArray___rarg___closed__6;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_3, x_3);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_1);
x_8 = l_Lake_instToTextArray___rarg___closed__6;
return x_8;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_11 = l_List_foldl___at_Lake_instToTextList___spec__1___rarg___closed__1;
x_12 = l_Array_foldlMUnsafe_fold___at_Lake_instToTextArray___spec__1___rarg(x_1, x_2, x_9, x_10, x_11);
x_13 = lean_string_utf8_byte_size(x_12);
lean_inc(x_13);
lean_inc(x_12);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_4);
lean_ctor_set(x_14, 2, x_13);
x_15 = lean_nat_sub(x_13, x_4);
lean_dec(x_13);
x_16 = lean_unsigned_to_nat(1u);
x_17 = l_Substring_prevn(x_14, x_16, x_15);
lean_dec(x_14);
x_18 = lean_nat_add(x_4, x_17);
lean_dec(x_17);
x_19 = lean_string_utf8_extract(x_12, x_4, x_18);
lean_dec(x_18);
lean_dec(x_12);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instToTextArray(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_instToTextArray___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_instToTextArray___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lake_instToTextArray___spec__1___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTextArray___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_instToTextArray___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_nullFormat___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Json_compress(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_nullFormat___rarg(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
lean_object* x_3; 
x_3 = l_List_foldl___at_Lake_instToTextList___spec__1___rarg___closed__1;
return x_3;
}
else
{
lean_object* x_4; 
x_4 = l_Lake_nullFormat___rarg___closed__1;
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lake_nullFormat(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_nullFormat___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_nullFormat___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_nullFormat___rarg(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_instFormatQuery___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_nullFormat___rarg___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instFormatQuery(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_instFormatQuery___closed__1;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_stdFormat___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
if (x_3 == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_4);
x_7 = l_Lean_Json_compress(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lake_stdFormat(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_stdFormat___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_stdFormat___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_Lake_stdFormat___rarg(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_instFormatQueryOfToTextOfToJson___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_stdFormat___rarg___boxed), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instFormatQueryOfToTextOfToJson(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_instFormatQueryOfToTextOfToJson___rarg), 2, 0);
return x_2;
}
}
static lean_object* _init_l_Lake_instFormatQueryUnit() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instFormatQuery___closed__1;
return x_1;
}
}
lean_object* initialize_Lean_Data_Json(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Job_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_OutFormat(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Json(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Job_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_OutFormat_noConfusion___rarg___closed__1 = _init_l_Lake_OutFormat_noConfusion___rarg___closed__1();
lean_mark_persistent(l_Lake_OutFormat_noConfusion___rarg___closed__1);
l_Lake_instToTextJson___closed__1 = _init_l_Lake_instToTextJson___closed__1();
lean_mark_persistent(l_Lake_instToTextJson___closed__1);
l_Lake_instToTextJson = _init_l_Lake_instToTextJson();
lean_mark_persistent(l_Lake_instToTextJson);
l_List_foldl___at_Lake_instToTextList___spec__1___rarg___closed__1 = _init_l_List_foldl___at_Lake_instToTextList___spec__1___rarg___closed__1();
lean_mark_persistent(l_List_foldl___at_Lake_instToTextList___spec__1___rarg___closed__1);
l_List_foldl___at_Lake_instToTextList___spec__1___rarg___closed__2 = _init_l_List_foldl___at_Lake_instToTextList___spec__1___rarg___closed__2();
lean_mark_persistent(l_List_foldl___at_Lake_instToTextList___spec__1___rarg___closed__2);
l_Lake_instToTextArray___rarg___closed__1 = _init_l_Lake_instToTextArray___rarg___closed__1();
lean_mark_persistent(l_Lake_instToTextArray___rarg___closed__1);
l_Lake_instToTextArray___rarg___closed__2 = _init_l_Lake_instToTextArray___rarg___closed__2();
lean_mark_persistent(l_Lake_instToTextArray___rarg___closed__2);
l_Lake_instToTextArray___rarg___closed__3 = _init_l_Lake_instToTextArray___rarg___closed__3();
lean_mark_persistent(l_Lake_instToTextArray___rarg___closed__3);
l_Lake_instToTextArray___rarg___closed__4 = _init_l_Lake_instToTextArray___rarg___closed__4();
lean_mark_persistent(l_Lake_instToTextArray___rarg___closed__4);
l_Lake_instToTextArray___rarg___closed__5 = _init_l_Lake_instToTextArray___rarg___closed__5();
lean_mark_persistent(l_Lake_instToTextArray___rarg___closed__5);
l_Lake_instToTextArray___rarg___closed__6 = _init_l_Lake_instToTextArray___rarg___closed__6();
lean_mark_persistent(l_Lake_instToTextArray___rarg___closed__6);
l_Lake_nullFormat___rarg___closed__1 = _init_l_Lake_nullFormat___rarg___closed__1();
lean_mark_persistent(l_Lake_nullFormat___rarg___closed__1);
l_Lake_instFormatQuery___closed__1 = _init_l_Lake_instFormatQuery___closed__1();
lean_mark_persistent(l_Lake_instFormatQuery___closed__1);
l_Lake_instFormatQueryUnit = _init_l_Lake_instFormatQueryUnit();
lean_mark_persistent(l_Lake_instFormatQueryUnit);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

// Lean compiler output
// Module: Init.Data.Hashable
// Imports: Init.Data.UInt Init.Data.String
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
lean_object* l_instHashableProd_match__1(lean_object*, lean_object*, lean_object*);
size_t l_UInt32_toUSize(uint32_t);
size_t l_instHashableProd___rarg(lean_object*, lean_object*, lean_object*);
size_t l_instHashableUSize(size_t);
lean_object* l_instHashableList(lean_object*);
lean_object* l_instHashableUSize___boxed(lean_object*);
lean_object* l_List_foldl___at_instHashableList___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
size_t l_Option_hash___rarg(lean_object*, lean_object*);
size_t l_instHashableBool(uint8_t);
lean_object* l_instHashableOption(lean_object*);
size_t l_instHashableInt(lean_object*);
lean_object* l_instHashable___closed__1___boxed__const__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Option_hash_match__1(lean_object*, lean_object*);
size_t l_UInt64_toUSize(uint64_t);
lean_object* l_List_foldl___at_instHashableList___spec__1(lean_object*);
lean_object* l_Function_const___rarg___boxed(lean_object*, lean_object*);
lean_object* l_instHashableUInt64___boxed(lean_object*);
lean_object* l_instHashableProd(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_instHashable___closed__1;
lean_object* l_instHashableBool_match__1(lean_object*);
lean_object* l_Option_hash___rarg___boxed(lean_object*, lean_object*);
lean_object* l_instHashableBool_match__1___rarg(uint8_t, lean_object*, lean_object*);
size_t l_instHashableUInt64(uint64_t);
lean_object* l_instHashableInt_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instHashableList___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Option_hash_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_instHashableUInt32___boxed(lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t l_instHashableNat(lean_object*);
size_t l_instHashableList___rarg(lean_object*, lean_object*);
lean_object* l_instHashableOption___rarg___boxed(lean_object*, lean_object*);
lean_object* l_instHashableInt_match__1___rarg(lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Int_instInhabitedInt___closed__1;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* l_instHashableInt_match__1(lean_object*);
lean_object* l_instHashableBool_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instHashableProd___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instHashableNat___boxed(lean_object*);
size_t lean_usize_mix_hash(size_t, size_t);
lean_object* l_instHashable(lean_object*);
size_t l_instHashableOption___rarg(lean_object*, lean_object*);
lean_object* l_instHashableProd_match__1___rarg(lean_object*, lean_object*);
lean_object* l_instHashableBool___boxed(lean_object*);
size_t l_instHashableUInt32(uint32_t);
lean_object* l_Option_hash(lean_object*);
size_t l_List_foldl___at_instHashableList___spec__1___rarg(lean_object*, size_t, lean_object*);
lean_object* l_instHashableInt___boxed(lean_object*);
size_t l_instHashableNat(lean_object* x_1) {
_start:
{
size_t x_2; 
x_2 = lean_usize_of_nat(x_1);
return x_2;
}
}
lean_object* l_instHashableNat___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = l_instHashableNat(x_1);
lean_dec(x_1);
x_3 = lean_box_usize(x_2);
return x_3;
}
}
lean_object* l_instHashableProd_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_instHashableProd_match__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_instHashableProd_match__1___rarg), 2, 0);
return x_4;
}
}
size_t l_instHashableProd___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_apply_1(x_1, x_4);
x_7 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_8 = lean_apply_1(x_2, x_5);
x_9 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_10 = lean_usize_mix_hash(x_7, x_9);
return x_10;
}
}
lean_object* l_instHashableProd(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_instHashableProd___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* l_instHashableProd___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = l_instHashableProd___rarg(x_1, x_2, x_3);
x_5 = lean_box_usize(x_4);
return x_5;
}
}
lean_object* l_instHashableBool_match__1___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (x_1 == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_instHashableBool_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instHashableBool_match__1___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_instHashableBool_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_instHashableBool_match__1___rarg(x_4, x_2, x_3);
return x_5;
}
}
size_t l_instHashableBool(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
size_t x_2; 
x_2 = 13;
return x_2;
}
else
{
size_t x_3; 
x_3 = 11;
return x_3;
}
}
}
lean_object* l_instHashableBool___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; size_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_instHashableBool(x_2);
x_4 = lean_box_usize(x_3);
return x_4;
}
}
lean_object* l_Option_hash_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l_Option_hash_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Option_hash_match__1___rarg), 3, 0);
return x_3;
}
}
size_t l_Option_hash___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
size_t x_3; 
lean_dec(x_1);
x_3 = 11;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_apply_1(x_1, x_4);
x_6 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_7 = 13;
x_8 = lean_usize_mix_hash(x_6, x_7);
return x_8;
}
}
}
lean_object* l_Option_hash(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Option_hash___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Option_hash___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; 
x_3 = l_Option_hash___rarg(x_1, x_2);
x_4 = lean_box_usize(x_3);
return x_4;
}
}
size_t l_instHashableOption___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
size_t x_3; 
lean_dec(x_1);
x_3 = 11;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_apply_1(x_1, x_4);
x_6 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_7 = 13;
x_8 = lean_usize_mix_hash(x_6, x_7);
return x_8;
}
}
}
lean_object* l_instHashableOption(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instHashableOption___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_instHashableOption___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; 
x_3 = l_instHashableOption___rarg(x_1, x_2);
x_4 = lean_box_usize(x_3);
return x_4;
}
}
size_t l_List_foldl___at_instHashableList___spec__1___rarg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
lean_inc(x_1);
x_6 = lean_apply_1(x_1, x_4);
x_7 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_8 = lean_usize_mix_hash(x_2, x_7);
x_2 = x_8;
x_3 = x_5;
goto _start;
}
}
}
lean_object* l_List_foldl___at_instHashableList___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_foldl___at_instHashableList___spec__1___rarg___boxed), 3, 0);
return x_2;
}
}
size_t l_instHashableList___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; 
x_3 = 7;
x_4 = l_List_foldl___at_instHashableList___spec__1___rarg(x_1, x_3, x_2);
return x_4;
}
}
lean_object* l_instHashableList(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instHashableList___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_List_foldl___at_instHashableList___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_List_foldl___at_instHashableList___spec__1___rarg(x_1, x_4, x_3);
x_6 = lean_box_usize(x_5);
return x_6;
}
}
lean_object* l_instHashableList___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; 
x_3 = l_instHashableList___rarg(x_1, x_2);
x_4 = lean_box_usize(x_3);
return x_4;
}
}
size_t l_instHashableUInt32(uint32_t x_1) {
_start:
{
size_t x_2; 
x_2 = x_1;
return x_2;
}
}
lean_object* l_instHashableUInt32___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; size_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_instHashableUInt32(x_2);
x_4 = lean_box_usize(x_3);
return x_4;
}
}
size_t l_instHashableUInt64(uint64_t x_1) {
_start:
{
size_t x_2; 
x_2 = ((size_t)x_1);
return x_2;
}
}
lean_object* l_instHashableUInt64___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; size_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = l_instHashableUInt64(x_2);
x_4 = lean_box_usize(x_3);
return x_4;
}
}
size_t l_instHashableUSize(size_t x_1) {
_start:
{
return x_1;
}
}
lean_object* l_instHashableUSize___boxed(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; lean_object* x_4; 
x_2 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_3 = l_instHashableUSize(x_2);
x_4 = lean_box_usize(x_3);
return x_4;
}
}
lean_object* l_instHashableInt_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Int_instInhabitedInt___closed__1;
x_5 = lean_int_dec_lt(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_nat_abs(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_8 = lean_nat_abs(x_1);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_8, x_9);
lean_dec(x_8);
x_11 = lean_apply_1(x_3, x_10);
return x_11;
}
}
}
lean_object* l_instHashableInt_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instHashableInt_match__1___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_instHashableInt_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_instHashableInt_match__1___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
size_t l_instHashableInt(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Int_instInhabitedInt___closed__1;
x_3 = lean_int_dec_lt(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; 
x_4 = lean_nat_abs(x_1);
x_5 = lean_unsigned_to_nat(2u);
x_6 = lean_nat_mul(x_5, x_4);
lean_dec(x_4);
x_7 = lean_usize_of_nat(x_6);
lean_dec(x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; 
x_8 = lean_nat_abs(x_1);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_8, x_9);
lean_dec(x_8);
x_11 = lean_unsigned_to_nat(2u);
x_12 = lean_nat_mul(x_11, x_10);
lean_dec(x_10);
x_13 = lean_nat_add(x_12, x_9);
lean_dec(x_12);
x_14 = lean_usize_of_nat(x_13);
lean_dec(x_13);
return x_14;
}
}
}
lean_object* l_instHashableInt___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = l_instHashableInt(x_1);
lean_dec(x_1);
x_3 = lean_box_usize(x_2);
return x_3;
}
}
static lean_object* _init_l_instHashable___closed__1___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
static lean_object* _init_l_instHashable___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instHashable___closed__1___boxed__const__1;
x_2 = lean_alloc_closure((void*)(l_Function_const___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_instHashable(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instHashable___closed__1;
return x_2;
}
}
lean_object* initialize_Init_Data_UInt(lean_object*);
lean_object* initialize_Init_Data_String(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Data_Hashable(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_UInt(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_instHashable___closed__1___boxed__const__1 = _init_l_instHashable___closed__1___boxed__const__1();
lean_mark_persistent(l_instHashable___closed__1___boxed__const__1);
l_instHashable___closed__1 = _init_l_instHashable___closed__1();
lean_mark_persistent(l_instHashable___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

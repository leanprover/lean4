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
LEAN_EXPORT uint64_t l_instHashableProd___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_instHashableUSize(size_t);
LEAN_EXPORT lean_object* l_instHashableList(lean_object*);
LEAN_EXPORT lean_object* l_instHashableUSize___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_instHashableList___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instHashable___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_instHashableBool(uint8_t);
LEAN_EXPORT lean_object* l_instHashableOption(lean_object*);
LEAN_EXPORT uint64_t l_instHashableInt(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instHashableFin___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_instHashableList___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_instHashableUInt64___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instHashableProd(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
LEAN_EXPORT uint64_t l_instHashableUInt64(uint64_t);
LEAN_EXPORT lean_object* l_instHashableList___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instHashableUInt32___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instHashableFin(lean_object*);
LEAN_EXPORT uint64_t l_instHashableNat(lean_object*);
LEAN_EXPORT lean_object* l_instHashableFin___rarg___boxed(lean_object*);
LEAN_EXPORT uint64_t l_instHashableList___rarg(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_instHashableFin___rarg(lean_object*);
LEAN_EXPORT lean_object* l_instHashableOption___rarg___boxed(lean_object*, lean_object*);
uint64_t l_USize_toUInt64(size_t);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
uint64_t l_UInt32_toUInt64(uint32_t);
LEAN_EXPORT lean_object* l_instHashableProd___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instHashableNat___boxed(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT uint64_t l_instHashable(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_instHashableOption___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instHashableBool___boxed(lean_object*);
LEAN_EXPORT uint64_t l_instHashableUInt32(uint32_t);
LEAN_EXPORT uint64_t l_List_foldl___at_instHashableList___spec__1___rarg(lean_object*, uint64_t, lean_object*);
static lean_object* l_instHashableInt___closed__1;
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_instHashableInt___boxed(lean_object*);
LEAN_EXPORT uint64_t l_instHashableNat(lean_object* x_1) {
_start:
{
uint64_t x_2; 
x_2 = lean_uint64_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instHashableNat___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_instHashableNat(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT uint64_t l_instHashableProd___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_apply_1(x_1, x_4);
x_7 = lean_unbox_uint64(x_6);
lean_dec(x_6);
x_8 = lean_apply_1(x_2, x_5);
x_9 = lean_unbox_uint64(x_8);
lean_dec(x_8);
x_10 = lean_uint64_mix_hash(x_7, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_instHashableProd(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_instHashableProd___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instHashableProd___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = l_instHashableProd___rarg(x_1, x_2, x_3);
x_5 = lean_box_uint64(x_4);
return x_5;
}
}
LEAN_EXPORT uint64_t l_instHashableBool(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
uint64_t x_2; 
x_2 = 13;
return x_2;
}
else
{
uint64_t x_3; 
x_3 = 11;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_instHashableBool___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint64_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_instHashableBool(x_2);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
LEAN_EXPORT uint64_t l_instHashableOption___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint64_t x_3; 
lean_dec(x_1);
x_3 = 11;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_apply_1(x_1, x_4);
x_6 = lean_unbox_uint64(x_5);
lean_dec(x_5);
x_7 = 13;
x_8 = lean_uint64_mix_hash(x_6, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_instHashableOption(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instHashableOption___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instHashableOption___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = l_instHashableOption___rarg(x_1, x_2);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
LEAN_EXPORT uint64_t l_List_foldl___at_instHashableList___spec__1___rarg(lean_object* x_1, uint64_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
lean_inc(x_1);
x_6 = lean_apply_1(x_1, x_4);
x_7 = lean_unbox_uint64(x_6);
lean_dec(x_6);
x_8 = lean_uint64_mix_hash(x_2, x_7);
x_2 = x_8;
x_3 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_instHashableList___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_foldl___at_instHashableList___spec__1___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT uint64_t l_instHashableList___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; 
x_3 = 7;
x_4 = l_List_foldl___at_instHashableList___spec__1___rarg(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_instHashableList(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instHashableList___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_instHashableList___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; uint64_t x_5; lean_object* x_6; 
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l_List_foldl___at_instHashableList___spec__1___rarg(x_1, x_4, x_3);
x_6 = lean_box_uint64(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_instHashableList___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = l_instHashableList___rarg(x_1, x_2);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
LEAN_EXPORT uint64_t l_instHashableUInt32(uint32_t x_1) {
_start:
{
uint64_t x_2; 
x_2 = ((uint64_t)x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instHashableUInt32___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint64_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_instHashableUInt32(x_2);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
LEAN_EXPORT uint64_t l_instHashableUInt64(uint64_t x_1) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l_instHashableUInt64___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = l_instHashableUInt64(x_2);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
LEAN_EXPORT uint64_t l_instHashableUSize(size_t x_1) {
_start:
{
uint64_t x_2; 
x_2 = (uint64_t)x_1;
return x_2;
}
}
LEAN_EXPORT lean_object* l_instHashableUSize___boxed(lean_object* x_1) {
_start:
{
size_t x_2; uint64_t x_3; lean_object* x_4; 
x_2 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_3 = l_instHashableUSize(x_2);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
LEAN_EXPORT uint64_t l_instHashableFin___rarg(lean_object* x_1) {
_start:
{
uint64_t x_2; 
x_2 = lean_uint64_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instHashableFin(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instHashableFin___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instHashableFin___rarg___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_instHashableFin___rarg(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instHashableFin___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instHashableFin(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_instHashableInt___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT uint64_t l_instHashableInt(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_instHashableInt___closed__1;
x_3 = lean_int_dec_lt(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; 
x_4 = lean_nat_abs(x_1);
x_5 = lean_unsigned_to_nat(2u);
x_6 = lean_nat_mul(x_5, x_4);
lean_dec(x_4);
x_7 = lean_uint64_of_nat(x_6);
lean_dec(x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint64_t x_14; 
x_8 = lean_nat_abs(x_1);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_8, x_9);
lean_dec(x_8);
x_11 = lean_unsigned_to_nat(2u);
x_12 = lean_nat_mul(x_11, x_10);
lean_dec(x_10);
x_13 = lean_nat_add(x_12, x_9);
lean_dec(x_12);
x_14 = lean_uint64_of_nat(x_13);
lean_dec(x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_instHashableInt___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_instHashableInt(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT uint64_t l_instHashable(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; 
x_3 = 0;
return x_3;
}
}
LEAN_EXPORT lean_object* l_instHashable___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = l_instHashable(x_1, x_2);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
lean_object* initialize_Init_Data_UInt(lean_object*);
lean_object* initialize_Init_Data_String(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Hashable(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_UInt(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_instHashableInt___closed__1 = _init_l_instHashableInt___closed__1();
lean_mark_persistent(l_instHashableInt___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

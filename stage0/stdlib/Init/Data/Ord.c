// Lean compiler output
// Module: Init.Data.Ord
// Imports: Init.Data.Int Init.Data.String
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
lean_object* l___private_Init_Data_Ord_0__beqOrdering____x40_Init_Data_Ord___hyg_10__match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_instOrdBool(uint8_t, uint8_t);
lean_object* l_instOrdUSize___boxed(lean_object*, lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* l_instBEqOrdering___closed__1;
lean_object* l_instOrdFin___rarg___boxed(lean_object*, lean_object*);
lean_object* l_instOrdFin___boxed(lean_object*);
lean_object* l_instOrdNat___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOrdering;
uint8_t l_USize_decLt(size_t, size_t);
lean_object* l_instOrdFin(lean_object*);
uint8_t l_USize_cmp(size_t, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_instOrdBool_match__1(lean_object*);
uint8_t l_UInt32_decLt(uint32_t, uint32_t);
uint8_t l___private_Init_Data_Ord_0__beqOrdering____x40_Init_Data_Ord___hyg_10_(uint8_t, uint8_t);
uint8_t l_instInhabitedOrdering;
lean_object* l_instOrdBool_match__1___rarg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Ord_0__beqOrdering____x40_Init_Data_Ord___hyg_10____boxed(lean_object*, lean_object*);
uint8_t l_instOrdInt(lean_object*, lean_object*);
uint8_t l_instOrdFin___rarg(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Ord_0__beqOrdering____x40_Init_Data_Ord___hyg_10__match__1___rarg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_instOrdNat(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Ord_0__beqOrdering____x40_Init_Data_Ord___hyg_10__match__1(lean_object*);
lean_object* l_instOrdString___boxed(lean_object*, lean_object*);
uint8_t l_UInt32_decEq(uint32_t, uint32_t);
lean_object* l_instOrdBool___boxed(lean_object*, lean_object*);
uint8_t l_compareOfLessAndEq___rarg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
uint8_t l_instOrdUSize(size_t, size_t);
lean_object* l_instOrdInt___boxed(lean_object*, lean_object*);
uint8_t l_instOrdString(lean_object*, lean_object*);
lean_object* l_instOrdChar___boxed(lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_instOrdBool_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_instOrdChar(uint32_t, uint32_t);
lean_object* l_USize_cmp___boxed(lean_object*, lean_object*);
lean_object* l_compareOfLessAndEq(lean_object*);
lean_object* l_compareOfLessAndEq___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static uint8_t _init_l_instInhabitedOrdering() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
lean_object* l___private_Init_Data_Ord_0__beqOrdering____x40_Init_Data_Ord___hyg_10__match__1___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_4);
x_7 = lean_box(x_2);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = lean_apply_1(x_3, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_3);
x_10 = lean_box(x_1);
x_11 = lean_box(x_2);
x_12 = lean_apply_2(x_6, x_10, x_11);
return x_12;
}
}
case 1:
{
lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_3);
x_13 = lean_box(x_2);
if (lean_obj_tag(x_13) == 1)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
x_14 = lean_box(0);
x_15 = lean_apply_1(x_4, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_13);
lean_dec(x_4);
x_16 = lean_box(x_1);
x_17 = lean_box(x_2);
x_18 = lean_apply_2(x_6, x_16, x_17);
return x_18;
}
}
default: 
{
lean_object* x_19; 
lean_dec(x_4);
lean_dec(x_3);
x_19 = lean_box(x_2);
if (lean_obj_tag(x_19) == 2)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_6);
x_20 = lean_box(0);
x_21 = lean_apply_1(x_5, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_19);
lean_dec(x_5);
x_22 = lean_box(x_1);
x_23 = lean_box(x_2);
x_24 = lean_apply_2(x_6, x_22, x_23);
return x_24;
}
}
}
}
}
lean_object* l___private_Init_Data_Ord_0__beqOrdering____x40_Init_Data_Ord___hyg_10__match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Data_Ord_0__beqOrdering____x40_Init_Data_Ord___hyg_10__match__1___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l___private_Init_Data_Ord_0__beqOrdering____x40_Init_Data_Ord___hyg_10__match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l___private_Init_Data_Ord_0__beqOrdering____x40_Init_Data_Ord___hyg_10__match__1___rarg(x_7, x_8, x_3, x_4, x_5, x_6);
return x_9;
}
}
uint8_t l___private_Init_Data_Ord_0__beqOrdering____x40_Init_Data_Ord___hyg_10_(uint8_t x_1, uint8_t x_2) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_3; 
x_3 = lean_box(x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8_t x_5; 
lean_dec(x_3);
x_5 = 0;
return x_5;
}
}
case 1:
{
lean_object* x_6; 
x_6 = lean_box(x_2);
if (lean_obj_tag(x_6) == 1)
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_6);
x_8 = 0;
return x_8;
}
}
default: 
{
lean_object* x_9; 
x_9 = lean_box(x_2);
if (lean_obj_tag(x_9) == 2)
{
uint8_t x_10; 
x_10 = 1;
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_9);
x_11 = 0;
return x_11;
}
}
}
}
}
lean_object* l___private_Init_Data_Ord_0__beqOrdering____x40_Init_Data_Ord___hyg_10____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l___private_Init_Data_Ord_0__beqOrdering____x40_Init_Data_Ord___hyg_10_(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_instBEqOrdering___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_Data_Ord_0__beqOrdering____x40_Init_Data_Ord___hyg_10____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instBEqOrdering() {
_start:
{
lean_object* x_1; 
x_1 = l_instBEqOrdering___closed__1;
return x_1;
}
}
uint8_t l_compareOfLessAndEq___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
if (x_4 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_apply_2(x_5, x_1, x_2);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = 2;
return x_8;
}
else
{
uint8_t x_9; 
x_9 = 1;
return x_9;
}
}
else
{
uint8_t x_10; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_10 = 0;
return x_10;
}
}
}
lean_object* l_compareOfLessAndEq(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_compareOfLessAndEq___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_compareOfLessAndEq___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l_compareOfLessAndEq___rarg(x_1, x_2, x_3, x_6, x_5);
lean_dec(x_3);
x_8 = lean_box(x_7);
return x_8;
}
}
uint8_t l_instOrdNat(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_lt(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = lean_nat_dec_eq(x_1, x_2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 2;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
lean_object* l_instOrdNat___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_instOrdNat(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_instOrdInt(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_int_dec_lt(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = lean_int_dec_eq(x_1, x_2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 2;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
lean_object* l_instOrdInt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_instOrdInt(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_instOrdBool_match__1___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (x_1 == 0)
{
lean_dec(x_4);
if (x_2 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_6 = lean_box(x_2);
x_7 = lean_box(x_2);
x_8 = lean_apply_2(x_5, x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
x_9 = lean_box(0);
x_10 = lean_apply_1(x_3, x_9);
return x_10;
}
}
else
{
lean_dec(x_3);
if (x_2 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
x_11 = lean_box(0);
x_12 = lean_apply_1(x_4, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
x_13 = lean_box(x_2);
x_14 = lean_box(x_2);
x_15 = lean_apply_2(x_5, x_13, x_14);
return x_15;
}
}
}
}
lean_object* l_instOrdBool_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instOrdBool_match__1___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_instOrdBool_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = lean_unbox(x_2);
lean_dec(x_2);
x_8 = l_instOrdBool_match__1___rarg(x_6, x_7, x_3, x_4, x_5);
return x_8;
}
}
uint8_t l_instOrdBool(uint8_t x_1, uint8_t x_2) {
_start:
{
if (x_1 == 0)
{
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
if (x_2 == 0)
{
uint8_t x_5; 
x_5 = 2;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
}
}
}
lean_object* l_instOrdBool___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_instOrdBool(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
uint8_t l_instOrdString(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_string_dec_lt(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = lean_string_dec_eq(x_1, x_2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 2;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
lean_object* l_instOrdString___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_instOrdString(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_instOrdFin___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_lt(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = lean_nat_dec_eq(x_1, x_2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 2;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
lean_object* l_instOrdFin(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instOrdFin___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_instOrdFin___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_instOrdFin___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_instOrdFin___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instOrdFin(x_1);
lean_dec(x_1);
return x_2;
}
}
uint8_t l_USize_cmp(size_t x_1, size_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_usize_to_nat(x_1);
x_4 = lean_usize_to_nat(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = 2;
return x_7;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
else
{
uint8_t x_9; 
lean_dec(x_4);
lean_dec(x_3);
x_9 = 0;
return x_9;
}
}
}
lean_object* l_USize_cmp___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_USize_cmp(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
uint8_t l_instOrdUSize(size_t x_1, size_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = x_1 < x_2;
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = x_1 == x_2;
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 2;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
lean_object* l_instOrdUSize___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_instOrdUSize(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
uint8_t l_instOrdChar(uint32_t x_1, uint32_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = x_1 < x_2;
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = x_1 == x_2;
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 2;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
lean_object* l_instOrdChar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l_instOrdChar(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* initialize_Init_Data_Int(lean_object*);
lean_object* initialize_Init_Data_String(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Data_Ord(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Int(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_instInhabitedOrdering = _init_l_instInhabitedOrdering();
l_instBEqOrdering___closed__1 = _init_l_instBEqOrdering___closed__1();
lean_mark_persistent(l_instBEqOrdering___closed__1);
l_instBEqOrdering = _init_l_instBEqOrdering();
lean_mark_persistent(l_instBEqOrdering);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

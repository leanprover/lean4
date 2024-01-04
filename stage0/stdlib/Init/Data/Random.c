// Lean compiler output
// Module: Init.Data.Random
// Imports: Init.System.IO Init.Data.Int
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
LEAN_EXPORT lean_object* l_mkStdGen___boxed(lean_object*);
static lean_object* l_stdRange___closed__1;
static lean_object* l_stdNext___closed__9;
static lean_object* l_stdNext___closed__10;
LEAN_EXPORT lean_object* l_IO_setRandSeed(lean_object*, lean_object*);
static lean_object* l_instRandomGenStdGen___closed__2;
LEAN_EXPORT lean_object* l_randNat(lean_object*);
LEAN_EXPORT lean_object* l_randNat___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_stdNext___closed__6;
LEAN_EXPORT lean_object* l_IO_rand(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_randNat___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_instReprStdGen___closed__4;
LEAN_EXPORT lean_object* l_IO_rand___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_instReprStdGen___closed__8;
static lean_object* l_stdNext___closed__3;
static lean_object* l_instRandomGenStdGen___closed__3;
LEAN_EXPORT lean_object* l_instRandomGenStdGen___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_stdGenRef;
LEAN_EXPORT lean_object* l___private_Init_Data_Random_0__randNatAux(lean_object*);
LEAN_EXPORT lean_object* l_randBool(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_stdNext___closed__8;
lean_object* lean_nat_div(lean_object*, lean_object*);
static lean_object* l_stdNext___closed__1;
static lean_object* l_instReprStdGen___closed__1;
static lean_object* l_instInhabitedStdGen___closed__1;
LEAN_EXPORT lean_object* l_instReprStdGen___boxed(lean_object*, lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
LEAN_EXPORT lean_object* l_instReprStdGen(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_randBool___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_randNat___at_IO_rand___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_stdNext___closed__4;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l_instRandomGenStdGen___closed__4;
LEAN_EXPORT lean_object* l___private_Init_Data_Random_0__randNatAux___at_IO_rand___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_stdNext___closed__2;
LEAN_EXPORT lean_object* l_initFn____x40_Init_Data_Random___hyg_747_(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Random_0__randNatAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instRandomGenStdGen;
static lean_object* l_instReprStdGen___closed__2;
static lean_object* l_instReprStdGen___closed__5;
lean_object* lean_int_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Random_0__randNatAux___at_IO_rand___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_stdNext___closed__7;
lean_object* lean_int_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_stdRange;
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_ByteArray_toUInt64LE_x21(lean_object*);
static lean_object* l_IO_setRandSeed___closed__1;
static lean_object* l_instReprStdGen___closed__6;
static lean_object* l_instReprStdGen___closed__7;
lean_object* l_Int_toNat(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_int_mod(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l_stdNext___closed__5;
LEAN_EXPORT lean_object* l___private_Init_Data_Random_0__randNatAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_stdNext___closed__11;
LEAN_EXPORT lean_object* l_stdNext(lean_object*);
LEAN_EXPORT lean_object* l_IO_setRandSeed___boxed(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
static lean_object* l_instRandomGenStdGen___closed__1;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instInhabitedStdGen;
LEAN_EXPORT lean_object* l_instRandomGenStdGen___lambda__1(lean_object*);
static lean_object* l_instReprStdGen___closed__3;
LEAN_EXPORT lean_object* l_stdSplit(lean_object*);
LEAN_EXPORT lean_object* l_mkStdGen(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_io_get_random_bytes(size_t, lean_object*);
lean_object* l_Nat_repr(lean_object*);
LEAN_EXPORT lean_object* l_randNat___at_IO_rand___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_instInhabitedStdGen___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_instInhabitedStdGen() {
_start:
{
lean_object* x_1; 
x_1 = l_instInhabitedStdGen___closed__1;
return x_1;
}
}
static lean_object* _init_l_stdRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_unsigned_to_nat(2147483562u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_stdRange() {
_start:
{
lean_object* x_1; 
x_1 = l_stdRange___closed__1;
return x_1;
}
}
static lean_object* _init_l_instReprStdGen___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(", ", 2);
return x_1;
}
}
static lean_object* _init_l_instReprStdGen___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instReprStdGen___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_instReprStdGen___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("⟨", 3);
return x_1;
}
}
static lean_object* _init_l_instReprStdGen___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instReprStdGen___closed__3;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l_instReprStdGen___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instReprStdGen___closed__4;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_instReprStdGen___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instReprStdGen___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_instReprStdGen___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("⟩", 3);
return x_1;
}
}
static lean_object* _init_l_instReprStdGen___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instReprStdGen___closed__7;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instReprStdGen(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Nat_repr(x_3);
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = l_instReprStdGen___closed__2;
x_8 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_Nat_repr(x_4);
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_instReprStdGen___closed__6;
x_13 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_instReprStdGen___closed__8;
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_instReprStdGen___closed__5;
x_17 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = 0;
x_19 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l_instReprStdGen___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instReprStdGen(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_stdNext___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(53668u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_stdNext___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(40014u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_stdNext___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(12211u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_stdNext___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_stdNext___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(52774u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_stdNext___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(40692u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_stdNext___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3791u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_stdNext___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_stdNext___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2147483562u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_stdNext___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2147483399u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_stdNext___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2147483563u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_stdNext(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_4 = x_1;
} else {
 lean_dec_ref(x_1);
 x_4 = lean_box(0);
}
x_5 = lean_nat_to_int(x_2);
x_6 = lean_nat_to_int(x_3);
x_7 = l_stdNext___closed__1;
x_8 = lean_int_div(x_5, x_7);
x_9 = lean_int_mul(x_8, x_7);
x_10 = lean_int_sub(x_5, x_9);
lean_dec(x_9);
lean_dec(x_5);
x_11 = l_stdNext___closed__2;
x_12 = lean_int_mul(x_11, x_10);
lean_dec(x_10);
x_13 = l_stdNext___closed__3;
x_14 = lean_int_mul(x_8, x_13);
lean_dec(x_8);
x_15 = lean_int_sub(x_12, x_14);
lean_dec(x_14);
lean_dec(x_12);
x_16 = l_stdNext___closed__4;
x_17 = lean_int_dec_lt(x_15, x_16);
x_18 = l_stdNext___closed__5;
x_19 = lean_int_div(x_6, x_18);
x_20 = lean_int_mul(x_19, x_18);
x_21 = lean_int_sub(x_6, x_20);
lean_dec(x_20);
lean_dec(x_6);
x_22 = l_stdNext___closed__6;
x_23 = lean_int_mul(x_22, x_21);
lean_dec(x_21);
x_24 = l_stdNext___closed__7;
x_25 = lean_int_mul(x_19, x_24);
lean_dec(x_19);
x_26 = lean_int_sub(x_23, x_25);
lean_dec(x_25);
lean_dec(x_23);
x_27 = lean_int_dec_lt(x_26, x_16);
if (x_17 == 0)
{
x_28 = x_15;
goto block_58;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = l_stdNext___closed__11;
x_60 = lean_int_add(x_15, x_59);
lean_dec(x_15);
x_28 = x_60;
goto block_58;
}
block_58:
{
lean_object* x_29; 
x_29 = l_Int_toNat(x_28);
if (x_27 == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_int_sub(x_28, x_26);
lean_dec(x_28);
x_31 = l_stdNext___closed__8;
x_32 = lean_int_dec_lt(x_30, x_31);
x_33 = l_Int_toNat(x_26);
lean_dec(x_26);
if (lean_is_scalar(x_4)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_4;
}
lean_ctor_set(x_34, 0, x_29);
lean_ctor_set(x_34, 1, x_33);
if (x_32 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = l_stdNext___closed__9;
x_36 = lean_int_mod(x_30, x_35);
lean_dec(x_30);
x_37 = l_Int_toNat(x_36);
lean_dec(x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_34);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = l_stdNext___closed__9;
x_40 = lean_int_add(x_30, x_39);
lean_dec(x_30);
x_41 = l_Int_toNat(x_40);
lean_dec(x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_34);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; 
x_43 = l_stdNext___closed__10;
x_44 = lean_int_add(x_26, x_43);
lean_dec(x_26);
x_45 = lean_int_sub(x_28, x_44);
lean_dec(x_28);
x_46 = l_stdNext___closed__8;
x_47 = lean_int_dec_lt(x_45, x_46);
x_48 = l_Int_toNat(x_44);
lean_dec(x_44);
if (lean_is_scalar(x_4)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_4;
}
lean_ctor_set(x_49, 0, x_29);
lean_ctor_set(x_49, 1, x_48);
if (x_47 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = l_stdNext___closed__9;
x_51 = lean_int_mod(x_45, x_50);
lean_dec(x_45);
x_52 = l_Int_toNat(x_51);
lean_dec(x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_49);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = l_stdNext___closed__9;
x_55 = lean_int_add(x_45, x_54);
lean_dec(x_45);
x_56 = l_Int_toNat(x_55);
lean_dec(x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_49);
return x_57;
}
}
}
}
}
LEAN_EXPORT lean_object* l_stdSplit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; uint8_t x_9; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_unsigned_to_nat(2147483562u);
x_5 = lean_nat_dec_eq(x_2, x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_dec_eq(x_3, x_6);
lean_inc(x_1);
x_8 = l_stdNext(x_1);
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 0);
lean_dec(x_11);
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_dec(x_8);
if (x_5 == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_nat_add(x_2, x_6);
lean_dec(x_2);
lean_ctor_set(x_12, 0, x_15);
if (x_7 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_nat_sub(x_3, x_6);
lean_dec(x_3);
lean_ctor_set(x_1, 1, x_16);
lean_ctor_set(x_1, 0, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_1);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
x_18 = lean_unsigned_to_nat(2147483398u);
lean_ctor_set(x_1, 1, x_18);
lean_ctor_set(x_1, 0, x_14);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_1);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
x_22 = lean_nat_add(x_2, x_6);
lean_dec(x_2);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
if (x_7 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_nat_sub(x_3, x_6);
lean_dec(x_3);
lean_ctor_set(x_1, 1, x_24);
lean_ctor_set(x_1, 0, x_20);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_1);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_3);
x_26 = lean_unsigned_to_nat(2147483398u);
lean_ctor_set(x_1, 1, x_26);
lean_ctor_set(x_1, 0, x_20);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_1);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_12);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_12, 0);
lean_ctor_set(x_12, 0, x_6);
if (x_7 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_nat_sub(x_3, x_6);
lean_dec(x_3);
lean_ctor_set(x_1, 1, x_30);
lean_ctor_set(x_1, 0, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_12);
lean_ctor_set(x_31, 1, x_1);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_3);
x_32 = lean_unsigned_to_nat(2147483398u);
lean_ctor_set(x_1, 1, x_32);
lean_ctor_set(x_1, 0, x_29);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_12);
lean_ctor_set(x_33, 1, x_1);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_12, 0);
x_35 = lean_ctor_get(x_12, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_12);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_6);
lean_ctor_set(x_36, 1, x_35);
if (x_7 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_nat_sub(x_3, x_6);
lean_dec(x_3);
lean_ctor_set(x_1, 1, x_37);
lean_ctor_set(x_1, 0, x_34);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_1);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_3);
x_39 = lean_unsigned_to_nat(2147483398u);
lean_ctor_set(x_1, 1, x_39);
lean_ctor_set(x_1, 0, x_34);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_36);
lean_ctor_set(x_40, 1, x_1);
return x_40;
}
}
}
}
else
{
lean_object* x_41; 
lean_dec(x_1);
x_41 = lean_ctor_get(x_8, 1);
lean_inc(x_41);
lean_dec(x_8);
if (x_5 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_44 = x_41;
} else {
 lean_dec_ref(x_41);
 x_44 = lean_box(0);
}
x_45 = lean_nat_add(x_2, x_6);
lean_dec(x_2);
if (lean_is_scalar(x_44)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_44;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_43);
if (x_7 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_nat_sub(x_3, x_6);
lean_dec(x_3);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_42);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_3);
x_50 = lean_unsigned_to_nat(2147483398u);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_42);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_46);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_2);
x_53 = lean_ctor_get(x_41, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_41, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_55 = x_41;
} else {
 lean_dec_ref(x_41);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_6);
lean_ctor_set(x_56, 1, x_54);
if (x_7 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_nat_sub(x_3, x_6);
lean_dec(x_3);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_53);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_3);
x_60 = lean_unsigned_to_nat(2147483398u);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_53);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_56);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instRandomGenStdGen___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_stdRange;
return x_2;
}
}
static lean_object* _init_l_instRandomGenStdGen___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instRandomGenStdGen___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_instRandomGenStdGen___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_stdNext), 1, 0);
return x_1;
}
}
static lean_object* _init_l_instRandomGenStdGen___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_stdSplit), 1, 0);
return x_1;
}
}
static lean_object* _init_l_instRandomGenStdGen___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_instRandomGenStdGen___closed__1;
x_2 = l_instRandomGenStdGen___closed__2;
x_3 = l_instRandomGenStdGen___closed__3;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_instRandomGenStdGen() {
_start:
{
lean_object* x_1; 
x_1 = l_instRandomGenStdGen___closed__4;
return x_1;
}
}
LEAN_EXPORT lean_object* l_instRandomGenStdGen___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instRandomGenStdGen___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_mkStdGen(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = lean_unsigned_to_nat(2147483562u);
x_3 = lean_nat_div(x_1, x_2);
x_4 = lean_nat_mod(x_1, x_2);
x_5 = lean_unsigned_to_nat(2147483398u);
x_6 = lean_nat_mod(x_3, x_5);
lean_dec(x_3);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_4, x_7);
lean_dec(x_4);
x_9 = lean_nat_add(x_6, x_7);
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_mkStdGen___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_mkStdGen(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Random_0__randNatAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_4, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_apply_1(x_10, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_nat_mul(x_8, x_3);
lean_dec(x_8);
x_15 = lean_nat_sub(x_13, x_2);
lean_dec(x_13);
x_16 = lean_nat_add(x_14, x_15);
lean_dec(x_15);
lean_dec(x_14);
x_17 = lean_nat_div(x_4, x_3);
lean_dec(x_4);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_17, x_18);
lean_dec(x_17);
lean_ctor_set(x_11, 0, x_16);
x_4 = x_19;
x_5 = x_11;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_11, 0);
x_22 = lean_ctor_get(x_11, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_11);
x_23 = lean_nat_mul(x_8, x_3);
lean_dec(x_8);
x_24 = lean_nat_sub(x_21, x_2);
lean_dec(x_21);
x_25 = lean_nat_add(x_23, x_24);
lean_dec(x_24);
lean_dec(x_23);
x_26 = lean_nat_div(x_4, x_3);
lean_dec(x_4);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_sub(x_26, x_27);
lean_dec(x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_22);
x_4 = x_28;
x_5 = x_29;
goto _start;
}
}
else
{
uint8_t x_31; 
lean_dec(x_4);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_5);
if (x_31 == 0)
{
return x_5;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_5, 0);
x_33 = lean_ctor_get(x_5, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_5);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Random_0__randNatAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Data_Random_0__randNatAux___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Random_0__randNatAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Random_0__randNatAux___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_randNat___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_nat_dec_lt(x_4, x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_inc(x_2);
x_7 = lean_apply_1(x_6, x_2);
if (x_5 == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_nat_sub(x_10, x_9);
lean_dec(x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_11, x_12);
lean_dec(x_11);
x_14 = lean_nat_sub(x_4, x_3);
x_15 = lean_nat_add(x_14, x_12);
lean_dec(x_14);
x_16 = lean_unsigned_to_nat(1000u);
x_17 = lean_nat_mul(x_15, x_16);
x_18 = lean_unsigned_to_nat(0u);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 0, x_18);
x_19 = l___private_Init_Data_Random_0__randNatAux___rarg(x_1, x_9, x_13, x_17, x_7);
lean_dec(x_13);
lean_dec(x_9);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_nat_mod(x_21, x_15);
lean_dec(x_15);
lean_dec(x_21);
x_23 = lean_nat_add(x_3, x_22);
lean_dec(x_22);
lean_ctor_set(x_19, 0, x_23);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_19, 0);
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_19);
x_26 = lean_nat_mod(x_24, x_15);
lean_dec(x_15);
lean_dec(x_24);
x_27 = lean_nat_add(x_3, x_26);
lean_dec(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_29 = lean_ctor_get(x_7, 0);
x_30 = lean_ctor_get(x_7, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_7);
x_31 = lean_nat_sub(x_30, x_29);
lean_dec(x_30);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_31, x_32);
lean_dec(x_31);
x_34 = lean_nat_sub(x_4, x_3);
x_35 = lean_nat_add(x_34, x_32);
lean_dec(x_34);
x_36 = lean_unsigned_to_nat(1000u);
x_37 = lean_nat_mul(x_35, x_36);
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_2);
x_40 = l___private_Init_Data_Random_0__randNatAux___rarg(x_1, x_29, x_33, x_37, x_39);
lean_dec(x_33);
lean_dec(x_29);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_43 = x_40;
} else {
 lean_dec_ref(x_40);
 x_43 = lean_box(0);
}
x_44 = lean_nat_mod(x_41, x_35);
lean_dec(x_35);
lean_dec(x_41);
x_45 = lean_nat_add(x_3, x_44);
lean_dec(x_44);
if (lean_is_scalar(x_43)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_43;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_42);
return x_46;
}
}
else
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_7);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_48 = lean_ctor_get(x_7, 0);
x_49 = lean_ctor_get(x_7, 1);
x_50 = lean_nat_sub(x_49, x_48);
lean_dec(x_49);
x_51 = lean_unsigned_to_nat(1u);
x_52 = lean_nat_add(x_50, x_51);
lean_dec(x_50);
x_53 = lean_nat_sub(x_3, x_4);
x_54 = lean_nat_add(x_53, x_51);
lean_dec(x_53);
x_55 = lean_unsigned_to_nat(1000u);
x_56 = lean_nat_mul(x_54, x_55);
x_57 = lean_unsigned_to_nat(0u);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 0, x_57);
x_58 = l___private_Init_Data_Random_0__randNatAux___rarg(x_1, x_48, x_52, x_56, x_7);
lean_dec(x_52);
lean_dec(x_48);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_58, 0);
x_61 = lean_nat_mod(x_60, x_54);
lean_dec(x_54);
lean_dec(x_60);
x_62 = lean_nat_add(x_4, x_61);
lean_dec(x_61);
lean_ctor_set(x_58, 0, x_62);
return x_58;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_63 = lean_ctor_get(x_58, 0);
x_64 = lean_ctor_get(x_58, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_58);
x_65 = lean_nat_mod(x_63, x_54);
lean_dec(x_54);
lean_dec(x_63);
x_66 = lean_nat_add(x_4, x_65);
lean_dec(x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_64);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_68 = lean_ctor_get(x_7, 0);
x_69 = lean_ctor_get(x_7, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_7);
x_70 = lean_nat_sub(x_69, x_68);
lean_dec(x_69);
x_71 = lean_unsigned_to_nat(1u);
x_72 = lean_nat_add(x_70, x_71);
lean_dec(x_70);
x_73 = lean_nat_sub(x_3, x_4);
x_74 = lean_nat_add(x_73, x_71);
lean_dec(x_73);
x_75 = lean_unsigned_to_nat(1000u);
x_76 = lean_nat_mul(x_74, x_75);
x_77 = lean_unsigned_to_nat(0u);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_2);
x_79 = l___private_Init_Data_Random_0__randNatAux___rarg(x_1, x_68, x_72, x_76, x_78);
lean_dec(x_72);
lean_dec(x_68);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_82 = x_79;
} else {
 lean_dec_ref(x_79);
 x_82 = lean_box(0);
}
x_83 = lean_nat_mod(x_80, x_74);
lean_dec(x_74);
lean_dec(x_80);
x_84 = lean_nat_add(x_4, x_83);
lean_dec(x_83);
if (lean_is_scalar(x_82)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_82;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_81);
return x_85;
}
}
}
}
LEAN_EXPORT lean_object* l_randNat(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_randNat___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_randNat___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_randNat___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_randBool___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_randNat___rarg(x_1, x_2, x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_nat_dec_eq(x_7, x_4);
lean_dec(x_7);
x_9 = lean_box(x_8);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_5);
x_12 = lean_nat_dec_eq(x_10, x_4);
lean_dec(x_10);
x_13 = lean_box(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_randBool(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_randBool___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_initFn____x40_Init_Data_Random___hyg_747_(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = 8;
x_3 = lean_io_get_random_bytes(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_ByteArray_toUInt64LE_x21(x_4);
x_7 = lean_unbox_uint64(x_6);
lean_dec(x_6);
x_8 = lean_uint64_to_nat(x_7);
x_9 = l_mkStdGen(x_8);
lean_dec(x_8);
x_10 = lean_st_mk_ref(x_9, x_5);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_3);
if (x_15 == 0)
{
return x_3;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_3, 0);
x_17 = lean_ctor_get(x_3, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_3);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
static lean_object* _init_l_IO_setRandSeed___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_IO_stdGenRef;
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_setRandSeed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = l_mkStdGen(x_1);
x_4 = l_IO_setRandSeed___closed__1;
x_5 = lean_st_ref_set(x_4, x_3, x_2);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_IO_setRandSeed___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_setRandSeed(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Random_0__randNatAux___at_IO_rand___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec(x_4);
x_9 = l_stdNext(x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_nat_mul(x_7, x_2);
lean_dec(x_7);
x_13 = lean_nat_sub(x_11, x_1);
lean_dec(x_11);
x_14 = lean_nat_add(x_12, x_13);
lean_dec(x_13);
lean_dec(x_12);
x_15 = lean_nat_div(x_3, x_2);
lean_dec(x_3);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_15, x_16);
lean_dec(x_15);
lean_ctor_set(x_9, 0, x_14);
x_3 = x_17;
x_4 = x_9;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_9, 0);
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_9);
x_21 = lean_nat_mul(x_7, x_2);
lean_dec(x_7);
x_22 = lean_nat_sub(x_19, x_1);
lean_dec(x_19);
x_23 = lean_nat_add(x_21, x_22);
lean_dec(x_22);
lean_dec(x_21);
x_24 = lean_nat_div(x_3, x_2);
lean_dec(x_3);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_sub(x_24, x_25);
lean_dec(x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_20);
x_3 = x_26;
x_4 = x_27;
goto _start;
}
}
else
{
uint8_t x_29; 
lean_dec(x_3);
x_29 = !lean_is_exclusive(x_4);
if (x_29 == 0)
{
return x_4;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_4, 0);
x_31 = lean_ctor_get(x_4, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_4);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_randNat___at_IO_rand___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_3, x_2);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_stdRange;
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_nat_sub(x_8, x_7);
lean_dec(x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_9, x_10);
lean_dec(x_9);
x_12 = lean_nat_sub(x_3, x_2);
x_13 = lean_nat_add(x_12, x_10);
lean_dec(x_12);
x_14 = lean_unsigned_to_nat(1000u);
x_15 = lean_nat_mul(x_13, x_14);
x_16 = lean_unsigned_to_nat(0u);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 0, x_16);
x_17 = l___private_Init_Data_Random_0__randNatAux___at_IO_rand___spec__2(x_7, x_11, x_15, x_5);
lean_dec(x_11);
lean_dec(x_7);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_nat_mod(x_19, x_13);
lean_dec(x_13);
lean_dec(x_19);
x_21 = lean_nat_add(x_2, x_20);
lean_dec(x_20);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_17, 0);
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_17);
x_24 = lean_nat_mod(x_22, x_13);
lean_dec(x_13);
lean_dec(x_22);
x_25 = lean_nat_add(x_2, x_24);
lean_dec(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_27 = lean_ctor_get(x_5, 0);
x_28 = lean_ctor_get(x_5, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_5);
x_29 = lean_nat_sub(x_28, x_27);
lean_dec(x_28);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_29, x_30);
lean_dec(x_29);
x_32 = lean_nat_sub(x_3, x_2);
x_33 = lean_nat_add(x_32, x_30);
lean_dec(x_32);
x_34 = lean_unsigned_to_nat(1000u);
x_35 = lean_nat_mul(x_33, x_34);
x_36 = lean_unsigned_to_nat(0u);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_1);
x_38 = l___private_Init_Data_Random_0__randNatAux___at_IO_rand___spec__2(x_27, x_31, x_35, x_37);
lean_dec(x_31);
lean_dec(x_27);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_41 = x_38;
} else {
 lean_dec_ref(x_38);
 x_41 = lean_box(0);
}
x_42 = lean_nat_mod(x_39, x_33);
lean_dec(x_33);
lean_dec(x_39);
x_43 = lean_nat_add(x_2, x_42);
lean_dec(x_42);
if (lean_is_scalar(x_41)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_41;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_40);
return x_44;
}
}
else
{
lean_object* x_45; uint8_t x_46; 
x_45 = l_stdRange;
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = lean_ctor_get(x_45, 1);
x_49 = lean_nat_sub(x_48, x_47);
lean_dec(x_48);
x_50 = lean_unsigned_to_nat(1u);
x_51 = lean_nat_add(x_49, x_50);
lean_dec(x_49);
x_52 = lean_nat_sub(x_2, x_3);
x_53 = lean_nat_add(x_52, x_50);
lean_dec(x_52);
x_54 = lean_unsigned_to_nat(1000u);
x_55 = lean_nat_mul(x_53, x_54);
x_56 = lean_unsigned_to_nat(0u);
lean_ctor_set(x_45, 1, x_1);
lean_ctor_set(x_45, 0, x_56);
x_57 = l___private_Init_Data_Random_0__randNatAux___at_IO_rand___spec__2(x_47, x_51, x_55, x_45);
lean_dec(x_51);
lean_dec(x_47);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_57, 0);
x_60 = lean_nat_mod(x_59, x_53);
lean_dec(x_53);
lean_dec(x_59);
x_61 = lean_nat_add(x_3, x_60);
lean_dec(x_60);
lean_ctor_set(x_57, 0, x_61);
return x_57;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_ctor_get(x_57, 0);
x_63 = lean_ctor_get(x_57, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_57);
x_64 = lean_nat_mod(x_62, x_53);
lean_dec(x_53);
lean_dec(x_62);
x_65 = lean_nat_add(x_3, x_64);
lean_dec(x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_63);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_67 = lean_ctor_get(x_45, 0);
x_68 = lean_ctor_get(x_45, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_45);
x_69 = lean_nat_sub(x_68, x_67);
lean_dec(x_68);
x_70 = lean_unsigned_to_nat(1u);
x_71 = lean_nat_add(x_69, x_70);
lean_dec(x_69);
x_72 = lean_nat_sub(x_2, x_3);
x_73 = lean_nat_add(x_72, x_70);
lean_dec(x_72);
x_74 = lean_unsigned_to_nat(1000u);
x_75 = lean_nat_mul(x_73, x_74);
x_76 = lean_unsigned_to_nat(0u);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_1);
x_78 = l___private_Init_Data_Random_0__randNatAux___at_IO_rand___spec__2(x_67, x_71, x_75, x_77);
lean_dec(x_71);
lean_dec(x_67);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_81 = x_78;
} else {
 lean_dec_ref(x_78);
 x_81 = lean_box(0);
}
x_82 = lean_nat_mod(x_79, x_73);
lean_dec(x_73);
lean_dec(x_79);
x_83 = lean_nat_add(x_3, x_82);
lean_dec(x_82);
if (lean_is_scalar(x_81)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_81;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_80);
return x_84;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_rand(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_4 = l_IO_setRandSeed___closed__1;
x_5 = lean_st_ref_get(x_4, x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_randNat___at_IO_rand___spec__1(x_6, x_1, x_2);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_st_ref_set(x_4, x_10, x_7);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_9);
return x_11;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Random_0__randNatAux___at_IO_rand___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_Random_0__randNatAux___at_IO_rand___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_randNat___at_IO_rand___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_randNat___at_IO_rand___spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_rand___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_rand(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* initialize_Init_System_IO(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Int(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Random(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_instInhabitedStdGen___closed__1 = _init_l_instInhabitedStdGen___closed__1();
lean_mark_persistent(l_instInhabitedStdGen___closed__1);
l_instInhabitedStdGen = _init_l_instInhabitedStdGen();
lean_mark_persistent(l_instInhabitedStdGen);
l_stdRange___closed__1 = _init_l_stdRange___closed__1();
lean_mark_persistent(l_stdRange___closed__1);
l_stdRange = _init_l_stdRange();
lean_mark_persistent(l_stdRange);
l_instReprStdGen___closed__1 = _init_l_instReprStdGen___closed__1();
lean_mark_persistent(l_instReprStdGen___closed__1);
l_instReprStdGen___closed__2 = _init_l_instReprStdGen___closed__2();
lean_mark_persistent(l_instReprStdGen___closed__2);
l_instReprStdGen___closed__3 = _init_l_instReprStdGen___closed__3();
lean_mark_persistent(l_instReprStdGen___closed__3);
l_instReprStdGen___closed__4 = _init_l_instReprStdGen___closed__4();
lean_mark_persistent(l_instReprStdGen___closed__4);
l_instReprStdGen___closed__5 = _init_l_instReprStdGen___closed__5();
lean_mark_persistent(l_instReprStdGen___closed__5);
l_instReprStdGen___closed__6 = _init_l_instReprStdGen___closed__6();
lean_mark_persistent(l_instReprStdGen___closed__6);
l_instReprStdGen___closed__7 = _init_l_instReprStdGen___closed__7();
lean_mark_persistent(l_instReprStdGen___closed__7);
l_instReprStdGen___closed__8 = _init_l_instReprStdGen___closed__8();
lean_mark_persistent(l_instReprStdGen___closed__8);
l_stdNext___closed__1 = _init_l_stdNext___closed__1();
lean_mark_persistent(l_stdNext___closed__1);
l_stdNext___closed__2 = _init_l_stdNext___closed__2();
lean_mark_persistent(l_stdNext___closed__2);
l_stdNext___closed__3 = _init_l_stdNext___closed__3();
lean_mark_persistent(l_stdNext___closed__3);
l_stdNext___closed__4 = _init_l_stdNext___closed__4();
lean_mark_persistent(l_stdNext___closed__4);
l_stdNext___closed__5 = _init_l_stdNext___closed__5();
lean_mark_persistent(l_stdNext___closed__5);
l_stdNext___closed__6 = _init_l_stdNext___closed__6();
lean_mark_persistent(l_stdNext___closed__6);
l_stdNext___closed__7 = _init_l_stdNext___closed__7();
lean_mark_persistent(l_stdNext___closed__7);
l_stdNext___closed__8 = _init_l_stdNext___closed__8();
lean_mark_persistent(l_stdNext___closed__8);
l_stdNext___closed__9 = _init_l_stdNext___closed__9();
lean_mark_persistent(l_stdNext___closed__9);
l_stdNext___closed__10 = _init_l_stdNext___closed__10();
lean_mark_persistent(l_stdNext___closed__10);
l_stdNext___closed__11 = _init_l_stdNext___closed__11();
lean_mark_persistent(l_stdNext___closed__11);
l_instRandomGenStdGen___closed__1 = _init_l_instRandomGenStdGen___closed__1();
lean_mark_persistent(l_instRandomGenStdGen___closed__1);
l_instRandomGenStdGen___closed__2 = _init_l_instRandomGenStdGen___closed__2();
lean_mark_persistent(l_instRandomGenStdGen___closed__2);
l_instRandomGenStdGen___closed__3 = _init_l_instRandomGenStdGen___closed__3();
lean_mark_persistent(l_instRandomGenStdGen___closed__3);
l_instRandomGenStdGen___closed__4 = _init_l_instRandomGenStdGen___closed__4();
lean_mark_persistent(l_instRandomGenStdGen___closed__4);
l_instRandomGenStdGen = _init_l_instRandomGenStdGen();
lean_mark_persistent(l_instRandomGenStdGen);
res = l_initFn____x40_Init_Data_Random___hyg_747_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_IO_stdGenRef = lean_io_result_get_value(res);
lean_mark_persistent(l_IO_stdGenRef);
lean_dec_ref(res);
l_IO_setRandSeed___closed__1 = _init_l_IO_setRandSeed___closed__1();
lean_mark_persistent(l_IO_setRandSeed___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

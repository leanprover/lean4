// Lean compiler output
// Module: Init.Data.Random
// Imports: public import Init.System.IO import Init.Data.ByteArray.Extra
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
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_mkStdGen(lean_object*);
LEAN_EXPORT lean_object* l_mkStdGen___boxed(lean_object*);
static lean_once_cell_t l_instInhabitedStdGen___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instInhabitedStdGen___closed__0;
LEAN_EXPORT lean_object* l_instInhabitedStdGen;
static const lean_ctor_object l_stdRange___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(2147483562) << 1) | 1))}};
static const lean_object* l_stdRange___closed__0 = (const lean_object*)&l_stdRange___closed__0_value;
LEAN_EXPORT const lean_object* l_stdRange = (const lean_object*)&l_stdRange___closed__0_value;
static const lean_string_object l_instReprStdGen___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟨"};
static const lean_object* l_instReprStdGen___lam__0___closed__0 = (const lean_object*)&l_instReprStdGen___lam__0___closed__0_value;
static const lean_string_object l_instReprStdGen___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_instReprStdGen___lam__0___closed__1 = (const lean_object*)&l_instReprStdGen___lam__0___closed__1_value;
static const lean_ctor_object l_instReprStdGen___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_instReprStdGen___lam__0___closed__1_value)}};
static const lean_object* l_instReprStdGen___lam__0___closed__2 = (const lean_object*)&l_instReprStdGen___lam__0___closed__2_value;
static const lean_string_object l_instReprStdGen___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟩"};
static const lean_object* l_instReprStdGen___lam__0___closed__3 = (const lean_object*)&l_instReprStdGen___lam__0___closed__3_value;
lean_object* lean_string_length(lean_object*);
static lean_once_cell_t l_instReprStdGen___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instReprStdGen___lam__0___closed__4;
lean_object* lean_nat_to_int(lean_object*);
static lean_once_cell_t l_instReprStdGen___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instReprStdGen___lam__0___closed__5;
static const lean_ctor_object l_instReprStdGen___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_instReprStdGen___lam__0___closed__0_value)}};
static const lean_object* l_instReprStdGen___lam__0___closed__6 = (const lean_object*)&l_instReprStdGen___lam__0___closed__6_value;
static const lean_ctor_object l_instReprStdGen___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_instReprStdGen___lam__0___closed__3_value)}};
static const lean_object* l_instReprStdGen___lam__0___closed__7 = (const lean_object*)&l_instReprStdGen___lam__0___closed__7_value;
lean_object* l_Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_instReprStdGen___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprStdGen___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instReprStdGen___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instReprStdGen___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instReprStdGen___closed__0 = (const lean_object*)&l_instReprStdGen___closed__0_value;
LEAN_EXPORT const lean_object* l_instReprStdGen = (const lean_object*)&l_instReprStdGen___closed__0_value;
static lean_once_cell_t l_stdNext___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_stdNext___closed__0;
static lean_once_cell_t l_stdNext___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_stdNext___closed__1;
static lean_once_cell_t l_stdNext___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_stdNext___closed__2;
static lean_once_cell_t l_stdNext___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_stdNext___closed__3;
static lean_once_cell_t l_stdNext___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_stdNext___closed__4;
static lean_once_cell_t l_stdNext___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_stdNext___closed__5;
static lean_once_cell_t l_stdNext___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_stdNext___closed__6;
static lean_once_cell_t l_stdNext___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_stdNext___closed__7;
static lean_once_cell_t l_stdNext___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_stdNext___closed__8;
static lean_once_cell_t l_stdNext___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_stdNext___closed__9;
static lean_once_cell_t l_stdNext___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_stdNext___closed__10;
lean_object* lean_int_sub(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_stdNext(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_stdSplit(lean_object*);
LEAN_EXPORT lean_object* l_instRandomGenStdGen___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_instRandomGenStdGen___lam__0___boxed(lean_object*);
static const lean_closure_object l_instRandomGenStdGen___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instRandomGenStdGen___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instRandomGenStdGen___closed__0 = (const lean_object*)&l_instRandomGenStdGen___closed__0_value;
static const lean_closure_object l_instRandomGenStdGen___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_stdNext, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instRandomGenStdGen___closed__1 = (const lean_object*)&l_instRandomGenStdGen___closed__1_value;
static const lean_closure_object l_instRandomGenStdGen___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_stdSplit, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instRandomGenStdGen___closed__2 = (const lean_object*)&l_instRandomGenStdGen___closed__2_value;
static const lean_ctor_object l_instRandomGenStdGen___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_instRandomGenStdGen___closed__0_value),((lean_object*)&l_instRandomGenStdGen___closed__1_value),((lean_object*)&l_instRandomGenStdGen___closed__2_value)}};
static const lean_object* l_instRandomGenStdGen___closed__3 = (const lean_object*)&l_instRandomGenStdGen___closed__3_value;
LEAN_EXPORT const lean_object* l_instRandomGenStdGen = (const lean_object*)&l_instRandomGenStdGen___closed__3_value;
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Random_0__randNatAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Random_0__randNatAux___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Random_0__randNatAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Random_0__randNatAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_randNat___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_randNat___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_randNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_randNat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_randBool___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_randBool(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_get_random_bytes(size_t);
uint64_t l_ByteArray_toUInt64LE_x21(lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
lean_object* lean_st_mk_ref(lean_object*);
LEAN_EXPORT lean_object* l_initFn_00___x40_Init_Data_Random_2456098205____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_initFn_00___x40_Init_Data_Random_2456098205____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_stdGenRef;
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_setRandSeed(lean_object*);
LEAN_EXPORT lean_object* l_IO_setRandSeed___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Random_0__randNatAux___at___00randNat___at___00IO_rand_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Random_0__randNatAux___at___00randNat___at___00IO_rand_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_randNat___at___00IO_rand_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_randNat___at___00IO_rand_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l_IO_rand(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_rand___boxed(lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l_instInhabitedStdGen___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_mkStdGen(x_1);
return x_2;
}
}
static lean_object* _init_l_instInhabitedStdGen(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_instInhabitedStdGen___closed__0, &l_instInhabitedStdGen___closed__0_once, _init_l_instInhabitedStdGen___closed__0);
return x_1;
}
}
static lean_object* _init_l_instReprStdGen___lam__0___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_instReprStdGen___lam__0___closed__0));
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l_instReprStdGen___lam__0___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_instReprStdGen___lam__0___closed__4, &l_instReprStdGen___lam__0___closed__4_once, _init_l_instReprStdGen___lam__0___closed__4);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instReprStdGen___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_25; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_25 = !lean_is_exclusive(x_1);
if (x_25 == 0)
{
x_5 = x_1;
x_6 = x_25;
goto block_24;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Nat_reprFast(x_3);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = ((lean_object*)(l_instReprStdGen___lam__0___closed__2));
if (x_6 == 0)
{
lean_ctor_set_tag(x_5, 5);
lean_ctor_set(x_5, 1, x_9);
lean_ctor_set(x_5, 0, x_8);
x_10 = x_5;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_23, 0, x_8);
lean_ctor_set(x_23, 1, x_9);
x_10 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_11 = l_Nat_reprFast(x_4);
x_12 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_obj_once(&l_instReprStdGen___lam__0___closed__5, &l_instReprStdGen___lam__0___closed__5_once, _init_l_instReprStdGen___lam__0___closed__5);
x_15 = ((lean_object*)(l_instReprStdGen___lam__0___closed__6));
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
x_17 = ((lean_object*)(l_instReprStdGen___lam__0___closed__7));
x_18 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_18);
x_20 = 0;
x_21 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_instReprStdGen___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instReprStdGen___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_stdNext___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_stdNext___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2147483562u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_stdNext___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(40014u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_stdNext___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(53668u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_stdNext___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(12211u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_stdNext___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_stdNext___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(40692u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_stdNext___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(52774u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_stdNext___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3791u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_stdNext___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2147483399u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_stdNext___closed__10(void) {
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
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_8; lean_object* x_9; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_56; 
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_dec_ref(x_1);
x_24 = lean_unsigned_to_nat(53668u);
x_25 = lean_nat_div(x_22, x_24);
x_26 = lean_nat_to_int(x_25);
x_27 = lean_obj_once(&l_stdNext___closed__2, &l_stdNext___closed__2_once, _init_l_stdNext___closed__2);
x_28 = lean_nat_to_int(x_22);
x_29 = lean_obj_once(&l_stdNext___closed__3, &l_stdNext___closed__3_once, _init_l_stdNext___closed__3);
x_30 = lean_int_mul(x_26, x_29);
x_31 = lean_int_sub(x_28, x_30);
lean_dec(x_30);
lean_dec(x_28);
x_32 = lean_int_mul(x_27, x_31);
lean_dec(x_31);
x_33 = lean_obj_once(&l_stdNext___closed__4, &l_stdNext___closed__4_once, _init_l_stdNext___closed__4);
x_34 = lean_int_mul(x_26, x_33);
lean_dec(x_26);
x_35 = lean_int_sub(x_32, x_34);
lean_dec(x_34);
lean_dec(x_32);
x_36 = lean_obj_once(&l_stdNext___closed__5, &l_stdNext___closed__5_once, _init_l_stdNext___closed__5);
x_56 = lean_int_dec_lt(x_35, x_36);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = l_Int_toNat(x_35);
lean_dec(x_35);
x_37 = x_57;
goto block_55;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_obj_once(&l_stdNext___closed__10, &l_stdNext___closed__10_once, _init_l_stdNext___closed__10);
x_59 = lean_int_add(x_35, x_58);
lean_dec(x_35);
x_60 = l_Int_toNat(x_59);
lean_dec(x_59);
x_37 = x_60;
goto block_55;
}
block_7:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
block_21:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_inc(x_8);
x_10 = lean_nat_to_int(x_8);
lean_inc(x_9);
x_11 = lean_nat_to_int(x_9);
x_12 = lean_int_sub(x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
x_13 = lean_obj_once(&l_stdNext___closed__0, &l_stdNext___closed__0_once, _init_l_stdNext___closed__0);
x_14 = lean_int_dec_lt(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = l_Int_toNat(x_12);
lean_dec(x_12);
x_16 = lean_unsigned_to_nat(2147483562u);
x_17 = lean_nat_mod(x_15, x_16);
lean_dec(x_15);
x_2 = x_9;
x_3 = x_8;
x_4 = x_17;
goto block_7;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_obj_once(&l_stdNext___closed__1, &l_stdNext___closed__1_once, _init_l_stdNext___closed__1);
x_19 = lean_int_add(x_12, x_18);
lean_dec(x_12);
x_20 = l_Int_toNat(x_19);
lean_dec(x_19);
x_2 = x_9;
x_3 = x_8;
x_4 = x_20;
goto block_7;
}
}
block_55:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_38 = lean_unsigned_to_nat(52774u);
x_39 = lean_nat_div(x_23, x_38);
x_40 = lean_nat_to_int(x_39);
x_41 = lean_obj_once(&l_stdNext___closed__6, &l_stdNext___closed__6_once, _init_l_stdNext___closed__6);
x_42 = lean_nat_to_int(x_23);
x_43 = lean_obj_once(&l_stdNext___closed__7, &l_stdNext___closed__7_once, _init_l_stdNext___closed__7);
x_44 = lean_int_mul(x_40, x_43);
x_45 = lean_int_sub(x_42, x_44);
lean_dec(x_44);
lean_dec(x_42);
x_46 = lean_int_mul(x_41, x_45);
lean_dec(x_45);
x_47 = lean_obj_once(&l_stdNext___closed__8, &l_stdNext___closed__8_once, _init_l_stdNext___closed__8);
x_48 = lean_int_mul(x_40, x_47);
lean_dec(x_40);
x_49 = lean_int_sub(x_46, x_48);
lean_dec(x_48);
lean_dec(x_46);
x_50 = lean_int_dec_lt(x_49, x_36);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = l_Int_toNat(x_49);
lean_dec(x_49);
x_8 = x_37;
x_9 = x_51;
goto block_21;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_obj_once(&l_stdNext___closed__9, &l_stdNext___closed__9_once, _init_l_stdNext___closed__9);
x_53 = lean_int_add(x_49, x_52);
lean_dec(x_49);
x_54 = l_Int_toNat(x_53);
lean_dec(x_53);
x_8 = x_37;
x_9 = x_54;
goto block_21;
}
}
}
}
LEAN_EXPORT lean_object* l_stdSplit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_33; uint8_t x_34; 
x_25 = lean_ctor_get(x_1, 0);
x_26 = lean_ctor_get(x_1, 1);
x_33 = lean_unsigned_to_nat(2147483562u);
x_34 = lean_nat_dec_eq(x_25, x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_add(x_25, x_35);
x_27 = x_36;
goto block_32;
}
else
{
lean_object* x_37; 
x_37 = lean_unsigned_to_nat(1u);
x_27 = x_37;
goto block_32;
}
block_24:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_22; 
x_4 = l_stdNext(x_1);
x_5 = lean_ctor_get(x_4, 1);
x_22 = !lean_is_exclusive(x_4);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_4, 0);
lean_dec(x_23);
x_6 = x_4;
x_7 = x_22;
goto block_21;
}
else
{
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_box(0);
x_7 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_20; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_5, 1);
x_20 = !lean_is_exclusive(x_5);
if (x_20 == 0)
{
x_10 = x_5;
x_11 = x_20;
goto block_19;
}
else
{
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_5);
x_10 = lean_box(0);
x_11 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_12; 
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_2);
x_12 = x_10;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_9);
x_12 = x_18;
goto block_17;
}
block_17:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_3);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_13);
lean_ctor_set(x_6, 0, x_12);
x_14 = x_6;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_13);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
}
}
block_32:
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_dec_eq(x_26, x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_nat_sub(x_26, x_28);
x_2 = x_27;
x_3 = x_30;
goto block_24;
}
else
{
lean_object* x_31; 
x_31 = lean_unsigned_to_nat(2147483398u);
x_2 = x_27;
x_3 = x_31;
goto block_24;
}
}
}
}
LEAN_EXPORT lean_object* l_instRandomGenStdGen___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_stdRange));
return x_2;
}
}
LEAN_EXPORT lean_object* l_instRandomGenStdGen___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instRandomGenStdGen___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Random_0__randNatAux___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_4, x_6);
if (x_7 == 1)
{
lean_dec(x_4);
lean_dec_ref(x_1);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_27; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec_ref(x_5);
x_10 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_10);
x_11 = lean_apply_1(x_10, x_9);
x_12 = lean_ctor_get(x_11, 0);
x_13 = lean_ctor_get(x_11, 1);
x_27 = !lean_is_exclusive(x_11);
if (x_27 == 0)
{
x_14 = x_11;
x_15 = x_27;
goto block_26;
}
else
{
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_nat_mul(x_8, x_3);
lean_dec(x_8);
x_17 = lean_nat_sub(x_12, x_2);
lean_dec(x_12);
x_18 = lean_nat_add(x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
x_19 = lean_nat_div(x_4, x_3);
lean_dec(x_4);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_sub(x_19, x_20);
lean_dec(x_19);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_18);
x_22 = x_14;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_13);
x_22 = x_25;
goto block_24;
}
block_24:
{
x_4 = x_21;
x_5 = x_22;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Random_0__randNatAux___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Random_0__randNatAux___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Random_0__randNatAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Random_0__randNatAux___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Random_0__randNatAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Random_0__randNatAux(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_randNat___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_39; lean_object* x_40; 
x_39 = lean_nat_dec_lt(x_4, x_3);
if (x_39 == 0)
{
x_40 = x_3;
goto block_41;
}
else
{
x_40 = x_4;
goto block_41;
}
block_38:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_37; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_7);
lean_inc(x_2);
x_8 = lean_apply_1(x_7, x_2);
x_9 = lean_ctor_get(x_8, 0);
x_10 = lean_ctor_get(x_8, 1);
x_37 = !lean_is_exclusive(x_8);
if (x_37 == 0)
{
x_11 = x_8;
x_12 = x_37;
goto block_36;
}
else
{
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_8);
x_11 = lean_box(0);
x_12 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_nat_sub(x_10, x_9);
lean_dec(x_10);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_13, x_14);
lean_dec(x_13);
x_16 = lean_unsigned_to_nat(1000u);
x_17 = lean_nat_sub(x_6, x_5);
x_18 = lean_nat_add(x_17, x_14);
lean_dec(x_17);
x_19 = lean_nat_mul(x_18, x_16);
x_20 = lean_unsigned_to_nat(0u);
if (x_12 == 0)
{
lean_ctor_set(x_11, 1, x_2);
lean_ctor_set(x_11, 0, x_20);
x_21 = x_11;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_20);
lean_ctor_set(x_35, 1, x_2);
x_21 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_33; 
x_22 = l___private_Init_Data_Random_0__randNatAux___redArg(x_1, x_9, x_15, x_19, x_21);
lean_dec(x_15);
lean_dec(x_9);
x_23 = lean_ctor_get(x_22, 0);
x_24 = lean_ctor_get(x_22, 1);
x_33 = !lean_is_exclusive(x_22);
if (x_33 == 0)
{
x_25 = x_22;
x_26 = x_33;
goto block_32;
}
else
{
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_22);
x_25 = lean_box(0);
x_26 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_nat_mod(x_23, x_18);
lean_dec(x_18);
lean_dec(x_23);
x_28 = lean_nat_add(x_5, x_27);
lean_dec(x_27);
if (x_26 == 0)
{
lean_ctor_set(x_25, 0, x_28);
x_29 = x_25;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_24);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
}
}
block_41:
{
if (x_39 == 0)
{
x_5 = x_40;
x_6 = x_4;
goto block_38;
}
else
{
x_5 = x_40;
x_6 = x_3;
goto block_38;
}
}
}
}
LEAN_EXPORT lean_object* l_randNat___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_randNat___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_randNat(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_randNat___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_randNat___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_randNat(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_randBool___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_16; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_randNat___redArg(x_1, x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_ctor_get(x_5, 1);
x_16 = !lean_is_exclusive(x_5);
if (x_16 == 0)
{
x_8 = x_5;
x_9 = x_16;
goto block_15;
}
else
{
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_5);
x_8 = lean_box(0);
x_9 = x_16;
goto block_15;
}
block_15:
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_nat_dec_eq(x_6, x_4);
lean_dec(x_6);
x_11 = lean_box(x_10);
if (x_9 == 0)
{
lean_ctor_set(x_8, 0, x_11);
x_12 = x_8;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_7);
x_12 = x_14;
goto block_13;
}
block_13:
{
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_randBool(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_randBool___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_initFn_00___x40_Init_Data_Random_2456098205____hygCtx___hyg_2_() {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = 8;
x_3 = lean_io_get_random_bytes(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_15; 
x_4 = lean_ctor_get(x_3, 0);
x_15 = !lean_is_exclusive(x_3);
if (x_15 == 0)
{
x_5 = x_3;
x_6 = x_15;
goto block_14;
}
else
{
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = x_15;
goto block_14;
}
block_14:
{
uint64_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_ByteArray_toUInt64LE_x21(x_4);
lean_dec(x_4);
x_8 = lean_uint64_to_nat(x_7);
x_9 = l_mkStdGen(x_8);
lean_dec(x_8);
x_10 = lean_st_mk_ref(x_9);
if (x_6 == 0)
{
lean_ctor_set(x_5, 0, x_10);
x_11 = x_5;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_10);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_23; 
x_16 = lean_ctor_get(x_3, 0);
x_23 = !lean_is_exclusive(x_3);
if (x_23 == 0)
{
x_17 = x_3;
x_18 = x_23;
goto block_22;
}
else
{
lean_inc(x_16);
lean_dec(x_3);
x_17 = lean_box(0);
x_18 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_19; 
if (x_18 == 0)
{
x_19 = x_17;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_16);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
}
}
}
LEAN_EXPORT lean_object* l_initFn_00___x40_Init_Data_Random_2456098205____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_initFn_00___x40_Init_Data_Random_2456098205____hygCtx___hyg_2_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_setRandSeed(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_IO_stdGenRef;
x_4 = l_mkStdGen(x_1);
x_5 = lean_st_ref_set(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_setRandSeed___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_setRandSeed(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Random_0__randNatAux___at___00randNat___at___00IO_rand_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_3, x_5);
if (x_6 == 1)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_25; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec_ref(x_4);
x_9 = l_stdNext(x_8);
x_10 = lean_ctor_get(x_9, 0);
x_11 = lean_ctor_get(x_9, 1);
x_25 = !lean_is_exclusive(x_9);
if (x_25 == 0)
{
x_12 = x_9;
x_13 = x_25;
goto block_24;
}
else
{
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_nat_mul(x_7, x_2);
lean_dec(x_7);
x_15 = lean_nat_sub(x_10, x_1);
lean_dec(x_10);
x_16 = lean_nat_add(x_14, x_15);
lean_dec(x_15);
lean_dec(x_14);
x_17 = lean_nat_div(x_3, x_2);
lean_dec(x_3);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_17, x_18);
lean_dec(x_17);
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_16);
x_20 = x_12;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_11);
x_20 = x_23;
goto block_22;
}
block_22:
{
x_3 = x_19;
x_4 = x_20;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Random_0__randNatAux___at___00randNat___at___00IO_rand_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_Random_0__randNatAux___at___00randNat___at___00IO_rand_spec__0_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_randNat___at___00IO_rand_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_37; lean_object* x_38; 
x_37 = lean_nat_dec_lt(x_3, x_2);
if (x_37 == 0)
{
x_38 = x_2;
goto block_39;
}
else
{
x_38 = x_3;
goto block_39;
}
block_36:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_35; 
x_6 = ((lean_object*)(l_stdRange));
x_7 = lean_ctor_get(x_6, 0);
x_8 = lean_ctor_get(x_6, 1);
x_35 = !lean_is_exclusive(x_6);
if (x_35 == 0)
{
x_9 = x_6;
x_10 = x_35;
goto block_34;
}
else
{
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_6);
x_9 = lean_box(0);
x_10 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = lean_nat_sub(x_8, x_7);
lean_dec(x_8);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_11, x_12);
lean_dec(x_11);
x_14 = lean_unsigned_to_nat(1000u);
x_15 = lean_nat_sub(x_5, x_4);
x_16 = lean_nat_add(x_15, x_12);
lean_dec(x_15);
x_17 = lean_nat_mul(x_16, x_14);
x_18 = lean_unsigned_to_nat(0u);
if (x_10 == 0)
{
lean_ctor_set(x_9, 1, x_1);
lean_ctor_set(x_9, 0, x_18);
x_19 = x_9;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_18);
lean_ctor_set(x_33, 1, x_1);
x_19 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_31; 
x_20 = l___private_Init_Data_Random_0__randNatAux___at___00randNat___at___00IO_rand_spec__0_spec__0(x_7, x_13, x_17, x_19);
lean_dec(x_13);
lean_dec(x_7);
x_21 = lean_ctor_get(x_20, 0);
x_22 = lean_ctor_get(x_20, 1);
x_31 = !lean_is_exclusive(x_20);
if (x_31 == 0)
{
x_23 = x_20;
x_24 = x_31;
goto block_30;
}
else
{
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_20);
x_23 = lean_box(0);
x_24 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_nat_mod(x_21, x_16);
lean_dec(x_16);
lean_dec(x_21);
x_26 = lean_nat_add(x_4, x_25);
lean_dec(x_25);
if (x_24 == 0)
{
lean_ctor_set(x_23, 0, x_26);
x_27 = x_23;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_22);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
}
}
block_39:
{
if (x_37 == 0)
{
x_4 = x_38;
x_5 = x_3;
goto block_36;
}
else
{
x_4 = x_38;
x_5 = x_2;
goto block_36;
}
}
}
}
LEAN_EXPORT lean_object* l_randNat___at___00IO_rand_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_randNat___at___00IO_rand_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_rand(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = l_IO_stdGenRef;
x_5 = lean_st_ref_get(x_4);
x_6 = l_randNat___at___00IO_rand_spec__0(x_5, x_1, x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_st_ref_set(x_4, x_8);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_rand___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_rand(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* runtime_initialize_Init_System_IO(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ByteArray_Extra(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Random(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_System_IO(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ByteArray_Extra(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_instInhabitedStdGen = _init_l_instInhabitedStdGen();
lean_mark_persistent(l_instInhabitedStdGen);
res = l_initFn_00___x40_Init_Data_Random_2456098205____hygCtx___hyg_2_()
;
if (lean_io_result_is_error(res)) return res;
l_IO_stdGenRef = lean_io_result_get_value(res);
lean_mark_persistent(l_IO_stdGenRef);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Random(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_System_IO(uint8_t builtin);
lean_object* initialize_Init_Data_ByteArray_Extra(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Random(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ByteArray_Extra(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Random(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Random(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Random(builtin);
}
#ifdef __cplusplus
}
#endif

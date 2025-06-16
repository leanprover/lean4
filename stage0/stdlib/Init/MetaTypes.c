// Lean compiler output
// Module: Init.MetaTypes
// Imports: Init.Core
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
LEAN_EXPORT lean_object* l_Lean_Meta_beqTransparencyMode____x40_Init_MetaTypes___hyg_73____boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_neutralConfig___closed__1;
LEAN_EXPORT lean_object* l_Lean_instInhabitedNameGenerator;
LEAN_EXPORT uint8_t l_Lean_Meta_instInhabitedEtaStructMode;
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_noConfusion___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_noConfusion___rarg(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT uint8_t l_List_hasDecEq___at_Lean_Meta_beqOccurrences____x40_Init_MetaTypes___hyg_1257____spec__1(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_beqOccurrences____x40_Init_MetaTypes___hyg_1257_(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instBEqTransparencyMode___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_instCoeListNatOccurrences(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_beqTransparencyMode____x40_Init_MetaTypes___hyg_73_(uint8_t, uint8_t);
static lean_object* l_Lean_Meta_TransparencyMode_noConfusion___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_beqConfig____x40_Init_MetaTypes___hyg_767____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DSimp_instBEqConfig;
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_noConfusion(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_neutralConfig;
static lean_object* l_Lean_Meta_Simp_instInhabitedConfig___closed__1;
LEAN_EXPORT lean_object* l_List_hasDecEq___at_Lean_Meta_beqOccurrences____x40_Init_MetaTypes___hyg_1257____spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_DSimp_beqConfig____x40_Init_MetaTypes___hyg_268_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_noConfusion___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instBEqOccurrences___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_DSimp_beqConfig____x40_Init_MetaTypes___hyg_268____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_noConfusion___rarg___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_noConfusion(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_beqConfig____x40_Init_MetaTypes___hyg_767_(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DSimp_instBEqConfig___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedConfig;
LEAN_EXPORT uint8_t l_Lean_Meta_instInhabitedTransparencyMode;
static lean_object* l_Lean_Meta_instBEqEtaStructMode___closed__1;
static lean_object* l_Lean_instInhabitedNameGenerator___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqOccurrences;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqEtaStructMode;
static lean_object* l_Lean_Meta_Simp_instBEqConfig___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedOccurrences;
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqTransparencyMode;
LEAN_EXPORT lean_object* l_Lean_Meta_DSimp_instInhabitedConfig;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_defaultMaxSteps;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instBEqConfig;
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_beqOccurrences____x40_Init_MetaTypes___hyg_1257____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_beqEtaStructMode____x40_Init_MetaTypes___hyg_106_(uint8_t, uint8_t);
static lean_object* l_Lean_Meta_DSimp_instInhabitedConfig___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_noConfusion___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_beqEtaStructMode____x40_Init_MetaTypes___hyg_106____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_noConfusion___rarg(uint8_t, uint8_t, lean_object*);
static lean_object* _init_l_Lean_instInhabitedNameGenerator___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instInhabitedNameGenerator() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedNameGenerator___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_toCtorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
default: 
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(3u);
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Meta_TransparencyMode_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_noConfusion___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_TransparencyMode_noConfusion___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_TransparencyMode_noConfusion___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_noConfusion___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_TransparencyMode_noConfusion___rarg___closed__1;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_noConfusion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_TransparencyMode_noConfusion___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_noConfusion___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_TransparencyMode_noConfusion___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_noConfusion___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Meta_TransparencyMode_noConfusion___rarg(x_4, x_5, x_3);
return x_6;
}
}
static uint8_t _init_l_Lean_Meta_instInhabitedTransparencyMode() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_beqTransparencyMode____x40_Init_MetaTypes___hyg_73_(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Meta_TransparencyMode_toCtorIdx(x_1);
x_4 = l_Lean_Meta_TransparencyMode_toCtorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_beqTransparencyMode____x40_Init_MetaTypes___hyg_73____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_Meta_beqTransparencyMode____x40_Init_MetaTypes___hyg_73_(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_instBEqTransparencyMode___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_beqTransparencyMode____x40_Init_MetaTypes___hyg_73____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instBEqTransparencyMode() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_instBEqTransparencyMode___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_toCtorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Meta_EtaStructMode_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_noConfusion___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_TransparencyMode_noConfusion___rarg___closed__1;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_noConfusion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_EtaStructMode_noConfusion___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_noConfusion___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Meta_EtaStructMode_noConfusion___rarg(x_4, x_5, x_3);
return x_6;
}
}
static uint8_t _init_l_Lean_Meta_instInhabitedEtaStructMode() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_beqEtaStructMode____x40_Init_MetaTypes___hyg_106_(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Meta_EtaStructMode_toCtorIdx(x_1);
x_4 = l_Lean_Meta_EtaStructMode_toCtorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_beqEtaStructMode____x40_Init_MetaTypes___hyg_106____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_Meta_beqEtaStructMode____x40_Init_MetaTypes___hyg_106_(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_instBEqEtaStructMode___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_beqEtaStructMode____x40_Init_MetaTypes___hyg_106____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instBEqEtaStructMode() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_instBEqEtaStructMode___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DSimp_instInhabitedConfig___closed__1() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; 
x_1 = 0;
x_2 = 0;
x_3 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, 1, x_1);
lean_ctor_set_uint8(x_3, 2, x_1);
lean_ctor_set_uint8(x_3, 3, x_2);
lean_ctor_set_uint8(x_3, 4, x_1);
lean_ctor_set_uint8(x_3, 5, x_1);
lean_ctor_set_uint8(x_3, 6, x_1);
lean_ctor_set_uint8(x_3, 7, x_1);
lean_ctor_set_uint8(x_3, 8, x_1);
lean_ctor_set_uint8(x_3, 9, x_1);
lean_ctor_set_uint8(x_3, 10, x_1);
lean_ctor_set_uint8(x_3, 11, x_1);
lean_ctor_set_uint8(x_3, 12, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_DSimp_instInhabitedConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_DSimp_instInhabitedConfig___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_DSimp_beqConfig____x40_Init_MetaTypes___hyg_268_(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_34; uint8_t x_41; uint8_t x_48; uint8_t x_55; uint8_t x_62; uint8_t x_69; uint8_t x_76; uint8_t x_83; uint8_t x_92; uint8_t x_99; 
x_3 = lean_ctor_get_uint8(x_1, 0);
x_4 = lean_ctor_get_uint8(x_1, 1);
x_5 = lean_ctor_get_uint8(x_1, 2);
x_6 = lean_ctor_get_uint8(x_1, 3);
x_7 = lean_ctor_get_uint8(x_1, 4);
x_8 = lean_ctor_get_uint8(x_1, 5);
x_9 = lean_ctor_get_uint8(x_1, 6);
x_10 = lean_ctor_get_uint8(x_1, 7);
x_11 = lean_ctor_get_uint8(x_1, 8);
x_12 = lean_ctor_get_uint8(x_1, 9);
x_13 = lean_ctor_get_uint8(x_1, 10);
x_14 = lean_ctor_get_uint8(x_1, 11);
x_15 = lean_ctor_get_uint8(x_1, 12);
x_16 = lean_ctor_get_uint8(x_2, 0);
x_17 = lean_ctor_get_uint8(x_2, 1);
x_18 = lean_ctor_get_uint8(x_2, 2);
x_19 = lean_ctor_get_uint8(x_2, 3);
x_20 = lean_ctor_get_uint8(x_2, 4);
x_21 = lean_ctor_get_uint8(x_2, 5);
x_22 = lean_ctor_get_uint8(x_2, 6);
x_23 = lean_ctor_get_uint8(x_2, 7);
x_24 = lean_ctor_get_uint8(x_2, 8);
x_25 = lean_ctor_get_uint8(x_2, 9);
x_26 = lean_ctor_get_uint8(x_2, 10);
x_27 = lean_ctor_get_uint8(x_2, 11);
x_28 = lean_ctor_get_uint8(x_2, 12);
if (x_3 == 0)
{
if (x_16 == 0)
{
uint8_t x_106; 
x_106 = 1;
x_99 = x_106;
goto block_105;
}
else
{
uint8_t x_107; 
x_107 = 0;
x_99 = x_107;
goto block_105;
}
}
else
{
if (x_16 == 0)
{
uint8_t x_108; 
x_108 = 0;
x_99 = x_108;
goto block_105;
}
else
{
uint8_t x_109; 
x_109 = 1;
x_99 = x_109;
goto block_105;
}
}
block_33:
{
if (x_29 == 0)
{
uint8_t x_30; 
x_30 = 0;
return x_30;
}
else
{
if (x_15 == 0)
{
if (x_28 == 0)
{
uint8_t x_31; 
x_31 = 1;
return x_31;
}
else
{
uint8_t x_32; 
x_32 = 0;
return x_32;
}
}
else
{
return x_28;
}
}
}
block_40:
{
if (x_34 == 0)
{
uint8_t x_35; 
x_35 = 0;
return x_35;
}
else
{
if (x_14 == 0)
{
if (x_27 == 0)
{
uint8_t x_36; 
x_36 = 1;
x_29 = x_36;
goto block_33;
}
else
{
uint8_t x_37; 
x_37 = 0;
x_29 = x_37;
goto block_33;
}
}
else
{
if (x_27 == 0)
{
uint8_t x_38; 
x_38 = 0;
x_29 = x_38;
goto block_33;
}
else
{
uint8_t x_39; 
x_39 = 1;
x_29 = x_39;
goto block_33;
}
}
}
}
block_47:
{
if (x_41 == 0)
{
uint8_t x_42; 
x_42 = 0;
return x_42;
}
else
{
if (x_13 == 0)
{
if (x_26 == 0)
{
uint8_t x_43; 
x_43 = 1;
x_34 = x_43;
goto block_40;
}
else
{
uint8_t x_44; 
x_44 = 0;
x_34 = x_44;
goto block_40;
}
}
else
{
if (x_26 == 0)
{
uint8_t x_45; 
x_45 = 0;
x_34 = x_45;
goto block_40;
}
else
{
uint8_t x_46; 
x_46 = 1;
x_34 = x_46;
goto block_40;
}
}
}
}
block_54:
{
if (x_48 == 0)
{
uint8_t x_49; 
x_49 = 0;
return x_49;
}
else
{
if (x_12 == 0)
{
if (x_25 == 0)
{
uint8_t x_50; 
x_50 = 1;
x_41 = x_50;
goto block_47;
}
else
{
uint8_t x_51; 
x_51 = 0;
x_41 = x_51;
goto block_47;
}
}
else
{
if (x_25 == 0)
{
uint8_t x_52; 
x_52 = 0;
x_41 = x_52;
goto block_47;
}
else
{
uint8_t x_53; 
x_53 = 1;
x_41 = x_53;
goto block_47;
}
}
}
}
block_61:
{
if (x_55 == 0)
{
uint8_t x_56; 
x_56 = 0;
return x_56;
}
else
{
if (x_11 == 0)
{
if (x_24 == 0)
{
uint8_t x_57; 
x_57 = 1;
x_48 = x_57;
goto block_54;
}
else
{
uint8_t x_58; 
x_58 = 0;
x_48 = x_58;
goto block_54;
}
}
else
{
if (x_24 == 0)
{
uint8_t x_59; 
x_59 = 0;
x_48 = x_59;
goto block_54;
}
else
{
uint8_t x_60; 
x_60 = 1;
x_48 = x_60;
goto block_54;
}
}
}
}
block_68:
{
if (x_62 == 0)
{
uint8_t x_63; 
x_63 = 0;
return x_63;
}
else
{
if (x_10 == 0)
{
if (x_23 == 0)
{
uint8_t x_64; 
x_64 = 1;
x_55 = x_64;
goto block_61;
}
else
{
uint8_t x_65; 
x_65 = 0;
x_55 = x_65;
goto block_61;
}
}
else
{
if (x_23 == 0)
{
uint8_t x_66; 
x_66 = 0;
x_55 = x_66;
goto block_61;
}
else
{
uint8_t x_67; 
x_67 = 1;
x_55 = x_67;
goto block_61;
}
}
}
}
block_75:
{
if (x_69 == 0)
{
uint8_t x_70; 
x_70 = 0;
return x_70;
}
else
{
if (x_9 == 0)
{
if (x_22 == 0)
{
uint8_t x_71; 
x_71 = 1;
x_62 = x_71;
goto block_68;
}
else
{
uint8_t x_72; 
x_72 = 0;
x_62 = x_72;
goto block_68;
}
}
else
{
if (x_22 == 0)
{
uint8_t x_73; 
x_73 = 0;
x_62 = x_73;
goto block_68;
}
else
{
uint8_t x_74; 
x_74 = 1;
x_62 = x_74;
goto block_68;
}
}
}
}
block_82:
{
if (x_76 == 0)
{
uint8_t x_77; 
x_77 = 0;
return x_77;
}
else
{
if (x_8 == 0)
{
if (x_21 == 0)
{
uint8_t x_78; 
x_78 = 1;
x_69 = x_78;
goto block_75;
}
else
{
uint8_t x_79; 
x_79 = 0;
x_69 = x_79;
goto block_75;
}
}
else
{
if (x_21 == 0)
{
uint8_t x_80; 
x_80 = 0;
x_69 = x_80;
goto block_75;
}
else
{
uint8_t x_81; 
x_81 = 1;
x_69 = x_81;
goto block_75;
}
}
}
}
block_91:
{
if (x_83 == 0)
{
uint8_t x_84; 
x_84 = 0;
return x_84;
}
else
{
uint8_t x_85; 
x_85 = l_Lean_Meta_beqEtaStructMode____x40_Init_MetaTypes___hyg_106_(x_6, x_19);
if (x_85 == 0)
{
uint8_t x_86; 
x_86 = 0;
return x_86;
}
else
{
if (x_7 == 0)
{
if (x_20 == 0)
{
uint8_t x_87; 
x_87 = 1;
x_76 = x_87;
goto block_82;
}
else
{
uint8_t x_88; 
x_88 = 0;
x_76 = x_88;
goto block_82;
}
}
else
{
if (x_20 == 0)
{
uint8_t x_89; 
x_89 = 0;
x_76 = x_89;
goto block_82;
}
else
{
uint8_t x_90; 
x_90 = 1;
x_76 = x_90;
goto block_82;
}
}
}
}
}
block_98:
{
if (x_92 == 0)
{
uint8_t x_93; 
x_93 = 0;
return x_93;
}
else
{
if (x_5 == 0)
{
if (x_18 == 0)
{
uint8_t x_94; 
x_94 = 1;
x_83 = x_94;
goto block_91;
}
else
{
uint8_t x_95; 
x_95 = 0;
x_83 = x_95;
goto block_91;
}
}
else
{
if (x_18 == 0)
{
uint8_t x_96; 
x_96 = 0;
x_83 = x_96;
goto block_91;
}
else
{
uint8_t x_97; 
x_97 = 1;
x_83 = x_97;
goto block_91;
}
}
}
}
block_105:
{
if (x_99 == 0)
{
uint8_t x_100; 
x_100 = 0;
return x_100;
}
else
{
if (x_4 == 0)
{
if (x_17 == 0)
{
uint8_t x_101; 
x_101 = 1;
x_92 = x_101;
goto block_98;
}
else
{
uint8_t x_102; 
x_102 = 0;
x_92 = x_102;
goto block_98;
}
}
else
{
if (x_17 == 0)
{
uint8_t x_103; 
x_103 = 0;
x_92 = x_103;
goto block_98;
}
else
{
uint8_t x_104; 
x_104 = 1;
x_92 = x_104;
goto block_98;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DSimp_beqConfig____x40_Init_MetaTypes___hyg_268____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_DSimp_beqConfig____x40_Init_MetaTypes___hyg_268_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_DSimp_instBEqConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_DSimp_beqConfig____x40_Init_MetaTypes___hyg_268____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DSimp_instBEqConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_DSimp_instBEqConfig___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_defaultMaxSteps() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(100000u);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedConfig___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = 0;
x_3 = 0;
x_4 = lean_alloc_ctor(0, 2, 21);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 1, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 2, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 3, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 4, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 5, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 6, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 7, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 8, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 9, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 10, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 11, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 12, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 13, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 14, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 15, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 16, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 17, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 18, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 19, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 20, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Simp_instInhabitedConfig___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_beqConfig____x40_Init_MetaTypes___hyg_767_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_54; uint8_t x_61; uint8_t x_68; uint8_t x_75; uint8_t x_82; uint8_t x_89; uint8_t x_96; uint8_t x_103; uint8_t x_110; uint8_t x_117; uint8_t x_124; uint8_t x_131; uint8_t x_138; uint8_t x_147; uint8_t x_154; uint8_t x_161; uint8_t x_168; uint8_t x_175; uint8_t x_182; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 1);
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 2);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 3);
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 4);
x_10 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 5);
x_11 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 6);
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 7);
x_13 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 8);
x_14 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 9);
x_15 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 10);
x_16 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 11);
x_17 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 12);
x_18 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 13);
x_19 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 14);
x_20 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 15);
x_21 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 16);
x_22 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 17);
x_23 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 18);
x_24 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 19);
x_25 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 20);
x_26 = lean_ctor_get(x_2, 0);
x_27 = lean_ctor_get(x_2, 1);
x_28 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_29 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 1);
x_30 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 2);
x_31 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 3);
x_32 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 4);
x_33 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 5);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 6);
x_35 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 7);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 8);
x_37 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 9);
x_38 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 10);
x_39 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 11);
x_40 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 12);
x_41 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 13);
x_42 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 14);
x_43 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 15);
x_44 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 16);
x_45 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 17);
x_46 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 18);
x_47 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 19);
x_48 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 20);
x_182 = lean_nat_dec_eq(x_3, x_26);
if (x_182 == 0)
{
uint8_t x_183; 
x_183 = 0;
return x_183;
}
else
{
uint8_t x_184; 
x_184 = lean_nat_dec_eq(x_4, x_27);
if (x_184 == 0)
{
uint8_t x_185; 
x_185 = 0;
return x_185;
}
else
{
if (x_5 == 0)
{
if (x_28 == 0)
{
uint8_t x_186; 
x_186 = 1;
x_175 = x_186;
goto block_181;
}
else
{
uint8_t x_187; 
x_187 = 0;
x_175 = x_187;
goto block_181;
}
}
else
{
if (x_28 == 0)
{
uint8_t x_188; 
x_188 = 0;
x_175 = x_188;
goto block_181;
}
else
{
uint8_t x_189; 
x_189 = 1;
x_175 = x_189;
goto block_181;
}
}
}
}
block_53:
{
if (x_49 == 0)
{
uint8_t x_50; 
x_50 = 0;
return x_50;
}
else
{
if (x_25 == 0)
{
if (x_48 == 0)
{
uint8_t x_51; 
x_51 = 1;
return x_51;
}
else
{
uint8_t x_52; 
x_52 = 0;
return x_52;
}
}
else
{
return x_48;
}
}
}
block_60:
{
if (x_54 == 0)
{
uint8_t x_55; 
x_55 = 0;
return x_55;
}
else
{
if (x_24 == 0)
{
if (x_47 == 0)
{
uint8_t x_56; 
x_56 = 1;
x_49 = x_56;
goto block_53;
}
else
{
uint8_t x_57; 
x_57 = 0;
x_49 = x_57;
goto block_53;
}
}
else
{
if (x_47 == 0)
{
uint8_t x_58; 
x_58 = 0;
x_49 = x_58;
goto block_53;
}
else
{
uint8_t x_59; 
x_59 = 1;
x_49 = x_59;
goto block_53;
}
}
}
}
block_67:
{
if (x_61 == 0)
{
uint8_t x_62; 
x_62 = 0;
return x_62;
}
else
{
if (x_23 == 0)
{
if (x_46 == 0)
{
uint8_t x_63; 
x_63 = 1;
x_54 = x_63;
goto block_60;
}
else
{
uint8_t x_64; 
x_64 = 0;
x_54 = x_64;
goto block_60;
}
}
else
{
if (x_46 == 0)
{
uint8_t x_65; 
x_65 = 0;
x_54 = x_65;
goto block_60;
}
else
{
uint8_t x_66; 
x_66 = 1;
x_54 = x_66;
goto block_60;
}
}
}
}
block_74:
{
if (x_68 == 0)
{
uint8_t x_69; 
x_69 = 0;
return x_69;
}
else
{
if (x_22 == 0)
{
if (x_45 == 0)
{
uint8_t x_70; 
x_70 = 1;
x_61 = x_70;
goto block_67;
}
else
{
uint8_t x_71; 
x_71 = 0;
x_61 = x_71;
goto block_67;
}
}
else
{
if (x_45 == 0)
{
uint8_t x_72; 
x_72 = 0;
x_61 = x_72;
goto block_67;
}
else
{
uint8_t x_73; 
x_73 = 1;
x_61 = x_73;
goto block_67;
}
}
}
}
block_81:
{
if (x_75 == 0)
{
uint8_t x_76; 
x_76 = 0;
return x_76;
}
else
{
if (x_21 == 0)
{
if (x_44 == 0)
{
uint8_t x_77; 
x_77 = 1;
x_68 = x_77;
goto block_74;
}
else
{
uint8_t x_78; 
x_78 = 0;
x_68 = x_78;
goto block_74;
}
}
else
{
if (x_44 == 0)
{
uint8_t x_79; 
x_79 = 0;
x_68 = x_79;
goto block_74;
}
else
{
uint8_t x_80; 
x_80 = 1;
x_68 = x_80;
goto block_74;
}
}
}
}
block_88:
{
if (x_82 == 0)
{
uint8_t x_83; 
x_83 = 0;
return x_83;
}
else
{
if (x_20 == 0)
{
if (x_43 == 0)
{
uint8_t x_84; 
x_84 = 1;
x_75 = x_84;
goto block_81;
}
else
{
uint8_t x_85; 
x_85 = 0;
x_75 = x_85;
goto block_81;
}
}
else
{
if (x_43 == 0)
{
uint8_t x_86; 
x_86 = 0;
x_75 = x_86;
goto block_81;
}
else
{
uint8_t x_87; 
x_87 = 1;
x_75 = x_87;
goto block_81;
}
}
}
}
block_95:
{
if (x_89 == 0)
{
uint8_t x_90; 
x_90 = 0;
return x_90;
}
else
{
if (x_19 == 0)
{
if (x_42 == 0)
{
uint8_t x_91; 
x_91 = 1;
x_82 = x_91;
goto block_88;
}
else
{
uint8_t x_92; 
x_92 = 0;
x_82 = x_92;
goto block_88;
}
}
else
{
if (x_42 == 0)
{
uint8_t x_93; 
x_93 = 0;
x_82 = x_93;
goto block_88;
}
else
{
uint8_t x_94; 
x_94 = 1;
x_82 = x_94;
goto block_88;
}
}
}
}
block_102:
{
if (x_96 == 0)
{
uint8_t x_97; 
x_97 = 0;
return x_97;
}
else
{
if (x_18 == 0)
{
if (x_41 == 0)
{
uint8_t x_98; 
x_98 = 1;
x_89 = x_98;
goto block_95;
}
else
{
uint8_t x_99; 
x_99 = 0;
x_89 = x_99;
goto block_95;
}
}
else
{
if (x_41 == 0)
{
uint8_t x_100; 
x_100 = 0;
x_89 = x_100;
goto block_95;
}
else
{
uint8_t x_101; 
x_101 = 1;
x_89 = x_101;
goto block_95;
}
}
}
}
block_109:
{
if (x_103 == 0)
{
uint8_t x_104; 
x_104 = 0;
return x_104;
}
else
{
if (x_17 == 0)
{
if (x_40 == 0)
{
uint8_t x_105; 
x_105 = 1;
x_96 = x_105;
goto block_102;
}
else
{
uint8_t x_106; 
x_106 = 0;
x_96 = x_106;
goto block_102;
}
}
else
{
if (x_40 == 0)
{
uint8_t x_107; 
x_107 = 0;
x_96 = x_107;
goto block_102;
}
else
{
uint8_t x_108; 
x_108 = 1;
x_96 = x_108;
goto block_102;
}
}
}
}
block_116:
{
if (x_110 == 0)
{
uint8_t x_111; 
x_111 = 0;
return x_111;
}
else
{
if (x_16 == 0)
{
if (x_39 == 0)
{
uint8_t x_112; 
x_112 = 1;
x_103 = x_112;
goto block_109;
}
else
{
uint8_t x_113; 
x_113 = 0;
x_103 = x_113;
goto block_109;
}
}
else
{
if (x_39 == 0)
{
uint8_t x_114; 
x_114 = 0;
x_103 = x_114;
goto block_109;
}
else
{
uint8_t x_115; 
x_115 = 1;
x_103 = x_115;
goto block_109;
}
}
}
}
block_123:
{
if (x_117 == 0)
{
uint8_t x_118; 
x_118 = 0;
return x_118;
}
else
{
if (x_15 == 0)
{
if (x_38 == 0)
{
uint8_t x_119; 
x_119 = 1;
x_110 = x_119;
goto block_116;
}
else
{
uint8_t x_120; 
x_120 = 0;
x_110 = x_120;
goto block_116;
}
}
else
{
if (x_38 == 0)
{
uint8_t x_121; 
x_121 = 0;
x_110 = x_121;
goto block_116;
}
else
{
uint8_t x_122; 
x_122 = 1;
x_110 = x_122;
goto block_116;
}
}
}
}
block_130:
{
if (x_124 == 0)
{
uint8_t x_125; 
x_125 = 0;
return x_125;
}
else
{
if (x_14 == 0)
{
if (x_37 == 0)
{
uint8_t x_126; 
x_126 = 1;
x_117 = x_126;
goto block_123;
}
else
{
uint8_t x_127; 
x_127 = 0;
x_117 = x_127;
goto block_123;
}
}
else
{
if (x_37 == 0)
{
uint8_t x_128; 
x_128 = 0;
x_117 = x_128;
goto block_123;
}
else
{
uint8_t x_129; 
x_129 = 1;
x_117 = x_129;
goto block_123;
}
}
}
}
block_137:
{
if (x_131 == 0)
{
uint8_t x_132; 
x_132 = 0;
return x_132;
}
else
{
if (x_13 == 0)
{
if (x_36 == 0)
{
uint8_t x_133; 
x_133 = 1;
x_124 = x_133;
goto block_130;
}
else
{
uint8_t x_134; 
x_134 = 0;
x_124 = x_134;
goto block_130;
}
}
else
{
if (x_36 == 0)
{
uint8_t x_135; 
x_135 = 0;
x_124 = x_135;
goto block_130;
}
else
{
uint8_t x_136; 
x_136 = 1;
x_124 = x_136;
goto block_130;
}
}
}
}
block_146:
{
if (x_138 == 0)
{
uint8_t x_139; 
x_139 = 0;
return x_139;
}
else
{
uint8_t x_140; 
x_140 = l_Lean_Meta_beqEtaStructMode____x40_Init_MetaTypes___hyg_106_(x_11, x_34);
if (x_140 == 0)
{
uint8_t x_141; 
x_141 = 0;
return x_141;
}
else
{
if (x_12 == 0)
{
if (x_35 == 0)
{
uint8_t x_142; 
x_142 = 1;
x_131 = x_142;
goto block_137;
}
else
{
uint8_t x_143; 
x_143 = 0;
x_131 = x_143;
goto block_137;
}
}
else
{
if (x_35 == 0)
{
uint8_t x_144; 
x_144 = 0;
x_131 = x_144;
goto block_137;
}
else
{
uint8_t x_145; 
x_145 = 1;
x_131 = x_145;
goto block_137;
}
}
}
}
}
block_153:
{
if (x_147 == 0)
{
uint8_t x_148; 
x_148 = 0;
return x_148;
}
else
{
if (x_10 == 0)
{
if (x_33 == 0)
{
uint8_t x_149; 
x_149 = 1;
x_138 = x_149;
goto block_146;
}
else
{
uint8_t x_150; 
x_150 = 0;
x_138 = x_150;
goto block_146;
}
}
else
{
if (x_33 == 0)
{
uint8_t x_151; 
x_151 = 0;
x_138 = x_151;
goto block_146;
}
else
{
uint8_t x_152; 
x_152 = 1;
x_138 = x_152;
goto block_146;
}
}
}
}
block_160:
{
if (x_154 == 0)
{
uint8_t x_155; 
x_155 = 0;
return x_155;
}
else
{
if (x_9 == 0)
{
if (x_32 == 0)
{
uint8_t x_156; 
x_156 = 1;
x_147 = x_156;
goto block_153;
}
else
{
uint8_t x_157; 
x_157 = 0;
x_147 = x_157;
goto block_153;
}
}
else
{
if (x_32 == 0)
{
uint8_t x_158; 
x_158 = 0;
x_147 = x_158;
goto block_153;
}
else
{
uint8_t x_159; 
x_159 = 1;
x_147 = x_159;
goto block_153;
}
}
}
}
block_167:
{
if (x_161 == 0)
{
uint8_t x_162; 
x_162 = 0;
return x_162;
}
else
{
if (x_8 == 0)
{
if (x_31 == 0)
{
uint8_t x_163; 
x_163 = 1;
x_154 = x_163;
goto block_160;
}
else
{
uint8_t x_164; 
x_164 = 0;
x_154 = x_164;
goto block_160;
}
}
else
{
if (x_31 == 0)
{
uint8_t x_165; 
x_165 = 0;
x_154 = x_165;
goto block_160;
}
else
{
uint8_t x_166; 
x_166 = 1;
x_154 = x_166;
goto block_160;
}
}
}
}
block_174:
{
if (x_168 == 0)
{
uint8_t x_169; 
x_169 = 0;
return x_169;
}
else
{
if (x_7 == 0)
{
if (x_30 == 0)
{
uint8_t x_170; 
x_170 = 1;
x_161 = x_170;
goto block_167;
}
else
{
uint8_t x_171; 
x_171 = 0;
x_161 = x_171;
goto block_167;
}
}
else
{
if (x_30 == 0)
{
uint8_t x_172; 
x_172 = 0;
x_161 = x_172;
goto block_167;
}
else
{
uint8_t x_173; 
x_173 = 1;
x_161 = x_173;
goto block_167;
}
}
}
}
block_181:
{
if (x_175 == 0)
{
uint8_t x_176; 
x_176 = 0;
return x_176;
}
else
{
if (x_6 == 0)
{
if (x_29 == 0)
{
uint8_t x_177; 
x_177 = 1;
x_168 = x_177;
goto block_174;
}
else
{
uint8_t x_178; 
x_178 = 0;
x_168 = x_178;
goto block_174;
}
}
else
{
if (x_29 == 0)
{
uint8_t x_179; 
x_179 = 0;
x_168 = x_179;
goto block_174;
}
else
{
uint8_t x_180; 
x_180 = 1;
x_168 = x_180;
goto block_174;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_beqConfig____x40_Init_MetaTypes___hyg_767____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_Simp_beqConfig____x40_Init_MetaTypes___hyg_767_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instBEqConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_beqConfig____x40_Init_MetaTypes___hyg_767____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instBEqConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Simp_instBEqConfig___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_neutralConfig___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Simp_defaultMaxSteps;
x_2 = lean_unsigned_to_nat(2u);
x_3 = 0;
x_4 = 1;
x_5 = 0;
x_6 = lean_alloc_ctor(0, 2, 21);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*2, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 1, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 2, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 3, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 4, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 5, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 6, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 7, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 8, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 9, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 10, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 11, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 12, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 13, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 14, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 15, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 16, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 17, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 18, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 19, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 20, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Simp_neutralConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Simp_neutralConfig___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedOccurrences() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_List_hasDecEq___at_Lean_Meta_beqOccurrences____x40_Init_MetaTypes___hyg_1257____spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
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
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_nat_dec_eq(x_6, x_8);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
else
{
x_1 = x_7;
x_2 = x_9;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_beqOccurrences____x40_Init_MetaTypes___hyg_1257_(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
if (lean_obj_tag(x_2) == 0)
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
case 1:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_2, 0);
x_7 = l_List_hasDecEq___at_Lean_Meta_beqOccurrences____x40_Init_MetaTypes___hyg_1257____spec__1(x_5, x_6);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
}
default: 
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_2, 0);
x_11 = l_List_hasDecEq___at_Lean_Meta_beqOccurrences____x40_Init_MetaTypes___hyg_1257____spec__1(x_9, x_10);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_hasDecEq___at_Lean_Meta_beqOccurrences____x40_Init_MetaTypes___hyg_1257____spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_hasDecEq___at_Lean_Meta_beqOccurrences____x40_Init_MetaTypes___hyg_1257____spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_beqOccurrences____x40_Init_MetaTypes___hyg_1257____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_beqOccurrences____x40_Init_MetaTypes___hyg_1257_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_instBEqOccurrences___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_beqOccurrences____x40_Init_MetaTypes___hyg_1257____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instBEqOccurrences() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_instBEqOccurrences___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instCoeListNatOccurrences(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* initialize_Init_Core(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_MetaTypes(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Core(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instInhabitedNameGenerator___closed__1 = _init_l_Lean_instInhabitedNameGenerator___closed__1();
lean_mark_persistent(l_Lean_instInhabitedNameGenerator___closed__1);
l_Lean_instInhabitedNameGenerator = _init_l_Lean_instInhabitedNameGenerator();
lean_mark_persistent(l_Lean_instInhabitedNameGenerator);
l_Lean_Meta_TransparencyMode_noConfusion___rarg___closed__1 = _init_l_Lean_Meta_TransparencyMode_noConfusion___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_TransparencyMode_noConfusion___rarg___closed__1);
l_Lean_Meta_instInhabitedTransparencyMode = _init_l_Lean_Meta_instInhabitedTransparencyMode();
l_Lean_Meta_instBEqTransparencyMode___closed__1 = _init_l_Lean_Meta_instBEqTransparencyMode___closed__1();
lean_mark_persistent(l_Lean_Meta_instBEqTransparencyMode___closed__1);
l_Lean_Meta_instBEqTransparencyMode = _init_l_Lean_Meta_instBEqTransparencyMode();
lean_mark_persistent(l_Lean_Meta_instBEqTransparencyMode);
l_Lean_Meta_instInhabitedEtaStructMode = _init_l_Lean_Meta_instInhabitedEtaStructMode();
l_Lean_Meta_instBEqEtaStructMode___closed__1 = _init_l_Lean_Meta_instBEqEtaStructMode___closed__1();
lean_mark_persistent(l_Lean_Meta_instBEqEtaStructMode___closed__1);
l_Lean_Meta_instBEqEtaStructMode = _init_l_Lean_Meta_instBEqEtaStructMode();
lean_mark_persistent(l_Lean_Meta_instBEqEtaStructMode);
l_Lean_Meta_DSimp_instInhabitedConfig___closed__1 = _init_l_Lean_Meta_DSimp_instInhabitedConfig___closed__1();
lean_mark_persistent(l_Lean_Meta_DSimp_instInhabitedConfig___closed__1);
l_Lean_Meta_DSimp_instInhabitedConfig = _init_l_Lean_Meta_DSimp_instInhabitedConfig();
lean_mark_persistent(l_Lean_Meta_DSimp_instInhabitedConfig);
l_Lean_Meta_DSimp_instBEqConfig___closed__1 = _init_l_Lean_Meta_DSimp_instBEqConfig___closed__1();
lean_mark_persistent(l_Lean_Meta_DSimp_instBEqConfig___closed__1);
l_Lean_Meta_DSimp_instBEqConfig = _init_l_Lean_Meta_DSimp_instBEqConfig();
lean_mark_persistent(l_Lean_Meta_DSimp_instBEqConfig);
l_Lean_Meta_Simp_defaultMaxSteps = _init_l_Lean_Meta_Simp_defaultMaxSteps();
lean_mark_persistent(l_Lean_Meta_Simp_defaultMaxSteps);
l_Lean_Meta_Simp_instInhabitedConfig___closed__1 = _init_l_Lean_Meta_Simp_instInhabitedConfig___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedConfig___closed__1);
l_Lean_Meta_Simp_instInhabitedConfig = _init_l_Lean_Meta_Simp_instInhabitedConfig();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedConfig);
l_Lean_Meta_Simp_instBEqConfig___closed__1 = _init_l_Lean_Meta_Simp_instBEqConfig___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_instBEqConfig___closed__1);
l_Lean_Meta_Simp_instBEqConfig = _init_l_Lean_Meta_Simp_instBEqConfig();
lean_mark_persistent(l_Lean_Meta_Simp_instBEqConfig);
l_Lean_Meta_Simp_neutralConfig___closed__1 = _init_l_Lean_Meta_Simp_neutralConfig___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_neutralConfig___closed__1);
l_Lean_Meta_Simp_neutralConfig = _init_l_Lean_Meta_Simp_neutralConfig();
lean_mark_persistent(l_Lean_Meta_Simp_neutralConfig);
l_Lean_Meta_instInhabitedOccurrences = _init_l_Lean_Meta_instInhabitedOccurrences();
lean_mark_persistent(l_Lean_Meta_instInhabitedOccurrences);
l_Lean_Meta_instBEqOccurrences___closed__1 = _init_l_Lean_Meta_instBEqOccurrences___closed__1();
lean_mark_persistent(l_Lean_Meta_instBEqOccurrences___closed__1);
l_Lean_Meta_instBEqOccurrences = _init_l_Lean_Meta_instBEqOccurrences();
lean_mark_persistent(l_Lean_Meta_instBEqOccurrences);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

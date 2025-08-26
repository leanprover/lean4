// Lean compiler output
// Module: Std.Sat.AIG.If
// Imports: Std.Sat.AIG.CachedGatesLemmas Std.Sat.AIG.LawfulVecOperator
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
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Bool_toNat(uint8_t);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkIfCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_mkGateCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_mkOrCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkIfCached(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_lor(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkIfCached___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_7);
lean_dec_ref(x_4);
lean_inc_ref(x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_9 = l_Std_Sat_AIG_mkGateCached___redArg(x_1, x_2, x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc_ref(x_11);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_12 = x_9;
} else {
 lean_dec_ref(x_9);
 x_12 = lean_box(0);
}
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
uint8_t x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
x_16 = lean_ctor_get_uint8(x_7, sizeof(void*)*1);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 x_17 = x_7;
} else {
 lean_dec_ref(x_7);
 x_17 = lean_box(0);
}
if (x_14 == 0)
{
uint8_t x_41; 
x_41 = 1;
lean_ctor_set_uint8(x_5, sizeof(void*)*1, x_41);
x_18 = x_10;
x_19 = x_5;
goto block_40;
}
else
{
uint8_t x_42; 
x_42 = 0;
lean_ctor_set_uint8(x_5, sizeof(void*)*1, x_42);
x_18 = x_10;
x_19 = x_5;
goto block_40;
}
block_40:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
if (lean_is_scalar(x_17)) {
 x_20 = lean_alloc_ctor(0, 1, 1);
} else {
 x_20 = x_17;
}
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set_uint8(x_20, sizeof(void*)*1, x_16);
if (lean_is_scalar(x_12)) {
 x_21 = lean_alloc_ctor(0, 2, 0);
} else {
 x_21 = x_12;
}
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_22 = l_Std_Sat_AIG_mkGateCached___redArg(x_1, x_2, x_18, x_21);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_11);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 0);
lean_ctor_set(x_22, 0, x_11);
x_26 = l_Std_Sat_AIG_mkOrCached___redArg(x_1, x_2, x_25, x_22);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_22, 0);
x_28 = lean_ctor_get(x_11, 0);
x_29 = lean_ctor_get_uint8(x_11, sizeof(void*)*1);
lean_inc(x_28);
lean_dec(x_11);
x_30 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*1, x_29);
lean_ctor_set(x_22, 0, x_30);
x_31 = l_Std_Sat_AIG_mkOrCached___redArg(x_1, x_2, x_27, x_22);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_ctor_get(x_22, 0);
x_33 = lean_ctor_get(x_22, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_22);
x_34 = lean_ctor_get(x_11, 0);
lean_inc(x_34);
x_35 = lean_ctor_get_uint8(x_11, sizeof(void*)*1);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 x_36 = x_11;
} else {
 lean_dec_ref(x_11);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(0, 1, 1);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_33);
x_39 = l_Std_Sat_AIG_mkOrCached___redArg(x_1, x_2, x_32, x_38);
return x_39;
}
}
}
else
{
lean_object* x_43; uint8_t x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_43 = lean_ctor_get(x_5, 0);
x_44 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
lean_inc(x_43);
lean_dec(x_5);
x_45 = lean_ctor_get(x_7, 0);
lean_inc(x_45);
x_46 = lean_ctor_get_uint8(x_7, sizeof(void*)*1);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 x_47 = x_7;
} else {
 lean_dec_ref(x_7);
 x_47 = lean_box(0);
}
if (x_44 == 0)
{
uint8_t x_63; lean_object* x_64; 
x_63 = 1;
x_64 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_64, 0, x_43);
lean_ctor_set_uint8(x_64, sizeof(void*)*1, x_63);
x_48 = x_10;
x_49 = x_64;
goto block_62;
}
else
{
uint8_t x_65; lean_object* x_66; 
x_65 = 0;
x_66 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_66, 0, x_43);
lean_ctor_set_uint8(x_66, sizeof(void*)*1, x_65);
x_48 = x_10;
x_49 = x_66;
goto block_62;
}
block_62:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
if (lean_is_scalar(x_47)) {
 x_50 = lean_alloc_ctor(0, 1, 1);
} else {
 x_50 = x_47;
}
lean_ctor_set(x_50, 0, x_45);
lean_ctor_set_uint8(x_50, sizeof(void*)*1, x_46);
if (lean_is_scalar(x_12)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_12;
}
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_52 = l_Std_Sat_AIG_mkGateCached___redArg(x_1, x_2, x_48, x_51);
x_53 = lean_ctor_get(x_52, 0);
lean_inc_ref(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc_ref(x_54);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_55 = x_52;
} else {
 lean_dec_ref(x_52);
 x_55 = lean_box(0);
}
x_56 = lean_ctor_get(x_11, 0);
lean_inc(x_56);
x_57 = lean_ctor_get_uint8(x_11, sizeof(void*)*1);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 x_58 = x_11;
} else {
 lean_dec_ref(x_11);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(0, 1, 1);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set_uint8(x_59, sizeof(void*)*1, x_57);
if (lean_is_scalar(x_55)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_55;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_54);
x_61 = l_Std_Sat_AIG_mkOrCached___redArg(x_1, x_2, x_53, x_60);
return x_61;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkIfCached(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Sat_AIG_mkIfCached___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite_go___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_41; lean_object* x_42; 
x_41 = lean_nat_dec_lt(x_5, x_3);
if (x_41 == 0)
{
lean_object* x_53; 
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_4);
lean_ctor_set(x_53, 1, x_9);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_54 = lean_array_fget_borrowed(x_7, x_5);
x_55 = lean_unsigned_to_nat(1u);
x_56 = lean_nat_shiftr(x_54, x_55);
x_57 = lean_nat_land(x_55, x_54);
x_58 = lean_unsigned_to_nat(0u);
x_59 = lean_nat_dec_eq(x_57, x_58);
lean_dec(x_57);
if (x_59 == 0)
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_60, 0, x_56);
lean_ctor_set_uint8(x_60, sizeof(void*)*1, x_41);
x_42 = x_60;
goto block_52;
}
else
{
uint8_t x_61; lean_object* x_62; 
x_61 = 0;
x_62 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_62, 0, x_56);
lean_ctor_set_uint8(x_62, sizeof(void*)*1, x_61);
x_42 = x_62;
goto block_52;
}
}
block_40:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; 
lean_inc_ref(x_6);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 2, x_11);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_13 = l_Std_Sat_AIG_mkIfCached___redArg(x_1, x_2, x_4, x_12);
x_14 = lean_ctor_get(x_13, 1);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_15);
lean_dec_ref(x_13);
x_16 = lean_ctor_get(x_6, 0);
lean_inc(x_16);
x_17 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
lean_dec_ref(x_6);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_ctor_get_uint8(x_14, sizeof(void*)*1);
lean_ctor_set(x_14, 0, x_16);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_17);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_5, x_21);
lean_dec(x_5);
x_23 = lean_unsigned_to_nat(2u);
x_24 = lean_nat_mul(x_19, x_23);
lean_dec(x_19);
x_25 = l_Bool_toNat(x_20);
x_26 = lean_nat_lor(x_24, x_25);
lean_dec(x_25);
lean_dec(x_24);
x_27 = lean_array_push(x_9, x_26);
x_4 = x_15;
x_5 = x_22;
x_6 = x_14;
x_9 = x_27;
goto _start;
}
else
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_29 = lean_ctor_get(x_14, 0);
x_30 = lean_ctor_get_uint8(x_14, sizeof(void*)*1);
lean_inc(x_29);
lean_dec(x_14);
x_31 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_31, 0, x_16);
lean_ctor_set_uint8(x_31, sizeof(void*)*1, x_17);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_5, x_32);
lean_dec(x_5);
x_34 = lean_unsigned_to_nat(2u);
x_35 = lean_nat_mul(x_29, x_34);
lean_dec(x_29);
x_36 = l_Bool_toNat(x_30);
x_37 = lean_nat_lor(x_35, x_36);
lean_dec(x_36);
lean_dec(x_35);
x_38 = lean_array_push(x_9, x_37);
x_4 = x_15;
x_5 = x_33;
x_6 = x_31;
x_9 = x_38;
goto _start;
}
}
block_52:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_43 = lean_array_fget_borrowed(x_8, x_5);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_shiftr(x_43, x_44);
x_46 = lean_nat_land(x_44, x_43);
x_47 = lean_unsigned_to_nat(0u);
x_48 = lean_nat_dec_eq(x_46, x_47);
lean_dec(x_46);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_49, 0, x_45);
lean_ctor_set_uint8(x_49, sizeof(void*)*1, x_41);
x_10 = x_42;
x_11 = x_49;
goto block_40;
}
else
{
uint8_t x_50; lean_object* x_51; 
x_50 = 0;
x_51 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_51, 0, x_45);
lean_ctor_set_uint8(x_51, sizeof(void*)*1, x_50);
x_10 = x_42;
x_11 = x_51;
goto block_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Sat_AIG_RefVec_ite_go___redArg(x_2, x_3, x_4, x_5, x_6, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite_go___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_Sat_AIG_RefVec_ite_go___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Sat_AIG_RefVec_ite_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_5, 2);
lean_inc_ref(x_8);
lean_dec_ref(x_5);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_mk_empty_array_with_capacity(x_3);
x_11 = l_Std_Sat_AIG_RefVec_ite_go___redArg(x_1, x_2, x_3, x_4, x_9, x_6, x_7, x_8, x_10);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Sat_AIG_RefVec_ite___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Sat_AIG_RefVec_ite___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Sat_AIG_RefVec_ite(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_7;
}
}
lean_object* initialize_Std_Sat_AIG_CachedGatesLemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Sat_AIG_LawfulVecOperator(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sat_AIG_If(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sat_AIG_CachedGatesLemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_AIG_LawfulVecOperator(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

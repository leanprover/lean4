// Lean compiler output
// Module: Std.Time.Zoned.Database.Basic
// Imports: Std.Time.Zoned.ZoneRules Std.Time.Zoned.Database.TzIf
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
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertLocalTimeType(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertTZifV1(lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_x27_loop___at_Std_Time_TimeZone_convertTZifV1___spec__1___closed__2;
extern lean_object* l_Std_Time_TimeZone_instInhabitedLocalTimeType;
lean_object* lean_uint32_to_nat(uint32_t);
extern lean_object* l_Int_instInhabited;
lean_object* lean_array_push(lean_object*, lean_object*);
static uint8_t l_Std_Time_TimeZone_convertLocalTimeType___closed__2;
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertTZifV1___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertTZifV1___boxed(lean_object*, lean_object*);
lean_object* l_Std_Time_TimeZone_Offset_toIsoString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Std_Time_TimeZone_convertTZifV1___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Std_Time_TimeZone_convertTZifV1___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Time_TimeZone_convertTZifV1___closed__3;
static lean_object* l_Std_Time_TimeZone_convertTZifV1___closed__2;
static lean_object* l_Std_Time_TimeZone_convertTZifV1___closed__1;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertTZifV2(lean_object*, lean_object*);
static uint8_t l_Std_Time_TimeZone_convertLocalTimeType___closed__1;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertTZif(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_TimeZone_convertWall(uint8_t);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Std_Time_TimeZone_convertTZifV1___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertTransition(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_x27_loop___at_Std_Time_TimeZone_convertTZifV1___spec__1___closed__1;
extern uint8_t l_instInhabitedUInt8;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_x27_loop___at_Std_Time_TimeZone_convertTZifV1___spec__2___closed__1;
LEAN_EXPORT uint8_t l_Std_Time_TimeZone_convertUt(uint8_t);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Std_Time_TimeZone_convertTZifV1___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertTZifV2___boxed(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_uint8_to_nat(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertWall___boxed(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertLocalTimeType___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertUt___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertTZif___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertTransition___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_get_x3f___rarg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_TimeZone_convertWall(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertWall___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Std_Time_TimeZone_convertWall(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_Time_TimeZone_convertUt(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertUt___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Std_Time_TimeZone_convertUt(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static uint8_t _init_l_Std_Time_TimeZone_convertLocalTimeType___closed__1() {
_start:
{
uint8_t x_1; uint8_t x_2; 
x_1 = 1;
x_2 = l_Std_Time_TimeZone_convertWall(x_1);
return x_2;
}
}
static uint8_t _init_l_Std_Time_TimeZone_convertLocalTimeType___closed__2() {
_start:
{
uint8_t x_1; uint8_t x_2; 
x_1 = 1;
x_2 = l_Std_Time_TimeZone_convertUt(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertLocalTimeType(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 3);
x_5 = l_Array_get_x3f___rarg(x_4, x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get_uint8(x_8, sizeof(void*)*1);
lean_dec(x_8);
x_11 = lean_ctor_get(x_2, 4);
x_12 = 1;
lean_inc(x_9);
x_13 = l_Std_Time_TimeZone_Offset_toIsoString(x_9, x_12);
x_14 = lean_array_get_size(x_11);
x_15 = lean_nat_dec_lt(x_1, x_14);
lean_dec(x_14);
x_16 = lean_ctor_get(x_2, 6);
x_17 = lean_array_get_size(x_16);
x_18 = lean_nat_dec_lt(x_1, x_17);
lean_dec(x_17);
x_19 = lean_ctor_get(x_2, 7);
x_20 = lean_array_get_size(x_19);
x_21 = lean_nat_dec_lt(x_1, x_20);
lean_dec(x_20);
if (x_15 == 0)
{
if (x_18 == 0)
{
if (x_21 == 0)
{
uint8_t x_22; uint8_t x_23; lean_object* x_24; 
x_22 = l_Std_Time_TimeZone_convertLocalTimeType___closed__1;
x_23 = l_Std_Time_TimeZone_convertLocalTimeType___closed__2;
x_24 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_24, 0, x_9);
lean_ctor_set(x_24, 1, x_13);
lean_ctor_set(x_24, 2, x_3);
lean_ctor_set_uint8(x_24, sizeof(void*)*3, x_10);
lean_ctor_set_uint8(x_24, sizeof(void*)*3 + 1, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*3 + 2, x_23);
lean_ctor_set(x_5, 0, x_24);
return x_5;
}
else
{
lean_object* x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; lean_object* x_29; 
x_25 = lean_array_fget(x_19, x_1);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
x_27 = l_Std_Time_TimeZone_convertUt(x_26);
x_28 = l_Std_Time_TimeZone_convertLocalTimeType___closed__1;
x_29 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_29, 0, x_9);
lean_ctor_set(x_29, 1, x_13);
lean_ctor_set(x_29, 2, x_3);
lean_ctor_set_uint8(x_29, sizeof(void*)*3, x_10);
lean_ctor_set_uint8(x_29, sizeof(void*)*3 + 1, x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*3 + 2, x_27);
lean_ctor_set(x_5, 0, x_29);
return x_5;
}
}
else
{
lean_object* x_30; uint8_t x_31; uint8_t x_32; 
x_30 = lean_array_fget(x_16, x_1);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
x_32 = l_Std_Time_TimeZone_convertWall(x_31);
if (x_21 == 0)
{
uint8_t x_33; lean_object* x_34; 
x_33 = l_Std_Time_TimeZone_convertLocalTimeType___closed__2;
x_34 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_34, 0, x_9);
lean_ctor_set(x_34, 1, x_13);
lean_ctor_set(x_34, 2, x_3);
lean_ctor_set_uint8(x_34, sizeof(void*)*3, x_10);
lean_ctor_set_uint8(x_34, sizeof(void*)*3 + 1, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*3 + 2, x_33);
lean_ctor_set(x_5, 0, x_34);
return x_5;
}
else
{
lean_object* x_35; uint8_t x_36; uint8_t x_37; lean_object* x_38; 
x_35 = lean_array_fget(x_19, x_1);
x_36 = lean_unbox(x_35);
lean_dec(x_35);
x_37 = l_Std_Time_TimeZone_convertUt(x_36);
x_38 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_38, 0, x_9);
lean_ctor_set(x_38, 1, x_13);
lean_ctor_set(x_38, 2, x_3);
lean_ctor_set_uint8(x_38, sizeof(void*)*3, x_10);
lean_ctor_set_uint8(x_38, sizeof(void*)*3 + 1, x_32);
lean_ctor_set_uint8(x_38, sizeof(void*)*3 + 2, x_37);
lean_ctor_set(x_5, 0, x_38);
return x_5;
}
}
}
else
{
lean_object* x_39; 
lean_dec(x_13);
x_39 = lean_array_fget(x_11, x_1);
if (x_18 == 0)
{
if (x_21 == 0)
{
uint8_t x_40; uint8_t x_41; lean_object* x_42; 
x_40 = l_Std_Time_TimeZone_convertLocalTimeType___closed__1;
x_41 = l_Std_Time_TimeZone_convertLocalTimeType___closed__2;
x_42 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_42, 0, x_9);
lean_ctor_set(x_42, 1, x_39);
lean_ctor_set(x_42, 2, x_3);
lean_ctor_set_uint8(x_42, sizeof(void*)*3, x_10);
lean_ctor_set_uint8(x_42, sizeof(void*)*3 + 1, x_40);
lean_ctor_set_uint8(x_42, sizeof(void*)*3 + 2, x_41);
lean_ctor_set(x_5, 0, x_42);
return x_5;
}
else
{
lean_object* x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; lean_object* x_47; 
x_43 = lean_array_fget(x_19, x_1);
x_44 = lean_unbox(x_43);
lean_dec(x_43);
x_45 = l_Std_Time_TimeZone_convertUt(x_44);
x_46 = l_Std_Time_TimeZone_convertLocalTimeType___closed__1;
x_47 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_47, 0, x_9);
lean_ctor_set(x_47, 1, x_39);
lean_ctor_set(x_47, 2, x_3);
lean_ctor_set_uint8(x_47, sizeof(void*)*3, x_10);
lean_ctor_set_uint8(x_47, sizeof(void*)*3 + 1, x_46);
lean_ctor_set_uint8(x_47, sizeof(void*)*3 + 2, x_45);
lean_ctor_set(x_5, 0, x_47);
return x_5;
}
}
else
{
lean_object* x_48; uint8_t x_49; uint8_t x_50; 
x_48 = lean_array_fget(x_16, x_1);
x_49 = lean_unbox(x_48);
lean_dec(x_48);
x_50 = l_Std_Time_TimeZone_convertWall(x_49);
if (x_21 == 0)
{
uint8_t x_51; lean_object* x_52; 
x_51 = l_Std_Time_TimeZone_convertLocalTimeType___closed__2;
x_52 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_52, 0, x_9);
lean_ctor_set(x_52, 1, x_39);
lean_ctor_set(x_52, 2, x_3);
lean_ctor_set_uint8(x_52, sizeof(void*)*3, x_10);
lean_ctor_set_uint8(x_52, sizeof(void*)*3 + 1, x_50);
lean_ctor_set_uint8(x_52, sizeof(void*)*3 + 2, x_51);
lean_ctor_set(x_5, 0, x_52);
return x_5;
}
else
{
lean_object* x_53; uint8_t x_54; uint8_t x_55; lean_object* x_56; 
x_53 = lean_array_fget(x_19, x_1);
x_54 = lean_unbox(x_53);
lean_dec(x_53);
x_55 = l_Std_Time_TimeZone_convertUt(x_54);
x_56 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_56, 0, x_9);
lean_ctor_set(x_56, 1, x_39);
lean_ctor_set(x_56, 2, x_3);
lean_ctor_set_uint8(x_56, sizeof(void*)*3, x_10);
lean_ctor_set_uint8(x_56, sizeof(void*)*3 + 1, x_50);
lean_ctor_set_uint8(x_56, sizeof(void*)*3 + 2, x_55);
lean_ctor_set(x_5, 0, x_56);
return x_5;
}
}
}
}
else
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_57 = lean_ctor_get(x_5, 0);
lean_inc(x_57);
lean_dec(x_5);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get_uint8(x_57, sizeof(void*)*1);
lean_dec(x_57);
x_60 = lean_ctor_get(x_2, 4);
x_61 = 1;
lean_inc(x_58);
x_62 = l_Std_Time_TimeZone_Offset_toIsoString(x_58, x_61);
x_63 = lean_array_get_size(x_60);
x_64 = lean_nat_dec_lt(x_1, x_63);
lean_dec(x_63);
x_65 = lean_ctor_get(x_2, 6);
x_66 = lean_array_get_size(x_65);
x_67 = lean_nat_dec_lt(x_1, x_66);
lean_dec(x_66);
x_68 = lean_ctor_get(x_2, 7);
x_69 = lean_array_get_size(x_68);
x_70 = lean_nat_dec_lt(x_1, x_69);
lean_dec(x_69);
if (x_64 == 0)
{
if (x_67 == 0)
{
if (x_70 == 0)
{
uint8_t x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; 
x_71 = l_Std_Time_TimeZone_convertLocalTimeType___closed__1;
x_72 = l_Std_Time_TimeZone_convertLocalTimeType___closed__2;
x_73 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_73, 0, x_58);
lean_ctor_set(x_73, 1, x_62);
lean_ctor_set(x_73, 2, x_3);
lean_ctor_set_uint8(x_73, sizeof(void*)*3, x_59);
lean_ctor_set_uint8(x_73, sizeof(void*)*3 + 1, x_71);
lean_ctor_set_uint8(x_73, sizeof(void*)*3 + 2, x_72);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_73);
return x_74;
}
else
{
lean_object* x_75; uint8_t x_76; uint8_t x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; 
x_75 = lean_array_fget(x_68, x_1);
x_76 = lean_unbox(x_75);
lean_dec(x_75);
x_77 = l_Std_Time_TimeZone_convertUt(x_76);
x_78 = l_Std_Time_TimeZone_convertLocalTimeType___closed__1;
x_79 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_79, 0, x_58);
lean_ctor_set(x_79, 1, x_62);
lean_ctor_set(x_79, 2, x_3);
lean_ctor_set_uint8(x_79, sizeof(void*)*3, x_59);
lean_ctor_set_uint8(x_79, sizeof(void*)*3 + 1, x_78);
lean_ctor_set_uint8(x_79, sizeof(void*)*3 + 2, x_77);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
return x_80;
}
}
else
{
lean_object* x_81; uint8_t x_82; uint8_t x_83; 
x_81 = lean_array_fget(x_65, x_1);
x_82 = lean_unbox(x_81);
lean_dec(x_81);
x_83 = l_Std_Time_TimeZone_convertWall(x_82);
if (x_70 == 0)
{
uint8_t x_84; lean_object* x_85; lean_object* x_86; 
x_84 = l_Std_Time_TimeZone_convertLocalTimeType___closed__2;
x_85 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_85, 0, x_58);
lean_ctor_set(x_85, 1, x_62);
lean_ctor_set(x_85, 2, x_3);
lean_ctor_set_uint8(x_85, sizeof(void*)*3, x_59);
lean_ctor_set_uint8(x_85, sizeof(void*)*3 + 1, x_83);
lean_ctor_set_uint8(x_85, sizeof(void*)*3 + 2, x_84);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_85);
return x_86;
}
else
{
lean_object* x_87; uint8_t x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; 
x_87 = lean_array_fget(x_68, x_1);
x_88 = lean_unbox(x_87);
lean_dec(x_87);
x_89 = l_Std_Time_TimeZone_convertUt(x_88);
x_90 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_90, 0, x_58);
lean_ctor_set(x_90, 1, x_62);
lean_ctor_set(x_90, 2, x_3);
lean_ctor_set_uint8(x_90, sizeof(void*)*3, x_59);
lean_ctor_set_uint8(x_90, sizeof(void*)*3 + 1, x_83);
lean_ctor_set_uint8(x_90, sizeof(void*)*3 + 2, x_89);
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_90);
return x_91;
}
}
}
else
{
lean_object* x_92; 
lean_dec(x_62);
x_92 = lean_array_fget(x_60, x_1);
if (x_67 == 0)
{
if (x_70 == 0)
{
uint8_t x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; 
x_93 = l_Std_Time_TimeZone_convertLocalTimeType___closed__1;
x_94 = l_Std_Time_TimeZone_convertLocalTimeType___closed__2;
x_95 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_95, 0, x_58);
lean_ctor_set(x_95, 1, x_92);
lean_ctor_set(x_95, 2, x_3);
lean_ctor_set_uint8(x_95, sizeof(void*)*3, x_59);
lean_ctor_set_uint8(x_95, sizeof(void*)*3 + 1, x_93);
lean_ctor_set_uint8(x_95, sizeof(void*)*3 + 2, x_94);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_95);
return x_96;
}
else
{
lean_object* x_97; uint8_t x_98; uint8_t x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; 
x_97 = lean_array_fget(x_68, x_1);
x_98 = lean_unbox(x_97);
lean_dec(x_97);
x_99 = l_Std_Time_TimeZone_convertUt(x_98);
x_100 = l_Std_Time_TimeZone_convertLocalTimeType___closed__1;
x_101 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_101, 0, x_58);
lean_ctor_set(x_101, 1, x_92);
lean_ctor_set(x_101, 2, x_3);
lean_ctor_set_uint8(x_101, sizeof(void*)*3, x_59);
lean_ctor_set_uint8(x_101, sizeof(void*)*3 + 1, x_100);
lean_ctor_set_uint8(x_101, sizeof(void*)*3 + 2, x_99);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_101);
return x_102;
}
}
else
{
lean_object* x_103; uint8_t x_104; uint8_t x_105; 
x_103 = lean_array_fget(x_65, x_1);
x_104 = lean_unbox(x_103);
lean_dec(x_103);
x_105 = l_Std_Time_TimeZone_convertWall(x_104);
if (x_70 == 0)
{
uint8_t x_106; lean_object* x_107; lean_object* x_108; 
x_106 = l_Std_Time_TimeZone_convertLocalTimeType___closed__2;
x_107 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_107, 0, x_58);
lean_ctor_set(x_107, 1, x_92);
lean_ctor_set(x_107, 2, x_3);
lean_ctor_set_uint8(x_107, sizeof(void*)*3, x_59);
lean_ctor_set_uint8(x_107, sizeof(void*)*3 + 1, x_105);
lean_ctor_set_uint8(x_107, sizeof(void*)*3 + 2, x_106);
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_107);
return x_108;
}
else
{
lean_object* x_109; uint8_t x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; 
x_109 = lean_array_fget(x_68, x_1);
x_110 = lean_unbox(x_109);
lean_dec(x_109);
x_111 = l_Std_Time_TimeZone_convertUt(x_110);
x_112 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_112, 0, x_58);
lean_ctor_set(x_112, 1, x_92);
lean_ctor_set(x_112, 2, x_3);
lean_ctor_set_uint8(x_112, sizeof(void*)*3, x_59);
lean_ctor_set_uint8(x_112, sizeof(void*)*3 + 1, x_105);
lean_ctor_set_uint8(x_112, sizeof(void*)*3 + 2, x_111);
x_113 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_113, 0, x_112);
return x_113;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertLocalTimeType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_TimeZone_convertLocalTimeType(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertTransition(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_4 = lean_ctor_get(x_3, 1);
x_5 = l_Int_instInhabited;
x_6 = lean_array_get(x_5, x_4, x_2);
x_7 = lean_ctor_get(x_3, 2);
x_8 = l_instInhabitedUInt8;
x_9 = lean_box(x_8);
x_10 = lean_array_get(x_9, x_7, x_2);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
x_12 = lean_uint8_to_nat(x_11);
x_13 = l_Std_Time_TimeZone_instInhabitedLocalTimeType;
x_14 = lean_array_get(x_13, x_1, x_12);
lean_dec(x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertTransition___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_TimeZone_convertTransition(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at_Std_Time_TimeZone_convertTZifV1___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cannot convert local time ", 26, 26);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at_Std_Time_TimeZone_convertTZifV1___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" of the file", 12, 12);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Std_Time_TimeZone_convertTZifV1___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_nat_dec_lt(x_8, x_5);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_10);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_7, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_7, x_15);
lean_dec(x_7);
lean_inc(x_2);
x_17 = l_Std_Time_TimeZone_convertLocalTimeType(x_8, x_1, x_2);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_2);
x_18 = l___private_Init_Data_Repr_0__Nat_reprFast(x_8);
x_19 = l_Std_Range_forIn_x27_loop___at_Std_Time_TimeZone_convertTZifV1___spec__1___closed__1;
x_20 = lean_string_append(x_19, x_18);
lean_dec(x_18);
x_21 = l_Std_Range_forIn_x27_loop___at_Std_Time_TimeZone_convertTZifV1___spec__1___closed__2;
x_22 = lean_string_append(x_20, x_21);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_17, 0);
lean_inc(x_24);
lean_dec(x_17);
x_25 = lean_array_push(x_10, x_24);
x_26 = lean_nat_add(x_8, x_6);
lean_dec(x_8);
x_7 = x_16;
x_8 = x_26;
x_9 = lean_box(0);
x_10 = x_25;
goto _start;
}
}
else
{
lean_object* x_28; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_10);
return x_28;
}
}
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at_Std_Time_TimeZone_convertTZifV1___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cannot convert transition ", 26, 26);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Std_Time_TimeZone_convertTZifV1___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_nat_dec_lt(x_8, x_5);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_10);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_7, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_7, x_15);
lean_dec(x_7);
x_17 = l_Std_Time_TimeZone_convertTransition(x_2, x_8, x_1);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_array_push(x_10, x_18);
x_20 = lean_nat_add(x_8, x_6);
lean_dec(x_8);
x_7 = x_16;
x_8 = x_20;
x_9 = lean_box(0);
x_10 = x_19;
goto _start;
}
else
{
lean_object* x_22; 
lean_dec(x_8);
lean_dec(x_7);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_10);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertTZifV1___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
static lean_object* _init_l_Std_Time_TimeZone_convertTZifV1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_TimeZone_convertTZifV1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("empty transitions for ", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Std_Time_TimeZone_convertTZifV1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertTZifV1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint32_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get_uint32(x_3, 16);
x_5 = lean_uint32_to_nat(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_unsigned_to_nat(1u);
lean_inc(x_5);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_5);
lean_ctor_set(x_8, 2, x_7);
x_9 = l_Std_Time_TimeZone_convertTZifV1___closed__1;
lean_inc(x_5);
lean_inc(x_2);
x_10 = l_Std_Range_forIn_x27_loop___at_Std_Time_TimeZone_convertTZifV1___spec__1(x_1, x_2, x_8, x_6, x_5, x_7, x_5, x_6, lean_box(0), x_9);
lean_dec(x_5);
lean_dec(x_8);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_ctor_get(x_1, 1);
x_16 = lean_array_get_size(x_15);
lean_inc(x_16);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_17, 2, x_7);
lean_inc(x_16);
x_18 = l_Std_Range_forIn_x27_loop___at_Std_Time_TimeZone_convertTZifV1___spec__2(x_1, x_14, x_17, x_6, x_16, x_7, x_16, x_6, lean_box(0), x_9);
lean_dec(x_16);
lean_dec(x_17);
lean_dec(x_14);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_2);
x_21 = l_Std_Time_TimeZone_convertLocalTimeType(x_6, x_1, x_2);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_20);
x_22 = l_Std_Time_TimeZone_convertTZifV1___closed__2;
x_23 = lean_string_append(x_22, x_2);
lean_dec(x_2);
x_24 = l_Std_Time_TimeZone_convertTZifV1___closed__3;
x_25 = lean_string_append(x_23, x_24);
lean_ctor_set_tag(x_18, 0);
lean_ctor_set(x_18, 0, x_25);
return x_18;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_free_object(x_18);
lean_dec(x_2);
x_26 = lean_ctor_get(x_21, 0);
lean_inc(x_26);
lean_dec(x_21);
x_27 = l_Std_Time_TimeZone_convertTZifV1___lambda__1(x_20, x_26);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_18, 0);
lean_inc(x_28);
lean_dec(x_18);
lean_inc(x_2);
x_29 = l_Std_Time_TimeZone_convertLocalTimeType(x_6, x_1, x_2);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_28);
x_30 = l_Std_Time_TimeZone_convertTZifV1___closed__2;
x_31 = lean_string_append(x_30, x_2);
lean_dec(x_2);
x_32 = l_Std_Time_TimeZone_convertTZifV1___closed__3;
x_33 = lean_string_append(x_31, x_32);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_2);
x_35 = lean_ctor_get(x_29, 0);
lean_inc(x_35);
lean_dec(x_29);
x_36 = l_Std_Time_TimeZone_convertTZifV1___lambda__1(x_28, x_35);
return x_36;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Std_Time_TimeZone_convertTZifV1___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Std_Range_forIn_x27_loop___at_Std_Time_TimeZone_convertTZifV1___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Std_Time_TimeZone_convertTZifV1___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Std_Range_forIn_x27_loop___at_Std_Time_TimeZone_convertTZifV1___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertTZifV1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_TimeZone_convertTZifV1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertTZifV2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Std_Time_TimeZone_convertTZifV1(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertTZifV2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_TimeZone_convertTZifV2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertTZif(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = l_Std_Time_TimeZone_convertTZifV1(x_4, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = l_Std_Time_TimeZone_convertTZifV2(x_6, x_2);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertTZif___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_TimeZone_convertTZif(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Std_Time_Zoned_ZoneRules(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Time_Zoned_Database_TzIf(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_Zoned_Database_Basic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time_Zoned_ZoneRules(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Zoned_Database_TzIf(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Time_TimeZone_convertLocalTimeType___closed__1 = _init_l_Std_Time_TimeZone_convertLocalTimeType___closed__1();
l_Std_Time_TimeZone_convertLocalTimeType___closed__2 = _init_l_Std_Time_TimeZone_convertLocalTimeType___closed__2();
l_Std_Range_forIn_x27_loop___at_Std_Time_TimeZone_convertTZifV1___spec__1___closed__1 = _init_l_Std_Range_forIn_x27_loop___at_Std_Time_TimeZone_convertTZifV1___spec__1___closed__1();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at_Std_Time_TimeZone_convertTZifV1___spec__1___closed__1);
l_Std_Range_forIn_x27_loop___at_Std_Time_TimeZone_convertTZifV1___spec__1___closed__2 = _init_l_Std_Range_forIn_x27_loop___at_Std_Time_TimeZone_convertTZifV1___spec__1___closed__2();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at_Std_Time_TimeZone_convertTZifV1___spec__1___closed__2);
l_Std_Range_forIn_x27_loop___at_Std_Time_TimeZone_convertTZifV1___spec__2___closed__1 = _init_l_Std_Range_forIn_x27_loop___at_Std_Time_TimeZone_convertTZifV1___spec__2___closed__1();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at_Std_Time_TimeZone_convertTZifV1___spec__2___closed__1);
l_Std_Time_TimeZone_convertTZifV1___closed__1 = _init_l_Std_Time_TimeZone_convertTZifV1___closed__1();
lean_mark_persistent(l_Std_Time_TimeZone_convertTZifV1___closed__1);
l_Std_Time_TimeZone_convertTZifV1___closed__2 = _init_l_Std_Time_TimeZone_convertTZifV1___closed__2();
lean_mark_persistent(l_Std_Time_TimeZone_convertTZifV1___closed__2);
l_Std_Time_TimeZone_convertTZifV1___closed__3 = _init_l_Std_Time_TimeZone_convertTZifV1___closed__3();
lean_mark_persistent(l_Std_Time_TimeZone_convertTZifV1___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

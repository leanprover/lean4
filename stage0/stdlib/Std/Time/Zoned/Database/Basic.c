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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertTZifV1(lean_object*, lean_object*);
extern lean_object* l_Std_Time_TimeZone_instInhabitedLocalTimeType;
lean_object* lean_uint32_to_nat(uint32_t);
extern lean_object* l_Int_instInhabited;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_x27_loop___at___Std_Time_TimeZone_convertTZifV1_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Time_TimeZone_convertTZifV1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Time_TimeZone_convertTZifV1___closed__0;
static lean_object* l_Std_Range_forIn_x27_loop___at___Std_Time_TimeZone_convertTZifV1_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertTZifV1___boxed(lean_object*, lean_object*);
lean_object* l_Std_Time_TimeZone_Offset_toIsoString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Time_TimeZone_convertTZifV1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
static lean_object* l_Std_Time_TimeZone_convertTZifV1___closed__1;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertTZifV2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertTZif(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_TimeZone_convertWall(uint8_t);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Time_TimeZone_convertTZifV1_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertTransition(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Time_TimeZone_convertTZifV1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Time_TimeZone_convertTZifV1_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern uint8_t l_instInhabitedUInt8;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_TimeZone_convertUt(uint8_t);
static lean_object* l_Std_Range_forIn_x27_loop___at___Std_Time_TimeZone_convertTZifV1_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Time_TimeZone_convertTZifV1_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertTZifV2___boxed(lean_object*, lean_object*);
lean_object* lean_uint8_to_nat(uint8_t);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Time_TimeZone_convertTZifV1_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertWall___boxed(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertLocalTimeType___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Time_TimeZone_convertTZifV1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertUt___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertTZif___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertTransition___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_TimeZone_convertWall(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
else
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(1);
x_5 = lean_unbox(x_4);
return x_5;
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
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(1);
x_3 = lean_unbox(x_2);
return x_3;
}
else
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
return x_5;
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
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertLocalTimeType(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_2, 3);
x_5 = lean_ctor_get(x_2, 4);
x_6 = lean_ctor_get(x_2, 6);
x_7 = lean_ctor_get(x_2, 7);
x_8 = lean_array_get_size(x_4);
x_9 = lean_nat_dec_lt(x_1, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_3);
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_21; uint8_t x_22; lean_object* x_29; lean_object* x_35; uint8_t x_36; 
x_11 = lean_array_fget(x_4, x_1);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get_uint8(x_11, sizeof(void*)*1);
lean_dec(x_11);
x_35 = lean_array_get_size(x_5);
x_36 = lean_nat_dec_lt(x_1, x_35);
lean_dec(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
lean_inc(x_12);
x_37 = l_Std_Time_TimeZone_Offset_toIsoString(x_12, x_9);
x_29 = x_37;
goto block_34;
}
else
{
lean_object* x_38; 
x_38 = lean_array_fget(x_5, x_1);
x_29 = x_38;
goto block_34;
}
block_20:
{
uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_17 = l_Std_Time_TimeZone_convertUt(x_16);
x_18 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set(x_18, 2, x_3);
lean_ctor_set_uint8(x_18, sizeof(void*)*3, x_13);
lean_ctor_set_uint8(x_18, sizeof(void*)*3 + 1, x_15);
lean_ctor_set_uint8(x_18, sizeof(void*)*3 + 2, x_17);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
block_28:
{
uint8_t x_23; lean_object* x_24; uint8_t x_25; 
x_23 = l_Std_Time_TimeZone_convertWall(x_22);
x_24 = lean_array_get_size(x_7);
x_25 = lean_nat_dec_lt(x_1, x_24);
lean_dec(x_24);
if (x_25 == 0)
{
x_14 = x_21;
x_15 = x_23;
x_16 = x_9;
goto block_20;
}
else
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_array_fget(x_7, x_1);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
x_14 = x_21;
x_15 = x_23;
x_16 = x_27;
goto block_20;
}
}
block_34:
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_array_get_size(x_6);
x_31 = lean_nat_dec_lt(x_1, x_30);
lean_dec(x_30);
if (x_31 == 0)
{
x_21 = x_29;
x_22 = x_9;
goto block_28;
}
else
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_array_fget(x_6, x_1);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
x_21 = x_29;
x_22 = x_33;
goto block_28;
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_4 = lean_ctor_get(x_3, 1);
x_5 = lean_ctor_get(x_3, 2);
x_6 = l_Int_instInhabited;
x_7 = l_instInhabitedUInt8;
x_8 = l_Std_Time_TimeZone_instInhabitedLocalTimeType;
x_9 = lean_array_get(x_6, x_4, x_2);
x_10 = lean_box(x_7);
x_11 = lean_array_get(x_10, x_5, x_2);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
x_13 = lean_uint8_to_nat(x_12);
x_14 = lean_array_get(x_8, x_1, x_13);
lean_dec(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_9);
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
static lean_object* _init_l_Std_Range_forIn_x27_loop___at___Std_Time_TimeZone_convertTZifV1_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cannot convert local time ", 26, 26);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at___Std_Time_TimeZone_convertTZifV1_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" of the file", 12, 12);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Time_TimeZone_convertTZifV1_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_nat_dec_lt(x_5, x_6);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_2);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_4);
return x_9;
}
else
{
lean_object* x_10; 
lean_inc(x_2);
x_10 = l_Std_Time_TimeZone_convertLocalTimeType(x_5, x_1, x_2);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
lean_dec(x_2);
x_11 = l_Std_Range_forIn_x27_loop___at___Std_Time_TimeZone_convertTZifV1_spec__0___redArg___closed__0;
x_12 = l_Nat_reprFast(x_5);
x_13 = lean_string_append(x_11, x_12);
lean_dec(x_12);
x_14 = l_Std_Range_forIn_x27_loop___at___Std_Time_TimeZone_convertTZifV1_spec__0___redArg___closed__1;
x_15 = lean_string_append(x_13, x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_10, 0);
lean_inc(x_17);
lean_dec(x_10);
x_18 = lean_array_push(x_4, x_17);
x_19 = lean_nat_add(x_5, x_7);
lean_dec(x_5);
x_4 = x_18;
x_5 = x_19;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Time_TimeZone_convertTZifV1_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Range_forIn_x27_loop___at___Std_Time_TimeZone_convertTZifV1_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at___Std_Time_TimeZone_convertTZifV1_spec__1___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cannot convert transition ", 26, 26);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Time_TimeZone_convertTZifV1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_nat_dec_lt(x_5, x_6);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Std_Time_TimeZone_convertTransition(x_1, x_5, x_2);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_array_push(x_4, x_11);
x_13 = lean_nat_add(x_5, x_7);
lean_dec(x_5);
x_4 = x_12;
x_5 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Time_TimeZone_convertTZifV1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Range_forIn_x27_loop___at___Std_Time_TimeZone_convertTZifV1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l_Std_Time_TimeZone_convertTZifV1___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_TimeZone_convertTZifV1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("empty transitions for ", 22, 22);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertTZifV1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint32_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get_uint32(x_3, 16);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Std_Time_TimeZone_convertTZifV1___closed__0;
x_8 = lean_uint32_to_nat(x_5);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_10, 2, x_9);
lean_inc(x_2);
x_11 = l_Std_Range_forIn_x27_loop___at___Std_Time_TimeZone_convertTZifV1_spec__0___redArg(x_1, x_2, x_10, x_7, x_6);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_array_get_size(x_4);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_17, 2, x_9);
x_18 = l_Std_Range_forIn_x27_loop___at___Std_Time_TimeZone_convertTZifV1_spec__1___redArg(x_15, x_1, x_17, x_7, x_6);
lean_dec(x_17);
lean_dec(x_15);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_2);
x_21 = l_Std_Time_TimeZone_convertLocalTimeType(x_6, x_1, x_2);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_20);
x_22 = l_Std_Time_TimeZone_convertTZifV1___closed__1;
x_23 = lean_string_append(x_22, x_2);
lean_dec(x_2);
lean_ctor_set_tag(x_18, 0);
lean_ctor_set(x_18, 0, x_23);
return x_18;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_2);
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_20);
lean_ctor_set(x_18, 0, x_25);
return x_18;
}
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_18, 0);
lean_inc(x_26);
lean_dec(x_18);
lean_inc(x_2);
x_27 = l_Std_Time_TimeZone_convertLocalTimeType(x_6, x_1, x_2);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_26);
x_28 = l_Std_Time_TimeZone_convertTZifV1___closed__1;
x_29 = lean_string_append(x_28, x_2);
lean_dec(x_2);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_2);
x_31 = lean_ctor_get(x_27, 0);
lean_inc(x_31);
lean_dec(x_27);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_26);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Time_TimeZone_convertTZifV1_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Range_forIn_x27_loop___at___Std_Time_TimeZone_convertTZifV1_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Time_TimeZone_convertTZifV1_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Range_forIn_x27_loop___at___Std_Time_TimeZone_convertTZifV1_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Time_TimeZone_convertTZifV1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Range_forIn_x27_loop___at___Std_Time_TimeZone_convertTZifV1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Time_TimeZone_convertTZifV1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Range_forIn_x27_loop___at___Std_Time_TimeZone_convertTZifV1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
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
l_Std_Range_forIn_x27_loop___at___Std_Time_TimeZone_convertTZifV1_spec__0___redArg___closed__0 = _init_l_Std_Range_forIn_x27_loop___at___Std_Time_TimeZone_convertTZifV1_spec__0___redArg___closed__0();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at___Std_Time_TimeZone_convertTZifV1_spec__0___redArg___closed__0);
l_Std_Range_forIn_x27_loop___at___Std_Time_TimeZone_convertTZifV1_spec__0___redArg___closed__1 = _init_l_Std_Range_forIn_x27_loop___at___Std_Time_TimeZone_convertTZifV1_spec__0___redArg___closed__1();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at___Std_Time_TimeZone_convertTZifV1_spec__0___redArg___closed__1);
l_Std_Range_forIn_x27_loop___at___Std_Time_TimeZone_convertTZifV1_spec__1___redArg___closed__0 = _init_l_Std_Range_forIn_x27_loop___at___Std_Time_TimeZone_convertTZifV1_spec__1___redArg___closed__0();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at___Std_Time_TimeZone_convertTZifV1_spec__1___redArg___closed__0);
l_Std_Time_TimeZone_convertTZifV1___closed__0 = _init_l_Std_Time_TimeZone_convertTZifV1___closed__0();
lean_mark_persistent(l_Std_Time_TimeZone_convertTZifV1___closed__0);
l_Std_Time_TimeZone_convertTZifV1___closed__1 = _init_l_Std_Time_TimeZone_convertTZifV1___closed__1();
lean_mark_persistent(l_Std_Time_TimeZone_convertTZifV1___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

// Lean compiler output
// Module: Std.Time.Zoned.Database.Windows
// Imports: public import Init.Data.SInt.Basic public import Std.Time.Zoned.Database.Basic
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_inst;
lean_object* lean_int64_to_int_sint(uint64_t);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Std_Time_Database_Windows_getZoneRules___closed__3;
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_inst___lam__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Time_Database_Windows_getZoneRules_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_inst___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_inst___lam__0(lean_object*, lean_object*);
static lean_object* l_Std_Time_Database_WindowsDb_inst___closed__2;
static lean_object* l_Std_Time_Database_WindowsDb_inst___closed__0;
static lean_object* l_Std_Time_Database_Windows_getZoneRules___closed__4;
static uint64_t l_Std_Time_Database_Windows_getZoneRules___closed__0;
lean_object* lean_nat_to_int(lean_object*);
uint64_t lean_int64_neg(uint64_t);
LEAN_EXPORT lean_object* l_Std_Time_Database_Windows_getZoneRules___closed__3___boxed__const__1;
static uint64_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Time_Database_Windows_getZoneRules_spec__1___closed__0;
uint8_t lean_int64_dec_le(uint64_t, uint64_t);
lean_object* lean_mk_io_user_error(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_inst___lam__1___boxed(lean_object*, lean_object*);
static uint64_t l_Std_Time_Database_Windows_getZoneRules___closed__1;
lean_object* lean_windows_get_next_transition(lean_object*, uint64_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_toCtorIdx(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Time_Database_Windows_getZoneRules_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_Windows_getNextTransition___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_Database_Windows_getZoneRules_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_Windows_0__Std_Time_Database_Windows_getZoneRules_toLocalTime___boxed(lean_object*);
static lean_object* l_Std_Time_Database_WindowsDb_inst___closed__1;
LEAN_EXPORT lean_object* l_Std_Time_Database_Windows_getLocalTimeZoneIdentifierAt___boxed(lean_object*, lean_object*);
static lean_object* l_Std_Time_Database_Windows_getZoneRules___closed__5;
uint64_t lean_int64_of_nat(lean_object*);
lean_object* lean_get_windows_local_timezone_id_at(uint64_t);
LEAN_EXPORT lean_object* l_Std_Time_Database_Windows_getZoneRules___boxed(lean_object*, lean_object*);
static lean_object* l_Std_Time_Database_Windows_getZoneRules___closed__2;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00Std_Time_Database_Windows_getZoneRules_spec__0_spec__0(lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_Windows_0__Std_Time_Database_Windows_getZoneRules_toLocalTime(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_default;
LEAN_EXPORT lean_object* l_Std_Time_Database_Windows_getZoneRules(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_Windows_getNextTransition___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_6 = lean_unbox(x_3);
x_7 = lean_windows_get_next_transition(x_1, x_5, x_6);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_Windows_getLocalTimeZoneIdentifierAt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_get_windows_local_timezone_id_at(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_Windows_0__Std_Time_Database_Windows_getZoneRules_toLocalTime(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_6 = 0;
x_7 = 1;
lean_inc_ref(x_3);
lean_inc_ref(x_4);
lean_inc(x_2);
x_8 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_4);
lean_ctor_set(x_8, 2, x_3);
lean_ctor_set_uint8(x_8, sizeof(void*)*3, x_5);
lean_ctor_set_uint8(x_8, sizeof(void*)*3 + 1, x_6);
lean_ctor_set_uint8(x_8, sizeof(void*)*3 + 2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_Windows_0__Std_Time_Database_Windows_getZoneRules_toLocalTime___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Std_Time_Zoned_Database_Windows_0__Std_Time_Database_Windows_getZoneRules_toLocalTime(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static uint64_t _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Time_Database_Windows_getZoneRules_spec__1___closed__0() {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = lean_cstr_to_nat("32503690800");
x_2 = lean_int64_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Time_Database_Windows_getZoneRules_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint64_t x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_6 = x_2;
} else {
 lean_dec_ref(x_2);
 x_6 = lean_box(0);
}
x_7 = 0;
x_8 = lean_unbox_uint64(x_4);
x_9 = lean_windows_get_next_transition(x_1, x_8, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 x_11 = x_9;
} else {
 lean_dec_ref(x_9);
 x_11 = lean_box(0);
}
if (lean_obj_tag(x_10) == 1)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint64_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint64_t x_23; uint64_t x_24; uint8_t x_25; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_unbox_uint64(x_4);
x_17 = lean_int64_to_int_sint(x_16);
x_18 = l___private_Std_Time_Zoned_Database_Windows_0__Std_Time_Database_Windows_getZoneRules_toLocalTime(x_15);
lean_dec(x_15);
lean_ctor_set(x_12, 1, x_18);
lean_ctor_set(x_12, 0, x_17);
x_19 = lean_array_push(x_5, x_12);
x_23 = lean_unbox_uint64(x_14);
x_24 = lean_unbox_uint64(x_4);
x_25 = lean_int64_dec_le(x_23, x_24);
if (x_25 == 0)
{
uint64_t x_26; uint64_t x_27; uint8_t x_28; 
x_26 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Time_Database_Windows_getZoneRules_spec__1___closed__0;
x_27 = lean_unbox_uint64(x_14);
x_28 = lean_int64_dec_le(x_26, x_27);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_4);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_14);
lean_ctor_set(x_29, 1, x_19);
x_2 = x_29;
goto _start;
}
else
{
lean_dec(x_14);
goto block_22;
}
}
else
{
lean_dec(x_14);
goto block_22;
}
block_22:
{
lean_object* x_20; lean_object* x_21; 
if (lean_is_scalar(x_6)) {
 x_20 = lean_alloc_ctor(0, 2, 0);
} else {
 x_20 = x_6;
}
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_19);
if (lean_is_scalar(x_11)) {
 x_21 = lean_alloc_ctor(0, 1, 0);
} else {
 x_21 = x_11;
}
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
else
{
lean_object* x_31; lean_object* x_32; uint64_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint64_t x_41; uint64_t x_42; uint8_t x_43; 
x_31 = lean_ctor_get(x_12, 0);
x_32 = lean_ctor_get(x_12, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_12);
x_33 = lean_unbox_uint64(x_4);
x_34 = lean_int64_to_int_sint(x_33);
x_35 = l___private_Std_Time_Zoned_Database_Windows_0__Std_Time_Database_Windows_getZoneRules_toLocalTime(x_32);
lean_dec(x_32);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_array_push(x_5, x_36);
x_41 = lean_unbox_uint64(x_31);
x_42 = lean_unbox_uint64(x_4);
x_43 = lean_int64_dec_le(x_41, x_42);
if (x_43 == 0)
{
uint64_t x_44; uint64_t x_45; uint8_t x_46; 
x_44 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Time_Database_Windows_getZoneRules_spec__1___closed__0;
x_45 = lean_unbox_uint64(x_31);
x_46 = lean_int64_dec_le(x_44, x_45);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_4);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_31);
lean_ctor_set(x_47, 1, x_37);
x_2 = x_47;
goto _start;
}
else
{
lean_dec(x_31);
goto block_40;
}
}
else
{
lean_dec(x_31);
goto block_40;
}
block_40:
{
lean_object* x_38; lean_object* x_39; 
if (lean_is_scalar(x_6)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_6;
}
lean_ctor_set(x_38, 0, x_4);
lean_ctor_set(x_38, 1, x_37);
if (lean_is_scalar(x_11)) {
 x_39 = lean_alloc_ctor(0, 1, 0);
} else {
 x_39 = x_11;
}
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_10);
if (lean_is_scalar(x_6)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_6;
}
lean_ctor_set(x_49, 0, x_4);
lean_ctor_set(x_49, 1, x_5);
if (lean_is_scalar(x_11)) {
 x_50 = lean_alloc_ctor(0, 1, 0);
} else {
 x_50 = x_11;
}
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
}
else
{
uint8_t x_51; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_51 = !lean_is_exclusive(x_9);
if (x_51 == 0)
{
return x_9;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_9, 0);
lean_inc(x_52);
lean_dec(x_9);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Time_Database_Windows_getZoneRules_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Time_Database_Windows_getZoneRules_spec__1(x_1, x_2);
lean_dec_ref(x_1);
return x_4;
}
}
static uint64_t _init_l_Std_Time_Database_Windows_getZoneRules___closed__0() {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = lean_unsigned_to_nat(2147483648u);
x_2 = lean_int64_of_nat(x_1);
return x_2;
}
}
static uint64_t _init_l_Std_Time_Database_Windows_getZoneRules___closed__1() {
_start:
{
uint64_t x_1; uint64_t x_2; 
x_1 = l_Std_Time_Database_Windows_getZoneRules___closed__0;
x_2 = lean_int64_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_Database_Windows_getZoneRules___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_Database_Windows_getZoneRules___closed__3___boxed__const__1() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = l_Std_Time_Database_Windows_getZoneRules___closed__1;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_Database_Windows_getZoneRules___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Time_Database_Windows_getZoneRules___closed__2;
x_2 = l_Std_Time_Database_Windows_getZoneRules___closed__3___boxed__const__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Time_Database_Windows_getZoneRules___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cannot find first transition in zone rules", 42, 42);
return x_1;
}
}
static lean_object* _init_l_Std_Time_Database_Windows_getZoneRules___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Time_Database_Windows_getZoneRules___closed__4;
x_2 = lean_mk_io_user_error(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_Windows_getZoneRules(lean_object* x_1) {
_start:
{
uint64_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = l_Std_Time_Database_Windows_getZoneRules___closed__1;
x_4 = 1;
x_5 = lean_windows_get_next_transition(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
if (lean_obj_tag(x_7) == 1)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_free_object(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = l_Std_Time_Database_Windows_getZoneRules___closed__3;
x_10 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Time_Database_Windows_getZoneRules_spec__1(x_1, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = !lean_is_exclusive(x_8);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_8, 1);
x_16 = lean_ctor_get(x_8, 0);
lean_dec(x_16);
x_17 = l___private_Std_Time_Zoned_Database_Windows_0__Std_Time_Database_Windows_getZoneRules_toLocalTime(x_15);
lean_dec(x_15);
lean_ctor_set(x_8, 1, x_13);
lean_ctor_set(x_8, 0, x_17);
lean_ctor_set(x_10, 0, x_8);
return x_10;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_dec(x_8);
x_19 = l___private_Std_Time_Zoned_Database_Windows_0__Std_Time_Database_Windows_getZoneRules_toLocalTime(x_18);
lean_dec(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_13);
lean_ctor_set(x_10, 0, x_20);
return x_10;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_10, 0);
lean_inc(x_21);
lean_dec(x_10);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_ctor_get(x_8, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_24 = x_8;
} else {
 lean_dec_ref(x_8);
 x_24 = lean_box(0);
}
x_25 = l___private_Std_Time_Zoned_Database_Windows_0__Std_Time_Database_Windows_getZoneRules_toLocalTime(x_23);
lean_dec(x_23);
if (lean_is_scalar(x_24)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_24;
}
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_22);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_8);
x_28 = !lean_is_exclusive(x_10);
if (x_28 == 0)
{
return x_10;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_10, 0);
lean_inc(x_29);
lean_dec(x_10);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; 
lean_dec(x_7);
x_31 = l_Std_Time_Database_Windows_getZoneRules___closed__5;
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_31);
return x_5;
}
}
else
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_5, 0);
lean_inc(x_32);
lean_dec(x_5);
if (lean_obj_tag(x_32) == 1)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_34 = l_Std_Time_Database_Windows_getZoneRules___closed__3;
x_35 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Time_Database_Windows_getZoneRules_spec__1(x_1, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 x_37 = x_35;
} else {
 lean_dec_ref(x_35);
 x_37 = lean_box(0);
}
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_40 = x_33;
} else {
 lean_dec_ref(x_33);
 x_40 = lean_box(0);
}
x_41 = l___private_Std_Time_Zoned_Database_Windows_0__Std_Time_Database_Windows_getZoneRules_toLocalTime(x_39);
lean_dec(x_39);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_38);
if (lean_is_scalar(x_37)) {
 x_43 = lean_alloc_ctor(0, 1, 0);
} else {
 x_43 = x_37;
}
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_33);
x_44 = lean_ctor_get(x_35, 0);
lean_inc(x_44);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 x_45 = x_35;
} else {
 lean_dec_ref(x_35);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(1, 1, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_44);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_32);
x_47 = l_Std_Time_Database_Windows_getZoneRules___closed__5;
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
}
else
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_5);
if (x_49 == 0)
{
return x_5;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_5, 0);
lean_inc(x_50);
lean_dec(x_5);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_Windows_getZoneRules___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_Database_Windows_getZoneRules(x_1);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00Std_Time_Database_Windows_getZoneRules_spec__0_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_Database_Windows_getZoneRules_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_nat_to_int(x_1);
x_3 = l_Rat_ofInt(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_toCtorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
static lean_object* _init_l_Std_Time_Database_WindowsDb_default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_inst___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_Database_Windows_getZoneRules(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_inst___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_Database_WindowsDb_inst___lam__0(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_inst___lam__1(lean_object* x_1) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = l_Std_Time_Database_Windows_getZoneRules___closed__1;
x_4 = lean_get_windows_local_timezone_id_at(x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = l_Std_Time_Database_Windows_getZoneRules(x_5);
lean_dec(x_5);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_inst___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_Database_WindowsDb_inst___lam__1(x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Time_Database_WindowsDb_inst___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Time_Database_WindowsDb_inst___lam__0___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Time_Database_WindowsDb_inst___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Time_Database_WindowsDb_inst___lam__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Time_Database_WindowsDb_inst___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Time_Database_WindowsDb_inst___closed__1;
x_2 = l_Std_Time_Database_WindowsDb_inst___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Time_Database_WindowsDb_inst() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Time_Database_WindowsDb_inst___closed__2;
return x_1;
}
}
lean_object* initialize_Init_Data_SInt_Basic(uint8_t builtin);
lean_object* initialize_Std_Time_Zoned_Database_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_Zoned_Database_Windows(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_SInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Zoned_Database_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Time_Database_Windows_getZoneRules_spec__1___closed__0 = _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Time_Database_Windows_getZoneRules_spec__1___closed__0();
l_Std_Time_Database_Windows_getZoneRules___closed__0 = _init_l_Std_Time_Database_Windows_getZoneRules___closed__0();
l_Std_Time_Database_Windows_getZoneRules___closed__1 = _init_l_Std_Time_Database_Windows_getZoneRules___closed__1();
l_Std_Time_Database_Windows_getZoneRules___closed__2 = _init_l_Std_Time_Database_Windows_getZoneRules___closed__2();
lean_mark_persistent(l_Std_Time_Database_Windows_getZoneRules___closed__2);
l_Std_Time_Database_Windows_getZoneRules___closed__3___boxed__const__1 = _init_l_Std_Time_Database_Windows_getZoneRules___closed__3___boxed__const__1();
lean_mark_persistent(l_Std_Time_Database_Windows_getZoneRules___closed__3___boxed__const__1);
l_Std_Time_Database_Windows_getZoneRules___closed__3 = _init_l_Std_Time_Database_Windows_getZoneRules___closed__3();
lean_mark_persistent(l_Std_Time_Database_Windows_getZoneRules___closed__3);
l_Std_Time_Database_Windows_getZoneRules___closed__4 = _init_l_Std_Time_Database_Windows_getZoneRules___closed__4();
lean_mark_persistent(l_Std_Time_Database_Windows_getZoneRules___closed__4);
l_Std_Time_Database_Windows_getZoneRules___closed__5 = _init_l_Std_Time_Database_Windows_getZoneRules___closed__5();
lean_mark_persistent(l_Std_Time_Database_Windows_getZoneRules___closed__5);
l_Std_Time_Database_WindowsDb_default = _init_l_Std_Time_Database_WindowsDb_default();
lean_mark_persistent(l_Std_Time_Database_WindowsDb_default);
l_Std_Time_Database_WindowsDb_inst___closed__0 = _init_l_Std_Time_Database_WindowsDb_inst___closed__0();
lean_mark_persistent(l_Std_Time_Database_WindowsDb_inst___closed__0);
l_Std_Time_Database_WindowsDb_inst___closed__1 = _init_l_Std_Time_Database_WindowsDb_inst___closed__1();
lean_mark_persistent(l_Std_Time_Database_WindowsDb_inst___closed__1);
l_Std_Time_Database_WindowsDb_inst___closed__2 = _init_l_Std_Time_Database_WindowsDb_inst___closed__2();
lean_mark_persistent(l_Std_Time_Database_WindowsDb_inst___closed__2);
l_Std_Time_Database_WindowsDb_inst = _init_l_Std_Time_Database_WindowsDb_inst();
lean_mark_persistent(l_Std_Time_Database_WindowsDb_inst);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

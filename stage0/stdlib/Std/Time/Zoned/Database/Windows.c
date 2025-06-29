// Lean compiler output
// Module: Std.Time.Zoned.Database.Windows
// Imports: Init.Data.SInt.Basic Std.Time.DateTime Std.Time.Zoned.TimeZone Std.Time.Zoned.ZoneRules Std.Time.Zoned.Database.Basic
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
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_noConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_inst;
lean_object* lean_int64_to_int_sint(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Std_Time_Database_Windows_getZoneRules_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Std_Time_Database_Windows_getZoneRules_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Std_Time_Database_Windows_getZoneRules___closed__3;
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_inst___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_inst___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_inst___lam__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Time_Database_Windows_getZoneRules___closed__4;
LEAN_EXPORT lean_object* l_Std_Time_Database_Windows_getZoneRules___closed__5___boxed__const__1;
static uint64_t l_Std_Time_Database_Windows_getZoneRules___closed__0;
uint64_t lean_int64_neg(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Std_Time_Database_Windows_getZoneRules_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_Windows_getZoneRules_toLocalTime(lean_object*);
uint8_t lean_int64_dec_le(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_noConfusion___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_inst___lam__1___boxed(lean_object*, lean_object*);
static uint64_t l_Std_Time_Database_Windows_getZoneRules___closed__1;
lean_object* lean_windows_get_next_transition(lean_object*, uint64_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_toCtorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_Windows_getNextTransition___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_noConfusion___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Std_Time_Database_Windows_getZoneRules_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_Windows_getLocalTimeZoneIdentifierAt___boxed(lean_object*, lean_object*);
static uint64_t l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Std_Time_Database_Windows_getZoneRules_spec__0_spec__0___closed__0;
static lean_object* l_Std_Time_Database_Windows_getZoneRules___closed__5;
uint64_t lean_int64_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_Windows_getZoneRules_toLocalTime___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_noConfusion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_toCtorIdx___boxed(lean_object*);
lean_object* lean_get_windows_local_timezone_id_at(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_Windows_getZoneRules___boxed(lean_object*, lean_object*);
static lean_object* l_Std_Time_Database_Windows_getZoneRules___closed__2;
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_default;
LEAN_EXPORT lean_object* l_Std_Time_Database_Windows_getZoneRules(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_Windows_getNextTransition___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = lean_windows_get_next_transition(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_Windows_getLocalTimeZoneIdentifierAt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_get_windows_local_timezone_id_at(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_Windows_getZoneRules_toLocalTime(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_6 = lean_box(0);
x_7 = lean_box(1);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
x_8 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_4);
lean_ctor_set(x_8, 2, x_3);
lean_ctor_set_uint8(x_8, sizeof(void*)*3, x_5);
x_9 = lean_unbox(x_6);
lean_ctor_set_uint8(x_8, sizeof(void*)*3 + 1, x_9);
x_10 = lean_unbox(x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*3 + 2, x_10);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_Windows_getZoneRules_toLocalTime___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_Database_Windows_getZoneRules_toLocalTime(x_1);
lean_dec(x_1);
return x_2;
}
}
static uint64_t _init_l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Std_Time_Database_Windows_getZoneRules_spec__0_spec__0___closed__0() {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = lean_cstr_to_nat("32503690800");
x_2 = lean_int64_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Std_Time_Database_Windows_getZoneRules_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; uint8_t x_9; lean_object* x_10; 
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
x_7 = lean_box(0);
x_8 = lean_unbox_uint64(x_4);
x_9 = lean_unbox(x_7);
x_10 = lean_windows_get_next_transition(x_1, x_8, x_9, x_3);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
if (lean_is_scalar(x_6)) {
 x_14 = lean_alloc_ctor(0, 2, 0);
} else {
 x_14 = x_6;
}
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_5);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
if (lean_is_scalar(x_6)) {
 x_16 = lean_alloc_ctor(0, 2, 0);
} else {
 x_16 = x_6;
}
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_5);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_11, 0);
lean_inc(x_18);
lean_dec(x_11);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_20 = x_10;
} else {
 lean_dec_ref(x_10);
 x_20 = lean_box(0);
}
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint64_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint64_t x_31; uint64_t x_32; uint8_t x_33; 
x_22 = lean_ctor_get(x_18, 0);
x_23 = lean_ctor_get(x_18, 1);
x_24 = lean_unbox_uint64(x_4);
x_25 = lean_int64_to_int_sint(x_24);
x_26 = l_Std_Time_Database_Windows_getZoneRules_toLocalTime(x_23);
lean_dec(x_23);
lean_ctor_set(x_18, 1, x_26);
lean_ctor_set(x_18, 0, x_25);
x_27 = lean_array_push(x_5, x_18);
x_31 = lean_unbox_uint64(x_22);
x_32 = lean_unbox_uint64(x_4);
x_33 = lean_int64_dec_le(x_31, x_32);
if (x_33 == 0)
{
uint64_t x_34; uint64_t x_35; uint8_t x_36; 
x_34 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Std_Time_Database_Windows_getZoneRules_spec__0_spec__0___closed__0;
x_35 = lean_unbox_uint64(x_22);
x_36 = lean_int64_dec_le(x_34, x_35);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_20);
lean_dec(x_6);
lean_dec(x_4);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_22);
lean_ctor_set(x_37, 1, x_27);
x_2 = x_37;
x_3 = x_19;
goto _start;
}
else
{
lean_dec(x_22);
goto block_30;
}
}
else
{
lean_dec(x_22);
goto block_30;
}
block_30:
{
lean_object* x_28; lean_object* x_29; 
if (lean_is_scalar(x_6)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_6;
}
lean_ctor_set(x_28, 0, x_4);
lean_ctor_set(x_28, 1, x_27);
if (lean_is_scalar(x_20)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_20;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_19);
return x_29;
}
}
else
{
lean_object* x_39; lean_object* x_40; uint64_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint64_t x_49; uint64_t x_50; uint8_t x_51; 
x_39 = lean_ctor_get(x_18, 0);
x_40 = lean_ctor_get(x_18, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_18);
x_41 = lean_unbox_uint64(x_4);
x_42 = lean_int64_to_int_sint(x_41);
x_43 = l_Std_Time_Database_Windows_getZoneRules_toLocalTime(x_40);
lean_dec(x_40);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_array_push(x_5, x_44);
x_49 = lean_unbox_uint64(x_39);
x_50 = lean_unbox_uint64(x_4);
x_51 = lean_int64_dec_le(x_49, x_50);
if (x_51 == 0)
{
uint64_t x_52; uint64_t x_53; uint8_t x_54; 
x_52 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Std_Time_Database_Windows_getZoneRules_spec__0_spec__0___closed__0;
x_53 = lean_unbox_uint64(x_39);
x_54 = lean_int64_dec_le(x_52, x_53);
if (x_54 == 0)
{
lean_object* x_55; 
lean_dec(x_20);
lean_dec(x_6);
lean_dec(x_4);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_39);
lean_ctor_set(x_55, 1, x_45);
x_2 = x_55;
x_3 = x_19;
goto _start;
}
else
{
lean_dec(x_39);
goto block_48;
}
}
else
{
lean_dec(x_39);
goto block_48;
}
block_48:
{
lean_object* x_46; lean_object* x_47; 
if (lean_is_scalar(x_6)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_6;
}
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_45);
if (lean_is_scalar(x_20)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_20;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_19);
return x_47;
}
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_57 = !lean_is_exclusive(x_10);
if (x_57 == 0)
{
return x_10;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_10, 0);
x_59 = lean_ctor_get(x_10, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_10);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Std_Time_Database_Windows_getZoneRules_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; uint8_t x_9; lean_object* x_10; 
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
x_7 = lean_box(0);
x_8 = lean_unbox_uint64(x_4);
x_9 = lean_unbox(x_7);
x_10 = lean_windows_get_next_transition(x_1, x_8, x_9, x_3);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
if (lean_is_scalar(x_6)) {
 x_14 = lean_alloc_ctor(0, 2, 0);
} else {
 x_14 = x_6;
}
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_5);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
if (lean_is_scalar(x_6)) {
 x_16 = lean_alloc_ctor(0, 2, 0);
} else {
 x_16 = x_6;
}
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_5);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_11, 0);
lean_inc(x_18);
lean_dec(x_11);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_20 = x_10;
} else {
 lean_dec_ref(x_10);
 x_20 = lean_box(0);
}
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint64_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint64_t x_31; uint64_t x_32; uint8_t x_33; 
x_22 = lean_ctor_get(x_18, 0);
x_23 = lean_ctor_get(x_18, 1);
x_24 = lean_unbox_uint64(x_4);
x_25 = lean_int64_to_int_sint(x_24);
x_26 = l_Std_Time_Database_Windows_getZoneRules_toLocalTime(x_23);
lean_dec(x_23);
lean_ctor_set(x_18, 1, x_26);
lean_ctor_set(x_18, 0, x_25);
x_27 = lean_array_push(x_5, x_18);
x_31 = lean_unbox_uint64(x_22);
x_32 = lean_unbox_uint64(x_4);
x_33 = lean_int64_dec_le(x_31, x_32);
if (x_33 == 0)
{
uint64_t x_34; uint64_t x_35; uint8_t x_36; 
x_34 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Std_Time_Database_Windows_getZoneRules_spec__0_spec__0___closed__0;
x_35 = lean_unbox_uint64(x_22);
x_36 = lean_int64_dec_le(x_34, x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_20);
lean_dec(x_6);
lean_dec(x_4);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_22);
lean_ctor_set(x_37, 1, x_27);
x_38 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Std_Time_Database_Windows_getZoneRules_spec__0_spec__0(x_1, x_37, x_19);
return x_38;
}
else
{
lean_dec(x_22);
goto block_30;
}
}
else
{
lean_dec(x_22);
goto block_30;
}
block_30:
{
lean_object* x_28; lean_object* x_29; 
if (lean_is_scalar(x_6)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_6;
}
lean_ctor_set(x_28, 0, x_4);
lean_ctor_set(x_28, 1, x_27);
if (lean_is_scalar(x_20)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_20;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_19);
return x_29;
}
}
else
{
lean_object* x_39; lean_object* x_40; uint64_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint64_t x_49; uint64_t x_50; uint8_t x_51; 
x_39 = lean_ctor_get(x_18, 0);
x_40 = lean_ctor_get(x_18, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_18);
x_41 = lean_unbox_uint64(x_4);
x_42 = lean_int64_to_int_sint(x_41);
x_43 = l_Std_Time_Database_Windows_getZoneRules_toLocalTime(x_40);
lean_dec(x_40);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_array_push(x_5, x_44);
x_49 = lean_unbox_uint64(x_39);
x_50 = lean_unbox_uint64(x_4);
x_51 = lean_int64_dec_le(x_49, x_50);
if (x_51 == 0)
{
uint64_t x_52; uint64_t x_53; uint8_t x_54; 
x_52 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Std_Time_Database_Windows_getZoneRules_spec__0_spec__0___closed__0;
x_53 = lean_unbox_uint64(x_39);
x_54 = lean_int64_dec_le(x_52, x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_20);
lean_dec(x_6);
lean_dec(x_4);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_39);
lean_ctor_set(x_55, 1, x_45);
x_56 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Std_Time_Database_Windows_getZoneRules_spec__0_spec__0(x_1, x_55, x_19);
return x_56;
}
else
{
lean_dec(x_39);
goto block_48;
}
}
else
{
lean_dec(x_39);
goto block_48;
}
block_48:
{
lean_object* x_46; lean_object* x_47; 
if (lean_is_scalar(x_6)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_6;
}
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_45);
if (lean_is_scalar(x_20)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_20;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_19);
return x_47;
}
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_57 = !lean_is_exclusive(x_10);
if (x_57 == 0)
{
return x_10;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_10, 0);
x_59 = lean_ctor_get(x_10, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_10);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
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
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cannot find first transition in zone rules", 42, 42);
return x_1;
}
}
static lean_object* _init_l_Std_Time_Database_Windows_getZoneRules___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Time_Database_Windows_getZoneRules___closed__2;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_Database_Windows_getZoneRules___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_Database_Windows_getZoneRules___closed__5___boxed__const__1() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = l_Std_Time_Database_Windows_getZoneRules___closed__1;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_Database_Windows_getZoneRules___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Time_Database_Windows_getZoneRules___closed__4;
x_2 = l_Std_Time_Database_Windows_getZoneRules___closed__5___boxed__const__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_Windows_getZoneRules(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_3 = l_Std_Time_Database_Windows_getZoneRules___closed__1;
x_4 = lean_box(1);
x_5 = lean_unbox(x_4);
x_6 = lean_windows_get_next_transition(x_1, x_3, x_5, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 0);
lean_dec(x_9);
x_10 = l_Std_Time_Database_Windows_getZoneRules___closed__3;
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_10);
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec(x_6);
x_12 = l_Std_Time_Database_Windows_getZoneRules___closed__3;
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_6, 1);
lean_inc(x_14);
lean_dec(x_6);
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
lean_dec(x_7);
x_16 = l_Std_Time_Database_Windows_getZoneRules___closed__5;
x_17 = l_Lean_Loop_forIn_loop___at___Std_Time_Database_Windows_getZoneRules_spec__0(x_1, x_16, x_14);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_15, 1);
x_23 = lean_ctor_get(x_15, 0);
lean_dec(x_23);
x_24 = l_Std_Time_Database_Windows_getZoneRules_toLocalTime(x_22);
lean_dec(x_22);
lean_ctor_set(x_15, 1, x_20);
lean_ctor_set(x_15, 0, x_24);
lean_ctor_set(x_17, 0, x_15);
return x_17;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
lean_dec(x_15);
x_26 = l_Std_Time_Database_Windows_getZoneRules_toLocalTime(x_25);
lean_dec(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_20);
lean_ctor_set(x_17, 0, x_27);
return x_17;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_28 = lean_ctor_get(x_17, 0);
x_29 = lean_ctor_get(x_17, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_17);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_15, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_32 = x_15;
} else {
 lean_dec_ref(x_15);
 x_32 = lean_box(0);
}
x_33 = l_Std_Time_Database_Windows_getZoneRules_toLocalTime(x_31);
lean_dec(x_31);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_30);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_29);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_15);
x_36 = !lean_is_exclusive(x_17);
if (x_36 == 0)
{
return x_17;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_17, 0);
x_38 = lean_ctor_get(x_17, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_17);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_6);
if (x_40 == 0)
{
return x_6;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_6, 0);
x_42 = lean_ctor_get(x_6, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_6);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Std_Time_Database_Windows_getZoneRules_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Std_Time_Database_Windows_getZoneRules_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Std_Time_Database_Windows_getZoneRules_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Loop_forIn_loop___at___Std_Time_Database_Windows_getZoneRules_spec__0(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_Windows_getZoneRules___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_Database_Windows_getZoneRules(x_1, x_2);
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_Database_WindowsDb_toCtorIdx(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_noConfusion___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_noConfusion(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_inc(x_5);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_noConfusion___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_Database_WindowsDb_noConfusion___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_noConfusion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Time_Database_WindowsDb_noConfusion(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
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
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_inst___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_Database_Windows_getZoneRules(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_inst___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = l_Std_Time_Database_Windows_getZoneRules___closed__1;
x_4 = lean_get_windows_local_timezone_id_at(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Std_Time_Database_Windows_getZoneRules(x_5, x_6);
lean_dec(x_5);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_4);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
}
static lean_object* _init_l_Std_Time_Database_WindowsDb_inst() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_alloc_closure((void*)(l_Std_Time_Database_WindowsDb_inst___lam__0___boxed), 3, 0);
x_2 = lean_alloc_closure((void*)(l_Std_Time_Database_WindowsDb_inst___lam__1___boxed), 2, 0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_inst___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_Database_WindowsDb_inst___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_inst___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_Database_WindowsDb_inst___lam__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init_Data_SInt_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Time_DateTime(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Time_Zoned_TimeZone(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Time_Zoned_ZoneRules(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Time_Zoned_Database_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_Zoned_Database_Windows(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_SInt_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_DateTime(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Zoned_TimeZone(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Zoned_ZoneRules(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Zoned_Database_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Std_Time_Database_Windows_getZoneRules_spec__0_spec__0___closed__0 = _init_l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Std_Time_Database_Windows_getZoneRules_spec__0_spec__0___closed__0();
l_Std_Time_Database_Windows_getZoneRules___closed__0 = _init_l_Std_Time_Database_Windows_getZoneRules___closed__0();
l_Std_Time_Database_Windows_getZoneRules___closed__1 = _init_l_Std_Time_Database_Windows_getZoneRules___closed__1();
l_Std_Time_Database_Windows_getZoneRules___closed__2 = _init_l_Std_Time_Database_Windows_getZoneRules___closed__2();
lean_mark_persistent(l_Std_Time_Database_Windows_getZoneRules___closed__2);
l_Std_Time_Database_Windows_getZoneRules___closed__3 = _init_l_Std_Time_Database_Windows_getZoneRules___closed__3();
lean_mark_persistent(l_Std_Time_Database_Windows_getZoneRules___closed__3);
l_Std_Time_Database_Windows_getZoneRules___closed__4 = _init_l_Std_Time_Database_Windows_getZoneRules___closed__4();
lean_mark_persistent(l_Std_Time_Database_Windows_getZoneRules___closed__4);
l_Std_Time_Database_Windows_getZoneRules___closed__5___boxed__const__1 = _init_l_Std_Time_Database_Windows_getZoneRules___closed__5___boxed__const__1();
lean_mark_persistent(l_Std_Time_Database_Windows_getZoneRules___closed__5___boxed__const__1);
l_Std_Time_Database_Windows_getZoneRules___closed__5 = _init_l_Std_Time_Database_Windows_getZoneRules___closed__5();
lean_mark_persistent(l_Std_Time_Database_Windows_getZoneRules___closed__5);
l_Std_Time_Database_WindowsDb_default = _init_l_Std_Time_Database_WindowsDb_default();
lean_mark_persistent(l_Std_Time_Database_WindowsDb_default);
l_Std_Time_Database_WindowsDb_inst = _init_l_Std_Time_Database_WindowsDb_inst();
lean_mark_persistent(l_Std_Time_Database_WindowsDb_inst);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

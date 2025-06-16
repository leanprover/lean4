// Lean compiler output
// Module: Std.Time.Zoned.Database
// Imports: Std.Time.Zoned.ZonedDateTime Std.Time.Zoned.Database.Basic Std.Time.Zoned.Database.TZdb Std.Time.Zoned.Database.Windows Init.System.Platform
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
LEAN_EXPORT lean_object* l_Std_Time_Database_defaultGetZoneRules___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__9;
static uint64_t l_Std_Time_Database_defaultGetLocalZoneRules___closed__2;
lean_object* lean_io_getenv(lean_object*, lean_object*);
lean_object* l_Std_Time_Database_TZdb_localRules(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_defaultGetLocalZoneRules(lean_object*);
static uint64_t l_Std_Time_Database_defaultGetLocalZoneRules___closed__3;
static lean_object* l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__5;
lean_object* l_System_FilePath_pathExists(lean_object*, lean_object*);
static lean_object* l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__8;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Std_Time_Database_defaultGetZoneRules___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_int64_neg(uint64_t);
static lean_object* l_Std_Time_Database_defaultGetLocalZoneRules___closed__4;
static lean_object* l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__7;
LEAN_EXPORT lean_object* l_Std_Time_Database_defaultGetLocalZoneRules___closed__4___boxed__const__1;
static size_t l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__11;
static lean_object* l_Std_Time_Database_defaultGetZoneRules___closed__1;
static lean_object* l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__10;
static lean_object* l_Std_Time_Database_defaultGetLocalZoneRules___closed__5;
static lean_object* l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__3;
lean_object* l_Std_Time_Database_Windows_getLocalTimeZoneIdentifierAt___boxed(lean_object*, lean_object*);
static lean_object* l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__6;
uint64_t lean_int64_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_defaultGetZoneRules___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_defaultGetZoneRules___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Time_Database_defaultGetZoneRules___lambda__1___closed__1;
lean_object* l_Bind_bindLeft___at_Std_Time_Database_WindowsDb_inst___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Std_Time_Database_defaultGetZoneRules___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Std_Time_Database_Windows_getZoneRules___boxed(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Std_Time_Database_TZdb_readRulesFromDisk(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__4;
static lean_object* l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__2;
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Std_Time_Database_defaultGetZoneRules___lambda__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_defaultGetZoneRules(lean_object*, lean_object*);
extern uint8_t l_System_Platform_isWindows;
static lean_object* l_Std_Time_Database_defaultGetLocalZoneRules___closed__1;
lean_object* l_Std_Time_Database_Windows_getZoneRules(lean_object*, lean_object*);
static lean_object* l_Std_Time_Database_defaultGetZoneRules___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Std_Time_Database_defaultGetZoneRules___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_7, x_6);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_8);
x_12 = lean_array_uget(x_5, x_7);
x_13 = l_System_FilePath_pathExists(x_12, x_9);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; size_t x_17; size_t x_18; 
lean_dec(x_12);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = 1;
x_18 = lean_usize_add(x_7, x_17);
lean_inc(x_4);
{
size_t _tmp_6 = x_18;
lean_object* _tmp_7 = x_4;
lean_object* _tmp_8 = x_16;
x_7 = _tmp_6;
x_8 = _tmp_7;
x_9 = _tmp_8;
}
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_4);
x_20 = !lean_is_exclusive(x_13);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_13, 1);
x_22 = lean_ctor_get(x_13, 0);
lean_dec(x_22);
x_23 = l_Std_Time_Database_TZdb_readRulesFromDisk(x_12, x_1, x_21);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_box(0);
lean_ctor_set(x_13, 1, x_27);
lean_ctor_set(x_13, 0, x_26);
lean_ctor_set(x_23, 0, x_13);
return x_23;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_23, 0);
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_23);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_28);
x_31 = lean_box(0);
lean_ctor_set(x_13, 1, x_31);
lean_ctor_set(x_13, 0, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_13);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_free_object(x_13);
x_33 = !lean_is_exclusive(x_23);
if (x_33 == 0)
{
return x_23;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_23, 0);
x_35 = lean_ctor_get(x_23, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_23);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_13, 1);
lean_inc(x_37);
lean_dec(x_13);
x_38 = l_Std_Time_Database_TZdb_readRulesFromDisk(x_12, x_1, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
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
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_39);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
if (lean_is_scalar(x_41)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_41;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_40);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_38, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_38, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_48 = x_38;
} else {
 lean_dec_ref(x_38);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(1, 2, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
}
}
}
}
static lean_object* _init_l_Std_Time_Database_defaultGetZoneRules___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cannot find ", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Std_Time_Database_defaultGetZoneRules___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" in the local timezone database", 31, 31);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_defaultGetZoneRules___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = l_Std_Time_Database_defaultGetZoneRules___lambda__1___closed__1;
x_5 = lean_string_append(x_4, x_1);
x_6 = l_Std_Time_Database_defaultGetZoneRules___lambda__1___closed__2;
x_7 = lean_string_append(x_5, x_6);
x_8 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
}
static lean_object* _init_l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("/usr/share/lib/zoneinfo", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("/etc/zoneinfo", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__3;
x_2 = l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("/share/zoneinfo", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__5;
x_2 = l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("/usr/share/zoneinfo", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__7;
x_2 = l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__6;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__8;
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static size_t _init_l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__11() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__9;
x_2 = lean_array_size(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_defaultGetZoneRules___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; size_t x_5; lean_object* x_6; lean_object* x_7; size_t x_8; lean_object* x_9; 
x_4 = lean_box(0);
x_5 = 0;
x_6 = l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__9;
x_7 = l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__10;
x_8 = l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__11;
lean_inc(x_1);
x_9 = l_Array_forIn_x27Unsafe_loop___at_Std_Time_Database_defaultGetZoneRules___spec__1(x_1, x_4, x_6, x_7, x_6, x_8, x_5, x_7, x_3);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_box(0);
x_14 = l_Std_Time_Database_defaultGetZoneRules___lambda__1(x_1, x_13, x_12);
lean_dec(x_1);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_9, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
lean_dec(x_11);
lean_ctor_set(x_9, 0, x_17);
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_dec(x_9);
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
else
{
uint8_t x_21; 
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_9);
if (x_21 == 0)
{
return x_9;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_9, 0);
x_23 = lean_ctor_get(x_9, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_9);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
static lean_object* _init_l_Std_Time_Database_defaultGetZoneRules___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("TZDIR", 5, 5);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_defaultGetZoneRules(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_System_Platform_isWindows;
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Std_Time_Database_defaultGetZoneRules___closed__1;
x_5 = lean_io_getenv(x_4, x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_box(0);
x_9 = l_Std_Time_Database_defaultGetZoneRules___lambda__2(x_1, x_8, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
lean_dec(x_6);
x_12 = l_Std_Time_Database_TZdb_readRulesFromDisk(x_11, x_1, x_10);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
else
{
lean_object* x_21; 
x_21 = l_Std_Time_Database_Windows_getZoneRules(x_1, x_2);
lean_dec(x_1);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Std_Time_Database_defaultGetZoneRules___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_11 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_12 = l_Array_forIn_x27Unsafe_loop___at_Std_Time_Database_defaultGetZoneRules___spec__1(x_1, x_2, x_3, x_4, x_5, x_10, x_11, x_8, x_9);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_defaultGetZoneRules___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_Database_defaultGetZoneRules___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_defaultGetZoneRules___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_Database_defaultGetZoneRules___lambda__2(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Std_Time_Database_defaultGetLocalZoneRules___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("/etc/localtime", 14, 14);
return x_1;
}
}
static uint64_t _init_l_Std_Time_Database_defaultGetLocalZoneRules___closed__2() {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = lean_unsigned_to_nat(2147483648u);
x_2 = lean_int64_of_nat(x_1);
return x_2;
}
}
static uint64_t _init_l_Std_Time_Database_defaultGetLocalZoneRules___closed__3() {
_start:
{
uint64_t x_1; uint64_t x_2; 
x_1 = l_Std_Time_Database_defaultGetLocalZoneRules___closed__2;
x_2 = lean_int64_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_Database_defaultGetLocalZoneRules___closed__4___boxed__const__1() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = l_Std_Time_Database_defaultGetLocalZoneRules___closed__3;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_Database_defaultGetLocalZoneRules___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Time_Database_defaultGetLocalZoneRules___closed__4___boxed__const__1;
x_2 = lean_alloc_closure((void*)(l_Std_Time_Database_Windows_getLocalTimeZoneIdentifierAt___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_Database_defaultGetLocalZoneRules___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Time_Database_Windows_getZoneRules___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_defaultGetLocalZoneRules(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_System_Platform_isWindows;
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Std_Time_Database_defaultGetLocalZoneRules___closed__1;
x_4 = l_Std_Time_Database_TZdb_localRules(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Std_Time_Database_defaultGetLocalZoneRules___closed__5;
x_6 = l_Std_Time_Database_defaultGetLocalZoneRules___closed__4;
x_7 = l_Bind_bindLeft___at_Std_Time_Database_WindowsDb_inst___spec__1(x_5, x_6, x_1);
return x_7;
}
}
}
lean_object* initialize_Std_Time_Zoned_ZonedDateTime(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Time_Zoned_Database_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Time_Zoned_Database_TZdb(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Time_Zoned_Database_Windows(uint8_t builtin, lean_object*);
lean_object* initialize_Init_System_Platform(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_Zoned_Database(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time_Zoned_ZonedDateTime(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Zoned_Database_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Zoned_Database_TZdb(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Zoned_Database_Windows(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_Platform(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Time_Database_defaultGetZoneRules___lambda__1___closed__1 = _init_l_Std_Time_Database_defaultGetZoneRules___lambda__1___closed__1();
lean_mark_persistent(l_Std_Time_Database_defaultGetZoneRules___lambda__1___closed__1);
l_Std_Time_Database_defaultGetZoneRules___lambda__1___closed__2 = _init_l_Std_Time_Database_defaultGetZoneRules___lambda__1___closed__2();
lean_mark_persistent(l_Std_Time_Database_defaultGetZoneRules___lambda__1___closed__2);
l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__1 = _init_l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__1();
lean_mark_persistent(l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__1);
l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__2 = _init_l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__2();
lean_mark_persistent(l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__2);
l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__3 = _init_l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__3();
lean_mark_persistent(l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__3);
l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__4 = _init_l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__4();
lean_mark_persistent(l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__4);
l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__5 = _init_l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__5();
lean_mark_persistent(l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__5);
l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__6 = _init_l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__6();
lean_mark_persistent(l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__6);
l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__7 = _init_l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__7();
lean_mark_persistent(l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__7);
l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__8 = _init_l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__8();
lean_mark_persistent(l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__8);
l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__9 = _init_l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__9();
lean_mark_persistent(l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__9);
l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__10 = _init_l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__10();
lean_mark_persistent(l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__10);
l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__11 = _init_l_Std_Time_Database_defaultGetZoneRules___lambda__2___closed__11();
l_Std_Time_Database_defaultGetZoneRules___closed__1 = _init_l_Std_Time_Database_defaultGetZoneRules___closed__1();
lean_mark_persistent(l_Std_Time_Database_defaultGetZoneRules___closed__1);
l_Std_Time_Database_defaultGetLocalZoneRules___closed__1 = _init_l_Std_Time_Database_defaultGetLocalZoneRules___closed__1();
lean_mark_persistent(l_Std_Time_Database_defaultGetLocalZoneRules___closed__1);
l_Std_Time_Database_defaultGetLocalZoneRules___closed__2 = _init_l_Std_Time_Database_defaultGetLocalZoneRules___closed__2();
l_Std_Time_Database_defaultGetLocalZoneRules___closed__3 = _init_l_Std_Time_Database_defaultGetLocalZoneRules___closed__3();
l_Std_Time_Database_defaultGetLocalZoneRules___closed__4___boxed__const__1 = _init_l_Std_Time_Database_defaultGetLocalZoneRules___closed__4___boxed__const__1();
lean_mark_persistent(l_Std_Time_Database_defaultGetLocalZoneRules___closed__4___boxed__const__1);
l_Std_Time_Database_defaultGetLocalZoneRules___closed__4 = _init_l_Std_Time_Database_defaultGetLocalZoneRules___closed__4();
lean_mark_persistent(l_Std_Time_Database_defaultGetLocalZoneRules___closed__4);
l_Std_Time_Database_defaultGetLocalZoneRules___closed__5 = _init_l_Std_Time_Database_defaultGetLocalZoneRules___closed__5();
lean_mark_persistent(l_Std_Time_Database_defaultGetLocalZoneRules___closed__5);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

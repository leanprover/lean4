// Lean compiler output
// Module: Std.Time.Zoned.Database
// Imports: public import Std.Time.Zoned.ZonedDateTime public import Std.Time.Zoned.Database.Basic public import Std.Time.Zoned.Database.TZdb public import Std.Time.Zoned.Database.Windows
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
LEAN_EXPORT lean_object* l_Std_Time_Database_defaultGetZoneRules___boxed(lean_object*, lean_object*);
static lean_object* l_Std_Time_Database_defaultGetZoneRules___closed__3;
static lean_object* l_Std_Time_Database_defaultGetZoneRules___closed__8;
LEAN_EXPORT lean_object* l_Std_Time_Database_defaultGetLocalZoneRules___boxed(lean_object*);
static lean_object* l_Std_Time_Database_defaultGetLocalZoneRules___closed__0;
lean_object* lean_array_push(lean_object*, lean_object*);
static uint64_t l_Std_Time_Database_defaultGetLocalZoneRules___closed__2;
static lean_object* l_Std_Time_Database_defaultGetZoneRules___closed__12;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_defaultGetZoneRules_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_io_getenv(lean_object*);
lean_object* l_Std_Time_Database_TZdb_localRules(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_defaultGetLocalZoneRules();
static lean_object* l_Std_Time_Database_defaultGetZoneRules___closed__13;
static lean_object* l_Std_Time_Database_defaultGetZoneRules___closed__10;
uint8_t l_System_FilePath_pathExists(lean_object*);
static lean_object* l_Std_Time_Database_defaultGetZoneRules___closed__4;
uint64_t lean_int64_neg(uint64_t);
static lean_object* l_Std_Time_Database_defaultGetZoneRules___closed__1;
static lean_object* l_Std_Time_Database_defaultGetZoneRules___closed__5;
lean_object* lean_mk_io_user_error(lean_object*);
static lean_object* l_Std_Time_Database_defaultGetZoneRules___closed__0;
static size_t l_Std_Time_Database_defaultGetZoneRules___closed__11;
uint64_t lean_int64_of_nat(lean_object*);
static lean_object* l_Std_Time_Database_defaultGetZoneRules___closed__9;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_defaultGetZoneRules_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_windows_local_timezone_id_at(uint64_t);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Std_Time_Database_defaultGetZoneRules___closed__2;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Std_Time_Database_TZdb_readRulesFromDisk(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Std_Time_Database_defaultGetZoneRules___closed__7;
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Std_Time_Database_defaultGetZoneRules___closed__6;
LEAN_EXPORT lean_object* l_Std_Time_Database_defaultGetZoneRules(lean_object*);
extern uint8_t l_System_Platform_isWindows;
static uint64_t l_Std_Time_Database_defaultGetLocalZoneRules___closed__1;
lean_object* l_Std_Time_Database_Windows_getZoneRules(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_defaultGetZoneRules_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_6, x_5);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_7);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
lean_dec_ref(x_7);
x_11 = lean_array_uget(x_4, x_6);
x_12 = l_System_FilePath_pathExists(x_11);
if (x_12 == 0)
{
size_t x_13; size_t x_14; 
lean_dec(x_11);
x_13 = 1;
x_14 = lean_usize_add(x_6, x_13);
lean_inc_ref(x_1);
{
size_t _tmp_5 = x_14;
lean_object* _tmp_6 = x_1;
x_6 = _tmp_5;
x_7 = _tmp_6;
}
goto _start;
}
else
{
lean_object* x_16; 
lean_dec_ref(x_1);
x_16 = l_Std_Time_Database_TZdb_readRulesFromDisk(x_11, x_2);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_3);
lean_ctor_set(x_16, 0, x_20);
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_16, 0);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_3);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_16);
if (x_25 == 0)
{
return x_16;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_16, 0);
lean_inc(x_26);
lean_dec(x_16);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_defaultGetZoneRules_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_11 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_defaultGetZoneRules_spec__0(x_1, x_2, x_3, x_4, x_9, x_10, x_7);
lean_dec_ref(x_4);
return x_11;
}
}
static lean_object* _init_l_Std_Time_Database_defaultGetZoneRules___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("TZDIR", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Std_Time_Database_defaultGetZoneRules___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("/usr/share/zoneinfo", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Std_Time_Database_defaultGetZoneRules___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("/share/zoneinfo", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Std_Time_Database_defaultGetZoneRules___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("/etc/zoneinfo", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Std_Time_Database_defaultGetZoneRules___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("/usr/share/lib/zoneinfo", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Std_Time_Database_defaultGetZoneRules___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_Database_defaultGetZoneRules___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Time_Database_defaultGetZoneRules___closed__1;
x_2 = l_Std_Time_Database_defaultGetZoneRules___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Time_Database_defaultGetZoneRules___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Time_Database_defaultGetZoneRules___closed__2;
x_2 = l_Std_Time_Database_defaultGetZoneRules___closed__6;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Time_Database_defaultGetZoneRules___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Time_Database_defaultGetZoneRules___closed__3;
x_2 = l_Std_Time_Database_defaultGetZoneRules___closed__7;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Time_Database_defaultGetZoneRules___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Time_Database_defaultGetZoneRules___closed__4;
x_2 = l_Std_Time_Database_defaultGetZoneRules___closed__8;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Time_Database_defaultGetZoneRules___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static size_t _init_l_Std_Time_Database_defaultGetZoneRules___closed__11() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = l_Std_Time_Database_defaultGetZoneRules___closed__9;
x_2 = lean_array_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_Database_defaultGetZoneRules___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cannot find ", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Std_Time_Database_defaultGetZoneRules___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" in the local timezone database", 31, 31);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_defaultGetZoneRules(lean_object* x_1) {
_start:
{
uint8_t x_3; 
x_3 = l_System_Platform_isWindows;
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Std_Time_Database_defaultGetZoneRules___closed__0;
x_5 = lean_io_getenv(x_4);
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = l_Std_Time_Database_TZdb_readRulesFromDisk(x_6, x_1);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
lean_dec(x_5);
x_8 = l_Std_Time_Database_defaultGetZoneRules___closed__9;
x_9 = lean_box(0);
x_10 = l_Std_Time_Database_defaultGetZoneRules___closed__10;
x_11 = l_Std_Time_Database_defaultGetZoneRules___closed__11;
x_12 = 0;
lean_inc_ref(x_1);
x_13 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_defaultGetZoneRules_spec__0(x_10, x_1, x_9, x_8, x_11, x_12, x_10);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = l_Std_Time_Database_defaultGetZoneRules___closed__12;
x_18 = lean_string_append(x_17, x_1);
lean_dec_ref(x_1);
x_19 = l_Std_Time_Database_defaultGetZoneRules___closed__13;
x_20 = lean_string_append(x_18, x_19);
x_21 = lean_mk_io_user_error(x_20);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_21);
return x_13;
}
else
{
lean_object* x_22; 
lean_dec_ref(x_1);
x_22 = lean_ctor_get(x_16, 0);
lean_inc(x_22);
lean_dec_ref(x_16);
lean_ctor_set(x_13, 0, x_22);
return x_13;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_13, 0);
lean_inc(x_23);
lean_dec(x_13);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = l_Std_Time_Database_defaultGetZoneRules___closed__12;
x_26 = lean_string_append(x_25, x_1);
lean_dec_ref(x_1);
x_27 = l_Std_Time_Database_defaultGetZoneRules___closed__13;
x_28 = lean_string_append(x_26, x_27);
x_29 = lean_mk_io_user_error(x_28);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec_ref(x_1);
x_31 = lean_ctor_get(x_24, 0);
lean_inc(x_31);
lean_dec_ref(x_24);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec_ref(x_1);
x_33 = !lean_is_exclusive(x_13);
if (x_33 == 0)
{
return x_13;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_13, 0);
lean_inc(x_34);
lean_dec(x_13);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
}
else
{
lean_object* x_36; 
x_36 = l_Std_Time_Database_Windows_getZoneRules(x_1);
lean_dec_ref(x_1);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_defaultGetZoneRules___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_Database_defaultGetZoneRules(x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Time_Database_defaultGetLocalZoneRules___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("/etc/localtime", 14, 14);
return x_1;
}
}
static uint64_t _init_l_Std_Time_Database_defaultGetLocalZoneRules___closed__1() {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = lean_unsigned_to_nat(2147483648u);
x_2 = lean_int64_of_nat(x_1);
return x_2;
}
}
static uint64_t _init_l_Std_Time_Database_defaultGetLocalZoneRules___closed__2() {
_start:
{
uint64_t x_1; uint64_t x_2; 
x_1 = l_Std_Time_Database_defaultGetLocalZoneRules___closed__1;
x_2 = lean_int64_neg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_defaultGetLocalZoneRules() {
_start:
{
uint8_t x_2; 
x_2 = l_System_Platform_isWindows;
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Std_Time_Database_defaultGetLocalZoneRules___closed__0;
x_4 = l_Std_Time_Database_TZdb_localRules(x_3);
return x_4;
}
else
{
uint64_t x_5; lean_object* x_6; 
x_5 = l_Std_Time_Database_defaultGetLocalZoneRules___closed__2;
x_6 = lean_get_windows_local_timezone_id_at(x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = l_Std_Time_Database_Windows_getZoneRules(x_7);
lean_dec(x_7);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_defaultGetLocalZoneRules___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_Database_defaultGetLocalZoneRules();
return x_2;
}
}
lean_object* initialize_Std_Time_Zoned_ZonedDateTime(uint8_t builtin);
lean_object* initialize_Std_Time_Zoned_Database_Basic(uint8_t builtin);
lean_object* initialize_Std_Time_Zoned_Database_TZdb(uint8_t builtin);
lean_object* initialize_Std_Time_Zoned_Database_Windows(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_Zoned_Database(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time_Zoned_ZonedDateTime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Zoned_Database_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Zoned_Database_TZdb(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Zoned_Database_Windows(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Time_Database_defaultGetZoneRules___closed__0 = _init_l_Std_Time_Database_defaultGetZoneRules___closed__0();
lean_mark_persistent(l_Std_Time_Database_defaultGetZoneRules___closed__0);
l_Std_Time_Database_defaultGetZoneRules___closed__1 = _init_l_Std_Time_Database_defaultGetZoneRules___closed__1();
lean_mark_persistent(l_Std_Time_Database_defaultGetZoneRules___closed__1);
l_Std_Time_Database_defaultGetZoneRules___closed__2 = _init_l_Std_Time_Database_defaultGetZoneRules___closed__2();
lean_mark_persistent(l_Std_Time_Database_defaultGetZoneRules___closed__2);
l_Std_Time_Database_defaultGetZoneRules___closed__3 = _init_l_Std_Time_Database_defaultGetZoneRules___closed__3();
lean_mark_persistent(l_Std_Time_Database_defaultGetZoneRules___closed__3);
l_Std_Time_Database_defaultGetZoneRules___closed__4 = _init_l_Std_Time_Database_defaultGetZoneRules___closed__4();
lean_mark_persistent(l_Std_Time_Database_defaultGetZoneRules___closed__4);
l_Std_Time_Database_defaultGetZoneRules___closed__5 = _init_l_Std_Time_Database_defaultGetZoneRules___closed__5();
lean_mark_persistent(l_Std_Time_Database_defaultGetZoneRules___closed__5);
l_Std_Time_Database_defaultGetZoneRules___closed__6 = _init_l_Std_Time_Database_defaultGetZoneRules___closed__6();
lean_mark_persistent(l_Std_Time_Database_defaultGetZoneRules___closed__6);
l_Std_Time_Database_defaultGetZoneRules___closed__7 = _init_l_Std_Time_Database_defaultGetZoneRules___closed__7();
lean_mark_persistent(l_Std_Time_Database_defaultGetZoneRules___closed__7);
l_Std_Time_Database_defaultGetZoneRules___closed__8 = _init_l_Std_Time_Database_defaultGetZoneRules___closed__8();
lean_mark_persistent(l_Std_Time_Database_defaultGetZoneRules___closed__8);
l_Std_Time_Database_defaultGetZoneRules___closed__9 = _init_l_Std_Time_Database_defaultGetZoneRules___closed__9();
lean_mark_persistent(l_Std_Time_Database_defaultGetZoneRules___closed__9);
l_Std_Time_Database_defaultGetZoneRules___closed__10 = _init_l_Std_Time_Database_defaultGetZoneRules___closed__10();
lean_mark_persistent(l_Std_Time_Database_defaultGetZoneRules___closed__10);
l_Std_Time_Database_defaultGetZoneRules___closed__11 = _init_l_Std_Time_Database_defaultGetZoneRules___closed__11();
l_Std_Time_Database_defaultGetZoneRules___closed__12 = _init_l_Std_Time_Database_defaultGetZoneRules___closed__12();
lean_mark_persistent(l_Std_Time_Database_defaultGetZoneRules___closed__12);
l_Std_Time_Database_defaultGetZoneRules___closed__13 = _init_l_Std_Time_Database_defaultGetZoneRules___closed__13();
lean_mark_persistent(l_Std_Time_Database_defaultGetZoneRules___closed__13);
l_Std_Time_Database_defaultGetLocalZoneRules___closed__0 = _init_l_Std_Time_Database_defaultGetLocalZoneRules___closed__0();
lean_mark_persistent(l_Std_Time_Database_defaultGetLocalZoneRules___closed__0);
l_Std_Time_Database_defaultGetLocalZoneRules___closed__1 = _init_l_Std_Time_Database_defaultGetLocalZoneRules___closed__1();
l_Std_Time_Database_defaultGetLocalZoneRules___closed__2 = _init_l_Std_Time_Database_defaultGetLocalZoneRules___closed__2();
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

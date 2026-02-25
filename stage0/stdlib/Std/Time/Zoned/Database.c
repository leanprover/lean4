// Lean compiler output
// Module: Std.Time.Zoned.Database
// Imports: public import Std.Time.Zoned.ZonedDateTime public import Std.Time.Zoned.Database.Basic public import Std.Time.Zoned.Database.TZdb public import Std.Time.Zoned.Database.Windows import Init.System.Platform
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
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_defaultGetZoneRules_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_defaultGetZoneRules_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_defaultGetZoneRules_spec__0___closed__0_value;
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_System_FilePath_pathExists(lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_defaultGetZoneRules_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Std_Time_Database_TZdb_readRulesFromDisk(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_defaultGetZoneRules_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Time_Database_defaultGetZoneRules___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "TZDIR"};
static const lean_object* l_Std_Time_Database_defaultGetZoneRules___closed__0 = (const lean_object*)&l_Std_Time_Database_defaultGetZoneRules___closed__0_value;
static const lean_string_object l_Std_Time_Database_defaultGetZoneRules___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "/usr/share/zoneinfo"};
static const lean_object* l_Std_Time_Database_defaultGetZoneRules___closed__1 = (const lean_object*)&l_Std_Time_Database_defaultGetZoneRules___closed__1_value;
static const lean_string_object l_Std_Time_Database_defaultGetZoneRules___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "/share/zoneinfo"};
static const lean_object* l_Std_Time_Database_defaultGetZoneRules___closed__2 = (const lean_object*)&l_Std_Time_Database_defaultGetZoneRules___closed__2_value;
static const lean_string_object l_Std_Time_Database_defaultGetZoneRules___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "/etc/zoneinfo"};
static const lean_object* l_Std_Time_Database_defaultGetZoneRules___closed__3 = (const lean_object*)&l_Std_Time_Database_defaultGetZoneRules___closed__3_value;
static const lean_string_object l_Std_Time_Database_defaultGetZoneRules___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "/usr/share/lib/zoneinfo"};
static const lean_object* l_Std_Time_Database_defaultGetZoneRules___closed__4 = (const lean_object*)&l_Std_Time_Database_defaultGetZoneRules___closed__4_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_once_cell_t l_Std_Time_Database_defaultGetZoneRules___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Database_defaultGetZoneRules___closed__5;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_Database_defaultGetZoneRules___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Database_defaultGetZoneRules___closed__6;
static lean_once_cell_t l_Std_Time_Database_defaultGetZoneRules___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Database_defaultGetZoneRules___closed__7;
static lean_once_cell_t l_Std_Time_Database_defaultGetZoneRules___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Database_defaultGetZoneRules___closed__8;
static lean_once_cell_t l_Std_Time_Database_defaultGetZoneRules___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Database_defaultGetZoneRules___closed__9;
size_t lean_array_size(lean_object*);
static lean_once_cell_t l_Std_Time_Database_defaultGetZoneRules___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Std_Time_Database_defaultGetZoneRules___closed__10;
static const lean_string_object l_Std_Time_Database_defaultGetZoneRules___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "cannot find "};
static const lean_object* l_Std_Time_Database_defaultGetZoneRules___closed__11 = (const lean_object*)&l_Std_Time_Database_defaultGetZoneRules___closed__11_value;
static const lean_string_object l_Std_Time_Database_defaultGetZoneRules___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = " in the local timezone database"};
static const lean_object* l_Std_Time_Database_defaultGetZoneRules___closed__12 = (const lean_object*)&l_Std_Time_Database_defaultGetZoneRules___closed__12_value;
extern uint8_t l_System_Platform_isWindows;
lean_object* lean_io_getenv(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Std_Time_Database_Windows_getZoneRules(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_defaultGetZoneRules(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_defaultGetZoneRules___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_Time_Database_defaultGetLocalZoneRules___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "/etc/localtime"};
static const lean_object* l_Std_Time_Database_defaultGetLocalZoneRules___closed__0 = (const lean_object*)&l_Std_Time_Database_defaultGetLocalZoneRules___closed__0_value;
uint64_t lean_int64_of_nat(lean_object*);
static lean_once_cell_t l_Std_Time_Database_defaultGetLocalZoneRules___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_Time_Database_defaultGetLocalZoneRules___closed__1;
uint64_t lean_int64_neg(uint64_t);
static lean_once_cell_t l_Std_Time_Database_defaultGetLocalZoneRules___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_Time_Database_defaultGetLocalZoneRules___closed__2;
lean_object* l_Std_Time_Database_TZdb_localRules(lean_object*);
lean_object* lean_get_windows_local_timezone_id_at(uint64_t);
LEAN_EXPORT lean_object* l_Std_Time_Database_defaultGetLocalZoneRules();
LEAN_EXPORT lean_object* l_Std_Time_Database_defaultGetLocalZoneRules___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_defaultGetZoneRules_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_4, x_3);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec_ref(x_1);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_5);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
lean_dec_ref(x_5);
x_9 = lean_array_uget_borrowed(x_2, x_4);
x_10 = l_System_FilePath_pathExists(x_9);
x_11 = lean_box(0);
if (x_10 == 0)
{
lean_object* x_12; size_t x_13; size_t x_14; 
x_12 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_defaultGetZoneRules_spec__0___closed__0));
x_13 = 1;
x_14 = lean_usize_add(x_4, x_13);
x_4 = x_14;
x_5 = x_12;
goto _start;
}
else
{
lean_object* x_16; 
lean_inc(x_9);
x_16 = l_Std_Time_Database_TZdb_readRulesFromDisk(x_9, x_1);
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
lean_ctor_set(x_20, 1, x_11);
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
lean_ctor_set(x_23, 1, x_11);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_defaultGetZoneRules_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_defaultGetZoneRules_spec__0(x_1, x_2, x_7, x_8, x_5);
lean_dec_ref(x_2);
return x_9;
}
}
static lean_object* _init_l_Std_Time_Database_defaultGetZoneRules___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_Database_defaultGetZoneRules___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Std_Time_Database_defaultGetZoneRules___closed__1));
x_2 = lean_obj_once(&l_Std_Time_Database_defaultGetZoneRules___closed__5, &l_Std_Time_Database_defaultGetZoneRules___closed__5_once, _init_l_Std_Time_Database_defaultGetZoneRules___closed__5);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Time_Database_defaultGetZoneRules___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Std_Time_Database_defaultGetZoneRules___closed__2));
x_2 = lean_obj_once(&l_Std_Time_Database_defaultGetZoneRules___closed__6, &l_Std_Time_Database_defaultGetZoneRules___closed__6_once, _init_l_Std_Time_Database_defaultGetZoneRules___closed__6);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Time_Database_defaultGetZoneRules___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Std_Time_Database_defaultGetZoneRules___closed__3));
x_2 = lean_obj_once(&l_Std_Time_Database_defaultGetZoneRules___closed__7, &l_Std_Time_Database_defaultGetZoneRules___closed__7_once, _init_l_Std_Time_Database_defaultGetZoneRules___closed__7);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Time_Database_defaultGetZoneRules___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Std_Time_Database_defaultGetZoneRules___closed__4));
x_2 = lean_obj_once(&l_Std_Time_Database_defaultGetZoneRules___closed__8, &l_Std_Time_Database_defaultGetZoneRules___closed__8_once, _init_l_Std_Time_Database_defaultGetZoneRules___closed__8);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static size_t _init_l_Std_Time_Database_defaultGetZoneRules___closed__10(void) {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = lean_obj_once(&l_Std_Time_Database_defaultGetZoneRules___closed__9, &l_Std_Time_Database_defaultGetZoneRules___closed__9_once, _init_l_Std_Time_Database_defaultGetZoneRules___closed__9);
x_2 = lean_array_size(x_1);
return x_2;
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
x_4 = ((lean_object*)(l_Std_Time_Database_defaultGetZoneRules___closed__0));
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
lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
lean_dec(x_5);
x_8 = lean_obj_once(&l_Std_Time_Database_defaultGetZoneRules___closed__9, &l_Std_Time_Database_defaultGetZoneRules___closed__9_once, _init_l_Std_Time_Database_defaultGetZoneRules___closed__9);
x_9 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_defaultGetZoneRules_spec__0___closed__0));
x_10 = lean_usize_once(&l_Std_Time_Database_defaultGetZoneRules___closed__10, &l_Std_Time_Database_defaultGetZoneRules___closed__10_once, _init_l_Std_Time_Database_defaultGetZoneRules___closed__10);
x_11 = 0;
lean_inc_ref(x_1);
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_defaultGetZoneRules_spec__0(x_1, x_8, x_10, x_11, x_9);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = ((lean_object*)(l_Std_Time_Database_defaultGetZoneRules___closed__11));
x_17 = lean_string_append(x_16, x_1);
lean_dec_ref(x_1);
x_18 = ((lean_object*)(l_Std_Time_Database_defaultGetZoneRules___closed__12));
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_mk_io_user_error(x_19);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 0, x_20);
return x_12;
}
else
{
lean_object* x_21; 
lean_dec_ref(x_1);
x_21 = lean_ctor_get(x_15, 0);
lean_inc(x_21);
lean_dec_ref(x_15);
lean_ctor_set(x_12, 0, x_21);
return x_12;
}
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_12, 0);
lean_inc(x_22);
lean_dec(x_12);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = ((lean_object*)(l_Std_Time_Database_defaultGetZoneRules___closed__11));
x_25 = lean_string_append(x_24, x_1);
lean_dec_ref(x_1);
x_26 = ((lean_object*)(l_Std_Time_Database_defaultGetZoneRules___closed__12));
x_27 = lean_string_append(x_25, x_26);
x_28 = lean_mk_io_user_error(x_27);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec_ref(x_1);
x_30 = lean_ctor_get(x_23, 0);
lean_inc(x_30);
lean_dec_ref(x_23);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec_ref(x_1);
x_32 = !lean_is_exclusive(x_12);
if (x_32 == 0)
{
return x_12;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_12, 0);
lean_inc(x_33);
lean_dec(x_12);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
}
else
{
lean_object* x_35; 
x_35 = l_Std_Time_Database_Windows_getZoneRules(x_1);
lean_dec_ref(x_1);
return x_35;
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
static uint64_t _init_l_Std_Time_Database_defaultGetLocalZoneRules___closed__1(void) {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = lean_unsigned_to_nat(2147483648u);
x_2 = lean_int64_of_nat(x_1);
return x_2;
}
}
static uint64_t _init_l_Std_Time_Database_defaultGetLocalZoneRules___closed__2(void) {
_start:
{
uint64_t x_1; uint64_t x_2; 
x_1 = lean_uint64_once(&l_Std_Time_Database_defaultGetLocalZoneRules___closed__1, &l_Std_Time_Database_defaultGetLocalZoneRules___closed__1_once, _init_l_Std_Time_Database_defaultGetLocalZoneRules___closed__1);
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
x_3 = ((lean_object*)(l_Std_Time_Database_defaultGetLocalZoneRules___closed__0));
x_4 = l_Std_Time_Database_TZdb_localRules(x_3);
return x_4;
}
else
{
uint64_t x_5; lean_object* x_6; 
x_5 = lean_uint64_once(&l_Std_Time_Database_defaultGetLocalZoneRules___closed__2, &l_Std_Time_Database_defaultGetLocalZoneRules___closed__2_once, _init_l_Std_Time_Database_defaultGetLocalZoneRules___closed__2);
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
lean_object* initialize_Init_System_Platform(uint8_t builtin);
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
res = initialize_Init_System_Platform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

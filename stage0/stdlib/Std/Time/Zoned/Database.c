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
static uint64_t l_Std_Time_Database_defaultGetLocalZoneRules___closed__2;
lean_object* l_Std_Time_Database_TZdb_localRules(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_defaultGetLocalZoneRules(lean_object*);
static uint64_t l_Std_Time_Database_defaultGetLocalZoneRules___closed__3;
uint64_t lean_int64_neg(uint64_t);
static lean_object* l_Std_Time_Database_defaultGetLocalZoneRules___closed__4;
LEAN_EXPORT lean_object* l_Std_Time_Database_defaultGetLocalZoneRules___closed__4___boxed__const__1;
static lean_object* l_Std_Time_Database_defaultGetZoneRules___closed__1;
static lean_object* l_Std_Time_Database_defaultGetLocalZoneRules___closed__5;
lean_object* l_Std_Time_Database_Windows_getLocalTimeZoneIdentifierAt___boxed(lean_object*, lean_object*);
uint64_t lean_int64_of_nat(lean_object*);
lean_object* l_Bind_bindLeft___at_Std_Time_Database_WindowsDb_inst___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Time_Database_Windows_getZoneRules___boxed(lean_object*, lean_object*);
lean_object* l_Std_Time_Database_TZdb_readRulesFromDisk(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_defaultGetZoneRules(lean_object*, lean_object*);
extern uint8_t l_System_Platform_isWindows;
static lean_object* l_Std_Time_Database_defaultGetLocalZoneRules___closed__1;
lean_object* l_Std_Time_Database_Windows_getZoneRules(lean_object*, lean_object*);
static lean_object* _init_l_Std_Time_Database_defaultGetZoneRules___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("/usr/share/zoneinfo/", 20, 20);
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
lean_object* x_4; lean_object* x_5; 
x_4 = l_Std_Time_Database_defaultGetZoneRules___closed__1;
x_5 = l_Std_Time_Database_TZdb_readRulesFromDisk(x_4, x_1, x_2);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = l_Std_Time_Database_Windows_getZoneRules(x_1, x_2);
lean_dec(x_1);
return x_6;
}
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

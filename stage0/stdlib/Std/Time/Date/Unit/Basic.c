// Lean compiler output
// Module: Std.Time.Date.Unit.Basic
// Imports: Std.Time.Date.Unit.Day Std.Time.Date.Unit.Month Std.Time.Date.Unit.Year Std.Time.Date.Unit.Weekday Std.Time.Date.Unit.Week
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
static lean_object* l_Std_Time_Day_Offset_ofWeeks___closed__1;
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toWeeks___boxed(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofWeeks___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toWeeks(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofWeeks(lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
static lean_object* _init_l_Std_Time_Day_Offset_ofWeeks___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(7u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofWeeks(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Std_Time_Day_Offset_ofWeeks___closed__1;
x_3 = lean_int_mul(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofWeeks___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_Day_Offset_ofWeeks(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toWeeks(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Std_Time_Day_Offset_ofWeeks___closed__1;
x_3 = lean_int_ediv(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toWeeks___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_Day_Offset_toWeeks(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Std_Time_Date_Unit_Day(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Time_Date_Unit_Month(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Time_Date_Unit_Year(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Time_Date_Unit_Weekday(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Time_Date_Unit_Week(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_Date_Unit_Basic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time_Date_Unit_Day(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Date_Unit_Month(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Date_Unit_Year(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Date_Unit_Weekday(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Date_Unit_Week(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Time_Day_Offset_ofWeeks___closed__1 = _init_l_Std_Time_Day_Offset_ofWeeks___closed__1();
lean_mark_persistent(l_Std_Time_Day_Offset_ofWeeks___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

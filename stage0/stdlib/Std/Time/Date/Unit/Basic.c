// Lean compiler output
// Module: Std.Time.Date.Unit.Basic
// Imports: public import Std.Time.Date.Unit.Year public import Std.Time.Date.Unit.Weekday public import Std.Time.Date.Unit.Week
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
lean_object* lean_nat_to_int(lean_object*);
static lean_once_cell_t l_Std_Time_Day_Offset_ofWeeks___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Day_Offset_ofWeeks___closed__0;
lean_object* lean_int_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofWeeks(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofWeeks___boxed(lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toWeeks(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toWeeks___boxed(lean_object*);
static lean_object* _init_l_Std_Time_Day_Offset_ofWeeks___closed__0(void) {
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
x_2 = lean_obj_once(&l_Std_Time_Day_Offset_ofWeeks___closed__0, &l_Std_Time_Day_Offset_ofWeeks___closed__0_once, _init_l_Std_Time_Day_Offset_ofWeeks___closed__0);
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
x_2 = lean_obj_once(&l_Std_Time_Day_Offset_ofWeeks___closed__0, &l_Std_Time_Day_Offset_ofWeeks___closed__0_once, _init_l_Std_Time_Day_Offset_ofWeeks___closed__0);
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
lean_object* initialize_Std_Time_Date_Unit_Year(uint8_t builtin);
lean_object* initialize_Std_Time_Date_Unit_Weekday(uint8_t builtin);
lean_object* initialize_Std_Time_Date_Unit_Week(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_Date_Unit_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time_Date_Unit_Year(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Date_Unit_Weekday(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Date_Unit_Week(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

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
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_Day_Offset_ofWeeks___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Day_Offset_ofWeeks___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofWeeks(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofWeeks___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toWeeks(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toWeeks___boxed(lean_object*);
static lean_object* _init_l_Std_Time_Day_Offset_ofWeeks___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(7u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofWeeks(lean_object* v_week_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_obj_once(&l_Std_Time_Day_Offset_ofWeeks___closed__0, &l_Std_Time_Day_Offset_ofWeeks___closed__0_once, _init_l_Std_Time_Day_Offset_ofWeeks___closed__0);
v___x_5_ = lean_int_mul(v_week_3_, v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofWeeks___boxed(lean_object* v_week_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = l_Std_Time_Day_Offset_ofWeeks(v_week_6_);
lean_dec(v_week_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toWeeks(lean_object* v_day_8_){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_9_ = lean_obj_once(&l_Std_Time_Day_Offset_ofWeeks___closed__0, &l_Std_Time_Day_Offset_ofWeeks___closed__0_once, _init_l_Std_Time_Day_Offset_ofWeeks___closed__0);
v___x_10_ = lean_int_ediv(v_day_8_, v___x_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toWeeks___boxed(lean_object* v_day_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Std_Time_Day_Offset_toWeeks(v_day_11_);
lean_dec(v_day_11_);
return v_res_12_;
}
}
lean_object* runtime_initialize_Std_Time_Date_Unit_Year(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_Date_Unit_Weekday(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_Date_Unit_Week(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_Date_Unit_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Time_Date_Unit_Year(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Date_Unit_Weekday(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Date_Unit_Week(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Time_Date_Unit_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
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
res = runtime_initialize_Std_Time_Date_Unit_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Time_Date_Unit_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Time_Date_Unit_Basic(builtin);
}
#ifdef __cplusplus
}
#endif

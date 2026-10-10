// Lean compiler output
// Module: Std.Time.Zoned.Database
// Imports: public import Std.Time.Zoned.Database.Basic public import Std.Time.Zoned.Database.TZdb public import Std.Time.Zoned.Database.Windows public import Std.Time.DateTime import Init.System.Platform
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
extern uint8_t l_System_Platform_isWindows;
extern lean_object* l_Std_Time_Database_TZdb_default;
lean_object* l_Std_Time_Database_TZdb_getZoneRules(lean_object*, lean_object*);
lean_object* l_Std_Time_Database_Windows_getZoneRules(lean_object*);
lean_object* l_Std_Time_Database_TZdb_getLocalZoneRules(lean_object*);
uint64_t lean_int64_of_nat(lean_object*);
uint64_t lean_int64_neg(uint64_t);
lean_object* lean_get_windows_local_timezone_id_at(uint64_t);
LEAN_EXPORT lean_object* l_Std_Time_Database_defaultGetZoneRules(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_defaultGetZoneRules___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_Database_defaultGetLocalZoneRules___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_Time_Database_defaultGetLocalZoneRules___closed__0;
static lean_once_cell_t l_Std_Time_Database_defaultGetLocalZoneRules___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_Time_Database_defaultGetLocalZoneRules___closed__1;
LEAN_EXPORT lean_object* l_Std_Time_Database_defaultGetLocalZoneRules();
LEAN_EXPORT lean_object* l_Std_Time_Database_defaultGetLocalZoneRules___boxed(lean_object*);
lean_object* l_Std_Time_Database_defaultGetZoneRules(lean_object* v_name_1_){
_start:
{
uint8_t v___x_3_; 
v___x_3_ = l_System_Platform_isWindows;
if (v___x_3_ == 0)
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = l_Std_Time_Database_TZdb_default;
v___x_5_ = l_Std_Time_Database_TZdb_getZoneRules(v___x_4_, v_name_1_);
return v___x_5_;
}
else
{
lean_object* v___x_6_; 
v___x_6_ = l_Std_Time_Database_Windows_getZoneRules(v_name_1_);
lean_dec_ref(v_name_1_);
return v___x_6_;
}
}
}
LEAN_EXPORT void l_Std_Time_Database_defaultGetZoneRules_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1_ = stack[0].m_obj;
lean_object* v_res_7_;
v_res_7_ = l_Std_Time_Database_defaultGetZoneRules(v_name_1_);
stack->m_obj
 = v_res_7_;
}
LEAN_EXPORT lean_object* l_Std_Time_Database_defaultGetZoneRules___boxed(lean_object* v_name_8_, lean_object* v_a_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Std_Time_Database_defaultGetZoneRules(v_name_8_);
return v_res_10_;
}
}
static uint64_t _init_l_Std_Time_Database_defaultGetLocalZoneRules___closed__0(void){
_start:
{
lean_object* v___x_11_; uint64_t v___x_12_; 
v___x_11_ = lean_unsigned_to_nat(2147483648u);
v___x_12_ = lean_int64_of_nat(v___x_11_);
return v___x_12_;
}
}
static uint64_t _init_l_Std_Time_Database_defaultGetLocalZoneRules___closed__1(void){
_start:
{
uint64_t v___x_13_; uint64_t v___x_14_; 
v___x_13_ = lean_uint64_once(&l_Std_Time_Database_defaultGetLocalZoneRules___closed__0, &l_Std_Time_Database_defaultGetLocalZoneRules___closed__0_once, _init_l_Std_Time_Database_defaultGetLocalZoneRules___closed__0);
v___x_14_ = lean_int64_neg(v___x_13_);
return v___x_14_;
}
}
lean_object* l_Std_Time_Database_defaultGetLocalZoneRules(){
_start:
{
uint8_t v___x_16_; 
v___x_16_ = l_System_Platform_isWindows;
if (v___x_16_ == 0)
{
lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_17_ = l_Std_Time_Database_TZdb_default;
v___x_18_ = l_Std_Time_Database_TZdb_getLocalZoneRules(v___x_17_);
return v___x_18_;
}
else
{
uint64_t v___x_19_; lean_object* v___x_20_; 
v___x_19_ = lean_uint64_once(&l_Std_Time_Database_defaultGetLocalZoneRules___closed__1, &l_Std_Time_Database_defaultGetLocalZoneRules___closed__1_once, _init_l_Std_Time_Database_defaultGetLocalZoneRules___closed__1);
v___x_20_ = lean_get_windows_local_timezone_id_at(v___x_19_);
if (lean_obj_tag(v___x_20_) == 0)
{
lean_object* v_a_21_; lean_object* v___x_22_; 
v_a_21_ = lean_ctor_get(v___x_20_, 0);
lean_inc(v_a_21_);
lean_dec_ref_known(v___x_20_, 1);
v___x_22_ = l_Std_Time_Database_Windows_getZoneRules(v_a_21_);
lean_dec(v_a_21_);
return v___x_22_;
}
else
{
lean_object* v_a_23_; lean_object* v___x_25_; uint8_t v_isShared_26_; uint8_t v_isSharedCheck_30_; 
v_a_23_ = lean_ctor_get(v___x_20_, 0);
v_isSharedCheck_30_ = !lean_is_exclusive(v___x_20_);
if (v_isSharedCheck_30_ == 0)
{
v___x_25_ = v___x_20_;
v_isShared_26_ = v_isSharedCheck_30_;
goto v_resetjp_24_;
}
else
{
lean_inc(v_a_23_);
lean_dec(v___x_20_);
v___x_25_ = lean_box(0);
v_isShared_26_ = v_isSharedCheck_30_;
goto v_resetjp_24_;
}
v_resetjp_24_:
{
lean_object* v___x_28_; 
if (v_isShared_26_ == 0)
{
v___x_28_ = v___x_25_;
goto v_reusejp_27_;
}
else
{
lean_object* v_reuseFailAlloc_29_; 
v_reuseFailAlloc_29_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_29_, 0, v_a_23_);
v___x_28_ = v_reuseFailAlloc_29_;
goto v_reusejp_27_;
}
v_reusejp_27_:
{
return v___x_28_;
}
}
}
}
}
}
LEAN_EXPORT void l_Std_Time_Database_defaultGetLocalZoneRules_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_31_;
v_res_31_ = l_Std_Time_Database_defaultGetLocalZoneRules();
stack->m_obj
 = v_res_31_;
}
LEAN_EXPORT lean_object* l_Std_Time_Database_defaultGetLocalZoneRules___boxed(lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Std_Time_Database_defaultGetLocalZoneRules();
return v_res_33_;
}
}
lean_object* runtime_initialize_Std_Time_Zoned_Database_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_Zoned_Database_TZdb(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_Zoned_Database_Windows(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_DateTime(uint8_t builtin);
lean_object* runtime_initialize_Init_System_Platform(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_Zoned_Database(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Time_Zoned_Database_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Zoned_Database_TZdb(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Zoned_Database_Windows(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_DateTime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_System_Platform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Time_Zoned_Database(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Time_Zoned_Database_Basic(uint8_t builtin);
lean_object* initialize_Std_Time_Zoned_Database_TZdb(uint8_t builtin);
lean_object* initialize_Std_Time_Zoned_Database_Windows(uint8_t builtin);
lean_object* initialize_Std_Time_DateTime(uint8_t builtin);
lean_object* initialize_Init_System_Platform(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_Zoned_Database(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time_Zoned_Database_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Zoned_Database_TZdb(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Zoned_Database_Windows(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_DateTime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_Platform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Zoned_Database(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Time_Zoned_Database(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Time_Zoned_Database(builtin);
}
#ifdef __cplusplus
}
#endif

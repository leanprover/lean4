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
LEAN_EXPORT lean_object* l_Std_Time_Database_defaultGetZoneRules(lean_object* v_name_1_){
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
LEAN_EXPORT lean_object* l_Std_Time_Database_defaultGetZoneRules___boxed(lean_object* v_name_7_, lean_object* v_a_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Std_Time_Database_defaultGetZoneRules(v_name_7_);
return v_res_9_;
}
}
static uint64_t _init_l_Std_Time_Database_defaultGetLocalZoneRules___closed__0(void){
_start:
{
lean_object* v___x_10_; uint64_t v___x_11_; 
v___x_10_ = lean_unsigned_to_nat(2147483648u);
v___x_11_ = lean_int64_of_nat(v___x_10_);
return v___x_11_;
}
}
static uint64_t _init_l_Std_Time_Database_defaultGetLocalZoneRules___closed__1(void){
_start:
{
uint64_t v___x_12_; uint64_t v___x_13_; 
v___x_12_ = lean_uint64_once(&l_Std_Time_Database_defaultGetLocalZoneRules___closed__0, &l_Std_Time_Database_defaultGetLocalZoneRules___closed__0_once, _init_l_Std_Time_Database_defaultGetLocalZoneRules___closed__0);
v___x_13_ = lean_int64_neg(v___x_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_defaultGetLocalZoneRules(){
_start:
{
uint8_t v___x_15_; 
v___x_15_ = l_System_Platform_isWindows;
if (v___x_15_ == 0)
{
lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_16_ = l_Std_Time_Database_TZdb_default;
v___x_17_ = l_Std_Time_Database_TZdb_getLocalZoneRules(v___x_16_);
return v___x_17_;
}
else
{
uint64_t v___x_18_; lean_object* v___x_19_; 
v___x_18_ = lean_uint64_once(&l_Std_Time_Database_defaultGetLocalZoneRules___closed__1, &l_Std_Time_Database_defaultGetLocalZoneRules___closed__1_once, _init_l_Std_Time_Database_defaultGetLocalZoneRules___closed__1);
v___x_19_ = lean_get_windows_local_timezone_id_at(v___x_18_);
if (lean_obj_tag(v___x_19_) == 0)
{
lean_object* v_a_20_; lean_object* v___x_21_; 
v_a_20_ = lean_ctor_get(v___x_19_, 0);
lean_inc(v_a_20_);
lean_dec_ref_known(v___x_19_, 1);
v___x_21_ = l_Std_Time_Database_Windows_getZoneRules(v_a_20_);
lean_dec(v_a_20_);
return v___x_21_;
}
else
{
lean_object* v_a_22_; lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_29_; 
v_a_22_ = lean_ctor_get(v___x_19_, 0);
v_isSharedCheck_29_ = !lean_is_exclusive(v___x_19_);
if (v_isSharedCheck_29_ == 0)
{
v___x_24_ = v___x_19_;
v_isShared_25_ = v_isSharedCheck_29_;
goto v_resetjp_23_;
}
else
{
lean_inc(v_a_22_);
lean_dec(v___x_19_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_29_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
lean_object* v___x_27_; 
if (v_isShared_25_ == 0)
{
v___x_27_ = v___x_24_;
goto v_reusejp_26_;
}
else
{
lean_object* v_reuseFailAlloc_28_; 
v_reuseFailAlloc_28_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_28_, 0, v_a_22_);
v___x_27_ = v_reuseFailAlloc_28_;
goto v_reusejp_26_;
}
v_reusejp_26_:
{
return v___x_27_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_defaultGetLocalZoneRules___boxed(lean_object* v_a_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_Std_Time_Database_defaultGetLocalZoneRules();
return v_res_31_;
}
}
lean_object* runtime_initialize_Std_Time_Zoned_ZonedDateTime(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_Zoned_Database_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_Zoned_Database_TZdb(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_Zoned_Database_Windows(uint8_t builtin);
lean_object* runtime_initialize_Init_System_Platform(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_Zoned_Database(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Time_Zoned_ZonedDateTime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Zoned_Database_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Zoned_Database_TZdb(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Zoned_Database_Windows(builtin);
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

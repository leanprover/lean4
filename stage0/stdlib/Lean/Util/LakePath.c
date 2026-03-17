// Lean compiler output
// Module: Lean.Util.LakePath
// Imports: public import Init.System.IO
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
lean_object* lean_io_getenv(lean_object*);
lean_object* l_IO_appDir();
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
static const lean_string_object l_Lean_determineLakePath___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LAKE"};
static const lean_object* l_Lean_determineLakePath___closed__0 = (const lean_object*)&l_Lean_determineLakePath___closed__0_value;
static const lean_string_object l_Lean_determineLakePath___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "LEAN_SYSROOT"};
static const lean_object* l_Lean_determineLakePath___closed__1 = (const lean_object*)&l_Lean_determineLakePath___closed__1_value;
static const lean_string_object l_Lean_determineLakePath___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lake"};
static const lean_object* l_Lean_determineLakePath___closed__2 = (const lean_object*)&l_Lean_determineLakePath___closed__2_value;
static const lean_string_object l_Lean_determineLakePath___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "bin"};
static const lean_object* l_Lean_determineLakePath___closed__3 = (const lean_object*)&l_Lean_determineLakePath___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_determineLakePath();
LEAN_EXPORT lean_object* l_Lean_determineLakePath___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_determineLakePath(){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_6_ = ((lean_object*)(l_Lean_determineLakePath___closed__0));
v___x_7_ = lean_io_getenv(v___x_6_);
if (lean_obj_tag(v___x_7_) == 1)
{
lean_object* v_val_8_; lean_object* v___x_10_; uint8_t v_isShared_11_; uint8_t v_isSharedCheck_15_; 
v_val_8_ = lean_ctor_get(v___x_7_, 0);
v_isSharedCheck_15_ = !lean_is_exclusive(v___x_7_);
if (v_isSharedCheck_15_ == 0)
{
v___x_10_ = v___x_7_;
v_isShared_11_ = v_isSharedCheck_15_;
goto v_resetjp_9_;
}
else
{
lean_inc(v_val_8_);
lean_dec(v___x_7_);
v___x_10_ = lean_box(0);
v_isShared_11_ = v_isSharedCheck_15_;
goto v_resetjp_9_;
}
v_resetjp_9_:
{
lean_object* v___x_13_; 
if (v_isShared_11_ == 0)
{
lean_ctor_set_tag(v___x_10_, 0);
v___x_13_ = v___x_10_;
goto v_reusejp_12_;
}
else
{
lean_object* v_reuseFailAlloc_14_; 
v_reuseFailAlloc_14_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_14_, 0, v_val_8_);
v___x_13_ = v_reuseFailAlloc_14_;
goto v_reusejp_12_;
}
v_reusejp_12_:
{
return v___x_13_;
}
}
}
else
{
lean_object* v___x_16_; lean_object* v___x_17_; 
lean_dec(v___x_7_);
v___x_16_ = ((lean_object*)(l_Lean_determineLakePath___closed__1));
v___x_17_ = lean_io_getenv(v___x_16_);
if (lean_obj_tag(v___x_17_) == 0)
{
lean_object* v___x_18_; 
v___x_18_ = l_IO_appDir();
if (lean_obj_tag(v___x_18_) == 0)
{
lean_object* v_a_19_; lean_object* v___x_21_; uint8_t v_isShared_22_; uint8_t v_isSharedCheck_28_; 
v_a_19_ = lean_ctor_get(v___x_18_, 0);
v_isSharedCheck_28_ = !lean_is_exclusive(v___x_18_);
if (v_isSharedCheck_28_ == 0)
{
v___x_21_ = v___x_18_;
v_isShared_22_ = v_isSharedCheck_28_;
goto v_resetjp_20_;
}
else
{
lean_inc(v_a_19_);
lean_dec(v___x_18_);
v___x_21_ = lean_box(0);
v_isShared_22_ = v_isSharedCheck_28_;
goto v_resetjp_20_;
}
v_resetjp_20_:
{
lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_26_; 
v___x_23_ = ((lean_object*)(l_Lean_determineLakePath___closed__2));
v___x_24_ = l_System_FilePath_join(v_a_19_, v___x_23_);
if (v_isShared_22_ == 0)
{
lean_ctor_set(v___x_21_, 0, v___x_24_);
v___x_26_ = v___x_21_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v___x_24_);
v___x_26_ = v_reuseFailAlloc_27_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
return v___x_26_;
}
}
}
else
{
return v___x_18_;
}
}
else
{
lean_object* v_val_29_; lean_object* v___x_31_; uint8_t v_isShared_32_; uint8_t v_isSharedCheck_40_; 
v_val_29_ = lean_ctor_get(v___x_17_, 0);
v_isSharedCheck_40_ = !lean_is_exclusive(v___x_17_);
if (v_isSharedCheck_40_ == 0)
{
v___x_31_ = v___x_17_;
v_isShared_32_ = v_isSharedCheck_40_;
goto v_resetjp_30_;
}
else
{
lean_inc(v_val_29_);
lean_dec(v___x_17_);
v___x_31_ = lean_box(0);
v_isShared_32_ = v_isSharedCheck_40_;
goto v_resetjp_30_;
}
v_resetjp_30_:
{
lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_38_; 
v___x_33_ = ((lean_object*)(l_Lean_determineLakePath___closed__3));
v___x_34_ = l_System_FilePath_join(v_val_29_, v___x_33_);
v___x_35_ = ((lean_object*)(l_Lean_determineLakePath___closed__2));
v___x_36_ = l_System_FilePath_join(v___x_34_, v___x_35_);
if (v_isShared_32_ == 0)
{
lean_ctor_set_tag(v___x_31_, 0);
lean_ctor_set(v___x_31_, 0, v___x_36_);
v___x_38_ = v___x_31_;
goto v_reusejp_37_;
}
else
{
lean_object* v_reuseFailAlloc_39_; 
v_reuseFailAlloc_39_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_39_, 0, v___x_36_);
v___x_38_ = v_reuseFailAlloc_39_;
goto v_reusejp_37_;
}
v_reusejp_37_:
{
return v___x_38_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_determineLakePath___boxed(lean_object* v_a_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_Lean_determineLakePath();
return v_res_42_;
}
}
lean_object* runtime_initialize_Init_System_IO(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_LakePath(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Util_LakePath(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_System_IO(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_LakePath(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_LakePath(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Util_LakePath(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Util_LakePath(builtin);
}
#ifdef __cplusplus
}
#endif

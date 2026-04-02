// Lean compiler output
// Module: Lean.Util.RecDepth
// Imports: public import Lean.Data.Options
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
extern lean_object* l_Lean_defaultMaxRecDepth;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_initFn___closed__0_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_initFn___closed__0_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__1_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(213, 238, 178, 82, 0, 139, 185, 177)}};
static const lean_object* l_Lean_initFn___closed__1_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_initFn___closed__2_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "maximum recursion depth for many Lean procedures, 0 means no limit"};
static const lean_object* l_Lean_initFn___closed__2_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4__value;
static lean_once_cell_t l_Lean_initFn___closed__3_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_initFn___closed__3_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4_;
static const lean_string_object l_Lean_initFn___closed__4_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_initFn___closed__4_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__5_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_initFn___closed__5_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(108, 252, 239, 255, 166, 128, 233, 59)}};
static const lean_object* l_Lean_initFn___closed__5_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_maxRecDepth;
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v___x_8_; uint8_t v_isShared_9_; uint8_t v_isSharedCheck_32_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_isSharedCheck_32_ = !lean_is_exclusive(v_decl_2_);
if (v_isSharedCheck_32_ == 0)
{
v___x_8_ = v_decl_2_;
v_isShared_9_ = v_isSharedCheck_32_;
goto v_resetjp_7_;
}
else
{
lean_inc(v_descr_6_);
lean_inc(v_defValue_5_);
lean_dec(v_decl_2_);
v___x_8_ = lean_box(0);
v_isShared_9_ = v_isSharedCheck_32_;
goto v_resetjp_7_;
}
v_resetjp_7_:
{
lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
lean_inc(v_defValue_5_);
v___x_10_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_10_, 0, v_defValue_5_);
lean_inc_n(v_name_1_, 2);
v___x_11_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_11_, 0, v_name_1_);
lean_ctor_set(v___x_11_, 1, v_ref_3_);
lean_ctor_set(v___x_11_, 2, v___x_10_);
lean_ctor_set(v___x_11_, 3, v_descr_6_);
v___x_12_ = lean_register_option(v_name_1_, v___x_11_);
if (lean_obj_tag(v___x_12_) == 0)
{
lean_object* v___x_14_; uint8_t v_isShared_15_; uint8_t v_isSharedCheck_22_; 
v_isSharedCheck_22_ = !lean_is_exclusive(v___x_12_);
if (v_isSharedCheck_22_ == 0)
{
lean_object* v_unused_23_; 
v_unused_23_ = lean_ctor_get(v___x_12_, 0);
lean_dec(v_unused_23_);
v___x_14_ = v___x_12_;
v_isShared_15_ = v_isSharedCheck_22_;
goto v_resetjp_13_;
}
else
{
lean_dec(v___x_12_);
v___x_14_ = lean_box(0);
v_isShared_15_ = v_isSharedCheck_22_;
goto v_resetjp_13_;
}
v_resetjp_13_:
{
lean_object* v___x_17_; 
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 1, v_defValue_5_);
lean_ctor_set(v___x_8_, 0, v_name_1_);
v___x_17_ = v___x_8_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_21_; 
v_reuseFailAlloc_21_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_21_, 0, v_name_1_);
lean_ctor_set(v_reuseFailAlloc_21_, 1, v_defValue_5_);
v___x_17_ = v_reuseFailAlloc_21_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
lean_object* v___x_19_; 
if (v_isShared_15_ == 0)
{
lean_ctor_set(v___x_14_, 0, v___x_17_);
v___x_19_ = v___x_14_;
goto v_reusejp_18_;
}
else
{
lean_object* v_reuseFailAlloc_20_; 
v_reuseFailAlloc_20_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_20_, 0, v___x_17_);
v___x_19_ = v_reuseFailAlloc_20_;
goto v_reusejp_18_;
}
v_reusejp_18_:
{
return v___x_19_;
}
}
}
}
else
{
lean_object* v_a_24_; lean_object* v___x_26_; uint8_t v_isShared_27_; uint8_t v_isSharedCheck_31_; 
lean_del_object(v___x_8_);
lean_dec(v_defValue_5_);
lean_dec(v_name_1_);
v_a_24_ = lean_ctor_get(v___x_12_, 0);
v_isSharedCheck_31_ = !lean_is_exclusive(v___x_12_);
if (v_isSharedCheck_31_ == 0)
{
v___x_26_ = v___x_12_;
v_isShared_27_ = v_isSharedCheck_31_;
goto v_resetjp_25_;
}
else
{
lean_inc(v_a_24_);
lean_dec(v___x_12_);
v___x_26_ = lean_box(0);
v_isShared_27_ = v_isSharedCheck_31_;
goto v_resetjp_25_;
}
v_resetjp_25_:
{
lean_object* v___x_29_; 
if (v_isShared_27_ == 0)
{
v___x_29_ = v___x_26_;
goto v_reusejp_28_;
}
else
{
lean_object* v_reuseFailAlloc_30_; 
v_reuseFailAlloc_30_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_30_, 0, v_a_24_);
v___x_29_ = v_reuseFailAlloc_30_;
goto v_reusejp_28_;
}
v_reusejp_28_:
{
return v___x_29_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_33_, lean_object* v_decl_34_, lean_object* v_ref_35_, lean_object* v_a_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4__spec__0(v_name_33_, v_decl_34_, v_ref_35_);
return v_res_37_;
}
}
static lean_object* _init_l_Lean_initFn___closed__3_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4_(void){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_42_ = ((lean_object*)(l_Lean_initFn___closed__2_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4_));
v___x_43_ = l_Lean_defaultMaxRecDepth;
v___x_44_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_44_, 0, v___x_43_);
lean_ctor_set(v___x_44_, 1, v___x_42_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_50_ = ((lean_object*)(l_Lean_initFn___closed__1_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4_));
v___x_51_ = lean_obj_once(&l_Lean_initFn___closed__3_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4_, &l_Lean_initFn___closed__3_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4__once, _init_l_Lean_initFn___closed__3_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4_);
v___x_52_ = ((lean_object*)(l_Lean_initFn___closed__5_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4_));
v___x_53_ = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4__spec__0(v___x_50_, v___x_51_, v___x_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4____boxed(lean_object* v_a_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_Lean_initFn_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4_();
return v_res_55_;
}
}
lean_object* runtime_initialize_Lean_Data_Options(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_RecDepth(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Data_Options(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_initFn_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_maxRecDepth = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_maxRecDepth);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Util_RecDepth(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_Options(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_RecDepth(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Options(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_RecDepth(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Util_RecDepth(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Util_RecDepth(builtin);
}
#ifdef __cplusplus
}
#endif

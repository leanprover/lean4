// Lean compiler output
// Module: Lean.CompactedRegion
// Imports: public import Init.System.IO public import Lean.Data.Name
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
LEAN_EXPORT lean_object* l___private_Lean_CompactedRegion_0__Lean_CompactorSpec;
lean_object* lean_compacted_region_free(lean_object*);
LEAN_EXPORT lean_object* l_Lean_CompactedRegion_free___boxed(lean_object*, lean_object*);
lean_object* lean_compacted_region_save(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_CompactedRegion_save___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_compacted_region_read(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CompactedRegion_read___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_CompactedRegion_0__Lean_CompactorSpec(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lean_box(0);
return v___x_1_;
}
}
LEAN_EXPORT lean_object* l_Lean_CompactedRegion_free___boxed(lean_object* v_region_4_, lean_object* v_a_00___x40___internal___hyg_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = lean_compacted_region_free(v_region_4_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_CompactedRegion_save___boxed(lean_object* v_00_u03b1_15_, lean_object* v_fname_16_, lean_object* v_key_17_, lean_object* v_data_18_, lean_object* v_depRegions_19_, lean_object* v_prev_20_, lean_object* v_allowClosures_21_, lean_object* v_a_00___x40___internal___hyg_22_){
_start:
{
uint8_t v_allowClosures_boxed_23_; lean_object* v_res_24_; 
v_allowClosures_boxed_23_ = lean_unbox(v_allowClosures_21_);
v_res_24_ = lean_compacted_region_save(v_fname_16_, v_key_17_, v_data_18_, v_depRegions_19_, v_prev_20_, v_allowClosures_boxed_23_);
lean_dec_ref(v_depRegions_19_);
lean_dec(v_data_18_);
lean_dec(v_key_17_);
lean_dec_ref(v_fname_16_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_CompactedRegion_read___boxed(lean_object* v_00_u03b1_29_, lean_object* v_fname_30_, lean_object* v_depRegions_31_, lean_object* v_a_00___x40___internal___hyg_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = lean_compacted_region_read(v_fname_30_, v_depRegions_31_);
lean_dec_ref(v_depRegions_31_);
lean_dec_ref(v_fname_30_);
return v_res_33_;
}
}
lean_object* runtime_initialize_Init_System_IO(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Name(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_CompactedRegion(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_CompactedRegion_0__Lean_CompactorSpec = _init_l___private_Lean_CompactedRegion_0__Lean_CompactorSpec();
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_CompactedRegion(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_System_IO(uint8_t builtin);
lean_object* initialize_Lean_Data_Name(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_CompactedRegion(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_CompactedRegion(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_CompactedRegion(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_CompactedRegion(builtin);
}
#ifdef __cplusplus
}
#endif

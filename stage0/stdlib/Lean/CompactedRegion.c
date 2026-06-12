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
uint8_t lean_compacted_region_is_memory_mapped(size_t);
LEAN_EXPORT lean_object* l_Lean_CompactedRegion_isMemoryMapped___boxed(lean_object*);
size_t lean_compacted_region_size(size_t);
LEAN_EXPORT lean_object* l_Lean_CompactedRegion_size___boxed(lean_object*);
lean_object* lean_compacted_region_free(size_t);
LEAN_EXPORT lean_object* l_Lean_CompactedRegion_free___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CompactedRegion_0__Lean_CompactorSpec;
lean_object* lean_compacted_region_save(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_CompactedRegion_save___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_compacted_region_read(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CompactedRegion_read___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CompactedRegion_isMemoryMapped___boxed(lean_object* v_a_00___x40___internal___hyg_2_){
_start:
{
size_t v_a_00___x40___internal___hyg_1__boxed_3_; uint8_t v_res_4_; lean_object* v_r_5_; 
v_a_00___x40___internal___hyg_1__boxed_3_ = lean_unbox_usize(v_a_00___x40___internal___hyg_2_);
lean_dec(v_a_00___x40___internal___hyg_2_);
v_res_4_ = lean_compacted_region_is_memory_mapped(v_a_00___x40___internal___hyg_1__boxed_3_);
v_r_5_ = lean_box(v_res_4_);
return v_r_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_CompactedRegion_size___boxed(lean_object* v_a_00___x40___internal___hyg_7_){
_start:
{
size_t v_a_00___x40___internal___hyg_1__boxed_8_; size_t v_res_9_; lean_object* v_r_10_; 
v_a_00___x40___internal___hyg_1__boxed_8_ = lean_unbox_usize(v_a_00___x40___internal___hyg_7_);
lean_dec(v_a_00___x40___internal___hyg_7_);
v_res_9_ = lean_compacted_region_size(v_a_00___x40___internal___hyg_1__boxed_8_);
v_r_10_ = lean_box_usize(v_res_9_);
return v_r_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_CompactedRegion_free___boxed(lean_object* v_a_00___x40___internal___hyg_13_, lean_object* v_a_00___x40___internal___hyg_14_){
_start:
{
size_t v_a_00___x40___internal___hyg_1__boxed_15_; lean_object* v_res_16_; 
v_a_00___x40___internal___hyg_1__boxed_15_ = lean_unbox_usize(v_a_00___x40___internal___hyg_13_);
lean_dec(v_a_00___x40___internal___hyg_13_);
v_res_16_ = lean_compacted_region_free(v_a_00___x40___internal___hyg_1__boxed_15_);
return v_res_16_;
}
}
static lean_object* _init_l___private_Lean_CompactedRegion_0__Lean_CompactorSpec(void){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = lean_box(0);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_CompactedRegion_save___boxed(lean_object* v_00_u03b1_26_, lean_object* v_fname_27_, lean_object* v_key_28_, lean_object* v_data_29_, lean_object* v_depRegions_30_, lean_object* v_prev_31_, lean_object* v_allowClosures_32_, lean_object* v_a_00___x40___internal___hyg_33_){
_start:
{
uint8_t v_allowClosures_boxed_34_; lean_object* v_res_35_; 
v_allowClosures_boxed_34_ = lean_unbox(v_allowClosures_32_);
v_res_35_ = lean_compacted_region_save(v_fname_27_, v_key_28_, v_data_29_, v_depRegions_30_, v_prev_31_, v_allowClosures_boxed_34_);
lean_dec_ref(v_depRegions_30_);
lean_dec(v_data_29_);
lean_dec(v_key_28_);
lean_dec_ref(v_fname_27_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_CompactedRegion_read___boxed(lean_object* v_00_u03b1_40_, lean_object* v_fname_41_, lean_object* v_depRegions_42_, lean_object* v_a_00___x40___internal___hyg_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = lean_compacted_region_read(v_fname_41_, v_depRegions_42_);
lean_dec_ref(v_depRegions_42_);
lean_dec_ref(v_fname_41_);
return v_res_44_;
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

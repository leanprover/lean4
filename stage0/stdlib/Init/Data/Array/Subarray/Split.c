// Lean compiler output
// Module: Init.Data.Array.Subarray.Split
// Imports: public import Init.Data.Array.Subarray import all Init.Data.Array.Subarray import Init.Omega
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
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_drop___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_drop___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_drop(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_drop___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_take___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_take___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_take(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_take___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_split___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_split___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_split(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_split___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_drop___redArg(lean_object* v_arr_1_, lean_object* v_i_2_){
_start:
{
lean_object* v_array_3_; lean_object* v_start_4_; lean_object* v_stop_5_; lean_object* v___x_7_; uint8_t v_isShared_8_; uint8_t v_isSharedCheck_17_; 
v_array_3_ = lean_ctor_get(v_arr_1_, 0);
v_start_4_ = lean_ctor_get(v_arr_1_, 1);
v_stop_5_ = lean_ctor_get(v_arr_1_, 2);
v_isSharedCheck_17_ = !lean_is_exclusive(v_arr_1_);
if (v_isSharedCheck_17_ == 0)
{
v___x_7_ = v_arr_1_;
v_isShared_8_ = v_isSharedCheck_17_;
goto v_resetjp_6_;
}
else
{
lean_inc(v_stop_5_);
lean_inc(v_start_4_);
lean_inc(v_array_3_);
lean_dec(v_arr_1_);
v___x_7_ = lean_box(0);
v_isShared_8_ = v_isSharedCheck_17_;
goto v_resetjp_6_;
}
v_resetjp_6_:
{
lean_object* v___x_9_; uint8_t v___x_10_; 
v___x_9_ = lean_nat_add(v_start_4_, v_i_2_);
lean_dec(v_start_4_);
v___x_10_ = lean_nat_dec_le(v___x_9_, v_stop_5_);
if (v___x_10_ == 0)
{
lean_object* v___x_12_; 
lean_dec(v___x_9_);
lean_inc(v_stop_5_);
if (v_isShared_8_ == 0)
{
lean_ctor_set(v___x_7_, 1, v_stop_5_);
v___x_12_ = v___x_7_;
goto v_reusejp_11_;
}
else
{
lean_object* v_reuseFailAlloc_13_; 
v_reuseFailAlloc_13_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_13_, 0, v_array_3_);
lean_ctor_set(v_reuseFailAlloc_13_, 1, v_stop_5_);
lean_ctor_set(v_reuseFailAlloc_13_, 2, v_stop_5_);
v___x_12_ = v_reuseFailAlloc_13_;
goto v_reusejp_11_;
}
v_reusejp_11_:
{
return v___x_12_;
}
}
else
{
lean_object* v___x_15_; 
if (v_isShared_8_ == 0)
{
lean_ctor_set(v___x_7_, 1, v___x_9_);
v___x_15_ = v___x_7_;
goto v_reusejp_14_;
}
else
{
lean_object* v_reuseFailAlloc_16_; 
v_reuseFailAlloc_16_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_16_, 0, v_array_3_);
lean_ctor_set(v_reuseFailAlloc_16_, 1, v___x_9_);
lean_ctor_set(v_reuseFailAlloc_16_, 2, v_stop_5_);
v___x_15_ = v_reuseFailAlloc_16_;
goto v_reusejp_14_;
}
v_reusejp_14_:
{
return v___x_15_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_drop___redArg___boxed(lean_object* v_arr_18_, lean_object* v_i_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Subarray_drop___redArg(v_arr_18_, v_i_19_);
lean_dec(v_i_19_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Subarray_drop(lean_object* v_00_u03b1_21_, lean_object* v_arr_22_, lean_object* v_i_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = l_Subarray_drop___redArg(v_arr_22_, v_i_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Subarray_drop___boxed(lean_object* v_00_u03b1_25_, lean_object* v_arr_26_, lean_object* v_i_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Subarray_drop(v_00_u03b1_25_, v_arr_26_, v_i_27_);
lean_dec(v_i_27_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Subarray_take___redArg(lean_object* v_arr_29_, lean_object* v_i_30_){
_start:
{
lean_object* v_array_31_; lean_object* v_start_32_; lean_object* v_stop_33_; lean_object* v___x_35_; uint8_t v_isShared_36_; uint8_t v_isSharedCheck_45_; 
v_array_31_ = lean_ctor_get(v_arr_29_, 0);
v_start_32_ = lean_ctor_get(v_arr_29_, 1);
v_stop_33_ = lean_ctor_get(v_arr_29_, 2);
v_isSharedCheck_45_ = !lean_is_exclusive(v_arr_29_);
if (v_isSharedCheck_45_ == 0)
{
v___x_35_ = v_arr_29_;
v_isShared_36_ = v_isSharedCheck_45_;
goto v_resetjp_34_;
}
else
{
lean_inc(v_stop_33_);
lean_inc(v_start_32_);
lean_inc(v_array_31_);
lean_dec(v_arr_29_);
v___x_35_ = lean_box(0);
v_isShared_36_ = v_isSharedCheck_45_;
goto v_resetjp_34_;
}
v_resetjp_34_:
{
lean_object* v___x_37_; uint8_t v___x_38_; 
v___x_37_ = lean_nat_add(v_start_32_, v_i_30_);
v___x_38_ = lean_nat_dec_le(v___x_37_, v_stop_33_);
if (v___x_38_ == 0)
{
lean_object* v___x_40_; 
lean_dec(v___x_37_);
if (v_isShared_36_ == 0)
{
v___x_40_ = v___x_35_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_41_; 
v_reuseFailAlloc_41_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_41_, 0, v_array_31_);
lean_ctor_set(v_reuseFailAlloc_41_, 1, v_start_32_);
lean_ctor_set(v_reuseFailAlloc_41_, 2, v_stop_33_);
v___x_40_ = v_reuseFailAlloc_41_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
return v___x_40_;
}
}
else
{
lean_object* v___x_43_; 
lean_dec(v_stop_33_);
if (v_isShared_36_ == 0)
{
lean_ctor_set(v___x_35_, 2, v___x_37_);
v___x_43_ = v___x_35_;
goto v_reusejp_42_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v_array_31_);
lean_ctor_set(v_reuseFailAlloc_44_, 1, v_start_32_);
lean_ctor_set(v_reuseFailAlloc_44_, 2, v___x_37_);
v___x_43_ = v_reuseFailAlloc_44_;
goto v_reusejp_42_;
}
v_reusejp_42_:
{
return v___x_43_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_take___redArg___boxed(lean_object* v_arr_46_, lean_object* v_i_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l_Subarray_take___redArg(v_arr_46_, v_i_47_);
lean_dec(v_i_47_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Subarray_take(lean_object* v_00_u03b1_49_, lean_object* v_arr_50_, lean_object* v_i_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l_Subarray_take___redArg(v_arr_50_, v_i_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Subarray_take___boxed(lean_object* v_00_u03b1_53_, lean_object* v_arr_54_, lean_object* v_i_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Subarray_take(v_00_u03b1_53_, v_arr_54_, v_i_55_);
lean_dec(v_i_55_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Subarray_split___redArg(lean_object* v_s_57_, lean_object* v_i_58_){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
lean_inc_ref(v_s_57_);
v___x_59_ = l_Subarray_take___redArg(v_s_57_, v_i_58_);
v___x_60_ = l_Subarray_drop___redArg(v_s_57_, v_i_58_);
v___x_61_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_61_, 0, v___x_59_);
lean_ctor_set(v___x_61_, 1, v___x_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Subarray_split___redArg___boxed(lean_object* v_s_62_, lean_object* v_i_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_Subarray_split___redArg(v_s_62_, v_i_63_);
lean_dec(v_i_63_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Subarray_split(lean_object* v_00_u03b1_65_, lean_object* v_s_66_, lean_object* v_i_67_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = l_Subarray_split___redArg(v_s_66_, v_i_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Subarray_split___boxed(lean_object* v_00_u03b1_69_, lean_object* v_s_70_, lean_object* v_i_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_Subarray_split(v_00_u03b1_69_, v_s_70_, v_i_71_);
lean_dec(v_i_71_);
return v_res_72_;
}
}
lean_object* runtime_initialize_Init_Data_Array_Subarray(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Subarray(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Array_Subarray_Split(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Array_Subarray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Subarray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Array_Subarray_Split(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Array_Subarray(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Subarray(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Array_Subarray_Split(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_Subarray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Subarray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Subarray_Split(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Array_Subarray_Split(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Array_Subarray_Split(builtin);
}
#ifdef __cplusplus
}
#endif

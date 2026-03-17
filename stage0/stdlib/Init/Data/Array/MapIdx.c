// Lean compiler output
// Module: Init.Data.Array.MapIdx
// Imports: import all Init.Data.Array.Basic public import Init.Data.List.MapIdx import all Init.Data.List.MapIdx import Init.Data.Array.OfFn
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_MapIdx_0__Array_mapFinIdxM_map_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_MapIdx_0__Array_mapFinIdxM_map_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_MapIdx_0__Array_mapFinIdxM_map_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_MapIdx_0__Array_mapFinIdxM_map_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_MapIdx_0__List_mapFinIdx_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_MapIdx_0__List_mapFinIdx_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_MapIdx_0__List_mapFinIdx_go_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_MapIdx_0__List_mapIdx_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_MapIdx_0__List_mapIdx_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_MapIdx_0__Array_mapFinIdxM_map_match__1_splitter___redArg(lean_object* v_i_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
_start:
{
lean_object* v_zero_4_; uint8_t v_isZero_5_; 
v_zero_4_ = lean_unsigned_to_nat(0u);
v_isZero_5_ = lean_nat_dec_eq(v_i_1_, v_zero_4_);
if (v_isZero_5_ == 1)
{
lean_object* v___x_6_; 
lean_dec(v_h__2_3_);
v___x_6_ = lean_apply_1(v_h__1_2_, lean_box(0));
return v___x_6_;
}
else
{
lean_object* v_one_7_; lean_object* v_n_8_; lean_object* v___x_9_; 
lean_dec(v_h__1_2_);
v_one_7_ = lean_unsigned_to_nat(1u);
v_n_8_ = lean_nat_sub(v_i_1_, v_one_7_);
v___x_9_ = lean_apply_2(v_h__2_3_, v_n_8_, lean_box(0));
return v___x_9_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_MapIdx_0__Array_mapFinIdxM_map_match__1_splitter___redArg___boxed(lean_object* v_i_10_, lean_object* v_h__1_11_, lean_object* v_h__2_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l___private_Init_Data_Array_MapIdx_0__Array_mapFinIdxM_map_match__1_splitter___redArg(v_i_10_, v_h__1_11_, v_h__2_12_);
lean_dec(v_i_10_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_MapIdx_0__Array_mapFinIdxM_map_match__1_splitter(lean_object* v_00_u03b1_14_, lean_object* v_as_15_, lean_object* v_j_16_, lean_object* v_motive_17_, lean_object* v_i_18_, lean_object* v_inv_19_, lean_object* v_h__1_20_, lean_object* v_h__2_21_){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = l___private_Init_Data_Array_MapIdx_0__Array_mapFinIdxM_map_match__1_splitter___redArg(v_i_18_, v_h__1_20_, v_h__2_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_MapIdx_0__Array_mapFinIdxM_map_match__1_splitter___boxed(lean_object* v_00_u03b1_23_, lean_object* v_as_24_, lean_object* v_j_25_, lean_object* v_motive_26_, lean_object* v_i_27_, lean_object* v_inv_28_, lean_object* v_h__1_29_, lean_object* v_h__2_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l___private_Init_Data_Array_MapIdx_0__Array_mapFinIdxM_map_match__1_splitter(v_00_u03b1_23_, v_as_24_, v_j_25_, v_motive_26_, v_i_27_, v_inv_28_, v_h__1_29_, v_h__2_30_);
lean_dec(v_i_27_);
lean_dec(v_j_25_);
lean_dec_ref(v_as_24_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_MapIdx_0__List_mapFinIdx_go_match__1_splitter___redArg(lean_object* v_x_32_, lean_object* v_x_33_, lean_object* v_h__1_34_, lean_object* v_h__2_35_){
_start:
{
if (lean_obj_tag(v_x_32_) == 0)
{
lean_object* v___x_36_; 
lean_dec(v_h__2_35_);
v___x_36_ = lean_apply_2(v_h__1_34_, v_x_33_, lean_box(0));
return v___x_36_;
}
else
{
lean_object* v_head_37_; lean_object* v_tail_38_; lean_object* v___x_39_; 
lean_dec(v_h__1_34_);
v_head_37_ = lean_ctor_get(v_x_32_, 0);
lean_inc(v_head_37_);
v_tail_38_ = lean_ctor_get(v_x_32_, 1);
lean_inc(v_tail_38_);
lean_dec_ref(v_x_32_);
v___x_39_ = lean_apply_4(v_h__2_35_, v_head_37_, v_tail_38_, v_x_33_, lean_box(0));
return v___x_39_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_MapIdx_0__List_mapFinIdx_go_match__1_splitter(lean_object* v_00_u03b1_40_, lean_object* v_00_u03b2_41_, lean_object* v_as_42_, lean_object* v_motive_43_, lean_object* v_x_44_, lean_object* v_x_45_, lean_object* v_x_46_, lean_object* v_h__1_47_, lean_object* v_h__2_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = l___private_Init_Data_Array_MapIdx_0__List_mapFinIdx_go_match__1_splitter___redArg(v_x_44_, v_x_45_, v_h__1_47_, v_h__2_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_MapIdx_0__List_mapFinIdx_go_match__1_splitter___boxed(lean_object* v_00_u03b1_50_, lean_object* v_00_u03b2_51_, lean_object* v_as_52_, lean_object* v_motive_53_, lean_object* v_x_54_, lean_object* v_x_55_, lean_object* v_x_56_, lean_object* v_h__1_57_, lean_object* v_h__2_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l___private_Init_Data_Array_MapIdx_0__List_mapFinIdx_go_match__1_splitter(v_00_u03b1_50_, v_00_u03b2_51_, v_as_52_, v_motive_53_, v_x_54_, v_x_55_, v_x_56_, v_h__1_57_, v_h__2_58_);
lean_dec(v_as_52_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_MapIdx_0__List_mapIdx_go_match__1_splitter___redArg(lean_object* v_x_60_, lean_object* v_x_61_, lean_object* v_h__1_62_, lean_object* v_h__2_63_){
_start:
{
if (lean_obj_tag(v_x_60_) == 0)
{
lean_object* v___x_64_; 
lean_dec(v_h__2_63_);
v___x_64_ = lean_apply_1(v_h__1_62_, v_x_61_);
return v___x_64_;
}
else
{
lean_object* v_head_65_; lean_object* v_tail_66_; lean_object* v___x_67_; 
lean_dec(v_h__1_62_);
v_head_65_ = lean_ctor_get(v_x_60_, 0);
lean_inc(v_head_65_);
v_tail_66_ = lean_ctor_get(v_x_60_, 1);
lean_inc(v_tail_66_);
lean_dec_ref(v_x_60_);
v___x_67_ = lean_apply_3(v_h__2_63_, v_head_65_, v_tail_66_, v_x_61_);
return v___x_67_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_MapIdx_0__List_mapIdx_go_match__1_splitter(lean_object* v_00_u03b1_68_, lean_object* v_00_u03b2_69_, lean_object* v_motive_70_, lean_object* v_x_71_, lean_object* v_x_72_, lean_object* v_h__1_73_, lean_object* v_h__2_74_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = l___private_Init_Data_Array_MapIdx_0__List_mapIdx_go_match__1_splitter___redArg(v_x_71_, v_x_72_, v_h__1_73_, v_h__2_74_);
return v___x_75_;
}
}
lean_object* runtime_initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_MapIdx(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_MapIdx(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_OfFn(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Array_MapIdx(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_MapIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_MapIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_OfFn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Array_MapIdx(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_List_MapIdx(uint8_t builtin);
lean_object* initialize_Init_Data_List_MapIdx(uint8_t builtin);
lean_object* initialize_Init_Data_Array_OfFn(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Array_MapIdx(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_MapIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_MapIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_OfFn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_MapIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Array_MapIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Array_MapIdx(builtin);
}
#ifdef __cplusplus
}
#endif

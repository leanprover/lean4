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
lean_object* v_zero_22_; uint8_t v_isZero_23_; 
v_zero_22_ = lean_unsigned_to_nat(0u);
v_isZero_23_ = lean_nat_dec_eq(v_i_18_, v_zero_22_);
if (v_isZero_23_ == 1)
{
lean_object* v___x_24_; 
lean_dec(v_h__2_21_);
v___x_24_ = lean_apply_1(v_h__1_20_, lean_box(0));
return v___x_24_;
}
else
{
lean_object* v_one_25_; lean_object* v_n_26_; lean_object* v___x_27_; 
lean_dec(v_h__1_20_);
v_one_25_ = lean_unsigned_to_nat(1u);
v_n_26_ = lean_nat_sub(v_i_18_, v_one_25_);
v___x_27_ = lean_apply_2(v_h__2_21_, v_n_26_, lean_box(0));
return v___x_27_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_MapIdx_0__Array_mapFinIdxM_map_match__1_splitter___boxed(lean_object* v_00_u03b1_28_, lean_object* v_as_29_, lean_object* v_j_30_, lean_object* v_motive_31_, lean_object* v_i_32_, lean_object* v_inv_33_, lean_object* v_h__1_34_, lean_object* v_h__2_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l___private_Init_Data_Array_MapIdx_0__Array_mapFinIdxM_map_match__1_splitter(v_00_u03b1_28_, v_as_29_, v_j_30_, v_motive_31_, v_i_32_, v_inv_33_, v_h__1_34_, v_h__2_35_);
lean_dec(v_i_32_);
lean_dec(v_j_30_);
lean_dec_ref(v_as_29_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_MapIdx_0__List_mapFinIdx_go_match__1_splitter___redArg(lean_object* v_x_37_, lean_object* v_x_38_, lean_object* v_h__1_39_, lean_object* v_h__2_40_){
_start:
{
if (lean_obj_tag(v_x_37_) == 0)
{
lean_object* v___x_41_; 
lean_dec(v_h__2_40_);
v___x_41_ = lean_apply_2(v_h__1_39_, v_x_38_, lean_box(0));
return v___x_41_;
}
else
{
lean_object* v_head_42_; lean_object* v_tail_43_; lean_object* v___x_44_; 
lean_dec(v_h__1_39_);
v_head_42_ = lean_ctor_get(v_x_37_, 0);
lean_inc(v_head_42_);
v_tail_43_ = lean_ctor_get(v_x_37_, 1);
lean_inc(v_tail_43_);
lean_dec_ref(v_x_37_);
v___x_44_ = lean_apply_4(v_h__2_40_, v_head_42_, v_tail_43_, v_x_38_, lean_box(0));
return v___x_44_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_MapIdx_0__List_mapFinIdx_go_match__1_splitter(lean_object* v_00_u03b1_45_, lean_object* v_00_u03b2_46_, lean_object* v_as_47_, lean_object* v_motive_48_, lean_object* v_x_49_, lean_object* v_x_50_, lean_object* v_x_51_, lean_object* v_h__1_52_, lean_object* v_h__2_53_){
_start:
{
if (lean_obj_tag(v_x_49_) == 0)
{
lean_object* v___x_54_; 
lean_dec(v_h__2_53_);
v___x_54_ = lean_apply_2(v_h__1_52_, v_x_50_, lean_box(0));
return v___x_54_;
}
else
{
lean_object* v_head_55_; lean_object* v_tail_56_; lean_object* v___x_57_; 
lean_dec(v_h__1_52_);
v_head_55_ = lean_ctor_get(v_x_49_, 0);
lean_inc(v_head_55_);
v_tail_56_ = lean_ctor_get(v_x_49_, 1);
lean_inc(v_tail_56_);
lean_dec_ref(v_x_49_);
v___x_57_ = lean_apply_4(v_h__2_53_, v_head_55_, v_tail_56_, v_x_50_, lean_box(0));
return v___x_57_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_MapIdx_0__List_mapFinIdx_go_match__1_splitter___boxed(lean_object* v_00_u03b1_58_, lean_object* v_00_u03b2_59_, lean_object* v_as_60_, lean_object* v_motive_61_, lean_object* v_x_62_, lean_object* v_x_63_, lean_object* v_x_64_, lean_object* v_h__1_65_, lean_object* v_h__2_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l___private_Init_Data_Array_MapIdx_0__List_mapFinIdx_go_match__1_splitter(v_00_u03b1_58_, v_00_u03b2_59_, v_as_60_, v_motive_61_, v_x_62_, v_x_63_, v_x_64_, v_h__1_65_, v_h__2_66_);
lean_dec(v_as_60_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_MapIdx_0__List_mapIdx_go_match__1_splitter___redArg(lean_object* v_x_68_, lean_object* v_x_69_, lean_object* v_h__1_70_, lean_object* v_h__2_71_){
_start:
{
if (lean_obj_tag(v_x_68_) == 0)
{
lean_object* v___x_72_; 
lean_dec(v_h__2_71_);
v___x_72_ = lean_apply_1(v_h__1_70_, v_x_69_);
return v___x_72_;
}
else
{
lean_object* v_head_73_; lean_object* v_tail_74_; lean_object* v___x_75_; 
lean_dec(v_h__1_70_);
v_head_73_ = lean_ctor_get(v_x_68_, 0);
lean_inc(v_head_73_);
v_tail_74_ = lean_ctor_get(v_x_68_, 1);
lean_inc(v_tail_74_);
lean_dec_ref(v_x_68_);
v___x_75_ = lean_apply_3(v_h__2_71_, v_head_73_, v_tail_74_, v_x_69_);
return v___x_75_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_MapIdx_0__List_mapIdx_go_match__1_splitter(lean_object* v_00_u03b1_76_, lean_object* v_00_u03b2_77_, lean_object* v_motive_78_, lean_object* v_x_79_, lean_object* v_x_80_, lean_object* v_h__1_81_, lean_object* v_h__2_82_){
_start:
{
if (lean_obj_tag(v_x_79_) == 0)
{
lean_object* v___x_83_; 
lean_dec(v_h__2_82_);
v___x_83_ = lean_apply_1(v_h__1_81_, v_x_80_);
return v___x_83_;
}
else
{
lean_object* v_head_84_; lean_object* v_tail_85_; lean_object* v___x_86_; 
lean_dec(v_h__1_81_);
v_head_84_ = lean_ctor_get(v_x_79_, 0);
lean_inc(v_head_84_);
v_tail_85_ = lean_ctor_get(v_x_79_, 1);
lean_inc(v_tail_85_);
lean_dec_ref(v_x_79_);
v___x_86_ = lean_apply_3(v_h__2_82_, v_head_84_, v_tail_85_, v_x_80_);
return v___x_86_;
}
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

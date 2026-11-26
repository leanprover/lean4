// Lean compiler output
// Module: Init.Data.Vector.MapIdx
// Imports: import all Init.Data.Array.Basic import all Init.Data.Vector.Basic public import Init.Data.Vector.Attach import Init.ByCases
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
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_MapIdx_0__Vector_mapFinIdxM_map_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_MapIdx_0__Vector_mapFinIdxM_map_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_MapIdx_0__Vector_mapFinIdxM_map_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_MapIdx_0__Vector_mapFinIdxM_map_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_MapIdx_0__Array_mapFinIdxM_map_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_MapIdx_0__Array_mapFinIdxM_map_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_MapIdx_0__Array_mapFinIdxM_map_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_MapIdx_0__Array_mapFinIdxM_map_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_MapIdx_0__Vector_mapFinIdxM_map_match__1_splitter___redArg(lean_object* v_i_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_MapIdx_0__Vector_mapFinIdxM_map_match__1_splitter___redArg___boxed(lean_object* v_i_10_, lean_object* v_h__1_11_, lean_object* v_h__2_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l___private_Init_Data_Vector_MapIdx_0__Vector_mapFinIdxM_map_match__1_splitter___redArg(v_i_10_, v_h__1_11_, v_h__2_12_);
lean_dec(v_i_10_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_MapIdx_0__Vector_mapFinIdxM_map_match__1_splitter(lean_object* v_n_14_, lean_object* v_j_15_, lean_object* v_motive_16_, lean_object* v_i_17_, lean_object* v_inv_18_, lean_object* v_h__1_19_, lean_object* v_h__2_20_){
_start:
{
lean_object* v_zero_21_; uint8_t v_isZero_22_; 
v_zero_21_ = lean_unsigned_to_nat(0u);
v_isZero_22_ = lean_nat_dec_eq(v_i_17_, v_zero_21_);
if (v_isZero_22_ == 1)
{
lean_object* v___x_23_; 
lean_dec(v_h__2_20_);
v___x_23_ = lean_apply_1(v_h__1_19_, lean_box(0));
return v___x_23_;
}
else
{
lean_object* v_one_24_; lean_object* v_n_25_; lean_object* v___x_26_; 
lean_dec(v_h__1_19_);
v_one_24_ = lean_unsigned_to_nat(1u);
v_n_25_ = lean_nat_sub(v_i_17_, v_one_24_);
v___x_26_ = lean_apply_2(v_h__2_20_, v_n_25_, lean_box(0));
return v___x_26_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_MapIdx_0__Vector_mapFinIdxM_map_match__1_splitter___boxed(lean_object* v_n_27_, lean_object* v_j_28_, lean_object* v_motive_29_, lean_object* v_i_30_, lean_object* v_inv_31_, lean_object* v_h__1_32_, lean_object* v_h__2_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l___private_Init_Data_Vector_MapIdx_0__Vector_mapFinIdxM_map_match__1_splitter(v_n_27_, v_j_28_, v_motive_29_, v_i_30_, v_inv_31_, v_h__1_32_, v_h__2_33_);
lean_dec(v_i_30_);
lean_dec(v_j_28_);
lean_dec(v_n_27_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_MapIdx_0__Array_mapFinIdxM_map_match__1_splitter___redArg(lean_object* v_i_35_, lean_object* v_h__1_36_, lean_object* v_h__2_37_){
_start:
{
lean_object* v_zero_38_; uint8_t v_isZero_39_; 
v_zero_38_ = lean_unsigned_to_nat(0u);
v_isZero_39_ = lean_nat_dec_eq(v_i_35_, v_zero_38_);
if (v_isZero_39_ == 1)
{
lean_object* v___x_40_; 
lean_dec(v_h__2_37_);
v___x_40_ = lean_apply_1(v_h__1_36_, lean_box(0));
return v___x_40_;
}
else
{
lean_object* v_one_41_; lean_object* v_n_42_; lean_object* v___x_43_; 
lean_dec(v_h__1_36_);
v_one_41_ = lean_unsigned_to_nat(1u);
v_n_42_ = lean_nat_sub(v_i_35_, v_one_41_);
v___x_43_ = lean_apply_2(v_h__2_37_, v_n_42_, lean_box(0));
return v___x_43_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_MapIdx_0__Array_mapFinIdxM_map_match__1_splitter___redArg___boxed(lean_object* v_i_44_, lean_object* v_h__1_45_, lean_object* v_h__2_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l___private_Init_Data_Vector_MapIdx_0__Array_mapFinIdxM_map_match__1_splitter___redArg(v_i_44_, v_h__1_45_, v_h__2_46_);
lean_dec(v_i_44_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_MapIdx_0__Array_mapFinIdxM_map_match__1_splitter(lean_object* v_00_u03b1_48_, lean_object* v_as_49_, lean_object* v_j_50_, lean_object* v_motive_51_, lean_object* v_i_52_, lean_object* v_inv_53_, lean_object* v_h__1_54_, lean_object* v_h__2_55_){
_start:
{
lean_object* v_zero_56_; uint8_t v_isZero_57_; 
v_zero_56_ = lean_unsigned_to_nat(0u);
v_isZero_57_ = lean_nat_dec_eq(v_i_52_, v_zero_56_);
if (v_isZero_57_ == 1)
{
lean_object* v___x_58_; 
lean_dec(v_h__2_55_);
v___x_58_ = lean_apply_1(v_h__1_54_, lean_box(0));
return v___x_58_;
}
else
{
lean_object* v_one_59_; lean_object* v_n_60_; lean_object* v___x_61_; 
lean_dec(v_h__1_54_);
v_one_59_ = lean_unsigned_to_nat(1u);
v_n_60_ = lean_nat_sub(v_i_52_, v_one_59_);
v___x_61_ = lean_apply_2(v_h__2_55_, v_n_60_, lean_box(0));
return v___x_61_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_MapIdx_0__Array_mapFinIdxM_map_match__1_splitter___boxed(lean_object* v_00_u03b1_62_, lean_object* v_as_63_, lean_object* v_j_64_, lean_object* v_motive_65_, lean_object* v_i_66_, lean_object* v_inv_67_, lean_object* v_h__1_68_, lean_object* v_h__2_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l___private_Init_Data_Vector_MapIdx_0__Array_mapFinIdxM_map_match__1_splitter(v_00_u03b1_62_, v_as_63_, v_j_64_, v_motive_65_, v_i_66_, v_inv_67_, v_h__1_68_, v_h__2_69_);
lean_dec(v_i_66_);
lean_dec(v_j_64_);
lean_dec_ref(v_as_63_);
return v_res_70_;
}
}
lean_object* runtime_initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Vector_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Vector_Attach(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Vector_MapIdx(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Vector_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Vector_MapIdx(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Vector_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Vector_Attach(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Vector_MapIdx(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Vector_MapIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Vector_MapIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Vector_MapIdx(builtin);
}
#ifdef __cplusplus
}
#endif

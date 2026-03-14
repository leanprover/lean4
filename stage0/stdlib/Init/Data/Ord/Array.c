// Lean compiler output
// Module: Init.Data.Ord.Array
// Imports: public import Init.Data.Ord.Basic import Init.Omega import Init.ByCases import Init.Data.Array.Basic import Init.WFTactics
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Ord_Array_0__Array_compareLex_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Array_0__Array_compareLex_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Ord_Array_0__Array_compareLex_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Array_0__Array_compareLex_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Array_0__Array_compareLex_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Array_0__Array_compareLex_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Array_0__Array_compareLex_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Array_0__Array_compareLex_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_compareLex___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_compareLex___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_compareLex(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_compareLex___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instOrd___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_instOrd(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Ord_Array_0__Array_compareLex_go___redArg(lean_object* v_cmp_1_, lean_object* v_a_u2081_2_, lean_object* v_a_u2082_3_, lean_object* v_i_4_){
_start:
{
lean_object* v___x_5_; uint8_t v___x_6_; 
v___x_5_ = lean_array_get_size(v_a_u2081_2_);
v___x_6_ = lean_nat_dec_le(v___x_5_, v_i_4_);
if (v___x_6_ == 0)
{
lean_object* v___x_7_; uint8_t v___x_8_; 
v___x_7_ = lean_array_get_size(v_a_u2082_3_);
v___x_8_ = lean_nat_dec_le(v___x_7_, v_i_4_);
if (v___x_8_ == 0)
{
lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; uint8_t v___x_12_; 
v___x_9_ = lean_array_fget_borrowed(v_a_u2081_2_, v_i_4_);
v___x_10_ = lean_array_fget_borrowed(v_a_u2082_3_, v_i_4_);
lean_inc_ref(v_cmp_1_);
lean_inc(v___x_10_);
lean_inc(v___x_9_);
v___x_11_ = lean_apply_2(v_cmp_1_, v___x_9_, v___x_10_);
v___x_12_ = lean_unbox(v___x_11_);
if (v___x_12_ == 1)
{
lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_13_ = lean_unsigned_to_nat(1u);
v___x_14_ = lean_nat_add(v_i_4_, v___x_13_);
lean_dec(v_i_4_);
v_i_4_ = v___x_14_;
goto _start;
}
else
{
uint8_t v___x_16_; 
lean_dec(v_i_4_);
lean_dec_ref(v_cmp_1_);
v___x_16_ = lean_unbox(v___x_11_);
return v___x_16_;
}
}
else
{
uint8_t v___x_17_; 
lean_dec(v_i_4_);
lean_dec_ref(v_cmp_1_);
v___x_17_ = 2;
return v___x_17_;
}
}
else
{
lean_object* v___x_18_; uint8_t v___x_19_; 
lean_dec_ref(v_cmp_1_);
v___x_18_ = lean_array_get_size(v_a_u2082_3_);
v___x_19_ = lean_nat_dec_le(v___x_18_, v_i_4_);
lean_dec(v_i_4_);
if (v___x_19_ == 0)
{
uint8_t v___x_20_; 
v___x_20_ = 0;
return v___x_20_;
}
else
{
uint8_t v___x_21_; 
v___x_21_ = 1;
return v___x_21_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Array_0__Array_compareLex_go___redArg___boxed(lean_object* v_cmp_22_, lean_object* v_a_u2081_23_, lean_object* v_a_u2082_24_, lean_object* v_i_25_){
_start:
{
uint8_t v_res_26_; lean_object* v_r_27_; 
v_res_26_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go___redArg(v_cmp_22_, v_a_u2081_23_, v_a_u2082_24_, v_i_25_);
lean_dec_ref(v_a_u2082_24_);
lean_dec_ref(v_a_u2081_23_);
v_r_27_ = lean_box(v_res_26_);
return v_r_27_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Ord_Array_0__Array_compareLex_go(lean_object* v_00_u03b1_28_, lean_object* v_cmp_29_, lean_object* v_a_u2081_30_, lean_object* v_a_u2082_31_, lean_object* v_i_32_){
_start:
{
uint8_t v___x_33_; 
v___x_33_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go___redArg(v_cmp_29_, v_a_u2081_30_, v_a_u2082_31_, v_i_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Array_0__Array_compareLex_go___boxed(lean_object* v_00_u03b1_34_, lean_object* v_cmp_35_, lean_object* v_a_u2081_36_, lean_object* v_a_u2082_37_, lean_object* v_i_38_){
_start:
{
uint8_t v_res_39_; lean_object* v_r_40_; 
v_res_39_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go(v_00_u03b1_34_, v_cmp_35_, v_a_u2081_36_, v_a_u2082_37_, v_i_38_);
lean_dec_ref(v_a_u2082_37_);
lean_dec_ref(v_a_u2081_36_);
v_r_40_ = lean_box(v_res_39_);
return v_r_40_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Array_0__Array_compareLex_match__1_splitter___redArg(uint8_t v_x_41_, lean_object* v_h__1_42_, lean_object* v_h__2_43_, lean_object* v_h__3_44_){
_start:
{
switch(v_x_41_)
{
case 0:
{
lean_object* v___x_45_; lean_object* v___x_46_; 
lean_dec(v_h__3_44_);
lean_dec(v_h__2_43_);
v___x_45_ = lean_box(0);
v___x_46_ = lean_apply_1(v_h__1_42_, v___x_45_);
return v___x_46_;
}
case 1:
{
lean_object* v___x_47_; lean_object* v___x_48_; 
lean_dec(v_h__3_44_);
lean_dec(v_h__1_42_);
v___x_47_ = lean_box(0);
v___x_48_ = lean_apply_1(v_h__2_43_, v___x_47_);
return v___x_48_;
}
default: 
{
lean_object* v___x_49_; lean_object* v___x_50_; 
lean_dec(v_h__2_43_);
lean_dec(v_h__1_42_);
v___x_49_ = lean_box(0);
v___x_50_ = lean_apply_1(v_h__3_44_, v___x_49_);
return v___x_50_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Array_0__Array_compareLex_match__1_splitter___redArg___boxed(lean_object* v_x_51_, lean_object* v_h__1_52_, lean_object* v_h__2_53_, lean_object* v_h__3_54_){
_start:
{
uint8_t v_x_30__boxed_55_; lean_object* v_res_56_; 
v_x_30__boxed_55_ = lean_unbox(v_x_51_);
v_res_56_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_match__1_splitter___redArg(v_x_30__boxed_55_, v_h__1_52_, v_h__2_53_, v_h__3_54_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Array_0__Array_compareLex_match__1_splitter(lean_object* v_motive_57_, uint8_t v_x_58_, lean_object* v_h__1_59_, lean_object* v_h__2_60_, lean_object* v_h__3_61_){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_match__1_splitter___redArg(v_x_58_, v_h__1_59_, v_h__2_60_, v_h__3_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Array_0__Array_compareLex_match__1_splitter___boxed(lean_object* v_motive_63_, lean_object* v_x_64_, lean_object* v_h__1_65_, lean_object* v_h__2_66_, lean_object* v_h__3_67_){
_start:
{
uint8_t v_x_45__boxed_68_; lean_object* v_res_69_; 
v_x_45__boxed_68_ = lean_unbox(v_x_64_);
v_res_69_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_match__1_splitter(v_motive_63_, v_x_45__boxed_68_, v_h__1_65_, v_h__2_66_, v_h__3_67_);
return v_res_69_;
}
}
LEAN_EXPORT uint8_t l_Array_compareLex___redArg(lean_object* v_cmp_70_, lean_object* v_a_u2081_71_, lean_object* v_a_u2082_72_){
_start:
{
lean_object* v___x_73_; uint8_t v___x_74_; 
v___x_73_ = lean_unsigned_to_nat(0u);
v___x_74_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go___redArg(v_cmp_70_, v_a_u2081_71_, v_a_u2082_72_, v___x_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Array_compareLex___redArg___boxed(lean_object* v_cmp_75_, lean_object* v_a_u2081_76_, lean_object* v_a_u2082_77_){
_start:
{
uint8_t v_res_78_; lean_object* v_r_79_; 
v_res_78_ = l_Array_compareLex___redArg(v_cmp_75_, v_a_u2081_76_, v_a_u2082_77_);
lean_dec_ref(v_a_u2082_77_);
lean_dec_ref(v_a_u2081_76_);
v_r_79_ = lean_box(v_res_78_);
return v_r_79_;
}
}
LEAN_EXPORT uint8_t l_Array_compareLex(lean_object* v_00_u03b1_80_, lean_object* v_cmp_81_, lean_object* v_a_u2081_82_, lean_object* v_a_u2082_83_){
_start:
{
uint8_t v___x_84_; 
v___x_84_ = l_Array_compareLex___redArg(v_cmp_81_, v_a_u2081_82_, v_a_u2082_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Array_compareLex___boxed(lean_object* v_00_u03b1_85_, lean_object* v_cmp_86_, lean_object* v_a_u2081_87_, lean_object* v_a_u2082_88_){
_start:
{
uint8_t v_res_89_; lean_object* v_r_90_; 
v_res_89_ = l_Array_compareLex(v_00_u03b1_85_, v_cmp_86_, v_a_u2081_87_, v_a_u2082_88_);
lean_dec_ref(v_a_u2082_88_);
lean_dec_ref(v_a_u2081_87_);
v_r_90_ = lean_box(v_res_89_);
return v_r_90_;
}
}
LEAN_EXPORT lean_object* l_Array_instOrd___redArg(lean_object* v_inst_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = lean_alloc_closure((void*)(l_Array_compareLex___boxed), 4, 2);
lean_closure_set(v___x_92_, 0, lean_box(0));
lean_closure_set(v___x_92_, 1, v_inst_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Array_instOrd(lean_object* v_00_u03b1_93_, lean_object* v_inst_94_){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = lean_alloc_closure((void*)(l_Array_compareLex___boxed), 4, 2);
lean_closure_set(v___x_95_, 0, lean_box(0));
lean_closure_set(v___x_95_, 1, v_inst_94_);
return v___x_95_;
}
}
lean_object* runtime_initialize_Init_Data_Ord_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_WFTactics(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Ord_Array(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Ord_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Ord_Array(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Ord_Basic(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* initialize_Init_WFTactics(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Ord_Array(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Ord_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Ord_Array(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Ord_Array(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Ord_Array(builtin);
}
#ifdef __cplusplus
}
#endif

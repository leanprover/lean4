// Lean compiler output
// Module: Init.Data.Array.GetLit
// Imports: public import Init.GetElem import Init.Data.Array.Basic
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
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Array_getLit___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_getLit___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_getLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_getLit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toListLitAux___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toListLitAux___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toListLitAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toListLitAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toArrayLit___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toArrayLit___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toArrayLit(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toArrayLit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_GetLit_0__List_take_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_GetLit_0__List_take_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_GetLit_0__List_take_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_GetLit_0__List_take_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_GetLit_0__Array_toListLitAux_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_GetLit_0__Array_toListLitAux_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_GetLit_0__Array_toListLitAux_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_GetLit_0__Array_toListLitAux_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_getLit___redArg(lean_object* v_xs_1_, lean_object* v_i_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_array_fget_borrowed(v_xs_1_, v_i_2_);
lean_inc(v___x_3_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Array_getLit___redArg___boxed(lean_object* v_xs_4_, lean_object* v_i_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l_Array_getLit___redArg(v_xs_4_, v_i_5_);
lean_dec(v_i_5_);
lean_dec_ref(v_xs_4_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Array_getLit(lean_object* v_00_u03b1_7_, lean_object* v_n_8_, lean_object* v_xs_9_, lean_object* v_i_10_, lean_object* v_h_u2081_11_, lean_object* v_h_u2082_12_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = lean_array_fget_borrowed(v_xs_9_, v_i_10_);
lean_inc(v___x_13_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_Array_getLit___boxed(lean_object* v_00_u03b1_14_, lean_object* v_n_15_, lean_object* v_xs_16_, lean_object* v_i_17_, lean_object* v_h_u2081_18_, lean_object* v_h_u2082_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Array_getLit(v_00_u03b1_14_, v_n_15_, v_xs_16_, v_i_17_, v_h_u2081_18_, v_h_u2082_19_);
lean_dec(v_i_17_);
lean_dec_ref(v_xs_16_);
lean_dec(v_n_15_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Array_toListLitAux___redArg(lean_object* v_xs_21_, lean_object* v_x_22_, lean_object* v_x_23_){
_start:
{
lean_object* v_zero_24_; uint8_t v_isZero_25_; 
v_zero_24_ = lean_unsigned_to_nat(0u);
v_isZero_25_ = lean_nat_dec_eq(v_x_22_, v_zero_24_);
if (v_isZero_25_ == 1)
{
lean_dec(v_x_22_);
return v_x_23_;
}
else
{
lean_object* v_one_26_; lean_object* v_n_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v_one_26_ = lean_unsigned_to_nat(1u);
v_n_27_ = lean_nat_sub(v_x_22_, v_one_26_);
lean_dec(v_x_22_);
v___x_28_ = lean_array_fget_borrowed(v_xs_21_, v_n_27_);
lean_inc(v___x_28_);
v___x_29_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_29_, 0, v___x_28_);
lean_ctor_set(v___x_29_, 1, v_x_23_);
v_x_22_ = v_n_27_;
v_x_23_ = v___x_29_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_toListLitAux___redArg___boxed(lean_object* v_xs_31_, lean_object* v_x_32_, lean_object* v_x_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Array_toListLitAux___redArg(v_xs_31_, v_x_32_, v_x_33_);
lean_dec_ref(v_xs_31_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Array_toListLitAux(lean_object* v_00_u03b1_35_, lean_object* v_xs_36_, lean_object* v_n_37_, lean_object* v_hsz_38_, lean_object* v_x_39_, lean_object* v_x_40_, lean_object* v_x_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Array_toListLitAux___redArg(v_xs_36_, v_x_39_, v_x_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Array_toListLitAux___boxed(lean_object* v_00_u03b1_43_, lean_object* v_xs_44_, lean_object* v_n_45_, lean_object* v_hsz_46_, lean_object* v_x_47_, lean_object* v_x_48_, lean_object* v_x_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Array_toListLitAux(v_00_u03b1_43_, v_xs_44_, v_n_45_, v_hsz_46_, v_x_47_, v_x_48_, v_x_49_);
lean_dec(v_n_45_);
lean_dec_ref(v_xs_44_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Array_toArrayLit___redArg(lean_object* v_xs_51_, lean_object* v_n_52_){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_53_ = lean_box(0);
v___x_54_ = l_Array_toListLitAux___redArg(v_xs_51_, v_n_52_, v___x_53_);
v___x_55_ = lean_array_mk(v___x_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Array_toArrayLit___redArg___boxed(lean_object* v_xs_56_, lean_object* v_n_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Array_toArrayLit___redArg(v_xs_56_, v_n_57_);
lean_dec_ref(v_xs_56_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l_Array_toArrayLit(lean_object* v_00_u03b1_59_, lean_object* v_xs_60_, lean_object* v_n_61_, lean_object* v_hsz_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = l_Array_toArrayLit___redArg(v_xs_60_, v_n_61_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Array_toArrayLit___boxed(lean_object* v_00_u03b1_64_, lean_object* v_xs_65_, lean_object* v_n_66_, lean_object* v_hsz_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l_Array_toArrayLit(v_00_u03b1_64_, v_xs_65_, v_n_66_, v_hsz_67_);
lean_dec_ref(v_xs_65_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_GetLit_0__List_take_match__1_splitter___redArg(lean_object* v_x_69_, lean_object* v_x_70_, lean_object* v_h__1_71_, lean_object* v_h__2_72_, lean_object* v_h__3_73_){
_start:
{
lean_object* v_zero_74_; uint8_t v_isZero_75_; 
v_zero_74_ = lean_unsigned_to_nat(0u);
v_isZero_75_ = lean_nat_dec_eq(v_x_69_, v_zero_74_);
if (v_isZero_75_ == 1)
{
lean_object* v___x_76_; 
lean_dec(v_h__3_73_);
lean_dec(v_h__2_72_);
v___x_76_ = lean_apply_1(v_h__1_71_, v_x_70_);
return v___x_76_;
}
else
{
lean_object* v_one_77_; lean_object* v_n_78_; 
lean_dec(v_h__1_71_);
v_one_77_ = lean_unsigned_to_nat(1u);
v_n_78_ = lean_nat_sub(v_x_69_, v_one_77_);
if (lean_obj_tag(v_x_70_) == 0)
{
lean_object* v___x_79_; 
lean_dec(v_h__3_73_);
v___x_79_ = lean_apply_1(v_h__2_72_, v_n_78_);
return v___x_79_;
}
else
{
lean_object* v_head_80_; lean_object* v_tail_81_; lean_object* v___x_82_; 
lean_dec(v_h__2_72_);
v_head_80_ = lean_ctor_get(v_x_70_, 0);
lean_inc(v_head_80_);
v_tail_81_ = lean_ctor_get(v_x_70_, 1);
lean_inc(v_tail_81_);
lean_dec_ref(v_x_70_);
v___x_82_ = lean_apply_3(v_h__3_73_, v_n_78_, v_head_80_, v_tail_81_);
return v___x_82_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_GetLit_0__List_take_match__1_splitter___redArg___boxed(lean_object* v_x_83_, lean_object* v_x_84_, lean_object* v_h__1_85_, lean_object* v_h__2_86_, lean_object* v_h__3_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l___private_Init_Data_Array_GetLit_0__List_take_match__1_splitter___redArg(v_x_83_, v_x_84_, v_h__1_85_, v_h__2_86_, v_h__3_87_);
lean_dec(v_x_83_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_GetLit_0__List_take_match__1_splitter(lean_object* v_00_u03b1_89_, lean_object* v_motive_90_, lean_object* v_x_91_, lean_object* v_x_92_, lean_object* v_h__1_93_, lean_object* v_h__2_94_, lean_object* v_h__3_95_){
_start:
{
lean_object* v_zero_96_; uint8_t v_isZero_97_; 
v_zero_96_ = lean_unsigned_to_nat(0u);
v_isZero_97_ = lean_nat_dec_eq(v_x_91_, v_zero_96_);
if (v_isZero_97_ == 1)
{
lean_object* v___x_98_; 
lean_dec(v_h__3_95_);
lean_dec(v_h__2_94_);
v___x_98_ = lean_apply_1(v_h__1_93_, v_x_92_);
return v___x_98_;
}
else
{
lean_object* v_one_99_; lean_object* v_n_100_; 
lean_dec(v_h__1_93_);
v_one_99_ = lean_unsigned_to_nat(1u);
v_n_100_ = lean_nat_sub(v_x_91_, v_one_99_);
if (lean_obj_tag(v_x_92_) == 0)
{
lean_object* v___x_101_; 
lean_dec(v_h__3_95_);
v___x_101_ = lean_apply_1(v_h__2_94_, v_n_100_);
return v___x_101_;
}
else
{
lean_object* v_head_102_; lean_object* v_tail_103_; lean_object* v___x_104_; 
lean_dec(v_h__2_94_);
v_head_102_ = lean_ctor_get(v_x_92_, 0);
lean_inc(v_head_102_);
v_tail_103_ = lean_ctor_get(v_x_92_, 1);
lean_inc(v_tail_103_);
lean_dec_ref(v_x_92_);
v___x_104_ = lean_apply_3(v_h__3_95_, v_n_100_, v_head_102_, v_tail_103_);
return v___x_104_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_GetLit_0__List_take_match__1_splitter___boxed(lean_object* v_00_u03b1_105_, lean_object* v_motive_106_, lean_object* v_x_107_, lean_object* v_x_108_, lean_object* v_h__1_109_, lean_object* v_h__2_110_, lean_object* v_h__3_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l___private_Init_Data_Array_GetLit_0__List_take_match__1_splitter(v_00_u03b1_105_, v_motive_106_, v_x_107_, v_x_108_, v_h__1_109_, v_h__2_110_, v_h__3_111_);
lean_dec(v_x_107_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_GetLit_0__Array_toListLitAux_match__1_splitter___redArg(lean_object* v_x_113_, lean_object* v_x_114_, lean_object* v_h__1_115_, lean_object* v_h__2_116_){
_start:
{
lean_object* v_zero_117_; uint8_t v_isZero_118_; 
v_zero_117_ = lean_unsigned_to_nat(0u);
v_isZero_118_ = lean_nat_dec_eq(v_x_113_, v_zero_117_);
if (v_isZero_118_ == 1)
{
lean_object* v___x_119_; 
lean_dec(v_h__2_116_);
v___x_119_ = lean_apply_2(v_h__1_115_, lean_box(0), v_x_114_);
return v___x_119_;
}
else
{
lean_object* v_one_120_; lean_object* v_n_121_; lean_object* v___x_122_; 
lean_dec(v_h__1_115_);
v_one_120_ = lean_unsigned_to_nat(1u);
v_n_121_ = lean_nat_sub(v_x_113_, v_one_120_);
v___x_122_ = lean_apply_3(v_h__2_116_, v_n_121_, lean_box(0), v_x_114_);
return v___x_122_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_GetLit_0__Array_toListLitAux_match__1_splitter___redArg___boxed(lean_object* v_x_123_, lean_object* v_x_124_, lean_object* v_h__1_125_, lean_object* v_h__2_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l___private_Init_Data_Array_GetLit_0__Array_toListLitAux_match__1_splitter___redArg(v_x_123_, v_x_124_, v_h__1_125_, v_h__2_126_);
lean_dec(v_x_123_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_GetLit_0__Array_toListLitAux_match__1_splitter(lean_object* v_00_u03b1_128_, lean_object* v_xs_129_, lean_object* v_motive_130_, lean_object* v_x_131_, lean_object* v_x_132_, lean_object* v_x_133_, lean_object* v_h__1_134_, lean_object* v_h__2_135_){
_start:
{
lean_object* v_zero_136_; uint8_t v_isZero_137_; 
v_zero_136_ = lean_unsigned_to_nat(0u);
v_isZero_137_ = lean_nat_dec_eq(v_x_131_, v_zero_136_);
if (v_isZero_137_ == 1)
{
lean_object* v___x_138_; 
lean_dec(v_h__2_135_);
v___x_138_ = lean_apply_2(v_h__1_134_, lean_box(0), v_x_133_);
return v___x_138_;
}
else
{
lean_object* v_one_139_; lean_object* v_n_140_; lean_object* v___x_141_; 
lean_dec(v_h__1_134_);
v_one_139_ = lean_unsigned_to_nat(1u);
v_n_140_ = lean_nat_sub(v_x_131_, v_one_139_);
v___x_141_ = lean_apply_3(v_h__2_135_, v_n_140_, lean_box(0), v_x_133_);
return v___x_141_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_GetLit_0__Array_toListLitAux_match__1_splitter___boxed(lean_object* v_00_u03b1_142_, lean_object* v_xs_143_, lean_object* v_motive_144_, lean_object* v_x_145_, lean_object* v_x_146_, lean_object* v_x_147_, lean_object* v_h__1_148_, lean_object* v_h__2_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l___private_Init_Data_Array_GetLit_0__Array_toListLitAux_match__1_splitter(v_00_u03b1_142_, v_xs_143_, v_motive_144_, v_x_145_, v_x_146_, v_x_147_, v_h__1_148_, v_h__2_149_);
lean_dec(v_x_145_);
lean_dec_ref(v_xs_143_);
return v_res_150_;
}
}
lean_object* runtime_initialize_Init_GetElem(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Array_GetLit(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_GetElem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Array_GetLit(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_GetElem(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Array_GetLit(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_GetElem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_GetLit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Array_GetLit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Array_GetLit(builtin);
}
#ifdef __cplusplus
}
#endif

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
uint8_t l___private_Init_Data_Ord_Array_0__Array_compareLex_go___redArg(lean_object* v_cmp_1_, lean_object* v_a_u2081_2_, lean_object* v_a_u2082_3_, lean_object* v_i_4_){
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
LEAN_EXPORT void l___private_Init_Data_Ord_Array_0__Array_compareLex_go___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_1_ = stack[0].m_obj;
lean_object* v_a_u2081_2_ = stack[1].m_obj;
lean_object* v_a_u2082_3_ = stack[2].m_obj;
lean_object* v_i_4_ = stack[3].m_obj;
uint8_t v_res_22_;
v_res_22_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go___redArg(v_cmp_1_, v_a_u2081_2_, v_a_u2082_3_, v_i_4_);
stack->m_num = v_res_22_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Array_0__Array_compareLex_go___redArg___boxed(lean_object* v_cmp_23_, lean_object* v_a_u2081_24_, lean_object* v_a_u2082_25_, lean_object* v_i_26_){
_start:
{
uint8_t v_res_27_; lean_object* v_r_28_; 
v_res_27_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go___redArg(v_cmp_23_, v_a_u2081_24_, v_a_u2082_25_, v_i_26_);
lean_dec_ref(v_a_u2082_25_);
lean_dec_ref(v_a_u2081_24_);
v_r_28_ = lean_box(v_res_27_);
return v_r_28_;
}
}
uint8_t l___private_Init_Data_Ord_Array_0__Array_compareLex_go(lean_object* v_00_u03b1_29_, lean_object* v_cmp_30_, lean_object* v_a_u2081_31_, lean_object* v_a_u2082_32_, lean_object* v_i_33_){
_start:
{
uint8_t v___x_34_; 
v___x_34_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go___redArg(v_cmp_30_, v_a_u2081_31_, v_a_u2082_32_, v_i_33_);
return v___x_34_;
}
}
LEAN_EXPORT void l___private_Init_Data_Ord_Array_0__Array_compareLex_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_30_ = stack[1].m_obj;
lean_object* v_a_u2081_31_ = stack[2].m_obj;
lean_object* v_a_u2082_32_ = stack[3].m_obj;
lean_object* v_i_33_ = stack[4].m_obj;
uint8_t v_res_35_;
v_res_35_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go(lean_box(0), v_cmp_30_, v_a_u2081_31_, v_a_u2082_32_, v_i_33_);
stack->m_num = v_res_35_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Array_0__Array_compareLex_go___boxed(lean_object* v_00_u03b1_36_, lean_object* v_cmp_37_, lean_object* v_a_u2081_38_, lean_object* v_a_u2082_39_, lean_object* v_i_40_){
_start:
{
uint8_t v_res_41_; lean_object* v_r_42_; 
v_res_41_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go(v_00_u03b1_36_, v_cmp_37_, v_a_u2081_38_, v_a_u2082_39_, v_i_40_);
lean_dec_ref(v_a_u2082_39_);
lean_dec_ref(v_a_u2081_38_);
v_r_42_ = lean_box(v_res_41_);
return v_r_42_;
}
}
lean_object* l___private_Init_Data_Ord_Array_0__Array_compareLex_match__1_splitter___redArg(uint8_t v_x_43_, lean_object* v_h__1_44_, lean_object* v_h__2_45_, lean_object* v_h__3_46_){
_start:
{
switch(v_x_43_)
{
case 0:
{
lean_object* v___x_47_; lean_object* v___x_48_; 
lean_dec(v_h__3_46_);
lean_dec(v_h__2_45_);
v___x_47_ = lean_box(0);
v___x_48_ = lean_apply_1(v_h__1_44_, v___x_47_);
return v___x_48_;
}
case 1:
{
lean_object* v___x_49_; lean_object* v___x_50_; 
lean_dec(v_h__3_46_);
lean_dec(v_h__1_44_);
v___x_49_ = lean_box(0);
v___x_50_ = lean_apply_1(v_h__2_45_, v___x_49_);
return v___x_50_;
}
default: 
{
lean_object* v___x_51_; lean_object* v___x_52_; 
lean_dec(v_h__2_45_);
lean_dec(v_h__1_44_);
v___x_51_ = lean_box(0);
v___x_52_ = lean_apply_1(v_h__3_46_, v___x_51_);
return v___x_52_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Ord_Array_0__Array_compareLex_match__1_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_43_ = stack[0].m_num;
lean_object* v_h__1_44_ = stack[1].m_obj;
lean_object* v_h__2_45_ = stack[2].m_obj;
lean_object* v_h__3_46_ = stack[3].m_obj;
lean_object* v_res_53_;
v_res_53_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_match__1_splitter___redArg(v_x_43_, v_h__1_44_, v_h__2_45_, v_h__3_46_);
stack->m_obj
 = v_res_53_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Array_0__Array_compareLex_match__1_splitter___redArg___boxed(lean_object* v_x_54_, lean_object* v_h__1_55_, lean_object* v_h__2_56_, lean_object* v_h__3_57_){
_start:
{
uint8_t v_x_33__boxed_58_; lean_object* v_res_59_; 
v_x_33__boxed_58_ = lean_unbox(v_x_54_);
v_res_59_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_match__1_splitter___redArg(v_x_33__boxed_58_, v_h__1_55_, v_h__2_56_, v_h__3_57_);
return v_res_59_;
}
}
lean_object* l___private_Init_Data_Ord_Array_0__Array_compareLex_match__1_splitter(lean_object* v_motive_60_, uint8_t v_x_61_, lean_object* v_h__1_62_, lean_object* v_h__2_63_, lean_object* v_h__3_64_){
_start:
{
switch(v_x_61_)
{
case 0:
{
lean_object* v___x_65_; lean_object* v___x_66_; 
lean_dec(v_h__3_64_);
lean_dec(v_h__2_63_);
v___x_65_ = lean_box(0);
v___x_66_ = lean_apply_1(v_h__1_62_, v___x_65_);
return v___x_66_;
}
case 1:
{
lean_object* v___x_67_; lean_object* v___x_68_; 
lean_dec(v_h__3_64_);
lean_dec(v_h__1_62_);
v___x_67_ = lean_box(0);
v___x_68_ = lean_apply_1(v_h__2_63_, v___x_67_);
return v___x_68_;
}
default: 
{
lean_object* v___x_69_; lean_object* v___x_70_; 
lean_dec(v_h__2_63_);
lean_dec(v_h__1_62_);
v___x_69_ = lean_box(0);
v___x_70_ = lean_apply_1(v_h__3_64_, v___x_69_);
return v___x_70_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Ord_Array_0__Array_compareLex_match__1_splitter_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_61_ = stack[1].m_num;
lean_object* v_h__1_62_ = stack[2].m_obj;
lean_object* v_h__2_63_ = stack[3].m_obj;
lean_object* v_h__3_64_ = stack[4].m_obj;
lean_object* v_res_71_;
v_res_71_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_match__1_splitter(lean_box(0), v_x_61_, v_h__1_62_, v_h__2_63_, v_h__3_64_);
stack->m_obj
 = v_res_71_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Array_0__Array_compareLex_match__1_splitter___boxed(lean_object* v_motive_72_, lean_object* v_x_73_, lean_object* v_h__1_74_, lean_object* v_h__2_75_, lean_object* v_h__3_76_){
_start:
{
uint8_t v_x_56__boxed_77_; lean_object* v_res_78_; 
v_x_56__boxed_77_ = lean_unbox(v_x_73_);
v_res_78_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_match__1_splitter(v_motive_72_, v_x_56__boxed_77_, v_h__1_74_, v_h__2_75_, v_h__3_76_);
return v_res_78_;
}
}
uint8_t l_Array_compareLex___redArg(lean_object* v_cmp_79_, lean_object* v_a_u2081_80_, lean_object* v_a_u2082_81_){
_start:
{
lean_object* v___x_82_; uint8_t v___x_83_; 
v___x_82_ = lean_unsigned_to_nat(0u);
v___x_83_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go___redArg(v_cmp_79_, v_a_u2081_80_, v_a_u2082_81_, v___x_82_);
return v___x_83_;
}
}
LEAN_EXPORT void l_Array_compareLex___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_79_ = stack[0].m_obj;
lean_object* v_a_u2081_80_ = stack[1].m_obj;
lean_object* v_a_u2082_81_ = stack[2].m_obj;
uint8_t v_res_84_;
v_res_84_ = l_Array_compareLex___redArg(v_cmp_79_, v_a_u2081_80_, v_a_u2082_81_);
stack->m_num = v_res_84_;
}
LEAN_EXPORT lean_object* l_Array_compareLex___redArg___boxed(lean_object* v_cmp_85_, lean_object* v_a_u2081_86_, lean_object* v_a_u2082_87_){
_start:
{
uint8_t v_res_88_; lean_object* v_r_89_; 
v_res_88_ = l_Array_compareLex___redArg(v_cmp_85_, v_a_u2081_86_, v_a_u2082_87_);
lean_dec_ref(v_a_u2082_87_);
lean_dec_ref(v_a_u2081_86_);
v_r_89_ = lean_box(v_res_88_);
return v_r_89_;
}
}
uint8_t l_Array_compareLex(lean_object* v_00_u03b1_90_, lean_object* v_cmp_91_, lean_object* v_a_u2081_92_, lean_object* v_a_u2082_93_){
_start:
{
lean_object* v___x_94_; uint8_t v___x_95_; 
v___x_94_ = lean_unsigned_to_nat(0u);
v___x_95_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go___redArg(v_cmp_91_, v_a_u2081_92_, v_a_u2082_93_, v___x_94_);
return v___x_95_;
}
}
LEAN_EXPORT void l_Array_compareLex_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_91_ = stack[1].m_obj;
lean_object* v_a_u2081_92_ = stack[2].m_obj;
lean_object* v_a_u2082_93_ = stack[3].m_obj;
uint8_t v_res_96_;
v_res_96_ = l_Array_compareLex(lean_box(0), v_cmp_91_, v_a_u2081_92_, v_a_u2082_93_);
stack->m_num = v_res_96_;
}
LEAN_EXPORT lean_object* l_Array_compareLex___boxed(lean_object* v_00_u03b1_97_, lean_object* v_cmp_98_, lean_object* v_a_u2081_99_, lean_object* v_a_u2082_100_){
_start:
{
uint8_t v_res_101_; lean_object* v_r_102_; 
v_res_101_ = l_Array_compareLex(v_00_u03b1_97_, v_cmp_98_, v_a_u2081_99_, v_a_u2082_100_);
lean_dec_ref(v_a_u2082_100_);
lean_dec_ref(v_a_u2081_99_);
v_r_102_ = lean_box(v_res_101_);
return v_r_102_;
}
}
LEAN_EXPORT lean_object* l_Array_instOrd___redArg(lean_object* v_inst_103_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = lean_alloc_closure((void*)(l_Array_compareLex___boxed), 4, 2);
lean_closure_set(v___x_104_, 0, lean_box(0));
lean_closure_set(v___x_104_, 1, v_inst_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Array_instOrd(lean_object* v_00_u03b1_105_, lean_object* v_inst_106_){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = lean_alloc_closure((void*)(l_Array_compareLex___boxed), 4, 2);
lean_closure_set(v___x_107_, 0, lean_box(0));
lean_closure_set(v___x_107_, 1, v_inst_106_);
return v___x_107_;
}
}
lean_object* runtime_initialize_Init_Data_Ord_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_WFTactics(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Ord_Array(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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

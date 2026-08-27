// Lean compiler output
// Module: Init.Data.Vector.Lemmas
// Imports: import all Init.Data.Array.Basic public import Init.Data.Vector.Basic import all Init.Data.Vector.Basic public import Init.Data.List.MapIdx import Init.ByCases import Init.Data.Array.Bootstrap import Init.Data.Array.Count import Init.Data.Array.Find import Init.Data.Array.OfFn import Init.Data.Bool import Init.Data.Fin.Lemmas import Init.Data.List.TakeDrop import Init.Data.Nat.Simproc import Init.TacticsExtra
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
uint8_t l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Init_Data_Nat_Lemmas_0__Nat_anyLTTR_loop(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_contains___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_instDecidableForallForallMemOfDecidablePred___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instDecidableForallForallMemOfDecidablePred___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_instDecidableForallForallMemOfDecidablePred___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instDecidableForallForallMemOfDecidablePred___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_instDecidableForallForallMemOfDecidablePred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instDecidableForallForallMemOfDecidablePred___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_instDecidableExistsAndMemOfDecidablePred___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instDecidableExistsAndMemOfDecidablePred___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_instDecidableExistsAndMemOfDecidablePred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instDecidableExistsAndMemOfDecidablePred___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_instDecidableMemOfLawfulBEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instDecidableMemOfLawfulBEq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_instDecidableMemOfLawfulBEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instDecidableMemOfLawfulBEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_instDecidableForallVectorZero___redArg(uint8_t);
LEAN_EXPORT lean_object* l_Vector_instDecidableForallVectorZero___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Vector_instDecidableForallVectorZero(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Vector_instDecidableForallVectorZero___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_instDecidableForallVectorSucc___redArg(uint8_t);
LEAN_EXPORT lean_object* l_Vector_instDecidableForallVectorSucc___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Vector_instDecidableForallVectorSucc(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Vector_instDecidableForallVectorSucc___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_instDecidableExistsVectorZero___redArg(uint8_t);
LEAN_EXPORT lean_object* l_Vector_instDecidableExistsVectorZero___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Vector_instDecidableExistsVectorZero(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Vector_instDecidableExistsVectorZero___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_instDecidableExistsVectorSucc___redArg(uint8_t);
LEAN_EXPORT lean_object* l_Vector_instDecidableExistsVectorSucc___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Vector_instDecidableExistsVectorSucc(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Vector_instDecidableExistsVectorSucc___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_instDecidableForallForallMemOfDecidablePred___redArg___lam__0(lean_object* v_xs_1_, lean_object* v_inst_2_, lean_object* v_i_3_, lean_object* v_h_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; uint8_t v___x_7_; 
v___x_5_ = lean_array_fget_borrowed(v_xs_1_, v_i_3_);
lean_inc(v___x_5_);
v___x_6_ = lean_apply_1(v_inst_2_, v___x_5_);
v___x_7_ = lean_unbox(v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Vector_instDecidableForallForallMemOfDecidablePred___redArg___lam__0___boxed(lean_object* v_xs_8_, lean_object* v_inst_9_, lean_object* v_i_10_, lean_object* v_h_11_){
_start:
{
uint8_t v_res_12_; lean_object* v_r_13_; 
v_res_12_ = l_Vector_instDecidableForallForallMemOfDecidablePred___redArg___lam__0(v_xs_8_, v_inst_9_, v_i_10_, v_h_11_);
lean_dec(v_i_10_);
lean_dec_ref(v_xs_8_);
v_r_13_ = lean_box(v_res_12_);
return v_r_13_;
}
}
LEAN_EXPORT uint8_t l_Vector_instDecidableForallForallMemOfDecidablePred___redArg(lean_object* v_n_14_, lean_object* v_xs_15_, lean_object* v_inst_16_){
_start:
{
lean_object* v___f_17_; uint8_t v___x_18_; 
v___f_17_ = lean_alloc_closure((void*)(l_Vector_instDecidableForallForallMemOfDecidablePred___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_17_, 0, v_xs_15_);
lean_closure_set(v___f_17_, 1, v_inst_16_);
lean_inc(v_n_14_);
v___x_18_ = l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop(v_n_14_, v___f_17_, v_n_14_, lean_box(0));
lean_dec(v_n_14_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Vector_instDecidableForallForallMemOfDecidablePred___redArg___boxed(lean_object* v_n_19_, lean_object* v_xs_20_, lean_object* v_inst_21_){
_start:
{
uint8_t v_res_22_; lean_object* v_r_23_; 
v_res_22_ = l_Vector_instDecidableForallForallMemOfDecidablePred___redArg(v_n_19_, v_xs_20_, v_inst_21_);
v_r_23_ = lean_box(v_res_22_);
return v_r_23_;
}
}
LEAN_EXPORT uint8_t l_Vector_instDecidableForallForallMemOfDecidablePred(lean_object* v_00_u03b1_24_, lean_object* v_n_25_, lean_object* v_xs_26_, lean_object* v_p_27_, lean_object* v_inst_28_){
_start:
{
uint8_t v___x_29_; 
v___x_29_ = l_Vector_instDecidableForallForallMemOfDecidablePred___redArg(v_n_25_, v_xs_26_, v_inst_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Vector_instDecidableForallForallMemOfDecidablePred___boxed(lean_object* v_00_u03b1_30_, lean_object* v_n_31_, lean_object* v_xs_32_, lean_object* v_p_33_, lean_object* v_inst_34_){
_start:
{
uint8_t v_res_35_; lean_object* v_r_36_; 
v_res_35_ = l_Vector_instDecidableForallForallMemOfDecidablePred(v_00_u03b1_30_, v_n_31_, v_xs_32_, v_p_33_, v_inst_34_);
v_r_36_ = lean_box(v_res_35_);
return v_r_36_;
}
}
LEAN_EXPORT uint8_t l_Vector_instDecidableExistsAndMemOfDecidablePred___redArg(lean_object* v_n_37_, lean_object* v_xs_38_, lean_object* v_inst_39_){
_start:
{
lean_object* v___f_40_; uint8_t v___x_41_; 
v___f_40_ = lean_alloc_closure((void*)(l_Vector_instDecidableForallForallMemOfDecidablePred___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_40_, 0, v_xs_38_);
lean_closure_set(v___f_40_, 1, v_inst_39_);
lean_inc(v_n_37_);
v___x_41_ = l___private_Init_Data_Nat_Lemmas_0__Nat_anyLTTR_loop(v_n_37_, v___f_40_, v_n_37_, lean_box(0));
lean_dec(v_n_37_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Vector_instDecidableExistsAndMemOfDecidablePred___redArg___boxed(lean_object* v_n_42_, lean_object* v_xs_43_, lean_object* v_inst_44_){
_start:
{
uint8_t v_res_45_; lean_object* v_r_46_; 
v_res_45_ = l_Vector_instDecidableExistsAndMemOfDecidablePred___redArg(v_n_42_, v_xs_43_, v_inst_44_);
v_r_46_ = lean_box(v_res_45_);
return v_r_46_;
}
}
LEAN_EXPORT uint8_t l_Vector_instDecidableExistsAndMemOfDecidablePred(lean_object* v_00_u03b1_47_, lean_object* v_n_48_, lean_object* v_xs_49_, lean_object* v_p_50_, lean_object* v_inst_51_){
_start:
{
uint8_t v___x_52_; 
v___x_52_ = l_Vector_instDecidableExistsAndMemOfDecidablePred___redArg(v_n_48_, v_xs_49_, v_inst_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Vector_instDecidableExistsAndMemOfDecidablePred___boxed(lean_object* v_00_u03b1_53_, lean_object* v_n_54_, lean_object* v_xs_55_, lean_object* v_p_56_, lean_object* v_inst_57_){
_start:
{
uint8_t v_res_58_; lean_object* v_r_59_; 
v_res_58_ = l_Vector_instDecidableExistsAndMemOfDecidablePred(v_00_u03b1_53_, v_n_54_, v_xs_55_, v_p_56_, v_inst_57_);
v_r_59_ = lean_box(v_res_58_);
return v_r_59_;
}
}
LEAN_EXPORT uint8_t l_Vector_instDecidableMemOfLawfulBEq___redArg(lean_object* v_inst_60_, lean_object* v_a_61_, lean_object* v_as_62_){
_start:
{
uint8_t v___x_63_; 
v___x_63_ = l_Array_contains___redArg(v_inst_60_, v_as_62_, v_a_61_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Vector_instDecidableMemOfLawfulBEq___redArg___boxed(lean_object* v_inst_64_, lean_object* v_a_65_, lean_object* v_as_66_){
_start:
{
uint8_t v_res_67_; lean_object* v_r_68_; 
v_res_67_ = l_Vector_instDecidableMemOfLawfulBEq___redArg(v_inst_64_, v_a_65_, v_as_66_);
v_r_68_ = lean_box(v_res_67_);
return v_r_68_;
}
}
LEAN_EXPORT uint8_t l_Vector_instDecidableMemOfLawfulBEq(lean_object* v_00_u03b1_69_, lean_object* v_n_70_, lean_object* v_inst_71_, lean_object* v_inst_72_, lean_object* v_a_73_, lean_object* v_as_74_){
_start:
{
uint8_t v___x_75_; 
v___x_75_ = l_Array_contains___redArg(v_inst_71_, v_as_74_, v_a_73_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Vector_instDecidableMemOfLawfulBEq___boxed(lean_object* v_00_u03b1_76_, lean_object* v_n_77_, lean_object* v_inst_78_, lean_object* v_inst_79_, lean_object* v_a_80_, lean_object* v_as_81_){
_start:
{
uint8_t v_res_82_; lean_object* v_r_83_; 
v_res_82_ = l_Vector_instDecidableMemOfLawfulBEq(v_00_u03b1_76_, v_n_77_, v_inst_78_, v_inst_79_, v_a_80_, v_as_81_);
lean_dec(v_n_77_);
v_r_83_ = lean_box(v_res_82_);
return v_r_83_;
}
}
LEAN_EXPORT uint8_t l_Vector_instDecidableForallVectorZero___redArg(uint8_t v_x_84_){
_start:
{
return v_x_84_;
}
}
LEAN_EXPORT lean_object* l_Vector_instDecidableForallVectorZero___redArg___boxed(lean_object* v_x_85_){
_start:
{
uint8_t v_x_25__boxed_86_; uint8_t v_res_87_; lean_object* v_r_88_; 
v_x_25__boxed_86_ = lean_unbox(v_x_85_);
v_res_87_ = l_Vector_instDecidableForallVectorZero___redArg(v_x_25__boxed_86_);
v_r_88_ = lean_box(v_res_87_);
return v_r_88_;
}
}
LEAN_EXPORT uint8_t l_Vector_instDecidableForallVectorZero(lean_object* v_00_u03b1_89_, lean_object* v_P_90_, uint8_t v_x_91_){
_start:
{
return v_x_91_;
}
}
LEAN_EXPORT lean_object* l_Vector_instDecidableForallVectorZero___boxed(lean_object* v_00_u03b1_92_, lean_object* v_P_93_, lean_object* v_x_94_){
_start:
{
uint8_t v_x_28__boxed_95_; uint8_t v_res_96_; lean_object* v_r_97_; 
v_x_28__boxed_95_ = lean_unbox(v_x_94_);
v_res_96_ = l_Vector_instDecidableForallVectorZero(v_00_u03b1_92_, v_P_93_, v_x_28__boxed_95_);
v_r_97_ = lean_box(v_res_96_);
return v_r_97_;
}
}
LEAN_EXPORT uint8_t l_Vector_instDecidableForallVectorSucc___redArg(uint8_t v_inst_98_){
_start:
{
return v_inst_98_;
}
}
LEAN_EXPORT lean_object* l_Vector_instDecidableForallVectorSucc___redArg___boxed(lean_object* v_inst_99_){
_start:
{
uint8_t v_inst_8__boxed_100_; uint8_t v_res_101_; lean_object* v_r_102_; 
v_inst_8__boxed_100_ = lean_unbox(v_inst_99_);
v_res_101_ = l_Vector_instDecidableForallVectorSucc___redArg(v_inst_8__boxed_100_);
v_r_102_ = lean_box(v_res_101_);
return v_r_102_;
}
}
LEAN_EXPORT uint8_t l_Vector_instDecidableForallVectorSucc(lean_object* v_00_u03b1_103_, lean_object* v_n_104_, lean_object* v_P_105_, uint8_t v_inst_106_){
_start:
{
return v_inst_106_;
}
}
LEAN_EXPORT lean_object* l_Vector_instDecidableForallVectorSucc___boxed(lean_object* v_00_u03b1_107_, lean_object* v_n_108_, lean_object* v_P_109_, lean_object* v_inst_110_){
_start:
{
uint8_t v_inst_11__boxed_111_; uint8_t v_res_112_; lean_object* v_r_113_; 
v_inst_11__boxed_111_ = lean_unbox(v_inst_110_);
v_res_112_ = l_Vector_instDecidableForallVectorSucc(v_00_u03b1_107_, v_n_108_, v_P_109_, v_inst_11__boxed_111_);
lean_dec(v_n_108_);
v_r_113_ = lean_box(v_res_112_);
return v_r_113_;
}
}
LEAN_EXPORT uint8_t l_Vector_instDecidableExistsVectorZero___redArg(uint8_t v_inst_114_){
_start:
{
return v_inst_114_;
}
}
LEAN_EXPORT lean_object* l_Vector_instDecidableExistsVectorZero___redArg___boxed(lean_object* v_inst_115_){
_start:
{
uint8_t v_inst_47__boxed_116_; uint8_t v_res_117_; lean_object* v_r_118_; 
v_inst_47__boxed_116_ = lean_unbox(v_inst_115_);
v_res_117_ = l_Vector_instDecidableExistsVectorZero___redArg(v_inst_47__boxed_116_);
v_r_118_ = lean_box(v_res_117_);
return v_r_118_;
}
}
LEAN_EXPORT uint8_t l_Vector_instDecidableExistsVectorZero(lean_object* v_00_u03b1_119_, lean_object* v_P_120_, uint8_t v_inst_121_){
_start:
{
return v_inst_121_;
}
}
LEAN_EXPORT lean_object* l_Vector_instDecidableExistsVectorZero___boxed(lean_object* v_00_u03b1_122_, lean_object* v_P_123_, lean_object* v_inst_124_){
_start:
{
uint8_t v_inst_50__boxed_125_; uint8_t v_res_126_; lean_object* v_r_127_; 
v_inst_50__boxed_125_ = lean_unbox(v_inst_124_);
v_res_126_ = l_Vector_instDecidableExistsVectorZero(v_00_u03b1_122_, v_P_123_, v_inst_50__boxed_125_);
v_r_127_ = lean_box(v_res_126_);
return v_r_127_;
}
}
LEAN_EXPORT uint8_t l_Vector_instDecidableExistsVectorSucc___redArg(uint8_t v_inst_128_){
_start:
{
if (v_inst_128_ == 0)
{
uint8_t v___x_129_; 
v___x_129_ = 1;
return v___x_129_;
}
else
{
uint8_t v___x_130_; 
v___x_130_ = 0;
return v___x_130_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_instDecidableExistsVectorSucc___redArg___boxed(lean_object* v_inst_131_){
_start:
{
uint8_t v_inst_34__boxed_132_; uint8_t v_res_133_; lean_object* v_r_134_; 
v_inst_34__boxed_132_ = lean_unbox(v_inst_131_);
v_res_133_ = l_Vector_instDecidableExistsVectorSucc___redArg(v_inst_34__boxed_132_);
v_r_134_ = lean_box(v_res_133_);
return v_r_134_;
}
}
LEAN_EXPORT uint8_t l_Vector_instDecidableExistsVectorSucc(lean_object* v_00_u03b1_135_, lean_object* v_n_136_, lean_object* v_P_137_, uint8_t v_inst_138_){
_start:
{
uint8_t v___x_139_; 
v___x_139_ = l_Vector_instDecidableExistsVectorSucc___redArg(v_inst_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Vector_instDecidableExistsVectorSucc___boxed(lean_object* v_00_u03b1_140_, lean_object* v_n_141_, lean_object* v_P_142_, lean_object* v_inst_143_){
_start:
{
uint8_t v_inst_41__boxed_144_; uint8_t v_res_145_; lean_object* v_r_146_; 
v_inst_41__boxed_144_ = lean_unbox(v_inst_143_);
v_res_145_ = l_Vector_instDecidableExistsVectorSucc(v_00_u03b1_140_, v_n_141_, v_P_142_, v_inst_41__boxed_144_);
lean_dec(v_n_141_);
v_r_146_ = lean_box(v_res_145_);
return v_r_146_;
}
}
lean_object* runtime_initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Vector_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Vector_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_MapIdx(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Count(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Find(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_OfFn(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Fin_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Init_TacticsExtra(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Vector_Lemmas(uint8_t builtin) {
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
res = runtime_initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_MapIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Count(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Find(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_OfFn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Fin_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Vector_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Vector_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Vector_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_List_MapIdx(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Count(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Find(uint8_t builtin);
lean_object* initialize_Init_Data_Array_OfFn(uint8_t builtin);
lean_object* initialize_Init_Data_Bool(uint8_t builtin);
lean_object* initialize_Init_Data_Fin_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Simproc(uint8_t builtin);
lean_object* initialize_Init_TacticsExtra(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Vector_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_MapIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Count(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Find(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_OfFn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Fin_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Vector_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Vector_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Vector_Lemmas(builtin);
}
#ifdef __cplusplus
}
#endif

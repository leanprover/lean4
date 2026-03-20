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
uint8_t l_Nat_decidableBallLT___redArg(lean_object*, lean_object*);
uint8_t l_Nat_decidableExistsLT_x27___redArg(lean_object*, lean_object*);
uint8_t l_Array_contains___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_instDecidableForallForallMemOfDecidablePred___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instDecidableForallForallMemOfDecidablePred___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_instDecidableForallForallMemOfDecidablePred___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instDecidableForallForallMemOfDecidablePred___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_instDecidableForallForallMemOfDecidablePred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instDecidableForallForallMemOfDecidablePred___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_instDecidableExistsAndMemOfDecidablePred___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instDecidableExistsAndMemOfDecidablePred___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Vector_instDecidableForallForallMemOfDecidablePred___redArg___lam__0(lean_object* v_xs_1_, lean_object* v_inst_2_, lean_object* v_n_3_, lean_object* v_h_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; uint8_t v___x_7_; 
v___x_5_ = lean_array_fget_borrowed(v_xs_1_, v_n_3_);
lean_inc(v___x_5_);
v___x_6_ = lean_apply_1(v_inst_2_, v___x_5_);
v___x_7_ = lean_unbox(v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Vector_instDecidableForallForallMemOfDecidablePred___redArg___lam__0___boxed(lean_object* v_xs_8_, lean_object* v_inst_9_, lean_object* v_n_10_, lean_object* v_h_11_){
_start:
{
uint8_t v_res_12_; lean_object* v_r_13_; 
v_res_12_ = l_Vector_instDecidableForallForallMemOfDecidablePred___redArg___lam__0(v_xs_8_, v_inst_9_, v_n_10_, v_h_11_);
lean_dec(v_n_10_);
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
v___x_18_ = l_Nat_decidableBallLT___redArg(v_n_14_, v___f_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Vector_instDecidableForallForallMemOfDecidablePred___redArg___boxed(lean_object* v_n_19_, lean_object* v_xs_20_, lean_object* v_inst_21_){
_start:
{
uint8_t v_res_22_; lean_object* v_r_23_; 
v_res_22_ = l_Vector_instDecidableForallForallMemOfDecidablePred___redArg(v_n_19_, v_xs_20_, v_inst_21_);
lean_dec(v_n_19_);
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
lean_dec(v_n_31_);
v_r_36_ = lean_box(v_res_35_);
return v_r_36_;
}
}
LEAN_EXPORT uint8_t l_Vector_instDecidableExistsAndMemOfDecidablePred___redArg___lam__0(lean_object* v_xs_37_, lean_object* v_inst_38_, lean_object* v_m_39_, lean_object* v_h_40_){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; uint8_t v___x_43_; 
v___x_41_ = lean_array_fget_borrowed(v_xs_37_, v_m_39_);
lean_inc(v___x_41_);
v___x_42_ = lean_apply_1(v_inst_38_, v___x_41_);
v___x_43_ = lean_unbox(v___x_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Vector_instDecidableExistsAndMemOfDecidablePred___redArg___lam__0___boxed(lean_object* v_xs_44_, lean_object* v_inst_45_, lean_object* v_m_46_, lean_object* v_h_47_){
_start:
{
uint8_t v_res_48_; lean_object* v_r_49_; 
v_res_48_ = l_Vector_instDecidableExistsAndMemOfDecidablePred___redArg___lam__0(v_xs_44_, v_inst_45_, v_m_46_, v_h_47_);
lean_dec(v_m_46_);
lean_dec_ref(v_xs_44_);
v_r_49_ = lean_box(v_res_48_);
return v_r_49_;
}
}
LEAN_EXPORT uint8_t l_Vector_instDecidableExistsAndMemOfDecidablePred___redArg(lean_object* v_n_50_, lean_object* v_xs_51_, lean_object* v_inst_52_){
_start:
{
lean_object* v___f_53_; uint8_t v___x_54_; 
v___f_53_ = lean_alloc_closure((void*)(l_Vector_instDecidableExistsAndMemOfDecidablePred___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_53_, 0, v_xs_51_);
lean_closure_set(v___f_53_, 1, v_inst_52_);
v___x_54_ = l_Nat_decidableExistsLT_x27___redArg(v_n_50_, v___f_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Vector_instDecidableExistsAndMemOfDecidablePred___redArg___boxed(lean_object* v_n_55_, lean_object* v_xs_56_, lean_object* v_inst_57_){
_start:
{
uint8_t v_res_58_; lean_object* v_r_59_; 
v_res_58_ = l_Vector_instDecidableExistsAndMemOfDecidablePred___redArg(v_n_55_, v_xs_56_, v_inst_57_);
lean_dec(v_n_55_);
v_r_59_ = lean_box(v_res_58_);
return v_r_59_;
}
}
LEAN_EXPORT uint8_t l_Vector_instDecidableExistsAndMemOfDecidablePred(lean_object* v_00_u03b1_60_, lean_object* v_n_61_, lean_object* v_xs_62_, lean_object* v_p_63_, lean_object* v_inst_64_){
_start:
{
uint8_t v___x_65_; 
v___x_65_ = l_Vector_instDecidableExistsAndMemOfDecidablePred___redArg(v_n_61_, v_xs_62_, v_inst_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Vector_instDecidableExistsAndMemOfDecidablePred___boxed(lean_object* v_00_u03b1_66_, lean_object* v_n_67_, lean_object* v_xs_68_, lean_object* v_p_69_, lean_object* v_inst_70_){
_start:
{
uint8_t v_res_71_; lean_object* v_r_72_; 
v_res_71_ = l_Vector_instDecidableExistsAndMemOfDecidablePred(v_00_u03b1_66_, v_n_67_, v_xs_68_, v_p_69_, v_inst_70_);
lean_dec(v_n_67_);
v_r_72_ = lean_box(v_res_71_);
return v_r_72_;
}
}
LEAN_EXPORT uint8_t l_Vector_instDecidableMemOfLawfulBEq___redArg(lean_object* v_inst_73_, lean_object* v_a_74_, lean_object* v_as_75_){
_start:
{
uint8_t v___x_76_; 
v___x_76_ = l_Array_contains___redArg(v_inst_73_, v_as_75_, v_a_74_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Vector_instDecidableMemOfLawfulBEq___redArg___boxed(lean_object* v_inst_77_, lean_object* v_a_78_, lean_object* v_as_79_){
_start:
{
uint8_t v_res_80_; lean_object* v_r_81_; 
v_res_80_ = l_Vector_instDecidableMemOfLawfulBEq___redArg(v_inst_77_, v_a_78_, v_as_79_);
v_r_81_ = lean_box(v_res_80_);
return v_r_81_;
}
}
LEAN_EXPORT uint8_t l_Vector_instDecidableMemOfLawfulBEq(lean_object* v_00_u03b1_82_, lean_object* v_n_83_, lean_object* v_inst_84_, lean_object* v_inst_85_, lean_object* v_a_86_, lean_object* v_as_87_){
_start:
{
uint8_t v___x_88_; 
v___x_88_ = l_Array_contains___redArg(v_inst_84_, v_as_87_, v_a_86_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Vector_instDecidableMemOfLawfulBEq___boxed(lean_object* v_00_u03b1_89_, lean_object* v_n_90_, lean_object* v_inst_91_, lean_object* v_inst_92_, lean_object* v_a_93_, lean_object* v_as_94_){
_start:
{
uint8_t v_res_95_; lean_object* v_r_96_; 
v_res_95_ = l_Vector_instDecidableMemOfLawfulBEq(v_00_u03b1_89_, v_n_90_, v_inst_91_, v_inst_92_, v_a_93_, v_as_94_);
lean_dec(v_n_90_);
v_r_96_ = lean_box(v_res_95_);
return v_r_96_;
}
}
LEAN_EXPORT uint8_t l_Vector_instDecidableForallVectorZero___redArg(uint8_t v_x_97_){
_start:
{
return v_x_97_;
}
}
LEAN_EXPORT lean_object* l_Vector_instDecidableForallVectorZero___redArg___boxed(lean_object* v_x_98_){
_start:
{
uint8_t v_x_18__boxed_99_; uint8_t v_res_100_; lean_object* v_r_101_; 
v_x_18__boxed_99_ = lean_unbox(v_x_98_);
v_res_100_ = l_Vector_instDecidableForallVectorZero___redArg(v_x_18__boxed_99_);
v_r_101_ = lean_box(v_res_100_);
return v_r_101_;
}
}
LEAN_EXPORT uint8_t l_Vector_instDecidableForallVectorZero(lean_object* v_00_u03b1_102_, lean_object* v_P_103_, uint8_t v_x_104_){
_start:
{
return v_x_104_;
}
}
LEAN_EXPORT lean_object* l_Vector_instDecidableForallVectorZero___boxed(lean_object* v_00_u03b1_105_, lean_object* v_P_106_, lean_object* v_x_107_){
_start:
{
uint8_t v_x_21__boxed_108_; uint8_t v_res_109_; lean_object* v_r_110_; 
v_x_21__boxed_108_ = lean_unbox(v_x_107_);
v_res_109_ = l_Vector_instDecidableForallVectorZero(v_00_u03b1_105_, v_P_106_, v_x_21__boxed_108_);
v_r_110_ = lean_box(v_res_109_);
return v_r_110_;
}
}
LEAN_EXPORT uint8_t l_Vector_instDecidableForallVectorSucc___redArg(uint8_t v_inst_111_){
_start:
{
return v_inst_111_;
}
}
LEAN_EXPORT lean_object* l_Vector_instDecidableForallVectorSucc___redArg___boxed(lean_object* v_inst_112_){
_start:
{
uint8_t v_inst_8__boxed_113_; uint8_t v_res_114_; lean_object* v_r_115_; 
v_inst_8__boxed_113_ = lean_unbox(v_inst_112_);
v_res_114_ = l_Vector_instDecidableForallVectorSucc___redArg(v_inst_8__boxed_113_);
v_r_115_ = lean_box(v_res_114_);
return v_r_115_;
}
}
LEAN_EXPORT uint8_t l_Vector_instDecidableForallVectorSucc(lean_object* v_00_u03b1_116_, lean_object* v_n_117_, lean_object* v_P_118_, uint8_t v_inst_119_){
_start:
{
return v_inst_119_;
}
}
LEAN_EXPORT lean_object* l_Vector_instDecidableForallVectorSucc___boxed(lean_object* v_00_u03b1_120_, lean_object* v_n_121_, lean_object* v_P_122_, lean_object* v_inst_123_){
_start:
{
uint8_t v_inst_11__boxed_124_; uint8_t v_res_125_; lean_object* v_r_126_; 
v_inst_11__boxed_124_ = lean_unbox(v_inst_123_);
v_res_125_ = l_Vector_instDecidableForallVectorSucc(v_00_u03b1_120_, v_n_121_, v_P_122_, v_inst_11__boxed_124_);
lean_dec(v_n_121_);
v_r_126_ = lean_box(v_res_125_);
return v_r_126_;
}
}
LEAN_EXPORT uint8_t l_Vector_instDecidableExistsVectorZero___redArg(uint8_t v_inst_127_){
_start:
{
return v_inst_127_;
}
}
LEAN_EXPORT lean_object* l_Vector_instDecidableExistsVectorZero___redArg___boxed(lean_object* v_inst_128_){
_start:
{
uint8_t v_inst_27__boxed_129_; uint8_t v_res_130_; lean_object* v_r_131_; 
v_inst_27__boxed_129_ = lean_unbox(v_inst_128_);
v_res_130_ = l_Vector_instDecidableExistsVectorZero___redArg(v_inst_27__boxed_129_);
v_r_131_ = lean_box(v_res_130_);
return v_r_131_;
}
}
LEAN_EXPORT uint8_t l_Vector_instDecidableExistsVectorZero(lean_object* v_00_u03b1_132_, lean_object* v_P_133_, uint8_t v_inst_134_){
_start:
{
return v_inst_134_;
}
}
LEAN_EXPORT lean_object* l_Vector_instDecidableExistsVectorZero___boxed(lean_object* v_00_u03b1_135_, lean_object* v_P_136_, lean_object* v_inst_137_){
_start:
{
uint8_t v_inst_30__boxed_138_; uint8_t v_res_139_; lean_object* v_r_140_; 
v_inst_30__boxed_138_ = lean_unbox(v_inst_137_);
v_res_139_ = l_Vector_instDecidableExistsVectorZero(v_00_u03b1_135_, v_P_136_, v_inst_30__boxed_138_);
v_r_140_ = lean_box(v_res_139_);
return v_r_140_;
}
}
LEAN_EXPORT uint8_t l_Vector_instDecidableExistsVectorSucc___redArg(uint8_t v_inst_141_){
_start:
{
if (v_inst_141_ == 0)
{
uint8_t v___x_142_; 
v___x_142_ = 1;
return v___x_142_;
}
else
{
uint8_t v___x_143_; 
v___x_143_ = 0;
return v___x_143_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_instDecidableExistsVectorSucc___redArg___boxed(lean_object* v_inst_144_){
_start:
{
uint8_t v_inst_14__boxed_145_; uint8_t v_res_146_; lean_object* v_r_147_; 
v_inst_14__boxed_145_ = lean_unbox(v_inst_144_);
v_res_146_ = l_Vector_instDecidableExistsVectorSucc___redArg(v_inst_14__boxed_145_);
v_r_147_ = lean_box(v_res_146_);
return v_r_147_;
}
}
LEAN_EXPORT uint8_t l_Vector_instDecidableExistsVectorSucc(lean_object* v_00_u03b1_148_, lean_object* v_n_149_, lean_object* v_P_150_, uint8_t v_inst_151_){
_start:
{
uint8_t v___x_152_; 
v___x_152_ = l_Vector_instDecidableExistsVectorSucc___redArg(v_inst_151_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Vector_instDecidableExistsVectorSucc___boxed(lean_object* v_00_u03b1_153_, lean_object* v_n_154_, lean_object* v_P_155_, lean_object* v_inst_156_){
_start:
{
uint8_t v_inst_21__boxed_157_; uint8_t v_res_158_; lean_object* v_r_159_; 
v_inst_21__boxed_157_ = lean_unbox(v_inst_156_);
v_res_158_ = l_Vector_instDecidableExistsVectorSucc(v_00_u03b1_153_, v_n_154_, v_P_155_, v_inst_21__boxed_157_);
lean_dec(v_n_154_);
v_r_159_ = lean_box(v_res_158_);
return v_r_159_;
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
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Vector_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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

// Lean compiler output
// Module: Init.Data.Vector.Lex
// Imports: import all Init.Data.Vector.Basic import all Init.Data.Array.Lex.Basic import Init.Data.Range.Polymorphic.Lemmas public import Init.Data.Array.Lex.Basic public import Init.Data.BEq public import Init.Data.Vector.Basic import Init.Data.Array.Lex.Lemmas import Init.Data.Vector.Lemmas
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
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Vector_lex___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Lex_0__Break_runK_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Lex_0__Break_runK_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instTransLt___redArg();
LEAN_EXPORT lean_object* l_Vector_instTransLt___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Vector_instTransLt(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instTransLt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instTransLeOfLawfulOrderLTOfIsLinearOrder___redArg();
LEAN_EXPORT lean_object* l_Vector_instTransLeOfLawfulOrderLTOfIsLinearOrder___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Vector_instTransLeOfLawfulOrderLTOfIsLinearOrder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instTransLeOfLawfulOrderLTOfIsLinearOrder___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_instDecidableLTOfDecidableEq___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instDecidableLTOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_instDecidableLTOfDecidableEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instDecidableLTOfDecidableEq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_instDecidableLTOfDecidableEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instDecidableLTOfDecidableEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_instDecidableLEOfDecidableEqOfDecidableLT___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instDecidableLEOfDecidableEqOfDecidableLT___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_instDecidableLEOfDecidableEqOfDecidableLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instDecidableLEOfDecidableEqOfDecidableLT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Lex_0__Break_runK_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_4_; lean_object* v___x_5_; 
lean_dec(v_h__1_2_);
v___x_4_ = lean_box(0);
v___x_5_ = lean_apply_1(v_h__2_3_, v___x_4_);
return v___x_5_;
}
else
{
lean_object* v_val_6_; lean_object* v___x_7_; 
lean_dec(v_h__2_3_);
v_val_6_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_val_6_);
lean_dec_ref_known(v_x_1_, 1);
v___x_7_ = lean_apply_1(v_h__1_2_, v_val_6_);
return v___x_7_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Lex_0__Break_runK_match__1_splitter(lean_object* v_00_u03b1_8_, lean_object* v_motive_9_, lean_object* v_x_10_, lean_object* v_h__1_11_, lean_object* v_h__2_12_){
_start:
{
if (lean_obj_tag(v_x_10_) == 0)
{
lean_object* v___x_13_; lean_object* v___x_14_; 
lean_dec(v_h__1_11_);
v___x_13_ = lean_box(0);
v___x_14_ = lean_apply_1(v_h__2_12_, v___x_13_);
return v___x_14_;
}
else
{
lean_object* v_val_15_; lean_object* v___x_16_; 
lean_dec(v_h__2_12_);
v_val_15_ = lean_ctor_get(v_x_10_, 0);
lean_inc(v_val_15_);
lean_dec_ref_known(v_x_10_, 1);
v___x_16_ = lean_apply_1(v_h__1_11_, v_val_15_);
return v___x_16_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_instTransLt___redArg(){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = lean_box(0);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Vector_instTransLt___redArg___boxed(lean_object* v___dummy_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Vector_instTransLt___redArg();
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Vector_instTransLt(lean_object* v_00_u03b1_21_, lean_object* v_n_22_, lean_object* v_inst_23_, lean_object* v_inst_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = lean_box(0);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Vector_instTransLt___boxed(lean_object* v_00_u03b1_26_, lean_object* v_n_27_, lean_object* v_inst_28_, lean_object* v_inst_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Vector_instTransLt(v_00_u03b1_26_, v_n_27_, v_inst_28_, v_inst_29_);
lean_dec(v_n_27_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Vector_instTransLeOfLawfulOrderLTOfIsLinearOrder___redArg(){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = lean_box(0);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Vector_instTransLeOfLawfulOrderLTOfIsLinearOrder___redArg___boxed(lean_object* v___dummy_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Vector_instTransLeOfLawfulOrderLTOfIsLinearOrder___redArg();
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Vector_instTransLeOfLawfulOrderLTOfIsLinearOrder(lean_object* v_00_u03b1_35_, lean_object* v_n_36_, lean_object* v_inst_37_, lean_object* v_inst_38_, lean_object* v_inst_39_, lean_object* v_inst_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = lean_box(0);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Vector_instTransLeOfLawfulOrderLTOfIsLinearOrder___boxed(lean_object* v_00_u03b1_42_, lean_object* v_n_43_, lean_object* v_inst_44_, lean_object* v_inst_45_, lean_object* v_inst_46_, lean_object* v_inst_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l_Vector_instTransLeOfLawfulOrderLTOfIsLinearOrder(v_00_u03b1_42_, v_n_43_, v_inst_44_, v_inst_45_, v_inst_46_, v_inst_47_);
lean_dec(v_n_43_);
return v_res_48_;
}
}
LEAN_EXPORT uint8_t l_Vector_instDecidableLTOfDecidableEq___redArg___lam__0(lean_object* v_inst_49_, lean_object* v_x1_50_, lean_object* v_x2_51_){
_start:
{
lean_object* v___x_52_; uint8_t v___x_53_; 
v___x_52_ = lean_apply_2(v_inst_49_, v_x1_50_, v_x2_51_);
v___x_53_ = lean_unbox(v___x_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Vector_instDecidableLTOfDecidableEq___redArg___lam__0___boxed(lean_object* v_inst_54_, lean_object* v_x1_55_, lean_object* v_x2_56_){
_start:
{
uint8_t v_res_57_; lean_object* v_r_58_; 
v_res_57_ = l_Vector_instDecidableLTOfDecidableEq___redArg___lam__0(v_inst_54_, v_x1_55_, v_x2_56_);
v_r_58_ = lean_box(v_res_57_);
return v_r_58_;
}
}
LEAN_EXPORT uint8_t l_Vector_instDecidableLTOfDecidableEq___redArg(lean_object* v_n_59_, lean_object* v_inst_60_, lean_object* v_inst_61_, lean_object* v_xs_62_, lean_object* v_ys_63_){
_start:
{
lean_object* v___f_64_; lean_object* v___f_65_; uint8_t v___x_66_; 
v___f_64_ = lean_alloc_closure((void*)(l_Vector_instDecidableLTOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_64_, 0, v_inst_61_);
v___f_65_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_65_, 0, v_inst_60_);
v___x_66_ = l_Vector_lex___redArg(v_n_59_, v___f_65_, v_xs_62_, v_ys_63_, v___f_64_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Vector_instDecidableLTOfDecidableEq___redArg___boxed(lean_object* v_n_67_, lean_object* v_inst_68_, lean_object* v_inst_69_, lean_object* v_xs_70_, lean_object* v_ys_71_){
_start:
{
uint8_t v_res_72_; lean_object* v_r_73_; 
v_res_72_ = l_Vector_instDecidableLTOfDecidableEq___redArg(v_n_67_, v_inst_68_, v_inst_69_, v_xs_70_, v_ys_71_);
v_r_73_ = lean_box(v_res_72_);
return v_r_73_;
}
}
LEAN_EXPORT uint8_t l_Vector_instDecidableLTOfDecidableEq(lean_object* v_00_u03b1_74_, lean_object* v_n_75_, lean_object* v_inst_76_, lean_object* v_inst_77_, lean_object* v_inst_78_, lean_object* v_xs_79_, lean_object* v_ys_80_){
_start:
{
uint8_t v___x_81_; 
v___x_81_ = l_Vector_instDecidableLTOfDecidableEq___redArg(v_n_75_, v_inst_76_, v_inst_78_, v_xs_79_, v_ys_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Vector_instDecidableLTOfDecidableEq___boxed(lean_object* v_00_u03b1_82_, lean_object* v_n_83_, lean_object* v_inst_84_, lean_object* v_inst_85_, lean_object* v_inst_86_, lean_object* v_xs_87_, lean_object* v_ys_88_){
_start:
{
uint8_t v_res_89_; lean_object* v_r_90_; 
v_res_89_ = l_Vector_instDecidableLTOfDecidableEq(v_00_u03b1_82_, v_n_83_, v_inst_84_, v_inst_85_, v_inst_86_, v_xs_87_, v_ys_88_);
v_r_90_ = lean_box(v_res_89_);
return v_r_90_;
}
}
LEAN_EXPORT uint8_t l_Vector_instDecidableLEOfDecidableEqOfDecidableLT___redArg(lean_object* v_n_91_, lean_object* v_inst_92_, lean_object* v_inst_93_, lean_object* v_xs_94_, lean_object* v_ys_95_){
_start:
{
lean_object* v___f_96_; lean_object* v___f_97_; uint8_t v___x_98_; 
v___f_96_ = lean_alloc_closure((void*)(l_Vector_instDecidableLTOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_96_, 0, v_inst_93_);
v___f_97_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_97_, 0, v_inst_92_);
v___x_98_ = l_Vector_lex___redArg(v_n_91_, v___f_97_, v_ys_95_, v_xs_94_, v___f_96_);
if (v___x_98_ == 0)
{
uint8_t v___x_99_; 
v___x_99_ = 1;
return v___x_99_;
}
else
{
uint8_t v___x_100_; 
v___x_100_ = 0;
return v___x_100_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_instDecidableLEOfDecidableEqOfDecidableLT___redArg___boxed(lean_object* v_n_101_, lean_object* v_inst_102_, lean_object* v_inst_103_, lean_object* v_xs_104_, lean_object* v_ys_105_){
_start:
{
uint8_t v_res_106_; lean_object* v_r_107_; 
v_res_106_ = l_Vector_instDecidableLEOfDecidableEqOfDecidableLT___redArg(v_n_101_, v_inst_102_, v_inst_103_, v_xs_104_, v_ys_105_);
v_r_107_ = lean_box(v_res_106_);
return v_r_107_;
}
}
LEAN_EXPORT uint8_t l_Vector_instDecidableLEOfDecidableEqOfDecidableLT(lean_object* v_00_u03b1_108_, lean_object* v_n_109_, lean_object* v_inst_110_, lean_object* v_inst_111_, lean_object* v_inst_112_, lean_object* v_xs_113_, lean_object* v_ys_114_){
_start:
{
uint8_t v___x_115_; 
v___x_115_ = l_Vector_instDecidableLEOfDecidableEqOfDecidableLT___redArg(v_n_109_, v_inst_110_, v_inst_112_, v_xs_113_, v_ys_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Vector_instDecidableLEOfDecidableEqOfDecidableLT___boxed(lean_object* v_00_u03b1_116_, lean_object* v_n_117_, lean_object* v_inst_118_, lean_object* v_inst_119_, lean_object* v_inst_120_, lean_object* v_xs_121_, lean_object* v_ys_122_){
_start:
{
uint8_t v_res_123_; lean_object* v_r_124_; 
v_res_123_ = l_Vector_instDecidableLEOfDecidableEqOfDecidableLT(v_00_u03b1_116_, v_n_117_, v_inst_118_, v_inst_119_, v_inst_120_, v_xs_121_, v_ys_122_);
v_r_124_ = lean_box(v_res_123_);
return v_r_124_;
}
}
lean_object* runtime_initialize_Init_Data_Vector_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Lex_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Lex_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BEq(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Vector_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Lex_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Vector_Lemmas(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Vector_Lex(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Lex_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Lex_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Lex_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Vector_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Vector_Lex(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Vector_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Lex_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Lex_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_BEq(uint8_t builtin);
lean_object* initialize_Init_Data_Vector_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Lex_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Vector_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Vector_Lex(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Lex_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Lex_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Lex_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Vector_Lex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Vector_Lex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Vector_Lex(builtin);
}
#ifdef __cplusplus
}
#endif

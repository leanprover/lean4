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
LEAN_EXPORT lean_object* l_Vector_instTransLt(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instTransLt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v_x_1_);
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
lean_dec_ref(v_x_10_);
v___x_16_ = lean_apply_1(v_h__1_11_, v_val_15_);
return v___x_16_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_instTransLt(lean_object* v_00_u03b1_17_, lean_object* v_n_18_, lean_object* v_inst_19_, lean_object* v_inst_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = lean_box(0);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_Vector_instTransLt___boxed(lean_object* v_00_u03b1_22_, lean_object* v_n_23_, lean_object* v_inst_24_, lean_object* v_inst_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Vector_instTransLt(v_00_u03b1_22_, v_n_23_, v_inst_24_, v_inst_25_);
lean_dec(v_n_23_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Vector_instTransLeOfLawfulOrderLTOfIsLinearOrder(lean_object* v_00_u03b1_27_, lean_object* v_n_28_, lean_object* v_inst_29_, lean_object* v_inst_30_, lean_object* v_inst_31_, lean_object* v_inst_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = lean_box(0);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Vector_instTransLeOfLawfulOrderLTOfIsLinearOrder___boxed(lean_object* v_00_u03b1_34_, lean_object* v_n_35_, lean_object* v_inst_36_, lean_object* v_inst_37_, lean_object* v_inst_38_, lean_object* v_inst_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Vector_instTransLeOfLawfulOrderLTOfIsLinearOrder(v_00_u03b1_34_, v_n_35_, v_inst_36_, v_inst_37_, v_inst_38_, v_inst_39_);
lean_dec(v_n_35_);
return v_res_40_;
}
}
LEAN_EXPORT uint8_t l_Vector_instDecidableLTOfDecidableEq___redArg___lam__0(lean_object* v_inst_41_, lean_object* v_x1_42_, lean_object* v_x2_43_){
_start:
{
lean_object* v___x_44_; uint8_t v___x_45_; 
v___x_44_ = lean_apply_2(v_inst_41_, v_x1_42_, v_x2_43_);
v___x_45_ = lean_unbox(v___x_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Vector_instDecidableLTOfDecidableEq___redArg___lam__0___boxed(lean_object* v_inst_46_, lean_object* v_x1_47_, lean_object* v_x2_48_){
_start:
{
uint8_t v_res_49_; lean_object* v_r_50_; 
v_res_49_ = l_Vector_instDecidableLTOfDecidableEq___redArg___lam__0(v_inst_46_, v_x1_47_, v_x2_48_);
v_r_50_ = lean_box(v_res_49_);
return v_r_50_;
}
}
LEAN_EXPORT uint8_t l_Vector_instDecidableLTOfDecidableEq___redArg(lean_object* v_n_51_, lean_object* v_inst_52_, lean_object* v_inst_53_, lean_object* v_xs_54_, lean_object* v_ys_55_){
_start:
{
lean_object* v___f_56_; lean_object* v___f_57_; uint8_t v___x_58_; 
v___f_56_ = lean_alloc_closure((void*)(l_Vector_instDecidableLTOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_56_, 0, v_inst_53_);
v___f_57_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_57_, 0, v_inst_52_);
v___x_58_ = l_Vector_lex___redArg(v_n_51_, v___f_57_, v_xs_54_, v_ys_55_, v___f_56_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Vector_instDecidableLTOfDecidableEq___redArg___boxed(lean_object* v_n_59_, lean_object* v_inst_60_, lean_object* v_inst_61_, lean_object* v_xs_62_, lean_object* v_ys_63_){
_start:
{
uint8_t v_res_64_; lean_object* v_r_65_; 
v_res_64_ = l_Vector_instDecidableLTOfDecidableEq___redArg(v_n_59_, v_inst_60_, v_inst_61_, v_xs_62_, v_ys_63_);
v_r_65_ = lean_box(v_res_64_);
return v_r_65_;
}
}
LEAN_EXPORT uint8_t l_Vector_instDecidableLTOfDecidableEq(lean_object* v_00_u03b1_66_, lean_object* v_n_67_, lean_object* v_inst_68_, lean_object* v_inst_69_, lean_object* v_inst_70_, lean_object* v_xs_71_, lean_object* v_ys_72_){
_start:
{
uint8_t v___x_73_; 
v___x_73_ = l_Vector_instDecidableLTOfDecidableEq___redArg(v_n_67_, v_inst_68_, v_inst_70_, v_xs_71_, v_ys_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Vector_instDecidableLTOfDecidableEq___boxed(lean_object* v_00_u03b1_74_, lean_object* v_n_75_, lean_object* v_inst_76_, lean_object* v_inst_77_, lean_object* v_inst_78_, lean_object* v_xs_79_, lean_object* v_ys_80_){
_start:
{
uint8_t v_res_81_; lean_object* v_r_82_; 
v_res_81_ = l_Vector_instDecidableLTOfDecidableEq(v_00_u03b1_74_, v_n_75_, v_inst_76_, v_inst_77_, v_inst_78_, v_xs_79_, v_ys_80_);
v_r_82_ = lean_box(v_res_81_);
return v_r_82_;
}
}
LEAN_EXPORT uint8_t l_Vector_instDecidableLEOfDecidableEqOfDecidableLT___redArg(lean_object* v_n_83_, lean_object* v_inst_84_, lean_object* v_inst_85_, lean_object* v_xs_86_, lean_object* v_ys_87_){
_start:
{
lean_object* v___f_88_; lean_object* v___f_89_; uint8_t v___x_90_; 
v___f_88_ = lean_alloc_closure((void*)(l_Vector_instDecidableLTOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_88_, 0, v_inst_85_);
v___f_89_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_89_, 0, v_inst_84_);
v___x_90_ = l_Vector_lex___redArg(v_n_83_, v___f_89_, v_ys_87_, v_xs_86_, v___f_88_);
if (v___x_90_ == 0)
{
uint8_t v___x_91_; 
v___x_91_ = 1;
return v___x_91_;
}
else
{
uint8_t v___x_92_; 
v___x_92_ = 0;
return v___x_92_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_instDecidableLEOfDecidableEqOfDecidableLT___redArg___boxed(lean_object* v_n_93_, lean_object* v_inst_94_, lean_object* v_inst_95_, lean_object* v_xs_96_, lean_object* v_ys_97_){
_start:
{
uint8_t v_res_98_; lean_object* v_r_99_; 
v_res_98_ = l_Vector_instDecidableLEOfDecidableEqOfDecidableLT___redArg(v_n_93_, v_inst_94_, v_inst_95_, v_xs_96_, v_ys_97_);
v_r_99_ = lean_box(v_res_98_);
return v_r_99_;
}
}
LEAN_EXPORT uint8_t l_Vector_instDecidableLEOfDecidableEqOfDecidableLT(lean_object* v_00_u03b1_100_, lean_object* v_n_101_, lean_object* v_inst_102_, lean_object* v_inst_103_, lean_object* v_inst_104_, lean_object* v_xs_105_, lean_object* v_ys_106_){
_start:
{
uint8_t v___x_107_; 
v___x_107_ = l_Vector_instDecidableLEOfDecidableEqOfDecidableLT___redArg(v_n_101_, v_inst_102_, v_inst_104_, v_xs_105_, v_ys_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Vector_instDecidableLEOfDecidableEqOfDecidableLT___boxed(lean_object* v_00_u03b1_108_, lean_object* v_n_109_, lean_object* v_inst_110_, lean_object* v_inst_111_, lean_object* v_inst_112_, lean_object* v_xs_113_, lean_object* v_ys_114_){
_start:
{
uint8_t v_res_115_; lean_object* v_r_116_; 
v_res_115_ = l_Vector_instDecidableLEOfDecidableEqOfDecidableLT(v_00_u03b1_108_, v_n_109_, v_inst_110_, v_inst_111_, v_inst_112_, v_xs_113_, v_ys_114_);
v_r_116_ = lean_box(v_res_115_);
return v_r_116_;
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
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Vector_Lex(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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

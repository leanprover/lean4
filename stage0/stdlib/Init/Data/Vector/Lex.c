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
lean_object* v___x_13_; 
v___x_13_ = l___private_Init_Data_Vector_Lex_0__Break_runK_match__1_splitter___redArg(v_x_10_, v_h__1_11_, v_h__2_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_Vector_instTransLt(lean_object* v_00_u03b1_14_, lean_object* v_n_15_, lean_object* v_inst_16_, lean_object* v_inst_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = lean_box(0);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Vector_instTransLt___boxed(lean_object* v_00_u03b1_19_, lean_object* v_n_20_, lean_object* v_inst_21_, lean_object* v_inst_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_Vector_instTransLt(v_00_u03b1_19_, v_n_20_, v_inst_21_, v_inst_22_);
lean_dec(v_n_20_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Vector_instTransLeOfLawfulOrderLTOfIsLinearOrder(lean_object* v_00_u03b1_24_, lean_object* v_n_25_, lean_object* v_inst_26_, lean_object* v_inst_27_, lean_object* v_inst_28_, lean_object* v_inst_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = lean_box(0);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Vector_instTransLeOfLawfulOrderLTOfIsLinearOrder___boxed(lean_object* v_00_u03b1_31_, lean_object* v_n_32_, lean_object* v_inst_33_, lean_object* v_inst_34_, lean_object* v_inst_35_, lean_object* v_inst_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Vector_instTransLeOfLawfulOrderLTOfIsLinearOrder(v_00_u03b1_31_, v_n_32_, v_inst_33_, v_inst_34_, v_inst_35_, v_inst_36_);
lean_dec(v_n_32_);
return v_res_37_;
}
}
LEAN_EXPORT uint8_t l_Vector_instDecidableLTOfDecidableEq___redArg___lam__0(lean_object* v_inst_38_, lean_object* v_x1_39_, lean_object* v_x2_40_){
_start:
{
lean_object* v___x_41_; uint8_t v___x_42_; 
v___x_41_ = lean_apply_2(v_inst_38_, v_x1_39_, v_x2_40_);
v___x_42_ = lean_unbox(v___x_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Vector_instDecidableLTOfDecidableEq___redArg___lam__0___boxed(lean_object* v_inst_43_, lean_object* v_x1_44_, lean_object* v_x2_45_){
_start:
{
uint8_t v_res_46_; lean_object* v_r_47_; 
v_res_46_ = l_Vector_instDecidableLTOfDecidableEq___redArg___lam__0(v_inst_43_, v_x1_44_, v_x2_45_);
v_r_47_ = lean_box(v_res_46_);
return v_r_47_;
}
}
LEAN_EXPORT uint8_t l_Vector_instDecidableLTOfDecidableEq___redArg(lean_object* v_n_48_, lean_object* v_inst_49_, lean_object* v_inst_50_, lean_object* v_xs_51_, lean_object* v_ys_52_){
_start:
{
lean_object* v___f_53_; lean_object* v___f_54_; uint8_t v___x_55_; 
v___f_53_ = lean_alloc_closure((void*)(l_Vector_instDecidableLTOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_53_, 0, v_inst_50_);
v___f_54_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_54_, 0, v_inst_49_);
v___x_55_ = l_Vector_lex___redArg(v_n_48_, v___f_54_, v_xs_51_, v_ys_52_, v___f_53_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Vector_instDecidableLTOfDecidableEq___redArg___boxed(lean_object* v_n_56_, lean_object* v_inst_57_, lean_object* v_inst_58_, lean_object* v_xs_59_, lean_object* v_ys_60_){
_start:
{
uint8_t v_res_61_; lean_object* v_r_62_; 
v_res_61_ = l_Vector_instDecidableLTOfDecidableEq___redArg(v_n_56_, v_inst_57_, v_inst_58_, v_xs_59_, v_ys_60_);
v_r_62_ = lean_box(v_res_61_);
return v_r_62_;
}
}
LEAN_EXPORT uint8_t l_Vector_instDecidableLTOfDecidableEq(lean_object* v_00_u03b1_63_, lean_object* v_n_64_, lean_object* v_inst_65_, lean_object* v_inst_66_, lean_object* v_inst_67_, lean_object* v_xs_68_, lean_object* v_ys_69_){
_start:
{
uint8_t v___x_70_; 
v___x_70_ = l_Vector_instDecidableLTOfDecidableEq___redArg(v_n_64_, v_inst_65_, v_inst_67_, v_xs_68_, v_ys_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Vector_instDecidableLTOfDecidableEq___boxed(lean_object* v_00_u03b1_71_, lean_object* v_n_72_, lean_object* v_inst_73_, lean_object* v_inst_74_, lean_object* v_inst_75_, lean_object* v_xs_76_, lean_object* v_ys_77_){
_start:
{
uint8_t v_res_78_; lean_object* v_r_79_; 
v_res_78_ = l_Vector_instDecidableLTOfDecidableEq(v_00_u03b1_71_, v_n_72_, v_inst_73_, v_inst_74_, v_inst_75_, v_xs_76_, v_ys_77_);
v_r_79_ = lean_box(v_res_78_);
return v_r_79_;
}
}
LEAN_EXPORT uint8_t l_Vector_instDecidableLEOfDecidableEqOfDecidableLT___redArg(lean_object* v_n_80_, lean_object* v_inst_81_, lean_object* v_inst_82_, lean_object* v_xs_83_, lean_object* v_ys_84_){
_start:
{
lean_object* v___f_85_; lean_object* v___f_86_; uint8_t v___x_87_; 
v___f_85_ = lean_alloc_closure((void*)(l_Vector_instDecidableLTOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_85_, 0, v_inst_82_);
v___f_86_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_86_, 0, v_inst_81_);
v___x_87_ = l_Vector_lex___redArg(v_n_80_, v___f_86_, v_ys_84_, v_xs_83_, v___f_85_);
if (v___x_87_ == 0)
{
uint8_t v___x_88_; 
v___x_88_ = 1;
return v___x_88_;
}
else
{
uint8_t v___x_89_; 
v___x_89_ = 0;
return v___x_89_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_instDecidableLEOfDecidableEqOfDecidableLT___redArg___boxed(lean_object* v_n_90_, lean_object* v_inst_91_, lean_object* v_inst_92_, lean_object* v_xs_93_, lean_object* v_ys_94_){
_start:
{
uint8_t v_res_95_; lean_object* v_r_96_; 
v_res_95_ = l_Vector_instDecidableLEOfDecidableEqOfDecidableLT___redArg(v_n_90_, v_inst_91_, v_inst_92_, v_xs_93_, v_ys_94_);
v_r_96_ = lean_box(v_res_95_);
return v_r_96_;
}
}
LEAN_EXPORT uint8_t l_Vector_instDecidableLEOfDecidableEqOfDecidableLT(lean_object* v_00_u03b1_97_, lean_object* v_n_98_, lean_object* v_inst_99_, lean_object* v_inst_100_, lean_object* v_inst_101_, lean_object* v_xs_102_, lean_object* v_ys_103_){
_start:
{
uint8_t v___x_104_; 
v___x_104_ = l_Vector_instDecidableLEOfDecidableEqOfDecidableLT___redArg(v_n_98_, v_inst_99_, v_inst_101_, v_xs_102_, v_ys_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Vector_instDecidableLEOfDecidableEqOfDecidableLT___boxed(lean_object* v_00_u03b1_105_, lean_object* v_n_106_, lean_object* v_inst_107_, lean_object* v_inst_108_, lean_object* v_inst_109_, lean_object* v_xs_110_, lean_object* v_ys_111_){
_start:
{
uint8_t v_res_112_; lean_object* v_r_113_; 
v_res_112_ = l_Vector_instDecidableLEOfDecidableEqOfDecidableLT(v_00_u03b1_105_, v_n_106_, v_inst_107_, v_inst_108_, v_inst_109_, v_xs_110_, v_ys_111_);
v_r_113_ = lean_box(v_res_112_);
return v_r_113_;
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

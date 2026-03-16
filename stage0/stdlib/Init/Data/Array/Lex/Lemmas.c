// Lean compiler output
// Module: Init.Data.Array.Lex.Lemmas
// Imports: import all Init.Data.Array.Lex.Basic public import Init.Data.Array.Lex.Basic import Init.Data.Range.Polymorphic.NatLemmas public import Init.Data.BEq import Init.Data.Array.DecidableEq import Init.Data.Array.Lemmas import Init.Data.Bool import Init.Data.List.Lex import Init.Data.Range.Polymorphic.Lemmas
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
uint8_t l_Array_lex___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lex_Lemmas_0__Break_runK_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lex_Lemmas_0__Break_runK_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lex_Lemmas_0__List_forIn_x27__cons_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lex_Lemmas_0__List_forIn_x27__cons_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instTransLt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instTransLeOfLawfulOrderLTOfIsLinearOrder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_instDecidableLTOfDecidableEq___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instDecidableLTOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_instDecidableLTOfDecidableEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instDecidableLTOfDecidableEq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_instDecidableLTOfDecidableEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instDecidableLTOfDecidableEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_instDecidableLEOfDecidableEqOfDecidableLT___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instDecidableLEOfDecidableEqOfDecidableLT___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_instDecidableLEOfDecidableEqOfDecidableLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instDecidableLEOfDecidableEqOfDecidableLT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lex_Lemmas_0__Break_runK_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lex_Lemmas_0__Break_runK_match__1_splitter(lean_object* v_00_u03b1_8_, lean_object* v_motive_9_, lean_object* v_x_10_, lean_object* v_h__1_11_, lean_object* v_h__2_12_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = l___private_Init_Data_Array_Lex_Lemmas_0__Break_runK_match__1_splitter___redArg(v_x_10_, v_h__1_11_, v_h__2_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lex_Lemmas_0__List_forIn_x27__cons_match__1_splitter___redArg(lean_object* v_x_14_, lean_object* v_h__1_15_, lean_object* v_h__2_16_){
_start:
{
if (lean_obj_tag(v_x_14_) == 0)
{
lean_object* v_a_17_; lean_object* v___x_18_; 
lean_dec(v_h__2_16_);
v_a_17_ = lean_ctor_get(v_x_14_, 0);
lean_inc(v_a_17_);
lean_dec_ref(v_x_14_);
v___x_18_ = lean_apply_1(v_h__1_15_, v_a_17_);
return v___x_18_;
}
else
{
lean_object* v_a_19_; lean_object* v___x_20_; 
lean_dec(v_h__1_15_);
v_a_19_ = lean_ctor_get(v_x_14_, 0);
lean_inc(v_a_19_);
lean_dec_ref(v_x_14_);
v___x_20_ = lean_apply_1(v_h__2_16_, v_a_19_);
return v___x_20_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lex_Lemmas_0__List_forIn_x27__cons_match__1_splitter(lean_object* v_00_u03b2_21_, lean_object* v_motive_22_, lean_object* v_x_23_, lean_object* v_h__1_24_, lean_object* v_h__2_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = l___private_Init_Data_Array_Lex_Lemmas_0__List_forIn_x27__cons_match__1_splitter___redArg(v_x_23_, v_h__1_24_, v_h__2_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Array_instTransLt(lean_object* v_00_u03b1_27_, lean_object* v_inst_28_, lean_object* v_inst_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = lean_box(0);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Array_instTransLeOfLawfulOrderLTOfIsLinearOrder(lean_object* v_00_u03b1_31_, lean_object* v_inst_32_, lean_object* v_inst_33_, lean_object* v_inst_34_, lean_object* v_inst_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = lean_box(0);
return v___x_36_;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableLTOfDecidableEq___redArg___lam__0(lean_object* v_inst_37_, lean_object* v_x1_38_, lean_object* v_x2_39_){
_start:
{
lean_object* v___x_40_; uint8_t v___x_41_; 
v___x_40_ = lean_apply_2(v_inst_37_, v_x1_38_, v_x2_39_);
v___x_41_ = lean_unbox(v___x_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableLTOfDecidableEq___redArg___lam__0___boxed(lean_object* v_inst_42_, lean_object* v_x1_43_, lean_object* v_x2_44_){
_start:
{
uint8_t v_res_45_; lean_object* v_r_46_; 
v_res_45_ = l_Array_instDecidableLTOfDecidableEq___redArg___lam__0(v_inst_42_, v_x1_43_, v_x2_44_);
v_r_46_ = lean_box(v_res_45_);
return v_r_46_;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableLTOfDecidableEq___redArg(lean_object* v_inst_47_, lean_object* v_inst_48_, lean_object* v_xs_49_, lean_object* v_ys_50_){
_start:
{
lean_object* v___f_51_; lean_object* v___f_52_; uint8_t v___x_53_; 
v___f_51_ = lean_alloc_closure((void*)(l_Array_instDecidableLTOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_51_, 0, v_inst_48_);
v___f_52_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_52_, 0, v_inst_47_);
v___x_53_ = l_Array_lex___redArg(v___f_52_, v_xs_49_, v_ys_50_, v___f_51_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableLTOfDecidableEq___redArg___boxed(lean_object* v_inst_54_, lean_object* v_inst_55_, lean_object* v_xs_56_, lean_object* v_ys_57_){
_start:
{
uint8_t v_res_58_; lean_object* v_r_59_; 
v_res_58_ = l_Array_instDecidableLTOfDecidableEq___redArg(v_inst_54_, v_inst_55_, v_xs_56_, v_ys_57_);
v_r_59_ = lean_box(v_res_58_);
return v_r_59_;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableLTOfDecidableEq(lean_object* v_00_u03b1_60_, lean_object* v_inst_61_, lean_object* v_inst_62_, lean_object* v_inst_63_, lean_object* v_xs_64_, lean_object* v_ys_65_){
_start:
{
uint8_t v___x_66_; 
v___x_66_ = l_Array_instDecidableLTOfDecidableEq___redArg(v_inst_61_, v_inst_63_, v_xs_64_, v_ys_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableLTOfDecidableEq___boxed(lean_object* v_00_u03b1_67_, lean_object* v_inst_68_, lean_object* v_inst_69_, lean_object* v_inst_70_, lean_object* v_xs_71_, lean_object* v_ys_72_){
_start:
{
uint8_t v_res_73_; lean_object* v_r_74_; 
v_res_73_ = l_Array_instDecidableLTOfDecidableEq(v_00_u03b1_67_, v_inst_68_, v_inst_69_, v_inst_70_, v_xs_71_, v_ys_72_);
v_r_74_ = lean_box(v_res_73_);
return v_r_74_;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableLEOfDecidableEqOfDecidableLT___redArg(lean_object* v_inst_75_, lean_object* v_inst_76_, lean_object* v_xs_77_, lean_object* v_ys_78_){
_start:
{
lean_object* v___f_79_; lean_object* v___f_80_; uint8_t v___x_81_; 
v___f_79_ = lean_alloc_closure((void*)(l_Array_instDecidableLTOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_79_, 0, v_inst_76_);
v___f_80_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_80_, 0, v_inst_75_);
v___x_81_ = l_Array_lex___redArg(v___f_80_, v_ys_78_, v_xs_77_, v___f_79_);
if (v___x_81_ == 0)
{
uint8_t v___x_82_; 
v___x_82_ = 1;
return v___x_82_;
}
else
{
uint8_t v___x_83_; 
v___x_83_ = 0;
return v___x_83_;
}
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableLEOfDecidableEqOfDecidableLT___redArg___boxed(lean_object* v_inst_84_, lean_object* v_inst_85_, lean_object* v_xs_86_, lean_object* v_ys_87_){
_start:
{
uint8_t v_res_88_; lean_object* v_r_89_; 
v_res_88_ = l_Array_instDecidableLEOfDecidableEqOfDecidableLT___redArg(v_inst_84_, v_inst_85_, v_xs_86_, v_ys_87_);
v_r_89_ = lean_box(v_res_88_);
return v_r_89_;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableLEOfDecidableEqOfDecidableLT(lean_object* v_00_u03b1_90_, lean_object* v_inst_91_, lean_object* v_inst_92_, lean_object* v_inst_93_, lean_object* v_xs_94_, lean_object* v_ys_95_){
_start:
{
uint8_t v___x_96_; 
v___x_96_ = l_Array_instDecidableLEOfDecidableEqOfDecidableLT___redArg(v_inst_91_, v_inst_93_, v_xs_94_, v_ys_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableLEOfDecidableEqOfDecidableLT___boxed(lean_object* v_00_u03b1_97_, lean_object* v_inst_98_, lean_object* v_inst_99_, lean_object* v_inst_100_, lean_object* v_xs_101_, lean_object* v_ys_102_){
_start:
{
uint8_t v_res_103_; lean_object* v_r_104_; 
v_res_103_ = l_Array_instDecidableLEOfDecidableEqOfDecidableLT(v_00_u03b1_97_, v_inst_98_, v_inst_99_, v_inst_100_, v_xs_101_, v_ys_102_);
v_r_104_ = lean_box(v_res_103_);
return v_r_104_;
}
}
lean_object* runtime_initialize_Init_Data_Array_Lex_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Lex_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_NatLemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BEq(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_DecidableEq(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Lex(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Lemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Array_Lex_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Array_Lex_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Lex_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_NatLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_DecidableEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Lex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Array_Lex_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Array_Lex_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Lex_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_NatLemmas(uint8_t builtin);
lean_object* initialize_Init_Data_BEq(uint8_t builtin);
lean_object* initialize_Init_Data_Array_DecidableEq(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Bool(uint8_t builtin);
lean_object* initialize_Init_Data_List_Lex(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Array_Lex_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_Lex_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Lex_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_NatLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_DecidableEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Lex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Lex_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Array_Lex_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Array_Lex_Lemmas(builtin);
}
#ifdef __cplusplus
}
#endif

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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lex_Lemmas_0__List_forIn_x27__cons_match__1_splitter___redArg(lean_object* v_x_17_, lean_object* v_h__1_18_, lean_object* v_h__2_19_){
_start:
{
if (lean_obj_tag(v_x_17_) == 0)
{
lean_object* v_a_20_; lean_object* v___x_21_; 
lean_dec(v_h__2_19_);
v_a_20_ = lean_ctor_get(v_x_17_, 0);
lean_inc(v_a_20_);
lean_dec_ref(v_x_17_);
v___x_21_ = lean_apply_1(v_h__1_18_, v_a_20_);
return v___x_21_;
}
else
{
lean_object* v_a_22_; lean_object* v___x_23_; 
lean_dec(v_h__1_18_);
v_a_22_ = lean_ctor_get(v_x_17_, 0);
lean_inc(v_a_22_);
lean_dec_ref(v_x_17_);
v___x_23_ = lean_apply_1(v_h__2_19_, v_a_22_);
return v___x_23_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lex_Lemmas_0__List_forIn_x27__cons_match__1_splitter(lean_object* v_00_u03b2_24_, lean_object* v_motive_25_, lean_object* v_x_26_, lean_object* v_h__1_27_, lean_object* v_h__2_28_){
_start:
{
if (lean_obj_tag(v_x_26_) == 0)
{
lean_object* v_a_29_; lean_object* v___x_30_; 
lean_dec(v_h__2_28_);
v_a_29_ = lean_ctor_get(v_x_26_, 0);
lean_inc(v_a_29_);
lean_dec_ref(v_x_26_);
v___x_30_ = lean_apply_1(v_h__1_27_, v_a_29_);
return v___x_30_;
}
else
{
lean_object* v_a_31_; lean_object* v___x_32_; 
lean_dec(v_h__1_27_);
v_a_31_ = lean_ctor_get(v_x_26_, 0);
lean_inc(v_a_31_);
lean_dec_ref(v_x_26_);
v___x_32_ = lean_apply_1(v_h__2_28_, v_a_31_);
return v___x_32_;
}
}
}
LEAN_EXPORT lean_object* l_Array_instTransLt(lean_object* v_00_u03b1_33_, lean_object* v_inst_34_, lean_object* v_inst_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = lean_box(0);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Array_instTransLeOfLawfulOrderLTOfIsLinearOrder(lean_object* v_00_u03b1_37_, lean_object* v_inst_38_, lean_object* v_inst_39_, lean_object* v_inst_40_, lean_object* v_inst_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = lean_box(0);
return v___x_42_;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableLTOfDecidableEq___redArg___lam__0(lean_object* v_inst_43_, lean_object* v_x1_44_, lean_object* v_x2_45_){
_start:
{
lean_object* v___x_46_; uint8_t v___x_47_; 
v___x_46_ = lean_apply_2(v_inst_43_, v_x1_44_, v_x2_45_);
v___x_47_ = lean_unbox(v___x_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableLTOfDecidableEq___redArg___lam__0___boxed(lean_object* v_inst_48_, lean_object* v_x1_49_, lean_object* v_x2_50_){
_start:
{
uint8_t v_res_51_; lean_object* v_r_52_; 
v_res_51_ = l_Array_instDecidableLTOfDecidableEq___redArg___lam__0(v_inst_48_, v_x1_49_, v_x2_50_);
v_r_52_ = lean_box(v_res_51_);
return v_r_52_;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableLTOfDecidableEq___redArg(lean_object* v_inst_53_, lean_object* v_inst_54_, lean_object* v_xs_55_, lean_object* v_ys_56_){
_start:
{
lean_object* v___f_57_; lean_object* v___f_58_; uint8_t v___x_59_; 
v___f_57_ = lean_alloc_closure((void*)(l_Array_instDecidableLTOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_57_, 0, v_inst_54_);
v___f_58_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_58_, 0, v_inst_53_);
v___x_59_ = l_Array_lex___redArg(v___f_58_, v_xs_55_, v_ys_56_, v___f_57_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableLTOfDecidableEq___redArg___boxed(lean_object* v_inst_60_, lean_object* v_inst_61_, lean_object* v_xs_62_, lean_object* v_ys_63_){
_start:
{
uint8_t v_res_64_; lean_object* v_r_65_; 
v_res_64_ = l_Array_instDecidableLTOfDecidableEq___redArg(v_inst_60_, v_inst_61_, v_xs_62_, v_ys_63_);
v_r_65_ = lean_box(v_res_64_);
return v_r_65_;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableLTOfDecidableEq(lean_object* v_00_u03b1_66_, lean_object* v_inst_67_, lean_object* v_inst_68_, lean_object* v_inst_69_, lean_object* v_xs_70_, lean_object* v_ys_71_){
_start:
{
uint8_t v___x_72_; 
v___x_72_ = l_Array_instDecidableLTOfDecidableEq___redArg(v_inst_67_, v_inst_69_, v_xs_70_, v_ys_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableLTOfDecidableEq___boxed(lean_object* v_00_u03b1_73_, lean_object* v_inst_74_, lean_object* v_inst_75_, lean_object* v_inst_76_, lean_object* v_xs_77_, lean_object* v_ys_78_){
_start:
{
uint8_t v_res_79_; lean_object* v_r_80_; 
v_res_79_ = l_Array_instDecidableLTOfDecidableEq(v_00_u03b1_73_, v_inst_74_, v_inst_75_, v_inst_76_, v_xs_77_, v_ys_78_);
v_r_80_ = lean_box(v_res_79_);
return v_r_80_;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableLEOfDecidableEqOfDecidableLT___redArg(lean_object* v_inst_81_, lean_object* v_inst_82_, lean_object* v_xs_83_, lean_object* v_ys_84_){
_start:
{
lean_object* v___f_85_; lean_object* v___f_86_; uint8_t v___x_87_; 
v___f_85_ = lean_alloc_closure((void*)(l_Array_instDecidableLTOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_85_, 0, v_inst_82_);
v___f_86_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_86_, 0, v_inst_81_);
v___x_87_ = l_Array_lex___redArg(v___f_86_, v_ys_84_, v_xs_83_, v___f_85_);
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
LEAN_EXPORT lean_object* l_Array_instDecidableLEOfDecidableEqOfDecidableLT___redArg___boxed(lean_object* v_inst_90_, lean_object* v_inst_91_, lean_object* v_xs_92_, lean_object* v_ys_93_){
_start:
{
uint8_t v_res_94_; lean_object* v_r_95_; 
v_res_94_ = l_Array_instDecidableLEOfDecidableEqOfDecidableLT___redArg(v_inst_90_, v_inst_91_, v_xs_92_, v_ys_93_);
v_r_95_ = lean_box(v_res_94_);
return v_r_95_;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableLEOfDecidableEqOfDecidableLT(lean_object* v_00_u03b1_96_, lean_object* v_inst_97_, lean_object* v_inst_98_, lean_object* v_inst_99_, lean_object* v_xs_100_, lean_object* v_ys_101_){
_start:
{
uint8_t v___x_102_; 
v___x_102_ = l_Array_instDecidableLEOfDecidableEqOfDecidableLT___redArg(v_inst_97_, v_inst_99_, v_xs_100_, v_ys_101_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableLEOfDecidableEqOfDecidableLT___boxed(lean_object* v_00_u03b1_103_, lean_object* v_inst_104_, lean_object* v_inst_105_, lean_object* v_inst_106_, lean_object* v_xs_107_, lean_object* v_ys_108_){
_start:
{
uint8_t v_res_109_; lean_object* v_r_110_; 
v_res_109_ = l_Array_instDecidableLEOfDecidableEqOfDecidableLT(v_00_u03b1_103_, v_inst_104_, v_inst_105_, v_inst_106_, v_xs_107_, v_ys_108_);
v_r_110_ = lean_box(v_res_109_);
return v_r_110_;
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

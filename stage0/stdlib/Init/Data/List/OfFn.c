// Lean compiler output
// Module: Init.Data.List.OfFn
// Imports: public import Init.Data.Fin.Fold public import Init.NotationExtra import Init.Data.Fin.Lemmas import Init.Data.List.Lemmas import Init.Data.Nat.Lemmas import Init.Data.Option.Lemmas
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_List_reverse(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_foldr_loop___at___00List_ofFn_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_ofFn___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_ofFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_foldr_loop___at___00List_ofFn_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_foldr_loop___at___00List_ofFn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_ofFnM___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_ofFnM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_List_ofFnM___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_reverse, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_List_ofFnM___redArg___closed__0 = (const lean_object*)&l_List_ofFnM___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_List_ofFnM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_ofFnM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_foldr_loop___at___00List_ofFn_spec__0___redArg(lean_object* v_f_1_, lean_object* v_i_2_, lean_object* v_a_3_){
_start:
{
lean_object* v_zero_4_; uint8_t v_isZero_5_; 
v_zero_4_ = lean_unsigned_to_nat(0u);
v_isZero_5_ = lean_nat_dec_eq(v_i_2_, v_zero_4_);
if (v_isZero_5_ == 1)
{
lean_dec(v_i_2_);
lean_dec(v_f_1_);
return v_a_3_;
}
else
{
lean_object* v_one_6_; lean_object* v_n_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v_one_6_ = lean_unsigned_to_nat(1u);
v_n_7_ = lean_nat_sub(v_i_2_, v_one_6_);
lean_dec(v_i_2_);
lean_inc(v_f_1_);
lean_inc(v_n_7_);
v___x_8_ = lean_apply_1(v_f_1_, v_n_7_);
v___x_9_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_9_, 0, v___x_8_);
lean_ctor_set(v___x_9_, 1, v_a_3_);
v_i_2_ = v_n_7_;
v_a_3_ = v___x_9_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_ofFn___redArg(lean_object* v_n_11_, lean_object* v_f_12_){
_start:
{
lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_13_ = lean_box(0);
v___x_14_ = l_Fin_foldr_loop___at___00List_ofFn_spec__0___redArg(v_f_12_, v_n_11_, v___x_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_List_ofFn(lean_object* v_00_u03b1_15_, lean_object* v_n_16_, lean_object* v_f_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = l_List_ofFn___redArg(v_n_16_, v_f_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Fin_foldr_loop___at___00List_ofFn_spec__0(lean_object* v_00_u03b1_19_, lean_object* v_f_20_, lean_object* v_n_21_, lean_object* v_i_22_, lean_object* v_a_23_, lean_object* v_a_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = l_Fin_foldr_loop___at___00List_ofFn_spec__0___redArg(v_f_20_, v_i_22_, v_a_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Fin_foldr_loop___at___00List_ofFn_spec__0___boxed(lean_object* v_00_u03b1_26_, lean_object* v_f_27_, lean_object* v_n_28_, lean_object* v_i_29_, lean_object* v_a_30_, lean_object* v_a_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Fin_foldr_loop___at___00List_ofFn_spec__0(v_00_u03b1_26_, v_f_27_, v_n_28_, v_i_29_, v_a_30_, v_a_31_);
lean_dec(v_n_28_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l_List_ofFnM___redArg___lam__0(lean_object* v_xs_33_, lean_object* v_x_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_35_, 0, v_x_34_);
lean_ctor_set(v___x_35_, 1, v_xs_33_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_List_ofFnM___redArg___lam__1(lean_object* v_f_36_, lean_object* v_map_37_, lean_object* v_xs_38_, lean_object* v_i_39_){
_start:
{
lean_object* v___f_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v___f_40_ = lean_alloc_closure((void*)(l_List_ofFnM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_40_, 0, v_xs_38_);
v___x_41_ = lean_apply_1(v_f_36_, v_i_39_);
v___x_42_ = lean_apply_4(v_map_37_, lean_box(0), lean_box(0), v___f_40_, v___x_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_List_ofFnM___redArg(lean_object* v_n_44_, lean_object* v_inst_45_, lean_object* v_f_46_){
_start:
{
lean_object* v_toApplicative_47_; lean_object* v_toFunctor_48_; lean_object* v_map_49_; lean_object* v___f_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v_toApplicative_47_ = lean_ctor_get(v_inst_45_, 0);
v_toFunctor_48_ = lean_ctor_get(v_toApplicative_47_, 0);
v_map_49_ = lean_ctor_get(v_toFunctor_48_, 0);
lean_inc(v_map_49_);
lean_inc(v_map_49_);
v___f_50_ = lean_alloc_closure((void*)(l_List_ofFnM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_50_, 0, v_f_46_);
lean_closure_set(v___f_50_, 1, v_map_49_);
v___x_51_ = ((lean_object*)(l_List_ofFnM___redArg___closed__0));
v___x_52_ = lean_box(0);
v___x_53_ = lean_unsigned_to_nat(0u);
v___x_54_ = l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop(lean_box(0), lean_box(0), v_inst_45_, v_n_44_, v___f_50_, v___x_52_, v___x_53_);
v___x_55_ = lean_apply_4(v_map_49_, lean_box(0), lean_box(0), v___x_51_, v___x_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_List_ofFnM(lean_object* v_m_56_, lean_object* v_00_u03b1_57_, lean_object* v_n_58_, lean_object* v_inst_59_, lean_object* v_f_60_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = l_List_ofFnM___redArg(v_n_58_, v_inst_59_, v_f_60_);
return v___x_61_;
}
}
lean_object* runtime_initialize_Init_Data_Fin_Fold(uint8_t builtin);
lean_object* runtime_initialize_Init_NotationExtra(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Fin_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_List_OfFn(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Fin_Fold(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_NotationExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Fin_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_List_OfFn(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Fin_Fold(uint8_t builtin);
lean_object* initialize_Init_NotationExtra(uint8_t builtin);
lean_object* initialize_Init_Data_Fin_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_List_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_List_OfFn(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Fin_Fold(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_NotationExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Fin_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_OfFn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_List_OfFn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_List_OfFn(builtin);
}
#ifdef __cplusplus
}
#endif

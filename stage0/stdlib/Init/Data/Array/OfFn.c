// Lean compiler output
// Module: Init.Data.Array.OfFn
// Imports: import all Init.Data.Array.Basic public import Init.Data.List.OfFn import Init.Data.Array.Bootstrap import Init.Data.Array.Monadic import Init.Data.Fin.Lemmas import Init.Data.List.FinRange import Init.Data.Option.Lemmas import Init.Omega
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
lean_object* l_Array_push___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_OfFn_0__Array_ofFn_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_OfFn_0__Array_ofFn_go_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_OfFn_0__Array_ofFn_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_OfFn_0__Array_ofFn_go_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_ofFnM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_ofFnM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_ofFnM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_OfFn_0__Array_ofFn_go_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
_start:
{
lean_object* v_zero_4_; uint8_t v_isZero_5_; 
v_zero_4_ = lean_unsigned_to_nat(0u);
v_isZero_5_ = lean_nat_dec_eq(v_x_1_, v_zero_4_);
if (v_isZero_5_ == 1)
{
lean_object* v___x_6_; 
lean_dec(v_h__1_2_);
v___x_6_ = lean_apply_1(v_h__2_3_, lean_box(0));
return v___x_6_;
}
else
{
lean_object* v_one_7_; lean_object* v_n_8_; lean_object* v___x_9_; 
lean_dec(v_h__2_3_);
v_one_7_ = lean_unsigned_to_nat(1u);
v_n_8_ = lean_nat_sub(v_x_1_, v_one_7_);
v___x_9_ = lean_apply_2(v_h__1_2_, v_n_8_, lean_box(0));
return v___x_9_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_OfFn_0__Array_ofFn_go_match__1_splitter___redArg___boxed(lean_object* v_x_10_, lean_object* v_h__1_11_, lean_object* v_h__2_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l___private_Init_Data_Array_OfFn_0__Array_ofFn_go_match__1_splitter___redArg(v_x_10_, v_h__1_11_, v_h__2_12_);
lean_dec(v_x_10_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_OfFn_0__Array_ofFn_go_match__1_splitter(lean_object* v_n_14_, lean_object* v_motive_15_, lean_object* v_x_16_, lean_object* v_x_17_, lean_object* v_h__1_18_, lean_object* v_h__2_19_){
_start:
{
lean_object* v_zero_20_; uint8_t v_isZero_21_; 
v_zero_20_ = lean_unsigned_to_nat(0u);
v_isZero_21_ = lean_nat_dec_eq(v_x_16_, v_zero_20_);
if (v_isZero_21_ == 1)
{
lean_object* v___x_22_; 
lean_dec(v_h__1_18_);
v___x_22_ = lean_apply_1(v_h__2_19_, lean_box(0));
return v___x_22_;
}
else
{
lean_object* v_one_23_; lean_object* v_n_24_; lean_object* v___x_25_; 
lean_dec(v_h__2_19_);
v_one_23_ = lean_unsigned_to_nat(1u);
v_n_24_ = lean_nat_sub(v_x_16_, v_one_23_);
v___x_25_ = lean_apply_2(v_h__1_18_, v_n_24_, lean_box(0));
return v___x_25_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_OfFn_0__Array_ofFn_go_match__1_splitter___boxed(lean_object* v_n_26_, lean_object* v_motive_27_, lean_object* v_x_28_, lean_object* v_x_29_, lean_object* v_h__1_30_, lean_object* v_h__2_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l___private_Init_Data_Array_OfFn_0__Array_ofFn_go_match__1_splitter(v_n_26_, v_motive_27_, v_x_28_, v_x_29_, v_h__1_30_, v_h__2_31_);
lean_dec(v_x_28_);
lean_dec(v_n_26_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l_Array_ofFnM___redArg___lam__0(lean_object* v_toFunctor_33_, lean_object* v_f_34_, lean_object* v_xs_35_, lean_object* v_i_36_){
_start:
{
lean_object* v_map_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v_map_37_ = lean_ctor_get(v_toFunctor_33_, 0);
lean_inc(v_map_37_);
lean_dec_ref(v_toFunctor_33_);
v___x_38_ = lean_alloc_closure((void*)(l_Array_push___boxed), 3, 2);
lean_closure_set(v___x_38_, 0, lean_box(0));
lean_closure_set(v___x_38_, 1, v_xs_35_);
v___x_39_ = lean_apply_1(v_f_34_, v_i_36_);
v___x_40_ = lean_apply_4(v_map_37_, lean_box(0), lean_box(0), v___x_38_, v___x_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Array_ofFnM___redArg(lean_object* v_n_41_, lean_object* v_inst_42_, lean_object* v_f_43_){
_start:
{
lean_object* v_toApplicative_44_; lean_object* v_toFunctor_45_; lean_object* v___f_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v_toApplicative_44_ = lean_ctor_get(v_inst_42_, 0);
v_toFunctor_45_ = lean_ctor_get(v_toApplicative_44_, 0);
lean_inc_ref(v_toFunctor_45_);
v___f_46_ = lean_alloc_closure((void*)(l_Array_ofFnM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_46_, 0, v_toFunctor_45_);
lean_closure_set(v___f_46_, 1, v_f_43_);
v___x_47_ = lean_mk_empty_array_with_capacity(v_n_41_);
v___x_48_ = lean_unsigned_to_nat(0u);
v___x_49_ = l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop(lean_box(0), lean_box(0), v_inst_42_, v_n_41_, v___f_46_, v___x_47_, v___x_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Array_ofFnM(lean_object* v_m_50_, lean_object* v_00_u03b1_51_, lean_object* v_n_52_, lean_object* v_inst_53_, lean_object* v_f_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = l_Array_ofFnM___redArg(v_n_52_, v_inst_53_, v_f_54_);
return v___x_55_;
}
}
lean_object* runtime_initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_OfFn(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Monadic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Fin_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_FinRange(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Array_OfFn(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_OfFn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Monadic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Fin_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_FinRange(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Array_OfFn(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_List_OfFn(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Monadic(uint8_t builtin);
lean_object* initialize_Init_Data_Fin_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_List_FinRange(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Array_OfFn(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_OfFn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Monadic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Fin_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_FinRange(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_OfFn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Array_OfFn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Array_OfFn(builtin);
}
#ifdef __cplusplus
}
#endif

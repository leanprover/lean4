// Lean compiler output
// Module: Init.Data.Fin.Iterate
// Imports: public import Init.Data.Fin.Basic import Init.PropLemmas import Init.WFTactics import Init.Hints
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_hIterateFrom___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_hIterateFrom___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_hIterateFrom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_hIterateFrom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_hIterate___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_hIterate___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_hIterate(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_hIterate___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_hIterateFrom___redArg(lean_object* v_n_1_, lean_object* v_f_2_, lean_object* v_i_3_, lean_object* v_a_4_){
_start:
{
uint8_t v___x_5_; 
v___x_5_ = lean_nat_dec_lt(v_i_3_, v_n_1_);
if (v___x_5_ == 0)
{
lean_dec(v_i_3_);
lean_dec(v_f_2_);
return v_a_4_;
}
else
{
lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_6_ = lean_unsigned_to_nat(1u);
v___x_7_ = lean_nat_add(v_i_3_, v___x_6_);
lean_inc(v_f_2_);
v___x_8_ = lean_apply_2(v_f_2_, v_i_3_, v_a_4_);
v_i_3_ = v___x_7_;
v_a_4_ = v___x_8_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Fin_hIterateFrom___redArg___boxed(lean_object* v_n_10_, lean_object* v_f_11_, lean_object* v_i_12_, lean_object* v_a_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Fin_hIterateFrom___redArg(v_n_10_, v_f_11_, v_i_12_, v_a_13_);
lean_dec(v_n_10_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Fin_hIterateFrom(lean_object* v_P_15_, lean_object* v_n_16_, lean_object* v_f_17_, lean_object* v_i_18_, lean_object* v_ubnd_19_, lean_object* v_a_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = l_Fin_hIterateFrom___redArg(v_n_16_, v_f_17_, v_i_18_, v_a_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_Fin_hIterateFrom___boxed(lean_object* v_P_22_, lean_object* v_n_23_, lean_object* v_f_24_, lean_object* v_i_25_, lean_object* v_ubnd_26_, lean_object* v_a_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Fin_hIterateFrom(v_P_22_, v_n_23_, v_f_24_, v_i_25_, v_ubnd_26_, v_a_27_);
lean_dec(v_n_23_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Fin_hIterate___redArg(lean_object* v_n_29_, lean_object* v_init_30_, lean_object* v_f_31_){
_start:
{
lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_32_ = lean_unsigned_to_nat(0u);
v___x_33_ = l_Fin_hIterateFrom___redArg(v_n_29_, v_f_31_, v___x_32_, v_init_30_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Fin_hIterate___redArg___boxed(lean_object* v_n_34_, lean_object* v_init_35_, lean_object* v_f_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Fin_hIterate___redArg(v_n_34_, v_init_35_, v_f_36_);
lean_dec(v_n_34_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Fin_hIterate(lean_object* v_P_38_, lean_object* v_n_39_, lean_object* v_init_40_, lean_object* v_f_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Fin_hIterate___redArg(v_n_39_, v_init_40_, v_f_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Fin_hIterate___boxed(lean_object* v_P_43_, lean_object* v_n_44_, lean_object* v_init_45_, lean_object* v_f_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_Fin_hIterate(v_P_43_, v_n_44_, v_init_45_, v_f_46_);
lean_dec(v_n_44_);
return v_res_47_;
}
}
lean_object* runtime_initialize_Init_Data_Fin_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_PropLemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_WFTactics(uint8_t builtin);
lean_object* runtime_initialize_Init_Hints(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Fin_Iterate(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Fin_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_PropLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Hints(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Fin_Iterate(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Fin_Basic(uint8_t builtin);
lean_object* initialize_Init_PropLemmas(uint8_t builtin);
lean_object* initialize_Init_WFTactics(uint8_t builtin);
lean_object* initialize_Init_Hints(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Fin_Iterate(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Fin_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_PropLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Hints(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Fin_Iterate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Fin_Iterate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Fin_Iterate(builtin);
}
#ifdef __cplusplus
}
#endif

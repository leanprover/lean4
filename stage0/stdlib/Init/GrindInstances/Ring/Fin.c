// Lean compiler output
// Module: Init.GrindInstances.Ring.Fin
// Imports: import all Init.Data.Zero public import Init.Data.Fin.Lemmas public import Init.Grind.Ring.Basic import Init.Omega import Init.Data.Nat.Div.Lemmas import Init.Data.Int.Order import Init.Data.Nat.Lemmas import Init.Data.Nat.MinMax
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
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Fin_NatCast_instNatCast___redArg___lam__0(lean_object*, lean_object*);
lean_object* l_Fin_mul(lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_intCast___redArg(lean_object*, lean_object*);
lean_object* l_Fin_add___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_mul___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_NatCast_instNatCast___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Fin_npow___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instPowNat___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_instHAdd___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_neg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Fin_sub___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_intCast___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg___lam__0(lean_object* v_n_1_, lean_object* v_n_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_nat_mod(v_n_2_, v_n_1_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg___lam__0___boxed(lean_object* v_n_4_, lean_object* v_n_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg___lam__0(v_n_4_, v_n_5_);
lean_dec(v_n_5_);
lean_dec(v_n_4_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg___lam__1(lean_object* v_n_7_, lean_object* v_k_8_, lean_object* v_i_9_){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_10_ = l_Fin_NatCast_instNatCast___redArg___lam__0(v_n_7_, v_k_8_);
v___x_11_ = l_Fin_mul(v_n_7_, v___x_10_, v_i_9_);
lean_dec(v___x_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg___lam__1___boxed(lean_object* v_n_12_, lean_object* v_k_13_, lean_object* v_i_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg___lam__1(v_n_12_, v_k_13_, v_i_14_);
lean_dec(v_i_14_);
lean_dec(v_k_13_);
lean_dec(v_n_12_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg___lam__2(lean_object* v_n_16_, lean_object* v_k_17_, lean_object* v_i_18_){
_start:
{
lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_19_ = l_Fin_intCast___redArg(v_n_16_, v_k_17_);
v___x_20_ = l_Fin_mul(v_n_16_, v___x_19_, v_i_18_);
lean_dec(v___x_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg___lam__2___boxed(lean_object* v_n_21_, lean_object* v_k_22_, lean_object* v_i_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg___lam__2(v_n_21_, v_k_22_, v_i_23_);
lean_dec(v_i_23_);
lean_dec(v_k_22_);
lean_dec(v_n_21_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg(lean_object* v_n_25_){
_start:
{
lean_object* v___f_26_; lean_object* v___f_27_; lean_object* v___f_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___f_31_; lean_object* v___x_32_; lean_object* v___f_33_; lean_object* v___f_34_; lean_object* v___f_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
lean_inc_n(v_n_25_, 9);
v___f_26_ = lean_alloc_closure((void*)(l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_26_, 0, v_n_25_);
v___f_27_ = lean_alloc_closure((void*)(l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_27_, 0, v_n_25_);
v___f_28_ = lean_alloc_closure((void*)(l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_28_, 0, v_n_25_);
v___x_29_ = lean_alloc_closure((void*)(l_Fin_add___boxed), 3, 1);
lean_closure_set(v___x_29_, 0, v_n_25_);
v___x_30_ = lean_alloc_closure((void*)(l_Fin_mul___boxed), 3, 1);
lean_closure_set(v___x_30_, 0, v_n_25_);
v___f_31_ = lean_alloc_closure((void*)(l_Fin_NatCast_instNatCast___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_31_, 0, v_n_25_);
v___x_32_ = lean_alloc_closure((void*)(l_Fin_npow___boxed), 3, 1);
lean_closure_set(v___x_32_, 0, v_n_25_);
v___f_33_ = lean_alloc_closure((void*)(l_instPowNat___redArg___lam__0), 3, 1);
lean_closure_set(v___f_33_, 0, v___x_32_);
v___f_34_ = lean_alloc_closure((void*)(l_instHAdd___redArg___lam__0), 3, 1);
lean_closure_set(v___f_34_, 0, v___f_33_);
v___f_35_ = lean_alloc_closure((void*)(l_Fin_neg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_35_, 0, v_n_25_);
v___x_36_ = lean_alloc_closure((void*)(l_Fin_sub___boxed), 3, 1);
lean_closure_set(v___x_36_, 0, v_n_25_);
v___x_37_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_37_, 0, v___x_29_);
lean_ctor_set(v___x_37_, 1, v___x_30_);
lean_ctor_set(v___x_37_, 2, v___f_31_);
lean_ctor_set(v___x_37_, 3, v___f_26_);
lean_ctor_set(v___x_37_, 4, v___f_27_);
lean_ctor_set(v___x_37_, 5, v___f_34_);
v___x_38_ = lean_alloc_closure((void*)(l_Fin_intCast___boxed), 3, 2);
lean_closure_set(v___x_38_, 0, v_n_25_);
lean_closure_set(v___x_38_, 1, lean_box(0));
v___x_39_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_39_, 0, v___x_37_);
lean_ctor_set(v___x_39_, 1, v___f_35_);
lean_ctor_set(v___x_39_, 2, v___x_36_);
lean_ctor_set(v___x_39_, 3, v___x_38_);
lean_ctor_set(v___x_39_, 4, v___f_28_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat(lean_object* v_n_40_, lean_object* v_inst_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg(v_n_40_);
return v___x_42_;
}
}
lean_object* runtime_initialize_Init_Data_Zero(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Fin_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Ring_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Div_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Order(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_MinMax(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_GrindInstances_Ring_Fin(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Zero(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Fin_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Ring_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Div_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_GrindInstances_Ring_Fin(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Zero(uint8_t builtin);
lean_object* initialize_Init_Data_Fin_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Grind_Ring_Basic(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Div_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Order(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_MinMax(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_GrindInstances_Ring_Fin(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Zero(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Fin_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Ring_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Div_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_GrindInstances_Ring_Fin(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_GrindInstances_Ring_Fin(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_GrindInstances_Ring_Fin(builtin);
}
#ifdef __cplusplus
}
#endif

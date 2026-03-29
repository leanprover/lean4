// Lean compiler output
// Module: Init.GrindInstances.Ring.Fin
// Imports: import all Init.Data.Zero public import Init.GrindInstances.ToInt import all Init.GrindInstances.ToInt public import Init.Data.Fin.Lemmas public import Init.Grind.Ring.Basic import Init.Data.Nat.Lemmas import Init.Data.Nat.MinMax
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
lean_object* l_Fin_neg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Fin_sub___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_npowRec___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_intCast___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_npow___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_npow___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_npow(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_npow___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_instHPowFinNatOfNeZero___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_instHPowFinNatOfNeZero(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_instPowFinNatOfNeZero___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_instPowFinNatOfNeZero(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_npow___redArg(lean_object* v_n_1_, lean_object* v_x_2_, lean_object* v_y_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_4_ = lean_unsigned_to_nat(1u);
v___x_5_ = lean_nat_mod(v___x_4_, v_n_1_);
v___x_6_ = lean_alloc_closure((void*)(l_Fin_mul___boxed), 3, 1);
lean_closure_set(v___x_6_, 0, v_n_1_);
v___x_7_ = l_npowRec___redArg(v___x_5_, v___x_6_, v_y_3_, v_x_2_);
lean_dec(v___x_5_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_npow___redArg___boxed(lean_object* v_n_8_, lean_object* v_x_9_, lean_object* v_y_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_Lean_Grind_Fin_npow___redArg(v_n_8_, v_x_9_, v_y_10_);
lean_dec(v_y_10_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_npow(lean_object* v_n_12_, lean_object* v_inst_13_, lean_object* v_x_14_, lean_object* v_y_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = l_Lean_Grind_Fin_npow___redArg(v_n_12_, v_x_14_, v_y_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_npow___boxed(lean_object* v_n_17_, lean_object* v_inst_18_, lean_object* v_x_19_, lean_object* v_y_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l_Lean_Grind_Fin_npow(v_n_17_, v_inst_18_, v_x_19_, v_y_20_);
lean_dec(v_y_20_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_instHPowFinNatOfNeZero___redArg(lean_object* v_n_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = lean_alloc_closure((void*)(l_Lean_Grind_Fin_npow___boxed), 4, 2);
lean_closure_set(v___x_23_, 0, v_n_22_);
lean_closure_set(v___x_23_, 1, lean_box(0));
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_instHPowFinNatOfNeZero(lean_object* v_n_24_, lean_object* v_inst_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = lean_alloc_closure((void*)(l_Lean_Grind_Fin_npow___boxed), 4, 2);
lean_closure_set(v___x_26_, 0, v_n_24_);
lean_closure_set(v___x_26_, 1, lean_box(0));
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_instPowFinNatOfNeZero___redArg(lean_object* v_n_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = lean_alloc_closure((void*)(l_Lean_Grind_Fin_npow___boxed), 4, 2);
lean_closure_set(v___x_28_, 0, v_n_27_);
lean_closure_set(v___x_28_, 1, lean_box(0));
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_instPowFinNatOfNeZero(lean_object* v_n_29_, lean_object* v_inst_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = lean_alloc_closure((void*)(l_Lean_Grind_Fin_npow___boxed), 4, 2);
lean_closure_set(v___x_31_, 0, v_n_29_);
lean_closure_set(v___x_31_, 1, lean_box(0));
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg___lam__0(lean_object* v_n_32_, lean_object* v_n_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = lean_nat_mod(v_n_33_, v_n_32_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg___lam__0___boxed(lean_object* v_n_35_, lean_object* v_n_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg___lam__0(v_n_35_, v_n_36_);
lean_dec(v_n_36_);
lean_dec(v_n_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg___lam__1(lean_object* v_n_38_, lean_object* v_k_39_, lean_object* v_i_40_){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_41_ = l_Fin_NatCast_instNatCast___redArg___lam__0(v_n_38_, v_k_39_);
v___x_42_ = l_Fin_mul(v_n_38_, v___x_41_, v_i_40_);
lean_dec(v___x_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg___lam__1___boxed(lean_object* v_n_43_, lean_object* v_k_44_, lean_object* v_i_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg___lam__1(v_n_43_, v_k_44_, v_i_45_);
lean_dec(v_i_45_);
lean_dec(v_k_44_);
lean_dec(v_n_43_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg___lam__2(lean_object* v_n_47_, lean_object* v_k_48_, lean_object* v_i_49_){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_50_ = l_Fin_intCast___redArg(v_n_47_, v_k_48_);
v___x_51_ = l_Fin_mul(v_n_47_, v___x_50_, v_i_49_);
lean_dec(v___x_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg___lam__2___boxed(lean_object* v_n_52_, lean_object* v_k_53_, lean_object* v_i_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg___lam__2(v_n_52_, v_k_53_, v_i_54_);
lean_dec(v_i_54_);
lean_dec(v_k_53_);
lean_dec(v_n_52_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg(lean_object* v_n_56_){
_start:
{
lean_object* v___f_57_; lean_object* v___f_58_; lean_object* v___f_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___f_62_; lean_object* v___f_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
lean_inc_n(v_n_56_, 9);
v___f_57_ = lean_alloc_closure((void*)(l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_57_, 0, v_n_56_);
v___f_58_ = lean_alloc_closure((void*)(l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_58_, 0, v_n_56_);
v___f_59_ = lean_alloc_closure((void*)(l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_59_, 0, v_n_56_);
v___x_60_ = lean_alloc_closure((void*)(l_Fin_add___boxed), 3, 1);
lean_closure_set(v___x_60_, 0, v_n_56_);
v___x_61_ = lean_alloc_closure((void*)(l_Fin_mul___boxed), 3, 1);
lean_closure_set(v___x_61_, 0, v_n_56_);
v___f_62_ = lean_alloc_closure((void*)(l_Fin_NatCast_instNatCast___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_62_, 0, v_n_56_);
v___f_63_ = lean_alloc_closure((void*)(l_Fin_neg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_63_, 0, v_n_56_);
v___x_64_ = lean_alloc_closure((void*)(l_Fin_sub___boxed), 3, 1);
lean_closure_set(v___x_64_, 0, v_n_56_);
v___x_65_ = lean_alloc_closure((void*)(l_Lean_Grind_Fin_npow___boxed), 4, 2);
lean_closure_set(v___x_65_, 0, v_n_56_);
lean_closure_set(v___x_65_, 1, lean_box(0));
v___x_66_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_66_, 0, v___x_60_);
lean_ctor_set(v___x_66_, 1, v___x_61_);
lean_ctor_set(v___x_66_, 2, v___f_62_);
lean_ctor_set(v___x_66_, 3, v___f_57_);
lean_ctor_set(v___x_66_, 4, v___f_58_);
lean_ctor_set(v___x_66_, 5, v___x_65_);
v___x_67_ = lean_alloc_closure((void*)(l_Fin_intCast___boxed), 3, 2);
lean_closure_set(v___x_67_, 0, v_n_56_);
lean_closure_set(v___x_67_, 1, lean_box(0));
v___x_68_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_68_, 0, v___x_66_);
lean_ctor_set(v___x_68_, 1, v___f_63_);
lean_ctor_set(v___x_68_, 2, v___x_64_);
lean_ctor_set(v___x_68_, 3, v___x_67_);
lean_ctor_set(v___x_68_, 4, v___f_59_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat(lean_object* v_n_69_, lean_object* v_inst_70_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg(v_n_69_);
return v___x_71_;
}
}
lean_object* runtime_initialize_Init_Data_Zero(uint8_t builtin);
lean_object* runtime_initialize_Init_GrindInstances_ToInt(uint8_t builtin);
lean_object* runtime_initialize_Init_GrindInstances_ToInt(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Fin_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Ring_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_MinMax(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_GrindInstances_Ring_Fin(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Zero(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_GrindInstances_ToInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_GrindInstances_ToInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Fin_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Ring_Basic(builtin);
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
lean_object* initialize_Init_GrindInstances_ToInt(uint8_t builtin);
lean_object* initialize_Init_GrindInstances_ToInt(uint8_t builtin);
lean_object* initialize_Init_Data_Fin_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Grind_Ring_Basic(uint8_t builtin);
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
res = initialize_Init_GrindInstances_ToInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_GrindInstances_ToInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Fin_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Ring_Basic(builtin);
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

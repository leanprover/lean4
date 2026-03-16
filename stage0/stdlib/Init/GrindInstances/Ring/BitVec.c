// Lean compiler output
// Module: Init.GrindInstances.Ring.BitVec
// Imports: public import Init.GrindInstances.ToInt import all Init.Data.BitVec.Basic import all Init.Grind.ToInt public import Init.Data.BitVec.Lemmas public import Init.Grind.Ring.Basic import Init.Data.BitVec.Bootstrap import Init.Grind.Ring.ToInt
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
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
lean_object* l_BitVec_mul(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_ofInt(lean_object*, lean_object*);
lean_object* l_BitVec_add___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_mul___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_instNatCast___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_BitVec_instOfNat___boxed(lean_object*, lean_object*);
lean_object* l_BitVec_instPowNat___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instHAdd___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_neg___boxed(lean_object*, lean_object*);
lean_object* l_BitVec_sub___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_ofInt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingBitVec___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingBitVec___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingBitVec___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingBitVec___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingBitVec(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingBitVec___lam__0(lean_object* v_w_1_, lean_object* v_x1_2_, lean_object* v_x2_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = l_BitVec_ofNat(v_w_1_, v_x1_2_);
v___x_5_ = l_BitVec_mul(v_w_1_, v___x_4_, v_x2_3_);
lean_dec(v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingBitVec___lam__0___boxed(lean_object* v_w_6_, lean_object* v_x1_7_, lean_object* v_x2_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_Grind_instCommRingBitVec___lam__0(v_w_6_, v_x1_7_, v_x2_8_);
lean_dec(v_x2_8_);
lean_dec(v_x1_7_);
lean_dec(v_w_6_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingBitVec___lam__1(lean_object* v_w_10_, lean_object* v_x1_11_, lean_object* v_x2_12_){
_start:
{
lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_13_ = l_BitVec_ofInt(v_w_10_, v_x1_11_);
v___x_14_ = l_BitVec_mul(v_w_10_, v___x_13_, v_x2_12_);
lean_dec(v___x_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingBitVec___lam__1___boxed(lean_object* v_w_15_, lean_object* v_x1_16_, lean_object* v_x2_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Lean_Grind_instCommRingBitVec___lam__1(v_w_15_, v_x1_16_, v_x2_17_);
lean_dec(v_x2_17_);
lean_dec(v_x1_16_);
lean_dec(v_w_15_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingBitVec(lean_object* v_w_19_){
_start:
{
lean_object* v___f_20_; lean_object* v___f_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___f_24_; lean_object* v___x_25_; lean_object* v___f_26_; lean_object* v___f_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
lean_inc(v_w_19_);
v___f_20_ = lean_alloc_closure((void*)(l_Lean_Grind_instCommRingBitVec___lam__0___boxed), 3, 1);
lean_closure_set(v___f_20_, 0, v_w_19_);
lean_inc(v_w_19_);
v___f_21_ = lean_alloc_closure((void*)(l_Lean_Grind_instCommRingBitVec___lam__1___boxed), 3, 1);
lean_closure_set(v___f_21_, 0, v_w_19_);
lean_inc(v_w_19_);
v___x_22_ = lean_alloc_closure((void*)(l_BitVec_add___boxed), 3, 1);
lean_closure_set(v___x_22_, 0, v_w_19_);
lean_inc(v_w_19_);
v___x_23_ = lean_alloc_closure((void*)(l_BitVec_mul___boxed), 3, 1);
lean_closure_set(v___x_23_, 0, v_w_19_);
lean_inc(v_w_19_);
v___f_24_ = lean_alloc_closure((void*)(l_BitVec_instNatCast___lam__0___boxed), 2, 1);
lean_closure_set(v___f_24_, 0, v_w_19_);
lean_inc(v_w_19_);
v___x_25_ = lean_alloc_closure((void*)(l_BitVec_instOfNat___boxed), 2, 1);
lean_closure_set(v___x_25_, 0, v_w_19_);
lean_inc(v_w_19_);
v___f_26_ = lean_alloc_closure((void*)(l_BitVec_instPowNat___lam__0___boxed), 3, 1);
lean_closure_set(v___f_26_, 0, v_w_19_);
v___f_27_ = lean_alloc_closure((void*)(l_instHAdd___redArg___lam__0), 3, 1);
lean_closure_set(v___f_27_, 0, v___f_26_);
lean_inc(v_w_19_);
v___x_28_ = lean_alloc_closure((void*)(l_BitVec_neg___boxed), 2, 1);
lean_closure_set(v___x_28_, 0, v_w_19_);
lean_inc(v_w_19_);
v___x_29_ = lean_alloc_closure((void*)(l_BitVec_sub___boxed), 3, 1);
lean_closure_set(v___x_29_, 0, v_w_19_);
v___x_30_ = lean_alloc_closure((void*)(l_BitVec_ofInt___boxed), 2, 1);
lean_closure_set(v___x_30_, 0, v_w_19_);
v___x_31_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_31_, 0, v___x_22_);
lean_ctor_set(v___x_31_, 1, v___x_23_);
lean_ctor_set(v___x_31_, 2, v___f_24_);
lean_ctor_set(v___x_31_, 3, v___x_25_);
lean_ctor_set(v___x_31_, 4, v___f_20_);
lean_ctor_set(v___x_31_, 5, v___f_27_);
v___x_32_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_32_, 0, v___x_31_);
lean_ctor_set(v___x_32_, 1, v___x_28_);
lean_ctor_set(v___x_32_, 2, v___x_29_);
lean_ctor_set(v___x_32_, 3, v___x_30_);
lean_ctor_set(v___x_32_, 4, v___f_21_);
return v___x_32_;
}
}
lean_object* runtime_initialize_Init_GrindInstances_ToInt(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_ToInt(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Ring_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_Bootstrap(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Ring_ToInt(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_GrindInstances_Ring_BitVec(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_GrindInstances_ToInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_ToInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Ring_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Ring_ToInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_GrindInstances_Ring_BitVec(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_GrindInstances_ToInt(uint8_t builtin);
lean_object* initialize_Init_Data_BitVec_Basic(uint8_t builtin);
lean_object* initialize_Init_Grind_ToInt(uint8_t builtin);
lean_object* initialize_Init_Data_BitVec_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Grind_Ring_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_BitVec_Bootstrap(uint8_t builtin);
lean_object* initialize_Init_Grind_Ring_ToInt(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_GrindInstances_Ring_BitVec(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_GrindInstances_ToInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_ToInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Ring_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Ring_ToInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_GrindInstances_Ring_BitVec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_GrindInstances_Ring_BitVec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_GrindInstances_Ring_BitVec(builtin);
}
#ifdef __cplusplus
}
#endif

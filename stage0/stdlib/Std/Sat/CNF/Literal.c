// Lean compiler output
// Module: Std.Sat.CNF.Literal
// Imports: public import Init.Data.Hashable public import Init.Data.ToString
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
uint8_t lean_bool_not(uint8_t);
LEAN_EXPORT lean_object* l_Std_Sat_Literal_negate___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_Literal_negate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_Literal_negate___redArg(lean_object* v_l_1_){
_start:
{
lean_object* v_fst_2_; lean_object* v_snd_3_; lean_object* v___x_5_; uint8_t v_isShared_6_; uint8_t v_isSharedCheck_13_; 
v_fst_2_ = lean_ctor_get(v_l_1_, 0);
v_snd_3_ = lean_ctor_get(v_l_1_, 1);
v_isSharedCheck_13_ = !lean_is_exclusive(v_l_1_);
if (v_isSharedCheck_13_ == 0)
{
v___x_5_ = v_l_1_;
v_isShared_6_ = v_isSharedCheck_13_;
goto v_resetjp_4_;
}
else
{
lean_inc(v_snd_3_);
lean_inc(v_fst_2_);
lean_dec(v_l_1_);
v___x_5_ = lean_box(0);
v_isShared_6_ = v_isSharedCheck_13_;
goto v_resetjp_4_;
}
v_resetjp_4_:
{
uint8_t v___x_7_; uint8_t v___x_8_; lean_object* v___x_9_; lean_object* v___x_11_; 
v___x_7_ = lean_unbox(v_snd_3_);
lean_dec(v_snd_3_);
v___x_8_ = lean_bool_not(v___x_7_);
v___x_9_ = lean_box(v___x_8_);
if (v_isShared_6_ == 0)
{
lean_ctor_set(v___x_5_, 1, v___x_9_);
v___x_11_ = v___x_5_;
goto v_reusejp_10_;
}
else
{
lean_object* v_reuseFailAlloc_12_; 
v_reuseFailAlloc_12_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_12_, 0, v_fst_2_);
lean_ctor_set(v_reuseFailAlloc_12_, 1, v___x_9_);
v___x_11_ = v_reuseFailAlloc_12_;
goto v_reusejp_10_;
}
v_reusejp_10_:
{
return v___x_11_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_Literal_negate(lean_object* v_00_u03b1_14_, lean_object* v_l_15_){
_start:
{
lean_object* v_fst_16_; lean_object* v_snd_17_; lean_object* v___x_19_; uint8_t v_isShared_20_; uint8_t v_isSharedCheck_27_; 
v_fst_16_ = lean_ctor_get(v_l_15_, 0);
v_snd_17_ = lean_ctor_get(v_l_15_, 1);
v_isSharedCheck_27_ = !lean_is_exclusive(v_l_15_);
if (v_isSharedCheck_27_ == 0)
{
v___x_19_ = v_l_15_;
v_isShared_20_ = v_isSharedCheck_27_;
goto v_resetjp_18_;
}
else
{
lean_inc(v_snd_17_);
lean_inc(v_fst_16_);
lean_dec(v_l_15_);
v___x_19_ = lean_box(0);
v_isShared_20_ = v_isSharedCheck_27_;
goto v_resetjp_18_;
}
v_resetjp_18_:
{
uint8_t v___x_21_; uint8_t v___x_22_; lean_object* v___x_23_; lean_object* v___x_25_; 
v___x_21_ = lean_unbox(v_snd_17_);
lean_dec(v_snd_17_);
v___x_22_ = lean_bool_not(v___x_21_);
v___x_23_ = lean_box(v___x_22_);
if (v_isShared_20_ == 0)
{
lean_ctor_set(v___x_19_, 1, v___x_23_);
v___x_25_ = v___x_19_;
goto v_reusejp_24_;
}
else
{
lean_object* v_reuseFailAlloc_26_; 
v_reuseFailAlloc_26_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_26_, 0, v_fst_16_);
lean_ctor_set(v_reuseFailAlloc_26_, 1, v___x_23_);
v___x_25_ = v_reuseFailAlloc_26_;
goto v_reusejp_24_;
}
v_reusejp_24_:
{
return v___x_25_;
}
}
}
}
lean_object* runtime_initialize_Init_Data_Hashable(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Sat_CNF_Literal(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Hashable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Sat_CNF_Literal(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Hashable(uint8_t builtin);
lean_object* initialize_Init_Data_ToString(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sat_CNF_Literal(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Hashable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sat_CNF_Literal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Sat_CNF_Literal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Sat_CNF_Literal(builtin);
}
#ifdef __cplusplus
}
#endif

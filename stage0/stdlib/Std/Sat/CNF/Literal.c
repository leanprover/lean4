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
LEAN_EXPORT lean_object* l_Std_Sat_Literal_negate___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_Literal_negate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_Literal_negate___redArg(lean_object* v_l_1_){
_start:
{
lean_object* v_snd_2_; uint8_t v___x_3_; 
v_snd_2_ = lean_ctor_get(v_l_1_, 1);
v___x_3_ = lean_unbox(v_snd_2_);
if (v___x_3_ == 0)
{
lean_object* v_fst_4_; lean_object* v___x_6_; uint8_t v_isShared_7_; uint8_t v_isSharedCheck_13_; 
v_fst_4_ = lean_ctor_get(v_l_1_, 0);
v_isSharedCheck_13_ = !lean_is_exclusive(v_l_1_);
if (v_isSharedCheck_13_ == 0)
{
lean_object* v_unused_14_; 
v_unused_14_ = lean_ctor_get(v_l_1_, 1);
lean_dec(v_unused_14_);
v___x_6_ = v_l_1_;
v_isShared_7_ = v_isSharedCheck_13_;
goto v_resetjp_5_;
}
else
{
lean_inc(v_fst_4_);
lean_dec(v_l_1_);
v___x_6_ = lean_box(0);
v_isShared_7_ = v_isSharedCheck_13_;
goto v_resetjp_5_;
}
v_resetjp_5_:
{
uint8_t v___x_8_; lean_object* v___x_9_; lean_object* v___x_11_; 
v___x_8_ = 1;
v___x_9_ = lean_box(v___x_8_);
if (v_isShared_7_ == 0)
{
lean_ctor_set(v___x_6_, 1, v___x_9_);
v___x_11_ = v___x_6_;
goto v_reusejp_10_;
}
else
{
lean_object* v_reuseFailAlloc_12_; 
v_reuseFailAlloc_12_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_12_, 0, v_fst_4_);
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
else
{
lean_object* v_fst_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_24_; 
v_fst_15_ = lean_ctor_get(v_l_1_, 0);
v_isSharedCheck_24_ = !lean_is_exclusive(v_l_1_);
if (v_isSharedCheck_24_ == 0)
{
lean_object* v_unused_25_; 
v_unused_25_ = lean_ctor_get(v_l_1_, 1);
lean_dec(v_unused_25_);
v___x_17_ = v_l_1_;
v_isShared_18_ = v_isSharedCheck_24_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_fst_15_);
lean_dec(v_l_1_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_24_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
uint8_t v___x_19_; lean_object* v___x_20_; lean_object* v___x_22_; 
v___x_19_ = 0;
v___x_20_ = lean_box(v___x_19_);
if (v_isShared_18_ == 0)
{
lean_ctor_set(v___x_17_, 1, v___x_20_);
v___x_22_ = v___x_17_;
goto v_reusejp_21_;
}
else
{
lean_object* v_reuseFailAlloc_23_; 
v_reuseFailAlloc_23_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_23_, 0, v_fst_15_);
lean_ctor_set(v_reuseFailAlloc_23_, 1, v___x_20_);
v___x_22_ = v_reuseFailAlloc_23_;
goto v_reusejp_21_;
}
v_reusejp_21_:
{
return v___x_22_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_Literal_negate(lean_object* v_00_u03b1_26_, lean_object* v_l_27_){
_start:
{
lean_object* v_snd_28_; uint8_t v___x_29_; 
v_snd_28_ = lean_ctor_get(v_l_27_, 1);
v___x_29_ = lean_unbox(v_snd_28_);
if (v___x_29_ == 0)
{
lean_object* v_fst_30_; lean_object* v___x_32_; uint8_t v_isShared_33_; uint8_t v_isSharedCheck_39_; 
v_fst_30_ = lean_ctor_get(v_l_27_, 0);
v_isSharedCheck_39_ = !lean_is_exclusive(v_l_27_);
if (v_isSharedCheck_39_ == 0)
{
lean_object* v_unused_40_; 
v_unused_40_ = lean_ctor_get(v_l_27_, 1);
lean_dec(v_unused_40_);
v___x_32_ = v_l_27_;
v_isShared_33_ = v_isSharedCheck_39_;
goto v_resetjp_31_;
}
else
{
lean_inc(v_fst_30_);
lean_dec(v_l_27_);
v___x_32_ = lean_box(0);
v_isShared_33_ = v_isSharedCheck_39_;
goto v_resetjp_31_;
}
v_resetjp_31_:
{
uint8_t v___x_34_; lean_object* v___x_35_; lean_object* v___x_37_; 
v___x_34_ = 1;
v___x_35_ = lean_box(v___x_34_);
if (v_isShared_33_ == 0)
{
lean_ctor_set(v___x_32_, 1, v___x_35_);
v___x_37_ = v___x_32_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v_fst_30_);
lean_ctor_set(v_reuseFailAlloc_38_, 1, v___x_35_);
v___x_37_ = v_reuseFailAlloc_38_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
return v___x_37_;
}
}
}
else
{
lean_object* v_fst_41_; lean_object* v___x_43_; uint8_t v_isShared_44_; uint8_t v_isSharedCheck_50_; 
v_fst_41_ = lean_ctor_get(v_l_27_, 0);
v_isSharedCheck_50_ = !lean_is_exclusive(v_l_27_);
if (v_isSharedCheck_50_ == 0)
{
lean_object* v_unused_51_; 
v_unused_51_ = lean_ctor_get(v_l_27_, 1);
lean_dec(v_unused_51_);
v___x_43_ = v_l_27_;
v_isShared_44_ = v_isSharedCheck_50_;
goto v_resetjp_42_;
}
else
{
lean_inc(v_fst_41_);
lean_dec(v_l_27_);
v___x_43_ = lean_box(0);
v_isShared_44_ = v_isSharedCheck_50_;
goto v_resetjp_42_;
}
v_resetjp_42_:
{
uint8_t v___x_45_; lean_object* v___x_46_; lean_object* v___x_48_; 
v___x_45_ = 0;
v___x_46_ = lean_box(v___x_45_);
if (v_isShared_44_ == 0)
{
lean_ctor_set(v___x_43_, 1, v___x_46_);
v___x_48_ = v___x_43_;
goto v_reusejp_47_;
}
else
{
lean_object* v_reuseFailAlloc_49_; 
v_reuseFailAlloc_49_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_49_, 0, v_fst_41_);
lean_ctor_set(v_reuseFailAlloc_49_, 1, v___x_46_);
v___x_48_ = v_reuseFailAlloc_49_;
goto v_reusejp_47_;
}
v_reusejp_47_:
{
return v___x_48_;
}
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

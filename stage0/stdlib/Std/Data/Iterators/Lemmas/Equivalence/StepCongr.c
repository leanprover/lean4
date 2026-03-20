// Lean compiler output
// Module: Std.Data.Iterators.Lemmas.Equivalence.StepCongr
// Imports: public import Std.Data.Iterators.Lemmas.Equivalence.Basic
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
LEAN_EXPORT lean_object* l_Std_IterStep_bundledQuotient___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterStep_bundledQuotient(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterStep_bundledQuotient___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_QuotStep_bundledQuotient___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_QuotStep_bundledQuotient(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_QuotStep_bundledQuotient___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterStep_bundledQuotient___redArg(lean_object* v_inst_1_, lean_object* v_step_2_){
_start:
{
switch(lean_obj_tag(v_step_2_))
{
case 0:
{
lean_object* v_it_3_; lean_object* v_out_4_; lean_object* v___x_6_; uint8_t v_isShared_7_; uint8_t v_isSharedCheck_12_; 
v_it_3_ = lean_ctor_get(v_step_2_, 0);
v_out_4_ = lean_ctor_get(v_step_2_, 1);
v_isSharedCheck_12_ = !lean_is_exclusive(v_step_2_);
if (v_isSharedCheck_12_ == 0)
{
v___x_6_ = v_step_2_;
v_isShared_7_ = v_isSharedCheck_12_;
goto v_resetjp_5_;
}
else
{
lean_inc(v_out_4_);
lean_inc(v_it_3_);
lean_dec(v_step_2_);
v___x_6_ = lean_box(0);
v_isShared_7_ = v_isSharedCheck_12_;
goto v_resetjp_5_;
}
v_resetjp_5_:
{
lean_object* v___x_8_; lean_object* v___x_10_; 
v___x_8_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_8_, 0, v_inst_1_);
lean_ctor_set(v___x_8_, 1, v_it_3_);
if (v_isShared_7_ == 0)
{
lean_ctor_set(v___x_6_, 0, v___x_8_);
v___x_10_ = v___x_6_;
goto v_reusejp_9_;
}
else
{
lean_object* v_reuseFailAlloc_11_; 
v_reuseFailAlloc_11_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_11_, 0, v___x_8_);
lean_ctor_set(v_reuseFailAlloc_11_, 1, v_out_4_);
v___x_10_ = v_reuseFailAlloc_11_;
goto v_reusejp_9_;
}
v_reusejp_9_:
{
return v___x_10_;
}
}
}
case 1:
{
lean_object* v_it_13_; lean_object* v___x_15_; uint8_t v_isShared_16_; uint8_t v_isSharedCheck_21_; 
v_it_13_ = lean_ctor_get(v_step_2_, 0);
v_isSharedCheck_21_ = !lean_is_exclusive(v_step_2_);
if (v_isSharedCheck_21_ == 0)
{
v___x_15_ = v_step_2_;
v_isShared_16_ = v_isSharedCheck_21_;
goto v_resetjp_14_;
}
else
{
lean_inc(v_it_13_);
lean_dec(v_step_2_);
v___x_15_ = lean_box(0);
v_isShared_16_ = v_isSharedCheck_21_;
goto v_resetjp_14_;
}
v_resetjp_14_:
{
lean_object* v___x_17_; lean_object* v___x_19_; 
v___x_17_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_17_, 0, v_inst_1_);
lean_ctor_set(v___x_17_, 1, v_it_13_);
if (v_isShared_16_ == 0)
{
lean_ctor_set(v___x_15_, 0, v___x_17_);
v___x_19_ = v___x_15_;
goto v_reusejp_18_;
}
else
{
lean_object* v_reuseFailAlloc_20_; 
v_reuseFailAlloc_20_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_20_, 0, v___x_17_);
v___x_19_ = v_reuseFailAlloc_20_;
goto v_reusejp_18_;
}
v_reusejp_18_:
{
return v___x_19_;
}
}
}
default: 
{
lean_object* v___x_22_; 
lean_dec(v_inst_1_);
v___x_22_ = lean_box(2);
return v___x_22_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_bundledQuotient(lean_object* v_00_u03b1_23_, lean_object* v_m_24_, lean_object* v_00_u03b2_25_, lean_object* v_inst_26_, lean_object* v_inst_27_, lean_object* v_inst_28_, lean_object* v_step_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = l_Std_IterStep_bundledQuotient___redArg(v_inst_26_, v_step_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_bundledQuotient___boxed(lean_object* v_00_u03b1_31_, lean_object* v_m_32_, lean_object* v_00_u03b2_33_, lean_object* v_inst_34_, lean_object* v_inst_35_, lean_object* v_inst_36_, lean_object* v_step_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Std_IterStep_bundledQuotient(v_00_u03b1_31_, v_m_32_, v_00_u03b2_33_, v_inst_34_, v_inst_35_, v_inst_36_, v_step_37_);
lean_dec_ref(v_inst_35_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_QuotStep_bundledQuotient___redArg(lean_object* v_inst_39_, lean_object* v_a_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Std_IterStep_bundledQuotient___redArg(v_inst_39_, v_a_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_QuotStep_bundledQuotient(lean_object* v_00_u03b1_42_, lean_object* v_m_43_, lean_object* v_00_u03b2_44_, lean_object* v_inst_45_, lean_object* v_inst_46_, lean_object* v_inst_47_, lean_object* v_it_48_, lean_object* v_a_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Std_IterStep_bundledQuotient___redArg(v_inst_45_, v_a_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_QuotStep_bundledQuotient___boxed(lean_object* v_00_u03b1_51_, lean_object* v_m_52_, lean_object* v_00_u03b2_53_, lean_object* v_inst_54_, lean_object* v_inst_55_, lean_object* v_inst_56_, lean_object* v_it_57_, lean_object* v_a_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Std_IterM_QuotStep_bundledQuotient(v_00_u03b1_51_, v_m_52_, v_00_u03b2_53_, v_inst_54_, v_inst_55_, v_inst_56_, v_it_57_, v_a_58_);
lean_dec(v_it_57_);
lean_dec_ref(v_inst_55_);
return v_res_59_;
}
}
lean_object* runtime_initialize_Std_Data_Iterators_Lemmas_Equivalence_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_Iterators_Lemmas_Equivalence_StepCongr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Data_Iterators_Lemmas_Equivalence_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_Iterators_Lemmas_Equivalence_StepCongr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_Iterators_Lemmas_Equivalence_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_Iterators_Lemmas_Equivalence_StepCongr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_Iterators_Lemmas_Equivalence_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_Iterators_Lemmas_Equivalence_StepCongr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_Iterators_Lemmas_Equivalence_StepCongr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_Iterators_Lemmas_Equivalence_StepCongr(builtin);
}
#ifdef __cplusplus
}
#endif

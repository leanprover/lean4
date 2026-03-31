// Lean compiler output
// Module: Init.Data.String.Iter.Intercalate
// Imports: public import Init.Data.Iterators.Combinators.Monadic.FilterMap public import Init.Data.String.Basic import Init.Data.String.Slice
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
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_joinString___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Iter_joinString___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Std_Iter_joinString___redArg___closed__0 = (const lean_object*)&l_Std_Iter_joinString___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Iter_joinString___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_joinString(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_intercalateString___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_intercalateString___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_intercalateString___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_intercalateString(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_joinString___redArg___lam__0(lean_object* v_inst_1_, lean_object* v_inst_2_, lean_object* v_it_3_, lean_object* v_acc_4_, lean_object* v_hP_5_, lean_object* v_recur_6_){
_start:
{
lean_object* v_val_7_; 
v_val_7_ = lean_apply_1(v_inst_1_, v_it_3_);
switch(lean_obj_tag(v_val_7_))
{
case 0:
{
lean_object* v_it_8_; lean_object* v_out_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v_it_8_ = lean_ctor_get(v_val_7_, 0);
lean_inc(v_it_8_);
v_out_9_ = lean_ctor_get(v_val_7_, 1);
lean_inc(v_out_9_);
lean_dec_ref(v_val_7_);
v___x_10_ = lean_apply_1(v_inst_2_, v_out_9_);
v___x_11_ = lean_string_append(v_acc_4_, v___x_10_);
lean_dec_ref(v___x_10_);
v___x_12_ = lean_apply_4(v_recur_6_, v_it_8_, v___x_11_, lean_box(0), lean_box(0));
return v___x_12_;
}
case 1:
{
lean_object* v_it_13_; lean_object* v___x_14_; 
lean_dec_ref(v_inst_2_);
v_it_13_ = lean_ctor_get(v_val_7_, 0);
lean_inc(v_it_13_);
lean_dec_ref(v_val_7_);
v___x_14_ = lean_apply_4(v_recur_6_, v_it_13_, v_acc_4_, lean_box(0), lean_box(0));
return v___x_14_;
}
default: 
{
lean_dec_ref(v_recur_6_);
lean_dec_ref(v_inst_2_);
return v_acc_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iter_joinString___redArg(lean_object* v_inst_16_, lean_object* v_inst_17_, lean_object* v_it_18_){
_start:
{
lean_object* v___f_19_; lean_object* v___x_20_; lean_object* v___x_21_; 
v___f_19_ = lean_alloc_closure((void*)(l_Std_Iter_joinString___redArg___lam__0), 6, 2);
lean_closure_set(v___f_19_, 0, v_inst_16_);
lean_closure_set(v___f_19_, 1, v_inst_17_);
v___x_20_ = ((lean_object*)(l_Std_Iter_joinString___redArg___closed__0));
v___x_21_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_19_, v_it_18_, v___x_20_, lean_box(0));
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_joinString(lean_object* v_00_u03b1_22_, lean_object* v_00_u03b2_23_, lean_object* v_inst_24_, lean_object* v_inst_25_, lean_object* v_it_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = l_Std_Iter_joinString___redArg(v_inst_24_, v_inst_25_, v_it_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_intercalateString___redArg___lam__0(lean_object* v_inst_28_, lean_object* v_inst_29_, lean_object* v_s_30_, lean_object* v_it_31_, lean_object* v_acc_32_, lean_object* v_hP_33_, lean_object* v_recur_34_){
_start:
{
lean_object* v_val_35_; 
v_val_35_ = lean_apply_1(v_inst_28_, v_it_31_);
switch(lean_obj_tag(v_val_35_))
{
case 0:
{
lean_object* v_it_36_; lean_object* v_out_37_; lean_object* v___x_38_; 
v_it_36_ = lean_ctor_get(v_val_35_, 0);
lean_inc(v_it_36_);
v_out_37_ = lean_ctor_get(v_val_35_, 1);
lean_inc(v_out_37_);
lean_dec_ref(v_val_35_);
v___x_38_ = lean_apply_1(v_inst_29_, v_out_37_);
if (lean_obj_tag(v_acc_32_) == 0)
{
lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_39_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_39_, 0, v___x_38_);
v___x_40_ = lean_apply_4(v_recur_34_, v_it_36_, v___x_39_, lean_box(0), lean_box(0));
return v___x_40_;
}
else
{
lean_object* v_val_41_; lean_object* v___x_43_; uint8_t v_isShared_44_; uint8_t v_isSharedCheck_55_; 
v_val_41_ = lean_ctor_get(v_acc_32_, 0);
v_isSharedCheck_55_ = !lean_is_exclusive(v_acc_32_);
if (v_isSharedCheck_55_ == 0)
{
v___x_43_ = v_acc_32_;
v_isShared_44_ = v_isSharedCheck_55_;
goto v_resetjp_42_;
}
else
{
lean_inc(v_val_41_);
lean_dec(v_acc_32_);
v___x_43_ = lean_box(0);
v_isShared_44_ = v_isSharedCheck_55_;
goto v_resetjp_42_;
}
v_resetjp_42_:
{
lean_object* v_str_45_; lean_object* v_startInclusive_46_; lean_object* v_endExclusive_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_52_; 
v_str_45_ = lean_ctor_get(v_s_30_, 0);
v_startInclusive_46_ = lean_ctor_get(v_s_30_, 1);
v_endExclusive_47_ = lean_ctor_get(v_s_30_, 2);
v___x_48_ = lean_string_utf8_extract(v_str_45_, v_startInclusive_46_, v_endExclusive_47_);
v___x_49_ = lean_string_append(v_val_41_, v___x_48_);
lean_dec_ref(v___x_48_);
v___x_50_ = lean_string_append(v___x_49_, v___x_38_);
lean_dec_ref(v___x_38_);
if (v_isShared_44_ == 0)
{
lean_ctor_set(v___x_43_, 0, v___x_50_);
v___x_52_ = v___x_43_;
goto v_reusejp_51_;
}
else
{
lean_object* v_reuseFailAlloc_54_; 
v_reuseFailAlloc_54_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_54_, 0, v___x_50_);
v___x_52_ = v_reuseFailAlloc_54_;
goto v_reusejp_51_;
}
v_reusejp_51_:
{
lean_object* v___x_53_; 
v___x_53_ = lean_apply_4(v_recur_34_, v_it_36_, v___x_52_, lean_box(0), lean_box(0));
return v___x_53_;
}
}
}
}
case 1:
{
lean_object* v_it_56_; lean_object* v___x_57_; 
lean_dec_ref(v_inst_29_);
v_it_56_ = lean_ctor_get(v_val_35_, 0);
lean_inc(v_it_56_);
lean_dec_ref(v_val_35_);
v___x_57_ = lean_apply_4(v_recur_34_, v_it_56_, v_acc_32_, lean_box(0), lean_box(0));
return v___x_57_;
}
default: 
{
lean_dec_ref(v_recur_34_);
lean_dec_ref(v_inst_29_);
return v_acc_32_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iter_intercalateString___redArg___lam__0___boxed(lean_object* v_inst_58_, lean_object* v_inst_59_, lean_object* v_s_60_, lean_object* v_it_61_, lean_object* v_acc_62_, lean_object* v_hP_63_, lean_object* v_recur_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_Std_Iter_intercalateString___redArg___lam__0(v_inst_58_, v_inst_59_, v_s_60_, v_it_61_, v_acc_62_, v_hP_63_, v_recur_64_);
lean_dec_ref(v_s_60_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_intercalateString___redArg(lean_object* v_inst_66_, lean_object* v_inst_67_, lean_object* v_s_68_, lean_object* v_it_69_){
_start:
{
lean_object* v___f_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v___f_70_ = lean_alloc_closure((void*)(l_Std_Iter_intercalateString___redArg___lam__0___boxed), 7, 3);
lean_closure_set(v___f_70_, 0, v_inst_66_);
lean_closure_set(v___f_70_, 1, v_inst_67_);
lean_closure_set(v___f_70_, 2, v_s_68_);
v___x_71_ = lean_box(0);
v___x_72_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_70_, v_it_69_, v___x_71_, lean_box(0));
if (lean_obj_tag(v___x_72_) == 0)
{
lean_object* v___x_73_; 
v___x_73_ = ((lean_object*)(l_Std_Iter_joinString___redArg___closed__0));
return v___x_73_;
}
else
{
lean_object* v_val_74_; 
v_val_74_ = lean_ctor_get(v___x_72_, 0);
lean_inc(v_val_74_);
lean_dec_ref(v___x_72_);
return v_val_74_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iter_intercalateString(lean_object* v_00_u03b1_75_, lean_object* v_00_u03b2_76_, lean_object* v_inst_77_, lean_object* v_inst_78_, lean_object* v_s_79_, lean_object* v_it_80_){
_start:
{
lean_object* v___f_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v___f_81_ = lean_alloc_closure((void*)(l_Std_Iter_intercalateString___redArg___lam__0___boxed), 7, 3);
lean_closure_set(v___f_81_, 0, v_inst_77_);
lean_closure_set(v___f_81_, 1, v_inst_78_);
lean_closure_set(v___f_81_, 2, v_s_79_);
v___x_82_ = lean_box(0);
v___x_83_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_81_, v_it_80_, v___x_82_, lean_box(0));
if (lean_obj_tag(v___x_83_) == 0)
{
lean_object* v___x_84_; 
v___x_84_ = ((lean_object*)(l_Std_Iter_joinString___redArg___closed__0));
return v___x_84_;
}
else
{
lean_object* v_val_85_; 
v_val_85_ = lean_ctor_get(v___x_83_, 0);
lean_inc(v_val_85_);
lean_dec_ref(v___x_83_);
return v_val_85_;
}
}
}
lean_object* runtime_initialize_Init_Data_Iterators_Combinators_Monadic_FilterMap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Slice(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Iter_Intercalate(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Iterators_Combinators_Monadic_FilterMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_String_Iter_Intercalate(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Iterators_Combinators_Monadic_FilterMap(uint8_t builtin);
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Slice(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Iter_Intercalate(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Iterators_Combinators_Monadic_FilterMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Iter_Intercalate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_String_Iter_Intercalate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_String_Iter_Intercalate(builtin);
}
#ifdef __cplusplus
}
#endif

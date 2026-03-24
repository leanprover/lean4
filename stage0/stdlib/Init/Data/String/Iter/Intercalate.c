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
LEAN_EXPORT lean_object* l_Std_Iter_joinString(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_joinString___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_intercalateString___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_intercalateString___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_intercalateString___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_intercalateString(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_intercalateString___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Iter_joinString(lean_object* v_00_u03b1_22_, lean_object* v_00_u03b2_23_, lean_object* v_inst_24_, lean_object* v_inst_25_, lean_object* v_inst_26_, lean_object* v_it_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = l_Std_Iter_joinString___redArg(v_inst_24_, v_inst_26_, v_it_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_joinString___boxed(lean_object* v_00_u03b1_29_, lean_object* v_00_u03b2_30_, lean_object* v_inst_31_, lean_object* v_inst_32_, lean_object* v_inst_33_, lean_object* v_it_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_Std_Iter_joinString(v_00_u03b1_29_, v_00_u03b2_30_, v_inst_31_, v_inst_32_, v_inst_33_, v_it_34_);
lean_dec(v_inst_32_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_intercalateString___redArg___lam__0(lean_object* v_inst_36_, lean_object* v_inst_37_, lean_object* v_s_38_, lean_object* v_it_39_, lean_object* v_acc_40_, lean_object* v_hP_41_, lean_object* v_recur_42_){
_start:
{
lean_object* v_val_43_; 
v_val_43_ = lean_apply_1(v_inst_36_, v_it_39_);
switch(lean_obj_tag(v_val_43_))
{
case 0:
{
lean_object* v_it_44_; lean_object* v_out_45_; lean_object* v___x_46_; 
v_it_44_ = lean_ctor_get(v_val_43_, 0);
lean_inc(v_it_44_);
v_out_45_ = lean_ctor_get(v_val_43_, 1);
lean_inc(v_out_45_);
lean_dec_ref(v_val_43_);
v___x_46_ = lean_apply_1(v_inst_37_, v_out_45_);
if (lean_obj_tag(v_acc_40_) == 0)
{
lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_47_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_47_, 0, v___x_46_);
v___x_48_ = lean_apply_4(v_recur_42_, v_it_44_, v___x_47_, lean_box(0), lean_box(0));
return v___x_48_;
}
else
{
lean_object* v_val_49_; lean_object* v___x_51_; uint8_t v_isShared_52_; uint8_t v_isSharedCheck_63_; 
v_val_49_ = lean_ctor_get(v_acc_40_, 0);
v_isSharedCheck_63_ = !lean_is_exclusive(v_acc_40_);
if (v_isSharedCheck_63_ == 0)
{
v___x_51_ = v_acc_40_;
v_isShared_52_ = v_isSharedCheck_63_;
goto v_resetjp_50_;
}
else
{
lean_inc(v_val_49_);
lean_dec(v_acc_40_);
v___x_51_ = lean_box(0);
v_isShared_52_ = v_isSharedCheck_63_;
goto v_resetjp_50_;
}
v_resetjp_50_:
{
lean_object* v_str_53_; lean_object* v_startInclusive_54_; lean_object* v_endExclusive_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_60_; 
v_str_53_ = lean_ctor_get(v_s_38_, 0);
v_startInclusive_54_ = lean_ctor_get(v_s_38_, 1);
v_endExclusive_55_ = lean_ctor_get(v_s_38_, 2);
v___x_56_ = lean_string_utf8_extract(v_str_53_, v_startInclusive_54_, v_endExclusive_55_);
v___x_57_ = lean_string_append(v_val_49_, v___x_56_);
lean_dec_ref(v___x_56_);
v___x_58_ = lean_string_append(v___x_57_, v___x_46_);
lean_dec_ref(v___x_46_);
if (v_isShared_52_ == 0)
{
lean_ctor_set(v___x_51_, 0, v___x_58_);
v___x_60_ = v___x_51_;
goto v_reusejp_59_;
}
else
{
lean_object* v_reuseFailAlloc_62_; 
v_reuseFailAlloc_62_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_62_, 0, v___x_58_);
v___x_60_ = v_reuseFailAlloc_62_;
goto v_reusejp_59_;
}
v_reusejp_59_:
{
lean_object* v___x_61_; 
v___x_61_ = lean_apply_4(v_recur_42_, v_it_44_, v___x_60_, lean_box(0), lean_box(0));
return v___x_61_;
}
}
}
}
case 1:
{
lean_object* v_it_64_; lean_object* v___x_65_; 
lean_dec_ref(v_inst_37_);
v_it_64_ = lean_ctor_get(v_val_43_, 0);
lean_inc(v_it_64_);
lean_dec_ref(v_val_43_);
v___x_65_ = lean_apply_4(v_recur_42_, v_it_64_, v_acc_40_, lean_box(0), lean_box(0));
return v___x_65_;
}
default: 
{
lean_dec_ref(v_recur_42_);
lean_dec_ref(v_inst_37_);
return v_acc_40_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iter_intercalateString___redArg___lam__0___boxed(lean_object* v_inst_66_, lean_object* v_inst_67_, lean_object* v_s_68_, lean_object* v_it_69_, lean_object* v_acc_70_, lean_object* v_hP_71_, lean_object* v_recur_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l_Std_Iter_intercalateString___redArg___lam__0(v_inst_66_, v_inst_67_, v_s_68_, v_it_69_, v_acc_70_, v_hP_71_, v_recur_72_);
lean_dec_ref(v_s_68_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_intercalateString___redArg(lean_object* v_inst_74_, lean_object* v_inst_75_, lean_object* v_s_76_, lean_object* v_it_77_){
_start:
{
lean_object* v___f_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v___f_78_ = lean_alloc_closure((void*)(l_Std_Iter_intercalateString___redArg___lam__0___boxed), 7, 3);
lean_closure_set(v___f_78_, 0, v_inst_74_);
lean_closure_set(v___f_78_, 1, v_inst_75_);
lean_closure_set(v___f_78_, 2, v_s_76_);
v___x_79_ = lean_box(0);
v___x_80_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_78_, v_it_77_, v___x_79_, lean_box(0));
if (lean_obj_tag(v___x_80_) == 0)
{
lean_object* v___x_81_; 
v___x_81_ = ((lean_object*)(l_Std_Iter_joinString___redArg___closed__0));
return v___x_81_;
}
else
{
lean_object* v_val_82_; 
v_val_82_ = lean_ctor_get(v___x_80_, 0);
lean_inc(v_val_82_);
lean_dec_ref(v___x_80_);
return v_val_82_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iter_intercalateString(lean_object* v_00_u03b1_83_, lean_object* v_00_u03b2_84_, lean_object* v_inst_85_, lean_object* v_inst_86_, lean_object* v_inst_87_, lean_object* v_s_88_, lean_object* v_it_89_){
_start:
{
lean_object* v___f_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___f_90_ = lean_alloc_closure((void*)(l_Std_Iter_intercalateString___redArg___lam__0___boxed), 7, 3);
lean_closure_set(v___f_90_, 0, v_inst_85_);
lean_closure_set(v___f_90_, 1, v_inst_87_);
lean_closure_set(v___f_90_, 2, v_s_88_);
v___x_91_ = lean_box(0);
v___x_92_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_90_, v_it_89_, v___x_91_, lean_box(0));
if (lean_obj_tag(v___x_92_) == 0)
{
lean_object* v___x_93_; 
v___x_93_ = ((lean_object*)(l_Std_Iter_joinString___redArg___closed__0));
return v___x_93_;
}
else
{
lean_object* v_val_94_; 
v_val_94_ = lean_ctor_get(v___x_92_, 0);
lean_inc(v_val_94_);
lean_dec_ref(v___x_92_);
return v_val_94_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iter_intercalateString___boxed(lean_object* v_00_u03b1_95_, lean_object* v_00_u03b2_96_, lean_object* v_inst_97_, lean_object* v_inst_98_, lean_object* v_inst_99_, lean_object* v_s_100_, lean_object* v_it_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_Std_Iter_intercalateString(v_00_u03b1_95_, v_00_u03b2_96_, v_inst_97_, v_inst_98_, v_inst_99_, v_s_100_, v_it_101_);
lean_dec(v_inst_98_);
return v_res_102_;
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

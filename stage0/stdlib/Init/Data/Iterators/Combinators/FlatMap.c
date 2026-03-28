// Lean compiler output
// Module: Init.Data.Iterators.Combinators.FlatMap
// Imports: public import Init.Data.Iterators.Combinators.Monadic.FlatMap import Init.Data.Iterators.Combinators.FilterMap
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
LEAN_EXPORT lean_object* l_Std_Iter_flatMapAfterM___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_flatMapAfterM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_flatMapAfterM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_flatMapM___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_flatMapM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_flatMapM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_flatMapAfter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_flatMapAfter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_flatMapAfter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_flatMap___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_flatMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_flatMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_flatMapAfterM___redArg(lean_object* v_it_u2081_1_, lean_object* v_it_u2082_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3_, 0, v_it_u2081_1_);
lean_ctor_set(v___x_3_, 1, v_it_u2082_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_flatMapAfterM(lean_object* v_00_u03b1_4_, lean_object* v_00_u03b2_5_, lean_object* v_00_u03b1_u2082_6_, lean_object* v_00_u03b3_7_, lean_object* v_m_8_, lean_object* v_inst_9_, lean_object* v_inst_10_, lean_object* v_inst_11_, lean_object* v_inst_12_, lean_object* v_f_13_, lean_object* v_it_u2081_14_, lean_object* v_it_u2082_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_16_, 0, v_it_u2081_14_);
lean_ctor_set(v___x_16_, 1, v_it_u2082_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_flatMapAfterM___boxed(lean_object* v_00_u03b1_17_, lean_object* v_00_u03b2_18_, lean_object* v_00_u03b1_u2082_19_, lean_object* v_00_u03b3_20_, lean_object* v_m_21_, lean_object* v_inst_22_, lean_object* v_inst_23_, lean_object* v_inst_24_, lean_object* v_inst_25_, lean_object* v_f_26_, lean_object* v_it_u2081_27_, lean_object* v_it_u2082_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Std_Iter_flatMapAfterM(v_00_u03b1_17_, v_00_u03b2_18_, v_00_u03b1_u2082_19_, v_00_u03b3_20_, v_m_21_, v_inst_22_, v_inst_23_, v_inst_24_, v_inst_25_, v_f_26_, v_it_u2081_27_, v_it_u2082_28_);
lean_dec(v_f_26_);
lean_dec(v_inst_25_);
lean_dec(v_inst_24_);
lean_dec(v_inst_23_);
lean_dec_ref(v_inst_22_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_flatMapM___redArg(lean_object* v_it_30_){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_31_ = lean_box(0);
v___x_32_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_32_, 0, v_it_30_);
lean_ctor_set(v___x_32_, 1, v___x_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_flatMapM(lean_object* v_00_u03b1_33_, lean_object* v_00_u03b2_34_, lean_object* v_00_u03b1_u2082_35_, lean_object* v_00_u03b3_36_, lean_object* v_m_37_, lean_object* v_inst_38_, lean_object* v_inst_39_, lean_object* v_inst_40_, lean_object* v_inst_41_, lean_object* v_f_42_, lean_object* v_it_43_){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_44_ = lean_box(0);
v___x_45_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_45_, 0, v_it_43_);
lean_ctor_set(v___x_45_, 1, v___x_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_flatMapM___boxed(lean_object* v_00_u03b1_46_, lean_object* v_00_u03b2_47_, lean_object* v_00_u03b1_u2082_48_, lean_object* v_00_u03b3_49_, lean_object* v_m_50_, lean_object* v_inst_51_, lean_object* v_inst_52_, lean_object* v_inst_53_, lean_object* v_inst_54_, lean_object* v_f_55_, lean_object* v_it_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Std_Iter_flatMapM(v_00_u03b1_46_, v_00_u03b2_47_, v_00_u03b1_u2082_48_, v_00_u03b3_49_, v_m_50_, v_inst_51_, v_inst_52_, v_inst_53_, v_inst_54_, v_f_55_, v_it_56_);
lean_dec(v_f_55_);
lean_dec(v_inst_54_);
lean_dec(v_inst_53_);
lean_dec(v_inst_52_);
lean_dec_ref(v_inst_51_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_flatMapAfter___redArg(lean_object* v_it_u2081_58_, lean_object* v_it_u2082_59_){
_start:
{
if (lean_obj_tag(v_it_u2082_59_) == 0)
{
lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_60_ = lean_box(0);
v___x_61_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_61_, 0, v_it_u2081_58_);
lean_ctor_set(v___x_61_, 1, v___x_60_);
return v___x_61_;
}
else
{
lean_object* v_val_62_; lean_object* v___x_64_; uint8_t v_isShared_65_; uint8_t v_isSharedCheck_70_; 
v_val_62_ = lean_ctor_get(v_it_u2082_59_, 0);
v_isSharedCheck_70_ = !lean_is_exclusive(v_it_u2082_59_);
if (v_isSharedCheck_70_ == 0)
{
v___x_64_ = v_it_u2082_59_;
v_isShared_65_ = v_isSharedCheck_70_;
goto v_resetjp_63_;
}
else
{
lean_inc(v_val_62_);
lean_dec(v_it_u2082_59_);
v___x_64_ = lean_box(0);
v_isShared_65_ = v_isSharedCheck_70_;
goto v_resetjp_63_;
}
v_resetjp_63_:
{
lean_object* v___x_67_; 
if (v_isShared_65_ == 0)
{
v___x_67_ = v___x_64_;
goto v_reusejp_66_;
}
else
{
lean_object* v_reuseFailAlloc_69_; 
v_reuseFailAlloc_69_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_69_, 0, v_val_62_);
v___x_67_ = v_reuseFailAlloc_69_;
goto v_reusejp_66_;
}
v_reusejp_66_:
{
lean_object* v___x_68_; 
v___x_68_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_68_, 0, v_it_u2081_58_);
lean_ctor_set(v___x_68_, 1, v___x_67_);
return v___x_68_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iter_flatMapAfter(lean_object* v_00_u03b1_71_, lean_object* v_00_u03b2_72_, lean_object* v_00_u03b1_u2082_73_, lean_object* v_00_u03b3_74_, lean_object* v_inst_75_, lean_object* v_inst_76_, lean_object* v_f_77_, lean_object* v_it_u2081_78_, lean_object* v_it_u2082_79_){
_start:
{
if (lean_obj_tag(v_it_u2082_79_) == 0)
{
lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_80_ = lean_box(0);
v___x_81_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_81_, 0, v_it_u2081_78_);
lean_ctor_set(v___x_81_, 1, v___x_80_);
return v___x_81_;
}
else
{
lean_object* v_val_82_; lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_90_; 
v_val_82_ = lean_ctor_get(v_it_u2082_79_, 0);
v_isSharedCheck_90_ = !lean_is_exclusive(v_it_u2082_79_);
if (v_isSharedCheck_90_ == 0)
{
v___x_84_ = v_it_u2082_79_;
v_isShared_85_ = v_isSharedCheck_90_;
goto v_resetjp_83_;
}
else
{
lean_inc(v_val_82_);
lean_dec(v_it_u2082_79_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_90_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
lean_object* v___x_87_; 
if (v_isShared_85_ == 0)
{
v___x_87_ = v___x_84_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v_val_82_);
v___x_87_ = v_reuseFailAlloc_89_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
lean_object* v___x_88_; 
v___x_88_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_88_, 0, v_it_u2081_78_);
lean_ctor_set(v___x_88_, 1, v___x_87_);
return v___x_88_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iter_flatMapAfter___boxed(lean_object* v_00_u03b1_91_, lean_object* v_00_u03b2_92_, lean_object* v_00_u03b1_u2082_93_, lean_object* v_00_u03b3_94_, lean_object* v_inst_95_, lean_object* v_inst_96_, lean_object* v_f_97_, lean_object* v_it_u2081_98_, lean_object* v_it_u2082_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Std_Iter_flatMapAfter(v_00_u03b1_91_, v_00_u03b2_92_, v_00_u03b1_u2082_93_, v_00_u03b3_94_, v_inst_95_, v_inst_96_, v_f_97_, v_it_u2081_98_, v_it_u2082_99_);
lean_dec(v_f_97_);
lean_dec(v_inst_96_);
lean_dec(v_inst_95_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_flatMap___redArg(lean_object* v_it_101_){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_102_ = lean_box(0);
v___x_103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_103_, 0, v_it_101_);
lean_ctor_set(v___x_103_, 1, v___x_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_flatMap(lean_object* v_00_u03b1_104_, lean_object* v_00_u03b2_105_, lean_object* v_00_u03b1_u2082_106_, lean_object* v_00_u03b3_107_, lean_object* v_inst_108_, lean_object* v_inst_109_, lean_object* v_f_110_, lean_object* v_it_111_){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_112_ = lean_box(0);
v___x_113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_113_, 0, v_it_111_);
lean_ctor_set(v___x_113_, 1, v___x_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_flatMap___boxed(lean_object* v_00_u03b1_114_, lean_object* v_00_u03b2_115_, lean_object* v_00_u03b1_u2082_116_, lean_object* v_00_u03b3_117_, lean_object* v_inst_118_, lean_object* v_inst_119_, lean_object* v_f_120_, lean_object* v_it_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l_Std_Iter_flatMap(v_00_u03b1_114_, v_00_u03b2_115_, v_00_u03b1_u2082_116_, v_00_u03b3_117_, v_inst_118_, v_inst_119_, v_f_120_, v_it_121_);
lean_dec(v_f_120_);
lean_dec(v_inst_119_);
lean_dec(v_inst_118_);
return v_res_122_;
}
}
lean_object* runtime_initialize_Init_Data_Iterators_Combinators_Monadic_FlatMap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Combinators_FilterMap(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Iterators_Combinators_FlatMap(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Iterators_Combinators_Monadic_FlatMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Combinators_FilterMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Iterators_Combinators_FlatMap(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Iterators_Combinators_Monadic_FlatMap(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Combinators_FilterMap(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Iterators_Combinators_FlatMap(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Iterators_Combinators_Monadic_FlatMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Combinators_FilterMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Combinators_FlatMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Iterators_Combinators_FlatMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Iterators_Combinators_FlatMap(builtin);
}
#ifdef __cplusplus
}
#endif

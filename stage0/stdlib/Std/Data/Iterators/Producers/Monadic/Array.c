// Lean compiler output
// Module: Std.Data.Iterators.Producers.Monadic.Array
// Imports: public import Init.Data.Iterators.Consumers import Init.Omega
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_iterFromIdxM___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_iterFromIdxM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_iterFromIdxM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_iterM___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_iterM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_iterM___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ArrayIterator_instIterator___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ArrayIterator_instIterator___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ArrayIterator_instIterator(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Producers_Monadic_Array_0__Std_Iterators_Types_ArrayIterator_instFinitenessRelation(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Producers_Monadic_Array_0__Std_Iterators_Types_ArrayIterator_instFinitenessRelation___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ArrayIterator_instIteratorLoop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ArrayIterator_instIteratorLoop___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ArrayIterator_instIteratorLoop___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ArrayIterator_instIteratorLoop___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ArrayIterator_instIteratorLoop___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ArrayIterator_instIteratorLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_iterFromIdxM___redArg(lean_object* v_array_1_, lean_object* v_pos_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3_, 0, v_array_1_);
lean_ctor_set(v___x_3_, 1, v_pos_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Array_iterFromIdxM(lean_object* v_00_u03b1_4_, lean_object* v_array_5_, lean_object* v_m_6_, lean_object* v_pos_7_, lean_object* v_inst_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_9_, 0, v_array_5_);
lean_ctor_set(v___x_9_, 1, v_pos_7_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Array_iterFromIdxM___boxed(lean_object* v_00_u03b1_10_, lean_object* v_array_11_, lean_object* v_m_12_, lean_object* v_pos_13_, lean_object* v_inst_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l_Array_iterFromIdxM(v_00_u03b1_10_, v_array_11_, v_m_12_, v_pos_13_, v_inst_14_);
lean_dec(v_inst_14_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Array_iterM___redArg(lean_object* v_array_16_){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_17_ = lean_unsigned_to_nat(0u);
v___x_18_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_18_, 0, v_array_16_);
lean_ctor_set(v___x_18_, 1, v___x_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Array_iterM(lean_object* v_00_u03b1_19_, lean_object* v_array_20_, lean_object* v_m_21_, lean_object* v_inst_22_){
_start:
{
lean_object* v___x_23_; lean_object* v___x_24_; 
v___x_23_ = lean_unsigned_to_nat(0u);
v___x_24_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_24_, 0, v_array_20_);
lean_ctor_set(v___x_24_, 1, v___x_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Array_iterM___boxed(lean_object* v_00_u03b1_25_, lean_object* v_array_26_, lean_object* v_m_27_, lean_object* v_inst_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Array_iterM(v_00_u03b1_25_, v_array_26_, v_m_27_, v_inst_28_);
lean_dec(v_inst_28_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ArrayIterator_instIterator___redArg___lam__0(lean_object* v_inst_30_, lean_object* v_it_31_){
_start:
{
lean_object* v_array_32_; lean_object* v_pos_33_; lean_object* v___x_35_; uint8_t v_isShared_36_; uint8_t v_isSharedCheck_49_; 
v_array_32_ = lean_ctor_get(v_it_31_, 0);
v_pos_33_ = lean_ctor_get(v_it_31_, 1);
v_isSharedCheck_49_ = !lean_is_exclusive(v_it_31_);
if (v_isSharedCheck_49_ == 0)
{
v___x_35_ = v_it_31_;
v_isShared_36_ = v_isSharedCheck_49_;
goto v_resetjp_34_;
}
else
{
lean_inc(v_pos_33_);
lean_inc(v_array_32_);
lean_dec(v_it_31_);
v___x_35_ = lean_box(0);
v_isShared_36_ = v_isSharedCheck_49_;
goto v_resetjp_34_;
}
v_resetjp_34_:
{
lean_object* v___x_37_; uint8_t v___x_38_; 
v___x_37_ = lean_array_get_size(v_array_32_);
v___x_38_ = lean_nat_dec_lt(v_pos_33_, v___x_37_);
if (v___x_38_ == 0)
{
lean_object* v___x_39_; lean_object* v___x_40_; 
lean_del_object(v___x_35_);
lean_dec(v_pos_33_);
lean_dec_ref(v_array_32_);
v___x_39_ = lean_box(2);
v___x_40_ = lean_apply_2(v_inst_30_, lean_box(0), v___x_39_);
return v___x_40_;
}
else
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_44_; 
v___x_41_ = lean_unsigned_to_nat(1u);
v___x_42_ = lean_nat_add(v_pos_33_, v___x_41_);
lean_inc_ref(v_array_32_);
if (v_isShared_36_ == 0)
{
lean_ctor_set(v___x_35_, 1, v___x_42_);
v___x_44_ = v___x_35_;
goto v_reusejp_43_;
}
else
{
lean_object* v_reuseFailAlloc_48_; 
v_reuseFailAlloc_48_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_48_, 0, v_array_32_);
lean_ctor_set(v_reuseFailAlloc_48_, 1, v___x_42_);
v___x_44_ = v_reuseFailAlloc_48_;
goto v_reusejp_43_;
}
v_reusejp_43_:
{
lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_45_ = lean_array_fget(v_array_32_, v_pos_33_);
lean_dec(v_pos_33_);
lean_dec_ref(v_array_32_);
v___x_46_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_46_, 0, v___x_44_);
lean_ctor_set(v___x_46_, 1, v___x_45_);
v___x_47_ = lean_apply_2(v_inst_30_, lean_box(0), v___x_46_);
return v___x_47_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ArrayIterator_instIterator___redArg(lean_object* v_inst_50_){
_start:
{
lean_object* v___f_51_; 
v___f_51_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_ArrayIterator_instIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_51_, 0, v_inst_50_);
return v___f_51_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ArrayIterator_instIterator(lean_object* v_m_52_, lean_object* v_00_u03b1_53_, lean_object* v_inst_54_){
_start:
{
lean_object* v___f_55_; 
v___f_55_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_ArrayIterator_instIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_55_, 0, v_inst_54_);
return v___f_55_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Producers_Monadic_Array_0__Std_Iterators_Types_ArrayIterator_instFinitenessRelation(lean_object* v_00_u03b1_56_, lean_object* v_m_57_, lean_object* v_inst_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = lean_box(0);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Producers_Monadic_Array_0__Std_Iterators_Types_ArrayIterator_instFinitenessRelation___boxed(lean_object* v_00_u03b1_60_, lean_object* v_m_61_, lean_object* v_inst_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l___private_Std_Data_Iterators_Producers_Monadic_Array_0__Std_Iterators_Types_ArrayIterator_instFinitenessRelation(v_00_u03b1_60_, v_m_61_, v_inst_62_);
lean_dec(v_inst_62_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ArrayIterator_instIteratorLoop___redArg___lam__0(lean_object* v_toPure_64_, lean_object* v_recur_65_, lean_object* v_it_66_, lean_object* v_____do__lift_67_){
_start:
{
if (lean_obj_tag(v_____do__lift_67_) == 0)
{
lean_object* v_a_68_; lean_object* v___x_69_; 
lean_dec_ref(v_it_66_);
lean_dec(v_recur_65_);
v_a_68_ = lean_ctor_get(v_____do__lift_67_, 0);
lean_inc(v_a_68_);
lean_dec_ref(v_____do__lift_67_);
v___x_69_ = lean_apply_2(v_toPure_64_, lean_box(0), v_a_68_);
return v___x_69_;
}
else
{
lean_object* v_a_70_; lean_object* v___x_71_; 
lean_dec(v_toPure_64_);
v_a_70_ = lean_ctor_get(v_____do__lift_67_, 0);
lean_inc(v_a_70_);
lean_dec_ref(v_____do__lift_67_);
v___x_71_ = lean_apply_4(v_recur_65_, v_it_66_, v_a_70_, lean_box(0), lean_box(0));
return v___x_71_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ArrayIterator_instIteratorLoop___redArg___lam__1(lean_object* v_toPure_72_, lean_object* v_recur_73_, lean_object* v___y_74_, lean_object* v_acc_75_, lean_object* v_toBind_76_, lean_object* v_s_77_){
_start:
{
switch(lean_obj_tag(v_s_77_))
{
case 0:
{
lean_object* v_it_78_; lean_object* v_out_79_; lean_object* v___f_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v_it_78_ = lean_ctor_get(v_s_77_, 0);
lean_inc(v_it_78_);
v_out_79_ = lean_ctor_get(v_s_77_, 1);
lean_inc(v_out_79_);
lean_dec_ref(v_s_77_);
v___f_80_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_ArrayIterator_instIteratorLoop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_80_, 0, v_toPure_72_);
lean_closure_set(v___f_80_, 1, v_recur_73_);
lean_closure_set(v___f_80_, 2, v_it_78_);
v___x_81_ = lean_apply_3(v___y_74_, v_out_79_, lean_box(0), v_acc_75_);
v___x_82_ = lean_apply_4(v_toBind_76_, lean_box(0), lean_box(0), v___x_81_, v___f_80_);
return v___x_82_;
}
case 1:
{
lean_object* v_it_83_; lean_object* v___x_84_; 
lean_dec(v_toBind_76_);
lean_dec(v___y_74_);
lean_dec(v_toPure_72_);
v_it_83_ = lean_ctor_get(v_s_77_, 0);
lean_inc(v_it_83_);
lean_dec_ref(v_s_77_);
v___x_84_ = lean_apply_4(v_recur_73_, v_it_83_, v_acc_75_, lean_box(0), lean_box(0));
return v___x_84_;
}
default: 
{
lean_object* v___x_85_; 
lean_dec(v_toBind_76_);
lean_dec(v___y_74_);
lean_dec(v_recur_73_);
v___x_85_ = lean_apply_2(v_toPure_72_, lean_box(0), v_acc_75_);
return v___x_85_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ArrayIterator_instIteratorLoop___redArg___lam__2(lean_object* v_toPure_86_, lean_object* v___y_87_, lean_object* v_toBind_88_, lean_object* v_toPure_89_, lean_object* v_lift_90_, lean_object* v_it_91_, lean_object* v_acc_92_, lean_object* v_hP_93_, lean_object* v_recur_94_){
_start:
{
lean_object* v_array_95_; lean_object* v_pos_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_115_; 
v_array_95_ = lean_ctor_get(v_it_91_, 0);
v_pos_96_ = lean_ctor_get(v_it_91_, 1);
v_isSharedCheck_115_ = !lean_is_exclusive(v_it_91_);
if (v_isSharedCheck_115_ == 0)
{
v___x_98_ = v_it_91_;
v_isShared_99_ = v_isSharedCheck_115_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_pos_96_);
lean_inc(v_array_95_);
lean_dec(v_it_91_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_115_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v___f_100_; lean_object* v___x_101_; uint8_t v___x_102_; 
v___f_100_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_ArrayIterator_instIteratorLoop___redArg___lam__1), 6, 5);
lean_closure_set(v___f_100_, 0, v_toPure_86_);
lean_closure_set(v___f_100_, 1, v_recur_94_);
lean_closure_set(v___f_100_, 2, v___y_87_);
lean_closure_set(v___f_100_, 3, v_acc_92_);
lean_closure_set(v___f_100_, 4, v_toBind_88_);
v___x_101_ = lean_array_get_size(v_array_95_);
v___x_102_ = lean_nat_dec_lt(v_pos_96_, v___x_101_);
if (v___x_102_ == 0)
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
lean_del_object(v___x_98_);
lean_dec(v_pos_96_);
lean_dec_ref(v_array_95_);
v___x_103_ = lean_box(2);
v___x_104_ = lean_apply_2(v_toPure_89_, lean_box(0), v___x_103_);
v___x_105_ = lean_apply_4(v_lift_90_, lean_box(0), lean_box(0), v___f_100_, v___x_104_);
return v___x_105_;
}
else
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_109_; 
v___x_106_ = lean_unsigned_to_nat(1u);
v___x_107_ = lean_nat_add(v_pos_96_, v___x_106_);
lean_inc_ref(v_array_95_);
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 1, v___x_107_);
v___x_109_ = v___x_98_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v_array_95_);
lean_ctor_set(v_reuseFailAlloc_114_, 1, v___x_107_);
v___x_109_ = v_reuseFailAlloc_114_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_110_ = lean_array_fget(v_array_95_, v_pos_96_);
lean_dec(v_pos_96_);
lean_dec_ref(v_array_95_);
v___x_111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_111_, 0, v___x_109_);
lean_ctor_set(v___x_111_, 1, v___x_110_);
v___x_112_ = lean_apply_2(v_toPure_89_, lean_box(0), v___x_111_);
v___x_113_ = lean_apply_4(v_lift_90_, lean_box(0), lean_box(0), v___f_100_, v___x_112_);
return v___x_113_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ArrayIterator_instIteratorLoop___redArg___lam__3(lean_object* v_inst_116_, lean_object* v_toPure_117_, lean_object* v_lift_118_, lean_object* v_00_u03b3_119_, lean_object* v_Pl_120_, lean_object* v_it_121_, lean_object* v_init_122_, lean_object* v___y_123_){
_start:
{
lean_object* v_toApplicative_124_; lean_object* v_toBind_125_; lean_object* v_toPure_126_; lean_object* v___f_127_; lean_object* v___x_128_; 
v_toApplicative_124_ = lean_ctor_get(v_inst_116_, 0);
lean_inc_ref(v_toApplicative_124_);
v_toBind_125_ = lean_ctor_get(v_inst_116_, 1);
lean_inc(v_toBind_125_);
lean_dec_ref(v_inst_116_);
v_toPure_126_ = lean_ctor_get(v_toApplicative_124_, 1);
lean_inc(v_toPure_126_);
lean_dec_ref(v_toApplicative_124_);
v___f_127_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_ArrayIterator_instIteratorLoop___redArg___lam__2), 9, 5);
lean_closure_set(v___f_127_, 0, v_toPure_126_);
lean_closure_set(v___f_127_, 1, v___y_123_);
lean_closure_set(v___f_127_, 2, v_toBind_125_);
lean_closure_set(v___f_127_, 3, v_toPure_117_);
lean_closure_set(v___f_127_, 4, v_lift_118_);
v___x_128_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_127_, v_it_121_, v_init_122_, lean_box(0));
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ArrayIterator_instIteratorLoop___redArg(lean_object* v_inst_129_, lean_object* v_inst_130_){
_start:
{
lean_object* v_toApplicative_131_; lean_object* v_toPure_132_; lean_object* v___f_133_; 
v_toApplicative_131_ = lean_ctor_get(v_inst_129_, 0);
lean_inc_ref(v_toApplicative_131_);
lean_dec_ref(v_inst_129_);
v_toPure_132_ = lean_ctor_get(v_toApplicative_131_, 1);
lean_inc(v_toPure_132_);
lean_dec_ref(v_toApplicative_131_);
v___f_133_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_ArrayIterator_instIteratorLoop___redArg___lam__3), 8, 2);
lean_closure_set(v___f_133_, 0, v_inst_130_);
lean_closure_set(v___f_133_, 1, v_toPure_132_);
return v___f_133_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ArrayIterator_instIteratorLoop(lean_object* v_m_134_, lean_object* v_00_u03b1_135_, lean_object* v_inst_136_, lean_object* v_n_137_, lean_object* v_inst_138_){
_start:
{
lean_object* v_toApplicative_139_; lean_object* v_toPure_140_; lean_object* v___f_141_; 
v_toApplicative_139_ = lean_ctor_get(v_inst_136_, 0);
lean_inc_ref(v_toApplicative_139_);
lean_dec_ref(v_inst_136_);
v_toPure_140_ = lean_ctor_get(v_toApplicative_139_, 1);
lean_inc(v_toPure_140_);
lean_dec_ref(v_toApplicative_139_);
v___f_141_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_ArrayIterator_instIteratorLoop___redArg___lam__3), 8, 2);
lean_closure_set(v___f_141_, 0, v_inst_138_);
lean_closure_set(v___f_141_, 1, v_toPure_140_);
return v___f_141_;
}
}
lean_object* runtime_initialize_Init_Data_Iterators_Consumers(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_Iterators_Producers_Monadic_Array(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Iterators_Consumers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_Iterators_Producers_Monadic_Array(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Iterators_Consumers(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_Iterators_Producers_Monadic_Array(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Iterators_Consumers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_Iterators_Producers_Monadic_Array(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_Iterators_Producers_Monadic_Array(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_Iterators_Producers_Monadic_Array(builtin);
}
#ifdef __cplusplus
}
#endif

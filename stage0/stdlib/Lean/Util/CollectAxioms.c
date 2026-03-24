// Lean compiler output
// Module: Lean.Util.CollectAxioms
// Imports: public import Lean.MonadEnv
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* lean_task_get_own(lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getUsedConstants(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CollectAxioms_collect_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectAxioms_collect___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectAxioms_collect(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_CollectAxioms_collect_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_CollectAxioms_collect_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CollectAxioms_collect_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectAxioms_collect___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_collectAxioms___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_collectAxioms___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_collectAxioms___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_collectAxioms___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_collectAxioms___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_collectAxioms___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_collectAxioms___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_collectAxioms(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CollectAxioms_collect_spec__0(lean_object* v_as_1_, size_t v_i_2_, size_t v_stop_3_, lean_object* v_b_4_, lean_object* v___y_5_, lean_object* v___y_6_){
_start:
{
uint8_t v___x_7_; 
v___x_7_ = lean_usize_dec_eq(v_i_2_, v_stop_3_);
if (v___x_7_ == 0)
{
lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v_fst_10_; lean_object* v_snd_11_; size_t v___x_12_; size_t v___x_13_; 
v___x_8_ = lean_array_uget_borrowed(v_as_1_, v_i_2_);
lean_inc_ref(v___y_5_);
lean_inc(v___x_8_);
v___x_9_ = l_Lean_CollectAxioms_collect(v___x_8_, v___y_5_, v___y_6_);
v_fst_10_ = lean_ctor_get(v___x_9_, 0);
lean_inc(v_fst_10_);
v_snd_11_ = lean_ctor_get(v___x_9_, 1);
lean_inc(v_snd_11_);
lean_dec_ref(v___x_9_);
v___x_12_ = ((size_t)1ULL);
v___x_13_ = lean_usize_add(v_i_2_, v___x_12_);
v_i_2_ = v___x_13_;
v_b_4_ = v_fst_10_;
v___y_6_ = v_snd_11_;
goto _start;
}
else
{
lean_object* v___x_15_; 
v___x_15_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_15_, 0, v_b_4_);
lean_ctor_set(v___x_15_, 1, v___y_6_);
return v___x_15_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_CollectAxioms_collect___lam__0(lean_object* v_e_16_, lean_object* v___y_17_, lean_object* v___y_18_){
_start:
{
lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; uint8_t v___x_23_; 
v___x_19_ = l_Lean_Expr_getUsedConstants(v_e_16_);
v___x_20_ = lean_unsigned_to_nat(0u);
v___x_21_ = lean_array_get_size(v___x_19_);
v___x_22_ = lean_box(0);
v___x_23_ = lean_nat_dec_lt(v___x_20_, v___x_21_);
if (v___x_23_ == 0)
{
lean_object* v___x_24_; 
lean_dec_ref(v___x_19_);
v___x_24_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_24_, 0, v___x_22_);
lean_ctor_set(v___x_24_, 1, v___y_18_);
return v___x_24_;
}
else
{
uint8_t v___x_25_; 
v___x_25_ = lean_nat_dec_le(v___x_21_, v___x_21_);
if (v___x_25_ == 0)
{
if (v___x_23_ == 0)
{
lean_object* v___x_26_; 
lean_dec_ref(v___x_19_);
v___x_26_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_26_, 0, v___x_22_);
lean_ctor_set(v___x_26_, 1, v___y_18_);
return v___x_26_;
}
else
{
size_t v___x_27_; size_t v___x_28_; lean_object* v___x_29_; 
v___x_27_ = ((size_t)0ULL);
v___x_28_ = lean_usize_of_nat(v___x_21_);
v___x_29_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CollectAxioms_collect_spec__0(v___x_19_, v___x_27_, v___x_28_, v___x_22_, v___y_17_, v___y_18_);
lean_dec_ref(v___x_19_);
return v___x_29_;
}
}
else
{
size_t v___x_30_; size_t v___x_31_; lean_object* v___x_32_; 
v___x_30_ = ((size_t)0ULL);
v___x_31_ = lean_usize_of_nat(v___x_21_);
v___x_32_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CollectAxioms_collect_spec__0(v___x_19_, v___x_30_, v___x_31_, v___x_22_, v___y_17_, v___y_18_);
lean_dec_ref(v___x_19_);
return v___x_32_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_CollectAxioms_collect(lean_object* v_c_33_, lean_object* v_a_34_, lean_object* v_a_35_){
_start:
{
lean_object* v_visited_36_; lean_object* v_axioms_37_; uint8_t v___x_38_; 
v_visited_36_ = lean_ctor_get(v_a_35_, 0);
v_axioms_37_ = lean_ctor_get(v_a_35_, 1);
v___x_38_ = l_Lean_NameSet_contains(v_visited_36_, v_c_33_);
if (v___x_38_ == 0)
{
lean_object* v___x_40_; uint8_t v_isShared_41_; uint8_t v_isSharedCheck_82_; 
lean_inc_ref(v_axioms_37_);
lean_inc(v_visited_36_);
v_isSharedCheck_82_ = !lean_is_exclusive(v_a_35_);
if (v_isSharedCheck_82_ == 0)
{
lean_object* v_unused_83_; lean_object* v_unused_84_; 
v_unused_83_ = lean_ctor_get(v_a_35_, 1);
lean_dec(v_unused_83_);
v_unused_84_ = lean_ctor_get(v_a_35_, 0);
lean_dec(v_unused_84_);
v___x_40_ = v_a_35_;
v_isShared_41_ = v_isSharedCheck_82_;
goto v_resetjp_39_;
}
else
{
lean_dec(v_a_35_);
v___x_40_ = lean_box(0);
v_isShared_41_ = v_isSharedCheck_82_;
goto v_resetjp_39_;
}
v_resetjp_39_:
{
lean_object* v_checked_42_; lean_object* v___x_43_; lean_object* v___x_45_; 
v_checked_42_ = lean_ctor_get(v_a_34_, 2);
lean_inc(v_c_33_);
v___x_43_ = l_Lean_NameSet_insert(v_visited_36_, v_c_33_);
lean_inc_ref(v_axioms_37_);
lean_inc(v___x_43_);
if (v_isShared_41_ == 0)
{
lean_ctor_set(v___x_40_, 0, v___x_43_);
v___x_45_ = v___x_40_;
goto v_reusejp_44_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v___x_43_);
lean_ctor_set(v_reuseFailAlloc_81_, 1, v_axioms_37_);
v___x_45_ = v_reuseFailAlloc_81_;
goto v_reusejp_44_;
}
v_reusejp_44_:
{
lean_object* v___x_46_; lean_object* v___x_47_; 
lean_inc_ref(v_checked_42_);
v___x_46_ = lean_task_get_own(v_checked_42_);
lean_inc(v_c_33_);
v___x_47_ = lean_environment_find(v___x_46_, v_c_33_);
if (lean_obj_tag(v___x_47_) == 0)
{
lean_object* v___x_48_; lean_object* v___x_49_; 
lean_dec(v___x_43_);
lean_dec_ref(v_axioms_37_);
lean_dec_ref(v_a_34_);
lean_dec(v_c_33_);
v___x_48_ = lean_box(0);
v___x_49_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_49_, 0, v___x_48_);
lean_ctor_set(v___x_49_, 1, v___x_45_);
return v___x_49_;
}
else
{
lean_object* v_val_50_; 
v_val_50_ = lean_ctor_get(v___x_47_, 0);
lean_inc(v_val_50_);
lean_dec_ref(v___x_47_);
switch(lean_obj_tag(v_val_50_))
{
case 0:
{
lean_object* v_val_51_; lean_object* v_toConstantVal_52_; lean_object* v_type_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
lean_dec_ref(v___x_45_);
v_val_51_ = lean_ctor_get(v_val_50_, 0);
lean_inc_ref(v_val_51_);
lean_dec_ref(v_val_50_);
v_toConstantVal_52_ = lean_ctor_get(v_val_51_, 0);
lean_inc_ref(v_toConstantVal_52_);
lean_dec_ref(v_val_51_);
v_type_53_ = lean_ctor_get(v_toConstantVal_52_, 2);
lean_inc_ref(v_type_53_);
lean_dec_ref(v_toConstantVal_52_);
v___x_54_ = lean_array_push(v_axioms_37_, v_c_33_);
v___x_55_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_55_, 0, v___x_43_);
lean_ctor_set(v___x_55_, 1, v___x_54_);
v___x_56_ = l_Lean_CollectAxioms_collect___lam__0(v_type_53_, v_a_34_, v___x_55_);
lean_dec_ref(v_a_34_);
return v___x_56_;
}
case 4:
{
lean_object* v___x_57_; lean_object* v___x_58_; 
lean_dec_ref(v_val_50_);
lean_dec(v___x_43_);
lean_dec_ref(v_axioms_37_);
lean_dec_ref(v_a_34_);
lean_dec(v_c_33_);
v___x_57_ = lean_box(0);
v___x_58_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_58_, 0, v___x_57_);
lean_ctor_set(v___x_58_, 1, v___x_45_);
return v___x_58_;
}
case 5:
{
lean_object* v_val_59_; lean_object* v_toConstantVal_60_; lean_object* v_ctors_61_; lean_object* v_type_62_; lean_object* v___x_63_; lean_object* v_snd_64_; lean_object* v___x_65_; 
lean_dec(v___x_43_);
lean_dec_ref(v_axioms_37_);
lean_dec(v_c_33_);
v_val_59_ = lean_ctor_get(v_val_50_, 0);
lean_inc_ref(v_val_59_);
lean_dec_ref(v_val_50_);
v_toConstantVal_60_ = lean_ctor_get(v_val_59_, 0);
lean_inc_ref(v_toConstantVal_60_);
v_ctors_61_ = lean_ctor_get(v_val_59_, 4);
lean_inc(v_ctors_61_);
lean_dec_ref(v_val_59_);
v_type_62_ = lean_ctor_get(v_toConstantVal_60_, 2);
lean_inc_ref(v_type_62_);
lean_dec_ref(v_toConstantVal_60_);
v___x_63_ = l_Lean_CollectAxioms_collect___lam__0(v_type_62_, v_a_34_, v___x_45_);
v_snd_64_ = lean_ctor_get(v___x_63_, 1);
lean_inc(v_snd_64_);
lean_dec_ref(v___x_63_);
v___x_65_ = l_List_forM___at___00Lean_CollectAxioms_collect_spec__1(v_ctors_61_, v_a_34_, v_snd_64_);
lean_dec_ref(v_a_34_);
return v___x_65_;
}
case 6:
{
lean_object* v_val_66_; lean_object* v_toConstantVal_67_; lean_object* v_type_68_; lean_object* v___x_69_; 
lean_dec(v___x_43_);
lean_dec_ref(v_axioms_37_);
lean_dec(v_c_33_);
v_val_66_ = lean_ctor_get(v_val_50_, 0);
lean_inc_ref(v_val_66_);
lean_dec_ref(v_val_50_);
v_toConstantVal_67_ = lean_ctor_get(v_val_66_, 0);
lean_inc_ref(v_toConstantVal_67_);
lean_dec_ref(v_val_66_);
v_type_68_ = lean_ctor_get(v_toConstantVal_67_, 2);
lean_inc_ref(v_type_68_);
lean_dec_ref(v_toConstantVal_67_);
v___x_69_ = l_Lean_CollectAxioms_collect___lam__0(v_type_68_, v_a_34_, v___x_45_);
lean_dec_ref(v_a_34_);
return v___x_69_;
}
case 7:
{
lean_object* v_val_70_; lean_object* v_toConstantVal_71_; lean_object* v_type_72_; lean_object* v___x_73_; 
lean_dec(v___x_43_);
lean_dec_ref(v_axioms_37_);
lean_dec(v_c_33_);
v_val_70_ = lean_ctor_get(v_val_50_, 0);
lean_inc_ref(v_val_70_);
lean_dec_ref(v_val_50_);
v_toConstantVal_71_ = lean_ctor_get(v_val_70_, 0);
lean_inc_ref(v_toConstantVal_71_);
lean_dec_ref(v_val_70_);
v_type_72_ = lean_ctor_get(v_toConstantVal_71_, 2);
lean_inc_ref(v_type_72_);
lean_dec_ref(v_toConstantVal_71_);
v___x_73_ = l_Lean_CollectAxioms_collect___lam__0(v_type_72_, v_a_34_, v___x_45_);
lean_dec_ref(v_a_34_);
return v___x_73_;
}
default: 
{
lean_object* v_val_74_; lean_object* v_toConstantVal_75_; lean_object* v_value_76_; lean_object* v_type_77_; lean_object* v___x_78_; lean_object* v_snd_79_; lean_object* v___x_80_; 
lean_dec(v___x_43_);
lean_dec_ref(v_axioms_37_);
lean_dec(v_c_33_);
v_val_74_ = lean_ctor_get(v_val_50_, 0);
lean_inc_ref(v_val_74_);
lean_dec(v_val_50_);
v_toConstantVal_75_ = lean_ctor_get(v_val_74_, 0);
lean_inc_ref(v_toConstantVal_75_);
v_value_76_ = lean_ctor_get(v_val_74_, 1);
lean_inc_ref(v_value_76_);
lean_dec_ref(v_val_74_);
v_type_77_ = lean_ctor_get(v_toConstantVal_75_, 2);
lean_inc_ref(v_type_77_);
lean_dec_ref(v_toConstantVal_75_);
v___x_78_ = l_Lean_CollectAxioms_collect___lam__0(v_type_77_, v_a_34_, v___x_45_);
v_snd_79_ = lean_ctor_get(v___x_78_, 1);
lean_inc(v_snd_79_);
lean_dec_ref(v___x_78_);
v___x_80_ = l_Lean_CollectAxioms_collect___lam__0(v_value_76_, v_a_34_, v_snd_79_);
lean_dec_ref(v_a_34_);
return v___x_80_;
}
}
}
}
}
}
else
{
lean_object* v___x_85_; lean_object* v___x_86_; 
lean_dec_ref(v_a_34_);
lean_dec(v_c_33_);
v___x_85_ = lean_box(0);
v___x_86_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_86_, 0, v___x_85_);
lean_ctor_set(v___x_86_, 1, v_a_35_);
return v___x_86_;
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_CollectAxioms_collect_spec__1(lean_object* v_as_87_, lean_object* v___y_88_, lean_object* v___y_89_){
_start:
{
if (lean_obj_tag(v_as_87_) == 0)
{
lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_90_ = lean_box(0);
v___x_91_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_91_, 0, v___x_90_);
lean_ctor_set(v___x_91_, 1, v___y_89_);
return v___x_91_;
}
else
{
lean_object* v_head_92_; lean_object* v_tail_93_; lean_object* v___x_94_; lean_object* v_snd_95_; 
v_head_92_ = lean_ctor_get(v_as_87_, 0);
lean_inc(v_head_92_);
v_tail_93_ = lean_ctor_get(v_as_87_, 1);
lean_inc(v_tail_93_);
lean_dec_ref(v_as_87_);
lean_inc_ref(v___y_88_);
v___x_94_ = l_Lean_CollectAxioms_collect(v_head_92_, v___y_88_, v___y_89_);
v_snd_95_ = lean_ctor_get(v___x_94_, 1);
lean_inc(v_snd_95_);
lean_dec_ref(v___x_94_);
v_as_87_ = v_tail_93_;
v___y_89_ = v_snd_95_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_CollectAxioms_collect_spec__1___boxed(lean_object* v_as_97_, lean_object* v___y_98_, lean_object* v___y_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_List_forM___at___00Lean_CollectAxioms_collect_spec__1(v_as_97_, v___y_98_, v___y_99_);
lean_dec_ref(v___y_98_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CollectAxioms_collect_spec__0___boxed(lean_object* v_as_101_, lean_object* v_i_102_, lean_object* v_stop_103_, lean_object* v_b_104_, lean_object* v___y_105_, lean_object* v___y_106_){
_start:
{
size_t v_i_boxed_107_; size_t v_stop_boxed_108_; lean_object* v_res_109_; 
v_i_boxed_107_ = lean_unbox_usize(v_i_102_);
lean_dec(v_i_102_);
v_stop_boxed_108_ = lean_unbox_usize(v_stop_103_);
lean_dec(v_stop_103_);
v_res_109_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CollectAxioms_collect_spec__0(v_as_101_, v_i_boxed_107_, v_stop_boxed_108_, v_b_104_, v___y_105_, v___y_106_);
lean_dec_ref(v___y_105_);
lean_dec_ref(v_as_101_);
return v_res_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_CollectAxioms_collect___lam__0___boxed(lean_object* v_e_110_, lean_object* v___y_111_, lean_object* v___y_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_Lean_CollectAxioms_collect___lam__0(v_e_110_, v___y_111_, v___y_112_);
lean_dec_ref(v___y_111_);
return v_res_113_;
}
}
static lean_object* _init_l_Lean_collectAxioms___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_116_ = ((lean_object*)(l_Lean_collectAxioms___redArg___lam__0___closed__0));
v___x_117_ = l_Lean_NameSet_empty;
v___x_118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_118_, 0, v___x_117_);
lean_ctor_set(v___x_118_, 1, v___x_116_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_collectAxioms___redArg___lam__0(lean_object* v_constName_119_, lean_object* v_toPure_120_, lean_object* v_env_121_){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v_snd_124_; lean_object* v_axioms_125_; lean_object* v___x_126_; 
v___x_122_ = lean_obj_once(&l_Lean_collectAxioms___redArg___lam__0___closed__1, &l_Lean_collectAxioms___redArg___lam__0___closed__1_once, _init_l_Lean_collectAxioms___redArg___lam__0___closed__1);
v___x_123_ = l_Lean_CollectAxioms_collect(v_constName_119_, v_env_121_, v___x_122_);
v_snd_124_ = lean_ctor_get(v___x_123_, 1);
lean_inc(v_snd_124_);
lean_dec_ref(v___x_123_);
v_axioms_125_ = lean_ctor_get(v_snd_124_, 1);
lean_inc_ref(v_axioms_125_);
lean_dec(v_snd_124_);
v___x_126_ = lean_apply_2(v_toPure_120_, lean_box(0), v_axioms_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_collectAxioms___redArg(lean_object* v_inst_127_, lean_object* v_inst_128_, lean_object* v_constName_129_){
_start:
{
lean_object* v_toApplicative_130_; lean_object* v_toBind_131_; lean_object* v_getEnv_132_; lean_object* v_toPure_133_; lean_object* v___f_134_; lean_object* v___x_135_; 
v_toApplicative_130_ = lean_ctor_get(v_inst_127_, 0);
lean_inc_ref(v_toApplicative_130_);
v_toBind_131_ = lean_ctor_get(v_inst_127_, 1);
lean_inc(v_toBind_131_);
lean_dec_ref(v_inst_127_);
v_getEnv_132_ = lean_ctor_get(v_inst_128_, 0);
lean_inc(v_getEnv_132_);
lean_dec_ref(v_inst_128_);
v_toPure_133_ = lean_ctor_get(v_toApplicative_130_, 1);
lean_inc(v_toPure_133_);
lean_dec_ref(v_toApplicative_130_);
v___f_134_ = lean_alloc_closure((void*)(l_Lean_collectAxioms___redArg___lam__0), 3, 2);
lean_closure_set(v___f_134_, 0, v_constName_129_);
lean_closure_set(v___f_134_, 1, v_toPure_133_);
v___x_135_ = lean_apply_4(v_toBind_131_, lean_box(0), lean_box(0), v_getEnv_132_, v___f_134_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_collectAxioms(lean_object* v_m_136_, lean_object* v_inst_137_, lean_object* v_inst_138_, lean_object* v_constName_139_){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = l_Lean_collectAxioms___redArg(v_inst_137_, v_inst_138_, v_constName_139_);
return v___x_140_;
}
}
lean_object* runtime_initialize_Lean_MonadEnv(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_CollectAxioms(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_MonadEnv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Util_CollectAxioms(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_MonadEnv(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_CollectAxioms(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_MonadEnv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_CollectAxioms(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Util_CollectAxioms(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Util_CollectAxioms(builtin);
}
#ifdef __cplusplus
}
#endif

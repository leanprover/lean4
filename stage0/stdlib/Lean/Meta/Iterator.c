// Lean compiler output
// Module: Lean.Meta.Iterator
// Imports: public import Lean.Meta.Basic
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
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Iterator_ofList___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Iterator_ofList___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Iterator_ofList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Iterator_ofList___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Iterator_ofList(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Iterator_ofList___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Iterator_filterMapM___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Iterator_filterMapM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Iterator_head_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Iterator_head_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Iterator_head_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Iterator_head_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Iterator_head___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "failed"};
static const lean_object* l_Lean_Meta_Iterator_head___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Iterator_head___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Iterator_head___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Iterator_head___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Iterator_head___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Iterator_head___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Iterator_head(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Iterator_head___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Iterator_head_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Iterator_head_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Iterator_firstM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Iterator_firstM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Iterator_firstM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Iterator_firstM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Iterator_ofList___redArg___lam__0(lean_object* v_a_1_, lean_object* v_val_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1_, v___y_4_, v___y_6_);
if (lean_obj_tag(v___x_8_) == 0)
{
lean_object* v___x_10_; uint8_t v_isShared_11_; uint8_t v_isSharedCheck_45_; 
v_isSharedCheck_45_ = !lean_is_exclusive(v___x_8_);
if (v_isSharedCheck_45_ == 0)
{
lean_object* v_unused_46_; 
v_unused_46_ = lean_ctor_get(v___x_8_, 0);
lean_dec(v_unused_46_);
v___x_10_ = v___x_8_;
v_isShared_11_ = v_isSharedCheck_45_;
goto v_resetjp_9_;
}
else
{
lean_dec(v___x_8_);
v___x_10_ = lean_box(0);
v_isShared_11_ = v_isSharedCheck_45_;
goto v_resetjp_9_;
}
v_resetjp_9_:
{
lean_object* v___x_12_; 
v___x_12_ = lean_st_ref_get(v_val_2_);
if (lean_obj_tag(v___x_12_) == 0)
{
lean_object* v___x_13_; lean_object* v___x_15_; 
v___x_13_ = lean_box(0);
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 0, v___x_13_);
v___x_15_ = v___x_10_;
goto v_reusejp_14_;
}
else
{
lean_object* v_reuseFailAlloc_16_; 
v_reuseFailAlloc_16_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_16_, 0, v___x_13_);
v___x_15_ = v_reuseFailAlloc_16_;
goto v_reusejp_14_;
}
v_reusejp_14_:
{
return v___x_15_;
}
}
else
{
lean_object* v_head_17_; lean_object* v_tail_18_; lean_object* v___x_20_; uint8_t v_isShared_21_; uint8_t v_isSharedCheck_44_; 
lean_del_object(v___x_10_);
v_head_17_ = lean_ctor_get(v___x_12_, 0);
v_tail_18_ = lean_ctor_get(v___x_12_, 1);
v_isSharedCheck_44_ = !lean_is_exclusive(v___x_12_);
if (v_isSharedCheck_44_ == 0)
{
v___x_20_ = v___x_12_;
v_isShared_21_ = v_isSharedCheck_44_;
goto v_resetjp_19_;
}
else
{
lean_inc(v_tail_18_);
lean_inc(v_head_17_);
lean_dec(v___x_12_);
v___x_20_ = lean_box(0);
v_isShared_21_ = v_isSharedCheck_44_;
goto v_resetjp_19_;
}
v_resetjp_19_:
{
lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_22_ = lean_st_ref_swap(v_val_2_, v_tail_18_);
lean_dec(v___x_22_);
v___x_23_ = l_Lean_Meta_saveState___redArg(v___y_4_, v___y_6_);
if (lean_obj_tag(v___x_23_) == 0)
{
lean_object* v_a_24_; lean_object* v___x_26_; uint8_t v_isShared_27_; uint8_t v_isSharedCheck_35_; 
v_a_24_ = lean_ctor_get(v___x_23_, 0);
v_isSharedCheck_35_ = !lean_is_exclusive(v___x_23_);
if (v_isSharedCheck_35_ == 0)
{
v___x_26_ = v___x_23_;
v_isShared_27_ = v_isSharedCheck_35_;
goto v_resetjp_25_;
}
else
{
lean_inc(v_a_24_);
lean_dec(v___x_23_);
v___x_26_ = lean_box(0);
v_isShared_27_ = v_isSharedCheck_35_;
goto v_resetjp_25_;
}
v_resetjp_25_:
{
lean_object* v___x_29_; 
if (v_isShared_21_ == 0)
{
lean_ctor_set_tag(v___x_20_, 0);
lean_ctor_set(v___x_20_, 1, v_a_24_);
v___x_29_ = v___x_20_;
goto v_reusejp_28_;
}
else
{
lean_object* v_reuseFailAlloc_34_; 
v_reuseFailAlloc_34_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_34_, 0, v_head_17_);
lean_ctor_set(v_reuseFailAlloc_34_, 1, v_a_24_);
v___x_29_ = v_reuseFailAlloc_34_;
goto v_reusejp_28_;
}
v_reusejp_28_:
{
lean_object* v___x_30_; lean_object* v___x_32_; 
v___x_30_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_30_, 0, v___x_29_);
if (v_isShared_27_ == 0)
{
lean_ctor_set(v___x_26_, 0, v___x_30_);
v___x_32_ = v___x_26_;
goto v_reusejp_31_;
}
else
{
lean_object* v_reuseFailAlloc_33_; 
v_reuseFailAlloc_33_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_33_, 0, v___x_30_);
v___x_32_ = v_reuseFailAlloc_33_;
goto v_reusejp_31_;
}
v_reusejp_31_:
{
return v___x_32_;
}
}
}
}
else
{
lean_object* v_a_36_; lean_object* v___x_38_; uint8_t v_isShared_39_; uint8_t v_isSharedCheck_43_; 
lean_del_object(v___x_20_);
lean_dec(v_head_17_);
v_a_36_ = lean_ctor_get(v___x_23_, 0);
v_isSharedCheck_43_ = !lean_is_exclusive(v___x_23_);
if (v_isSharedCheck_43_ == 0)
{
v___x_38_ = v___x_23_;
v_isShared_39_ = v_isSharedCheck_43_;
goto v_resetjp_37_;
}
else
{
lean_inc(v_a_36_);
lean_dec(v___x_23_);
v___x_38_ = lean_box(0);
v_isShared_39_ = v_isSharedCheck_43_;
goto v_resetjp_37_;
}
v_resetjp_37_:
{
lean_object* v___x_41_; 
if (v_isShared_39_ == 0)
{
v___x_41_ = v___x_38_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_42_; 
v_reuseFailAlloc_42_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_42_, 0, v_a_36_);
v___x_41_ = v_reuseFailAlloc_42_;
goto v_reusejp_40_;
}
v_reusejp_40_:
{
return v___x_41_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_47_; lean_object* v___x_49_; uint8_t v_isShared_50_; uint8_t v_isSharedCheck_54_; 
v_a_47_ = lean_ctor_get(v___x_8_, 0);
v_isSharedCheck_54_ = !lean_is_exclusive(v___x_8_);
if (v_isSharedCheck_54_ == 0)
{
v___x_49_ = v___x_8_;
v_isShared_50_ = v_isSharedCheck_54_;
goto v_resetjp_48_;
}
else
{
lean_inc(v_a_47_);
lean_dec(v___x_8_);
v___x_49_ = lean_box(0);
v_isShared_50_ = v_isSharedCheck_54_;
goto v_resetjp_48_;
}
v_resetjp_48_:
{
lean_object* v___x_52_; 
if (v_isShared_50_ == 0)
{
v___x_52_ = v___x_49_;
goto v_reusejp_51_;
}
else
{
lean_object* v_reuseFailAlloc_53_; 
v_reuseFailAlloc_53_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_53_, 0, v_a_47_);
v___x_52_ = v_reuseFailAlloc_53_;
goto v_reusejp_51_;
}
v_reusejp_51_:
{
return v___x_52_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Iterator_ofList___redArg___lam__0___boxed(lean_object* v_a_55_, lean_object* v_val_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lean_Meta_Iterator_ofList___redArg___lam__0(v_a_55_, v_val_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_);
lean_dec(v___y_60_);
lean_dec_ref(v___y_59_);
lean_dec(v___y_58_);
lean_dec_ref(v___y_57_);
lean_dec(v_val_56_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Iterator_ofList___redArg(lean_object* v_l_63_, lean_object* v_a_64_, lean_object* v_a_65_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = l_Lean_Meta_saveState___redArg(v_a_64_, v_a_65_);
if (lean_obj_tag(v___x_67_) == 0)
{
lean_object* v_a_68_; lean_object* v___x_70_; uint8_t v_isShared_71_; uint8_t v_isSharedCheck_77_; 
v_a_68_ = lean_ctor_get(v___x_67_, 0);
v_isSharedCheck_77_ = !lean_is_exclusive(v___x_67_);
if (v_isSharedCheck_77_ == 0)
{
v___x_70_ = v___x_67_;
v_isShared_71_ = v_isSharedCheck_77_;
goto v_resetjp_69_;
}
else
{
lean_inc(v_a_68_);
lean_dec(v___x_67_);
v___x_70_ = lean_box(0);
v_isShared_71_ = v_isSharedCheck_77_;
goto v_resetjp_69_;
}
v_resetjp_69_:
{
lean_object* v___x_72_; lean_object* v___f_73_; lean_object* v___x_75_; 
v___x_72_ = lean_st_mk_ref(v_l_63_);
v___f_73_ = lean_alloc_closure((void*)(l_Lean_Meta_Iterator_ofList___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_73_, 0, v_a_68_);
lean_closure_set(v___f_73_, 1, v___x_72_);
if (v_isShared_71_ == 0)
{
lean_ctor_set(v___x_70_, 0, v___f_73_);
v___x_75_ = v___x_70_;
goto v_reusejp_74_;
}
else
{
lean_object* v_reuseFailAlloc_76_; 
v_reuseFailAlloc_76_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_76_, 0, v___f_73_);
v___x_75_ = v_reuseFailAlloc_76_;
goto v_reusejp_74_;
}
v_reusejp_74_:
{
return v___x_75_;
}
}
}
else
{
lean_object* v_a_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_85_; 
lean_dec(v_l_63_);
v_a_78_ = lean_ctor_get(v___x_67_, 0);
v_isSharedCheck_85_ = !lean_is_exclusive(v___x_67_);
if (v_isSharedCheck_85_ == 0)
{
v___x_80_ = v___x_67_;
v_isShared_81_ = v_isSharedCheck_85_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_a_78_);
lean_dec(v___x_67_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_85_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
lean_object* v___x_83_; 
if (v_isShared_81_ == 0)
{
v___x_83_ = v___x_80_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_84_; 
v_reuseFailAlloc_84_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_84_, 0, v_a_78_);
v___x_83_ = v_reuseFailAlloc_84_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
return v___x_83_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Iterator_ofList___redArg___boxed(lean_object* v_l_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Lean_Meta_Iterator_ofList___redArg(v_l_86_, v_a_87_, v_a_88_);
lean_dec(v_a_88_);
lean_dec(v_a_87_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Iterator_ofList(lean_object* v_00_u03b1_91_, lean_object* v_l_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = l_Lean_Meta_Iterator_ofList___redArg(v_l_92_, v_a_94_, v_a_96_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Iterator_ofList___boxed(lean_object* v_00_u03b1_99_, lean_object* v_l_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_Lean_Meta_Iterator_ofList(v_00_u03b1_99_, v_l_100_, v_a_101_, v_a_102_, v_a_103_, v_a_104_);
lean_dec(v_a_104_);
lean_dec_ref(v_a_103_);
lean_dec(v_a_102_);
lean_dec_ref(v_a_101_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next___redArg(lean_object* v_f_107_, lean_object* v_L_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_){
_start:
{
lean_object* v___x_114_; 
lean_inc_ref(v_L_108_);
lean_inc(v_a_112_);
lean_inc_ref(v_a_111_);
lean_inc(v_a_110_);
lean_inc_ref(v_a_109_);
v___x_114_ = lean_apply_5(v_L_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_, lean_box(0));
if (lean_obj_tag(v___x_114_) == 0)
{
lean_object* v_a_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_178_; 
v_a_115_ = lean_ctor_get(v___x_114_, 0);
v_isSharedCheck_178_ = !lean_is_exclusive(v___x_114_);
if (v_isSharedCheck_178_ == 0)
{
v___x_117_ = v___x_114_;
v_isShared_118_ = v_isSharedCheck_178_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_a_115_);
lean_dec(v___x_114_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_178_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
if (lean_obj_tag(v_a_115_) == 0)
{
lean_object* v___x_119_; lean_object* v___x_121_; 
lean_dec_ref(v_L_108_);
lean_dec_ref(v_f_107_);
v___x_119_ = lean_box(0);
if (v_isShared_118_ == 0)
{
lean_ctor_set(v___x_117_, 0, v___x_119_);
v___x_121_ = v___x_117_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v___x_119_);
v___x_121_ = v_reuseFailAlloc_122_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
return v___x_121_;
}
}
else
{
lean_object* v_val_123_; lean_object* v_fst_124_; lean_object* v_snd_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_177_; 
lean_del_object(v___x_117_);
v_val_123_ = lean_ctor_get(v_a_115_, 0);
lean_inc(v_val_123_);
lean_dec_ref_known(v_a_115_, 1);
v_fst_124_ = lean_ctor_get(v_val_123_, 0);
v_snd_125_ = lean_ctor_get(v_val_123_, 1);
v_isSharedCheck_177_ = !lean_is_exclusive(v_val_123_);
if (v_isSharedCheck_177_ == 0)
{
v___x_127_ = v_val_123_;
v_isShared_128_ = v_isSharedCheck_177_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_snd_125_);
lean_inc(v_fst_124_);
lean_dec(v_val_123_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_177_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___x_129_; 
v___x_129_ = l_Lean_Meta_SavedState_restore___redArg(v_snd_125_, v_a_110_, v_a_112_);
if (lean_obj_tag(v___x_129_) == 0)
{
lean_object* v___x_130_; 
lean_dec_ref_known(v___x_129_, 1);
lean_inc_ref(v_f_107_);
lean_inc(v_a_112_);
lean_inc_ref(v_a_111_);
lean_inc(v_a_110_);
lean_inc_ref(v_a_109_);
v___x_130_ = lean_apply_6(v_f_107_, v_fst_124_, v_a_109_, v_a_110_, v_a_111_, v_a_112_, lean_box(0));
if (lean_obj_tag(v___x_130_) == 0)
{
lean_object* v_a_131_; 
v_a_131_ = lean_ctor_get(v___x_130_, 0);
lean_inc(v_a_131_);
lean_dec_ref_known(v___x_130_, 1);
if (lean_obj_tag(v_a_131_) == 0)
{
lean_del_object(v___x_127_);
goto _start;
}
else
{
lean_object* v_val_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_160_; 
lean_dec_ref(v_L_108_);
lean_dec_ref(v_f_107_);
v_val_133_ = lean_ctor_get(v_a_131_, 0);
v_isSharedCheck_160_ = !lean_is_exclusive(v_a_131_);
if (v_isSharedCheck_160_ == 0)
{
v___x_135_ = v_a_131_;
v_isShared_136_ = v_isSharedCheck_160_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_val_133_);
lean_dec(v_a_131_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_160_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v___x_137_; 
v___x_137_ = l_Lean_Meta_saveState___redArg(v_a_110_, v_a_112_);
if (lean_obj_tag(v___x_137_) == 0)
{
lean_object* v_a_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_151_; 
v_a_138_ = lean_ctor_get(v___x_137_, 0);
v_isSharedCheck_151_ = !lean_is_exclusive(v___x_137_);
if (v_isSharedCheck_151_ == 0)
{
v___x_140_ = v___x_137_;
v_isShared_141_ = v_isSharedCheck_151_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_a_138_);
lean_dec(v___x_137_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_151_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_143_; 
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 1, v_a_138_);
lean_ctor_set(v___x_127_, 0, v_val_133_);
v___x_143_ = v___x_127_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v_val_133_);
lean_ctor_set(v_reuseFailAlloc_150_, 1, v_a_138_);
v___x_143_ = v_reuseFailAlloc_150_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
lean_object* v___x_145_; 
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 0, v___x_143_);
v___x_145_ = v___x_135_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v___x_143_);
v___x_145_ = v_reuseFailAlloc_149_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
lean_object* v___x_147_; 
if (v_isShared_141_ == 0)
{
lean_ctor_set(v___x_140_, 0, v___x_145_);
v___x_147_ = v___x_140_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v___x_145_);
v___x_147_ = v_reuseFailAlloc_148_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
return v___x_147_;
}
}
}
}
}
else
{
lean_object* v_a_152_; lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_159_; 
lean_del_object(v___x_135_);
lean_dec(v_val_133_);
lean_del_object(v___x_127_);
v_a_152_ = lean_ctor_get(v___x_137_, 0);
v_isSharedCheck_159_ = !lean_is_exclusive(v___x_137_);
if (v_isSharedCheck_159_ == 0)
{
v___x_154_ = v___x_137_;
v_isShared_155_ = v_isSharedCheck_159_;
goto v_resetjp_153_;
}
else
{
lean_inc(v_a_152_);
lean_dec(v___x_137_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_159_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
lean_object* v___x_157_; 
if (v_isShared_155_ == 0)
{
v___x_157_ = v___x_154_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v_a_152_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
return v___x_157_;
}
}
}
}
}
}
else
{
lean_object* v_a_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_168_; 
lean_del_object(v___x_127_);
lean_dec_ref(v_L_108_);
lean_dec_ref(v_f_107_);
v_a_161_ = lean_ctor_get(v___x_130_, 0);
v_isSharedCheck_168_ = !lean_is_exclusive(v___x_130_);
if (v_isSharedCheck_168_ == 0)
{
v___x_163_ = v___x_130_;
v_isShared_164_ = v_isSharedCheck_168_;
goto v_resetjp_162_;
}
else
{
lean_inc(v_a_161_);
lean_dec(v___x_130_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_168_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
lean_object* v___x_166_; 
if (v_isShared_164_ == 0)
{
v___x_166_ = v___x_163_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v_a_161_);
v___x_166_ = v_reuseFailAlloc_167_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
return v___x_166_;
}
}
}
}
else
{
lean_object* v_a_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_176_; 
lean_del_object(v___x_127_);
lean_dec(v_fst_124_);
lean_dec_ref(v_L_108_);
lean_dec_ref(v_f_107_);
v_a_169_ = lean_ctor_get(v___x_129_, 0);
v_isSharedCheck_176_ = !lean_is_exclusive(v___x_129_);
if (v_isSharedCheck_176_ == 0)
{
v___x_171_ = v___x_129_;
v_isShared_172_ = v_isSharedCheck_176_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_a_169_);
lean_dec(v___x_129_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_176_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v___x_174_; 
if (v_isShared_172_ == 0)
{
v___x_174_ = v___x_171_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v_a_169_);
v___x_174_ = v_reuseFailAlloc_175_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
return v___x_174_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_186_; 
lean_dec_ref(v_L_108_);
lean_dec_ref(v_f_107_);
v_a_179_ = lean_ctor_get(v___x_114_, 0);
v_isSharedCheck_186_ = !lean_is_exclusive(v___x_114_);
if (v_isSharedCheck_186_ == 0)
{
v___x_181_ = v___x_114_;
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_a_179_);
lean_dec(v___x_114_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_184_; 
if (v_isShared_182_ == 0)
{
v___x_184_ = v___x_181_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v_a_179_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
return v___x_184_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next___redArg___boxed(lean_object* v_f_187_, lean_object* v_L_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next___redArg(v_f_187_, v_L_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_);
lean_dec(v_a_192_);
lean_dec_ref(v_a_191_);
lean_dec(v_a_190_);
lean_dec_ref(v_a_189_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next(lean_object* v_00_u03b1_195_, lean_object* v_00_u03b2_196_, lean_object* v_f_197_, lean_object* v_L_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next___redArg(v_f_197_, v_L_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next___boxed(lean_object* v_00_u03b1_205_, lean_object* v_00_u03b2_206_, lean_object* v_f_207_, lean_object* v_L_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next(v_00_u03b1_205_, v_00_u03b2_206_, v_f_207_, v_L_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_);
lean_dec(v_a_212_);
lean_dec_ref(v_a_211_);
lean_dec(v_a_210_);
lean_dec_ref(v_a_209_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Iterator_filterMapM___redArg(lean_object* v_f_215_, lean_object* v_L_216_){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next___boxed), 9, 4);
lean_closure_set(v___x_217_, 0, lean_box(0));
lean_closure_set(v___x_217_, 1, lean_box(0));
lean_closure_set(v___x_217_, 2, v_f_215_);
lean_closure_set(v___x_217_, 3, v_L_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Iterator_filterMapM(lean_object* v_00_u03b1_218_, lean_object* v_00_u03b2_219_, lean_object* v_f_220_, lean_object* v_L_221_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next___boxed), 9, 4);
lean_closure_set(v___x_222_, 0, lean_box(0));
lean_closure_set(v___x_222_, 1, lean_box(0));
lean_closure_set(v___x_222_, 2, v_f_220_);
lean_closure_set(v___x_222_, 3, v_L_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Iterator_head_spec__0_spec__0(lean_object* v_msgData_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_){
_start:
{
lean_object* v___x_229_; lean_object* v_env_230_; uint8_t v___x_231_; lean_object* v_env_232_; lean_object* v___x_233_; lean_object* v_toCold_234_; lean_object* v_mctx_235_; lean_object* v_lctx_236_; lean_object* v_options_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_229_ = lean_st_ref_get(v___y_227_);
v_env_230_ = lean_ctor_get(v___x_229_, 0);
lean_inc_ref(v_env_230_);
lean_dec(v___x_229_);
v___x_231_ = 0;
v_env_232_ = l_Lean_Environment_setRecordingDeps(v_env_230_, v___x_231_);
v___x_233_ = lean_st_ref_get(v___y_225_);
v_toCold_234_ = lean_ctor_get(v___y_226_, 0);
v_mctx_235_ = lean_ctor_get(v___x_233_, 0);
lean_inc_ref(v_mctx_235_);
lean_dec(v___x_233_);
v_lctx_236_ = lean_ctor_get(v___y_224_, 2);
v_options_237_ = lean_ctor_get(v_toCold_234_, 2);
lean_inc_ref(v_options_237_);
lean_inc_ref(v_lctx_236_);
v___x_238_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_238_, 0, v_env_232_);
lean_ctor_set(v___x_238_, 1, v_mctx_235_);
lean_ctor_set(v___x_238_, 2, v_lctx_236_);
lean_ctor_set(v___x_238_, 3, v_options_237_);
v___x_239_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
lean_ctor_set(v___x_239_, 1, v_msgData_223_);
v___x_240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Iterator_head_spec__0_spec__0___boxed(lean_object* v_msgData_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Iterator_head_spec__0_spec__0(v_msgData_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_);
lean_dec(v___y_245_);
lean_dec_ref(v___y_244_);
lean_dec(v___y_243_);
lean_dec_ref(v___y_242_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Iterator_head_spec__0___redArg(lean_object* v_msg_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_){
_start:
{
lean_object* v_ref_254_; lean_object* v___x_255_; lean_object* v_a_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_264_; 
v_ref_254_ = lean_ctor_get(v___y_251_, 2);
v___x_255_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Iterator_head_spec__0_spec__0(v_msg_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_);
v_a_256_ = lean_ctor_get(v___x_255_, 0);
v_isSharedCheck_264_ = !lean_is_exclusive(v___x_255_);
if (v_isSharedCheck_264_ == 0)
{
v___x_258_ = v___x_255_;
v_isShared_259_ = v_isSharedCheck_264_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_a_256_);
lean_dec(v___x_255_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_264_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v___x_260_; lean_object* v___x_262_; 
lean_inc(v_ref_254_);
v___x_260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_260_, 0, v_ref_254_);
lean_ctor_set(v___x_260_, 1, v_a_256_);
if (v_isShared_259_ == 0)
{
lean_ctor_set_tag(v___x_258_, 1);
lean_ctor_set(v___x_258_, 0, v___x_260_);
v___x_262_ = v___x_258_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v___x_260_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Iterator_head_spec__0___redArg___boxed(lean_object* v_msg_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_Lean_throwError___at___00Lean_Meta_Iterator_head_spec__0___redArg(v_msg_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_);
lean_dec(v___y_269_);
lean_dec_ref(v___y_268_);
lean_dec(v___y_267_);
lean_dec_ref(v___y_266_);
return v_res_271_;
}
}
static lean_object* _init_l_Lean_Meta_Iterator_head___redArg___closed__1(void){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_273_ = ((lean_object*)(l_Lean_Meta_Iterator_head___redArg___closed__0));
v___x_274_ = l_Lean_stringToMessageData(v___x_273_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Iterator_head___redArg(lean_object* v_L_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_){
_start:
{
lean_object* v___x_281_; 
lean_inc(v_a_279_);
lean_inc_ref(v_a_278_);
lean_inc(v_a_277_);
lean_inc_ref(v_a_276_);
v___x_281_ = lean_apply_5(v_L_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_, lean_box(0));
if (lean_obj_tag(v___x_281_) == 0)
{
lean_object* v_a_282_; 
v_a_282_ = lean_ctor_get(v___x_281_, 0);
lean_inc(v_a_282_);
lean_dec_ref_known(v___x_281_, 1);
if (lean_obj_tag(v_a_282_) == 0)
{
lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_283_ = lean_obj_once(&l_Lean_Meta_Iterator_head___redArg___closed__1, &l_Lean_Meta_Iterator_head___redArg___closed__1_once, _init_l_Lean_Meta_Iterator_head___redArg___closed__1);
v___x_284_ = l_Lean_throwError___at___00Lean_Meta_Iterator_head_spec__0___redArg(v___x_283_, v_a_276_, v_a_277_, v_a_278_, v_a_279_);
return v___x_284_;
}
else
{
lean_object* v_val_285_; lean_object* v_fst_286_; lean_object* v_snd_287_; lean_object* v___x_288_; 
v_val_285_ = lean_ctor_get(v_a_282_, 0);
lean_inc(v_val_285_);
lean_dec_ref_known(v_a_282_, 1);
v_fst_286_ = lean_ctor_get(v_val_285_, 0);
lean_inc(v_fst_286_);
v_snd_287_ = lean_ctor_get(v_val_285_, 1);
lean_inc(v_snd_287_);
lean_dec(v_val_285_);
v___x_288_ = l_Lean_Meta_SavedState_restore___redArg(v_snd_287_, v_a_277_, v_a_279_);
if (lean_obj_tag(v___x_288_) == 0)
{
lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_295_; 
v_isSharedCheck_295_ = !lean_is_exclusive(v___x_288_);
if (v_isSharedCheck_295_ == 0)
{
lean_object* v_unused_296_; 
v_unused_296_ = lean_ctor_get(v___x_288_, 0);
lean_dec(v_unused_296_);
v___x_290_ = v___x_288_;
v_isShared_291_ = v_isSharedCheck_295_;
goto v_resetjp_289_;
}
else
{
lean_dec(v___x_288_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_295_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v___x_293_; 
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 0, v_fst_286_);
v___x_293_ = v___x_290_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v_fst_286_);
v___x_293_ = v_reuseFailAlloc_294_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
return v___x_293_;
}
}
}
else
{
lean_object* v_a_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_304_; 
lean_dec(v_fst_286_);
v_a_297_ = lean_ctor_get(v___x_288_, 0);
v_isSharedCheck_304_ = !lean_is_exclusive(v___x_288_);
if (v_isSharedCheck_304_ == 0)
{
v___x_299_ = v___x_288_;
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_a_297_);
lean_dec(v___x_288_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_302_; 
if (v_isShared_300_ == 0)
{
v___x_302_ = v___x_299_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_a_297_);
v___x_302_ = v_reuseFailAlloc_303_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
return v___x_302_;
}
}
}
}
}
else
{
lean_object* v_a_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_312_; 
v_a_305_ = lean_ctor_get(v___x_281_, 0);
v_isSharedCheck_312_ = !lean_is_exclusive(v___x_281_);
if (v_isSharedCheck_312_ == 0)
{
v___x_307_ = v___x_281_;
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_a_305_);
lean_dec(v___x_281_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_310_; 
if (v_isShared_308_ == 0)
{
v___x_310_ = v___x_307_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v_a_305_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Iterator_head___redArg___boxed(lean_object* v_L_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Lean_Meta_Iterator_head___redArg(v_L_313_, v_a_314_, v_a_315_, v_a_316_, v_a_317_);
lean_dec(v_a_317_);
lean_dec_ref(v_a_316_);
lean_dec(v_a_315_);
lean_dec_ref(v_a_314_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Iterator_head(lean_object* v_00_u03b1_320_, lean_object* v_L_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = l_Lean_Meta_Iterator_head___redArg(v_L_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Iterator_head___boxed(lean_object* v_00_u03b1_328_, lean_object* v_L_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Lean_Meta_Iterator_head(v_00_u03b1_328_, v_L_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
lean_dec(v_a_331_);
lean_dec_ref(v_a_330_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Iterator_head_spec__0(lean_object* v_00_u03b1_336_, lean_object* v_msg_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_){
_start:
{
lean_object* v___x_343_; 
v___x_343_ = l_Lean_throwError___at___00Lean_Meta_Iterator_head_spec__0___redArg(v_msg_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Iterator_head_spec__0___boxed(lean_object* v_00_u03b1_344_, lean_object* v_msg_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_Lean_throwError___at___00Lean_Meta_Iterator_head_spec__0(v_00_u03b1_344_, v_msg_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_);
lean_dec(v___y_349_);
lean_dec_ref(v___y_348_);
lean_dec(v___y_347_);
lean_dec_ref(v___y_346_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Iterator_firstM___redArg(lean_object* v_L_352_, lean_object* v_f_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_359_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next___boxed), 9, 4);
lean_closure_set(v___x_359_, 0, lean_box(0));
lean_closure_set(v___x_359_, 1, lean_box(0));
lean_closure_set(v___x_359_, 2, v_f_353_);
lean_closure_set(v___x_359_, 3, v_L_352_);
v___x_360_ = l_Lean_Meta_Iterator_head___redArg(v___x_359_, v_a_354_, v_a_355_, v_a_356_, v_a_357_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Iterator_firstM___redArg___boxed(lean_object* v_L_361_, lean_object* v_f_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_Lean_Meta_Iterator_firstM___redArg(v_L_361_, v_f_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_);
lean_dec(v_a_366_);
lean_dec_ref(v_a_365_);
lean_dec(v_a_364_);
lean_dec_ref(v_a_363_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Iterator_firstM(lean_object* v_00_u03b1_369_, lean_object* v_00_u03b2_370_, lean_object* v_L_371_, lean_object* v_f_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_){
_start:
{
lean_object* v___x_378_; 
v___x_378_ = l_Lean_Meta_Iterator_firstM___redArg(v_L_371_, v_f_372_, v_a_373_, v_a_374_, v_a_375_, v_a_376_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Iterator_firstM___boxed(lean_object* v_00_u03b1_379_, lean_object* v_00_u03b2_380_, lean_object* v_L_381_, lean_object* v_f_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l_Lean_Meta_Iterator_firstM(v_00_u03b1_379_, v_00_u03b2_380_, v_L_381_, v_f_382_, v_a_383_, v_a_384_, v_a_385_, v_a_386_);
lean_dec(v_a_386_);
lean_dec_ref(v_a_385_);
lean_dec(v_a_384_);
lean_dec_ref(v_a_383_);
return v_res_388_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Iterator(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Iterator(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Iterator(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Iterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Iterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Iterator(builtin);
}
#ifdef __cplusplus
}
#endif

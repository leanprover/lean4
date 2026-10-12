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
lean_object* l_Lean_Meta_Iterator_ofList___redArg___lam__0(lean_object* v_a_1_, lean_object* v_val_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_){
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
LEAN_EXPORT void l_Lean_Meta_Iterator_ofList___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1_ = stack[0].m_obj;
lean_object* v_val_2_ = stack[1].m_obj;
lean_object* v___y_3_ = stack[2].m_obj;
lean_object* v___y_4_ = stack[3].m_obj;
lean_object* v___y_5_ = stack[4].m_obj;
lean_object* v___y_6_ = stack[5].m_obj;
lean_object* v_res_55_;
v_res_55_ = l_Lean_Meta_Iterator_ofList___redArg___lam__0(v_a_1_, v_val_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_);
stack->m_obj
 = v_res_55_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Iterator_ofList___redArg___lam__0___boxed(lean_object* v_a_56_, lean_object* v_val_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l_Lean_Meta_Iterator_ofList___redArg___lam__0(v_a_56_, v_val_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_);
lean_dec(v___y_61_);
lean_dec_ref(v___y_60_);
lean_dec(v___y_59_);
lean_dec_ref(v___y_58_);
lean_dec(v_val_57_);
return v_res_63_;
}
}
lean_object* l_Lean_Meta_Iterator_ofList___redArg(lean_object* v_l_64_, lean_object* v_a_65_, lean_object* v_a_66_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = l_Lean_Meta_saveState___redArg(v_a_65_, v_a_66_);
if (lean_obj_tag(v___x_68_) == 0)
{
lean_object* v_a_69_; lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_78_; 
v_a_69_ = lean_ctor_get(v___x_68_, 0);
v_isSharedCheck_78_ = !lean_is_exclusive(v___x_68_);
if (v_isSharedCheck_78_ == 0)
{
v___x_71_ = v___x_68_;
v_isShared_72_ = v_isSharedCheck_78_;
goto v_resetjp_70_;
}
else
{
lean_inc(v_a_69_);
lean_dec(v___x_68_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_78_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
lean_object* v___x_73_; lean_object* v___f_74_; lean_object* v___x_76_; 
v___x_73_ = lean_st_mk_ref(v_l_64_);
v___f_74_ = lean_alloc_closure((void*)(l_Lean_Meta_Iterator_ofList___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_74_, 0, v_a_69_);
lean_closure_set(v___f_74_, 1, v___x_73_);
if (v_isShared_72_ == 0)
{
lean_ctor_set(v___x_71_, 0, v___f_74_);
v___x_76_ = v___x_71_;
goto v_reusejp_75_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_77_, 0, v___f_74_);
v___x_76_ = v_reuseFailAlloc_77_;
goto v_reusejp_75_;
}
v_reusejp_75_:
{
return v___x_76_;
}
}
}
else
{
lean_object* v_a_79_; lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_86_; 
lean_dec(v_l_64_);
v_a_79_ = lean_ctor_get(v___x_68_, 0);
v_isSharedCheck_86_ = !lean_is_exclusive(v___x_68_);
if (v_isSharedCheck_86_ == 0)
{
v___x_81_ = v___x_68_;
v_isShared_82_ = v_isSharedCheck_86_;
goto v_resetjp_80_;
}
else
{
lean_inc(v_a_79_);
lean_dec(v___x_68_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_86_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
lean_object* v___x_84_; 
if (v_isShared_82_ == 0)
{
v___x_84_ = v___x_81_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v_a_79_);
v___x_84_ = v_reuseFailAlloc_85_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
return v___x_84_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Iterator_ofList___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_l_64_ = stack[0].m_obj;
lean_object* v_a_65_ = stack[1].m_obj;
lean_object* v_a_66_ = stack[2].m_obj;
lean_object* v_res_87_;
v_res_87_ = l_Lean_Meta_Iterator_ofList___redArg(v_l_64_, v_a_65_, v_a_66_);
stack->m_obj
 = v_res_87_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Iterator_ofList___redArg___boxed(lean_object* v_l_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l_Lean_Meta_Iterator_ofList___redArg(v_l_88_, v_a_89_, v_a_90_);
lean_dec(v_a_90_);
lean_dec(v_a_89_);
return v_res_92_;
}
}
lean_object* l_Lean_Meta_Iterator_ofList(lean_object* v_00_u03b1_93_, lean_object* v_l_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = l_Lean_Meta_Iterator_ofList___redArg(v_l_94_, v_a_96_, v_a_98_);
return v___x_100_;
}
}
LEAN_EXPORT void l_Lean_Meta_Iterator_ofList_0interp(lean_interpreter_value* stack)
{
lean_object* v_l_94_ = stack[1].m_obj;
lean_object* v_a_95_ = stack[2].m_obj;
lean_object* v_a_96_ = stack[3].m_obj;
lean_object* v_a_97_ = stack[4].m_obj;
lean_object* v_a_98_ = stack[5].m_obj;
lean_object* v_res_101_;
v_res_101_ = l_Lean_Meta_Iterator_ofList(lean_box(0), v_l_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_);
stack->m_obj
 = v_res_101_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Iterator_ofList___boxed(lean_object* v_00_u03b1_102_, lean_object* v_l_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = l_Lean_Meta_Iterator_ofList(v_00_u03b1_102_, v_l_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_);
lean_dec(v_a_107_);
lean_dec_ref(v_a_106_);
lean_dec(v_a_105_);
lean_dec_ref(v_a_104_);
return v_res_109_;
}
}
lean_object* l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next___redArg(lean_object* v_f_110_, lean_object* v_L_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_){
_start:
{
lean_object* v___x_117_; 
lean_inc_ref(v_L_111_);
lean_inc(v_a_115_);
lean_inc_ref(v_a_114_);
lean_inc(v_a_113_);
lean_inc_ref(v_a_112_);
v___x_117_ = lean_apply_5(v_L_111_, v_a_112_, v_a_113_, v_a_114_, v_a_115_, lean_box(0));
if (lean_obj_tag(v___x_117_) == 0)
{
lean_object* v_a_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_181_; 
v_a_118_ = lean_ctor_get(v___x_117_, 0);
v_isSharedCheck_181_ = !lean_is_exclusive(v___x_117_);
if (v_isSharedCheck_181_ == 0)
{
v___x_120_ = v___x_117_;
v_isShared_121_ = v_isSharedCheck_181_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_a_118_);
lean_dec(v___x_117_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_181_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
if (lean_obj_tag(v_a_118_) == 0)
{
lean_object* v___x_122_; lean_object* v___x_124_; 
lean_dec_ref(v_L_111_);
lean_dec_ref(v_f_110_);
v___x_122_ = lean_box(0);
if (v_isShared_121_ == 0)
{
lean_ctor_set(v___x_120_, 0, v___x_122_);
v___x_124_ = v___x_120_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v___x_122_);
v___x_124_ = v_reuseFailAlloc_125_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
return v___x_124_;
}
}
else
{
lean_object* v_val_126_; lean_object* v_fst_127_; lean_object* v_snd_128_; lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_180_; 
lean_del_object(v___x_120_);
v_val_126_ = lean_ctor_get(v_a_118_, 0);
lean_inc(v_val_126_);
lean_dec_ref_known(v_a_118_, 1);
v_fst_127_ = lean_ctor_get(v_val_126_, 0);
v_snd_128_ = lean_ctor_get(v_val_126_, 1);
v_isSharedCheck_180_ = !lean_is_exclusive(v_val_126_);
if (v_isSharedCheck_180_ == 0)
{
v___x_130_ = v_val_126_;
v_isShared_131_ = v_isSharedCheck_180_;
goto v_resetjp_129_;
}
else
{
lean_inc(v_snd_128_);
lean_inc(v_fst_127_);
lean_dec(v_val_126_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_180_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
lean_object* v___x_132_; 
v___x_132_ = l_Lean_Meta_SavedState_restore___redArg(v_snd_128_, v_a_113_, v_a_115_);
if (lean_obj_tag(v___x_132_) == 0)
{
lean_object* v___x_133_; 
lean_dec_ref_known(v___x_132_, 1);
lean_inc_ref(v_f_110_);
lean_inc(v_a_115_);
lean_inc_ref(v_a_114_);
lean_inc(v_a_113_);
lean_inc_ref(v_a_112_);
v___x_133_ = lean_apply_6(v_f_110_, v_fst_127_, v_a_112_, v_a_113_, v_a_114_, v_a_115_, lean_box(0));
if (lean_obj_tag(v___x_133_) == 0)
{
lean_object* v_a_134_; 
v_a_134_ = lean_ctor_get(v___x_133_, 0);
lean_inc(v_a_134_);
lean_dec_ref_known(v___x_133_, 1);
if (lean_obj_tag(v_a_134_) == 0)
{
lean_del_object(v___x_130_);
goto _start;
}
else
{
lean_object* v_val_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_163_; 
lean_dec_ref(v_L_111_);
lean_dec_ref(v_f_110_);
v_val_136_ = lean_ctor_get(v_a_134_, 0);
v_isSharedCheck_163_ = !lean_is_exclusive(v_a_134_);
if (v_isSharedCheck_163_ == 0)
{
v___x_138_ = v_a_134_;
v_isShared_139_ = v_isSharedCheck_163_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_val_136_);
lean_dec(v_a_134_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_163_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v___x_140_; 
v___x_140_ = l_Lean_Meta_saveState___redArg(v_a_113_, v_a_115_);
if (lean_obj_tag(v___x_140_) == 0)
{
lean_object* v_a_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_154_; 
v_a_141_ = lean_ctor_get(v___x_140_, 0);
v_isSharedCheck_154_ = !lean_is_exclusive(v___x_140_);
if (v_isSharedCheck_154_ == 0)
{
v___x_143_ = v___x_140_;
v_isShared_144_ = v_isSharedCheck_154_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_a_141_);
lean_dec(v___x_140_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_154_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___x_146_; 
if (v_isShared_131_ == 0)
{
lean_ctor_set(v___x_130_, 1, v_a_141_);
lean_ctor_set(v___x_130_, 0, v_val_136_);
v___x_146_ = v___x_130_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v_val_136_);
lean_ctor_set(v_reuseFailAlloc_153_, 1, v_a_141_);
v___x_146_ = v_reuseFailAlloc_153_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
lean_object* v___x_148_; 
if (v_isShared_139_ == 0)
{
lean_ctor_set(v___x_138_, 0, v___x_146_);
v___x_148_ = v___x_138_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v___x_146_);
v___x_148_ = v_reuseFailAlloc_152_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
lean_object* v___x_150_; 
if (v_isShared_144_ == 0)
{
lean_ctor_set(v___x_143_, 0, v___x_148_);
v___x_150_ = v___x_143_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v___x_148_);
v___x_150_ = v_reuseFailAlloc_151_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
return v___x_150_;
}
}
}
}
}
else
{
lean_object* v_a_155_; lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_162_; 
lean_del_object(v___x_138_);
lean_dec(v_val_136_);
lean_del_object(v___x_130_);
v_a_155_ = lean_ctor_get(v___x_140_, 0);
v_isSharedCheck_162_ = !lean_is_exclusive(v___x_140_);
if (v_isSharedCheck_162_ == 0)
{
v___x_157_ = v___x_140_;
v_isShared_158_ = v_isSharedCheck_162_;
goto v_resetjp_156_;
}
else
{
lean_inc(v_a_155_);
lean_dec(v___x_140_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_162_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
lean_object* v___x_160_; 
if (v_isShared_158_ == 0)
{
v___x_160_ = v___x_157_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v_a_155_);
v___x_160_ = v_reuseFailAlloc_161_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
return v___x_160_;
}
}
}
}
}
}
else
{
lean_object* v_a_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_171_; 
lean_del_object(v___x_130_);
lean_dec_ref(v_L_111_);
lean_dec_ref(v_f_110_);
v_a_164_ = lean_ctor_get(v___x_133_, 0);
v_isSharedCheck_171_ = !lean_is_exclusive(v___x_133_);
if (v_isSharedCheck_171_ == 0)
{
v___x_166_ = v___x_133_;
v_isShared_167_ = v_isSharedCheck_171_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_a_164_);
lean_dec(v___x_133_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_171_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v___x_169_; 
if (v_isShared_167_ == 0)
{
v___x_169_ = v___x_166_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v_a_164_);
v___x_169_ = v_reuseFailAlloc_170_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
return v___x_169_;
}
}
}
}
else
{
lean_object* v_a_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_179_; 
lean_del_object(v___x_130_);
lean_dec(v_fst_127_);
lean_dec_ref(v_L_111_);
lean_dec_ref(v_f_110_);
v_a_172_ = lean_ctor_get(v___x_132_, 0);
v_isSharedCheck_179_ = !lean_is_exclusive(v___x_132_);
if (v_isSharedCheck_179_ == 0)
{
v___x_174_ = v___x_132_;
v_isShared_175_ = v_isSharedCheck_179_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_a_172_);
lean_dec(v___x_132_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_179_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
lean_object* v___x_177_; 
if (v_isShared_175_ == 0)
{
v___x_177_ = v___x_174_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v_a_172_);
v___x_177_ = v_reuseFailAlloc_178_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
return v___x_177_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_189_; 
lean_dec_ref(v_L_111_);
lean_dec_ref(v_f_110_);
v_a_182_ = lean_ctor_get(v___x_117_, 0);
v_isSharedCheck_189_ = !lean_is_exclusive(v___x_117_);
if (v_isSharedCheck_189_ == 0)
{
v___x_184_ = v___x_117_;
v_isShared_185_ = v_isSharedCheck_189_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_a_182_);
lean_dec(v___x_117_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_189_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v___x_187_; 
if (v_isShared_185_ == 0)
{
v___x_187_ = v___x_184_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v_a_182_);
v___x_187_ = v_reuseFailAlloc_188_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
return v___x_187_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_110_ = stack[0].m_obj;
lean_object* v_L_111_ = stack[1].m_obj;
lean_object* v_a_112_ = stack[2].m_obj;
lean_object* v_a_113_ = stack[3].m_obj;
lean_object* v_a_114_ = stack[4].m_obj;
lean_object* v_a_115_ = stack[5].m_obj;
lean_object* v_res_190_;
v_res_190_ = l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next___redArg(v_f_110_, v_L_111_, v_a_112_, v_a_113_, v_a_114_, v_a_115_);
stack->m_obj
 = v_res_190_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next___redArg___boxed(lean_object* v_f_191_, lean_object* v_L_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next___redArg(v_f_191_, v_L_192_, v_a_193_, v_a_194_, v_a_195_, v_a_196_);
lean_dec(v_a_196_);
lean_dec_ref(v_a_195_);
lean_dec(v_a_194_);
lean_dec_ref(v_a_193_);
return v_res_198_;
}
}
lean_object* l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next(lean_object* v_00_u03b1_199_, lean_object* v_00_u03b2_200_, lean_object* v_f_201_, lean_object* v_L_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next___redArg(v_f_201_, v_L_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_);
return v___x_208_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_201_ = stack[2].m_obj;
lean_object* v_L_202_ = stack[3].m_obj;
lean_object* v_a_203_ = stack[4].m_obj;
lean_object* v_a_204_ = stack[5].m_obj;
lean_object* v_a_205_ = stack[6].m_obj;
lean_object* v_a_206_ = stack[7].m_obj;
lean_object* v_res_209_;
v_res_209_ = l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next(lean_box(0), lean_box(0), v_f_201_, v_L_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_);
stack->m_obj
 = v_res_209_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next___boxed(lean_object* v_00_u03b1_210_, lean_object* v_00_u03b2_211_, lean_object* v_f_212_, lean_object* v_L_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next(v_00_u03b1_210_, v_00_u03b2_211_, v_f_212_, v_L_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_);
lean_dec(v_a_217_);
lean_dec_ref(v_a_216_);
lean_dec(v_a_215_);
lean_dec_ref(v_a_214_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Iterator_filterMapM___redArg(lean_object* v_f_220_, lean_object* v_L_221_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_Iterator_filterMapM(lean_object* v_00_u03b1_223_, lean_object* v_00_u03b2_224_, lean_object* v_f_225_, lean_object* v_L_226_){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next___boxed), 9, 4);
lean_closure_set(v___x_227_, 0, lean_box(0));
lean_closure_set(v___x_227_, 1, lean_box(0));
lean_closure_set(v___x_227_, 2, v_f_225_);
lean_closure_set(v___x_227_, 3, v_L_226_);
return v___x_227_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Iterator_head_spec__0_spec__0(lean_object* v_msgData_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_){
_start:
{
lean_object* v___x_234_; lean_object* v_env_235_; uint8_t v___x_236_; lean_object* v_env_237_; lean_object* v___x_238_; lean_object* v_toCold_239_; lean_object* v_mctx_240_; lean_object* v_lctx_241_; lean_object* v_options_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_234_ = lean_st_ref_get(v___y_232_);
v_env_235_ = lean_ctor_get(v___x_234_, 0);
lean_inc_ref(v_env_235_);
lean_dec(v___x_234_);
v___x_236_ = 0;
v_env_237_ = l_Lean_Environment_setRecordingDeps(v_env_235_, v___x_236_);
v___x_238_ = lean_st_ref_get(v___y_230_);
v_toCold_239_ = lean_ctor_get(v___y_231_, 0);
v_mctx_240_ = lean_ctor_get(v___x_238_, 0);
lean_inc_ref(v_mctx_240_);
lean_dec(v___x_238_);
v_lctx_241_ = lean_ctor_get(v___y_229_, 2);
v_options_242_ = lean_ctor_get(v_toCold_239_, 2);
lean_inc_ref(v_options_242_);
lean_inc_ref(v_lctx_241_);
v___x_243_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_243_, 0, v_env_237_);
lean_ctor_set(v___x_243_, 1, v_mctx_240_);
lean_ctor_set(v___x_243_, 2, v_lctx_241_);
lean_ctor_set(v___x_243_, 3, v_options_242_);
v___x_244_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_244_, 0, v___x_243_);
lean_ctor_set(v___x_244_, 1, v_msgData_228_);
v___x_245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
return v___x_245_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Iterator_head_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_228_ = stack[0].m_obj;
lean_object* v___y_229_ = stack[1].m_obj;
lean_object* v___y_230_ = stack[2].m_obj;
lean_object* v___y_231_ = stack[3].m_obj;
lean_object* v___y_232_ = stack[4].m_obj;
lean_object* v_res_246_;
v_res_246_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Iterator_head_spec__0_spec__0(v_msgData_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_);
stack->m_obj
 = v_res_246_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Iterator_head_spec__0_spec__0___boxed(lean_object* v_msgData_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Iterator_head_spec__0_spec__0(v_msgData_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_);
lean_dec(v___y_251_);
lean_dec_ref(v___y_250_);
lean_dec(v___y_249_);
lean_dec_ref(v___y_248_);
return v_res_253_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Iterator_head_spec__0___redArg(lean_object* v_msg_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_){
_start:
{
lean_object* v_ref_260_; lean_object* v___x_261_; lean_object* v_a_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_270_; 
v_ref_260_ = lean_ctor_get(v___y_257_, 2);
v___x_261_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Iterator_head_spec__0_spec__0(v_msg_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_);
v_a_262_ = lean_ctor_get(v___x_261_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_261_);
if (v_isSharedCheck_270_ == 0)
{
v___x_264_ = v___x_261_;
v_isShared_265_ = v_isSharedCheck_270_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_a_262_);
lean_dec(v___x_261_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_270_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___x_266_; lean_object* v___x_268_; 
lean_inc(v_ref_260_);
v___x_266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_266_, 0, v_ref_260_);
lean_ctor_set(v___x_266_, 1, v_a_262_);
if (v_isShared_265_ == 0)
{
lean_ctor_set_tag(v___x_264_, 1);
lean_ctor_set(v___x_264_, 0, v___x_266_);
v___x_268_ = v___x_264_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v___x_266_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Iterator_head_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_254_ = stack[0].m_obj;
lean_object* v___y_255_ = stack[1].m_obj;
lean_object* v___y_256_ = stack[2].m_obj;
lean_object* v___y_257_ = stack[3].m_obj;
lean_object* v___y_258_ = stack[4].m_obj;
lean_object* v_res_271_;
v_res_271_ = l_Lean_throwError___at___00Lean_Meta_Iterator_head_spec__0___redArg(v_msg_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_);
stack->m_obj
 = v_res_271_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Iterator_head_spec__0___redArg___boxed(lean_object* v_msg_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_Lean_throwError___at___00Lean_Meta_Iterator_head_spec__0___redArg(v_msg_272_, v___y_273_, v___y_274_, v___y_275_, v___y_276_);
lean_dec(v___y_276_);
lean_dec_ref(v___y_275_);
lean_dec(v___y_274_);
lean_dec_ref(v___y_273_);
return v_res_278_;
}
}
static lean_object* _init_l_Lean_Meta_Iterator_head___redArg___closed__1(void){
_start:
{
lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_280_ = ((lean_object*)(l_Lean_Meta_Iterator_head___redArg___closed__0));
v___x_281_ = l_Lean_stringToMessageData(v___x_280_);
return v___x_281_;
}
}
lean_object* l_Lean_Meta_Iterator_head___redArg(lean_object* v_L_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_){
_start:
{
lean_object* v___x_288_; 
lean_inc(v_a_286_);
lean_inc_ref(v_a_285_);
lean_inc(v_a_284_);
lean_inc_ref(v_a_283_);
v___x_288_ = lean_apply_5(v_L_282_, v_a_283_, v_a_284_, v_a_285_, v_a_286_, lean_box(0));
if (lean_obj_tag(v___x_288_) == 0)
{
lean_object* v_a_289_; 
v_a_289_ = lean_ctor_get(v___x_288_, 0);
lean_inc(v_a_289_);
lean_dec_ref_known(v___x_288_, 1);
if (lean_obj_tag(v_a_289_) == 0)
{
lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_290_ = lean_obj_once(&l_Lean_Meta_Iterator_head___redArg___closed__1, &l_Lean_Meta_Iterator_head___redArg___closed__1_once, _init_l_Lean_Meta_Iterator_head___redArg___closed__1);
v___x_291_ = l_Lean_throwError___at___00Lean_Meta_Iterator_head_spec__0___redArg(v___x_290_, v_a_283_, v_a_284_, v_a_285_, v_a_286_);
return v___x_291_;
}
else
{
lean_object* v_val_292_; lean_object* v_fst_293_; lean_object* v_snd_294_; lean_object* v___x_295_; 
v_val_292_ = lean_ctor_get(v_a_289_, 0);
lean_inc(v_val_292_);
lean_dec_ref_known(v_a_289_, 1);
v_fst_293_ = lean_ctor_get(v_val_292_, 0);
lean_inc(v_fst_293_);
v_snd_294_ = lean_ctor_get(v_val_292_, 1);
lean_inc(v_snd_294_);
lean_dec(v_val_292_);
v___x_295_ = l_Lean_Meta_SavedState_restore___redArg(v_snd_294_, v_a_284_, v_a_286_);
if (lean_obj_tag(v___x_295_) == 0)
{
lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_302_; 
v_isSharedCheck_302_ = !lean_is_exclusive(v___x_295_);
if (v_isSharedCheck_302_ == 0)
{
lean_object* v_unused_303_; 
v_unused_303_ = lean_ctor_get(v___x_295_, 0);
lean_dec(v_unused_303_);
v___x_297_ = v___x_295_;
v_isShared_298_ = v_isSharedCheck_302_;
goto v_resetjp_296_;
}
else
{
lean_dec(v___x_295_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_302_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___x_300_; 
if (v_isShared_298_ == 0)
{
lean_ctor_set(v___x_297_, 0, v_fst_293_);
v___x_300_ = v___x_297_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v_fst_293_);
v___x_300_ = v_reuseFailAlloc_301_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
return v___x_300_;
}
}
}
else
{
lean_object* v_a_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_311_; 
lean_dec(v_fst_293_);
v_a_304_ = lean_ctor_get(v___x_295_, 0);
v_isSharedCheck_311_ = !lean_is_exclusive(v___x_295_);
if (v_isSharedCheck_311_ == 0)
{
v___x_306_ = v___x_295_;
v_isShared_307_ = v_isSharedCheck_311_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_a_304_);
lean_dec(v___x_295_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_311_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v___x_309_; 
if (v_isShared_307_ == 0)
{
v___x_309_ = v___x_306_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v_a_304_);
v___x_309_ = v_reuseFailAlloc_310_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
return v___x_309_;
}
}
}
}
}
else
{
lean_object* v_a_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_319_; 
v_a_312_ = lean_ctor_get(v___x_288_, 0);
v_isSharedCheck_319_ = !lean_is_exclusive(v___x_288_);
if (v_isSharedCheck_319_ == 0)
{
v___x_314_ = v___x_288_;
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_a_312_);
lean_dec(v___x_288_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_317_; 
if (v_isShared_315_ == 0)
{
v___x_317_ = v___x_314_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_a_312_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Iterator_head___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_L_282_ = stack[0].m_obj;
lean_object* v_a_283_ = stack[1].m_obj;
lean_object* v_a_284_ = stack[2].m_obj;
lean_object* v_a_285_ = stack[3].m_obj;
lean_object* v_a_286_ = stack[4].m_obj;
lean_object* v_res_320_;
v_res_320_ = l_Lean_Meta_Iterator_head___redArg(v_L_282_, v_a_283_, v_a_284_, v_a_285_, v_a_286_);
stack->m_obj
 = v_res_320_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Iterator_head___redArg___boxed(lean_object* v_L_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_Lean_Meta_Iterator_head___redArg(v_L_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_);
lean_dec(v_a_325_);
lean_dec_ref(v_a_324_);
lean_dec(v_a_323_);
lean_dec_ref(v_a_322_);
return v_res_327_;
}
}
lean_object* l_Lean_Meta_Iterator_head(lean_object* v_00_u03b1_328_, lean_object* v_L_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = l_Lean_Meta_Iterator_head___redArg(v_L_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_);
return v___x_335_;
}
}
LEAN_EXPORT void l_Lean_Meta_Iterator_head_0interp(lean_interpreter_value* stack)
{
lean_object* v_L_329_ = stack[1].m_obj;
lean_object* v_a_330_ = stack[2].m_obj;
lean_object* v_a_331_ = stack[3].m_obj;
lean_object* v_a_332_ = stack[4].m_obj;
lean_object* v_a_333_ = stack[5].m_obj;
lean_object* v_res_336_;
v_res_336_ = l_Lean_Meta_Iterator_head(lean_box(0), v_L_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_);
stack->m_obj
 = v_res_336_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Iterator_head___boxed(lean_object* v_00_u03b1_337_, lean_object* v_L_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l_Lean_Meta_Iterator_head(v_00_u03b1_337_, v_L_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_);
lean_dec(v_a_342_);
lean_dec_ref(v_a_341_);
lean_dec(v_a_340_);
lean_dec_ref(v_a_339_);
return v_res_344_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Iterator_head_spec__0(lean_object* v_00_u03b1_345_, lean_object* v_msg_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = l_Lean_throwError___at___00Lean_Meta_Iterator_head_spec__0___redArg(v_msg_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_);
return v___x_352_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Iterator_head_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_346_ = stack[1].m_obj;
lean_object* v___y_347_ = stack[2].m_obj;
lean_object* v___y_348_ = stack[3].m_obj;
lean_object* v___y_349_ = stack[4].m_obj;
lean_object* v___y_350_ = stack[5].m_obj;
lean_object* v_res_353_;
v_res_353_ = l_Lean_throwError___at___00Lean_Meta_Iterator_head_spec__0(lean_box(0), v_msg_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_);
stack->m_obj
 = v_res_353_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Iterator_head_spec__0___boxed(lean_object* v_00_u03b1_354_, lean_object* v_msg_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Lean_throwError___at___00Lean_Meta_Iterator_head_spec__0(v_00_u03b1_354_, v_msg_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_);
lean_dec(v___y_359_);
lean_dec_ref(v___y_358_);
lean_dec(v___y_357_);
lean_dec_ref(v___y_356_);
return v_res_361_;
}
}
lean_object* l_Lean_Meta_Iterator_firstM___redArg(lean_object* v_L_362_, lean_object* v_f_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_369_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next___boxed), 9, 4);
lean_closure_set(v___x_369_, 0, lean_box(0));
lean_closure_set(v___x_369_, 1, lean_box(0));
lean_closure_set(v___x_369_, 2, v_f_363_);
lean_closure_set(v___x_369_, 3, v_L_362_);
v___x_370_ = l_Lean_Meta_Iterator_head___redArg(v___x_369_, v_a_364_, v_a_365_, v_a_366_, v_a_367_);
return v___x_370_;
}
}
LEAN_EXPORT void l_Lean_Meta_Iterator_firstM___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_L_362_ = stack[0].m_obj;
lean_object* v_f_363_ = stack[1].m_obj;
lean_object* v_a_364_ = stack[2].m_obj;
lean_object* v_a_365_ = stack[3].m_obj;
lean_object* v_a_366_ = stack[4].m_obj;
lean_object* v_a_367_ = stack[5].m_obj;
lean_object* v_res_371_;
v_res_371_ = l_Lean_Meta_Iterator_firstM___redArg(v_L_362_, v_f_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_);
stack->m_obj
 = v_res_371_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Iterator_firstM___redArg___boxed(lean_object* v_L_372_, lean_object* v_f_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Lean_Meta_Iterator_firstM___redArg(v_L_372_, v_f_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_);
lean_dec(v_a_377_);
lean_dec_ref(v_a_376_);
lean_dec(v_a_375_);
lean_dec_ref(v_a_374_);
return v_res_379_;
}
}
lean_object* l_Lean_Meta_Iterator_firstM(lean_object* v_00_u03b1_380_, lean_object* v_00_u03b2_381_, lean_object* v_L_382_, lean_object* v_f_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = l_Lean_Meta_Iterator_firstM___redArg(v_L_382_, v_f_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_);
return v___x_389_;
}
}
LEAN_EXPORT void l_Lean_Meta_Iterator_firstM_0interp(lean_interpreter_value* stack)
{
lean_object* v_L_382_ = stack[2].m_obj;
lean_object* v_f_383_ = stack[3].m_obj;
lean_object* v_a_384_ = stack[4].m_obj;
lean_object* v_a_385_ = stack[5].m_obj;
lean_object* v_a_386_ = stack[6].m_obj;
lean_object* v_a_387_ = stack[7].m_obj;
lean_object* v_res_390_;
v_res_390_ = l_Lean_Meta_Iterator_firstM(lean_box(0), lean_box(0), v_L_382_, v_f_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_);
stack->m_obj
 = v_res_390_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Iterator_firstM___boxed(lean_object* v_00_u03b1_391_, lean_object* v_00_u03b2_392_, lean_object* v_L_393_, lean_object* v_f_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_Lean_Meta_Iterator_firstM(v_00_u03b1_391_, v_00_u03b2_392_, v_L_393_, v_f_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_);
lean_dec(v_a_398_);
lean_dec_ref(v_a_397_);
lean_dec(v_a_396_);
lean_dec_ref(v_a_395_);
return v_res_400_;
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

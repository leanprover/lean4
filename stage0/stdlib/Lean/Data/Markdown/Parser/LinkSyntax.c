// Lean compiler output
// Module: Lean.Data.Markdown.Parser.LinkSyntax
// Imports: public import Init.While public import Lean.Data.Markdown.Inline public import Lean.Data.Markdown.InlineCursor import Lean.Data.Markdown.Text
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
uint8_t l_Lean_Markdown_InlineCursor_isEmpty___redArg(lean_object*);
uint32_t l_Lean_Markdown_InlineCursor_front(lean_object*, lean_object*);
lean_object* l_Lean_Markdown_InlineCursor_drop1(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_uint32_to_nat(uint32_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Markdown_InlineCursor_front_x3f(lean_object*, lean_object*);
uint8_t l_Lean_Markdown_isAsciiPunctuation(uint32_t);
lean_object* l_Lean_Markdown_InlineCursor_charSubslice_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Markdown_InlineSource_linesBetween(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Markdown_subsliceClamped___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Markdown_parseLinkDestination_x3f_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Markdown_parseLinkDestination_x3f_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseLinkDestination_x3f_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseLinkDestination_x3f_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseLinkDestination_x3f_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseLinkDestination_x3f_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_parseLinkDestination_x3f___closed__0___boxed__const__1;
static lean_once_cell_t l_Lean_Markdown_parseLinkDestination_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Markdown_parseLinkDestination_x3f___closed__0;
LEAN_EXPORT lean_object* l_Lean_Markdown_parseLinkDestination_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_parseLinkDestination_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseLinkDestination_x3f_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseLinkDestination_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseLinkDestination_x3f_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseLinkDestination_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseLinkTitle_x3f_spec__0___redArg(lean_object*, uint32_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseLinkTitle_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_parseLinkTitle_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_parseLinkTitle_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseLinkTitle_x3f_spec__0(lean_object*, uint32_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseLinkTitle_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Markdown_parseLinkDestination_x3f_spec__0(lean_object* v_x_1_, lean_object* v_x_2_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
if (lean_obj_tag(v_x_2_) == 0)
{
uint8_t v___x_3_; 
v___x_3_ = 1;
return v___x_3_;
}
else
{
uint8_t v___x_4_; 
v___x_4_ = 0;
return v___x_4_;
}
}
else
{
if (lean_obj_tag(v_x_2_) == 0)
{
uint8_t v___x_5_; 
v___x_5_ = 0;
return v___x_5_;
}
else
{
lean_object* v_val_6_; lean_object* v_val_7_; uint32_t v___x_8_; uint32_t v___x_9_; uint8_t v___x_10_; 
v_val_6_ = lean_ctor_get(v_x_1_, 0);
v_val_7_ = lean_ctor_get(v_x_2_, 0);
v___x_8_ = lean_unbox_uint32(v_val_6_);
v___x_9_ = lean_unbox_uint32(v_val_7_);
v___x_10_ = lean_uint32_dec_eq(v___x_8_, v___x_9_);
return v___x_10_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Markdown_parseLinkDestination_x3f_spec__0___boxed(lean_object* v_x_11_, lean_object* v_x_12_){
_start:
{
uint8_t v_res_13_; lean_object* v_r_14_; 
v_res_13_ = l_instBEqOption_beq___at___00Lean_Markdown_parseLinkDestination_x3f_spec__0(v_x_11_, v_x_12_);
lean_dec(v_x_12_);
lean_dec(v_x_11_);
v_r_14_ = lean_box(v_res_13_);
return v_r_14_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseLinkDestination_x3f_spec__1___redArg(lean_object* v_s_15_, lean_object* v_a_16_){
_start:
{
lean_object* v_fst_17_; lean_object* v_snd_18_; lean_object* v___x_20_; uint8_t v_isShared_21_; uint8_t v_isSharedCheck_75_; 
v_fst_17_ = lean_ctor_get(v_a_16_, 0);
v_snd_18_ = lean_ctor_get(v_a_16_, 1);
v_isSharedCheck_75_ = !lean_is_exclusive(v_a_16_);
if (v_isSharedCheck_75_ == 0)
{
v___x_20_ = v_a_16_;
v_isShared_21_ = v_isSharedCheck_75_;
goto v_resetjp_19_;
}
else
{
lean_inc(v_snd_18_);
lean_inc(v_fst_17_);
lean_dec(v_a_16_);
v___x_20_ = lean_box(0);
v_isShared_21_ = v_isSharedCheck_75_;
goto v_resetjp_19_;
}
v_resetjp_19_:
{
uint8_t v___x_27_; 
v___x_27_ = l_Lean_Markdown_InlineCursor_isEmpty___redArg(v_fst_17_);
if (v___x_27_ == 0)
{
lean_object* v_parenDepth_28_; uint32_t v___x_29_; lean_object* v___x_30_; uint32_t v___x_64_; uint8_t v___x_65_; 
v_parenDepth_28_ = lean_unsigned_to_nat(0u);
v___x_29_ = l_Lean_Markdown_InlineCursor_front(v_s_15_, v_fst_17_);
lean_inc(v_fst_17_);
v___x_30_ = l_Lean_Markdown_InlineCursor_drop1(v_s_15_, v_fst_17_);
v___x_64_ = 92;
v___x_65_ = lean_uint32_dec_eq(v___x_29_, v___x_64_);
if (v___x_65_ == 0)
{
goto v___jp_31_;
}
else
{
lean_object* v___x_66_; 
v___x_66_ = l_Lean_Markdown_InlineCursor_front_x3f(v_s_15_, v___x_30_);
if (lean_obj_tag(v___x_66_) == 0)
{
goto v___jp_31_;
}
else
{
lean_object* v_val_67_; uint32_t v___x_68_; uint8_t v___x_69_; 
v_val_67_ = lean_ctor_get(v___x_66_, 0);
lean_inc(v_val_67_);
lean_dec_ref_known(v___x_66_, 1);
v___x_68_ = lean_unbox_uint32(v_val_67_);
lean_dec(v_val_67_);
v___x_69_ = l_Lean_Markdown_isAsciiPunctuation(v___x_68_);
if (v___x_69_ == 0)
{
goto v___jp_31_;
}
else
{
lean_object* v___x_70_; lean_object* v___x_71_; 
lean_del_object(v___x_20_);
lean_dec(v_fst_17_);
v___x_70_ = l_Lean_Markdown_InlineCursor_drop1(v_s_15_, v___x_30_);
v___x_71_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
lean_ctor_set(v___x_71_, 1, v_snd_18_);
v_a_16_ = v___x_71_;
goto _start;
}
}
}
v___jp_31_:
{
uint32_t v___x_32_; uint8_t v___x_33_; 
v___x_32_ = 32;
v___x_33_ = lean_uint32_dec_eq(v___x_29_, v___x_32_);
if (v___x_33_ == 0)
{
uint32_t v___x_34_; uint8_t v___x_35_; 
v___x_34_ = 9;
v___x_35_ = lean_uint32_dec_eq(v___x_29_, v___x_34_);
if (v___x_35_ == 0)
{
uint32_t v___x_36_; uint8_t v___x_37_; 
v___x_36_ = 13;
v___x_37_ = lean_uint32_dec_eq(v___x_29_, v___x_36_);
if (v___x_37_ == 0)
{
uint32_t v___x_38_; uint8_t v___x_39_; 
v___x_38_ = 10;
v___x_39_ = lean_uint32_dec_eq(v___x_29_, v___x_38_);
if (v___x_39_ == 0)
{
lean_object* v___x_40_; lean_object* v___x_41_; uint8_t v___x_42_; 
v___x_40_ = lean_unsigned_to_nat(32u);
v___x_41_ = lean_uint32_to_nat(v___x_29_);
v___x_42_ = lean_nat_dec_lt(v___x_41_, v___x_40_);
if (v___x_42_ == 0)
{
lean_object* v___x_43_; uint8_t v___x_44_; 
v___x_43_ = lean_unsigned_to_nat(127u);
v___x_44_ = lean_nat_dec_eq(v___x_41_, v___x_43_);
lean_dec(v___x_41_);
if (v___x_44_ == 0)
{
uint32_t v___x_45_; uint8_t v___x_46_; 
lean_del_object(v___x_20_);
v___x_45_ = 40;
v___x_46_ = lean_uint32_dec_eq(v___x_29_, v___x_45_);
if (v___x_46_ == 0)
{
uint32_t v___x_47_; uint8_t v___x_48_; 
v___x_47_ = 41;
v___x_48_ = lean_uint32_dec_eq(v___x_29_, v___x_47_);
if (v___x_48_ == 0)
{
lean_object* v___x_49_; 
lean_dec(v_fst_17_);
v___x_49_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_49_, 0, v___x_30_);
lean_ctor_set(v___x_49_, 1, v_snd_18_);
v_a_16_ = v___x_49_;
goto _start;
}
else
{
uint8_t v___x_51_; 
v___x_51_ = lean_nat_dec_eq(v_snd_18_, v_parenDepth_28_);
if (v___x_51_ == 0)
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
lean_dec(v_fst_17_);
v___x_52_ = lean_unsigned_to_nat(1u);
v___x_53_ = lean_nat_sub(v_snd_18_, v___x_52_);
lean_dec(v_snd_18_);
v___x_54_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_54_, 0, v___x_30_);
lean_ctor_set(v___x_54_, 1, v___x_53_);
v_a_16_ = v___x_54_;
goto _start;
}
else
{
lean_object* v___x_56_; lean_object* v___x_57_; 
lean_dec_ref(v___x_30_);
v___x_56_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_56_, 0, v_fst_17_);
lean_ctor_set(v___x_56_, 1, v_snd_18_);
v___x_57_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_57_, 0, v___x_56_);
return v___x_57_;
}
}
}
else
{
lean_object* v___x_58_; lean_object* v___x_59_; uint8_t v___x_60_; 
lean_dec(v_fst_17_);
v___x_58_ = lean_unsigned_to_nat(1u);
v___x_59_ = lean_nat_add(v_snd_18_, v___x_58_);
lean_dec(v_snd_18_);
v___x_60_ = lean_nat_dec_lt(v___x_40_, v___x_59_);
if (v___x_60_ == 0)
{
lean_object* v___x_61_; 
v___x_61_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_61_, 0, v___x_30_);
lean_ctor_set(v___x_61_, 1, v___x_59_);
v_a_16_ = v___x_61_;
goto _start;
}
else
{
lean_object* v___x_63_; 
lean_dec(v___x_59_);
lean_dec_ref(v___x_30_);
v___x_63_ = lean_box(0);
return v___x_63_;
}
}
}
else
{
lean_dec_ref(v___x_30_);
goto v___jp_22_;
}
}
else
{
lean_dec(v___x_41_);
lean_dec_ref(v___x_30_);
goto v___jp_22_;
}
}
else
{
lean_dec_ref(v___x_30_);
goto v___jp_22_;
}
}
else
{
lean_dec_ref(v___x_30_);
goto v___jp_22_;
}
}
else
{
lean_dec_ref(v___x_30_);
goto v___jp_22_;
}
}
else
{
lean_dec_ref(v___x_30_);
goto v___jp_22_;
}
}
}
else
{
lean_object* v___x_73_; lean_object* v___x_74_; 
lean_del_object(v___x_20_);
v___x_73_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_73_, 0, v_fst_17_);
lean_ctor_set(v___x_73_, 1, v_snd_18_);
v___x_74_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_74_, 0, v___x_73_);
return v___x_74_;
}
v___jp_22_:
{
lean_object* v___x_24_; 
if (v_isShared_21_ == 0)
{
v___x_24_ = v___x_20_;
goto v_reusejp_23_;
}
else
{
lean_object* v_reuseFailAlloc_26_; 
v_reuseFailAlloc_26_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_26_, 0, v_fst_17_);
lean_ctor_set(v_reuseFailAlloc_26_, 1, v_snd_18_);
v___x_24_ = v_reuseFailAlloc_26_;
goto v_reusejp_23_;
}
v_reusejp_23_:
{
lean_object* v___x_25_; 
v___x_25_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_25_, 0, v___x_24_);
return v___x_25_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseLinkDestination_x3f_spec__1___redArg___boxed(lean_object* v_s_76_, lean_object* v_a_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseLinkDestination_x3f_spec__1___redArg(v_s_76_, v_a_77_);
lean_dec_ref(v_s_76_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseLinkDestination_x3f_spec__2___redArg(lean_object* v_s_79_, lean_object* v_val_80_, lean_object* v___x_81_, lean_object* v_a_82_){
_start:
{
lean_object* v_snd_83_; lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_136_; 
v_snd_83_ = lean_ctor_get(v_a_82_, 1);
v_isSharedCheck_136_ = !lean_is_exclusive(v_a_82_);
if (v_isSharedCheck_136_ == 0)
{
lean_object* v_unused_137_; 
v_unused_137_ = lean_ctor_get(v_a_82_, 0);
lean_dec(v_unused_137_);
v___x_85_ = v_a_82_;
v_isShared_86_ = v_isSharedCheck_136_;
goto v_resetjp_84_;
}
else
{
lean_inc(v_snd_83_);
lean_dec(v_a_82_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_136_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
lean_object* v___x_87_; uint8_t v___x_88_; 
v___x_87_ = lean_box(0);
v___x_88_ = l_Lean_Markdown_InlineCursor_isEmpty___redArg(v_snd_83_);
if (v___x_88_ == 0)
{
uint32_t v___x_89_; uint32_t v___x_90_; lean_object* v___x_91_; uint32_t v___x_123_; uint8_t v___x_124_; 
v___x_89_ = 60;
v___x_90_ = l_Lean_Markdown_InlineCursor_front(v_s_79_, v_snd_83_);
lean_inc(v_snd_83_);
v___x_91_ = l_Lean_Markdown_InlineCursor_drop1(v_s_79_, v_snd_83_);
v___x_123_ = 92;
v___x_124_ = lean_uint32_dec_eq(v___x_90_, v___x_123_);
if (v___x_124_ == 0)
{
goto v___jp_92_;
}
else
{
lean_object* v___x_125_; 
v___x_125_ = l_Lean_Markdown_InlineCursor_front_x3f(v_s_79_, v___x_91_);
if (lean_obj_tag(v___x_125_) == 0)
{
goto v___jp_92_;
}
else
{
lean_object* v_val_126_; uint32_t v___x_127_; uint8_t v___x_128_; 
v_val_126_ = lean_ctor_get(v___x_125_, 0);
lean_inc(v_val_126_);
lean_dec_ref_known(v___x_125_, 1);
v___x_127_ = lean_unbox_uint32(v_val_126_);
lean_dec(v_val_126_);
v___x_128_ = l_Lean_Markdown_isAsciiPunctuation(v___x_127_);
if (v___x_128_ == 0)
{
goto v___jp_92_;
}
else
{
lean_object* v___x_129_; lean_object* v___x_130_; 
lean_del_object(v___x_85_);
lean_dec(v_snd_83_);
v___x_129_ = l_Lean_Markdown_InlineCursor_drop1(v_s_79_, v___x_91_);
v___x_130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_130_, 0, v___x_87_);
lean_ctor_set(v___x_130_, 1, v___x_129_);
v_a_82_ = v___x_130_;
goto _start;
}
}
}
v___jp_92_:
{
uint32_t v___x_93_; uint8_t v___x_94_; 
v___x_93_ = 62;
v___x_94_ = lean_uint32_dec_eq(v___x_90_, v___x_93_);
if (v___x_94_ == 0)
{
uint8_t v___x_95_; 
lean_dec(v_snd_83_);
v___x_95_ = lean_uint32_dec_eq(v___x_90_, v___x_89_);
if (v___x_95_ == 0)
{
uint32_t v___x_96_; uint8_t v___x_97_; 
v___x_96_ = 10;
v___x_97_ = lean_uint32_dec_eq(v___x_90_, v___x_96_);
if (v___x_97_ == 0)
{
uint32_t v___x_98_; uint8_t v___x_99_; 
v___x_98_ = 13;
v___x_99_ = lean_uint32_dec_eq(v___x_90_, v___x_98_);
if (v___x_99_ == 0)
{
lean_object* v___x_101_; 
if (v_isShared_86_ == 0)
{
lean_ctor_set(v___x_85_, 1, v___x_91_);
lean_ctor_set(v___x_85_, 0, v___x_87_);
v___x_101_ = v___x_85_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v___x_87_);
lean_ctor_set(v_reuseFailAlloc_103_, 1, v___x_91_);
v___x_101_ = v_reuseFailAlloc_103_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
v_a_82_ = v___x_101_;
goto _start;
}
}
else
{
lean_dec_ref(v___x_91_);
lean_del_object(v___x_85_);
lean_dec(v___x_81_);
lean_dec_ref(v_val_80_);
return v___x_87_;
}
}
else
{
lean_dec_ref(v___x_91_);
lean_del_object(v___x_85_);
lean_dec(v___x_81_);
lean_dec_ref(v_val_80_);
return v___x_87_;
}
}
else
{
lean_dec_ref(v___x_91_);
lean_del_object(v___x_85_);
lean_dec(v___x_81_);
lean_dec_ref(v_val_80_);
return v___x_87_;
}
}
else
{
lean_object* v___x_104_; 
v___x_104_ = l_Lean_Markdown_InlineCursor_charSubslice_x3f(v_s_79_, v_snd_83_);
if (lean_obj_tag(v___x_104_) == 0)
{
lean_dec_ref(v___x_91_);
lean_del_object(v___x_85_);
lean_dec(v_snd_83_);
lean_dec(v___x_81_);
lean_dec_ref(v_val_80_);
return v___x_87_;
}
else
{
lean_object* v_val_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_122_; 
v_val_105_ = lean_ctor_get(v___x_104_, 0);
v_isSharedCheck_122_ = !lean_is_exclusive(v___x_104_);
if (v_isSharedCheck_122_ == 0)
{
v___x_107_ = v___x_104_;
v_isShared_108_ = v_isSharedCheck_122_;
goto v_resetjp_106_;
}
else
{
lean_inc(v_val_105_);
lean_dec(v___x_104_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_122_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v_startPos_109_; lean_object* v___x_111_; 
v_startPos_109_ = lean_ctor_get(v_snd_83_, 2);
if (v_isShared_86_ == 0)
{
lean_ctor_set(v___x_85_, 1, v_val_105_);
lean_ctor_set(v___x_85_, 0, v_val_80_);
v___x_111_ = v___x_85_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v_val_80_);
lean_ctor_set(v_reuseFailAlloc_121_, 1, v_val_105_);
v___x_111_ = v_reuseFailAlloc_121_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
lean_object* v___x_113_; 
if (v_isShared_108_ == 0)
{
lean_ctor_set(v___x_107_, 0, v___x_111_);
v___x_113_ = v___x_107_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v___x_111_);
v___x_113_ = v_reuseFailAlloc_120_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
lean_inc(v_startPos_109_);
v___x_114_ = l_Lean_Markdown_subsliceClamped___redArg(v___x_81_, v_startPos_109_);
v___x_115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_115_, 0, v___x_113_);
lean_ctor_set(v___x_115_, 1, v___x_114_);
v___x_116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_116_, 0, v___x_115_);
lean_ctor_set(v___x_116_, 1, v___x_91_);
v___x_117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_117_, 0, v___x_116_);
v___x_118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_118_, 0, v___x_117_);
lean_ctor_set(v___x_118_, 1, v_snd_83_);
v___x_119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_119_, 0, v___x_118_);
return v___x_119_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_133_; 
lean_dec(v___x_81_);
lean_dec_ref(v_val_80_);
if (v_isShared_86_ == 0)
{
lean_ctor_set(v___x_85_, 0, v___x_87_);
v___x_133_ = v___x_85_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v___x_87_);
lean_ctor_set(v_reuseFailAlloc_135_, 1, v_snd_83_);
v___x_133_ = v_reuseFailAlloc_135_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
lean_object* v___x_134_; 
v___x_134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_134_, 0, v___x_133_);
return v___x_134_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseLinkDestination_x3f_spec__2___redArg___boxed(lean_object* v_s_138_, lean_object* v_val_139_, lean_object* v___x_140_, lean_object* v_a_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseLinkDestination_x3f_spec__2___redArg(v_s_138_, v_val_139_, v___x_140_, v_a_141_);
lean_dec_ref(v_s_138_);
return v_res_142_;
}
}
static lean_object* _init_l_Lean_Markdown_parseLinkDestination_x3f___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_143_; lean_object* v___x_144_; 
v___x_143_ = 60;
v___x_144_ = lean_box_uint32(v___x_143_);
return v___x_144_;
}
}
static lean_object* _init_l_Lean_Markdown_parseLinkDestination_x3f___closed__0(void){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_145_ = l_Lean_Markdown_parseLinkDestination_x3f___closed__0___boxed__const__1;
v___x_146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_146_, 0, v___x_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_parseLinkDestination_x3f(lean_object* v_s_147_, lean_object* v_cur_148_){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; uint8_t v___x_151_; 
v___x_149_ = l_Lean_Markdown_InlineCursor_front_x3f(v_s_147_, v_cur_148_);
v___x_150_ = lean_obj_once(&l_Lean_Markdown_parseLinkDestination_x3f___closed__0, &l_Lean_Markdown_parseLinkDestination_x3f___closed__0_once, _init_l_Lean_Markdown_parseLinkDestination_x3f___closed__0);
v___x_151_ = l_instBEqOption_beq___at___00Lean_Markdown_parseLinkDestination_x3f_spec__0(v___x_149_, v___x_150_);
lean_dec(v___x_149_);
if (v___x_151_ == 0)
{
lean_object* v_startPos_152_; lean_object* v_parenDepth_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v_startPos_152_ = lean_ctor_get(v_cur_148_, 2);
lean_inc(v_startPos_152_);
v_parenDepth_153_ = lean_unsigned_to_nat(0u);
v___x_154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_154_, 0, v_cur_148_);
lean_ctor_set(v___x_154_, 1, v_parenDepth_153_);
v___x_155_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseLinkDestination_x3f_spec__1___redArg(v_s_147_, v___x_154_);
if (lean_obj_tag(v___x_155_) == 0)
{
lean_object* v___x_156_; 
lean_dec(v_startPos_152_);
v___x_156_ = lean_box(0);
return v___x_156_;
}
else
{
lean_object* v_val_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_179_; 
v_val_157_ = lean_ctor_get(v___x_155_, 0);
v_isSharedCheck_179_ = !lean_is_exclusive(v___x_155_);
if (v_isSharedCheck_179_ == 0)
{
v___x_159_ = v___x_155_;
v_isShared_160_ = v_isSharedCheck_179_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_val_157_);
lean_dec(v___x_155_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_179_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
lean_object* v_fst_161_; lean_object* v_snd_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_178_; 
v_fst_161_ = lean_ctor_get(v_val_157_, 0);
v_snd_162_ = lean_ctor_get(v_val_157_, 1);
v_isSharedCheck_178_ = !lean_is_exclusive(v_val_157_);
if (v_isSharedCheck_178_ == 0)
{
v___x_164_ = v_val_157_;
v_isShared_165_ = v_isSharedCheck_178_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_snd_162_);
lean_inc(v_fst_161_);
lean_dec(v_val_157_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_178_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
uint8_t v___x_166_; 
v___x_166_ = lean_nat_dec_eq(v_snd_162_, v_parenDepth_153_);
lean_dec(v_snd_162_);
if (v___x_166_ == 0)
{
lean_object* v___x_167_; 
lean_del_object(v___x_164_);
lean_dec(v_fst_161_);
lean_del_object(v___x_159_);
lean_dec(v_startPos_152_);
v___x_167_ = lean_box(0);
return v___x_167_;
}
else
{
lean_object* v_startPos_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_173_; 
v_startPos_168_ = lean_ctor_get(v_fst_161_, 2);
v___x_169_ = lean_box(0);
lean_inc(v_startPos_168_);
v___x_170_ = l_Lean_Markdown_subsliceClamped___redArg(v_startPos_152_, v_startPos_168_);
v___x_171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_171_, 0, v___x_169_);
lean_ctor_set(v___x_171_, 1, v___x_170_);
if (v_isShared_165_ == 0)
{
lean_ctor_set(v___x_164_, 1, v_fst_161_);
lean_ctor_set(v___x_164_, 0, v___x_171_);
v___x_173_ = v___x_164_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v___x_171_);
lean_ctor_set(v_reuseFailAlloc_177_, 1, v_fst_161_);
v___x_173_ = v_reuseFailAlloc_177_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
lean_object* v___x_175_; 
if (v_isShared_160_ == 0)
{
lean_ctor_set(v___x_159_, 0, v___x_173_);
v___x_175_ = v___x_159_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v___x_173_);
v___x_175_ = v_reuseFailAlloc_176_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
return v___x_175_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_180_; 
v___x_180_ = l_Lean_Markdown_InlineCursor_charSubslice_x3f(v_s_147_, v_cur_148_);
if (lean_obj_tag(v___x_180_) == 0)
{
lean_object* v___x_181_; 
lean_dec_ref(v_cur_148_);
v___x_181_ = lean_box(0);
return v___x_181_;
}
else
{
lean_object* v_val_182_; lean_object* v___x_183_; lean_object* v_startPos_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v_val_182_ = lean_ctor_get(v___x_180_, 0);
lean_inc(v_val_182_);
lean_dec_ref_known(v___x_180_, 1);
v___x_183_ = l_Lean_Markdown_InlineCursor_drop1(v_s_147_, v_cur_148_);
v_startPos_184_ = lean_ctor_get(v___x_183_, 2);
lean_inc(v_startPos_184_);
v___x_185_ = lean_box(0);
v___x_186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_186_, 0, v___x_185_);
lean_ctor_set(v___x_186_, 1, v___x_183_);
v___x_187_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseLinkDestination_x3f_spec__2___redArg(v_s_147_, v_val_182_, v_startPos_184_, v___x_186_);
if (lean_obj_tag(v___x_187_) == 0)
{
return v___x_185_;
}
else
{
lean_object* v_val_188_; lean_object* v_fst_189_; 
v_val_188_ = lean_ctor_get(v___x_187_, 0);
lean_inc(v_val_188_);
lean_dec_ref_known(v___x_187_, 1);
v_fst_189_ = lean_ctor_get(v_val_188_, 0);
lean_inc(v_fst_189_);
lean_dec(v_val_188_);
return v_fst_189_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_parseLinkDestination_x3f___boxed(lean_object* v_s_190_, lean_object* v_cur_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Lean_Markdown_parseLinkDestination_x3f(v_s_190_, v_cur_191_);
lean_dec_ref(v_s_190_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseLinkDestination_x3f_spec__1(lean_object* v_s_193_, lean_object* v_inst_194_, lean_object* v_a_195_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseLinkDestination_x3f_spec__1___redArg(v_s_193_, v_a_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseLinkDestination_x3f_spec__1___boxed(lean_object* v_s_197_, lean_object* v_inst_198_, lean_object* v_a_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseLinkDestination_x3f_spec__1(v_s_197_, v_inst_198_, v_a_199_);
lean_dec_ref(v_s_197_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseLinkDestination_x3f_spec__2(lean_object* v_s_201_, lean_object* v_val_202_, lean_object* v___x_203_, lean_object* v_inst_204_, lean_object* v_a_205_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseLinkDestination_x3f_spec__2___redArg(v_s_201_, v_val_202_, v___x_203_, v_a_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseLinkDestination_x3f_spec__2___boxed(lean_object* v_s_207_, lean_object* v_val_208_, lean_object* v___x_209_, lean_object* v_inst_210_, lean_object* v_a_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseLinkDestination_x3f_spec__2(v_s_207_, v_val_208_, v___x_209_, v_inst_210_, v_a_211_);
lean_dec_ref(v_s_207_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseLinkTitle_x3f_spec__0___redArg(lean_object* v_s_213_, uint32_t v_closerChar_214_, lean_object* v___x_215_, lean_object* v_val_216_, lean_object* v_a_217_){
_start:
{
lean_object* v_snd_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_266_; 
v_snd_218_ = lean_ctor_get(v_a_217_, 1);
v_isSharedCheck_266_ = !lean_is_exclusive(v_a_217_);
if (v_isSharedCheck_266_ == 0)
{
lean_object* v_unused_267_; 
v_unused_267_ = lean_ctor_get(v_a_217_, 0);
lean_dec(v_unused_267_);
v___x_220_ = v_a_217_;
v_isShared_221_ = v_isSharedCheck_266_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_snd_218_);
lean_dec(v_a_217_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_266_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_222_; uint8_t v___x_223_; 
v___x_222_ = lean_box(0);
v___x_223_ = l_Lean_Markdown_InlineCursor_isEmpty___redArg(v_snd_218_);
if (v___x_223_ == 0)
{
uint32_t v___x_224_; lean_object* v___x_225_; uint32_t v___x_253_; uint8_t v___x_254_; 
v___x_224_ = l_Lean_Markdown_InlineCursor_front(v_s_213_, v_snd_218_);
lean_inc(v_snd_218_);
v___x_225_ = l_Lean_Markdown_InlineCursor_drop1(v_s_213_, v_snd_218_);
v___x_253_ = 92;
v___x_254_ = lean_uint32_dec_eq(v___x_224_, v___x_253_);
if (v___x_254_ == 0)
{
goto v___jp_231_;
}
else
{
lean_object* v___x_255_; 
v___x_255_ = l_Lean_Markdown_InlineCursor_front_x3f(v_s_213_, v___x_225_);
if (lean_obj_tag(v___x_255_) == 0)
{
goto v___jp_231_;
}
else
{
lean_object* v_val_256_; uint32_t v___x_257_; uint8_t v___x_258_; 
v_val_256_ = lean_ctor_get(v___x_255_, 0);
lean_inc(v_val_256_);
lean_dec_ref_known(v___x_255_, 1);
v___x_257_ = lean_unbox_uint32(v_val_256_);
lean_dec(v_val_256_);
v___x_258_ = l_Lean_Markdown_isAsciiPunctuation(v___x_257_);
if (v___x_258_ == 0)
{
goto v___jp_231_;
}
else
{
lean_object* v___x_259_; lean_object* v___x_260_; 
lean_del_object(v___x_220_);
lean_dec(v_snd_218_);
v___x_259_ = l_Lean_Markdown_InlineCursor_drop1(v_s_213_, v___x_225_);
v___x_260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_260_, 0, v___x_222_);
lean_ctor_set(v___x_260_, 1, v___x_259_);
v_a_217_ = v___x_260_;
goto _start;
}
}
}
v___jp_226_:
{
lean_object* v___x_228_; 
if (v_isShared_221_ == 0)
{
lean_ctor_set(v___x_220_, 1, v___x_225_);
lean_ctor_set(v___x_220_, 0, v___x_222_);
v___x_228_ = v___x_220_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v___x_222_);
lean_ctor_set(v_reuseFailAlloc_230_, 1, v___x_225_);
v___x_228_ = v_reuseFailAlloc_230_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
v_a_217_ = v___x_228_;
goto _start;
}
}
v___jp_231_:
{
uint8_t v___x_232_; 
v___x_232_ = lean_uint32_dec_eq(v___x_224_, v_closerChar_214_);
if (v___x_232_ == 0)
{
uint32_t v___x_233_; uint8_t v___x_234_; 
lean_dec(v_snd_218_);
v___x_233_ = 40;
v___x_234_ = lean_uint32_dec_eq(v___x_224_, v___x_233_);
if (v___x_234_ == 0)
{
goto v___jp_226_;
}
else
{
uint32_t v___x_235_; uint8_t v___x_236_; 
v___x_235_ = 41;
v___x_236_ = lean_uint32_dec_eq(v_closerChar_214_, v___x_235_);
if (v___x_236_ == 0)
{
goto v___jp_226_;
}
else
{
lean_dec_ref(v___x_225_);
lean_del_object(v___x_220_);
lean_dec_ref(v_val_216_);
lean_dec(v___x_215_);
return v___x_222_;
}
}
}
else
{
lean_object* v___x_237_; 
lean_del_object(v___x_220_);
v___x_237_ = l_Lean_Markdown_InlineCursor_charSubslice_x3f(v_s_213_, v_snd_218_);
if (lean_obj_tag(v___x_237_) == 0)
{
lean_dec_ref(v___x_225_);
lean_dec(v_snd_218_);
lean_dec_ref(v_val_216_);
lean_dec(v___x_215_);
return v___x_222_;
}
else
{
lean_object* v_val_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_252_; 
v_val_238_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_252_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_252_ == 0)
{
v___x_240_ = v___x_237_;
v_isShared_241_ = v_isSharedCheck_252_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_val_238_);
lean_dec(v___x_237_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_252_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v_source_242_; lean_object* v_startPos_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_248_; 
v_source_242_ = lean_ctor_get(v_snd_218_, 0);
v_startPos_243_ = lean_ctor_get(v_snd_218_, 2);
lean_inc(v_startPos_243_);
v___x_244_ = l_Lean_Markdown_InlineSource_linesBetween(v_s_213_, v_source_242_, v___x_215_, v_startPos_243_);
v___x_245_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_245_, 0, v_val_216_);
lean_ctor_set(v___x_245_, 1, v___x_244_);
lean_ctor_set(v___x_245_, 2, v_val_238_);
v___x_246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_246_, 0, v___x_245_);
lean_ctor_set(v___x_246_, 1, v___x_225_);
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 0, v___x_246_);
v___x_248_ = v___x_240_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v___x_246_);
v___x_248_ = v_reuseFailAlloc_251_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_249_, 0, v___x_248_);
lean_ctor_set(v___x_249_, 1, v_snd_218_);
v___x_250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_250_, 0, v___x_249_);
return v___x_250_;
}
}
}
}
}
}
else
{
lean_object* v___x_263_; 
lean_dec_ref(v_val_216_);
lean_dec(v___x_215_);
if (v_isShared_221_ == 0)
{
lean_ctor_set(v___x_220_, 0, v___x_222_);
v___x_263_ = v___x_220_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v___x_222_);
lean_ctor_set(v_reuseFailAlloc_265_, 1, v_snd_218_);
v___x_263_ = v_reuseFailAlloc_265_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
lean_object* v___x_264_; 
v___x_264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
return v___x_264_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseLinkTitle_x3f_spec__0___redArg___boxed(lean_object* v_s_268_, lean_object* v_closerChar_269_, lean_object* v___x_270_, lean_object* v_val_271_, lean_object* v_a_272_){
_start:
{
uint32_t v_closerChar_boxed_273_; lean_object* v_res_274_; 
v_closerChar_boxed_273_ = lean_unbox_uint32(v_closerChar_269_);
lean_dec(v_closerChar_269_);
v_res_274_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseLinkTitle_x3f_spec__0___redArg(v_s_268_, v_closerChar_boxed_273_, v___x_270_, v_val_271_, v_a_272_);
lean_dec_ref(v_s_268_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_parseLinkTitle_x3f(lean_object* v_s_275_, lean_object* v_cur_276_){
_start:
{
uint32_t v_closerChar_278_; lean_object* v___x_289_; 
v___x_289_ = l_Lean_Markdown_InlineCursor_front_x3f(v_s_275_, v_cur_276_);
if (lean_obj_tag(v___x_289_) == 1)
{
lean_object* v_val_290_; uint32_t v___x_291_; uint32_t v___x_292_; uint8_t v___x_293_; 
v_val_290_ = lean_ctor_get(v___x_289_, 0);
lean_inc(v_val_290_);
lean_dec_ref_known(v___x_289_, 1);
v___x_291_ = 34;
v___x_292_ = lean_unbox_uint32(v_val_290_);
v___x_293_ = lean_uint32_dec_eq(v___x_292_, v___x_291_);
if (v___x_293_ == 0)
{
uint32_t v___x_294_; uint32_t v___x_295_; uint8_t v___x_296_; 
v___x_294_ = 39;
v___x_295_ = lean_unbox_uint32(v_val_290_);
v___x_296_ = lean_uint32_dec_eq(v___x_295_, v___x_294_);
if (v___x_296_ == 0)
{
uint32_t v___x_297_; uint32_t v___x_298_; uint8_t v___x_299_; 
v___x_297_ = 40;
v___x_298_ = lean_unbox_uint32(v_val_290_);
lean_dec(v_val_290_);
v___x_299_ = lean_uint32_dec_eq(v___x_298_, v___x_297_);
if (v___x_299_ == 0)
{
lean_object* v___x_300_; 
lean_dec_ref(v_cur_276_);
v___x_300_ = lean_box(0);
return v___x_300_;
}
else
{
uint32_t v___x_301_; 
v___x_301_ = 41;
v_closerChar_278_ = v___x_301_;
goto v___jp_277_;
}
}
else
{
lean_dec(v_val_290_);
v_closerChar_278_ = v___x_294_;
goto v___jp_277_;
}
}
else
{
lean_dec(v_val_290_);
v_closerChar_278_ = v___x_291_;
goto v___jp_277_;
}
}
else
{
lean_object* v___x_302_; 
lean_dec(v___x_289_);
lean_dec_ref(v_cur_276_);
v___x_302_ = lean_box(0);
return v___x_302_;
}
v___jp_277_:
{
lean_object* v___x_279_; 
v___x_279_ = l_Lean_Markdown_InlineCursor_charSubslice_x3f(v_s_275_, v_cur_276_);
if (lean_obj_tag(v___x_279_) == 0)
{
lean_object* v___x_280_; 
lean_dec_ref(v_cur_276_);
v___x_280_ = lean_box(0);
return v___x_280_;
}
else
{
lean_object* v_val_281_; lean_object* v_endExclusive_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v_val_281_ = lean_ctor_get(v___x_279_, 0);
lean_inc(v_val_281_);
lean_dec_ref_known(v___x_279_, 1);
v_endExclusive_282_ = lean_ctor_get(v_val_281_, 1);
lean_inc(v_endExclusive_282_);
v___x_283_ = l_Lean_Markdown_InlineCursor_drop1(v_s_275_, v_cur_276_);
v___x_284_ = lean_box(0);
v___x_285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
lean_ctor_set(v___x_285_, 1, v___x_283_);
v___x_286_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseLinkTitle_x3f_spec__0___redArg(v_s_275_, v_closerChar_278_, v_endExclusive_282_, v_val_281_, v___x_285_);
if (lean_obj_tag(v___x_286_) == 0)
{
return v___x_284_;
}
else
{
lean_object* v_val_287_; lean_object* v_fst_288_; 
v_val_287_ = lean_ctor_get(v___x_286_, 0);
lean_inc(v_val_287_);
lean_dec_ref_known(v___x_286_, 1);
v_fst_288_ = lean_ctor_get(v_val_287_, 0);
lean_inc(v_fst_288_);
lean_dec(v_val_287_);
return v_fst_288_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_parseLinkTitle_x3f___boxed(lean_object* v_s_303_, lean_object* v_cur_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Lean_Markdown_parseLinkTitle_x3f(v_s_303_, v_cur_304_);
lean_dec_ref(v_s_303_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseLinkTitle_x3f_spec__0(lean_object* v_s_306_, uint32_t v_closerChar_307_, lean_object* v___x_308_, lean_object* v_val_309_, lean_object* v_inst_310_, lean_object* v_a_311_){
_start:
{
lean_object* v___x_312_; 
v___x_312_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseLinkTitle_x3f_spec__0___redArg(v_s_306_, v_closerChar_307_, v___x_308_, v_val_309_, v_a_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseLinkTitle_x3f_spec__0___boxed(lean_object* v_s_313_, lean_object* v_closerChar_314_, lean_object* v___x_315_, lean_object* v_val_316_, lean_object* v_inst_317_, lean_object* v_a_318_){
_start:
{
uint32_t v_closerChar_boxed_319_; lean_object* v_res_320_; 
v_closerChar_boxed_319_ = lean_unbox_uint32(v_closerChar_314_);
lean_dec(v_closerChar_314_);
v_res_320_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseLinkTitle_x3f_spec__0(v_s_313_, v_closerChar_boxed_319_, v___x_315_, v_val_316_, v_inst_317_, v_a_318_);
lean_dec_ref(v_s_313_);
return v_res_320_;
}
}
lean_object* runtime_initialize_Init_While(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Markdown_Inline(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Markdown_InlineCursor(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Markdown_Text(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Markdown_Parser_LinkSyntax(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Markdown_Inline(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Markdown_InlineCursor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Markdown_Text(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Markdown_parseLinkDestination_x3f___closed__0___boxed__const__1 = _init_l_Lean_Markdown_parseLinkDestination_x3f___closed__0___boxed__const__1();
lean_mark_persistent(l_Lean_Markdown_parseLinkDestination_x3f___closed__0___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_Markdown_Parser_LinkSyntax(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_While(uint8_t builtin);
lean_object* initialize_Lean_Data_Markdown_Inline(uint8_t builtin);
lean_object* initialize_Lean_Data_Markdown_InlineCursor(uint8_t builtin);
lean_object* initialize_Lean_Data_Markdown_Text(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Markdown_Parser_LinkSyntax(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Markdown_Inline(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Markdown_InlineCursor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Markdown_Text(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Markdown_Parser_LinkSyntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_Markdown_Parser_LinkSyntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_Markdown_Parser_LinkSyntax(builtin);
}
#ifdef __cplusplus
}
#endif

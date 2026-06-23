// Lean compiler output
// Module: Lean.Meta.Sym.DSimp.DSimproc
// Imports: public import Lean.Meta.Sym.DSimp.Result
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
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_DSimproc_andThen(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_DSimproc_andThen___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_instAndThenDSimproc___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_instAndThenDSimproc___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Sym_DSimp_instAndThenDSimproc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_DSimp_instAndThenDSimproc___lam__0___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_DSimp_instAndThenDSimproc___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_DSimp_instAndThenDSimproc___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_DSimp_instAndThenDSimproc = (const lean_object*)&l_Lean_Meta_Sym_DSimp_instAndThenDSimproc___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_DSimproc_orElse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_DSimproc_orElse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_instOrElseDSimproc___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_instOrElseDSimproc___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Sym_DSimp_instOrElseDSimproc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_DSimp_instOrElseDSimproc___lam__0___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_DSimp_instOrElseDSimproc___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_DSimp_instOrElseDSimproc___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_DSimp_instOrElseDSimproc = (const lean_object*)&l_Lean_Meta_Sym_DSimp_instOrElseDSimproc___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_DSimproc_tryCatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_DSimproc_tryCatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_DSimproc_andThen(lean_object* v_f_1_, lean_object* v_g_2_, lean_object* v_e_u2081_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_){
_start:
{
lean_object* v___x_14_; 
lean_inc(v_a_12_);
lean_inc_ref(v_a_11_);
lean_inc(v_a_10_);
lean_inc_ref(v_a_9_);
lean_inc(v_a_8_);
lean_inc_ref(v_a_7_);
lean_inc(v_a_6_);
lean_inc(v_a_5_);
lean_inc(v_a_4_);
lean_inc_ref(v_e_u2081_3_);
v___x_14_ = lean_apply_11(v_f_1_, v_e_u2081_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_, lean_box(0));
if (lean_obj_tag(v___x_14_) == 0)
{
lean_object* v_a_15_; 
v_a_15_ = lean_ctor_get(v___x_14_, 0);
lean_inc(v_a_15_);
if (lean_obj_tag(v_a_15_) == 0)
{
uint8_t v_done_16_; 
v_done_16_ = lean_ctor_get_uint8(v_a_15_, 0);
lean_dec_ref_known(v_a_15_, 0);
if (v_done_16_ == 0)
{
lean_object* v___x_17_; 
lean_dec_ref_known(v___x_14_, 1);
lean_inc(v_a_12_);
lean_inc_ref(v_a_11_);
lean_inc(v_a_10_);
lean_inc_ref(v_a_9_);
lean_inc(v_a_8_);
lean_inc_ref(v_a_7_);
lean_inc(v_a_6_);
lean_inc(v_a_5_);
lean_inc(v_a_4_);
v___x_17_ = lean_apply_11(v_g_2_, v_e_u2081_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_, lean_box(0));
return v___x_17_;
}
else
{
lean_dec_ref(v_e_u2081_3_);
lean_dec_ref(v_g_2_);
return v___x_14_;
}
}
else
{
uint8_t v_done_18_; 
lean_dec_ref(v_e_u2081_3_);
v_done_18_ = lean_ctor_get_uint8(v_a_15_, sizeof(void*)*1);
if (v_done_18_ == 0)
{
lean_object* v_e_x27_19_; lean_object* v___x_21_; uint8_t v_isShared_22_; uint8_t v_isSharedCheck_37_; 
lean_dec_ref_known(v___x_14_, 1);
v_e_x27_19_ = lean_ctor_get(v_a_15_, 0);
v_isSharedCheck_37_ = !lean_is_exclusive(v_a_15_);
if (v_isSharedCheck_37_ == 0)
{
v___x_21_ = v_a_15_;
v_isShared_22_ = v_isSharedCheck_37_;
goto v_resetjp_20_;
}
else
{
lean_inc(v_e_x27_19_);
lean_dec(v_a_15_);
v___x_21_ = lean_box(0);
v_isShared_22_ = v_isSharedCheck_37_;
goto v_resetjp_20_;
}
v_resetjp_20_:
{
lean_object* v___x_23_; 
lean_inc(v_a_12_);
lean_inc_ref(v_a_11_);
lean_inc(v_a_10_);
lean_inc_ref(v_a_9_);
lean_inc(v_a_8_);
lean_inc_ref(v_a_7_);
lean_inc(v_a_6_);
lean_inc(v_a_5_);
lean_inc(v_a_4_);
lean_inc_ref(v_e_x27_19_);
v___x_23_ = lean_apply_11(v_g_2_, v_e_x27_19_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_, lean_box(0));
if (lean_obj_tag(v___x_23_) == 0)
{
lean_object* v_a_24_; 
v_a_24_ = lean_ctor_get(v___x_23_, 0);
lean_inc(v_a_24_);
if (lean_obj_tag(v_a_24_) == 0)
{
lean_object* v___x_26_; uint8_t v_isShared_27_; uint8_t v_isSharedCheck_35_; 
v_isSharedCheck_35_ = !lean_is_exclusive(v___x_23_);
if (v_isSharedCheck_35_ == 0)
{
lean_object* v_unused_36_; 
v_unused_36_ = lean_ctor_get(v___x_23_, 0);
lean_dec(v_unused_36_);
v___x_26_ = v___x_23_;
v_isShared_27_ = v_isSharedCheck_35_;
goto v_resetjp_25_;
}
else
{
lean_dec(v___x_23_);
v___x_26_ = lean_box(0);
v_isShared_27_ = v_isSharedCheck_35_;
goto v_resetjp_25_;
}
v_resetjp_25_:
{
uint8_t v_done_28_; lean_object* v___x_30_; 
v_done_28_ = lean_ctor_get_uint8(v_a_24_, 0);
lean_dec_ref_known(v_a_24_, 0);
if (v_isShared_22_ == 0)
{
v___x_30_ = v___x_21_;
goto v_reusejp_29_;
}
else
{
lean_object* v_reuseFailAlloc_34_; 
v_reuseFailAlloc_34_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_34_, 0, v_e_x27_19_);
v___x_30_ = v_reuseFailAlloc_34_;
goto v_reusejp_29_;
}
v_reusejp_29_:
{
lean_object* v___x_32_; 
lean_ctor_set_uint8(v___x_30_, sizeof(void*)*1, v_done_28_);
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
lean_dec_ref_known(v_a_24_, 1);
lean_del_object(v___x_21_);
lean_dec_ref(v_e_x27_19_);
return v___x_23_;
}
}
else
{
lean_del_object(v___x_21_);
lean_dec_ref(v_e_x27_19_);
return v___x_23_;
}
}
}
else
{
lean_dec_ref_known(v_a_15_, 1);
lean_dec_ref(v_g_2_);
return v___x_14_;
}
}
}
else
{
lean_dec_ref(v_e_u2081_3_);
lean_dec_ref(v_g_2_);
return v___x_14_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_DSimproc_andThen___boxed(lean_object* v_f_38_, lean_object* v_g_39_, lean_object* v_e_u2081_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_Meta_Sym_DSimp_DSimproc_andThen(v_f_38_, v_g_39_, v_e_u2081_40_, v_a_41_, v_a_42_, v_a_43_, v_a_44_, v_a_45_, v_a_46_, v_a_47_, v_a_48_, v_a_49_);
lean_dec(v_a_49_);
lean_dec_ref(v_a_48_);
lean_dec(v_a_47_);
lean_dec_ref(v_a_46_);
lean_dec(v_a_45_);
lean_dec_ref(v_a_44_);
lean_dec(v_a_43_);
lean_dec(v_a_42_);
lean_dec(v_a_41_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_instAndThenDSimproc___lam__0(lean_object* v_f_52_, lean_object* v_g_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_){
_start:
{
lean_object* v___x_65_; 
lean_inc(v___y_63_);
lean_inc_ref(v___y_62_);
lean_inc(v___y_61_);
lean_inc_ref(v___y_60_);
lean_inc(v___y_59_);
lean_inc_ref(v___y_58_);
lean_inc(v___y_57_);
lean_inc(v___y_56_);
lean_inc(v___y_55_);
lean_inc_ref(v___y_54_);
v___x_65_ = lean_apply_11(v_f_52_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_, lean_box(0));
if (lean_obj_tag(v___x_65_) == 0)
{
lean_object* v_a_66_; lean_object* v___x_67_; 
v_a_66_ = lean_ctor_get(v___x_65_, 0);
lean_inc(v_a_66_);
v___x_67_ = lean_box(0);
if (lean_obj_tag(v_a_66_) == 0)
{
uint8_t v_done_68_; 
v_done_68_ = lean_ctor_get_uint8(v_a_66_, 0);
lean_dec_ref_known(v_a_66_, 0);
if (v_done_68_ == 0)
{
lean_object* v___x_69_; 
lean_dec_ref_known(v___x_65_, 1);
lean_inc(v___y_63_);
lean_inc_ref(v___y_62_);
lean_inc(v___y_61_);
lean_inc_ref(v___y_60_);
lean_inc(v___y_59_);
lean_inc_ref(v___y_58_);
lean_inc(v___y_57_);
lean_inc(v___y_56_);
lean_inc(v___y_55_);
v___x_69_ = lean_apply_12(v_g_53_, v___x_67_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_, lean_box(0));
return v___x_69_;
}
else
{
lean_dec_ref(v___y_54_);
lean_dec_ref(v_g_53_);
return v___x_65_;
}
}
else
{
uint8_t v_done_70_; 
lean_dec_ref(v___y_54_);
v_done_70_ = lean_ctor_get_uint8(v_a_66_, sizeof(void*)*1);
if (v_done_70_ == 0)
{
lean_object* v_e_x27_71_; lean_object* v___x_73_; uint8_t v_isShared_74_; uint8_t v_isSharedCheck_89_; 
lean_dec_ref_known(v___x_65_, 1);
v_e_x27_71_ = lean_ctor_get(v_a_66_, 0);
v_isSharedCheck_89_ = !lean_is_exclusive(v_a_66_);
if (v_isSharedCheck_89_ == 0)
{
v___x_73_ = v_a_66_;
v_isShared_74_ = v_isSharedCheck_89_;
goto v_resetjp_72_;
}
else
{
lean_inc(v_e_x27_71_);
lean_dec(v_a_66_);
v___x_73_ = lean_box(0);
v_isShared_74_ = v_isSharedCheck_89_;
goto v_resetjp_72_;
}
v_resetjp_72_:
{
lean_object* v___x_75_; 
lean_inc(v___y_63_);
lean_inc_ref(v___y_62_);
lean_inc(v___y_61_);
lean_inc_ref(v___y_60_);
lean_inc(v___y_59_);
lean_inc_ref(v___y_58_);
lean_inc(v___y_57_);
lean_inc(v___y_56_);
lean_inc(v___y_55_);
lean_inc_ref(v_e_x27_71_);
v___x_75_ = lean_apply_12(v_g_53_, v___x_67_, v_e_x27_71_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_, lean_box(0));
if (lean_obj_tag(v___x_75_) == 0)
{
lean_object* v_a_76_; 
v_a_76_ = lean_ctor_get(v___x_75_, 0);
lean_inc(v_a_76_);
if (lean_obj_tag(v_a_76_) == 0)
{
lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_87_; 
v_isSharedCheck_87_ = !lean_is_exclusive(v___x_75_);
if (v_isSharedCheck_87_ == 0)
{
lean_object* v_unused_88_; 
v_unused_88_ = lean_ctor_get(v___x_75_, 0);
lean_dec(v_unused_88_);
v___x_78_ = v___x_75_;
v_isShared_79_ = v_isSharedCheck_87_;
goto v_resetjp_77_;
}
else
{
lean_dec(v___x_75_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_87_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
uint8_t v_done_80_; lean_object* v___x_82_; 
v_done_80_ = lean_ctor_get_uint8(v_a_76_, 0);
lean_dec_ref_known(v_a_76_, 0);
if (v_isShared_74_ == 0)
{
v___x_82_ = v___x_73_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_86_; 
v_reuseFailAlloc_86_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_86_, 0, v_e_x27_71_);
v___x_82_ = v_reuseFailAlloc_86_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
lean_object* v___x_84_; 
lean_ctor_set_uint8(v___x_82_, sizeof(void*)*1, v_done_80_);
if (v_isShared_79_ == 0)
{
lean_ctor_set(v___x_78_, 0, v___x_82_);
v___x_84_ = v___x_78_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v___x_82_);
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
else
{
lean_dec_ref_known(v_a_76_, 1);
lean_del_object(v___x_73_);
lean_dec_ref(v_e_x27_71_);
return v___x_75_;
}
}
else
{
lean_del_object(v___x_73_);
lean_dec_ref(v_e_x27_71_);
return v___x_75_;
}
}
}
else
{
lean_dec_ref_known(v_a_66_, 1);
lean_dec_ref(v_g_53_);
return v___x_65_;
}
}
}
else
{
lean_dec_ref(v___y_54_);
lean_dec_ref(v_g_53_);
return v___x_65_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_instAndThenDSimproc___lam__0___boxed(lean_object* v_f_90_, lean_object* v_g_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l_Lean_Meta_Sym_DSimp_instAndThenDSimproc___lam__0(v_f_90_, v_g_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_, v___y_101_);
lean_dec(v___y_101_);
lean_dec_ref(v___y_100_);
lean_dec(v___y_99_);
lean_dec_ref(v___y_98_);
lean_dec(v___y_97_);
lean_dec_ref(v___y_96_);
lean_dec(v___y_95_);
lean_dec(v___y_94_);
lean_dec(v___y_93_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_DSimproc_orElse(lean_object* v_f_106_, lean_object* v_g_107_, lean_object* v_e_u2081_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_){
_start:
{
lean_object* v___x_119_; 
lean_inc(v_a_117_);
lean_inc_ref(v_a_116_);
lean_inc(v_a_115_);
lean_inc_ref(v_a_114_);
lean_inc(v_a_113_);
lean_inc_ref(v_a_112_);
lean_inc(v_a_111_);
lean_inc(v_a_110_);
lean_inc(v_a_109_);
lean_inc_ref(v_e_u2081_108_);
v___x_119_ = lean_apply_11(v_f_106_, v_e_u2081_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_, v_a_113_, v_a_114_, v_a_115_, v_a_116_, v_a_117_, lean_box(0));
if (lean_obj_tag(v___x_119_) == 0)
{
lean_object* v_a_120_; 
v_a_120_ = lean_ctor_get(v___x_119_, 0);
lean_inc(v_a_120_);
if (lean_obj_tag(v_a_120_) == 0)
{
uint8_t v_done_121_; 
v_done_121_ = lean_ctor_get_uint8(v_a_120_, 0);
lean_dec_ref_known(v_a_120_, 0);
if (v_done_121_ == 0)
{
lean_object* v___x_122_; 
lean_dec_ref_known(v___x_119_, 1);
lean_inc(v_a_117_);
lean_inc_ref(v_a_116_);
lean_inc(v_a_115_);
lean_inc_ref(v_a_114_);
lean_inc(v_a_113_);
lean_inc_ref(v_a_112_);
lean_inc(v_a_111_);
lean_inc(v_a_110_);
lean_inc(v_a_109_);
v___x_122_ = lean_apply_11(v_g_107_, v_e_u2081_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_, v_a_113_, v_a_114_, v_a_115_, v_a_116_, v_a_117_, lean_box(0));
return v___x_122_;
}
else
{
lean_dec_ref(v_e_u2081_108_);
lean_dec_ref(v_g_107_);
return v___x_119_;
}
}
else
{
lean_dec_ref_known(v_a_120_, 1);
lean_dec_ref(v_e_u2081_108_);
lean_dec_ref(v_g_107_);
return v___x_119_;
}
}
else
{
lean_dec_ref(v_e_u2081_108_);
lean_dec_ref(v_g_107_);
return v___x_119_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_DSimproc_orElse___boxed(lean_object* v_f_123_, lean_object* v_g_124_, lean_object* v_e_u2081_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l_Lean_Meta_Sym_DSimp_DSimproc_orElse(v_f_123_, v_g_124_, v_e_u2081_125_, v_a_126_, v_a_127_, v_a_128_, v_a_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_, v_a_134_);
lean_dec(v_a_134_);
lean_dec_ref(v_a_133_);
lean_dec(v_a_132_);
lean_dec_ref(v_a_131_);
lean_dec(v_a_130_);
lean_dec_ref(v_a_129_);
lean_dec(v_a_128_);
lean_dec(v_a_127_);
lean_dec(v_a_126_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_instOrElseDSimproc___lam__0(lean_object* v_f_137_, lean_object* v_g_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_){
_start:
{
lean_object* v___x_150_; 
lean_inc(v___y_148_);
lean_inc_ref(v___y_147_);
lean_inc(v___y_146_);
lean_inc_ref(v___y_145_);
lean_inc(v___y_144_);
lean_inc_ref(v___y_143_);
lean_inc(v___y_142_);
lean_inc(v___y_141_);
lean_inc(v___y_140_);
lean_inc_ref(v___y_139_);
v___x_150_ = lean_apply_11(v_f_137_, v___y_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_, lean_box(0));
if (lean_obj_tag(v___x_150_) == 0)
{
lean_object* v_a_151_; 
v_a_151_ = lean_ctor_get(v___x_150_, 0);
lean_inc(v_a_151_);
if (lean_obj_tag(v_a_151_) == 0)
{
uint8_t v_done_152_; 
v_done_152_ = lean_ctor_get_uint8(v_a_151_, 0);
lean_dec_ref_known(v_a_151_, 0);
if (v_done_152_ == 0)
{
lean_object* v___x_153_; lean_object* v___x_154_; 
lean_dec_ref_known(v___x_150_, 1);
v___x_153_ = lean_box(0);
lean_inc(v___y_148_);
lean_inc_ref(v___y_147_);
lean_inc(v___y_146_);
lean_inc_ref(v___y_145_);
lean_inc(v___y_144_);
lean_inc_ref(v___y_143_);
lean_inc(v___y_142_);
lean_inc(v___y_141_);
lean_inc(v___y_140_);
v___x_154_ = lean_apply_12(v_g_138_, v___x_153_, v___y_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_, lean_box(0));
return v___x_154_;
}
else
{
lean_dec_ref(v___y_139_);
lean_dec_ref(v_g_138_);
return v___x_150_;
}
}
else
{
lean_dec_ref_known(v_a_151_, 1);
lean_dec_ref(v___y_139_);
lean_dec_ref(v_g_138_);
return v___x_150_;
}
}
else
{
lean_dec_ref(v___y_139_);
lean_dec_ref(v_g_138_);
return v___x_150_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_instOrElseDSimproc___lam__0___boxed(lean_object* v_f_155_, lean_object* v_g_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Lean_Meta_Sym_DSimp_instOrElseDSimproc___lam__0(v_f_155_, v_g_156_, v___y_157_, v___y_158_, v___y_159_, v___y_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_, v___y_166_);
lean_dec(v___y_166_);
lean_dec_ref(v___y_165_);
lean_dec(v___y_164_);
lean_dec_ref(v___y_163_);
lean_dec(v___y_162_);
lean_dec_ref(v___y_161_);
lean_dec(v___y_160_);
lean_dec(v___y_159_);
lean_dec(v___y_158_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_DSimproc_tryCatch(lean_object* v_f_171_, lean_object* v_e_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_){
_start:
{
lean_object* v___x_183_; 
lean_inc(v_a_181_);
lean_inc_ref(v_a_180_);
lean_inc(v_a_179_);
lean_inc_ref(v_a_178_);
lean_inc(v_a_177_);
lean_inc_ref(v_a_176_);
lean_inc(v_a_175_);
lean_inc(v_a_174_);
lean_inc(v_a_173_);
v___x_183_ = lean_apply_11(v_f_171_, v_e_172_, v_a_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_, lean_box(0));
if (lean_obj_tag(v___x_183_) == 0)
{
return v___x_183_;
}
else
{
lean_object* v_a_184_; uint8_t v___y_186_; uint8_t v___x_196_; 
v_a_184_ = lean_ctor_get(v___x_183_, 0);
lean_inc(v_a_184_);
v___x_196_ = l_Lean_Exception_isInterrupt(v_a_184_);
if (v___x_196_ == 0)
{
uint8_t v___x_197_; 
v___x_197_ = l_Lean_Exception_isRuntime(v_a_184_);
v___y_186_ = v___x_197_;
goto v___jp_185_;
}
else
{
lean_dec(v_a_184_);
v___y_186_ = v___x_196_;
goto v___jp_185_;
}
v___jp_185_:
{
if (v___y_186_ == 0)
{
lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_194_; 
v_isSharedCheck_194_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_194_ == 0)
{
lean_object* v_unused_195_; 
v_unused_195_ = lean_ctor_get(v___x_183_, 0);
lean_dec(v_unused_195_);
v___x_188_ = v___x_183_;
v_isShared_189_ = v_isSharedCheck_194_;
goto v_resetjp_187_;
}
else
{
lean_dec(v___x_183_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_194_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___x_190_; lean_object* v___x_192_; 
v___x_190_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_190_, 0, v___y_186_);
if (v_isShared_189_ == 0)
{
lean_ctor_set_tag(v___x_188_, 0);
lean_ctor_set(v___x_188_, 0, v___x_190_);
v___x_192_ = v___x_188_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v___x_190_);
v___x_192_ = v_reuseFailAlloc_193_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
return v___x_192_;
}
}
}
else
{
return v___x_183_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_DSimproc_tryCatch___boxed(lean_object* v_f_198_, lean_object* v_e_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Lean_Meta_Sym_DSimp_DSimproc_tryCatch(v_f_198_, v_e_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_);
lean_dec(v_a_208_);
lean_dec_ref(v_a_207_);
lean_dec(v_a_206_);
lean_dec_ref(v_a_205_);
lean_dec(v_a_204_);
lean_dec_ref(v_a_203_);
lean_dec(v_a_202_);
lean_dec(v_a_201_);
lean_dec(v_a_200_);
return v_res_210_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_Result(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_DSimproc(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Sym_DSimp_Result(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_DSimp_DSimproc(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_DSimp_Result(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_DSimp_DSimproc(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_DSimp_Result(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_DSimp_DSimproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_DSimp_DSimproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_DSimp_DSimproc(builtin);
}
#ifdef __cplusplus
}
#endif

// Lean compiler output
// Module: Lean.Meta.Sym.Simp.Simproc
// Imports: public import Lean.Meta.Sym.Simp.Result
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
lean_object* l_Lean_Meta_Sym_Simp_Result_withContextDependent(lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_Meta_Sym_Simp_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Simproc_andThen(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Simproc_andThen___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instAndThenSimproc___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instAndThenSimproc___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Sym_Simp_instAndThenSimproc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_instAndThenSimproc___lam__0___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Simp_instAndThenSimproc___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Simp_instAndThenSimproc___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_Simp_instAndThenSimproc = (const lean_object*)&l_Lean_Meta_Sym_Simp_instAndThenSimproc___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Simproc_orElse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Simproc_orElse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instOrElseSimproc___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instOrElseSimproc___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Sym_Simp_instOrElseSimproc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_instOrElseSimproc___lam__0___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Simp_instOrElseSimproc___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Simp_instOrElseSimproc___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_Simp_instOrElseSimproc = (const lean_object*)&l_Lean_Meta_Sym_Simp_instOrElseSimproc___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Simproc_tryCatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Simproc_tryCatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Simproc_andThen(lean_object* v_f_1_, lean_object* v_g_2_, lean_object* v_e_u2081_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_){
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
lean_inc_ref(v_a_5_);
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
if (v_done_16_ == 0)
{
uint8_t v_contextDependent_17_; lean_object* v___x_18_; 
lean_dec_ref_known(v___x_14_, 1);
v_contextDependent_17_ = lean_ctor_get_uint8(v_a_15_, 1);
lean_dec_ref_known(v_a_15_, 0);
lean_inc(v_a_12_);
lean_inc_ref(v_a_11_);
lean_inc(v_a_10_);
lean_inc_ref(v_a_9_);
lean_inc(v_a_8_);
lean_inc_ref(v_a_7_);
lean_inc(v_a_6_);
lean_inc_ref(v_a_5_);
lean_inc(v_a_4_);
v___x_18_ = lean_apply_11(v_g_2_, v_e_u2081_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_, lean_box(0));
if (lean_obj_tag(v___x_18_) == 0)
{
lean_object* v_a_19_; uint8_t v___y_21_; 
v_a_19_ = lean_ctor_get(v___x_18_, 0);
lean_inc(v_a_19_);
if (v_contextDependent_17_ == 0)
{
lean_dec(v_a_19_);
return v___x_18_;
}
else
{
if (lean_obj_tag(v_a_19_) == 0)
{
uint8_t v_contextDependent_31_; uint8_t v___x_32_; 
v_contextDependent_31_ = lean_ctor_get_uint8(v_a_19_, 1);
v___x_32_ = lean_bool_not(v_contextDependent_31_);
v___y_21_ = v___x_32_;
goto v___jp_20_;
}
else
{
uint8_t v_contextDependent_33_; uint8_t v___x_34_; 
v_contextDependent_33_ = lean_ctor_get_uint8(v_a_19_, sizeof(void*)*2 + 1);
v___x_34_ = lean_bool_not(v_contextDependent_33_);
v___y_21_ = v___x_34_;
goto v___jp_20_;
}
}
v___jp_20_:
{
if (v___y_21_ == 0)
{
lean_dec(v_a_19_);
return v___x_18_;
}
else
{
lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_29_; 
v_isSharedCheck_29_ = !lean_is_exclusive(v___x_18_);
if (v_isSharedCheck_29_ == 0)
{
lean_object* v_unused_30_; 
v_unused_30_ = lean_ctor_get(v___x_18_, 0);
lean_dec(v_unused_30_);
v___x_23_ = v___x_18_;
v_isShared_24_ = v_isSharedCheck_29_;
goto v_resetjp_22_;
}
else
{
lean_dec(v___x_18_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_29_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v___x_25_; lean_object* v___x_27_; 
v___x_25_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_19_);
if (v_isShared_24_ == 0)
{
lean_ctor_set(v___x_23_, 0, v___x_25_);
v___x_27_ = v___x_23_;
goto v_reusejp_26_;
}
else
{
lean_object* v_reuseFailAlloc_28_; 
v_reuseFailAlloc_28_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_28_, 0, v___x_25_);
v___x_27_ = v_reuseFailAlloc_28_;
goto v_reusejp_26_;
}
v_reusejp_26_:
{
return v___x_27_;
}
}
}
}
}
else
{
return v___x_18_;
}
}
else
{
lean_dec_ref_known(v_a_15_, 0);
lean_dec_ref(v_e_u2081_3_);
lean_dec_ref(v_g_2_);
return v___x_14_;
}
}
else
{
uint8_t v_done_35_; 
v_done_35_ = lean_ctor_get_uint8(v_a_15_, sizeof(void*)*2);
if (v_done_35_ == 0)
{
lean_object* v_e_x27_36_; lean_object* v_proof_37_; uint8_t v_contextDependent_38_; lean_object* v___x_40_; uint8_t v_isShared_41_; uint8_t v_isSharedCheck_88_; 
lean_dec_ref_known(v___x_14_, 1);
v_e_x27_36_ = lean_ctor_get(v_a_15_, 0);
v_proof_37_ = lean_ctor_get(v_a_15_, 1);
v_contextDependent_38_ = lean_ctor_get_uint8(v_a_15_, sizeof(void*)*2 + 1);
v_isSharedCheck_88_ = !lean_is_exclusive(v_a_15_);
if (v_isSharedCheck_88_ == 0)
{
v___x_40_ = v_a_15_;
v_isShared_41_ = v_isSharedCheck_88_;
goto v_resetjp_39_;
}
else
{
lean_inc(v_proof_37_);
lean_inc(v_e_x27_36_);
lean_dec(v_a_15_);
v___x_40_ = lean_box(0);
v_isShared_41_ = v_isSharedCheck_88_;
goto v_resetjp_39_;
}
v_resetjp_39_:
{
lean_object* v___x_42_; 
lean_inc(v_a_12_);
lean_inc_ref(v_a_11_);
lean_inc(v_a_10_);
lean_inc_ref(v_a_9_);
lean_inc(v_a_8_);
lean_inc_ref(v_a_7_);
lean_inc(v_a_6_);
lean_inc_ref(v_a_5_);
lean_inc(v_a_4_);
lean_inc_ref(v_e_x27_36_);
v___x_42_ = lean_apply_11(v_g_2_, v_e_x27_36_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_, lean_box(0));
if (lean_obj_tag(v___x_42_) == 0)
{
lean_object* v_a_43_; lean_object* v___x_45_; uint8_t v_isShared_46_; uint8_t v_isSharedCheck_87_; 
v_a_43_ = lean_ctor_get(v___x_42_, 0);
v_isSharedCheck_87_ = !lean_is_exclusive(v___x_42_);
if (v_isSharedCheck_87_ == 0)
{
v___x_45_ = v___x_42_;
v_isShared_46_ = v_isSharedCheck_87_;
goto v_resetjp_44_;
}
else
{
lean_inc(v_a_43_);
lean_dec(v___x_42_);
v___x_45_ = lean_box(0);
v_isShared_46_ = v_isSharedCheck_87_;
goto v_resetjp_44_;
}
v_resetjp_44_:
{
if (lean_obj_tag(v_a_43_) == 0)
{
uint8_t v_done_47_; uint8_t v_contextDependent_48_; uint8_t v___y_50_; 
lean_dec_ref(v_e_u2081_3_);
v_done_47_ = lean_ctor_get_uint8(v_a_43_, 0);
v_contextDependent_48_ = lean_ctor_get_uint8(v_a_43_, 1);
lean_dec_ref_known(v_a_43_, 0);
if (v_contextDependent_38_ == 0)
{
v___y_50_ = v_contextDependent_48_;
goto v___jp_49_;
}
else
{
v___y_50_ = v_contextDependent_38_;
goto v___jp_49_;
}
v___jp_49_:
{
lean_object* v___x_52_; 
if (v_isShared_41_ == 0)
{
v___x_52_ = v___x_40_;
goto v_reusejp_51_;
}
else
{
lean_object* v_reuseFailAlloc_56_; 
v_reuseFailAlloc_56_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_56_, 0, v_e_x27_36_);
lean_ctor_set(v_reuseFailAlloc_56_, 1, v_proof_37_);
v___x_52_ = v_reuseFailAlloc_56_;
goto v_reusejp_51_;
}
v_reusejp_51_:
{
lean_object* v___x_54_; 
lean_ctor_set_uint8(v___x_52_, sizeof(void*)*2, v_done_47_);
lean_ctor_set_uint8(v___x_52_, sizeof(void*)*2 + 1, v___y_50_);
if (v_isShared_46_ == 0)
{
lean_ctor_set(v___x_45_, 0, v___x_52_);
v___x_54_ = v___x_45_;
goto v_reusejp_53_;
}
else
{
lean_object* v_reuseFailAlloc_55_; 
v_reuseFailAlloc_55_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_55_, 0, v___x_52_);
v___x_54_ = v_reuseFailAlloc_55_;
goto v_reusejp_53_;
}
v_reusejp_53_:
{
return v___x_54_;
}
}
}
}
else
{
lean_object* v_e_x27_57_; lean_object* v_proof_58_; uint8_t v_done_59_; uint8_t v_contextDependent_60_; lean_object* v___x_62_; uint8_t v_isShared_63_; uint8_t v_isSharedCheck_86_; 
lean_del_object(v___x_45_);
lean_del_object(v___x_40_);
v_e_x27_57_ = lean_ctor_get(v_a_43_, 0);
v_proof_58_ = lean_ctor_get(v_a_43_, 1);
v_done_59_ = lean_ctor_get_uint8(v_a_43_, sizeof(void*)*2);
v_contextDependent_60_ = lean_ctor_get_uint8(v_a_43_, sizeof(void*)*2 + 1);
v_isSharedCheck_86_ = !lean_is_exclusive(v_a_43_);
if (v_isSharedCheck_86_ == 0)
{
v___x_62_ = v_a_43_;
v_isShared_63_ = v_isSharedCheck_86_;
goto v_resetjp_61_;
}
else
{
lean_inc(v_proof_58_);
lean_inc(v_e_x27_57_);
lean_dec(v_a_43_);
v___x_62_ = lean_box(0);
v_isShared_63_ = v_isSharedCheck_86_;
goto v_resetjp_61_;
}
v_resetjp_61_:
{
lean_object* v___x_64_; 
lean_inc_ref(v_e_x27_57_);
v___x_64_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v_e_u2081_3_, v_e_x27_36_, v_proof_37_, v_e_x27_57_, v_proof_58_, v_a_7_, v_a_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_);
if (lean_obj_tag(v___x_64_) == 0)
{
lean_object* v_a_65_; lean_object* v___x_67_; uint8_t v_isShared_68_; uint8_t v_isSharedCheck_77_; 
v_a_65_ = lean_ctor_get(v___x_64_, 0);
v_isSharedCheck_77_ = !lean_is_exclusive(v___x_64_);
if (v_isSharedCheck_77_ == 0)
{
v___x_67_ = v___x_64_;
v_isShared_68_ = v_isSharedCheck_77_;
goto v_resetjp_66_;
}
else
{
lean_inc(v_a_65_);
lean_dec(v___x_64_);
v___x_67_ = lean_box(0);
v_isShared_68_ = v_isSharedCheck_77_;
goto v_resetjp_66_;
}
v_resetjp_66_:
{
uint8_t v___y_70_; 
if (v_contextDependent_38_ == 0)
{
v___y_70_ = v_contextDependent_60_;
goto v___jp_69_;
}
else
{
v___y_70_ = v_contextDependent_38_;
goto v___jp_69_;
}
v___jp_69_:
{
lean_object* v___x_72_; 
if (v_isShared_63_ == 0)
{
lean_ctor_set(v___x_62_, 1, v_a_65_);
v___x_72_ = v___x_62_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_76_; 
v_reuseFailAlloc_76_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_76_, 0, v_e_x27_57_);
lean_ctor_set(v_reuseFailAlloc_76_, 1, v_a_65_);
lean_ctor_set_uint8(v_reuseFailAlloc_76_, sizeof(void*)*2, v_done_59_);
v___x_72_ = v_reuseFailAlloc_76_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
lean_object* v___x_74_; 
lean_ctor_set_uint8(v___x_72_, sizeof(void*)*2 + 1, v___y_70_);
if (v_isShared_68_ == 0)
{
lean_ctor_set(v___x_67_, 0, v___x_72_);
v___x_74_ = v___x_67_;
goto v_reusejp_73_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v___x_72_);
v___x_74_ = v_reuseFailAlloc_75_;
goto v_reusejp_73_;
}
v_reusejp_73_:
{
return v___x_74_;
}
}
}
}
}
else
{
lean_object* v_a_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_85_; 
lean_del_object(v___x_62_);
lean_dec_ref(v_e_x27_57_);
v_a_78_ = lean_ctor_get(v___x_64_, 0);
v_isSharedCheck_85_ = !lean_is_exclusive(v___x_64_);
if (v_isSharedCheck_85_ == 0)
{
v___x_80_ = v___x_64_;
v_isShared_81_ = v_isSharedCheck_85_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_a_78_);
lean_dec(v___x_64_);
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
}
}
else
{
lean_del_object(v___x_40_);
lean_dec_ref(v_proof_37_);
lean_dec_ref(v_e_x27_36_);
lean_dec_ref(v_e_u2081_3_);
return v___x_42_;
}
}
}
else
{
lean_dec_ref_known(v_a_15_, 2);
lean_dec_ref(v_e_u2081_3_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Simproc_andThen___boxed(lean_object* v_f_89_, lean_object* v_g_90_, lean_object* v_e_u2081_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_Lean_Meta_Sym_Simp_Simproc_andThen(v_f_89_, v_g_90_, v_e_u2081_91_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_);
lean_dec(v_a_100_);
lean_dec_ref(v_a_99_);
lean_dec(v_a_98_);
lean_dec_ref(v_a_97_);
lean_dec(v_a_96_);
lean_dec_ref(v_a_95_);
lean_dec(v_a_94_);
lean_dec_ref(v_a_93_);
lean_dec(v_a_92_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instAndThenSimproc___lam__0(lean_object* v_f_103_, lean_object* v_g_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_){
_start:
{
lean_object* v___x_116_; 
lean_inc(v___y_114_);
lean_inc_ref(v___y_113_);
lean_inc(v___y_112_);
lean_inc_ref(v___y_111_);
lean_inc(v___y_110_);
lean_inc_ref(v___y_109_);
lean_inc(v___y_108_);
lean_inc_ref(v___y_107_);
lean_inc(v___y_106_);
lean_inc_ref(v___y_105_);
v___x_116_ = lean_apply_11(v_f_103_, v___y_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_, lean_box(0));
if (lean_obj_tag(v___x_116_) == 0)
{
lean_object* v_a_117_; lean_object* v___x_118_; 
v_a_117_ = lean_ctor_get(v___x_116_, 0);
lean_inc(v_a_117_);
v___x_118_ = lean_box(0);
if (lean_obj_tag(v_a_117_) == 0)
{
uint8_t v_done_119_; 
v_done_119_ = lean_ctor_get_uint8(v_a_117_, 0);
if (v_done_119_ == 0)
{
uint8_t v_contextDependent_120_; lean_object* v___x_121_; 
lean_dec_ref_known(v___x_116_, 1);
v_contextDependent_120_ = lean_ctor_get_uint8(v_a_117_, 1);
lean_dec_ref_known(v_a_117_, 0);
lean_inc(v___y_114_);
lean_inc_ref(v___y_113_);
lean_inc(v___y_112_);
lean_inc_ref(v___y_111_);
lean_inc(v___y_110_);
lean_inc_ref(v___y_109_);
lean_inc(v___y_108_);
lean_inc_ref(v___y_107_);
lean_inc(v___y_106_);
v___x_121_ = lean_apply_12(v_g_104_, v___x_118_, v___y_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_, lean_box(0));
if (lean_obj_tag(v___x_121_) == 0)
{
lean_object* v_a_122_; uint8_t v___y_124_; 
v_a_122_ = lean_ctor_get(v___x_121_, 0);
lean_inc(v_a_122_);
if (v_contextDependent_120_ == 0)
{
lean_dec(v_a_122_);
return v___x_121_;
}
else
{
if (lean_obj_tag(v_a_122_) == 0)
{
uint8_t v_contextDependent_134_; uint8_t v___x_135_; 
v_contextDependent_134_ = lean_ctor_get_uint8(v_a_122_, 1);
v___x_135_ = lean_bool_not(v_contextDependent_134_);
v___y_124_ = v___x_135_;
goto v___jp_123_;
}
else
{
uint8_t v_contextDependent_136_; uint8_t v___x_137_; 
v_contextDependent_136_ = lean_ctor_get_uint8(v_a_122_, sizeof(void*)*2 + 1);
v___x_137_ = lean_bool_not(v_contextDependent_136_);
v___y_124_ = v___x_137_;
goto v___jp_123_;
}
}
v___jp_123_:
{
if (v___y_124_ == 0)
{
lean_dec(v_a_122_);
return v___x_121_;
}
else
{
lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_132_; 
v_isSharedCheck_132_ = !lean_is_exclusive(v___x_121_);
if (v_isSharedCheck_132_ == 0)
{
lean_object* v_unused_133_; 
v_unused_133_ = lean_ctor_get(v___x_121_, 0);
lean_dec(v_unused_133_);
v___x_126_ = v___x_121_;
v_isShared_127_ = v_isSharedCheck_132_;
goto v_resetjp_125_;
}
else
{
lean_dec(v___x_121_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_132_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
lean_object* v___x_128_; lean_object* v___x_130_; 
v___x_128_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_122_);
if (v_isShared_127_ == 0)
{
lean_ctor_set(v___x_126_, 0, v___x_128_);
v___x_130_ = v___x_126_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v___x_128_);
v___x_130_ = v_reuseFailAlloc_131_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
return v___x_130_;
}
}
}
}
}
else
{
return v___x_121_;
}
}
else
{
lean_dec_ref_known(v_a_117_, 0);
lean_dec_ref(v___y_105_);
lean_dec_ref(v_g_104_);
return v___x_116_;
}
}
else
{
uint8_t v_done_138_; 
v_done_138_ = lean_ctor_get_uint8(v_a_117_, sizeof(void*)*2);
if (v_done_138_ == 0)
{
lean_object* v_e_x27_139_; lean_object* v_proof_140_; uint8_t v_contextDependent_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_191_; 
lean_dec_ref_known(v___x_116_, 1);
v_e_x27_139_ = lean_ctor_get(v_a_117_, 0);
v_proof_140_ = lean_ctor_get(v_a_117_, 1);
v_contextDependent_141_ = lean_ctor_get_uint8(v_a_117_, sizeof(void*)*2 + 1);
v_isSharedCheck_191_ = !lean_is_exclusive(v_a_117_);
if (v_isSharedCheck_191_ == 0)
{
v___x_143_ = v_a_117_;
v_isShared_144_ = v_isSharedCheck_191_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_proof_140_);
lean_inc(v_e_x27_139_);
lean_dec(v_a_117_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_191_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___x_145_; 
lean_inc(v___y_114_);
lean_inc_ref(v___y_113_);
lean_inc(v___y_112_);
lean_inc_ref(v___y_111_);
lean_inc(v___y_110_);
lean_inc_ref(v___y_109_);
lean_inc(v___y_108_);
lean_inc_ref(v___y_107_);
lean_inc(v___y_106_);
lean_inc_ref(v_e_x27_139_);
v___x_145_ = lean_apply_12(v_g_104_, v___x_118_, v_e_x27_139_, v___y_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_, lean_box(0));
if (lean_obj_tag(v___x_145_) == 0)
{
lean_object* v_a_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_190_; 
v_a_146_ = lean_ctor_get(v___x_145_, 0);
v_isSharedCheck_190_ = !lean_is_exclusive(v___x_145_);
if (v_isSharedCheck_190_ == 0)
{
v___x_148_ = v___x_145_;
v_isShared_149_ = v_isSharedCheck_190_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_a_146_);
lean_dec(v___x_145_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_190_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
if (lean_obj_tag(v_a_146_) == 0)
{
uint8_t v_done_150_; uint8_t v_contextDependent_151_; uint8_t v___y_153_; 
lean_dec_ref(v___y_105_);
v_done_150_ = lean_ctor_get_uint8(v_a_146_, 0);
v_contextDependent_151_ = lean_ctor_get_uint8(v_a_146_, 1);
lean_dec_ref_known(v_a_146_, 0);
if (v_contextDependent_141_ == 0)
{
v___y_153_ = v_contextDependent_151_;
goto v___jp_152_;
}
else
{
v___y_153_ = v_contextDependent_141_;
goto v___jp_152_;
}
v___jp_152_:
{
lean_object* v___x_155_; 
if (v_isShared_144_ == 0)
{
v___x_155_ = v___x_143_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v_e_x27_139_);
lean_ctor_set(v_reuseFailAlloc_159_, 1, v_proof_140_);
v___x_155_ = v_reuseFailAlloc_159_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
lean_object* v___x_157_; 
lean_ctor_set_uint8(v___x_155_, sizeof(void*)*2, v_done_150_);
lean_ctor_set_uint8(v___x_155_, sizeof(void*)*2 + 1, v___y_153_);
if (v_isShared_149_ == 0)
{
lean_ctor_set(v___x_148_, 0, v___x_155_);
v___x_157_ = v___x_148_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v___x_155_);
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
else
{
lean_object* v_e_x27_160_; lean_object* v_proof_161_; uint8_t v_done_162_; uint8_t v_contextDependent_163_; lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_189_; 
lean_del_object(v___x_148_);
lean_del_object(v___x_143_);
v_e_x27_160_ = lean_ctor_get(v_a_146_, 0);
v_proof_161_ = lean_ctor_get(v_a_146_, 1);
v_done_162_ = lean_ctor_get_uint8(v_a_146_, sizeof(void*)*2);
v_contextDependent_163_ = lean_ctor_get_uint8(v_a_146_, sizeof(void*)*2 + 1);
v_isSharedCheck_189_ = !lean_is_exclusive(v_a_146_);
if (v_isSharedCheck_189_ == 0)
{
v___x_165_ = v_a_146_;
v_isShared_166_ = v_isSharedCheck_189_;
goto v_resetjp_164_;
}
else
{
lean_inc(v_proof_161_);
lean_inc(v_e_x27_160_);
lean_dec(v_a_146_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_189_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
lean_object* v___x_167_; 
lean_inc_ref(v_e_x27_160_);
v___x_167_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_105_, v_e_x27_139_, v_proof_140_, v_e_x27_160_, v_proof_161_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_);
if (lean_obj_tag(v___x_167_) == 0)
{
lean_object* v_a_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_180_; 
v_a_168_ = lean_ctor_get(v___x_167_, 0);
v_isSharedCheck_180_ = !lean_is_exclusive(v___x_167_);
if (v_isSharedCheck_180_ == 0)
{
v___x_170_ = v___x_167_;
v_isShared_171_ = v_isSharedCheck_180_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_a_168_);
lean_dec(v___x_167_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_180_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
uint8_t v___y_173_; 
if (v_contextDependent_141_ == 0)
{
v___y_173_ = v_contextDependent_163_;
goto v___jp_172_;
}
else
{
v___y_173_ = v_contextDependent_141_;
goto v___jp_172_;
}
v___jp_172_:
{
lean_object* v___x_175_; 
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 1, v_a_168_);
v___x_175_ = v___x_165_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v_e_x27_160_);
lean_ctor_set(v_reuseFailAlloc_179_, 1, v_a_168_);
lean_ctor_set_uint8(v_reuseFailAlloc_179_, sizeof(void*)*2, v_done_162_);
v___x_175_ = v_reuseFailAlloc_179_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
lean_object* v___x_177_; 
lean_ctor_set_uint8(v___x_175_, sizeof(void*)*2 + 1, v___y_173_);
if (v_isShared_171_ == 0)
{
lean_ctor_set(v___x_170_, 0, v___x_175_);
v___x_177_ = v___x_170_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v___x_175_);
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
else
{
lean_object* v_a_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_188_; 
lean_del_object(v___x_165_);
lean_dec_ref(v_e_x27_160_);
v_a_181_ = lean_ctor_get(v___x_167_, 0);
v_isSharedCheck_188_ = !lean_is_exclusive(v___x_167_);
if (v_isSharedCheck_188_ == 0)
{
v___x_183_ = v___x_167_;
v_isShared_184_ = v_isSharedCheck_188_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_a_181_);
lean_dec(v___x_167_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_188_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___x_186_; 
if (v_isShared_184_ == 0)
{
v___x_186_ = v___x_183_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v_a_181_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
return v___x_186_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_143_);
lean_dec_ref(v_proof_140_);
lean_dec_ref(v_e_x27_139_);
lean_dec_ref(v___y_105_);
return v___x_145_;
}
}
}
else
{
lean_dec_ref_known(v_a_117_, 2);
lean_dec_ref(v___y_105_);
lean_dec_ref(v_g_104_);
return v___x_116_;
}
}
}
else
{
lean_dec_ref(v___y_105_);
lean_dec_ref(v_g_104_);
return v___x_116_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instAndThenSimproc___lam__0___boxed(lean_object* v_f_192_, lean_object* v_g_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_Lean_Meta_Sym_Simp_instAndThenSimproc___lam__0(v_f_192_, v_g_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_);
lean_dec(v___y_203_);
lean_dec_ref(v___y_202_);
lean_dec(v___y_201_);
lean_dec_ref(v___y_200_);
lean_dec(v___y_199_);
lean_dec_ref(v___y_198_);
lean_dec(v___y_197_);
lean_dec_ref(v___y_196_);
lean_dec(v___y_195_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Simproc_orElse(lean_object* v_f_208_, lean_object* v_g_209_, lean_object* v_e_u2081_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_){
_start:
{
lean_object* v___x_221_; 
lean_inc(v_a_219_);
lean_inc_ref(v_a_218_);
lean_inc(v_a_217_);
lean_inc_ref(v_a_216_);
lean_inc(v_a_215_);
lean_inc_ref(v_a_214_);
lean_inc(v_a_213_);
lean_inc_ref(v_a_212_);
lean_inc(v_a_211_);
lean_inc_ref(v_e_u2081_210_);
v___x_221_ = lean_apply_11(v_f_208_, v_e_u2081_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, lean_box(0));
if (lean_obj_tag(v___x_221_) == 0)
{
lean_object* v_a_222_; 
v_a_222_ = lean_ctor_get(v___x_221_, 0);
lean_inc(v_a_222_);
if (lean_obj_tag(v_a_222_) == 0)
{
uint8_t v_done_223_; 
v_done_223_ = lean_ctor_get_uint8(v_a_222_, 0);
if (v_done_223_ == 0)
{
uint8_t v_contextDependent_224_; lean_object* v___x_225_; 
lean_dec_ref_known(v___x_221_, 1);
v_contextDependent_224_ = lean_ctor_get_uint8(v_a_222_, 1);
lean_dec_ref_known(v_a_222_, 0);
lean_inc(v_a_219_);
lean_inc_ref(v_a_218_);
lean_inc(v_a_217_);
lean_inc_ref(v_a_216_);
lean_inc(v_a_215_);
lean_inc_ref(v_a_214_);
lean_inc(v_a_213_);
lean_inc_ref(v_a_212_);
lean_inc(v_a_211_);
v___x_225_ = lean_apply_11(v_g_209_, v_e_u2081_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, lean_box(0));
if (lean_obj_tag(v___x_225_) == 0)
{
lean_object* v_a_226_; uint8_t v___y_228_; 
v_a_226_ = lean_ctor_get(v___x_225_, 0);
lean_inc(v_a_226_);
if (v_contextDependent_224_ == 0)
{
lean_dec(v_a_226_);
return v___x_225_;
}
else
{
if (lean_obj_tag(v_a_226_) == 0)
{
uint8_t v_contextDependent_238_; uint8_t v___x_239_; 
v_contextDependent_238_ = lean_ctor_get_uint8(v_a_226_, 1);
v___x_239_ = lean_bool_not(v_contextDependent_238_);
v___y_228_ = v___x_239_;
goto v___jp_227_;
}
else
{
uint8_t v_contextDependent_240_; uint8_t v___x_241_; 
v_contextDependent_240_ = lean_ctor_get_uint8(v_a_226_, sizeof(void*)*2 + 1);
v___x_241_ = lean_bool_not(v_contextDependent_240_);
v___y_228_ = v___x_241_;
goto v___jp_227_;
}
}
v___jp_227_:
{
if (v___y_228_ == 0)
{
lean_dec(v_a_226_);
return v___x_225_;
}
else
{
lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_236_; 
v_isSharedCheck_236_ = !lean_is_exclusive(v___x_225_);
if (v_isSharedCheck_236_ == 0)
{
lean_object* v_unused_237_; 
v_unused_237_ = lean_ctor_get(v___x_225_, 0);
lean_dec(v_unused_237_);
v___x_230_ = v___x_225_;
v_isShared_231_ = v_isSharedCheck_236_;
goto v_resetjp_229_;
}
else
{
lean_dec(v___x_225_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_236_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___x_232_; lean_object* v___x_234_; 
v___x_232_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_226_);
if (v_isShared_231_ == 0)
{
lean_ctor_set(v___x_230_, 0, v___x_232_);
v___x_234_ = v___x_230_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v___x_232_);
v___x_234_ = v_reuseFailAlloc_235_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
return v___x_234_;
}
}
}
}
}
else
{
return v___x_225_;
}
}
else
{
lean_dec_ref_known(v_a_222_, 0);
lean_dec_ref(v_e_u2081_210_);
lean_dec_ref(v_g_209_);
return v___x_221_;
}
}
else
{
lean_dec_ref_known(v_a_222_, 2);
lean_dec_ref(v_e_u2081_210_);
lean_dec_ref(v_g_209_);
return v___x_221_;
}
}
else
{
lean_dec_ref(v_e_u2081_210_);
lean_dec_ref(v_g_209_);
return v___x_221_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Simproc_orElse___boxed(lean_object* v_f_242_, lean_object* v_g_243_, lean_object* v_e_u2081_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Lean_Meta_Sym_Simp_Simproc_orElse(v_f_242_, v_g_243_, v_e_u2081_244_, v_a_245_, v_a_246_, v_a_247_, v_a_248_, v_a_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_);
lean_dec(v_a_253_);
lean_dec_ref(v_a_252_);
lean_dec(v_a_251_);
lean_dec_ref(v_a_250_);
lean_dec(v_a_249_);
lean_dec_ref(v_a_248_);
lean_dec(v_a_247_);
lean_dec_ref(v_a_246_);
lean_dec(v_a_245_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instOrElseSimproc___lam__0(lean_object* v_f_256_, lean_object* v_g_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_){
_start:
{
lean_object* v___x_269_; 
lean_inc(v___y_267_);
lean_inc_ref(v___y_266_);
lean_inc(v___y_265_);
lean_inc_ref(v___y_264_);
lean_inc(v___y_263_);
lean_inc_ref(v___y_262_);
lean_inc(v___y_261_);
lean_inc_ref(v___y_260_);
lean_inc(v___y_259_);
lean_inc_ref(v___y_258_);
v___x_269_ = lean_apply_11(v_f_256_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_, lean_box(0));
if (lean_obj_tag(v___x_269_) == 0)
{
lean_object* v_a_270_; 
v_a_270_ = lean_ctor_get(v___x_269_, 0);
lean_inc(v_a_270_);
if (lean_obj_tag(v_a_270_) == 0)
{
uint8_t v_done_271_; 
v_done_271_ = lean_ctor_get_uint8(v_a_270_, 0);
if (v_done_271_ == 0)
{
uint8_t v_contextDependent_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
lean_dec_ref_known(v___x_269_, 1);
v_contextDependent_272_ = lean_ctor_get_uint8(v_a_270_, 1);
lean_dec_ref_known(v_a_270_, 0);
v___x_273_ = lean_box(0);
lean_inc(v___y_267_);
lean_inc_ref(v___y_266_);
lean_inc(v___y_265_);
lean_inc_ref(v___y_264_);
lean_inc(v___y_263_);
lean_inc_ref(v___y_262_);
lean_inc(v___y_261_);
lean_inc_ref(v___y_260_);
lean_inc(v___y_259_);
v___x_274_ = lean_apply_12(v_g_257_, v___x_273_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_, lean_box(0));
if (lean_obj_tag(v___x_274_) == 0)
{
lean_object* v_a_275_; uint8_t v___y_277_; 
v_a_275_ = lean_ctor_get(v___x_274_, 0);
lean_inc(v_a_275_);
if (v_contextDependent_272_ == 0)
{
lean_dec(v_a_275_);
return v___x_274_;
}
else
{
if (lean_obj_tag(v_a_275_) == 0)
{
uint8_t v_contextDependent_287_; uint8_t v___x_288_; 
v_contextDependent_287_ = lean_ctor_get_uint8(v_a_275_, 1);
v___x_288_ = lean_bool_not(v_contextDependent_287_);
v___y_277_ = v___x_288_;
goto v___jp_276_;
}
else
{
uint8_t v_contextDependent_289_; uint8_t v___x_290_; 
v_contextDependent_289_ = lean_ctor_get_uint8(v_a_275_, sizeof(void*)*2 + 1);
v___x_290_ = lean_bool_not(v_contextDependent_289_);
v___y_277_ = v___x_290_;
goto v___jp_276_;
}
}
v___jp_276_:
{
if (v___y_277_ == 0)
{
lean_dec(v_a_275_);
return v___x_274_;
}
else
{
lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_285_; 
v_isSharedCheck_285_ = !lean_is_exclusive(v___x_274_);
if (v_isSharedCheck_285_ == 0)
{
lean_object* v_unused_286_; 
v_unused_286_ = lean_ctor_get(v___x_274_, 0);
lean_dec(v_unused_286_);
v___x_279_ = v___x_274_;
v_isShared_280_ = v_isSharedCheck_285_;
goto v_resetjp_278_;
}
else
{
lean_dec(v___x_274_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_285_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___x_281_; lean_object* v___x_283_; 
v___x_281_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_275_);
if (v_isShared_280_ == 0)
{
lean_ctor_set(v___x_279_, 0, v___x_281_);
v___x_283_ = v___x_279_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v___x_281_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
}
}
else
{
return v___x_274_;
}
}
else
{
lean_dec_ref_known(v_a_270_, 0);
lean_dec_ref(v___y_258_);
lean_dec_ref(v_g_257_);
return v___x_269_;
}
}
else
{
lean_dec_ref_known(v_a_270_, 2);
lean_dec_ref(v___y_258_);
lean_dec_ref(v_g_257_);
return v___x_269_;
}
}
else
{
lean_dec_ref(v___y_258_);
lean_dec_ref(v_g_257_);
return v___x_269_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instOrElseSimproc___lam__0___boxed(lean_object* v_f_291_, lean_object* v_g_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Lean_Meta_Sym_Simp_instOrElseSimproc___lam__0(v_f_291_, v_g_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
lean_dec(v___y_300_);
lean_dec_ref(v___y_299_);
lean_dec(v___y_298_);
lean_dec_ref(v___y_297_);
lean_dec(v___y_296_);
lean_dec_ref(v___y_295_);
lean_dec(v___y_294_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Simproc_tryCatch(lean_object* v_f_307_, lean_object* v_e_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_){
_start:
{
lean_object* v___x_319_; 
lean_inc(v_a_317_);
lean_inc_ref(v_a_316_);
lean_inc(v_a_315_);
lean_inc_ref(v_a_314_);
lean_inc(v_a_313_);
lean_inc_ref(v_a_312_);
lean_inc(v_a_311_);
lean_inc_ref(v_a_310_);
lean_inc(v_a_309_);
v___x_319_ = lean_apply_11(v_f_307_, v_e_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_, v_a_314_, v_a_315_, v_a_316_, v_a_317_, lean_box(0));
if (lean_obj_tag(v___x_319_) == 0)
{
return v___x_319_;
}
else
{
lean_object* v_a_320_; uint8_t v___y_322_; uint8_t v___x_332_; 
v_a_320_ = lean_ctor_get(v___x_319_, 0);
lean_inc(v_a_320_);
v___x_332_ = l_Lean_Exception_isInterrupt(v_a_320_);
if (v___x_332_ == 0)
{
uint8_t v___x_333_; 
v___x_333_ = l_Lean_Exception_isRuntime(v_a_320_);
v___y_322_ = v___x_333_;
goto v___jp_321_;
}
else
{
lean_dec(v_a_320_);
v___y_322_ = v___x_332_;
goto v___jp_321_;
}
v___jp_321_:
{
if (v___y_322_ == 0)
{
lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_330_; 
v_isSharedCheck_330_ = !lean_is_exclusive(v___x_319_);
if (v_isSharedCheck_330_ == 0)
{
lean_object* v_unused_331_; 
v_unused_331_ = lean_ctor_get(v___x_319_, 0);
lean_dec(v_unused_331_);
v___x_324_ = v___x_319_;
v_isShared_325_ = v_isSharedCheck_330_;
goto v_resetjp_323_;
}
else
{
lean_dec(v___x_319_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_330_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_326_; lean_object* v___x_328_; 
v___x_326_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_326_, 0, v___y_322_);
lean_ctor_set_uint8(v___x_326_, 1, v___y_322_);
if (v_isShared_325_ == 0)
{
lean_ctor_set_tag(v___x_324_, 0);
lean_ctor_set(v___x_324_, 0, v___x_326_);
v___x_328_ = v___x_324_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v___x_326_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
return v___x_328_;
}
}
}
else
{
return v___x_319_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Simproc_tryCatch___boxed(lean_object* v_f_334_, lean_object* v_e_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Lean_Meta_Sym_Simp_Simproc_tryCatch(v_f_334_, v_e_335_, v_a_336_, v_a_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_);
lean_dec(v_a_344_);
lean_dec_ref(v_a_343_);
lean_dec(v_a_342_);
lean_dec_ref(v_a_341_);
lean_dec(v_a_340_);
lean_dec_ref(v_a_339_);
lean_dec(v_a_338_);
lean_dec_ref(v_a_337_);
lean_dec(v_a_336_);
return v_res_346_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Result(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Simproc(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Sym_Simp_Result(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_Simp_Simproc(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_Simp_Result(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_Simp_Simproc(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_Simp_Result(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_Simp_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_Simp_Simproc(builtin);
}
#ifdef __cplusplus
}
#endif

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
lean_object* l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v___x_14_);
v_contextDependent_17_ = lean_ctor_get_uint8(v_a_15_, 1);
lean_dec_ref(v_a_15_);
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
uint8_t v_contextDependent_31_; 
v_contextDependent_31_ = lean_ctor_get_uint8(v_a_19_, 1);
v___y_21_ = v_contextDependent_31_;
goto v___jp_20_;
}
else
{
uint8_t v_contextDependent_32_; 
v_contextDependent_32_ = lean_ctor_get_uint8(v_a_19_, sizeof(void*)*2 + 1);
v___y_21_ = v_contextDependent_32_;
goto v___jp_20_;
}
}
v___jp_20_:
{
if (v___y_21_ == 0)
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
else
{
lean_dec(v_a_19_);
return v___x_18_;
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
lean_dec_ref(v_a_15_);
lean_dec_ref(v_e_u2081_3_);
lean_dec_ref(v_g_2_);
return v___x_14_;
}
}
else
{
uint8_t v_done_33_; 
v_done_33_ = lean_ctor_get_uint8(v_a_15_, sizeof(void*)*2);
if (v_done_33_ == 0)
{
lean_object* v_e_x27_34_; lean_object* v_proof_35_; uint8_t v_contextDependent_36_; lean_object* v___x_38_; uint8_t v_isShared_39_; uint8_t v_isSharedCheck_86_; 
lean_dec_ref(v___x_14_);
v_e_x27_34_ = lean_ctor_get(v_a_15_, 0);
v_proof_35_ = lean_ctor_get(v_a_15_, 1);
v_contextDependent_36_ = lean_ctor_get_uint8(v_a_15_, sizeof(void*)*2 + 1);
v_isSharedCheck_86_ = !lean_is_exclusive(v_a_15_);
if (v_isSharedCheck_86_ == 0)
{
v___x_38_ = v_a_15_;
v_isShared_39_ = v_isSharedCheck_86_;
goto v_resetjp_37_;
}
else
{
lean_inc(v_proof_35_);
lean_inc(v_e_x27_34_);
lean_dec(v_a_15_);
v___x_38_ = lean_box(0);
v_isShared_39_ = v_isSharedCheck_86_;
goto v_resetjp_37_;
}
v_resetjp_37_:
{
lean_object* v___x_40_; 
lean_inc(v_a_12_);
lean_inc_ref(v_a_11_);
lean_inc(v_a_10_);
lean_inc_ref(v_a_9_);
lean_inc(v_a_8_);
lean_inc_ref(v_a_7_);
lean_inc(v_a_6_);
lean_inc_ref(v_a_5_);
lean_inc(v_a_4_);
lean_inc_ref(v_e_x27_34_);
v___x_40_ = lean_apply_11(v_g_2_, v_e_x27_34_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_, lean_box(0));
if (lean_obj_tag(v___x_40_) == 0)
{
lean_object* v_a_41_; lean_object* v___x_43_; uint8_t v_isShared_44_; uint8_t v_isSharedCheck_85_; 
v_a_41_ = lean_ctor_get(v___x_40_, 0);
v_isSharedCheck_85_ = !lean_is_exclusive(v___x_40_);
if (v_isSharedCheck_85_ == 0)
{
v___x_43_ = v___x_40_;
v_isShared_44_ = v_isSharedCheck_85_;
goto v_resetjp_42_;
}
else
{
lean_inc(v_a_41_);
lean_dec(v___x_40_);
v___x_43_ = lean_box(0);
v_isShared_44_ = v_isSharedCheck_85_;
goto v_resetjp_42_;
}
v_resetjp_42_:
{
if (lean_obj_tag(v_a_41_) == 0)
{
uint8_t v_done_45_; uint8_t v_contextDependent_46_; uint8_t v___y_48_; 
lean_dec_ref(v_e_u2081_3_);
v_done_45_ = lean_ctor_get_uint8(v_a_41_, 0);
v_contextDependent_46_ = lean_ctor_get_uint8(v_a_41_, 1);
lean_dec_ref(v_a_41_);
if (v_contextDependent_36_ == 0)
{
v___y_48_ = v_contextDependent_46_;
goto v___jp_47_;
}
else
{
v___y_48_ = v_contextDependent_36_;
goto v___jp_47_;
}
v___jp_47_:
{
lean_object* v___x_50_; 
if (v_isShared_39_ == 0)
{
v___x_50_ = v___x_38_;
goto v_reusejp_49_;
}
else
{
lean_object* v_reuseFailAlloc_54_; 
v_reuseFailAlloc_54_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_54_, 0, v_e_x27_34_);
lean_ctor_set(v_reuseFailAlloc_54_, 1, v_proof_35_);
v___x_50_ = v_reuseFailAlloc_54_;
goto v_reusejp_49_;
}
v_reusejp_49_:
{
lean_object* v___x_52_; 
lean_ctor_set_uint8(v___x_50_, sizeof(void*)*2, v_done_45_);
lean_ctor_set_uint8(v___x_50_, sizeof(void*)*2 + 1, v___y_48_);
if (v_isShared_44_ == 0)
{
lean_ctor_set(v___x_43_, 0, v___x_50_);
v___x_52_ = v___x_43_;
goto v_reusejp_51_;
}
else
{
lean_object* v_reuseFailAlloc_53_; 
v_reuseFailAlloc_53_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_53_, 0, v___x_50_);
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
else
{
lean_object* v_e_x27_55_; lean_object* v_proof_56_; uint8_t v_done_57_; uint8_t v_contextDependent_58_; lean_object* v___x_60_; uint8_t v_isShared_61_; uint8_t v_isSharedCheck_84_; 
lean_del_object(v___x_43_);
lean_del_object(v___x_38_);
v_e_x27_55_ = lean_ctor_get(v_a_41_, 0);
v_proof_56_ = lean_ctor_get(v_a_41_, 1);
v_done_57_ = lean_ctor_get_uint8(v_a_41_, sizeof(void*)*2);
v_contextDependent_58_ = lean_ctor_get_uint8(v_a_41_, sizeof(void*)*2 + 1);
v_isSharedCheck_84_ = !lean_is_exclusive(v_a_41_);
if (v_isSharedCheck_84_ == 0)
{
v___x_60_ = v_a_41_;
v_isShared_61_ = v_isSharedCheck_84_;
goto v_resetjp_59_;
}
else
{
lean_inc(v_proof_56_);
lean_inc(v_e_x27_55_);
lean_dec(v_a_41_);
v___x_60_ = lean_box(0);
v_isShared_61_ = v_isSharedCheck_84_;
goto v_resetjp_59_;
}
v_resetjp_59_:
{
lean_object* v___x_62_; 
lean_inc_ref(v_e_x27_55_);
v___x_62_ = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(v_e_u2081_3_, v_e_x27_34_, v_proof_35_, v_e_x27_55_, v_proof_56_, v_a_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_);
if (lean_obj_tag(v___x_62_) == 0)
{
lean_object* v_a_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_75_; 
v_a_63_ = lean_ctor_get(v___x_62_, 0);
v_isSharedCheck_75_ = !lean_is_exclusive(v___x_62_);
if (v_isSharedCheck_75_ == 0)
{
v___x_65_ = v___x_62_;
v_isShared_66_ = v_isSharedCheck_75_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_a_63_);
lean_dec(v___x_62_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_75_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
uint8_t v___y_68_; 
if (v_contextDependent_36_ == 0)
{
v___y_68_ = v_contextDependent_58_;
goto v___jp_67_;
}
else
{
v___y_68_ = v_contextDependent_36_;
goto v___jp_67_;
}
v___jp_67_:
{
lean_object* v___x_70_; 
if (v_isShared_61_ == 0)
{
lean_ctor_set(v___x_60_, 1, v_a_63_);
v___x_70_ = v___x_60_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v_e_x27_55_);
lean_ctor_set(v_reuseFailAlloc_74_, 1, v_a_63_);
lean_ctor_set_uint8(v_reuseFailAlloc_74_, sizeof(void*)*2, v_done_57_);
v___x_70_ = v_reuseFailAlloc_74_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
lean_object* v___x_72_; 
lean_ctor_set_uint8(v___x_70_, sizeof(void*)*2 + 1, v___y_68_);
if (v_isShared_66_ == 0)
{
lean_ctor_set(v___x_65_, 0, v___x_70_);
v___x_72_ = v___x_65_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v___x_70_);
v___x_72_ = v_reuseFailAlloc_73_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
return v___x_72_;
}
}
}
}
}
else
{
lean_object* v_a_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_83_; 
lean_del_object(v___x_60_);
lean_dec_ref(v_e_x27_55_);
v_a_76_ = lean_ctor_get(v___x_62_, 0);
v_isSharedCheck_83_ = !lean_is_exclusive(v___x_62_);
if (v_isSharedCheck_83_ == 0)
{
v___x_78_ = v___x_62_;
v_isShared_79_ = v_isSharedCheck_83_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_a_76_);
lean_dec(v___x_62_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_83_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
lean_object* v___x_81_; 
if (v_isShared_79_ == 0)
{
v___x_81_ = v___x_78_;
goto v_reusejp_80_;
}
else
{
lean_object* v_reuseFailAlloc_82_; 
v_reuseFailAlloc_82_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_82_, 0, v_a_76_);
v___x_81_ = v_reuseFailAlloc_82_;
goto v_reusejp_80_;
}
v_reusejp_80_:
{
return v___x_81_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_38_);
lean_dec_ref(v_proof_35_);
lean_dec_ref(v_e_x27_34_);
lean_dec_ref(v_e_u2081_3_);
return v___x_40_;
}
}
}
else
{
lean_dec_ref(v_a_15_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Simproc_andThen___boxed(lean_object* v_f_87_, lean_object* v_g_88_, lean_object* v_e_u2081_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Lean_Meta_Sym_Simp_Simproc_andThen(v_f_87_, v_g_88_, v_e_u2081_89_, v_a_90_, v_a_91_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_);
lean_dec(v_a_98_);
lean_dec_ref(v_a_97_);
lean_dec(v_a_96_);
lean_dec_ref(v_a_95_);
lean_dec(v_a_94_);
lean_dec_ref(v_a_93_);
lean_dec(v_a_92_);
lean_dec_ref(v_a_91_);
lean_dec(v_a_90_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instAndThenSimproc___lam__0(lean_object* v_f_101_, lean_object* v_g_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_){
_start:
{
lean_object* v___x_114_; 
lean_inc(v___y_112_);
lean_inc_ref(v___y_111_);
lean_inc(v___y_110_);
lean_inc_ref(v___y_109_);
lean_inc(v___y_108_);
lean_inc_ref(v___y_107_);
lean_inc(v___y_106_);
lean_inc_ref(v___y_105_);
lean_inc(v___y_104_);
lean_inc_ref(v___y_103_);
v___x_114_ = lean_apply_11(v_f_101_, v___y_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, lean_box(0));
if (lean_obj_tag(v___x_114_) == 0)
{
lean_object* v_a_115_; lean_object* v___x_116_; 
v_a_115_ = lean_ctor_get(v___x_114_, 0);
lean_inc(v_a_115_);
v___x_116_ = lean_box(0);
if (lean_obj_tag(v_a_115_) == 0)
{
uint8_t v_done_117_; 
v_done_117_ = lean_ctor_get_uint8(v_a_115_, 0);
if (v_done_117_ == 0)
{
uint8_t v_contextDependent_118_; lean_object* v___x_119_; 
lean_dec_ref(v___x_114_);
v_contextDependent_118_ = lean_ctor_get_uint8(v_a_115_, 1);
lean_dec_ref(v_a_115_);
lean_inc(v___y_112_);
lean_inc_ref(v___y_111_);
lean_inc(v___y_110_);
lean_inc_ref(v___y_109_);
lean_inc(v___y_108_);
lean_inc_ref(v___y_107_);
lean_inc(v___y_106_);
lean_inc_ref(v___y_105_);
lean_inc(v___y_104_);
v___x_119_ = lean_apply_12(v_g_102_, v___x_116_, v___y_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, lean_box(0));
if (lean_obj_tag(v___x_119_) == 0)
{
lean_object* v_a_120_; uint8_t v___y_122_; 
v_a_120_ = lean_ctor_get(v___x_119_, 0);
lean_inc(v_a_120_);
if (v_contextDependent_118_ == 0)
{
lean_dec(v_a_120_);
return v___x_119_;
}
else
{
if (lean_obj_tag(v_a_120_) == 0)
{
uint8_t v_contextDependent_132_; 
v_contextDependent_132_ = lean_ctor_get_uint8(v_a_120_, 1);
v___y_122_ = v_contextDependent_132_;
goto v___jp_121_;
}
else
{
uint8_t v_contextDependent_133_; 
v_contextDependent_133_ = lean_ctor_get_uint8(v_a_120_, sizeof(void*)*2 + 1);
v___y_122_ = v_contextDependent_133_;
goto v___jp_121_;
}
}
v___jp_121_:
{
if (v___y_122_ == 0)
{
lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_130_; 
v_isSharedCheck_130_ = !lean_is_exclusive(v___x_119_);
if (v_isSharedCheck_130_ == 0)
{
lean_object* v_unused_131_; 
v_unused_131_ = lean_ctor_get(v___x_119_, 0);
lean_dec(v_unused_131_);
v___x_124_ = v___x_119_;
v_isShared_125_ = v_isSharedCheck_130_;
goto v_resetjp_123_;
}
else
{
lean_dec(v___x_119_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_130_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___x_126_; lean_object* v___x_128_; 
v___x_126_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_120_);
if (v_isShared_125_ == 0)
{
lean_ctor_set(v___x_124_, 0, v___x_126_);
v___x_128_ = v___x_124_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v___x_126_);
v___x_128_ = v_reuseFailAlloc_129_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
return v___x_128_;
}
}
}
else
{
lean_dec(v_a_120_);
return v___x_119_;
}
}
}
else
{
return v___x_119_;
}
}
else
{
lean_dec_ref(v_a_115_);
lean_dec_ref(v___y_103_);
lean_dec_ref(v_g_102_);
return v___x_114_;
}
}
else
{
uint8_t v_done_134_; 
v_done_134_ = lean_ctor_get_uint8(v_a_115_, sizeof(void*)*2);
if (v_done_134_ == 0)
{
lean_object* v_e_x27_135_; lean_object* v_proof_136_; uint8_t v_contextDependent_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_187_; 
lean_dec_ref(v___x_114_);
v_e_x27_135_ = lean_ctor_get(v_a_115_, 0);
v_proof_136_ = lean_ctor_get(v_a_115_, 1);
v_contextDependent_137_ = lean_ctor_get_uint8(v_a_115_, sizeof(void*)*2 + 1);
v_isSharedCheck_187_ = !lean_is_exclusive(v_a_115_);
if (v_isSharedCheck_187_ == 0)
{
v___x_139_ = v_a_115_;
v_isShared_140_ = v_isSharedCheck_187_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_proof_136_);
lean_inc(v_e_x27_135_);
lean_dec(v_a_115_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_187_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
lean_object* v___x_141_; 
lean_inc(v___y_112_);
lean_inc_ref(v___y_111_);
lean_inc(v___y_110_);
lean_inc_ref(v___y_109_);
lean_inc(v___y_108_);
lean_inc_ref(v___y_107_);
lean_inc(v___y_106_);
lean_inc_ref(v___y_105_);
lean_inc(v___y_104_);
lean_inc_ref(v_e_x27_135_);
v___x_141_ = lean_apply_12(v_g_102_, v___x_116_, v_e_x27_135_, v___y_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, lean_box(0));
if (lean_obj_tag(v___x_141_) == 0)
{
lean_object* v_a_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_186_; 
v_a_142_ = lean_ctor_get(v___x_141_, 0);
v_isSharedCheck_186_ = !lean_is_exclusive(v___x_141_);
if (v_isSharedCheck_186_ == 0)
{
v___x_144_ = v___x_141_;
v_isShared_145_ = v_isSharedCheck_186_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_a_142_);
lean_dec(v___x_141_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_186_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
if (lean_obj_tag(v_a_142_) == 0)
{
uint8_t v_done_146_; uint8_t v_contextDependent_147_; uint8_t v___y_149_; 
lean_dec_ref(v___y_103_);
v_done_146_ = lean_ctor_get_uint8(v_a_142_, 0);
v_contextDependent_147_ = lean_ctor_get_uint8(v_a_142_, 1);
lean_dec_ref(v_a_142_);
if (v_contextDependent_137_ == 0)
{
v___y_149_ = v_contextDependent_147_;
goto v___jp_148_;
}
else
{
v___y_149_ = v_contextDependent_137_;
goto v___jp_148_;
}
v___jp_148_:
{
lean_object* v___x_151_; 
if (v_isShared_140_ == 0)
{
v___x_151_ = v___x_139_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v_e_x27_135_);
lean_ctor_set(v_reuseFailAlloc_155_, 1, v_proof_136_);
v___x_151_ = v_reuseFailAlloc_155_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
lean_object* v___x_153_; 
lean_ctor_set_uint8(v___x_151_, sizeof(void*)*2, v_done_146_);
lean_ctor_set_uint8(v___x_151_, sizeof(void*)*2 + 1, v___y_149_);
if (v_isShared_145_ == 0)
{
lean_ctor_set(v___x_144_, 0, v___x_151_);
v___x_153_ = v___x_144_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v___x_151_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
return v___x_153_;
}
}
}
}
else
{
lean_object* v_e_x27_156_; lean_object* v_proof_157_; uint8_t v_done_158_; uint8_t v_contextDependent_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_185_; 
lean_del_object(v___x_144_);
lean_del_object(v___x_139_);
v_e_x27_156_ = lean_ctor_get(v_a_142_, 0);
v_proof_157_ = lean_ctor_get(v_a_142_, 1);
v_done_158_ = lean_ctor_get_uint8(v_a_142_, sizeof(void*)*2);
v_contextDependent_159_ = lean_ctor_get_uint8(v_a_142_, sizeof(void*)*2 + 1);
v_isSharedCheck_185_ = !lean_is_exclusive(v_a_142_);
if (v_isSharedCheck_185_ == 0)
{
v___x_161_ = v_a_142_;
v_isShared_162_ = v_isSharedCheck_185_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_proof_157_);
lean_inc(v_e_x27_156_);
lean_dec(v_a_142_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_185_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___x_163_; 
lean_inc_ref(v_e_x27_156_);
v___x_163_ = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(v___y_103_, v_e_x27_135_, v_proof_136_, v_e_x27_156_, v_proof_157_, v___y_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_);
if (lean_obj_tag(v___x_163_) == 0)
{
lean_object* v_a_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_176_; 
v_a_164_ = lean_ctor_get(v___x_163_, 0);
v_isSharedCheck_176_ = !lean_is_exclusive(v___x_163_);
if (v_isSharedCheck_176_ == 0)
{
v___x_166_ = v___x_163_;
v_isShared_167_ = v_isSharedCheck_176_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_a_164_);
lean_dec(v___x_163_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_176_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
uint8_t v___y_169_; 
if (v_contextDependent_137_ == 0)
{
v___y_169_ = v_contextDependent_159_;
goto v___jp_168_;
}
else
{
v___y_169_ = v_contextDependent_137_;
goto v___jp_168_;
}
v___jp_168_:
{
lean_object* v___x_171_; 
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 1, v_a_164_);
v___x_171_ = v___x_161_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v_e_x27_156_);
lean_ctor_set(v_reuseFailAlloc_175_, 1, v_a_164_);
lean_ctor_set_uint8(v_reuseFailAlloc_175_, sizeof(void*)*2, v_done_158_);
v___x_171_ = v_reuseFailAlloc_175_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
lean_object* v___x_173_; 
lean_ctor_set_uint8(v___x_171_, sizeof(void*)*2 + 1, v___y_169_);
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 0, v___x_171_);
v___x_173_ = v___x_166_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v___x_171_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
return v___x_173_;
}
}
}
}
}
else
{
lean_object* v_a_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_184_; 
lean_del_object(v___x_161_);
lean_dec_ref(v_e_x27_156_);
v_a_177_ = lean_ctor_get(v___x_163_, 0);
v_isSharedCheck_184_ = !lean_is_exclusive(v___x_163_);
if (v_isSharedCheck_184_ == 0)
{
v___x_179_ = v___x_163_;
v_isShared_180_ = v_isSharedCheck_184_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_a_177_);
lean_dec(v___x_163_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_184_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v___x_182_; 
if (v_isShared_180_ == 0)
{
v___x_182_ = v___x_179_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v_a_177_);
v___x_182_ = v_reuseFailAlloc_183_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
return v___x_182_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_139_);
lean_dec_ref(v_proof_136_);
lean_dec_ref(v_e_x27_135_);
lean_dec_ref(v___y_103_);
return v___x_141_;
}
}
}
else
{
lean_dec_ref(v_a_115_);
lean_dec_ref(v___y_103_);
lean_dec_ref(v_g_102_);
return v___x_114_;
}
}
}
else
{
lean_dec_ref(v___y_103_);
lean_dec_ref(v_g_102_);
return v___x_114_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instAndThenSimproc___lam__0___boxed(lean_object* v_f_188_, lean_object* v_g_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Lean_Meta_Sym_Simp_instAndThenSimproc___lam__0(v_f_188_, v_g_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_);
lean_dec(v___y_199_);
lean_dec_ref(v___y_198_);
lean_dec(v___y_197_);
lean_dec_ref(v___y_196_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
lean_dec(v___y_193_);
lean_dec_ref(v___y_192_);
lean_dec(v___y_191_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Simproc_orElse(lean_object* v_f_204_, lean_object* v_g_205_, lean_object* v_e_u2081_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_){
_start:
{
lean_object* v___x_217_; 
lean_inc(v_a_215_);
lean_inc_ref(v_a_214_);
lean_inc(v_a_213_);
lean_inc_ref(v_a_212_);
lean_inc(v_a_211_);
lean_inc_ref(v_a_210_);
lean_inc(v_a_209_);
lean_inc_ref(v_a_208_);
lean_inc(v_a_207_);
lean_inc_ref(v_e_u2081_206_);
v___x_217_ = lean_apply_11(v_f_204_, v_e_u2081_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, lean_box(0));
if (lean_obj_tag(v___x_217_) == 0)
{
lean_object* v_a_218_; 
v_a_218_ = lean_ctor_get(v___x_217_, 0);
lean_inc(v_a_218_);
if (lean_obj_tag(v_a_218_) == 0)
{
uint8_t v_done_219_; 
v_done_219_ = lean_ctor_get_uint8(v_a_218_, 0);
if (v_done_219_ == 0)
{
uint8_t v_contextDependent_220_; lean_object* v___x_221_; 
lean_dec_ref(v___x_217_);
v_contextDependent_220_ = lean_ctor_get_uint8(v_a_218_, 1);
lean_dec_ref(v_a_218_);
lean_inc(v_a_215_);
lean_inc_ref(v_a_214_);
lean_inc(v_a_213_);
lean_inc_ref(v_a_212_);
lean_inc(v_a_211_);
lean_inc_ref(v_a_210_);
lean_inc(v_a_209_);
lean_inc_ref(v_a_208_);
lean_inc(v_a_207_);
v___x_221_ = lean_apply_11(v_g_205_, v_e_u2081_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, lean_box(0));
if (lean_obj_tag(v___x_221_) == 0)
{
lean_object* v_a_222_; uint8_t v___y_224_; 
v_a_222_ = lean_ctor_get(v___x_221_, 0);
lean_inc(v_a_222_);
if (v_contextDependent_220_ == 0)
{
lean_dec(v_a_222_);
return v___x_221_;
}
else
{
if (lean_obj_tag(v_a_222_) == 0)
{
uint8_t v_contextDependent_234_; 
v_contextDependent_234_ = lean_ctor_get_uint8(v_a_222_, 1);
v___y_224_ = v_contextDependent_234_;
goto v___jp_223_;
}
else
{
uint8_t v_contextDependent_235_; 
v_contextDependent_235_ = lean_ctor_get_uint8(v_a_222_, sizeof(void*)*2 + 1);
v___y_224_ = v_contextDependent_235_;
goto v___jp_223_;
}
}
v___jp_223_:
{
if (v___y_224_ == 0)
{
lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_232_; 
v_isSharedCheck_232_ = !lean_is_exclusive(v___x_221_);
if (v_isSharedCheck_232_ == 0)
{
lean_object* v_unused_233_; 
v_unused_233_ = lean_ctor_get(v___x_221_, 0);
lean_dec(v_unused_233_);
v___x_226_ = v___x_221_;
v_isShared_227_ = v_isSharedCheck_232_;
goto v_resetjp_225_;
}
else
{
lean_dec(v___x_221_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_232_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v___x_228_; lean_object* v___x_230_; 
v___x_228_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_222_);
if (v_isShared_227_ == 0)
{
lean_ctor_set(v___x_226_, 0, v___x_228_);
v___x_230_ = v___x_226_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v___x_228_);
v___x_230_ = v_reuseFailAlloc_231_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
return v___x_230_;
}
}
}
else
{
lean_dec(v_a_222_);
return v___x_221_;
}
}
}
else
{
return v___x_221_;
}
}
else
{
lean_dec_ref(v_a_218_);
lean_dec_ref(v_e_u2081_206_);
lean_dec_ref(v_g_205_);
return v___x_217_;
}
}
else
{
lean_dec_ref(v_a_218_);
lean_dec_ref(v_e_u2081_206_);
lean_dec_ref(v_g_205_);
return v___x_217_;
}
}
else
{
lean_dec_ref(v_e_u2081_206_);
lean_dec_ref(v_g_205_);
return v___x_217_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Simproc_orElse___boxed(lean_object* v_f_236_, lean_object* v_g_237_, lean_object* v_e_u2081_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l_Lean_Meta_Sym_Simp_Simproc_orElse(v_f_236_, v_g_237_, v_e_u2081_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_, v_a_245_, v_a_246_, v_a_247_);
lean_dec(v_a_247_);
lean_dec_ref(v_a_246_);
lean_dec(v_a_245_);
lean_dec_ref(v_a_244_);
lean_dec(v_a_243_);
lean_dec_ref(v_a_242_);
lean_dec(v_a_241_);
lean_dec_ref(v_a_240_);
lean_dec(v_a_239_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instOrElseSimproc___lam__0(lean_object* v_f_250_, lean_object* v_g_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_){
_start:
{
lean_object* v___x_263_; 
lean_inc(v___y_261_);
lean_inc_ref(v___y_260_);
lean_inc(v___y_259_);
lean_inc_ref(v___y_258_);
lean_inc(v___y_257_);
lean_inc_ref(v___y_256_);
lean_inc(v___y_255_);
lean_inc_ref(v___y_254_);
lean_inc(v___y_253_);
lean_inc_ref(v___y_252_);
v___x_263_ = lean_apply_11(v_f_250_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, lean_box(0));
if (lean_obj_tag(v___x_263_) == 0)
{
lean_object* v_a_264_; 
v_a_264_ = lean_ctor_get(v___x_263_, 0);
lean_inc(v_a_264_);
if (lean_obj_tag(v_a_264_) == 0)
{
uint8_t v_done_265_; 
v_done_265_ = lean_ctor_get_uint8(v_a_264_, 0);
if (v_done_265_ == 0)
{
uint8_t v_contextDependent_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
lean_dec_ref(v___x_263_);
v_contextDependent_266_ = lean_ctor_get_uint8(v_a_264_, 1);
lean_dec_ref(v_a_264_);
v___x_267_ = lean_box(0);
lean_inc(v___y_261_);
lean_inc_ref(v___y_260_);
lean_inc(v___y_259_);
lean_inc_ref(v___y_258_);
lean_inc(v___y_257_);
lean_inc_ref(v___y_256_);
lean_inc(v___y_255_);
lean_inc_ref(v___y_254_);
lean_inc(v___y_253_);
v___x_268_ = lean_apply_12(v_g_251_, v___x_267_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, lean_box(0));
if (lean_obj_tag(v___x_268_) == 0)
{
lean_object* v_a_269_; uint8_t v___y_271_; 
v_a_269_ = lean_ctor_get(v___x_268_, 0);
lean_inc(v_a_269_);
if (v_contextDependent_266_ == 0)
{
lean_dec(v_a_269_);
return v___x_268_;
}
else
{
if (lean_obj_tag(v_a_269_) == 0)
{
uint8_t v_contextDependent_281_; 
v_contextDependent_281_ = lean_ctor_get_uint8(v_a_269_, 1);
v___y_271_ = v_contextDependent_281_;
goto v___jp_270_;
}
else
{
uint8_t v_contextDependent_282_; 
v_contextDependent_282_ = lean_ctor_get_uint8(v_a_269_, sizeof(void*)*2 + 1);
v___y_271_ = v_contextDependent_282_;
goto v___jp_270_;
}
}
v___jp_270_:
{
if (v___y_271_ == 0)
{
lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_279_; 
v_isSharedCheck_279_ = !lean_is_exclusive(v___x_268_);
if (v_isSharedCheck_279_ == 0)
{
lean_object* v_unused_280_; 
v_unused_280_ = lean_ctor_get(v___x_268_, 0);
lean_dec(v_unused_280_);
v___x_273_ = v___x_268_;
v_isShared_274_ = v_isSharedCheck_279_;
goto v_resetjp_272_;
}
else
{
lean_dec(v___x_268_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_279_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v___x_275_; lean_object* v___x_277_; 
v___x_275_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_269_);
if (v_isShared_274_ == 0)
{
lean_ctor_set(v___x_273_, 0, v___x_275_);
v___x_277_ = v___x_273_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v___x_275_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
return v___x_277_;
}
}
}
else
{
lean_dec(v_a_269_);
return v___x_268_;
}
}
}
else
{
return v___x_268_;
}
}
else
{
lean_dec_ref(v_a_264_);
lean_dec_ref(v___y_252_);
lean_dec_ref(v_g_251_);
return v___x_263_;
}
}
else
{
lean_dec_ref(v_a_264_);
lean_dec_ref(v___y_252_);
lean_dec_ref(v_g_251_);
return v___x_263_;
}
}
else
{
lean_dec_ref(v___y_252_);
lean_dec_ref(v_g_251_);
return v___x_263_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instOrElseSimproc___lam__0___boxed(lean_object* v_f_283_, lean_object* v_g_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Lean_Meta_Sym_Simp_instOrElseSimproc___lam__0(v_f_283_, v_g_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_);
lean_dec(v___y_294_);
lean_dec_ref(v___y_293_);
lean_dec(v___y_292_);
lean_dec_ref(v___y_291_);
lean_dec(v___y_290_);
lean_dec_ref(v___y_289_);
lean_dec(v___y_288_);
lean_dec_ref(v___y_287_);
lean_dec(v___y_286_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Simproc_tryCatch(lean_object* v_f_299_, lean_object* v_e_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_){
_start:
{
lean_object* v___x_311_; 
lean_inc(v_a_309_);
lean_inc_ref(v_a_308_);
lean_inc(v_a_307_);
lean_inc_ref(v_a_306_);
lean_inc(v_a_305_);
lean_inc_ref(v_a_304_);
lean_inc(v_a_303_);
lean_inc_ref(v_a_302_);
lean_inc(v_a_301_);
v___x_311_ = lean_apply_11(v_f_299_, v_e_300_, v_a_301_, v_a_302_, v_a_303_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_, v_a_309_, lean_box(0));
if (lean_obj_tag(v___x_311_) == 0)
{
return v___x_311_;
}
else
{
lean_object* v_a_312_; uint8_t v___y_314_; uint8_t v___x_324_; 
v_a_312_ = lean_ctor_get(v___x_311_, 0);
lean_inc(v_a_312_);
v___x_324_ = l_Lean_Exception_isInterrupt(v_a_312_);
if (v___x_324_ == 0)
{
uint8_t v___x_325_; 
v___x_325_ = l_Lean_Exception_isRuntime(v_a_312_);
v___y_314_ = v___x_325_;
goto v___jp_313_;
}
else
{
lean_dec(v_a_312_);
v___y_314_ = v___x_324_;
goto v___jp_313_;
}
v___jp_313_:
{
if (v___y_314_ == 0)
{
lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_322_; 
v_isSharedCheck_322_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_322_ == 0)
{
lean_object* v_unused_323_; 
v_unused_323_ = lean_ctor_get(v___x_311_, 0);
lean_dec(v_unused_323_);
v___x_316_ = v___x_311_;
v_isShared_317_ = v_isSharedCheck_322_;
goto v_resetjp_315_;
}
else
{
lean_dec(v___x_311_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_322_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_318_; lean_object* v___x_320_; 
v___x_318_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_318_, 0, v___y_314_);
lean_ctor_set_uint8(v___x_318_, 1, v___y_314_);
if (v_isShared_317_ == 0)
{
lean_ctor_set_tag(v___x_316_, 0);
lean_ctor_set(v___x_316_, 0, v___x_318_);
v___x_320_ = v___x_316_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v___x_318_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
return v___x_320_;
}
}
}
else
{
return v___x_311_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Simproc_tryCatch___boxed(lean_object* v_f_326_, lean_object* v_e_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Lean_Meta_Sym_Simp_Simproc_tryCatch(v_f_326_, v_e_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_);
lean_dec(v_a_336_);
lean_dec_ref(v_a_335_);
lean_dec(v_a_334_);
lean_dec_ref(v_a_333_);
lean_dec(v_a_332_);
lean_dec_ref(v_a_331_);
lean_dec(v_a_330_);
lean_dec_ref(v_a_329_);
lean_dec(v_a_328_);
return v_res_338_;
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

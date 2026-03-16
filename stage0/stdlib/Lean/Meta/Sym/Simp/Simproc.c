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
lean_dec_ref(v_a_15_);
if (v_done_16_ == 0)
{
lean_object* v___x_17_; 
lean_dec_ref(v___x_14_);
v___x_17_ = lean_apply_11(v_g_2_, v_e_u2081_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_, lean_box(0));
return v___x_17_;
}
else
{
lean_dec(v_a_12_);
lean_dec_ref(v_a_11_);
lean_dec(v_a_10_);
lean_dec_ref(v_a_9_);
lean_dec(v_a_8_);
lean_dec_ref(v_a_7_);
lean_dec(v_a_6_);
lean_dec_ref(v_a_5_);
lean_dec(v_a_4_);
lean_dec_ref(v_e_u2081_3_);
lean_dec_ref(v_g_2_);
return v___x_14_;
}
}
else
{
uint8_t v_done_18_; 
v_done_18_ = lean_ctor_get_uint8(v_a_15_, sizeof(void*)*2);
if (v_done_18_ == 0)
{
lean_object* v_e_x27_19_; lean_object* v_proof_20_; lean_object* v___x_22_; uint8_t v_isShared_23_; uint8_t v_isSharedCheck_64_; 
lean_dec_ref(v___x_14_);
v_e_x27_19_ = lean_ctor_get(v_a_15_, 0);
v_proof_20_ = lean_ctor_get(v_a_15_, 1);
v_isSharedCheck_64_ = !lean_is_exclusive(v_a_15_);
if (v_isSharedCheck_64_ == 0)
{
v___x_22_ = v_a_15_;
v_isShared_23_ = v_isSharedCheck_64_;
goto v_resetjp_21_;
}
else
{
lean_inc(v_proof_20_);
lean_inc(v_e_x27_19_);
lean_dec(v_a_15_);
v___x_22_ = lean_box(0);
v_isShared_23_ = v_isSharedCheck_64_;
goto v_resetjp_21_;
}
v_resetjp_21_:
{
lean_object* v___x_24_; 
lean_inc(v_a_12_);
lean_inc_ref(v_a_11_);
lean_inc(v_a_10_);
lean_inc_ref(v_a_9_);
lean_inc(v_a_8_);
lean_inc_ref(v_e_x27_19_);
v___x_24_ = lean_apply_11(v_g_2_, v_e_x27_19_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_, lean_box(0));
if (lean_obj_tag(v___x_24_) == 0)
{
lean_object* v_a_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_63_; 
v_a_25_ = lean_ctor_get(v___x_24_, 0);
v_isSharedCheck_63_ = !lean_is_exclusive(v___x_24_);
if (v_isSharedCheck_63_ == 0)
{
v___x_27_ = v___x_24_;
v_isShared_28_ = v_isSharedCheck_63_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_a_25_);
lean_dec(v___x_24_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_63_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
if (lean_obj_tag(v_a_25_) == 0)
{
uint8_t v_done_29_; lean_object* v___x_31_; 
lean_dec(v_a_12_);
lean_dec_ref(v_a_11_);
lean_dec(v_a_10_);
lean_dec_ref(v_a_9_);
lean_dec(v_a_8_);
lean_dec_ref(v_e_u2081_3_);
v_done_29_ = lean_ctor_get_uint8(v_a_25_, 0);
lean_dec_ref(v_a_25_);
if (v_isShared_23_ == 0)
{
v___x_31_ = v___x_22_;
goto v_reusejp_30_;
}
else
{
lean_object* v_reuseFailAlloc_35_; 
v_reuseFailAlloc_35_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_35_, 0, v_e_x27_19_);
lean_ctor_set(v_reuseFailAlloc_35_, 1, v_proof_20_);
v___x_31_ = v_reuseFailAlloc_35_;
goto v_reusejp_30_;
}
v_reusejp_30_:
{
lean_object* v___x_33_; 
lean_ctor_set_uint8(v___x_31_, sizeof(void*)*2, v_done_29_);
if (v_isShared_28_ == 0)
{
lean_ctor_set(v___x_27_, 0, v___x_31_);
v___x_33_ = v___x_27_;
goto v_reusejp_32_;
}
else
{
lean_object* v_reuseFailAlloc_34_; 
v_reuseFailAlloc_34_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_34_, 0, v___x_31_);
v___x_33_ = v_reuseFailAlloc_34_;
goto v_reusejp_32_;
}
v_reusejp_32_:
{
return v___x_33_;
}
}
}
else
{
lean_object* v_e_x27_36_; lean_object* v_proof_37_; uint8_t v_done_38_; lean_object* v___x_40_; uint8_t v_isShared_41_; uint8_t v_isSharedCheck_62_; 
lean_del_object(v___x_27_);
lean_del_object(v___x_22_);
v_e_x27_36_ = lean_ctor_get(v_a_25_, 0);
v_proof_37_ = lean_ctor_get(v_a_25_, 1);
v_done_38_ = lean_ctor_get_uint8(v_a_25_, sizeof(void*)*2);
v_isSharedCheck_62_ = !lean_is_exclusive(v_a_25_);
if (v_isSharedCheck_62_ == 0)
{
v___x_40_ = v_a_25_;
v_isShared_41_ = v_isSharedCheck_62_;
goto v_resetjp_39_;
}
else
{
lean_inc(v_proof_37_);
lean_inc(v_e_x27_36_);
lean_dec(v_a_25_);
v___x_40_ = lean_box(0);
v_isShared_41_ = v_isSharedCheck_62_;
goto v_resetjp_39_;
}
v_resetjp_39_:
{
lean_object* v___x_42_; 
lean_inc_ref(v_e_x27_36_);
v___x_42_ = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(v_e_u2081_3_, v_e_x27_19_, v_proof_20_, v_e_x27_36_, v_proof_37_, v_a_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_);
lean_dec(v_a_8_);
if (lean_obj_tag(v___x_42_) == 0)
{
lean_object* v_a_43_; lean_object* v___x_45_; uint8_t v_isShared_46_; uint8_t v_isSharedCheck_53_; 
v_a_43_ = lean_ctor_get(v___x_42_, 0);
v_isSharedCheck_53_ = !lean_is_exclusive(v___x_42_);
if (v_isSharedCheck_53_ == 0)
{
v___x_45_ = v___x_42_;
v_isShared_46_ = v_isSharedCheck_53_;
goto v_resetjp_44_;
}
else
{
lean_inc(v_a_43_);
lean_dec(v___x_42_);
v___x_45_ = lean_box(0);
v_isShared_46_ = v_isSharedCheck_53_;
goto v_resetjp_44_;
}
v_resetjp_44_:
{
lean_object* v___x_48_; 
if (v_isShared_41_ == 0)
{
lean_ctor_set(v___x_40_, 1, v_a_43_);
v___x_48_ = v___x_40_;
goto v_reusejp_47_;
}
else
{
lean_object* v_reuseFailAlloc_52_; 
v_reuseFailAlloc_52_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_52_, 0, v_e_x27_36_);
lean_ctor_set(v_reuseFailAlloc_52_, 1, v_a_43_);
lean_ctor_set_uint8(v_reuseFailAlloc_52_, sizeof(void*)*2, v_done_38_);
v___x_48_ = v_reuseFailAlloc_52_;
goto v_reusejp_47_;
}
v_reusejp_47_:
{
lean_object* v___x_50_; 
if (v_isShared_46_ == 0)
{
lean_ctor_set(v___x_45_, 0, v___x_48_);
v___x_50_ = v___x_45_;
goto v_reusejp_49_;
}
else
{
lean_object* v_reuseFailAlloc_51_; 
v_reuseFailAlloc_51_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_51_, 0, v___x_48_);
v___x_50_ = v_reuseFailAlloc_51_;
goto v_reusejp_49_;
}
v_reusejp_49_:
{
return v___x_50_;
}
}
}
}
else
{
lean_object* v_a_54_; lean_object* v___x_56_; uint8_t v_isShared_57_; uint8_t v_isSharedCheck_61_; 
lean_del_object(v___x_40_);
lean_dec_ref(v_e_x27_36_);
v_a_54_ = lean_ctor_get(v___x_42_, 0);
v_isSharedCheck_61_ = !lean_is_exclusive(v___x_42_);
if (v_isSharedCheck_61_ == 0)
{
v___x_56_ = v___x_42_;
v_isShared_57_ = v_isSharedCheck_61_;
goto v_resetjp_55_;
}
else
{
lean_inc(v_a_54_);
lean_dec(v___x_42_);
v___x_56_ = lean_box(0);
v_isShared_57_ = v_isSharedCheck_61_;
goto v_resetjp_55_;
}
v_resetjp_55_:
{
lean_object* v___x_59_; 
if (v_isShared_57_ == 0)
{
v___x_59_ = v___x_56_;
goto v_reusejp_58_;
}
else
{
lean_object* v_reuseFailAlloc_60_; 
v_reuseFailAlloc_60_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_60_, 0, v_a_54_);
v___x_59_ = v_reuseFailAlloc_60_;
goto v_reusejp_58_;
}
v_reusejp_58_:
{
return v___x_59_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_22_);
lean_dec_ref(v_proof_20_);
lean_dec_ref(v_e_x27_19_);
lean_dec(v_a_12_);
lean_dec_ref(v_a_11_);
lean_dec(v_a_10_);
lean_dec_ref(v_a_9_);
lean_dec(v_a_8_);
lean_dec_ref(v_e_u2081_3_);
return v___x_24_;
}
}
}
else
{
lean_dec_ref(v_a_15_);
lean_dec(v_a_12_);
lean_dec_ref(v_a_11_);
lean_dec(v_a_10_);
lean_dec_ref(v_a_9_);
lean_dec(v_a_8_);
lean_dec_ref(v_a_7_);
lean_dec(v_a_6_);
lean_dec_ref(v_a_5_);
lean_dec(v_a_4_);
lean_dec_ref(v_e_u2081_3_);
lean_dec_ref(v_g_2_);
return v___x_14_;
}
}
}
else
{
lean_dec(v_a_12_);
lean_dec_ref(v_a_11_);
lean_dec(v_a_10_);
lean_dec_ref(v_a_9_);
lean_dec(v_a_8_);
lean_dec_ref(v_a_7_);
lean_dec(v_a_6_);
lean_dec_ref(v_a_5_);
lean_dec(v_a_4_);
lean_dec_ref(v_e_u2081_3_);
lean_dec_ref(v_g_2_);
return v___x_14_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Simproc_andThen___boxed(lean_object* v_f_65_, lean_object* v_g_66_, lean_object* v_e_u2081_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l_Lean_Meta_Sym_Simp_Simproc_andThen(v_f_65_, v_g_66_, v_e_u2081_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_, v_a_73_, v_a_74_, v_a_75_, v_a_76_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instAndThenSimproc___lam__0(lean_object* v_f_79_, lean_object* v_g_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_){
_start:
{
lean_object* v___x_92_; 
lean_inc(v___y_90_);
lean_inc_ref(v___y_89_);
lean_inc(v___y_88_);
lean_inc_ref(v___y_87_);
lean_inc(v___y_86_);
lean_inc_ref(v___y_85_);
lean_inc(v___y_84_);
lean_inc_ref(v___y_83_);
lean_inc(v___y_82_);
lean_inc_ref(v___y_81_);
v___x_92_ = lean_apply_11(v_f_79_, v___y_81_, v___y_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_, lean_box(0));
if (lean_obj_tag(v___x_92_) == 0)
{
lean_object* v_a_93_; lean_object* v___x_94_; 
v_a_93_ = lean_ctor_get(v___x_92_, 0);
lean_inc(v_a_93_);
v___x_94_ = lean_box(0);
if (lean_obj_tag(v_a_93_) == 0)
{
uint8_t v_done_95_; 
v_done_95_ = lean_ctor_get_uint8(v_a_93_, 0);
lean_dec_ref(v_a_93_);
if (v_done_95_ == 0)
{
lean_object* v___x_96_; 
lean_dec_ref(v___x_92_);
v___x_96_ = lean_apply_12(v_g_80_, v___x_94_, v___y_81_, v___y_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_, lean_box(0));
return v___x_96_;
}
else
{
lean_dec(v___y_90_);
lean_dec_ref(v___y_89_);
lean_dec(v___y_88_);
lean_dec_ref(v___y_87_);
lean_dec(v___y_86_);
lean_dec_ref(v___y_85_);
lean_dec(v___y_84_);
lean_dec_ref(v___y_83_);
lean_dec(v___y_82_);
lean_dec_ref(v___y_81_);
lean_dec_ref(v_g_80_);
return v___x_92_;
}
}
else
{
uint8_t v_done_97_; 
v_done_97_ = lean_ctor_get_uint8(v_a_93_, sizeof(void*)*2);
if (v_done_97_ == 0)
{
lean_object* v_e_x27_98_; lean_object* v_proof_99_; lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_143_; 
lean_dec_ref(v___x_92_);
v_e_x27_98_ = lean_ctor_get(v_a_93_, 0);
v_proof_99_ = lean_ctor_get(v_a_93_, 1);
v_isSharedCheck_143_ = !lean_is_exclusive(v_a_93_);
if (v_isSharedCheck_143_ == 0)
{
v___x_101_ = v_a_93_;
v_isShared_102_ = v_isSharedCheck_143_;
goto v_resetjp_100_;
}
else
{
lean_inc(v_proof_99_);
lean_inc(v_e_x27_98_);
lean_dec(v_a_93_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_143_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v___x_103_; 
lean_inc(v___y_90_);
lean_inc_ref(v___y_89_);
lean_inc(v___y_88_);
lean_inc_ref(v___y_87_);
lean_inc(v___y_86_);
lean_inc_ref(v_e_x27_98_);
v___x_103_ = lean_apply_12(v_g_80_, v___x_94_, v_e_x27_98_, v___y_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_, lean_box(0));
if (lean_obj_tag(v___x_103_) == 0)
{
lean_object* v_a_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_142_; 
v_a_104_ = lean_ctor_get(v___x_103_, 0);
v_isSharedCheck_142_ = !lean_is_exclusive(v___x_103_);
if (v_isSharedCheck_142_ == 0)
{
v___x_106_ = v___x_103_;
v_isShared_107_ = v_isSharedCheck_142_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_a_104_);
lean_dec(v___x_103_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_142_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
if (lean_obj_tag(v_a_104_) == 0)
{
uint8_t v_done_108_; lean_object* v___x_110_; 
lean_dec(v___y_90_);
lean_dec_ref(v___y_89_);
lean_dec(v___y_88_);
lean_dec_ref(v___y_87_);
lean_dec(v___y_86_);
lean_dec_ref(v___y_81_);
v_done_108_ = lean_ctor_get_uint8(v_a_104_, 0);
lean_dec_ref(v_a_104_);
if (v_isShared_102_ == 0)
{
v___x_110_ = v___x_101_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v_e_x27_98_);
lean_ctor_set(v_reuseFailAlloc_114_, 1, v_proof_99_);
v___x_110_ = v_reuseFailAlloc_114_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
lean_object* v___x_112_; 
lean_ctor_set_uint8(v___x_110_, sizeof(void*)*2, v_done_108_);
if (v_isShared_107_ == 0)
{
lean_ctor_set(v___x_106_, 0, v___x_110_);
v___x_112_ = v___x_106_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v___x_110_);
v___x_112_ = v_reuseFailAlloc_113_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
return v___x_112_;
}
}
}
else
{
lean_object* v_e_x27_115_; lean_object* v_proof_116_; uint8_t v_done_117_; lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_141_; 
lean_del_object(v___x_106_);
lean_del_object(v___x_101_);
v_e_x27_115_ = lean_ctor_get(v_a_104_, 0);
v_proof_116_ = lean_ctor_get(v_a_104_, 1);
v_done_117_ = lean_ctor_get_uint8(v_a_104_, sizeof(void*)*2);
v_isSharedCheck_141_ = !lean_is_exclusive(v_a_104_);
if (v_isSharedCheck_141_ == 0)
{
v___x_119_ = v_a_104_;
v_isShared_120_ = v_isSharedCheck_141_;
goto v_resetjp_118_;
}
else
{
lean_inc(v_proof_116_);
lean_inc(v_e_x27_115_);
lean_dec(v_a_104_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_141_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
lean_object* v___x_121_; 
lean_inc_ref(v_e_x27_115_);
v___x_121_ = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(v___y_81_, v_e_x27_98_, v_proof_99_, v_e_x27_115_, v_proof_116_, v___y_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_);
lean_dec(v___y_86_);
if (lean_obj_tag(v___x_121_) == 0)
{
lean_object* v_a_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_132_; 
v_a_122_ = lean_ctor_get(v___x_121_, 0);
v_isSharedCheck_132_ = !lean_is_exclusive(v___x_121_);
if (v_isSharedCheck_132_ == 0)
{
v___x_124_ = v___x_121_;
v_isShared_125_ = v_isSharedCheck_132_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_a_122_);
lean_dec(v___x_121_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_132_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___x_127_; 
if (v_isShared_120_ == 0)
{
lean_ctor_set(v___x_119_, 1, v_a_122_);
v___x_127_ = v___x_119_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v_e_x27_115_);
lean_ctor_set(v_reuseFailAlloc_131_, 1, v_a_122_);
lean_ctor_set_uint8(v_reuseFailAlloc_131_, sizeof(void*)*2, v_done_117_);
v___x_127_ = v_reuseFailAlloc_131_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
lean_object* v___x_129_; 
if (v_isShared_125_ == 0)
{
lean_ctor_set(v___x_124_, 0, v___x_127_);
v___x_129_ = v___x_124_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v___x_127_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
}
}
else
{
lean_object* v_a_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_140_; 
lean_del_object(v___x_119_);
lean_dec_ref(v_e_x27_115_);
v_a_133_ = lean_ctor_get(v___x_121_, 0);
v_isSharedCheck_140_ = !lean_is_exclusive(v___x_121_);
if (v_isSharedCheck_140_ == 0)
{
v___x_135_ = v___x_121_;
v_isShared_136_ = v_isSharedCheck_140_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_a_133_);
lean_dec(v___x_121_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_140_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v___x_138_; 
if (v_isShared_136_ == 0)
{
v___x_138_ = v___x_135_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v_a_133_);
v___x_138_ = v_reuseFailAlloc_139_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
return v___x_138_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_101_);
lean_dec_ref(v_proof_99_);
lean_dec_ref(v_e_x27_98_);
lean_dec(v___y_90_);
lean_dec_ref(v___y_89_);
lean_dec(v___y_88_);
lean_dec_ref(v___y_87_);
lean_dec(v___y_86_);
lean_dec_ref(v___y_81_);
return v___x_103_;
}
}
}
else
{
lean_dec_ref(v_a_93_);
lean_dec(v___y_90_);
lean_dec_ref(v___y_89_);
lean_dec(v___y_88_);
lean_dec_ref(v___y_87_);
lean_dec(v___y_86_);
lean_dec_ref(v___y_85_);
lean_dec(v___y_84_);
lean_dec_ref(v___y_83_);
lean_dec(v___y_82_);
lean_dec_ref(v___y_81_);
lean_dec_ref(v_g_80_);
return v___x_92_;
}
}
}
else
{
lean_dec(v___y_90_);
lean_dec_ref(v___y_89_);
lean_dec(v___y_88_);
lean_dec_ref(v___y_87_);
lean_dec(v___y_86_);
lean_dec_ref(v___y_85_);
lean_dec(v___y_84_);
lean_dec_ref(v___y_83_);
lean_dec(v___y_82_);
lean_dec_ref(v___y_81_);
lean_dec_ref(v_g_80_);
return v___x_92_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instAndThenSimproc___lam__0___boxed(lean_object* v_f_144_, lean_object* v_g_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_Lean_Meta_Sym_Simp_instAndThenSimproc___lam__0(v_f_144_, v_g_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Simproc_orElse(lean_object* v_f_160_, lean_object* v_g_161_, lean_object* v_e_u2081_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_){
_start:
{
lean_object* v___x_173_; 
lean_inc(v_a_171_);
lean_inc_ref(v_a_170_);
lean_inc(v_a_169_);
lean_inc_ref(v_a_168_);
lean_inc(v_a_167_);
lean_inc_ref(v_a_166_);
lean_inc(v_a_165_);
lean_inc_ref(v_a_164_);
lean_inc(v_a_163_);
lean_inc_ref(v_e_u2081_162_);
v___x_173_ = lean_apply_11(v_f_160_, v_e_u2081_162_, v_a_163_, v_a_164_, v_a_165_, v_a_166_, v_a_167_, v_a_168_, v_a_169_, v_a_170_, v_a_171_, lean_box(0));
if (lean_obj_tag(v___x_173_) == 0)
{
lean_object* v_a_174_; 
v_a_174_ = lean_ctor_get(v___x_173_, 0);
lean_inc(v_a_174_);
if (lean_obj_tag(v_a_174_) == 0)
{
uint8_t v_done_175_; 
v_done_175_ = lean_ctor_get_uint8(v_a_174_, 0);
lean_dec_ref(v_a_174_);
if (v_done_175_ == 0)
{
lean_object* v___x_176_; 
lean_dec_ref(v___x_173_);
v___x_176_ = lean_apply_11(v_g_161_, v_e_u2081_162_, v_a_163_, v_a_164_, v_a_165_, v_a_166_, v_a_167_, v_a_168_, v_a_169_, v_a_170_, v_a_171_, lean_box(0));
return v___x_176_;
}
else
{
lean_dec(v_a_171_);
lean_dec_ref(v_a_170_);
lean_dec(v_a_169_);
lean_dec_ref(v_a_168_);
lean_dec(v_a_167_);
lean_dec_ref(v_a_166_);
lean_dec(v_a_165_);
lean_dec_ref(v_a_164_);
lean_dec(v_a_163_);
lean_dec_ref(v_e_u2081_162_);
lean_dec_ref(v_g_161_);
return v___x_173_;
}
}
else
{
lean_dec_ref(v_a_174_);
lean_dec(v_a_171_);
lean_dec_ref(v_a_170_);
lean_dec(v_a_169_);
lean_dec_ref(v_a_168_);
lean_dec(v_a_167_);
lean_dec_ref(v_a_166_);
lean_dec(v_a_165_);
lean_dec_ref(v_a_164_);
lean_dec(v_a_163_);
lean_dec_ref(v_e_u2081_162_);
lean_dec_ref(v_g_161_);
return v___x_173_;
}
}
else
{
lean_dec(v_a_171_);
lean_dec_ref(v_a_170_);
lean_dec(v_a_169_);
lean_dec_ref(v_a_168_);
lean_dec(v_a_167_);
lean_dec_ref(v_a_166_);
lean_dec(v_a_165_);
lean_dec_ref(v_a_164_);
lean_dec(v_a_163_);
lean_dec_ref(v_e_u2081_162_);
lean_dec_ref(v_g_161_);
return v___x_173_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Simproc_orElse___boxed(lean_object* v_f_177_, lean_object* v_g_178_, lean_object* v_e_u2081_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l_Lean_Meta_Sym_Simp_Simproc_orElse(v_f_177_, v_g_178_, v_e_u2081_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_, v_a_184_, v_a_185_, v_a_186_, v_a_187_, v_a_188_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instOrElseSimproc___lam__0(lean_object* v_f_191_, lean_object* v_g_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_){
_start:
{
lean_object* v___x_204_; 
lean_inc(v___y_202_);
lean_inc_ref(v___y_201_);
lean_inc(v___y_200_);
lean_inc_ref(v___y_199_);
lean_inc(v___y_198_);
lean_inc_ref(v___y_197_);
lean_inc(v___y_196_);
lean_inc_ref(v___y_195_);
lean_inc(v___y_194_);
lean_inc_ref(v___y_193_);
v___x_204_ = lean_apply_11(v_f_191_, v___y_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_, v___y_200_, v___y_201_, v___y_202_, lean_box(0));
if (lean_obj_tag(v___x_204_) == 0)
{
lean_object* v_a_205_; 
v_a_205_ = lean_ctor_get(v___x_204_, 0);
lean_inc(v_a_205_);
if (lean_obj_tag(v_a_205_) == 0)
{
uint8_t v_done_206_; 
v_done_206_ = lean_ctor_get_uint8(v_a_205_, 0);
lean_dec_ref(v_a_205_);
if (v_done_206_ == 0)
{
lean_object* v___x_207_; lean_object* v___x_208_; 
lean_dec_ref(v___x_204_);
v___x_207_ = lean_box(0);
v___x_208_ = lean_apply_12(v_g_192_, v___x_207_, v___y_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_, v___y_200_, v___y_201_, v___y_202_, lean_box(0));
return v___x_208_;
}
else
{
lean_dec(v___y_202_);
lean_dec_ref(v___y_201_);
lean_dec(v___y_200_);
lean_dec_ref(v___y_199_);
lean_dec(v___y_198_);
lean_dec_ref(v___y_197_);
lean_dec(v___y_196_);
lean_dec_ref(v___y_195_);
lean_dec(v___y_194_);
lean_dec_ref(v___y_193_);
lean_dec_ref(v_g_192_);
return v___x_204_;
}
}
else
{
lean_dec_ref(v_a_205_);
lean_dec(v___y_202_);
lean_dec_ref(v___y_201_);
lean_dec(v___y_200_);
lean_dec_ref(v___y_199_);
lean_dec(v___y_198_);
lean_dec_ref(v___y_197_);
lean_dec(v___y_196_);
lean_dec_ref(v___y_195_);
lean_dec(v___y_194_);
lean_dec_ref(v___y_193_);
lean_dec_ref(v_g_192_);
return v___x_204_;
}
}
else
{
lean_dec(v___y_202_);
lean_dec_ref(v___y_201_);
lean_dec(v___y_200_);
lean_dec_ref(v___y_199_);
lean_dec(v___y_198_);
lean_dec_ref(v___y_197_);
lean_dec(v___y_196_);
lean_dec_ref(v___y_195_);
lean_dec(v___y_194_);
lean_dec_ref(v___y_193_);
lean_dec_ref(v_g_192_);
return v___x_204_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instOrElseSimproc___lam__0___boxed(lean_object* v_f_209_, lean_object* v_g_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Lean_Meta_Sym_Simp_instOrElseSimproc___lam__0(v_f_209_, v_g_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Simproc_tryCatch(lean_object* v_f_225_, lean_object* v_e_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = lean_apply_11(v_f_225_, v_e_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_, v_a_231_, v_a_232_, v_a_233_, v_a_234_, v_a_235_, lean_box(0));
if (lean_obj_tag(v___x_237_) == 0)
{
return v___x_237_;
}
else
{
lean_object* v_a_238_; uint8_t v___y_240_; uint8_t v___x_250_; 
v_a_238_ = lean_ctor_get(v___x_237_, 0);
lean_inc(v_a_238_);
v___x_250_ = l_Lean_Exception_isInterrupt(v_a_238_);
if (v___x_250_ == 0)
{
uint8_t v___x_251_; 
v___x_251_ = l_Lean_Exception_isRuntime(v_a_238_);
v___y_240_ = v___x_251_;
goto v___jp_239_;
}
else
{
lean_dec(v_a_238_);
v___y_240_ = v___x_250_;
goto v___jp_239_;
}
v___jp_239_:
{
if (v___y_240_ == 0)
{
lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_248_; 
v_isSharedCheck_248_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_248_ == 0)
{
lean_object* v_unused_249_; 
v_unused_249_ = lean_ctor_get(v___x_237_, 0);
lean_dec(v_unused_249_);
v___x_242_ = v___x_237_;
v_isShared_243_ = v_isSharedCheck_248_;
goto v_resetjp_241_;
}
else
{
lean_dec(v___x_237_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_248_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_244_; lean_object* v___x_246_; 
v___x_244_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_244_, 0, v___y_240_);
if (v_isShared_243_ == 0)
{
lean_ctor_set_tag(v___x_242_, 0);
lean_ctor_set(v___x_242_, 0, v___x_244_);
v___x_246_ = v___x_242_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v___x_244_);
v___x_246_ = v_reuseFailAlloc_247_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
return v___x_246_;
}
}
}
else
{
return v___x_237_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Simproc_tryCatch___boxed(lean_object* v_f_252_, lean_object* v_e_253_, lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Lean_Meta_Sym_Simp_Simproc_tryCatch(v_f_252_, v_e_253_, v_a_254_, v_a_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_);
return v_res_264_;
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

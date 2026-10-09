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
lean_object* l_Lean_Meta_Sym_Simp_Simproc_andThen(lean_object* v_f_1_, lean_object* v_g_2_, lean_object* v_e_u2081_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_){
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
lean_dec_ref_known(v_a_15_, 0);
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
lean_dec_ref_known(v___x_14_, 1);
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
lean_dec_ref_known(v_a_41_, 0);
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
v___x_62_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v_e_u2081_3_, v_e_x27_34_, v_proof_35_, v_e_x27_55_, v_proof_56_, v_a_7_, v_a_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_);
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
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_Simproc_andThen_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1_ = stack[0].m_obj;
lean_object* v_g_2_ = stack[1].m_obj;
lean_object* v_e_u2081_3_ = stack[2].m_obj;
lean_object* v_a_4_ = stack[3].m_obj;
lean_object* v_a_5_ = stack[4].m_obj;
lean_object* v_a_6_ = stack[5].m_obj;
lean_object* v_a_7_ = stack[6].m_obj;
lean_object* v_a_8_ = stack[7].m_obj;
lean_object* v_a_9_ = stack[8].m_obj;
lean_object* v_a_10_ = stack[9].m_obj;
lean_object* v_a_11_ = stack[10].m_obj;
lean_object* v_a_12_ = stack[11].m_obj;
lean_object* v_res_87_;
v_res_87_ = l_Lean_Meta_Sym_Simp_Simproc_andThen(v_f_1_, v_g_2_, v_e_u2081_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_);
stack->m_obj
 = v_res_87_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Simproc_andThen___boxed(lean_object* v_f_88_, lean_object* v_g_89_, lean_object* v_e_u2081_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l_Lean_Meta_Sym_Simp_Simproc_andThen(v_f_88_, v_g_89_, v_e_u2081_90_, v_a_91_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_);
lean_dec(v_a_99_);
lean_dec_ref(v_a_98_);
lean_dec(v_a_97_);
lean_dec_ref(v_a_96_);
lean_dec(v_a_95_);
lean_dec_ref(v_a_94_);
lean_dec(v_a_93_);
lean_dec_ref(v_a_92_);
lean_dec(v_a_91_);
return v_res_101_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_instAndThenSimproc___lam__0(lean_object* v_f_102_, lean_object* v_g_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_115_ = lean_box(0);
lean_inc(v___y_113_);
lean_inc_ref(v___y_112_);
lean_inc(v___y_111_);
lean_inc_ref(v___y_110_);
lean_inc(v___y_109_);
lean_inc_ref(v___y_108_);
lean_inc(v___y_107_);
lean_inc_ref(v___y_106_);
lean_inc(v___y_105_);
lean_inc_ref(v___y_104_);
v___x_116_ = lean_apply_11(v_f_102_, v___y_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_, lean_box(0));
if (lean_obj_tag(v___x_116_) == 0)
{
lean_object* v_a_117_; 
v_a_117_ = lean_ctor_get(v___x_116_, 0);
lean_inc(v_a_117_);
if (lean_obj_tag(v_a_117_) == 0)
{
uint8_t v_done_118_; 
v_done_118_ = lean_ctor_get_uint8(v_a_117_, 0);
if (v_done_118_ == 0)
{
uint8_t v_contextDependent_119_; lean_object* v___x_120_; 
lean_dec_ref_known(v___x_116_, 1);
v_contextDependent_119_ = lean_ctor_get_uint8(v_a_117_, 1);
lean_dec_ref_known(v_a_117_, 0);
lean_inc(v___y_113_);
lean_inc_ref(v___y_112_);
lean_inc(v___y_111_);
lean_inc_ref(v___y_110_);
lean_inc(v___y_109_);
lean_inc_ref(v___y_108_);
lean_inc(v___y_107_);
lean_inc_ref(v___y_106_);
lean_inc(v___y_105_);
v___x_120_ = lean_apply_12(v_g_103_, v___x_115_, v___y_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_, lean_box(0));
if (lean_obj_tag(v___x_120_) == 0)
{
lean_object* v_a_121_; uint8_t v___y_123_; 
v_a_121_ = lean_ctor_get(v___x_120_, 0);
lean_inc(v_a_121_);
if (v_contextDependent_119_ == 0)
{
lean_dec(v_a_121_);
return v___x_120_;
}
else
{
if (lean_obj_tag(v_a_121_) == 0)
{
uint8_t v_contextDependent_133_; 
v_contextDependent_133_ = lean_ctor_get_uint8(v_a_121_, 1);
v___y_123_ = v_contextDependent_133_;
goto v___jp_122_;
}
else
{
uint8_t v_contextDependent_134_; 
v_contextDependent_134_ = lean_ctor_get_uint8(v_a_121_, sizeof(void*)*2 + 1);
v___y_123_ = v_contextDependent_134_;
goto v___jp_122_;
}
}
v___jp_122_:
{
if (v___y_123_ == 0)
{
lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_131_; 
v_isSharedCheck_131_ = !lean_is_exclusive(v___x_120_);
if (v_isSharedCheck_131_ == 0)
{
lean_object* v_unused_132_; 
v_unused_132_ = lean_ctor_get(v___x_120_, 0);
lean_dec(v_unused_132_);
v___x_125_ = v___x_120_;
v_isShared_126_ = v_isSharedCheck_131_;
goto v_resetjp_124_;
}
else
{
lean_dec(v___x_120_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_131_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_127_; lean_object* v___x_129_; 
v___x_127_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_121_);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 0, v___x_127_);
v___x_129_ = v___x_125_;
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
else
{
lean_dec(v_a_121_);
return v___x_120_;
}
}
}
else
{
return v___x_120_;
}
}
else
{
lean_dec_ref_known(v_a_117_, 0);
lean_dec_ref(v___y_104_);
lean_dec_ref(v_g_103_);
return v___x_116_;
}
}
else
{
uint8_t v_done_135_; 
v_done_135_ = lean_ctor_get_uint8(v_a_117_, sizeof(void*)*2);
if (v_done_135_ == 0)
{
lean_object* v_e_x27_136_; lean_object* v_proof_137_; uint8_t v_contextDependent_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_188_; 
lean_dec_ref_known(v___x_116_, 1);
v_e_x27_136_ = lean_ctor_get(v_a_117_, 0);
v_proof_137_ = lean_ctor_get(v_a_117_, 1);
v_contextDependent_138_ = lean_ctor_get_uint8(v_a_117_, sizeof(void*)*2 + 1);
v_isSharedCheck_188_ = !lean_is_exclusive(v_a_117_);
if (v_isSharedCheck_188_ == 0)
{
v___x_140_ = v_a_117_;
v_isShared_141_ = v_isSharedCheck_188_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_proof_137_);
lean_inc(v_e_x27_136_);
lean_dec(v_a_117_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_188_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_142_; 
lean_inc(v___y_113_);
lean_inc_ref(v___y_112_);
lean_inc(v___y_111_);
lean_inc_ref(v___y_110_);
lean_inc(v___y_109_);
lean_inc_ref(v___y_108_);
lean_inc(v___y_107_);
lean_inc_ref(v___y_106_);
lean_inc(v___y_105_);
lean_inc_ref(v_e_x27_136_);
v___x_142_ = lean_apply_12(v_g_103_, v___x_115_, v_e_x27_136_, v___y_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_, lean_box(0));
if (lean_obj_tag(v___x_142_) == 0)
{
lean_object* v_a_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_187_; 
v_a_143_ = lean_ctor_get(v___x_142_, 0);
v_isSharedCheck_187_ = !lean_is_exclusive(v___x_142_);
if (v_isSharedCheck_187_ == 0)
{
v___x_145_ = v___x_142_;
v_isShared_146_ = v_isSharedCheck_187_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_a_143_);
lean_dec(v___x_142_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_187_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
if (lean_obj_tag(v_a_143_) == 0)
{
uint8_t v_done_147_; uint8_t v_contextDependent_148_; uint8_t v___y_150_; 
lean_dec_ref(v___y_104_);
v_done_147_ = lean_ctor_get_uint8(v_a_143_, 0);
v_contextDependent_148_ = lean_ctor_get_uint8(v_a_143_, 1);
lean_dec_ref_known(v_a_143_, 0);
if (v_contextDependent_138_ == 0)
{
v___y_150_ = v_contextDependent_148_;
goto v___jp_149_;
}
else
{
v___y_150_ = v_contextDependent_138_;
goto v___jp_149_;
}
v___jp_149_:
{
lean_object* v___x_152_; 
if (v_isShared_141_ == 0)
{
v___x_152_ = v___x_140_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v_e_x27_136_);
lean_ctor_set(v_reuseFailAlloc_156_, 1, v_proof_137_);
v___x_152_ = v_reuseFailAlloc_156_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
lean_object* v___x_154_; 
lean_ctor_set_uint8(v___x_152_, sizeof(void*)*2, v_done_147_);
lean_ctor_set_uint8(v___x_152_, sizeof(void*)*2 + 1, v___y_150_);
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 0, v___x_152_);
v___x_154_ = v___x_145_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v___x_152_);
v___x_154_ = v_reuseFailAlloc_155_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
return v___x_154_;
}
}
}
}
else
{
lean_object* v_e_x27_157_; lean_object* v_proof_158_; uint8_t v_done_159_; uint8_t v_contextDependent_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_186_; 
lean_del_object(v___x_145_);
lean_del_object(v___x_140_);
v_e_x27_157_ = lean_ctor_get(v_a_143_, 0);
v_proof_158_ = lean_ctor_get(v_a_143_, 1);
v_done_159_ = lean_ctor_get_uint8(v_a_143_, sizeof(void*)*2);
v_contextDependent_160_ = lean_ctor_get_uint8(v_a_143_, sizeof(void*)*2 + 1);
v_isSharedCheck_186_ = !lean_is_exclusive(v_a_143_);
if (v_isSharedCheck_186_ == 0)
{
v___x_162_ = v_a_143_;
v_isShared_163_ = v_isSharedCheck_186_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_proof_158_);
lean_inc(v_e_x27_157_);
lean_dec(v_a_143_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_186_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___x_164_; 
lean_inc_ref(v_e_x27_157_);
v___x_164_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_104_, v_e_x27_136_, v_proof_137_, v_e_x27_157_, v_proof_158_, v___y_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_);
if (lean_obj_tag(v___x_164_) == 0)
{
lean_object* v_a_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_177_; 
v_a_165_ = lean_ctor_get(v___x_164_, 0);
v_isSharedCheck_177_ = !lean_is_exclusive(v___x_164_);
if (v_isSharedCheck_177_ == 0)
{
v___x_167_ = v___x_164_;
v_isShared_168_ = v_isSharedCheck_177_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_a_165_);
lean_dec(v___x_164_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_177_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
uint8_t v___y_170_; 
if (v_contextDependent_138_ == 0)
{
v___y_170_ = v_contextDependent_160_;
goto v___jp_169_;
}
else
{
v___y_170_ = v_contextDependent_138_;
goto v___jp_169_;
}
v___jp_169_:
{
lean_object* v___x_172_; 
if (v_isShared_163_ == 0)
{
lean_ctor_set(v___x_162_, 1, v_a_165_);
v___x_172_ = v___x_162_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v_e_x27_157_);
lean_ctor_set(v_reuseFailAlloc_176_, 1, v_a_165_);
lean_ctor_set_uint8(v_reuseFailAlloc_176_, sizeof(void*)*2, v_done_159_);
v___x_172_ = v_reuseFailAlloc_176_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
lean_object* v___x_174_; 
lean_ctor_set_uint8(v___x_172_, sizeof(void*)*2 + 1, v___y_170_);
if (v_isShared_168_ == 0)
{
lean_ctor_set(v___x_167_, 0, v___x_172_);
v___x_174_ = v___x_167_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v___x_172_);
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
else
{
lean_object* v_a_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_185_; 
lean_del_object(v___x_162_);
lean_dec_ref(v_e_x27_157_);
v_a_178_ = lean_ctor_get(v___x_164_, 0);
v_isSharedCheck_185_ = !lean_is_exclusive(v___x_164_);
if (v_isSharedCheck_185_ == 0)
{
v___x_180_ = v___x_164_;
v_isShared_181_ = v_isSharedCheck_185_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_a_178_);
lean_dec(v___x_164_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_185_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v___x_183_; 
if (v_isShared_181_ == 0)
{
v___x_183_ = v___x_180_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v_a_178_);
v___x_183_ = v_reuseFailAlloc_184_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
return v___x_183_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_140_);
lean_dec_ref(v_proof_137_);
lean_dec_ref(v_e_x27_136_);
lean_dec_ref(v___y_104_);
return v___x_142_;
}
}
}
else
{
lean_dec_ref_known(v_a_117_, 2);
lean_dec_ref(v___y_104_);
lean_dec_ref(v_g_103_);
return v___x_116_;
}
}
}
else
{
lean_dec_ref(v___y_104_);
lean_dec_ref(v_g_103_);
return v___x_116_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_instAndThenSimproc___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_102_ = stack[0].m_obj;
lean_object* v_g_103_ = stack[1].m_obj;
lean_object* v___y_104_ = stack[2].m_obj;
lean_object* v___y_105_ = stack[3].m_obj;
lean_object* v___y_106_ = stack[4].m_obj;
lean_object* v___y_107_ = stack[5].m_obj;
lean_object* v___y_108_ = stack[6].m_obj;
lean_object* v___y_109_ = stack[7].m_obj;
lean_object* v___y_110_ = stack[8].m_obj;
lean_object* v___y_111_ = stack[9].m_obj;
lean_object* v___y_112_ = stack[10].m_obj;
lean_object* v___y_113_ = stack[11].m_obj;
lean_object* v_res_189_;
v_res_189_ = l_Lean_Meta_Sym_Simp_instAndThenSimproc___lam__0(v_f_102_, v_g_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_);
stack->m_obj
 = v_res_189_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instAndThenSimproc___lam__0___boxed(lean_object* v_f_190_, lean_object* v_g_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l_Lean_Meta_Sym_Simp_instAndThenSimproc___lam__0(v_f_190_, v_g_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_, v___y_200_, v___y_201_);
lean_dec(v___y_201_);
lean_dec_ref(v___y_200_);
lean_dec(v___y_199_);
lean_dec_ref(v___y_198_);
lean_dec(v___y_197_);
lean_dec_ref(v___y_196_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
lean_dec(v___y_193_);
return v_res_203_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_Simproc_orElse(lean_object* v_f_206_, lean_object* v_g_207_, lean_object* v_e_u2081_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_){
_start:
{
lean_object* v___x_219_; 
lean_inc(v_a_217_);
lean_inc_ref(v_a_216_);
lean_inc(v_a_215_);
lean_inc_ref(v_a_214_);
lean_inc(v_a_213_);
lean_inc_ref(v_a_212_);
lean_inc(v_a_211_);
lean_inc_ref(v_a_210_);
lean_inc(v_a_209_);
lean_inc_ref(v_e_u2081_208_);
v___x_219_ = lean_apply_11(v_f_206_, v_e_u2081_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, lean_box(0));
if (lean_obj_tag(v___x_219_) == 0)
{
lean_object* v_a_220_; 
v_a_220_ = lean_ctor_get(v___x_219_, 0);
lean_inc(v_a_220_);
if (lean_obj_tag(v_a_220_) == 0)
{
uint8_t v_done_221_; 
v_done_221_ = lean_ctor_get_uint8(v_a_220_, 0);
if (v_done_221_ == 0)
{
uint8_t v_contextDependent_222_; lean_object* v___x_223_; 
lean_dec_ref_known(v___x_219_, 1);
v_contextDependent_222_ = lean_ctor_get_uint8(v_a_220_, 1);
lean_dec_ref_known(v_a_220_, 0);
lean_inc(v_a_217_);
lean_inc_ref(v_a_216_);
lean_inc(v_a_215_);
lean_inc_ref(v_a_214_);
lean_inc(v_a_213_);
lean_inc_ref(v_a_212_);
lean_inc(v_a_211_);
lean_inc_ref(v_a_210_);
lean_inc(v_a_209_);
v___x_223_ = lean_apply_11(v_g_207_, v_e_u2081_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, lean_box(0));
if (lean_obj_tag(v___x_223_) == 0)
{
lean_object* v_a_224_; uint8_t v___y_226_; 
v_a_224_ = lean_ctor_get(v___x_223_, 0);
lean_inc(v_a_224_);
if (v_contextDependent_222_ == 0)
{
lean_dec(v_a_224_);
return v___x_223_;
}
else
{
if (lean_obj_tag(v_a_224_) == 0)
{
uint8_t v_contextDependent_236_; 
v_contextDependent_236_ = lean_ctor_get_uint8(v_a_224_, 1);
v___y_226_ = v_contextDependent_236_;
goto v___jp_225_;
}
else
{
uint8_t v_contextDependent_237_; 
v_contextDependent_237_ = lean_ctor_get_uint8(v_a_224_, sizeof(void*)*2 + 1);
v___y_226_ = v_contextDependent_237_;
goto v___jp_225_;
}
}
v___jp_225_:
{
if (v___y_226_ == 0)
{
lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_234_; 
v_isSharedCheck_234_ = !lean_is_exclusive(v___x_223_);
if (v_isSharedCheck_234_ == 0)
{
lean_object* v_unused_235_; 
v_unused_235_ = lean_ctor_get(v___x_223_, 0);
lean_dec(v_unused_235_);
v___x_228_ = v___x_223_;
v_isShared_229_ = v_isSharedCheck_234_;
goto v_resetjp_227_;
}
else
{
lean_dec(v___x_223_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_234_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v___x_230_; lean_object* v___x_232_; 
v___x_230_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_224_);
if (v_isShared_229_ == 0)
{
lean_ctor_set(v___x_228_, 0, v___x_230_);
v___x_232_ = v___x_228_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v___x_230_);
v___x_232_ = v_reuseFailAlloc_233_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
return v___x_232_;
}
}
}
else
{
lean_dec(v_a_224_);
return v___x_223_;
}
}
}
else
{
return v___x_223_;
}
}
else
{
lean_dec_ref_known(v_a_220_, 0);
lean_dec_ref(v_e_u2081_208_);
lean_dec_ref(v_g_207_);
return v___x_219_;
}
}
else
{
lean_dec_ref_known(v_a_220_, 2);
lean_dec_ref(v_e_u2081_208_);
lean_dec_ref(v_g_207_);
return v___x_219_;
}
}
else
{
lean_dec_ref(v_e_u2081_208_);
lean_dec_ref(v_g_207_);
return v___x_219_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_Simproc_orElse_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_206_ = stack[0].m_obj;
lean_object* v_g_207_ = stack[1].m_obj;
lean_object* v_e_u2081_208_ = stack[2].m_obj;
lean_object* v_a_209_ = stack[3].m_obj;
lean_object* v_a_210_ = stack[4].m_obj;
lean_object* v_a_211_ = stack[5].m_obj;
lean_object* v_a_212_ = stack[6].m_obj;
lean_object* v_a_213_ = stack[7].m_obj;
lean_object* v_a_214_ = stack[8].m_obj;
lean_object* v_a_215_ = stack[9].m_obj;
lean_object* v_a_216_ = stack[10].m_obj;
lean_object* v_a_217_ = stack[11].m_obj;
lean_object* v_res_238_;
v_res_238_ = l_Lean_Meta_Sym_Simp_Simproc_orElse(v_f_206_, v_g_207_, v_e_u2081_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_);
stack->m_obj
 = v_res_238_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Simproc_orElse___boxed(lean_object* v_f_239_, lean_object* v_g_240_, lean_object* v_e_u2081_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Lean_Meta_Sym_Simp_Simproc_orElse(v_f_239_, v_g_240_, v_e_u2081_241_, v_a_242_, v_a_243_, v_a_244_, v_a_245_, v_a_246_, v_a_247_, v_a_248_, v_a_249_, v_a_250_);
lean_dec(v_a_250_);
lean_dec_ref(v_a_249_);
lean_dec(v_a_248_);
lean_dec_ref(v_a_247_);
lean_dec(v_a_246_);
lean_dec_ref(v_a_245_);
lean_dec(v_a_244_);
lean_dec_ref(v_a_243_);
lean_dec(v_a_242_);
return v_res_252_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_instOrElseSimproc___lam__0(lean_object* v_f_253_, lean_object* v_g_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_){
_start:
{
lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_266_ = lean_box(0);
lean_inc(v___y_264_);
lean_inc_ref(v___y_263_);
lean_inc(v___y_262_);
lean_inc_ref(v___y_261_);
lean_inc(v___y_260_);
lean_inc_ref(v___y_259_);
lean_inc(v___y_258_);
lean_inc_ref(v___y_257_);
lean_inc(v___y_256_);
lean_inc_ref(v___y_255_);
v___x_267_ = lean_apply_11(v_f_253_, v___y_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_, lean_box(0));
if (lean_obj_tag(v___x_267_) == 0)
{
lean_object* v_a_268_; 
v_a_268_ = lean_ctor_get(v___x_267_, 0);
lean_inc(v_a_268_);
if (lean_obj_tag(v_a_268_) == 0)
{
uint8_t v_done_269_; 
v_done_269_ = lean_ctor_get_uint8(v_a_268_, 0);
if (v_done_269_ == 0)
{
uint8_t v_contextDependent_270_; lean_object* v___x_271_; 
lean_dec_ref_known(v___x_267_, 1);
v_contextDependent_270_ = lean_ctor_get_uint8(v_a_268_, 1);
lean_dec_ref_known(v_a_268_, 0);
lean_inc(v___y_264_);
lean_inc_ref(v___y_263_);
lean_inc(v___y_262_);
lean_inc_ref(v___y_261_);
lean_inc(v___y_260_);
lean_inc_ref(v___y_259_);
lean_inc(v___y_258_);
lean_inc_ref(v___y_257_);
lean_inc(v___y_256_);
v___x_271_ = lean_apply_12(v_g_254_, v___x_266_, v___y_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_, lean_box(0));
if (lean_obj_tag(v___x_271_) == 0)
{
lean_object* v_a_272_; uint8_t v___y_274_; 
v_a_272_ = lean_ctor_get(v___x_271_, 0);
lean_inc(v_a_272_);
if (v_contextDependent_270_ == 0)
{
lean_dec(v_a_272_);
return v___x_271_;
}
else
{
if (lean_obj_tag(v_a_272_) == 0)
{
uint8_t v_contextDependent_284_; 
v_contextDependent_284_ = lean_ctor_get_uint8(v_a_272_, 1);
v___y_274_ = v_contextDependent_284_;
goto v___jp_273_;
}
else
{
uint8_t v_contextDependent_285_; 
v_contextDependent_285_ = lean_ctor_get_uint8(v_a_272_, sizeof(void*)*2 + 1);
v___y_274_ = v_contextDependent_285_;
goto v___jp_273_;
}
}
v___jp_273_:
{
if (v___y_274_ == 0)
{
lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_282_; 
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_271_);
if (v_isSharedCheck_282_ == 0)
{
lean_object* v_unused_283_; 
v_unused_283_ = lean_ctor_get(v___x_271_, 0);
lean_dec(v_unused_283_);
v___x_276_ = v___x_271_;
v_isShared_277_ = v_isSharedCheck_282_;
goto v_resetjp_275_;
}
else
{
lean_dec(v___x_271_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_282_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_278_; lean_object* v___x_280_; 
v___x_278_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_272_);
if (v_isShared_277_ == 0)
{
lean_ctor_set(v___x_276_, 0, v___x_278_);
v___x_280_ = v___x_276_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v___x_278_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
}
else
{
lean_dec(v_a_272_);
return v___x_271_;
}
}
}
else
{
return v___x_271_;
}
}
else
{
lean_dec_ref_known(v_a_268_, 0);
lean_dec_ref(v___y_255_);
lean_dec_ref(v_g_254_);
return v___x_267_;
}
}
else
{
lean_dec_ref_known(v_a_268_, 2);
lean_dec_ref(v___y_255_);
lean_dec_ref(v_g_254_);
return v___x_267_;
}
}
else
{
lean_dec_ref(v___y_255_);
lean_dec_ref(v_g_254_);
return v___x_267_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_instOrElseSimproc___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_253_ = stack[0].m_obj;
lean_object* v_g_254_ = stack[1].m_obj;
lean_object* v___y_255_ = stack[2].m_obj;
lean_object* v___y_256_ = stack[3].m_obj;
lean_object* v___y_257_ = stack[4].m_obj;
lean_object* v___y_258_ = stack[5].m_obj;
lean_object* v___y_259_ = stack[6].m_obj;
lean_object* v___y_260_ = stack[7].m_obj;
lean_object* v___y_261_ = stack[8].m_obj;
lean_object* v___y_262_ = stack[9].m_obj;
lean_object* v___y_263_ = stack[10].m_obj;
lean_object* v___y_264_ = stack[11].m_obj;
lean_object* v_res_286_;
v_res_286_ = l_Lean_Meta_Sym_Simp_instOrElseSimproc___lam__0(v_f_253_, v_g_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_);
stack->m_obj
 = v_res_286_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instOrElseSimproc___lam__0___boxed(lean_object* v_f_287_, lean_object* v_g_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Lean_Meta_Sym_Simp_instOrElseSimproc___lam__0(v_f_287_, v_g_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_);
lean_dec(v___y_298_);
lean_dec_ref(v___y_297_);
lean_dec(v___y_296_);
lean_dec_ref(v___y_295_);
lean_dec(v___y_294_);
lean_dec_ref(v___y_293_);
lean_dec(v___y_292_);
lean_dec_ref(v___y_291_);
lean_dec(v___y_290_);
return v_res_300_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_Simproc_tryCatch(lean_object* v_f_303_, lean_object* v_e_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_){
_start:
{
lean_object* v___x_315_; 
lean_inc(v_a_313_);
lean_inc_ref(v_a_312_);
lean_inc(v_a_311_);
lean_inc_ref(v_a_310_);
lean_inc(v_a_309_);
lean_inc_ref(v_a_308_);
lean_inc(v_a_307_);
lean_inc_ref(v_a_306_);
lean_inc(v_a_305_);
v___x_315_ = lean_apply_11(v_f_303_, v_e_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_, lean_box(0));
if (lean_obj_tag(v___x_315_) == 0)
{
return v___x_315_;
}
else
{
lean_object* v_a_316_; uint8_t v___y_318_; uint8_t v___x_328_; 
v_a_316_ = lean_ctor_get(v___x_315_, 0);
lean_inc(v_a_316_);
v___x_328_ = l_Lean_Exception_isInterrupt(v_a_316_);
if (v___x_328_ == 0)
{
uint8_t v___x_329_; 
v___x_329_ = l_Lean_Exception_isRuntime(v_a_316_);
v___y_318_ = v___x_329_;
goto v___jp_317_;
}
else
{
lean_dec(v_a_316_);
v___y_318_ = v___x_328_;
goto v___jp_317_;
}
v___jp_317_:
{
if (v___y_318_ == 0)
{
lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_326_; 
v_isSharedCheck_326_ = !lean_is_exclusive(v___x_315_);
if (v_isSharedCheck_326_ == 0)
{
lean_object* v_unused_327_; 
v_unused_327_ = lean_ctor_get(v___x_315_, 0);
lean_dec(v_unused_327_);
v___x_320_ = v___x_315_;
v_isShared_321_ = v_isSharedCheck_326_;
goto v_resetjp_319_;
}
else
{
lean_dec(v___x_315_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_326_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_322_; lean_object* v___x_324_; 
v___x_322_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_322_, 0, v___y_318_);
lean_ctor_set_uint8(v___x_322_, 1, v___y_318_);
if (v_isShared_321_ == 0)
{
lean_ctor_set_tag(v___x_320_, 0);
lean_ctor_set(v___x_320_, 0, v___x_322_);
v___x_324_ = v___x_320_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v___x_322_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
else
{
return v___x_315_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_Simproc_tryCatch_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_303_ = stack[0].m_obj;
lean_object* v_e_304_ = stack[1].m_obj;
lean_object* v_a_305_ = stack[2].m_obj;
lean_object* v_a_306_ = stack[3].m_obj;
lean_object* v_a_307_ = stack[4].m_obj;
lean_object* v_a_308_ = stack[5].m_obj;
lean_object* v_a_309_ = stack[6].m_obj;
lean_object* v_a_310_ = stack[7].m_obj;
lean_object* v_a_311_ = stack[8].m_obj;
lean_object* v_a_312_ = stack[9].m_obj;
lean_object* v_a_313_ = stack[10].m_obj;
lean_object* v_res_330_;
v_res_330_ = l_Lean_Meta_Sym_Simp_Simproc_tryCatch(v_f_303_, v_e_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_);
stack->m_obj
 = v_res_330_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Simproc_tryCatch___boxed(lean_object* v_f_331_, lean_object* v_e_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_Lean_Meta_Sym_Simp_Simproc_tryCatch(v_f_331_, v_e_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_);
lean_dec(v_a_341_);
lean_dec_ref(v_a_340_);
lean_dec(v_a_339_);
lean_dec_ref(v_a_338_);
lean_dec(v_a_337_);
lean_dec_ref(v_a_336_);
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
lean_dec(v_a_333_);
return v_res_343_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Result(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Simproc(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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

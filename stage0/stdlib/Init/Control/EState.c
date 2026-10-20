// Lean compiler output
// Module: Init.Control.EState
// Imports: public import Init.Data.ToString.Basic public import Init.Control.State
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
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static const lean_string_object l_EStateM_instToStringResult___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "ok: "};
static const lean_object* l_EStateM_instToStringResult___redArg___lam__0___closed__0 = (const lean_object*)&l_EStateM_instToStringResult___redArg___lam__0___closed__0_value;
static const lean_string_object l_EStateM_instToStringResult___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "error: "};
static const lean_object* l_EStateM_instToStringResult___redArg___lam__0___closed__1 = (const lean_object*)&l_EStateM_instToStringResult___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_EStateM_instToStringResult___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EStateM_instToStringResult___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EStateM_instToStringResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_EStateM_instReprResult___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "EStateM.Result.ok "};
static const lean_object* l_EStateM_instReprResult___redArg___lam__0___closed__0 = (const lean_object*)&l_EStateM_instReprResult___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_EStateM_instReprResult___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_EStateM_instReprResult___redArg___lam__0___closed__0_value)}};
static const lean_object* l_EStateM_instReprResult___redArg___lam__0___closed__1 = (const lean_object*)&l_EStateM_instReprResult___redArg___lam__0___closed__1_value;
static const lean_string_object l_EStateM_instReprResult___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "EStateM.Result.error "};
static const lean_object* l_EStateM_instReprResult___redArg___lam__0___closed__2 = (const lean_object*)&l_EStateM_instReprResult___redArg___lam__0___closed__2_value;
static const lean_ctor_object l_EStateM_instReprResult___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_EStateM_instReprResult___redArg___lam__0___closed__2_value)}};
static const lean_object* l_EStateM_instReprResult___redArg___lam__0___closed__3 = (const lean_object*)&l_EStateM_instReprResult___redArg___lam__0___closed__3_value;
LEAN_EXPORT lean_object* l_EStateM_instReprResult___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EStateM_instReprResult___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EStateM_instReprResult___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EStateM_instReprResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EStateM_instMonadAttach___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_EStateM_instMonadAttach___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonadAttach___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_EStateM_instMonadAttach___redArg___closed__0 = (const lean_object*)&l_EStateM_instMonadAttach___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_EStateM_instMonadAttach___redArg();
LEAN_EXPORT lean_object* l_EStateM_instMonadAttach___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_EStateM_instMonadAttach(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EStateM_orElse_x27___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_EStateM_orElse_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EStateM_orElse_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_EStateM_orElse_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EStateM_instMonadFinally___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_EStateM_instMonadFinally___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonadFinally___redArg___lam__0, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_EStateM_instMonadFinally___redArg___closed__0 = (const lean_object*)&l_EStateM_instMonadFinally___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_EStateM_instMonadFinally___redArg();
LEAN_EXPORT lean_object* l_EStateM_instMonadFinally___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_EStateM_instMonadFinally(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EStateM_fromStateM___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EStateM_fromStateM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EStateM_instToStringResult___redArg___lam__0(lean_object* v_inst_3_, lean_object* v_inst_4_, lean_object* v_x_5_){
_start:
{
if (lean_obj_tag(v_x_5_) == 0)
{
lean_object* v_a_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
lean_dec_ref(v_inst_4_);
v_a_6_ = lean_ctor_get(v_x_5_, 0);
lean_inc(v_a_6_);
lean_dec_ref_known(v_x_5_, 2);
v___x_7_ = ((lean_object*)(l_EStateM_instToStringResult___redArg___lam__0___closed__0));
v___x_8_ = lean_apply_1(v_inst_3_, v_a_6_);
v___x_9_ = lean_string_append(v___x_7_, v___x_8_);
lean_dec_ref(v___x_8_);
return v___x_9_;
}
else
{
lean_object* v_a_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
lean_dec_ref(v_inst_3_);
v_a_10_ = lean_ctor_get(v_x_5_, 0);
lean_inc(v_a_10_);
lean_dec_ref_known(v_x_5_, 2);
v___x_11_ = ((lean_object*)(l_EStateM_instToStringResult___redArg___lam__0___closed__1));
v___x_12_ = lean_apply_1(v_inst_4_, v_a_10_);
v___x_13_ = lean_string_append(v___x_11_, v___x_12_);
lean_dec_ref(v___x_12_);
return v___x_13_;
}
}
}
LEAN_EXPORT lean_object* l_EStateM_instToStringResult___redArg(lean_object* v_inst_14_, lean_object* v_inst_15_){
_start:
{
lean_object* v___f_16_; 
v___f_16_ = lean_alloc_closure((void*)(l_EStateM_instToStringResult___redArg___lam__0), 3, 2);
lean_closure_set(v___f_16_, 0, v_inst_15_);
lean_closure_set(v___f_16_, 1, v_inst_14_);
return v___f_16_;
}
}
LEAN_EXPORT lean_object* l_EStateM_instToStringResult(lean_object* v_00_u03b5_17_, lean_object* v_00_u03c3_18_, lean_object* v_00_u03b1_19_, lean_object* v_inst_20_, lean_object* v_inst_21_){
_start:
{
lean_object* v___f_22_; 
v___f_22_ = lean_alloc_closure((void*)(l_EStateM_instToStringResult___redArg___lam__0), 3, 2);
lean_closure_set(v___f_22_, 0, v_inst_21_);
lean_closure_set(v___f_22_, 1, v_inst_20_);
return v___f_22_;
}
}
LEAN_EXPORT lean_object* l_EStateM_instReprResult___redArg___lam__0(lean_object* v_inst_29_, lean_object* v_inst_30_, lean_object* v_x_31_, lean_object* v_x_32_){
_start:
{
if (lean_obj_tag(v_x_31_) == 0)
{
lean_object* v_a_33_; lean_object* v___x_35_; uint8_t v_isShared_36_; uint8_t v_isSharedCheck_44_; 
lean_dec_ref(v_inst_30_);
v_a_33_ = lean_ctor_get(v_x_31_, 0);
v_isSharedCheck_44_ = !lean_is_exclusive(v_x_31_);
if (v_isSharedCheck_44_ == 0)
{
lean_object* v_unused_45_; 
v_unused_45_ = lean_ctor_get(v_x_31_, 1);
lean_dec(v_unused_45_);
v___x_35_ = v_x_31_;
v_isShared_36_ = v_isSharedCheck_44_;
goto v_resetjp_34_;
}
else
{
lean_inc(v_a_33_);
lean_dec(v_x_31_);
v___x_35_ = lean_box(0);
v_isShared_36_ = v_isSharedCheck_44_;
goto v_resetjp_34_;
}
v_resetjp_34_:
{
lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_41_; 
v___x_37_ = ((lean_object*)(l_EStateM_instReprResult___redArg___lam__0___closed__1));
v___x_38_ = lean_unsigned_to_nat(1024u);
v___x_39_ = lean_apply_2(v_inst_29_, v_a_33_, v___x_38_);
if (v_isShared_36_ == 0)
{
lean_ctor_set_tag(v___x_35_, 5);
lean_ctor_set(v___x_35_, 1, v___x_39_);
lean_ctor_set(v___x_35_, 0, v___x_37_);
v___x_41_ = v___x_35_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_43_; 
v_reuseFailAlloc_43_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_43_, 0, v___x_37_);
lean_ctor_set(v_reuseFailAlloc_43_, 1, v___x_39_);
v___x_41_ = v_reuseFailAlloc_43_;
goto v_reusejp_40_;
}
v_reusejp_40_:
{
lean_object* v___x_42_; 
v___x_42_ = l_Repr_addAppParen(v___x_41_, v_x_32_);
return v___x_42_;
}
}
}
else
{
lean_object* v_a_46_; lean_object* v___x_48_; uint8_t v_isShared_49_; uint8_t v_isSharedCheck_57_; 
lean_dec_ref(v_inst_29_);
v_a_46_ = lean_ctor_get(v_x_31_, 0);
v_isSharedCheck_57_ = !lean_is_exclusive(v_x_31_);
if (v_isSharedCheck_57_ == 0)
{
lean_object* v_unused_58_; 
v_unused_58_ = lean_ctor_get(v_x_31_, 1);
lean_dec(v_unused_58_);
v___x_48_ = v_x_31_;
v_isShared_49_ = v_isSharedCheck_57_;
goto v_resetjp_47_;
}
else
{
lean_inc(v_a_46_);
lean_dec(v_x_31_);
v___x_48_ = lean_box(0);
v_isShared_49_ = v_isSharedCheck_57_;
goto v_resetjp_47_;
}
v_resetjp_47_:
{
lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_54_; 
v___x_50_ = ((lean_object*)(l_EStateM_instReprResult___redArg___lam__0___closed__3));
v___x_51_ = lean_unsigned_to_nat(1024u);
v___x_52_ = lean_apply_2(v_inst_30_, v_a_46_, v___x_51_);
if (v_isShared_49_ == 0)
{
lean_ctor_set_tag(v___x_48_, 5);
lean_ctor_set(v___x_48_, 1, v___x_52_);
lean_ctor_set(v___x_48_, 0, v___x_50_);
v___x_54_ = v___x_48_;
goto v_reusejp_53_;
}
else
{
lean_object* v_reuseFailAlloc_56_; 
v_reuseFailAlloc_56_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_56_, 0, v___x_50_);
lean_ctor_set(v_reuseFailAlloc_56_, 1, v___x_52_);
v___x_54_ = v_reuseFailAlloc_56_;
goto v_reusejp_53_;
}
v_reusejp_53_:
{
lean_object* v___x_55_; 
v___x_55_ = l_Repr_addAppParen(v___x_54_, v_x_32_);
return v___x_55_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_EStateM_instReprResult___redArg___lam__0___boxed(lean_object* v_inst_59_, lean_object* v_inst_60_, lean_object* v_x_61_, lean_object* v_x_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l_EStateM_instReprResult___redArg___lam__0(v_inst_59_, v_inst_60_, v_x_61_, v_x_62_);
lean_dec(v_x_62_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l_EStateM_instReprResult___redArg(lean_object* v_inst_64_, lean_object* v_inst_65_){
_start:
{
lean_object* v___f_66_; 
v___f_66_ = lean_alloc_closure((void*)(l_EStateM_instReprResult___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_66_, 0, v_inst_65_);
lean_closure_set(v___f_66_, 1, v_inst_64_);
return v___f_66_;
}
}
LEAN_EXPORT lean_object* l_EStateM_instReprResult(lean_object* v_00_u03b5_67_, lean_object* v_00_u03c3_68_, lean_object* v_00_u03b1_69_, lean_object* v_inst_70_, lean_object* v_inst_71_){
_start:
{
lean_object* v___f_72_; 
v___f_72_ = lean_alloc_closure((void*)(l_EStateM_instReprResult___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_72_, 0, v_inst_71_);
lean_closure_set(v___f_72_, 1, v_inst_70_);
return v___f_72_;
}
}
LEAN_EXPORT lean_object* l_EStateM_instMonadAttach___redArg___lam__0(lean_object* v_00_u03b1_73_, lean_object* v_x_74_, lean_object* v_s_75_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = lean_apply_1(v_x_74_, v_s_75_);
if (lean_obj_tag(v___x_76_) == 0)
{
lean_object* v_a_77_; lean_object* v_a_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_85_; 
v_a_77_ = lean_ctor_get(v___x_76_, 0);
v_a_78_ = lean_ctor_get(v___x_76_, 1);
v_isSharedCheck_85_ = !lean_is_exclusive(v___x_76_);
if (v_isSharedCheck_85_ == 0)
{
v___x_80_ = v___x_76_;
v_isShared_81_ = v_isSharedCheck_85_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_a_78_);
lean_inc(v_a_77_);
lean_dec(v___x_76_);
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
v_reuseFailAlloc_84_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_84_, 0, v_a_77_);
lean_ctor_set(v_reuseFailAlloc_84_, 1, v_a_78_);
v___x_83_ = v_reuseFailAlloc_84_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
return v___x_83_;
}
}
}
else
{
lean_object* v_a_86_; lean_object* v_a_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_94_; 
v_a_86_ = lean_ctor_get(v___x_76_, 0);
v_a_87_ = lean_ctor_get(v___x_76_, 1);
v_isSharedCheck_94_ = !lean_is_exclusive(v___x_76_);
if (v_isSharedCheck_94_ == 0)
{
v___x_89_ = v___x_76_;
v_isShared_90_ = v_isSharedCheck_94_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_a_87_);
lean_inc(v_a_86_);
lean_dec(v___x_76_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_94_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v___x_92_; 
if (v_isShared_90_ == 0)
{
v___x_92_ = v___x_89_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v_a_86_);
lean_ctor_set(v_reuseFailAlloc_93_, 1, v_a_87_);
v___x_92_ = v_reuseFailAlloc_93_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
return v___x_92_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_EStateM_instMonadAttach___redArg(){
_start:
{
lean_object* v___f_97_; 
v___f_97_ = ((lean_object*)(l_EStateM_instMonadAttach___redArg___closed__0));
return v___f_97_;
}
}
LEAN_EXPORT lean_object* l_EStateM_instMonadAttach___redArg___boxed(lean_object* v___dummy_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_EStateM_instMonadAttach___redArg();
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l_EStateM_instMonadAttach(lean_object* v_00_u03b5_100_, lean_object* v_00_u03c3_101_){
_start:
{
lean_object* v___f_102_; 
v___f_102_ = ((lean_object*)(l_EStateM_instMonadAttach___redArg___closed__0));
return v___f_102_;
}
}
LEAN_EXPORT lean_object* l_EStateM_orElse_x27___redArg(lean_object* v_inst_103_, lean_object* v_x_u2081_104_, lean_object* v_x_u2082_105_, uint8_t v_useFirstEx_106_, lean_object* v_s_107_){
_start:
{
lean_object* v_save_108_; lean_object* v_restore_109_; lean_object* v_d_110_; lean_object* v___x_111_; 
v_save_108_ = lean_ctor_get(v_inst_103_, 0);
lean_inc(v_save_108_);
v_restore_109_ = lean_ctor_get(v_inst_103_, 1);
lean_inc(v_restore_109_);
lean_dec_ref(v_inst_103_);
lean_inc(v_s_107_);
v_d_110_ = lean_apply_1(v_save_108_, v_s_107_);
v___x_111_ = lean_apply_1(v_x_u2081_104_, v_s_107_);
if (lean_obj_tag(v___x_111_) == 1)
{
lean_object* v_a_112_; lean_object* v_a_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v_a_112_ = lean_ctor_get(v___x_111_, 0);
lean_inc(v_a_112_);
v_a_113_ = lean_ctor_get(v___x_111_, 1);
lean_inc(v_a_113_);
lean_dec_ref_known(v___x_111_, 2);
v___x_114_ = lean_apply_2(v_restore_109_, v_a_113_, v_d_110_);
v___x_115_ = lean_apply_1(v_x_u2082_105_, v___x_114_);
if (lean_obj_tag(v___x_115_) == 1)
{
if (v_useFirstEx_106_ == 0)
{
lean_dec(v_a_112_);
return v___x_115_;
}
else
{
lean_object* v_a_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_123_; 
v_a_116_ = lean_ctor_get(v___x_115_, 1);
v_isSharedCheck_123_ = !lean_is_exclusive(v___x_115_);
if (v_isSharedCheck_123_ == 0)
{
lean_object* v_unused_124_; 
v_unused_124_ = lean_ctor_get(v___x_115_, 0);
lean_dec(v_unused_124_);
v___x_118_ = v___x_115_;
v_isShared_119_ = v_isSharedCheck_123_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_a_116_);
lean_dec(v___x_115_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_123_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v___x_121_; 
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 0, v_a_112_);
v___x_121_ = v___x_118_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v_a_112_);
lean_ctor_set(v_reuseFailAlloc_122_, 1, v_a_116_);
v___x_121_ = v_reuseFailAlloc_122_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
return v___x_121_;
}
}
}
}
else
{
lean_dec(v_a_112_);
return v___x_115_;
}
}
else
{
lean_dec(v_d_110_);
lean_dec(v_restore_109_);
lean_dec_ref(v_x_u2082_105_);
return v___x_111_;
}
}
}
LEAN_EXPORT lean_object* l_EStateM_orElse_x27___redArg___boxed(lean_object* v_inst_125_, lean_object* v_x_u2081_126_, lean_object* v_x_u2082_127_, lean_object* v_useFirstEx_128_, lean_object* v_s_129_){
_start:
{
uint8_t v_useFirstEx_boxed_130_; lean_object* v_res_131_; 
v_useFirstEx_boxed_130_ = lean_unbox(v_useFirstEx_128_);
v_res_131_ = l_EStateM_orElse_x27___redArg(v_inst_125_, v_x_u2081_126_, v_x_u2082_127_, v_useFirstEx_boxed_130_, v_s_129_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l_EStateM_orElse_x27(lean_object* v_00_u03b5_132_, lean_object* v_00_u03c3_133_, lean_object* v_00_u03b1_134_, lean_object* v_00_u03b4_135_, lean_object* v_inst_136_, lean_object* v_x_u2081_137_, lean_object* v_x_u2082_138_, uint8_t v_useFirstEx_139_, lean_object* v_s_140_){
_start:
{
lean_object* v_save_141_; lean_object* v_restore_142_; lean_object* v_d_143_; lean_object* v___x_144_; 
v_save_141_ = lean_ctor_get(v_inst_136_, 0);
lean_inc(v_save_141_);
v_restore_142_ = lean_ctor_get(v_inst_136_, 1);
lean_inc(v_restore_142_);
lean_dec_ref(v_inst_136_);
lean_inc(v_s_140_);
v_d_143_ = lean_apply_1(v_save_141_, v_s_140_);
v___x_144_ = lean_apply_1(v_x_u2081_137_, v_s_140_);
if (lean_obj_tag(v___x_144_) == 1)
{
lean_object* v_a_145_; lean_object* v_a_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v_a_145_ = lean_ctor_get(v___x_144_, 0);
lean_inc(v_a_145_);
v_a_146_ = lean_ctor_get(v___x_144_, 1);
lean_inc(v_a_146_);
lean_dec_ref_known(v___x_144_, 2);
v___x_147_ = lean_apply_2(v_restore_142_, v_a_146_, v_d_143_);
v___x_148_ = lean_apply_1(v_x_u2082_138_, v___x_147_);
if (lean_obj_tag(v___x_148_) == 1)
{
if (v_useFirstEx_139_ == 0)
{
lean_dec(v_a_145_);
return v___x_148_;
}
else
{
lean_object* v_a_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_156_; 
v_a_149_ = lean_ctor_get(v___x_148_, 1);
v_isSharedCheck_156_ = !lean_is_exclusive(v___x_148_);
if (v_isSharedCheck_156_ == 0)
{
lean_object* v_unused_157_; 
v_unused_157_ = lean_ctor_get(v___x_148_, 0);
lean_dec(v_unused_157_);
v___x_151_ = v___x_148_;
v_isShared_152_ = v_isSharedCheck_156_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_a_149_);
lean_dec(v___x_148_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_156_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v___x_154_; 
if (v_isShared_152_ == 0)
{
lean_ctor_set(v___x_151_, 0, v_a_145_);
v___x_154_ = v___x_151_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v_a_145_);
lean_ctor_set(v_reuseFailAlloc_155_, 1, v_a_149_);
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
lean_dec(v_a_145_);
return v___x_148_;
}
}
else
{
lean_dec(v_d_143_);
lean_dec(v_restore_142_);
lean_dec_ref(v_x_u2082_138_);
return v___x_144_;
}
}
}
LEAN_EXPORT lean_object* l_EStateM_orElse_x27___boxed(lean_object* v_00_u03b5_158_, lean_object* v_00_u03c3_159_, lean_object* v_00_u03b1_160_, lean_object* v_00_u03b4_161_, lean_object* v_inst_162_, lean_object* v_x_u2081_163_, lean_object* v_x_u2082_164_, lean_object* v_useFirstEx_165_, lean_object* v_s_166_){
_start:
{
uint8_t v_useFirstEx_boxed_167_; lean_object* v_res_168_; 
v_useFirstEx_boxed_167_ = lean_unbox(v_useFirstEx_165_);
v_res_168_ = l_EStateM_orElse_x27(v_00_u03b5_158_, v_00_u03c3_159_, v_00_u03b1_160_, v_00_u03b4_161_, v_inst_162_, v_x_u2081_163_, v_x_u2082_164_, v_useFirstEx_boxed_167_, v_s_166_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_EStateM_instMonadFinally___redArg___lam__0(lean_object* v_00_u03b1_169_, lean_object* v_00_u03b2_170_, lean_object* v_x_171_, lean_object* v_h_172_, lean_object* v_s_173_){
_start:
{
lean_object* v_r_174_; 
v_r_174_ = lean_apply_1(v_x_171_, v_s_173_);
if (lean_obj_tag(v_r_174_) == 0)
{
lean_object* v_a_175_; lean_object* v_a_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_203_; 
v_a_175_ = lean_ctor_get(v_r_174_, 0);
v_a_176_ = lean_ctor_get(v_r_174_, 1);
v_isSharedCheck_203_ = !lean_is_exclusive(v_r_174_);
if (v_isSharedCheck_203_ == 0)
{
v___x_178_ = v_r_174_;
v_isShared_179_ = v_isSharedCheck_203_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_a_176_);
lean_inc(v_a_175_);
lean_dec(v_r_174_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_203_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___x_180_; lean_object* v___x_181_; 
lean_inc(v_a_175_);
v___x_180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_180_, 0, v_a_175_);
v___x_181_ = lean_apply_2(v_h_172_, v___x_180_, v_a_176_);
if (lean_obj_tag(v___x_181_) == 0)
{
lean_object* v_a_182_; lean_object* v_a_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_193_; 
v_a_182_ = lean_ctor_get(v___x_181_, 0);
v_a_183_ = lean_ctor_get(v___x_181_, 1);
v_isSharedCheck_193_ = !lean_is_exclusive(v___x_181_);
if (v_isSharedCheck_193_ == 0)
{
v___x_185_ = v___x_181_;
v_isShared_186_ = v_isSharedCheck_193_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_a_183_);
lean_inc(v_a_182_);
lean_dec(v___x_181_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_193_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___x_188_; 
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 1, v_a_182_);
v___x_188_ = v___x_178_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v_a_175_);
lean_ctor_set(v_reuseFailAlloc_192_, 1, v_a_182_);
v___x_188_ = v_reuseFailAlloc_192_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
lean_object* v___x_190_; 
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 0, v___x_188_);
v___x_190_ = v___x_185_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v___x_188_);
lean_ctor_set(v_reuseFailAlloc_191_, 1, v_a_183_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
}
}
else
{
lean_object* v_a_194_; lean_object* v_a_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_202_; 
lean_del_object(v___x_178_);
lean_dec(v_a_175_);
v_a_194_ = lean_ctor_get(v___x_181_, 0);
v_a_195_ = lean_ctor_get(v___x_181_, 1);
v_isSharedCheck_202_ = !lean_is_exclusive(v___x_181_);
if (v_isSharedCheck_202_ == 0)
{
v___x_197_ = v___x_181_;
v_isShared_198_ = v_isSharedCheck_202_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_a_195_);
lean_inc(v_a_194_);
lean_dec(v___x_181_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_202_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___x_200_; 
if (v_isShared_198_ == 0)
{
v___x_200_ = v___x_197_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v_a_194_);
lean_ctor_set(v_reuseFailAlloc_201_, 1, v_a_195_);
v___x_200_ = v_reuseFailAlloc_201_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
return v___x_200_;
}
}
}
}
}
else
{
lean_object* v_a_204_; lean_object* v_a_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v_a_204_ = lean_ctor_get(v_r_174_, 0);
lean_inc(v_a_204_);
v_a_205_ = lean_ctor_get(v_r_174_, 1);
lean_inc(v_a_205_);
lean_dec_ref_known(v_r_174_, 2);
v___x_206_ = lean_box(0);
v___x_207_ = lean_apply_2(v_h_172_, v___x_206_, v_a_205_);
if (lean_obj_tag(v___x_207_) == 0)
{
lean_object* v_a_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_215_; 
v_a_208_ = lean_ctor_get(v___x_207_, 1);
v_isSharedCheck_215_ = !lean_is_exclusive(v___x_207_);
if (v_isSharedCheck_215_ == 0)
{
lean_object* v_unused_216_; 
v_unused_216_ = lean_ctor_get(v___x_207_, 0);
lean_dec(v_unused_216_);
v___x_210_ = v___x_207_;
v_isShared_211_ = v_isSharedCheck_215_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_a_208_);
lean_dec(v___x_207_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_215_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___x_213_; 
if (v_isShared_211_ == 0)
{
lean_ctor_set_tag(v___x_210_, 1);
lean_ctor_set(v___x_210_, 0, v_a_204_);
v___x_213_ = v___x_210_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_a_204_);
lean_ctor_set(v_reuseFailAlloc_214_, 1, v_a_208_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
return v___x_213_;
}
}
}
else
{
lean_object* v_a_217_; lean_object* v_a_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_225_; 
lean_dec(v_a_204_);
v_a_217_ = lean_ctor_get(v___x_207_, 0);
v_a_218_ = lean_ctor_get(v___x_207_, 1);
v_isSharedCheck_225_ = !lean_is_exclusive(v___x_207_);
if (v_isSharedCheck_225_ == 0)
{
v___x_220_ = v___x_207_;
v_isShared_221_ = v_isSharedCheck_225_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_a_218_);
lean_inc(v_a_217_);
lean_dec(v___x_207_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_225_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_223_; 
if (v_isShared_221_ == 0)
{
v___x_223_ = v___x_220_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v_a_217_);
lean_ctor_set(v_reuseFailAlloc_224_, 1, v_a_218_);
v___x_223_ = v_reuseFailAlloc_224_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
return v___x_223_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_EStateM_instMonadFinally___redArg(){
_start:
{
lean_object* v___f_228_; 
v___f_228_ = ((lean_object*)(l_EStateM_instMonadFinally___redArg___closed__0));
return v___f_228_;
}
}
LEAN_EXPORT lean_object* l_EStateM_instMonadFinally___redArg___boxed(lean_object* v___dummy_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_EStateM_instMonadFinally___redArg();
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_EStateM_instMonadFinally(lean_object* v_00_u03b5_231_, lean_object* v_00_u03c3_232_){
_start:
{
lean_object* v___f_233_; 
v___f_233_ = ((lean_object*)(l_EStateM_instMonadFinally___redArg___closed__0));
return v___f_233_;
}
}
LEAN_EXPORT lean_object* l_EStateM_fromStateM___redArg(lean_object* v_x_234_, lean_object* v_s_235_){
_start:
{
lean_object* v___x_236_; lean_object* v_fst_237_; lean_object* v_snd_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_245_; 
v___x_236_ = lean_apply_1(v_x_234_, v_s_235_);
v_fst_237_ = lean_ctor_get(v___x_236_, 0);
v_snd_238_ = lean_ctor_get(v___x_236_, 1);
v_isSharedCheck_245_ = !lean_is_exclusive(v___x_236_);
if (v_isSharedCheck_245_ == 0)
{
v___x_240_ = v___x_236_;
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_snd_238_);
lean_inc(v_fst_237_);
lean_dec(v___x_236_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_243_; 
if (v_isShared_241_ == 0)
{
v___x_243_ = v___x_240_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_fst_237_);
lean_ctor_set(v_reuseFailAlloc_244_, 1, v_snd_238_);
v___x_243_ = v_reuseFailAlloc_244_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
return v___x_243_;
}
}
}
}
LEAN_EXPORT lean_object* l_EStateM_fromStateM(lean_object* v_00_u03b5_246_, lean_object* v_00_u03c3_247_, lean_object* v_00_u03b1_248_, lean_object* v_x_249_, lean_object* v_s_250_){
_start:
{
lean_object* v___x_251_; lean_object* v_fst_252_; lean_object* v_snd_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_260_; 
v___x_251_ = lean_apply_1(v_x_249_, v_s_250_);
v_fst_252_ = lean_ctor_get(v___x_251_, 0);
v_snd_253_ = lean_ctor_get(v___x_251_, 1);
v_isSharedCheck_260_ = !lean_is_exclusive(v___x_251_);
if (v_isSharedCheck_260_ == 0)
{
v___x_255_ = v___x_251_;
v_isShared_256_ = v_isSharedCheck_260_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_snd_253_);
lean_inc(v_fst_252_);
lean_dec(v___x_251_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_260_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v___x_258_; 
if (v_isShared_256_ == 0)
{
v___x_258_ = v___x_255_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_fst_252_);
lean_ctor_set(v_reuseFailAlloc_259_, 1, v_snd_253_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
}
}
lean_object* runtime_initialize_Init_Data_ToString_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_State(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Control_EState(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_ToString_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_State(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Control_EState(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_ToString_Basic(uint8_t builtin);
lean_object* initialize_Init_Control_State(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Control_EState(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_ToString_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_State(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_EState(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Control_EState(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Control_EState(builtin);
}
#ifdef __cplusplus
}
#endif

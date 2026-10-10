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
lean_object* l_EStateM_instMonadAttach___redArg(){
_start:
{
lean_object* v___f_97_; 
v___f_97_ = ((lean_object*)(l_EStateM_instMonadAttach___redArg___closed__0));
return v___f_97_;
}
}
LEAN_EXPORT void l_EStateM_instMonadAttach___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_98_;
v_res_98_ = l_EStateM_instMonadAttach___redArg();
stack->m_obj
 = v_res_98_;
}
LEAN_EXPORT lean_object* l_EStateM_instMonadAttach___redArg___boxed(lean_object* v___dummy_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_EStateM_instMonadAttach___redArg();
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_EStateM_instMonadAttach(lean_object* v_00_u03b5_101_, lean_object* v_00_u03c3_102_){
_start:
{
lean_object* v___f_103_; 
v___f_103_ = ((lean_object*)(l_EStateM_instMonadAttach___redArg___closed__0));
return v___f_103_;
}
}
lean_object* l_EStateM_orElse_x27___redArg(lean_object* v_inst_104_, lean_object* v_x_u2081_105_, lean_object* v_x_u2082_106_, uint8_t v_useFirstEx_107_, lean_object* v_s_108_){
_start:
{
lean_object* v_save_109_; lean_object* v_restore_110_; lean_object* v_d_111_; lean_object* v___x_112_; 
v_save_109_ = lean_ctor_get(v_inst_104_, 0);
lean_inc(v_save_109_);
v_restore_110_ = lean_ctor_get(v_inst_104_, 1);
lean_inc(v_restore_110_);
lean_dec_ref(v_inst_104_);
lean_inc(v_s_108_);
v_d_111_ = lean_apply_1(v_save_109_, v_s_108_);
v___x_112_ = lean_apply_1(v_x_u2081_105_, v_s_108_);
if (lean_obj_tag(v___x_112_) == 1)
{
lean_object* v_a_113_; lean_object* v_a_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v_a_113_ = lean_ctor_get(v___x_112_, 0);
lean_inc(v_a_113_);
v_a_114_ = lean_ctor_get(v___x_112_, 1);
lean_inc(v_a_114_);
lean_dec_ref_known(v___x_112_, 2);
v___x_115_ = lean_apply_2(v_restore_110_, v_a_114_, v_d_111_);
v___x_116_ = lean_apply_1(v_x_u2082_106_, v___x_115_);
if (lean_obj_tag(v___x_116_) == 1)
{
if (v_useFirstEx_107_ == 0)
{
lean_dec(v_a_113_);
return v___x_116_;
}
else
{
lean_object* v_a_117_; lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_124_; 
v_a_117_ = lean_ctor_get(v___x_116_, 1);
v_isSharedCheck_124_ = !lean_is_exclusive(v___x_116_);
if (v_isSharedCheck_124_ == 0)
{
lean_object* v_unused_125_; 
v_unused_125_ = lean_ctor_get(v___x_116_, 0);
lean_dec(v_unused_125_);
v___x_119_ = v___x_116_;
v_isShared_120_ = v_isSharedCheck_124_;
goto v_resetjp_118_;
}
else
{
lean_inc(v_a_117_);
lean_dec(v___x_116_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_124_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
lean_object* v___x_122_; 
if (v_isShared_120_ == 0)
{
lean_ctor_set(v___x_119_, 0, v_a_113_);
v___x_122_ = v___x_119_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v_a_113_);
lean_ctor_set(v_reuseFailAlloc_123_, 1, v_a_117_);
v___x_122_ = v_reuseFailAlloc_123_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
return v___x_122_;
}
}
}
}
else
{
lean_dec(v_a_113_);
return v___x_116_;
}
}
else
{
lean_dec(v_d_111_);
lean_dec(v_restore_110_);
lean_dec_ref(v_x_u2082_106_);
return v___x_112_;
}
}
}
LEAN_EXPORT void l_EStateM_orElse_x27___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_104_ = stack[0].m_obj;
lean_object* v_x_u2081_105_ = stack[1].m_obj;
lean_object* v_x_u2082_106_ = stack[2].m_obj;
uint8_t v_useFirstEx_107_ = stack[3].m_num;
lean_object* v_s_108_ = stack[4].m_obj;
lean_object* v_res_126_;
v_res_126_ = l_EStateM_orElse_x27___redArg(v_inst_104_, v_x_u2081_105_, v_x_u2082_106_, v_useFirstEx_107_, v_s_108_);
stack->m_obj
 = v_res_126_;
}
LEAN_EXPORT lean_object* l_EStateM_orElse_x27___redArg___boxed(lean_object* v_inst_127_, lean_object* v_x_u2081_128_, lean_object* v_x_u2082_129_, lean_object* v_useFirstEx_130_, lean_object* v_s_131_){
_start:
{
uint8_t v_useFirstEx_boxed_132_; lean_object* v_res_133_; 
v_useFirstEx_boxed_132_ = lean_unbox(v_useFirstEx_130_);
v_res_133_ = l_EStateM_orElse_x27___redArg(v_inst_127_, v_x_u2081_128_, v_x_u2082_129_, v_useFirstEx_boxed_132_, v_s_131_);
return v_res_133_;
}
}
lean_object* l_EStateM_orElse_x27(lean_object* v_00_u03b5_134_, lean_object* v_00_u03c3_135_, lean_object* v_00_u03b1_136_, lean_object* v_00_u03b4_137_, lean_object* v_inst_138_, lean_object* v_x_u2081_139_, lean_object* v_x_u2082_140_, uint8_t v_useFirstEx_141_, lean_object* v_s_142_){
_start:
{
lean_object* v_save_143_; lean_object* v_restore_144_; lean_object* v_d_145_; lean_object* v___x_146_; 
v_save_143_ = lean_ctor_get(v_inst_138_, 0);
lean_inc(v_save_143_);
v_restore_144_ = lean_ctor_get(v_inst_138_, 1);
lean_inc(v_restore_144_);
lean_dec_ref(v_inst_138_);
lean_inc(v_s_142_);
v_d_145_ = lean_apply_1(v_save_143_, v_s_142_);
v___x_146_ = lean_apply_1(v_x_u2081_139_, v_s_142_);
if (lean_obj_tag(v___x_146_) == 1)
{
lean_object* v_a_147_; lean_object* v_a_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v_a_147_ = lean_ctor_get(v___x_146_, 0);
lean_inc(v_a_147_);
v_a_148_ = lean_ctor_get(v___x_146_, 1);
lean_inc(v_a_148_);
lean_dec_ref_known(v___x_146_, 2);
v___x_149_ = lean_apply_2(v_restore_144_, v_a_148_, v_d_145_);
v___x_150_ = lean_apply_1(v_x_u2082_140_, v___x_149_);
if (lean_obj_tag(v___x_150_) == 1)
{
if (v_useFirstEx_141_ == 0)
{
lean_dec(v_a_147_);
return v___x_150_;
}
else
{
lean_object* v_a_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_158_; 
v_a_151_ = lean_ctor_get(v___x_150_, 1);
v_isSharedCheck_158_ = !lean_is_exclusive(v___x_150_);
if (v_isSharedCheck_158_ == 0)
{
lean_object* v_unused_159_; 
v_unused_159_ = lean_ctor_get(v___x_150_, 0);
lean_dec(v_unused_159_);
v___x_153_ = v___x_150_;
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_a_151_);
lean_dec(v___x_150_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_156_; 
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 0, v_a_147_);
v___x_156_ = v___x_153_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v_a_147_);
lean_ctor_set(v_reuseFailAlloc_157_, 1, v_a_151_);
v___x_156_ = v_reuseFailAlloc_157_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
return v___x_156_;
}
}
}
}
else
{
lean_dec(v_a_147_);
return v___x_150_;
}
}
else
{
lean_dec(v_d_145_);
lean_dec(v_restore_144_);
lean_dec_ref(v_x_u2082_140_);
return v___x_146_;
}
}
}
LEAN_EXPORT void l_EStateM_orElse_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_138_ = stack[4].m_obj;
lean_object* v_x_u2081_139_ = stack[5].m_obj;
lean_object* v_x_u2082_140_ = stack[6].m_obj;
uint8_t v_useFirstEx_141_ = stack[7].m_num;
lean_object* v_s_142_ = stack[8].m_obj;
lean_object* v_res_160_;
v_res_160_ = l_EStateM_orElse_x27(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_138_, v_x_u2081_139_, v_x_u2082_140_, v_useFirstEx_141_, v_s_142_);
stack->m_obj
 = v_res_160_;
}
LEAN_EXPORT lean_object* l_EStateM_orElse_x27___boxed(lean_object* v_00_u03b5_161_, lean_object* v_00_u03c3_162_, lean_object* v_00_u03b1_163_, lean_object* v_00_u03b4_164_, lean_object* v_inst_165_, lean_object* v_x_u2081_166_, lean_object* v_x_u2082_167_, lean_object* v_useFirstEx_168_, lean_object* v_s_169_){
_start:
{
uint8_t v_useFirstEx_boxed_170_; lean_object* v_res_171_; 
v_useFirstEx_boxed_170_ = lean_unbox(v_useFirstEx_168_);
v_res_171_ = l_EStateM_orElse_x27(v_00_u03b5_161_, v_00_u03c3_162_, v_00_u03b1_163_, v_00_u03b4_164_, v_inst_165_, v_x_u2081_166_, v_x_u2082_167_, v_useFirstEx_boxed_170_, v_s_169_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l_EStateM_instMonadFinally___redArg___lam__0(lean_object* v_00_u03b1_172_, lean_object* v_00_u03b2_173_, lean_object* v_x_174_, lean_object* v_h_175_, lean_object* v_s_176_){
_start:
{
lean_object* v_r_177_; 
v_r_177_ = lean_apply_1(v_x_174_, v_s_176_);
if (lean_obj_tag(v_r_177_) == 0)
{
lean_object* v_a_178_; lean_object* v_a_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_206_; 
v_a_178_ = lean_ctor_get(v_r_177_, 0);
v_a_179_ = lean_ctor_get(v_r_177_, 1);
v_isSharedCheck_206_ = !lean_is_exclusive(v_r_177_);
if (v_isSharedCheck_206_ == 0)
{
v___x_181_ = v_r_177_;
v_isShared_182_ = v_isSharedCheck_206_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_a_179_);
lean_inc(v_a_178_);
lean_dec(v_r_177_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_206_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_183_; lean_object* v___x_184_; 
lean_inc(v_a_178_);
v___x_183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_183_, 0, v_a_178_);
v___x_184_ = lean_apply_2(v_h_175_, v___x_183_, v_a_179_);
if (lean_obj_tag(v___x_184_) == 0)
{
lean_object* v_a_185_; lean_object* v_a_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_196_; 
v_a_185_ = lean_ctor_get(v___x_184_, 0);
v_a_186_ = lean_ctor_get(v___x_184_, 1);
v_isSharedCheck_196_ = !lean_is_exclusive(v___x_184_);
if (v_isSharedCheck_196_ == 0)
{
v___x_188_ = v___x_184_;
v_isShared_189_ = v_isSharedCheck_196_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_a_186_);
lean_inc(v_a_185_);
lean_dec(v___x_184_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_196_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___x_191_; 
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 1, v_a_185_);
v___x_191_ = v___x_181_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v_a_178_);
lean_ctor_set(v_reuseFailAlloc_195_, 1, v_a_185_);
v___x_191_ = v_reuseFailAlloc_195_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
lean_object* v___x_193_; 
if (v_isShared_189_ == 0)
{
lean_ctor_set(v___x_188_, 0, v___x_191_);
v___x_193_ = v___x_188_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v___x_191_);
lean_ctor_set(v_reuseFailAlloc_194_, 1, v_a_186_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
}
}
else
{
lean_object* v_a_197_; lean_object* v_a_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_205_; 
lean_del_object(v___x_181_);
lean_dec(v_a_178_);
v_a_197_ = lean_ctor_get(v___x_184_, 0);
v_a_198_ = lean_ctor_get(v___x_184_, 1);
v_isSharedCheck_205_ = !lean_is_exclusive(v___x_184_);
if (v_isSharedCheck_205_ == 0)
{
v___x_200_ = v___x_184_;
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_a_198_);
lean_inc(v_a_197_);
lean_dec(v___x_184_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v___x_203_; 
if (v_isShared_201_ == 0)
{
v___x_203_ = v___x_200_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v_a_197_);
lean_ctor_set(v_reuseFailAlloc_204_, 1, v_a_198_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
return v___x_203_;
}
}
}
}
}
else
{
lean_object* v_a_207_; lean_object* v_a_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v_a_207_ = lean_ctor_get(v_r_177_, 0);
lean_inc(v_a_207_);
v_a_208_ = lean_ctor_get(v_r_177_, 1);
lean_inc(v_a_208_);
lean_dec_ref_known(v_r_177_, 2);
v___x_209_ = lean_box(0);
v___x_210_ = lean_apply_2(v_h_175_, v___x_209_, v_a_208_);
if (lean_obj_tag(v___x_210_) == 0)
{
lean_object* v_a_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_218_; 
v_a_211_ = lean_ctor_get(v___x_210_, 1);
v_isSharedCheck_218_ = !lean_is_exclusive(v___x_210_);
if (v_isSharedCheck_218_ == 0)
{
lean_object* v_unused_219_; 
v_unused_219_ = lean_ctor_get(v___x_210_, 0);
lean_dec(v_unused_219_);
v___x_213_ = v___x_210_;
v_isShared_214_ = v_isSharedCheck_218_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_a_211_);
lean_dec(v___x_210_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_218_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v___x_216_; 
if (v_isShared_214_ == 0)
{
lean_ctor_set_tag(v___x_213_, 1);
lean_ctor_set(v___x_213_, 0, v_a_207_);
v___x_216_ = v___x_213_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v_a_207_);
lean_ctor_set(v_reuseFailAlloc_217_, 1, v_a_211_);
v___x_216_ = v_reuseFailAlloc_217_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
return v___x_216_;
}
}
}
else
{
lean_object* v_a_220_; lean_object* v_a_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_228_; 
lean_dec(v_a_207_);
v_a_220_ = lean_ctor_get(v___x_210_, 0);
v_a_221_ = lean_ctor_get(v___x_210_, 1);
v_isSharedCheck_228_ = !lean_is_exclusive(v___x_210_);
if (v_isSharedCheck_228_ == 0)
{
v___x_223_ = v___x_210_;
v_isShared_224_ = v_isSharedCheck_228_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_a_221_);
lean_inc(v_a_220_);
lean_dec(v___x_210_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_228_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___x_226_; 
if (v_isShared_224_ == 0)
{
v___x_226_ = v___x_223_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v_a_220_);
lean_ctor_set(v_reuseFailAlloc_227_, 1, v_a_221_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
return v___x_226_;
}
}
}
}
}
}
lean_object* l_EStateM_instMonadFinally___redArg(){
_start:
{
lean_object* v___f_231_; 
v___f_231_ = ((lean_object*)(l_EStateM_instMonadFinally___redArg___closed__0));
return v___f_231_;
}
}
LEAN_EXPORT void l_EStateM_instMonadFinally___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_232_;
v_res_232_ = l_EStateM_instMonadFinally___redArg();
stack->m_obj
 = v_res_232_;
}
LEAN_EXPORT lean_object* l_EStateM_instMonadFinally___redArg___boxed(lean_object* v___dummy_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l_EStateM_instMonadFinally___redArg();
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_EStateM_instMonadFinally(lean_object* v_00_u03b5_235_, lean_object* v_00_u03c3_236_){
_start:
{
lean_object* v___f_237_; 
v___f_237_ = ((lean_object*)(l_EStateM_instMonadFinally___redArg___closed__0));
return v___f_237_;
}
}
LEAN_EXPORT lean_object* l_EStateM_fromStateM___redArg(lean_object* v_x_238_, lean_object* v_s_239_){
_start:
{
lean_object* v___x_240_; lean_object* v_fst_241_; lean_object* v_snd_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_249_; 
v___x_240_ = lean_apply_1(v_x_238_, v_s_239_);
v_fst_241_ = lean_ctor_get(v___x_240_, 0);
v_snd_242_ = lean_ctor_get(v___x_240_, 1);
v_isSharedCheck_249_ = !lean_is_exclusive(v___x_240_);
if (v_isSharedCheck_249_ == 0)
{
v___x_244_ = v___x_240_;
v_isShared_245_ = v_isSharedCheck_249_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_snd_242_);
lean_inc(v_fst_241_);
lean_dec(v___x_240_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_249_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v___x_247_; 
if (v_isShared_245_ == 0)
{
v___x_247_ = v___x_244_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v_fst_241_);
lean_ctor_set(v_reuseFailAlloc_248_, 1, v_snd_242_);
v___x_247_ = v_reuseFailAlloc_248_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
return v___x_247_;
}
}
}
}
LEAN_EXPORT lean_object* l_EStateM_fromStateM(lean_object* v_00_u03b5_250_, lean_object* v_00_u03c3_251_, lean_object* v_00_u03b1_252_, lean_object* v_x_253_, lean_object* v_s_254_){
_start:
{
lean_object* v___x_255_; lean_object* v_fst_256_; lean_object* v_snd_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_264_; 
v___x_255_ = lean_apply_1(v_x_253_, v_s_254_);
v_fst_256_ = lean_ctor_get(v___x_255_, 0);
v_snd_257_ = lean_ctor_get(v___x_255_, 1);
v_isSharedCheck_264_ = !lean_is_exclusive(v___x_255_);
if (v_isSharedCheck_264_ == 0)
{
v___x_259_ = v___x_255_;
v_isShared_260_ = v_isSharedCheck_264_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_snd_257_);
lean_inc(v_fst_256_);
lean_dec(v___x_255_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_264_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_262_; 
if (v_isShared_260_ == 0)
{
v___x_262_ = v___x_259_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v_fst_256_);
lean_ctor_set(v_reuseFailAlloc_263_, 1, v_snd_257_);
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

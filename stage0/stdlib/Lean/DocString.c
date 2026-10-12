// Lean compiler output
// Module: Lean.DocString
// Imports: public import Lean.DocString.Extension public import Lean.DocString.Markdown public import Lean.DocString.Links public import Lean.Parser.Tactic.Doc public import Lean.Parser.Term.Doc public import Lean.ResolveName
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
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Parser_Tactic_Doc_getTacticExtensionString(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_Doc_getRecommendedSpellingString(lean_object*, lean_object*);
lean_object* l_Lean_findSimpleDocString_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_rewriteManualLinks(lean_object*);
lean_object* l_Lean_Parser_Tactic_Doc_alternativeOfTactic(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDocString_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDocString_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findMarkdownDocString_x3f___redArg___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findMarkdownDocString_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findMarkdownDocString_x3f___redArg___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findMarkdownDocString_x3f___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findMarkdownDocString_x3f___redArg___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findMarkdownDocString_x3f___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findMarkdownDocString_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_findMarkdownDocString_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findMarkdownDocString_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_findMarkdownDocString_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_findDocString_x3f(lean_object* v_env_1_, lean_object* v_declName_2_, uint8_t v_includeBuiltin_3_, lean_object* v_options_4_, lean_object* v_currNamespace_5_, lean_object* v_openDecls_6_){
_start:
{
lean_object* v___y_9_; lean_object* v___x_34_; 
lean_inc(v_declName_2_);
lean_inc_ref(v_env_1_);
v___x_34_ = l_Lean_Parser_Tactic_Doc_alternativeOfTactic(v_env_1_, v_declName_2_);
if (lean_obj_tag(v___x_34_) == 0)
{
v___y_9_ = v_declName_2_;
goto v___jp_8_;
}
else
{
lean_object* v_val_35_; 
lean_dec(v_declName_2_);
v_val_35_ = lean_ctor_get(v___x_34_, 0);
lean_inc(v_val_35_);
lean_dec_ref_known(v___x_34_, 1);
v___y_9_ = v_val_35_;
goto v___jp_8_;
}
v___jp_8_:
{
lean_object* v_exts_10_; lean_object* v_spellings_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
lean_inc_n(v___y_9_, 2);
lean_inc_ref_n(v_env_1_, 2);
v_exts_10_ = l_Lean_Parser_Tactic_Doc_getTacticExtensionString(v_env_1_, v___y_9_);
v_spellings_11_ = l_Lean_Parser_Term_Doc_getRecommendedSpellingString(v_env_1_, v___y_9_);
v___x_12_ = lean_box(0);
v___x_13_ = l_Lean_findSimpleDocString_x3f(v_env_1_, v___y_9_, v_includeBuiltin_3_, v_options_4_, v_currNamespace_5_, v_openDecls_6_, v___x_12_);
if (lean_obj_tag(v___x_13_) == 0)
{
lean_object* v_a_14_; 
v_a_14_ = lean_ctor_get(v___x_13_, 0);
lean_inc(v_a_14_);
if (lean_obj_tag(v_a_14_) == 0)
{
lean_dec_ref(v_spellings_11_);
lean_dec_ref(v_exts_10_);
return v___x_13_;
}
else
{
lean_object* v___x_16_; uint8_t v_isShared_17_; uint8_t v_isSharedCheck_32_; 
v_isSharedCheck_32_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_32_ == 0)
{
lean_object* v_unused_33_; 
v_unused_33_ = lean_ctor_get(v___x_13_, 0);
lean_dec(v_unused_33_);
v___x_16_ = v___x_13_;
v_isShared_17_ = v_isSharedCheck_32_;
goto v_resetjp_15_;
}
else
{
lean_dec(v___x_13_);
v___x_16_ = lean_box(0);
v_isShared_17_ = v_isSharedCheck_32_;
goto v_resetjp_15_;
}
v_resetjp_15_:
{
lean_object* v_val_18_; lean_object* v___x_20_; uint8_t v_isShared_21_; uint8_t v_isSharedCheck_31_; 
v_val_18_ = lean_ctor_get(v_a_14_, 0);
v_isSharedCheck_31_ = !lean_is_exclusive(v_a_14_);
if (v_isSharedCheck_31_ == 0)
{
v___x_20_ = v_a_14_;
v_isShared_21_ = v_isSharedCheck_31_;
goto v_resetjp_19_;
}
else
{
lean_inc(v_val_18_);
lean_dec(v_a_14_);
v___x_20_ = lean_box(0);
v_isShared_21_ = v_isSharedCheck_31_;
goto v_resetjp_19_;
}
v_resetjp_19_:
{
lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_26_; 
v___x_22_ = lean_string_append(v_val_18_, v_exts_10_);
lean_dec_ref(v_exts_10_);
v___x_23_ = lean_string_append(v___x_22_, v_spellings_11_);
lean_dec_ref(v_spellings_11_);
v___x_24_ = l_Lean_rewriteManualLinks(v___x_23_);
if (v_isShared_21_ == 0)
{
lean_ctor_set(v___x_20_, 0, v___x_24_);
v___x_26_ = v___x_20_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_30_; 
v_reuseFailAlloc_30_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_30_, 0, v___x_24_);
v___x_26_ = v_reuseFailAlloc_30_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
lean_object* v___x_28_; 
if (v_isShared_17_ == 0)
{
lean_ctor_set(v___x_16_, 0, v___x_26_);
v___x_28_ = v___x_16_;
goto v_reusejp_27_;
}
else
{
lean_object* v_reuseFailAlloc_29_; 
v_reuseFailAlloc_29_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_29_, 0, v___x_26_);
v___x_28_ = v_reuseFailAlloc_29_;
goto v_reusejp_27_;
}
v_reusejp_27_:
{
return v___x_28_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_spellings_11_);
lean_dec_ref(v_exts_10_);
return v___x_13_;
}
}
}
}
LEAN_EXPORT void l_Lean_findDocString_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_1_ = stack[0].m_obj;
lean_object* v_declName_2_ = stack[1].m_obj;
uint8_t v_includeBuiltin_3_ = stack[2].m_num;
lean_object* v_options_4_ = stack[3].m_obj;
lean_object* v_currNamespace_5_ = stack[4].m_obj;
lean_object* v_openDecls_6_ = stack[5].m_obj;
lean_object* v_res_36_;
v_res_36_ = l_Lean_findDocString_x3f(v_env_1_, v_declName_2_, v_includeBuiltin_3_, v_options_4_, v_currNamespace_5_, v_openDecls_6_);
stack->m_obj
 = v_res_36_;
}
LEAN_EXPORT lean_object* l_Lean_findDocString_x3f___boxed(lean_object* v_env_37_, lean_object* v_declName_38_, lean_object* v_includeBuiltin_39_, lean_object* v_options_40_, lean_object* v_currNamespace_41_, lean_object* v_openDecls_42_, lean_object* v_a_43_){
_start:
{
uint8_t v_includeBuiltin_boxed_44_; lean_object* v_res_45_; 
v_includeBuiltin_boxed_44_ = lean_unbox(v_includeBuiltin_39_);
v_res_45_ = l_Lean_findDocString_x3f(v_env_37_, v_declName_38_, v_includeBuiltin_boxed_44_, v_options_40_, v_currNamespace_41_, v_openDecls_42_);
return v_res_45_;
}
}
lean_object* l_Lean_findMarkdownDocString_x3f___redArg___lam__0(lean_object* v_____do__lift_46_, lean_object* v_declName_47_, uint8_t v_includeBuiltin_48_, lean_object* v_____do__lift_49_, lean_object* v_inst_50_, lean_object* v_____do__lift_51_){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_52_ = l_Lean_Options_empty;
v___x_53_ = lean_box(v_includeBuiltin_48_);
v___x_54_ = lean_alloc_closure((void*)(l_Lean_findDocString_x3f___boxed), 7, 6);
lean_closure_set(v___x_54_, 0, v_____do__lift_46_);
lean_closure_set(v___x_54_, 1, v_declName_47_);
lean_closure_set(v___x_54_, 2, v___x_53_);
lean_closure_set(v___x_54_, 3, v___x_52_);
lean_closure_set(v___x_54_, 4, v_____do__lift_49_);
lean_closure_set(v___x_54_, 5, v_____do__lift_51_);
v___x_55_ = lean_apply_2(v_inst_50_, lean_box(0), v___x_54_);
return v___x_55_;
}
}
LEAN_EXPORT void l_Lean_findMarkdownDocString_x3f___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_____do__lift_46_ = stack[0].m_obj;
lean_object* v_declName_47_ = stack[1].m_obj;
uint8_t v_includeBuiltin_48_ = stack[2].m_num;
lean_object* v_____do__lift_49_ = stack[3].m_obj;
lean_object* v_inst_50_ = stack[4].m_obj;
lean_object* v_____do__lift_51_ = stack[5].m_obj;
lean_object* v_res_56_;
v_res_56_ = l_Lean_findMarkdownDocString_x3f___redArg___lam__0(v_____do__lift_46_, v_declName_47_, v_includeBuiltin_48_, v_____do__lift_49_, v_inst_50_, v_____do__lift_51_);
stack->m_obj
 = v_res_56_;
}
LEAN_EXPORT lean_object* l_Lean_findMarkdownDocString_x3f___redArg___lam__0___boxed(lean_object* v_____do__lift_57_, lean_object* v_declName_58_, lean_object* v_includeBuiltin_59_, lean_object* v_____do__lift_60_, lean_object* v_inst_61_, lean_object* v_____do__lift_62_){
_start:
{
uint8_t v_includeBuiltin_boxed_63_; lean_object* v_res_64_; 
v_includeBuiltin_boxed_63_ = lean_unbox(v_includeBuiltin_59_);
v_res_64_ = l_Lean_findMarkdownDocString_x3f___redArg___lam__0(v_____do__lift_57_, v_declName_58_, v_includeBuiltin_boxed_63_, v_____do__lift_60_, v_inst_61_, v_____do__lift_62_);
return v_res_64_;
}
}
lean_object* l_Lean_findMarkdownDocString_x3f___redArg___lam__1(lean_object* v_____do__lift_65_, lean_object* v_declName_66_, uint8_t v_includeBuiltin_67_, lean_object* v_inst_68_, lean_object* v_toBind_69_, lean_object* v_getOpenDecls_70_, lean_object* v_____do__lift_71_){
_start:
{
lean_object* v___x_72_; lean_object* v___f_73_; lean_object* v___x_74_; 
v___x_72_ = lean_box(v_includeBuiltin_67_);
v___f_73_ = lean_alloc_closure((void*)(l_Lean_findMarkdownDocString_x3f___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_73_, 0, v_____do__lift_65_);
lean_closure_set(v___f_73_, 1, v_declName_66_);
lean_closure_set(v___f_73_, 2, v___x_72_);
lean_closure_set(v___f_73_, 3, v_____do__lift_71_);
lean_closure_set(v___f_73_, 4, v_inst_68_);
v___x_74_ = lean_apply_4(v_toBind_69_, lean_box(0), lean_box(0), v_getOpenDecls_70_, v___f_73_);
return v___x_74_;
}
}
LEAN_EXPORT void l_Lean_findMarkdownDocString_x3f___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_____do__lift_65_ = stack[0].m_obj;
lean_object* v_declName_66_ = stack[1].m_obj;
uint8_t v_includeBuiltin_67_ = stack[2].m_num;
lean_object* v_inst_68_ = stack[3].m_obj;
lean_object* v_toBind_69_ = stack[4].m_obj;
lean_object* v_getOpenDecls_70_ = stack[5].m_obj;
lean_object* v_____do__lift_71_ = stack[6].m_obj;
lean_object* v_res_75_;
v_res_75_ = l_Lean_findMarkdownDocString_x3f___redArg___lam__1(v_____do__lift_65_, v_declName_66_, v_includeBuiltin_67_, v_inst_68_, v_toBind_69_, v_getOpenDecls_70_, v_____do__lift_71_);
stack->m_obj
 = v_res_75_;
}
LEAN_EXPORT lean_object* l_Lean_findMarkdownDocString_x3f___redArg___lam__1___boxed(lean_object* v_____do__lift_76_, lean_object* v_declName_77_, lean_object* v_includeBuiltin_78_, lean_object* v_inst_79_, lean_object* v_toBind_80_, lean_object* v_getOpenDecls_81_, lean_object* v_____do__lift_82_){
_start:
{
uint8_t v_includeBuiltin_boxed_83_; lean_object* v_res_84_; 
v_includeBuiltin_boxed_83_ = lean_unbox(v_includeBuiltin_78_);
v_res_84_ = l_Lean_findMarkdownDocString_x3f___redArg___lam__1(v_____do__lift_76_, v_declName_77_, v_includeBuiltin_boxed_83_, v_inst_79_, v_toBind_80_, v_getOpenDecls_81_, v_____do__lift_82_);
return v_res_84_;
}
}
lean_object* l_Lean_findMarkdownDocString_x3f___redArg___lam__2(lean_object* v_inst_85_, lean_object* v_declName_86_, uint8_t v_includeBuiltin_87_, lean_object* v_inst_88_, lean_object* v_toBind_89_, lean_object* v_____do__lift_90_){
_start:
{
lean_object* v_getCurrNamespace_91_; lean_object* v_getOpenDecls_92_; lean_object* v___x_93_; lean_object* v___f_94_; lean_object* v___x_95_; 
v_getCurrNamespace_91_ = lean_ctor_get(v_inst_85_, 0);
lean_inc(v_getCurrNamespace_91_);
v_getOpenDecls_92_ = lean_ctor_get(v_inst_85_, 1);
lean_inc(v_getOpenDecls_92_);
lean_dec_ref(v_inst_85_);
v___x_93_ = lean_box(v_includeBuiltin_87_);
lean_inc(v_toBind_89_);
v___f_94_ = lean_alloc_closure((void*)(l_Lean_findMarkdownDocString_x3f___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_94_, 0, v_____do__lift_90_);
lean_closure_set(v___f_94_, 1, v_declName_86_);
lean_closure_set(v___f_94_, 2, v___x_93_);
lean_closure_set(v___f_94_, 3, v_inst_88_);
lean_closure_set(v___f_94_, 4, v_toBind_89_);
lean_closure_set(v___f_94_, 5, v_getOpenDecls_92_);
v___x_95_ = lean_apply_4(v_toBind_89_, lean_box(0), lean_box(0), v_getCurrNamespace_91_, v___f_94_);
return v___x_95_;
}
}
LEAN_EXPORT void l_Lean_findMarkdownDocString_x3f___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_85_ = stack[0].m_obj;
lean_object* v_declName_86_ = stack[1].m_obj;
uint8_t v_includeBuiltin_87_ = stack[2].m_num;
lean_object* v_inst_88_ = stack[3].m_obj;
lean_object* v_toBind_89_ = stack[4].m_obj;
lean_object* v_____do__lift_90_ = stack[5].m_obj;
lean_object* v_res_96_;
v_res_96_ = l_Lean_findMarkdownDocString_x3f___redArg___lam__2(v_inst_85_, v_declName_86_, v_includeBuiltin_87_, v_inst_88_, v_toBind_89_, v_____do__lift_90_);
stack->m_obj
 = v_res_96_;
}
LEAN_EXPORT lean_object* l_Lean_findMarkdownDocString_x3f___redArg___lam__2___boxed(lean_object* v_inst_97_, lean_object* v_declName_98_, lean_object* v_includeBuiltin_99_, lean_object* v_inst_100_, lean_object* v_toBind_101_, lean_object* v_____do__lift_102_){
_start:
{
uint8_t v_includeBuiltin_boxed_103_; lean_object* v_res_104_; 
v_includeBuiltin_boxed_103_ = lean_unbox(v_includeBuiltin_99_);
v_res_104_ = l_Lean_findMarkdownDocString_x3f___redArg___lam__2(v_inst_97_, v_declName_98_, v_includeBuiltin_boxed_103_, v_inst_100_, v_toBind_101_, v_____do__lift_102_);
return v_res_104_;
}
}
lean_object* l_Lean_findMarkdownDocString_x3f___redArg(lean_object* v_inst_105_, lean_object* v_inst_106_, lean_object* v_inst_107_, lean_object* v_inst_108_, lean_object* v_declName_109_, uint8_t v_includeBuiltin_110_){
_start:
{
lean_object* v_toBind_111_; lean_object* v_getEnv_112_; lean_object* v___x_113_; lean_object* v___f_114_; lean_object* v___x_115_; 
v_toBind_111_ = lean_ctor_get(v_inst_105_, 1);
lean_inc_n(v_toBind_111_, 2);
lean_dec_ref(v_inst_105_);
v_getEnv_112_ = lean_ctor_get(v_inst_106_, 0);
lean_inc(v_getEnv_112_);
lean_dec_ref(v_inst_106_);
v___x_113_ = lean_box(v_includeBuiltin_110_);
v___f_114_ = lean_alloc_closure((void*)(l_Lean_findMarkdownDocString_x3f___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_114_, 0, v_inst_107_);
lean_closure_set(v___f_114_, 1, v_declName_109_);
lean_closure_set(v___f_114_, 2, v___x_113_);
lean_closure_set(v___f_114_, 3, v_inst_108_);
lean_closure_set(v___f_114_, 4, v_toBind_111_);
v___x_115_ = lean_apply_4(v_toBind_111_, lean_box(0), lean_box(0), v_getEnv_112_, v___f_114_);
return v___x_115_;
}
}
LEAN_EXPORT void l_Lean_findMarkdownDocString_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_105_ = stack[0].m_obj;
lean_object* v_inst_106_ = stack[1].m_obj;
lean_object* v_inst_107_ = stack[2].m_obj;
lean_object* v_inst_108_ = stack[3].m_obj;
lean_object* v_declName_109_ = stack[4].m_obj;
uint8_t v_includeBuiltin_110_ = stack[5].m_num;
lean_object* v_res_116_;
v_res_116_ = l_Lean_findMarkdownDocString_x3f___redArg(v_inst_105_, v_inst_106_, v_inst_107_, v_inst_108_, v_declName_109_, v_includeBuiltin_110_);
stack->m_obj
 = v_res_116_;
}
LEAN_EXPORT lean_object* l_Lean_findMarkdownDocString_x3f___redArg___boxed(lean_object* v_inst_117_, lean_object* v_inst_118_, lean_object* v_inst_119_, lean_object* v_inst_120_, lean_object* v_declName_121_, lean_object* v_includeBuiltin_122_){
_start:
{
uint8_t v_includeBuiltin_boxed_123_; lean_object* v_res_124_; 
v_includeBuiltin_boxed_123_ = lean_unbox(v_includeBuiltin_122_);
v_res_124_ = l_Lean_findMarkdownDocString_x3f___redArg(v_inst_117_, v_inst_118_, v_inst_119_, v_inst_120_, v_declName_121_, v_includeBuiltin_boxed_123_);
return v_res_124_;
}
}
lean_object* l_Lean_findMarkdownDocString_x3f(lean_object* v_m_125_, lean_object* v_inst_126_, lean_object* v_inst_127_, lean_object* v_inst_128_, lean_object* v_inst_129_, lean_object* v_declName_130_, uint8_t v_includeBuiltin_131_){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = l_Lean_findMarkdownDocString_x3f___redArg(v_inst_126_, v_inst_127_, v_inst_128_, v_inst_129_, v_declName_130_, v_includeBuiltin_131_);
return v___x_132_;
}
}
LEAN_EXPORT void l_Lean_findMarkdownDocString_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_126_ = stack[1].m_obj;
lean_object* v_inst_127_ = stack[2].m_obj;
lean_object* v_inst_128_ = stack[3].m_obj;
lean_object* v_inst_129_ = stack[4].m_obj;
lean_object* v_declName_130_ = stack[5].m_obj;
uint8_t v_includeBuiltin_131_ = stack[6].m_num;
lean_object* v_res_133_;
v_res_133_ = l_Lean_findMarkdownDocString_x3f(lean_box(0), v_inst_126_, v_inst_127_, v_inst_128_, v_inst_129_, v_declName_130_, v_includeBuiltin_131_);
stack->m_obj
 = v_res_133_;
}
LEAN_EXPORT lean_object* l_Lean_findMarkdownDocString_x3f___boxed(lean_object* v_m_134_, lean_object* v_inst_135_, lean_object* v_inst_136_, lean_object* v_inst_137_, lean_object* v_inst_138_, lean_object* v_declName_139_, lean_object* v_includeBuiltin_140_){
_start:
{
uint8_t v_includeBuiltin_boxed_141_; lean_object* v_res_142_; 
v_includeBuiltin_boxed_141_ = lean_unbox(v_includeBuiltin_140_);
v_res_142_ = l_Lean_findMarkdownDocString_x3f(v_m_134_, v_inst_135_, v_inst_136_, v_inst_137_, v_inst_138_, v_declName_139_, v_includeBuiltin_boxed_141_);
return v_res_142_;
}
}
lean_object* runtime_initialize_Lean_DocString_Extension(uint8_t builtin);
lean_object* runtime_initialize_Lean_DocString_Markdown(uint8_t builtin);
lean_object* runtime_initialize_Lean_DocString_Links(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Tactic_Doc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Term_Doc(uint8_t builtin);
lean_object* runtime_initialize_Lean_ResolveName(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_DocString(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_DocString_Extension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DocString_Markdown(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DocString_Links(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Tactic_Doc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Term_Doc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_ResolveName(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_DocString(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_DocString_Extension(uint8_t builtin);
lean_object* initialize_Lean_DocString_Markdown(uint8_t builtin);
lean_object* initialize_Lean_DocString_Links(uint8_t builtin);
lean_object* initialize_Lean_Parser_Tactic_Doc(uint8_t builtin);
lean_object* initialize_Lean_Parser_Term_Doc(uint8_t builtin);
lean_object* initialize_Lean_ResolveName(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_DocString(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_DocString_Extension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DocString_Markdown(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DocString_Links(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Tactic_Doc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Term_Doc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ResolveName(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DocString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_DocString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_DocString(builtin);
}
#ifdef __cplusplus
}
#endif

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
LEAN_EXPORT lean_object* l_Lean_findDocString_x3f(lean_object* v_env_1_, lean_object* v_declName_2_, uint8_t v_includeBuiltin_3_, lean_object* v_options_4_, lean_object* v_currNamespace_5_, lean_object* v_openDecls_6_){
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
LEAN_EXPORT lean_object* l_Lean_findDocString_x3f___boxed(lean_object* v_env_36_, lean_object* v_declName_37_, lean_object* v_includeBuiltin_38_, lean_object* v_options_39_, lean_object* v_currNamespace_40_, lean_object* v_openDecls_41_, lean_object* v_a_42_){
_start:
{
uint8_t v_includeBuiltin_boxed_43_; lean_object* v_res_44_; 
v_includeBuiltin_boxed_43_ = lean_unbox(v_includeBuiltin_38_);
v_res_44_ = l_Lean_findDocString_x3f(v_env_36_, v_declName_37_, v_includeBuiltin_boxed_43_, v_options_39_, v_currNamespace_40_, v_openDecls_41_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_findMarkdownDocString_x3f___redArg___lam__0(lean_object* v_____do__lift_45_, lean_object* v_declName_46_, uint8_t v_includeBuiltin_47_, lean_object* v_____do__lift_48_, lean_object* v_inst_49_, lean_object* v_____do__lift_50_){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_51_ = l_Lean_Options_empty;
v___x_52_ = lean_box(v_includeBuiltin_47_);
v___x_53_ = lean_alloc_closure((void*)(l_Lean_findDocString_x3f___boxed), 7, 6);
lean_closure_set(v___x_53_, 0, v_____do__lift_45_);
lean_closure_set(v___x_53_, 1, v_declName_46_);
lean_closure_set(v___x_53_, 2, v___x_52_);
lean_closure_set(v___x_53_, 3, v___x_51_);
lean_closure_set(v___x_53_, 4, v_____do__lift_48_);
lean_closure_set(v___x_53_, 5, v_____do__lift_50_);
v___x_54_ = lean_apply_2(v_inst_49_, lean_box(0), v___x_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_findMarkdownDocString_x3f___redArg___lam__0___boxed(lean_object* v_____do__lift_55_, lean_object* v_declName_56_, lean_object* v_includeBuiltin_57_, lean_object* v_____do__lift_58_, lean_object* v_inst_59_, lean_object* v_____do__lift_60_){
_start:
{
uint8_t v_includeBuiltin_boxed_61_; lean_object* v_res_62_; 
v_includeBuiltin_boxed_61_ = lean_unbox(v_includeBuiltin_57_);
v_res_62_ = l_Lean_findMarkdownDocString_x3f___redArg___lam__0(v_____do__lift_55_, v_declName_56_, v_includeBuiltin_boxed_61_, v_____do__lift_58_, v_inst_59_, v_____do__lift_60_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_findMarkdownDocString_x3f___redArg___lam__1(lean_object* v_____do__lift_63_, lean_object* v_declName_64_, uint8_t v_includeBuiltin_65_, lean_object* v_inst_66_, lean_object* v_toBind_67_, lean_object* v_getOpenDecls_68_, lean_object* v_____do__lift_69_){
_start:
{
lean_object* v___x_70_; lean_object* v___f_71_; lean_object* v___x_72_; 
v___x_70_ = lean_box(v_includeBuiltin_65_);
v___f_71_ = lean_alloc_closure((void*)(l_Lean_findMarkdownDocString_x3f___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_71_, 0, v_____do__lift_63_);
lean_closure_set(v___f_71_, 1, v_declName_64_);
lean_closure_set(v___f_71_, 2, v___x_70_);
lean_closure_set(v___f_71_, 3, v_____do__lift_69_);
lean_closure_set(v___f_71_, 4, v_inst_66_);
v___x_72_ = lean_apply_4(v_toBind_67_, lean_box(0), lean_box(0), v_getOpenDecls_68_, v___f_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_findMarkdownDocString_x3f___redArg___lam__1___boxed(lean_object* v_____do__lift_73_, lean_object* v_declName_74_, lean_object* v_includeBuiltin_75_, lean_object* v_inst_76_, lean_object* v_toBind_77_, lean_object* v_getOpenDecls_78_, lean_object* v_____do__lift_79_){
_start:
{
uint8_t v_includeBuiltin_boxed_80_; lean_object* v_res_81_; 
v_includeBuiltin_boxed_80_ = lean_unbox(v_includeBuiltin_75_);
v_res_81_ = l_Lean_findMarkdownDocString_x3f___redArg___lam__1(v_____do__lift_73_, v_declName_74_, v_includeBuiltin_boxed_80_, v_inst_76_, v_toBind_77_, v_getOpenDecls_78_, v_____do__lift_79_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_findMarkdownDocString_x3f___redArg___lam__2(lean_object* v_inst_82_, lean_object* v_declName_83_, uint8_t v_includeBuiltin_84_, lean_object* v_inst_85_, lean_object* v_toBind_86_, lean_object* v_____do__lift_87_){
_start:
{
lean_object* v_getCurrNamespace_88_; lean_object* v_getOpenDecls_89_; lean_object* v___x_90_; lean_object* v___f_91_; lean_object* v___x_92_; 
v_getCurrNamespace_88_ = lean_ctor_get(v_inst_82_, 0);
lean_inc(v_getCurrNamespace_88_);
v_getOpenDecls_89_ = lean_ctor_get(v_inst_82_, 1);
lean_inc(v_getOpenDecls_89_);
lean_dec_ref(v_inst_82_);
v___x_90_ = lean_box(v_includeBuiltin_84_);
lean_inc(v_toBind_86_);
v___f_91_ = lean_alloc_closure((void*)(l_Lean_findMarkdownDocString_x3f___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_91_, 0, v_____do__lift_87_);
lean_closure_set(v___f_91_, 1, v_declName_83_);
lean_closure_set(v___f_91_, 2, v___x_90_);
lean_closure_set(v___f_91_, 3, v_inst_85_);
lean_closure_set(v___f_91_, 4, v_toBind_86_);
lean_closure_set(v___f_91_, 5, v_getOpenDecls_89_);
v___x_92_ = lean_apply_4(v_toBind_86_, lean_box(0), lean_box(0), v_getCurrNamespace_88_, v___f_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_findMarkdownDocString_x3f___redArg___lam__2___boxed(lean_object* v_inst_93_, lean_object* v_declName_94_, lean_object* v_includeBuiltin_95_, lean_object* v_inst_96_, lean_object* v_toBind_97_, lean_object* v_____do__lift_98_){
_start:
{
uint8_t v_includeBuiltin_boxed_99_; lean_object* v_res_100_; 
v_includeBuiltin_boxed_99_ = lean_unbox(v_includeBuiltin_95_);
v_res_100_ = l_Lean_findMarkdownDocString_x3f___redArg___lam__2(v_inst_93_, v_declName_94_, v_includeBuiltin_boxed_99_, v_inst_96_, v_toBind_97_, v_____do__lift_98_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_findMarkdownDocString_x3f___redArg(lean_object* v_inst_101_, lean_object* v_inst_102_, lean_object* v_inst_103_, lean_object* v_inst_104_, lean_object* v_declName_105_, uint8_t v_includeBuiltin_106_){
_start:
{
lean_object* v_toBind_107_; lean_object* v_getEnv_108_; lean_object* v___x_109_; lean_object* v___f_110_; lean_object* v___x_111_; 
v_toBind_107_ = lean_ctor_get(v_inst_101_, 1);
lean_inc_n(v_toBind_107_, 2);
lean_dec_ref(v_inst_101_);
v_getEnv_108_ = lean_ctor_get(v_inst_102_, 0);
lean_inc(v_getEnv_108_);
lean_dec_ref(v_inst_102_);
v___x_109_ = lean_box(v_includeBuiltin_106_);
v___f_110_ = lean_alloc_closure((void*)(l_Lean_findMarkdownDocString_x3f___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_110_, 0, v_inst_103_);
lean_closure_set(v___f_110_, 1, v_declName_105_);
lean_closure_set(v___f_110_, 2, v___x_109_);
lean_closure_set(v___f_110_, 3, v_inst_104_);
lean_closure_set(v___f_110_, 4, v_toBind_107_);
v___x_111_ = lean_apply_4(v_toBind_107_, lean_box(0), lean_box(0), v_getEnv_108_, v___f_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_findMarkdownDocString_x3f___redArg___boxed(lean_object* v_inst_112_, lean_object* v_inst_113_, lean_object* v_inst_114_, lean_object* v_inst_115_, lean_object* v_declName_116_, lean_object* v_includeBuiltin_117_){
_start:
{
uint8_t v_includeBuiltin_boxed_118_; lean_object* v_res_119_; 
v_includeBuiltin_boxed_118_ = lean_unbox(v_includeBuiltin_117_);
v_res_119_ = l_Lean_findMarkdownDocString_x3f___redArg(v_inst_112_, v_inst_113_, v_inst_114_, v_inst_115_, v_declName_116_, v_includeBuiltin_boxed_118_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_findMarkdownDocString_x3f(lean_object* v_m_120_, lean_object* v_inst_121_, lean_object* v_inst_122_, lean_object* v_inst_123_, lean_object* v_inst_124_, lean_object* v_declName_125_, uint8_t v_includeBuiltin_126_){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = l_Lean_findMarkdownDocString_x3f___redArg(v_inst_121_, v_inst_122_, v_inst_123_, v_inst_124_, v_declName_125_, v_includeBuiltin_126_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_findMarkdownDocString_x3f___boxed(lean_object* v_m_128_, lean_object* v_inst_129_, lean_object* v_inst_130_, lean_object* v_inst_131_, lean_object* v_inst_132_, lean_object* v_declName_133_, lean_object* v_includeBuiltin_134_){
_start:
{
uint8_t v_includeBuiltin_boxed_135_; lean_object* v_res_136_; 
v_includeBuiltin_boxed_135_ = lean_unbox(v_includeBuiltin_134_);
v_res_136_ = l_Lean_findMarkdownDocString_x3f(v_m_128_, v_inst_129_, v_inst_130_, v_inst_131_, v_inst_132_, v_declName_133_, v_includeBuiltin_boxed_135_);
return v_res_136_;
}
}
lean_object* runtime_initialize_Lean_DocString_Extension(uint8_t builtin);
lean_object* runtime_initialize_Lean_DocString_Markdown(uint8_t builtin);
lean_object* runtime_initialize_Lean_DocString_Links(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Tactic_Doc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Term_Doc(uint8_t builtin);
lean_object* runtime_initialize_Lean_ResolveName(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_DocString(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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

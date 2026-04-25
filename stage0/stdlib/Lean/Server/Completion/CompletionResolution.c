// Lean compiler output
// Module: Lean.Server.Completion.CompletionResolution
// Imports: public import Lean.Data.Lsp public import Lean.Server.Completion.CompletionInfoSelection public import Lean.Linter.Deprecated
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
lean_object* l_Lean_Meta_ppExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Completion_findCompletionInfosAt(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Elab_CompletionInfo_lctx(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_addParenHeuristic(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_findDocString_x3f(lean_object*, lean_object*, uint8_t);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
extern lean_object* l_Lean_Linter_instInhabitedDeprecationEntry_default;
extern lean_object* l_Lean_Linter_deprecatedAttr;
lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_CompletionItem_resolve___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_CompletionItem_resolve___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_CompletionItem_resolve___closed__0 = (const lean_object*)&l_Lean_Lsp_CompletionItem_resolve___closed__0_value;
static const lean_string_object l_Lean_Lsp_CompletionItem_resolve___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\n\n"};
static const lean_object* l_Lean_Lsp_CompletionItem_resolve___closed__1 = (const lean_object*)&l_Lean_Lsp_CompletionItem_resolve___closed__1_value;
static const lean_string_object l_Lean_Lsp_CompletionItem_resolve___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_Lean_Lsp_CompletionItem_resolve___closed__2 = (const lean_object*)&l_Lean_Lsp_CompletionItem_resolve___closed__2_value;
static const lean_string_object l_Lean_Lsp_CompletionItem_resolve___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "(some "};
static const lean_object* l_Lean_Lsp_CompletionItem_resolve___closed__3 = (const lean_object*)&l_Lean_Lsp_CompletionItem_resolve___closed__3_value;
static const lean_string_object l_Lean_Lsp_CompletionItem_resolve___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_Lsp_CompletionItem_resolve___closed__4 = (const lean_object*)&l_Lean_Lsp_CompletionItem_resolve___closed__4_value;
static const lean_string_object l_Lean_Lsp_CompletionItem_resolve___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Lsp_CompletionItem_resolve___closed__5 = (const lean_object*)&l_Lean_Lsp_CompletionItem_resolve___closed__5_value;
static const lean_string_object l_Lean_Lsp_CompletionItem_resolve___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "` has been deprecated, use `"};
static const lean_object* l_Lean_Lsp_CompletionItem_resolve___closed__6 = (const lean_object*)&l_Lean_Lsp_CompletionItem_resolve___closed__6_value;
static const lean_string_object l_Lean_Lsp_CompletionItem_resolve___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "` instead."};
static const lean_object* l_Lean_Lsp_CompletionItem_resolve___closed__7 = (const lean_object*)&l_Lean_Lsp_CompletionItem_resolve___closed__7_value;
static const lean_string_object l_Lean_Lsp_CompletionItem_resolve___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "` has been deprecated."};
static const lean_object* l_Lean_Lsp_CompletionItem_resolve___closed__8 = (const lean_object*)&l_Lean_Lsp_CompletionItem_resolve___closed__8_value;
static const lean_closure_object l_Lean_Lsp_CompletionItem_resolve___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_CompletionItem_resolve___lam__2___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_CompletionItem_resolve___closed__9 = (const lean_object*)&l_Lean_Lsp_CompletionItem_resolve___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_resolveCompletionItem_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_resolveCompletionItem_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___redArg___lam__0(lean_object* v_k_1_, lean_object* v_b_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_){
_start:
{
lean_object* v___x_8_; 
lean_inc(v___y_6_);
lean_inc_ref(v___y_5_);
lean_inc(v___y_4_);
lean_inc_ref(v___y_3_);
v___x_8_ = lean_apply_6(v_k_1_, v_b_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, lean_box(0));
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___redArg___lam__0___boxed(lean_object* v_k_9_, lean_object* v_b_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___redArg___lam__0(v_k_9_, v_b_10_, v___y_11_, v___y_12_, v___y_13_, v___y_14_);
lean_dec(v___y_14_);
lean_dec_ref(v___y_13_);
lean_dec(v___y_12_);
lean_dec_ref(v___y_11_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___redArg(lean_object* v_name_17_, uint8_t v_bi_18_, lean_object* v_type_19_, lean_object* v_k_20_, uint8_t v_kind_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_){
_start:
{
lean_object* v___f_27_; lean_object* v___x_28_; 
v___f_27_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_27_, 0, v_k_20_);
v___x_28_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_17_, v_bi_18_, v_type_19_, v___f_27_, v_kind_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_);
if (lean_obj_tag(v___x_28_) == 0)
{
lean_object* v_a_29_; lean_object* v___x_31_; uint8_t v_isShared_32_; uint8_t v_isSharedCheck_36_; 
v_a_29_ = lean_ctor_get(v___x_28_, 0);
v_isSharedCheck_36_ = !lean_is_exclusive(v___x_28_);
if (v_isSharedCheck_36_ == 0)
{
v___x_31_ = v___x_28_;
v_isShared_32_ = v_isSharedCheck_36_;
goto v_resetjp_30_;
}
else
{
lean_inc(v_a_29_);
lean_dec(v___x_28_);
v___x_31_ = lean_box(0);
v_isShared_32_ = v_isSharedCheck_36_;
goto v_resetjp_30_;
}
v_resetjp_30_:
{
lean_object* v___x_34_; 
if (v_isShared_32_ == 0)
{
v___x_34_ = v___x_31_;
goto v_reusejp_33_;
}
else
{
lean_object* v_reuseFailAlloc_35_; 
v_reuseFailAlloc_35_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_35_, 0, v_a_29_);
v___x_34_ = v_reuseFailAlloc_35_;
goto v_reusejp_33_;
}
v_reusejp_33_:
{
return v___x_34_;
}
}
}
else
{
lean_object* v_a_37_; lean_object* v___x_39_; uint8_t v_isShared_40_; uint8_t v_isSharedCheck_44_; 
v_a_37_ = lean_ctor_get(v___x_28_, 0);
v_isSharedCheck_44_ = !lean_is_exclusive(v___x_28_);
if (v_isSharedCheck_44_ == 0)
{
v___x_39_ = v___x_28_;
v_isShared_40_ = v_isSharedCheck_44_;
goto v_resetjp_38_;
}
else
{
lean_inc(v_a_37_);
lean_dec(v___x_28_);
v___x_39_ = lean_box(0);
v_isShared_40_ = v_isSharedCheck_44_;
goto v_resetjp_38_;
}
v_resetjp_38_:
{
lean_object* v___x_42_; 
if (v_isShared_40_ == 0)
{
v___x_42_ = v___x_39_;
goto v_reusejp_41_;
}
else
{
lean_object* v_reuseFailAlloc_43_; 
v_reuseFailAlloc_43_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_43_, 0, v_a_37_);
v___x_42_ = v_reuseFailAlloc_43_;
goto v_reusejp_41_;
}
v_reusejp_41_:
{
return v___x_42_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___redArg___boxed(lean_object* v_name_45_, lean_object* v_bi_46_, lean_object* v_type_47_, lean_object* v_k_48_, lean_object* v_kind_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_){
_start:
{
uint8_t v_bi_boxed_55_; uint8_t v_kind_boxed_56_; lean_object* v_res_57_; 
v_bi_boxed_55_ = lean_unbox(v_bi_46_);
v_kind_boxed_56_ = lean_unbox(v_kind_49_);
v_res_57_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___redArg(v_name_45_, v_bi_boxed_55_, v_type_47_, v_k_48_, v_kind_boxed_56_, v___y_50_, v___y_51_, v___y_52_, v___y_53_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
lean_dec(v___y_51_);
lean_dec_ref(v___y_50_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0(lean_object* v_00_u03b1_58_, lean_object* v_name_59_, uint8_t v_bi_60_, lean_object* v_type_61_, lean_object* v_k_62_, uint8_t v_kind_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___redArg(v_name_59_, v_bi_60_, v_type_61_, v_k_62_, v_kind_63_, v___y_64_, v___y_65_, v___y_66_, v___y_67_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___boxed(lean_object* v_00_u03b1_70_, lean_object* v_name_71_, lean_object* v_bi_72_, lean_object* v_type_73_, lean_object* v_k_74_, lean_object* v_kind_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_){
_start:
{
uint8_t v_bi_boxed_81_; uint8_t v_kind_boxed_82_; lean_object* v_res_83_; 
v_bi_boxed_81_ = lean_unbox(v_bi_72_);
v_kind_boxed_82_ = lean_unbox(v_kind_75_);
v_res_83_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0(v_00_u03b1_70_, v_name_71_, v_bi_boxed_81_, v_type_73_, v_k_74_, v_kind_boxed_82_, v___y_76_, v___y_77_, v___y_78_, v___y_79_);
lean_dec(v___y_79_);
lean_dec_ref(v___y_78_);
lean_dec(v___y_77_);
lean_dec_ref(v___y_76_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg___lam__0___boxed(lean_object* v_body_84_, lean_object* v_k_85_, lean_object* v_arg_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg___lam__0(v_body_84_, v_k_85_, v_arg_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_);
lean_dec(v___y_90_);
lean_dec_ref(v___y_89_);
lean_dec(v___y_88_);
lean_dec_ref(v___y_87_);
lean_dec_ref(v_arg_86_);
lean_dec_ref(v_body_84_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg(lean_object* v_e_93_, lean_object* v_k_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_){
_start:
{
if (lean_obj_tag(v_e_93_) == 7)
{
lean_object* v_binderName_100_; lean_object* v_binderType_101_; lean_object* v_body_102_; uint8_t v_binderInfo_103_; uint8_t v___x_104_; uint8_t v___x_105_; 
v_binderName_100_ = lean_ctor_get(v_e_93_, 0);
v_binderType_101_ = lean_ctor_get(v_e_93_, 1);
v_body_102_ = lean_ctor_get(v_e_93_, 2);
v_binderInfo_103_ = lean_ctor_get_uint8(v_e_93_, sizeof(void*)*3 + 8);
v___x_104_ = 1;
v___x_105_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_103_, v___x_104_);
if (v___x_105_ == 0)
{
lean_object* v___x_106_; 
lean_inc(v_a_98_);
lean_inc_ref(v_a_97_);
lean_inc(v_a_96_);
lean_inc_ref(v_a_95_);
v___x_106_ = lean_apply_6(v_k_94_, v_e_93_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, lean_box(0));
return v___x_106_;
}
else
{
lean_object* v___f_107_; uint8_t v___x_108_; lean_object* v___x_109_; 
lean_inc_ref(v_body_102_);
lean_inc_ref(v_binderType_101_);
lean_inc(v_binderName_100_);
lean_dec_ref(v_e_93_);
v___f_107_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_107_, 0, v_body_102_);
lean_closure_set(v___f_107_, 1, v_k_94_);
v___x_108_ = 0;
v___x_109_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___redArg(v_binderName_100_, v_binderInfo_103_, v_binderType_101_, v___f_107_, v___x_108_, v_a_95_, v_a_96_, v_a_97_, v_a_98_);
return v___x_109_;
}
}
else
{
lean_object* v___x_110_; 
lean_inc(v_a_98_);
lean_inc_ref(v_a_97_);
lean_inc(v_a_96_);
lean_inc_ref(v_a_95_);
v___x_110_ = lean_apply_6(v_k_94_, v_e_93_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, lean_box(0));
return v___x_110_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg___lam__0(lean_object* v_body_111_, lean_object* v_k_112_, lean_object* v_arg_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_119_ = lean_expr_instantiate1(v_body_111_, v_arg_113_);
v___x_120_ = l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg(v___x_119_, v_k_112_, v___y_114_, v___y_115_, v___y_116_, v___y_117_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg___boxed(lean_object* v_e_121_, lean_object* v_k_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg(v_e_121_, v_k_122_, v_a_123_, v_a_124_, v_a_125_, v_a_126_);
lean_dec(v_a_126_);
lean_dec_ref(v_a_125_);
lean_dec(v_a_124_);
lean_dec_ref(v_a_123_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix(lean_object* v_00_u03b1_129_, lean_object* v_e_130_, lean_object* v_k_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg(v_e_130_, v_k_131_, v_a_132_, v_a_133_, v_a_134_, v_a_135_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___boxed(lean_object* v_00_u03b1_138_, lean_object* v_e_139_, lean_object* v_k_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix(v_00_u03b1_138_, v_e_139_, v_k_140_, v_a_141_, v_a_142_, v_a_143_, v_a_144_);
lean_dec(v_a_144_);
lean_dec_ref(v_a_143_);
lean_dec(v_a_142_);
lean_dec_ref(v_a_141_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___lam__0(lean_object* v_docValue_147_){
_start:
{
uint8_t v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_148_ = 1;
v___x_149_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_149_, 0, v_docValue_147_);
lean_ctor_set_uint8(v___x_149_, sizeof(void*)*1, v___x_148_);
v___x_150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_150_, 0, v___x_149_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___lam__1(lean_object* v_documentation_x3f_151_, lean_object* v___f_152_, lean_object* v_docStringPrefix_153_){
_start:
{
if (lean_obj_tag(v_docStringPrefix_153_) == 0)
{
lean_dec_ref(v___f_152_);
lean_inc(v_documentation_x3f_151_);
return v_documentation_x3f_151_;
}
else
{
lean_object* v_val_154_; lean_object* v___x_155_; 
v_val_154_ = lean_ctor_get(v_docStringPrefix_153_, 0);
lean_inc(v_val_154_);
lean_dec_ref(v_docStringPrefix_153_);
v___x_155_ = lean_apply_1(v___f_152_, v_val_154_);
return v___x_155_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___lam__1___boxed(lean_object* v_documentation_x3f_156_, lean_object* v___f_157_, lean_object* v_docStringPrefix_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l_Lean_Lsp_CompletionItem_resolve___lam__1(v_documentation_x3f_156_, v___f_157_, v_docStringPrefix_158_);
lean_dec(v_documentation_x3f_156_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___lam__2(lean_object* v_typeWithoutImplicits_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = l_Lean_Meta_ppExpr(v_typeWithoutImplicits_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_);
if (lean_obj_tag(v___x_166_) == 0)
{
lean_object* v_a_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_177_; 
v_a_167_ = lean_ctor_get(v___x_166_, 0);
v_isSharedCheck_177_ = !lean_is_exclusive(v___x_166_);
if (v_isSharedCheck_177_ == 0)
{
v___x_169_ = v___x_166_;
v_isShared_170_ = v_isSharedCheck_177_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_a_167_);
lean_dec(v___x_166_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_177_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_175_; 
v___x_171_ = l_Std_Format_defWidth;
v___x_172_ = lean_unsigned_to_nat(0u);
v___x_173_ = l_Std_Format_pretty(v_a_167_, v___x_171_, v___x_172_, v___x_172_);
if (v_isShared_170_ == 0)
{
lean_ctor_set(v___x_169_, 0, v___x_173_);
v___x_175_ = v___x_169_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_185_; 
v_a_178_ = lean_ctor_get(v___x_166_, 0);
v_isSharedCheck_185_ = !lean_is_exclusive(v___x_166_);
if (v_isSharedCheck_185_ == 0)
{
v___x_180_ = v___x_166_;
v_isShared_181_ = v_isSharedCheck_185_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_a_178_);
lean_dec(v___x_166_);
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
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___lam__2___boxed(lean_object* v_typeWithoutImplicits_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Lean_Lsp_CompletionItem_resolve___lam__2(v_typeWithoutImplicits_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_);
lean_dec(v___y_190_);
lean_dec_ref(v___y_189_);
lean_dec(v___y_188_);
lean_dec_ref(v___y_187_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve(lean_object* v_item_203_, lean_object* v_id_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_){
_start:
{
lean_object* v___y_211_; lean_object* v___y_212_; lean_object* v___y_213_; lean_object* v___y_214_; lean_object* v___y_215_; lean_object* v___y_216_; lean_object* v___y_217_; lean_object* v___y_218_; lean_object* v___x_221_; lean_object* v_env_222_; lean_object* v_label_223_; lean_object* v_detail_x3f_224_; lean_object* v_documentation_x3f_225_; lean_object* v_kind_x3f_226_; lean_object* v_textEdit_x3f_227_; lean_object* v_sortText_x3f_228_; lean_object* v_data_x3f_229_; lean_object* v_tags_x3f_230_; lean_object* v___f_231_; lean_object* v___y_233_; lean_object* v___y_234_; lean_object* v___y_235_; lean_object* v___y_236_; lean_object* v___y_237_; lean_object* v___y_238_; lean_object* v___y_239_; lean_object* v___y_240_; lean_object* v___y_241_; lean_object* v___y_247_; lean_object* v___y_248_; lean_object* v___y_249_; lean_object* v___y_250_; lean_object* v___y_251_; lean_object* v___y_252_; lean_object* v___y_253_; lean_object* v___y_254_; lean_object* v___y_255_; lean_object* v___y_256_; lean_object* v_docString_x3f_257_; lean_object* v___y_272_; lean_object* v___y_273_; lean_object* v___y_274_; lean_object* v___y_275_; lean_object* v___y_276_; lean_object* v___y_277_; lean_object* v___y_278_; lean_object* v___y_279_; lean_object* v___y_280_; lean_object* v___y_281_; uint8_t v___y_282_; lean_object* v___y_283_; lean_object* v___y_308_; lean_object* v___y_309_; lean_object* v___y_310_; lean_object* v___y_311_; lean_object* v___y_312_; lean_object* v___y_313_; lean_object* v___y_314_; lean_object* v___y_315_; lean_object* v___y_316_; lean_object* v___y_317_; uint8_t v___y_318_; lean_object* v___y_319_; lean_object* v_item_322_; lean_object* v_label_323_; lean_object* v_detail_x3f_324_; lean_object* v_documentation_x3f_325_; lean_object* v_kind_x3f_326_; lean_object* v_textEdit_x3f_327_; lean_object* v_sortText_x3f_328_; lean_object* v_data_x3f_329_; lean_object* v_tags_x3f_330_; lean_object* v___y_331_; lean_object* v_a_384_; 
v___x_221_ = lean_st_ref_get(v_a_208_);
v_env_222_ = lean_ctor_get(v___x_221_, 0);
lean_inc_ref(v_env_222_);
lean_dec(v___x_221_);
v_label_223_ = lean_ctor_get(v_item_203_, 0);
lean_inc_ref(v_label_223_);
v_detail_x3f_224_ = lean_ctor_get(v_item_203_, 1);
lean_inc(v_detail_x3f_224_);
v_documentation_x3f_225_ = lean_ctor_get(v_item_203_, 2);
lean_inc(v_documentation_x3f_225_);
v_kind_x3f_226_ = lean_ctor_get(v_item_203_, 3);
lean_inc(v_kind_x3f_226_);
v_textEdit_x3f_227_ = lean_ctor_get(v_item_203_, 4);
lean_inc(v_textEdit_x3f_227_);
v_sortText_x3f_228_ = lean_ctor_get(v_item_203_, 5);
lean_inc(v_sortText_x3f_228_);
v_data_x3f_229_ = lean_ctor_get(v_item_203_, 6);
lean_inc(v_data_x3f_229_);
v_tags_x3f_230_ = lean_ctor_get(v_item_203_, 7);
lean_inc(v_tags_x3f_230_);
v___f_231_ = ((lean_object*)(l_Lean_Lsp_CompletionItem_resolve___closed__0));
if (lean_obj_tag(v_detail_x3f_224_) == 0)
{
lean_object* v___f_386_; lean_object* v_val_388_; 
lean_dec_ref(v_item_203_);
v___f_386_ = ((lean_object*)(l_Lean_Lsp_CompletionItem_resolve___closed__9));
if (lean_obj_tag(v_id_204_) == 0)
{
lean_object* v_declName_400_; uint8_t v___x_401_; lean_object* v___x_402_; 
v_declName_400_ = lean_ctor_get(v_id_204_, 0);
v___x_401_ = 0;
lean_inc(v_declName_400_);
lean_inc_ref(v_env_222_);
v___x_402_ = l_Lean_Environment_find_x3f(v_env_222_, v_declName_400_, v___x_401_);
if (lean_obj_tag(v___x_402_) == 0)
{
v_a_384_ = v_detail_x3f_224_;
goto v___jp_383_;
}
else
{
lean_object* v_val_403_; lean_object* v___x_404_; 
v_val_403_ = lean_ctor_get(v___x_402_, 0);
lean_inc(v_val_403_);
lean_dec_ref(v___x_402_);
v___x_404_ = l_Lean_ConstantInfo_type(v_val_403_);
lean_dec(v_val_403_);
v_val_388_ = v___x_404_;
goto v___jp_387_;
}
}
else
{
lean_object* v_id_405_; lean_object* v_lctx_406_; lean_object* v___x_407_; 
v_id_405_ = lean_ctor_get(v_id_204_, 0);
v_lctx_406_ = lean_ctor_get(v_a_205_, 2);
lean_inc(v_id_405_);
lean_inc_ref(v_lctx_406_);
v___x_407_ = lean_local_ctx_find(v_lctx_406_, v_id_405_);
if (lean_obj_tag(v___x_407_) == 0)
{
v_a_384_ = v_detail_x3f_224_;
goto v___jp_383_;
}
else
{
lean_object* v_val_408_; lean_object* v___x_409_; 
v_val_408_ = lean_ctor_get(v___x_407_, 0);
lean_inc(v_val_408_);
lean_dec_ref(v___x_407_);
v___x_409_ = l_Lean_LocalDecl_type(v_val_408_);
lean_dec(v_val_408_);
v_val_388_ = v___x_409_;
goto v___jp_387_;
}
}
v___jp_387_:
{
lean_object* v___x_389_; 
v___x_389_ = l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg(v_val_388_, v___f_386_, v_a_205_, v_a_206_, v_a_207_, v_a_208_);
if (lean_obj_tag(v___x_389_) == 0)
{
lean_object* v_a_390_; lean_object* v___x_391_; 
v_a_390_ = lean_ctor_get(v___x_389_, 0);
lean_inc(v_a_390_);
lean_dec_ref(v___x_389_);
v___x_391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_391_, 0, v_a_390_);
v_a_384_ = v___x_391_;
goto v___jp_383_;
}
else
{
lean_object* v_a_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_399_; 
lean_dec(v_tags_x3f_230_);
lean_dec(v_data_x3f_229_);
lean_dec(v_sortText_x3f_228_);
lean_dec(v_textEdit_x3f_227_);
lean_dec(v_kind_x3f_226_);
lean_dec(v_documentation_x3f_225_);
lean_dec_ref(v_label_223_);
lean_dec_ref(v_env_222_);
lean_dec_ref(v_id_204_);
v_a_392_ = lean_ctor_get(v___x_389_, 0);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_389_);
if (v_isSharedCheck_399_ == 0)
{
v___x_394_ = v___x_389_;
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_a_392_);
lean_dec(v___x_389_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_397_; 
if (v_isShared_395_ == 0)
{
v___x_397_ = v___x_394_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_a_392_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
}
}
}
else
{
v_item_322_ = v_item_203_;
v_label_323_ = v_label_223_;
v_detail_x3f_324_ = v_detail_x3f_224_;
v_documentation_x3f_325_ = v_documentation_x3f_225_;
v_kind_x3f_326_ = v_kind_x3f_226_;
v_textEdit_x3f_327_ = v_textEdit_x3f_227_;
v_sortText_x3f_328_ = v_sortText_x3f_228_;
v_data_x3f_329_ = v_data_x3f_229_;
v_tags_x3f_330_ = v_tags_x3f_230_;
v___y_331_ = v_a_207_;
goto v___jp_321_;
}
v___jp_210_:
{
lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_219_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_219_, 0, v___y_215_);
lean_ctor_set(v___x_219_, 1, v___y_214_);
lean_ctor_set(v___x_219_, 2, v___y_218_);
lean_ctor_set(v___x_219_, 3, v___y_217_);
lean_ctor_set(v___x_219_, 4, v___y_213_);
lean_ctor_set(v___x_219_, 5, v___y_211_);
lean_ctor_set(v___x_219_, 6, v___y_212_);
lean_ctor_set(v___x_219_, 7, v___y_216_);
v___x_220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_220_, 0, v___x_219_);
return v___x_220_;
}
v___jp_232_:
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_242_ = ((lean_object*)(l_Lean_Lsp_CompletionItem_resolve___closed__1));
v___x_243_ = lean_string_append(v___y_241_, v___x_242_);
v___x_244_ = lean_string_append(v___x_243_, v___y_235_);
lean_dec_ref(v___y_235_);
v___x_245_ = l_Lean_Lsp_CompletionItem_resolve___lam__0(v___x_244_);
v___y_211_ = v___y_233_;
v___y_212_ = v___y_234_;
v___y_213_ = v___y_236_;
v___y_214_ = v___y_237_;
v___y_215_ = v___y_238_;
v___y_216_ = v___y_239_;
v___y_217_ = v___y_240_;
v___y_218_ = v___x_245_;
goto v___jp_210_;
}
v___jp_246_:
{
if (lean_obj_tag(v___y_252_) == 0)
{
if (lean_obj_tag(v_docString_x3f_257_) == 0)
{
lean_dec_ref(v___y_249_);
v___y_211_ = v___y_247_;
v___y_212_ = v___y_248_;
v___y_213_ = v___y_250_;
v___y_214_ = v___y_251_;
v___y_215_ = v___y_253_;
v___y_216_ = v___y_255_;
v___y_217_ = v___y_256_;
v___y_218_ = v___y_254_;
goto v___jp_210_;
}
else
{
lean_object* v___x_258_; 
lean_dec(v___y_254_);
v___x_258_ = lean_apply_1(v___y_249_, v_docString_x3f_257_);
v___y_211_ = v___y_247_;
v___y_212_ = v___y_248_;
v___y_213_ = v___y_250_;
v___y_214_ = v___y_251_;
v___y_215_ = v___y_253_;
v___y_216_ = v___y_255_;
v___y_217_ = v___y_256_;
v___y_218_ = v___x_258_;
goto v___jp_210_;
}
}
else
{
lean_dec(v___y_254_);
if (lean_obj_tag(v_docString_x3f_257_) == 0)
{
lean_object* v_val_259_; lean_object* v___x_260_; 
v_val_259_ = lean_ctor_get(v___y_252_, 0);
lean_inc(v_val_259_);
lean_dec_ref(v___y_252_);
v___x_260_ = lean_apply_1(v___y_249_, v_val_259_);
v___y_211_ = v___y_247_;
v___y_212_ = v___y_248_;
v___y_213_ = v___y_250_;
v___y_214_ = v___y_251_;
v___y_215_ = v___y_253_;
v___y_216_ = v___y_255_;
v___y_217_ = v___y_256_;
v___y_218_ = v___x_260_;
goto v___jp_210_;
}
else
{
lean_object* v_val_261_; 
lean_dec_ref(v___y_249_);
v_val_261_ = lean_ctor_get(v___y_252_, 0);
lean_inc(v_val_261_);
lean_dec_ref(v___y_252_);
if (lean_obj_tag(v_val_261_) == 0)
{
lean_object* v_val_262_; lean_object* v___x_263_; 
v_val_262_ = lean_ctor_get(v_docString_x3f_257_, 0);
lean_inc(v_val_262_);
lean_dec_ref(v_docString_x3f_257_);
v___x_263_ = ((lean_object*)(l_Lean_Lsp_CompletionItem_resolve___closed__2));
v___y_233_ = v___y_247_;
v___y_234_ = v___y_248_;
v___y_235_ = v_val_262_;
v___y_236_ = v___y_250_;
v___y_237_ = v___y_251_;
v___y_238_ = v___y_253_;
v___y_239_ = v___y_255_;
v___y_240_ = v___y_256_;
v___y_241_ = v___x_263_;
goto v___jp_232_;
}
else
{
lean_object* v_val_264_; lean_object* v_val_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v_val_264_ = lean_ctor_get(v_docString_x3f_257_, 0);
lean_inc(v_val_264_);
lean_dec_ref(v_docString_x3f_257_);
v_val_265_ = lean_ctor_get(v_val_261_, 0);
lean_inc(v_val_265_);
lean_dec_ref(v_val_261_);
v___x_266_ = ((lean_object*)(l_Lean_Lsp_CompletionItem_resolve___closed__3));
v___x_267_ = l_addParenHeuristic(v_val_265_);
v___x_268_ = lean_string_append(v___x_266_, v___x_267_);
lean_dec_ref(v___x_267_);
v___x_269_ = ((lean_object*)(l_Lean_Lsp_CompletionItem_resolve___closed__4));
v___x_270_ = lean_string_append(v___x_268_, v___x_269_);
v___y_233_ = v___y_247_;
v___y_234_ = v___y_248_;
v___y_235_ = v_val_264_;
v___y_236_ = v___y_250_;
v___y_237_ = v___y_251_;
v___y_238_ = v___y_253_;
v___y_239_ = v___y_255_;
v___y_240_ = v___y_256_;
v___y_241_ = v___x_270_;
goto v___jp_232_;
}
}
}
}
v___jp_271_:
{
if (lean_obj_tag(v_id_204_) == 0)
{
lean_object* v_declName_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_305_; 
v_declName_284_ = lean_ctor_get(v_id_204_, 0);
v_isSharedCheck_305_ = !lean_is_exclusive(v_id_204_);
if (v_isSharedCheck_305_ == 0)
{
v___x_286_ = v_id_204_;
v_isShared_287_ = v_isSharedCheck_305_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_declName_284_);
lean_dec(v_id_204_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_305_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v___x_288_; 
v___x_288_ = l_Lean_findDocString_x3f(v_env_222_, v_declName_284_, v___y_282_);
if (lean_obj_tag(v___x_288_) == 0)
{
lean_object* v_a_289_; 
lean_del_object(v___x_286_);
v_a_289_ = lean_ctor_get(v___x_288_, 0);
lean_inc(v_a_289_);
lean_dec_ref(v___x_288_);
v___y_247_ = v___y_272_;
v___y_248_ = v___y_273_;
v___y_249_ = v___y_275_;
v___y_250_ = v___y_276_;
v___y_251_ = v___y_277_;
v___y_252_ = v___y_283_;
v___y_253_ = v___y_278_;
v___y_254_ = v___y_280_;
v___y_255_ = v___y_279_;
v___y_256_ = v___y_281_;
v_docString_x3f_257_ = v_a_289_;
goto v___jp_246_;
}
else
{
lean_object* v_a_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_304_; 
lean_dec(v___y_283_);
lean_dec(v___y_281_);
lean_dec(v___y_280_);
lean_dec(v___y_279_);
lean_dec_ref(v___y_278_);
lean_dec(v___y_277_);
lean_dec(v___y_276_);
lean_dec_ref(v___y_275_);
lean_dec(v___y_273_);
lean_dec(v___y_272_);
v_a_290_ = lean_ctor_get(v___x_288_, 0);
v_isSharedCheck_304_ = !lean_is_exclusive(v___x_288_);
if (v_isSharedCheck_304_ == 0)
{
v___x_292_ = v___x_288_;
v_isShared_293_ = v_isSharedCheck_304_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_a_290_);
lean_dec(v___x_288_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_304_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v_ref_294_; lean_object* v___x_295_; lean_object* v___x_297_; 
v_ref_294_ = lean_ctor_get(v___y_274_, 5);
v___x_295_ = lean_io_error_to_string(v_a_290_);
if (v_isShared_287_ == 0)
{
lean_ctor_set_tag(v___x_286_, 3);
lean_ctor_set(v___x_286_, 0, v___x_295_);
v___x_297_ = v___x_286_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v___x_295_);
v___x_297_ = v_reuseFailAlloc_303_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_301_; 
v___x_298_ = l_Lean_MessageData_ofFormat(v___x_297_);
lean_inc(v_ref_294_);
v___x_299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_299_, 0, v_ref_294_);
lean_ctor_set(v___x_299_, 1, v___x_298_);
if (v_isShared_293_ == 0)
{
lean_ctor_set(v___x_292_, 0, v___x_299_);
v___x_301_ = v___x_292_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v___x_299_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
return v___x_301_;
}
}
}
}
}
}
else
{
lean_object* v___x_306_; 
lean_dec_ref(v_env_222_);
lean_dec_ref(v_id_204_);
v___x_306_ = lean_box(0);
v___y_247_ = v___y_272_;
v___y_248_ = v___y_273_;
v___y_249_ = v___y_275_;
v___y_250_ = v___y_276_;
v___y_251_ = v___y_277_;
v___y_252_ = v___y_283_;
v___y_253_ = v___y_278_;
v___y_254_ = v___y_280_;
v___y_255_ = v___y_279_;
v___y_256_ = v___y_281_;
v_docString_x3f_257_ = v___x_306_;
goto v___jp_246_;
}
}
v___jp_307_:
{
lean_object* v___x_320_; 
v___x_320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_320_, 0, v___y_319_);
v___y_272_ = v___y_308_;
v___y_273_ = v___y_309_;
v___y_274_ = v___y_311_;
v___y_275_ = v___y_310_;
v___y_276_ = v___y_312_;
v___y_277_ = v___y_313_;
v___y_278_ = v___y_314_;
v___y_279_ = v___y_316_;
v___y_280_ = v___y_315_;
v___y_281_ = v___y_317_;
v___y_282_ = v___y_318_;
v___y_283_ = v___x_320_;
goto v___jp_271_;
}
v___jp_321_:
{
if (lean_obj_tag(v_documentation_x3f_325_) == 0)
{
lean_object* v___f_332_; uint8_t v___x_333_; 
lean_dec_ref(v_item_322_);
v___f_332_ = lean_alloc_closure((void*)(l_Lean_Lsp_CompletionItem_resolve___lam__1___boxed), 3, 2);
lean_closure_set(v___f_332_, 0, v_documentation_x3f_325_);
lean_closure_set(v___f_332_, 1, v___f_231_);
v___x_333_ = 1;
if (lean_obj_tag(v_id_204_) == 0)
{
lean_object* v_declName_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v_declName_334_ = lean_ctor_get(v_id_204_, 0);
v___x_335_ = l_Lean_Linter_instInhabitedDeprecationEntry_default;
v___x_336_ = l_Lean_Linter_deprecatedAttr;
lean_inc(v_declName_334_);
lean_inc_ref(v_env_222_);
v___x_337_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_335_, v___x_336_, v_env_222_, v_declName_334_);
if (lean_obj_tag(v___x_337_) == 1)
{
lean_object* v_val_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_372_; 
v_val_338_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_372_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_372_ == 0)
{
v___x_340_ = v___x_337_;
v_isShared_341_ = v_isSharedCheck_372_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_val_338_);
lean_dec(v___x_337_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_372_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v_text_x3f_342_; 
v_text_x3f_342_ = lean_ctor_get(v_val_338_, 1);
if (lean_obj_tag(v_text_x3f_342_) == 1)
{
lean_object* v___x_344_; 
lean_inc_ref(v_text_x3f_342_);
lean_dec(v_val_338_);
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 0, v_text_x3f_342_);
v___x_344_ = v___x_340_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_text_x3f_342_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
v___y_272_ = v_sortText_x3f_328_;
v___y_273_ = v_data_x3f_329_;
v___y_274_ = v___y_331_;
v___y_275_ = v___f_332_;
v___y_276_ = v_textEdit_x3f_327_;
v___y_277_ = v_detail_x3f_324_;
v___y_278_ = v_label_323_;
v___y_279_ = v_tags_x3f_330_;
v___y_280_ = v_documentation_x3f_325_;
v___y_281_ = v_kind_x3f_326_;
v___y_282_ = v___x_333_;
v___y_283_ = v___x_344_;
goto v___jp_271_;
}
}
else
{
lean_object* v_newName_x3f_346_; 
v_newName_x3f_346_ = lean_ctor_get(v_val_338_, 0);
lean_inc(v_newName_x3f_346_);
lean_dec(v_val_338_);
if (lean_obj_tag(v_newName_x3f_346_) == 1)
{
lean_object* v_val_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_363_; 
lean_del_object(v___x_340_);
v_val_347_ = lean_ctor_get(v_newName_x3f_346_, 0);
v_isSharedCheck_363_ = !lean_is_exclusive(v_newName_x3f_346_);
if (v_isSharedCheck_363_ == 0)
{
v___x_349_ = v_newName_x3f_346_;
v_isShared_350_ = v_isSharedCheck_363_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_val_347_);
lean_dec(v_newName_x3f_346_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_363_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_361_; 
v___x_351_ = ((lean_object*)(l_Lean_Lsp_CompletionItem_resolve___closed__5));
lean_inc(v_declName_334_);
v___x_352_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_334_, v___x_333_);
v___x_353_ = lean_string_append(v___x_351_, v___x_352_);
lean_dec_ref(v___x_352_);
v___x_354_ = ((lean_object*)(l_Lean_Lsp_CompletionItem_resolve___closed__6));
v___x_355_ = lean_string_append(v___x_353_, v___x_354_);
v___x_356_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_347_, v___x_333_);
v___x_357_ = lean_string_append(v___x_355_, v___x_356_);
lean_dec_ref(v___x_356_);
v___x_358_ = ((lean_object*)(l_Lean_Lsp_CompletionItem_resolve___closed__7));
v___x_359_ = lean_string_append(v___x_357_, v___x_358_);
if (v_isShared_350_ == 0)
{
lean_ctor_set(v___x_349_, 0, v___x_359_);
v___x_361_ = v___x_349_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v___x_359_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
v___y_308_ = v_sortText_x3f_328_;
v___y_309_ = v_data_x3f_329_;
v___y_310_ = v___f_332_;
v___y_311_ = v___y_331_;
v___y_312_ = v_textEdit_x3f_327_;
v___y_313_ = v_detail_x3f_324_;
v___y_314_ = v_label_323_;
v___y_315_ = v_documentation_x3f_325_;
v___y_316_ = v_tags_x3f_330_;
v___y_317_ = v_kind_x3f_326_;
v___y_318_ = v___x_333_;
v___y_319_ = v___x_361_;
goto v___jp_307_;
}
}
}
else
{
lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_370_; 
lean_dec(v_newName_x3f_346_);
v___x_364_ = ((lean_object*)(l_Lean_Lsp_CompletionItem_resolve___closed__5));
lean_inc(v_declName_334_);
v___x_365_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_334_, v___x_333_);
v___x_366_ = lean_string_append(v___x_364_, v___x_365_);
lean_dec_ref(v___x_365_);
v___x_367_ = ((lean_object*)(l_Lean_Lsp_CompletionItem_resolve___closed__8));
v___x_368_ = lean_string_append(v___x_366_, v___x_367_);
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 0, v___x_368_);
v___x_370_ = v___x_340_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v___x_368_);
v___x_370_ = v_reuseFailAlloc_371_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
v___y_308_ = v_sortText_x3f_328_;
v___y_309_ = v_data_x3f_329_;
v___y_310_ = v___f_332_;
v___y_311_ = v___y_331_;
v___y_312_ = v_textEdit_x3f_327_;
v___y_313_ = v_detail_x3f_324_;
v___y_314_ = v_label_323_;
v___y_315_ = v_documentation_x3f_325_;
v___y_316_ = v_tags_x3f_330_;
v___y_317_ = v_kind_x3f_326_;
v___y_318_ = v___x_333_;
v___y_319_ = v___x_370_;
goto v___jp_307_;
}
}
}
}
}
else
{
lean_object* v___x_373_; 
lean_dec(v___x_337_);
v___x_373_ = lean_box(0);
v___y_272_ = v_sortText_x3f_328_;
v___y_273_ = v_data_x3f_329_;
v___y_274_ = v___y_331_;
v___y_275_ = v___f_332_;
v___y_276_ = v_textEdit_x3f_327_;
v___y_277_ = v_detail_x3f_324_;
v___y_278_ = v_label_323_;
v___y_279_ = v_tags_x3f_330_;
v___y_280_ = v_documentation_x3f_325_;
v___y_281_ = v_kind_x3f_326_;
v___y_282_ = v___x_333_;
v___y_283_ = v___x_373_;
goto v___jp_271_;
}
}
else
{
lean_object* v___x_374_; 
v___x_374_ = lean_box(0);
v___y_272_ = v_sortText_x3f_328_;
v___y_273_ = v_data_x3f_329_;
v___y_274_ = v___y_331_;
v___y_275_ = v___f_332_;
v___y_276_ = v_textEdit_x3f_327_;
v___y_277_ = v_detail_x3f_324_;
v___y_278_ = v_label_323_;
v___y_279_ = v_tags_x3f_330_;
v___y_280_ = v_documentation_x3f_325_;
v___y_281_ = v_kind_x3f_326_;
v___y_282_ = v___x_333_;
v___y_283_ = v___x_374_;
goto v___jp_271_;
}
}
else
{
lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_381_; 
lean_dec(v_tags_x3f_330_);
lean_dec(v_data_x3f_329_);
lean_dec(v_sortText_x3f_328_);
lean_dec(v_textEdit_x3f_327_);
lean_dec(v_kind_x3f_326_);
lean_dec(v_detail_x3f_324_);
lean_dec_ref(v_label_323_);
lean_dec_ref(v_env_222_);
lean_dec_ref(v_id_204_);
v_isSharedCheck_381_ = !lean_is_exclusive(v_documentation_x3f_325_);
if (v_isSharedCheck_381_ == 0)
{
lean_object* v_unused_382_; 
v_unused_382_ = lean_ctor_get(v_documentation_x3f_325_, 0);
lean_dec(v_unused_382_);
v___x_376_ = v_documentation_x3f_325_;
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
else
{
lean_dec(v_documentation_x3f_325_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_379_; 
if (v_isShared_377_ == 0)
{
lean_ctor_set_tag(v___x_376_, 0);
lean_ctor_set(v___x_376_, 0, v_item_322_);
v___x_379_ = v___x_376_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_item_322_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
}
}
v___jp_383_:
{
lean_object* v___x_385_; 
lean_inc(v_tags_x3f_230_);
lean_inc(v_data_x3f_229_);
lean_inc(v_sortText_x3f_228_);
lean_inc(v_textEdit_x3f_227_);
lean_inc(v_kind_x3f_226_);
lean_inc(v_documentation_x3f_225_);
lean_inc(v_a_384_);
lean_inc_ref(v_label_223_);
v___x_385_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_385_, 0, v_label_223_);
lean_ctor_set(v___x_385_, 1, v_a_384_);
lean_ctor_set(v___x_385_, 2, v_documentation_x3f_225_);
lean_ctor_set(v___x_385_, 3, v_kind_x3f_226_);
lean_ctor_set(v___x_385_, 4, v_textEdit_x3f_227_);
lean_ctor_set(v___x_385_, 5, v_sortText_x3f_228_);
lean_ctor_set(v___x_385_, 6, v_data_x3f_229_);
lean_ctor_set(v___x_385_, 7, v_tags_x3f_230_);
v_item_322_ = v___x_385_;
v_label_323_ = v_label_223_;
v_detail_x3f_324_ = v_a_384_;
v_documentation_x3f_325_ = v_documentation_x3f_225_;
v_kind_x3f_326_ = v_kind_x3f_226_;
v_textEdit_x3f_327_ = v_textEdit_x3f_227_;
v_sortText_x3f_328_ = v_sortText_x3f_228_;
v_data_x3f_329_ = v_data_x3f_229_;
v_tags_x3f_330_ = v_tags_x3f_230_;
v___y_331_ = v_a_207_;
goto v___jp_321_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___boxed(lean_object* v_item_410_, lean_object* v_id_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Lean_Lsp_CompletionItem_resolve(v_item_410_, v_id_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_);
lean_dec(v_a_415_);
lean_dec_ref(v_a_414_);
lean_dec(v_a_413_);
lean_dec_ref(v_a_412_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_resolveCompletionItem_x3f(lean_object* v_fileMap_418_, lean_object* v_hoverPos_419_, lean_object* v_cmdStx_420_, lean_object* v_infoTree_421_, lean_object* v_item_422_, lean_object* v_id_423_, lean_object* v_completionInfoPos_424_){
_start:
{
lean_object* v___x_426_; lean_object* v_fst_427_; lean_object* v___x_428_; uint8_t v___x_429_; 
v___x_426_ = l_Lean_Server_Completion_findCompletionInfosAt(v_fileMap_418_, v_hoverPos_419_, v_cmdStx_420_, v_infoTree_421_);
v_fst_427_ = lean_ctor_get(v___x_426_, 0);
lean_inc(v_fst_427_);
lean_dec_ref(v___x_426_);
v___x_428_ = lean_array_get_size(v_fst_427_);
v___x_429_ = lean_nat_dec_lt(v_completionInfoPos_424_, v___x_428_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; 
lean_dec(v_fst_427_);
lean_dec_ref(v_id_423_);
v___x_430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_430_, 0, v_item_422_);
return v___x_430_;
}
else
{
lean_object* v___x_431_; lean_object* v_ctx_432_; lean_object* v_info_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_431_ = lean_array_fget(v_fst_427_, v_completionInfoPos_424_);
lean_dec(v_fst_427_);
v_ctx_432_ = lean_ctor_get(v___x_431_, 1);
lean_inc_ref(v_ctx_432_);
v_info_433_ = lean_ctor_get(v___x_431_, 2);
lean_inc_ref(v_info_433_);
lean_dec(v___x_431_);
v___x_434_ = l_Lean_Elab_CompletionInfo_lctx(v_info_433_);
lean_dec_ref(v_info_433_);
v___x_435_ = lean_alloc_closure((void*)(l_Lean_Lsp_CompletionItem_resolve___boxed), 7, 2);
lean_closure_set(v___x_435_, 0, v_item_422_);
lean_closure_set(v___x_435_, 1, v_id_423_);
v___x_436_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_432_, v___x_434_, v___x_435_);
return v___x_436_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_resolveCompletionItem_x3f___boxed(lean_object* v_fileMap_437_, lean_object* v_hoverPos_438_, lean_object* v_cmdStx_439_, lean_object* v_infoTree_440_, lean_object* v_item_441_, lean_object* v_id_442_, lean_object* v_completionInfoPos_443_, lean_object* v_a_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Lean_Server_Completion_resolveCompletionItem_x3f(v_fileMap_437_, v_hoverPos_438_, v_cmdStx_439_, v_infoTree_440_, v_item_441_, v_id_442_, v_completionInfoPos_443_);
lean_dec(v_completionInfoPos_443_);
return v_res_445_;
}
}
lean_object* runtime_initialize_Lean_Data_Lsp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_Completion_CompletionInfoSelection(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Deprecated(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Server_Completion_CompletionResolution(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Data_Lsp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_Completion_CompletionInfoSelection(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_Deprecated(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Server_Completion_CompletionResolution(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_Lsp(uint8_t builtin);
lean_object* initialize_Lean_Server_Completion_CompletionInfoSelection(uint8_t builtin);
lean_object* initialize_Lean_Linter_Deprecated(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_Completion_CompletionResolution(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Lsp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Completion_CompletionInfoSelection(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_Deprecated(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_Completion_CompletionResolution(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Server_Completion_CompletionResolution(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Server_Completion_CompletionResolution(builtin);
}
#ifdef __cplusplus
}
#endif

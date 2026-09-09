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
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_findDocString_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_findMarkdownDocString_x3f___at___00Lean_Lsp_CompletionItem_resolve_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findMarkdownDocString_x3f___at___00Lean_Lsp_CompletionItem_resolve_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findMarkdownDocString_x3f___at___00Lean_Lsp_CompletionItem_resolve_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findMarkdownDocString_x3f___at___00Lean_Lsp_CompletionItem_resolve_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref_known(v_e_93_, 3);
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
LEAN_EXPORT lean_object* l_Lean_findMarkdownDocString_x3f___at___00Lean_Lsp_CompletionItem_resolve_spec__0___redArg(lean_object* v_declName_147_, uint8_t v_includeBuiltin_148_, lean_object* v___y_149_, lean_object* v___y_150_){
_start:
{
lean_object* v___x_152_; lean_object* v_toCold_153_; lean_object* v_env_154_; lean_object* v_ref_155_; lean_object* v_currNamespace_156_; lean_object* v_openDecls_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_152_ = lean_st_ref_get(v___y_150_);
v_toCold_153_ = lean_ctor_get(v___y_149_, 0);
v_env_154_ = lean_ctor_get(v___x_152_, 0);
lean_inc_ref(v_env_154_);
lean_dec(v___x_152_);
v_ref_155_ = lean_ctor_get(v___y_149_, 2);
v_currNamespace_156_ = lean_ctor_get(v_toCold_153_, 4);
v_openDecls_157_ = lean_ctor_get(v_toCold_153_, 5);
v___x_158_ = l_Lean_Options_empty;
lean_inc(v_openDecls_157_);
lean_inc(v_currNamespace_156_);
v___x_159_ = l_Lean_findDocString_x3f(v_env_154_, v_declName_147_, v_includeBuiltin_148_, v___x_158_, v_currNamespace_156_, v_openDecls_157_);
if (lean_obj_tag(v___x_159_) == 0)
{
lean_object* v_a_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_167_; 
v_a_160_ = lean_ctor_get(v___x_159_, 0);
v_isSharedCheck_167_ = !lean_is_exclusive(v___x_159_);
if (v_isSharedCheck_167_ == 0)
{
v___x_162_ = v___x_159_;
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_a_160_);
lean_dec(v___x_159_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___x_165_; 
if (v_isShared_163_ == 0)
{
v___x_165_ = v___x_162_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v_a_160_);
v___x_165_ = v_reuseFailAlloc_166_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
return v___x_165_;
}
}
}
else
{
lean_object* v_a_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_179_; 
v_a_168_ = lean_ctor_get(v___x_159_, 0);
v_isSharedCheck_179_ = !lean_is_exclusive(v___x_159_);
if (v_isSharedCheck_179_ == 0)
{
v___x_170_ = v___x_159_;
v_isShared_171_ = v_isSharedCheck_179_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_a_168_);
lean_dec(v___x_159_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_179_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_177_; 
v___x_172_ = lean_io_error_to_string(v_a_168_);
v___x_173_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_173_, 0, v___x_172_);
v___x_174_ = l_Lean_MessageData_ofFormat(v___x_173_);
lean_inc(v_ref_155_);
v___x_175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_175_, 0, v_ref_155_);
lean_ctor_set(v___x_175_, 1, v___x_174_);
if (v_isShared_171_ == 0)
{
lean_ctor_set(v___x_170_, 0, v___x_175_);
v___x_177_ = v___x_170_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(1, 1, 0);
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
LEAN_EXPORT lean_object* l_Lean_findMarkdownDocString_x3f___at___00Lean_Lsp_CompletionItem_resolve_spec__0___redArg___boxed(lean_object* v_declName_180_, lean_object* v_includeBuiltin_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_){
_start:
{
uint8_t v_includeBuiltin_boxed_185_; lean_object* v_res_186_; 
v_includeBuiltin_boxed_185_ = lean_unbox(v_includeBuiltin_181_);
v_res_186_ = l_Lean_findMarkdownDocString_x3f___at___00Lean_Lsp_CompletionItem_resolve_spec__0___redArg(v_declName_180_, v_includeBuiltin_boxed_185_, v___y_182_, v___y_183_);
lean_dec(v___y_183_);
lean_dec_ref(v___y_182_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_findMarkdownDocString_x3f___at___00Lean_Lsp_CompletionItem_resolve_spec__0(lean_object* v_declName_187_, uint8_t v_includeBuiltin_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = l_Lean_findMarkdownDocString_x3f___at___00Lean_Lsp_CompletionItem_resolve_spec__0___redArg(v_declName_187_, v_includeBuiltin_188_, v___y_191_, v___y_192_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_findMarkdownDocString_x3f___at___00Lean_Lsp_CompletionItem_resolve_spec__0___boxed(lean_object* v_declName_195_, lean_object* v_includeBuiltin_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_){
_start:
{
uint8_t v_includeBuiltin_boxed_202_; lean_object* v_res_203_; 
v_includeBuiltin_boxed_202_ = lean_unbox(v_includeBuiltin_196_);
v_res_203_ = l_Lean_findMarkdownDocString_x3f___at___00Lean_Lsp_CompletionItem_resolve_spec__0(v_declName_195_, v_includeBuiltin_boxed_202_, v___y_197_, v___y_198_, v___y_199_, v___y_200_);
lean_dec(v___y_200_);
lean_dec_ref(v___y_199_);
lean_dec(v___y_198_);
lean_dec_ref(v___y_197_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___lam__0(lean_object* v_docValue_204_){
_start:
{
uint8_t v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_205_ = 1;
v___x_206_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_206_, 0, v_docValue_204_);
lean_ctor_set_uint8(v___x_206_, sizeof(void*)*1, v___x_205_);
v___x_207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_207_, 0, v___x_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___lam__1(lean_object* v_documentation_x3f_208_, lean_object* v___f_209_, lean_object* v_docStringPrefix_210_){
_start:
{
if (lean_obj_tag(v_docStringPrefix_210_) == 0)
{
lean_dec_ref(v___f_209_);
lean_inc(v_documentation_x3f_208_);
return v_documentation_x3f_208_;
}
else
{
lean_object* v_val_211_; lean_object* v___x_212_; 
v_val_211_ = lean_ctor_get(v_docStringPrefix_210_, 0);
lean_inc(v_val_211_);
lean_dec_ref_known(v_docStringPrefix_210_, 1);
v___x_212_ = lean_apply_1(v___f_209_, v_val_211_);
return v___x_212_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___lam__1___boxed(lean_object* v_documentation_x3f_213_, lean_object* v___f_214_, lean_object* v_docStringPrefix_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Lean_Lsp_CompletionItem_resolve___lam__1(v_documentation_x3f_213_, v___f_214_, v_docStringPrefix_215_);
lean_dec(v_documentation_x3f_213_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___lam__2(lean_object* v_typeWithoutImplicits_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = l_Lean_Meta_ppExpr(v_typeWithoutImplicits_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_);
if (lean_obj_tag(v___x_223_) == 0)
{
lean_object* v_a_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_234_; 
v_a_224_ = lean_ctor_get(v___x_223_, 0);
v_isSharedCheck_234_ = !lean_is_exclusive(v___x_223_);
if (v_isSharedCheck_234_ == 0)
{
v___x_226_ = v___x_223_;
v_isShared_227_ = v_isSharedCheck_234_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_a_224_);
lean_dec(v___x_223_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_234_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_232_; 
v___x_228_ = l_Std_Format_defWidth;
v___x_229_ = lean_unsigned_to_nat(0u);
v___x_230_ = l_Std_Format_pretty(v_a_224_, v___x_228_, v___x_229_, v___x_229_);
if (v_isShared_227_ == 0)
{
lean_ctor_set(v___x_226_, 0, v___x_230_);
v___x_232_ = v___x_226_;
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
lean_object* v_a_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_242_; 
v_a_235_ = lean_ctor_get(v___x_223_, 0);
v_isSharedCheck_242_ = !lean_is_exclusive(v___x_223_);
if (v_isSharedCheck_242_ == 0)
{
v___x_237_ = v___x_223_;
v_isShared_238_ = v_isSharedCheck_242_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_a_235_);
lean_dec(v___x_223_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_242_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_240_; 
if (v_isShared_238_ == 0)
{
v___x_240_ = v___x_237_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v_a_235_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
return v___x_240_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___lam__2___boxed(lean_object* v_typeWithoutImplicits_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l_Lean_Lsp_CompletionItem_resolve___lam__2(v_typeWithoutImplicits_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_);
lean_dec(v___y_247_);
lean_dec_ref(v___y_246_);
lean_dec(v___y_245_);
lean_dec_ref(v___y_244_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve(lean_object* v_item_260_, lean_object* v_id_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_){
_start:
{
lean_object* v___y_268_; lean_object* v___y_269_; lean_object* v___y_270_; lean_object* v___y_271_; lean_object* v___y_272_; lean_object* v___y_273_; lean_object* v___y_274_; lean_object* v___y_275_; lean_object* v___x_278_; lean_object* v_env_279_; lean_object* v_label_280_; lean_object* v_detail_x3f_281_; lean_object* v_documentation_x3f_282_; lean_object* v_kind_x3f_283_; lean_object* v_textEdit_x3f_284_; lean_object* v_sortText_x3f_285_; lean_object* v_data_x3f_286_; lean_object* v_tags_x3f_287_; lean_object* v___f_288_; lean_object* v___y_290_; lean_object* v___y_291_; lean_object* v___y_292_; lean_object* v___y_293_; lean_object* v___y_294_; lean_object* v___y_295_; lean_object* v___y_296_; lean_object* v___y_297_; lean_object* v___y_298_; lean_object* v___y_304_; lean_object* v___y_305_; lean_object* v___y_306_; lean_object* v___y_307_; lean_object* v___y_308_; lean_object* v___y_309_; lean_object* v___y_310_; lean_object* v___y_311_; lean_object* v___y_312_; lean_object* v___y_313_; lean_object* v_docString_x3f_314_; lean_object* v___y_329_; lean_object* v___y_330_; lean_object* v___y_331_; lean_object* v___y_332_; lean_object* v___y_333_; lean_object* v___y_334_; lean_object* v___y_335_; lean_object* v___y_336_; uint8_t v___y_337_; lean_object* v___y_338_; lean_object* v___y_339_; lean_object* v___y_340_; lean_object* v___y_341_; lean_object* v___y_355_; lean_object* v___y_356_; lean_object* v___y_357_; lean_object* v___y_358_; lean_object* v___y_359_; lean_object* v___y_360_; lean_object* v___y_361_; lean_object* v___y_362_; uint8_t v___y_363_; lean_object* v___y_364_; lean_object* v___y_365_; lean_object* v___y_366_; lean_object* v___y_367_; lean_object* v___x_369_; lean_object* v_item_371_; lean_object* v_label_372_; lean_object* v_detail_x3f_373_; lean_object* v_documentation_x3f_374_; lean_object* v_kind_x3f_375_; lean_object* v_textEdit_x3f_376_; lean_object* v_sortText_x3f_377_; lean_object* v_data_x3f_378_; lean_object* v_tags_x3f_379_; lean_object* v___y_380_; lean_object* v___y_381_; lean_object* v_a_433_; 
v___x_278_ = lean_st_ref_get(v_a_265_);
v_env_279_ = lean_ctor_get(v___x_278_, 0);
lean_inc_ref(v_env_279_);
lean_dec(v___x_278_);
v_label_280_ = lean_ctor_get(v_item_260_, 0);
lean_inc_ref(v_label_280_);
v_detail_x3f_281_ = lean_ctor_get(v_item_260_, 1);
lean_inc(v_detail_x3f_281_);
v_documentation_x3f_282_ = lean_ctor_get(v_item_260_, 2);
lean_inc(v_documentation_x3f_282_);
v_kind_x3f_283_ = lean_ctor_get(v_item_260_, 3);
lean_inc(v_kind_x3f_283_);
v_textEdit_x3f_284_ = lean_ctor_get(v_item_260_, 4);
lean_inc(v_textEdit_x3f_284_);
v_sortText_x3f_285_ = lean_ctor_get(v_item_260_, 5);
lean_inc(v_sortText_x3f_285_);
v_data_x3f_286_ = lean_ctor_get(v_item_260_, 6);
lean_inc(v_data_x3f_286_);
v_tags_x3f_287_ = lean_ctor_get(v_item_260_, 7);
lean_inc(v_tags_x3f_287_);
v___f_288_ = ((lean_object*)(l_Lean_Lsp_CompletionItem_resolve___closed__0));
v___x_369_ = l_Lean_Linter_instInhabitedDeprecationEntry_default;
if (lean_obj_tag(v_detail_x3f_281_) == 0)
{
lean_object* v___f_435_; lean_object* v_val_437_; 
lean_dec_ref(v_item_260_);
v___f_435_ = ((lean_object*)(l_Lean_Lsp_CompletionItem_resolve___closed__9));
if (lean_obj_tag(v_id_261_) == 0)
{
lean_object* v_declName_449_; uint8_t v___x_450_; lean_object* v___x_451_; 
v_declName_449_ = lean_ctor_get(v_id_261_, 0);
v___x_450_ = 0;
lean_inc(v_declName_449_);
lean_inc_ref(v_env_279_);
v___x_451_ = l_Lean_Environment_find_x3f(v_env_279_, v_declName_449_, v___x_450_);
if (lean_obj_tag(v___x_451_) == 0)
{
v_a_433_ = v_detail_x3f_281_;
goto v___jp_432_;
}
else
{
lean_object* v_val_452_; lean_object* v___x_453_; 
v_val_452_ = lean_ctor_get(v___x_451_, 0);
lean_inc(v_val_452_);
lean_dec_ref_known(v___x_451_, 1);
v___x_453_ = l_Lean_ConstantInfo_type(v_val_452_);
lean_dec(v_val_452_);
v_val_437_ = v___x_453_;
goto v___jp_436_;
}
}
else
{
lean_object* v_id_454_; lean_object* v_lctx_455_; lean_object* v___x_456_; 
v_id_454_ = lean_ctor_get(v_id_261_, 0);
v_lctx_455_ = lean_ctor_get(v_a_262_, 2);
lean_inc(v_id_454_);
lean_inc_ref(v_lctx_455_);
v___x_456_ = lean_local_ctx_find(v_lctx_455_, v_id_454_);
if (lean_obj_tag(v___x_456_) == 0)
{
v_a_433_ = v_detail_x3f_281_;
goto v___jp_432_;
}
else
{
lean_object* v_val_457_; lean_object* v___x_458_; 
v_val_457_ = lean_ctor_get(v___x_456_, 0);
lean_inc(v_val_457_);
lean_dec_ref_known(v___x_456_, 1);
v___x_458_ = l_Lean_LocalDecl_type(v_val_457_);
lean_dec(v_val_457_);
v_val_437_ = v___x_458_;
goto v___jp_436_;
}
}
v___jp_436_:
{
lean_object* v___x_438_; 
v___x_438_ = l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg(v_val_437_, v___f_435_, v_a_262_, v_a_263_, v_a_264_, v_a_265_);
if (lean_obj_tag(v___x_438_) == 0)
{
lean_object* v_a_439_; lean_object* v___x_440_; 
v_a_439_ = lean_ctor_get(v___x_438_, 0);
lean_inc(v_a_439_);
lean_dec_ref_known(v___x_438_, 1);
v___x_440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_440_, 0, v_a_439_);
v_a_433_ = v___x_440_;
goto v___jp_432_;
}
else
{
lean_object* v_a_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_448_; 
lean_dec(v_tags_x3f_287_);
lean_dec(v_data_x3f_286_);
lean_dec(v_sortText_x3f_285_);
lean_dec(v_textEdit_x3f_284_);
lean_dec(v_kind_x3f_283_);
lean_dec(v_documentation_x3f_282_);
lean_dec_ref(v_label_280_);
lean_dec_ref(v_env_279_);
lean_dec_ref(v_id_261_);
v_a_441_ = lean_ctor_get(v___x_438_, 0);
v_isSharedCheck_448_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_448_ == 0)
{
v___x_443_ = v___x_438_;
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_a_441_);
lean_dec(v___x_438_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_446_; 
if (v_isShared_444_ == 0)
{
v___x_446_ = v___x_443_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_a_441_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
}
}
}
else
{
v_item_371_ = v_item_260_;
v_label_372_ = v_label_280_;
v_detail_x3f_373_ = v_detail_x3f_281_;
v_documentation_x3f_374_ = v_documentation_x3f_282_;
v_kind_x3f_375_ = v_kind_x3f_283_;
v_textEdit_x3f_376_ = v_textEdit_x3f_284_;
v_sortText_x3f_377_ = v_sortText_x3f_285_;
v_data_x3f_378_ = v_data_x3f_286_;
v_tags_x3f_379_ = v_tags_x3f_287_;
v___y_380_ = v_a_264_;
v___y_381_ = v_a_265_;
goto v___jp_370_;
}
v___jp_267_:
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_276_, 0, v___y_271_);
lean_ctor_set(v___x_276_, 1, v___y_274_);
lean_ctor_set(v___x_276_, 2, v___y_275_);
lean_ctor_set(v___x_276_, 3, v___y_272_);
lean_ctor_set(v___x_276_, 4, v___y_268_);
lean_ctor_set(v___x_276_, 5, v___y_269_);
lean_ctor_set(v___x_276_, 6, v___y_270_);
lean_ctor_set(v___x_276_, 7, v___y_273_);
v___x_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_277_, 0, v___x_276_);
return v___x_277_;
}
v___jp_289_:
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_299_ = ((lean_object*)(l_Lean_Lsp_CompletionItem_resolve___closed__1));
v___x_300_ = lean_string_append(v___y_298_, v___x_299_);
v___x_301_ = lean_string_append(v___x_300_, v___y_296_);
lean_dec_ref(v___y_296_);
v___x_302_ = l_Lean_Lsp_CompletionItem_resolve___lam__0(v___x_301_);
v___y_268_ = v___y_290_;
v___y_269_ = v___y_291_;
v___y_270_ = v___y_293_;
v___y_271_ = v___y_292_;
v___y_272_ = v___y_294_;
v___y_273_ = v___y_295_;
v___y_274_ = v___y_297_;
v___y_275_ = v___x_302_;
goto v___jp_267_;
}
v___jp_303_:
{
if (lean_obj_tag(v___y_312_) == 0)
{
if (lean_obj_tag(v_docString_x3f_314_) == 0)
{
lean_dec_ref(v___y_304_);
v___y_268_ = v___y_305_;
v___y_269_ = v___y_306_;
v___y_270_ = v___y_308_;
v___y_271_ = v___y_307_;
v___y_272_ = v___y_309_;
v___y_273_ = v___y_310_;
v___y_274_ = v___y_313_;
v___y_275_ = v___y_311_;
goto v___jp_267_;
}
else
{
lean_object* v___x_315_; 
lean_dec(v___y_311_);
v___x_315_ = lean_apply_1(v___y_304_, v_docString_x3f_314_);
v___y_268_ = v___y_305_;
v___y_269_ = v___y_306_;
v___y_270_ = v___y_308_;
v___y_271_ = v___y_307_;
v___y_272_ = v___y_309_;
v___y_273_ = v___y_310_;
v___y_274_ = v___y_313_;
v___y_275_ = v___x_315_;
goto v___jp_267_;
}
}
else
{
lean_dec(v___y_311_);
if (lean_obj_tag(v_docString_x3f_314_) == 0)
{
lean_object* v_val_316_; lean_object* v___x_317_; 
v_val_316_ = lean_ctor_get(v___y_312_, 0);
lean_inc(v_val_316_);
lean_dec_ref_known(v___y_312_, 1);
v___x_317_ = lean_apply_1(v___y_304_, v_val_316_);
v___y_268_ = v___y_305_;
v___y_269_ = v___y_306_;
v___y_270_ = v___y_308_;
v___y_271_ = v___y_307_;
v___y_272_ = v___y_309_;
v___y_273_ = v___y_310_;
v___y_274_ = v___y_313_;
v___y_275_ = v___x_317_;
goto v___jp_267_;
}
else
{
lean_object* v_val_318_; 
lean_dec_ref(v___y_304_);
v_val_318_ = lean_ctor_get(v___y_312_, 0);
lean_inc(v_val_318_);
lean_dec_ref_known(v___y_312_, 1);
if (lean_obj_tag(v_val_318_) == 0)
{
lean_object* v_val_319_; lean_object* v___x_320_; 
v_val_319_ = lean_ctor_get(v_docString_x3f_314_, 0);
lean_inc(v_val_319_);
lean_dec_ref_known(v_docString_x3f_314_, 1);
v___x_320_ = ((lean_object*)(l_Lean_Lsp_CompletionItem_resolve___closed__2));
v___y_290_ = v___y_305_;
v___y_291_ = v___y_306_;
v___y_292_ = v___y_307_;
v___y_293_ = v___y_308_;
v___y_294_ = v___y_309_;
v___y_295_ = v___y_310_;
v___y_296_ = v_val_319_;
v___y_297_ = v___y_313_;
v___y_298_ = v___x_320_;
goto v___jp_289_;
}
else
{
lean_object* v_val_321_; lean_object* v_val_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v_val_321_ = lean_ctor_get(v_docString_x3f_314_, 0);
lean_inc(v_val_321_);
lean_dec_ref_known(v_docString_x3f_314_, 1);
v_val_322_ = lean_ctor_get(v_val_318_, 0);
lean_inc(v_val_322_);
lean_dec_ref_known(v_val_318_, 1);
v___x_323_ = ((lean_object*)(l_Lean_Lsp_CompletionItem_resolve___closed__3));
v___x_324_ = l_addParenHeuristic(v_val_322_);
v___x_325_ = lean_string_append(v___x_323_, v___x_324_);
lean_dec_ref(v___x_324_);
v___x_326_ = ((lean_object*)(l_Lean_Lsp_CompletionItem_resolve___closed__4));
v___x_327_ = lean_string_append(v___x_325_, v___x_326_);
v___y_290_ = v___y_305_;
v___y_291_ = v___y_306_;
v___y_292_ = v___y_307_;
v___y_293_ = v___y_308_;
v___y_294_ = v___y_309_;
v___y_295_ = v___y_310_;
v___y_296_ = v_val_321_;
v___y_297_ = v___y_313_;
v___y_298_ = v___x_327_;
goto v___jp_289_;
}
}
}
}
v___jp_328_:
{
if (lean_obj_tag(v_id_261_) == 0)
{
lean_object* v_declName_342_; lean_object* v___x_343_; 
v_declName_342_ = lean_ctor_get(v_id_261_, 0);
lean_inc(v_declName_342_);
lean_dec_ref_known(v_id_261_, 1);
v___x_343_ = l_Lean_findMarkdownDocString_x3f___at___00Lean_Lsp_CompletionItem_resolve_spec__0___redArg(v_declName_342_, v___y_337_, v___y_335_, v___y_334_);
if (lean_obj_tag(v___x_343_) == 0)
{
lean_object* v_a_344_; 
v_a_344_ = lean_ctor_get(v___x_343_, 0);
lean_inc(v_a_344_);
lean_dec_ref_known(v___x_343_, 1);
v___y_304_ = v___y_329_;
v___y_305_ = v___y_336_;
v___y_306_ = v___y_338_;
v___y_307_ = v___y_339_;
v___y_308_ = v___y_340_;
v___y_309_ = v___y_330_;
v___y_310_ = v___y_331_;
v___y_311_ = v___y_332_;
v___y_312_ = v___y_341_;
v___y_313_ = v___y_333_;
v_docString_x3f_314_ = v_a_344_;
goto v___jp_303_;
}
else
{
lean_object* v_a_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_352_; 
lean_dec(v___y_341_);
lean_dec(v___y_340_);
lean_dec_ref(v___y_339_);
lean_dec(v___y_338_);
lean_dec(v___y_336_);
lean_dec(v___y_333_);
lean_dec(v___y_332_);
lean_dec(v___y_331_);
lean_dec(v___y_330_);
lean_dec_ref(v___y_329_);
v_a_345_ = lean_ctor_get(v___x_343_, 0);
v_isSharedCheck_352_ = !lean_is_exclusive(v___x_343_);
if (v_isSharedCheck_352_ == 0)
{
v___x_347_ = v___x_343_;
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_a_345_);
lean_dec(v___x_343_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_350_; 
if (v_isShared_348_ == 0)
{
v___x_350_ = v___x_347_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v_a_345_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
}
}
else
{
lean_object* v___x_353_; 
lean_dec_ref(v_id_261_);
v___x_353_ = lean_box(0);
v___y_304_ = v___y_329_;
v___y_305_ = v___y_336_;
v___y_306_ = v___y_338_;
v___y_307_ = v___y_339_;
v___y_308_ = v___y_340_;
v___y_309_ = v___y_330_;
v___y_310_ = v___y_331_;
v___y_311_ = v___y_332_;
v___y_312_ = v___y_341_;
v___y_313_ = v___y_333_;
v_docString_x3f_314_ = v___x_353_;
goto v___jp_303_;
}
}
v___jp_354_:
{
lean_object* v___x_368_; 
v___x_368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_368_, 0, v___y_367_);
v___y_329_ = v___y_355_;
v___y_330_ = v___y_356_;
v___y_331_ = v___y_357_;
v___y_332_ = v___y_358_;
v___y_333_ = v___y_359_;
v___y_334_ = v___y_360_;
v___y_335_ = v___y_361_;
v___y_336_ = v___y_362_;
v___y_337_ = v___y_363_;
v___y_338_ = v___y_364_;
v___y_339_ = v___y_366_;
v___y_340_ = v___y_365_;
v___y_341_ = v___x_368_;
goto v___jp_328_;
}
v___jp_370_:
{
if (lean_obj_tag(v_documentation_x3f_374_) == 0)
{
lean_object* v___f_382_; uint8_t v___x_383_; 
lean_dec_ref(v_item_371_);
v___f_382_ = lean_alloc_closure((void*)(l_Lean_Lsp_CompletionItem_resolve___lam__1___boxed), 3, 2);
lean_closure_set(v___f_382_, 0, v_documentation_x3f_374_);
lean_closure_set(v___f_382_, 1, v___f_288_);
v___x_383_ = 1;
if (lean_obj_tag(v_id_261_) == 0)
{
lean_object* v_declName_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v_declName_384_ = lean_ctor_get(v_id_261_, 0);
v___x_385_ = l_Lean_Linter_deprecatedAttr;
lean_inc(v_declName_384_);
v___x_386_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_369_, v___x_385_, v_env_279_, v_declName_384_);
if (lean_obj_tag(v___x_386_) == 1)
{
lean_object* v_val_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_421_; 
v_val_387_ = lean_ctor_get(v___x_386_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_386_);
if (v_isSharedCheck_421_ == 0)
{
v___x_389_ = v___x_386_;
v_isShared_390_ = v_isSharedCheck_421_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_val_387_);
lean_dec(v___x_386_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_421_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v_text_x3f_391_; 
v_text_x3f_391_ = lean_ctor_get(v_val_387_, 1);
if (lean_obj_tag(v_text_x3f_391_) == 1)
{
lean_object* v___x_393_; 
lean_inc_ref(v_text_x3f_391_);
lean_dec(v_val_387_);
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 0, v_text_x3f_391_);
v___x_393_ = v___x_389_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v_text_x3f_391_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
v___y_329_ = v___f_382_;
v___y_330_ = v_kind_x3f_375_;
v___y_331_ = v_tags_x3f_379_;
v___y_332_ = v_documentation_x3f_374_;
v___y_333_ = v_detail_x3f_373_;
v___y_334_ = v___y_381_;
v___y_335_ = v___y_380_;
v___y_336_ = v_textEdit_x3f_376_;
v___y_337_ = v___x_383_;
v___y_338_ = v_sortText_x3f_377_;
v___y_339_ = v_label_372_;
v___y_340_ = v_data_x3f_378_;
v___y_341_ = v___x_393_;
goto v___jp_328_;
}
}
else
{
lean_object* v_newName_x3f_395_; 
v_newName_x3f_395_ = lean_ctor_get(v_val_387_, 0);
lean_inc(v_newName_x3f_395_);
lean_dec(v_val_387_);
if (lean_obj_tag(v_newName_x3f_395_) == 1)
{
lean_object* v_val_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_412_; 
lean_del_object(v___x_389_);
v_val_396_ = lean_ctor_get(v_newName_x3f_395_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v_newName_x3f_395_);
if (v_isSharedCheck_412_ == 0)
{
v___x_398_ = v_newName_x3f_395_;
v_isShared_399_ = v_isSharedCheck_412_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_val_396_);
lean_dec(v_newName_x3f_395_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_412_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_410_; 
v___x_400_ = ((lean_object*)(l_Lean_Lsp_CompletionItem_resolve___closed__5));
lean_inc(v_declName_384_);
v___x_401_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_384_, v___x_383_);
v___x_402_ = lean_string_append(v___x_400_, v___x_401_);
lean_dec_ref(v___x_401_);
v___x_403_ = ((lean_object*)(l_Lean_Lsp_CompletionItem_resolve___closed__6));
v___x_404_ = lean_string_append(v___x_402_, v___x_403_);
v___x_405_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_396_, v___x_383_);
v___x_406_ = lean_string_append(v___x_404_, v___x_405_);
lean_dec_ref(v___x_405_);
v___x_407_ = ((lean_object*)(l_Lean_Lsp_CompletionItem_resolve___closed__7));
v___x_408_ = lean_string_append(v___x_406_, v___x_407_);
if (v_isShared_399_ == 0)
{
lean_ctor_set(v___x_398_, 0, v___x_408_);
v___x_410_ = v___x_398_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v___x_408_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
v___y_355_ = v___f_382_;
v___y_356_ = v_kind_x3f_375_;
v___y_357_ = v_tags_x3f_379_;
v___y_358_ = v_documentation_x3f_374_;
v___y_359_ = v_detail_x3f_373_;
v___y_360_ = v___y_381_;
v___y_361_ = v___y_380_;
v___y_362_ = v_textEdit_x3f_376_;
v___y_363_ = v___x_383_;
v___y_364_ = v_sortText_x3f_377_;
v___y_365_ = v_data_x3f_378_;
v___y_366_ = v_label_372_;
v___y_367_ = v___x_410_;
goto v___jp_354_;
}
}
}
else
{
lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_419_; 
lean_dec(v_newName_x3f_395_);
v___x_413_ = ((lean_object*)(l_Lean_Lsp_CompletionItem_resolve___closed__5));
lean_inc(v_declName_384_);
v___x_414_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_384_, v___x_383_);
v___x_415_ = lean_string_append(v___x_413_, v___x_414_);
lean_dec_ref(v___x_414_);
v___x_416_ = ((lean_object*)(l_Lean_Lsp_CompletionItem_resolve___closed__8));
v___x_417_ = lean_string_append(v___x_415_, v___x_416_);
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 0, v___x_417_);
v___x_419_ = v___x_389_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v___x_417_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
v___y_355_ = v___f_382_;
v___y_356_ = v_kind_x3f_375_;
v___y_357_ = v_tags_x3f_379_;
v___y_358_ = v_documentation_x3f_374_;
v___y_359_ = v_detail_x3f_373_;
v___y_360_ = v___y_381_;
v___y_361_ = v___y_380_;
v___y_362_ = v_textEdit_x3f_376_;
v___y_363_ = v___x_383_;
v___y_364_ = v_sortText_x3f_377_;
v___y_365_ = v_data_x3f_378_;
v___y_366_ = v_label_372_;
v___y_367_ = v___x_419_;
goto v___jp_354_;
}
}
}
}
}
else
{
lean_object* v___x_422_; 
lean_dec(v___x_386_);
v___x_422_ = lean_box(0);
v___y_329_ = v___f_382_;
v___y_330_ = v_kind_x3f_375_;
v___y_331_ = v_tags_x3f_379_;
v___y_332_ = v_documentation_x3f_374_;
v___y_333_ = v_detail_x3f_373_;
v___y_334_ = v___y_381_;
v___y_335_ = v___y_380_;
v___y_336_ = v_textEdit_x3f_376_;
v___y_337_ = v___x_383_;
v___y_338_ = v_sortText_x3f_377_;
v___y_339_ = v_label_372_;
v___y_340_ = v_data_x3f_378_;
v___y_341_ = v___x_422_;
goto v___jp_328_;
}
}
else
{
lean_object* v___x_423_; 
lean_dec_ref(v_env_279_);
v___x_423_ = lean_box(0);
v___y_329_ = v___f_382_;
v___y_330_ = v_kind_x3f_375_;
v___y_331_ = v_tags_x3f_379_;
v___y_332_ = v_documentation_x3f_374_;
v___y_333_ = v_detail_x3f_373_;
v___y_334_ = v___y_381_;
v___y_335_ = v___y_380_;
v___y_336_ = v_textEdit_x3f_376_;
v___y_337_ = v___x_383_;
v___y_338_ = v_sortText_x3f_377_;
v___y_339_ = v_label_372_;
v___y_340_ = v_data_x3f_378_;
v___y_341_ = v___x_423_;
goto v___jp_328_;
}
}
else
{
lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_430_; 
lean_dec(v_tags_x3f_379_);
lean_dec(v_data_x3f_378_);
lean_dec(v_sortText_x3f_377_);
lean_dec(v_textEdit_x3f_376_);
lean_dec(v_kind_x3f_375_);
lean_dec(v_detail_x3f_373_);
lean_dec_ref(v_label_372_);
lean_dec_ref(v_env_279_);
lean_dec_ref(v_id_261_);
v_isSharedCheck_430_ = !lean_is_exclusive(v_documentation_x3f_374_);
if (v_isSharedCheck_430_ == 0)
{
lean_object* v_unused_431_; 
v_unused_431_ = lean_ctor_get(v_documentation_x3f_374_, 0);
lean_dec(v_unused_431_);
v___x_425_ = v_documentation_x3f_374_;
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
else
{
lean_dec(v_documentation_x3f_374_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_428_; 
if (v_isShared_426_ == 0)
{
lean_ctor_set_tag(v___x_425_, 0);
lean_ctor_set(v___x_425_, 0, v_item_371_);
v___x_428_ = v___x_425_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_item_371_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
}
v___jp_432_:
{
lean_object* v___x_434_; 
lean_inc(v_tags_x3f_287_);
lean_inc(v_data_x3f_286_);
lean_inc(v_sortText_x3f_285_);
lean_inc(v_textEdit_x3f_284_);
lean_inc(v_kind_x3f_283_);
lean_inc(v_documentation_x3f_282_);
lean_inc(v_a_433_);
lean_inc_ref(v_label_280_);
v___x_434_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_434_, 0, v_label_280_);
lean_ctor_set(v___x_434_, 1, v_a_433_);
lean_ctor_set(v___x_434_, 2, v_documentation_x3f_282_);
lean_ctor_set(v___x_434_, 3, v_kind_x3f_283_);
lean_ctor_set(v___x_434_, 4, v_textEdit_x3f_284_);
lean_ctor_set(v___x_434_, 5, v_sortText_x3f_285_);
lean_ctor_set(v___x_434_, 6, v_data_x3f_286_);
lean_ctor_set(v___x_434_, 7, v_tags_x3f_287_);
v_item_371_ = v___x_434_;
v_label_372_ = v_label_280_;
v_detail_x3f_373_ = v_a_433_;
v_documentation_x3f_374_ = v_documentation_x3f_282_;
v_kind_x3f_375_ = v_kind_x3f_283_;
v_textEdit_x3f_376_ = v_textEdit_x3f_284_;
v_sortText_x3f_377_ = v_sortText_x3f_285_;
v_data_x3f_378_ = v_data_x3f_286_;
v_tags_x3f_379_ = v_tags_x3f_287_;
v___y_380_ = v_a_264_;
v___y_381_ = v_a_265_;
goto v___jp_370_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___boxed(lean_object* v_item_459_, lean_object* v_id_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_Lean_Lsp_CompletionItem_resolve(v_item_459_, v_id_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_);
lean_dec(v_a_464_);
lean_dec_ref(v_a_463_);
lean_dec(v_a_462_);
lean_dec_ref(v_a_461_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_resolveCompletionItem_x3f(lean_object* v_fileMap_467_, lean_object* v_hoverPos_468_, lean_object* v_cmdStx_469_, lean_object* v_infoTree_470_, lean_object* v_item_471_, lean_object* v_id_472_, lean_object* v_completionInfoPos_473_){
_start:
{
lean_object* v___x_475_; lean_object* v_fst_476_; lean_object* v___x_477_; uint8_t v___x_478_; 
v___x_475_ = l_Lean_Server_Completion_findCompletionInfosAt(v_fileMap_467_, v_hoverPos_468_, v_cmdStx_469_, v_infoTree_470_);
v_fst_476_ = lean_ctor_get(v___x_475_, 0);
lean_inc(v_fst_476_);
lean_dec_ref(v___x_475_);
v___x_477_ = lean_array_get_size(v_fst_476_);
v___x_478_ = lean_nat_dec_lt(v_completionInfoPos_473_, v___x_477_);
if (v___x_478_ == 0)
{
lean_object* v___x_479_; 
lean_dec(v_fst_476_);
lean_dec_ref(v_id_472_);
v___x_479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_479_, 0, v_item_471_);
return v___x_479_;
}
else
{
lean_object* v___x_480_; lean_object* v_ctx_481_; lean_object* v_info_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_480_ = lean_array_fget(v_fst_476_, v_completionInfoPos_473_);
lean_dec(v_fst_476_);
v_ctx_481_ = lean_ctor_get(v___x_480_, 1);
lean_inc_ref(v_ctx_481_);
v_info_482_ = lean_ctor_get(v___x_480_, 2);
lean_inc_ref(v_info_482_);
lean_dec(v___x_480_);
v___x_483_ = l_Lean_Elab_CompletionInfo_lctx(v_info_482_);
lean_dec_ref(v_info_482_);
v___x_484_ = lean_alloc_closure((void*)(l_Lean_Lsp_CompletionItem_resolve___boxed), 7, 2);
lean_closure_set(v___x_484_, 0, v_item_471_);
lean_closure_set(v___x_484_, 1, v_id_472_);
v___x_485_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_481_, v___x_483_, v___x_484_);
return v___x_485_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_resolveCompletionItem_x3f___boxed(lean_object* v_fileMap_486_, lean_object* v_hoverPos_487_, lean_object* v_cmdStx_488_, lean_object* v_infoTree_489_, lean_object* v_item_490_, lean_object* v_id_491_, lean_object* v_completionInfoPos_492_, lean_object* v_a_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l_Lean_Server_Completion_resolveCompletionItem_x3f(v_fileMap_486_, v_hoverPos_487_, v_cmdStx_488_, v_infoTree_489_, v_item_490_, v_id_491_, v_completionInfoPos_492_);
lean_dec(v_completionInfoPos_492_);
return v_res_494_;
}
}
lean_object* runtime_initialize_Lean_Data_Lsp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_Completion_CompletionInfoSelection(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Deprecated(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Server_Completion_CompletionResolution(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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

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
lean_object* v___x_152_; lean_object* v_env_153_; lean_object* v_ref_154_; lean_object* v_currNamespace_155_; lean_object* v_openDecls_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_152_ = lean_st_ref_get(v___y_150_);
v_env_153_ = lean_ctor_get(v___x_152_, 0);
lean_inc_ref(v_env_153_);
lean_dec(v___x_152_);
v_ref_154_ = lean_ctor_get(v___y_149_, 5);
v_currNamespace_155_ = lean_ctor_get(v___y_149_, 6);
v_openDecls_156_ = lean_ctor_get(v___y_149_, 7);
v___x_157_ = l_Lean_Options_empty;
lean_inc(v_openDecls_156_);
lean_inc(v_currNamespace_155_);
v___x_158_ = l_Lean_findDocString_x3f(v_env_153_, v_declName_147_, v_includeBuiltin_148_, v___x_157_, v_currNamespace_155_, v_openDecls_156_);
if (lean_obj_tag(v___x_158_) == 0)
{
lean_object* v_a_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_166_; 
v_a_159_ = lean_ctor_get(v___x_158_, 0);
v_isSharedCheck_166_ = !lean_is_exclusive(v___x_158_);
if (v_isSharedCheck_166_ == 0)
{
v___x_161_ = v___x_158_;
v_isShared_162_ = v_isSharedCheck_166_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_a_159_);
lean_dec(v___x_158_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_166_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___x_164_; 
if (v_isShared_162_ == 0)
{
v___x_164_ = v___x_161_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v_a_159_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
}
else
{
lean_object* v_a_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_178_; 
v_a_167_ = lean_ctor_get(v___x_158_, 0);
v_isSharedCheck_178_ = !lean_is_exclusive(v___x_158_);
if (v_isSharedCheck_178_ == 0)
{
v___x_169_ = v___x_158_;
v_isShared_170_ = v_isSharedCheck_178_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_a_167_);
lean_dec(v___x_158_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_178_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_176_; 
v___x_171_ = lean_io_error_to_string(v_a_167_);
v___x_172_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_172_, 0, v___x_171_);
v___x_173_ = l_Lean_MessageData_ofFormat(v___x_172_);
lean_inc(v_ref_154_);
v___x_174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_174_, 0, v_ref_154_);
lean_ctor_set(v___x_174_, 1, v___x_173_);
if (v_isShared_170_ == 0)
{
lean_ctor_set(v___x_169_, 0, v___x_174_);
v___x_176_ = v___x_169_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v___x_174_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findMarkdownDocString_x3f___at___00Lean_Lsp_CompletionItem_resolve_spec__0___redArg___boxed(lean_object* v_declName_179_, lean_object* v_includeBuiltin_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_){
_start:
{
uint8_t v_includeBuiltin_boxed_184_; lean_object* v_res_185_; 
v_includeBuiltin_boxed_184_ = lean_unbox(v_includeBuiltin_180_);
v_res_185_ = l_Lean_findMarkdownDocString_x3f___at___00Lean_Lsp_CompletionItem_resolve_spec__0___redArg(v_declName_179_, v_includeBuiltin_boxed_184_, v___y_181_, v___y_182_);
lean_dec(v___y_182_);
lean_dec_ref(v___y_181_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_findMarkdownDocString_x3f___at___00Lean_Lsp_CompletionItem_resolve_spec__0(lean_object* v_declName_186_, uint8_t v_includeBuiltin_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = l_Lean_findMarkdownDocString_x3f___at___00Lean_Lsp_CompletionItem_resolve_spec__0___redArg(v_declName_186_, v_includeBuiltin_187_, v___y_190_, v___y_191_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_findMarkdownDocString_x3f___at___00Lean_Lsp_CompletionItem_resolve_spec__0___boxed(lean_object* v_declName_194_, lean_object* v_includeBuiltin_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_){
_start:
{
uint8_t v_includeBuiltin_boxed_201_; lean_object* v_res_202_; 
v_includeBuiltin_boxed_201_ = lean_unbox(v_includeBuiltin_195_);
v_res_202_ = l_Lean_findMarkdownDocString_x3f___at___00Lean_Lsp_CompletionItem_resolve_spec__0(v_declName_194_, v_includeBuiltin_boxed_201_, v___y_196_, v___y_197_, v___y_198_, v___y_199_);
lean_dec(v___y_199_);
lean_dec_ref(v___y_198_);
lean_dec(v___y_197_);
lean_dec_ref(v___y_196_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___lam__0(lean_object* v_docValue_203_){
_start:
{
uint8_t v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_204_ = 1;
v___x_205_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_205_, 0, v_docValue_203_);
lean_ctor_set_uint8(v___x_205_, sizeof(void*)*1, v___x_204_);
v___x_206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_206_, 0, v___x_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___lam__1(lean_object* v_documentation_x3f_207_, lean_object* v___f_208_, lean_object* v_docStringPrefix_209_){
_start:
{
if (lean_obj_tag(v_docStringPrefix_209_) == 0)
{
lean_dec_ref(v___f_208_);
lean_inc(v_documentation_x3f_207_);
return v_documentation_x3f_207_;
}
else
{
lean_object* v_val_210_; lean_object* v___x_211_; 
v_val_210_ = lean_ctor_get(v_docStringPrefix_209_, 0);
lean_inc(v_val_210_);
lean_dec_ref_known(v_docStringPrefix_209_, 1);
v___x_211_ = lean_apply_1(v___f_208_, v_val_210_);
return v___x_211_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___lam__1___boxed(lean_object* v_documentation_x3f_212_, lean_object* v___f_213_, lean_object* v_docStringPrefix_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_Lean_Lsp_CompletionItem_resolve___lam__1(v_documentation_x3f_212_, v___f_213_, v_docStringPrefix_214_);
lean_dec(v_documentation_x3f_212_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___lam__2(lean_object* v_typeWithoutImplicits_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = l_Lean_Meta_ppExpr(v_typeWithoutImplicits_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_);
if (lean_obj_tag(v___x_222_) == 0)
{
lean_object* v_a_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_233_; 
v_a_223_ = lean_ctor_get(v___x_222_, 0);
v_isSharedCheck_233_ = !lean_is_exclusive(v___x_222_);
if (v_isSharedCheck_233_ == 0)
{
v___x_225_ = v___x_222_;
v_isShared_226_ = v_isSharedCheck_233_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_a_223_);
lean_dec(v___x_222_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_233_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_231_; 
v___x_227_ = l_Std_Format_defWidth;
v___x_228_ = lean_unsigned_to_nat(0u);
v___x_229_ = l_Std_Format_pretty(v_a_223_, v___x_227_, v___x_228_, v___x_228_);
if (v_isShared_226_ == 0)
{
lean_ctor_set(v___x_225_, 0, v___x_229_);
v___x_231_ = v___x_225_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v___x_229_);
v___x_231_ = v_reuseFailAlloc_232_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
return v___x_231_;
}
}
}
else
{
lean_object* v_a_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_241_; 
v_a_234_ = lean_ctor_get(v___x_222_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v___x_222_);
if (v_isSharedCheck_241_ == 0)
{
v___x_236_ = v___x_222_;
v_isShared_237_ = v_isSharedCheck_241_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_a_234_);
lean_dec(v___x_222_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_241_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v___x_239_; 
if (v_isShared_237_ == 0)
{
v___x_239_ = v___x_236_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_a_234_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___lam__2___boxed(lean_object* v_typeWithoutImplicits_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_Lean_Lsp_CompletionItem_resolve___lam__2(v_typeWithoutImplicits_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_);
lean_dec(v___y_246_);
lean_dec_ref(v___y_245_);
lean_dec(v___y_244_);
lean_dec_ref(v___y_243_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve(lean_object* v_item_259_, lean_object* v_id_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_){
_start:
{
lean_object* v___y_267_; lean_object* v___y_268_; lean_object* v___y_269_; lean_object* v___y_270_; lean_object* v___y_271_; lean_object* v___y_272_; lean_object* v___y_273_; lean_object* v___y_274_; lean_object* v___x_277_; lean_object* v_env_278_; lean_object* v_label_279_; lean_object* v_detail_x3f_280_; lean_object* v_documentation_x3f_281_; lean_object* v_kind_x3f_282_; lean_object* v_textEdit_x3f_283_; lean_object* v_sortText_x3f_284_; lean_object* v_data_x3f_285_; lean_object* v_tags_x3f_286_; lean_object* v___f_287_; lean_object* v___y_289_; lean_object* v___y_290_; lean_object* v___y_291_; lean_object* v___y_292_; lean_object* v___y_293_; lean_object* v___y_294_; lean_object* v___y_295_; lean_object* v___y_296_; lean_object* v___y_297_; lean_object* v___y_303_; lean_object* v___y_304_; lean_object* v___y_305_; lean_object* v___y_306_; lean_object* v___y_307_; lean_object* v___y_308_; lean_object* v___y_309_; lean_object* v___y_310_; lean_object* v___y_311_; lean_object* v___y_312_; lean_object* v_docString_x3f_313_; lean_object* v___y_328_; lean_object* v___y_329_; lean_object* v___y_330_; lean_object* v___y_331_; lean_object* v___y_332_; uint8_t v___y_333_; lean_object* v___y_334_; lean_object* v___y_335_; lean_object* v___y_336_; lean_object* v___y_337_; lean_object* v___y_338_; lean_object* v___y_339_; lean_object* v___y_340_; lean_object* v___y_354_; lean_object* v___y_355_; lean_object* v___y_356_; lean_object* v___y_357_; lean_object* v___y_358_; uint8_t v___y_359_; lean_object* v___y_360_; lean_object* v___y_361_; lean_object* v___y_362_; lean_object* v___y_363_; lean_object* v___y_364_; lean_object* v___y_365_; lean_object* v___y_366_; lean_object* v_item_369_; lean_object* v_label_370_; lean_object* v_detail_x3f_371_; lean_object* v_documentation_x3f_372_; lean_object* v_kind_x3f_373_; lean_object* v_textEdit_x3f_374_; lean_object* v_sortText_x3f_375_; lean_object* v_data_x3f_376_; lean_object* v_tags_x3f_377_; lean_object* v___y_378_; lean_object* v___y_379_; lean_object* v_a_432_; 
v___x_277_ = lean_st_ref_get(v_a_264_);
v_env_278_ = lean_ctor_get(v___x_277_, 0);
lean_inc_ref(v_env_278_);
lean_dec(v___x_277_);
v_label_279_ = lean_ctor_get(v_item_259_, 0);
lean_inc_ref(v_label_279_);
v_detail_x3f_280_ = lean_ctor_get(v_item_259_, 1);
lean_inc(v_detail_x3f_280_);
v_documentation_x3f_281_ = lean_ctor_get(v_item_259_, 2);
lean_inc(v_documentation_x3f_281_);
v_kind_x3f_282_ = lean_ctor_get(v_item_259_, 3);
lean_inc(v_kind_x3f_282_);
v_textEdit_x3f_283_ = lean_ctor_get(v_item_259_, 4);
lean_inc(v_textEdit_x3f_283_);
v_sortText_x3f_284_ = lean_ctor_get(v_item_259_, 5);
lean_inc(v_sortText_x3f_284_);
v_data_x3f_285_ = lean_ctor_get(v_item_259_, 6);
lean_inc(v_data_x3f_285_);
v_tags_x3f_286_ = lean_ctor_get(v_item_259_, 7);
lean_inc(v_tags_x3f_286_);
v___f_287_ = ((lean_object*)(l_Lean_Lsp_CompletionItem_resolve___closed__0));
if (lean_obj_tag(v_detail_x3f_280_) == 0)
{
lean_object* v___f_434_; lean_object* v_val_436_; 
lean_dec_ref(v_item_259_);
v___f_434_ = ((lean_object*)(l_Lean_Lsp_CompletionItem_resolve___closed__9));
if (lean_obj_tag(v_id_260_) == 0)
{
lean_object* v_declName_448_; uint8_t v___x_449_; lean_object* v___x_450_; 
v_declName_448_ = lean_ctor_get(v_id_260_, 0);
v___x_449_ = 0;
lean_inc(v_declName_448_);
lean_inc_ref(v_env_278_);
v___x_450_ = l_Lean_Environment_find_x3f(v_env_278_, v_declName_448_, v___x_449_);
if (lean_obj_tag(v___x_450_) == 0)
{
v_a_432_ = v_detail_x3f_280_;
goto v___jp_431_;
}
else
{
lean_object* v_val_451_; lean_object* v___x_452_; 
v_val_451_ = lean_ctor_get(v___x_450_, 0);
lean_inc(v_val_451_);
lean_dec_ref_known(v___x_450_, 1);
v___x_452_ = l_Lean_ConstantInfo_type(v_val_451_);
lean_dec(v_val_451_);
v_val_436_ = v___x_452_;
goto v___jp_435_;
}
}
else
{
lean_object* v_id_453_; lean_object* v_lctx_454_; lean_object* v___x_455_; 
v_id_453_ = lean_ctor_get(v_id_260_, 0);
v_lctx_454_ = lean_ctor_get(v_a_261_, 2);
lean_inc(v_id_453_);
lean_inc_ref(v_lctx_454_);
v___x_455_ = lean_local_ctx_find(v_lctx_454_, v_id_453_);
if (lean_obj_tag(v___x_455_) == 0)
{
v_a_432_ = v_detail_x3f_280_;
goto v___jp_431_;
}
else
{
lean_object* v_val_456_; lean_object* v___x_457_; 
v_val_456_ = lean_ctor_get(v___x_455_, 0);
lean_inc(v_val_456_);
lean_dec_ref_known(v___x_455_, 1);
v___x_457_ = l_Lean_LocalDecl_type(v_val_456_);
lean_dec(v_val_456_);
v_val_436_ = v___x_457_;
goto v___jp_435_;
}
}
v___jp_435_:
{
lean_object* v___x_437_; 
v___x_437_ = l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg(v_val_436_, v___f_434_, v_a_261_, v_a_262_, v_a_263_, v_a_264_);
if (lean_obj_tag(v___x_437_) == 0)
{
lean_object* v_a_438_; lean_object* v___x_439_; 
v_a_438_ = lean_ctor_get(v___x_437_, 0);
lean_inc(v_a_438_);
lean_dec_ref_known(v___x_437_, 1);
v___x_439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_439_, 0, v_a_438_);
v_a_432_ = v___x_439_;
goto v___jp_431_;
}
else
{
lean_object* v_a_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_447_; 
lean_dec(v_tags_x3f_286_);
lean_dec(v_data_x3f_285_);
lean_dec(v_sortText_x3f_284_);
lean_dec(v_textEdit_x3f_283_);
lean_dec(v_kind_x3f_282_);
lean_dec(v_documentation_x3f_281_);
lean_dec_ref(v_label_279_);
lean_dec_ref(v_env_278_);
lean_dec_ref(v_id_260_);
v_a_440_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_447_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_447_ == 0)
{
v___x_442_ = v___x_437_;
v_isShared_443_ = v_isSharedCheck_447_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_a_440_);
lean_dec(v___x_437_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_447_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_445_; 
if (v_isShared_443_ == 0)
{
v___x_445_ = v___x_442_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_a_440_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
return v___x_445_;
}
}
}
}
}
else
{
v_item_369_ = v_item_259_;
v_label_370_ = v_label_279_;
v_detail_x3f_371_ = v_detail_x3f_280_;
v_documentation_x3f_372_ = v_documentation_x3f_281_;
v_kind_x3f_373_ = v_kind_x3f_282_;
v_textEdit_x3f_374_ = v_textEdit_x3f_283_;
v_sortText_x3f_375_ = v_sortText_x3f_284_;
v_data_x3f_376_ = v_data_x3f_285_;
v_tags_x3f_377_ = v_tags_x3f_286_;
v___y_378_ = v_a_263_;
v___y_379_ = v_a_264_;
goto v___jp_368_;
}
v___jp_266_:
{
lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_275_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_275_, 0, v___y_273_);
lean_ctor_set(v___x_275_, 1, v___y_271_);
lean_ctor_set(v___x_275_, 2, v___y_274_);
lean_ctor_set(v___x_275_, 3, v___y_269_);
lean_ctor_set(v___x_275_, 4, v___y_270_);
lean_ctor_set(v___x_275_, 5, v___y_268_);
lean_ctor_set(v___x_275_, 6, v___y_272_);
lean_ctor_set(v___x_275_, 7, v___y_267_);
v___x_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_276_, 0, v___x_275_);
return v___x_276_;
}
v___jp_288_:
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_298_ = ((lean_object*)(l_Lean_Lsp_CompletionItem_resolve___closed__1));
v___x_299_ = lean_string_append(v___y_297_, v___x_298_);
v___x_300_ = lean_string_append(v___x_299_, v___y_295_);
lean_dec_ref(v___y_295_);
v___x_301_ = l_Lean_Lsp_CompletionItem_resolve___lam__0(v___x_300_);
v___y_267_ = v___y_289_;
v___y_268_ = v___y_290_;
v___y_269_ = v___y_291_;
v___y_270_ = v___y_293_;
v___y_271_ = v___y_292_;
v___y_272_ = v___y_294_;
v___y_273_ = v___y_296_;
v___y_274_ = v___x_301_;
goto v___jp_266_;
}
v___jp_302_:
{
if (lean_obj_tag(v___y_311_) == 0)
{
if (lean_obj_tag(v_docString_x3f_313_) == 0)
{
lean_dec_ref(v___y_310_);
v___y_267_ = v___y_303_;
v___y_268_ = v___y_304_;
v___y_269_ = v___y_305_;
v___y_270_ = v___y_307_;
v___y_271_ = v___y_306_;
v___y_272_ = v___y_308_;
v___y_273_ = v___y_312_;
v___y_274_ = v___y_309_;
goto v___jp_266_;
}
else
{
lean_object* v___x_314_; 
lean_dec(v___y_309_);
v___x_314_ = lean_apply_1(v___y_310_, v_docString_x3f_313_);
v___y_267_ = v___y_303_;
v___y_268_ = v___y_304_;
v___y_269_ = v___y_305_;
v___y_270_ = v___y_307_;
v___y_271_ = v___y_306_;
v___y_272_ = v___y_308_;
v___y_273_ = v___y_312_;
v___y_274_ = v___x_314_;
goto v___jp_266_;
}
}
else
{
lean_dec(v___y_309_);
if (lean_obj_tag(v_docString_x3f_313_) == 0)
{
lean_object* v_val_315_; lean_object* v___x_316_; 
v_val_315_ = lean_ctor_get(v___y_311_, 0);
lean_inc(v_val_315_);
lean_dec_ref_known(v___y_311_, 1);
v___x_316_ = lean_apply_1(v___y_310_, v_val_315_);
v___y_267_ = v___y_303_;
v___y_268_ = v___y_304_;
v___y_269_ = v___y_305_;
v___y_270_ = v___y_307_;
v___y_271_ = v___y_306_;
v___y_272_ = v___y_308_;
v___y_273_ = v___y_312_;
v___y_274_ = v___x_316_;
goto v___jp_266_;
}
else
{
lean_object* v_val_317_; 
lean_dec_ref(v___y_310_);
v_val_317_ = lean_ctor_get(v___y_311_, 0);
lean_inc(v_val_317_);
lean_dec_ref_known(v___y_311_, 1);
if (lean_obj_tag(v_val_317_) == 0)
{
lean_object* v_val_318_; lean_object* v___x_319_; 
v_val_318_ = lean_ctor_get(v_docString_x3f_313_, 0);
lean_inc(v_val_318_);
lean_dec_ref_known(v_docString_x3f_313_, 1);
v___x_319_ = ((lean_object*)(l_Lean_Lsp_CompletionItem_resolve___closed__2));
v___y_289_ = v___y_303_;
v___y_290_ = v___y_304_;
v___y_291_ = v___y_305_;
v___y_292_ = v___y_306_;
v___y_293_ = v___y_307_;
v___y_294_ = v___y_308_;
v___y_295_ = v_val_318_;
v___y_296_ = v___y_312_;
v___y_297_ = v___x_319_;
goto v___jp_288_;
}
else
{
lean_object* v_val_320_; lean_object* v_val_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v_val_320_ = lean_ctor_get(v_docString_x3f_313_, 0);
lean_inc(v_val_320_);
lean_dec_ref_known(v_docString_x3f_313_, 1);
v_val_321_ = lean_ctor_get(v_val_317_, 0);
lean_inc(v_val_321_);
lean_dec_ref_known(v_val_317_, 1);
v___x_322_ = ((lean_object*)(l_Lean_Lsp_CompletionItem_resolve___closed__3));
v___x_323_ = l_addParenHeuristic(v_val_321_);
v___x_324_ = lean_string_append(v___x_322_, v___x_323_);
lean_dec_ref(v___x_323_);
v___x_325_ = ((lean_object*)(l_Lean_Lsp_CompletionItem_resolve___closed__4));
v___x_326_ = lean_string_append(v___x_324_, v___x_325_);
v___y_289_ = v___y_303_;
v___y_290_ = v___y_304_;
v___y_291_ = v___y_305_;
v___y_292_ = v___y_306_;
v___y_293_ = v___y_307_;
v___y_294_ = v___y_308_;
v___y_295_ = v_val_320_;
v___y_296_ = v___y_312_;
v___y_297_ = v___x_326_;
goto v___jp_288_;
}
}
}
}
v___jp_327_:
{
if (lean_obj_tag(v_id_260_) == 0)
{
lean_object* v_declName_341_; lean_object* v___x_342_; 
v_declName_341_ = lean_ctor_get(v_id_260_, 0);
lean_inc(v_declName_341_);
lean_dec_ref_known(v_id_260_, 1);
v___x_342_ = l_Lean_findMarkdownDocString_x3f___at___00Lean_Lsp_CompletionItem_resolve_spec__0___redArg(v_declName_341_, v___y_333_, v___y_334_, v___y_330_);
if (lean_obj_tag(v___x_342_) == 0)
{
lean_object* v_a_343_; 
v_a_343_ = lean_ctor_get(v___x_342_, 0);
lean_inc(v_a_343_);
lean_dec_ref_known(v___x_342_, 1);
v___y_303_ = v___y_328_;
v___y_304_ = v___y_329_;
v___y_305_ = v___y_335_;
v___y_306_ = v___y_331_;
v___y_307_ = v___y_332_;
v___y_308_ = v___y_336_;
v___y_309_ = v___y_337_;
v___y_310_ = v___y_338_;
v___y_311_ = v___y_340_;
v___y_312_ = v___y_339_;
v_docString_x3f_313_ = v_a_343_;
goto v___jp_302_;
}
else
{
lean_object* v_a_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_351_; 
lean_dec(v___y_340_);
lean_dec_ref(v___y_339_);
lean_dec_ref(v___y_338_);
lean_dec(v___y_337_);
lean_dec(v___y_336_);
lean_dec(v___y_335_);
lean_dec(v___y_332_);
lean_dec(v___y_331_);
lean_dec(v___y_329_);
lean_dec(v___y_328_);
v_a_344_ = lean_ctor_get(v___x_342_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v___x_342_);
if (v_isSharedCheck_351_ == 0)
{
v___x_346_ = v___x_342_;
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_a_344_);
lean_dec(v___x_342_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_349_; 
if (v_isShared_347_ == 0)
{
v___x_349_ = v___x_346_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_a_344_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
}
}
}
}
else
{
lean_object* v___x_352_; 
lean_dec_ref(v_id_260_);
v___x_352_ = lean_box(0);
v___y_303_ = v___y_328_;
v___y_304_ = v___y_329_;
v___y_305_ = v___y_335_;
v___y_306_ = v___y_331_;
v___y_307_ = v___y_332_;
v___y_308_ = v___y_336_;
v___y_309_ = v___y_337_;
v___y_310_ = v___y_338_;
v___y_311_ = v___y_340_;
v___y_312_ = v___y_339_;
v_docString_x3f_313_ = v___x_352_;
goto v___jp_302_;
}
}
v___jp_353_:
{
lean_object* v___x_367_; 
v___x_367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_367_, 0, v___y_366_);
v___y_328_ = v___y_354_;
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
v___y_339_ = v___y_365_;
v___y_340_ = v___x_367_;
goto v___jp_327_;
}
v___jp_368_:
{
if (lean_obj_tag(v_documentation_x3f_372_) == 0)
{
lean_object* v___f_380_; uint8_t v___x_381_; 
lean_dec_ref(v_item_369_);
v___f_380_ = lean_alloc_closure((void*)(l_Lean_Lsp_CompletionItem_resolve___lam__1___boxed), 3, 2);
lean_closure_set(v___f_380_, 0, v_documentation_x3f_372_);
lean_closure_set(v___f_380_, 1, v___f_287_);
v___x_381_ = 1;
if (lean_obj_tag(v_id_260_) == 0)
{
lean_object* v_declName_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v_declName_382_ = lean_ctor_get(v_id_260_, 0);
v___x_383_ = l_Lean_Linter_instInhabitedDeprecationEntry_default;
v___x_384_ = l_Lean_Linter_deprecatedAttr;
lean_inc(v_declName_382_);
v___x_385_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_383_, v___x_384_, v_env_278_, v_declName_382_);
if (lean_obj_tag(v___x_385_) == 1)
{
lean_object* v_val_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_420_; 
v_val_386_ = lean_ctor_get(v___x_385_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_385_);
if (v_isSharedCheck_420_ == 0)
{
v___x_388_ = v___x_385_;
v_isShared_389_ = v_isSharedCheck_420_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_val_386_);
lean_dec(v___x_385_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_420_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v_text_x3f_390_; 
v_text_x3f_390_ = lean_ctor_get(v_val_386_, 1);
if (lean_obj_tag(v_text_x3f_390_) == 1)
{
lean_object* v___x_392_; 
lean_inc_ref(v_text_x3f_390_);
lean_dec(v_val_386_);
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 0, v_text_x3f_390_);
v___x_392_ = v___x_388_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v_text_x3f_390_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
v___y_328_ = v_tags_x3f_377_;
v___y_329_ = v_sortText_x3f_375_;
v___y_330_ = v___y_379_;
v___y_331_ = v_detail_x3f_371_;
v___y_332_ = v_textEdit_x3f_374_;
v___y_333_ = v___x_381_;
v___y_334_ = v___y_378_;
v___y_335_ = v_kind_x3f_373_;
v___y_336_ = v_data_x3f_376_;
v___y_337_ = v_documentation_x3f_372_;
v___y_338_ = v___f_380_;
v___y_339_ = v_label_370_;
v___y_340_ = v___x_392_;
goto v___jp_327_;
}
}
else
{
lean_object* v_newName_x3f_394_; 
v_newName_x3f_394_ = lean_ctor_get(v_val_386_, 0);
lean_inc(v_newName_x3f_394_);
lean_dec(v_val_386_);
if (lean_obj_tag(v_newName_x3f_394_) == 1)
{
lean_object* v_val_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_411_; 
lean_del_object(v___x_388_);
v_val_395_ = lean_ctor_get(v_newName_x3f_394_, 0);
v_isSharedCheck_411_ = !lean_is_exclusive(v_newName_x3f_394_);
if (v_isSharedCheck_411_ == 0)
{
v___x_397_ = v_newName_x3f_394_;
v_isShared_398_ = v_isSharedCheck_411_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_val_395_);
lean_dec(v_newName_x3f_394_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_411_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_409_; 
v___x_399_ = ((lean_object*)(l_Lean_Lsp_CompletionItem_resolve___closed__5));
lean_inc(v_declName_382_);
v___x_400_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_382_, v___x_381_);
v___x_401_ = lean_string_append(v___x_399_, v___x_400_);
lean_dec_ref(v___x_400_);
v___x_402_ = ((lean_object*)(l_Lean_Lsp_CompletionItem_resolve___closed__6));
v___x_403_ = lean_string_append(v___x_401_, v___x_402_);
v___x_404_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_395_, v___x_381_);
v___x_405_ = lean_string_append(v___x_403_, v___x_404_);
lean_dec_ref(v___x_404_);
v___x_406_ = ((lean_object*)(l_Lean_Lsp_CompletionItem_resolve___closed__7));
v___x_407_ = lean_string_append(v___x_405_, v___x_406_);
if (v_isShared_398_ == 0)
{
lean_ctor_set(v___x_397_, 0, v___x_407_);
v___x_409_ = v___x_397_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_407_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
v___y_354_ = v_tags_x3f_377_;
v___y_355_ = v_sortText_x3f_375_;
v___y_356_ = v___y_379_;
v___y_357_ = v_detail_x3f_371_;
v___y_358_ = v_textEdit_x3f_374_;
v___y_359_ = v___x_381_;
v___y_360_ = v___y_378_;
v___y_361_ = v_kind_x3f_373_;
v___y_362_ = v_data_x3f_376_;
v___y_363_ = v_documentation_x3f_372_;
v___y_364_ = v___f_380_;
v___y_365_ = v_label_370_;
v___y_366_ = v___x_409_;
goto v___jp_353_;
}
}
}
else
{
lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_418_; 
lean_dec(v_newName_x3f_394_);
v___x_412_ = ((lean_object*)(l_Lean_Lsp_CompletionItem_resolve___closed__5));
lean_inc(v_declName_382_);
v___x_413_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_382_, v___x_381_);
v___x_414_ = lean_string_append(v___x_412_, v___x_413_);
lean_dec_ref(v___x_413_);
v___x_415_ = ((lean_object*)(l_Lean_Lsp_CompletionItem_resolve___closed__8));
v___x_416_ = lean_string_append(v___x_414_, v___x_415_);
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 0, v___x_416_);
v___x_418_ = v___x_388_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v___x_416_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
v___y_354_ = v_tags_x3f_377_;
v___y_355_ = v_sortText_x3f_375_;
v___y_356_ = v___y_379_;
v___y_357_ = v_detail_x3f_371_;
v___y_358_ = v_textEdit_x3f_374_;
v___y_359_ = v___x_381_;
v___y_360_ = v___y_378_;
v___y_361_ = v_kind_x3f_373_;
v___y_362_ = v_data_x3f_376_;
v___y_363_ = v_documentation_x3f_372_;
v___y_364_ = v___f_380_;
v___y_365_ = v_label_370_;
v___y_366_ = v___x_418_;
goto v___jp_353_;
}
}
}
}
}
else
{
lean_object* v___x_421_; 
lean_dec(v___x_385_);
v___x_421_ = lean_box(0);
v___y_328_ = v_tags_x3f_377_;
v___y_329_ = v_sortText_x3f_375_;
v___y_330_ = v___y_379_;
v___y_331_ = v_detail_x3f_371_;
v___y_332_ = v_textEdit_x3f_374_;
v___y_333_ = v___x_381_;
v___y_334_ = v___y_378_;
v___y_335_ = v_kind_x3f_373_;
v___y_336_ = v_data_x3f_376_;
v___y_337_ = v_documentation_x3f_372_;
v___y_338_ = v___f_380_;
v___y_339_ = v_label_370_;
v___y_340_ = v___x_421_;
goto v___jp_327_;
}
}
else
{
lean_object* v___x_422_; 
lean_dec_ref(v_env_278_);
v___x_422_ = lean_box(0);
v___y_328_ = v_tags_x3f_377_;
v___y_329_ = v_sortText_x3f_375_;
v___y_330_ = v___y_379_;
v___y_331_ = v_detail_x3f_371_;
v___y_332_ = v_textEdit_x3f_374_;
v___y_333_ = v___x_381_;
v___y_334_ = v___y_378_;
v___y_335_ = v_kind_x3f_373_;
v___y_336_ = v_data_x3f_376_;
v___y_337_ = v_documentation_x3f_372_;
v___y_338_ = v___f_380_;
v___y_339_ = v_label_370_;
v___y_340_ = v___x_422_;
goto v___jp_327_;
}
}
else
{
lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_429_; 
lean_dec(v_tags_x3f_377_);
lean_dec(v_data_x3f_376_);
lean_dec(v_sortText_x3f_375_);
lean_dec(v_textEdit_x3f_374_);
lean_dec(v_kind_x3f_373_);
lean_dec(v_detail_x3f_371_);
lean_dec_ref(v_label_370_);
lean_dec_ref(v_env_278_);
lean_dec_ref(v_id_260_);
v_isSharedCheck_429_ = !lean_is_exclusive(v_documentation_x3f_372_);
if (v_isSharedCheck_429_ == 0)
{
lean_object* v_unused_430_; 
v_unused_430_ = lean_ctor_get(v_documentation_x3f_372_, 0);
lean_dec(v_unused_430_);
v___x_424_ = v_documentation_x3f_372_;
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
else
{
lean_dec(v_documentation_x3f_372_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_427_; 
if (v_isShared_425_ == 0)
{
lean_ctor_set_tag(v___x_424_, 0);
lean_ctor_set(v___x_424_, 0, v_item_369_);
v___x_427_ = v___x_424_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_item_369_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
}
v___jp_431_:
{
lean_object* v___x_433_; 
lean_inc(v_tags_x3f_286_);
lean_inc(v_data_x3f_285_);
lean_inc(v_sortText_x3f_284_);
lean_inc(v_textEdit_x3f_283_);
lean_inc(v_kind_x3f_282_);
lean_inc(v_documentation_x3f_281_);
lean_inc(v_a_432_);
lean_inc_ref(v_label_279_);
v___x_433_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_433_, 0, v_label_279_);
lean_ctor_set(v___x_433_, 1, v_a_432_);
lean_ctor_set(v___x_433_, 2, v_documentation_x3f_281_);
lean_ctor_set(v___x_433_, 3, v_kind_x3f_282_);
lean_ctor_set(v___x_433_, 4, v_textEdit_x3f_283_);
lean_ctor_set(v___x_433_, 5, v_sortText_x3f_284_);
lean_ctor_set(v___x_433_, 6, v_data_x3f_285_);
lean_ctor_set(v___x_433_, 7, v_tags_x3f_286_);
v_item_369_ = v___x_433_;
v_label_370_ = v_label_279_;
v_detail_x3f_371_ = v_a_432_;
v_documentation_x3f_372_ = v_documentation_x3f_281_;
v_kind_x3f_373_ = v_kind_x3f_282_;
v_textEdit_x3f_374_ = v_textEdit_x3f_283_;
v_sortText_x3f_375_ = v_sortText_x3f_284_;
v_data_x3f_376_ = v_data_x3f_285_;
v_tags_x3f_377_ = v_tags_x3f_286_;
v___y_378_ = v_a_263_;
v___y_379_ = v_a_264_;
goto v___jp_368_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___boxed(lean_object* v_item_458_, lean_object* v_id_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Lean_Lsp_CompletionItem_resolve(v_item_458_, v_id_459_, v_a_460_, v_a_461_, v_a_462_, v_a_463_);
lean_dec(v_a_463_);
lean_dec_ref(v_a_462_);
lean_dec(v_a_461_);
lean_dec_ref(v_a_460_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_resolveCompletionItem_x3f(lean_object* v_fileMap_466_, lean_object* v_hoverPos_467_, lean_object* v_cmdStx_468_, lean_object* v_infoTree_469_, lean_object* v_item_470_, lean_object* v_id_471_, lean_object* v_completionInfoPos_472_){
_start:
{
lean_object* v___x_474_; lean_object* v_fst_475_; lean_object* v___x_476_; uint8_t v___x_477_; 
v___x_474_ = l_Lean_Server_Completion_findCompletionInfosAt(v_fileMap_466_, v_hoverPos_467_, v_cmdStx_468_, v_infoTree_469_);
v_fst_475_ = lean_ctor_get(v___x_474_, 0);
lean_inc(v_fst_475_);
lean_dec_ref(v___x_474_);
v___x_476_ = lean_array_get_size(v_fst_475_);
v___x_477_ = lean_nat_dec_lt(v_completionInfoPos_472_, v___x_476_);
if (v___x_477_ == 0)
{
lean_object* v___x_478_; 
lean_dec(v_fst_475_);
lean_dec_ref(v_id_471_);
v___x_478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_478_, 0, v_item_470_);
return v___x_478_;
}
else
{
lean_object* v___x_479_; lean_object* v_ctx_480_; lean_object* v_info_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_479_ = lean_array_fget(v_fst_475_, v_completionInfoPos_472_);
lean_dec(v_fst_475_);
v_ctx_480_ = lean_ctor_get(v___x_479_, 1);
lean_inc_ref(v_ctx_480_);
v_info_481_ = lean_ctor_get(v___x_479_, 2);
lean_inc_ref(v_info_481_);
lean_dec(v___x_479_);
v___x_482_ = l_Lean_Elab_CompletionInfo_lctx(v_info_481_);
lean_dec_ref(v_info_481_);
v___x_483_ = lean_alloc_closure((void*)(l_Lean_Lsp_CompletionItem_resolve___boxed), 7, 2);
lean_closure_set(v___x_483_, 0, v_item_470_);
lean_closure_set(v___x_483_, 1, v_id_471_);
v___x_484_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_480_, v___x_482_, v___x_483_);
return v___x_484_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_resolveCompletionItem_x3f___boxed(lean_object* v_fileMap_485_, lean_object* v_hoverPos_486_, lean_object* v_cmdStx_487_, lean_object* v_infoTree_488_, lean_object* v_item_489_, lean_object* v_id_490_, lean_object* v_completionInfoPos_491_, lean_object* v_a_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_Lean_Server_Completion_resolveCompletionItem_x3f(v_fileMap_485_, v_hoverPos_486_, v_cmdStx_487_, v_infoTree_488_, v_item_489_, v_id_490_, v_completionInfoPos_491_);
lean_dec(v_completionInfoPos_491_);
return v_res_493_;
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

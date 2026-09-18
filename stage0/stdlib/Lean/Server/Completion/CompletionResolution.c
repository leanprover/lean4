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
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_addParenHeuristic(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___lam__2___boxed(lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_Lsp_CompletionItem_resolve___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_CompletionItem_resolve___lam__1___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_CompletionItem_resolve___closed__5 = (const lean_object*)&l_Lean_Lsp_CompletionItem_resolve___closed__5_value;
static const lean_string_object l_Lean_Lsp_CompletionItem_resolve___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Lsp_CompletionItem_resolve___closed__6 = (const lean_object*)&l_Lean_Lsp_CompletionItem_resolve___closed__6_value;
static const lean_string_object l_Lean_Lsp_CompletionItem_resolve___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "` has been deprecated, use `"};
static const lean_object* l_Lean_Lsp_CompletionItem_resolve___closed__7 = (const lean_object*)&l_Lean_Lsp_CompletionItem_resolve___closed__7_value;
static const lean_string_object l_Lean_Lsp_CompletionItem_resolve___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "` instead."};
static const lean_object* l_Lean_Lsp_CompletionItem_resolve___closed__8 = (const lean_object*)&l_Lean_Lsp_CompletionItem_resolve___closed__8_value;
static const lean_string_object l_Lean_Lsp_CompletionItem_resolve___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "` has been deprecated."};
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
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___lam__1(lean_object* v_typeWithoutImplicits_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = l_Lean_Meta_ppExpr(v_typeWithoutImplicits_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_);
if (lean_obj_tag(v___x_214_) == 0)
{
lean_object* v_a_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_225_; 
v_a_215_ = lean_ctor_get(v___x_214_, 0);
v_isSharedCheck_225_ = !lean_is_exclusive(v___x_214_);
if (v_isSharedCheck_225_ == 0)
{
v___x_217_ = v___x_214_;
v_isShared_218_ = v_isSharedCheck_225_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_a_215_);
lean_dec(v___x_214_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_225_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_223_; 
v___x_219_ = l_Std_Format_defWidth;
v___x_220_ = lean_unsigned_to_nat(0u);
v___x_221_ = l_Std_Format_pretty(v_a_215_, v___x_219_, v___x_220_, v___x_220_);
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 0, v___x_221_);
v___x_223_ = v___x_217_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v___x_221_);
v___x_223_ = v_reuseFailAlloc_224_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
return v___x_223_;
}
}
}
else
{
lean_object* v_a_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_233_; 
v_a_226_ = lean_ctor_get(v___x_214_, 0);
v_isSharedCheck_233_ = !lean_is_exclusive(v___x_214_);
if (v_isSharedCheck_233_ == 0)
{
v___x_228_ = v___x_214_;
v_isShared_229_ = v_isSharedCheck_233_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_a_226_);
lean_dec(v___x_214_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_233_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v___x_231_; 
if (v_isShared_229_ == 0)
{
v___x_231_ = v___x_228_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v_a_226_);
v___x_231_ = v_reuseFailAlloc_232_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
return v___x_231_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___lam__1___boxed(lean_object* v_typeWithoutImplicits_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Lean_Lsp_CompletionItem_resolve___lam__1(v_typeWithoutImplicits_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_);
lean_dec(v___y_238_);
lean_dec_ref(v___y_237_);
lean_dec(v___y_236_);
lean_dec_ref(v___y_235_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___lam__2(lean_object* v_documentation_x3f_241_, lean_object* v___f_242_, lean_object* v_docStringPrefix_243_){
_start:
{
if (lean_obj_tag(v_docStringPrefix_243_) == 0)
{
lean_dec_ref(v___f_242_);
lean_inc(v_documentation_x3f_241_);
return v_documentation_x3f_241_;
}
else
{
lean_object* v_val_244_; lean_object* v___x_245_; 
v_val_244_ = lean_ctor_get(v_docStringPrefix_243_, 0);
lean_inc(v_val_244_);
lean_dec_ref_known(v_docStringPrefix_243_, 1);
v___x_245_ = lean_apply_1(v___f_242_, v_val_244_);
return v___x_245_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___lam__2___boxed(lean_object* v_documentation_x3f_246_, lean_object* v___f_247_, lean_object* v_docStringPrefix_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l_Lean_Lsp_CompletionItem_resolve___lam__2(v_documentation_x3f_246_, v___f_247_, v_docStringPrefix_248_);
lean_dec(v_documentation_x3f_246_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve(lean_object* v_item_260_, lean_object* v_id_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_){
_start:
{
lean_object* v___y_268_; lean_object* v___y_269_; lean_object* v___y_270_; lean_object* v___y_271_; lean_object* v___y_272_; lean_object* v___y_273_; lean_object* v___y_274_; lean_object* v___y_275_; lean_object* v___f_278_; lean_object* v___y_280_; lean_object* v___y_281_; lean_object* v___y_282_; lean_object* v___y_283_; lean_object* v___y_284_; lean_object* v___y_285_; lean_object* v___y_286_; lean_object* v___y_287_; lean_object* v___y_288_; lean_object* v___y_294_; lean_object* v___y_295_; lean_object* v___y_296_; lean_object* v___y_297_; lean_object* v___y_298_; lean_object* v___y_299_; lean_object* v___y_300_; lean_object* v___y_301_; lean_object* v___y_302_; lean_object* v___y_303_; lean_object* v_docString_x3f_304_; lean_object* v___y_319_; lean_object* v___y_320_; lean_object* v___y_321_; lean_object* v___y_322_; lean_object* v___y_323_; lean_object* v___y_324_; lean_object* v___y_325_; lean_object* v___y_326_; lean_object* v___y_327_; uint8_t v___y_328_; lean_object* v___y_329_; lean_object* v___y_330_; lean_object* v___y_331_; lean_object* v___y_345_; lean_object* v___y_346_; lean_object* v___y_347_; lean_object* v___y_348_; lean_object* v___y_349_; lean_object* v___y_350_; lean_object* v___y_351_; lean_object* v___y_352_; lean_object* v___y_353_; uint8_t v___y_354_; lean_object* v___y_355_; lean_object* v___y_356_; lean_object* v___y_357_; lean_object* v___f_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v_env_362_; lean_object* v_item_364_; lean_object* v_label_365_; lean_object* v_detail_x3f_366_; lean_object* v_documentation_x3f_367_; lean_object* v_kind_x3f_368_; lean_object* v_textEdit_x3f_369_; lean_object* v_sortText_x3f_370_; lean_object* v_data_x3f_371_; lean_object* v_tags_x3f_372_; lean_object* v___y_373_; lean_object* v___y_374_; lean_object* v_label_425_; lean_object* v_detail_x3f_426_; lean_object* v_documentation_x3f_427_; lean_object* v_kind_x3f_428_; lean_object* v_textEdit_x3f_429_; lean_object* v_sortText_x3f_430_; lean_object* v_data_x3f_431_; lean_object* v_tags_x3f_432_; lean_object* v_a_434_; lean_object* v_val_437_; 
v___f_278_ = ((lean_object*)(l_Lean_Lsp_CompletionItem_resolve___closed__0));
v___f_359_ = ((lean_object*)(l_Lean_Lsp_CompletionItem_resolve___closed__5));
v___x_360_ = l_Lean_Linter_instInhabitedDeprecationEntry_default;
v___x_361_ = lean_st_ref_get(v_a_265_);
v_env_362_ = lean_ctor_get(v___x_361_, 0);
lean_inc_ref(v_env_362_);
lean_dec(v___x_361_);
v_label_425_ = lean_ctor_get(v_item_260_, 0);
lean_inc_ref(v_label_425_);
v_detail_x3f_426_ = lean_ctor_get(v_item_260_, 1);
lean_inc(v_detail_x3f_426_);
v_documentation_x3f_427_ = lean_ctor_get(v_item_260_, 2);
lean_inc(v_documentation_x3f_427_);
v_kind_x3f_428_ = lean_ctor_get(v_item_260_, 3);
lean_inc(v_kind_x3f_428_);
v_textEdit_x3f_429_ = lean_ctor_get(v_item_260_, 4);
lean_inc(v_textEdit_x3f_429_);
v_sortText_x3f_430_ = lean_ctor_get(v_item_260_, 5);
lean_inc(v_sortText_x3f_430_);
v_data_x3f_431_ = lean_ctor_get(v_item_260_, 6);
lean_inc(v_data_x3f_431_);
v_tags_x3f_432_ = lean_ctor_get(v_item_260_, 7);
lean_inc(v_tags_x3f_432_);
if (lean_obj_tag(v_detail_x3f_426_) == 0)
{
lean_dec_ref(v_item_260_);
if (lean_obj_tag(v_id_261_) == 0)
{
lean_object* v_declName_449_; uint8_t v___x_450_; lean_object* v___x_451_; 
v_declName_449_ = lean_ctor_get(v_id_261_, 0);
v___x_450_ = 0;
lean_inc(v_declName_449_);
lean_inc_ref(v_env_362_);
v___x_451_ = l_Lean_Environment_find_x3f(v_env_362_, v_declName_449_, v___x_450_);
if (lean_obj_tag(v___x_451_) == 0)
{
v_a_434_ = v_detail_x3f_426_;
goto v___jp_433_;
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
v_a_434_ = v_detail_x3f_426_;
goto v___jp_433_;
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
}
else
{
v_item_364_ = v_item_260_;
v_label_365_ = v_label_425_;
v_detail_x3f_366_ = v_detail_x3f_426_;
v_documentation_x3f_367_ = v_documentation_x3f_427_;
v_kind_x3f_368_ = v_kind_x3f_428_;
v_textEdit_x3f_369_ = v_textEdit_x3f_429_;
v_sortText_x3f_370_ = v_sortText_x3f_430_;
v_data_x3f_371_ = v_data_x3f_431_;
v_tags_x3f_372_ = v_tags_x3f_432_;
v___y_373_ = v_a_264_;
v___y_374_ = v_a_265_;
goto v___jp_363_;
}
v___jp_267_:
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_276_, 0, v___y_274_);
lean_ctor_set(v___x_276_, 1, v___y_271_);
lean_ctor_set(v___x_276_, 2, v___y_275_);
lean_ctor_set(v___x_276_, 3, v___y_268_);
lean_ctor_set(v___x_276_, 4, v___y_270_);
lean_ctor_set(v___x_276_, 5, v___y_273_);
lean_ctor_set(v___x_276_, 6, v___y_272_);
lean_ctor_set(v___x_276_, 7, v___y_269_);
v___x_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_277_, 0, v___x_276_);
return v___x_277_;
}
v___jp_279_:
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_289_ = ((lean_object*)(l_Lean_Lsp_CompletionItem_resolve___closed__1));
v___x_290_ = lean_string_append(v___y_288_, v___x_289_);
v___x_291_ = lean_string_append(v___x_290_, v___y_286_);
lean_dec_ref(v___y_286_);
v___x_292_ = l_Lean_Lsp_CompletionItem_resolve___lam__0(v___x_291_);
v___y_268_ = v___y_280_;
v___y_269_ = v___y_282_;
v___y_270_ = v___y_281_;
v___y_271_ = v___y_283_;
v___y_272_ = v___y_284_;
v___y_273_ = v___y_285_;
v___y_274_ = v___y_287_;
v___y_275_ = v___x_292_;
goto v___jp_267_;
}
v___jp_293_:
{
if (lean_obj_tag(v___y_302_) == 0)
{
if (lean_obj_tag(v_docString_x3f_304_) == 0)
{
lean_dec_ref(v___y_294_);
v___y_268_ = v___y_296_;
v___y_269_ = v___y_298_;
v___y_270_ = v___y_297_;
v___y_271_ = v___y_299_;
v___y_272_ = v___y_300_;
v___y_273_ = v___y_301_;
v___y_274_ = v___y_303_;
v___y_275_ = v___y_295_;
goto v___jp_267_;
}
else
{
lean_object* v___x_305_; 
lean_dec(v___y_295_);
v___x_305_ = lean_apply_1(v___y_294_, v_docString_x3f_304_);
v___y_268_ = v___y_296_;
v___y_269_ = v___y_298_;
v___y_270_ = v___y_297_;
v___y_271_ = v___y_299_;
v___y_272_ = v___y_300_;
v___y_273_ = v___y_301_;
v___y_274_ = v___y_303_;
v___y_275_ = v___x_305_;
goto v___jp_267_;
}
}
else
{
lean_dec(v___y_295_);
if (lean_obj_tag(v_docString_x3f_304_) == 0)
{
lean_object* v_val_306_; lean_object* v___x_307_; 
v_val_306_ = lean_ctor_get(v___y_302_, 0);
lean_inc(v_val_306_);
lean_dec_ref_known(v___y_302_, 1);
v___x_307_ = lean_apply_1(v___y_294_, v_val_306_);
v___y_268_ = v___y_296_;
v___y_269_ = v___y_298_;
v___y_270_ = v___y_297_;
v___y_271_ = v___y_299_;
v___y_272_ = v___y_300_;
v___y_273_ = v___y_301_;
v___y_274_ = v___y_303_;
v___y_275_ = v___x_307_;
goto v___jp_267_;
}
else
{
lean_object* v_val_308_; 
lean_dec_ref(v___y_294_);
v_val_308_ = lean_ctor_get(v___y_302_, 0);
lean_inc(v_val_308_);
lean_dec_ref_known(v___y_302_, 1);
if (lean_obj_tag(v_val_308_) == 0)
{
lean_object* v_val_309_; lean_object* v___x_310_; 
v_val_309_ = lean_ctor_get(v_docString_x3f_304_, 0);
lean_inc(v_val_309_);
lean_dec_ref_known(v_docString_x3f_304_, 1);
v___x_310_ = ((lean_object*)(l_Lean_Lsp_CompletionItem_resolve___closed__2));
v___y_280_ = v___y_296_;
v___y_281_ = v___y_297_;
v___y_282_ = v___y_298_;
v___y_283_ = v___y_299_;
v___y_284_ = v___y_300_;
v___y_285_ = v___y_301_;
v___y_286_ = v_val_309_;
v___y_287_ = v___y_303_;
v___y_288_ = v___x_310_;
goto v___jp_279_;
}
else
{
lean_object* v_val_311_; lean_object* v_val_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v_val_311_ = lean_ctor_get(v_docString_x3f_304_, 0);
lean_inc(v_val_311_);
lean_dec_ref_known(v_docString_x3f_304_, 1);
v_val_312_ = lean_ctor_get(v_val_308_, 0);
lean_inc(v_val_312_);
lean_dec_ref_known(v_val_308_, 1);
v___x_313_ = ((lean_object*)(l_Lean_Lsp_CompletionItem_resolve___closed__3));
v___x_314_ = l_addParenHeuristic(v_val_312_);
v___x_315_ = lean_string_append(v___x_313_, v___x_314_);
lean_dec_ref(v___x_314_);
v___x_316_ = ((lean_object*)(l_Lean_Lsp_CompletionItem_resolve___closed__4));
v___x_317_ = lean_string_append(v___x_315_, v___x_316_);
v___y_280_ = v___y_296_;
v___y_281_ = v___y_297_;
v___y_282_ = v___y_298_;
v___y_283_ = v___y_299_;
v___y_284_ = v___y_300_;
v___y_285_ = v___y_301_;
v___y_286_ = v_val_311_;
v___y_287_ = v___y_303_;
v___y_288_ = v___x_317_;
goto v___jp_279_;
}
}
}
}
v___jp_318_:
{
if (lean_obj_tag(v_id_261_) == 0)
{
lean_object* v_declName_332_; lean_object* v___x_333_; 
v_declName_332_ = lean_ctor_get(v_id_261_, 0);
lean_inc(v_declName_332_);
lean_dec_ref_known(v_id_261_, 1);
v___x_333_ = l_Lean_findMarkdownDocString_x3f___at___00Lean_Lsp_CompletionItem_resolve_spec__0___redArg(v_declName_332_, v___y_328_, v___y_326_, v___y_325_);
if (lean_obj_tag(v___x_333_) == 0)
{
lean_object* v_a_334_; 
v_a_334_ = lean_ctor_get(v___x_333_, 0);
lean_inc(v_a_334_);
lean_dec_ref_known(v___x_333_, 1);
v___y_294_ = v___y_319_;
v___y_295_ = v___y_327_;
v___y_296_ = v___y_329_;
v___y_297_ = v___y_330_;
v___y_298_ = v___y_320_;
v___y_299_ = v___y_321_;
v___y_300_ = v___y_322_;
v___y_301_ = v___y_323_;
v___y_302_ = v___y_331_;
v___y_303_ = v___y_324_;
v_docString_x3f_304_ = v_a_334_;
goto v___jp_293_;
}
else
{
lean_object* v_a_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_342_; 
lean_dec(v___y_331_);
lean_dec(v___y_330_);
lean_dec(v___y_329_);
lean_dec(v___y_327_);
lean_dec_ref(v___y_324_);
lean_dec(v___y_323_);
lean_dec(v___y_322_);
lean_dec(v___y_321_);
lean_dec(v___y_320_);
lean_dec_ref(v___y_319_);
v_a_335_ = lean_ctor_get(v___x_333_, 0);
v_isSharedCheck_342_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_342_ == 0)
{
v___x_337_ = v___x_333_;
v_isShared_338_ = v_isSharedCheck_342_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_a_335_);
lean_dec(v___x_333_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_342_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___x_340_; 
if (v_isShared_338_ == 0)
{
v___x_340_ = v___x_337_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v_a_335_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
return v___x_340_;
}
}
}
}
else
{
lean_object* v___x_343_; 
lean_dec_ref(v_id_261_);
v___x_343_ = lean_box(0);
v___y_294_ = v___y_319_;
v___y_295_ = v___y_327_;
v___y_296_ = v___y_329_;
v___y_297_ = v___y_330_;
v___y_298_ = v___y_320_;
v___y_299_ = v___y_321_;
v___y_300_ = v___y_322_;
v___y_301_ = v___y_323_;
v___y_302_ = v___y_331_;
v___y_303_ = v___y_324_;
v_docString_x3f_304_ = v___x_343_;
goto v___jp_293_;
}
}
v___jp_344_:
{
lean_object* v___x_358_; 
v___x_358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_358_, 0, v___y_357_);
v___y_319_ = v___y_345_;
v___y_320_ = v___y_346_;
v___y_321_ = v___y_347_;
v___y_322_ = v___y_348_;
v___y_323_ = v___y_349_;
v___y_324_ = v___y_350_;
v___y_325_ = v___y_351_;
v___y_326_ = v___y_352_;
v___y_327_ = v___y_353_;
v___y_328_ = v___y_354_;
v___y_329_ = v___y_355_;
v___y_330_ = v___y_356_;
v___y_331_ = v___x_358_;
goto v___jp_318_;
}
v___jp_363_:
{
if (lean_obj_tag(v_documentation_x3f_367_) == 0)
{
lean_object* v___f_375_; uint8_t v___x_376_; 
lean_dec_ref(v_item_364_);
v___f_375_ = lean_alloc_closure((void*)(l_Lean_Lsp_CompletionItem_resolve___lam__2___boxed), 3, 2);
lean_closure_set(v___f_375_, 0, v_documentation_x3f_367_);
lean_closure_set(v___f_375_, 1, v___f_278_);
v___x_376_ = 1;
if (lean_obj_tag(v_id_261_) == 0)
{
lean_object* v_declName_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v_declName_377_ = lean_ctor_get(v_id_261_, 0);
v___x_378_ = l_Lean_Linter_deprecatedAttr;
lean_inc(v_declName_377_);
v___x_379_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_360_, v___x_378_, v_env_362_, v_declName_377_);
if (lean_obj_tag(v___x_379_) == 1)
{
lean_object* v_val_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_414_; 
v_val_380_ = lean_ctor_get(v___x_379_, 0);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_414_ == 0)
{
v___x_382_ = v___x_379_;
v_isShared_383_ = v_isSharedCheck_414_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_val_380_);
lean_dec(v___x_379_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_414_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v_text_x3f_384_; 
v_text_x3f_384_ = lean_ctor_get(v_val_380_, 1);
if (lean_obj_tag(v_text_x3f_384_) == 1)
{
lean_object* v___x_386_; 
lean_inc_ref(v_text_x3f_384_);
lean_dec(v_val_380_);
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 0, v_text_x3f_384_);
v___x_386_ = v___x_382_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v_text_x3f_384_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
v___y_319_ = v___f_375_;
v___y_320_ = v_tags_x3f_372_;
v___y_321_ = v_detail_x3f_366_;
v___y_322_ = v_data_x3f_371_;
v___y_323_ = v_sortText_x3f_370_;
v___y_324_ = v_label_365_;
v___y_325_ = v___y_374_;
v___y_326_ = v___y_373_;
v___y_327_ = v_documentation_x3f_367_;
v___y_328_ = v___x_376_;
v___y_329_ = v_kind_x3f_368_;
v___y_330_ = v_textEdit_x3f_369_;
v___y_331_ = v___x_386_;
goto v___jp_318_;
}
}
else
{
lean_object* v_newName_x3f_388_; 
v_newName_x3f_388_ = lean_ctor_get(v_val_380_, 0);
lean_inc(v_newName_x3f_388_);
lean_dec(v_val_380_);
if (lean_obj_tag(v_newName_x3f_388_) == 1)
{
lean_object* v_val_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_405_; 
lean_del_object(v___x_382_);
v_val_389_ = lean_ctor_get(v_newName_x3f_388_, 0);
v_isSharedCheck_405_ = !lean_is_exclusive(v_newName_x3f_388_);
if (v_isSharedCheck_405_ == 0)
{
v___x_391_ = v_newName_x3f_388_;
v_isShared_392_ = v_isSharedCheck_405_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_val_389_);
lean_dec(v_newName_x3f_388_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_405_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_403_; 
v___x_393_ = ((lean_object*)(l_Lean_Lsp_CompletionItem_resolve___closed__6));
lean_inc(v_declName_377_);
v___x_394_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_377_, v___x_376_);
v___x_395_ = lean_string_append(v___x_393_, v___x_394_);
lean_dec_ref(v___x_394_);
v___x_396_ = ((lean_object*)(l_Lean_Lsp_CompletionItem_resolve___closed__7));
v___x_397_ = lean_string_append(v___x_395_, v___x_396_);
v___x_398_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_389_, v___x_376_);
v___x_399_ = lean_string_append(v___x_397_, v___x_398_);
lean_dec_ref(v___x_398_);
v___x_400_ = ((lean_object*)(l_Lean_Lsp_CompletionItem_resolve___closed__8));
v___x_401_ = lean_string_append(v___x_399_, v___x_400_);
if (v_isShared_392_ == 0)
{
lean_ctor_set(v___x_391_, 0, v___x_401_);
v___x_403_ = v___x_391_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v___x_401_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
v___y_345_ = v___f_375_;
v___y_346_ = v_tags_x3f_372_;
v___y_347_ = v_detail_x3f_366_;
v___y_348_ = v_data_x3f_371_;
v___y_349_ = v_sortText_x3f_370_;
v___y_350_ = v_label_365_;
v___y_351_ = v___y_374_;
v___y_352_ = v___y_373_;
v___y_353_ = v_documentation_x3f_367_;
v___y_354_ = v___x_376_;
v___y_355_ = v_kind_x3f_368_;
v___y_356_ = v_textEdit_x3f_369_;
v___y_357_ = v___x_403_;
goto v___jp_344_;
}
}
}
else
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_412_; 
lean_dec(v_newName_x3f_388_);
v___x_406_ = ((lean_object*)(l_Lean_Lsp_CompletionItem_resolve___closed__6));
lean_inc(v_declName_377_);
v___x_407_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_377_, v___x_376_);
v___x_408_ = lean_string_append(v___x_406_, v___x_407_);
lean_dec_ref(v___x_407_);
v___x_409_ = ((lean_object*)(l_Lean_Lsp_CompletionItem_resolve___closed__9));
v___x_410_ = lean_string_append(v___x_408_, v___x_409_);
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 0, v___x_410_);
v___x_412_ = v___x_382_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v___x_410_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
v___y_345_ = v___f_375_;
v___y_346_ = v_tags_x3f_372_;
v___y_347_ = v_detail_x3f_366_;
v___y_348_ = v_data_x3f_371_;
v___y_349_ = v_sortText_x3f_370_;
v___y_350_ = v_label_365_;
v___y_351_ = v___y_374_;
v___y_352_ = v___y_373_;
v___y_353_ = v_documentation_x3f_367_;
v___y_354_ = v___x_376_;
v___y_355_ = v_kind_x3f_368_;
v___y_356_ = v_textEdit_x3f_369_;
v___y_357_ = v___x_412_;
goto v___jp_344_;
}
}
}
}
}
else
{
lean_object* v___x_415_; 
lean_dec(v___x_379_);
v___x_415_ = lean_box(0);
v___y_319_ = v___f_375_;
v___y_320_ = v_tags_x3f_372_;
v___y_321_ = v_detail_x3f_366_;
v___y_322_ = v_data_x3f_371_;
v___y_323_ = v_sortText_x3f_370_;
v___y_324_ = v_label_365_;
v___y_325_ = v___y_374_;
v___y_326_ = v___y_373_;
v___y_327_ = v_documentation_x3f_367_;
v___y_328_ = v___x_376_;
v___y_329_ = v_kind_x3f_368_;
v___y_330_ = v_textEdit_x3f_369_;
v___y_331_ = v___x_415_;
goto v___jp_318_;
}
}
else
{
lean_object* v___x_416_; 
lean_dec_ref(v_env_362_);
v___x_416_ = lean_box(0);
v___y_319_ = v___f_375_;
v___y_320_ = v_tags_x3f_372_;
v___y_321_ = v_detail_x3f_366_;
v___y_322_ = v_data_x3f_371_;
v___y_323_ = v_sortText_x3f_370_;
v___y_324_ = v_label_365_;
v___y_325_ = v___y_374_;
v___y_326_ = v___y_373_;
v___y_327_ = v_documentation_x3f_367_;
v___y_328_ = v___x_376_;
v___y_329_ = v_kind_x3f_368_;
v___y_330_ = v_textEdit_x3f_369_;
v___y_331_ = v___x_416_;
goto v___jp_318_;
}
}
else
{
lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_423_; 
lean_dec(v_tags_x3f_372_);
lean_dec(v_data_x3f_371_);
lean_dec(v_sortText_x3f_370_);
lean_dec(v_textEdit_x3f_369_);
lean_dec(v_kind_x3f_368_);
lean_dec(v_detail_x3f_366_);
lean_dec_ref(v_label_365_);
lean_dec_ref(v_env_362_);
lean_dec_ref(v_id_261_);
v_isSharedCheck_423_ = !lean_is_exclusive(v_documentation_x3f_367_);
if (v_isSharedCheck_423_ == 0)
{
lean_object* v_unused_424_; 
v_unused_424_ = lean_ctor_get(v_documentation_x3f_367_, 0);
lean_dec(v_unused_424_);
v___x_418_ = v_documentation_x3f_367_;
v_isShared_419_ = v_isSharedCheck_423_;
goto v_resetjp_417_;
}
else
{
lean_dec(v_documentation_x3f_367_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_423_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_421_; 
if (v_isShared_419_ == 0)
{
lean_ctor_set_tag(v___x_418_, 0);
lean_ctor_set(v___x_418_, 0, v_item_364_);
v___x_421_ = v___x_418_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v_item_364_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
return v___x_421_;
}
}
}
}
v___jp_433_:
{
lean_object* v___x_435_; 
lean_inc(v_tags_x3f_432_);
lean_inc(v_data_x3f_431_);
lean_inc(v_sortText_x3f_430_);
lean_inc(v_textEdit_x3f_429_);
lean_inc(v_kind_x3f_428_);
lean_inc(v_documentation_x3f_427_);
lean_inc(v_a_434_);
lean_inc_ref(v_label_425_);
v___x_435_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_435_, 0, v_label_425_);
lean_ctor_set(v___x_435_, 1, v_a_434_);
lean_ctor_set(v___x_435_, 2, v_documentation_x3f_427_);
lean_ctor_set(v___x_435_, 3, v_kind_x3f_428_);
lean_ctor_set(v___x_435_, 4, v_textEdit_x3f_429_);
lean_ctor_set(v___x_435_, 5, v_sortText_x3f_430_);
lean_ctor_set(v___x_435_, 6, v_data_x3f_431_);
lean_ctor_set(v___x_435_, 7, v_tags_x3f_432_);
v_item_364_ = v___x_435_;
v_label_365_ = v_label_425_;
v_detail_x3f_366_ = v_a_434_;
v_documentation_x3f_367_ = v_documentation_x3f_427_;
v_kind_x3f_368_ = v_kind_x3f_428_;
v_textEdit_x3f_369_ = v_textEdit_x3f_429_;
v_sortText_x3f_370_ = v_sortText_x3f_430_;
v_data_x3f_371_ = v_data_x3f_431_;
v_tags_x3f_372_ = v_tags_x3f_432_;
v___y_373_ = v_a_264_;
v___y_374_ = v_a_265_;
goto v___jp_363_;
}
v___jp_436_:
{
lean_object* v___x_438_; 
v___x_438_ = l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg(v_val_437_, v___f_359_, v_a_262_, v_a_263_, v_a_264_, v_a_265_);
if (lean_obj_tag(v___x_438_) == 0)
{
lean_object* v_a_439_; lean_object* v___x_440_; 
v_a_439_ = lean_ctor_get(v___x_438_, 0);
lean_inc(v_a_439_);
lean_dec_ref_known(v___x_438_, 1);
v___x_440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_440_, 0, v_a_439_);
v_a_434_ = v___x_440_;
goto v___jp_433_;
}
else
{
lean_object* v_a_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_448_; 
lean_dec(v_tags_x3f_432_);
lean_dec(v_data_x3f_431_);
lean_dec(v_sortText_x3f_430_);
lean_dec(v_textEdit_x3f_429_);
lean_dec(v_kind_x3f_428_);
lean_dec(v_documentation_x3f_427_);
lean_dec_ref(v_label_425_);
lean_dec_ref(v_env_362_);
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

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
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___redArg___lam__0(lean_object* v_k_1_, lean_object* v_b_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_){
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
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1_ = stack[0].m_obj;
lean_object* v_b_2_ = stack[1].m_obj;
lean_object* v___y_3_ = stack[2].m_obj;
lean_object* v___y_4_ = stack[3].m_obj;
lean_object* v___y_5_ = stack[4].m_obj;
lean_object* v___y_6_ = stack[5].m_obj;
lean_object* v_res_9_;
v_res_9_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___redArg___lam__0(v_k_1_, v_b_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_);
stack->m_obj
 = v_res_9_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___redArg___lam__0___boxed(lean_object* v_k_10_, lean_object* v_b_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___redArg___lam__0(v_k_10_, v_b_11_, v___y_12_, v___y_13_, v___y_14_, v___y_15_);
lean_dec(v___y_15_);
lean_dec_ref(v___y_14_);
lean_dec(v___y_13_);
lean_dec_ref(v___y_12_);
return v_res_17_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___redArg(lean_object* v_name_18_, uint8_t v_bi_19_, lean_object* v_type_20_, lean_object* v_k_21_, uint8_t v_kind_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_){
_start:
{
lean_object* v___f_28_; lean_object* v___x_29_; 
v___f_28_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_28_, 0, v_k_21_);
v___x_29_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_18_, v_bi_19_, v_type_20_, v___f_28_, v_kind_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_);
if (lean_obj_tag(v___x_29_) == 0)
{
lean_object* v_a_30_; lean_object* v___x_32_; uint8_t v_isShared_33_; uint8_t v_isSharedCheck_37_; 
v_a_30_ = lean_ctor_get(v___x_29_, 0);
v_isSharedCheck_37_ = !lean_is_exclusive(v___x_29_);
if (v_isSharedCheck_37_ == 0)
{
v___x_32_ = v___x_29_;
v_isShared_33_ = v_isSharedCheck_37_;
goto v_resetjp_31_;
}
else
{
lean_inc(v_a_30_);
lean_dec(v___x_29_);
v___x_32_ = lean_box(0);
v_isShared_33_ = v_isSharedCheck_37_;
goto v_resetjp_31_;
}
v_resetjp_31_:
{
lean_object* v___x_35_; 
if (v_isShared_33_ == 0)
{
v___x_35_ = v___x_32_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_36_; 
v_reuseFailAlloc_36_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_36_, 0, v_a_30_);
v___x_35_ = v_reuseFailAlloc_36_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
return v___x_35_;
}
}
}
else
{
lean_object* v_a_38_; lean_object* v___x_40_; uint8_t v_isShared_41_; uint8_t v_isSharedCheck_45_; 
v_a_38_ = lean_ctor_get(v___x_29_, 0);
v_isSharedCheck_45_ = !lean_is_exclusive(v___x_29_);
if (v_isSharedCheck_45_ == 0)
{
v___x_40_ = v___x_29_;
v_isShared_41_ = v_isSharedCheck_45_;
goto v_resetjp_39_;
}
else
{
lean_inc(v_a_38_);
lean_dec(v___x_29_);
v___x_40_ = lean_box(0);
v_isShared_41_ = v_isSharedCheck_45_;
goto v_resetjp_39_;
}
v_resetjp_39_:
{
lean_object* v___x_43_; 
if (v_isShared_41_ == 0)
{
v___x_43_ = v___x_40_;
goto v_reusejp_42_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v_a_38_);
v___x_43_ = v_reuseFailAlloc_44_;
goto v_reusejp_42_;
}
v_reusejp_42_:
{
return v___x_43_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_18_ = stack[0].m_obj;
uint8_t v_bi_19_ = stack[1].m_num;
lean_object* v_type_20_ = stack[2].m_obj;
lean_object* v_k_21_ = stack[3].m_obj;
uint8_t v_kind_22_ = stack[4].m_num;
lean_object* v___y_23_ = stack[5].m_obj;
lean_object* v___y_24_ = stack[6].m_obj;
lean_object* v___y_25_ = stack[7].m_obj;
lean_object* v___y_26_ = stack[8].m_obj;
lean_object* v_res_46_;
v_res_46_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___redArg(v_name_18_, v_bi_19_, v_type_20_, v_k_21_, v_kind_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_);
stack->m_obj
 = v_res_46_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___redArg___boxed(lean_object* v_name_47_, lean_object* v_bi_48_, lean_object* v_type_49_, lean_object* v_k_50_, lean_object* v_kind_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_){
_start:
{
uint8_t v_bi_boxed_57_; uint8_t v_kind_boxed_58_; lean_object* v_res_59_; 
v_bi_boxed_57_ = lean_unbox(v_bi_48_);
v_kind_boxed_58_ = lean_unbox(v_kind_51_);
v_res_59_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___redArg(v_name_47_, v_bi_boxed_57_, v_type_49_, v_k_50_, v_kind_boxed_58_, v___y_52_, v___y_53_, v___y_54_, v___y_55_);
lean_dec(v___y_55_);
lean_dec_ref(v___y_54_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
return v_res_59_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0(lean_object* v_00_u03b1_60_, lean_object* v_name_61_, uint8_t v_bi_62_, lean_object* v_type_63_, lean_object* v_k_64_, uint8_t v_kind_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___redArg(v_name_61_, v_bi_62_, v_type_63_, v_k_64_, v_kind_65_, v___y_66_, v___y_67_, v___y_68_, v___y_69_);
return v___x_71_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_61_ = stack[1].m_obj;
uint8_t v_bi_62_ = stack[2].m_num;
lean_object* v_type_63_ = stack[3].m_obj;
lean_object* v_k_64_ = stack[4].m_obj;
uint8_t v_kind_65_ = stack[5].m_num;
lean_object* v___y_66_ = stack[6].m_obj;
lean_object* v___y_67_ = stack[7].m_obj;
lean_object* v___y_68_ = stack[8].m_obj;
lean_object* v___y_69_ = stack[9].m_obj;
lean_object* v_res_72_;
v_res_72_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0(lean_box(0), v_name_61_, v_bi_62_, v_type_63_, v_k_64_, v_kind_65_, v___y_66_, v___y_67_, v___y_68_, v___y_69_);
stack->m_obj
 = v_res_72_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___boxed(lean_object* v_00_u03b1_73_, lean_object* v_name_74_, lean_object* v_bi_75_, lean_object* v_type_76_, lean_object* v_k_77_, lean_object* v_kind_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_){
_start:
{
uint8_t v_bi_boxed_84_; uint8_t v_kind_boxed_85_; lean_object* v_res_86_; 
v_bi_boxed_84_ = lean_unbox(v_bi_75_);
v_kind_boxed_85_ = lean_unbox(v_kind_78_);
v_res_86_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0(v_00_u03b1_73_, v_name_74_, v_bi_boxed_84_, v_type_76_, v_k_77_, v_kind_boxed_85_, v___y_79_, v___y_80_, v___y_81_, v___y_82_);
lean_dec(v___y_82_);
lean_dec_ref(v___y_81_);
lean_dec(v___y_80_);
lean_dec_ref(v___y_79_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg___lam__0___boxed(lean_object* v_body_87_, lean_object* v_k_88_, lean_object* v_arg_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg___lam__0(v_body_87_, v_k_88_, v_arg_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_);
lean_dec(v___y_93_);
lean_dec_ref(v___y_92_);
lean_dec(v___y_91_);
lean_dec_ref(v___y_90_);
lean_dec_ref(v_arg_89_);
lean_dec_ref(v_body_87_);
return v_res_95_;
}
}
lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg(lean_object* v_e_96_, lean_object* v_k_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_){
_start:
{
if (lean_obj_tag(v_e_96_) == 7)
{
lean_object* v_binderName_103_; lean_object* v_binderType_104_; lean_object* v_body_105_; uint8_t v_binderInfo_106_; uint8_t v___x_107_; uint8_t v___x_108_; 
v_binderName_103_ = lean_ctor_get(v_e_96_, 0);
v_binderType_104_ = lean_ctor_get(v_e_96_, 1);
v_body_105_ = lean_ctor_get(v_e_96_, 2);
v_binderInfo_106_ = lean_ctor_get_uint8(v_e_96_, sizeof(void*)*3 + 8);
v___x_107_ = 1;
v___x_108_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_106_, v___x_107_);
if (v___x_108_ == 0)
{
lean_object* v___x_109_; 
lean_inc(v_a_101_);
lean_inc_ref(v_a_100_);
lean_inc(v_a_99_);
lean_inc_ref(v_a_98_);
v___x_109_ = lean_apply_6(v_k_97_, v_e_96_, v_a_98_, v_a_99_, v_a_100_, v_a_101_, lean_box(0));
return v___x_109_;
}
else
{
lean_object* v___f_110_; uint8_t v___x_111_; lean_object* v___x_112_; 
lean_inc_ref(v_body_105_);
lean_inc_ref(v_binderType_104_);
lean_inc(v_binderName_103_);
lean_dec_ref_known(v_e_96_, 3);
v___f_110_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_110_, 0, v_body_105_);
lean_closure_set(v___f_110_, 1, v_k_97_);
v___x_111_ = 0;
v___x_112_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___redArg(v_binderName_103_, v_binderInfo_106_, v_binderType_104_, v___f_110_, v___x_111_, v_a_98_, v_a_99_, v_a_100_, v_a_101_);
return v___x_112_;
}
}
else
{
lean_object* v___x_113_; 
lean_inc(v_a_101_);
lean_inc_ref(v_a_100_);
lean_inc(v_a_99_);
lean_inc_ref(v_a_98_);
v___x_113_ = lean_apply_6(v_k_97_, v_e_96_, v_a_98_, v_a_99_, v_a_100_, v_a_101_, lean_box(0));
return v___x_113_;
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_96_ = stack[0].m_obj;
lean_object* v_k_97_ = stack[1].m_obj;
lean_object* v_a_98_ = stack[2].m_obj;
lean_object* v_a_99_ = stack[3].m_obj;
lean_object* v_a_100_ = stack[4].m_obj;
lean_object* v_a_101_ = stack[5].m_obj;
lean_object* v_res_114_;
v_res_114_ = l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg(v_e_96_, v_k_97_, v_a_98_, v_a_99_, v_a_100_, v_a_101_);
stack->m_obj
 = v_res_114_;
}
lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg___lam__0(lean_object* v_body_115_, lean_object* v_k_116_, lean_object* v_arg_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_123_ = lean_expr_instantiate1(v_body_115_, v_arg_117_);
v___x_124_ = l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg(v___x_123_, v_k_116_, v___y_118_, v___y_119_, v___y_120_, v___y_121_);
return v___x_124_;
}
}
LEAN_EXPORT void l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_body_115_ = stack[0].m_obj;
lean_object* v_k_116_ = stack[1].m_obj;
lean_object* v_arg_117_ = stack[2].m_obj;
lean_object* v___y_118_ = stack[3].m_obj;
lean_object* v___y_119_ = stack[4].m_obj;
lean_object* v___y_120_ = stack[5].m_obj;
lean_object* v___y_121_ = stack[6].m_obj;
lean_object* v_res_125_;
v_res_125_ = l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg___lam__0(v_body_115_, v_k_116_, v_arg_117_, v___y_118_, v___y_119_, v___y_120_, v___y_121_);
stack->m_obj
 = v_res_125_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg___boxed(lean_object* v_e_126_, lean_object* v_k_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg(v_e_126_, v_k_127_, v_a_128_, v_a_129_, v_a_130_, v_a_131_);
lean_dec(v_a_131_);
lean_dec_ref(v_a_130_);
lean_dec(v_a_129_);
lean_dec_ref(v_a_128_);
return v_res_133_;
}
}
lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix(lean_object* v_00_u03b1_134_, lean_object* v_e_135_, lean_object* v_k_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_){
_start:
{
lean_object* v___x_142_; 
v___x_142_ = l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg(v_e_135_, v_k_136_, v_a_137_, v_a_138_, v_a_139_, v_a_140_);
return v___x_142_;
}
}
LEAN_EXPORT void l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_135_ = stack[1].m_obj;
lean_object* v_k_136_ = stack[2].m_obj;
lean_object* v_a_137_ = stack[3].m_obj;
lean_object* v_a_138_ = stack[4].m_obj;
lean_object* v_a_139_ = stack[5].m_obj;
lean_object* v_a_140_ = stack[6].m_obj;
lean_object* v_res_143_;
v_res_143_ = l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix(lean_box(0), v_e_135_, v_k_136_, v_a_137_, v_a_138_, v_a_139_, v_a_140_);
stack->m_obj
 = v_res_143_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___boxed(lean_object* v_00_u03b1_144_, lean_object* v_e_145_, lean_object* v_k_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix(v_00_u03b1_144_, v_e_145_, v_k_146_, v_a_147_, v_a_148_, v_a_149_, v_a_150_);
lean_dec(v_a_150_);
lean_dec_ref(v_a_149_);
lean_dec(v_a_148_);
lean_dec_ref(v_a_147_);
return v_res_152_;
}
}
lean_object* l_Lean_findMarkdownDocString_x3f___at___00Lean_Lsp_CompletionItem_resolve_spec__0___redArg(lean_object* v_declName_153_, uint8_t v_includeBuiltin_154_, lean_object* v___y_155_, lean_object* v___y_156_){
_start:
{
lean_object* v___x_158_; lean_object* v_toCold_159_; lean_object* v_env_160_; lean_object* v_ref_161_; lean_object* v_currNamespace_162_; lean_object* v_openDecls_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_158_ = lean_st_ref_get(v___y_156_);
v_toCold_159_ = lean_ctor_get(v___y_155_, 0);
v_env_160_ = lean_ctor_get(v___x_158_, 0);
lean_inc_ref(v_env_160_);
lean_dec(v___x_158_);
v_ref_161_ = lean_ctor_get(v___y_155_, 2);
v_currNamespace_162_ = lean_ctor_get(v_toCold_159_, 4);
v_openDecls_163_ = lean_ctor_get(v_toCold_159_, 5);
v___x_164_ = l_Lean_Options_empty;
lean_inc(v_openDecls_163_);
lean_inc(v_currNamespace_162_);
v___x_165_ = l_Lean_findDocString_x3f(v_env_160_, v_declName_153_, v_includeBuiltin_154_, v___x_164_, v_currNamespace_162_, v_openDecls_163_);
if (lean_obj_tag(v___x_165_) == 0)
{
lean_object* v_a_166_; lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_173_; 
v_a_166_ = lean_ctor_get(v___x_165_, 0);
v_isSharedCheck_173_ = !lean_is_exclusive(v___x_165_);
if (v_isSharedCheck_173_ == 0)
{
v___x_168_ = v___x_165_;
v_isShared_169_ = v_isSharedCheck_173_;
goto v_resetjp_167_;
}
else
{
lean_inc(v_a_166_);
lean_dec(v___x_165_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_173_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
lean_object* v___x_171_; 
if (v_isShared_169_ == 0)
{
v___x_171_ = v___x_168_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v_a_166_);
v___x_171_ = v_reuseFailAlloc_172_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
return v___x_171_;
}
}
}
else
{
lean_object* v_a_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_185_; 
v_a_174_ = lean_ctor_get(v___x_165_, 0);
v_isSharedCheck_185_ = !lean_is_exclusive(v___x_165_);
if (v_isSharedCheck_185_ == 0)
{
v___x_176_ = v___x_165_;
v_isShared_177_ = v_isSharedCheck_185_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_a_174_);
lean_dec(v___x_165_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_185_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_183_; 
v___x_178_ = lean_io_error_to_string(v_a_174_);
v___x_179_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_179_, 0, v___x_178_);
v___x_180_ = l_Lean_MessageData_ofFormat(v___x_179_);
lean_inc(v_ref_161_);
v___x_181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_181_, 0, v_ref_161_);
lean_ctor_set(v___x_181_, 1, v___x_180_);
if (v_isShared_177_ == 0)
{
lean_ctor_set(v___x_176_, 0, v___x_181_);
v___x_183_ = v___x_176_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v___x_181_);
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
LEAN_EXPORT void l_Lean_findMarkdownDocString_x3f___at___00Lean_Lsp_CompletionItem_resolve_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_153_ = stack[0].m_obj;
uint8_t v_includeBuiltin_154_ = stack[1].m_num;
lean_object* v___y_155_ = stack[2].m_obj;
lean_object* v___y_156_ = stack[3].m_obj;
lean_object* v_res_186_;
v_res_186_ = l_Lean_findMarkdownDocString_x3f___at___00Lean_Lsp_CompletionItem_resolve_spec__0___redArg(v_declName_153_, v_includeBuiltin_154_, v___y_155_, v___y_156_);
stack->m_obj
 = v_res_186_;
}
LEAN_EXPORT lean_object* l_Lean_findMarkdownDocString_x3f___at___00Lean_Lsp_CompletionItem_resolve_spec__0___redArg___boxed(lean_object* v_declName_187_, lean_object* v_includeBuiltin_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_){
_start:
{
uint8_t v_includeBuiltin_boxed_192_; lean_object* v_res_193_; 
v_includeBuiltin_boxed_192_ = lean_unbox(v_includeBuiltin_188_);
v_res_193_ = l_Lean_findMarkdownDocString_x3f___at___00Lean_Lsp_CompletionItem_resolve_spec__0___redArg(v_declName_187_, v_includeBuiltin_boxed_192_, v___y_189_, v___y_190_);
lean_dec(v___y_190_);
lean_dec_ref(v___y_189_);
return v_res_193_;
}
}
lean_object* l_Lean_findMarkdownDocString_x3f___at___00Lean_Lsp_CompletionItem_resolve_spec__0(lean_object* v_declName_194_, uint8_t v_includeBuiltin_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = l_Lean_findMarkdownDocString_x3f___at___00Lean_Lsp_CompletionItem_resolve_spec__0___redArg(v_declName_194_, v_includeBuiltin_195_, v___y_198_, v___y_199_);
return v___x_201_;
}
}
LEAN_EXPORT void l_Lean_findMarkdownDocString_x3f___at___00Lean_Lsp_CompletionItem_resolve_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_194_ = stack[0].m_obj;
uint8_t v_includeBuiltin_195_ = stack[1].m_num;
lean_object* v___y_196_ = stack[2].m_obj;
lean_object* v___y_197_ = stack[3].m_obj;
lean_object* v___y_198_ = stack[4].m_obj;
lean_object* v___y_199_ = stack[5].m_obj;
lean_object* v_res_202_;
v_res_202_ = l_Lean_findMarkdownDocString_x3f___at___00Lean_Lsp_CompletionItem_resolve_spec__0(v_declName_194_, v_includeBuiltin_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_);
stack->m_obj
 = v_res_202_;
}
LEAN_EXPORT lean_object* l_Lean_findMarkdownDocString_x3f___at___00Lean_Lsp_CompletionItem_resolve_spec__0___boxed(lean_object* v_declName_203_, lean_object* v_includeBuiltin_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_){
_start:
{
uint8_t v_includeBuiltin_boxed_210_; lean_object* v_res_211_; 
v_includeBuiltin_boxed_210_ = lean_unbox(v_includeBuiltin_204_);
v_res_211_ = l_Lean_findMarkdownDocString_x3f___at___00Lean_Lsp_CompletionItem_resolve_spec__0(v_declName_203_, v_includeBuiltin_boxed_210_, v___y_205_, v___y_206_, v___y_207_, v___y_208_);
lean_dec(v___y_208_);
lean_dec_ref(v___y_207_);
lean_dec(v___y_206_);
lean_dec_ref(v___y_205_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___lam__0(lean_object* v_docValue_212_){
_start:
{
uint8_t v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_213_ = 1;
v___x_214_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_214_, 0, v_docValue_212_);
lean_ctor_set_uint8(v___x_214_, sizeof(void*)*1, v___x_213_);
v___x_215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_215_, 0, v___x_214_);
return v___x_215_;
}
}
lean_object* l_Lean_Lsp_CompletionItem_resolve___lam__1(lean_object* v_typeWithoutImplicits_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_){
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
LEAN_EXPORT void l_Lean_Lsp_CompletionItem_resolve___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_typeWithoutImplicits_216_ = stack[0].m_obj;
lean_object* v___y_217_ = stack[1].m_obj;
lean_object* v___y_218_ = stack[2].m_obj;
lean_object* v___y_219_ = stack[3].m_obj;
lean_object* v___y_220_ = stack[4].m_obj;
lean_object* v_res_242_;
v_res_242_ = l_Lean_Lsp_CompletionItem_resolve___lam__1(v_typeWithoutImplicits_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_);
stack->m_obj
 = v_res_242_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___lam__1___boxed(lean_object* v_typeWithoutImplicits_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l_Lean_Lsp_CompletionItem_resolve___lam__1(v_typeWithoutImplicits_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_);
lean_dec(v___y_247_);
lean_dec_ref(v___y_246_);
lean_dec(v___y_245_);
lean_dec_ref(v___y_244_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___lam__2(lean_object* v_documentation_x3f_250_, lean_object* v___f_251_, lean_object* v_docStringPrefix_252_){
_start:
{
if (lean_obj_tag(v_docStringPrefix_252_) == 0)
{
lean_dec_ref(v___f_251_);
lean_inc(v_documentation_x3f_250_);
return v_documentation_x3f_250_;
}
else
{
lean_object* v_val_253_; lean_object* v___x_254_; 
v_val_253_ = lean_ctor_get(v_docStringPrefix_252_, 0);
lean_inc(v_val_253_);
lean_dec_ref_known(v_docStringPrefix_252_, 1);
v___x_254_ = lean_apply_1(v___f_251_, v_val_253_);
return v___x_254_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___lam__2___boxed(lean_object* v_documentation_x3f_255_, lean_object* v___f_256_, lean_object* v_docStringPrefix_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Lean_Lsp_CompletionItem_resolve___lam__2(v_documentation_x3f_255_, v___f_256_, v_docStringPrefix_257_);
lean_dec(v_documentation_x3f_255_);
return v_res_258_;
}
}
lean_object* l_Lean_Lsp_CompletionItem_resolve(lean_object* v_item_269_, lean_object* v_id_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_){
_start:
{
lean_object* v___y_277_; lean_object* v___y_278_; lean_object* v___y_279_; lean_object* v___y_280_; lean_object* v___y_281_; lean_object* v___y_282_; lean_object* v___y_283_; lean_object* v___y_284_; lean_object* v___f_287_; lean_object* v___y_289_; lean_object* v___y_290_; lean_object* v___y_291_; lean_object* v___y_292_; lean_object* v___y_293_; lean_object* v___y_294_; lean_object* v___y_295_; lean_object* v___y_296_; lean_object* v___y_297_; lean_object* v___y_303_; lean_object* v___y_304_; lean_object* v___y_305_; lean_object* v___y_306_; lean_object* v___y_307_; lean_object* v___y_308_; lean_object* v___y_309_; lean_object* v___y_310_; lean_object* v___y_311_; lean_object* v___y_312_; lean_object* v_docString_x3f_313_; lean_object* v___y_328_; lean_object* v___y_329_; lean_object* v___y_330_; uint8_t v___y_331_; lean_object* v___y_332_; lean_object* v___y_333_; lean_object* v___y_334_; lean_object* v___y_335_; lean_object* v___y_336_; lean_object* v___y_337_; lean_object* v___y_338_; lean_object* v___y_339_; lean_object* v___y_340_; lean_object* v___y_354_; lean_object* v___y_355_; lean_object* v___y_356_; uint8_t v___y_357_; lean_object* v___y_358_; lean_object* v___y_359_; lean_object* v___y_360_; lean_object* v___y_361_; lean_object* v___y_362_; lean_object* v___y_363_; lean_object* v___y_364_; lean_object* v___y_365_; lean_object* v___y_366_; lean_object* v___f_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v_env_371_; lean_object* v_item_373_; lean_object* v_label_374_; lean_object* v_detail_x3f_375_; lean_object* v_documentation_x3f_376_; lean_object* v_kind_x3f_377_; lean_object* v_textEdit_x3f_378_; lean_object* v_sortText_x3f_379_; lean_object* v_data_x3f_380_; lean_object* v_tags_x3f_381_; lean_object* v___y_382_; lean_object* v___y_383_; lean_object* v_label_434_; lean_object* v_detail_x3f_435_; lean_object* v_documentation_x3f_436_; lean_object* v_kind_x3f_437_; lean_object* v_textEdit_x3f_438_; lean_object* v_sortText_x3f_439_; lean_object* v_data_x3f_440_; lean_object* v_tags_x3f_441_; lean_object* v_a_443_; lean_object* v_val_446_; 
v___f_287_ = ((lean_object*)(l_Lean_Lsp_CompletionItem_resolve___closed__0));
v___f_368_ = ((lean_object*)(l_Lean_Lsp_CompletionItem_resolve___closed__5));
v___x_369_ = l_Lean_Linter_instInhabitedDeprecationEntry_default;
v___x_370_ = lean_st_ref_get(v_a_274_);
v_env_371_ = lean_ctor_get(v___x_370_, 0);
lean_inc_ref(v_env_371_);
lean_dec(v___x_370_);
v_label_434_ = lean_ctor_get(v_item_269_, 0);
lean_inc_ref(v_label_434_);
v_detail_x3f_435_ = lean_ctor_get(v_item_269_, 1);
lean_inc(v_detail_x3f_435_);
v_documentation_x3f_436_ = lean_ctor_get(v_item_269_, 2);
lean_inc(v_documentation_x3f_436_);
v_kind_x3f_437_ = lean_ctor_get(v_item_269_, 3);
lean_inc(v_kind_x3f_437_);
v_textEdit_x3f_438_ = lean_ctor_get(v_item_269_, 4);
lean_inc(v_textEdit_x3f_438_);
v_sortText_x3f_439_ = lean_ctor_get(v_item_269_, 5);
lean_inc(v_sortText_x3f_439_);
v_data_x3f_440_ = lean_ctor_get(v_item_269_, 6);
lean_inc(v_data_x3f_440_);
v_tags_x3f_441_ = lean_ctor_get(v_item_269_, 7);
lean_inc(v_tags_x3f_441_);
if (lean_obj_tag(v_detail_x3f_435_) == 0)
{
lean_dec_ref(v_item_269_);
if (lean_obj_tag(v_id_270_) == 0)
{
lean_object* v_declName_458_; uint8_t v___x_459_; lean_object* v___x_460_; 
v_declName_458_ = lean_ctor_get(v_id_270_, 0);
v___x_459_ = 0;
lean_inc(v_declName_458_);
lean_inc_ref(v_env_371_);
v___x_460_ = l_Lean_Environment_find_x3f(v_env_371_, v_declName_458_, v___x_459_);
if (lean_obj_tag(v___x_460_) == 0)
{
v_a_443_ = v_detail_x3f_435_;
goto v___jp_442_;
}
else
{
lean_object* v_val_461_; lean_object* v___x_462_; 
v_val_461_ = lean_ctor_get(v___x_460_, 0);
lean_inc(v_val_461_);
lean_dec_ref_known(v___x_460_, 1);
v___x_462_ = l_Lean_ConstantInfo_type(v_val_461_);
lean_dec(v_val_461_);
v_val_446_ = v___x_462_;
goto v___jp_445_;
}
}
else
{
lean_object* v_id_463_; lean_object* v_lctx_464_; lean_object* v___x_465_; 
v_id_463_ = lean_ctor_get(v_id_270_, 0);
v_lctx_464_ = lean_ctor_get(v_a_271_, 2);
lean_inc(v_id_463_);
lean_inc_ref(v_lctx_464_);
v___x_465_ = lean_local_ctx_find(v_lctx_464_, v_id_463_);
if (lean_obj_tag(v___x_465_) == 0)
{
v_a_443_ = v_detail_x3f_435_;
goto v___jp_442_;
}
else
{
lean_object* v_val_466_; lean_object* v___x_467_; 
v_val_466_ = lean_ctor_get(v___x_465_, 0);
lean_inc(v_val_466_);
lean_dec_ref_known(v___x_465_, 1);
v___x_467_ = l_Lean_LocalDecl_type(v_val_466_);
lean_dec(v_val_466_);
v_val_446_ = v___x_467_;
goto v___jp_445_;
}
}
}
else
{
v_item_373_ = v_item_269_;
v_label_374_ = v_label_434_;
v_detail_x3f_375_ = v_detail_x3f_435_;
v_documentation_x3f_376_ = v_documentation_x3f_436_;
v_kind_x3f_377_ = v_kind_x3f_437_;
v_textEdit_x3f_378_ = v_textEdit_x3f_438_;
v_sortText_x3f_379_ = v_sortText_x3f_439_;
v_data_x3f_380_ = v_data_x3f_440_;
v_tags_x3f_381_ = v_tags_x3f_441_;
v___y_382_ = v_a_273_;
v___y_383_ = v_a_274_;
goto v___jp_372_;
}
v___jp_276_:
{
lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_285_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_285_, 0, v___y_282_);
lean_ctor_set(v___x_285_, 1, v___y_280_);
lean_ctor_set(v___x_285_, 2, v___y_284_);
lean_ctor_set(v___x_285_, 3, v___y_279_);
lean_ctor_set(v___x_285_, 4, v___y_281_);
lean_ctor_set(v___x_285_, 5, v___y_283_);
lean_ctor_set(v___x_285_, 6, v___y_278_);
lean_ctor_set(v___x_285_, 7, v___y_277_);
v___x_286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_286_, 0, v___x_285_);
return v___x_286_;
}
v___jp_288_:
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_298_ = ((lean_object*)(l_Lean_Lsp_CompletionItem_resolve___closed__1));
v___x_299_ = lean_string_append(v___y_297_, v___x_298_);
v___x_300_ = lean_string_append(v___x_299_, v___y_293_);
lean_dec_ref(v___y_293_);
v___x_301_ = l_Lean_Lsp_CompletionItem_resolve___lam__0(v___x_300_);
v___y_277_ = v___y_289_;
v___y_278_ = v___y_291_;
v___y_279_ = v___y_290_;
v___y_280_ = v___y_292_;
v___y_281_ = v___y_294_;
v___y_282_ = v___y_295_;
v___y_283_ = v___y_296_;
v___y_284_ = v___x_301_;
goto v___jp_276_;
}
v___jp_302_:
{
if (lean_obj_tag(v___y_306_) == 0)
{
if (lean_obj_tag(v_docString_x3f_313_) == 0)
{
lean_dec_ref(v___y_303_);
v___y_277_ = v___y_304_;
v___y_278_ = v___y_308_;
v___y_279_ = v___y_307_;
v___y_280_ = v___y_309_;
v___y_281_ = v___y_310_;
v___y_282_ = v___y_311_;
v___y_283_ = v___y_312_;
v___y_284_ = v___y_305_;
goto v___jp_276_;
}
else
{
lean_object* v___x_314_; 
lean_dec(v___y_305_);
v___x_314_ = lean_apply_1(v___y_303_, v_docString_x3f_313_);
v___y_277_ = v___y_304_;
v___y_278_ = v___y_308_;
v___y_279_ = v___y_307_;
v___y_280_ = v___y_309_;
v___y_281_ = v___y_310_;
v___y_282_ = v___y_311_;
v___y_283_ = v___y_312_;
v___y_284_ = v___x_314_;
goto v___jp_276_;
}
}
else
{
lean_dec(v___y_305_);
if (lean_obj_tag(v_docString_x3f_313_) == 0)
{
lean_object* v_val_315_; lean_object* v___x_316_; 
v_val_315_ = lean_ctor_get(v___y_306_, 0);
lean_inc(v_val_315_);
lean_dec_ref_known(v___y_306_, 1);
v___x_316_ = lean_apply_1(v___y_303_, v_val_315_);
v___y_277_ = v___y_304_;
v___y_278_ = v___y_308_;
v___y_279_ = v___y_307_;
v___y_280_ = v___y_309_;
v___y_281_ = v___y_310_;
v___y_282_ = v___y_311_;
v___y_283_ = v___y_312_;
v___y_284_ = v___x_316_;
goto v___jp_276_;
}
else
{
lean_object* v_val_317_; 
lean_dec_ref(v___y_303_);
v_val_317_ = lean_ctor_get(v___y_306_, 0);
lean_inc(v_val_317_);
lean_dec_ref_known(v___y_306_, 1);
if (lean_obj_tag(v_val_317_) == 0)
{
lean_object* v_val_318_; lean_object* v___x_319_; 
v_val_318_ = lean_ctor_get(v_docString_x3f_313_, 0);
lean_inc(v_val_318_);
lean_dec_ref_known(v_docString_x3f_313_, 1);
v___x_319_ = ((lean_object*)(l_Lean_Lsp_CompletionItem_resolve___closed__2));
v___y_289_ = v___y_304_;
v___y_290_ = v___y_307_;
v___y_291_ = v___y_308_;
v___y_292_ = v___y_309_;
v___y_293_ = v_val_318_;
v___y_294_ = v___y_310_;
v___y_295_ = v___y_311_;
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
v___y_289_ = v___y_304_;
v___y_290_ = v___y_307_;
v___y_291_ = v___y_308_;
v___y_292_ = v___y_309_;
v___y_293_ = v_val_320_;
v___y_294_ = v___y_310_;
v___y_295_ = v___y_311_;
v___y_296_ = v___y_312_;
v___y_297_ = v___x_326_;
goto v___jp_288_;
}
}
}
}
v___jp_327_:
{
if (lean_obj_tag(v_id_270_) == 0)
{
lean_object* v_declName_341_; lean_object* v___x_342_; 
v_declName_341_ = lean_ctor_get(v_id_270_, 0);
lean_inc(v_declName_341_);
lean_dec_ref_known(v_id_270_, 1);
v___x_342_ = l_Lean_findMarkdownDocString_x3f___at___00Lean_Lsp_CompletionItem_resolve_spec__0___redArg(v_declName_341_, v___y_331_, v___y_339_, v___y_338_);
if (lean_obj_tag(v___x_342_) == 0)
{
lean_object* v_a_343_; 
v_a_343_ = lean_ctor_get(v___x_342_, 0);
lean_inc(v_a_343_);
lean_dec_ref_known(v___x_342_, 1);
v___y_303_ = v___y_334_;
v___y_304_ = v___y_328_;
v___y_305_ = v___y_335_;
v___y_306_ = v___y_340_;
v___y_307_ = v___y_329_;
v___y_308_ = v___y_330_;
v___y_309_ = v___y_336_;
v___y_310_ = v___y_337_;
v___y_311_ = v___y_332_;
v___y_312_ = v___y_333_;
v_docString_x3f_313_ = v_a_343_;
goto v___jp_302_;
}
else
{
lean_object* v_a_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_351_; 
lean_dec(v___y_340_);
lean_dec(v___y_337_);
lean_dec(v___y_336_);
lean_dec(v___y_335_);
lean_dec_ref(v___y_334_);
lean_dec(v___y_333_);
lean_dec_ref(v___y_332_);
lean_dec(v___y_330_);
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
lean_dec_ref(v_id_270_);
v___x_352_ = lean_box(0);
v___y_303_ = v___y_334_;
v___y_304_ = v___y_328_;
v___y_305_ = v___y_335_;
v___y_306_ = v___y_340_;
v___y_307_ = v___y_329_;
v___y_308_ = v___y_330_;
v___y_309_ = v___y_336_;
v___y_310_ = v___y_337_;
v___y_311_ = v___y_332_;
v___y_312_ = v___y_333_;
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
v___jp_372_:
{
if (lean_obj_tag(v_documentation_x3f_376_) == 0)
{
lean_object* v___f_384_; uint8_t v___x_385_; 
lean_dec_ref(v_item_373_);
v___f_384_ = lean_alloc_closure((void*)(l_Lean_Lsp_CompletionItem_resolve___lam__2___boxed), 3, 2);
lean_closure_set(v___f_384_, 0, v_documentation_x3f_376_);
lean_closure_set(v___f_384_, 1, v___f_287_);
v___x_385_ = 1;
if (lean_obj_tag(v_id_270_) == 0)
{
lean_object* v_declName_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v_declName_386_ = lean_ctor_get(v_id_270_, 0);
v___x_387_ = l_Lean_Linter_deprecatedAttr;
lean_inc(v_declName_386_);
v___x_388_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_369_, v___x_387_, v_env_371_, v_declName_386_);
if (lean_obj_tag(v___x_388_) == 1)
{
lean_object* v_val_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_423_; 
v_val_389_ = lean_ctor_get(v___x_388_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v___x_388_);
if (v_isSharedCheck_423_ == 0)
{
v___x_391_ = v___x_388_;
v_isShared_392_ = v_isSharedCheck_423_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_val_389_);
lean_dec(v___x_388_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_423_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v_text_x3f_393_; 
v_text_x3f_393_ = lean_ctor_get(v_val_389_, 1);
if (lean_obj_tag(v_text_x3f_393_) == 1)
{
lean_object* v___x_395_; 
lean_inc_ref(v_text_x3f_393_);
lean_dec(v_val_389_);
if (v_isShared_392_ == 0)
{
lean_ctor_set(v___x_391_, 0, v_text_x3f_393_);
v___x_395_ = v___x_391_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_text_x3f_393_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
v___y_328_ = v_tags_x3f_381_;
v___y_329_ = v_kind_x3f_377_;
v___y_330_ = v_data_x3f_380_;
v___y_331_ = v___x_385_;
v___y_332_ = v_label_374_;
v___y_333_ = v_sortText_x3f_379_;
v___y_334_ = v___f_384_;
v___y_335_ = v_documentation_x3f_376_;
v___y_336_ = v_detail_x3f_375_;
v___y_337_ = v_textEdit_x3f_378_;
v___y_338_ = v___y_383_;
v___y_339_ = v___y_382_;
v___y_340_ = v___x_395_;
goto v___jp_327_;
}
}
else
{
lean_object* v_newName_x3f_397_; 
v_newName_x3f_397_ = lean_ctor_get(v_val_389_, 0);
lean_inc(v_newName_x3f_397_);
lean_dec(v_val_389_);
if (lean_obj_tag(v_newName_x3f_397_) == 1)
{
lean_object* v_val_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_414_; 
lean_del_object(v___x_391_);
v_val_398_ = lean_ctor_get(v_newName_x3f_397_, 0);
v_isSharedCheck_414_ = !lean_is_exclusive(v_newName_x3f_397_);
if (v_isSharedCheck_414_ == 0)
{
v___x_400_ = v_newName_x3f_397_;
v_isShared_401_ = v_isSharedCheck_414_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_val_398_);
lean_dec(v_newName_x3f_397_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_414_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_412_; 
v___x_402_ = ((lean_object*)(l_Lean_Lsp_CompletionItem_resolve___closed__6));
lean_inc(v_declName_386_);
v___x_403_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_386_, v___x_385_);
v___x_404_ = lean_string_append(v___x_402_, v___x_403_);
lean_dec_ref(v___x_403_);
v___x_405_ = ((lean_object*)(l_Lean_Lsp_CompletionItem_resolve___closed__7));
v___x_406_ = lean_string_append(v___x_404_, v___x_405_);
v___x_407_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_398_, v___x_385_);
v___x_408_ = lean_string_append(v___x_406_, v___x_407_);
lean_dec_ref(v___x_407_);
v___x_409_ = ((lean_object*)(l_Lean_Lsp_CompletionItem_resolve___closed__8));
v___x_410_ = lean_string_append(v___x_408_, v___x_409_);
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 0, v___x_410_);
v___x_412_ = v___x_400_;
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
v___y_354_ = v_tags_x3f_381_;
v___y_355_ = v_kind_x3f_377_;
v___y_356_ = v_data_x3f_380_;
v___y_357_ = v___x_385_;
v___y_358_ = v_label_374_;
v___y_359_ = v_sortText_x3f_379_;
v___y_360_ = v___f_384_;
v___y_361_ = v_documentation_x3f_376_;
v___y_362_ = v_detail_x3f_375_;
v___y_363_ = v_textEdit_x3f_378_;
v___y_364_ = v___y_383_;
v___y_365_ = v___y_382_;
v___y_366_ = v___x_412_;
goto v___jp_353_;
}
}
}
else
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_421_; 
lean_dec(v_newName_x3f_397_);
v___x_415_ = ((lean_object*)(l_Lean_Lsp_CompletionItem_resolve___closed__6));
lean_inc(v_declName_386_);
v___x_416_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_386_, v___x_385_);
v___x_417_ = lean_string_append(v___x_415_, v___x_416_);
lean_dec_ref(v___x_416_);
v___x_418_ = ((lean_object*)(l_Lean_Lsp_CompletionItem_resolve___closed__9));
v___x_419_ = lean_string_append(v___x_417_, v___x_418_);
if (v_isShared_392_ == 0)
{
lean_ctor_set(v___x_391_, 0, v___x_419_);
v___x_421_ = v___x_391_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v___x_419_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
v___y_354_ = v_tags_x3f_381_;
v___y_355_ = v_kind_x3f_377_;
v___y_356_ = v_data_x3f_380_;
v___y_357_ = v___x_385_;
v___y_358_ = v_label_374_;
v___y_359_ = v_sortText_x3f_379_;
v___y_360_ = v___f_384_;
v___y_361_ = v_documentation_x3f_376_;
v___y_362_ = v_detail_x3f_375_;
v___y_363_ = v_textEdit_x3f_378_;
v___y_364_ = v___y_383_;
v___y_365_ = v___y_382_;
v___y_366_ = v___x_421_;
goto v___jp_353_;
}
}
}
}
}
else
{
lean_object* v___x_424_; 
lean_dec(v___x_388_);
v___x_424_ = lean_box(0);
v___y_328_ = v_tags_x3f_381_;
v___y_329_ = v_kind_x3f_377_;
v___y_330_ = v_data_x3f_380_;
v___y_331_ = v___x_385_;
v___y_332_ = v_label_374_;
v___y_333_ = v_sortText_x3f_379_;
v___y_334_ = v___f_384_;
v___y_335_ = v_documentation_x3f_376_;
v___y_336_ = v_detail_x3f_375_;
v___y_337_ = v_textEdit_x3f_378_;
v___y_338_ = v___y_383_;
v___y_339_ = v___y_382_;
v___y_340_ = v___x_424_;
goto v___jp_327_;
}
}
else
{
lean_object* v___x_425_; 
lean_dec_ref(v_env_371_);
v___x_425_ = lean_box(0);
v___y_328_ = v_tags_x3f_381_;
v___y_329_ = v_kind_x3f_377_;
v___y_330_ = v_data_x3f_380_;
v___y_331_ = v___x_385_;
v___y_332_ = v_label_374_;
v___y_333_ = v_sortText_x3f_379_;
v___y_334_ = v___f_384_;
v___y_335_ = v_documentation_x3f_376_;
v___y_336_ = v_detail_x3f_375_;
v___y_337_ = v_textEdit_x3f_378_;
v___y_338_ = v___y_383_;
v___y_339_ = v___y_382_;
v___y_340_ = v___x_425_;
goto v___jp_327_;
}
}
else
{
lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_432_; 
lean_dec(v_tags_x3f_381_);
lean_dec(v_data_x3f_380_);
lean_dec(v_sortText_x3f_379_);
lean_dec(v_textEdit_x3f_378_);
lean_dec(v_kind_x3f_377_);
lean_dec(v_detail_x3f_375_);
lean_dec_ref(v_label_374_);
lean_dec_ref(v_env_371_);
lean_dec_ref(v_id_270_);
v_isSharedCheck_432_ = !lean_is_exclusive(v_documentation_x3f_376_);
if (v_isSharedCheck_432_ == 0)
{
lean_object* v_unused_433_; 
v_unused_433_ = lean_ctor_get(v_documentation_x3f_376_, 0);
lean_dec(v_unused_433_);
v___x_427_ = v_documentation_x3f_376_;
v_isShared_428_ = v_isSharedCheck_432_;
goto v_resetjp_426_;
}
else
{
lean_dec(v_documentation_x3f_376_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_432_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_430_; 
if (v_isShared_428_ == 0)
{
lean_ctor_set_tag(v___x_427_, 0);
lean_ctor_set(v___x_427_, 0, v_item_373_);
v___x_430_ = v___x_427_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_item_373_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
return v___x_430_;
}
}
}
}
v___jp_442_:
{
lean_object* v___x_444_; 
lean_inc(v_tags_x3f_441_);
lean_inc(v_data_x3f_440_);
lean_inc(v_sortText_x3f_439_);
lean_inc(v_textEdit_x3f_438_);
lean_inc(v_kind_x3f_437_);
lean_inc(v_documentation_x3f_436_);
lean_inc(v_a_443_);
lean_inc_ref(v_label_434_);
v___x_444_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_444_, 0, v_label_434_);
lean_ctor_set(v___x_444_, 1, v_a_443_);
lean_ctor_set(v___x_444_, 2, v_documentation_x3f_436_);
lean_ctor_set(v___x_444_, 3, v_kind_x3f_437_);
lean_ctor_set(v___x_444_, 4, v_textEdit_x3f_438_);
lean_ctor_set(v___x_444_, 5, v_sortText_x3f_439_);
lean_ctor_set(v___x_444_, 6, v_data_x3f_440_);
lean_ctor_set(v___x_444_, 7, v_tags_x3f_441_);
v_item_373_ = v___x_444_;
v_label_374_ = v_label_434_;
v_detail_x3f_375_ = v_a_443_;
v_documentation_x3f_376_ = v_documentation_x3f_436_;
v_kind_x3f_377_ = v_kind_x3f_437_;
v_textEdit_x3f_378_ = v_textEdit_x3f_438_;
v_sortText_x3f_379_ = v_sortText_x3f_439_;
v_data_x3f_380_ = v_data_x3f_440_;
v_tags_x3f_381_ = v_tags_x3f_441_;
v___y_382_ = v_a_273_;
v___y_383_ = v_a_274_;
goto v___jp_372_;
}
v___jp_445_:
{
lean_object* v___x_447_; 
v___x_447_ = l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg(v_val_446_, v___f_368_, v_a_271_, v_a_272_, v_a_273_, v_a_274_);
if (lean_obj_tag(v___x_447_) == 0)
{
lean_object* v_a_448_; lean_object* v___x_449_; 
v_a_448_ = lean_ctor_get(v___x_447_, 0);
lean_inc(v_a_448_);
lean_dec_ref_known(v___x_447_, 1);
v___x_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_449_, 0, v_a_448_);
v_a_443_ = v___x_449_;
goto v___jp_442_;
}
else
{
lean_object* v_a_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_457_; 
lean_dec(v_tags_x3f_441_);
lean_dec(v_data_x3f_440_);
lean_dec(v_sortText_x3f_439_);
lean_dec(v_textEdit_x3f_438_);
lean_dec(v_kind_x3f_437_);
lean_dec(v_documentation_x3f_436_);
lean_dec_ref(v_label_434_);
lean_dec_ref(v_env_371_);
lean_dec_ref(v_id_270_);
v_a_450_ = lean_ctor_get(v___x_447_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_457_ == 0)
{
v___x_452_ = v___x_447_;
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_a_450_);
lean_dec(v___x_447_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_455_; 
if (v_isShared_453_ == 0)
{
v___x_455_ = v___x_452_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_a_450_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Lsp_CompletionItem_resolve_0interp(lean_interpreter_value* stack)
{
lean_object* v_item_269_ = stack[0].m_obj;
lean_object* v_id_270_ = stack[1].m_obj;
lean_object* v_a_271_ = stack[2].m_obj;
lean_object* v_a_272_ = stack[3].m_obj;
lean_object* v_a_273_ = stack[4].m_obj;
lean_object* v_a_274_ = stack[5].m_obj;
lean_object* v_res_468_;
v_res_468_ = l_Lean_Lsp_CompletionItem_resolve(v_item_269_, v_id_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_);
stack->m_obj
 = v_res_468_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___boxed(lean_object* v_item_469_, lean_object* v_id_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Lean_Lsp_CompletionItem_resolve(v_item_469_, v_id_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_);
lean_dec(v_a_474_);
lean_dec_ref(v_a_473_);
lean_dec(v_a_472_);
lean_dec_ref(v_a_471_);
return v_res_476_;
}
}
lean_object* l_Lean_Server_Completion_resolveCompletionItem_x3f(lean_object* v_fileMap_477_, lean_object* v_hoverPos_478_, lean_object* v_cmdStx_479_, lean_object* v_infoTree_480_, lean_object* v_item_481_, lean_object* v_id_482_, lean_object* v_completionInfoPos_483_){
_start:
{
lean_object* v___x_485_; lean_object* v_fst_486_; lean_object* v___x_487_; uint8_t v___x_488_; 
v___x_485_ = l_Lean_Server_Completion_findCompletionInfosAt(v_fileMap_477_, v_hoverPos_478_, v_cmdStx_479_, v_infoTree_480_);
v_fst_486_ = lean_ctor_get(v___x_485_, 0);
lean_inc(v_fst_486_);
lean_dec_ref(v___x_485_);
v___x_487_ = lean_array_get_size(v_fst_486_);
v___x_488_ = lean_nat_dec_lt(v_completionInfoPos_483_, v___x_487_);
if (v___x_488_ == 0)
{
lean_object* v___x_489_; 
lean_dec(v_fst_486_);
lean_dec_ref(v_id_482_);
v___x_489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_489_, 0, v_item_481_);
return v___x_489_;
}
else
{
lean_object* v___x_490_; lean_object* v_ctx_491_; lean_object* v_info_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_490_ = lean_array_fget(v_fst_486_, v_completionInfoPos_483_);
lean_dec(v_fst_486_);
v_ctx_491_ = lean_ctor_get(v___x_490_, 1);
lean_inc_ref(v_ctx_491_);
v_info_492_ = lean_ctor_get(v___x_490_, 2);
lean_inc_ref(v_info_492_);
lean_dec(v___x_490_);
v___x_493_ = l_Lean_Elab_CompletionInfo_lctx(v_info_492_);
lean_dec_ref(v_info_492_);
v___x_494_ = lean_alloc_closure((void*)(l_Lean_Lsp_CompletionItem_resolve___boxed), 7, 2);
lean_closure_set(v___x_494_, 0, v_item_481_);
lean_closure_set(v___x_494_, 1, v_id_482_);
v___x_495_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_491_, v___x_493_, v___x_494_);
return v___x_495_;
}
}
}
LEAN_EXPORT void l_Lean_Server_Completion_resolveCompletionItem_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_fileMap_477_ = stack[0].m_obj;
lean_object* v_hoverPos_478_ = stack[1].m_obj;
lean_object* v_cmdStx_479_ = stack[2].m_obj;
lean_object* v_infoTree_480_ = stack[3].m_obj;
lean_object* v_item_481_ = stack[4].m_obj;
lean_object* v_id_482_ = stack[5].m_obj;
lean_object* v_completionInfoPos_483_ = stack[6].m_obj;
lean_object* v_res_496_;
v_res_496_ = l_Lean_Server_Completion_resolveCompletionItem_x3f(v_fileMap_477_, v_hoverPos_478_, v_cmdStx_479_, v_infoTree_480_, v_item_481_, v_id_482_, v_completionInfoPos_483_);
stack->m_obj
 = v_res_496_;
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_resolveCompletionItem_x3f___boxed(lean_object* v_fileMap_497_, lean_object* v_hoverPos_498_, lean_object* v_cmdStx_499_, lean_object* v_infoTree_500_, lean_object* v_item_501_, lean_object* v_id_502_, lean_object* v_completionInfoPos_503_, lean_object* v_a_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Lean_Server_Completion_resolveCompletionItem_x3f(v_fileMap_497_, v_hoverPos_498_, v_cmdStx_499_, v_infoTree_500_, v_item_501_, v_id_502_, v_completionInfoPos_503_);
lean_dec(v_completionInfoPos_503_);
return v_res_505_;
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

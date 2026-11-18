// Lean compiler output
// Module: Lean.Linter.Util
// Imports: public import Lean.Elab.InfoTree.Util public import Lean.Linter.Init public import Lean.Elab.Term public import Lean.Linter.CodeQuality.Basic
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
lean_object* l_Lean_Elab_getDeclarationRange_x3f___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Position_lt(lean_object*, lean_object*);
lean_object* l_Lean_findDeclarationRangesCore_x3f___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
lean_object* l_Lean_Elab_InfoTree_collectNodesBottomUp___redArg(lean_object*, lean_object*);
lean_object* l_List_forIn_x27_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getInfoTrees___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Environment_mainModule(lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_List_filterMapTR_go___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Info_contains(lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Dynamic_0__Dynamic_typeNameImpl(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__0_value;
static const lean_array_object l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_collectMacroExpansions_x3f___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_collectMacroExpansions_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_collectMacroExpansions_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_getDeclsByBody___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Linter_getDeclsByBody___lam__0___closed__0 = (const lean_object*)&l_Lean_Linter_getDeclsByBody___lam__0___closed__0_value;
static const lean_string_object l_Lean_Linter_getDeclsByBody___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Linter_getDeclsByBody___lam__0___closed__1 = (const lean_object*)&l_Lean_Linter_getDeclsByBody___lam__0___closed__1_value;
static const lean_string_object l_Lean_Linter_getDeclsByBody___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Linter_getDeclsByBody___lam__0___closed__2 = (const lean_object*)&l_Lean_Linter_getDeclsByBody___lam__0___closed__2_value;
static const lean_string_object l_Lean_Linter_getDeclsByBody___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "BodyInfo"};
static const lean_object* l_Lean_Linter_getDeclsByBody___lam__0___closed__3 = (const lean_object*)&l_Lean_Linter_getDeclsByBody___lam__0___closed__3_value;
static const lean_ctor_object l_Lean_Linter_getDeclsByBody___lam__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_getDeclsByBody___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_getDeclsByBody___lam__0___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_getDeclsByBody___lam__0___closed__4_value_aux_0),((lean_object*)&l_Lean_Linter_getDeclsByBody___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Linter_getDeclsByBody___lam__0___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_getDeclsByBody___lam__0___closed__4_value_aux_1),((lean_object*)&l_Lean_Linter_getDeclsByBody___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l_Lean_Linter_getDeclsByBody___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_getDeclsByBody___lam__0___closed__4_value_aux_2),((lean_object*)&l_Lean_Linter_getDeclsByBody___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(19, 55, 149, 208, 231, 10, 140, 188)}};
static const lean_object* l_Lean_Linter_getDeclsByBody___lam__0___closed__4 = (const lean_object*)&l_Lean_Linter_getDeclsByBody___lam__0___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Linter_getDeclsByBody___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getDeclsByBody___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Linter_getDeclsByBody___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Linter_getDeclsByBody___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Linter_getDeclsByBody___closed__0 = (const lean_object*)&l_Lean_Linter_getDeclsByBody___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Linter_getDeclsByBody(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getNewDecls___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getNewDecls___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Linter_getNewDecls___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Linter_getNewDecls___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Linter_getNewDecls___closed__0 = (const lean_object*)&l_Lean_Linter_getNewDecls___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Linter_getNewDecls(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_findMatchingDecl_x3f___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_findMatchingDecl_x3f___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_findMatchingDecl_x3f___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_findMatchingDecl_x3f___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_findMatchingDecl_x3f___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_findMatchingDecl_x3f___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_findMatchingDecl_x3f___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_findMatchingDecl_x3f___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_findMatchingDecl_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_findMatchingDecl_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_findMatchingDecl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_findMatchingDecl_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_findCodeQualitySource_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_findCodeQualitySource_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_findCodeQualitySource_x3f___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_findCodeQualitySource_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_findCodeQualitySource_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_findCodeQualitySource_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_findCodeQualitySource_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_findCodeQualitySource___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_findCodeQualitySource___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_findCodeQualitySource___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_findCodeQualitySource___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_findCodeQualitySource___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_findCodeQualitySource___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_findCodeQualitySource___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_findCodeQualitySource(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_findCodeQualitySource___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__0(lean_object* v_toPure_1_, lean_object* v_x_2_, lean_object* v_x_3_, lean_object* v_x_4_){
_start:
{
uint8_t v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_5_ = 1;
v___x_6_ = lean_box(v___x_5_);
v___x_7_ = lean_apply_2(v_toPure_1_, lean_box(0), v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__0___boxed(lean_object* v_toPure_8_, lean_object* v_x_9_, lean_object* v_x_10_, lean_object* v_x_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__0(v_toPure_8_, v_x_9_, v_x_10_, v_x_11_);
lean_dec_ref(v_x_11_);
lean_dec_ref(v_x_10_);
lean_dec_ref(v_x_9_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1(lean_object* v_toPure_18_, lean_object* v_range_19_, lean_object* v_x_20_, lean_object* v_i_21_, lean_object* v_x_22_, lean_object* v_results_23_){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v_results_30_; 
v___x_27_ = ((lean_object*)(l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__0));
v___x_28_ = ((lean_object*)(l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__1));
v___x_29_ = l_List_filterMapTR_go___redArg(v___x_27_, v_results_23_, v___x_28_);
v_results_30_ = l_List_filterMapTR_go___redArg(v___x_27_, v___x_29_, v___x_28_);
if (lean_obj_tag(v_results_30_) == 1)
{
lean_dec_ref(v_range_19_);
if (lean_obj_tag(v_i_21_) == 4)
{
lean_object* v_head_31_; lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_47_; 
v_head_31_ = lean_ctor_get(v_results_30_, 0);
v_isSharedCheck_47_ = !lean_is_exclusive(v_results_30_);
if (v_isSharedCheck_47_ == 0)
{
lean_object* v_unused_48_; 
v_unused_48_ = lean_ctor_get(v_results_30_, 1);
lean_dec(v_unused_48_);
v___x_33_ = v_results_30_;
v_isShared_34_ = v_isSharedCheck_47_;
goto v_resetjp_32_;
}
else
{
lean_inc(v_head_31_);
lean_dec(v_results_30_);
v___x_33_ = lean_box(0);
v_isShared_34_ = v_isSharedCheck_47_;
goto v_resetjp_32_;
}
v_resetjp_32_:
{
lean_object* v_i_35_; lean_object* v___x_37_; uint8_t v_isShared_38_; uint8_t v_isSharedCheck_46_; 
v_i_35_ = lean_ctor_get(v_i_21_, 0);
v_isSharedCheck_46_ = !lean_is_exclusive(v_i_21_);
if (v_isSharedCheck_46_ == 0)
{
v___x_37_ = v_i_21_;
v_isShared_38_ = v_isSharedCheck_46_;
goto v_resetjp_36_;
}
else
{
lean_inc(v_i_35_);
lean_dec(v_i_21_);
v___x_37_ = lean_box(0);
v_isShared_38_ = v_isSharedCheck_46_;
goto v_resetjp_36_;
}
v_resetjp_36_:
{
lean_object* v___x_40_; 
if (v_isShared_34_ == 0)
{
lean_ctor_set(v___x_33_, 1, v_head_31_);
lean_ctor_set(v___x_33_, 0, v_i_35_);
v___x_40_ = v___x_33_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v_i_35_);
lean_ctor_set(v_reuseFailAlloc_45_, 1, v_head_31_);
v___x_40_ = v_reuseFailAlloc_45_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
lean_object* v___x_42_; 
if (v_isShared_38_ == 0)
{
lean_ctor_set_tag(v___x_37_, 1);
lean_ctor_set(v___x_37_, 0, v___x_40_);
v___x_42_ = v___x_37_;
goto v_reusejp_41_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v___x_40_);
v___x_42_ = v_reuseFailAlloc_44_;
goto v_reusejp_41_;
}
v_reusejp_41_:
{
lean_object* v___x_43_; 
v___x_43_ = lean_apply_2(v_toPure_18_, lean_box(0), v___x_42_);
return v___x_43_;
}
}
}
}
}
else
{
lean_object* v_head_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
lean_dec_ref(v_i_21_);
v_head_49_ = lean_ctor_get(v_results_30_, 0);
lean_inc(v_head_49_);
lean_dec_ref_known(v_results_30_, 2);
v___x_50_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_50_, 0, v_head_49_);
v___x_51_ = lean_apply_2(v_toPure_18_, lean_box(0), v___x_50_);
return v___x_51_;
}
}
else
{
lean_object* v_start_52_; lean_object* v_stop_53_; lean_object* v___x_55_; uint8_t v_isShared_56_; uint8_t v_isSharedCheck_75_; 
lean_dec(v_results_30_);
v_start_52_ = lean_ctor_get(v_range_19_, 0);
v_stop_53_ = lean_ctor_get(v_range_19_, 1);
v_isSharedCheck_75_ = !lean_is_exclusive(v_range_19_);
if (v_isSharedCheck_75_ == 0)
{
v___x_55_ = v_range_19_;
v_isShared_56_ = v_isSharedCheck_75_;
goto v_resetjp_54_;
}
else
{
lean_inc(v_stop_53_);
lean_inc(v_start_52_);
lean_dec(v_range_19_);
v___x_55_ = lean_box(0);
v_isShared_56_ = v_isSharedCheck_75_;
goto v_resetjp_54_;
}
v_resetjp_54_:
{
uint8_t v___x_57_; uint8_t v___x_58_; 
v___x_57_ = 0;
v___x_58_ = l_Lean_Elab_Info_contains(v_i_21_, v_start_52_, v___x_57_);
lean_dec(v_start_52_);
if (v___x_58_ == 0)
{
lean_del_object(v___x_55_);
lean_dec(v_stop_53_);
lean_dec_ref(v_i_21_);
goto v___jp_24_;
}
else
{
uint8_t v___x_59_; 
v___x_59_ = l_Lean_Elab_Info_contains(v_i_21_, v_stop_53_, v___x_58_);
lean_dec(v_stop_53_);
if (v___x_59_ == 0)
{
lean_del_object(v___x_55_);
lean_dec_ref(v_i_21_);
goto v___jp_24_;
}
else
{
if (lean_obj_tag(v_i_21_) == 4)
{
lean_object* v_i_60_; lean_object* v___x_62_; uint8_t v_isShared_63_; uint8_t v_isSharedCheck_72_; 
v_i_60_ = lean_ctor_get(v_i_21_, 0);
v_isSharedCheck_72_ = !lean_is_exclusive(v_i_21_);
if (v_isSharedCheck_72_ == 0)
{
v___x_62_ = v_i_21_;
v_isShared_63_ = v_isSharedCheck_72_;
goto v_resetjp_61_;
}
else
{
lean_inc(v_i_60_);
lean_dec(v_i_21_);
v___x_62_ = lean_box(0);
v_isShared_63_ = v_isSharedCheck_72_;
goto v_resetjp_61_;
}
v_resetjp_61_:
{
lean_object* v___x_64_; lean_object* v___x_66_; 
v___x_64_ = lean_box(0);
if (v_isShared_56_ == 0)
{
lean_ctor_set_tag(v___x_55_, 1);
lean_ctor_set(v___x_55_, 1, v___x_64_);
lean_ctor_set(v___x_55_, 0, v_i_60_);
v___x_66_ = v___x_55_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_71_; 
v_reuseFailAlloc_71_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_71_, 0, v_i_60_);
lean_ctor_set(v_reuseFailAlloc_71_, 1, v___x_64_);
v___x_66_ = v_reuseFailAlloc_71_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
lean_object* v___x_68_; 
if (v_isShared_63_ == 0)
{
lean_ctor_set_tag(v___x_62_, 1);
lean_ctor_set(v___x_62_, 0, v___x_66_);
v___x_68_ = v___x_62_;
goto v_reusejp_67_;
}
else
{
lean_object* v_reuseFailAlloc_70_; 
v_reuseFailAlloc_70_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_70_, 0, v___x_66_);
v___x_68_ = v_reuseFailAlloc_70_;
goto v_reusejp_67_;
}
v_reusejp_67_:
{
lean_object* v___x_69_; 
v___x_69_ = lean_apply_2(v_toPure_18_, lean_box(0), v___x_68_);
return v___x_69_;
}
}
}
}
else
{
lean_object* v___x_73_; lean_object* v___x_74_; 
lean_del_object(v___x_55_);
lean_dec_ref(v_i_21_);
v___x_73_ = ((lean_object*)(l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__2));
v___x_74_ = lean_apply_2(v_toPure_18_, lean_box(0), v___x_73_);
return v___x_74_;
}
}
}
}
}
v___jp_24_:
{
lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_25_ = lean_box(0);
v___x_26_ = lean_apply_2(v_toPure_18_, lean_box(0), v___x_25_);
return v___x_26_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___boxed(lean_object* v_toPure_76_, lean_object* v_range_77_, lean_object* v_x_78_, lean_object* v_i_79_, lean_object* v_x_80_, lean_object* v_results_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1(v_toPure_76_, v_range_77_, v_x_78_, v_i_79_, v_x_80_, v_results_81_);
lean_dec_ref(v_x_80_);
lean_dec_ref(v_x_78_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg(lean_object* v_inst_83_, lean_object* v_range_84_, lean_object* v_tree_85_){
_start:
{
lean_object* v_toApplicative_86_; lean_object* v_toPure_87_; lean_object* v___f_88_; lean_object* v___f_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v_toApplicative_86_ = lean_ctor_get(v_inst_83_, 0);
v_toPure_87_ = lean_ctor_get(v_toApplicative_86_, 1);
lean_inc_n(v_toPure_87_, 2);
v___f_88_ = lean_alloc_closure((void*)(l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_88_, 0, v_toPure_87_);
v___f_89_ = lean_alloc_closure((void*)(l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___boxed), 6, 2);
lean_closure_set(v___f_89_, 0, v_toPure_87_);
lean_closure_set(v___f_89_, 1, v_range_84_);
v___x_90_ = lean_box(0);
v___x_91_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go(lean_box(0), lean_box(0), v_inst_83_, v___f_88_, v___f_89_, v___x_90_, v_tree_85_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go(lean_object* v_m_92_, lean_object* v_inst_93_, lean_object* v_range_94_, lean_object* v_tree_95_){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg(v_inst_93_, v_range_94_, v_tree_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_collectMacroExpansions_x3f___redArg___lam__0(lean_object* v_toPure_97_, lean_object* v_____do__lift_98_){
_start:
{
if (lean_obj_tag(v_____do__lift_98_) == 1)
{
lean_object* v_val_102_; 
v_val_102_ = lean_ctor_get(v_____do__lift_98_, 0);
lean_inc(v_val_102_);
lean_dec_ref_known(v_____do__lift_98_, 1);
if (lean_obj_tag(v_val_102_) == 1)
{
lean_object* v_val_103_; lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_112_; 
v_val_103_ = lean_ctor_get(v_val_102_, 0);
v_isSharedCheck_112_ = !lean_is_exclusive(v_val_102_);
if (v_isSharedCheck_112_ == 0)
{
v___x_105_ = v_val_102_;
v_isShared_106_ = v_isSharedCheck_112_;
goto v_resetjp_104_;
}
else
{
lean_inc(v_val_103_);
lean_dec(v_val_102_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_112_;
goto v_resetjp_104_;
}
v_resetjp_104_:
{
lean_object* v___x_107_; lean_object* v___x_109_; 
v___x_107_ = l_List_reverse___redArg(v_val_103_);
if (v_isShared_106_ == 0)
{
lean_ctor_set(v___x_105_, 0, v___x_107_);
v___x_109_ = v___x_105_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v___x_107_);
v___x_109_ = v_reuseFailAlloc_111_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
lean_object* v___x_110_; 
v___x_110_ = lean_apply_2(v_toPure_97_, lean_box(0), v___x_109_);
return v___x_110_;
}
}
}
else
{
lean_dec(v_val_102_);
goto v___jp_99_;
}
}
else
{
lean_dec(v_____do__lift_98_);
goto v___jp_99_;
}
v___jp_99_:
{
lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_100_ = lean_box(0);
v___x_101_ = lean_apply_2(v_toPure_97_, lean_box(0), v___x_100_);
return v___x_101_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_collectMacroExpansions_x3f___redArg(lean_object* v_inst_113_, lean_object* v_range_114_, lean_object* v_tree_115_){
_start:
{
lean_object* v_toApplicative_116_; lean_object* v_toBind_117_; lean_object* v_toPure_118_; lean_object* v___x_119_; lean_object* v___f_120_; lean_object* v___x_121_; 
v_toApplicative_116_ = lean_ctor_get(v_inst_113_, 0);
v_toBind_117_ = lean_ctor_get(v_inst_113_, 1);
lean_inc(v_toBind_117_);
v_toPure_118_ = lean_ctor_get(v_toApplicative_116_, 1);
lean_inc(v_toPure_118_);
v___x_119_ = l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg(v_inst_113_, v_range_114_, v_tree_115_);
v___f_120_ = lean_alloc_closure((void*)(l_Lean_Linter_collectMacroExpansions_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_120_, 0, v_toPure_118_);
v___x_121_ = lean_apply_4(v_toBind_117_, lean_box(0), lean_box(0), v___x_119_, v___f_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_collectMacroExpansions_x3f(lean_object* v_m_122_, lean_object* v_inst_123_, lean_object* v_range_124_, lean_object* v_tree_125_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = l_Lean_Linter_collectMacroExpansions_x3f___redArg(v_inst_123_, v_range_124_, v_tree_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getDeclsByBody___lam__0(lean_object* v_ctx_136_, lean_object* v_i_137_, lean_object* v_x_138_, lean_object* v_decls_139_){
_start:
{
if (lean_obj_tag(v_i_137_) == 10)
{
lean_object* v_i_140_; lean_object* v_value_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_153_; 
v_i_140_ = lean_ctor_get(v_i_137_, 0);
lean_inc_ref(v_i_140_);
lean_dec_ref_known(v_i_137_, 1);
v_value_141_ = lean_ctor_get(v_i_140_, 1);
v_isSharedCheck_153_ = !lean_is_exclusive(v_i_140_);
if (v_isSharedCheck_153_ == 0)
{
lean_object* v_unused_154_; 
v_unused_154_ = lean_ctor_get(v_i_140_, 0);
lean_dec(v_unused_154_);
v___x_143_ = v_i_140_;
v_isShared_144_ = v_isSharedCheck_153_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_value_141_);
lean_dec(v_i_140_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_153_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___x_145_; lean_object* v___x_146_; uint8_t v___x_147_; 
v___x_145_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_value_141_);
lean_dec(v_value_141_);
v___x_146_ = ((lean_object*)(l_Lean_Linter_getDeclsByBody___lam__0___closed__4));
v___x_147_ = lean_name_eq(v___x_145_, v___x_146_);
lean_dec(v___x_145_);
if (v___x_147_ == 0)
{
lean_del_object(v___x_143_);
return v_decls_139_;
}
else
{
lean_object* v_parentDecl_x3f_148_; 
v_parentDecl_x3f_148_ = lean_ctor_get(v_ctx_136_, 1);
if (lean_obj_tag(v_parentDecl_x3f_148_) == 1)
{
lean_object* v_val_149_; lean_object* v___x_151_; 
v_val_149_ = lean_ctor_get(v_parentDecl_x3f_148_, 0);
lean_inc(v_val_149_);
if (v_isShared_144_ == 0)
{
lean_ctor_set_tag(v___x_143_, 1);
lean_ctor_set(v___x_143_, 1, v_decls_139_);
lean_ctor_set(v___x_143_, 0, v_val_149_);
v___x_151_ = v___x_143_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_val_149_);
lean_ctor_set(v_reuseFailAlloc_152_, 1, v_decls_139_);
v___x_151_ = v_reuseFailAlloc_152_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
return v___x_151_;
}
}
else
{
lean_del_object(v___x_143_);
return v_decls_139_;
}
}
}
}
else
{
lean_dec_ref(v_i_137_);
return v_decls_139_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getDeclsByBody___lam__0___boxed(lean_object* v_ctx_155_, lean_object* v_i_156_, lean_object* v_x_157_, lean_object* v_decls_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l_Lean_Linter_getDeclsByBody___lam__0(v_ctx_155_, v_i_156_, v_x_157_, v_decls_158_);
lean_dec_ref(v_x_157_);
lean_dec_ref(v_ctx_155_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getDeclsByBody(lean_object* v_t_161_){
_start:
{
lean_object* v___f_162_; lean_object* v___x_163_; 
v___f_162_ = ((lean_object*)(l_Lean_Linter_getDeclsByBody___closed__0));
v___x_163_ = l_Lean_Elab_InfoTree_collectNodesBottomUp___redArg(v___f_162_, v_t_161_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getNewDecls___lam__0(lean_object* v_x_164_, lean_object* v_i_165_, lean_object* v_x_166_, lean_object* v_acc_167_){
_start:
{
if (lean_obj_tag(v_i_165_) == 1)
{
lean_object* v_i_168_; uint8_t v_isBinder_169_; 
v_i_168_ = lean_ctor_get(v_i_165_, 0);
v_isBinder_169_ = lean_ctor_get_uint8(v_i_168_, sizeof(void*)*4);
if (v_isBinder_169_ == 0)
{
return v_acc_167_;
}
else
{
lean_object* v_expr_170_; uint8_t v___x_171_; 
v_expr_170_ = lean_ctor_get(v_i_168_, 3);
v___x_171_ = l_Lean_Expr_isConst(v_expr_170_);
if (v___x_171_ == 0)
{
return v_acc_167_;
}
else
{
lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_172_ = l_Lean_Expr_constName_x21(v_expr_170_);
v___x_173_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_173_, 0, v___x_172_);
lean_ctor_set(v___x_173_, 1, v_acc_167_);
return v___x_173_;
}
}
}
else
{
return v_acc_167_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getNewDecls___lam__0___boxed(lean_object* v_x_174_, lean_object* v_i_175_, lean_object* v_x_176_, lean_object* v_acc_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Lean_Linter_getNewDecls___lam__0(v_x_174_, v_i_175_, v_x_176_, v_acc_177_);
lean_dec_ref(v_x_176_);
lean_dec_ref(v_i_175_);
lean_dec_ref(v_x_174_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getNewDecls(lean_object* v_t_180_){
_start:
{
lean_object* v___f_181_; lean_object* v___x_182_; 
v___f_181_ = ((lean_object*)(l_Lean_Linter_getNewDecls___closed__0));
v___x_182_ = l_Lean_Elab_InfoTree_collectNodesBottomUp___redArg(v___f_181_, v_t_180_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_findMatchingDecl_x3f___redArg___lam__0(lean_object* v_toPure_183_, lean_object* v_____s_184_){
_start:
{
if (lean_obj_tag(v_____s_184_) == 0)
{
lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_185_ = lean_box(0);
v___x_186_ = lean_apply_2(v_toPure_183_, lean_box(0), v___x_185_);
return v___x_186_;
}
else
{
lean_object* v_val_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_196_; 
v_val_187_ = lean_ctor_get(v_____s_184_, 0);
v_isSharedCheck_196_ = !lean_is_exclusive(v_____s_184_);
if (v_isSharedCheck_196_ == 0)
{
v___x_189_ = v_____s_184_;
v_isShared_190_ = v_isSharedCheck_196_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_val_187_);
lean_dec(v_____s_184_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_196_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v_fst_191_; lean_object* v___x_193_; 
v_fst_191_ = lean_ctor_get(v_val_187_, 0);
lean_inc(v_fst_191_);
lean_dec(v_val_187_);
if (v_isShared_190_ == 0)
{
lean_ctor_set(v___x_189_, 0, v_fst_191_);
v___x_193_ = v___x_189_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v_fst_191_);
v___x_193_ = v_reuseFailAlloc_195_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
lean_object* v___x_194_; 
v___x_194_ = lean_apply_2(v_toPure_183_, lean_box(0), v___x_193_);
return v___x_194_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_findMatchingDecl_x3f___redArg___lam__1(lean_object* v_toPure_197_, lean_object* v_____s_198_){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_199_, 0, v_____s_198_);
v___x_200_ = lean_apply_2(v_toPure_197_, lean_box(0), v___x_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_findMatchingDecl_x3f___redArg___lam__2(lean_object* v_val_201_, lean_object* v___y_202_, lean_object* v_toPure_203_, lean_object* v_a_204_, lean_object* v_____x_205_){
_start:
{
if (lean_obj_tag(v_____x_205_) == 1)
{
lean_object* v_val_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_240_; 
v_val_209_ = lean_ctor_get(v_____x_205_, 0);
v_isSharedCheck_240_ = !lean_is_exclusive(v_____x_205_);
if (v_isSharedCheck_240_ == 0)
{
v___x_211_ = v_____x_205_;
v_isShared_212_ = v_isSharedCheck_240_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_val_209_);
lean_dec(v_____x_205_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_240_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v_range_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_238_; 
v_range_213_ = lean_ctor_get(v_val_209_, 0);
v_isSharedCheck_238_ = !lean_is_exclusive(v_val_209_);
if (v_isSharedCheck_238_ == 0)
{
lean_object* v_unused_239_; 
v_unused_239_ = lean_ctor_get(v_val_209_, 1);
lean_dec(v_unused_239_);
v___x_215_ = v_val_209_;
v_isShared_216_ = v_isSharedCheck_238_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_range_213_);
lean_dec(v_val_209_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_238_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v_pos_226_; lean_object* v_endPos_227_; lean_object* v_pos_228_; lean_object* v_endPos_229_; uint8_t v___x_230_; 
v_pos_226_ = lean_ctor_get(v_range_213_, 0);
v_endPos_227_ = lean_ctor_get(v_range_213_, 2);
v_pos_228_ = lean_ctor_get(v_val_201_, 0);
lean_inc_ref(v_pos_228_);
v_endPos_229_ = lean_ctor_get(v_val_201_, 2);
lean_inc_ref(v_endPos_229_);
lean_dec_ref(v_val_201_);
lean_inc_ref(v_pos_226_);
v___x_230_ = l_Lean_Position_lt(v_pos_226_, v_pos_228_);
if (v___x_230_ == 0)
{
uint8_t v___x_231_; 
lean_inc_ref(v_endPos_227_);
v___x_231_ = l_Lean_Position_lt(v_endPos_229_, v_endPos_227_);
if (v___x_231_ == 0)
{
if (lean_obj_tag(v___y_202_) == 0)
{
goto v___jp_217_;
}
else
{
lean_object* v_val_232_; lean_object* v_snd_233_; lean_object* v_pos_234_; uint8_t v___x_235_; 
v_val_232_ = lean_ctor_get(v___y_202_, 0);
v_snd_233_ = lean_ctor_get(v_val_232_, 1);
v_pos_234_ = lean_ctor_get(v_snd_233_, 0);
lean_inc_ref(v_pos_234_);
lean_inc_ref(v_pos_226_);
v___x_235_ = l_Lean_Position_lt(v_pos_226_, v_pos_234_);
if (v___x_235_ == 0)
{
lean_object* v___x_236_; lean_object* v___x_237_; 
lean_del_object(v___x_215_);
lean_dec_ref(v_range_213_);
lean_del_object(v___x_211_);
lean_dec(v_a_204_);
v___x_236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_236_, 0, v___y_202_);
v___x_237_ = lean_apply_2(v_toPure_203_, lean_box(0), v___x_236_);
return v___x_237_;
}
else
{
lean_dec_ref_known(v___y_202_, 1);
goto v___jp_217_;
}
}
}
else
{
lean_del_object(v___x_215_);
lean_dec_ref(v_range_213_);
lean_del_object(v___x_211_);
lean_dec(v_a_204_);
goto v___jp_206_;
}
}
else
{
lean_dec_ref(v_endPos_229_);
lean_del_object(v___x_215_);
lean_dec_ref(v_range_213_);
lean_del_object(v___x_211_);
lean_dec(v_a_204_);
goto v___jp_206_;
}
v___jp_217_:
{
lean_object* v___x_219_; 
if (v_isShared_216_ == 0)
{
lean_ctor_set(v___x_215_, 1, v_range_213_);
lean_ctor_set(v___x_215_, 0, v_a_204_);
v___x_219_ = v___x_215_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v_a_204_);
lean_ctor_set(v_reuseFailAlloc_225_, 1, v_range_213_);
v___x_219_ = v_reuseFailAlloc_225_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
lean_object* v___x_221_; 
if (v_isShared_212_ == 0)
{
lean_ctor_set(v___x_211_, 0, v___x_219_);
v___x_221_ = v___x_211_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v___x_219_);
v___x_221_ = v_reuseFailAlloc_224_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_222_, 0, v___x_221_);
v___x_223_ = lean_apply_2(v_toPure_203_, lean_box(0), v___x_222_);
return v___x_223_;
}
}
}
}
}
}
else
{
lean_object* v___x_241_; lean_object* v___x_242_; 
lean_dec(v_____x_205_);
lean_dec(v_a_204_);
lean_dec_ref(v_val_201_);
v___x_241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_241_, 0, v___y_202_);
v___x_242_ = lean_apply_2(v_toPure_203_, lean_box(0), v___x_241_);
return v___x_242_;
}
v___jp_206_:
{
lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_207_, 0, v___y_202_);
v___x_208_ = lean_apply_2(v_toPure_203_, lean_box(0), v___x_207_);
return v___x_208_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_findMatchingDecl_x3f___redArg___lam__3(lean_object* v_val_243_, lean_object* v_toPure_244_, lean_object* v_inst_245_, lean_object* v_inst_246_, lean_object* v_toBind_247_, lean_object* v_a_248_, lean_object* v_x_249_, lean_object* v___y_250_){
_start:
{
lean_object* v___f_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
lean_inc(v_a_248_);
v___f_251_ = lean_alloc_closure((void*)(l_Lean_Linter_findMatchingDecl_x3f___redArg___lam__2), 5, 4);
lean_closure_set(v___f_251_, 0, v_val_243_);
lean_closure_set(v___f_251_, 1, v___y_250_);
lean_closure_set(v___f_251_, 2, v_toPure_244_);
lean_closure_set(v___f_251_, 3, v_a_248_);
v___x_252_ = l_Lean_findDeclarationRangesCore_x3f___redArg(v_inst_245_, v_inst_246_, v_a_248_);
v___x_253_ = lean_apply_4(v_toBind_247_, lean_box(0), lean_box(0), v___x_252_, v___f_251_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_findMatchingDecl_x3f___redArg___lam__4(lean_object* v_inst_254_, lean_object* v___f_255_, lean_object* v_toBind_256_, lean_object* v___f_257_, lean_object* v_t_258_, lean_object* v_____s_259_){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_260_ = l_Lean_Linter_getNewDecls(v_t_258_);
v___x_261_ = l_List_forIn_x27_loop___redArg(v_inst_254_, v___f_255_, v___x_260_, v_____s_259_);
lean_dec(v___x_260_);
v___x_262_ = lean_apply_4(v_toBind_256_, lean_box(0), lean_box(0), v___x_261_, v___f_257_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_findMatchingDecl_x3f___redArg___lam__5(lean_object* v_inst_263_, lean_object* v_best_x3f_264_, lean_object* v___f_265_, lean_object* v_toBind_266_, lean_object* v___f_267_, lean_object* v_____do__lift_268_){
_start:
{
lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_269_ = l_Lean_PersistentArray_forIn___redArg(v_inst_263_, v_____do__lift_268_, v_best_x3f_264_, v___f_265_);
v___x_270_ = lean_apply_4(v_toBind_266_, lean_box(0), lean_box(0), v___x_269_, v___f_267_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_findMatchingDecl_x3f___redArg___lam__5___boxed(lean_object* v_inst_271_, lean_object* v_best_x3f_272_, lean_object* v___f_273_, lean_object* v_toBind_274_, lean_object* v___f_275_, lean_object* v_____do__lift_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Lean_Linter_findMatchingDecl_x3f___redArg___lam__5(v_inst_271_, v_best_x3f_272_, v___f_273_, v_toBind_274_, v___f_275_, v_____do__lift_276_);
lean_dec_ref(v_____do__lift_276_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_findMatchingDecl_x3f___redArg___lam__6(lean_object* v_toPure_278_, lean_object* v_inst_279_, lean_object* v_inst_280_, lean_object* v_toBind_281_, lean_object* v___f_282_, lean_object* v___f_283_, lean_object* v_inst_284_, lean_object* v_____x_285_){
_start:
{
if (lean_obj_tag(v_____x_285_) == 1)
{
lean_object* v_val_286_; lean_object* v___f_287_; lean_object* v___f_288_; lean_object* v_best_x3f_289_; lean_object* v___f_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v_val_286_ = lean_ctor_get(v_____x_285_, 0);
lean_inc(v_val_286_);
lean_dec_ref_known(v_____x_285_, 1);
lean_inc_n(v_toBind_281_, 3);
lean_inc_ref_n(v_inst_279_, 3);
v___f_287_ = lean_alloc_closure((void*)(l_Lean_Linter_findMatchingDecl_x3f___redArg___lam__3), 8, 5);
lean_closure_set(v___f_287_, 0, v_val_286_);
lean_closure_set(v___f_287_, 1, v_toPure_278_);
lean_closure_set(v___f_287_, 2, v_inst_279_);
lean_closure_set(v___f_287_, 3, v_inst_280_);
lean_closure_set(v___f_287_, 4, v_toBind_281_);
v___f_288_ = lean_alloc_closure((void*)(l_Lean_Linter_findMatchingDecl_x3f___redArg___lam__4), 6, 4);
lean_closure_set(v___f_288_, 0, v_inst_279_);
lean_closure_set(v___f_288_, 1, v___f_287_);
lean_closure_set(v___f_288_, 2, v_toBind_281_);
lean_closure_set(v___f_288_, 3, v___f_282_);
v_best_x3f_289_ = lean_box(0);
v___f_290_ = lean_alloc_closure((void*)(l_Lean_Linter_findMatchingDecl_x3f___redArg___lam__5___boxed), 6, 5);
lean_closure_set(v___f_290_, 0, v_inst_279_);
lean_closure_set(v___f_290_, 1, v_best_x3f_289_);
lean_closure_set(v___f_290_, 2, v___f_288_);
lean_closure_set(v___f_290_, 3, v_toBind_281_);
lean_closure_set(v___f_290_, 4, v___f_283_);
v___x_291_ = l_Lean_Elab_getInfoTrees___redArg(v_inst_284_, v_inst_279_);
v___x_292_ = lean_apply_4(v_toBind_281_, lean_box(0), lean_box(0), v___x_291_, v___f_290_);
return v___x_292_;
}
else
{
lean_object* v___x_293_; lean_object* v___x_294_; 
lean_dec(v_____x_285_);
lean_dec_ref(v_inst_284_);
lean_dec(v___f_283_);
lean_dec(v___f_282_);
lean_dec(v_toBind_281_);
lean_dec_ref(v_inst_280_);
lean_dec_ref(v_inst_279_);
v___x_293_ = lean_box(0);
v___x_294_ = lean_apply_2(v_toPure_278_, lean_box(0), v___x_293_);
return v___x_294_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_findMatchingDecl_x3f___redArg(lean_object* v_inst_295_, lean_object* v_inst_296_, lean_object* v_inst_297_, lean_object* v_inst_298_, lean_object* v_stx_299_){
_start:
{
lean_object* v_toApplicative_300_; lean_object* v_toBind_301_; lean_object* v_toPure_302_; lean_object* v___x_303_; lean_object* v___f_304_; lean_object* v___f_305_; lean_object* v___f_306_; lean_object* v___x_307_; 
v_toApplicative_300_ = lean_ctor_get(v_inst_295_, 0);
v_toBind_301_ = lean_ctor_get(v_inst_295_, 1);
lean_inc_n(v_toBind_301_, 2);
v_toPure_302_ = lean_ctor_get(v_toApplicative_300_, 1);
lean_inc_n(v_toPure_302_, 3);
lean_inc_ref(v_inst_295_);
v___x_303_ = l_Lean_Elab_getDeclarationRange_x3f___redArg(v_inst_295_, v_inst_298_, v_stx_299_);
v___f_304_ = lean_alloc_closure((void*)(l_Lean_Linter_findMatchingDecl_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_304_, 0, v_toPure_302_);
v___f_305_ = lean_alloc_closure((void*)(l_Lean_Linter_findMatchingDecl_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_305_, 0, v_toPure_302_);
v___f_306_ = lean_alloc_closure((void*)(l_Lean_Linter_findMatchingDecl_x3f___redArg___lam__6), 8, 7);
lean_closure_set(v___f_306_, 0, v_toPure_302_);
lean_closure_set(v___f_306_, 1, v_inst_295_);
lean_closure_set(v___f_306_, 2, v_inst_297_);
lean_closure_set(v___f_306_, 3, v_toBind_301_);
lean_closure_set(v___f_306_, 4, v___f_305_);
lean_closure_set(v___f_306_, 5, v___f_304_);
lean_closure_set(v___f_306_, 6, v_inst_296_);
v___x_307_ = lean_apply_4(v_toBind_301_, lean_box(0), lean_box(0), v___x_303_, v___f_306_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_findMatchingDecl_x3f___redArg___boxed(lean_object* v_inst_308_, lean_object* v_inst_309_, lean_object* v_inst_310_, lean_object* v_inst_311_, lean_object* v_stx_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Lean_Linter_findMatchingDecl_x3f___redArg(v_inst_308_, v_inst_309_, v_inst_310_, v_inst_311_, v_stx_312_);
lean_dec(v_stx_312_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_findMatchingDecl_x3f(lean_object* v_m_314_, lean_object* v_inst_315_, lean_object* v_inst_316_, lean_object* v_inst_317_, lean_object* v_inst_318_, lean_object* v_stx_319_){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = l_Lean_Linter_findMatchingDecl_x3f___redArg(v_inst_315_, v_inst_316_, v_inst_317_, v_inst_318_, v_stx_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_findMatchingDecl_x3f___boxed(lean_object* v_m_321_, lean_object* v_inst_322_, lean_object* v_inst_323_, lean_object* v_inst_324_, lean_object* v_inst_325_, lean_object* v_stx_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_Lean_Linter_findMatchingDecl_x3f(v_m_321_, v_inst_322_, v_inst_323_, v_inst_324_, v_inst_325_, v_stx_326_);
lean_dec(v_stx_326_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_findCodeQualitySource_x3f___redArg___lam__0(lean_object* v_val_328_, lean_object* v_toPure_329_, lean_object* v_____do__lift_330_){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_331_ = l_Lean_Environment_mainModule(v_____do__lift_330_);
v___x_332_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_332_, 0, v___x_331_);
lean_ctor_set(v___x_332_, 1, v_val_328_);
v___x_333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
v___x_334_ = lean_apply_2(v_toPure_329_, lean_box(0), v___x_333_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_findCodeQualitySource_x3f___redArg___lam__0___boxed(lean_object* v_val_335_, lean_object* v_toPure_336_, lean_object* v_____do__lift_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Lean_Linter_findCodeQualitySource_x3f___redArg___lam__0(v_val_335_, v_toPure_336_, v_____do__lift_337_);
lean_dec_ref(v_____do__lift_337_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_findCodeQualitySource_x3f___redArg___lam__1(lean_object* v_inst_339_, lean_object* v_toPure_340_, lean_object* v_toBind_341_, lean_object* v_____x_342_){
_start:
{
if (lean_obj_tag(v_____x_342_) == 1)
{
lean_object* v_val_343_; lean_object* v_getEnv_344_; lean_object* v___f_345_; lean_object* v___x_346_; 
v_val_343_ = lean_ctor_get(v_____x_342_, 0);
lean_inc(v_val_343_);
lean_dec_ref_known(v_____x_342_, 1);
v_getEnv_344_ = lean_ctor_get(v_inst_339_, 0);
lean_inc(v_getEnv_344_);
lean_dec_ref(v_inst_339_);
v___f_345_ = lean_alloc_closure((void*)(l_Lean_Linter_findCodeQualitySource_x3f___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_345_, 0, v_val_343_);
lean_closure_set(v___f_345_, 1, v_toPure_340_);
v___x_346_ = lean_apply_4(v_toBind_341_, lean_box(0), lean_box(0), v_getEnv_344_, v___f_345_);
return v___x_346_;
}
else
{
lean_object* v___x_347_; lean_object* v___x_348_; 
lean_dec(v_____x_342_);
lean_dec(v_toBind_341_);
lean_dec_ref(v_inst_339_);
v___x_347_ = lean_box(0);
v___x_348_ = lean_apply_2(v_toPure_340_, lean_box(0), v___x_347_);
return v___x_348_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_findCodeQualitySource_x3f___redArg(lean_object* v_inst_349_, lean_object* v_inst_350_, lean_object* v_inst_351_, lean_object* v_inst_352_, lean_object* v_stx_353_){
_start:
{
lean_object* v_toApplicative_354_; lean_object* v_toBind_355_; lean_object* v_toPure_356_; lean_object* v___x_357_; lean_object* v___f_358_; lean_object* v___x_359_; 
v_toApplicative_354_ = lean_ctor_get(v_inst_349_, 0);
v_toBind_355_ = lean_ctor_get(v_inst_349_, 1);
lean_inc_n(v_toBind_355_, 2);
v_toPure_356_ = lean_ctor_get(v_toApplicative_354_, 1);
lean_inc(v_toPure_356_);
lean_inc_ref(v_inst_351_);
v___x_357_ = l_Lean_Linter_findMatchingDecl_x3f___redArg(v_inst_349_, v_inst_350_, v_inst_351_, v_inst_352_, v_stx_353_);
v___f_358_ = lean_alloc_closure((void*)(l_Lean_Linter_findCodeQualitySource_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_358_, 0, v_inst_351_);
lean_closure_set(v___f_358_, 1, v_toPure_356_);
lean_closure_set(v___f_358_, 2, v_toBind_355_);
v___x_359_ = lean_apply_4(v_toBind_355_, lean_box(0), lean_box(0), v___x_357_, v___f_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_findCodeQualitySource_x3f___redArg___boxed(lean_object* v_inst_360_, lean_object* v_inst_361_, lean_object* v_inst_362_, lean_object* v_inst_363_, lean_object* v_stx_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Lean_Linter_findCodeQualitySource_x3f___redArg(v_inst_360_, v_inst_361_, v_inst_362_, v_inst_363_, v_stx_364_);
lean_dec(v_stx_364_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_findCodeQualitySource_x3f(lean_object* v_m_366_, lean_object* v_inst_367_, lean_object* v_inst_368_, lean_object* v_inst_369_, lean_object* v_inst_370_, lean_object* v_stx_371_){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = l_Lean_Linter_findCodeQualitySource_x3f___redArg(v_inst_367_, v_inst_368_, v_inst_369_, v_inst_370_, v_stx_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_findCodeQualitySource_x3f___boxed(lean_object* v_m_373_, lean_object* v_inst_374_, lean_object* v_inst_375_, lean_object* v_inst_376_, lean_object* v_inst_377_, lean_object* v_stx_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Lean_Linter_findCodeQualitySource_x3f(v_m_373_, v_inst_374_, v_inst_375_, v_inst_376_, v_inst_377_, v_stx_378_);
lean_dec(v_stx_378_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_findCodeQualitySource___redArg___lam__0(lean_object* v_toPure_380_, lean_object* v_____do__lift_381_){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_382_ = l_Lean_Environment_mainModule(v_____do__lift_381_);
v___x_383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_383_, 0, v___x_382_);
v___x_384_ = lean_apply_2(v_toPure_380_, lean_box(0), v___x_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_findCodeQualitySource___redArg___lam__0___boxed(lean_object* v_toPure_385_, lean_object* v_____do__lift_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Lean_Linter_findCodeQualitySource___redArg___lam__0(v_toPure_385_, v_____do__lift_386_);
lean_dec_ref(v_____do__lift_386_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_findCodeQualitySource___redArg___lam__1(lean_object* v_val_388_, lean_object* v_toPure_389_, lean_object* v_____do__lift_390_){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_391_ = l_Lean_Environment_mainModule(v_____do__lift_390_);
v___x_392_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_392_, 0, v___x_391_);
lean_ctor_set(v___x_392_, 1, v_val_388_);
v___x_393_ = lean_apply_2(v_toPure_389_, lean_box(0), v___x_392_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_findCodeQualitySource___redArg___lam__1___boxed(lean_object* v_val_394_, lean_object* v_toPure_395_, lean_object* v_____do__lift_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Lean_Linter_findCodeQualitySource___redArg___lam__1(v_val_394_, v_toPure_395_, v_____do__lift_396_);
lean_dec_ref(v_____do__lift_396_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_findCodeQualitySource___redArg___lam__2(lean_object* v_inst_398_, lean_object* v_toBind_399_, lean_object* v___f_400_, lean_object* v_toPure_401_, lean_object* v_____do__lift_402_){
_start:
{
if (lean_obj_tag(v_____do__lift_402_) == 0)
{
lean_object* v_getEnv_403_; lean_object* v___x_404_; 
lean_dec(v_toPure_401_);
v_getEnv_403_ = lean_ctor_get(v_inst_398_, 0);
lean_inc(v_getEnv_403_);
lean_dec_ref(v_inst_398_);
v___x_404_ = lean_apply_4(v_toBind_399_, lean_box(0), lean_box(0), v_getEnv_403_, v___f_400_);
return v___x_404_;
}
else
{
lean_object* v_val_405_; lean_object* v_getEnv_406_; lean_object* v___f_407_; lean_object* v___x_408_; 
lean_dec(v___f_400_);
v_val_405_ = lean_ctor_get(v_____do__lift_402_, 0);
lean_inc(v_val_405_);
lean_dec_ref_known(v_____do__lift_402_, 1);
v_getEnv_406_ = lean_ctor_get(v_inst_398_, 0);
lean_inc(v_getEnv_406_);
lean_dec_ref(v_inst_398_);
v___f_407_ = lean_alloc_closure((void*)(l_Lean_Linter_findCodeQualitySource___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_407_, 0, v_val_405_);
lean_closure_set(v___f_407_, 1, v_toPure_401_);
v___x_408_ = lean_apply_4(v_toBind_399_, lean_box(0), lean_box(0), v_getEnv_406_, v___f_407_);
return v___x_408_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_findCodeQualitySource___redArg(lean_object* v_inst_409_, lean_object* v_inst_410_, lean_object* v_inst_411_, lean_object* v_inst_412_, lean_object* v_stx_413_){
_start:
{
lean_object* v_toApplicative_414_; lean_object* v_toBind_415_; lean_object* v_toPure_416_; lean_object* v___x_417_; lean_object* v___f_418_; lean_object* v___f_419_; lean_object* v___x_420_; 
v_toApplicative_414_ = lean_ctor_get(v_inst_409_, 0);
v_toBind_415_ = lean_ctor_get(v_inst_409_, 1);
lean_inc_n(v_toBind_415_, 2);
v_toPure_416_ = lean_ctor_get(v_toApplicative_414_, 1);
lean_inc_n(v_toPure_416_, 2);
lean_inc_ref(v_inst_411_);
v___x_417_ = l_Lean_Linter_findMatchingDecl_x3f___redArg(v_inst_409_, v_inst_410_, v_inst_411_, v_inst_412_, v_stx_413_);
v___f_418_ = lean_alloc_closure((void*)(l_Lean_Linter_findCodeQualitySource___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_418_, 0, v_toPure_416_);
v___f_419_ = lean_alloc_closure((void*)(l_Lean_Linter_findCodeQualitySource___redArg___lam__2), 5, 4);
lean_closure_set(v___f_419_, 0, v_inst_411_);
lean_closure_set(v___f_419_, 1, v_toBind_415_);
lean_closure_set(v___f_419_, 2, v___f_418_);
lean_closure_set(v___f_419_, 3, v_toPure_416_);
v___x_420_ = lean_apply_4(v_toBind_415_, lean_box(0), lean_box(0), v___x_417_, v___f_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_findCodeQualitySource___redArg___boxed(lean_object* v_inst_421_, lean_object* v_inst_422_, lean_object* v_inst_423_, lean_object* v_inst_424_, lean_object* v_stx_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Lean_Linter_findCodeQualitySource___redArg(v_inst_421_, v_inst_422_, v_inst_423_, v_inst_424_, v_stx_425_);
lean_dec(v_stx_425_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_findCodeQualitySource(lean_object* v_m_427_, lean_object* v_inst_428_, lean_object* v_inst_429_, lean_object* v_inst_430_, lean_object* v_inst_431_, lean_object* v_stx_432_){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = l_Lean_Linter_findCodeQualitySource___redArg(v_inst_428_, v_inst_429_, v_inst_430_, v_inst_431_, v_stx_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_findCodeQualitySource___boxed(lean_object* v_m_434_, lean_object* v_inst_435_, lean_object* v_inst_436_, lean_object* v_inst_437_, lean_object* v_inst_438_, lean_object* v_stx_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Lean_Linter_findCodeQualitySource(v_m_434_, v_inst_435_, v_inst_436_, v_inst_437_, v_inst_438_, v_stx_439_);
lean_dec(v_stx_439_);
return v_res_440_;
}
}
lean_object* runtime_initialize_Lean_Elab_InfoTree_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Init(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Term(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_CodeQuality_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Linter_Util(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_InfoTree_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_CodeQuality_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Linter_Util(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_InfoTree_Util(uint8_t builtin);
lean_object* initialize_Lean_Linter_Init(uint8_t builtin);
lean_object* initialize_Lean_Elab_Term(uint8_t builtin);
lean_object* initialize_Lean_Linter_CodeQuality_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Linter_Util(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_InfoTree_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_CodeQuality_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Linter_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Linter_Util(builtin);
}
#ifdef __cplusplus
}
#endif

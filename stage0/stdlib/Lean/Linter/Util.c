// Lean compiler output
// Module: Lean.Linter.Util
// Imports: public import Lean.Server.InfoUtils public import Lean.Linter.Init public import Lean.Elab.Term public import Lean.Linter.CodeQuality.Basic
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
lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Dynamic_0__Dynamic_typeNameImpl(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__0_value;
static const lean_closure_object l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__1_value;
static const lean_array_object l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
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
uint8_t v___y_25_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v_results_44_; 
v___x_41_ = ((lean_object*)(l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__1));
v___x_42_ = ((lean_object*)(l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__2));
v___x_43_ = l_List_filterMapTR_go___redArg(v___x_41_, v_results_23_, v___x_42_);
v_results_44_ = l_List_filterMapTR_go___redArg(v___x_41_, v___x_43_, v___x_42_);
if (lean_obj_tag(v_results_44_) == 1)
{
if (lean_obj_tag(v_i_21_) == 4)
{
lean_object* v_head_45_; lean_object* v___x_47_; uint8_t v_isShared_48_; uint8_t v_isSharedCheck_61_; 
v_head_45_ = lean_ctor_get(v_results_44_, 0);
v_isSharedCheck_61_ = !lean_is_exclusive(v_results_44_);
if (v_isSharedCheck_61_ == 0)
{
lean_object* v_unused_62_; 
v_unused_62_ = lean_ctor_get(v_results_44_, 1);
lean_dec(v_unused_62_);
v___x_47_ = v_results_44_;
v_isShared_48_ = v_isSharedCheck_61_;
goto v_resetjp_46_;
}
else
{
lean_inc(v_head_45_);
lean_dec(v_results_44_);
v___x_47_ = lean_box(0);
v_isShared_48_ = v_isSharedCheck_61_;
goto v_resetjp_46_;
}
v_resetjp_46_:
{
lean_object* v_i_49_; lean_object* v___x_51_; uint8_t v_isShared_52_; uint8_t v_isSharedCheck_60_; 
v_i_49_ = lean_ctor_get(v_i_21_, 0);
v_isSharedCheck_60_ = !lean_is_exclusive(v_i_21_);
if (v_isSharedCheck_60_ == 0)
{
v___x_51_ = v_i_21_;
v_isShared_52_ = v_isSharedCheck_60_;
goto v_resetjp_50_;
}
else
{
lean_inc(v_i_49_);
lean_dec(v_i_21_);
v___x_51_ = lean_box(0);
v_isShared_52_ = v_isSharedCheck_60_;
goto v_resetjp_50_;
}
v_resetjp_50_:
{
lean_object* v___x_54_; 
if (v_isShared_48_ == 0)
{
lean_ctor_set(v___x_47_, 1, v_head_45_);
lean_ctor_set(v___x_47_, 0, v_i_49_);
v___x_54_ = v___x_47_;
goto v_reusejp_53_;
}
else
{
lean_object* v_reuseFailAlloc_59_; 
v_reuseFailAlloc_59_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_59_, 0, v_i_49_);
lean_ctor_set(v_reuseFailAlloc_59_, 1, v_head_45_);
v___x_54_ = v_reuseFailAlloc_59_;
goto v_reusejp_53_;
}
v_reusejp_53_:
{
lean_object* v___x_56_; 
if (v_isShared_52_ == 0)
{
lean_ctor_set_tag(v___x_51_, 1);
lean_ctor_set(v___x_51_, 0, v___x_54_);
v___x_56_ = v___x_51_;
goto v_reusejp_55_;
}
else
{
lean_object* v_reuseFailAlloc_58_; 
v_reuseFailAlloc_58_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_58_, 0, v___x_54_);
v___x_56_ = v_reuseFailAlloc_58_;
goto v_reusejp_55_;
}
v_reusejp_55_:
{
lean_object* v___x_57_; 
v___x_57_ = lean_apply_2(v_toPure_18_, lean_box(0), v___x_56_);
return v___x_57_;
}
}
}
}
}
else
{
lean_object* v_head_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
lean_dec_ref(v_i_21_);
v_head_63_ = lean_ctor_get(v_results_44_, 0);
lean_inc(v_head_63_);
lean_dec_ref_known(v_results_44_, 2);
v___x_64_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_64_, 0, v_head_63_);
v___x_65_ = lean_apply_2(v_toPure_18_, lean_box(0), v___x_64_);
return v___x_65_;
}
}
else
{
lean_object* v_start_66_; lean_object* v_stop_67_; uint8_t v___x_68_; uint8_t v___x_69_; 
lean_dec(v_results_44_);
v_start_66_ = lean_ctor_get(v_range_19_, 0);
v_stop_67_ = lean_ctor_get(v_range_19_, 1);
v___x_68_ = 0;
v___x_69_ = l_Lean_Elab_Info_contains(v_i_21_, v_start_66_, v___x_68_);
if (v___x_69_ == 0)
{
v___y_25_ = v___x_69_;
goto v___jp_24_;
}
else
{
uint8_t v___x_70_; 
v___x_70_ = l_Lean_Elab_Info_contains(v_i_21_, v_stop_67_, v___x_69_);
v___y_25_ = v___x_70_;
goto v___jp_24_;
}
}
v___jp_24_:
{
if (v___y_25_ == 0)
{
lean_object* v___x_26_; lean_object* v___x_27_; 
lean_dec_ref(v_i_21_);
v___x_26_ = lean_box(0);
v___x_27_ = lean_apply_2(v_toPure_18_, lean_box(0), v___x_26_);
return v___x_27_;
}
else
{
if (lean_obj_tag(v_i_21_) == 4)
{
lean_object* v_i_28_; lean_object* v___x_30_; uint8_t v_isShared_31_; uint8_t v_isSharedCheck_38_; 
v_i_28_ = lean_ctor_get(v_i_21_, 0);
v_isSharedCheck_38_ = !lean_is_exclusive(v_i_21_);
if (v_isSharedCheck_38_ == 0)
{
v___x_30_ = v_i_21_;
v_isShared_31_ = v_isSharedCheck_38_;
goto v_resetjp_29_;
}
else
{
lean_inc(v_i_28_);
lean_dec(v_i_21_);
v___x_30_ = lean_box(0);
v_isShared_31_ = v_isSharedCheck_38_;
goto v_resetjp_29_;
}
v_resetjp_29_:
{
lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_35_; 
v___x_32_ = lean_box(0);
v___x_33_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_33_, 0, v_i_28_);
lean_ctor_set(v___x_33_, 1, v___x_32_);
if (v_isShared_31_ == 0)
{
lean_ctor_set_tag(v___x_30_, 1);
lean_ctor_set(v___x_30_, 0, v___x_33_);
v___x_35_ = v___x_30_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_37_; 
v_reuseFailAlloc_37_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_37_, 0, v___x_33_);
v___x_35_ = v_reuseFailAlloc_37_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
lean_object* v___x_36_; 
v___x_36_ = lean_apply_2(v_toPure_18_, lean_box(0), v___x_35_);
return v___x_36_;
}
}
}
else
{
lean_object* v___x_39_; lean_object* v___x_40_; 
lean_dec_ref(v_i_21_);
v___x_39_ = ((lean_object*)(l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__0));
v___x_40_ = lean_apply_2(v_toPure_18_, lean_box(0), v___x_39_);
return v___x_40_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___boxed(lean_object* v_toPure_71_, lean_object* v_range_72_, lean_object* v_x_73_, lean_object* v_i_74_, lean_object* v_x_75_, lean_object* v_results_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1(v_toPure_71_, v_range_72_, v_x_73_, v_i_74_, v_x_75_, v_results_76_);
lean_dec_ref(v_x_75_);
lean_dec_ref(v_x_73_);
lean_dec_ref(v_range_72_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg(lean_object* v_inst_78_, lean_object* v_range_79_, lean_object* v_tree_80_){
_start:
{
lean_object* v_toApplicative_81_; lean_object* v_toPure_82_; lean_object* v___f_83_; lean_object* v___f_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v_toApplicative_81_ = lean_ctor_get(v_inst_78_, 0);
v_toPure_82_ = lean_ctor_get(v_toApplicative_81_, 1);
lean_inc_n(v_toPure_82_, 2);
v___f_83_ = lean_alloc_closure((void*)(l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_83_, 0, v_toPure_82_);
v___f_84_ = lean_alloc_closure((void*)(l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___boxed), 6, 2);
lean_closure_set(v___f_84_, 0, v_toPure_82_);
lean_closure_set(v___f_84_, 1, v_range_79_);
v___x_85_ = lean_box(0);
v___x_86_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go(lean_box(0), lean_box(0), v_inst_78_, v___f_83_, v___f_84_, v___x_85_, v_tree_80_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go(lean_object* v_m_87_, lean_object* v_inst_88_, lean_object* v_range_89_, lean_object* v_tree_90_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg(v_inst_88_, v_range_89_, v_tree_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_collectMacroExpansions_x3f___redArg___lam__0(lean_object* v_toPure_92_, lean_object* v_____do__lift_93_){
_start:
{
if (lean_obj_tag(v_____do__lift_93_) == 1)
{
lean_object* v_val_97_; 
v_val_97_ = lean_ctor_get(v_____do__lift_93_, 0);
lean_inc(v_val_97_);
lean_dec_ref_known(v_____do__lift_93_, 1);
if (lean_obj_tag(v_val_97_) == 1)
{
lean_object* v_val_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_107_; 
v_val_98_ = lean_ctor_get(v_val_97_, 0);
v_isSharedCheck_107_ = !lean_is_exclusive(v_val_97_);
if (v_isSharedCheck_107_ == 0)
{
v___x_100_ = v_val_97_;
v_isShared_101_ = v_isSharedCheck_107_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_val_98_);
lean_dec(v_val_97_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_107_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
lean_object* v___x_102_; lean_object* v___x_104_; 
v___x_102_ = l_List_reverse___redArg(v_val_98_);
if (v_isShared_101_ == 0)
{
lean_ctor_set(v___x_100_, 0, v___x_102_);
v___x_104_ = v___x_100_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v___x_102_);
v___x_104_ = v_reuseFailAlloc_106_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
lean_object* v___x_105_; 
v___x_105_ = lean_apply_2(v_toPure_92_, lean_box(0), v___x_104_);
return v___x_105_;
}
}
}
else
{
lean_dec(v_val_97_);
goto v___jp_94_;
}
}
else
{
lean_dec(v_____do__lift_93_);
goto v___jp_94_;
}
v___jp_94_:
{
lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_95_ = lean_box(0);
v___x_96_ = lean_apply_2(v_toPure_92_, lean_box(0), v___x_95_);
return v___x_96_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_collectMacroExpansions_x3f___redArg(lean_object* v_inst_108_, lean_object* v_range_109_, lean_object* v_tree_110_){
_start:
{
lean_object* v_toApplicative_111_; lean_object* v_toBind_112_; lean_object* v_toPure_113_; lean_object* v___x_114_; lean_object* v___f_115_; lean_object* v___x_116_; 
v_toApplicative_111_ = lean_ctor_get(v_inst_108_, 0);
v_toBind_112_ = lean_ctor_get(v_inst_108_, 1);
lean_inc(v_toBind_112_);
v_toPure_113_ = lean_ctor_get(v_toApplicative_111_, 1);
lean_inc(v_toPure_113_);
v___x_114_ = l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg(v_inst_108_, v_range_109_, v_tree_110_);
v___f_115_ = lean_alloc_closure((void*)(l_Lean_Linter_collectMacroExpansions_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_115_, 0, v_toPure_113_);
v___x_116_ = lean_apply_4(v_toBind_112_, lean_box(0), lean_box(0), v___x_114_, v___f_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_collectMacroExpansions_x3f(lean_object* v_m_117_, lean_object* v_inst_118_, lean_object* v_range_119_, lean_object* v_tree_120_){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = l_Lean_Linter_collectMacroExpansions_x3f___redArg(v_inst_118_, v_range_119_, v_tree_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getDeclsByBody___lam__0(lean_object* v_ctx_131_, lean_object* v_i_132_, lean_object* v_x_133_, lean_object* v_decls_134_){
_start:
{
if (lean_obj_tag(v_i_132_) == 10)
{
lean_object* v_i_135_; lean_object* v_value_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_148_; 
v_i_135_ = lean_ctor_get(v_i_132_, 0);
lean_inc_ref(v_i_135_);
lean_dec_ref_known(v_i_132_, 1);
v_value_136_ = lean_ctor_get(v_i_135_, 1);
v_isSharedCheck_148_ = !lean_is_exclusive(v_i_135_);
if (v_isSharedCheck_148_ == 0)
{
lean_object* v_unused_149_; 
v_unused_149_ = lean_ctor_get(v_i_135_, 0);
lean_dec(v_unused_149_);
v___x_138_ = v_i_135_;
v_isShared_139_ = v_isSharedCheck_148_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_value_136_);
lean_dec(v_i_135_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_148_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v___x_140_; lean_object* v___x_141_; uint8_t v___x_142_; 
v___x_140_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_value_136_);
lean_dec(v_value_136_);
v___x_141_ = ((lean_object*)(l_Lean_Linter_getDeclsByBody___lam__0___closed__4));
v___x_142_ = lean_name_eq(v___x_140_, v___x_141_);
lean_dec(v___x_140_);
if (v___x_142_ == 0)
{
lean_del_object(v___x_138_);
return v_decls_134_;
}
else
{
lean_object* v_parentDecl_x3f_143_; 
v_parentDecl_x3f_143_ = lean_ctor_get(v_ctx_131_, 1);
if (lean_obj_tag(v_parentDecl_x3f_143_) == 1)
{
lean_object* v_val_144_; lean_object* v___x_146_; 
v_val_144_ = lean_ctor_get(v_parentDecl_x3f_143_, 0);
lean_inc(v_val_144_);
if (v_isShared_139_ == 0)
{
lean_ctor_set_tag(v___x_138_, 1);
lean_ctor_set(v___x_138_, 1, v_decls_134_);
lean_ctor_set(v___x_138_, 0, v_val_144_);
v___x_146_ = v___x_138_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v_val_144_);
lean_ctor_set(v_reuseFailAlloc_147_, 1, v_decls_134_);
v___x_146_ = v_reuseFailAlloc_147_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
return v___x_146_;
}
}
else
{
lean_del_object(v___x_138_);
return v_decls_134_;
}
}
}
}
else
{
lean_dec_ref(v_i_132_);
return v_decls_134_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getDeclsByBody___lam__0___boxed(lean_object* v_ctx_150_, lean_object* v_i_151_, lean_object* v_x_152_, lean_object* v_decls_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_Lean_Linter_getDeclsByBody___lam__0(v_ctx_150_, v_i_151_, v_x_152_, v_decls_153_);
lean_dec_ref(v_x_152_);
lean_dec_ref(v_ctx_150_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getDeclsByBody(lean_object* v_t_156_){
_start:
{
lean_object* v___f_157_; lean_object* v___x_158_; 
v___f_157_ = ((lean_object*)(l_Lean_Linter_getDeclsByBody___closed__0));
v___x_158_ = l_Lean_Elab_InfoTree_collectNodesBottomUp___redArg(v___f_157_, v_t_156_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getNewDecls___lam__0(lean_object* v_x_159_, lean_object* v_i_160_, lean_object* v_x_161_, lean_object* v_acc_162_){
_start:
{
if (lean_obj_tag(v_i_160_) == 1)
{
lean_object* v_i_163_; uint8_t v_isBinder_164_; 
v_i_163_ = lean_ctor_get(v_i_160_, 0);
v_isBinder_164_ = lean_ctor_get_uint8(v_i_163_, sizeof(void*)*4);
if (v_isBinder_164_ == 0)
{
return v_acc_162_;
}
else
{
lean_object* v_expr_165_; uint8_t v___x_166_; 
v_expr_165_ = lean_ctor_get(v_i_163_, 3);
v___x_166_ = l_Lean_Expr_isConst(v_expr_165_);
if (v___x_166_ == 0)
{
return v_acc_162_;
}
else
{
lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_167_ = l_Lean_Expr_constName_x21(v_expr_165_);
v___x_168_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_168_, 0, v___x_167_);
lean_ctor_set(v___x_168_, 1, v_acc_162_);
return v___x_168_;
}
}
}
else
{
return v_acc_162_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getNewDecls___lam__0___boxed(lean_object* v_x_169_, lean_object* v_i_170_, lean_object* v_x_171_, lean_object* v_acc_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_Lean_Linter_getNewDecls___lam__0(v_x_169_, v_i_170_, v_x_171_, v_acc_172_);
lean_dec_ref(v_x_171_);
lean_dec_ref(v_i_170_);
lean_dec_ref(v_x_169_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getNewDecls(lean_object* v_t_175_){
_start:
{
lean_object* v___f_176_; lean_object* v___x_177_; 
v___f_176_ = ((lean_object*)(l_Lean_Linter_getNewDecls___closed__0));
v___x_177_ = l_Lean_Elab_InfoTree_collectNodesBottomUp___redArg(v___f_176_, v_t_175_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_findMatchingDecl_x3f___redArg___lam__0(lean_object* v_toPure_178_, lean_object* v_____s_179_){
_start:
{
if (lean_obj_tag(v_____s_179_) == 0)
{
lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_180_ = lean_box(0);
v___x_181_ = lean_apply_2(v_toPure_178_, lean_box(0), v___x_180_);
return v___x_181_;
}
else
{
lean_object* v_val_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_191_; 
v_val_182_ = lean_ctor_get(v_____s_179_, 0);
v_isSharedCheck_191_ = !lean_is_exclusive(v_____s_179_);
if (v_isSharedCheck_191_ == 0)
{
v___x_184_ = v_____s_179_;
v_isShared_185_ = v_isSharedCheck_191_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_val_182_);
lean_dec(v_____s_179_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_191_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v_fst_186_; lean_object* v___x_188_; 
v_fst_186_ = lean_ctor_get(v_val_182_, 0);
lean_inc(v_fst_186_);
lean_dec(v_val_182_);
if (v_isShared_185_ == 0)
{
lean_ctor_set(v___x_184_, 0, v_fst_186_);
v___x_188_ = v___x_184_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v_fst_186_);
v___x_188_ = v_reuseFailAlloc_190_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
lean_object* v___x_189_; 
v___x_189_ = lean_apply_2(v_toPure_178_, lean_box(0), v___x_188_);
return v___x_189_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_findMatchingDecl_x3f___redArg___lam__1(lean_object* v_toPure_192_, lean_object* v_____s_193_){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_194_, 0, v_____s_193_);
v___x_195_ = lean_apply_2(v_toPure_192_, lean_box(0), v___x_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_findMatchingDecl_x3f___redArg___lam__2(lean_object* v_val_196_, lean_object* v___y_197_, lean_object* v_toPure_198_, lean_object* v_a_199_, lean_object* v_____x_200_){
_start:
{
if (lean_obj_tag(v_____x_200_) == 1)
{
lean_object* v_val_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_235_; 
v_val_204_ = lean_ctor_get(v_____x_200_, 0);
v_isSharedCheck_235_ = !lean_is_exclusive(v_____x_200_);
if (v_isSharedCheck_235_ == 0)
{
v___x_206_ = v_____x_200_;
v_isShared_207_ = v_isSharedCheck_235_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_val_204_);
lean_dec(v_____x_200_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_235_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v_range_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_233_; 
v_range_208_ = lean_ctor_get(v_val_204_, 0);
v_isSharedCheck_233_ = !lean_is_exclusive(v_val_204_);
if (v_isSharedCheck_233_ == 0)
{
lean_object* v_unused_234_; 
v_unused_234_ = lean_ctor_get(v_val_204_, 1);
lean_dec(v_unused_234_);
v___x_210_ = v_val_204_;
v_isShared_211_ = v_isSharedCheck_233_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_range_208_);
lean_dec(v_val_204_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_233_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v_pos_221_; lean_object* v_endPos_222_; lean_object* v_pos_223_; lean_object* v_endPos_224_; uint8_t v___x_225_; 
v_pos_221_ = lean_ctor_get(v_range_208_, 0);
v_endPos_222_ = lean_ctor_get(v_range_208_, 2);
v_pos_223_ = lean_ctor_get(v_val_196_, 0);
lean_inc_ref(v_pos_223_);
v_endPos_224_ = lean_ctor_get(v_val_196_, 2);
lean_inc_ref(v_endPos_224_);
lean_dec_ref(v_val_196_);
lean_inc_ref(v_pos_221_);
v___x_225_ = l_Lean_Position_lt(v_pos_221_, v_pos_223_);
if (v___x_225_ == 0)
{
uint8_t v___x_226_; 
lean_inc_ref(v_endPos_222_);
v___x_226_ = l_Lean_Position_lt(v_endPos_224_, v_endPos_222_);
if (v___x_226_ == 0)
{
if (lean_obj_tag(v___y_197_) == 0)
{
goto v___jp_212_;
}
else
{
lean_object* v_val_227_; lean_object* v_snd_228_; lean_object* v_pos_229_; uint8_t v___x_230_; 
v_val_227_ = lean_ctor_get(v___y_197_, 0);
v_snd_228_ = lean_ctor_get(v_val_227_, 1);
v_pos_229_ = lean_ctor_get(v_snd_228_, 0);
lean_inc_ref(v_pos_229_);
lean_inc_ref(v_pos_221_);
v___x_230_ = l_Lean_Position_lt(v_pos_221_, v_pos_229_);
if (v___x_230_ == 0)
{
lean_object* v___x_231_; lean_object* v___x_232_; 
lean_del_object(v___x_210_);
lean_dec_ref(v_range_208_);
lean_del_object(v___x_206_);
lean_dec(v_a_199_);
v___x_231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_231_, 0, v___y_197_);
v___x_232_ = lean_apply_2(v_toPure_198_, lean_box(0), v___x_231_);
return v___x_232_;
}
else
{
lean_dec_ref_known(v___y_197_, 1);
goto v___jp_212_;
}
}
}
else
{
lean_del_object(v___x_210_);
lean_dec_ref(v_range_208_);
lean_del_object(v___x_206_);
lean_dec(v_a_199_);
goto v___jp_201_;
}
}
else
{
lean_dec_ref(v_endPos_224_);
lean_del_object(v___x_210_);
lean_dec_ref(v_range_208_);
lean_del_object(v___x_206_);
lean_dec(v_a_199_);
goto v___jp_201_;
}
v___jp_212_:
{
lean_object* v___x_214_; 
if (v_isShared_211_ == 0)
{
lean_ctor_set(v___x_210_, 1, v_range_208_);
lean_ctor_set(v___x_210_, 0, v_a_199_);
v___x_214_ = v___x_210_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v_a_199_);
lean_ctor_set(v_reuseFailAlloc_220_, 1, v_range_208_);
v___x_214_ = v_reuseFailAlloc_220_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
lean_object* v___x_216_; 
if (v_isShared_207_ == 0)
{
lean_ctor_set(v___x_206_, 0, v___x_214_);
v___x_216_ = v___x_206_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v___x_214_);
v___x_216_ = v_reuseFailAlloc_219_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_217_, 0, v___x_216_);
v___x_218_ = lean_apply_2(v_toPure_198_, lean_box(0), v___x_217_);
return v___x_218_;
}
}
}
}
}
}
else
{
lean_object* v___x_236_; lean_object* v___x_237_; 
lean_dec(v_____x_200_);
lean_dec(v_a_199_);
lean_dec_ref(v_val_196_);
v___x_236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_236_, 0, v___y_197_);
v___x_237_ = lean_apply_2(v_toPure_198_, lean_box(0), v___x_236_);
return v___x_237_;
}
v___jp_201_:
{
lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_202_, 0, v___y_197_);
v___x_203_ = lean_apply_2(v_toPure_198_, lean_box(0), v___x_202_);
return v___x_203_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_findMatchingDecl_x3f___redArg___lam__3(lean_object* v_val_238_, lean_object* v_toPure_239_, lean_object* v_inst_240_, lean_object* v_inst_241_, lean_object* v_toBind_242_, lean_object* v_a_243_, lean_object* v_x_244_, lean_object* v___y_245_){
_start:
{
lean_object* v___f_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
lean_inc(v_a_243_);
v___f_246_ = lean_alloc_closure((void*)(l_Lean_Linter_findMatchingDecl_x3f___redArg___lam__2), 5, 4);
lean_closure_set(v___f_246_, 0, v_val_238_);
lean_closure_set(v___f_246_, 1, v___y_245_);
lean_closure_set(v___f_246_, 2, v_toPure_239_);
lean_closure_set(v___f_246_, 3, v_a_243_);
v___x_247_ = l_Lean_findDeclarationRangesCore_x3f___redArg(v_inst_240_, v_inst_241_, v_a_243_);
v___x_248_ = lean_apply_4(v_toBind_242_, lean_box(0), lean_box(0), v___x_247_, v___f_246_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_findMatchingDecl_x3f___redArg___lam__4(lean_object* v_inst_249_, lean_object* v___f_250_, lean_object* v_toBind_251_, lean_object* v___f_252_, lean_object* v_t_253_, lean_object* v_____s_254_){
_start:
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_255_ = l_Lean_Linter_getNewDecls(v_t_253_);
v___x_256_ = l_List_forIn_x27_loop___redArg(v_inst_249_, v___f_250_, v___x_255_, v_____s_254_);
lean_dec(v___x_255_);
v___x_257_ = lean_apply_4(v_toBind_251_, lean_box(0), lean_box(0), v___x_256_, v___f_252_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_findMatchingDecl_x3f___redArg___lam__5(lean_object* v_inst_258_, lean_object* v_best_x3f_259_, lean_object* v___f_260_, lean_object* v_toBind_261_, lean_object* v___f_262_, lean_object* v_____do__lift_263_){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_264_ = l_Lean_PersistentArray_forIn___redArg(v_inst_258_, v_____do__lift_263_, v_best_x3f_259_, v___f_260_);
v___x_265_ = lean_apply_4(v_toBind_261_, lean_box(0), lean_box(0), v___x_264_, v___f_262_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_findMatchingDecl_x3f___redArg___lam__5___boxed(lean_object* v_inst_266_, lean_object* v_best_x3f_267_, lean_object* v___f_268_, lean_object* v_toBind_269_, lean_object* v___f_270_, lean_object* v_____do__lift_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Lean_Linter_findMatchingDecl_x3f___redArg___lam__5(v_inst_266_, v_best_x3f_267_, v___f_268_, v_toBind_269_, v___f_270_, v_____do__lift_271_);
lean_dec_ref(v_____do__lift_271_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_findMatchingDecl_x3f___redArg___lam__6(lean_object* v_toPure_273_, lean_object* v_inst_274_, lean_object* v_inst_275_, lean_object* v_toBind_276_, lean_object* v___f_277_, lean_object* v___f_278_, lean_object* v_inst_279_, lean_object* v_____x_280_){
_start:
{
if (lean_obj_tag(v_____x_280_) == 1)
{
lean_object* v_val_281_; lean_object* v___f_282_; lean_object* v___f_283_; lean_object* v_best_x3f_284_; lean_object* v___f_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v_val_281_ = lean_ctor_get(v_____x_280_, 0);
lean_inc(v_val_281_);
lean_dec_ref_known(v_____x_280_, 1);
lean_inc_n(v_toBind_276_, 3);
lean_inc_ref_n(v_inst_274_, 3);
v___f_282_ = lean_alloc_closure((void*)(l_Lean_Linter_findMatchingDecl_x3f___redArg___lam__3), 8, 5);
lean_closure_set(v___f_282_, 0, v_val_281_);
lean_closure_set(v___f_282_, 1, v_toPure_273_);
lean_closure_set(v___f_282_, 2, v_inst_274_);
lean_closure_set(v___f_282_, 3, v_inst_275_);
lean_closure_set(v___f_282_, 4, v_toBind_276_);
v___f_283_ = lean_alloc_closure((void*)(l_Lean_Linter_findMatchingDecl_x3f___redArg___lam__4), 6, 4);
lean_closure_set(v___f_283_, 0, v_inst_274_);
lean_closure_set(v___f_283_, 1, v___f_282_);
lean_closure_set(v___f_283_, 2, v_toBind_276_);
lean_closure_set(v___f_283_, 3, v___f_277_);
v_best_x3f_284_ = lean_box(0);
v___f_285_ = lean_alloc_closure((void*)(l_Lean_Linter_findMatchingDecl_x3f___redArg___lam__5___boxed), 6, 5);
lean_closure_set(v___f_285_, 0, v_inst_274_);
lean_closure_set(v___f_285_, 1, v_best_x3f_284_);
lean_closure_set(v___f_285_, 2, v___f_283_);
lean_closure_set(v___f_285_, 3, v_toBind_276_);
lean_closure_set(v___f_285_, 4, v___f_278_);
v___x_286_ = l_Lean_Elab_getInfoTrees___redArg(v_inst_279_, v_inst_274_);
v___x_287_ = lean_apply_4(v_toBind_276_, lean_box(0), lean_box(0), v___x_286_, v___f_285_);
return v___x_287_;
}
else
{
lean_object* v___x_288_; lean_object* v___x_289_; 
lean_dec(v_____x_280_);
lean_dec_ref(v_inst_279_);
lean_dec(v___f_278_);
lean_dec(v___f_277_);
lean_dec(v_toBind_276_);
lean_dec_ref(v_inst_275_);
lean_dec_ref(v_inst_274_);
v___x_288_ = lean_box(0);
v___x_289_ = lean_apply_2(v_toPure_273_, lean_box(0), v___x_288_);
return v___x_289_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_findMatchingDecl_x3f___redArg(lean_object* v_inst_290_, lean_object* v_inst_291_, lean_object* v_inst_292_, lean_object* v_inst_293_, lean_object* v_stx_294_){
_start:
{
lean_object* v_toApplicative_295_; lean_object* v_toBind_296_; lean_object* v_toPure_297_; lean_object* v___x_298_; lean_object* v___f_299_; lean_object* v___f_300_; lean_object* v___f_301_; lean_object* v___x_302_; 
v_toApplicative_295_ = lean_ctor_get(v_inst_290_, 0);
v_toBind_296_ = lean_ctor_get(v_inst_290_, 1);
lean_inc_n(v_toBind_296_, 2);
v_toPure_297_ = lean_ctor_get(v_toApplicative_295_, 1);
lean_inc_n(v_toPure_297_, 3);
lean_inc_ref(v_inst_290_);
v___x_298_ = l_Lean_Elab_getDeclarationRange_x3f___redArg(v_inst_290_, v_inst_293_, v_stx_294_);
v___f_299_ = lean_alloc_closure((void*)(l_Lean_Linter_findMatchingDecl_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_299_, 0, v_toPure_297_);
v___f_300_ = lean_alloc_closure((void*)(l_Lean_Linter_findMatchingDecl_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_300_, 0, v_toPure_297_);
v___f_301_ = lean_alloc_closure((void*)(l_Lean_Linter_findMatchingDecl_x3f___redArg___lam__6), 8, 7);
lean_closure_set(v___f_301_, 0, v_toPure_297_);
lean_closure_set(v___f_301_, 1, v_inst_290_);
lean_closure_set(v___f_301_, 2, v_inst_292_);
lean_closure_set(v___f_301_, 3, v_toBind_296_);
lean_closure_set(v___f_301_, 4, v___f_300_);
lean_closure_set(v___f_301_, 5, v___f_299_);
lean_closure_set(v___f_301_, 6, v_inst_291_);
v___x_302_ = lean_apply_4(v_toBind_296_, lean_box(0), lean_box(0), v___x_298_, v___f_301_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_findMatchingDecl_x3f___redArg___boxed(lean_object* v_inst_303_, lean_object* v_inst_304_, lean_object* v_inst_305_, lean_object* v_inst_306_, lean_object* v_stx_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l_Lean_Linter_findMatchingDecl_x3f___redArg(v_inst_303_, v_inst_304_, v_inst_305_, v_inst_306_, v_stx_307_);
lean_dec(v_stx_307_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_findMatchingDecl_x3f(lean_object* v_m_309_, lean_object* v_inst_310_, lean_object* v_inst_311_, lean_object* v_inst_312_, lean_object* v_inst_313_, lean_object* v_stx_314_){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = l_Lean_Linter_findMatchingDecl_x3f___redArg(v_inst_310_, v_inst_311_, v_inst_312_, v_inst_313_, v_stx_314_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_findMatchingDecl_x3f___boxed(lean_object* v_m_316_, lean_object* v_inst_317_, lean_object* v_inst_318_, lean_object* v_inst_319_, lean_object* v_inst_320_, lean_object* v_stx_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Lean_Linter_findMatchingDecl_x3f(v_m_316_, v_inst_317_, v_inst_318_, v_inst_319_, v_inst_320_, v_stx_321_);
lean_dec(v_stx_321_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_findCodeQualitySource_x3f___redArg___lam__0(lean_object* v_val_323_, lean_object* v_toPure_324_, lean_object* v_____do__lift_325_){
_start:
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_326_ = l_Lean_Environment_mainModule(v_____do__lift_325_);
v___x_327_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_327_, 0, v___x_326_);
lean_ctor_set(v___x_327_, 1, v_val_323_);
v___x_328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_328_, 0, v___x_327_);
v___x_329_ = lean_apply_2(v_toPure_324_, lean_box(0), v___x_328_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_findCodeQualitySource_x3f___redArg___lam__0___boxed(lean_object* v_val_330_, lean_object* v_toPure_331_, lean_object* v_____do__lift_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Lean_Linter_findCodeQualitySource_x3f___redArg___lam__0(v_val_330_, v_toPure_331_, v_____do__lift_332_);
lean_dec_ref(v_____do__lift_332_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_findCodeQualitySource_x3f___redArg___lam__1(lean_object* v_inst_334_, lean_object* v_toPure_335_, lean_object* v_toBind_336_, lean_object* v_____x_337_){
_start:
{
if (lean_obj_tag(v_____x_337_) == 1)
{
lean_object* v_val_338_; lean_object* v_getEnv_339_; lean_object* v___f_340_; lean_object* v___x_341_; 
v_val_338_ = lean_ctor_get(v_____x_337_, 0);
lean_inc(v_val_338_);
lean_dec_ref_known(v_____x_337_, 1);
v_getEnv_339_ = lean_ctor_get(v_inst_334_, 0);
lean_inc(v_getEnv_339_);
lean_dec_ref(v_inst_334_);
v___f_340_ = lean_alloc_closure((void*)(l_Lean_Linter_findCodeQualitySource_x3f___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_340_, 0, v_val_338_);
lean_closure_set(v___f_340_, 1, v_toPure_335_);
v___x_341_ = lean_apply_4(v_toBind_336_, lean_box(0), lean_box(0), v_getEnv_339_, v___f_340_);
return v___x_341_;
}
else
{
lean_object* v___x_342_; lean_object* v___x_343_; 
lean_dec(v_____x_337_);
lean_dec(v_toBind_336_);
lean_dec_ref(v_inst_334_);
v___x_342_ = lean_box(0);
v___x_343_ = lean_apply_2(v_toPure_335_, lean_box(0), v___x_342_);
return v___x_343_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_findCodeQualitySource_x3f___redArg(lean_object* v_inst_344_, lean_object* v_inst_345_, lean_object* v_inst_346_, lean_object* v_inst_347_, lean_object* v_stx_348_){
_start:
{
lean_object* v_toApplicative_349_; lean_object* v_toBind_350_; lean_object* v_toPure_351_; lean_object* v___x_352_; lean_object* v___f_353_; lean_object* v___x_354_; 
v_toApplicative_349_ = lean_ctor_get(v_inst_344_, 0);
v_toBind_350_ = lean_ctor_get(v_inst_344_, 1);
lean_inc_n(v_toBind_350_, 2);
v_toPure_351_ = lean_ctor_get(v_toApplicative_349_, 1);
lean_inc(v_toPure_351_);
lean_inc_ref(v_inst_346_);
v___x_352_ = l_Lean_Linter_findMatchingDecl_x3f___redArg(v_inst_344_, v_inst_345_, v_inst_346_, v_inst_347_, v_stx_348_);
v___f_353_ = lean_alloc_closure((void*)(l_Lean_Linter_findCodeQualitySource_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_353_, 0, v_inst_346_);
lean_closure_set(v___f_353_, 1, v_toPure_351_);
lean_closure_set(v___f_353_, 2, v_toBind_350_);
v___x_354_ = lean_apply_4(v_toBind_350_, lean_box(0), lean_box(0), v___x_352_, v___f_353_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_findCodeQualitySource_x3f___redArg___boxed(lean_object* v_inst_355_, lean_object* v_inst_356_, lean_object* v_inst_357_, lean_object* v_inst_358_, lean_object* v_stx_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l_Lean_Linter_findCodeQualitySource_x3f___redArg(v_inst_355_, v_inst_356_, v_inst_357_, v_inst_358_, v_stx_359_);
lean_dec(v_stx_359_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_findCodeQualitySource_x3f(lean_object* v_m_361_, lean_object* v_inst_362_, lean_object* v_inst_363_, lean_object* v_inst_364_, lean_object* v_inst_365_, lean_object* v_stx_366_){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = l_Lean_Linter_findCodeQualitySource_x3f___redArg(v_inst_362_, v_inst_363_, v_inst_364_, v_inst_365_, v_stx_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_findCodeQualitySource_x3f___boxed(lean_object* v_m_368_, lean_object* v_inst_369_, lean_object* v_inst_370_, lean_object* v_inst_371_, lean_object* v_inst_372_, lean_object* v_stx_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l_Lean_Linter_findCodeQualitySource_x3f(v_m_368_, v_inst_369_, v_inst_370_, v_inst_371_, v_inst_372_, v_stx_373_);
lean_dec(v_stx_373_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_findCodeQualitySource___redArg___lam__0(lean_object* v_toPure_375_, lean_object* v_____do__lift_376_){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_377_ = l_Lean_Environment_mainModule(v_____do__lift_376_);
v___x_378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_378_, 0, v___x_377_);
v___x_379_ = lean_apply_2(v_toPure_375_, lean_box(0), v___x_378_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_findCodeQualitySource___redArg___lam__0___boxed(lean_object* v_toPure_380_, lean_object* v_____do__lift_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lean_Linter_findCodeQualitySource___redArg___lam__0(v_toPure_380_, v_____do__lift_381_);
lean_dec_ref(v_____do__lift_381_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_findCodeQualitySource___redArg___lam__1(lean_object* v_val_383_, lean_object* v_toPure_384_, lean_object* v_____do__lift_385_){
_start:
{
lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_386_ = l_Lean_Environment_mainModule(v_____do__lift_385_);
v___x_387_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_387_, 0, v___x_386_);
lean_ctor_set(v___x_387_, 1, v_val_383_);
v___x_388_ = lean_apply_2(v_toPure_384_, lean_box(0), v___x_387_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_findCodeQualitySource___redArg___lam__1___boxed(lean_object* v_val_389_, lean_object* v_toPure_390_, lean_object* v_____do__lift_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_Lean_Linter_findCodeQualitySource___redArg___lam__1(v_val_389_, v_toPure_390_, v_____do__lift_391_);
lean_dec_ref(v_____do__lift_391_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_findCodeQualitySource___redArg___lam__2(lean_object* v_inst_393_, lean_object* v_toBind_394_, lean_object* v___f_395_, lean_object* v_toPure_396_, lean_object* v_____do__lift_397_){
_start:
{
if (lean_obj_tag(v_____do__lift_397_) == 0)
{
lean_object* v_getEnv_398_; lean_object* v___x_399_; 
lean_dec(v_toPure_396_);
v_getEnv_398_ = lean_ctor_get(v_inst_393_, 0);
lean_inc(v_getEnv_398_);
lean_dec_ref(v_inst_393_);
v___x_399_ = lean_apply_4(v_toBind_394_, lean_box(0), lean_box(0), v_getEnv_398_, v___f_395_);
return v___x_399_;
}
else
{
lean_object* v_val_400_; lean_object* v_getEnv_401_; lean_object* v___f_402_; lean_object* v___x_403_; 
lean_dec(v___f_395_);
v_val_400_ = lean_ctor_get(v_____do__lift_397_, 0);
lean_inc(v_val_400_);
lean_dec_ref_known(v_____do__lift_397_, 1);
v_getEnv_401_ = lean_ctor_get(v_inst_393_, 0);
lean_inc(v_getEnv_401_);
lean_dec_ref(v_inst_393_);
v___f_402_ = lean_alloc_closure((void*)(l_Lean_Linter_findCodeQualitySource___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_402_, 0, v_val_400_);
lean_closure_set(v___f_402_, 1, v_toPure_396_);
v___x_403_ = lean_apply_4(v_toBind_394_, lean_box(0), lean_box(0), v_getEnv_401_, v___f_402_);
return v___x_403_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_findCodeQualitySource___redArg(lean_object* v_inst_404_, lean_object* v_inst_405_, lean_object* v_inst_406_, lean_object* v_inst_407_, lean_object* v_stx_408_){
_start:
{
lean_object* v_toApplicative_409_; lean_object* v_toBind_410_; lean_object* v_toPure_411_; lean_object* v___x_412_; lean_object* v___f_413_; lean_object* v___f_414_; lean_object* v___x_415_; 
v_toApplicative_409_ = lean_ctor_get(v_inst_404_, 0);
v_toBind_410_ = lean_ctor_get(v_inst_404_, 1);
lean_inc_n(v_toBind_410_, 2);
v_toPure_411_ = lean_ctor_get(v_toApplicative_409_, 1);
lean_inc_n(v_toPure_411_, 2);
lean_inc_ref(v_inst_406_);
v___x_412_ = l_Lean_Linter_findMatchingDecl_x3f___redArg(v_inst_404_, v_inst_405_, v_inst_406_, v_inst_407_, v_stx_408_);
v___f_413_ = lean_alloc_closure((void*)(l_Lean_Linter_findCodeQualitySource___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_413_, 0, v_toPure_411_);
v___f_414_ = lean_alloc_closure((void*)(l_Lean_Linter_findCodeQualitySource___redArg___lam__2), 5, 4);
lean_closure_set(v___f_414_, 0, v_inst_406_);
lean_closure_set(v___f_414_, 1, v_toBind_410_);
lean_closure_set(v___f_414_, 2, v___f_413_);
lean_closure_set(v___f_414_, 3, v_toPure_411_);
v___x_415_ = lean_apply_4(v_toBind_410_, lean_box(0), lean_box(0), v___x_412_, v___f_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_findCodeQualitySource___redArg___boxed(lean_object* v_inst_416_, lean_object* v_inst_417_, lean_object* v_inst_418_, lean_object* v_inst_419_, lean_object* v_stx_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_Lean_Linter_findCodeQualitySource___redArg(v_inst_416_, v_inst_417_, v_inst_418_, v_inst_419_, v_stx_420_);
lean_dec(v_stx_420_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_findCodeQualitySource(lean_object* v_m_422_, lean_object* v_inst_423_, lean_object* v_inst_424_, lean_object* v_inst_425_, lean_object* v_inst_426_, lean_object* v_stx_427_){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = l_Lean_Linter_findCodeQualitySource___redArg(v_inst_423_, v_inst_424_, v_inst_425_, v_inst_426_, v_stx_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_findCodeQualitySource___boxed(lean_object* v_m_429_, lean_object* v_inst_430_, lean_object* v_inst_431_, lean_object* v_inst_432_, lean_object* v_inst_433_, lean_object* v_stx_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l_Lean_Linter_findCodeQualitySource(v_m_429_, v_inst_430_, v_inst_431_, v_inst_432_, v_inst_433_, v_stx_434_);
lean_dec(v_stx_434_);
return v_res_435_;
}
}
lean_object* runtime_initialize_Lean_Server_InfoUtils(uint8_t builtin);
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
res = runtime_initialize_Lean_Server_InfoUtils(builtin);
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
lean_object* initialize_Lean_Server_InfoUtils(uint8_t builtin);
lean_object* initialize_Lean_Linter_Init(uint8_t builtin);
lean_object* initialize_Lean_Elab_Term(uint8_t builtin);
lean_object* initialize_Lean_Linter_CodeQuality_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Linter_Util(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Server_InfoUtils(builtin);
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

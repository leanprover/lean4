// Lean compiler output
// Module: Lean.Data.RArray
// Imports: public import Lean.Meta.DecLevel public import Init.Data.RArray import Init.Omega
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
lean_object* l_Lean_Meta_getDecLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_RArray_0__Lean_RArray_ofFn_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_RArray_0__Lean_RArray_ofFn_go___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_RArray_0__Lean_RArray_ofFn_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_RArray_0__Lean_RArray_ofFn_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RArray_ofFn___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RArray_ofFn___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RArray_ofFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RArray_ofFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RArray_ofArray___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RArray_ofArray___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RArray_ofArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RArray_ofArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_RArray_0__Lean_RArray_toExpr_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_RArray_0__Lean_RArray_toExpr_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_RArray_0__Lean_RArray_toExpr_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_RArray_0__Lean_RArray_toExpr_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_RArray_toExpr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_RArray_toExpr___redArg___closed__0 = (const lean_object*)&l_Lean_RArray_toExpr___redArg___closed__0_value;
static const lean_string_object l_Lean_RArray_toExpr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "RArray"};
static const lean_object* l_Lean_RArray_toExpr___redArg___closed__1 = (const lean_object*)&l_Lean_RArray_toExpr___redArg___closed__1_value;
static const lean_string_object l_Lean_RArray_toExpr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "leaf"};
static const lean_object* l_Lean_RArray_toExpr___redArg___closed__2 = (const lean_object*)&l_Lean_RArray_toExpr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_RArray_toExpr___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_RArray_toExpr___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_RArray_toExpr___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_RArray_toExpr___redArg___closed__3_value_aux_0),((lean_object*)&l_Lean_RArray_toExpr___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(94, 141, 178, 243, 105, 175, 161, 86)}};
static const lean_ctor_object l_Lean_RArray_toExpr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_RArray_toExpr___redArg___closed__3_value_aux_1),((lean_object*)&l_Lean_RArray_toExpr___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(57, 177, 112, 28, 190, 252, 39, 11)}};
static const lean_object* l_Lean_RArray_toExpr___redArg___closed__3 = (const lean_object*)&l_Lean_RArray_toExpr___redArg___closed__3_value;
static const lean_string_object l_Lean_RArray_toExpr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "branch"};
static const lean_object* l_Lean_RArray_toExpr___redArg___closed__4 = (const lean_object*)&l_Lean_RArray_toExpr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_RArray_toExpr___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_RArray_toExpr___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_RArray_toExpr___redArg___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_RArray_toExpr___redArg___closed__5_value_aux_0),((lean_object*)&l_Lean_RArray_toExpr___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(94, 141, 178, 243, 105, 175, 161, 86)}};
static const lean_ctor_object l_Lean_RArray_toExpr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_RArray_toExpr___redArg___closed__5_value_aux_1),((lean_object*)&l_Lean_RArray_toExpr___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(175, 39, 200, 249, 3, 45, 189, 78)}};
static const lean_object* l_Lean_RArray_toExpr___redArg___closed__5 = (const lean_object*)&l_Lean_RArray_toExpr___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_RArray_toExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RArray_toExpr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RArray_toExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RArray_toExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_RArray_0__Lean_RArray_ofFn_go___redArg(lean_object* v_f_1_, lean_object* v_lb_2_, lean_object* v_ub_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; uint8_t v___x_6_; 
v___x_4_ = lean_unsigned_to_nat(1u);
v___x_5_ = lean_nat_add(v_lb_2_, v___x_4_);
v___x_6_ = lean_nat_dec_eq(v___x_5_, v_ub_3_);
lean_dec(v___x_5_);
if (v___x_6_ == 0)
{
lean_object* v___x_7_; lean_object* v_mid_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_7_ = lean_nat_add(v_lb_2_, v_ub_3_);
v_mid_8_ = lean_nat_shiftr(v___x_7_, v___x_4_);
lean_dec(v___x_7_);
lean_inc(v_f_1_);
v___x_9_ = l___private_Lean_Data_RArray_0__Lean_RArray_ofFn_go___redArg(v_f_1_, v_lb_2_, v_mid_8_);
lean_inc(v_mid_8_);
v___x_10_ = l___private_Lean_Data_RArray_0__Lean_RArray_ofFn_go___redArg(v_f_1_, v_mid_8_, v_ub_3_);
v___x_11_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_11_, 0, v_mid_8_);
lean_ctor_set(v___x_11_, 1, v___x_9_);
lean_ctor_set(v___x_11_, 2, v___x_10_);
return v___x_11_;
}
else
{
lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_12_ = lean_apply_1(v_f_1_, v_lb_2_);
v___x_13_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_13_, 0, v___x_12_);
return v___x_13_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RArray_0__Lean_RArray_ofFn_go___redArg___boxed(lean_object* v_f_14_, lean_object* v_lb_15_, lean_object* v_ub_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l___private_Lean_Data_RArray_0__Lean_RArray_ofFn_go___redArg(v_f_14_, v_lb_15_, v_ub_16_);
lean_dec(v_ub_16_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RArray_0__Lean_RArray_ofFn_go(lean_object* v_00_u03b1_18_, lean_object* v_n_19_, lean_object* v_f_20_, lean_object* v_lb_21_, lean_object* v_ub_22_, lean_object* v_h1_23_, lean_object* v_h2_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = l___private_Lean_Data_RArray_0__Lean_RArray_ofFn_go___redArg(v_f_20_, v_lb_21_, v_ub_22_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RArray_0__Lean_RArray_ofFn_go___boxed(lean_object* v_00_u03b1_26_, lean_object* v_n_27_, lean_object* v_f_28_, lean_object* v_lb_29_, lean_object* v_ub_30_, lean_object* v_h1_31_, lean_object* v_h2_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l___private_Lean_Data_RArray_0__Lean_RArray_ofFn_go(v_00_u03b1_26_, v_n_27_, v_f_28_, v_lb_29_, v_ub_30_, v_h1_31_, v_h2_32_);
lean_dec(v_ub_30_);
lean_dec(v_n_27_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_ofFn___redArg(lean_object* v_n_34_, lean_object* v_f_35_){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_36_ = lean_unsigned_to_nat(0u);
v___x_37_ = l___private_Lean_Data_RArray_0__Lean_RArray_ofFn_go___redArg(v_f_35_, v___x_36_, v_n_34_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_ofFn___redArg___boxed(lean_object* v_n_38_, lean_object* v_f_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_RArray_ofFn___redArg(v_n_38_, v_f_39_);
lean_dec(v_n_38_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_ofFn(lean_object* v_00_u03b1_41_, lean_object* v_n_42_, lean_object* v_f_43_, lean_object* v_h_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l_Lean_RArray_ofFn___redArg(v_n_42_, v_f_43_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_ofFn___boxed(lean_object* v_00_u03b1_46_, lean_object* v_n_47_, lean_object* v_f_48_, lean_object* v_h_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Lean_RArray_ofFn(v_00_u03b1_46_, v_n_47_, v_f_48_, v_h_49_);
lean_dec(v_n_47_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_ofArray___redArg___lam__0(lean_object* v_xs_51_, lean_object* v_x_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = lean_array_fget_borrowed(v_xs_51_, v_x_52_);
lean_inc(v___x_53_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_ofArray___redArg___lam__0___boxed(lean_object* v_xs_54_, lean_object* v_x_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lean_RArray_ofArray___redArg___lam__0(v_xs_54_, v_x_55_);
lean_dec(v_x_55_);
lean_dec_ref(v_xs_54_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_ofArray___redArg(lean_object* v_xs_57_){
_start:
{
lean_object* v___f_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
lean_inc_ref(v_xs_57_);
v___f_58_ = lean_alloc_closure((void*)(l_Lean_RArray_ofArray___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_58_, 0, v_xs_57_);
v___x_59_ = lean_array_get_size(v_xs_57_);
lean_dec_ref(v_xs_57_);
v___x_60_ = l_Lean_RArray_ofFn___redArg(v___x_59_, v___f_58_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_ofArray(lean_object* v_00_u03b1_61_, lean_object* v_xs_62_, lean_object* v_h_63_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = l_Lean_RArray_ofArray___redArg(v_xs_62_);
return v___x_64_;
}
}
lean_object* l___private_Lean_Data_RArray_0__Lean_RArray_toExpr_go___redArg(lean_object* v_ty_65_, lean_object* v_f_66_, lean_object* v_leaf_67_, lean_object* v_branch_68_, lean_object* v_a_69_){
_start:
{
if (lean_obj_tag(v_a_69_) == 0)
{
lean_object* v_a_71_; lean_object* v___x_73_; uint8_t v_isShared_74_; uint8_t v_isSharedCheck_80_; 
lean_dec_ref(v_branch_68_);
v_a_71_ = lean_ctor_get(v_a_69_, 0);
v_isSharedCheck_80_ = !lean_is_exclusive(v_a_69_);
if (v_isSharedCheck_80_ == 0)
{
v___x_73_ = v_a_69_;
v_isShared_74_ = v_isSharedCheck_80_;
goto v_resetjp_72_;
}
else
{
lean_inc(v_a_71_);
lean_dec(v_a_69_);
v___x_73_ = lean_box(0);
v_isShared_74_ = v_isSharedCheck_80_;
goto v_resetjp_72_;
}
v_resetjp_72_:
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_78_; 
v___x_75_ = lean_apply_1(v_f_66_, v_a_71_);
v___x_76_ = l_Lean_mkAppB(v_leaf_67_, v_ty_65_, v___x_75_);
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 0, v___x_76_);
v___x_78_ = v___x_73_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v___x_76_);
v___x_78_ = v_reuseFailAlloc_79_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
return v___x_78_;
}
}
}
else
{
lean_object* v_a_81_; lean_object* v_a_82_; lean_object* v_a_83_; lean_object* v___x_84_; lean_object* v_a_85_; lean_object* v___x_86_; lean_object* v_a_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_96_; 
v_a_81_ = lean_ctor_get(v_a_69_, 0);
lean_inc(v_a_81_);
v_a_82_ = lean_ctor_get(v_a_69_, 1);
lean_inc_ref(v_a_82_);
v_a_83_ = lean_ctor_get(v_a_69_, 2);
lean_inc_ref(v_a_83_);
lean_dec_ref_known(v_a_69_, 3);
lean_inc_ref_n(v_branch_68_, 2);
lean_inc_ref(v_leaf_67_);
lean_inc_ref(v_f_66_);
lean_inc_ref_n(v_ty_65_, 2);
v___x_84_ = l___private_Lean_Data_RArray_0__Lean_RArray_toExpr_go___redArg(v_ty_65_, v_f_66_, v_leaf_67_, v_branch_68_, v_a_82_);
v_a_85_ = lean_ctor_get(v___x_84_, 0);
lean_inc(v_a_85_);
lean_dec_ref(v___x_84_);
v___x_86_ = l___private_Lean_Data_RArray_0__Lean_RArray_toExpr_go___redArg(v_ty_65_, v_f_66_, v_leaf_67_, v_branch_68_, v_a_83_);
v_a_87_ = lean_ctor_get(v___x_86_, 0);
v_isSharedCheck_96_ = !lean_is_exclusive(v___x_86_);
if (v_isSharedCheck_96_ == 0)
{
v___x_89_ = v___x_86_;
v_isShared_90_ = v_isSharedCheck_96_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_a_87_);
lean_dec(v___x_86_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_96_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_94_; 
v___x_91_ = l_Lean_mkRawNatLit(v_a_81_);
v___x_92_ = l_Lean_mkApp4(v_branch_68_, v_ty_65_, v___x_91_, v_a_85_, v_a_87_);
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 0, v___x_92_);
v___x_94_ = v___x_89_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v___x_92_);
v___x_94_ = v_reuseFailAlloc_95_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
return v___x_94_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_RArray_0__Lean_RArray_toExpr_go___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ty_65_ = stack[0].m_obj;
lean_object* v_f_66_ = stack[1].m_obj;
lean_object* v_leaf_67_ = stack[2].m_obj;
lean_object* v_branch_68_ = stack[3].m_obj;
lean_object* v_a_69_ = stack[4].m_obj;
lean_object* v_res_97_;
v_res_97_ = l___private_Lean_Data_RArray_0__Lean_RArray_toExpr_go___redArg(v_ty_65_, v_f_66_, v_leaf_67_, v_branch_68_, v_a_69_);
stack->m_obj
 = v_res_97_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RArray_0__Lean_RArray_toExpr_go___redArg___boxed(lean_object* v_ty_98_, lean_object* v_f_99_, lean_object* v_leaf_100_, lean_object* v_branch_101_, lean_object* v_a_102_, lean_object* v_a_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l___private_Lean_Data_RArray_0__Lean_RArray_toExpr_go___redArg(v_ty_98_, v_f_99_, v_leaf_100_, v_branch_101_, v_a_102_);
return v_res_104_;
}
}
lean_object* l___private_Lean_Data_RArray_0__Lean_RArray_toExpr_go(lean_object* v_00_u03b1_105_, lean_object* v_ty_106_, lean_object* v_f_107_, lean_object* v_leaf_108_, lean_object* v_branch_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = l___private_Lean_Data_RArray_0__Lean_RArray_toExpr_go___redArg(v_ty_106_, v_f_107_, v_leaf_108_, v_branch_109_, v_a_110_);
return v___x_116_;
}
}
LEAN_EXPORT void l___private_Lean_Data_RArray_0__Lean_RArray_toExpr_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_ty_106_ = stack[1].m_obj;
lean_object* v_f_107_ = stack[2].m_obj;
lean_object* v_leaf_108_ = stack[3].m_obj;
lean_object* v_branch_109_ = stack[4].m_obj;
lean_object* v_a_110_ = stack[5].m_obj;
lean_object* v_a_111_ = stack[6].m_obj;
lean_object* v_a_112_ = stack[7].m_obj;
lean_object* v_a_113_ = stack[8].m_obj;
lean_object* v_a_114_ = stack[9].m_obj;
lean_object* v_res_117_;
v_res_117_ = l___private_Lean_Data_RArray_0__Lean_RArray_toExpr_go(lean_box(0), v_ty_106_, v_f_107_, v_leaf_108_, v_branch_109_, v_a_110_, v_a_111_, v_a_112_, v_a_113_, v_a_114_);
stack->m_obj
 = v_res_117_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RArray_0__Lean_RArray_toExpr_go___boxed(lean_object* v_00_u03b1_118_, lean_object* v_ty_119_, lean_object* v_f_120_, lean_object* v_leaf_121_, lean_object* v_branch_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l___private_Lean_Data_RArray_0__Lean_RArray_toExpr_go(v_00_u03b1_118_, v_ty_119_, v_f_120_, v_leaf_121_, v_branch_122_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_);
lean_dec(v_a_127_);
lean_dec_ref(v_a_126_);
lean_dec(v_a_125_);
lean_dec_ref(v_a_124_);
return v_res_129_;
}
}
lean_object* l_Lean_RArray_toExpr___redArg(lean_object* v_ty_142_, lean_object* v_f_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_){
_start:
{
lean_object* v___x_150_; 
lean_inc_ref(v_ty_142_);
v___x_150_ = l_Lean_Meta_getDecLevel(v_ty_142_, v_a_145_, v_a_146_, v_a_147_, v_a_148_);
if (lean_obj_tag(v___x_150_) == 0)
{
lean_object* v_a_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v_a_151_ = lean_ctor_get(v___x_150_, 0);
lean_inc(v_a_151_);
lean_dec_ref_known(v___x_150_, 1);
v___x_152_ = ((lean_object*)(l_Lean_RArray_toExpr___redArg___closed__3));
v___x_153_ = lean_box(0);
v___x_154_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_154_, 0, v_a_151_);
lean_ctor_set(v___x_154_, 1, v___x_153_);
lean_inc_ref(v___x_154_);
v___x_155_ = l_Lean_mkConst(v___x_152_, v___x_154_);
v___x_156_ = ((lean_object*)(l_Lean_RArray_toExpr___redArg___closed__5));
v___x_157_ = l_Lean_mkConst(v___x_156_, v___x_154_);
v___x_158_ = l___private_Lean_Data_RArray_0__Lean_RArray_toExpr_go___redArg(v_ty_142_, v_f_143_, v___x_155_, v___x_157_, v_a_144_);
return v___x_158_;
}
else
{
lean_object* v_a_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_166_; 
lean_dec_ref(v_a_144_);
lean_dec_ref(v_f_143_);
lean_dec_ref(v_ty_142_);
v_a_159_ = lean_ctor_get(v___x_150_, 0);
v_isSharedCheck_166_ = !lean_is_exclusive(v___x_150_);
if (v_isSharedCheck_166_ == 0)
{
v___x_161_ = v___x_150_;
v_isShared_162_ = v_isSharedCheck_166_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_a_159_);
lean_dec(v___x_150_);
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
v_reuseFailAlloc_165_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT void l_Lean_RArray_toExpr___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ty_142_ = stack[0].m_obj;
lean_object* v_f_143_ = stack[1].m_obj;
lean_object* v_a_144_ = stack[2].m_obj;
lean_object* v_a_145_ = stack[3].m_obj;
lean_object* v_a_146_ = stack[4].m_obj;
lean_object* v_a_147_ = stack[5].m_obj;
lean_object* v_a_148_ = stack[6].m_obj;
lean_object* v_res_167_;
v_res_167_ = l_Lean_RArray_toExpr___redArg(v_ty_142_, v_f_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_);
stack->m_obj
 = v_res_167_;
}
LEAN_EXPORT lean_object* l_Lean_RArray_toExpr___redArg___boxed(lean_object* v_ty_168_, lean_object* v_f_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Lean_RArray_toExpr___redArg(v_ty_168_, v_f_169_, v_a_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_);
lean_dec(v_a_174_);
lean_dec_ref(v_a_173_);
lean_dec(v_a_172_);
lean_dec_ref(v_a_171_);
return v_res_176_;
}
}
lean_object* l_Lean_RArray_toExpr(lean_object* v_00_u03b1_177_, lean_object* v_ty_178_, lean_object* v_f_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = l_Lean_RArray_toExpr___redArg(v_ty_178_, v_f_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_, v_a_184_);
return v___x_186_;
}
}
LEAN_EXPORT void l_Lean_RArray_toExpr_0interp(lean_interpreter_value* stack)
{
lean_object* v_ty_178_ = stack[1].m_obj;
lean_object* v_f_179_ = stack[2].m_obj;
lean_object* v_a_180_ = stack[3].m_obj;
lean_object* v_a_181_ = stack[4].m_obj;
lean_object* v_a_182_ = stack[5].m_obj;
lean_object* v_a_183_ = stack[6].m_obj;
lean_object* v_a_184_ = stack[7].m_obj;
lean_object* v_res_187_;
v_res_187_ = l_Lean_RArray_toExpr(lean_box(0), v_ty_178_, v_f_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_, v_a_184_);
stack->m_obj
 = v_res_187_;
}
LEAN_EXPORT lean_object* l_Lean_RArray_toExpr___boxed(lean_object* v_00_u03b1_188_, lean_object* v_ty_189_, lean_object* v_f_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Lean_RArray_toExpr(v_00_u03b1_188_, v_ty_189_, v_f_190_, v_a_191_, v_a_192_, v_a_193_, v_a_194_, v_a_195_);
lean_dec(v_a_195_);
lean_dec_ref(v_a_194_);
lean_dec(v_a_193_);
lean_dec_ref(v_a_192_);
return v_res_197_;
}
}
lean_object* runtime_initialize_Lean_Meta_DecLevel(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_RArray(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_RArray(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_DecLevel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_RArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_RArray(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_DecLevel(uint8_t builtin);
lean_object* initialize_Init_Data_RArray(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_RArray(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_DecLevel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_RArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_RArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_RArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_RArray(builtin);
}
#ifdef __cplusplus
}
#endif

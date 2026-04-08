// Lean compiler output
// Module: Lean.Compiler.LCNF.Renaming
// Imports: public import Lean.Compiler.LCNF.CompilerM
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
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_addLetDecl(uint8_t, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_addParam(uint8_t, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_addFunDecl(uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Param_applyRenaming_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Param_applyRenaming_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_applyRenaming___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_applyRenaming___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_applyRenaming(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_applyRenaming___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Param_applyRenaming_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Param_applyRenaming_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_applyRenaming___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_applyRenaming___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_applyRenaming(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_applyRenaming___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__1___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_applyRenaming(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_applyRenaming(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_applyRenaming___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_applyRenaming___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_applyRenaming_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_applyRenaming_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_applyRenaming_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_applyRenaming_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_applyRenaming___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_applyRenaming___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_applyRenaming(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_applyRenaming___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Param_applyRenaming_spec__0___redArg(lean_object* v_t_1_, lean_object* v_k_2_){
_start:
{
if (lean_obj_tag(v_t_1_) == 0)
{
lean_object* v_k_3_; lean_object* v_v_4_; lean_object* v_l_5_; lean_object* v_r_6_; uint8_t v___x_7_; 
v_k_3_ = lean_ctor_get(v_t_1_, 1);
v_v_4_ = lean_ctor_get(v_t_1_, 2);
v_l_5_ = lean_ctor_get(v_t_1_, 3);
v_r_6_ = lean_ctor_get(v_t_1_, 4);
v___x_7_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2_, v_k_3_);
switch(v___x_7_)
{
case 0:
{
v_t_1_ = v_l_5_;
goto _start;
}
case 1:
{
lean_object* v___x_9_; 
lean_inc(v_v_4_);
v___x_9_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_9_, 0, v_v_4_);
return v___x_9_;
}
default: 
{
v_t_1_ = v_r_6_;
goto _start;
}
}
}
else
{
lean_object* v___x_11_; 
v___x_11_ = lean_box(0);
return v___x_11_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Param_applyRenaming_spec__0___redArg___boxed(lean_object* v_t_12_, lean_object* v_k_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Param_applyRenaming_spec__0___redArg(v_t_12_, v_k_13_);
lean_dec(v_k_13_);
lean_dec(v_t_12_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_applyRenaming___redArg(uint8_t v_pu_15_, lean_object* v_param_16_, lean_object* v_r_17_, lean_object* v_a_18_){
_start:
{
lean_object* v_fvarId_20_; lean_object* v_type_21_; uint8_t v_borrow_22_; lean_object* v___x_23_; 
v_fvarId_20_ = lean_ctor_get(v_param_16_, 0);
v_type_21_ = lean_ctor_get(v_param_16_, 2);
v_borrow_22_ = lean_ctor_get_uint8(v_param_16_, sizeof(void*)*3);
v___x_23_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Param_applyRenaming_spec__0___redArg(v_r_17_, v_fvarId_20_);
if (lean_obj_tag(v___x_23_) == 1)
{
lean_object* v___x_25_; uint8_t v_isShared_26_; uint8_t v_isSharedCheck_50_; 
lean_inc_ref(v_type_21_);
lean_inc(v_fvarId_20_);
v_isSharedCheck_50_ = !lean_is_exclusive(v_param_16_);
if (v_isSharedCheck_50_ == 0)
{
lean_object* v_unused_51_; lean_object* v_unused_52_; lean_object* v_unused_53_; 
v_unused_51_ = lean_ctor_get(v_param_16_, 2);
lean_dec(v_unused_51_);
v_unused_52_ = lean_ctor_get(v_param_16_, 1);
lean_dec(v_unused_52_);
v_unused_53_ = lean_ctor_get(v_param_16_, 0);
lean_dec(v_unused_53_);
v___x_25_ = v_param_16_;
v_isShared_26_ = v_isSharedCheck_50_;
goto v_resetjp_24_;
}
else
{
lean_dec(v_param_16_);
v___x_25_ = lean_box(0);
v_isShared_26_ = v_isSharedCheck_50_;
goto v_resetjp_24_;
}
v_resetjp_24_:
{
lean_object* v_val_27_; lean_object* v___x_29_; uint8_t v_isShared_30_; uint8_t v_isSharedCheck_49_; 
v_val_27_ = lean_ctor_get(v___x_23_, 0);
v_isSharedCheck_49_ = !lean_is_exclusive(v___x_23_);
if (v_isSharedCheck_49_ == 0)
{
v___x_29_ = v___x_23_;
v_isShared_30_ = v_isSharedCheck_49_;
goto v_resetjp_28_;
}
else
{
lean_inc(v_val_27_);
lean_dec(v___x_23_);
v___x_29_ = lean_box(0);
v_isShared_30_ = v_isSharedCheck_49_;
goto v_resetjp_28_;
}
v_resetjp_28_:
{
lean_object* v___x_31_; lean_object* v_lctx_32_; lean_object* v_nextIdx_33_; lean_object* v___x_35_; uint8_t v_isShared_36_; uint8_t v_isSharedCheck_48_; 
v___x_31_ = lean_st_ref_take(v_a_18_);
v_lctx_32_ = lean_ctor_get(v___x_31_, 0);
v_nextIdx_33_ = lean_ctor_get(v___x_31_, 1);
v_isSharedCheck_48_ = !lean_is_exclusive(v___x_31_);
if (v_isSharedCheck_48_ == 0)
{
v___x_35_ = v___x_31_;
v_isShared_36_ = v_isSharedCheck_48_;
goto v_resetjp_34_;
}
else
{
lean_inc(v_nextIdx_33_);
lean_inc(v_lctx_32_);
lean_dec(v___x_31_);
v___x_35_ = lean_box(0);
v_isShared_36_ = v_isSharedCheck_48_;
goto v_resetjp_34_;
}
v_resetjp_34_:
{
lean_object* v_param_38_; 
if (v_isShared_26_ == 0)
{
lean_ctor_set(v___x_25_, 1, v_val_27_);
v_param_38_ = v___x_25_;
goto v_reusejp_37_;
}
else
{
lean_object* v_reuseFailAlloc_47_; 
v_reuseFailAlloc_47_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_47_, 0, v_fvarId_20_);
lean_ctor_set(v_reuseFailAlloc_47_, 1, v_val_27_);
lean_ctor_set(v_reuseFailAlloc_47_, 2, v_type_21_);
lean_ctor_set_uint8(v_reuseFailAlloc_47_, sizeof(void*)*3, v_borrow_22_);
v_param_38_ = v_reuseFailAlloc_47_;
goto v_reusejp_37_;
}
v_reusejp_37_:
{
lean_object* v___x_39_; lean_object* v___x_41_; 
lean_inc_ref(v_param_38_);
v___x_39_ = l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_15_, v_lctx_32_, v_param_38_);
if (v_isShared_36_ == 0)
{
lean_ctor_set(v___x_35_, 0, v___x_39_);
v___x_41_ = v___x_35_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_46_; 
v_reuseFailAlloc_46_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_46_, 0, v___x_39_);
lean_ctor_set(v_reuseFailAlloc_46_, 1, v_nextIdx_33_);
v___x_41_ = v_reuseFailAlloc_46_;
goto v_reusejp_40_;
}
v_reusejp_40_:
{
lean_object* v___x_42_; lean_object* v___x_44_; 
v___x_42_ = lean_st_ref_set(v_a_18_, v___x_41_);
if (v_isShared_30_ == 0)
{
lean_ctor_set_tag(v___x_29_, 0);
lean_ctor_set(v___x_29_, 0, v_param_38_);
v___x_44_ = v___x_29_;
goto v_reusejp_43_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v_param_38_);
v___x_44_ = v_reuseFailAlloc_45_;
goto v_reusejp_43_;
}
v_reusejp_43_:
{
return v___x_44_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_54_; 
lean_dec(v___x_23_);
v___x_54_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_54_, 0, v_param_16_);
return v___x_54_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_applyRenaming___redArg___boxed(lean_object* v_pu_55_, lean_object* v_param_56_, lean_object* v_r_57_, lean_object* v_a_58_, lean_object* v_a_59_){
_start:
{
uint8_t v_pu_boxed_60_; lean_object* v_res_61_; 
v_pu_boxed_60_ = lean_unbox(v_pu_55_);
v_res_61_ = l_Lean_Compiler_LCNF_Param_applyRenaming___redArg(v_pu_boxed_60_, v_param_56_, v_r_57_, v_a_58_);
lean_dec(v_a_58_);
lean_dec(v_r_57_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_applyRenaming(uint8_t v_pu_62_, lean_object* v_param_63_, lean_object* v_r_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = l_Lean_Compiler_LCNF_Param_applyRenaming___redArg(v_pu_62_, v_param_63_, v_r_64_, v_a_66_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_applyRenaming___boxed(lean_object* v_pu_71_, lean_object* v_param_72_, lean_object* v_r_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_, lean_object* v_a_78_){
_start:
{
uint8_t v_pu_boxed_79_; lean_object* v_res_80_; 
v_pu_boxed_79_ = lean_unbox(v_pu_71_);
v_res_80_ = l_Lean_Compiler_LCNF_Param_applyRenaming(v_pu_boxed_79_, v_param_72_, v_r_73_, v_a_74_, v_a_75_, v_a_76_, v_a_77_);
lean_dec(v_a_77_);
lean_dec_ref(v_a_76_);
lean_dec(v_a_75_);
lean_dec_ref(v_a_74_);
lean_dec(v_r_73_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Param_applyRenaming_spec__0(lean_object* v_00_u03b4_81_, lean_object* v_t_82_, lean_object* v_k_83_){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Param_applyRenaming_spec__0___redArg(v_t_82_, v_k_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Param_applyRenaming_spec__0___boxed(lean_object* v_00_u03b4_85_, lean_object* v_t_86_, lean_object* v_k_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Param_applyRenaming_spec__0(v_00_u03b4_85_, v_t_86_, v_k_87_);
lean_dec(v_k_87_);
lean_dec(v_t_86_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_applyRenaming___redArg(uint8_t v_pu_89_, lean_object* v_decl_90_, lean_object* v_r_91_, lean_object* v_a_92_){
_start:
{
lean_object* v_fvarId_94_; lean_object* v_type_95_; lean_object* v_value_96_; lean_object* v___x_97_; 
v_fvarId_94_ = lean_ctor_get(v_decl_90_, 0);
v_type_95_ = lean_ctor_get(v_decl_90_, 2);
v_value_96_ = lean_ctor_get(v_decl_90_, 3);
v___x_97_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Param_applyRenaming_spec__0___redArg(v_r_91_, v_fvarId_94_);
if (lean_obj_tag(v___x_97_) == 1)
{
lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_124_; 
lean_inc(v_value_96_);
lean_inc_ref(v_type_95_);
lean_inc(v_fvarId_94_);
v_isSharedCheck_124_ = !lean_is_exclusive(v_decl_90_);
if (v_isSharedCheck_124_ == 0)
{
lean_object* v_unused_125_; lean_object* v_unused_126_; lean_object* v_unused_127_; lean_object* v_unused_128_; 
v_unused_125_ = lean_ctor_get(v_decl_90_, 3);
lean_dec(v_unused_125_);
v_unused_126_ = lean_ctor_get(v_decl_90_, 2);
lean_dec(v_unused_126_);
v_unused_127_ = lean_ctor_get(v_decl_90_, 1);
lean_dec(v_unused_127_);
v_unused_128_ = lean_ctor_get(v_decl_90_, 0);
lean_dec(v_unused_128_);
v___x_99_ = v_decl_90_;
v_isShared_100_ = v_isSharedCheck_124_;
goto v_resetjp_98_;
}
else
{
lean_dec(v_decl_90_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_124_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v_val_101_; lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_123_; 
v_val_101_ = lean_ctor_get(v___x_97_, 0);
v_isSharedCheck_123_ = !lean_is_exclusive(v___x_97_);
if (v_isSharedCheck_123_ == 0)
{
v___x_103_ = v___x_97_;
v_isShared_104_ = v_isSharedCheck_123_;
goto v_resetjp_102_;
}
else
{
lean_inc(v_val_101_);
lean_dec(v___x_97_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_123_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
lean_object* v___x_105_; lean_object* v_lctx_106_; lean_object* v_nextIdx_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_122_; 
v___x_105_ = lean_st_ref_take(v_a_92_);
v_lctx_106_ = lean_ctor_get(v___x_105_, 0);
v_nextIdx_107_ = lean_ctor_get(v___x_105_, 1);
v_isSharedCheck_122_ = !lean_is_exclusive(v___x_105_);
if (v_isSharedCheck_122_ == 0)
{
v___x_109_ = v___x_105_;
v_isShared_110_ = v_isSharedCheck_122_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_nextIdx_107_);
lean_inc(v_lctx_106_);
lean_dec(v___x_105_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_122_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v_decl_112_; 
if (v_isShared_100_ == 0)
{
lean_ctor_set(v___x_99_, 1, v_val_101_);
v_decl_112_ = v___x_99_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v_fvarId_94_);
lean_ctor_set(v_reuseFailAlloc_121_, 1, v_val_101_);
lean_ctor_set(v_reuseFailAlloc_121_, 2, v_type_95_);
lean_ctor_set(v_reuseFailAlloc_121_, 3, v_value_96_);
v_decl_112_ = v_reuseFailAlloc_121_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
lean_object* v___x_113_; lean_object* v___x_115_; 
lean_inc_ref(v_decl_112_);
v___x_113_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v_pu_89_, v_lctx_106_, v_decl_112_);
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 0, v___x_113_);
v___x_115_ = v___x_109_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v___x_113_);
lean_ctor_set(v_reuseFailAlloc_120_, 1, v_nextIdx_107_);
v___x_115_ = v_reuseFailAlloc_120_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
lean_object* v___x_116_; lean_object* v___x_118_; 
v___x_116_ = lean_st_ref_set(v_a_92_, v___x_115_);
if (v_isShared_104_ == 0)
{
lean_ctor_set_tag(v___x_103_, 0);
lean_ctor_set(v___x_103_, 0, v_decl_112_);
v___x_118_ = v___x_103_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v_decl_112_);
v___x_118_ = v_reuseFailAlloc_119_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
return v___x_118_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_129_; 
lean_dec(v___x_97_);
v___x_129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_129_, 0, v_decl_90_);
return v___x_129_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_applyRenaming___redArg___boxed(lean_object* v_pu_130_, lean_object* v_decl_131_, lean_object* v_r_132_, lean_object* v_a_133_, lean_object* v_a_134_){
_start:
{
uint8_t v_pu_boxed_135_; lean_object* v_res_136_; 
v_pu_boxed_135_ = lean_unbox(v_pu_130_);
v_res_136_ = l_Lean_Compiler_LCNF_LetDecl_applyRenaming___redArg(v_pu_boxed_135_, v_decl_131_, v_r_132_, v_a_133_);
lean_dec(v_a_133_);
lean_dec(v_r_132_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_applyRenaming(uint8_t v_pu_137_, lean_object* v_decl_138_, lean_object* v_r_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_){
_start:
{
lean_object* v___x_145_; 
v___x_145_ = l_Lean_Compiler_LCNF_LetDecl_applyRenaming___redArg(v_pu_137_, v_decl_138_, v_r_139_, v_a_141_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_applyRenaming___boxed(lean_object* v_pu_146_, lean_object* v_decl_147_, lean_object* v_r_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_){
_start:
{
uint8_t v_pu_boxed_154_; lean_object* v_res_155_; 
v_pu_boxed_154_ = lean_unbox(v_pu_146_);
v_res_155_ = l_Lean_Compiler_LCNF_LetDecl_applyRenaming(v_pu_boxed_154_, v_decl_147_, v_r_148_, v_a_149_, v_a_150_, v_a_151_, v_a_152_);
lean_dec(v_a_152_);
lean_dec_ref(v_a_151_);
lean_dec(v_a_150_);
lean_dec_ref(v_a_149_);
lean_dec(v_r_148_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__1___redArg(uint8_t v_pu_156_, lean_object* v_r_157_, lean_object* v_i_158_, lean_object* v_as_159_, lean_object* v___y_160_){
_start:
{
lean_object* v___x_162_; uint8_t v___x_163_; 
v___x_162_ = lean_array_get_size(v_as_159_);
v___x_163_ = lean_nat_dec_lt(v_i_158_, v___x_162_);
if (v___x_163_ == 0)
{
lean_object* v___x_164_; 
lean_dec(v_i_158_);
v___x_164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_164_, 0, v_as_159_);
return v___x_164_;
}
else
{
lean_object* v_a_165_; lean_object* v___x_166_; 
v_a_165_ = lean_array_fget_borrowed(v_as_159_, v_i_158_);
lean_inc(v_a_165_);
v___x_166_ = l_Lean_Compiler_LCNF_Param_applyRenaming___redArg(v_pu_156_, v_a_165_, v_r_157_, v___y_160_);
if (lean_obj_tag(v___x_166_) == 0)
{
lean_object* v_a_167_; size_t v___x_168_; size_t v___x_169_; uint8_t v___x_170_; 
v_a_167_ = lean_ctor_get(v___x_166_, 0);
lean_inc(v_a_167_);
lean_dec_ref(v___x_166_);
v___x_168_ = lean_ptr_addr(v_a_165_);
v___x_169_ = lean_ptr_addr(v_a_167_);
v___x_170_ = lean_usize_dec_eq(v___x_168_, v___x_169_);
if (v___x_170_ == 0)
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_171_ = lean_unsigned_to_nat(1u);
v___x_172_ = lean_nat_add(v_i_158_, v___x_171_);
v___x_173_ = lean_array_fset(v_as_159_, v_i_158_, v_a_167_);
lean_dec(v_i_158_);
v_i_158_ = v___x_172_;
v_as_159_ = v___x_173_;
goto _start;
}
else
{
lean_object* v___x_175_; lean_object* v___x_176_; 
lean_dec(v_a_167_);
v___x_175_ = lean_unsigned_to_nat(1u);
v___x_176_ = lean_nat_add(v_i_158_, v___x_175_);
lean_dec(v_i_158_);
v_i_158_ = v___x_176_;
goto _start;
}
}
else
{
lean_object* v_a_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_185_; 
lean_dec_ref(v_as_159_);
lean_dec(v_i_158_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__1___redArg___boxed(lean_object* v_pu_186_, lean_object* v_r_187_, lean_object* v_i_188_, lean_object* v_as_189_, lean_object* v___y_190_, lean_object* v___y_191_){
_start:
{
uint8_t v_pu_boxed_192_; lean_object* v_res_193_; 
v_pu_boxed_192_ = lean_unbox(v_pu_186_);
v_res_193_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__1___redArg(v_pu_boxed_192_, v_r_187_, v_i_188_, v_as_189_, v___y_190_);
lean_dec(v___y_190_);
lean_dec(v_r_187_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__2(uint8_t v_pu_194_, lean_object* v_r_195_, lean_object* v_i_196_, lean_object* v_as_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_){
_start:
{
lean_object* v___x_203_; uint8_t v___x_204_; 
v___x_203_ = lean_array_get_size(v_as_197_);
v___x_204_ = lean_nat_dec_lt(v_i_196_, v___x_203_);
if (v___x_204_ == 0)
{
lean_object* v___x_205_; 
lean_dec(v_i_196_);
v___x_205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_205_, 0, v_as_197_);
return v___x_205_;
}
else
{
lean_object* v_a_206_; lean_object* v_a_208_; 
v_a_206_ = lean_array_fget_borrowed(v_as_197_, v_i_196_);
switch(lean_obj_tag(v_a_206_))
{
case 0:
{
lean_object* v_params_219_; lean_object* v_code_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v_params_219_ = lean_ctor_get(v_a_206_, 1);
v_code_220_ = lean_ctor_get(v_a_206_, 2);
v___x_221_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_params_219_);
v___x_222_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__1___redArg(v_pu_194_, v_r_195_, v___x_221_, v_params_219_, v___y_199_);
if (lean_obj_tag(v___x_222_) == 0)
{
lean_object* v_a_223_; lean_object* v___x_224_; 
v_a_223_ = lean_ctor_get(v___x_222_, 0);
lean_inc(v_a_223_);
lean_dec_ref(v___x_222_);
lean_inc_ref(v_code_220_);
v___x_224_ = l_Lean_Compiler_LCNF_Code_applyRenaming(v_pu_194_, v_code_220_, v_r_195_, v___y_198_, v___y_199_, v___y_200_, v___y_201_);
if (lean_obj_tag(v___x_224_) == 0)
{
lean_object* v_a_225_; lean_object* v___x_226_; 
v_a_225_ = lean_ctor_get(v___x_224_, 0);
lean_inc(v_a_225_);
lean_dec_ref(v___x_224_);
lean_inc_ref(v_a_206_);
v___x_226_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp(v_pu_194_, v_a_206_, v_a_223_, v_a_225_);
v_a_208_ = v___x_226_;
goto v___jp_207_;
}
else
{
lean_object* v_a_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_234_; 
lean_dec(v_a_223_);
lean_dec_ref(v_as_197_);
lean_dec(v_i_196_);
v_a_227_ = lean_ctor_get(v___x_224_, 0);
v_isSharedCheck_234_ = !lean_is_exclusive(v___x_224_);
if (v_isSharedCheck_234_ == 0)
{
v___x_229_ = v___x_224_;
v_isShared_230_ = v_isSharedCheck_234_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_a_227_);
lean_dec(v___x_224_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_234_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v___x_232_; 
if (v_isShared_230_ == 0)
{
v___x_232_ = v___x_229_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v_a_227_);
v___x_232_ = v_reuseFailAlloc_233_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
return v___x_232_;
}
}
}
}
else
{
lean_object* v_a_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_242_; 
lean_dec_ref(v_as_197_);
lean_dec(v_i_196_);
v_a_235_ = lean_ctor_get(v___x_222_, 0);
v_isSharedCheck_242_ = !lean_is_exclusive(v___x_222_);
if (v_isSharedCheck_242_ == 0)
{
v___x_237_ = v___x_222_;
v_isShared_238_ = v_isSharedCheck_242_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_a_235_);
lean_dec(v___x_222_);
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
case 1:
{
lean_object* v_code_243_; lean_object* v___x_244_; 
v_code_243_ = lean_ctor_get(v_a_206_, 1);
lean_inc_ref(v_code_243_);
v___x_244_ = l_Lean_Compiler_LCNF_Code_applyRenaming(v_pu_194_, v_code_243_, v_r_195_, v___y_198_, v___y_199_, v___y_200_, v___y_201_);
if (lean_obj_tag(v___x_244_) == 0)
{
lean_object* v_a_245_; lean_object* v___x_246_; 
v_a_245_ = lean_ctor_get(v___x_244_, 0);
lean_inc(v_a_245_);
lean_dec_ref(v___x_244_);
lean_inc_ref(v_a_206_);
v___x_246_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_206_, v_a_245_);
v_a_208_ = v___x_246_;
goto v___jp_207_;
}
else
{
lean_object* v_a_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_254_; 
lean_dec_ref(v_as_197_);
lean_dec(v_i_196_);
v_a_247_ = lean_ctor_get(v___x_244_, 0);
v_isSharedCheck_254_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_254_ == 0)
{
v___x_249_ = v___x_244_;
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_a_247_);
lean_dec(v___x_244_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v___x_252_; 
if (v_isShared_250_ == 0)
{
v___x_252_ = v___x_249_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v_a_247_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
return v___x_252_;
}
}
}
}
default: 
{
lean_object* v_code_255_; lean_object* v___x_256_; 
v_code_255_ = lean_ctor_get(v_a_206_, 0);
lean_inc_ref(v_code_255_);
v___x_256_ = l_Lean_Compiler_LCNF_Code_applyRenaming(v_pu_194_, v_code_255_, v_r_195_, v___y_198_, v___y_199_, v___y_200_, v___y_201_);
if (lean_obj_tag(v___x_256_) == 0)
{
lean_object* v_a_257_; lean_object* v___x_258_; 
v_a_257_ = lean_ctor_get(v___x_256_, 0);
lean_inc(v_a_257_);
lean_dec_ref(v___x_256_);
lean_inc_ref(v_a_206_);
v___x_258_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_206_, v_a_257_);
v_a_208_ = v___x_258_;
goto v___jp_207_;
}
else
{
lean_object* v_a_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_266_; 
lean_dec_ref(v_as_197_);
lean_dec(v_i_196_);
v_a_259_ = lean_ctor_get(v___x_256_, 0);
v_isSharedCheck_266_ = !lean_is_exclusive(v___x_256_);
if (v_isSharedCheck_266_ == 0)
{
v___x_261_ = v___x_256_;
v_isShared_262_ = v_isSharedCheck_266_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_a_259_);
lean_dec(v___x_256_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_266_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_264_; 
if (v_isShared_262_ == 0)
{
v___x_264_ = v___x_261_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_a_259_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
}
}
v___jp_207_:
{
size_t v___x_209_; size_t v___x_210_; uint8_t v___x_211_; 
v___x_209_ = lean_ptr_addr(v_a_206_);
v___x_210_ = lean_ptr_addr(v_a_208_);
v___x_211_ = lean_usize_dec_eq(v___x_209_, v___x_210_);
if (v___x_211_ == 0)
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_212_ = lean_unsigned_to_nat(1u);
v___x_213_ = lean_nat_add(v_i_196_, v___x_212_);
v___x_214_ = lean_array_fset(v_as_197_, v_i_196_, v_a_208_);
lean_dec(v_i_196_);
v_i_196_ = v___x_213_;
v_as_197_ = v___x_214_;
goto _start;
}
else
{
lean_object* v___x_216_; lean_object* v___x_217_; 
lean_dec_ref(v_a_208_);
v___x_216_ = lean_unsigned_to_nat(1u);
v___x_217_ = lean_nat_add(v_i_196_, v___x_216_);
lean_dec(v_i_196_);
v_i_196_ = v___x_217_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_applyRenaming(uint8_t v_pu_267_, lean_object* v_code_268_, lean_object* v_r_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_){
_start:
{
switch(lean_obj_tag(v_code_268_))
{
case 0:
{
lean_object* v_decl_275_; lean_object* v_k_276_; lean_object* v___x_277_; 
v_decl_275_ = lean_ctor_get(v_code_268_, 0);
v_k_276_ = lean_ctor_get(v_code_268_, 1);
lean_inc_ref(v_decl_275_);
v___x_277_ = l_Lean_Compiler_LCNF_LetDecl_applyRenaming___redArg(v_pu_267_, v_decl_275_, v_r_269_, v_a_271_);
if (lean_obj_tag(v___x_277_) == 0)
{
lean_object* v_a_278_; lean_object* v___x_279_; 
v_a_278_ = lean_ctor_get(v___x_277_, 0);
lean_inc(v_a_278_);
lean_dec_ref(v___x_277_);
lean_inc_ref(v_k_276_);
v___x_279_ = l_Lean_Compiler_LCNF_Code_applyRenaming(v_pu_267_, v_k_276_, v_r_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_);
if (lean_obj_tag(v___x_279_) == 0)
{
lean_object* v_a_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_307_; 
v_a_280_ = lean_ctor_get(v___x_279_, 0);
v_isSharedCheck_307_ = !lean_is_exclusive(v___x_279_);
if (v_isSharedCheck_307_ == 0)
{
v___x_282_ = v___x_279_;
v_isShared_283_ = v_isSharedCheck_307_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_a_280_);
lean_dec(v___x_279_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_307_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
uint8_t v___y_285_; size_t v___x_301_; size_t v___x_302_; uint8_t v___x_303_; 
v___x_301_ = lean_ptr_addr(v_k_276_);
v___x_302_ = lean_ptr_addr(v_a_280_);
v___x_303_ = lean_usize_dec_eq(v___x_301_, v___x_302_);
if (v___x_303_ == 0)
{
v___y_285_ = v___x_303_;
goto v___jp_284_;
}
else
{
size_t v___x_304_; size_t v___x_305_; uint8_t v___x_306_; 
v___x_304_ = lean_ptr_addr(v_decl_275_);
v___x_305_ = lean_ptr_addr(v_a_278_);
v___x_306_ = lean_usize_dec_eq(v___x_304_, v___x_305_);
v___y_285_ = v___x_306_;
goto v___jp_284_;
}
v___jp_284_:
{
if (v___y_285_ == 0)
{
lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_295_; 
v_isSharedCheck_295_ = !lean_is_exclusive(v_code_268_);
if (v_isSharedCheck_295_ == 0)
{
lean_object* v_unused_296_; lean_object* v_unused_297_; 
v_unused_296_ = lean_ctor_get(v_code_268_, 1);
lean_dec(v_unused_296_);
v_unused_297_ = lean_ctor_get(v_code_268_, 0);
lean_dec(v_unused_297_);
v___x_287_ = v_code_268_;
v_isShared_288_ = v_isSharedCheck_295_;
goto v_resetjp_286_;
}
else
{
lean_dec(v_code_268_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_295_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_290_; 
if (v_isShared_288_ == 0)
{
lean_ctor_set(v___x_287_, 1, v_a_280_);
lean_ctor_set(v___x_287_, 0, v_a_278_);
v___x_290_ = v___x_287_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v_a_278_);
lean_ctor_set(v_reuseFailAlloc_294_, 1, v_a_280_);
v___x_290_ = v_reuseFailAlloc_294_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
lean_object* v___x_292_; 
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 0, v___x_290_);
v___x_292_ = v___x_282_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v___x_290_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
}
else
{
lean_object* v___x_299_; 
lean_dec(v_a_280_);
lean_dec(v_a_278_);
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 0, v_code_268_);
v___x_299_ = v___x_282_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v_code_268_);
v___x_299_ = v_reuseFailAlloc_300_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
return v___x_299_;
}
}
}
}
}
else
{
lean_dec(v_a_278_);
lean_dec_ref(v_code_268_);
return v___x_279_;
}
}
else
{
lean_object* v_a_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_315_; 
lean_dec_ref(v_code_268_);
v_a_308_ = lean_ctor_get(v___x_277_, 0);
v_isSharedCheck_315_ = !lean_is_exclusive(v___x_277_);
if (v_isSharedCheck_315_ == 0)
{
v___x_310_ = v___x_277_;
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_a_308_);
lean_dec(v___x_277_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_313_; 
if (v_isShared_311_ == 0)
{
v___x_313_ = v___x_310_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_a_308_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
}
case 1:
{
lean_object* v_decl_316_; lean_object* v_k_317_; lean_object* v___x_318_; 
v_decl_316_ = lean_ctor_get(v_code_268_, 0);
v_k_317_ = lean_ctor_get(v_code_268_, 1);
lean_inc_ref(v_decl_316_);
v___x_318_ = l_Lean_Compiler_LCNF_FunDecl_applyRenaming(v_pu_267_, v_decl_316_, v_r_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_);
if (lean_obj_tag(v___x_318_) == 0)
{
lean_object* v_a_319_; lean_object* v___x_320_; 
v_a_319_ = lean_ctor_get(v___x_318_, 0);
lean_inc(v_a_319_);
lean_dec_ref(v___x_318_);
lean_inc_ref(v_k_317_);
v___x_320_ = l_Lean_Compiler_LCNF_Code_applyRenaming(v_pu_267_, v_k_317_, v_r_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_);
if (lean_obj_tag(v___x_320_) == 0)
{
lean_object* v_a_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_348_; 
v_a_321_ = lean_ctor_get(v___x_320_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_320_);
if (v_isSharedCheck_348_ == 0)
{
v___x_323_ = v___x_320_;
v_isShared_324_ = v_isSharedCheck_348_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_a_321_);
lean_dec(v___x_320_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_348_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
uint8_t v___y_326_; size_t v___x_342_; size_t v___x_343_; uint8_t v___x_344_; 
v___x_342_ = lean_ptr_addr(v_k_317_);
v___x_343_ = lean_ptr_addr(v_a_321_);
v___x_344_ = lean_usize_dec_eq(v___x_342_, v___x_343_);
if (v___x_344_ == 0)
{
v___y_326_ = v___x_344_;
goto v___jp_325_;
}
else
{
size_t v___x_345_; size_t v___x_346_; uint8_t v___x_347_; 
v___x_345_ = lean_ptr_addr(v_decl_316_);
v___x_346_ = lean_ptr_addr(v_a_319_);
v___x_347_ = lean_usize_dec_eq(v___x_345_, v___x_346_);
v___y_326_ = v___x_347_;
goto v___jp_325_;
}
v___jp_325_:
{
if (v___y_326_ == 0)
{
lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_336_; 
v_isSharedCheck_336_ = !lean_is_exclusive(v_code_268_);
if (v_isSharedCheck_336_ == 0)
{
lean_object* v_unused_337_; lean_object* v_unused_338_; 
v_unused_337_ = lean_ctor_get(v_code_268_, 1);
lean_dec(v_unused_337_);
v_unused_338_ = lean_ctor_get(v_code_268_, 0);
lean_dec(v_unused_338_);
v___x_328_ = v_code_268_;
v_isShared_329_ = v_isSharedCheck_336_;
goto v_resetjp_327_;
}
else
{
lean_dec(v_code_268_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_336_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_331_; 
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 1, v_a_321_);
lean_ctor_set(v___x_328_, 0, v_a_319_);
v___x_331_ = v___x_328_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v_a_319_);
lean_ctor_set(v_reuseFailAlloc_335_, 1, v_a_321_);
v___x_331_ = v_reuseFailAlloc_335_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
lean_object* v___x_333_; 
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 0, v___x_331_);
v___x_333_ = v___x_323_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v___x_331_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
}
else
{
lean_object* v___x_340_; 
lean_dec(v_a_321_);
lean_dec(v_a_319_);
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 0, v_code_268_);
v___x_340_ = v___x_323_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v_code_268_);
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
}
else
{
lean_dec(v_a_319_);
lean_dec_ref(v_code_268_);
return v___x_320_;
}
}
else
{
lean_object* v_a_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_356_; 
lean_dec_ref(v_code_268_);
v_a_349_ = lean_ctor_get(v___x_318_, 0);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_318_);
if (v_isSharedCheck_356_ == 0)
{
v___x_351_ = v___x_318_;
v_isShared_352_ = v_isSharedCheck_356_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_a_349_);
lean_dec(v___x_318_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_356_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v___x_354_; 
if (v_isShared_352_ == 0)
{
v___x_354_ = v___x_351_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_a_349_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
}
}
case 2:
{
lean_object* v_decl_357_; lean_object* v_k_358_; lean_object* v___x_359_; 
v_decl_357_ = lean_ctor_get(v_code_268_, 0);
v_k_358_ = lean_ctor_get(v_code_268_, 1);
lean_inc_ref(v_decl_357_);
v___x_359_ = l_Lean_Compiler_LCNF_FunDecl_applyRenaming(v_pu_267_, v_decl_357_, v_r_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_);
if (lean_obj_tag(v___x_359_) == 0)
{
lean_object* v_a_360_; lean_object* v___x_361_; 
v_a_360_ = lean_ctor_get(v___x_359_, 0);
lean_inc(v_a_360_);
lean_dec_ref(v___x_359_);
lean_inc_ref(v_k_358_);
v___x_361_ = l_Lean_Compiler_LCNF_Code_applyRenaming(v_pu_267_, v_k_358_, v_r_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_);
if (lean_obj_tag(v___x_361_) == 0)
{
lean_object* v_a_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_389_; 
v_a_362_ = lean_ctor_get(v___x_361_, 0);
v_isSharedCheck_389_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_389_ == 0)
{
v___x_364_ = v___x_361_;
v_isShared_365_ = v_isSharedCheck_389_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_a_362_);
lean_dec(v___x_361_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_389_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
uint8_t v___y_367_; size_t v___x_383_; size_t v___x_384_; uint8_t v___x_385_; 
v___x_383_ = lean_ptr_addr(v_k_358_);
v___x_384_ = lean_ptr_addr(v_a_362_);
v___x_385_ = lean_usize_dec_eq(v___x_383_, v___x_384_);
if (v___x_385_ == 0)
{
v___y_367_ = v___x_385_;
goto v___jp_366_;
}
else
{
size_t v___x_386_; size_t v___x_387_; uint8_t v___x_388_; 
v___x_386_ = lean_ptr_addr(v_decl_357_);
v___x_387_ = lean_ptr_addr(v_a_360_);
v___x_388_ = lean_usize_dec_eq(v___x_386_, v___x_387_);
v___y_367_ = v___x_388_;
goto v___jp_366_;
}
v___jp_366_:
{
if (v___y_367_ == 0)
{
lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_377_; 
v_isSharedCheck_377_ = !lean_is_exclusive(v_code_268_);
if (v_isSharedCheck_377_ == 0)
{
lean_object* v_unused_378_; lean_object* v_unused_379_; 
v_unused_378_ = lean_ctor_get(v_code_268_, 1);
lean_dec(v_unused_378_);
v_unused_379_ = lean_ctor_get(v_code_268_, 0);
lean_dec(v_unused_379_);
v___x_369_ = v_code_268_;
v_isShared_370_ = v_isSharedCheck_377_;
goto v_resetjp_368_;
}
else
{
lean_dec(v_code_268_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_377_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_372_; 
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 1, v_a_362_);
lean_ctor_set(v___x_369_, 0, v_a_360_);
v___x_372_ = v___x_369_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_a_360_);
lean_ctor_set(v_reuseFailAlloc_376_, 1, v_a_362_);
v___x_372_ = v_reuseFailAlloc_376_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
lean_object* v___x_374_; 
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 0, v___x_372_);
v___x_374_ = v___x_364_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v___x_372_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
}
}
else
{
lean_object* v___x_381_; 
lean_dec(v_a_362_);
lean_dec(v_a_360_);
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 0, v_code_268_);
v___x_381_ = v___x_364_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_code_268_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
}
}
}
else
{
lean_dec(v_a_360_);
lean_dec_ref(v_code_268_);
return v___x_361_;
}
}
else
{
lean_object* v_a_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_397_; 
lean_dec_ref(v_code_268_);
v_a_390_ = lean_ctor_get(v___x_359_, 0);
v_isSharedCheck_397_ = !lean_is_exclusive(v___x_359_);
if (v_isSharedCheck_397_ == 0)
{
v___x_392_ = v___x_359_;
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_a_390_);
lean_dec(v___x_359_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___x_395_; 
if (v_isShared_393_ == 0)
{
v___x_395_ = v___x_392_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_a_390_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
}
}
case 4:
{
lean_object* v_cases_398_; lean_object* v_typeName_399_; lean_object* v_resultType_400_; lean_object* v_discr_401_; lean_object* v_alts_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_441_; 
v_cases_398_ = lean_ctor_get(v_code_268_, 0);
lean_inc_ref(v_cases_398_);
v_typeName_399_ = lean_ctor_get(v_cases_398_, 0);
v_resultType_400_ = lean_ctor_get(v_cases_398_, 1);
v_discr_401_ = lean_ctor_get(v_cases_398_, 2);
v_alts_402_ = lean_ctor_get(v_cases_398_, 3);
v_isSharedCheck_441_ = !lean_is_exclusive(v_cases_398_);
if (v_isSharedCheck_441_ == 0)
{
v___x_404_ = v_cases_398_;
v_isShared_405_ = v_isSharedCheck_441_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_alts_402_);
lean_inc(v_discr_401_);
lean_inc(v_resultType_400_);
lean_inc(v_typeName_399_);
lean_dec(v_cases_398_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_441_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_406_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_402_);
v___x_407_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__2(v_pu_267_, v_r_269_, v___x_406_, v_alts_402_, v_a_270_, v_a_271_, v_a_272_, v_a_273_);
if (lean_obj_tag(v___x_407_) == 0)
{
lean_object* v_a_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_432_; 
v_a_408_ = lean_ctor_get(v___x_407_, 0);
v_isSharedCheck_432_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_432_ == 0)
{
v___x_410_ = v___x_407_;
v_isShared_411_ = v_isSharedCheck_432_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_a_408_);
lean_dec(v___x_407_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_432_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
size_t v___x_412_; size_t v___x_413_; uint8_t v___x_414_; 
v___x_412_ = lean_ptr_addr(v_alts_402_);
lean_dec_ref(v_alts_402_);
v___x_413_ = lean_ptr_addr(v_a_408_);
v___x_414_ = lean_usize_dec_eq(v___x_412_, v___x_413_);
if (v___x_414_ == 0)
{
lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_427_; 
v_isSharedCheck_427_ = !lean_is_exclusive(v_code_268_);
if (v_isSharedCheck_427_ == 0)
{
lean_object* v_unused_428_; 
v_unused_428_ = lean_ctor_get(v_code_268_, 0);
lean_dec(v_unused_428_);
v___x_416_ = v_code_268_;
v_isShared_417_ = v_isSharedCheck_427_;
goto v_resetjp_415_;
}
else
{
lean_dec(v_code_268_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_427_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_419_; 
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 3, v_a_408_);
v___x_419_ = v___x_404_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v_typeName_399_);
lean_ctor_set(v_reuseFailAlloc_426_, 1, v_resultType_400_);
lean_ctor_set(v_reuseFailAlloc_426_, 2, v_discr_401_);
lean_ctor_set(v_reuseFailAlloc_426_, 3, v_a_408_);
v___x_419_ = v_reuseFailAlloc_426_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
lean_object* v___x_421_; 
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 0, v___x_419_);
v___x_421_ = v___x_416_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v___x_419_);
v___x_421_ = v_reuseFailAlloc_425_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
lean_object* v___x_423_; 
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 0, v___x_421_);
v___x_423_ = v___x_410_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v___x_421_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
}
}
else
{
lean_object* v___x_430_; 
lean_dec(v_a_408_);
lean_del_object(v___x_404_);
lean_dec(v_discr_401_);
lean_dec_ref(v_resultType_400_);
lean_dec(v_typeName_399_);
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 0, v_code_268_);
v___x_430_ = v___x_410_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_code_268_);
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
else
{
lean_object* v_a_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_440_; 
lean_del_object(v___x_404_);
lean_dec_ref(v_alts_402_);
lean_dec(v_discr_401_);
lean_dec_ref(v_resultType_400_);
lean_dec(v_typeName_399_);
lean_dec_ref(v_code_268_);
v_a_433_ = lean_ctor_get(v___x_407_, 0);
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_440_ == 0)
{
v___x_435_ = v___x_407_;
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_a_433_);
lean_dec(v___x_407_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_438_; 
if (v_isShared_436_ == 0)
{
v___x_438_ = v___x_435_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v_a_433_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
}
}
case 7:
{
lean_object* v_fvarId_442_; lean_object* v_i_443_; lean_object* v_y_444_; lean_object* v_k_445_; lean_object* v___x_446_; 
v_fvarId_442_ = lean_ctor_get(v_code_268_, 0);
v_i_443_ = lean_ctor_get(v_code_268_, 1);
v_y_444_ = lean_ctor_get(v_code_268_, 2);
v_k_445_ = lean_ctor_get(v_code_268_, 3);
lean_inc_ref(v_k_445_);
v___x_446_ = l_Lean_Compiler_LCNF_Code_applyRenaming(v_pu_267_, v_k_445_, v_r_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_);
if (lean_obj_tag(v___x_446_) == 0)
{
lean_object* v_a_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_471_; 
v_a_447_ = lean_ctor_get(v___x_446_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_471_ == 0)
{
v___x_449_ = v___x_446_;
v_isShared_450_ = v_isSharedCheck_471_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_a_447_);
lean_dec(v___x_446_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_471_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
size_t v___x_451_; size_t v___x_452_; uint8_t v___x_453_; 
v___x_451_ = lean_ptr_addr(v_k_445_);
v___x_452_ = lean_ptr_addr(v_a_447_);
v___x_453_ = lean_usize_dec_eq(v___x_451_, v___x_452_);
if (v___x_453_ == 0)
{
lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_463_; 
lean_inc(v_y_444_);
lean_inc(v_i_443_);
lean_inc(v_fvarId_442_);
v_isSharedCheck_463_ = !lean_is_exclusive(v_code_268_);
if (v_isSharedCheck_463_ == 0)
{
lean_object* v_unused_464_; lean_object* v_unused_465_; lean_object* v_unused_466_; lean_object* v_unused_467_; 
v_unused_464_ = lean_ctor_get(v_code_268_, 3);
lean_dec(v_unused_464_);
v_unused_465_ = lean_ctor_get(v_code_268_, 2);
lean_dec(v_unused_465_);
v_unused_466_ = lean_ctor_get(v_code_268_, 1);
lean_dec(v_unused_466_);
v_unused_467_ = lean_ctor_get(v_code_268_, 0);
lean_dec(v_unused_467_);
v___x_455_ = v_code_268_;
v_isShared_456_ = v_isSharedCheck_463_;
goto v_resetjp_454_;
}
else
{
lean_dec(v_code_268_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_463_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_458_; 
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 3, v_a_447_);
v___x_458_ = v___x_455_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v_fvarId_442_);
lean_ctor_set(v_reuseFailAlloc_462_, 1, v_i_443_);
lean_ctor_set(v_reuseFailAlloc_462_, 2, v_y_444_);
lean_ctor_set(v_reuseFailAlloc_462_, 3, v_a_447_);
v___x_458_ = v_reuseFailAlloc_462_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
lean_object* v___x_460_; 
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 0, v___x_458_);
v___x_460_ = v___x_449_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v___x_458_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
return v___x_460_;
}
}
}
}
else
{
lean_object* v___x_469_; 
lean_dec(v_a_447_);
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 0, v_code_268_);
v___x_469_ = v___x_449_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v_code_268_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
}
}
else
{
lean_dec_ref(v_code_268_);
return v___x_446_;
}
}
case 8:
{
lean_object* v_fvarId_472_; lean_object* v_i_473_; lean_object* v_y_474_; lean_object* v_k_475_; lean_object* v___x_476_; 
v_fvarId_472_ = lean_ctor_get(v_code_268_, 0);
v_i_473_ = lean_ctor_get(v_code_268_, 1);
v_y_474_ = lean_ctor_get(v_code_268_, 2);
v_k_475_ = lean_ctor_get(v_code_268_, 3);
lean_inc_ref(v_k_475_);
v___x_476_ = l_Lean_Compiler_LCNF_Code_applyRenaming(v_pu_267_, v_k_475_, v_r_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_);
if (lean_obj_tag(v___x_476_) == 0)
{
lean_object* v_a_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_501_; 
v_a_477_ = lean_ctor_get(v___x_476_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_501_ == 0)
{
v___x_479_ = v___x_476_;
v_isShared_480_ = v_isSharedCheck_501_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_a_477_);
lean_dec(v___x_476_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_501_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
size_t v___x_481_; size_t v___x_482_; uint8_t v___x_483_; 
v___x_481_ = lean_ptr_addr(v_k_475_);
v___x_482_ = lean_ptr_addr(v_a_477_);
v___x_483_ = lean_usize_dec_eq(v___x_481_, v___x_482_);
if (v___x_483_ == 0)
{
lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_493_; 
lean_inc(v_y_474_);
lean_inc(v_i_473_);
lean_inc(v_fvarId_472_);
v_isSharedCheck_493_ = !lean_is_exclusive(v_code_268_);
if (v_isSharedCheck_493_ == 0)
{
lean_object* v_unused_494_; lean_object* v_unused_495_; lean_object* v_unused_496_; lean_object* v_unused_497_; 
v_unused_494_ = lean_ctor_get(v_code_268_, 3);
lean_dec(v_unused_494_);
v_unused_495_ = lean_ctor_get(v_code_268_, 2);
lean_dec(v_unused_495_);
v_unused_496_ = lean_ctor_get(v_code_268_, 1);
lean_dec(v_unused_496_);
v_unused_497_ = lean_ctor_get(v_code_268_, 0);
lean_dec(v_unused_497_);
v___x_485_ = v_code_268_;
v_isShared_486_ = v_isSharedCheck_493_;
goto v_resetjp_484_;
}
else
{
lean_dec(v_code_268_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_493_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_488_; 
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 3, v_a_477_);
v___x_488_ = v___x_485_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_fvarId_472_);
lean_ctor_set(v_reuseFailAlloc_492_, 1, v_i_473_);
lean_ctor_set(v_reuseFailAlloc_492_, 2, v_y_474_);
lean_ctor_set(v_reuseFailAlloc_492_, 3, v_a_477_);
v___x_488_ = v_reuseFailAlloc_492_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
lean_object* v___x_490_; 
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 0, v___x_488_);
v___x_490_ = v___x_479_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v___x_488_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
}
}
else
{
lean_object* v___x_499_; 
lean_dec(v_a_477_);
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 0, v_code_268_);
v___x_499_ = v___x_479_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_code_268_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
}
}
else
{
lean_dec_ref(v_code_268_);
return v___x_476_;
}
}
case 9:
{
lean_object* v_fvarId_502_; lean_object* v_i_503_; lean_object* v_offset_504_; lean_object* v_y_505_; lean_object* v_ty_506_; lean_object* v_k_507_; lean_object* v___x_508_; 
v_fvarId_502_ = lean_ctor_get(v_code_268_, 0);
v_i_503_ = lean_ctor_get(v_code_268_, 1);
v_offset_504_ = lean_ctor_get(v_code_268_, 2);
v_y_505_ = lean_ctor_get(v_code_268_, 3);
v_ty_506_ = lean_ctor_get(v_code_268_, 4);
v_k_507_ = lean_ctor_get(v_code_268_, 5);
lean_inc_ref(v_k_507_);
v___x_508_ = l_Lean_Compiler_LCNF_Code_applyRenaming(v_pu_267_, v_k_507_, v_r_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_);
if (lean_obj_tag(v___x_508_) == 0)
{
lean_object* v_a_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_535_; 
v_a_509_ = lean_ctor_get(v___x_508_, 0);
v_isSharedCheck_535_ = !lean_is_exclusive(v___x_508_);
if (v_isSharedCheck_535_ == 0)
{
v___x_511_ = v___x_508_;
v_isShared_512_ = v_isSharedCheck_535_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_a_509_);
lean_dec(v___x_508_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_535_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
size_t v___x_513_; size_t v___x_514_; uint8_t v___x_515_; 
v___x_513_ = lean_ptr_addr(v_k_507_);
v___x_514_ = lean_ptr_addr(v_a_509_);
v___x_515_ = lean_usize_dec_eq(v___x_513_, v___x_514_);
if (v___x_515_ == 0)
{
lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_525_; 
lean_inc_ref(v_ty_506_);
lean_inc(v_y_505_);
lean_inc(v_offset_504_);
lean_inc(v_i_503_);
lean_inc(v_fvarId_502_);
v_isSharedCheck_525_ = !lean_is_exclusive(v_code_268_);
if (v_isSharedCheck_525_ == 0)
{
lean_object* v_unused_526_; lean_object* v_unused_527_; lean_object* v_unused_528_; lean_object* v_unused_529_; lean_object* v_unused_530_; lean_object* v_unused_531_; 
v_unused_526_ = lean_ctor_get(v_code_268_, 5);
lean_dec(v_unused_526_);
v_unused_527_ = lean_ctor_get(v_code_268_, 4);
lean_dec(v_unused_527_);
v_unused_528_ = lean_ctor_get(v_code_268_, 3);
lean_dec(v_unused_528_);
v_unused_529_ = lean_ctor_get(v_code_268_, 2);
lean_dec(v_unused_529_);
v_unused_530_ = lean_ctor_get(v_code_268_, 1);
lean_dec(v_unused_530_);
v_unused_531_ = lean_ctor_get(v_code_268_, 0);
lean_dec(v_unused_531_);
v___x_517_ = v_code_268_;
v_isShared_518_ = v_isSharedCheck_525_;
goto v_resetjp_516_;
}
else
{
lean_dec(v_code_268_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_525_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_520_; 
if (v_isShared_518_ == 0)
{
lean_ctor_set(v___x_517_, 5, v_a_509_);
v___x_520_ = v___x_517_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_fvarId_502_);
lean_ctor_set(v_reuseFailAlloc_524_, 1, v_i_503_);
lean_ctor_set(v_reuseFailAlloc_524_, 2, v_offset_504_);
lean_ctor_set(v_reuseFailAlloc_524_, 3, v_y_505_);
lean_ctor_set(v_reuseFailAlloc_524_, 4, v_ty_506_);
lean_ctor_set(v_reuseFailAlloc_524_, 5, v_a_509_);
v___x_520_ = v_reuseFailAlloc_524_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
lean_object* v___x_522_; 
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 0, v___x_520_);
v___x_522_ = v___x_511_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v___x_520_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
}
}
else
{
lean_object* v___x_533_; 
lean_dec(v_a_509_);
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 0, v_code_268_);
v___x_533_ = v___x_511_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v_code_268_);
v___x_533_ = v_reuseFailAlloc_534_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
return v___x_533_;
}
}
}
}
else
{
lean_dec_ref(v_code_268_);
return v___x_508_;
}
}
case 10:
{
lean_object* v_fvarId_536_; lean_object* v_cidx_537_; lean_object* v_k_538_; lean_object* v___x_539_; 
v_fvarId_536_ = lean_ctor_get(v_code_268_, 0);
v_cidx_537_ = lean_ctor_get(v_code_268_, 1);
v_k_538_ = lean_ctor_get(v_code_268_, 2);
lean_inc_ref(v_k_538_);
v___x_539_ = l_Lean_Compiler_LCNF_Code_applyRenaming(v_pu_267_, v_k_538_, v_r_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_);
if (lean_obj_tag(v___x_539_) == 0)
{
lean_object* v_a_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_563_; 
v_a_540_ = lean_ctor_get(v___x_539_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_539_);
if (v_isSharedCheck_563_ == 0)
{
v___x_542_ = v___x_539_;
v_isShared_543_ = v_isSharedCheck_563_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_a_540_);
lean_dec(v___x_539_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_563_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
size_t v___x_544_; size_t v___x_545_; uint8_t v___x_546_; 
v___x_544_ = lean_ptr_addr(v_k_538_);
v___x_545_ = lean_ptr_addr(v_a_540_);
v___x_546_ = lean_usize_dec_eq(v___x_544_, v___x_545_);
if (v___x_546_ == 0)
{
lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_556_; 
lean_inc(v_cidx_537_);
lean_inc(v_fvarId_536_);
v_isSharedCheck_556_ = !lean_is_exclusive(v_code_268_);
if (v_isSharedCheck_556_ == 0)
{
lean_object* v_unused_557_; lean_object* v_unused_558_; lean_object* v_unused_559_; 
v_unused_557_ = lean_ctor_get(v_code_268_, 2);
lean_dec(v_unused_557_);
v_unused_558_ = lean_ctor_get(v_code_268_, 1);
lean_dec(v_unused_558_);
v_unused_559_ = lean_ctor_get(v_code_268_, 0);
lean_dec(v_unused_559_);
v___x_548_ = v_code_268_;
v_isShared_549_ = v_isSharedCheck_556_;
goto v_resetjp_547_;
}
else
{
lean_dec(v_code_268_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_556_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_551_; 
if (v_isShared_549_ == 0)
{
lean_ctor_set(v___x_548_, 2, v_a_540_);
v___x_551_ = v___x_548_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_fvarId_536_);
lean_ctor_set(v_reuseFailAlloc_555_, 1, v_cidx_537_);
lean_ctor_set(v_reuseFailAlloc_555_, 2, v_a_540_);
v___x_551_ = v_reuseFailAlloc_555_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
lean_object* v___x_553_; 
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 0, v___x_551_);
v___x_553_ = v___x_542_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_551_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
}
else
{
lean_object* v___x_561_; 
lean_dec(v_a_540_);
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 0, v_code_268_);
v___x_561_ = v___x_542_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_code_268_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
}
else
{
lean_dec_ref(v_code_268_);
return v___x_539_;
}
}
case 11:
{
lean_object* v_fvarId_564_; lean_object* v_n_565_; uint8_t v_check_566_; uint8_t v_persistent_567_; lean_object* v_k_568_; lean_object* v___x_569_; 
v_fvarId_564_ = lean_ctor_get(v_code_268_, 0);
v_n_565_ = lean_ctor_get(v_code_268_, 1);
v_check_566_ = lean_ctor_get_uint8(v_code_268_, sizeof(void*)*3);
v_persistent_567_ = lean_ctor_get_uint8(v_code_268_, sizeof(void*)*3 + 1);
v_k_568_ = lean_ctor_get(v_code_268_, 2);
lean_inc_ref(v_k_568_);
v___x_569_ = l_Lean_Compiler_LCNF_Code_applyRenaming(v_pu_267_, v_k_568_, v_r_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_);
if (lean_obj_tag(v___x_569_) == 0)
{
lean_object* v_a_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_593_; 
v_a_570_ = lean_ctor_get(v___x_569_, 0);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_593_ == 0)
{
v___x_572_ = v___x_569_;
v_isShared_573_ = v_isSharedCheck_593_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_a_570_);
lean_dec(v___x_569_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_593_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
size_t v___x_574_; size_t v___x_575_; uint8_t v___x_576_; 
v___x_574_ = lean_ptr_addr(v_k_568_);
v___x_575_ = lean_ptr_addr(v_a_570_);
v___x_576_ = lean_usize_dec_eq(v___x_574_, v___x_575_);
if (v___x_576_ == 0)
{
lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_586_; 
lean_inc(v_n_565_);
lean_inc(v_fvarId_564_);
v_isSharedCheck_586_ = !lean_is_exclusive(v_code_268_);
if (v_isSharedCheck_586_ == 0)
{
lean_object* v_unused_587_; lean_object* v_unused_588_; lean_object* v_unused_589_; 
v_unused_587_ = lean_ctor_get(v_code_268_, 2);
lean_dec(v_unused_587_);
v_unused_588_ = lean_ctor_get(v_code_268_, 1);
lean_dec(v_unused_588_);
v_unused_589_ = lean_ctor_get(v_code_268_, 0);
lean_dec(v_unused_589_);
v___x_578_ = v_code_268_;
v_isShared_579_ = v_isSharedCheck_586_;
goto v_resetjp_577_;
}
else
{
lean_dec(v_code_268_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_586_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_581_; 
if (v_isShared_579_ == 0)
{
lean_ctor_set(v___x_578_, 2, v_a_570_);
v___x_581_ = v___x_578_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_fvarId_564_);
lean_ctor_set(v_reuseFailAlloc_585_, 1, v_n_565_);
lean_ctor_set(v_reuseFailAlloc_585_, 2, v_a_570_);
lean_ctor_set_uint8(v_reuseFailAlloc_585_, sizeof(void*)*3, v_check_566_);
lean_ctor_set_uint8(v_reuseFailAlloc_585_, sizeof(void*)*3 + 1, v_persistent_567_);
v___x_581_ = v_reuseFailAlloc_585_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
lean_object* v___x_583_; 
if (v_isShared_573_ == 0)
{
lean_ctor_set(v___x_572_, 0, v___x_581_);
v___x_583_ = v___x_572_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v___x_581_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
}
else
{
lean_object* v___x_591_; 
lean_dec(v_a_570_);
if (v_isShared_573_ == 0)
{
lean_ctor_set(v___x_572_, 0, v_code_268_);
v___x_591_ = v___x_572_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_code_268_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
}
}
else
{
lean_dec_ref(v_code_268_);
return v___x_569_;
}
}
case 12:
{
lean_object* v_fvarId_594_; lean_object* v_n_595_; uint8_t v_check_596_; uint8_t v_persistent_597_; lean_object* v_k_598_; lean_object* v___x_599_; 
v_fvarId_594_ = lean_ctor_get(v_code_268_, 0);
v_n_595_ = lean_ctor_get(v_code_268_, 1);
v_check_596_ = lean_ctor_get_uint8(v_code_268_, sizeof(void*)*3);
v_persistent_597_ = lean_ctor_get_uint8(v_code_268_, sizeof(void*)*3 + 1);
v_k_598_ = lean_ctor_get(v_code_268_, 2);
lean_inc_ref(v_k_598_);
v___x_599_ = l_Lean_Compiler_LCNF_Code_applyRenaming(v_pu_267_, v_k_598_, v_r_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_);
if (lean_obj_tag(v___x_599_) == 0)
{
lean_object* v_a_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_623_; 
v_a_600_ = lean_ctor_get(v___x_599_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_623_ == 0)
{
v___x_602_ = v___x_599_;
v_isShared_603_ = v_isSharedCheck_623_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_a_600_);
lean_dec(v___x_599_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_623_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
size_t v___x_604_; size_t v___x_605_; uint8_t v___x_606_; 
v___x_604_ = lean_ptr_addr(v_k_598_);
v___x_605_ = lean_ptr_addr(v_a_600_);
v___x_606_ = lean_usize_dec_eq(v___x_604_, v___x_605_);
if (v___x_606_ == 0)
{
lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_616_; 
lean_inc(v_n_595_);
lean_inc(v_fvarId_594_);
v_isSharedCheck_616_ = !lean_is_exclusive(v_code_268_);
if (v_isSharedCheck_616_ == 0)
{
lean_object* v_unused_617_; lean_object* v_unused_618_; lean_object* v_unused_619_; 
v_unused_617_ = lean_ctor_get(v_code_268_, 2);
lean_dec(v_unused_617_);
v_unused_618_ = lean_ctor_get(v_code_268_, 1);
lean_dec(v_unused_618_);
v_unused_619_ = lean_ctor_get(v_code_268_, 0);
lean_dec(v_unused_619_);
v___x_608_ = v_code_268_;
v_isShared_609_ = v_isSharedCheck_616_;
goto v_resetjp_607_;
}
else
{
lean_dec(v_code_268_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_616_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_611_; 
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 2, v_a_600_);
v___x_611_ = v___x_608_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(12, 3, 2);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_fvarId_594_);
lean_ctor_set(v_reuseFailAlloc_615_, 1, v_n_595_);
lean_ctor_set(v_reuseFailAlloc_615_, 2, v_a_600_);
lean_ctor_set_uint8(v_reuseFailAlloc_615_, sizeof(void*)*3, v_check_596_);
lean_ctor_set_uint8(v_reuseFailAlloc_615_, sizeof(void*)*3 + 1, v_persistent_597_);
v___x_611_ = v_reuseFailAlloc_615_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
lean_object* v___x_613_; 
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 0, v___x_611_);
v___x_613_ = v___x_602_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v___x_611_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
}
else
{
lean_object* v___x_621_; 
lean_dec(v_a_600_);
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 0, v_code_268_);
v___x_621_ = v___x_602_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_code_268_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
}
else
{
lean_dec_ref(v_code_268_);
return v___x_599_;
}
}
case 13:
{
lean_object* v_fvarId_624_; lean_object* v_k_625_; lean_object* v___x_626_; 
v_fvarId_624_ = lean_ctor_get(v_code_268_, 0);
v_k_625_ = lean_ctor_get(v_code_268_, 1);
lean_inc_ref(v_k_625_);
v___x_626_ = l_Lean_Compiler_LCNF_Code_applyRenaming(v_pu_267_, v_k_625_, v_r_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_);
if (lean_obj_tag(v___x_626_) == 0)
{
lean_object* v_a_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_649_; 
v_a_627_ = lean_ctor_get(v___x_626_, 0);
v_isSharedCheck_649_ = !lean_is_exclusive(v___x_626_);
if (v_isSharedCheck_649_ == 0)
{
v___x_629_ = v___x_626_;
v_isShared_630_ = v_isSharedCheck_649_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_a_627_);
lean_dec(v___x_626_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_649_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
size_t v___x_631_; size_t v___x_632_; uint8_t v___x_633_; 
v___x_631_ = lean_ptr_addr(v_k_625_);
v___x_632_ = lean_ptr_addr(v_a_627_);
v___x_633_ = lean_usize_dec_eq(v___x_631_, v___x_632_);
if (v___x_633_ == 0)
{
lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_643_; 
lean_inc(v_fvarId_624_);
v_isSharedCheck_643_ = !lean_is_exclusive(v_code_268_);
if (v_isSharedCheck_643_ == 0)
{
lean_object* v_unused_644_; lean_object* v_unused_645_; 
v_unused_644_ = lean_ctor_get(v_code_268_, 1);
lean_dec(v_unused_644_);
v_unused_645_ = lean_ctor_get(v_code_268_, 0);
lean_dec(v_unused_645_);
v___x_635_ = v_code_268_;
v_isShared_636_ = v_isSharedCheck_643_;
goto v_resetjp_634_;
}
else
{
lean_dec(v_code_268_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_643_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_638_; 
if (v_isShared_636_ == 0)
{
lean_ctor_set(v___x_635_, 1, v_a_627_);
v___x_638_ = v___x_635_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_fvarId_624_);
lean_ctor_set(v_reuseFailAlloc_642_, 1, v_a_627_);
v___x_638_ = v_reuseFailAlloc_642_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
lean_object* v___x_640_; 
if (v_isShared_630_ == 0)
{
lean_ctor_set(v___x_629_, 0, v___x_638_);
v___x_640_ = v___x_629_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v___x_638_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
}
}
else
{
lean_object* v___x_647_; 
lean_dec(v_a_627_);
if (v_isShared_630_ == 0)
{
lean_ctor_set(v___x_629_, 0, v_code_268_);
v___x_647_ = v___x_629_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_code_268_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
}
}
else
{
lean_dec_ref(v_code_268_);
return v___x_626_;
}
}
default: 
{
lean_object* v___x_650_; 
v___x_650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_650_, 0, v_code_268_);
return v___x_650_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_applyRenaming(uint8_t v_pu_651_, lean_object* v_decl_652_, lean_object* v_r_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_){
_start:
{
lean_object* v_fvarId_659_; lean_object* v_params_660_; lean_object* v_type_661_; lean_object* v_value_662_; lean_object* v___x_663_; 
v_fvarId_659_ = lean_ctor_get(v_decl_652_, 0);
v_params_660_ = lean_ctor_get(v_decl_652_, 2);
lean_inc_ref(v_params_660_);
v_type_661_ = lean_ctor_get(v_decl_652_, 3);
lean_inc_ref(v_type_661_);
v_value_662_ = lean_ctor_get(v_decl_652_, 4);
v___x_663_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Param_applyRenaming_spec__0___redArg(v_r_653_, v_fvarId_659_);
if (lean_obj_tag(v___x_663_) == 1)
{
lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_694_; 
lean_inc_ref(v_value_662_);
lean_inc(v_fvarId_659_);
v_isSharedCheck_694_ = !lean_is_exclusive(v_decl_652_);
if (v_isSharedCheck_694_ == 0)
{
lean_object* v_unused_695_; lean_object* v_unused_696_; lean_object* v_unused_697_; lean_object* v_unused_698_; lean_object* v_unused_699_; 
v_unused_695_ = lean_ctor_get(v_decl_652_, 4);
lean_dec(v_unused_695_);
v_unused_696_ = lean_ctor_get(v_decl_652_, 3);
lean_dec(v_unused_696_);
v_unused_697_ = lean_ctor_get(v_decl_652_, 2);
lean_dec(v_unused_697_);
v_unused_698_ = lean_ctor_get(v_decl_652_, 1);
lean_dec(v_unused_698_);
v_unused_699_ = lean_ctor_get(v_decl_652_, 0);
lean_dec(v_unused_699_);
v___x_665_ = v_decl_652_;
v_isShared_666_ = v_isSharedCheck_694_;
goto v_resetjp_664_;
}
else
{
lean_dec(v_decl_652_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_694_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v_val_667_; lean_object* v___x_668_; lean_object* v_lctx_669_; lean_object* v_nextIdx_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_693_; 
v_val_667_ = lean_ctor_get(v___x_663_, 0);
lean_inc(v_val_667_);
lean_dec_ref(v___x_663_);
v___x_668_ = lean_st_ref_take(v_a_655_);
v_lctx_669_ = lean_ctor_get(v___x_668_, 0);
v_nextIdx_670_ = lean_ctor_get(v___x_668_, 1);
v_isSharedCheck_693_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_693_ == 0)
{
v___x_672_ = v___x_668_;
v_isShared_673_ = v_isSharedCheck_693_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_nextIdx_670_);
lean_inc(v_lctx_669_);
lean_dec(v___x_668_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_693_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v_decl_675_; 
lean_inc_ref(v_value_662_);
lean_inc_ref(v_type_661_);
lean_inc_ref(v_params_660_);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 1, v_val_667_);
v_decl_675_ = v___x_665_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_fvarId_659_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v_val_667_);
lean_ctor_set(v_reuseFailAlloc_692_, 2, v_params_660_);
lean_ctor_set(v_reuseFailAlloc_692_, 3, v_type_661_);
lean_ctor_set(v_reuseFailAlloc_692_, 4, v_value_662_);
v_decl_675_ = v_reuseFailAlloc_692_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
lean_object* v___x_676_; lean_object* v___x_678_; 
lean_inc_ref(v_decl_675_);
v___x_676_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v_pu_651_, v_lctx_669_, v_decl_675_);
if (v_isShared_673_ == 0)
{
lean_ctor_set(v___x_672_, 0, v___x_676_);
v___x_678_ = v___x_672_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v___x_676_);
lean_ctor_set(v_reuseFailAlloc_691_, 1, v_nextIdx_670_);
v___x_678_ = v_reuseFailAlloc_691_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_679_ = lean_st_ref_set(v_a_655_, v___x_678_);
v___x_680_ = l_Lean_Compiler_LCNF_Code_applyRenaming(v_pu_651_, v_value_662_, v_r_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_);
if (lean_obj_tag(v___x_680_) == 0)
{
lean_object* v_a_681_; lean_object* v___x_682_; 
v_a_681_ = lean_ctor_get(v___x_680_, 0);
lean_inc(v_a_681_);
lean_dec_ref(v___x_680_);
v___x_682_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_651_, v_decl_675_, v_type_661_, v_params_660_, v_a_681_, v_a_655_);
return v___x_682_;
}
else
{
lean_object* v_a_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_690_; 
lean_dec_ref(v_decl_675_);
lean_dec_ref(v_type_661_);
lean_dec_ref(v_params_660_);
v_a_683_ = lean_ctor_get(v___x_680_, 0);
v_isSharedCheck_690_ = !lean_is_exclusive(v___x_680_);
if (v_isSharedCheck_690_ == 0)
{
v___x_685_ = v___x_680_;
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_a_683_);
lean_dec(v___x_680_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_688_; 
if (v_isShared_686_ == 0)
{
v___x_688_ = v___x_685_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_a_683_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
return v___x_688_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_700_; 
lean_dec(v___x_663_);
lean_inc_ref(v_value_662_);
v___x_700_ = l_Lean_Compiler_LCNF_Code_applyRenaming(v_pu_651_, v_value_662_, v_r_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_);
if (lean_obj_tag(v___x_700_) == 0)
{
lean_object* v_a_701_; lean_object* v___x_702_; 
v_a_701_ = lean_ctor_get(v___x_700_, 0);
lean_inc(v_a_701_);
lean_dec_ref(v___x_700_);
v___x_702_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_651_, v_decl_652_, v_type_661_, v_params_660_, v_a_701_, v_a_655_);
return v___x_702_;
}
else
{
lean_object* v_a_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_710_; 
lean_dec_ref(v_type_661_);
lean_dec_ref(v_params_660_);
lean_dec_ref(v_decl_652_);
v_a_703_ = lean_ctor_get(v___x_700_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_710_ == 0)
{
v___x_705_ = v___x_700_;
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_a_703_);
lean_dec(v___x_700_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_708_; 
if (v_isShared_706_ == 0)
{
v___x_708_ = v___x_705_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v_a_703_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_applyRenaming___boxed(lean_object* v_pu_711_, lean_object* v_decl_712_, lean_object* v_r_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_){
_start:
{
uint8_t v_pu_boxed_719_; lean_object* v_res_720_; 
v_pu_boxed_719_ = lean_unbox(v_pu_711_);
v_res_720_ = l_Lean_Compiler_LCNF_FunDecl_applyRenaming(v_pu_boxed_719_, v_decl_712_, v_r_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
lean_dec(v_a_717_);
lean_dec_ref(v_a_716_);
lean_dec(v_a_715_);
lean_dec_ref(v_a_714_);
lean_dec(v_r_713_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__2___boxed(lean_object* v_pu_721_, lean_object* v_r_722_, lean_object* v_i_723_, lean_object* v_as_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_){
_start:
{
uint8_t v_pu_boxed_730_; lean_object* v_res_731_; 
v_pu_boxed_730_ = lean_unbox(v_pu_721_);
v_res_731_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__2(v_pu_boxed_730_, v_r_722_, v_i_723_, v_as_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_);
lean_dec(v___y_728_);
lean_dec_ref(v___y_727_);
lean_dec(v___y_726_);
lean_dec_ref(v___y_725_);
lean_dec(v_r_722_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_applyRenaming___boxed(lean_object* v_pu_732_, lean_object* v_code_733_, lean_object* v_r_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_){
_start:
{
uint8_t v_pu_boxed_740_; lean_object* v_res_741_; 
v_pu_boxed_740_ = lean_unbox(v_pu_732_);
v_res_741_ = l_Lean_Compiler_LCNF_Code_applyRenaming(v_pu_boxed_740_, v_code_733_, v_r_734_, v_a_735_, v_a_736_, v_a_737_, v_a_738_);
lean_dec(v_a_738_);
lean_dec_ref(v_a_737_);
lean_dec(v_a_736_);
lean_dec_ref(v_a_735_);
lean_dec(v_r_734_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__1(uint8_t v_pu_742_, lean_object* v_r_743_, lean_object* v_i_744_, lean_object* v_as_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__1___redArg(v_pu_742_, v_r_743_, v_i_744_, v_as_745_, v___y_747_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__1___boxed(lean_object* v_pu_752_, lean_object* v_r_753_, lean_object* v_i_754_, lean_object* v_as_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_){
_start:
{
uint8_t v_pu_boxed_761_; lean_object* v_res_762_; 
v_pu_boxed_761_ = lean_unbox(v_pu_752_);
v_res_762_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__1(v_pu_boxed_761_, v_r_753_, v_i_754_, v_as_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
lean_dec(v___y_757_);
lean_dec_ref(v___y_756_);
lean_dec(v_r_753_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_applyRenaming_spec__0___redArg(lean_object* v_f_763_, lean_object* v_v_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_){
_start:
{
if (lean_obj_tag(v_v_764_) == 0)
{
lean_object* v_code_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_794_; 
v_code_770_ = lean_ctor_get(v_v_764_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v_v_764_);
if (v_isSharedCheck_794_ == 0)
{
v___x_772_ = v_v_764_;
v_isShared_773_ = v_isSharedCheck_794_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_code_770_);
lean_dec(v_v_764_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_794_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_774_; 
lean_inc(v___y_768_);
lean_inc_ref(v___y_767_);
lean_inc(v___y_766_);
lean_inc_ref(v___y_765_);
v___x_774_ = lean_apply_6(v_f_763_, v_code_770_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, lean_box(0));
if (lean_obj_tag(v___x_774_) == 0)
{
lean_object* v_a_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_785_; 
v_a_775_ = lean_ctor_get(v___x_774_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_785_ == 0)
{
v___x_777_ = v___x_774_;
v_isShared_778_ = v_isSharedCheck_785_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_a_775_);
lean_dec(v___x_774_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_785_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_780_; 
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 0, v_a_775_);
v___x_780_ = v___x_772_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_a_775_);
v___x_780_ = v_reuseFailAlloc_784_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
lean_object* v___x_782_; 
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 0, v___x_780_);
v___x_782_ = v___x_777_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v___x_780_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
}
}
else
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_793_; 
lean_del_object(v___x_772_);
v_a_786_ = lean_ctor_get(v___x_774_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_793_ == 0)
{
v___x_788_ = v___x_774_;
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_774_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_791_; 
if (v_isShared_789_ == 0)
{
v___x_791_ = v___x_788_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_a_786_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
}
}
else
{
lean_object* v___x_795_; 
lean_dec_ref(v_f_763_);
v___x_795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_795_, 0, v_v_764_);
return v___x_795_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_applyRenaming_spec__0___redArg___boxed(lean_object* v_f_796_, lean_object* v_v_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_applyRenaming_spec__0___redArg(v_f_796_, v_v_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_applyRenaming_spec__0(uint8_t v_pu_804_, lean_object* v_f_805_, lean_object* v_v_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_){
_start:
{
lean_object* v___x_812_; 
v___x_812_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_applyRenaming_spec__0___redArg(v_f_805_, v_v_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_applyRenaming_spec__0___boxed(lean_object* v_pu_813_, lean_object* v_f_814_, lean_object* v_v_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_){
_start:
{
uint8_t v_pu_boxed_821_; lean_object* v_res_822_; 
v_pu_boxed_821_ = lean_unbox(v_pu_813_);
v_res_822_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_applyRenaming_spec__0(v_pu_boxed_821_, v_f_814_, v_v_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_);
lean_dec(v___y_819_);
lean_dec_ref(v___y_818_);
lean_dec(v___y_817_);
lean_dec_ref(v___y_816_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_applyRenaming___lam__0(uint8_t v_pu_823_, lean_object* v_r_824_, lean_object* v_x_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_){
_start:
{
lean_object* v___x_831_; 
v___x_831_ = l_Lean_Compiler_LCNF_Code_applyRenaming(v_pu_823_, v_x_825_, v_r_824_, v___y_826_, v___y_827_, v___y_828_, v___y_829_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_applyRenaming___lam__0___boxed(lean_object* v_pu_832_, lean_object* v_r_833_, lean_object* v_x_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_){
_start:
{
uint8_t v_pu_boxed_840_; lean_object* v_res_841_; 
v_pu_boxed_840_ = lean_unbox(v_pu_832_);
v_res_841_ = l_Lean_Compiler_LCNF_Decl_applyRenaming___lam__0(v_pu_boxed_840_, v_r_833_, v_x_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_);
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec(v_r_833_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_applyRenaming(uint8_t v_pu_842_, lean_object* v_decl_843_, lean_object* v_r_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_){
_start:
{
if (lean_obj_tag(v_r_844_) == 0)
{
lean_object* v_toSignature_850_; lean_object* v_value_851_; uint8_t v_recursive_852_; lean_object* v_inlineAttr_x3f_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_902_; 
v_toSignature_850_ = lean_ctor_get(v_decl_843_, 0);
v_value_851_ = lean_ctor_get(v_decl_843_, 1);
v_recursive_852_ = lean_ctor_get_uint8(v_decl_843_, sizeof(void*)*3);
v_inlineAttr_x3f_853_ = lean_ctor_get(v_decl_843_, 2);
v_isSharedCheck_902_ = !lean_is_exclusive(v_decl_843_);
if (v_isSharedCheck_902_ == 0)
{
v___x_855_ = v_decl_843_;
v_isShared_856_ = v_isSharedCheck_902_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_inlineAttr_x3f_853_);
lean_inc(v_value_851_);
lean_inc(v_toSignature_850_);
lean_dec(v_decl_843_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_902_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v_name_857_; lean_object* v_levelParams_858_; lean_object* v_type_859_; lean_object* v_params_860_; uint8_t v_safe_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_901_; 
v_name_857_ = lean_ctor_get(v_toSignature_850_, 0);
v_levelParams_858_ = lean_ctor_get(v_toSignature_850_, 1);
v_type_859_ = lean_ctor_get(v_toSignature_850_, 2);
v_params_860_ = lean_ctor_get(v_toSignature_850_, 3);
v_safe_861_ = lean_ctor_get_uint8(v_toSignature_850_, sizeof(void*)*4);
v_isSharedCheck_901_ = !lean_is_exclusive(v_toSignature_850_);
if (v_isSharedCheck_901_ == 0)
{
v___x_863_ = v_toSignature_850_;
v_isShared_864_ = v_isSharedCheck_901_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_params_860_);
lean_inc(v_type_859_);
lean_inc(v_levelParams_858_);
lean_inc(v_name_857_);
lean_dec(v_toSignature_850_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_901_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_865_; lean_object* v___x_866_; 
v___x_865_ = lean_unsigned_to_nat(0u);
v___x_866_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__1___redArg(v_pu_842_, v_r_844_, v___x_865_, v_params_860_, v_a_846_);
if (lean_obj_tag(v___x_866_) == 0)
{
lean_object* v_a_867_; lean_object* v___x_868_; lean_object* v___f_869_; lean_object* v___x_870_; 
v_a_867_ = lean_ctor_get(v___x_866_, 0);
lean_inc(v_a_867_);
lean_dec_ref(v___x_866_);
v___x_868_ = lean_box(v_pu_842_);
v___f_869_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_applyRenaming___lam__0___boxed), 8, 2);
lean_closure_set(v___f_869_, 0, v___x_868_);
lean_closure_set(v___f_869_, 1, v_r_844_);
v___x_870_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_applyRenaming_spec__0___redArg(v___f_869_, v_value_851_, v_a_845_, v_a_846_, v_a_847_, v_a_848_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v_a_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_884_; 
v_a_871_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_884_ == 0)
{
v___x_873_ = v___x_870_;
v_isShared_874_ = v_isSharedCheck_884_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_a_871_);
lean_dec(v___x_870_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_884_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___x_876_; 
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 3, v_a_867_);
v___x_876_ = v___x_863_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_name_857_);
lean_ctor_set(v_reuseFailAlloc_883_, 1, v_levelParams_858_);
lean_ctor_set(v_reuseFailAlloc_883_, 2, v_type_859_);
lean_ctor_set(v_reuseFailAlloc_883_, 3, v_a_867_);
lean_ctor_set_uint8(v_reuseFailAlloc_883_, sizeof(void*)*4, v_safe_861_);
v___x_876_ = v_reuseFailAlloc_883_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
lean_object* v___x_878_; 
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 1, v_a_871_);
lean_ctor_set(v___x_855_, 0, v___x_876_);
v___x_878_ = v___x_855_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v___x_876_);
lean_ctor_set(v_reuseFailAlloc_882_, 1, v_a_871_);
lean_ctor_set(v_reuseFailAlloc_882_, 2, v_inlineAttr_x3f_853_);
lean_ctor_set_uint8(v_reuseFailAlloc_882_, sizeof(void*)*3, v_recursive_852_);
v___x_878_ = v_reuseFailAlloc_882_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
lean_object* v___x_880_; 
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 0, v___x_878_);
v___x_880_ = v___x_873_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v___x_878_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
}
}
else
{
lean_object* v_a_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_892_; 
lean_dec(v_a_867_);
lean_del_object(v___x_863_);
lean_dec_ref(v_type_859_);
lean_dec(v_levelParams_858_);
lean_dec(v_name_857_);
lean_del_object(v___x_855_);
lean_dec(v_inlineAttr_x3f_853_);
v_a_885_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_892_ == 0)
{
v___x_887_ = v___x_870_;
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_a_885_);
lean_dec(v___x_870_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_890_; 
if (v_isShared_888_ == 0)
{
v___x_890_ = v___x_887_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_a_885_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
}
else
{
lean_object* v_a_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_900_; 
lean_del_object(v___x_863_);
lean_dec_ref(v_type_859_);
lean_dec(v_levelParams_858_);
lean_dec(v_name_857_);
lean_del_object(v___x_855_);
lean_dec(v_inlineAttr_x3f_853_);
lean_dec_ref(v_value_851_);
lean_dec_ref(v_r_844_);
v_a_893_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_900_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_900_ == 0)
{
v___x_895_ = v___x_866_;
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_a_893_);
lean_dec(v___x_866_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v___x_898_; 
if (v_isShared_896_ == 0)
{
v___x_898_ = v___x_895_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v_a_893_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
}
}
}
}
else
{
lean_object* v___x_903_; 
v___x_903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_903_, 0, v_decl_843_);
return v___x_903_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_applyRenaming___boxed(lean_object* v_pu_904_, lean_object* v_decl_905_, lean_object* v_r_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_){
_start:
{
uint8_t v_pu_boxed_912_; lean_object* v_res_913_; 
v_pu_boxed_912_ = lean_unbox(v_pu_904_);
v_res_913_ = l_Lean_Compiler_LCNF_Decl_applyRenaming(v_pu_boxed_912_, v_decl_905_, v_r_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_);
lean_dec(v_a_910_);
lean_dec_ref(v_a_909_);
lean_dec(v_a_908_);
lean_dec_ref(v_a_907_);
return v_res_913_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_Renaming(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Compiler_LCNF_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_Renaming(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_Renaming(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Renaming(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_Renaming(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_Renaming(builtin);
}
#ifdef __cplusplus
}
#endif

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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
v___x_42_ = lean_st_ref_put(v_a_18_, v___x_41_);
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
v___x_116_ = lean_st_ref_put(v_a_92_, v___x_115_);
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
lean_dec_ref_known(v___x_166_, 1);
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
lean_dec_ref_known(v___x_222_, 1);
lean_inc_ref(v_code_220_);
v___x_224_ = l_Lean_Compiler_LCNF_Code_applyRenaming(v_pu_194_, v_code_220_, v_r_195_, v___y_198_, v___y_199_, v___y_200_, v___y_201_);
if (lean_obj_tag(v___x_224_) == 0)
{
lean_object* v_a_225_; lean_object* v___x_226_; 
v_a_225_ = lean_ctor_get(v___x_224_, 0);
lean_inc(v_a_225_);
lean_dec_ref_known(v___x_224_, 1);
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
lean_dec_ref_known(v___x_244_, 1);
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
lean_dec_ref_known(v___x_256_, 1);
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
lean_dec_ref_known(v___x_277_, 1);
lean_inc_ref(v_k_276_);
v___x_279_ = l_Lean_Compiler_LCNF_Code_applyRenaming(v_pu_267_, v_k_276_, v_r_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_);
if (lean_obj_tag(v___x_279_) == 0)
{
lean_object* v_a_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_317_; 
v_a_280_ = lean_ctor_get(v___x_279_, 0);
v_isSharedCheck_317_ = !lean_is_exclusive(v___x_279_);
if (v_isSharedCheck_317_ == 0)
{
v___x_282_ = v___x_279_;
v_isShared_283_ = v_isSharedCheck_317_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_a_280_);
lean_dec(v___x_279_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_317_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
size_t v___x_284_; size_t v___x_285_; uint8_t v___x_286_; 
v___x_284_ = lean_ptr_addr(v_k_276_);
v___x_285_ = lean_ptr_addr(v_a_280_);
v___x_286_ = lean_usize_dec_eq(v___x_284_, v___x_285_);
if (v___x_286_ == 0)
{
lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_296_; 
v_isSharedCheck_296_ = !lean_is_exclusive(v_code_268_);
if (v_isSharedCheck_296_ == 0)
{
lean_object* v_unused_297_; lean_object* v_unused_298_; 
v_unused_297_ = lean_ctor_get(v_code_268_, 1);
lean_dec(v_unused_297_);
v_unused_298_ = lean_ctor_get(v_code_268_, 0);
lean_dec(v_unused_298_);
v___x_288_ = v_code_268_;
v_isShared_289_ = v_isSharedCheck_296_;
goto v_resetjp_287_;
}
else
{
lean_dec(v_code_268_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_296_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_291_; 
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 1, v_a_280_);
lean_ctor_set(v___x_288_, 0, v_a_278_);
v___x_291_ = v___x_288_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_a_278_);
lean_ctor_set(v_reuseFailAlloc_295_, 1, v_a_280_);
v___x_291_ = v_reuseFailAlloc_295_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
lean_object* v___x_293_; 
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 0, v___x_291_);
v___x_293_ = v___x_282_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v___x_291_);
v___x_293_ = v_reuseFailAlloc_294_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
return v___x_293_;
}
}
}
}
else
{
size_t v___x_299_; size_t v___x_300_; uint8_t v___x_301_; 
v___x_299_ = lean_ptr_addr(v_decl_275_);
v___x_300_ = lean_ptr_addr(v_a_278_);
v___x_301_ = lean_usize_dec_eq(v___x_299_, v___x_300_);
if (v___x_301_ == 0)
{
lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_311_; 
v_isSharedCheck_311_ = !lean_is_exclusive(v_code_268_);
if (v_isSharedCheck_311_ == 0)
{
lean_object* v_unused_312_; lean_object* v_unused_313_; 
v_unused_312_ = lean_ctor_get(v_code_268_, 1);
lean_dec(v_unused_312_);
v_unused_313_ = lean_ctor_get(v_code_268_, 0);
lean_dec(v_unused_313_);
v___x_303_ = v_code_268_;
v_isShared_304_ = v_isSharedCheck_311_;
goto v_resetjp_302_;
}
else
{
lean_dec(v_code_268_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_311_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_306_; 
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 1, v_a_280_);
lean_ctor_set(v___x_303_, 0, v_a_278_);
v___x_306_ = v___x_303_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v_a_278_);
lean_ctor_set(v_reuseFailAlloc_310_, 1, v_a_280_);
v___x_306_ = v_reuseFailAlloc_310_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
lean_object* v___x_308_; 
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 0, v___x_306_);
v___x_308_ = v___x_282_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v___x_306_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
return v___x_308_;
}
}
}
}
else
{
lean_object* v___x_315_; 
lean_dec(v_a_280_);
lean_dec(v_a_278_);
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 0, v_code_268_);
v___x_315_ = v___x_282_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_code_268_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
}
}
}
else
{
lean_dec(v_a_278_);
lean_dec_ref_known(v_code_268_, 2);
return v___x_279_;
}
}
else
{
lean_object* v_a_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_325_; 
lean_dec_ref_known(v_code_268_, 2);
v_a_318_ = lean_ctor_get(v___x_277_, 0);
v_isSharedCheck_325_ = !lean_is_exclusive(v___x_277_);
if (v_isSharedCheck_325_ == 0)
{
v___x_320_ = v___x_277_;
v_isShared_321_ = v_isSharedCheck_325_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_a_318_);
lean_dec(v___x_277_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_325_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_323_; 
if (v_isShared_321_ == 0)
{
v___x_323_ = v___x_320_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v_a_318_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
}
}
case 1:
{
lean_object* v_decl_326_; lean_object* v_k_327_; lean_object* v___x_328_; 
v_decl_326_ = lean_ctor_get(v_code_268_, 0);
v_k_327_ = lean_ctor_get(v_code_268_, 1);
lean_inc_ref(v_decl_326_);
v___x_328_ = l_Lean_Compiler_LCNF_FunDecl_applyRenaming(v_pu_267_, v_decl_326_, v_r_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_);
if (lean_obj_tag(v___x_328_) == 0)
{
lean_object* v_a_329_; lean_object* v___x_330_; 
v_a_329_ = lean_ctor_get(v___x_328_, 0);
lean_inc(v_a_329_);
lean_dec_ref_known(v___x_328_, 1);
lean_inc_ref(v_k_327_);
v___x_330_ = l_Lean_Compiler_LCNF_Code_applyRenaming(v_pu_267_, v_k_327_, v_r_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_);
if (lean_obj_tag(v___x_330_) == 0)
{
lean_object* v_a_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_368_; 
v_a_331_ = lean_ctor_get(v___x_330_, 0);
v_isSharedCheck_368_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_368_ == 0)
{
v___x_333_ = v___x_330_;
v_isShared_334_ = v_isSharedCheck_368_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_a_331_);
lean_dec(v___x_330_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_368_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
size_t v___x_335_; size_t v___x_336_; uint8_t v___x_337_; 
v___x_335_ = lean_ptr_addr(v_k_327_);
v___x_336_ = lean_ptr_addr(v_a_331_);
v___x_337_ = lean_usize_dec_eq(v___x_335_, v___x_336_);
if (v___x_337_ == 0)
{
lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_347_; 
v_isSharedCheck_347_ = !lean_is_exclusive(v_code_268_);
if (v_isSharedCheck_347_ == 0)
{
lean_object* v_unused_348_; lean_object* v_unused_349_; 
v_unused_348_ = lean_ctor_get(v_code_268_, 1);
lean_dec(v_unused_348_);
v_unused_349_ = lean_ctor_get(v_code_268_, 0);
lean_dec(v_unused_349_);
v___x_339_ = v_code_268_;
v_isShared_340_ = v_isSharedCheck_347_;
goto v_resetjp_338_;
}
else
{
lean_dec(v_code_268_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_347_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_342_; 
if (v_isShared_340_ == 0)
{
lean_ctor_set(v___x_339_, 1, v_a_331_);
lean_ctor_set(v___x_339_, 0, v_a_329_);
v___x_342_ = v___x_339_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v_a_329_);
lean_ctor_set(v_reuseFailAlloc_346_, 1, v_a_331_);
v___x_342_ = v_reuseFailAlloc_346_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
lean_object* v___x_344_; 
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 0, v___x_342_);
v___x_344_ = v___x_333_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v___x_342_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
}
}
else
{
size_t v___x_350_; size_t v___x_351_; uint8_t v___x_352_; 
v___x_350_ = lean_ptr_addr(v_decl_326_);
v___x_351_ = lean_ptr_addr(v_a_329_);
v___x_352_ = lean_usize_dec_eq(v___x_350_, v___x_351_);
if (v___x_352_ == 0)
{
lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_362_; 
v_isSharedCheck_362_ = !lean_is_exclusive(v_code_268_);
if (v_isSharedCheck_362_ == 0)
{
lean_object* v_unused_363_; lean_object* v_unused_364_; 
v_unused_363_ = lean_ctor_get(v_code_268_, 1);
lean_dec(v_unused_363_);
v_unused_364_ = lean_ctor_get(v_code_268_, 0);
lean_dec(v_unused_364_);
v___x_354_ = v_code_268_;
v_isShared_355_ = v_isSharedCheck_362_;
goto v_resetjp_353_;
}
else
{
lean_dec(v_code_268_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_362_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_357_; 
if (v_isShared_355_ == 0)
{
lean_ctor_set(v___x_354_, 1, v_a_331_);
lean_ctor_set(v___x_354_, 0, v_a_329_);
v___x_357_ = v___x_354_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_a_329_);
lean_ctor_set(v_reuseFailAlloc_361_, 1, v_a_331_);
v___x_357_ = v_reuseFailAlloc_361_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
lean_object* v___x_359_; 
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 0, v___x_357_);
v___x_359_ = v___x_333_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v___x_357_);
v___x_359_ = v_reuseFailAlloc_360_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
return v___x_359_;
}
}
}
}
else
{
lean_object* v___x_366_; 
lean_dec(v_a_331_);
lean_dec(v_a_329_);
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 0, v_code_268_);
v___x_366_ = v___x_333_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_code_268_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
return v___x_366_;
}
}
}
}
}
else
{
lean_dec(v_a_329_);
lean_dec_ref_known(v_code_268_, 2);
return v___x_330_;
}
}
else
{
lean_object* v_a_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_376_; 
lean_dec_ref_known(v_code_268_, 2);
v_a_369_ = lean_ctor_get(v___x_328_, 0);
v_isSharedCheck_376_ = !lean_is_exclusive(v___x_328_);
if (v_isSharedCheck_376_ == 0)
{
v___x_371_ = v___x_328_;
v_isShared_372_ = v_isSharedCheck_376_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_a_369_);
lean_dec(v___x_328_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_376_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_374_; 
if (v_isShared_372_ == 0)
{
v___x_374_ = v___x_371_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_a_369_);
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
case 2:
{
lean_object* v_decl_377_; lean_object* v_k_378_; lean_object* v___x_379_; 
v_decl_377_ = lean_ctor_get(v_code_268_, 0);
v_k_378_ = lean_ctor_get(v_code_268_, 1);
lean_inc_ref(v_decl_377_);
v___x_379_ = l_Lean_Compiler_LCNF_FunDecl_applyRenaming(v_pu_267_, v_decl_377_, v_r_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_);
if (lean_obj_tag(v___x_379_) == 0)
{
lean_object* v_a_380_; lean_object* v___x_381_; 
v_a_380_ = lean_ctor_get(v___x_379_, 0);
lean_inc(v_a_380_);
lean_dec_ref_known(v___x_379_, 1);
lean_inc_ref(v_k_378_);
v___x_381_ = l_Lean_Compiler_LCNF_Code_applyRenaming(v_pu_267_, v_k_378_, v_r_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_);
if (lean_obj_tag(v___x_381_) == 0)
{
lean_object* v_a_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_419_; 
v_a_382_ = lean_ctor_get(v___x_381_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_419_ == 0)
{
v___x_384_ = v___x_381_;
v_isShared_385_ = v_isSharedCheck_419_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_a_382_);
lean_dec(v___x_381_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_419_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
size_t v___x_386_; size_t v___x_387_; uint8_t v___x_388_; 
v___x_386_ = lean_ptr_addr(v_k_378_);
v___x_387_ = lean_ptr_addr(v_a_382_);
v___x_388_ = lean_usize_dec_eq(v___x_386_, v___x_387_);
if (v___x_388_ == 0)
{
lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_398_; 
v_isSharedCheck_398_ = !lean_is_exclusive(v_code_268_);
if (v_isSharedCheck_398_ == 0)
{
lean_object* v_unused_399_; lean_object* v_unused_400_; 
v_unused_399_ = lean_ctor_get(v_code_268_, 1);
lean_dec(v_unused_399_);
v_unused_400_ = lean_ctor_get(v_code_268_, 0);
lean_dec(v_unused_400_);
v___x_390_ = v_code_268_;
v_isShared_391_ = v_isSharedCheck_398_;
goto v_resetjp_389_;
}
else
{
lean_dec(v_code_268_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_398_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_393_; 
if (v_isShared_391_ == 0)
{
lean_ctor_set(v___x_390_, 1, v_a_382_);
lean_ctor_set(v___x_390_, 0, v_a_380_);
v___x_393_ = v___x_390_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_a_380_);
lean_ctor_set(v_reuseFailAlloc_397_, 1, v_a_382_);
v___x_393_ = v_reuseFailAlloc_397_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
lean_object* v___x_395_; 
if (v_isShared_385_ == 0)
{
lean_ctor_set(v___x_384_, 0, v___x_393_);
v___x_395_ = v___x_384_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v___x_393_);
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
else
{
size_t v___x_401_; size_t v___x_402_; uint8_t v___x_403_; 
v___x_401_ = lean_ptr_addr(v_decl_377_);
v___x_402_ = lean_ptr_addr(v_a_380_);
v___x_403_ = lean_usize_dec_eq(v___x_401_, v___x_402_);
if (v___x_403_ == 0)
{
lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_413_; 
v_isSharedCheck_413_ = !lean_is_exclusive(v_code_268_);
if (v_isSharedCheck_413_ == 0)
{
lean_object* v_unused_414_; lean_object* v_unused_415_; 
v_unused_414_ = lean_ctor_get(v_code_268_, 1);
lean_dec(v_unused_414_);
v_unused_415_ = lean_ctor_get(v_code_268_, 0);
lean_dec(v_unused_415_);
v___x_405_ = v_code_268_;
v_isShared_406_ = v_isSharedCheck_413_;
goto v_resetjp_404_;
}
else
{
lean_dec(v_code_268_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_413_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_408_; 
if (v_isShared_406_ == 0)
{
lean_ctor_set(v___x_405_, 1, v_a_382_);
lean_ctor_set(v___x_405_, 0, v_a_380_);
v___x_408_ = v___x_405_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v_a_380_);
lean_ctor_set(v_reuseFailAlloc_412_, 1, v_a_382_);
v___x_408_ = v_reuseFailAlloc_412_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
lean_object* v___x_410_; 
if (v_isShared_385_ == 0)
{
lean_ctor_set(v___x_384_, 0, v___x_408_);
v___x_410_ = v___x_384_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v___x_408_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
}
else
{
lean_object* v___x_417_; 
lean_dec(v_a_382_);
lean_dec(v_a_380_);
if (v_isShared_385_ == 0)
{
lean_ctor_set(v___x_384_, 0, v_code_268_);
v___x_417_ = v___x_384_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_code_268_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
}
}
else
{
lean_dec(v_a_380_);
lean_dec_ref_known(v_code_268_, 2);
return v___x_381_;
}
}
else
{
lean_object* v_a_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_427_; 
lean_dec_ref_known(v_code_268_, 2);
v_a_420_ = lean_ctor_get(v___x_379_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_427_ == 0)
{
v___x_422_ = v___x_379_;
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_a_420_);
lean_dec(v___x_379_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_425_; 
if (v_isShared_423_ == 0)
{
v___x_425_ = v___x_422_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v_a_420_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
return v___x_425_;
}
}
}
}
case 4:
{
lean_object* v_cases_428_; lean_object* v_typeName_429_; lean_object* v_resultType_430_; lean_object* v_discr_431_; lean_object* v_alts_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_471_; 
v_cases_428_ = lean_ctor_get(v_code_268_, 0);
lean_inc_ref(v_cases_428_);
v_typeName_429_ = lean_ctor_get(v_cases_428_, 0);
v_resultType_430_ = lean_ctor_get(v_cases_428_, 1);
v_discr_431_ = lean_ctor_get(v_cases_428_, 2);
v_alts_432_ = lean_ctor_get(v_cases_428_, 3);
v_isSharedCheck_471_ = !lean_is_exclusive(v_cases_428_);
if (v_isSharedCheck_471_ == 0)
{
v___x_434_ = v_cases_428_;
v_isShared_435_ = v_isSharedCheck_471_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_alts_432_);
lean_inc(v_discr_431_);
lean_inc(v_resultType_430_);
lean_inc(v_typeName_429_);
lean_dec(v_cases_428_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_471_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_436_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_432_);
v___x_437_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__2(v_pu_267_, v_r_269_, v___x_436_, v_alts_432_, v_a_270_, v_a_271_, v_a_272_, v_a_273_);
if (lean_obj_tag(v___x_437_) == 0)
{
lean_object* v_a_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_462_; 
v_a_438_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_462_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_462_ == 0)
{
v___x_440_ = v___x_437_;
v_isShared_441_ = v_isSharedCheck_462_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_a_438_);
lean_dec(v___x_437_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_462_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
size_t v___x_442_; size_t v___x_443_; uint8_t v___x_444_; 
v___x_442_ = lean_ptr_addr(v_alts_432_);
lean_dec_ref(v_alts_432_);
v___x_443_ = lean_ptr_addr(v_a_438_);
v___x_444_ = lean_usize_dec_eq(v___x_442_, v___x_443_);
if (v___x_444_ == 0)
{
lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_457_; 
v_isSharedCheck_457_ = !lean_is_exclusive(v_code_268_);
if (v_isSharedCheck_457_ == 0)
{
lean_object* v_unused_458_; 
v_unused_458_ = lean_ctor_get(v_code_268_, 0);
lean_dec(v_unused_458_);
v___x_446_ = v_code_268_;
v_isShared_447_ = v_isSharedCheck_457_;
goto v_resetjp_445_;
}
else
{
lean_dec(v_code_268_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_457_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v___x_449_; 
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 3, v_a_438_);
v___x_449_ = v___x_434_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_typeName_429_);
lean_ctor_set(v_reuseFailAlloc_456_, 1, v_resultType_430_);
lean_ctor_set(v_reuseFailAlloc_456_, 2, v_discr_431_);
lean_ctor_set(v_reuseFailAlloc_456_, 3, v_a_438_);
v___x_449_ = v_reuseFailAlloc_456_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
lean_object* v___x_451_; 
if (v_isShared_447_ == 0)
{
lean_ctor_set(v___x_446_, 0, v___x_449_);
v___x_451_ = v___x_446_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v___x_449_);
v___x_451_ = v_reuseFailAlloc_455_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
lean_object* v___x_453_; 
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 0, v___x_451_);
v___x_453_ = v___x_440_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v___x_451_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
}
}
else
{
lean_object* v___x_460_; 
lean_dec(v_a_438_);
lean_del_object(v___x_434_);
lean_dec(v_discr_431_);
lean_dec_ref(v_resultType_430_);
lean_dec(v_typeName_429_);
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 0, v_code_268_);
v___x_460_ = v___x_440_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_code_268_);
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
lean_object* v_a_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_470_; 
lean_del_object(v___x_434_);
lean_dec_ref(v_alts_432_);
lean_dec(v_discr_431_);
lean_dec_ref(v_resultType_430_);
lean_dec(v_typeName_429_);
lean_dec_ref_known(v_code_268_, 1);
v_a_463_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_470_ == 0)
{
v___x_465_ = v___x_437_;
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_a_463_);
lean_dec(v___x_437_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_468_; 
if (v_isShared_466_ == 0)
{
v___x_468_ = v___x_465_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_a_463_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
}
}
case 7:
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
v_reuseFailAlloc_492_ = lean_alloc_ctor(7, 4, 0);
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
lean_dec_ref_known(v_code_268_, 4);
return v___x_476_;
}
}
case 8:
{
lean_object* v_fvarId_502_; lean_object* v_i_503_; lean_object* v_y_504_; lean_object* v_k_505_; lean_object* v___x_506_; 
v_fvarId_502_ = lean_ctor_get(v_code_268_, 0);
v_i_503_ = lean_ctor_get(v_code_268_, 1);
v_y_504_ = lean_ctor_get(v_code_268_, 2);
v_k_505_ = lean_ctor_get(v_code_268_, 3);
lean_inc_ref(v_k_505_);
v___x_506_ = l_Lean_Compiler_LCNF_Code_applyRenaming(v_pu_267_, v_k_505_, v_r_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_);
if (lean_obj_tag(v___x_506_) == 0)
{
lean_object* v_a_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_531_; 
v_a_507_ = lean_ctor_get(v___x_506_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_506_);
if (v_isSharedCheck_531_ == 0)
{
v___x_509_ = v___x_506_;
v_isShared_510_ = v_isSharedCheck_531_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_a_507_);
lean_dec(v___x_506_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_531_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
size_t v___x_511_; size_t v___x_512_; uint8_t v___x_513_; 
v___x_511_ = lean_ptr_addr(v_k_505_);
v___x_512_ = lean_ptr_addr(v_a_507_);
v___x_513_ = lean_usize_dec_eq(v___x_511_, v___x_512_);
if (v___x_513_ == 0)
{
lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_523_; 
lean_inc(v_y_504_);
lean_inc(v_i_503_);
lean_inc(v_fvarId_502_);
v_isSharedCheck_523_ = !lean_is_exclusive(v_code_268_);
if (v_isSharedCheck_523_ == 0)
{
lean_object* v_unused_524_; lean_object* v_unused_525_; lean_object* v_unused_526_; lean_object* v_unused_527_; 
v_unused_524_ = lean_ctor_get(v_code_268_, 3);
lean_dec(v_unused_524_);
v_unused_525_ = lean_ctor_get(v_code_268_, 2);
lean_dec(v_unused_525_);
v_unused_526_ = lean_ctor_get(v_code_268_, 1);
lean_dec(v_unused_526_);
v_unused_527_ = lean_ctor_get(v_code_268_, 0);
lean_dec(v_unused_527_);
v___x_515_ = v_code_268_;
v_isShared_516_ = v_isSharedCheck_523_;
goto v_resetjp_514_;
}
else
{
lean_dec(v_code_268_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_523_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_518_; 
if (v_isShared_516_ == 0)
{
lean_ctor_set(v___x_515_, 3, v_a_507_);
v___x_518_ = v___x_515_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_fvarId_502_);
lean_ctor_set(v_reuseFailAlloc_522_, 1, v_i_503_);
lean_ctor_set(v_reuseFailAlloc_522_, 2, v_y_504_);
lean_ctor_set(v_reuseFailAlloc_522_, 3, v_a_507_);
v___x_518_ = v_reuseFailAlloc_522_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
lean_object* v___x_520_; 
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 0, v___x_518_);
v___x_520_ = v___x_509_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v___x_518_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
}
}
else
{
lean_object* v___x_529_; 
lean_dec(v_a_507_);
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 0, v_code_268_);
v___x_529_ = v___x_509_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_code_268_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_268_, 4);
return v___x_506_;
}
}
case 9:
{
lean_object* v_fvarId_532_; lean_object* v_i_533_; lean_object* v_offset_534_; lean_object* v_y_535_; lean_object* v_ty_536_; lean_object* v_k_537_; lean_object* v___x_538_; 
v_fvarId_532_ = lean_ctor_get(v_code_268_, 0);
v_i_533_ = lean_ctor_get(v_code_268_, 1);
v_offset_534_ = lean_ctor_get(v_code_268_, 2);
v_y_535_ = lean_ctor_get(v_code_268_, 3);
v_ty_536_ = lean_ctor_get(v_code_268_, 4);
v_k_537_ = lean_ctor_get(v_code_268_, 5);
lean_inc_ref(v_k_537_);
v___x_538_ = l_Lean_Compiler_LCNF_Code_applyRenaming(v_pu_267_, v_k_537_, v_r_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_);
if (lean_obj_tag(v___x_538_) == 0)
{
lean_object* v_a_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_565_; 
v_a_539_ = lean_ctor_get(v___x_538_, 0);
v_isSharedCheck_565_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_565_ == 0)
{
v___x_541_ = v___x_538_;
v_isShared_542_ = v_isSharedCheck_565_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_a_539_);
lean_dec(v___x_538_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_565_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
size_t v___x_543_; size_t v___x_544_; uint8_t v___x_545_; 
v___x_543_ = lean_ptr_addr(v_k_537_);
v___x_544_ = lean_ptr_addr(v_a_539_);
v___x_545_ = lean_usize_dec_eq(v___x_543_, v___x_544_);
if (v___x_545_ == 0)
{
lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_555_; 
lean_inc_ref(v_ty_536_);
lean_inc(v_y_535_);
lean_inc(v_offset_534_);
lean_inc(v_i_533_);
lean_inc(v_fvarId_532_);
v_isSharedCheck_555_ = !lean_is_exclusive(v_code_268_);
if (v_isSharedCheck_555_ == 0)
{
lean_object* v_unused_556_; lean_object* v_unused_557_; lean_object* v_unused_558_; lean_object* v_unused_559_; lean_object* v_unused_560_; lean_object* v_unused_561_; 
v_unused_556_ = lean_ctor_get(v_code_268_, 5);
lean_dec(v_unused_556_);
v_unused_557_ = lean_ctor_get(v_code_268_, 4);
lean_dec(v_unused_557_);
v_unused_558_ = lean_ctor_get(v_code_268_, 3);
lean_dec(v_unused_558_);
v_unused_559_ = lean_ctor_get(v_code_268_, 2);
lean_dec(v_unused_559_);
v_unused_560_ = lean_ctor_get(v_code_268_, 1);
lean_dec(v_unused_560_);
v_unused_561_ = lean_ctor_get(v_code_268_, 0);
lean_dec(v_unused_561_);
v___x_547_ = v_code_268_;
v_isShared_548_ = v_isSharedCheck_555_;
goto v_resetjp_546_;
}
else
{
lean_dec(v_code_268_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_555_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_550_; 
if (v_isShared_548_ == 0)
{
lean_ctor_set(v___x_547_, 5, v_a_539_);
v___x_550_ = v___x_547_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_fvarId_532_);
lean_ctor_set(v_reuseFailAlloc_554_, 1, v_i_533_);
lean_ctor_set(v_reuseFailAlloc_554_, 2, v_offset_534_);
lean_ctor_set(v_reuseFailAlloc_554_, 3, v_y_535_);
lean_ctor_set(v_reuseFailAlloc_554_, 4, v_ty_536_);
lean_ctor_set(v_reuseFailAlloc_554_, 5, v_a_539_);
v___x_550_ = v_reuseFailAlloc_554_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
lean_object* v___x_552_; 
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 0, v___x_550_);
v___x_552_ = v___x_541_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v___x_550_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
}
else
{
lean_object* v___x_563_; 
lean_dec(v_a_539_);
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 0, v_code_268_);
v___x_563_ = v___x_541_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v_code_268_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
return v___x_563_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_268_, 6);
return v___x_538_;
}
}
case 10:
{
lean_object* v_fvarId_566_; lean_object* v_cidx_567_; lean_object* v_k_568_; lean_object* v___x_569_; 
v_fvarId_566_ = lean_ctor_get(v_code_268_, 0);
v_cidx_567_ = lean_ctor_get(v_code_268_, 1);
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
lean_inc(v_cidx_567_);
lean_inc(v_fvarId_566_);
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
v_reuseFailAlloc_585_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_fvarId_566_);
lean_ctor_set(v_reuseFailAlloc_585_, 1, v_cidx_567_);
lean_ctor_set(v_reuseFailAlloc_585_, 2, v_a_570_);
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
lean_dec_ref_known(v_code_268_, 3);
return v___x_569_;
}
}
case 11:
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
v_reuseFailAlloc_615_ = lean_alloc_ctor(11, 3, 2);
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
lean_dec_ref_known(v_code_268_, 3);
return v___x_599_;
}
}
case 12:
{
lean_object* v_fvarId_624_; lean_object* v_n_625_; uint8_t v_check_626_; uint8_t v_persistent_627_; lean_object* v_objs_x3f_628_; lean_object* v_k_629_; lean_object* v___x_630_; 
v_fvarId_624_ = lean_ctor_get(v_code_268_, 0);
v_n_625_ = lean_ctor_get(v_code_268_, 1);
v_check_626_ = lean_ctor_get_uint8(v_code_268_, sizeof(void*)*4);
v_persistent_627_ = lean_ctor_get_uint8(v_code_268_, sizeof(void*)*4 + 1);
v_objs_x3f_628_ = lean_ctor_get(v_code_268_, 2);
v_k_629_ = lean_ctor_get(v_code_268_, 3);
lean_inc_ref(v_k_629_);
v___x_630_ = l_Lean_Compiler_LCNF_Code_applyRenaming(v_pu_267_, v_k_629_, v_r_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_);
if (lean_obj_tag(v___x_630_) == 0)
{
lean_object* v_a_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_655_; 
v_a_631_ = lean_ctor_get(v___x_630_, 0);
v_isSharedCheck_655_ = !lean_is_exclusive(v___x_630_);
if (v_isSharedCheck_655_ == 0)
{
v___x_633_ = v___x_630_;
v_isShared_634_ = v_isSharedCheck_655_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_a_631_);
lean_dec(v___x_630_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_655_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
size_t v___x_635_; size_t v___x_636_; uint8_t v___x_637_; 
v___x_635_ = lean_ptr_addr(v_k_629_);
v___x_636_ = lean_ptr_addr(v_a_631_);
v___x_637_ = lean_usize_dec_eq(v___x_635_, v___x_636_);
if (v___x_637_ == 0)
{
lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_647_; 
lean_inc(v_objs_x3f_628_);
lean_inc(v_n_625_);
lean_inc(v_fvarId_624_);
v_isSharedCheck_647_ = !lean_is_exclusive(v_code_268_);
if (v_isSharedCheck_647_ == 0)
{
lean_object* v_unused_648_; lean_object* v_unused_649_; lean_object* v_unused_650_; lean_object* v_unused_651_; 
v_unused_648_ = lean_ctor_get(v_code_268_, 3);
lean_dec(v_unused_648_);
v_unused_649_ = lean_ctor_get(v_code_268_, 2);
lean_dec(v_unused_649_);
v_unused_650_ = lean_ctor_get(v_code_268_, 1);
lean_dec(v_unused_650_);
v_unused_651_ = lean_ctor_get(v_code_268_, 0);
lean_dec(v_unused_651_);
v___x_639_ = v_code_268_;
v_isShared_640_ = v_isSharedCheck_647_;
goto v_resetjp_638_;
}
else
{
lean_dec(v_code_268_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_647_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_642_; 
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 3, v_a_631_);
v___x_642_ = v___x_639_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_fvarId_624_);
lean_ctor_set(v_reuseFailAlloc_646_, 1, v_n_625_);
lean_ctor_set(v_reuseFailAlloc_646_, 2, v_objs_x3f_628_);
lean_ctor_set(v_reuseFailAlloc_646_, 3, v_a_631_);
lean_ctor_set_uint8(v_reuseFailAlloc_646_, sizeof(void*)*4, v_check_626_);
lean_ctor_set_uint8(v_reuseFailAlloc_646_, sizeof(void*)*4 + 1, v_persistent_627_);
v___x_642_ = v_reuseFailAlloc_646_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
lean_object* v___x_644_; 
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 0, v___x_642_);
v___x_644_ = v___x_633_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v___x_642_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
return v___x_644_;
}
}
}
}
else
{
lean_object* v___x_653_; 
lean_dec(v_a_631_);
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 0, v_code_268_);
v___x_653_ = v___x_633_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_code_268_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_268_, 4);
return v___x_630_;
}
}
case 13:
{
lean_object* v_fvarId_656_; lean_object* v_k_657_; lean_object* v___x_658_; 
v_fvarId_656_ = lean_ctor_get(v_code_268_, 0);
v_k_657_ = lean_ctor_get(v_code_268_, 1);
lean_inc_ref(v_k_657_);
v___x_658_ = l_Lean_Compiler_LCNF_Code_applyRenaming(v_pu_267_, v_k_657_, v_r_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_);
if (lean_obj_tag(v___x_658_) == 0)
{
lean_object* v_a_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_681_; 
v_a_659_ = lean_ctor_get(v___x_658_, 0);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_681_ == 0)
{
v___x_661_ = v___x_658_;
v_isShared_662_ = v_isSharedCheck_681_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_a_659_);
lean_dec(v___x_658_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_681_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
size_t v___x_663_; size_t v___x_664_; uint8_t v___x_665_; 
v___x_663_ = lean_ptr_addr(v_k_657_);
v___x_664_ = lean_ptr_addr(v_a_659_);
v___x_665_ = lean_usize_dec_eq(v___x_663_, v___x_664_);
if (v___x_665_ == 0)
{
lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_675_; 
lean_inc(v_fvarId_656_);
v_isSharedCheck_675_ = !lean_is_exclusive(v_code_268_);
if (v_isSharedCheck_675_ == 0)
{
lean_object* v_unused_676_; lean_object* v_unused_677_; 
v_unused_676_ = lean_ctor_get(v_code_268_, 1);
lean_dec(v_unused_676_);
v_unused_677_ = lean_ctor_get(v_code_268_, 0);
lean_dec(v_unused_677_);
v___x_667_ = v_code_268_;
v_isShared_668_ = v_isSharedCheck_675_;
goto v_resetjp_666_;
}
else
{
lean_dec(v_code_268_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_675_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_670_; 
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 1, v_a_659_);
v___x_670_ = v___x_667_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v_fvarId_656_);
lean_ctor_set(v_reuseFailAlloc_674_, 1, v_a_659_);
v___x_670_ = v_reuseFailAlloc_674_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
lean_object* v___x_672_; 
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 0, v___x_670_);
v___x_672_ = v___x_661_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v___x_670_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
}
}
else
{
lean_object* v___x_679_; 
lean_dec(v_a_659_);
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 0, v_code_268_);
v___x_679_ = v___x_661_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_code_268_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_268_, 2);
return v___x_658_;
}
}
default: 
{
lean_object* v___x_682_; 
v___x_682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_682_, 0, v_code_268_);
return v___x_682_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_applyRenaming(uint8_t v_pu_683_, lean_object* v_decl_684_, lean_object* v_r_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_){
_start:
{
lean_object* v_fvarId_691_; lean_object* v_params_692_; lean_object* v_type_693_; lean_object* v_value_694_; lean_object* v___x_695_; 
v_fvarId_691_ = lean_ctor_get(v_decl_684_, 0);
v_params_692_ = lean_ctor_get(v_decl_684_, 2);
lean_inc_ref(v_params_692_);
v_type_693_ = lean_ctor_get(v_decl_684_, 3);
lean_inc_ref(v_type_693_);
v_value_694_ = lean_ctor_get(v_decl_684_, 4);
v___x_695_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Param_applyRenaming_spec__0___redArg(v_r_685_, v_fvarId_691_);
if (lean_obj_tag(v___x_695_) == 1)
{
lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_726_; 
lean_inc_ref(v_value_694_);
lean_inc(v_fvarId_691_);
v_isSharedCheck_726_ = !lean_is_exclusive(v_decl_684_);
if (v_isSharedCheck_726_ == 0)
{
lean_object* v_unused_727_; lean_object* v_unused_728_; lean_object* v_unused_729_; lean_object* v_unused_730_; lean_object* v_unused_731_; 
v_unused_727_ = lean_ctor_get(v_decl_684_, 4);
lean_dec(v_unused_727_);
v_unused_728_ = lean_ctor_get(v_decl_684_, 3);
lean_dec(v_unused_728_);
v_unused_729_ = lean_ctor_get(v_decl_684_, 2);
lean_dec(v_unused_729_);
v_unused_730_ = lean_ctor_get(v_decl_684_, 1);
lean_dec(v_unused_730_);
v_unused_731_ = lean_ctor_get(v_decl_684_, 0);
lean_dec(v_unused_731_);
v___x_697_ = v_decl_684_;
v_isShared_698_ = v_isSharedCheck_726_;
goto v_resetjp_696_;
}
else
{
lean_dec(v_decl_684_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_726_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v_val_699_; lean_object* v___x_700_; lean_object* v_lctx_701_; lean_object* v_nextIdx_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_725_; 
v_val_699_ = lean_ctor_get(v___x_695_, 0);
lean_inc(v_val_699_);
lean_dec_ref_known(v___x_695_, 1);
v___x_700_ = lean_st_ref_take(v_a_687_);
v_lctx_701_ = lean_ctor_get(v___x_700_, 0);
v_nextIdx_702_ = lean_ctor_get(v___x_700_, 1);
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_725_ == 0)
{
v___x_704_ = v___x_700_;
v_isShared_705_ = v_isSharedCheck_725_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_nextIdx_702_);
lean_inc(v_lctx_701_);
lean_dec(v___x_700_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_725_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v_decl_707_; 
lean_inc_ref(v_value_694_);
lean_inc_ref(v_type_693_);
lean_inc_ref(v_params_692_);
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 1, v_val_699_);
v_decl_707_ = v___x_697_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_fvarId_691_);
lean_ctor_set(v_reuseFailAlloc_724_, 1, v_val_699_);
lean_ctor_set(v_reuseFailAlloc_724_, 2, v_params_692_);
lean_ctor_set(v_reuseFailAlloc_724_, 3, v_type_693_);
lean_ctor_set(v_reuseFailAlloc_724_, 4, v_value_694_);
v_decl_707_ = v_reuseFailAlloc_724_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
lean_object* v___x_708_; lean_object* v___x_710_; 
lean_inc_ref(v_decl_707_);
v___x_708_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v_pu_683_, v_lctx_701_, v_decl_707_);
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 0, v___x_708_);
v___x_710_ = v___x_704_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v___x_708_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v_nextIdx_702_);
v___x_710_ = v_reuseFailAlloc_723_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_711_ = lean_st_ref_put(v_a_687_, v___x_710_);
v___x_712_ = l_Lean_Compiler_LCNF_Code_applyRenaming(v_pu_683_, v_value_694_, v_r_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_);
if (lean_obj_tag(v___x_712_) == 0)
{
lean_object* v_a_713_; lean_object* v___x_714_; 
v_a_713_ = lean_ctor_get(v___x_712_, 0);
lean_inc(v_a_713_);
lean_dec_ref_known(v___x_712_, 1);
v___x_714_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_683_, v_decl_707_, v_type_693_, v_params_692_, v_a_713_, v_a_687_);
return v___x_714_;
}
else
{
lean_object* v_a_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_722_; 
lean_dec_ref(v_decl_707_);
lean_dec_ref(v_type_693_);
lean_dec_ref(v_params_692_);
v_a_715_ = lean_ctor_get(v___x_712_, 0);
v_isSharedCheck_722_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_722_ == 0)
{
v___x_717_ = v___x_712_;
v_isShared_718_ = v_isSharedCheck_722_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_a_715_);
lean_dec(v___x_712_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_722_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___x_720_; 
if (v_isShared_718_ == 0)
{
v___x_720_ = v___x_717_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_a_715_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
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
lean_object* v___x_732_; 
lean_dec(v___x_695_);
lean_inc_ref(v_value_694_);
v___x_732_ = l_Lean_Compiler_LCNF_Code_applyRenaming(v_pu_683_, v_value_694_, v_r_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_);
if (lean_obj_tag(v___x_732_) == 0)
{
lean_object* v_a_733_; lean_object* v___x_734_; 
v_a_733_ = lean_ctor_get(v___x_732_, 0);
lean_inc(v_a_733_);
lean_dec_ref_known(v___x_732_, 1);
v___x_734_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_683_, v_decl_684_, v_type_693_, v_params_692_, v_a_733_, v_a_687_);
return v___x_734_;
}
else
{
lean_object* v_a_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_742_; 
lean_dec_ref(v_type_693_);
lean_dec_ref(v_params_692_);
lean_dec_ref(v_decl_684_);
v_a_735_ = lean_ctor_get(v___x_732_, 0);
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_742_ == 0)
{
v___x_737_ = v___x_732_;
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_a_735_);
lean_dec(v___x_732_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_740_; 
if (v_isShared_738_ == 0)
{
v___x_740_ = v___x_737_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v_a_735_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_applyRenaming___boxed(lean_object* v_pu_743_, lean_object* v_decl_744_, lean_object* v_r_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_){
_start:
{
uint8_t v_pu_boxed_751_; lean_object* v_res_752_; 
v_pu_boxed_751_ = lean_unbox(v_pu_743_);
v_res_752_ = l_Lean_Compiler_LCNF_FunDecl_applyRenaming(v_pu_boxed_751_, v_decl_744_, v_r_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_);
lean_dec(v_a_749_);
lean_dec_ref(v_a_748_);
lean_dec(v_a_747_);
lean_dec_ref(v_a_746_);
lean_dec(v_r_745_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__2___boxed(lean_object* v_pu_753_, lean_object* v_r_754_, lean_object* v_i_755_, lean_object* v_as_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_){
_start:
{
uint8_t v_pu_boxed_762_; lean_object* v_res_763_; 
v_pu_boxed_762_ = lean_unbox(v_pu_753_);
v_res_763_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__2(v_pu_boxed_762_, v_r_754_, v_i_755_, v_as_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_);
lean_dec(v___y_760_);
lean_dec_ref(v___y_759_);
lean_dec(v___y_758_);
lean_dec_ref(v___y_757_);
lean_dec(v_r_754_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_applyRenaming___boxed(lean_object* v_pu_764_, lean_object* v_code_765_, lean_object* v_r_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_){
_start:
{
uint8_t v_pu_boxed_772_; lean_object* v_res_773_; 
v_pu_boxed_772_ = lean_unbox(v_pu_764_);
v_res_773_ = l_Lean_Compiler_LCNF_Code_applyRenaming(v_pu_boxed_772_, v_code_765_, v_r_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_);
lean_dec(v_a_770_);
lean_dec_ref(v_a_769_);
lean_dec(v_a_768_);
lean_dec_ref(v_a_767_);
lean_dec(v_r_766_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__1(uint8_t v_pu_774_, lean_object* v_r_775_, lean_object* v_i_776_, lean_object* v_as_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_){
_start:
{
lean_object* v___x_783_; 
v___x_783_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__1___redArg(v_pu_774_, v_r_775_, v_i_776_, v_as_777_, v___y_779_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__1___boxed(lean_object* v_pu_784_, lean_object* v_r_785_, lean_object* v_i_786_, lean_object* v_as_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_){
_start:
{
uint8_t v_pu_boxed_793_; lean_object* v_res_794_; 
v_pu_boxed_793_ = lean_unbox(v_pu_784_);
v_res_794_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__1(v_pu_boxed_793_, v_r_785_, v_i_786_, v_as_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_);
lean_dec(v___y_791_);
lean_dec_ref(v___y_790_);
lean_dec(v___y_789_);
lean_dec_ref(v___y_788_);
lean_dec(v_r_785_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_applyRenaming_spec__0___redArg(lean_object* v_f_795_, lean_object* v_v_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_){
_start:
{
if (lean_obj_tag(v_v_796_) == 0)
{
lean_object* v_code_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_826_; 
v_code_802_ = lean_ctor_get(v_v_796_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v_v_796_);
if (v_isSharedCheck_826_ == 0)
{
v___x_804_ = v_v_796_;
v_isShared_805_ = v_isSharedCheck_826_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_code_802_);
lean_dec(v_v_796_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_826_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_806_; 
lean_inc(v___y_800_);
lean_inc_ref(v___y_799_);
lean_inc(v___y_798_);
lean_inc_ref(v___y_797_);
v___x_806_ = lean_apply_6(v_f_795_, v_code_802_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, lean_box(0));
if (lean_obj_tag(v___x_806_) == 0)
{
lean_object* v_a_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_817_; 
v_a_807_ = lean_ctor_get(v___x_806_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_806_);
if (v_isSharedCheck_817_ == 0)
{
v___x_809_ = v___x_806_;
v_isShared_810_ = v_isSharedCheck_817_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_a_807_);
lean_dec(v___x_806_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_817_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_812_; 
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 0, v_a_807_);
v___x_812_ = v___x_804_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_a_807_);
v___x_812_ = v_reuseFailAlloc_816_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
lean_object* v___x_814_; 
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 0, v___x_812_);
v___x_814_ = v___x_809_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v___x_812_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
}
}
else
{
lean_object* v_a_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_825_; 
lean_del_object(v___x_804_);
v_a_818_ = lean_ctor_get(v___x_806_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_806_);
if (v_isSharedCheck_825_ == 0)
{
v___x_820_ = v___x_806_;
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_a_818_);
lean_dec(v___x_806_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_823_; 
if (v_isShared_821_ == 0)
{
v___x_823_ = v___x_820_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_a_818_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
}
}
else
{
lean_object* v___x_827_; 
lean_dec_ref(v_f_795_);
v___x_827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_827_, 0, v_v_796_);
return v___x_827_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_applyRenaming_spec__0___redArg___boxed(lean_object* v_f_828_, lean_object* v_v_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_applyRenaming_spec__0___redArg(v_f_828_, v_v_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_);
lean_dec(v___y_833_);
lean_dec_ref(v___y_832_);
lean_dec(v___y_831_);
lean_dec_ref(v___y_830_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_applyRenaming_spec__0(uint8_t v_pu_836_, lean_object* v_f_837_, lean_object* v_v_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_){
_start:
{
lean_object* v___x_844_; 
v___x_844_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_applyRenaming_spec__0___redArg(v_f_837_, v_v_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_applyRenaming_spec__0___boxed(lean_object* v_pu_845_, lean_object* v_f_846_, lean_object* v_v_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
uint8_t v_pu_boxed_853_; lean_object* v_res_854_; 
v_pu_boxed_853_ = lean_unbox(v_pu_845_);
v_res_854_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_applyRenaming_spec__0(v_pu_boxed_853_, v_f_846_, v_v_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_applyRenaming___lam__0(uint8_t v_pu_855_, lean_object* v_r_856_, lean_object* v_x_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_){
_start:
{
lean_object* v___x_863_; 
v___x_863_ = l_Lean_Compiler_LCNF_Code_applyRenaming(v_pu_855_, v_x_857_, v_r_856_, v___y_858_, v___y_859_, v___y_860_, v___y_861_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_applyRenaming___lam__0___boxed(lean_object* v_pu_864_, lean_object* v_r_865_, lean_object* v_x_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_){
_start:
{
uint8_t v_pu_boxed_872_; lean_object* v_res_873_; 
v_pu_boxed_872_ = lean_unbox(v_pu_864_);
v_res_873_ = l_Lean_Compiler_LCNF_Decl_applyRenaming___lam__0(v_pu_boxed_872_, v_r_865_, v_x_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_);
lean_dec(v___y_870_);
lean_dec_ref(v___y_869_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
lean_dec(v_r_865_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_applyRenaming(uint8_t v_pu_874_, lean_object* v_decl_875_, lean_object* v_r_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_){
_start:
{
if (lean_obj_tag(v_r_876_) == 0)
{
lean_object* v_toSignature_882_; lean_object* v_value_883_; uint8_t v_recursive_884_; lean_object* v_inlineAttr_x3f_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_934_; 
v_toSignature_882_ = lean_ctor_get(v_decl_875_, 0);
v_value_883_ = lean_ctor_get(v_decl_875_, 1);
v_recursive_884_ = lean_ctor_get_uint8(v_decl_875_, sizeof(void*)*3);
v_inlineAttr_x3f_885_ = lean_ctor_get(v_decl_875_, 2);
v_isSharedCheck_934_ = !lean_is_exclusive(v_decl_875_);
if (v_isSharedCheck_934_ == 0)
{
v___x_887_ = v_decl_875_;
v_isShared_888_ = v_isSharedCheck_934_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_inlineAttr_x3f_885_);
lean_inc(v_value_883_);
lean_inc(v_toSignature_882_);
lean_dec(v_decl_875_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_934_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v_name_889_; lean_object* v_levelParams_890_; lean_object* v_type_891_; lean_object* v_params_892_; uint8_t v_safe_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_933_; 
v_name_889_ = lean_ctor_get(v_toSignature_882_, 0);
v_levelParams_890_ = lean_ctor_get(v_toSignature_882_, 1);
v_type_891_ = lean_ctor_get(v_toSignature_882_, 2);
v_params_892_ = lean_ctor_get(v_toSignature_882_, 3);
v_safe_893_ = lean_ctor_get_uint8(v_toSignature_882_, sizeof(void*)*4);
v_isSharedCheck_933_ = !lean_is_exclusive(v_toSignature_882_);
if (v_isSharedCheck_933_ == 0)
{
v___x_895_ = v_toSignature_882_;
v_isShared_896_ = v_isSharedCheck_933_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_params_892_);
lean_inc(v_type_891_);
lean_inc(v_levelParams_890_);
lean_inc(v_name_889_);
lean_dec(v_toSignature_882_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_933_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_897_ = lean_unsigned_to_nat(0u);
v___x_898_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__1___redArg(v_pu_874_, v_r_876_, v___x_897_, v_params_892_, v_a_878_);
if (lean_obj_tag(v___x_898_) == 0)
{
lean_object* v_a_899_; lean_object* v___x_900_; lean_object* v___f_901_; lean_object* v___x_902_; 
v_a_899_ = lean_ctor_get(v___x_898_, 0);
lean_inc(v_a_899_);
lean_dec_ref_known(v___x_898_, 1);
v___x_900_ = lean_box(v_pu_874_);
v___f_901_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_applyRenaming___lam__0___boxed), 8, 2);
lean_closure_set(v___f_901_, 0, v___x_900_);
lean_closure_set(v___f_901_, 1, v_r_876_);
v___x_902_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_applyRenaming_spec__0___redArg(v___f_901_, v_value_883_, v_a_877_, v_a_878_, v_a_879_, v_a_880_);
if (lean_obj_tag(v___x_902_) == 0)
{
lean_object* v_a_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_916_; 
v_a_903_ = lean_ctor_get(v___x_902_, 0);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_916_ == 0)
{
v___x_905_ = v___x_902_;
v_isShared_906_ = v_isSharedCheck_916_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_a_903_);
lean_dec(v___x_902_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_916_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_908_; 
if (v_isShared_896_ == 0)
{
lean_ctor_set(v___x_895_, 3, v_a_899_);
v___x_908_ = v___x_895_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_name_889_);
lean_ctor_set(v_reuseFailAlloc_915_, 1, v_levelParams_890_);
lean_ctor_set(v_reuseFailAlloc_915_, 2, v_type_891_);
lean_ctor_set(v_reuseFailAlloc_915_, 3, v_a_899_);
lean_ctor_set_uint8(v_reuseFailAlloc_915_, sizeof(void*)*4, v_safe_893_);
v___x_908_ = v_reuseFailAlloc_915_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
lean_object* v___x_910_; 
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 1, v_a_903_);
lean_ctor_set(v___x_887_, 0, v___x_908_);
v___x_910_ = v___x_887_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v___x_908_);
lean_ctor_set(v_reuseFailAlloc_914_, 1, v_a_903_);
lean_ctor_set(v_reuseFailAlloc_914_, 2, v_inlineAttr_x3f_885_);
lean_ctor_set_uint8(v_reuseFailAlloc_914_, sizeof(void*)*3, v_recursive_884_);
v___x_910_ = v_reuseFailAlloc_914_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
lean_object* v___x_912_; 
if (v_isShared_906_ == 0)
{
lean_ctor_set(v___x_905_, 0, v___x_910_);
v___x_912_ = v___x_905_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v___x_910_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
}
}
}
else
{
lean_object* v_a_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_924_; 
lean_dec(v_a_899_);
lean_del_object(v___x_895_);
lean_dec_ref(v_type_891_);
lean_dec(v_levelParams_890_);
lean_dec(v_name_889_);
lean_del_object(v___x_887_);
lean_dec(v_inlineAttr_x3f_885_);
v_a_917_ = lean_ctor_get(v___x_902_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_924_ == 0)
{
v___x_919_ = v___x_902_;
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_a_917_);
lean_dec(v___x_902_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_922_; 
if (v_isShared_920_ == 0)
{
v___x_922_ = v___x_919_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_a_917_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
}
else
{
lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_932_; 
lean_del_object(v___x_895_);
lean_dec_ref(v_type_891_);
lean_dec(v_levelParams_890_);
lean_dec(v_name_889_);
lean_del_object(v___x_887_);
lean_dec(v_inlineAttr_x3f_885_);
lean_dec_ref(v_value_883_);
lean_dec_ref_known(v_r_876_, 5);
v_a_925_ = lean_ctor_get(v___x_898_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_898_);
if (v_isSharedCheck_932_ == 0)
{
v___x_927_ = v___x_898_;
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v___x_898_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_930_; 
if (v_isShared_928_ == 0)
{
v___x_930_ = v___x_927_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_a_925_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
}
}
}
else
{
lean_object* v___x_935_; 
v___x_935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_935_, 0, v_decl_875_);
return v___x_935_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_applyRenaming___boxed(lean_object* v_pu_936_, lean_object* v_decl_937_, lean_object* v_r_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_){
_start:
{
uint8_t v_pu_boxed_944_; lean_object* v_res_945_; 
v_pu_boxed_944_ = lean_unbox(v_pu_936_);
v_res_945_ = l_Lean_Compiler_LCNF_Decl_applyRenaming(v_pu_boxed_944_, v_decl_937_, v_r_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_);
lean_dec(v_a_942_);
lean_dec_ref(v_a_941_);
lean_dec(v_a_940_);
lean_dec_ref(v_a_939_);
return v_res_945_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_Renaming(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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

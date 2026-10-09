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
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_LCtx_addFunDecl(uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_addParam(uint8_t, lean_object*, lean_object*);
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
lean_object* l_Lean_Compiler_LCNF_Param_applyRenaming___redArg(uint8_t v_pu_15_, lean_object* v_param_16_, lean_object* v_r_17_, lean_object* v_a_18_){
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
lean_object* v_param_32_; 
if (v_isShared_26_ == 0)
{
lean_ctor_set(v___x_25_, 1, v_val_27_);
v_param_32_ = v___x_25_;
goto v_reusejp_31_;
}
else
{
lean_object* v_reuseFailAlloc_48_; 
v_reuseFailAlloc_48_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_48_, 0, v_fvarId_20_);
lean_ctor_set(v_reuseFailAlloc_48_, 1, v_val_27_);
lean_ctor_set(v_reuseFailAlloc_48_, 2, v_type_21_);
lean_ctor_set_uint8(v_reuseFailAlloc_48_, sizeof(void*)*3, v_borrow_22_);
v_param_32_ = v_reuseFailAlloc_48_;
goto v_reusejp_31_;
}
v_reusejp_31_:
{
lean_object* v___x_33_; lean_object* v_lctx_34_; lean_object* v_nextIdx_35_; lean_object* v___x_37_; uint8_t v_isShared_38_; uint8_t v_isSharedCheck_47_; 
v___x_33_ = lean_st_ref_take(v_a_18_);
v_lctx_34_ = lean_ctor_get(v___x_33_, 0);
v_nextIdx_35_ = lean_ctor_get(v___x_33_, 1);
v_isSharedCheck_47_ = !lean_is_exclusive(v___x_33_);
if (v_isSharedCheck_47_ == 0)
{
v___x_37_ = v___x_33_;
v_isShared_38_ = v_isSharedCheck_47_;
goto v_resetjp_36_;
}
else
{
lean_inc(v_nextIdx_35_);
lean_inc(v_lctx_34_);
lean_dec(v___x_33_);
v___x_37_ = lean_box(0);
v_isShared_38_ = v_isSharedCheck_47_;
goto v_resetjp_36_;
}
v_resetjp_36_:
{
lean_object* v___x_39_; lean_object* v___x_41_; 
lean_inc_ref(v_param_32_);
v___x_39_ = l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_15_, v_lctx_34_, v_param_32_);
if (v_isShared_38_ == 0)
{
lean_ctor_set(v___x_37_, 0, v___x_39_);
v___x_41_ = v___x_37_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_46_; 
v_reuseFailAlloc_46_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_46_, 0, v___x_39_);
lean_ctor_set(v_reuseFailAlloc_46_, 1, v_nextIdx_35_);
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
lean_ctor_set(v___x_29_, 0, v_param_32_);
v___x_44_ = v___x_29_;
goto v_reusejp_43_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v_param_32_);
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
LEAN_EXPORT void l_Lean_Compiler_LCNF_Param_applyRenaming___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_15_ = stack[0].m_num;
lean_object* v_param_16_ = stack[1].m_obj;
lean_object* v_r_17_ = stack[2].m_obj;
lean_object* v_a_18_ = stack[3].m_obj;
lean_object* v_res_55_;
v_res_55_ = l_Lean_Compiler_LCNF_Param_applyRenaming___redArg(v_pu_15_, v_param_16_, v_r_17_, v_a_18_);
stack->m_obj
 = v_res_55_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_applyRenaming___redArg___boxed(lean_object* v_pu_56_, lean_object* v_param_57_, lean_object* v_r_58_, lean_object* v_a_59_, lean_object* v_a_60_){
_start:
{
uint8_t v_pu_boxed_61_; lean_object* v_res_62_; 
v_pu_boxed_61_ = lean_unbox(v_pu_56_);
v_res_62_ = l_Lean_Compiler_LCNF_Param_applyRenaming___redArg(v_pu_boxed_61_, v_param_57_, v_r_58_, v_a_59_);
lean_dec(v_a_59_);
lean_dec(v_r_58_);
return v_res_62_;
}
}
lean_object* l_Lean_Compiler_LCNF_Param_applyRenaming(uint8_t v_pu_63_, lean_object* v_param_64_, lean_object* v_r_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = l_Lean_Compiler_LCNF_Param_applyRenaming___redArg(v_pu_63_, v_param_64_, v_r_65_, v_a_67_);
return v___x_71_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Param_applyRenaming_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_63_ = stack[0].m_num;
lean_object* v_param_64_ = stack[1].m_obj;
lean_object* v_r_65_ = stack[2].m_obj;
lean_object* v_a_66_ = stack[3].m_obj;
lean_object* v_a_67_ = stack[4].m_obj;
lean_object* v_a_68_ = stack[5].m_obj;
lean_object* v_a_69_ = stack[6].m_obj;
lean_object* v_res_72_;
v_res_72_ = l_Lean_Compiler_LCNF_Param_applyRenaming(v_pu_63_, v_param_64_, v_r_65_, v_a_66_, v_a_67_, v_a_68_, v_a_69_);
stack->m_obj
 = v_res_72_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_applyRenaming___boxed(lean_object* v_pu_73_, lean_object* v_param_74_, lean_object* v_r_75_, lean_object* v_a_76_, lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_){
_start:
{
uint8_t v_pu_boxed_81_; lean_object* v_res_82_; 
v_pu_boxed_81_ = lean_unbox(v_pu_73_);
v_res_82_ = l_Lean_Compiler_LCNF_Param_applyRenaming(v_pu_boxed_81_, v_param_74_, v_r_75_, v_a_76_, v_a_77_, v_a_78_, v_a_79_);
lean_dec(v_a_79_);
lean_dec_ref(v_a_78_);
lean_dec(v_a_77_);
lean_dec_ref(v_a_76_);
lean_dec(v_r_75_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Param_applyRenaming_spec__0(lean_object* v_00_u03b4_83_, lean_object* v_t_84_, lean_object* v_k_85_){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Param_applyRenaming_spec__0___redArg(v_t_84_, v_k_85_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Param_applyRenaming_spec__0___boxed(lean_object* v_00_u03b4_87_, lean_object* v_t_88_, lean_object* v_k_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Param_applyRenaming_spec__0(v_00_u03b4_87_, v_t_88_, v_k_89_);
lean_dec(v_k_89_);
lean_dec(v_t_88_);
return v_res_90_;
}
}
lean_object* l_Lean_Compiler_LCNF_LetDecl_applyRenaming___redArg(uint8_t v_pu_91_, lean_object* v_decl_92_, lean_object* v_r_93_, lean_object* v_a_94_){
_start:
{
lean_object* v_fvarId_96_; lean_object* v_type_97_; lean_object* v_value_98_; lean_object* v___x_99_; 
v_fvarId_96_ = lean_ctor_get(v_decl_92_, 0);
v_type_97_ = lean_ctor_get(v_decl_92_, 2);
v_value_98_ = lean_ctor_get(v_decl_92_, 3);
v___x_99_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Param_applyRenaming_spec__0___redArg(v_r_93_, v_fvarId_96_);
if (lean_obj_tag(v___x_99_) == 1)
{
lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_126_; 
lean_inc(v_value_98_);
lean_inc_ref(v_type_97_);
lean_inc(v_fvarId_96_);
v_isSharedCheck_126_ = !lean_is_exclusive(v_decl_92_);
if (v_isSharedCheck_126_ == 0)
{
lean_object* v_unused_127_; lean_object* v_unused_128_; lean_object* v_unused_129_; lean_object* v_unused_130_; 
v_unused_127_ = lean_ctor_get(v_decl_92_, 3);
lean_dec(v_unused_127_);
v_unused_128_ = lean_ctor_get(v_decl_92_, 2);
lean_dec(v_unused_128_);
v_unused_129_ = lean_ctor_get(v_decl_92_, 1);
lean_dec(v_unused_129_);
v_unused_130_ = lean_ctor_get(v_decl_92_, 0);
lean_dec(v_unused_130_);
v___x_101_ = v_decl_92_;
v_isShared_102_ = v_isSharedCheck_126_;
goto v_resetjp_100_;
}
else
{
lean_dec(v_decl_92_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_126_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v_val_103_; lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_125_; 
v_val_103_ = lean_ctor_get(v___x_99_, 0);
v_isSharedCheck_125_ = !lean_is_exclusive(v___x_99_);
if (v_isSharedCheck_125_ == 0)
{
v___x_105_ = v___x_99_;
v_isShared_106_ = v_isSharedCheck_125_;
goto v_resetjp_104_;
}
else
{
lean_inc(v_val_103_);
lean_dec(v___x_99_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_125_;
goto v_resetjp_104_;
}
v_resetjp_104_:
{
lean_object* v_decl_108_; 
if (v_isShared_102_ == 0)
{
lean_ctor_set(v___x_101_, 1, v_val_103_);
v_decl_108_ = v___x_101_;
goto v_reusejp_107_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v_fvarId_96_);
lean_ctor_set(v_reuseFailAlloc_124_, 1, v_val_103_);
lean_ctor_set(v_reuseFailAlloc_124_, 2, v_type_97_);
lean_ctor_set(v_reuseFailAlloc_124_, 3, v_value_98_);
v_decl_108_ = v_reuseFailAlloc_124_;
goto v_reusejp_107_;
}
v_reusejp_107_:
{
lean_object* v___x_109_; lean_object* v_lctx_110_; lean_object* v_nextIdx_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_123_; 
v___x_109_ = lean_st_ref_take(v_a_94_);
v_lctx_110_ = lean_ctor_get(v___x_109_, 0);
v_nextIdx_111_ = lean_ctor_get(v___x_109_, 1);
v_isSharedCheck_123_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_123_ == 0)
{
v___x_113_ = v___x_109_;
v_isShared_114_ = v_isSharedCheck_123_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_nextIdx_111_);
lean_inc(v_lctx_110_);
lean_dec(v___x_109_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_123_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v___x_115_; lean_object* v___x_117_; 
lean_inc_ref(v_decl_108_);
v___x_115_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v_pu_91_, v_lctx_110_, v_decl_108_);
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 0, v___x_115_);
v___x_117_ = v___x_113_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v___x_115_);
lean_ctor_set(v_reuseFailAlloc_122_, 1, v_nextIdx_111_);
v___x_117_ = v_reuseFailAlloc_122_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
lean_object* v___x_118_; lean_object* v___x_120_; 
v___x_118_ = lean_st_ref_put(v_a_94_, v___x_117_);
if (v_isShared_106_ == 0)
{
lean_ctor_set_tag(v___x_105_, 0);
lean_ctor_set(v___x_105_, 0, v_decl_108_);
v___x_120_ = v___x_105_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v_decl_108_);
v___x_120_ = v_reuseFailAlloc_121_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
return v___x_120_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_131_; 
lean_dec(v___x_99_);
v___x_131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_131_, 0, v_decl_92_);
return v___x_131_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_LetDecl_applyRenaming___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_91_ = stack[0].m_num;
lean_object* v_decl_92_ = stack[1].m_obj;
lean_object* v_r_93_ = stack[2].m_obj;
lean_object* v_a_94_ = stack[3].m_obj;
lean_object* v_res_132_;
v_res_132_ = l_Lean_Compiler_LCNF_LetDecl_applyRenaming___redArg(v_pu_91_, v_decl_92_, v_r_93_, v_a_94_);
stack->m_obj
 = v_res_132_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_applyRenaming___redArg___boxed(lean_object* v_pu_133_, lean_object* v_decl_134_, lean_object* v_r_135_, lean_object* v_a_136_, lean_object* v_a_137_){
_start:
{
uint8_t v_pu_boxed_138_; lean_object* v_res_139_; 
v_pu_boxed_138_ = lean_unbox(v_pu_133_);
v_res_139_ = l_Lean_Compiler_LCNF_LetDecl_applyRenaming___redArg(v_pu_boxed_138_, v_decl_134_, v_r_135_, v_a_136_);
lean_dec(v_a_136_);
lean_dec(v_r_135_);
return v_res_139_;
}
}
lean_object* l_Lean_Compiler_LCNF_LetDecl_applyRenaming(uint8_t v_pu_140_, lean_object* v_decl_141_, lean_object* v_r_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = l_Lean_Compiler_LCNF_LetDecl_applyRenaming___redArg(v_pu_140_, v_decl_141_, v_r_142_, v_a_144_);
return v___x_148_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_LetDecl_applyRenaming_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_140_ = stack[0].m_num;
lean_object* v_decl_141_ = stack[1].m_obj;
lean_object* v_r_142_ = stack[2].m_obj;
lean_object* v_a_143_ = stack[3].m_obj;
lean_object* v_a_144_ = stack[4].m_obj;
lean_object* v_a_145_ = stack[5].m_obj;
lean_object* v_a_146_ = stack[6].m_obj;
lean_object* v_res_149_;
v_res_149_ = l_Lean_Compiler_LCNF_LetDecl_applyRenaming(v_pu_140_, v_decl_141_, v_r_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_);
stack->m_obj
 = v_res_149_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_applyRenaming___boxed(lean_object* v_pu_150_, lean_object* v_decl_151_, lean_object* v_r_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_){
_start:
{
uint8_t v_pu_boxed_158_; lean_object* v_res_159_; 
v_pu_boxed_158_ = lean_unbox(v_pu_150_);
v_res_159_ = l_Lean_Compiler_LCNF_LetDecl_applyRenaming(v_pu_boxed_158_, v_decl_151_, v_r_152_, v_a_153_, v_a_154_, v_a_155_, v_a_156_);
lean_dec(v_a_156_);
lean_dec_ref(v_a_155_);
lean_dec(v_a_154_);
lean_dec_ref(v_a_153_);
lean_dec(v_r_152_);
return v_res_159_;
}
}
lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__1___redArg(uint8_t v_pu_160_, lean_object* v_r_161_, lean_object* v_i_162_, lean_object* v_as_163_, lean_object* v___y_164_){
_start:
{
lean_object* v___x_166_; uint8_t v___x_167_; 
v___x_166_ = lean_array_get_size(v_as_163_);
v___x_167_ = lean_nat_dec_lt(v_i_162_, v___x_166_);
if (v___x_167_ == 0)
{
lean_object* v___x_168_; 
lean_dec(v_i_162_);
v___x_168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_168_, 0, v_as_163_);
return v___x_168_;
}
else
{
lean_object* v_a_169_; lean_object* v___x_170_; 
v_a_169_ = lean_array_fget_borrowed(v_as_163_, v_i_162_);
lean_inc(v_a_169_);
v___x_170_ = l_Lean_Compiler_LCNF_Param_applyRenaming___redArg(v_pu_160_, v_a_169_, v_r_161_, v___y_164_);
if (lean_obj_tag(v___x_170_) == 0)
{
lean_object* v_a_171_; size_t v___x_172_; size_t v___x_173_; uint8_t v___x_174_; 
v_a_171_ = lean_ctor_get(v___x_170_, 0);
lean_inc(v_a_171_);
lean_dec_ref_known(v___x_170_, 1);
v___x_172_ = lean_ptr_addr(v_a_169_);
v___x_173_ = lean_ptr_addr(v_a_171_);
v___x_174_ = lean_usize_dec_eq(v___x_172_, v___x_173_);
if (v___x_174_ == 0)
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_175_ = lean_unsigned_to_nat(1u);
v___x_176_ = lean_nat_add(v_i_162_, v___x_175_);
v___x_177_ = lean_array_fset(v_as_163_, v_i_162_, v_a_171_);
lean_dec(v_i_162_);
v_i_162_ = v___x_176_;
v_as_163_ = v___x_177_;
goto _start;
}
else
{
lean_object* v___x_179_; lean_object* v___x_180_; 
lean_dec(v_a_171_);
v___x_179_ = lean_unsigned_to_nat(1u);
v___x_180_ = lean_nat_add(v_i_162_, v___x_179_);
lean_dec(v_i_162_);
v_i_162_ = v___x_180_;
goto _start;
}
}
else
{
lean_object* v_a_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_189_; 
lean_dec_ref(v_as_163_);
lean_dec(v_i_162_);
v_a_182_ = lean_ctor_get(v___x_170_, 0);
v_isSharedCheck_189_ = !lean_is_exclusive(v___x_170_);
if (v_isSharedCheck_189_ == 0)
{
v___x_184_ = v___x_170_;
v_isShared_185_ = v_isSharedCheck_189_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_a_182_);
lean_dec(v___x_170_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_189_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v___x_187_; 
if (v_isShared_185_ == 0)
{
v___x_187_ = v___x_184_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v_a_182_);
v___x_187_ = v_reuseFailAlloc_188_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
return v___x_187_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_160_ = stack[0].m_num;
lean_object* v_r_161_ = stack[1].m_obj;
lean_object* v_i_162_ = stack[2].m_obj;
lean_object* v_as_163_ = stack[3].m_obj;
lean_object* v___y_164_ = stack[4].m_obj;
lean_object* v_res_190_;
v_res_190_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__1___redArg(v_pu_160_, v_r_161_, v_i_162_, v_as_163_, v___y_164_);
stack->m_obj
 = v_res_190_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__1___redArg___boxed(lean_object* v_pu_191_, lean_object* v_r_192_, lean_object* v_i_193_, lean_object* v_as_194_, lean_object* v___y_195_, lean_object* v___y_196_){
_start:
{
uint8_t v_pu_boxed_197_; lean_object* v_res_198_; 
v_pu_boxed_197_ = lean_unbox(v_pu_191_);
v_res_198_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__1___redArg(v_pu_boxed_197_, v_r_192_, v_i_193_, v_as_194_, v___y_195_);
lean_dec(v___y_195_);
lean_dec(v_r_192_);
return v_res_198_;
}
}
lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__2(uint8_t v_pu_199_, lean_object* v_r_200_, lean_object* v_i_201_, lean_object* v_as_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_){
_start:
{
lean_object* v___x_208_; uint8_t v___x_209_; 
v___x_208_ = lean_array_get_size(v_as_202_);
v___x_209_ = lean_nat_dec_lt(v_i_201_, v___x_208_);
if (v___x_209_ == 0)
{
lean_object* v___x_210_; 
lean_dec(v_i_201_);
v___x_210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_210_, 0, v_as_202_);
return v___x_210_;
}
else
{
lean_object* v_a_211_; lean_object* v_a_213_; 
v_a_211_ = lean_array_fget_borrowed(v_as_202_, v_i_201_);
switch(lean_obj_tag(v_a_211_))
{
case 0:
{
lean_object* v_params_224_; lean_object* v_code_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v_params_224_ = lean_ctor_get(v_a_211_, 1);
v_code_225_ = lean_ctor_get(v_a_211_, 2);
v___x_226_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_params_224_);
v___x_227_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__1___redArg(v_pu_199_, v_r_200_, v___x_226_, v_params_224_, v___y_204_);
if (lean_obj_tag(v___x_227_) == 0)
{
lean_object* v_a_228_; lean_object* v___x_229_; 
v_a_228_ = lean_ctor_get(v___x_227_, 0);
lean_inc(v_a_228_);
lean_dec_ref_known(v___x_227_, 1);
lean_inc_ref(v_code_225_);
v___x_229_ = l_Lean_Compiler_LCNF_Code_applyRenaming(v_pu_199_, v_code_225_, v_r_200_, v___y_203_, v___y_204_, v___y_205_, v___y_206_);
if (lean_obj_tag(v___x_229_) == 0)
{
lean_object* v_a_230_; lean_object* v___x_231_; 
v_a_230_ = lean_ctor_get(v___x_229_, 0);
lean_inc(v_a_230_);
lean_dec_ref_known(v___x_229_, 1);
lean_inc_ref(v_a_211_);
v___x_231_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp(v_pu_199_, v_a_211_, v_a_228_, v_a_230_);
v_a_213_ = v___x_231_;
goto v___jp_212_;
}
else
{
lean_object* v_a_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_239_; 
lean_dec(v_a_228_);
lean_dec_ref(v_as_202_);
lean_dec(v_i_201_);
v_a_232_ = lean_ctor_get(v___x_229_, 0);
v_isSharedCheck_239_ = !lean_is_exclusive(v___x_229_);
if (v_isSharedCheck_239_ == 0)
{
v___x_234_ = v___x_229_;
v_isShared_235_ = v_isSharedCheck_239_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_a_232_);
lean_dec(v___x_229_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_239_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v___x_237_; 
if (v_isShared_235_ == 0)
{
v___x_237_ = v___x_234_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v_a_232_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
}
}
else
{
lean_object* v_a_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_247_; 
lean_dec_ref(v_as_202_);
lean_dec(v_i_201_);
v_a_240_ = lean_ctor_get(v___x_227_, 0);
v_isSharedCheck_247_ = !lean_is_exclusive(v___x_227_);
if (v_isSharedCheck_247_ == 0)
{
v___x_242_ = v___x_227_;
v_isShared_243_ = v_isSharedCheck_247_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_a_240_);
lean_dec(v___x_227_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_247_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_245_; 
if (v_isShared_243_ == 0)
{
v___x_245_ = v___x_242_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v_a_240_);
v___x_245_ = v_reuseFailAlloc_246_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
return v___x_245_;
}
}
}
}
case 1:
{
lean_object* v_code_248_; lean_object* v___x_249_; 
v_code_248_ = lean_ctor_get(v_a_211_, 1);
lean_inc_ref(v_code_248_);
v___x_249_ = l_Lean_Compiler_LCNF_Code_applyRenaming(v_pu_199_, v_code_248_, v_r_200_, v___y_203_, v___y_204_, v___y_205_, v___y_206_);
if (lean_obj_tag(v___x_249_) == 0)
{
lean_object* v_a_250_; lean_object* v___x_251_; 
v_a_250_ = lean_ctor_get(v___x_249_, 0);
lean_inc(v_a_250_);
lean_dec_ref_known(v___x_249_, 1);
lean_inc_ref(v_a_211_);
v___x_251_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_211_, v_a_250_);
v_a_213_ = v___x_251_;
goto v___jp_212_;
}
else
{
lean_object* v_a_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_259_; 
lean_dec_ref(v_as_202_);
lean_dec(v_i_201_);
v_a_252_ = lean_ctor_get(v___x_249_, 0);
v_isSharedCheck_259_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_259_ == 0)
{
v___x_254_ = v___x_249_;
v_isShared_255_ = v_isSharedCheck_259_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_a_252_);
lean_dec(v___x_249_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_259_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_257_; 
if (v_isShared_255_ == 0)
{
v___x_257_ = v___x_254_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v_a_252_);
v___x_257_ = v_reuseFailAlloc_258_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
return v___x_257_;
}
}
}
}
default: 
{
lean_object* v_code_260_; lean_object* v___x_261_; 
v_code_260_ = lean_ctor_get(v_a_211_, 0);
lean_inc_ref(v_code_260_);
v___x_261_ = l_Lean_Compiler_LCNF_Code_applyRenaming(v_pu_199_, v_code_260_, v_r_200_, v___y_203_, v___y_204_, v___y_205_, v___y_206_);
if (lean_obj_tag(v___x_261_) == 0)
{
lean_object* v_a_262_; lean_object* v___x_263_; 
v_a_262_ = lean_ctor_get(v___x_261_, 0);
lean_inc(v_a_262_);
lean_dec_ref_known(v___x_261_, 1);
lean_inc_ref(v_a_211_);
v___x_263_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_211_, v_a_262_);
v_a_213_ = v___x_263_;
goto v___jp_212_;
}
else
{
lean_object* v_a_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_271_; 
lean_dec_ref(v_as_202_);
lean_dec(v_i_201_);
v_a_264_ = lean_ctor_get(v___x_261_, 0);
v_isSharedCheck_271_ = !lean_is_exclusive(v___x_261_);
if (v_isSharedCheck_271_ == 0)
{
v___x_266_ = v___x_261_;
v_isShared_267_ = v_isSharedCheck_271_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_a_264_);
lean_dec(v___x_261_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_271_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_269_; 
if (v_isShared_267_ == 0)
{
v___x_269_ = v___x_266_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v_a_264_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
return v___x_269_;
}
}
}
}
}
v___jp_212_:
{
size_t v___x_214_; size_t v___x_215_; uint8_t v___x_216_; 
v___x_214_ = lean_ptr_addr(v_a_211_);
v___x_215_ = lean_ptr_addr(v_a_213_);
v___x_216_ = lean_usize_dec_eq(v___x_214_, v___x_215_);
if (v___x_216_ == 0)
{
lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_217_ = lean_unsigned_to_nat(1u);
v___x_218_ = lean_nat_add(v_i_201_, v___x_217_);
v___x_219_ = lean_array_fset(v_as_202_, v_i_201_, v_a_213_);
lean_dec(v_i_201_);
v_i_201_ = v___x_218_;
v_as_202_ = v___x_219_;
goto _start;
}
else
{
lean_object* v___x_221_; lean_object* v___x_222_; 
lean_dec_ref(v_a_213_);
v___x_221_ = lean_unsigned_to_nat(1u);
v___x_222_ = lean_nat_add(v_i_201_, v___x_221_);
lean_dec(v_i_201_);
v_i_201_ = v___x_222_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__2_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_199_ = stack[0].m_num;
lean_object* v_r_200_ = stack[1].m_obj;
lean_object* v_i_201_ = stack[2].m_obj;
lean_object* v_as_202_ = stack[3].m_obj;
lean_object* v___y_203_ = stack[4].m_obj;
lean_object* v___y_204_ = stack[5].m_obj;
lean_object* v___y_205_ = stack[6].m_obj;
lean_object* v___y_206_ = stack[7].m_obj;
lean_object* v_res_272_;
v_res_272_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__2(v_pu_199_, v_r_200_, v_i_201_, v_as_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_);
stack->m_obj
 = v_res_272_;
}
lean_object* l_Lean_Compiler_LCNF_Code_applyRenaming(uint8_t v_pu_273_, lean_object* v_code_274_, lean_object* v_r_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_){
_start:
{
switch(lean_obj_tag(v_code_274_))
{
case 0:
{
lean_object* v_decl_281_; lean_object* v_k_282_; lean_object* v___x_283_; 
v_decl_281_ = lean_ctor_get(v_code_274_, 0);
v_k_282_ = lean_ctor_get(v_code_274_, 1);
lean_inc_ref(v_decl_281_);
v___x_283_ = l_Lean_Compiler_LCNF_LetDecl_applyRenaming___redArg(v_pu_273_, v_decl_281_, v_r_275_, v_a_277_);
if (lean_obj_tag(v___x_283_) == 0)
{
lean_object* v_a_284_; lean_object* v___x_285_; 
v_a_284_ = lean_ctor_get(v___x_283_, 0);
lean_inc(v_a_284_);
lean_dec_ref_known(v___x_283_, 1);
lean_inc_ref(v_k_282_);
v___x_285_ = l_Lean_Compiler_LCNF_Code_applyRenaming(v_pu_273_, v_k_282_, v_r_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_);
if (lean_obj_tag(v___x_285_) == 0)
{
lean_object* v_a_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_323_; 
v_a_286_ = lean_ctor_get(v___x_285_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v___x_285_);
if (v_isSharedCheck_323_ == 0)
{
v___x_288_ = v___x_285_;
v_isShared_289_ = v_isSharedCheck_323_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_a_286_);
lean_dec(v___x_285_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_323_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
size_t v___x_290_; size_t v___x_291_; uint8_t v___x_292_; 
v___x_290_ = lean_ptr_addr(v_k_282_);
v___x_291_ = lean_ptr_addr(v_a_286_);
v___x_292_ = lean_usize_dec_eq(v___x_290_, v___x_291_);
if (v___x_292_ == 0)
{
lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_302_; 
v_isSharedCheck_302_ = !lean_is_exclusive(v_code_274_);
if (v_isSharedCheck_302_ == 0)
{
lean_object* v_unused_303_; lean_object* v_unused_304_; 
v_unused_303_ = lean_ctor_get(v_code_274_, 1);
lean_dec(v_unused_303_);
v_unused_304_ = lean_ctor_get(v_code_274_, 0);
lean_dec(v_unused_304_);
v___x_294_ = v_code_274_;
v_isShared_295_ = v_isSharedCheck_302_;
goto v_resetjp_293_;
}
else
{
lean_dec(v_code_274_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_302_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___x_297_; 
if (v_isShared_295_ == 0)
{
lean_ctor_set(v___x_294_, 1, v_a_286_);
lean_ctor_set(v___x_294_, 0, v_a_284_);
v___x_297_ = v___x_294_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v_a_284_);
lean_ctor_set(v_reuseFailAlloc_301_, 1, v_a_286_);
v___x_297_ = v_reuseFailAlloc_301_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
lean_object* v___x_299_; 
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 0, v___x_297_);
v___x_299_ = v___x_288_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v___x_297_);
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
else
{
size_t v___x_305_; size_t v___x_306_; uint8_t v___x_307_; 
v___x_305_ = lean_ptr_addr(v_decl_281_);
v___x_306_ = lean_ptr_addr(v_a_284_);
v___x_307_ = lean_usize_dec_eq(v___x_305_, v___x_306_);
if (v___x_307_ == 0)
{
lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_317_; 
v_isSharedCheck_317_ = !lean_is_exclusive(v_code_274_);
if (v_isSharedCheck_317_ == 0)
{
lean_object* v_unused_318_; lean_object* v_unused_319_; 
v_unused_318_ = lean_ctor_get(v_code_274_, 1);
lean_dec(v_unused_318_);
v_unused_319_ = lean_ctor_get(v_code_274_, 0);
lean_dec(v_unused_319_);
v___x_309_ = v_code_274_;
v_isShared_310_ = v_isSharedCheck_317_;
goto v_resetjp_308_;
}
else
{
lean_dec(v_code_274_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_317_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_312_; 
if (v_isShared_310_ == 0)
{
lean_ctor_set(v___x_309_, 1, v_a_286_);
lean_ctor_set(v___x_309_, 0, v_a_284_);
v___x_312_ = v___x_309_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_a_284_);
lean_ctor_set(v_reuseFailAlloc_316_, 1, v_a_286_);
v___x_312_ = v_reuseFailAlloc_316_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
lean_object* v___x_314_; 
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 0, v___x_312_);
v___x_314_ = v___x_288_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v___x_312_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
}
}
else
{
lean_object* v___x_321_; 
lean_dec(v_a_286_);
lean_dec(v_a_284_);
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 0, v_code_274_);
v___x_321_ = v___x_288_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_code_274_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
}
}
}
else
{
lean_dec(v_a_284_);
lean_dec_ref_known(v_code_274_, 2);
return v___x_285_;
}
}
else
{
lean_object* v_a_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_331_; 
lean_dec_ref_known(v_code_274_, 2);
v_a_324_ = lean_ctor_get(v___x_283_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_283_);
if (v_isSharedCheck_331_ == 0)
{
v___x_326_ = v___x_283_;
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_a_324_);
lean_dec(v___x_283_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_329_; 
if (v_isShared_327_ == 0)
{
v___x_329_ = v___x_326_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_a_324_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
}
}
case 1:
{
lean_object* v_decl_332_; lean_object* v_k_333_; lean_object* v___x_334_; 
v_decl_332_ = lean_ctor_get(v_code_274_, 0);
v_k_333_ = lean_ctor_get(v_code_274_, 1);
lean_inc_ref(v_decl_332_);
v___x_334_ = l_Lean_Compiler_LCNF_FunDecl_applyRenaming(v_pu_273_, v_decl_332_, v_r_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_);
if (lean_obj_tag(v___x_334_) == 0)
{
lean_object* v_a_335_; lean_object* v___x_336_; 
v_a_335_ = lean_ctor_get(v___x_334_, 0);
lean_inc(v_a_335_);
lean_dec_ref_known(v___x_334_, 1);
lean_inc_ref(v_k_333_);
v___x_336_ = l_Lean_Compiler_LCNF_Code_applyRenaming(v_pu_273_, v_k_333_, v_r_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_);
if (lean_obj_tag(v___x_336_) == 0)
{
lean_object* v_a_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_374_; 
v_a_337_ = lean_ctor_get(v___x_336_, 0);
v_isSharedCheck_374_ = !lean_is_exclusive(v___x_336_);
if (v_isSharedCheck_374_ == 0)
{
v___x_339_ = v___x_336_;
v_isShared_340_ = v_isSharedCheck_374_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_a_337_);
lean_dec(v___x_336_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_374_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
size_t v___x_341_; size_t v___x_342_; uint8_t v___x_343_; 
v___x_341_ = lean_ptr_addr(v_k_333_);
v___x_342_ = lean_ptr_addr(v_a_337_);
v___x_343_ = lean_usize_dec_eq(v___x_341_, v___x_342_);
if (v___x_343_ == 0)
{
lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_353_; 
v_isSharedCheck_353_ = !lean_is_exclusive(v_code_274_);
if (v_isSharedCheck_353_ == 0)
{
lean_object* v_unused_354_; lean_object* v_unused_355_; 
v_unused_354_ = lean_ctor_get(v_code_274_, 1);
lean_dec(v_unused_354_);
v_unused_355_ = lean_ctor_get(v_code_274_, 0);
lean_dec(v_unused_355_);
v___x_345_ = v_code_274_;
v_isShared_346_ = v_isSharedCheck_353_;
goto v_resetjp_344_;
}
else
{
lean_dec(v_code_274_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_353_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_348_; 
if (v_isShared_346_ == 0)
{
lean_ctor_set(v___x_345_, 1, v_a_337_);
lean_ctor_set(v___x_345_, 0, v_a_335_);
v___x_348_ = v___x_345_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_a_335_);
lean_ctor_set(v_reuseFailAlloc_352_, 1, v_a_337_);
v___x_348_ = v_reuseFailAlloc_352_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
lean_object* v___x_350_; 
if (v_isShared_340_ == 0)
{
lean_ctor_set(v___x_339_, 0, v___x_348_);
v___x_350_ = v___x_339_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v___x_348_);
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
size_t v___x_356_; size_t v___x_357_; uint8_t v___x_358_; 
v___x_356_ = lean_ptr_addr(v_decl_332_);
v___x_357_ = lean_ptr_addr(v_a_335_);
v___x_358_ = lean_usize_dec_eq(v___x_356_, v___x_357_);
if (v___x_358_ == 0)
{
lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_368_; 
v_isSharedCheck_368_ = !lean_is_exclusive(v_code_274_);
if (v_isSharedCheck_368_ == 0)
{
lean_object* v_unused_369_; lean_object* v_unused_370_; 
v_unused_369_ = lean_ctor_get(v_code_274_, 1);
lean_dec(v_unused_369_);
v_unused_370_ = lean_ctor_get(v_code_274_, 0);
lean_dec(v_unused_370_);
v___x_360_ = v_code_274_;
v_isShared_361_ = v_isSharedCheck_368_;
goto v_resetjp_359_;
}
else
{
lean_dec(v_code_274_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_368_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_363_; 
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 1, v_a_337_);
lean_ctor_set(v___x_360_, 0, v_a_335_);
v___x_363_ = v___x_360_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_a_335_);
lean_ctor_set(v_reuseFailAlloc_367_, 1, v_a_337_);
v___x_363_ = v_reuseFailAlloc_367_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
lean_object* v___x_365_; 
if (v_isShared_340_ == 0)
{
lean_ctor_set(v___x_339_, 0, v___x_363_);
v___x_365_ = v___x_339_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v___x_363_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
}
}
else
{
lean_object* v___x_372_; 
lean_dec(v_a_337_);
lean_dec(v_a_335_);
if (v_isShared_340_ == 0)
{
lean_ctor_set(v___x_339_, 0, v_code_274_);
v___x_372_ = v___x_339_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_code_274_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
}
}
}
}
}
else
{
lean_dec(v_a_335_);
lean_dec_ref_known(v_code_274_, 2);
return v___x_336_;
}
}
else
{
lean_object* v_a_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_382_; 
lean_dec_ref_known(v_code_274_, 2);
v_a_375_ = lean_ctor_get(v___x_334_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_334_);
if (v_isSharedCheck_382_ == 0)
{
v___x_377_ = v___x_334_;
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_a_375_);
lean_dec(v___x_334_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_380_; 
if (v_isShared_378_ == 0)
{
v___x_380_ = v___x_377_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_a_375_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
}
case 2:
{
lean_object* v_decl_383_; lean_object* v_k_384_; lean_object* v___x_385_; 
v_decl_383_ = lean_ctor_get(v_code_274_, 0);
v_k_384_ = lean_ctor_get(v_code_274_, 1);
lean_inc_ref(v_decl_383_);
v___x_385_ = l_Lean_Compiler_LCNF_FunDecl_applyRenaming(v_pu_273_, v_decl_383_, v_r_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_);
if (lean_obj_tag(v___x_385_) == 0)
{
lean_object* v_a_386_; lean_object* v___x_387_; 
v_a_386_ = lean_ctor_get(v___x_385_, 0);
lean_inc(v_a_386_);
lean_dec_ref_known(v___x_385_, 1);
lean_inc_ref(v_k_384_);
v___x_387_ = l_Lean_Compiler_LCNF_Code_applyRenaming(v_pu_273_, v_k_384_, v_r_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_);
if (lean_obj_tag(v___x_387_) == 0)
{
lean_object* v_a_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_425_; 
v_a_388_ = lean_ctor_get(v___x_387_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_387_);
if (v_isSharedCheck_425_ == 0)
{
v___x_390_ = v___x_387_;
v_isShared_391_ = v_isSharedCheck_425_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_a_388_);
lean_dec(v___x_387_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_425_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
size_t v___x_392_; size_t v___x_393_; uint8_t v___x_394_; 
v___x_392_ = lean_ptr_addr(v_k_384_);
v___x_393_ = lean_ptr_addr(v_a_388_);
v___x_394_ = lean_usize_dec_eq(v___x_392_, v___x_393_);
if (v___x_394_ == 0)
{
lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_404_; 
v_isSharedCheck_404_ = !lean_is_exclusive(v_code_274_);
if (v_isSharedCheck_404_ == 0)
{
lean_object* v_unused_405_; lean_object* v_unused_406_; 
v_unused_405_ = lean_ctor_get(v_code_274_, 1);
lean_dec(v_unused_405_);
v_unused_406_ = lean_ctor_get(v_code_274_, 0);
lean_dec(v_unused_406_);
v___x_396_ = v_code_274_;
v_isShared_397_ = v_isSharedCheck_404_;
goto v_resetjp_395_;
}
else
{
lean_dec(v_code_274_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_404_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_399_; 
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 1, v_a_388_);
lean_ctor_set(v___x_396_, 0, v_a_386_);
v___x_399_ = v___x_396_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_a_386_);
lean_ctor_set(v_reuseFailAlloc_403_, 1, v_a_388_);
v___x_399_ = v_reuseFailAlloc_403_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
lean_object* v___x_401_; 
if (v_isShared_391_ == 0)
{
lean_ctor_set(v___x_390_, 0, v___x_399_);
v___x_401_ = v___x_390_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v___x_399_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
}
}
else
{
size_t v___x_407_; size_t v___x_408_; uint8_t v___x_409_; 
v___x_407_ = lean_ptr_addr(v_decl_383_);
v___x_408_ = lean_ptr_addr(v_a_386_);
v___x_409_ = lean_usize_dec_eq(v___x_407_, v___x_408_);
if (v___x_409_ == 0)
{
lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_419_; 
v_isSharedCheck_419_ = !lean_is_exclusive(v_code_274_);
if (v_isSharedCheck_419_ == 0)
{
lean_object* v_unused_420_; lean_object* v_unused_421_; 
v_unused_420_ = lean_ctor_get(v_code_274_, 1);
lean_dec(v_unused_420_);
v_unused_421_ = lean_ctor_get(v_code_274_, 0);
lean_dec(v_unused_421_);
v___x_411_ = v_code_274_;
v_isShared_412_ = v_isSharedCheck_419_;
goto v_resetjp_410_;
}
else
{
lean_dec(v_code_274_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_419_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v___x_414_; 
if (v_isShared_412_ == 0)
{
lean_ctor_set(v___x_411_, 1, v_a_388_);
lean_ctor_set(v___x_411_, 0, v_a_386_);
v___x_414_ = v___x_411_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_a_386_);
lean_ctor_set(v_reuseFailAlloc_418_, 1, v_a_388_);
v___x_414_ = v_reuseFailAlloc_418_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
lean_object* v___x_416_; 
if (v_isShared_391_ == 0)
{
lean_ctor_set(v___x_390_, 0, v___x_414_);
v___x_416_ = v___x_390_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v___x_414_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
}
else
{
lean_object* v___x_423_; 
lean_dec(v_a_388_);
lean_dec(v_a_386_);
if (v_isShared_391_ == 0)
{
lean_ctor_set(v___x_390_, 0, v_code_274_);
v___x_423_ = v___x_390_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_code_274_);
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
lean_dec(v_a_386_);
lean_dec_ref_known(v_code_274_, 2);
return v___x_387_;
}
}
else
{
lean_object* v_a_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_433_; 
lean_dec_ref_known(v_code_274_, 2);
v_a_426_ = lean_ctor_get(v___x_385_, 0);
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_385_);
if (v_isSharedCheck_433_ == 0)
{
v___x_428_ = v___x_385_;
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_a_426_);
lean_dec(v___x_385_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_431_; 
if (v_isShared_429_ == 0)
{
v___x_431_ = v___x_428_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_a_426_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
}
}
case 4:
{
lean_object* v_cases_434_; lean_object* v_typeName_435_; lean_object* v_resultType_436_; lean_object* v_discr_437_; lean_object* v_alts_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_477_; 
v_cases_434_ = lean_ctor_get(v_code_274_, 0);
lean_inc_ref(v_cases_434_);
v_typeName_435_ = lean_ctor_get(v_cases_434_, 0);
v_resultType_436_ = lean_ctor_get(v_cases_434_, 1);
v_discr_437_ = lean_ctor_get(v_cases_434_, 2);
v_alts_438_ = lean_ctor_get(v_cases_434_, 3);
v_isSharedCheck_477_ = !lean_is_exclusive(v_cases_434_);
if (v_isSharedCheck_477_ == 0)
{
v___x_440_ = v_cases_434_;
v_isShared_441_ = v_isSharedCheck_477_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_alts_438_);
lean_inc(v_discr_437_);
lean_inc(v_resultType_436_);
lean_inc(v_typeName_435_);
lean_dec(v_cases_434_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_477_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_442_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_438_);
v___x_443_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__2(v_pu_273_, v_r_275_, v___x_442_, v_alts_438_, v_a_276_, v_a_277_, v_a_278_, v_a_279_);
if (lean_obj_tag(v___x_443_) == 0)
{
lean_object* v_a_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_468_; 
v_a_444_ = lean_ctor_get(v___x_443_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_468_ == 0)
{
v___x_446_ = v___x_443_;
v_isShared_447_ = v_isSharedCheck_468_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_a_444_);
lean_dec(v___x_443_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_468_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
size_t v___x_448_; size_t v___x_449_; uint8_t v___x_450_; 
v___x_448_ = lean_ptr_addr(v_alts_438_);
lean_dec_ref(v_alts_438_);
v___x_449_ = lean_ptr_addr(v_a_444_);
v___x_450_ = lean_usize_dec_eq(v___x_448_, v___x_449_);
if (v___x_450_ == 0)
{
lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_463_; 
v_isSharedCheck_463_ = !lean_is_exclusive(v_code_274_);
if (v_isSharedCheck_463_ == 0)
{
lean_object* v_unused_464_; 
v_unused_464_ = lean_ctor_get(v_code_274_, 0);
lean_dec(v_unused_464_);
v___x_452_ = v_code_274_;
v_isShared_453_ = v_isSharedCheck_463_;
goto v_resetjp_451_;
}
else
{
lean_dec(v_code_274_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_463_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_455_; 
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 3, v_a_444_);
v___x_455_ = v___x_440_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v_typeName_435_);
lean_ctor_set(v_reuseFailAlloc_462_, 1, v_resultType_436_);
lean_ctor_set(v_reuseFailAlloc_462_, 2, v_discr_437_);
lean_ctor_set(v_reuseFailAlloc_462_, 3, v_a_444_);
v___x_455_ = v_reuseFailAlloc_462_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
lean_object* v___x_457_; 
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 0, v___x_455_);
v___x_457_ = v___x_452_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v___x_455_);
v___x_457_ = v_reuseFailAlloc_461_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
lean_object* v___x_459_; 
if (v_isShared_447_ == 0)
{
lean_ctor_set(v___x_446_, 0, v___x_457_);
v___x_459_ = v___x_446_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v___x_457_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
}
}
}
else
{
lean_object* v___x_466_; 
lean_dec(v_a_444_);
lean_del_object(v___x_440_);
lean_dec(v_discr_437_);
lean_dec_ref(v_resultType_436_);
lean_dec(v_typeName_435_);
if (v_isShared_447_ == 0)
{
lean_ctor_set(v___x_446_, 0, v_code_274_);
v___x_466_ = v___x_446_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_code_274_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
}
}
else
{
lean_object* v_a_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_476_; 
lean_del_object(v___x_440_);
lean_dec_ref(v_alts_438_);
lean_dec(v_discr_437_);
lean_dec_ref(v_resultType_436_);
lean_dec(v_typeName_435_);
lean_dec_ref_known(v_code_274_, 1);
v_a_469_ = lean_ctor_get(v___x_443_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_476_ == 0)
{
v___x_471_ = v___x_443_;
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_a_469_);
lean_dec(v___x_443_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_474_; 
if (v_isShared_472_ == 0)
{
v___x_474_ = v___x_471_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_a_469_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
}
}
}
case 7:
{
lean_object* v_fvarId_478_; lean_object* v_i_479_; lean_object* v_y_480_; lean_object* v_k_481_; lean_object* v___x_482_; 
v_fvarId_478_ = lean_ctor_get(v_code_274_, 0);
v_i_479_ = lean_ctor_get(v_code_274_, 1);
v_y_480_ = lean_ctor_get(v_code_274_, 2);
v_k_481_ = lean_ctor_get(v_code_274_, 3);
lean_inc_ref(v_k_481_);
v___x_482_ = l_Lean_Compiler_LCNF_Code_applyRenaming(v_pu_273_, v_k_481_, v_r_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_);
if (lean_obj_tag(v___x_482_) == 0)
{
lean_object* v_a_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_507_; 
v_a_483_ = lean_ctor_get(v___x_482_, 0);
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_507_ == 0)
{
v___x_485_ = v___x_482_;
v_isShared_486_ = v_isSharedCheck_507_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_a_483_);
lean_dec(v___x_482_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_507_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
size_t v___x_487_; size_t v___x_488_; uint8_t v___x_489_; 
v___x_487_ = lean_ptr_addr(v_k_481_);
v___x_488_ = lean_ptr_addr(v_a_483_);
v___x_489_ = lean_usize_dec_eq(v___x_487_, v___x_488_);
if (v___x_489_ == 0)
{
lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_499_; 
lean_inc(v_y_480_);
lean_inc(v_i_479_);
lean_inc(v_fvarId_478_);
v_isSharedCheck_499_ = !lean_is_exclusive(v_code_274_);
if (v_isSharedCheck_499_ == 0)
{
lean_object* v_unused_500_; lean_object* v_unused_501_; lean_object* v_unused_502_; lean_object* v_unused_503_; 
v_unused_500_ = lean_ctor_get(v_code_274_, 3);
lean_dec(v_unused_500_);
v_unused_501_ = lean_ctor_get(v_code_274_, 2);
lean_dec(v_unused_501_);
v_unused_502_ = lean_ctor_get(v_code_274_, 1);
lean_dec(v_unused_502_);
v_unused_503_ = lean_ctor_get(v_code_274_, 0);
lean_dec(v_unused_503_);
v___x_491_ = v_code_274_;
v_isShared_492_ = v_isSharedCheck_499_;
goto v_resetjp_490_;
}
else
{
lean_dec(v_code_274_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_499_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v___x_494_; 
if (v_isShared_492_ == 0)
{
lean_ctor_set(v___x_491_, 3, v_a_483_);
v___x_494_ = v___x_491_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v_fvarId_478_);
lean_ctor_set(v_reuseFailAlloc_498_, 1, v_i_479_);
lean_ctor_set(v_reuseFailAlloc_498_, 2, v_y_480_);
lean_ctor_set(v_reuseFailAlloc_498_, 3, v_a_483_);
v___x_494_ = v_reuseFailAlloc_498_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
lean_object* v___x_496_; 
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 0, v___x_494_);
v___x_496_ = v___x_485_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v___x_494_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
}
else
{
lean_object* v___x_505_; 
lean_dec(v_a_483_);
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 0, v_code_274_);
v___x_505_ = v___x_485_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_code_274_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_274_, 4);
return v___x_482_;
}
}
case 8:
{
lean_object* v_fvarId_508_; lean_object* v_i_509_; lean_object* v_y_510_; lean_object* v_k_511_; lean_object* v___x_512_; 
v_fvarId_508_ = lean_ctor_get(v_code_274_, 0);
v_i_509_ = lean_ctor_get(v_code_274_, 1);
v_y_510_ = lean_ctor_get(v_code_274_, 2);
v_k_511_ = lean_ctor_get(v_code_274_, 3);
lean_inc_ref(v_k_511_);
v___x_512_ = l_Lean_Compiler_LCNF_Code_applyRenaming(v_pu_273_, v_k_511_, v_r_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_);
if (lean_obj_tag(v___x_512_) == 0)
{
lean_object* v_a_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_537_; 
v_a_513_ = lean_ctor_get(v___x_512_, 0);
v_isSharedCheck_537_ = !lean_is_exclusive(v___x_512_);
if (v_isSharedCheck_537_ == 0)
{
v___x_515_ = v___x_512_;
v_isShared_516_ = v_isSharedCheck_537_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_a_513_);
lean_dec(v___x_512_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_537_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
size_t v___x_517_; size_t v___x_518_; uint8_t v___x_519_; 
v___x_517_ = lean_ptr_addr(v_k_511_);
v___x_518_ = lean_ptr_addr(v_a_513_);
v___x_519_ = lean_usize_dec_eq(v___x_517_, v___x_518_);
if (v___x_519_ == 0)
{
lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_529_; 
lean_inc(v_y_510_);
lean_inc(v_i_509_);
lean_inc(v_fvarId_508_);
v_isSharedCheck_529_ = !lean_is_exclusive(v_code_274_);
if (v_isSharedCheck_529_ == 0)
{
lean_object* v_unused_530_; lean_object* v_unused_531_; lean_object* v_unused_532_; lean_object* v_unused_533_; 
v_unused_530_ = lean_ctor_get(v_code_274_, 3);
lean_dec(v_unused_530_);
v_unused_531_ = lean_ctor_get(v_code_274_, 2);
lean_dec(v_unused_531_);
v_unused_532_ = lean_ctor_get(v_code_274_, 1);
lean_dec(v_unused_532_);
v_unused_533_ = lean_ctor_get(v_code_274_, 0);
lean_dec(v_unused_533_);
v___x_521_ = v_code_274_;
v_isShared_522_ = v_isSharedCheck_529_;
goto v_resetjp_520_;
}
else
{
lean_dec(v_code_274_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_529_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_524_; 
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 3, v_a_513_);
v___x_524_ = v___x_521_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_fvarId_508_);
lean_ctor_set(v_reuseFailAlloc_528_, 1, v_i_509_);
lean_ctor_set(v_reuseFailAlloc_528_, 2, v_y_510_);
lean_ctor_set(v_reuseFailAlloc_528_, 3, v_a_513_);
v___x_524_ = v_reuseFailAlloc_528_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
lean_object* v___x_526_; 
if (v_isShared_516_ == 0)
{
lean_ctor_set(v___x_515_, 0, v___x_524_);
v___x_526_ = v___x_515_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v___x_524_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
}
}
else
{
lean_object* v___x_535_; 
lean_dec(v_a_513_);
if (v_isShared_516_ == 0)
{
lean_ctor_set(v___x_515_, 0, v_code_274_);
v___x_535_ = v___x_515_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v_code_274_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_274_, 4);
return v___x_512_;
}
}
case 9:
{
lean_object* v_fvarId_538_; lean_object* v_i_539_; lean_object* v_offset_540_; lean_object* v_y_541_; lean_object* v_ty_542_; lean_object* v_k_543_; lean_object* v___x_544_; 
v_fvarId_538_ = lean_ctor_get(v_code_274_, 0);
v_i_539_ = lean_ctor_get(v_code_274_, 1);
v_offset_540_ = lean_ctor_get(v_code_274_, 2);
v_y_541_ = lean_ctor_get(v_code_274_, 3);
v_ty_542_ = lean_ctor_get(v_code_274_, 4);
v_k_543_ = lean_ctor_get(v_code_274_, 5);
lean_inc_ref(v_k_543_);
v___x_544_ = l_Lean_Compiler_LCNF_Code_applyRenaming(v_pu_273_, v_k_543_, v_r_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_);
if (lean_obj_tag(v___x_544_) == 0)
{
lean_object* v_a_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_571_; 
v_a_545_ = lean_ctor_get(v___x_544_, 0);
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_571_ == 0)
{
v___x_547_ = v___x_544_;
v_isShared_548_ = v_isSharedCheck_571_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_a_545_);
lean_dec(v___x_544_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_571_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
size_t v___x_549_; size_t v___x_550_; uint8_t v___x_551_; 
v___x_549_ = lean_ptr_addr(v_k_543_);
v___x_550_ = lean_ptr_addr(v_a_545_);
v___x_551_ = lean_usize_dec_eq(v___x_549_, v___x_550_);
if (v___x_551_ == 0)
{
lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_561_; 
lean_inc_ref(v_ty_542_);
lean_inc(v_y_541_);
lean_inc(v_offset_540_);
lean_inc(v_i_539_);
lean_inc(v_fvarId_538_);
v_isSharedCheck_561_ = !lean_is_exclusive(v_code_274_);
if (v_isSharedCheck_561_ == 0)
{
lean_object* v_unused_562_; lean_object* v_unused_563_; lean_object* v_unused_564_; lean_object* v_unused_565_; lean_object* v_unused_566_; lean_object* v_unused_567_; 
v_unused_562_ = lean_ctor_get(v_code_274_, 5);
lean_dec(v_unused_562_);
v_unused_563_ = lean_ctor_get(v_code_274_, 4);
lean_dec(v_unused_563_);
v_unused_564_ = lean_ctor_get(v_code_274_, 3);
lean_dec(v_unused_564_);
v_unused_565_ = lean_ctor_get(v_code_274_, 2);
lean_dec(v_unused_565_);
v_unused_566_ = lean_ctor_get(v_code_274_, 1);
lean_dec(v_unused_566_);
v_unused_567_ = lean_ctor_get(v_code_274_, 0);
lean_dec(v_unused_567_);
v___x_553_ = v_code_274_;
v_isShared_554_ = v_isSharedCheck_561_;
goto v_resetjp_552_;
}
else
{
lean_dec(v_code_274_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_561_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v___x_556_; 
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 5, v_a_545_);
v___x_556_ = v___x_553_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_fvarId_538_);
lean_ctor_set(v_reuseFailAlloc_560_, 1, v_i_539_);
lean_ctor_set(v_reuseFailAlloc_560_, 2, v_offset_540_);
lean_ctor_set(v_reuseFailAlloc_560_, 3, v_y_541_);
lean_ctor_set(v_reuseFailAlloc_560_, 4, v_ty_542_);
lean_ctor_set(v_reuseFailAlloc_560_, 5, v_a_545_);
v___x_556_ = v_reuseFailAlloc_560_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
lean_object* v___x_558_; 
if (v_isShared_548_ == 0)
{
lean_ctor_set(v___x_547_, 0, v___x_556_);
v___x_558_ = v___x_547_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v___x_556_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
}
else
{
lean_object* v___x_569_; 
lean_dec(v_a_545_);
if (v_isShared_548_ == 0)
{
lean_ctor_set(v___x_547_, 0, v_code_274_);
v___x_569_ = v___x_547_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_code_274_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_274_, 6);
return v___x_544_;
}
}
case 10:
{
lean_object* v_fvarId_572_; lean_object* v_cidx_573_; lean_object* v_k_574_; lean_object* v___x_575_; 
v_fvarId_572_ = lean_ctor_get(v_code_274_, 0);
v_cidx_573_ = lean_ctor_get(v_code_274_, 1);
v_k_574_ = lean_ctor_get(v_code_274_, 2);
lean_inc_ref(v_k_574_);
v___x_575_ = l_Lean_Compiler_LCNF_Code_applyRenaming(v_pu_273_, v_k_574_, v_r_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_);
if (lean_obj_tag(v___x_575_) == 0)
{
lean_object* v_a_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_599_; 
v_a_576_ = lean_ctor_get(v___x_575_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_599_ == 0)
{
v___x_578_ = v___x_575_;
v_isShared_579_ = v_isSharedCheck_599_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_a_576_);
lean_dec(v___x_575_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_599_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
size_t v___x_580_; size_t v___x_581_; uint8_t v___x_582_; 
v___x_580_ = lean_ptr_addr(v_k_574_);
v___x_581_ = lean_ptr_addr(v_a_576_);
v___x_582_ = lean_usize_dec_eq(v___x_580_, v___x_581_);
if (v___x_582_ == 0)
{
lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_592_; 
lean_inc(v_cidx_573_);
lean_inc(v_fvarId_572_);
v_isSharedCheck_592_ = !lean_is_exclusive(v_code_274_);
if (v_isSharedCheck_592_ == 0)
{
lean_object* v_unused_593_; lean_object* v_unused_594_; lean_object* v_unused_595_; 
v_unused_593_ = lean_ctor_get(v_code_274_, 2);
lean_dec(v_unused_593_);
v_unused_594_ = lean_ctor_get(v_code_274_, 1);
lean_dec(v_unused_594_);
v_unused_595_ = lean_ctor_get(v_code_274_, 0);
lean_dec(v_unused_595_);
v___x_584_ = v_code_274_;
v_isShared_585_ = v_isSharedCheck_592_;
goto v_resetjp_583_;
}
else
{
lean_dec(v_code_274_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_592_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_587_; 
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 2, v_a_576_);
v___x_587_ = v___x_584_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_fvarId_572_);
lean_ctor_set(v_reuseFailAlloc_591_, 1, v_cidx_573_);
lean_ctor_set(v_reuseFailAlloc_591_, 2, v_a_576_);
v___x_587_ = v_reuseFailAlloc_591_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
lean_object* v___x_589_; 
if (v_isShared_579_ == 0)
{
lean_ctor_set(v___x_578_, 0, v___x_587_);
v___x_589_ = v___x_578_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v___x_587_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
}
}
else
{
lean_object* v___x_597_; 
lean_dec(v_a_576_);
if (v_isShared_579_ == 0)
{
lean_ctor_set(v___x_578_, 0, v_code_274_);
v___x_597_ = v___x_578_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_code_274_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_274_, 3);
return v___x_575_;
}
}
case 11:
{
lean_object* v_fvarId_600_; lean_object* v_n_601_; uint8_t v_check_602_; uint8_t v_persistent_603_; lean_object* v_k_604_; lean_object* v___x_605_; 
v_fvarId_600_ = lean_ctor_get(v_code_274_, 0);
v_n_601_ = lean_ctor_get(v_code_274_, 1);
v_check_602_ = lean_ctor_get_uint8(v_code_274_, sizeof(void*)*3);
v_persistent_603_ = lean_ctor_get_uint8(v_code_274_, sizeof(void*)*3 + 1);
v_k_604_ = lean_ctor_get(v_code_274_, 2);
lean_inc_ref(v_k_604_);
v___x_605_ = l_Lean_Compiler_LCNF_Code_applyRenaming(v_pu_273_, v_k_604_, v_r_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_);
if (lean_obj_tag(v___x_605_) == 0)
{
lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_629_; 
v_a_606_ = lean_ctor_get(v___x_605_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_605_);
if (v_isSharedCheck_629_ == 0)
{
v___x_608_ = v___x_605_;
v_isShared_609_ = v_isSharedCheck_629_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_dec(v___x_605_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_629_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
size_t v___x_610_; size_t v___x_611_; uint8_t v___x_612_; 
v___x_610_ = lean_ptr_addr(v_k_604_);
v___x_611_ = lean_ptr_addr(v_a_606_);
v___x_612_ = lean_usize_dec_eq(v___x_610_, v___x_611_);
if (v___x_612_ == 0)
{
lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_622_; 
lean_inc(v_n_601_);
lean_inc(v_fvarId_600_);
v_isSharedCheck_622_ = !lean_is_exclusive(v_code_274_);
if (v_isSharedCheck_622_ == 0)
{
lean_object* v_unused_623_; lean_object* v_unused_624_; lean_object* v_unused_625_; 
v_unused_623_ = lean_ctor_get(v_code_274_, 2);
lean_dec(v_unused_623_);
v_unused_624_ = lean_ctor_get(v_code_274_, 1);
lean_dec(v_unused_624_);
v_unused_625_ = lean_ctor_get(v_code_274_, 0);
lean_dec(v_unused_625_);
v___x_614_ = v_code_274_;
v_isShared_615_ = v_isSharedCheck_622_;
goto v_resetjp_613_;
}
else
{
lean_dec(v_code_274_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_622_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___x_617_; 
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 2, v_a_606_);
v___x_617_ = v___x_614_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_fvarId_600_);
lean_ctor_set(v_reuseFailAlloc_621_, 1, v_n_601_);
lean_ctor_set(v_reuseFailAlloc_621_, 2, v_a_606_);
lean_ctor_set_uint8(v_reuseFailAlloc_621_, sizeof(void*)*3, v_check_602_);
lean_ctor_set_uint8(v_reuseFailAlloc_621_, sizeof(void*)*3 + 1, v_persistent_603_);
v___x_617_ = v_reuseFailAlloc_621_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
lean_object* v___x_619_; 
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 0, v___x_617_);
v___x_619_ = v___x_608_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v___x_617_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
}
}
else
{
lean_object* v___x_627_; 
lean_dec(v_a_606_);
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 0, v_code_274_);
v___x_627_ = v___x_608_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_code_274_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_274_, 3);
return v___x_605_;
}
}
case 12:
{
lean_object* v_fvarId_630_; lean_object* v_n_631_; uint8_t v_check_632_; uint8_t v_persistent_633_; lean_object* v_objs_x3f_634_; lean_object* v_k_635_; lean_object* v___x_636_; 
v_fvarId_630_ = lean_ctor_get(v_code_274_, 0);
v_n_631_ = lean_ctor_get(v_code_274_, 1);
v_check_632_ = lean_ctor_get_uint8(v_code_274_, sizeof(void*)*4);
v_persistent_633_ = lean_ctor_get_uint8(v_code_274_, sizeof(void*)*4 + 1);
v_objs_x3f_634_ = lean_ctor_get(v_code_274_, 2);
v_k_635_ = lean_ctor_get(v_code_274_, 3);
lean_inc_ref(v_k_635_);
v___x_636_ = l_Lean_Compiler_LCNF_Code_applyRenaming(v_pu_273_, v_k_635_, v_r_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_);
if (lean_obj_tag(v___x_636_) == 0)
{
lean_object* v_a_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_661_; 
v_a_637_ = lean_ctor_get(v___x_636_, 0);
v_isSharedCheck_661_ = !lean_is_exclusive(v___x_636_);
if (v_isSharedCheck_661_ == 0)
{
v___x_639_ = v___x_636_;
v_isShared_640_ = v_isSharedCheck_661_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_a_637_);
lean_dec(v___x_636_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_661_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
size_t v___x_641_; size_t v___x_642_; uint8_t v___x_643_; 
v___x_641_ = lean_ptr_addr(v_k_635_);
v___x_642_ = lean_ptr_addr(v_a_637_);
v___x_643_ = lean_usize_dec_eq(v___x_641_, v___x_642_);
if (v___x_643_ == 0)
{
lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_653_; 
lean_inc(v_objs_x3f_634_);
lean_inc(v_n_631_);
lean_inc(v_fvarId_630_);
v_isSharedCheck_653_ = !lean_is_exclusive(v_code_274_);
if (v_isSharedCheck_653_ == 0)
{
lean_object* v_unused_654_; lean_object* v_unused_655_; lean_object* v_unused_656_; lean_object* v_unused_657_; 
v_unused_654_ = lean_ctor_get(v_code_274_, 3);
lean_dec(v_unused_654_);
v_unused_655_ = lean_ctor_get(v_code_274_, 2);
lean_dec(v_unused_655_);
v_unused_656_ = lean_ctor_get(v_code_274_, 1);
lean_dec(v_unused_656_);
v_unused_657_ = lean_ctor_get(v_code_274_, 0);
lean_dec(v_unused_657_);
v___x_645_ = v_code_274_;
v_isShared_646_ = v_isSharedCheck_653_;
goto v_resetjp_644_;
}
else
{
lean_dec(v_code_274_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_653_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_648_; 
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 3, v_a_637_);
v___x_648_ = v___x_645_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_fvarId_630_);
lean_ctor_set(v_reuseFailAlloc_652_, 1, v_n_631_);
lean_ctor_set(v_reuseFailAlloc_652_, 2, v_objs_x3f_634_);
lean_ctor_set(v_reuseFailAlloc_652_, 3, v_a_637_);
lean_ctor_set_uint8(v_reuseFailAlloc_652_, sizeof(void*)*4, v_check_632_);
lean_ctor_set_uint8(v_reuseFailAlloc_652_, sizeof(void*)*4 + 1, v_persistent_633_);
v___x_648_ = v_reuseFailAlloc_652_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
lean_object* v___x_650_; 
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 0, v___x_648_);
v___x_650_ = v___x_639_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v___x_648_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
}
else
{
lean_object* v___x_659_; 
lean_dec(v_a_637_);
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 0, v_code_274_);
v___x_659_ = v___x_639_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_code_274_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_274_, 4);
return v___x_636_;
}
}
case 13:
{
lean_object* v_fvarId_662_; lean_object* v_k_663_; lean_object* v___x_664_; 
v_fvarId_662_ = lean_ctor_get(v_code_274_, 0);
v_k_663_ = lean_ctor_get(v_code_274_, 1);
lean_inc_ref(v_k_663_);
v___x_664_ = l_Lean_Compiler_LCNF_Code_applyRenaming(v_pu_273_, v_k_663_, v_r_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_);
if (lean_obj_tag(v___x_664_) == 0)
{
lean_object* v_a_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_687_; 
v_a_665_ = lean_ctor_get(v___x_664_, 0);
v_isSharedCheck_687_ = !lean_is_exclusive(v___x_664_);
if (v_isSharedCheck_687_ == 0)
{
v___x_667_ = v___x_664_;
v_isShared_668_ = v_isSharedCheck_687_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_a_665_);
lean_dec(v___x_664_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_687_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
size_t v___x_669_; size_t v___x_670_; uint8_t v___x_671_; 
v___x_669_ = lean_ptr_addr(v_k_663_);
v___x_670_ = lean_ptr_addr(v_a_665_);
v___x_671_ = lean_usize_dec_eq(v___x_669_, v___x_670_);
if (v___x_671_ == 0)
{
lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_681_; 
lean_inc(v_fvarId_662_);
v_isSharedCheck_681_ = !lean_is_exclusive(v_code_274_);
if (v_isSharedCheck_681_ == 0)
{
lean_object* v_unused_682_; lean_object* v_unused_683_; 
v_unused_682_ = lean_ctor_get(v_code_274_, 1);
lean_dec(v_unused_682_);
v_unused_683_ = lean_ctor_get(v_code_274_, 0);
lean_dec(v_unused_683_);
v___x_673_ = v_code_274_;
v_isShared_674_ = v_isSharedCheck_681_;
goto v_resetjp_672_;
}
else
{
lean_dec(v_code_274_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_681_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_676_; 
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 1, v_a_665_);
v___x_676_ = v___x_673_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_fvarId_662_);
lean_ctor_set(v_reuseFailAlloc_680_, 1, v_a_665_);
v___x_676_ = v_reuseFailAlloc_680_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
lean_object* v___x_678_; 
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 0, v___x_676_);
v___x_678_ = v___x_667_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v___x_676_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
}
}
else
{
lean_object* v___x_685_; 
lean_dec(v_a_665_);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 0, v_code_274_);
v___x_685_ = v___x_667_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_code_274_);
v___x_685_ = v_reuseFailAlloc_686_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
return v___x_685_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_274_, 2);
return v___x_664_;
}
}
default: 
{
lean_object* v___x_688_; 
v___x_688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_688_, 0, v_code_274_);
return v___x_688_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Code_applyRenaming_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_273_ = stack[0].m_num;
lean_object* v_code_274_ = stack[1].m_obj;
lean_object* v_r_275_ = stack[2].m_obj;
lean_object* v_a_276_ = stack[3].m_obj;
lean_object* v_a_277_ = stack[4].m_obj;
lean_object* v_a_278_ = stack[5].m_obj;
lean_object* v_a_279_ = stack[6].m_obj;
lean_object* v_res_689_;
v_res_689_ = l_Lean_Compiler_LCNF_Code_applyRenaming(v_pu_273_, v_code_274_, v_r_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_);
stack->m_obj
 = v_res_689_;
}
lean_object* l_Lean_Compiler_LCNF_FunDecl_applyRenaming(uint8_t v_pu_690_, lean_object* v_decl_691_, lean_object* v_r_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_){
_start:
{
lean_object* v_fvarId_698_; lean_object* v_params_699_; lean_object* v_type_700_; lean_object* v_value_701_; lean_object* v___x_702_; 
v_fvarId_698_ = lean_ctor_get(v_decl_691_, 0);
v_params_699_ = lean_ctor_get(v_decl_691_, 2);
lean_inc_ref(v_params_699_);
v_type_700_ = lean_ctor_get(v_decl_691_, 3);
lean_inc_ref(v_type_700_);
v_value_701_ = lean_ctor_get(v_decl_691_, 4);
v___x_702_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Param_applyRenaming_spec__0___redArg(v_r_692_, v_fvarId_698_);
if (lean_obj_tag(v___x_702_) == 1)
{
lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_733_; 
lean_inc_ref(v_value_701_);
lean_inc(v_fvarId_698_);
v_isSharedCheck_733_ = !lean_is_exclusive(v_decl_691_);
if (v_isSharedCheck_733_ == 0)
{
lean_object* v_unused_734_; lean_object* v_unused_735_; lean_object* v_unused_736_; lean_object* v_unused_737_; lean_object* v_unused_738_; 
v_unused_734_ = lean_ctor_get(v_decl_691_, 4);
lean_dec(v_unused_734_);
v_unused_735_ = lean_ctor_get(v_decl_691_, 3);
lean_dec(v_unused_735_);
v_unused_736_ = lean_ctor_get(v_decl_691_, 2);
lean_dec(v_unused_736_);
v_unused_737_ = lean_ctor_get(v_decl_691_, 1);
lean_dec(v_unused_737_);
v_unused_738_ = lean_ctor_get(v_decl_691_, 0);
lean_dec(v_unused_738_);
v___x_704_ = v_decl_691_;
v_isShared_705_ = v_isSharedCheck_733_;
goto v_resetjp_703_;
}
else
{
lean_dec(v_decl_691_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_733_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v_val_706_; lean_object* v_decl_708_; 
v_val_706_ = lean_ctor_get(v___x_702_, 0);
lean_inc(v_val_706_);
lean_dec_ref_known(v___x_702_, 1);
lean_inc_ref(v_value_701_);
lean_inc_ref(v_type_700_);
lean_inc_ref(v_params_699_);
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 1, v_val_706_);
v_decl_708_ = v___x_704_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_fvarId_698_);
lean_ctor_set(v_reuseFailAlloc_732_, 1, v_val_706_);
lean_ctor_set(v_reuseFailAlloc_732_, 2, v_params_699_);
lean_ctor_set(v_reuseFailAlloc_732_, 3, v_type_700_);
lean_ctor_set(v_reuseFailAlloc_732_, 4, v_value_701_);
v_decl_708_ = v_reuseFailAlloc_732_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
lean_object* v___x_709_; lean_object* v_lctx_710_; lean_object* v_nextIdx_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_731_; 
v___x_709_ = lean_st_ref_take(v_a_694_);
v_lctx_710_ = lean_ctor_get(v___x_709_, 0);
v_nextIdx_711_ = lean_ctor_get(v___x_709_, 1);
v_isSharedCheck_731_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_731_ == 0)
{
v___x_713_ = v___x_709_;
v_isShared_714_ = v_isSharedCheck_731_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_nextIdx_711_);
lean_inc(v_lctx_710_);
lean_dec(v___x_709_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_731_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_715_; lean_object* v___x_717_; 
lean_inc_ref(v_decl_708_);
v___x_715_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v_pu_690_, v_lctx_710_, v_decl_708_);
if (v_isShared_714_ == 0)
{
lean_ctor_set(v___x_713_, 0, v___x_715_);
v___x_717_ = v___x_713_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v___x_715_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v_nextIdx_711_);
v___x_717_ = v_reuseFailAlloc_730_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_718_ = lean_st_ref_put(v_a_694_, v___x_717_);
v___x_719_ = l_Lean_Compiler_LCNF_Code_applyRenaming(v_pu_690_, v_value_701_, v_r_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_);
if (lean_obj_tag(v___x_719_) == 0)
{
lean_object* v_a_720_; lean_object* v___x_721_; 
v_a_720_ = lean_ctor_get(v___x_719_, 0);
lean_inc(v_a_720_);
lean_dec_ref_known(v___x_719_, 1);
v___x_721_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_690_, v_decl_708_, v_type_700_, v_params_699_, v_a_720_, v_a_694_);
return v___x_721_;
}
else
{
lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_729_; 
lean_dec_ref(v_decl_708_);
lean_dec_ref(v_type_700_);
lean_dec_ref(v_params_699_);
v_a_722_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_729_ == 0)
{
v___x_724_ = v___x_719_;
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v___x_719_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_727_; 
if (v_isShared_725_ == 0)
{
v___x_727_ = v___x_724_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_a_722_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
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
lean_object* v___x_739_; 
lean_dec(v___x_702_);
lean_inc_ref(v_value_701_);
v___x_739_ = l_Lean_Compiler_LCNF_Code_applyRenaming(v_pu_690_, v_value_701_, v_r_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_);
if (lean_obj_tag(v___x_739_) == 0)
{
lean_object* v_a_740_; lean_object* v___x_741_; 
v_a_740_ = lean_ctor_get(v___x_739_, 0);
lean_inc(v_a_740_);
lean_dec_ref_known(v___x_739_, 1);
v___x_741_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_690_, v_decl_691_, v_type_700_, v_params_699_, v_a_740_, v_a_694_);
return v___x_741_;
}
else
{
lean_object* v_a_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_749_; 
lean_dec_ref(v_type_700_);
lean_dec_ref(v_params_699_);
lean_dec_ref(v_decl_691_);
v_a_742_ = lean_ctor_get(v___x_739_, 0);
v_isSharedCheck_749_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_749_ == 0)
{
v___x_744_ = v___x_739_;
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_a_742_);
lean_dec(v___x_739_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_747_; 
if (v_isShared_745_ == 0)
{
v___x_747_ = v___x_744_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_a_742_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_FunDecl_applyRenaming_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_690_ = stack[0].m_num;
lean_object* v_decl_691_ = stack[1].m_obj;
lean_object* v_r_692_ = stack[2].m_obj;
lean_object* v_a_693_ = stack[3].m_obj;
lean_object* v_a_694_ = stack[4].m_obj;
lean_object* v_a_695_ = stack[5].m_obj;
lean_object* v_a_696_ = stack[6].m_obj;
lean_object* v_res_750_;
v_res_750_ = l_Lean_Compiler_LCNF_FunDecl_applyRenaming(v_pu_690_, v_decl_691_, v_r_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_);
stack->m_obj
 = v_res_750_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_applyRenaming___boxed(lean_object* v_pu_751_, lean_object* v_decl_752_, lean_object* v_r_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_){
_start:
{
uint8_t v_pu_boxed_759_; lean_object* v_res_760_; 
v_pu_boxed_759_ = lean_unbox(v_pu_751_);
v_res_760_ = l_Lean_Compiler_LCNF_FunDecl_applyRenaming(v_pu_boxed_759_, v_decl_752_, v_r_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_);
lean_dec(v_a_757_);
lean_dec_ref(v_a_756_);
lean_dec(v_a_755_);
lean_dec_ref(v_a_754_);
lean_dec(v_r_753_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__2___boxed(lean_object* v_pu_761_, lean_object* v_r_762_, lean_object* v_i_763_, lean_object* v_as_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_){
_start:
{
uint8_t v_pu_boxed_770_; lean_object* v_res_771_; 
v_pu_boxed_770_ = lean_unbox(v_pu_761_);
v_res_771_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__2(v_pu_boxed_770_, v_r_762_, v_i_763_, v_as_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_);
lean_dec(v___y_768_);
lean_dec_ref(v___y_767_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
lean_dec(v_r_762_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_applyRenaming___boxed(lean_object* v_pu_772_, lean_object* v_code_773_, lean_object* v_r_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_){
_start:
{
uint8_t v_pu_boxed_780_; lean_object* v_res_781_; 
v_pu_boxed_780_ = lean_unbox(v_pu_772_);
v_res_781_ = l_Lean_Compiler_LCNF_Code_applyRenaming(v_pu_boxed_780_, v_code_773_, v_r_774_, v_a_775_, v_a_776_, v_a_777_, v_a_778_);
lean_dec(v_a_778_);
lean_dec_ref(v_a_777_);
lean_dec(v_a_776_);
lean_dec_ref(v_a_775_);
lean_dec(v_r_774_);
return v_res_781_;
}
}
lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__1(uint8_t v_pu_782_, lean_object* v_r_783_, lean_object* v_i_784_, lean_object* v_as_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_){
_start:
{
lean_object* v___x_791_; 
v___x_791_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__1___redArg(v_pu_782_, v_r_783_, v_i_784_, v_as_785_, v___y_787_);
return v___x_791_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_782_ = stack[0].m_num;
lean_object* v_r_783_ = stack[1].m_obj;
lean_object* v_i_784_ = stack[2].m_obj;
lean_object* v_as_785_ = stack[3].m_obj;
lean_object* v___y_786_ = stack[4].m_obj;
lean_object* v___y_787_ = stack[5].m_obj;
lean_object* v___y_788_ = stack[6].m_obj;
lean_object* v___y_789_ = stack[7].m_obj;
lean_object* v_res_792_;
v_res_792_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__1(v_pu_782_, v_r_783_, v_i_784_, v_as_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_);
stack->m_obj
 = v_res_792_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__1___boxed(lean_object* v_pu_793_, lean_object* v_r_794_, lean_object* v_i_795_, lean_object* v_as_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_){
_start:
{
uint8_t v_pu_boxed_802_; lean_object* v_res_803_; 
v_pu_boxed_802_ = lean_unbox(v_pu_793_);
v_res_803_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__1(v_pu_boxed_802_, v_r_794_, v_i_795_, v_as_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_);
lean_dec(v___y_800_);
lean_dec_ref(v___y_799_);
lean_dec(v___y_798_);
lean_dec_ref(v___y_797_);
lean_dec(v_r_794_);
return v_res_803_;
}
}
lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_applyRenaming_spec__0___redArg(lean_object* v_f_804_, lean_object* v_v_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_){
_start:
{
if (lean_obj_tag(v_v_805_) == 0)
{
lean_object* v_code_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_835_; 
v_code_811_ = lean_ctor_get(v_v_805_, 0);
v_isSharedCheck_835_ = !lean_is_exclusive(v_v_805_);
if (v_isSharedCheck_835_ == 0)
{
v___x_813_ = v_v_805_;
v_isShared_814_ = v_isSharedCheck_835_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_code_811_);
lean_dec(v_v_805_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_835_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_815_; 
lean_inc(v___y_809_);
lean_inc_ref(v___y_808_);
lean_inc(v___y_807_);
lean_inc_ref(v___y_806_);
v___x_815_ = lean_apply_6(v_f_804_, v_code_811_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, lean_box(0));
if (lean_obj_tag(v___x_815_) == 0)
{
lean_object* v_a_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_826_; 
v_a_816_ = lean_ctor_get(v___x_815_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_815_);
if (v_isSharedCheck_826_ == 0)
{
v___x_818_ = v___x_815_;
v_isShared_819_ = v_isSharedCheck_826_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_a_816_);
lean_dec(v___x_815_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_826_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v___x_821_; 
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 0, v_a_816_);
v___x_821_ = v___x_813_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_a_816_);
v___x_821_ = v_reuseFailAlloc_825_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
lean_object* v___x_823_; 
if (v_isShared_819_ == 0)
{
lean_ctor_set(v___x_818_, 0, v___x_821_);
v___x_823_ = v___x_818_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v___x_821_);
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
else
{
lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_834_; 
lean_del_object(v___x_813_);
v_a_827_ = lean_ctor_get(v___x_815_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_815_);
if (v_isSharedCheck_834_ == 0)
{
v___x_829_ = v___x_815_;
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_815_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_832_; 
if (v_isShared_830_ == 0)
{
v___x_832_ = v___x_829_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_a_827_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
}
}
else
{
lean_object* v___x_836_; 
lean_dec_ref(v_f_804_);
v___x_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_836_, 0, v_v_805_);
return v___x_836_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_applyRenaming_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_804_ = stack[0].m_obj;
lean_object* v_v_805_ = stack[1].m_obj;
lean_object* v___y_806_ = stack[2].m_obj;
lean_object* v___y_807_ = stack[3].m_obj;
lean_object* v___y_808_ = stack[4].m_obj;
lean_object* v___y_809_ = stack[5].m_obj;
lean_object* v_res_837_;
v_res_837_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_applyRenaming_spec__0___redArg(v_f_804_, v_v_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_);
stack->m_obj
 = v_res_837_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_applyRenaming_spec__0___redArg___boxed(lean_object* v_f_838_, lean_object* v_v_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_applyRenaming_spec__0___redArg(v_f_838_, v_v_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
lean_dec(v___y_841_);
lean_dec_ref(v___y_840_);
return v_res_845_;
}
}
lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_applyRenaming_spec__0(uint8_t v_pu_846_, lean_object* v_f_847_, lean_object* v_v_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
lean_object* v___x_854_; 
v___x_854_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_applyRenaming_spec__0___redArg(v_f_847_, v_v_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
return v___x_854_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_applyRenaming_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_846_ = stack[0].m_num;
lean_object* v_f_847_ = stack[1].m_obj;
lean_object* v_v_848_ = stack[2].m_obj;
lean_object* v___y_849_ = stack[3].m_obj;
lean_object* v___y_850_ = stack[4].m_obj;
lean_object* v___y_851_ = stack[5].m_obj;
lean_object* v___y_852_ = stack[6].m_obj;
lean_object* v_res_855_;
v_res_855_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_applyRenaming_spec__0(v_pu_846_, v_f_847_, v_v_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
stack->m_obj
 = v_res_855_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_applyRenaming_spec__0___boxed(lean_object* v_pu_856_, lean_object* v_f_857_, lean_object* v_v_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_){
_start:
{
uint8_t v_pu_boxed_864_; lean_object* v_res_865_; 
v_pu_boxed_864_ = lean_unbox(v_pu_856_);
v_res_865_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_applyRenaming_spec__0(v_pu_boxed_864_, v_f_857_, v_v_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_);
lean_dec(v___y_862_);
lean_dec_ref(v___y_861_);
lean_dec(v___y_860_);
lean_dec_ref(v___y_859_);
return v_res_865_;
}
}
lean_object* l_Lean_Compiler_LCNF_Decl_applyRenaming___lam__0(uint8_t v_pu_866_, lean_object* v_r_867_, lean_object* v_x_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_){
_start:
{
lean_object* v___x_874_; 
v___x_874_ = l_Lean_Compiler_LCNF_Code_applyRenaming(v_pu_866_, v_x_868_, v_r_867_, v___y_869_, v___y_870_, v___y_871_, v___y_872_);
return v___x_874_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Decl_applyRenaming___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_866_ = stack[0].m_num;
lean_object* v_r_867_ = stack[1].m_obj;
lean_object* v_x_868_ = stack[2].m_obj;
lean_object* v___y_869_ = stack[3].m_obj;
lean_object* v___y_870_ = stack[4].m_obj;
lean_object* v___y_871_ = stack[5].m_obj;
lean_object* v___y_872_ = stack[6].m_obj;
lean_object* v_res_875_;
v_res_875_ = l_Lean_Compiler_LCNF_Decl_applyRenaming___lam__0(v_pu_866_, v_r_867_, v_x_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_);
stack->m_obj
 = v_res_875_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_applyRenaming___lam__0___boxed(lean_object* v_pu_876_, lean_object* v_r_877_, lean_object* v_x_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_){
_start:
{
uint8_t v_pu_boxed_884_; lean_object* v_res_885_; 
v_pu_boxed_884_ = lean_unbox(v_pu_876_);
v_res_885_ = l_Lean_Compiler_LCNF_Decl_applyRenaming___lam__0(v_pu_boxed_884_, v_r_877_, v_x_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_);
lean_dec(v___y_882_);
lean_dec_ref(v___y_881_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
lean_dec(v_r_877_);
return v_res_885_;
}
}
lean_object* l_Lean_Compiler_LCNF_Decl_applyRenaming(uint8_t v_pu_886_, lean_object* v_decl_887_, lean_object* v_r_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_){
_start:
{
if (lean_obj_tag(v_r_888_) == 0)
{
lean_object* v_toSignature_894_; lean_object* v_value_895_; uint8_t v_recursive_896_; lean_object* v_inlineAttr_x3f_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_946_; 
v_toSignature_894_ = lean_ctor_get(v_decl_887_, 0);
v_value_895_ = lean_ctor_get(v_decl_887_, 1);
v_recursive_896_ = lean_ctor_get_uint8(v_decl_887_, sizeof(void*)*3);
v_inlineAttr_x3f_897_ = lean_ctor_get(v_decl_887_, 2);
v_isSharedCheck_946_ = !lean_is_exclusive(v_decl_887_);
if (v_isSharedCheck_946_ == 0)
{
v___x_899_ = v_decl_887_;
v_isShared_900_ = v_isSharedCheck_946_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_inlineAttr_x3f_897_);
lean_inc(v_value_895_);
lean_inc(v_toSignature_894_);
lean_dec(v_decl_887_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_946_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v_name_901_; lean_object* v_levelParams_902_; lean_object* v_type_903_; lean_object* v_params_904_; uint8_t v_safe_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_945_; 
v_name_901_ = lean_ctor_get(v_toSignature_894_, 0);
v_levelParams_902_ = lean_ctor_get(v_toSignature_894_, 1);
v_type_903_ = lean_ctor_get(v_toSignature_894_, 2);
v_params_904_ = lean_ctor_get(v_toSignature_894_, 3);
v_safe_905_ = lean_ctor_get_uint8(v_toSignature_894_, sizeof(void*)*4);
v_isSharedCheck_945_ = !lean_is_exclusive(v_toSignature_894_);
if (v_isSharedCheck_945_ == 0)
{
v___x_907_ = v_toSignature_894_;
v_isShared_908_ = v_isSharedCheck_945_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_params_904_);
lean_inc(v_type_903_);
lean_inc(v_levelParams_902_);
lean_inc(v_name_901_);
lean_dec(v_toSignature_894_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_945_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_909_; lean_object* v___f_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_909_ = lean_box(v_pu_886_);
lean_inc_ref(v_r_888_);
v___f_910_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_applyRenaming___lam__0___boxed), 8, 2);
lean_closure_set(v___f_910_, 0, v___x_909_);
lean_closure_set(v___f_910_, 1, v_r_888_);
v___x_911_ = lean_unsigned_to_nat(0u);
v___x_912_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__1___redArg(v_pu_886_, v_r_888_, v___x_911_, v_params_904_, v_a_890_);
lean_dec_ref_known(v_r_888_, 5);
if (lean_obj_tag(v___x_912_) == 0)
{
lean_object* v_a_913_; lean_object* v___x_914_; 
v_a_913_ = lean_ctor_get(v___x_912_, 0);
lean_inc(v_a_913_);
lean_dec_ref_known(v___x_912_, 1);
v___x_914_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_applyRenaming_spec__0___redArg(v___f_910_, v_value_895_, v_a_889_, v_a_890_, v_a_891_, v_a_892_);
if (lean_obj_tag(v___x_914_) == 0)
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_928_; 
v_a_915_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_928_ == 0)
{
v___x_917_ = v___x_914_;
v_isShared_918_ = v_isSharedCheck_928_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v___x_914_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_928_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_920_; 
if (v_isShared_908_ == 0)
{
lean_ctor_set(v___x_907_, 3, v_a_913_);
v___x_920_ = v___x_907_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_name_901_);
lean_ctor_set(v_reuseFailAlloc_927_, 1, v_levelParams_902_);
lean_ctor_set(v_reuseFailAlloc_927_, 2, v_type_903_);
lean_ctor_set(v_reuseFailAlloc_927_, 3, v_a_913_);
lean_ctor_set_uint8(v_reuseFailAlloc_927_, sizeof(void*)*4, v_safe_905_);
v___x_920_ = v_reuseFailAlloc_927_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
lean_object* v___x_922_; 
if (v_isShared_900_ == 0)
{
lean_ctor_set(v___x_899_, 1, v_a_915_);
lean_ctor_set(v___x_899_, 0, v___x_920_);
v___x_922_ = v___x_899_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v___x_920_);
lean_ctor_set(v_reuseFailAlloc_926_, 1, v_a_915_);
lean_ctor_set(v_reuseFailAlloc_926_, 2, v_inlineAttr_x3f_897_);
lean_ctor_set_uint8(v_reuseFailAlloc_926_, sizeof(void*)*3, v_recursive_896_);
v___x_922_ = v_reuseFailAlloc_926_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
lean_object* v___x_924_; 
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 0, v___x_922_);
v___x_924_ = v___x_917_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v___x_922_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
}
}
}
}
}
else
{
lean_object* v_a_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_936_; 
lean_dec(v_a_913_);
lean_del_object(v___x_907_);
lean_dec_ref(v_type_903_);
lean_dec(v_levelParams_902_);
lean_dec(v_name_901_);
lean_del_object(v___x_899_);
lean_dec(v_inlineAttr_x3f_897_);
v_a_929_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_936_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_936_ == 0)
{
v___x_931_ = v___x_914_;
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_a_929_);
lean_dec(v___x_914_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___x_934_; 
if (v_isShared_932_ == 0)
{
v___x_934_ = v___x_931_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_a_929_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
}
}
else
{
lean_object* v_a_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_944_; 
lean_dec_ref(v___f_910_);
lean_del_object(v___x_907_);
lean_dec_ref(v_type_903_);
lean_dec(v_levelParams_902_);
lean_dec(v_name_901_);
lean_del_object(v___x_899_);
lean_dec(v_inlineAttr_x3f_897_);
lean_dec_ref(v_value_895_);
v_a_937_ = lean_ctor_get(v___x_912_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_912_);
if (v_isSharedCheck_944_ == 0)
{
v___x_939_ = v___x_912_;
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_a_937_);
lean_dec(v___x_912_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_942_; 
if (v_isShared_940_ == 0)
{
v___x_942_ = v___x_939_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_a_937_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
}
}
}
}
else
{
lean_object* v___x_947_; 
v___x_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_947_, 0, v_decl_887_);
return v___x_947_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Decl_applyRenaming_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_886_ = stack[0].m_num;
lean_object* v_decl_887_ = stack[1].m_obj;
lean_object* v_r_888_ = stack[2].m_obj;
lean_object* v_a_889_ = stack[3].m_obj;
lean_object* v_a_890_ = stack[4].m_obj;
lean_object* v_a_891_ = stack[5].m_obj;
lean_object* v_a_892_ = stack[6].m_obj;
lean_object* v_res_948_;
v_res_948_ = l_Lean_Compiler_LCNF_Decl_applyRenaming(v_pu_886_, v_decl_887_, v_r_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_);
stack->m_obj
 = v_res_948_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_applyRenaming___boxed(lean_object* v_pu_949_, lean_object* v_decl_950_, lean_object* v_r_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_){
_start:
{
uint8_t v_pu_boxed_957_; lean_object* v_res_958_; 
v_pu_boxed_957_ = lean_unbox(v_pu_949_);
v_res_958_ = l_Lean_Compiler_LCNF_Decl_applyRenaming(v_pu_boxed_957_, v_decl_950_, v_r_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_);
lean_dec(v_a_955_);
lean_dec_ref(v_a_954_);
lean_dec(v_a_953_);
lean_dec_ref(v_a_952_);
return v_res_958_;
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

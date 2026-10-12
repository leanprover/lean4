// Lean compiler output
// Module: Lean.Meta.CollectFVars
// Imports: public import Lean.Util.CollectFVars public import Lean.Meta.Basic
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
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_collectFVars(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_erase(lean_object*, lean_object*);
lean_object* l_Lean_LocalInstances_erase(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Expr_collectFVars_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Expr_collectFVars_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Expr_collectFVars_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Expr_collectFVars_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_collectFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_collectFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_collectFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_collectFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_getNext_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_getNext_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_getNext_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_getNext_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectFVars_State_addDependencies(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectFVars_State_addDependencies___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_removeUnused_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_removeUnused_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_removeUnused_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_removeUnused_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_removeUnused___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_removeUnused___closed__0 = (const lean_object*)&l_Lean_Meta_removeUnused___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_removeUnused(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_removeUnused___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_removeUnused_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_removeUnused_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at___00Lean_Expr_collectFVars_spec__0___redArg(lean_object* v_e_1_, lean_object* v___y_2_){
_start:
{
uint8_t v___x_4_; 
v___x_4_ = l_Lean_Expr_hasMVar(v_e_1_);
if (v___x_4_ == 0)
{
lean_object* v___x_5_; 
v___x_5_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5_, 0, v_e_1_);
return v___x_5_;
}
else
{
lean_object* v___x_6_; lean_object* v_mctx_7_; lean_object* v___x_8_; lean_object* v_fst_9_; lean_object* v_snd_10_; lean_object* v___x_11_; lean_object* v_cache_12_; lean_object* v_zetaDeltaFVarIds_13_; lean_object* v_postponed_14_; lean_object* v_diag_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_24_; 
v___x_6_ = lean_st_ref_get(v___y_2_);
v_mctx_7_ = lean_ctor_get(v___x_6_, 0);
lean_inc_ref(v_mctx_7_);
lean_dec(v___x_6_);
v___x_8_ = l_Lean_instantiateMVarsCore(v_mctx_7_, v_e_1_);
v_fst_9_ = lean_ctor_get(v___x_8_, 0);
lean_inc(v_fst_9_);
v_snd_10_ = lean_ctor_get(v___x_8_, 1);
lean_inc(v_snd_10_);
lean_dec_ref(v___x_8_);
v___x_11_ = lean_st_ref_take(v___y_2_);
v_cache_12_ = lean_ctor_get(v___x_11_, 1);
v_zetaDeltaFVarIds_13_ = lean_ctor_get(v___x_11_, 2);
v_postponed_14_ = lean_ctor_get(v___x_11_, 3);
v_diag_15_ = lean_ctor_get(v___x_11_, 4);
v_isSharedCheck_24_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_24_ == 0)
{
lean_object* v_unused_25_; 
v_unused_25_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_25_);
v___x_17_ = v___x_11_;
v_isShared_18_ = v_isSharedCheck_24_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_diag_15_);
lean_inc(v_postponed_14_);
lean_inc(v_zetaDeltaFVarIds_13_);
lean_inc(v_cache_12_);
lean_dec(v___x_11_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_24_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
lean_object* v___x_20_; 
if (v_isShared_18_ == 0)
{
lean_ctor_set(v___x_17_, 0, v_snd_10_);
v___x_20_ = v___x_17_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_23_; 
v_reuseFailAlloc_23_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_23_, 0, v_snd_10_);
lean_ctor_set(v_reuseFailAlloc_23_, 1, v_cache_12_);
lean_ctor_set(v_reuseFailAlloc_23_, 2, v_zetaDeltaFVarIds_13_);
lean_ctor_set(v_reuseFailAlloc_23_, 3, v_postponed_14_);
lean_ctor_set(v_reuseFailAlloc_23_, 4, v_diag_15_);
v___x_20_ = v_reuseFailAlloc_23_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_21_ = lean_st_ref_put(v___y_2_, v___x_20_);
v___x_22_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_22_, 0, v_fst_9_);
return v___x_22_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Expr_collectFVars_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1_ = stack[0].m_obj;
lean_object* v___y_2_ = stack[1].m_obj;
lean_object* v_res_26_;
v_res_26_ = l_Lean_instantiateMVars___at___00Lean_Expr_collectFVars_spec__0___redArg(v_e_1_, v___y_2_);
stack->m_obj
 = v_res_26_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Expr_collectFVars_spec__0___redArg___boxed(lean_object* v_e_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_instantiateMVars___at___00Lean_Expr_collectFVars_spec__0___redArg(v_e_27_, v___y_28_);
lean_dec(v___y_28_);
return v_res_30_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Expr_collectFVars_spec__0(lean_object* v_e_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_Lean_instantiateMVars___at___00Lean_Expr_collectFVars_spec__0___redArg(v_e_31_, v___y_34_);
return v___x_38_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Expr_collectFVars_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_31_ = stack[0].m_obj;
lean_object* v___y_32_ = stack[1].m_obj;
lean_object* v___y_33_ = stack[2].m_obj;
lean_object* v___y_34_ = stack[3].m_obj;
lean_object* v___y_35_ = stack[4].m_obj;
lean_object* v___y_36_ = stack[5].m_obj;
lean_object* v_res_39_;
v_res_39_ = l_Lean_instantiateMVars___at___00Lean_Expr_collectFVars_spec__0(v_e_31_, v___y_32_, v___y_33_, v___y_34_, v___y_35_, v___y_36_);
stack->m_obj
 = v_res_39_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Expr_collectFVars_spec__0___boxed(lean_object* v_e_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_Lean_instantiateMVars___at___00Lean_Expr_collectFVars_spec__0(v_e_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_);
lean_dec(v___y_45_);
lean_dec_ref(v___y_44_);
lean_dec(v___y_43_);
lean_dec_ref(v___y_42_);
lean_dec(v___y_41_);
return v_res_47_;
}
}
lean_object* l_Lean_Expr_collectFVars(lean_object* v_e_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_){
_start:
{
lean_object* v___x_55_; lean_object* v_a_56_; lean_object* v___x_58_; uint8_t v_isShared_59_; uint8_t v_isSharedCheck_67_; 
v___x_55_ = l_Lean_instantiateMVars___at___00Lean_Expr_collectFVars_spec__0___redArg(v_e_48_, v_a_51_);
v_a_56_ = lean_ctor_get(v___x_55_, 0);
v_isSharedCheck_67_ = !lean_is_exclusive(v___x_55_);
if (v_isSharedCheck_67_ == 0)
{
v___x_58_ = v___x_55_;
v_isShared_59_ = v_isSharedCheck_67_;
goto v_resetjp_57_;
}
else
{
lean_inc(v_a_56_);
lean_dec(v___x_55_);
v___x_58_ = lean_box(0);
v_isShared_59_ = v_isSharedCheck_67_;
goto v_resetjp_57_;
}
v_resetjp_57_:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_65_; 
v___x_60_ = lean_st_ref_take(v_a_49_);
v___x_61_ = lean_box(0);
v___x_62_ = l_Lean_collectFVars(v___x_60_, v_a_56_);
v___x_63_ = lean_st_ref_put(v_a_49_, v___x_62_);
if (v_isShared_59_ == 0)
{
lean_ctor_set(v___x_58_, 0, v___x_61_);
v___x_65_ = v___x_58_;
goto v_reusejp_64_;
}
else
{
lean_object* v_reuseFailAlloc_66_; 
v_reuseFailAlloc_66_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_66_, 0, v___x_61_);
v___x_65_ = v_reuseFailAlloc_66_;
goto v_reusejp_64_;
}
v_reusejp_64_:
{
return v___x_65_;
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_collectFVars_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_48_ = stack[0].m_obj;
lean_object* v_a_49_ = stack[1].m_obj;
lean_object* v_a_50_ = stack[2].m_obj;
lean_object* v_a_51_ = stack[3].m_obj;
lean_object* v_a_52_ = stack[4].m_obj;
lean_object* v_a_53_ = stack[5].m_obj;
lean_object* v_res_68_;
v_res_68_ = l_Lean_Expr_collectFVars(v_e_48_, v_a_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_);
stack->m_obj
 = v_res_68_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_collectFVars___boxed(lean_object* v_e_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_Lean_Expr_collectFVars(v_e_69_, v_a_70_, v_a_71_, v_a_72_, v_a_73_, v_a_74_);
lean_dec(v_a_74_);
lean_dec_ref(v_a_73_);
lean_dec(v_a_72_);
lean_dec_ref(v_a_71_);
lean_dec(v_a_70_);
return v_res_76_;
}
}
lean_object* l_Lean_LocalDecl_collectFVars(lean_object* v_localDecl_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_){
_start:
{
if (lean_obj_tag(v_localDecl_77_) == 0)
{
lean_object* v_type_84_; lean_object* v___x_85_; 
v_type_84_ = lean_ctor_get(v_localDecl_77_, 3);
lean_inc_ref(v_type_84_);
lean_dec_ref_known(v_localDecl_77_, 4);
v___x_85_ = l_Lean_Expr_collectFVars(v_type_84_, v_a_78_, v_a_79_, v_a_80_, v_a_81_, v_a_82_);
return v___x_85_;
}
else
{
lean_object* v_type_86_; lean_object* v_value_87_; lean_object* v___x_88_; 
v_type_86_ = lean_ctor_get(v_localDecl_77_, 3);
lean_inc_ref(v_type_86_);
v_value_87_ = lean_ctor_get(v_localDecl_77_, 4);
lean_inc_ref(v_value_87_);
lean_dec_ref_known(v_localDecl_77_, 5);
v___x_88_ = l_Lean_Expr_collectFVars(v_type_86_, v_a_78_, v_a_79_, v_a_80_, v_a_81_, v_a_82_);
if (lean_obj_tag(v___x_88_) == 0)
{
lean_object* v___x_89_; 
lean_dec_ref_known(v___x_88_, 1);
v___x_89_ = l_Lean_Expr_collectFVars(v_value_87_, v_a_78_, v_a_79_, v_a_80_, v_a_81_, v_a_82_);
return v___x_89_;
}
else
{
lean_dec_ref(v_value_87_);
return v___x_88_;
}
}
}
}
LEAN_EXPORT void l_Lean_LocalDecl_collectFVars_0interp(lean_interpreter_value* stack)
{
lean_object* v_localDecl_77_ = stack[0].m_obj;
lean_object* v_a_78_ = stack[1].m_obj;
lean_object* v_a_79_ = stack[2].m_obj;
lean_object* v_a_80_ = stack[3].m_obj;
lean_object* v_a_81_ = stack[4].m_obj;
lean_object* v_a_82_ = stack[5].m_obj;
lean_object* v_res_90_;
v_res_90_ = l_Lean_LocalDecl_collectFVars(v_localDecl_77_, v_a_78_, v_a_79_, v_a_80_, v_a_81_, v_a_82_);
stack->m_obj
 = v_res_90_;
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_collectFVars___boxed(lean_object* v_localDecl_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Lean_LocalDecl_collectFVars(v_localDecl_91_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_);
lean_dec(v_a_96_);
lean_dec_ref(v_a_95_);
lean_dec(v_a_94_);
lean_dec_ref(v_a_93_);
lean_dec(v_a_92_);
return v_res_98_;
}
}
lean_object* l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_getNext_x3f___redArg(lean_object* v_a_99_, lean_object* v_a_100_){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v_fvarIds_104_; lean_object* v___x_105_; uint8_t v___x_106_; 
v___x_102_ = lean_st_ref_get(v_a_100_);
v___x_103_ = lean_st_ref_get(v_a_99_);
v_fvarIds_104_ = lean_ctor_get(v___x_102_, 2);
lean_inc_ref(v_fvarIds_104_);
lean_dec(v___x_102_);
v___x_105_ = lean_array_get_size(v_fvarIds_104_);
v___x_106_ = lean_nat_dec_lt(v___x_103_, v___x_105_);
if (v___x_106_ == 0)
{
lean_object* v___x_107_; lean_object* v___x_108_; 
lean_dec_ref(v_fvarIds_104_);
lean_dec(v___x_103_);
v___x_107_ = lean_box(0);
v___x_108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_108_, 0, v___x_107_);
return v___x_108_;
}
else
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_109_ = lean_array_fget(v_fvarIds_104_, v___x_103_);
lean_dec(v___x_103_);
lean_dec_ref(v_fvarIds_104_);
v___x_110_ = lean_st_ref_take(v_a_99_);
v___x_111_ = lean_unsigned_to_nat(1u);
v___x_112_ = lean_nat_add(v___x_110_, v___x_111_);
lean_dec(v___x_110_);
v___x_113_ = lean_st_ref_put(v_a_99_, v___x_112_);
v___x_114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_114_, 0, v___x_109_);
v___x_115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_115_, 0, v___x_114_);
return v___x_115_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_getNext_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_99_ = stack[0].m_obj;
lean_object* v_a_100_ = stack[1].m_obj;
lean_object* v_res_116_;
v_res_116_ = l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_getNext_x3f___redArg(v_a_99_, v_a_100_);
stack->m_obj
 = v_res_116_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_getNext_x3f___redArg___boxed(lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_getNext_x3f___redArg(v_a_117_, v_a_118_);
lean_dec(v_a_118_);
lean_dec(v_a_117_);
return v_res_120_;
}
}
lean_object* l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_getNext_x3f(lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_getNext_x3f___redArg(v_a_121_, v_a_122_);
return v___x_128_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_getNext_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_121_ = stack[0].m_obj;
lean_object* v_a_122_ = stack[1].m_obj;
lean_object* v_a_123_ = stack[2].m_obj;
lean_object* v_a_124_ = stack[3].m_obj;
lean_object* v_a_125_ = stack[4].m_obj;
lean_object* v_a_126_ = stack[5].m_obj;
lean_object* v_res_129_;
v_res_129_ = l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_getNext_x3f(v_a_121_, v_a_122_, v_a_123_, v_a_124_, v_a_125_, v_a_126_);
stack->m_obj
 = v_res_129_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_getNext_x3f___boxed(lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_getNext_x3f(v_a_130_, v_a_131_, v_a_132_, v_a_133_, v_a_134_, v_a_135_);
lean_dec(v_a_135_);
lean_dec_ref(v_a_134_);
lean_dec(v_a_133_);
lean_dec_ref(v_a_132_);
lean_dec(v_a_131_);
lean_dec(v_a_130_);
return v_res_137_;
}
}
lean_object* l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_go(lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_){
_start:
{
lean_object* v___x_145_; 
v___x_145_ = l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_getNext_x3f___redArg(v_a_138_, v_a_139_);
if (lean_obj_tag(v___x_145_) == 0)
{
lean_object* v_a_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_164_; 
v_a_146_ = lean_ctor_get(v___x_145_, 0);
v_isSharedCheck_164_ = !lean_is_exclusive(v___x_145_);
if (v_isSharedCheck_164_ == 0)
{
v___x_148_ = v___x_145_;
v_isShared_149_ = v_isSharedCheck_164_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_a_146_);
lean_dec(v___x_145_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_164_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
if (lean_obj_tag(v_a_146_) == 1)
{
lean_object* v_val_150_; lean_object* v_lctx_151_; lean_object* v___x_152_; 
v_val_150_ = lean_ctor_get(v_a_146_, 0);
lean_inc(v_val_150_);
lean_dec_ref_known(v_a_146_, 1);
v_lctx_151_ = lean_ctor_get(v_a_140_, 2);
lean_inc_ref(v_lctx_151_);
v___x_152_ = lean_local_ctx_find(v_lctx_151_, v_val_150_);
if (lean_obj_tag(v___x_152_) == 1)
{
lean_object* v_val_153_; lean_object* v___x_154_; 
lean_del_object(v___x_148_);
v_val_153_ = lean_ctor_get(v___x_152_, 0);
lean_inc(v_val_153_);
lean_dec_ref_known(v___x_152_, 1);
v___x_154_ = l_Lean_LocalDecl_collectFVars(v_val_153_, v_a_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_);
if (lean_obj_tag(v___x_154_) == 0)
{
lean_dec_ref_known(v___x_154_, 1);
goto _start;
}
else
{
return v___x_154_;
}
}
else
{
lean_object* v___x_156_; lean_object* v___x_158_; 
lean_dec(v___x_152_);
v___x_156_ = lean_box(0);
if (v_isShared_149_ == 0)
{
lean_ctor_set(v___x_148_, 0, v___x_156_);
v___x_158_ = v___x_148_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v___x_156_);
v___x_158_ = v_reuseFailAlloc_159_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
return v___x_158_;
}
}
}
else
{
lean_object* v___x_160_; lean_object* v___x_162_; 
lean_dec(v_a_146_);
v___x_160_ = lean_box(0);
if (v_isShared_149_ == 0)
{
lean_ctor_set(v___x_148_, 0, v___x_160_);
v___x_162_ = v___x_148_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v___x_160_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
}
}
else
{
lean_object* v_a_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_172_; 
v_a_165_ = lean_ctor_get(v___x_145_, 0);
v_isSharedCheck_172_ = !lean_is_exclusive(v___x_145_);
if (v_isSharedCheck_172_ == 0)
{
v___x_167_ = v___x_145_;
v_isShared_168_ = v_isSharedCheck_172_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_a_165_);
lean_dec(v___x_145_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_172_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
lean_object* v___x_170_; 
if (v_isShared_168_ == 0)
{
v___x_170_ = v___x_167_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v_a_165_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_138_ = stack[0].m_obj;
lean_object* v_a_139_ = stack[1].m_obj;
lean_object* v_a_140_ = stack[2].m_obj;
lean_object* v_a_141_ = stack[3].m_obj;
lean_object* v_a_142_ = stack[4].m_obj;
lean_object* v_a_143_ = stack[5].m_obj;
lean_object* v_res_173_;
v_res_173_ = l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_go(v_a_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_);
stack->m_obj
 = v_res_173_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_go___boxed(lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_go(v_a_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_);
lean_dec(v_a_179_);
lean_dec_ref(v_a_178_);
lean_dec(v_a_177_);
lean_dec_ref(v_a_176_);
lean_dec(v_a_175_);
lean_dec(v_a_174_);
return v_res_181_;
}
}
lean_object* l_Lean_CollectFVars_State_addDependencies(lean_object* v_s_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_188_ = lean_unsigned_to_nat(0u);
v___x_189_ = lean_st_mk_ref(v_s_182_);
v___x_190_ = lean_st_mk_ref(v___x_188_);
v___x_191_ = l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_go(v___x_190_, v___x_189_, v_a_183_, v_a_184_, v_a_185_, v_a_186_);
if (lean_obj_tag(v___x_191_) == 0)
{
lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_200_; 
v_isSharedCheck_200_ = !lean_is_exclusive(v___x_191_);
if (v_isSharedCheck_200_ == 0)
{
lean_object* v_unused_201_; 
v_unused_201_ = lean_ctor_get(v___x_191_, 0);
lean_dec(v_unused_201_);
v___x_193_ = v___x_191_;
v_isShared_194_ = v_isSharedCheck_200_;
goto v_resetjp_192_;
}
else
{
lean_dec(v___x_191_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_200_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_198_; 
v___x_195_ = lean_st_ref_get(v___x_190_);
lean_dec(v___x_190_);
lean_dec(v___x_195_);
v___x_196_ = lean_st_ref_get(v___x_189_);
lean_dec(v___x_189_);
if (v_isShared_194_ == 0)
{
lean_ctor_set(v___x_193_, 0, v___x_196_);
v___x_198_ = v___x_193_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v___x_196_);
v___x_198_ = v_reuseFailAlloc_199_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
return v___x_198_;
}
}
}
else
{
lean_object* v_a_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_209_; 
lean_dec(v___x_190_);
lean_dec(v___x_189_);
v_a_202_ = lean_ctor_get(v___x_191_, 0);
v_isSharedCheck_209_ = !lean_is_exclusive(v___x_191_);
if (v_isSharedCheck_209_ == 0)
{
v___x_204_ = v___x_191_;
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_a_202_);
lean_dec(v___x_191_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_207_; 
if (v_isShared_205_ == 0)
{
v___x_207_ = v___x_204_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v_a_202_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
return v___x_207_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_CollectFVars_State_addDependencies_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_182_ = stack[0].m_obj;
lean_object* v_a_183_ = stack[1].m_obj;
lean_object* v_a_184_ = stack[2].m_obj;
lean_object* v_a_185_ = stack[3].m_obj;
lean_object* v_a_186_ = stack[4].m_obj;
lean_object* v_res_210_;
v_res_210_ = l_Lean_CollectFVars_State_addDependencies(v_s_182_, v_a_183_, v_a_184_, v_a_185_, v_a_186_);
stack->m_obj
 = v_res_210_;
}
LEAN_EXPORT lean_object* l_Lean_CollectFVars_State_addDependencies___boxed(lean_object* v_s_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_Lean_CollectFVars_State_addDependencies(v_s_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_);
lean_dec(v_a_215_);
lean_dec_ref(v_a_214_);
lean_dec(v_a_213_);
lean_dec_ref(v_a_212_);
return v_res_217_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_removeUnused_spec__0___redArg(lean_object* v_k_218_, lean_object* v_t_219_){
_start:
{
if (lean_obj_tag(v_t_219_) == 0)
{
lean_object* v_k_220_; lean_object* v_l_221_; lean_object* v_r_222_; uint8_t v___x_223_; 
v_k_220_ = lean_ctor_get(v_t_219_, 1);
v_l_221_ = lean_ctor_get(v_t_219_, 3);
v_r_222_ = lean_ctor_get(v_t_219_, 4);
v___x_223_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_218_, v_k_220_);
switch(v___x_223_)
{
case 0:
{
v_t_219_ = v_l_221_;
goto _start;
}
case 1:
{
uint8_t v___x_225_; 
v___x_225_ = 1;
return v___x_225_;
}
default: 
{
v_t_219_ = v_r_222_;
goto _start;
}
}
}
else
{
uint8_t v___x_227_; 
v___x_227_ = 0;
return v___x_227_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_removeUnused_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_218_ = stack[0].m_obj;
lean_object* v_t_219_ = stack[1].m_obj;
uint8_t v_res_228_;
v_res_228_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_removeUnused_spec__0___redArg(v_k_218_, v_t_219_);
stack->m_num = v_res_228_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_removeUnused_spec__0___redArg___boxed(lean_object* v_k_229_, lean_object* v_t_230_){
_start:
{
uint8_t v_res_231_; lean_object* v_r_232_; 
v_res_231_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_removeUnused_spec__0___redArg(v_k_229_, v_t_230_);
lean_dec(v_t_230_);
lean_dec(v_k_229_);
v_r_232_ = lean_box(v_res_231_);
return v_r_232_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_removeUnused_spec__1(lean_object* v_as_233_, size_t v_i_234_, size_t v_stop_235_, lean_object* v_b_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_){
_start:
{
uint8_t v___x_242_; 
v___x_242_ = lean_usize_dec_eq(v_i_234_, v_stop_235_);
if (v___x_242_ == 0)
{
lean_object* v_snd_243_; lean_object* v_snd_244_; lean_object* v_snd_245_; lean_object* v_fst_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_310_; 
v_snd_243_ = lean_ctor_get(v_b_236_, 1);
lean_inc(v_snd_243_);
v_snd_244_ = lean_ctor_get(v_snd_243_, 1);
lean_inc(v_snd_244_);
v_snd_245_ = lean_ctor_get(v_snd_244_, 1);
v_fst_246_ = lean_ctor_get(v_b_236_, 0);
v_isSharedCheck_310_ = !lean_is_exclusive(v_b_236_);
if (v_isSharedCheck_310_ == 0)
{
lean_object* v_unused_311_; 
v_unused_311_ = lean_ctor_get(v_b_236_, 1);
lean_dec(v_unused_311_);
v___x_248_ = v_b_236_;
v_isShared_249_ = v_isSharedCheck_310_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_fst_246_);
lean_dec(v_b_236_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_310_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v_fst_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_308_; 
v_fst_250_ = lean_ctor_get(v_snd_243_, 0);
v_isSharedCheck_308_ = !lean_is_exclusive(v_snd_243_);
if (v_isSharedCheck_308_ == 0)
{
lean_object* v_unused_309_; 
v_unused_309_ = lean_ctor_get(v_snd_243_, 1);
lean_dec(v_unused_309_);
v___x_252_ = v_snd_243_;
v_isShared_253_ = v_isSharedCheck_308_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_fst_250_);
lean_dec(v_snd_243_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_308_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v_fst_254_; lean_object* v_fvarSet_255_; size_t v___x_256_; size_t v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; uint8_t v___x_260_; 
v_fst_254_ = lean_ctor_get(v_snd_244_, 0);
v_fvarSet_255_ = lean_ctor_get(v_snd_245_, 1);
v___x_256_ = ((size_t)1ULL);
v___x_257_ = lean_usize_sub(v_i_234_, v___x_256_);
v___x_258_ = lean_array_uget_borrowed(v_as_233_, v___x_257_);
v___x_259_ = l_Lean_Expr_fvarId_x21(v___x_258_);
v___x_260_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_removeUnused_spec__0___redArg(v___x_259_, v_fvarSet_255_);
if (v___x_260_ == 0)
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_264_; 
v___x_261_ = l_Lean_LocalContext_erase(v_fst_246_, v___x_259_);
v___x_262_ = l_Lean_LocalInstances_erase(v_fst_250_, v___x_259_);
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 0, v___x_262_);
v___x_264_ = v___x_252_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v___x_262_);
lean_ctor_set(v_reuseFailAlloc_269_, 1, v_snd_244_);
v___x_264_ = v_reuseFailAlloc_269_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
lean_object* v___x_266_; 
if (v_isShared_249_ == 0)
{
lean_ctor_set(v___x_248_, 1, v___x_264_);
lean_ctor_set(v___x_248_, 0, v___x_261_);
v___x_266_ = v___x_248_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v___x_261_);
lean_ctor_set(v_reuseFailAlloc_268_, 1, v___x_264_);
v___x_266_ = v_reuseFailAlloc_268_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
v_i_234_ = v___x_257_;
v_b_236_ = v___x_266_;
goto _start;
}
}
}
else
{
lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_305_; 
lean_inc(v_fst_254_);
lean_inc(v_snd_245_);
lean_dec(v___x_259_);
v_isSharedCheck_305_ = !lean_is_exclusive(v_snd_244_);
if (v_isSharedCheck_305_ == 0)
{
lean_object* v_unused_306_; lean_object* v_unused_307_; 
v_unused_306_ = lean_ctor_get(v_snd_244_, 1);
lean_dec(v_unused_306_);
v_unused_307_ = lean_ctor_get(v_snd_244_, 0);
lean_dec(v_unused_307_);
v___x_271_ = v_snd_244_;
v_isShared_272_ = v_isSharedCheck_305_;
goto v_resetjp_270_;
}
else
{
lean_dec(v_snd_244_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_305_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_273_; 
lean_inc(v___y_240_);
lean_inc_ref(v___y_239_);
lean_inc(v___y_238_);
lean_inc_ref(v___y_237_);
lean_inc(v___x_258_);
v___x_273_ = lean_infer_type(v___x_258_, v___y_237_, v___y_238_, v___y_239_, v___y_240_);
if (lean_obj_tag(v___x_273_) == 0)
{
lean_object* v_a_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v_a_274_ = lean_ctor_get(v___x_273_, 0);
lean_inc(v_a_274_);
lean_dec_ref_known(v___x_273_, 1);
v___x_275_ = lean_st_mk_ref(v_snd_245_);
v___x_276_ = l_Lean_Expr_collectFVars(v_a_274_, v___x_275_, v___y_237_, v___y_238_, v___y_239_, v___y_240_);
if (lean_obj_tag(v___x_276_) == 0)
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_280_; 
lean_dec_ref_known(v___x_276_, 1);
v___x_277_ = lean_st_ref_get(v___x_275_);
lean_dec(v___x_275_);
lean_inc(v___x_258_);
v___x_278_ = lean_array_push(v_fst_254_, v___x_258_);
if (v_isShared_272_ == 0)
{
lean_ctor_set(v___x_271_, 1, v___x_277_);
lean_ctor_set(v___x_271_, 0, v___x_278_);
v___x_280_ = v___x_271_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v___x_278_);
lean_ctor_set(v_reuseFailAlloc_288_, 1, v___x_277_);
v___x_280_ = v_reuseFailAlloc_288_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
lean_object* v___x_282_; 
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 1, v___x_280_);
v___x_282_ = v___x_252_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v_fst_250_);
lean_ctor_set(v_reuseFailAlloc_287_, 1, v___x_280_);
v___x_282_ = v_reuseFailAlloc_287_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
lean_object* v___x_284_; 
if (v_isShared_249_ == 0)
{
lean_ctor_set(v___x_248_, 1, v___x_282_);
v___x_284_ = v___x_248_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v_fst_246_);
lean_ctor_set(v_reuseFailAlloc_286_, 1, v___x_282_);
v___x_284_ = v_reuseFailAlloc_286_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
v_i_234_ = v___x_257_;
v_b_236_ = v___x_284_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_296_; 
lean_dec(v___x_275_);
lean_del_object(v___x_271_);
lean_dec(v_fst_254_);
lean_del_object(v___x_252_);
lean_dec(v_fst_250_);
lean_del_object(v___x_248_);
lean_dec(v_fst_246_);
v_a_289_ = lean_ctor_get(v___x_276_, 0);
v_isSharedCheck_296_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_296_ == 0)
{
v___x_291_ = v___x_276_;
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_a_289_);
lean_dec(v___x_276_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_294_; 
if (v_isShared_292_ == 0)
{
v___x_294_ = v___x_291_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_a_289_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
}
}
else
{
lean_object* v_a_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_304_; 
lean_del_object(v___x_271_);
lean_dec(v_fst_254_);
lean_del_object(v___x_252_);
lean_dec(v_fst_250_);
lean_del_object(v___x_248_);
lean_dec(v_fst_246_);
lean_dec(v_snd_245_);
v_a_297_ = lean_ctor_get(v___x_273_, 0);
v_isSharedCheck_304_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_304_ == 0)
{
v___x_299_ = v___x_273_;
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_a_297_);
lean_dec(v___x_273_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_302_; 
if (v_isShared_300_ == 0)
{
v___x_302_ = v___x_299_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_a_297_);
v___x_302_ = v_reuseFailAlloc_303_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
return v___x_302_;
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
lean_object* v___x_312_; 
v___x_312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_312_, 0, v_b_236_);
return v___x_312_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_removeUnused_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_233_ = stack[0].m_obj;
size_t v_i_234_ = stack[1].m_num;
size_t v_stop_235_ = stack[2].m_num;
lean_object* v_b_236_ = stack[3].m_obj;
lean_object* v___y_237_ = stack[4].m_obj;
lean_object* v___y_238_ = stack[5].m_obj;
lean_object* v___y_239_ = stack[6].m_obj;
lean_object* v___y_240_ = stack[7].m_obj;
lean_object* v_res_313_;
v_res_313_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_removeUnused_spec__1(v_as_233_, v_i_234_, v_stop_235_, v_b_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_);
stack->m_obj
 = v_res_313_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_removeUnused_spec__1___boxed(lean_object* v_as_314_, lean_object* v_i_315_, lean_object* v_stop_316_, lean_object* v_b_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_){
_start:
{
size_t v_i_boxed_323_; size_t v_stop_boxed_324_; lean_object* v_res_325_; 
v_i_boxed_323_ = lean_unbox_usize(v_i_315_);
lean_dec(v_i_315_);
v_stop_boxed_324_ = lean_unbox_usize(v_stop_316_);
lean_dec(v_stop_316_);
v_res_325_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_removeUnused_spec__1(v_as_314_, v_i_boxed_323_, v_stop_boxed_324_, v_b_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_);
lean_dec(v___y_321_);
lean_dec_ref(v___y_320_);
lean_dec(v___y_319_);
lean_dec_ref(v___y_318_);
lean_dec_ref(v_as_314_);
return v_res_325_;
}
}
lean_object* l_Lean_Meta_removeUnused(lean_object* v_vars_328_, lean_object* v_used_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_){
_start:
{
lean_object* v_fst_336_; lean_object* v_fst_337_; lean_object* v_fst_338_; lean_object* v_lctx_343_; lean_object* v_localInstances_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; uint8_t v___x_348_; 
v_lctx_343_ = lean_ctor_get(v_a_330_, 2);
v_localInstances_344_ = lean_ctor_get(v_a_330_, 3);
v___x_345_ = lean_unsigned_to_nat(0u);
v___x_346_ = ((lean_object*)(l_Lean_Meta_removeUnused___closed__0));
v___x_347_ = lean_array_get_size(v_vars_328_);
v___x_348_ = lean_nat_dec_lt(v___x_345_, v___x_347_);
if (v___x_348_ == 0)
{
lean_dec_ref(v_used_329_);
lean_inc_ref(v_localInstances_344_);
lean_inc_ref(v_lctx_343_);
v_fst_336_ = v_lctx_343_;
v_fst_337_ = v_localInstances_344_;
v_fst_338_ = v___x_346_;
goto v___jp_335_;
}
else
{
lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; size_t v___x_352_; size_t v___x_353_; lean_object* v___x_354_; 
v___x_349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_349_, 0, v___x_346_);
lean_ctor_set(v___x_349_, 1, v_used_329_);
lean_inc_ref(v_localInstances_344_);
v___x_350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_350_, 0, v_localInstances_344_);
lean_ctor_set(v___x_350_, 1, v___x_349_);
lean_inc_ref(v_lctx_343_);
v___x_351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_351_, 0, v_lctx_343_);
lean_ctor_set(v___x_351_, 1, v___x_350_);
v___x_352_ = lean_usize_of_nat(v___x_347_);
v___x_353_ = ((size_t)0ULL);
v___x_354_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_removeUnused_spec__1(v_vars_328_, v___x_352_, v___x_353_, v___x_351_, v_a_330_, v_a_331_, v_a_332_, v_a_333_);
if (lean_obj_tag(v___x_354_) == 0)
{
lean_object* v_a_355_; lean_object* v_snd_356_; lean_object* v_snd_357_; lean_object* v_fst_358_; lean_object* v_fst_359_; lean_object* v_fst_360_; 
v_a_355_ = lean_ctor_get(v___x_354_, 0);
lean_inc(v_a_355_);
lean_dec_ref_known(v___x_354_, 1);
v_snd_356_ = lean_ctor_get(v_a_355_, 1);
lean_inc(v_snd_356_);
v_snd_357_ = lean_ctor_get(v_snd_356_, 1);
lean_inc(v_snd_357_);
v_fst_358_ = lean_ctor_get(v_a_355_, 0);
lean_inc(v_fst_358_);
lean_dec(v_a_355_);
v_fst_359_ = lean_ctor_get(v_snd_356_, 0);
lean_inc(v_fst_359_);
lean_dec(v_snd_356_);
v_fst_360_ = lean_ctor_get(v_snd_357_, 0);
lean_inc(v_fst_360_);
lean_dec(v_snd_357_);
v_fst_336_ = v_fst_358_;
v_fst_337_ = v_fst_359_;
v_fst_338_ = v_fst_360_;
goto v___jp_335_;
}
else
{
lean_object* v_a_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_368_; 
v_a_361_ = lean_ctor_get(v___x_354_, 0);
v_isSharedCheck_368_ = !lean_is_exclusive(v___x_354_);
if (v_isSharedCheck_368_ == 0)
{
v___x_363_ = v___x_354_;
v_isShared_364_ = v_isSharedCheck_368_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_a_361_);
lean_dec(v___x_354_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_368_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_366_; 
if (v_isShared_364_ == 0)
{
v___x_366_ = v___x_363_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_a_361_);
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
v___jp_335_:
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_339_ = l_Array_reverse___redArg(v_fst_338_);
v___x_340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_340_, 0, v_fst_337_);
lean_ctor_set(v___x_340_, 1, v___x_339_);
v___x_341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_341_, 0, v_fst_336_);
lean_ctor_set(v___x_341_, 1, v___x_340_);
v___x_342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
return v___x_342_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_removeUnused_0interp(lean_interpreter_value* stack)
{
lean_object* v_vars_328_ = stack[0].m_obj;
lean_object* v_used_329_ = stack[1].m_obj;
lean_object* v_a_330_ = stack[2].m_obj;
lean_object* v_a_331_ = stack[3].m_obj;
lean_object* v_a_332_ = stack[4].m_obj;
lean_object* v_a_333_ = stack[5].m_obj;
lean_object* v_res_369_;
v_res_369_ = l_Lean_Meta_removeUnused(v_vars_328_, v_used_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_);
stack->m_obj
 = v_res_369_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_removeUnused___boxed(lean_object* v_vars_370_, lean_object* v_used_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l_Lean_Meta_removeUnused(v_vars_370_, v_used_371_, v_a_372_, v_a_373_, v_a_374_, v_a_375_);
lean_dec(v_a_375_);
lean_dec_ref(v_a_374_);
lean_dec(v_a_373_);
lean_dec_ref(v_a_372_);
lean_dec_ref(v_vars_370_);
return v_res_377_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_removeUnused_spec__0(lean_object* v_00_u03b2_378_, lean_object* v_k_379_, lean_object* v_t_380_){
_start:
{
uint8_t v___x_381_; 
v___x_381_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_removeUnused_spec__0___redArg(v_k_379_, v_t_380_);
return v___x_381_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_removeUnused_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_379_ = stack[1].m_obj;
lean_object* v_t_380_ = stack[2].m_obj;
uint8_t v_res_382_;
v_res_382_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_removeUnused_spec__0(lean_box(0), v_k_379_, v_t_380_);
stack->m_num = v_res_382_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_removeUnused_spec__0___boxed(lean_object* v_00_u03b2_383_, lean_object* v_k_384_, lean_object* v_t_385_){
_start:
{
uint8_t v_res_386_; lean_object* v_r_387_; 
v_res_386_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_removeUnused_spec__0(v_00_u03b2_383_, v_k_384_, v_t_385_);
lean_dec(v_t_385_);
lean_dec(v_k_384_);
v_r_387_ = lean_box(v_res_386_);
return v_r_387_;
}
}
lean_object* runtime_initialize_Lean_Util_CollectFVars(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_CollectFVars(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Util_CollectFVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_CollectFVars(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Util_CollectFVars(uint8_t builtin);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_CollectFVars(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Util_CollectFVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_CollectFVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_CollectFVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_CollectFVars(builtin);
}
#ifdef __cplusplus
}
#endif

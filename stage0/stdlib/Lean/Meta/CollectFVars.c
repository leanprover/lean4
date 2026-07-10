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
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_collectFVars(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_local_ctx_erase(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Expr_collectFVars_spec__0___redArg(lean_object* v_e_1_, lean_object* v___y_2_){
_start:
{
uint8_t v___x_4_; uint8_t v___x_5_; 
v___x_4_ = l_Lean_Expr_hasMVar(v_e_1_);
v___x_5_ = lean_bool_not(v___x_4_);
if (v___x_5_ == 0)
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
v___x_21_ = lean_st_ref_set(v___y_2_, v___x_20_);
v___x_22_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_22_, 0, v_fst_9_);
return v___x_22_;
}
}
}
else
{
lean_object* v___x_26_; 
v___x_26_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_26_, 0, v_e_1_);
return v___x_26_;
}
}
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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Expr_collectFVars_spec__0(lean_object* v_e_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_Lean_instantiateMVars___at___00Lean_Expr_collectFVars_spec__0___redArg(v_e_31_, v___y_34_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Expr_collectFVars_spec__0___boxed(lean_object* v_e_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Lean_instantiateMVars___at___00Lean_Expr_collectFVars_spec__0(v_e_39_, v___y_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_);
lean_dec(v___y_44_);
lean_dec_ref(v___y_43_);
lean_dec(v___y_42_);
lean_dec_ref(v___y_41_);
lean_dec(v___y_40_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_collectFVars(lean_object* v_e_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_){
_start:
{
lean_object* v___x_54_; lean_object* v_a_55_; lean_object* v___x_57_; uint8_t v_isShared_58_; uint8_t v_isSharedCheck_66_; 
v___x_54_ = l_Lean_instantiateMVars___at___00Lean_Expr_collectFVars_spec__0___redArg(v_e_47_, v_a_50_);
v_a_55_ = lean_ctor_get(v___x_54_, 0);
v_isSharedCheck_66_ = !lean_is_exclusive(v___x_54_);
if (v_isSharedCheck_66_ == 0)
{
v___x_57_ = v___x_54_;
v_isShared_58_ = v_isSharedCheck_66_;
goto v_resetjp_56_;
}
else
{
lean_inc(v_a_55_);
lean_dec(v___x_54_);
v___x_57_ = lean_box(0);
v_isShared_58_ = v_isSharedCheck_66_;
goto v_resetjp_56_;
}
v_resetjp_56_:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_64_; 
v___x_59_ = lean_st_ref_take(v_a_48_);
v___x_60_ = l_Lean_collectFVars(v___x_59_, v_a_55_);
v___x_61_ = lean_st_ref_set(v_a_48_, v___x_60_);
v___x_62_ = lean_box(0);
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 0, v___x_62_);
v___x_64_ = v___x_57_;
goto v_reusejp_63_;
}
else
{
lean_object* v_reuseFailAlloc_65_; 
v_reuseFailAlloc_65_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_65_, 0, v___x_62_);
v___x_64_ = v_reuseFailAlloc_65_;
goto v_reusejp_63_;
}
v_reusejp_63_:
{
return v___x_64_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_collectFVars___boxed(lean_object* v_e_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l_Lean_Expr_collectFVars(v_e_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_);
lean_dec(v_a_72_);
lean_dec_ref(v_a_71_);
lean_dec(v_a_70_);
lean_dec_ref(v_a_69_);
lean_dec(v_a_68_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_collectFVars(lean_object* v_localDecl_75_, lean_object* v_a_76_, lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_){
_start:
{
if (lean_obj_tag(v_localDecl_75_) == 0)
{
lean_object* v_type_82_; lean_object* v___x_83_; 
v_type_82_ = lean_ctor_get(v_localDecl_75_, 3);
lean_inc_ref(v_type_82_);
lean_dec_ref_known(v_localDecl_75_, 4);
v___x_83_ = l_Lean_Expr_collectFVars(v_type_82_, v_a_76_, v_a_77_, v_a_78_, v_a_79_, v_a_80_);
return v___x_83_;
}
else
{
lean_object* v_type_84_; lean_object* v_value_85_; lean_object* v___x_86_; 
v_type_84_ = lean_ctor_get(v_localDecl_75_, 3);
lean_inc_ref(v_type_84_);
v_value_85_ = lean_ctor_get(v_localDecl_75_, 4);
lean_inc_ref(v_value_85_);
lean_dec_ref_known(v_localDecl_75_, 5);
v___x_86_ = l_Lean_Expr_collectFVars(v_type_84_, v_a_76_, v_a_77_, v_a_78_, v_a_79_, v_a_80_);
if (lean_obj_tag(v___x_86_) == 0)
{
lean_object* v___x_87_; 
lean_dec_ref_known(v___x_86_, 1);
v___x_87_ = l_Lean_Expr_collectFVars(v_value_85_, v_a_76_, v_a_77_, v_a_78_, v_a_79_, v_a_80_);
return v___x_87_;
}
else
{
lean_dec_ref(v_value_85_);
return v___x_86_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_collectFVars___boxed(lean_object* v_localDecl_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l_Lean_LocalDecl_collectFVars(v_localDecl_88_, v_a_89_, v_a_90_, v_a_91_, v_a_92_, v_a_93_);
lean_dec(v_a_93_);
lean_dec_ref(v_a_92_);
lean_dec(v_a_91_);
lean_dec_ref(v_a_90_);
lean_dec(v_a_89_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_getNext_x3f___redArg(lean_object* v_a_96_, lean_object* v_a_97_){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v_fvarIds_101_; lean_object* v___x_102_; uint8_t v___x_103_; 
v___x_99_ = lean_st_ref_get(v_a_97_);
v___x_100_ = lean_st_ref_get(v_a_96_);
v_fvarIds_101_ = lean_ctor_get(v___x_99_, 2);
lean_inc_ref(v_fvarIds_101_);
lean_dec(v___x_99_);
v___x_102_ = lean_array_get_size(v_fvarIds_101_);
v___x_103_ = lean_nat_dec_lt(v___x_100_, v___x_102_);
if (v___x_103_ == 0)
{
lean_object* v___x_104_; lean_object* v___x_105_; 
lean_dec_ref(v_fvarIds_101_);
lean_dec(v___x_100_);
v___x_104_ = lean_box(0);
v___x_105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_105_, 0, v___x_104_);
return v___x_105_;
}
else
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_106_ = lean_st_ref_take(v_a_96_);
v___x_107_ = lean_unsigned_to_nat(1u);
v___x_108_ = lean_nat_add(v___x_106_, v___x_107_);
lean_dec(v___x_106_);
v___x_109_ = lean_st_ref_set(v_a_96_, v___x_108_);
v___x_110_ = lean_array_fget(v_fvarIds_101_, v___x_100_);
lean_dec(v___x_100_);
lean_dec_ref(v_fvarIds_101_);
v___x_111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_111_, 0, v___x_110_);
v___x_112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_112_, 0, v___x_111_);
return v___x_112_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_getNext_x3f___redArg___boxed(lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_getNext_x3f___redArg(v_a_113_, v_a_114_);
lean_dec(v_a_114_);
lean_dec(v_a_113_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_getNext_x3f(lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_getNext_x3f___redArg(v_a_117_, v_a_118_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_getNext_x3f___boxed(lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_getNext_x3f(v_a_125_, v_a_126_, v_a_127_, v_a_128_, v_a_129_, v_a_130_);
lean_dec(v_a_130_);
lean_dec_ref(v_a_129_);
lean_dec(v_a_128_);
lean_dec_ref(v_a_127_);
lean_dec(v_a_126_);
lean_dec(v_a_125_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_go(lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_getNext_x3f___redArg(v_a_133_, v_a_134_);
if (lean_obj_tag(v___x_140_) == 0)
{
lean_object* v_a_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_159_; 
v_a_141_ = lean_ctor_get(v___x_140_, 0);
v_isSharedCheck_159_ = !lean_is_exclusive(v___x_140_);
if (v_isSharedCheck_159_ == 0)
{
v___x_143_ = v___x_140_;
v_isShared_144_ = v_isSharedCheck_159_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_a_141_);
lean_dec(v___x_140_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_159_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
if (lean_obj_tag(v_a_141_) == 1)
{
lean_object* v_val_145_; lean_object* v_lctx_146_; lean_object* v___x_147_; 
v_val_145_ = lean_ctor_get(v_a_141_, 0);
lean_inc(v_val_145_);
lean_dec_ref_known(v_a_141_, 1);
v_lctx_146_ = lean_ctor_get(v_a_135_, 2);
lean_inc_ref(v_lctx_146_);
v___x_147_ = lean_local_ctx_find(v_lctx_146_, v_val_145_);
if (lean_obj_tag(v___x_147_) == 1)
{
lean_object* v_val_148_; lean_object* v___x_149_; 
lean_del_object(v___x_143_);
v_val_148_ = lean_ctor_get(v___x_147_, 0);
lean_inc(v_val_148_);
lean_dec_ref_known(v___x_147_, 1);
v___x_149_ = l_Lean_LocalDecl_collectFVars(v_val_148_, v_a_134_, v_a_135_, v_a_136_, v_a_137_, v_a_138_);
if (lean_obj_tag(v___x_149_) == 0)
{
lean_dec_ref_known(v___x_149_, 1);
goto _start;
}
else
{
return v___x_149_;
}
}
else
{
lean_object* v___x_151_; lean_object* v___x_153_; 
lean_dec(v___x_147_);
v___x_151_ = lean_box(0);
if (v_isShared_144_ == 0)
{
lean_ctor_set(v___x_143_, 0, v___x_151_);
v___x_153_ = v___x_143_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v___x_151_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
return v___x_153_;
}
}
}
else
{
lean_object* v___x_155_; lean_object* v___x_157_; 
lean_dec(v_a_141_);
v___x_155_ = lean_box(0);
if (v_isShared_144_ == 0)
{
lean_ctor_set(v___x_143_, 0, v___x_155_);
v___x_157_ = v___x_143_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v___x_155_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
return v___x_157_;
}
}
}
}
else
{
lean_object* v_a_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_167_; 
v_a_160_ = lean_ctor_get(v___x_140_, 0);
v_isSharedCheck_167_ = !lean_is_exclusive(v___x_140_);
if (v_isSharedCheck_167_ == 0)
{
v___x_162_ = v___x_140_;
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_a_160_);
lean_dec(v___x_140_);
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
v_reuseFailAlloc_166_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_go___boxed(lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_go(v_a_168_, v_a_169_, v_a_170_, v_a_171_, v_a_172_, v_a_173_);
lean_dec(v_a_173_);
lean_dec_ref(v_a_172_);
lean_dec(v_a_171_);
lean_dec_ref(v_a_170_);
lean_dec(v_a_169_);
lean_dec(v_a_168_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_CollectFVars_State_addDependencies(lean_object* v_s_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_182_ = lean_st_mk_ref(v_s_176_);
v___x_183_ = lean_unsigned_to_nat(0u);
v___x_184_ = lean_st_mk_ref(v___x_183_);
v___x_185_ = l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_go(v___x_184_, v___x_182_, v_a_177_, v_a_178_, v_a_179_, v_a_180_);
if (lean_obj_tag(v___x_185_) == 0)
{
lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_194_; 
v_isSharedCheck_194_ = !lean_is_exclusive(v___x_185_);
if (v_isSharedCheck_194_ == 0)
{
lean_object* v_unused_195_; 
v_unused_195_ = lean_ctor_get(v___x_185_, 0);
lean_dec(v_unused_195_);
v___x_187_ = v___x_185_;
v_isShared_188_ = v_isSharedCheck_194_;
goto v_resetjp_186_;
}
else
{
lean_dec(v___x_185_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_194_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_192_; 
v___x_189_ = lean_st_ref_get(v___x_184_);
lean_dec(v___x_184_);
lean_dec(v___x_189_);
v___x_190_ = lean_st_ref_get(v___x_182_);
lean_dec(v___x_182_);
if (v_isShared_188_ == 0)
{
lean_ctor_set(v___x_187_, 0, v___x_190_);
v___x_192_ = v___x_187_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v___x_190_);
v___x_192_ = v_reuseFailAlloc_193_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
return v___x_192_;
}
}
}
else
{
lean_object* v_a_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_203_; 
lean_dec(v___x_184_);
lean_dec(v___x_182_);
v_a_196_ = lean_ctor_get(v___x_185_, 0);
v_isSharedCheck_203_ = !lean_is_exclusive(v___x_185_);
if (v_isSharedCheck_203_ == 0)
{
v___x_198_ = v___x_185_;
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_a_196_);
lean_dec(v___x_185_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_201_; 
if (v_isShared_199_ == 0)
{
v___x_201_ = v___x_198_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v_a_196_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
return v___x_201_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_CollectFVars_State_addDependencies___boxed(lean_object* v_s_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Lean_CollectFVars_State_addDependencies(v_s_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_);
lean_dec(v_a_208_);
lean_dec_ref(v_a_207_);
lean_dec(v_a_206_);
lean_dec_ref(v_a_205_);
return v_res_210_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_removeUnused_spec__0___redArg(lean_object* v_k_211_, lean_object* v_t_212_){
_start:
{
if (lean_obj_tag(v_t_212_) == 0)
{
lean_object* v_k_213_; lean_object* v_l_214_; lean_object* v_r_215_; uint8_t v___x_216_; 
v_k_213_ = lean_ctor_get(v_t_212_, 1);
v_l_214_ = lean_ctor_get(v_t_212_, 3);
v_r_215_ = lean_ctor_get(v_t_212_, 4);
v___x_216_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_211_, v_k_213_);
switch(v___x_216_)
{
case 0:
{
v_t_212_ = v_l_214_;
goto _start;
}
case 1:
{
uint8_t v___x_218_; 
v___x_218_ = 1;
return v___x_218_;
}
default: 
{
v_t_212_ = v_r_215_;
goto _start;
}
}
}
else
{
uint8_t v___x_220_; 
v___x_220_ = 0;
return v___x_220_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_removeUnused_spec__0___redArg___boxed(lean_object* v_k_221_, lean_object* v_t_222_){
_start:
{
uint8_t v_res_223_; lean_object* v_r_224_; 
v_res_223_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_removeUnused_spec__0___redArg(v_k_221_, v_t_222_);
lean_dec(v_t_222_);
lean_dec(v_k_221_);
v_r_224_ = lean_box(v_res_223_);
return v_r_224_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_removeUnused_spec__1(lean_object* v_as_225_, size_t v_i_226_, size_t v_stop_227_, lean_object* v_b_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_){
_start:
{
uint8_t v___x_234_; 
v___x_234_ = lean_usize_dec_eq(v_i_226_, v_stop_227_);
if (v___x_234_ == 0)
{
lean_object* v_snd_235_; lean_object* v_snd_236_; lean_object* v_snd_237_; lean_object* v_fst_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_302_; 
v_snd_235_ = lean_ctor_get(v_b_228_, 1);
lean_inc(v_snd_235_);
v_snd_236_ = lean_ctor_get(v_snd_235_, 1);
lean_inc(v_snd_236_);
v_snd_237_ = lean_ctor_get(v_snd_236_, 1);
v_fst_238_ = lean_ctor_get(v_b_228_, 0);
v_isSharedCheck_302_ = !lean_is_exclusive(v_b_228_);
if (v_isSharedCheck_302_ == 0)
{
lean_object* v_unused_303_; 
v_unused_303_ = lean_ctor_get(v_b_228_, 1);
lean_dec(v_unused_303_);
v___x_240_ = v_b_228_;
v_isShared_241_ = v_isSharedCheck_302_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_fst_238_);
lean_dec(v_b_228_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_302_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v_fst_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_300_; 
v_fst_242_ = lean_ctor_get(v_snd_235_, 0);
v_isSharedCheck_300_ = !lean_is_exclusive(v_snd_235_);
if (v_isSharedCheck_300_ == 0)
{
lean_object* v_unused_301_; 
v_unused_301_ = lean_ctor_get(v_snd_235_, 1);
lean_dec(v_unused_301_);
v___x_244_ = v_snd_235_;
v_isShared_245_ = v_isSharedCheck_300_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_fst_242_);
lean_dec(v_snd_235_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_300_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v_fst_246_; lean_object* v_fvarSet_247_; size_t v___x_248_; size_t v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; uint8_t v___x_252_; 
v_fst_246_ = lean_ctor_get(v_snd_236_, 0);
v_fvarSet_247_ = lean_ctor_get(v_snd_237_, 1);
v___x_248_ = ((size_t)1ULL);
v___x_249_ = lean_usize_sub(v_i_226_, v___x_248_);
v___x_250_ = lean_array_uget_borrowed(v_as_225_, v___x_249_);
v___x_251_ = l_Lean_Expr_fvarId_x21(v___x_250_);
v___x_252_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_removeUnused_spec__0___redArg(v___x_251_, v_fvarSet_247_);
if (v___x_252_ == 0)
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_256_; 
lean_inc(v___x_251_);
v___x_253_ = lean_local_ctx_erase(v_fst_238_, v___x_251_);
v___x_254_ = l_Lean_LocalInstances_erase(v_fst_242_, v___x_251_);
if (v_isShared_245_ == 0)
{
lean_ctor_set(v___x_244_, 0, v___x_254_);
v___x_256_ = v___x_244_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v___x_254_);
lean_ctor_set(v_reuseFailAlloc_261_, 1, v_snd_236_);
v___x_256_ = v_reuseFailAlloc_261_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
lean_object* v___x_258_; 
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 1, v___x_256_);
lean_ctor_set(v___x_240_, 0, v___x_253_);
v___x_258_ = v___x_240_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v___x_253_);
lean_ctor_set(v_reuseFailAlloc_260_, 1, v___x_256_);
v___x_258_ = v_reuseFailAlloc_260_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
v_i_226_ = v___x_249_;
v_b_228_ = v___x_258_;
goto _start;
}
}
}
else
{
lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_297_; 
lean_inc(v_fst_246_);
lean_inc(v_snd_237_);
lean_dec(v___x_251_);
v_isSharedCheck_297_ = !lean_is_exclusive(v_snd_236_);
if (v_isSharedCheck_297_ == 0)
{
lean_object* v_unused_298_; lean_object* v_unused_299_; 
v_unused_298_ = lean_ctor_get(v_snd_236_, 1);
lean_dec(v_unused_298_);
v_unused_299_ = lean_ctor_get(v_snd_236_, 0);
lean_dec(v_unused_299_);
v___x_263_ = v_snd_236_;
v_isShared_264_ = v_isSharedCheck_297_;
goto v_resetjp_262_;
}
else
{
lean_dec(v_snd_236_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_297_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_265_; 
lean_inc(v___y_232_);
lean_inc_ref(v___y_231_);
lean_inc(v___y_230_);
lean_inc_ref(v___y_229_);
lean_inc(v___x_250_);
v___x_265_ = lean_infer_type(v___x_250_, v___y_229_, v___y_230_, v___y_231_, v___y_232_);
if (lean_obj_tag(v___x_265_) == 0)
{
lean_object* v_a_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v_a_266_ = lean_ctor_get(v___x_265_, 0);
lean_inc(v_a_266_);
lean_dec_ref_known(v___x_265_, 1);
v___x_267_ = lean_st_mk_ref(v_snd_237_);
v___x_268_ = l_Lean_Expr_collectFVars(v_a_266_, v___x_267_, v___y_229_, v___y_230_, v___y_231_, v___y_232_);
if (lean_obj_tag(v___x_268_) == 0)
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_272_; 
lean_dec_ref_known(v___x_268_, 1);
v___x_269_ = lean_st_ref_get(v___x_267_);
lean_dec(v___x_267_);
lean_inc(v___x_250_);
v___x_270_ = lean_array_push(v_fst_246_, v___x_250_);
if (v_isShared_264_ == 0)
{
lean_ctor_set(v___x_263_, 1, v___x_269_);
lean_ctor_set(v___x_263_, 0, v___x_270_);
v___x_272_ = v___x_263_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v___x_270_);
lean_ctor_set(v_reuseFailAlloc_280_, 1, v___x_269_);
v___x_272_ = v_reuseFailAlloc_280_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
lean_object* v___x_274_; 
if (v_isShared_245_ == 0)
{
lean_ctor_set(v___x_244_, 1, v___x_272_);
v___x_274_ = v___x_244_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_fst_242_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v___x_272_);
v___x_274_ = v_reuseFailAlloc_279_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
lean_object* v___x_276_; 
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 1, v___x_274_);
v___x_276_ = v___x_240_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v_fst_238_);
lean_ctor_set(v_reuseFailAlloc_278_, 1, v___x_274_);
v___x_276_ = v_reuseFailAlloc_278_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
v_i_226_ = v___x_249_;
v_b_228_ = v___x_276_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_288_; 
lean_dec(v___x_267_);
lean_del_object(v___x_263_);
lean_dec(v_fst_246_);
lean_del_object(v___x_244_);
lean_dec(v_fst_242_);
lean_del_object(v___x_240_);
lean_dec(v_fst_238_);
v_a_281_ = lean_ctor_get(v___x_268_, 0);
v_isSharedCheck_288_ = !lean_is_exclusive(v___x_268_);
if (v_isSharedCheck_288_ == 0)
{
v___x_283_ = v___x_268_;
v_isShared_284_ = v_isSharedCheck_288_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_a_281_);
lean_dec(v___x_268_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_288_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_286_; 
if (v_isShared_284_ == 0)
{
v___x_286_ = v___x_283_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v_a_281_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
return v___x_286_;
}
}
}
}
else
{
lean_object* v_a_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_296_; 
lean_del_object(v___x_263_);
lean_dec(v_fst_246_);
lean_del_object(v___x_244_);
lean_dec(v_fst_242_);
lean_del_object(v___x_240_);
lean_dec(v_fst_238_);
lean_dec(v_snd_237_);
v_a_289_ = lean_ctor_get(v___x_265_, 0);
v_isSharedCheck_296_ = !lean_is_exclusive(v___x_265_);
if (v_isSharedCheck_296_ == 0)
{
v___x_291_ = v___x_265_;
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_a_289_);
lean_dec(v___x_265_);
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
}
}
}
}
else
{
lean_object* v___x_304_; 
v___x_304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_304_, 0, v_b_228_);
return v___x_304_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_removeUnused_spec__1___boxed(lean_object* v_as_305_, lean_object* v_i_306_, lean_object* v_stop_307_, lean_object* v_b_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_){
_start:
{
size_t v_i_boxed_314_; size_t v_stop_boxed_315_; lean_object* v_res_316_; 
v_i_boxed_314_ = lean_unbox_usize(v_i_306_);
lean_dec(v_i_306_);
v_stop_boxed_315_ = lean_unbox_usize(v_stop_307_);
lean_dec(v_stop_307_);
v_res_316_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_removeUnused_spec__1(v_as_305_, v_i_boxed_314_, v_stop_boxed_315_, v_b_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_);
lean_dec(v___y_312_);
lean_dec_ref(v___y_311_);
lean_dec(v___y_310_);
lean_dec_ref(v___y_309_);
lean_dec_ref(v_as_305_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_removeUnused(lean_object* v_vars_319_, lean_object* v_used_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_){
_start:
{
lean_object* v_fst_327_; lean_object* v_fst_328_; lean_object* v_fst_329_; lean_object* v_lctx_334_; lean_object* v_localInstances_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; uint8_t v___x_339_; 
v_lctx_334_ = lean_ctor_get(v_a_321_, 2);
v_localInstances_335_ = lean_ctor_get(v_a_321_, 3);
v___x_336_ = lean_unsigned_to_nat(0u);
v___x_337_ = ((lean_object*)(l_Lean_Meta_removeUnused___closed__0));
v___x_338_ = lean_array_get_size(v_vars_319_);
v___x_339_ = lean_nat_dec_lt(v___x_336_, v___x_338_);
if (v___x_339_ == 0)
{
lean_dec_ref(v_used_320_);
lean_inc_ref(v_localInstances_335_);
lean_inc_ref(v_lctx_334_);
v_fst_327_ = v_lctx_334_;
v_fst_328_ = v_localInstances_335_;
v_fst_329_ = v___x_337_;
goto v___jp_326_;
}
else
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; size_t v___x_343_; size_t v___x_344_; lean_object* v___x_345_; 
v___x_340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_340_, 0, v___x_337_);
lean_ctor_set(v___x_340_, 1, v_used_320_);
lean_inc_ref(v_localInstances_335_);
v___x_341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_341_, 0, v_localInstances_335_);
lean_ctor_set(v___x_341_, 1, v___x_340_);
lean_inc_ref(v_lctx_334_);
v___x_342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_342_, 0, v_lctx_334_);
lean_ctor_set(v___x_342_, 1, v___x_341_);
v___x_343_ = lean_usize_of_nat(v___x_338_);
v___x_344_ = ((size_t)0ULL);
v___x_345_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_removeUnused_spec__1(v_vars_319_, v___x_343_, v___x_344_, v___x_342_, v_a_321_, v_a_322_, v_a_323_, v_a_324_);
if (lean_obj_tag(v___x_345_) == 0)
{
lean_object* v_a_346_; lean_object* v_snd_347_; lean_object* v_snd_348_; lean_object* v_fst_349_; lean_object* v_fst_350_; lean_object* v_fst_351_; 
v_a_346_ = lean_ctor_get(v___x_345_, 0);
lean_inc(v_a_346_);
lean_dec_ref_known(v___x_345_, 1);
v_snd_347_ = lean_ctor_get(v_a_346_, 1);
lean_inc(v_snd_347_);
v_snd_348_ = lean_ctor_get(v_snd_347_, 1);
lean_inc(v_snd_348_);
v_fst_349_ = lean_ctor_get(v_a_346_, 0);
lean_inc(v_fst_349_);
lean_dec(v_a_346_);
v_fst_350_ = lean_ctor_get(v_snd_347_, 0);
lean_inc(v_fst_350_);
lean_dec(v_snd_347_);
v_fst_351_ = lean_ctor_get(v_snd_348_, 0);
lean_inc(v_fst_351_);
lean_dec(v_snd_348_);
v_fst_327_ = v_fst_349_;
v_fst_328_ = v_fst_350_;
v_fst_329_ = v_fst_351_;
goto v___jp_326_;
}
else
{
lean_object* v_a_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_359_; 
v_a_352_ = lean_ctor_get(v___x_345_, 0);
v_isSharedCheck_359_ = !lean_is_exclusive(v___x_345_);
if (v_isSharedCheck_359_ == 0)
{
v___x_354_ = v___x_345_;
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_a_352_);
lean_dec(v___x_345_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_357_; 
if (v_isShared_355_ == 0)
{
v___x_357_ = v___x_354_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v_a_352_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
}
}
}
}
v___jp_326_:
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_330_ = l_Array_reverse___redArg(v_fst_329_);
v___x_331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_331_, 0, v_fst_328_);
lean_ctor_set(v___x_331_, 1, v___x_330_);
v___x_332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_332_, 0, v_fst_327_);
lean_ctor_set(v___x_332_, 1, v___x_331_);
v___x_333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
return v___x_333_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_removeUnused___boxed(lean_object* v_vars_360_, lean_object* v_used_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l_Lean_Meta_removeUnused(v_vars_360_, v_used_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_);
lean_dec(v_a_365_);
lean_dec_ref(v_a_364_);
lean_dec(v_a_363_);
lean_dec_ref(v_a_362_);
lean_dec_ref(v_vars_360_);
return v_res_367_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_removeUnused_spec__0(lean_object* v_00_u03b2_368_, lean_object* v_k_369_, lean_object* v_t_370_){
_start:
{
uint8_t v___x_371_; 
v___x_371_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_removeUnused_spec__0___redArg(v_k_369_, v_t_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_removeUnused_spec__0___boxed(lean_object* v_00_u03b2_372_, lean_object* v_k_373_, lean_object* v_t_374_){
_start:
{
uint8_t v_res_375_; lean_object* v_r_376_; 
v_res_375_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_removeUnused_spec__0(v_00_u03b2_372_, v_k_373_, v_t_374_);
lean_dec(v_t_374_);
lean_dec(v_k_373_);
v_r_376_ = lean_box(v_res_375_);
return v_r_376_;
}
}
lean_object* runtime_initialize_Lean_Util_CollectFVars(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_CollectFVars(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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

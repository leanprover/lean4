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
lean_object* l_Lean_Meta_getLocalInstances___redArg(lean_object*);
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
v___x_21_ = lean_st_ref_set(v___y_2_, v___x_20_);
v___x_22_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_22_, 0, v_fst_9_);
return v___x_22_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Expr_collectFVars_spec__0___redArg___boxed(lean_object* v_e_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_instantiateMVars___at___00Lean_Expr_collectFVars_spec__0___redArg(v_e_26_, v___y_27_);
lean_dec(v___y_27_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Expr_collectFVars_spec__0(lean_object* v_e_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Lean_instantiateMVars___at___00Lean_Expr_collectFVars_spec__0___redArg(v_e_30_, v___y_33_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Expr_collectFVars_spec__0___boxed(lean_object* v_e_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_Lean_instantiateMVars___at___00Lean_Expr_collectFVars_spec__0(v_e_38_, v___y_39_, v___y_40_, v___y_41_, v___y_42_, v___y_43_);
lean_dec(v___y_43_);
lean_dec_ref(v___y_42_);
lean_dec(v___y_41_);
lean_dec_ref(v___y_40_);
lean_dec(v___y_39_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_collectFVars(lean_object* v_e_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_){
_start:
{
lean_object* v___x_53_; lean_object* v_a_54_; lean_object* v___x_56_; uint8_t v_isShared_57_; uint8_t v_isSharedCheck_65_; 
v___x_53_ = l_Lean_instantiateMVars___at___00Lean_Expr_collectFVars_spec__0___redArg(v_e_46_, v_a_49_);
v_a_54_ = lean_ctor_get(v___x_53_, 0);
v_isSharedCheck_65_ = !lean_is_exclusive(v___x_53_);
if (v_isSharedCheck_65_ == 0)
{
v___x_56_ = v___x_53_;
v_isShared_57_ = v_isSharedCheck_65_;
goto v_resetjp_55_;
}
else
{
lean_inc(v_a_54_);
lean_dec(v___x_53_);
v___x_56_ = lean_box(0);
v_isShared_57_ = v_isSharedCheck_65_;
goto v_resetjp_55_;
}
v_resetjp_55_:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_63_; 
v___x_58_ = lean_st_ref_take(v_a_47_);
v___x_59_ = l_Lean_collectFVars(v___x_58_, v_a_54_);
v___x_60_ = lean_st_ref_set(v_a_47_, v___x_59_);
v___x_61_ = lean_box(0);
if (v_isShared_57_ == 0)
{
lean_ctor_set(v___x_56_, 0, v___x_61_);
v___x_63_ = v___x_56_;
goto v_reusejp_62_;
}
else
{
lean_object* v_reuseFailAlloc_64_; 
v_reuseFailAlloc_64_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_64_, 0, v___x_61_);
v___x_63_ = v_reuseFailAlloc_64_;
goto v_reusejp_62_;
}
v_reusejp_62_:
{
return v___x_63_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_collectFVars___boxed(lean_object* v_e_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l_Lean_Expr_collectFVars(v_e_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_);
lean_dec(v_a_71_);
lean_dec_ref(v_a_70_);
lean_dec(v_a_69_);
lean_dec_ref(v_a_68_);
lean_dec(v_a_67_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_collectFVars(lean_object* v_localDecl_74_, lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_){
_start:
{
if (lean_obj_tag(v_localDecl_74_) == 0)
{
lean_object* v_type_81_; lean_object* v___x_82_; 
v_type_81_ = lean_ctor_get(v_localDecl_74_, 3);
lean_inc_ref(v_type_81_);
lean_dec_ref(v_localDecl_74_);
v___x_82_ = l_Lean_Expr_collectFVars(v_type_81_, v_a_75_, v_a_76_, v_a_77_, v_a_78_, v_a_79_);
return v___x_82_;
}
else
{
lean_object* v_type_83_; lean_object* v_value_84_; lean_object* v___x_85_; 
v_type_83_ = lean_ctor_get(v_localDecl_74_, 3);
lean_inc_ref(v_type_83_);
v_value_84_ = lean_ctor_get(v_localDecl_74_, 4);
lean_inc_ref(v_value_84_);
lean_dec_ref(v_localDecl_74_);
v___x_85_ = l_Lean_Expr_collectFVars(v_type_83_, v_a_75_, v_a_76_, v_a_77_, v_a_78_, v_a_79_);
if (lean_obj_tag(v___x_85_) == 0)
{
lean_object* v___x_86_; 
lean_dec_ref(v___x_85_);
v___x_86_ = l_Lean_Expr_collectFVars(v_value_84_, v_a_75_, v_a_76_, v_a_77_, v_a_78_, v_a_79_);
return v___x_86_;
}
else
{
lean_dec_ref(v_value_84_);
return v___x_85_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_collectFVars___boxed(lean_object* v_localDecl_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_Lean_LocalDecl_collectFVars(v_localDecl_87_, v_a_88_, v_a_89_, v_a_90_, v_a_91_, v_a_92_);
lean_dec(v_a_92_);
lean_dec_ref(v_a_91_);
lean_dec(v_a_90_);
lean_dec_ref(v_a_89_);
lean_dec(v_a_88_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_getNext_x3f___redArg(lean_object* v_a_95_, lean_object* v_a_96_){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v_fvarIds_100_; lean_object* v___x_101_; uint8_t v___x_102_; 
v___x_98_ = lean_st_ref_get(v_a_96_);
v___x_99_ = lean_st_ref_get(v_a_95_);
v_fvarIds_100_ = lean_ctor_get(v___x_98_, 2);
lean_inc_ref(v_fvarIds_100_);
lean_dec(v___x_98_);
v___x_101_ = lean_array_get_size(v_fvarIds_100_);
v___x_102_ = lean_nat_dec_lt(v___x_99_, v___x_101_);
if (v___x_102_ == 0)
{
lean_object* v___x_103_; lean_object* v___x_104_; 
lean_dec_ref(v_fvarIds_100_);
lean_dec(v___x_99_);
v___x_103_ = lean_box(0);
v___x_104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_104_, 0, v___x_103_);
return v___x_104_;
}
else
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_105_ = lean_st_ref_take(v_a_95_);
v___x_106_ = lean_unsigned_to_nat(1u);
v___x_107_ = lean_nat_add(v___x_105_, v___x_106_);
lean_dec(v___x_105_);
v___x_108_ = lean_st_ref_set(v_a_95_, v___x_107_);
v___x_109_ = lean_array_fget(v_fvarIds_100_, v___x_99_);
lean_dec(v___x_99_);
lean_dec_ref(v_fvarIds_100_);
v___x_110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_110_, 0, v___x_109_);
v___x_111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_111_, 0, v___x_110_);
return v___x_111_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_getNext_x3f___redArg___boxed(lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_getNext_x3f___redArg(v_a_112_, v_a_113_);
lean_dec(v_a_113_);
lean_dec(v_a_112_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_getNext_x3f(lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_getNext_x3f___redArg(v_a_116_, v_a_117_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_getNext_x3f___boxed(lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_getNext_x3f(v_a_124_, v_a_125_, v_a_126_, v_a_127_, v_a_128_, v_a_129_);
lean_dec(v_a_129_);
lean_dec_ref(v_a_128_);
lean_dec(v_a_127_);
lean_dec_ref(v_a_126_);
lean_dec(v_a_125_);
lean_dec(v_a_124_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_go(lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_getNext_x3f___redArg(v_a_132_, v_a_133_);
if (lean_obj_tag(v___x_139_) == 0)
{
lean_object* v_a_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_158_; 
v_a_140_ = lean_ctor_get(v___x_139_, 0);
v_isSharedCheck_158_ = !lean_is_exclusive(v___x_139_);
if (v_isSharedCheck_158_ == 0)
{
v___x_142_ = v___x_139_;
v_isShared_143_ = v_isSharedCheck_158_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_a_140_);
lean_dec(v___x_139_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_158_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
if (lean_obj_tag(v_a_140_) == 1)
{
lean_object* v_val_144_; lean_object* v_lctx_145_; lean_object* v___x_146_; 
v_val_144_ = lean_ctor_get(v_a_140_, 0);
lean_inc(v_val_144_);
lean_dec_ref(v_a_140_);
v_lctx_145_ = lean_ctor_get(v_a_134_, 2);
lean_inc_ref(v_lctx_145_);
v___x_146_ = lean_local_ctx_find(v_lctx_145_, v_val_144_);
if (lean_obj_tag(v___x_146_) == 1)
{
lean_object* v_val_147_; lean_object* v___x_148_; 
lean_del_object(v___x_142_);
v_val_147_ = lean_ctor_get(v___x_146_, 0);
lean_inc(v_val_147_);
lean_dec_ref(v___x_146_);
v___x_148_ = l_Lean_LocalDecl_collectFVars(v_val_147_, v_a_133_, v_a_134_, v_a_135_, v_a_136_, v_a_137_);
if (lean_obj_tag(v___x_148_) == 0)
{
lean_dec_ref(v___x_148_);
goto _start;
}
else
{
lean_dec_ref(v_a_134_);
return v___x_148_;
}
}
else
{
lean_object* v___x_150_; lean_object* v___x_152_; 
lean_dec(v___x_146_);
lean_dec_ref(v_a_134_);
v___x_150_ = lean_box(0);
if (v_isShared_143_ == 0)
{
lean_ctor_set(v___x_142_, 0, v___x_150_);
v___x_152_ = v___x_142_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v___x_150_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
return v___x_152_;
}
}
}
else
{
lean_object* v___x_154_; lean_object* v___x_156_; 
lean_dec(v_a_140_);
lean_dec_ref(v_a_134_);
v___x_154_ = lean_box(0);
if (v_isShared_143_ == 0)
{
lean_ctor_set(v___x_142_, 0, v___x_154_);
v___x_156_ = v___x_142_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v___x_154_);
v___x_156_ = v_reuseFailAlloc_157_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
return v___x_156_;
}
}
}
}
else
{
lean_object* v_a_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_166_; 
lean_dec_ref(v_a_134_);
v_a_159_ = lean_ctor_get(v___x_139_, 0);
v_isSharedCheck_166_ = !lean_is_exclusive(v___x_139_);
if (v_isSharedCheck_166_ == 0)
{
v___x_161_ = v___x_139_;
v_isShared_162_ = v_isSharedCheck_166_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_a_159_);
lean_dec(v___x_139_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_go___boxed(lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_go(v_a_167_, v_a_168_, v_a_169_, v_a_170_, v_a_171_, v_a_172_);
lean_dec(v_a_172_);
lean_dec_ref(v_a_171_);
lean_dec(v_a_170_);
lean_dec(v_a_168_);
lean_dec(v_a_167_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_CollectFVars_State_addDependencies(lean_object* v_s_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_181_ = lean_st_mk_ref(v_s_175_);
v___x_182_ = lean_unsigned_to_nat(0u);
v___x_183_ = lean_st_mk_ref(v___x_182_);
v___x_184_ = l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_go(v___x_183_, v___x_181_, v_a_176_, v_a_177_, v_a_178_, v_a_179_);
if (lean_obj_tag(v___x_184_) == 0)
{
lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_193_; 
v_isSharedCheck_193_ = !lean_is_exclusive(v___x_184_);
if (v_isSharedCheck_193_ == 0)
{
lean_object* v_unused_194_; 
v_unused_194_ = lean_ctor_get(v___x_184_, 0);
lean_dec(v_unused_194_);
v___x_186_ = v___x_184_;
v_isShared_187_ = v_isSharedCheck_193_;
goto v_resetjp_185_;
}
else
{
lean_dec(v___x_184_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_193_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_191_; 
v___x_188_ = lean_st_ref_get(v___x_183_);
lean_dec(v___x_183_);
lean_dec(v___x_188_);
v___x_189_ = lean_st_ref_get(v___x_181_);
lean_dec(v___x_181_);
if (v_isShared_187_ == 0)
{
lean_ctor_set(v___x_186_, 0, v___x_189_);
v___x_191_ = v___x_186_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v___x_189_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
return v___x_191_;
}
}
}
else
{
lean_object* v_a_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_202_; 
lean_dec(v___x_183_);
lean_dec(v___x_181_);
v_a_195_ = lean_ctor_get(v___x_184_, 0);
v_isSharedCheck_202_ = !lean_is_exclusive(v___x_184_);
if (v_isSharedCheck_202_ == 0)
{
v___x_197_ = v___x_184_;
v_isShared_198_ = v_isSharedCheck_202_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_a_195_);
lean_dec(v___x_184_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_202_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___x_200_; 
if (v_isShared_198_ == 0)
{
v___x_200_ = v___x_197_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v_a_195_);
v___x_200_ = v_reuseFailAlloc_201_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
return v___x_200_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_CollectFVars_State_addDependencies___boxed(lean_object* v_s_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Lean_CollectFVars_State_addDependencies(v_s_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_);
lean_dec(v_a_207_);
lean_dec_ref(v_a_206_);
lean_dec(v_a_205_);
return v_res_209_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_removeUnused_spec__0___redArg(lean_object* v_k_210_, lean_object* v_t_211_){
_start:
{
if (lean_obj_tag(v_t_211_) == 0)
{
lean_object* v_k_212_; lean_object* v_l_213_; lean_object* v_r_214_; uint8_t v___x_215_; 
v_k_212_ = lean_ctor_get(v_t_211_, 1);
v_l_213_ = lean_ctor_get(v_t_211_, 3);
v_r_214_ = lean_ctor_get(v_t_211_, 4);
v___x_215_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_210_, v_k_212_);
switch(v___x_215_)
{
case 0:
{
v_t_211_ = v_l_213_;
goto _start;
}
case 1:
{
uint8_t v___x_217_; 
v___x_217_ = 1;
return v___x_217_;
}
default: 
{
v_t_211_ = v_r_214_;
goto _start;
}
}
}
else
{
uint8_t v___x_219_; 
v___x_219_ = 0;
return v___x_219_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_removeUnused_spec__0___redArg___boxed(lean_object* v_k_220_, lean_object* v_t_221_){
_start:
{
uint8_t v_res_222_; lean_object* v_r_223_; 
v_res_222_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_removeUnused_spec__0___redArg(v_k_220_, v_t_221_);
lean_dec(v_t_221_);
lean_dec(v_k_220_);
v_r_223_ = lean_box(v_res_222_);
return v_r_223_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_removeUnused_spec__1(lean_object* v_as_224_, size_t v_i_225_, size_t v_stop_226_, lean_object* v_b_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_){
_start:
{
uint8_t v___x_233_; 
v___x_233_ = lean_usize_dec_eq(v_i_225_, v_stop_226_);
if (v___x_233_ == 0)
{
lean_object* v_snd_234_; lean_object* v_snd_235_; lean_object* v_snd_236_; lean_object* v_fst_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_301_; 
v_snd_234_ = lean_ctor_get(v_b_227_, 1);
lean_inc(v_snd_234_);
v_snd_235_ = lean_ctor_get(v_snd_234_, 1);
lean_inc(v_snd_235_);
v_snd_236_ = lean_ctor_get(v_snd_235_, 1);
v_fst_237_ = lean_ctor_get(v_b_227_, 0);
v_isSharedCheck_301_ = !lean_is_exclusive(v_b_227_);
if (v_isSharedCheck_301_ == 0)
{
lean_object* v_unused_302_; 
v_unused_302_ = lean_ctor_get(v_b_227_, 1);
lean_dec(v_unused_302_);
v___x_239_ = v_b_227_;
v_isShared_240_ = v_isSharedCheck_301_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_fst_237_);
lean_dec(v_b_227_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_301_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v_fst_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_299_; 
v_fst_241_ = lean_ctor_get(v_snd_234_, 0);
v_isSharedCheck_299_ = !lean_is_exclusive(v_snd_234_);
if (v_isSharedCheck_299_ == 0)
{
lean_object* v_unused_300_; 
v_unused_300_ = lean_ctor_get(v_snd_234_, 1);
lean_dec(v_unused_300_);
v___x_243_ = v_snd_234_;
v_isShared_244_ = v_isSharedCheck_299_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_fst_241_);
lean_dec(v_snd_234_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_299_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v_fst_245_; lean_object* v_fvarSet_246_; size_t v___x_247_; size_t v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; uint8_t v___x_251_; 
v_fst_245_ = lean_ctor_get(v_snd_235_, 0);
v_fvarSet_246_ = lean_ctor_get(v_snd_236_, 1);
v___x_247_ = ((size_t)1ULL);
v___x_248_ = lean_usize_sub(v_i_225_, v___x_247_);
v___x_249_ = lean_array_uget_borrowed(v_as_224_, v___x_248_);
v___x_250_ = l_Lean_Expr_fvarId_x21(v___x_249_);
v___x_251_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_removeUnused_spec__0___redArg(v___x_250_, v_fvarSet_246_);
if (v___x_251_ == 0)
{
lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_255_; 
lean_inc(v___x_250_);
v___x_252_ = lean_local_ctx_erase(v_fst_237_, v___x_250_);
v___x_253_ = l_Lean_LocalInstances_erase(v_fst_241_, v___x_250_);
if (v_isShared_244_ == 0)
{
lean_ctor_set(v___x_243_, 0, v___x_253_);
v___x_255_ = v___x_243_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v___x_253_);
lean_ctor_set(v_reuseFailAlloc_260_, 1, v_snd_235_);
v___x_255_ = v_reuseFailAlloc_260_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
lean_object* v___x_257_; 
if (v_isShared_240_ == 0)
{
lean_ctor_set(v___x_239_, 1, v___x_255_);
lean_ctor_set(v___x_239_, 0, v___x_252_);
v___x_257_ = v___x_239_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v___x_252_);
lean_ctor_set(v_reuseFailAlloc_259_, 1, v___x_255_);
v___x_257_ = v_reuseFailAlloc_259_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
v_i_225_ = v___x_248_;
v_b_227_ = v___x_257_;
goto _start;
}
}
}
else
{
lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_296_; 
lean_inc(v_fst_245_);
lean_inc(v_snd_236_);
lean_dec(v___x_250_);
v_isSharedCheck_296_ = !lean_is_exclusive(v_snd_235_);
if (v_isSharedCheck_296_ == 0)
{
lean_object* v_unused_297_; lean_object* v_unused_298_; 
v_unused_297_ = lean_ctor_get(v_snd_235_, 1);
lean_dec(v_unused_297_);
v_unused_298_ = lean_ctor_get(v_snd_235_, 0);
lean_dec(v_unused_298_);
v___x_262_ = v_snd_235_;
v_isShared_263_ = v_isSharedCheck_296_;
goto v_resetjp_261_;
}
else
{
lean_dec(v_snd_235_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_296_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___x_264_; 
lean_inc(v___y_231_);
lean_inc_ref(v___y_230_);
lean_inc(v___y_229_);
lean_inc_ref(v___y_228_);
lean_inc(v___x_249_);
v___x_264_ = lean_infer_type(v___x_249_, v___y_228_, v___y_229_, v___y_230_, v___y_231_);
if (lean_obj_tag(v___x_264_) == 0)
{
lean_object* v_a_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v_a_265_ = lean_ctor_get(v___x_264_, 0);
lean_inc(v_a_265_);
lean_dec_ref(v___x_264_);
v___x_266_ = lean_st_mk_ref(v_snd_236_);
v___x_267_ = l_Lean_Expr_collectFVars(v_a_265_, v___x_266_, v___y_228_, v___y_229_, v___y_230_, v___y_231_);
if (lean_obj_tag(v___x_267_) == 0)
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_271_; 
lean_dec_ref(v___x_267_);
v___x_268_ = lean_st_ref_get(v___x_266_);
lean_dec(v___x_266_);
lean_inc(v___x_249_);
v___x_269_ = lean_array_push(v_fst_245_, v___x_249_);
if (v_isShared_263_ == 0)
{
lean_ctor_set(v___x_262_, 1, v___x_268_);
lean_ctor_set(v___x_262_, 0, v___x_269_);
v___x_271_ = v___x_262_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v___x_269_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v___x_268_);
v___x_271_ = v_reuseFailAlloc_279_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
lean_object* v___x_273_; 
if (v_isShared_244_ == 0)
{
lean_ctor_set(v___x_243_, 1, v___x_271_);
v___x_273_ = v___x_243_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v_fst_241_);
lean_ctor_set(v_reuseFailAlloc_278_, 1, v___x_271_);
v___x_273_ = v_reuseFailAlloc_278_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
lean_object* v___x_275_; 
if (v_isShared_240_ == 0)
{
lean_ctor_set(v___x_239_, 1, v___x_273_);
v___x_275_ = v___x_239_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v_fst_237_);
lean_ctor_set(v_reuseFailAlloc_277_, 1, v___x_273_);
v___x_275_ = v_reuseFailAlloc_277_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
v_i_225_ = v___x_248_;
v_b_227_ = v___x_275_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_287_; 
lean_dec(v___x_266_);
lean_del_object(v___x_262_);
lean_dec(v_fst_245_);
lean_del_object(v___x_243_);
lean_dec(v_fst_241_);
lean_del_object(v___x_239_);
lean_dec(v_fst_237_);
lean_dec(v___y_231_);
lean_dec_ref(v___y_230_);
lean_dec(v___y_229_);
lean_dec_ref(v___y_228_);
v_a_280_ = lean_ctor_get(v___x_267_, 0);
v_isSharedCheck_287_ = !lean_is_exclusive(v___x_267_);
if (v_isSharedCheck_287_ == 0)
{
v___x_282_ = v___x_267_;
v_isShared_283_ = v_isSharedCheck_287_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_a_280_);
lean_dec(v___x_267_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_287_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___x_285_; 
if (v_isShared_283_ == 0)
{
v___x_285_ = v___x_282_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v_a_280_);
v___x_285_ = v_reuseFailAlloc_286_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
return v___x_285_;
}
}
}
}
else
{
lean_object* v_a_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_295_; 
lean_del_object(v___x_262_);
lean_dec(v_fst_245_);
lean_del_object(v___x_243_);
lean_dec(v_fst_241_);
lean_del_object(v___x_239_);
lean_dec(v_fst_237_);
lean_dec(v_snd_236_);
lean_dec(v___y_231_);
lean_dec_ref(v___y_230_);
lean_dec(v___y_229_);
lean_dec_ref(v___y_228_);
v_a_288_ = lean_ctor_get(v___x_264_, 0);
v_isSharedCheck_295_ = !lean_is_exclusive(v___x_264_);
if (v_isSharedCheck_295_ == 0)
{
v___x_290_ = v___x_264_;
v_isShared_291_ = v_isSharedCheck_295_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_a_288_);
lean_dec(v___x_264_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_295_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v___x_293_; 
if (v_isShared_291_ == 0)
{
v___x_293_ = v___x_290_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v_a_288_);
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
}
}
}
}
else
{
lean_object* v___x_303_; 
lean_dec(v___y_231_);
lean_dec_ref(v___y_230_);
lean_dec(v___y_229_);
lean_dec_ref(v___y_228_);
v___x_303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_303_, 0, v_b_227_);
return v___x_303_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_removeUnused_spec__1___boxed(lean_object* v_as_304_, lean_object* v_i_305_, lean_object* v_stop_306_, lean_object* v_b_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_){
_start:
{
size_t v_i_boxed_313_; size_t v_stop_boxed_314_; lean_object* v_res_315_; 
v_i_boxed_313_ = lean_unbox_usize(v_i_305_);
lean_dec(v_i_305_);
v_stop_boxed_314_ = lean_unbox_usize(v_stop_306_);
lean_dec(v_stop_306_);
v_res_315_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_removeUnused_spec__1(v_as_304_, v_i_boxed_313_, v_stop_boxed_314_, v_b_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_);
lean_dec_ref(v_as_304_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_removeUnused(lean_object* v_vars_318_, lean_object* v_used_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_){
_start:
{
lean_object* v_fst_326_; lean_object* v_fst_327_; lean_object* v_fst_328_; lean_object* v___x_333_; 
v___x_333_ = l_Lean_Meta_getLocalInstances___redArg(v_a_320_);
if (lean_obj_tag(v___x_333_) == 0)
{
lean_object* v_a_334_; lean_object* v_lctx_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; uint8_t v___x_339_; 
v_a_334_ = lean_ctor_get(v___x_333_, 0);
lean_inc(v_a_334_);
lean_dec_ref(v___x_333_);
v_lctx_335_ = lean_ctor_get(v_a_320_, 2);
v___x_336_ = lean_unsigned_to_nat(0u);
v___x_337_ = ((lean_object*)(l_Lean_Meta_removeUnused___closed__0));
v___x_338_ = lean_array_get_size(v_vars_318_);
v___x_339_ = lean_nat_dec_lt(v___x_336_, v___x_338_);
if (v___x_339_ == 0)
{
lean_inc_ref(v_lctx_335_);
lean_dec(v_a_323_);
lean_dec_ref(v_a_322_);
lean_dec(v_a_321_);
lean_dec_ref(v_a_320_);
lean_dec_ref(v_used_319_);
v_fst_326_ = v_lctx_335_;
v_fst_327_ = v_a_334_;
v_fst_328_ = v___x_337_;
goto v___jp_325_;
}
else
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; size_t v___x_343_; size_t v___x_344_; lean_object* v___x_345_; 
v___x_340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_340_, 0, v___x_337_);
lean_ctor_set(v___x_340_, 1, v_used_319_);
v___x_341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_341_, 0, v_a_334_);
lean_ctor_set(v___x_341_, 1, v___x_340_);
lean_inc_ref(v_lctx_335_);
v___x_342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_342_, 0, v_lctx_335_);
lean_ctor_set(v___x_342_, 1, v___x_341_);
v___x_343_ = lean_usize_of_nat(v___x_338_);
v___x_344_ = ((size_t)0ULL);
v___x_345_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_removeUnused_spec__1(v_vars_318_, v___x_343_, v___x_344_, v___x_342_, v_a_320_, v_a_321_, v_a_322_, v_a_323_);
if (lean_obj_tag(v___x_345_) == 0)
{
lean_object* v_a_346_; lean_object* v_snd_347_; lean_object* v_snd_348_; lean_object* v_fst_349_; lean_object* v_fst_350_; lean_object* v_fst_351_; 
v_a_346_ = lean_ctor_get(v___x_345_, 0);
lean_inc(v_a_346_);
lean_dec_ref(v___x_345_);
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
v_fst_326_ = v_fst_349_;
v_fst_327_ = v_fst_350_;
v_fst_328_ = v_fst_351_;
goto v___jp_325_;
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
}
else
{
lean_object* v_a_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_367_; 
lean_dec(v_a_323_);
lean_dec_ref(v_a_322_);
lean_dec(v_a_321_);
lean_dec_ref(v_a_320_);
lean_dec_ref(v_used_319_);
v_a_360_ = lean_ctor_get(v___x_333_, 0);
v_isSharedCheck_367_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_367_ == 0)
{
v___x_362_ = v___x_333_;
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_a_360_);
lean_dec(v___x_333_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_365_; 
if (v_isShared_363_ == 0)
{
v___x_365_ = v___x_362_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_a_360_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
}
v___jp_325_:
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_329_ = l_Array_reverse___redArg(v_fst_328_);
v___x_330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_330_, 0, v_fst_327_);
lean_ctor_set(v___x_330_, 1, v___x_329_);
v___x_331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_331_, 0, v_fst_326_);
lean_ctor_set(v___x_331_, 1, v___x_330_);
v___x_332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_332_, 0, v___x_331_);
return v___x_332_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_removeUnused___boxed(lean_object* v_vars_368_, lean_object* v_used_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l_Lean_Meta_removeUnused(v_vars_368_, v_used_369_, v_a_370_, v_a_371_, v_a_372_, v_a_373_);
lean_dec_ref(v_vars_368_);
return v_res_375_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_removeUnused_spec__0(lean_object* v_00_u03b2_376_, lean_object* v_k_377_, lean_object* v_t_378_){
_start:
{
uint8_t v___x_379_; 
v___x_379_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_removeUnused_spec__0___redArg(v_k_377_, v_t_378_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_removeUnused_spec__0___boxed(lean_object* v_00_u03b2_380_, lean_object* v_k_381_, lean_object* v_t_382_){
_start:
{
uint8_t v_res_383_; lean_object* v_r_384_; 
v_res_383_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_removeUnused_spec__0(v_00_u03b2_380_, v_k_381_, v_t_382_);
lean_dec(v_t_382_);
lean_dec(v_k_381_);
v_r_384_ = lean_box(v_res_383_);
return v_r_384_;
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

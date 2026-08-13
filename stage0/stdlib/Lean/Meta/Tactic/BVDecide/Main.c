// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Main
// Imports: public import Lean.Meta.Tactic.BVDecide.Prover.Bitblast public import Lean.Meta.Tactic.BVDecide.Normalize import Lean.Meta.Sym.Util
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_M_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_TacticContext_preProcessContext(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_TacticContext_preProcessContext___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Main_0__Lean_Meta_Tactic_BVDecide_bvUnsat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Main_0__Lean_Meta_Tactic_BVDecide_bvUnsat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__1;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__2;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__3;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__4;
static const lean_array_object l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__6 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_bvDecide_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_bvDecide___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_bvDecide___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_bvDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_bvDecide___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_TacticContext_preProcessContext(lean_object* v_ctx_1_){
_start:
{
lean_object* v_config_2_; lean_object* v_restrictedTypes_3_; lean_object* v___x_4_; 
v_config_2_ = lean_ctor_get(v_ctx_1_, 5);
v_restrictedTypes_3_ = lean_ctor_get(v_ctx_1_, 6);
lean_inc(v_restrictedTypes_3_);
lean_inc_ref(v_config_2_);
v___x_4_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4_, 0, v_config_2_);
lean_ctor_set(v___x_4_, 1, v_restrictedTypes_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_TacticContext_preProcessContext___boxed(lean_object* v_ctx_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l_Lean_Meta_Tactic_BVDecide_TacticContext_preProcessContext(v_ctx_5_);
lean_dec_ref(v_ctx_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Main_0__Lean_Meta_Tactic_BVDecide_bvUnsat(lean_object* v_g_7_, lean_object* v_hypotheses_8_, lean_object* v_ctx_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_, lean_object* v_a_13_, lean_object* v_a_14_, lean_object* v_a_15_){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_17_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___boxed), 9, 1);
lean_closure_set(v___x_17_, 0, v_ctx_9_);
v___x_18_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___boxed), 12, 3);
lean_closure_set(v___x_18_, 0, lean_box(0));
lean_closure_set(v___x_18_, 1, v_g_7_);
lean_closure_set(v___x_18_, 2, v___x_17_);
v___x_19_ = l_Lean_Meta_Tactic_BVDecide_M_run___redArg(v___x_18_, v_hypotheses_8_, v_a_10_, v_a_11_, v_a_12_, v_a_13_, v_a_14_, v_a_15_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Main_0__Lean_Meta_Tactic_BVDecide_bvUnsat___boxed(lean_object* v_g_20_, lean_object* v_hypotheses_21_, lean_object* v_ctx_22_, lean_object* v_a_23_, lean_object* v_a_24_, lean_object* v_a_25_, lean_object* v_a_26_, lean_object* v_a_27_, lean_object* v_a_28_, lean_object* v_a_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l___private_Lean_Meta_Tactic_BVDecide_Main_0__Lean_Meta_Tactic_BVDecide_bvUnsat(v_g_20_, v_hypotheses_21_, v_ctx_22_, v_a_23_, v_a_24_, v_a_25_, v_a_26_, v_a_27_, v_a_28_);
lean_dec(v_a_28_);
lean_dec_ref(v_a_27_);
lean_dec(v_a_26_);
lean_dec_ref(v_a_25_);
lean_dec(v_a_24_);
lean_dec_ref(v_a_23_);
return v_res_30_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__0(void){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_31_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__1(void){
_start:
{
lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_32_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__0, &l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__0);
v___x_33_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_33_, 0, v___x_32_);
return v___x_33_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__2(void){
_start:
{
lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_34_ = lean_box(0);
v___x_35_ = lean_unsigned_to_nat(16u);
v___x_36_ = lean_mk_array(v___x_35_, v___x_34_);
return v___x_36_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__3(void){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_37_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__2, &l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__2);
v___x_38_ = lean_unsigned_to_nat(0u);
v___x_39_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_39_, 0, v___x_38_);
lean_ctor_set(v___x_39_, 1, v___x_37_);
return v___x_39_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__4(void){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_40_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__3, &l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__3);
v___x_41_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_41_, 0, v___x_40_);
lean_ctor_set(v___x_41_, 1, v___x_40_);
lean_ctor_set(v___x_41_, 2, v___x_40_);
lean_ctor_set(v___x_41_, 3, v___x_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_bvDecide_x27(lean_object* v_target_46_, lean_object* v_ctx_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; uint8_t v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v_a_65_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_58_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__1, &l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__1);
v___x_59_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__4, &l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__4);
v___x_60_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__5));
v___x_61_ = 0;
v___x_62_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_62_, 0, v___x_58_);
lean_ctor_set(v___x_62_, 1, v___x_58_);
lean_ctor_set(v___x_62_, 2, v___x_58_);
lean_ctor_set(v___x_62_, 3, v___x_59_);
lean_ctor_set(v___x_62_, 4, v_target_46_);
lean_ctor_set(v___x_62_, 5, v___x_60_);
lean_ctor_set_uint8(v___x_62_, sizeof(void*)*6, v___x_61_);
v___x_63_ = lean_st_mk_ref(v___x_62_);
v___x_68_ = l_Lean_Meta_Tactic_BVDecide_TacticContext_preProcessContext(v_ctx_47_);
v___x_69_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(v___x_68_, v___x_63_, v_a_48_, v_a_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_, v_a_56_);
lean_dec_ref(v___x_68_);
if (lean_obj_tag(v___x_69_) == 0)
{
lean_object* v_a_70_; uint8_t v___x_71_; 
v_a_70_ = lean_ctor_get(v___x_69_, 0);
lean_inc(v_a_70_);
lean_dec_ref_known(v___x_69_, 1);
v___x_71_ = lean_unbox(v_a_70_);
lean_dec(v_a_70_);
if (v___x_71_ == 0)
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v_target_74_; lean_object* v_hypotheses_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_72_ = lean_st_ref_get(v___x_63_);
v___x_73_ = lean_st_ref_get(v___x_63_);
v_target_74_ = lean_ctor_get(v___x_72_, 4);
lean_inc_ref(v_target_74_);
lean_dec(v___x_72_);
v_hypotheses_75_ = lean_ctor_get(v___x_73_, 5);
lean_inc_ref(v_hypotheses_75_);
lean_dec(v___x_73_);
v___x_76_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_74_);
lean_dec_ref(v_target_74_);
v___x_77_ = l___private_Lean_Meta_Tactic_BVDecide_Main_0__Lean_Meta_Tactic_BVDecide_bvUnsat(v___x_76_, v_hypotheses_75_, v_ctx_47_, v_a_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_, v_a_56_);
if (lean_obj_tag(v___x_77_) == 0)
{
lean_object* v_a_78_; 
v_a_78_ = lean_ctor_get(v___x_77_, 0);
lean_inc(v_a_78_);
lean_dec_ref_known(v___x_77_, 1);
if (lean_obj_tag(v_a_78_) == 0)
{
lean_object* v_a_79_; lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_86_; 
v_a_79_ = lean_ctor_get(v_a_78_, 0);
v_isSharedCheck_86_ = !lean_is_exclusive(v_a_78_);
if (v_isSharedCheck_86_ == 0)
{
v___x_81_ = v_a_78_;
v_isShared_82_ = v_isSharedCheck_86_;
goto v_resetjp_80_;
}
else
{
lean_inc(v_a_79_);
lean_dec(v_a_78_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_86_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
lean_object* v___x_84_; 
if (v_isShared_82_ == 0)
{
v___x_84_ = v___x_81_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v_a_79_);
v___x_84_ = v_reuseFailAlloc_85_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
v_a_65_ = v___x_84_;
goto v___jp_64_;
}
}
}
else
{
lean_object* v_a_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_95_; 
v_a_87_ = lean_ctor_get(v_a_78_, 0);
v_isSharedCheck_95_ = !lean_is_exclusive(v_a_78_);
if (v_isSharedCheck_95_ == 0)
{
v___x_89_ = v_a_78_;
v_isShared_90_ = v_isSharedCheck_95_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_a_87_);
lean_dec(v_a_78_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_95_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v___x_91_; lean_object* v___x_93_; 
v___x_91_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_91_, 0, v_a_87_);
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 0, v___x_91_);
v___x_93_ = v___x_89_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v___x_91_);
v___x_93_ = v_reuseFailAlloc_94_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
v_a_65_ = v___x_93_;
goto v___jp_64_;
}
}
}
}
else
{
lean_object* v_a_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_103_; 
lean_dec(v___x_63_);
v_a_96_ = lean_ctor_get(v___x_77_, 0);
v_isSharedCheck_103_ = !lean_is_exclusive(v___x_77_);
if (v_isSharedCheck_103_ == 0)
{
v___x_98_ = v___x_77_;
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_a_96_);
lean_dec(v___x_77_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v___x_101_; 
if (v_isShared_99_ == 0)
{
v___x_101_ = v___x_98_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v_a_96_);
v___x_101_ = v_reuseFailAlloc_102_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
return v___x_101_;
}
}
}
}
else
{
lean_object* v___x_104_; 
lean_dec_ref(v_ctx_47_);
v___x_104_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__6));
v_a_65_ = v___x_104_;
goto v___jp_64_;
}
}
else
{
lean_object* v_a_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_112_; 
lean_dec(v___x_63_);
lean_dec_ref(v_ctx_47_);
v_a_105_ = lean_ctor_get(v___x_69_, 0);
v_isSharedCheck_112_ = !lean_is_exclusive(v___x_69_);
if (v_isSharedCheck_112_ == 0)
{
v___x_107_ = v___x_69_;
v_isShared_108_ = v_isSharedCheck_112_;
goto v_resetjp_106_;
}
else
{
lean_inc(v_a_105_);
lean_dec(v___x_69_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_112_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v___x_110_; 
if (v_isShared_108_ == 0)
{
v___x_110_ = v___x_107_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v_a_105_);
v___x_110_ = v_reuseFailAlloc_111_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
return v___x_110_;
}
}
}
v___jp_64_:
{
lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_66_ = lean_st_ref_get(v___x_63_);
lean_dec(v___x_63_);
lean_dec(v___x_66_);
v___x_67_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_67_, 0, v_a_65_);
return v___x_67_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___boxed(lean_object* v_target_113_, lean_object* v_ctx_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Lean_Meta_Tactic_BVDecide_bvDecide_x27(v_target_113_, v_ctx_114_, v_a_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_);
lean_dec(v_a_123_);
lean_dec_ref(v_a_122_);
lean_dec(v_a_121_);
lean_dec_ref(v_a_120_);
lean_dec(v_a_119_);
lean_dec_ref(v_a_118_);
lean_dec(v_a_117_);
lean_dec_ref(v_a_116_);
lean_dec(v_a_115_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__0___redArg(lean_object* v_msgData_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_){
_start:
{
lean_object* v___x_132_; lean_object* v_env_133_; lean_object* v___x_134_; lean_object* v_mctx_135_; lean_object* v_lctx_136_; lean_object* v_options_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_132_ = lean_st_ref_get(v___y_130_);
v_env_133_ = lean_ctor_get(v___x_132_, 0);
lean_inc_ref(v_env_133_);
lean_dec(v___x_132_);
v___x_134_ = lean_st_ref_get(v___y_128_);
v_mctx_135_ = lean_ctor_get(v___x_134_, 0);
lean_inc_ref(v_mctx_135_);
lean_dec(v___x_134_);
v_lctx_136_ = lean_ctor_get(v___y_127_, 2);
v_options_137_ = lean_ctor_get(v___y_129_, 2);
lean_inc_ref(v_options_137_);
lean_inc_ref(v_lctx_136_);
v___x_138_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_138_, 0, v_env_133_);
lean_ctor_set(v___x_138_, 1, v_mctx_135_);
lean_ctor_set(v___x_138_, 2, v_lctx_136_);
lean_ctor_set(v___x_138_, 3, v_options_137_);
v___x_139_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_139_, 0, v___x_138_);
lean_ctor_set(v___x_139_, 1, v_msgData_126_);
v___x_140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_140_, 0, v___x_139_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__0___redArg___boxed(lean_object* v_msgData_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__0___redArg(v_msgData_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_);
lean_dec(v___y_145_);
lean_dec_ref(v___y_144_);
lean_dec(v___y_143_);
lean_dec_ref(v___y_142_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__0(lean_object* v_msgData_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__0___redArg(v_msgData_148_, v___y_154_, v___y_155_, v___y_156_, v___y_157_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__0___boxed(lean_object* v_msgData_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__0(v_msgData_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_);
lean_dec(v___y_169_);
lean_dec_ref(v___y_168_);
lean_dec(v___y_167_);
lean_dec_ref(v___y_166_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
lean_dec(v___y_161_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2___redArg___lam__0(lean_object* v_x_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_){
_start:
{
lean_object* v___x_183_; 
lean_inc(v___y_177_);
lean_inc_ref(v___y_176_);
lean_inc(v___y_175_);
lean_inc_ref(v___y_174_);
lean_inc(v___y_173_);
v___x_183_ = lean_apply_10(v_x_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_, lean_box(0));
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2___redArg___lam__0___boxed(lean_object* v_x_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2___redArg___lam__0(v_x_184_, v___y_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_);
lean_dec(v___y_189_);
lean_dec_ref(v___y_188_);
lean_dec(v___y_187_);
lean_dec_ref(v___y_186_);
lean_dec(v___y_185_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2___redArg(lean_object* v_mvarId_196_, lean_object* v_x_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_){
_start:
{
lean_object* v___f_208_; lean_object* v___x_209_; 
lean_inc(v___y_202_);
lean_inc_ref(v___y_201_);
lean_inc(v___y_200_);
lean_inc_ref(v___y_199_);
lean_inc(v___y_198_);
v___f_208_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_208_, 0, v_x_197_);
lean_closure_set(v___f_208_, 1, v___y_198_);
lean_closure_set(v___f_208_, 2, v___y_199_);
lean_closure_set(v___f_208_, 3, v___y_200_);
lean_closure_set(v___f_208_, 4, v___y_201_);
lean_closure_set(v___f_208_, 5, v___y_202_);
v___x_209_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_196_, v___f_208_, v___y_203_, v___y_204_, v___y_205_, v___y_206_);
if (lean_obj_tag(v___x_209_) == 0)
{
return v___x_209_;
}
else
{
lean_object* v_a_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_217_; 
v_a_210_ = lean_ctor_get(v___x_209_, 0);
v_isSharedCheck_217_ = !lean_is_exclusive(v___x_209_);
if (v_isSharedCheck_217_ == 0)
{
v___x_212_ = v___x_209_;
v_isShared_213_ = v_isSharedCheck_217_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_a_210_);
lean_dec(v___x_209_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_217_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___x_215_; 
if (v_isShared_213_ == 0)
{
v___x_215_ = v___x_212_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v_a_210_);
v___x_215_ = v_reuseFailAlloc_216_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
return v___x_215_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2___redArg___boxed(lean_object* v_mvarId_218_, lean_object* v_x_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2___redArg(v_mvarId_218_, v_x_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_, v___y_228_);
lean_dec(v___y_228_);
lean_dec_ref(v___y_227_);
lean_dec(v___y_226_);
lean_dec_ref(v___y_225_);
lean_dec(v___y_224_);
lean_dec_ref(v___y_223_);
lean_dec(v___y_222_);
lean_dec_ref(v___y_221_);
lean_dec(v___y_220_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2(lean_object* v_00_u03b1_231_, lean_object* v_mvarId_232_, lean_object* v_x_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2___redArg(v_mvarId_232_, v_x_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2___boxed(lean_object* v_00_u03b1_245_, lean_object* v_mvarId_246_, lean_object* v_x_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2(v_00_u03b1_245_, v_mvarId_246_, v_x_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_);
lean_dec(v___y_256_);
lean_dec_ref(v___y_255_);
lean_dec(v___y_254_);
lean_dec_ref(v___y_253_);
lean_dec(v___y_252_);
lean_dec_ref(v___y_251_);
lean_dec(v___y_250_);
lean_dec_ref(v___y_249_);
lean_dec(v___y_248_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1_spec__1(lean_object* v_msgData_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_){
_start:
{
lean_object* v___x_265_; lean_object* v_env_266_; lean_object* v___x_267_; lean_object* v_mctx_268_; lean_object* v_lctx_269_; lean_object* v_options_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_265_ = lean_st_ref_get(v___y_263_);
v_env_266_ = lean_ctor_get(v___x_265_, 0);
lean_inc_ref(v_env_266_);
lean_dec(v___x_265_);
v___x_267_ = lean_st_ref_get(v___y_261_);
v_mctx_268_ = lean_ctor_get(v___x_267_, 0);
lean_inc_ref(v_mctx_268_);
lean_dec(v___x_267_);
v_lctx_269_ = lean_ctor_get(v___y_260_, 2);
v_options_270_ = lean_ctor_get(v___y_262_, 2);
lean_inc_ref(v_options_270_);
lean_inc_ref(v_lctx_269_);
v___x_271_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_271_, 0, v_env_266_);
lean_ctor_set(v___x_271_, 1, v_mctx_268_);
lean_ctor_set(v___x_271_, 2, v_lctx_269_);
lean_ctor_set(v___x_271_, 3, v_options_270_);
v___x_272_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_272_, 0, v___x_271_);
lean_ctor_set(v___x_272_, 1, v_msgData_259_);
v___x_273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_273_, 0, v___x_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1_spec__1___boxed(lean_object* v_msgData_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1_spec__1(v_msgData_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_);
lean_dec(v___y_278_);
lean_dec_ref(v___y_277_);
lean_dec(v___y_276_);
lean_dec_ref(v___y_275_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1___redArg(lean_object* v_msg_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_){
_start:
{
lean_object* v_ref_287_; lean_object* v___x_288_; lean_object* v_a_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_297_; 
v_ref_287_ = lean_ctor_get(v___y_284_, 5);
v___x_288_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1_spec__1(v_msg_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_);
v_a_289_ = lean_ctor_get(v___x_288_, 0);
v_isSharedCheck_297_ = !lean_is_exclusive(v___x_288_);
if (v_isSharedCheck_297_ == 0)
{
v___x_291_ = v___x_288_;
v_isShared_292_ = v_isSharedCheck_297_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_a_289_);
lean_dec(v___x_288_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_297_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_293_; lean_object* v___x_295_; 
lean_inc(v_ref_287_);
v___x_293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_293_, 0, v_ref_287_);
lean_ctor_set(v___x_293_, 1, v_a_289_);
if (v_isShared_292_ == 0)
{
lean_ctor_set_tag(v___x_291_, 1);
lean_ctor_set(v___x_291_, 0, v___x_293_);
v___x_295_ = v___x_291_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v___x_293_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1___redArg___boxed(lean_object* v_msg_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1___redArg(v_msg_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
lean_dec(v___y_300_);
lean_dec_ref(v___y_299_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_bvDecide___lam__0(lean_object* v_a_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_){
_start:
{
lean_object* v___x_316_; 
v___x_316_ = l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality(v_a_305_, v___y_311_, v___y_312_, v___y_313_, v___y_314_);
if (lean_obj_tag(v___x_316_) == 0)
{
lean_object* v_a_317_; lean_object* v___x_318_; lean_object* v_a_319_; lean_object* v___x_320_; 
v_a_317_ = lean_ctor_get(v___x_316_, 0);
lean_inc(v_a_317_);
lean_dec_ref_known(v___x_316_, 1);
v___x_318_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__0___redArg(v_a_317_, v___y_311_, v___y_312_, v___y_313_, v___y_314_);
v_a_319_ = lean_ctor_get(v___x_318_, 0);
lean_inc(v_a_319_);
lean_dec_ref(v___x_318_);
v___x_320_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1___redArg(v_a_319_, v___y_311_, v___y_312_, v___y_313_, v___y_314_);
return v___x_320_;
}
else
{
lean_object* v_a_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_328_; 
v_a_321_ = lean_ctor_get(v___x_316_, 0);
v_isSharedCheck_328_ = !lean_is_exclusive(v___x_316_);
if (v_isSharedCheck_328_ == 0)
{
v___x_323_ = v___x_316_;
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_a_321_);
lean_dec(v___x_316_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_326_; 
if (v_isShared_324_ == 0)
{
v___x_326_ = v___x_323_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_a_321_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
return v___x_326_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_bvDecide___lam__0___boxed(lean_object* v_a_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_Lean_Meta_Tactic_BVDecide_bvDecide___lam__0(v_a_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_);
lean_dec(v___y_338_);
lean_dec_ref(v___y_337_);
lean_dec(v___y_336_);
lean_dec_ref(v___y_335_);
lean_dec(v___y_334_);
lean_dec_ref(v___y_333_);
lean_dec(v___y_332_);
lean_dec_ref(v___y_331_);
lean_dec(v___y_330_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_bvDecide(lean_object* v_target_341_, lean_object* v_ctx_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_){
_start:
{
lean_object* v___x_353_; 
v___x_353_ = l_Lean_Meta_Tactic_BVDecide_bvDecide_x27(v_target_341_, v_ctx_342_, v_a_343_, v_a_344_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_);
if (lean_obj_tag(v___x_353_) == 0)
{
lean_object* v_a_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_366_; 
v_a_354_ = lean_ctor_get(v___x_353_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_353_);
if (v_isSharedCheck_366_ == 0)
{
v___x_356_ = v___x_353_;
v_isShared_357_ = v_isSharedCheck_366_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_a_354_);
lean_dec(v___x_353_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_366_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
if (lean_obj_tag(v_a_354_) == 0)
{
lean_object* v_a_358_; lean_object* v_goal_359_; lean_object* v___f_360_; lean_object* v___x_361_; 
lean_del_object(v___x_356_);
v_a_358_ = lean_ctor_get(v_a_354_, 0);
lean_inc(v_a_358_);
lean_dec_ref_known(v_a_354_, 1);
v_goal_359_ = lean_ctor_get(v_a_358_, 0);
lean_inc(v_goal_359_);
v___f_360_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_bvDecide___lam__0___boxed), 11, 1);
lean_closure_set(v___f_360_, 0, v_a_358_);
v___x_361_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2___redArg(v_goal_359_, v___f_360_, v_a_343_, v_a_344_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_);
return v___x_361_;
}
else
{
lean_object* v_a_362_; lean_object* v___x_364_; 
v_a_362_ = lean_ctor_get(v_a_354_, 0);
lean_inc(v_a_362_);
lean_dec_ref_known(v_a_354_, 1);
if (v_isShared_357_ == 0)
{
lean_ctor_set(v___x_356_, 0, v_a_362_);
v___x_364_ = v___x_356_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_a_362_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
}
else
{
lean_object* v_a_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_374_; 
v_a_367_ = lean_ctor_get(v___x_353_, 0);
v_isSharedCheck_374_ = !lean_is_exclusive(v___x_353_);
if (v_isSharedCheck_374_ == 0)
{
v___x_369_ = v___x_353_;
v_isShared_370_ = v_isSharedCheck_374_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_a_367_);
lean_dec(v___x_353_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_374_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_372_; 
if (v_isShared_370_ == 0)
{
v___x_372_ = v___x_369_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_a_367_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_bvDecide___boxed(lean_object* v_target_375_, lean_object* v_ctx_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Lean_Meta_Tactic_BVDecide_bvDecide(v_target_375_, v_ctx_376_, v_a_377_, v_a_378_, v_a_379_, v_a_380_, v_a_381_, v_a_382_, v_a_383_, v_a_384_, v_a_385_);
lean_dec(v_a_385_);
lean_dec_ref(v_a_384_);
lean_dec(v_a_383_);
lean_dec_ref(v_a_382_);
lean_dec(v_a_381_);
lean_dec_ref(v_a_380_);
lean_dec(v_a_379_);
lean_dec_ref(v_a_378_);
lean_dec(v_a_377_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1(lean_object* v_00_u03b1_388_, lean_object* v_msg_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1___redArg(v_msg_389_, v___y_395_, v___y_396_, v___y_397_, v___y_398_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1___boxed(lean_object* v_00_u03b1_401_, lean_object* v_msg_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1(v_00_u03b1_401_, v_msg_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_);
lean_dec(v___y_411_);
lean_dec_ref(v___y_410_);
lean_dec(v___y_409_);
lean_dec_ref(v___y_408_);
lean_dec(v___y_407_);
lean_dec_ref(v___y_406_);
lean_dec(v___y_405_);
lean_dec_ref(v___y_404_);
lean_dec(v___y_403_);
return v_res_413_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Bitblast(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Util(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Main(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Bitblast(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_BVDecide_Main(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Prover_Bitblast(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Util(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_BVDecide_Main(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_BVDecide_Prover_Bitblast(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Normalize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_BVDecide_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_BVDecide_Main(builtin);
}
#ifdef __cplusplus
}
#endif

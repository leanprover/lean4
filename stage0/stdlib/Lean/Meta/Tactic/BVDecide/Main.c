// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Main
// Imports: public import Lean.Meta.Tactic.BVDecide.Prover.Bitblast public import Lean.Meta.Tactic.BVDecide.Prover.Cegar public import Lean.Meta.Tactic.BVDecide.Normalize import Lean.Meta.Sym.Util
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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Meta_Tactic_BVDecide_TacticContext_preProcessContext(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_cegarBlaster___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Tactic_BVDecide_CegarCert_solvedWithPreProcessing;
lean_object* l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Main_0__Lean_Meta_Tactic_BVDecide_bvUnsat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Main_0__Lean_Meta_Tactic_BVDecide_bvUnsat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__5;
static const lean_array_object l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__6 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__7;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Main_0__Lean_Meta_Tactic_BVDecide_bvUnsat(lean_object* v_g_1_, lean_object* v_hypotheses_2_, lean_object* v_ctx_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_){
_start:
{
lean_object* v_config_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
v_config_14_ = lean_ctor_get(v_ctx_3_, 5);
lean_inc_ref(v_config_14_);
v___x_15_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_cegarBlaster___boxed), 16, 1);
lean_closure_set(v___x_15_, 0, v_ctx_3_);
v___x_16_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___boxed), 15, 3);
lean_closure_set(v___x_16_, 0, lean_box(0));
lean_closure_set(v___x_16_, 1, v_g_1_);
lean_closure_set(v___x_16_, 2, v___x_15_);
v___x_17_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg(v___x_16_, v_hypotheses_2_, v_config_14_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Main_0__Lean_Meta_Tactic_BVDecide_bvUnsat___boxed(lean_object* v_g_18_, lean_object* v_hypotheses_19_, lean_object* v_ctx_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_, lean_object* v_a_25_, lean_object* v_a_26_, lean_object* v_a_27_, lean_object* v_a_28_, lean_object* v_a_29_, lean_object* v_a_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l___private_Lean_Meta_Tactic_BVDecide_Main_0__Lean_Meta_Tactic_BVDecide_bvUnsat(v_g_18_, v_hypotheses_19_, v_ctx_20_, v_a_21_, v_a_22_, v_a_23_, v_a_24_, v_a_25_, v_a_26_, v_a_27_, v_a_28_, v_a_29_);
lean_dec(v_a_29_);
lean_dec_ref(v_a_28_);
lean_dec(v_a_27_);
lean_dec_ref(v_a_26_);
lean_dec(v_a_25_);
lean_dec_ref(v_a_24_);
lean_dec(v_a_23_);
lean_dec_ref(v_a_22_);
lean_dec(v_a_21_);
return v_res_31_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__0(void){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_32_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__1(void){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_33_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__0, &l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__0);
v___x_34_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_34_, 0, v___x_33_);
return v___x_34_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__2(void){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_35_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__1, &l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__1);
v___x_36_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_36_, 0, v___x_35_);
lean_ctor_set(v___x_36_, 1, v___x_35_);
lean_ctor_set(v___x_36_, 2, v___x_35_);
lean_ctor_set(v___x_36_, 3, v___x_35_);
return v___x_36_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__3(void){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_37_ = lean_box(0);
v___x_38_ = lean_unsigned_to_nat(16u);
v___x_39_ = lean_mk_array(v___x_38_, v___x_37_);
return v___x_39_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__4(void){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_40_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__3, &l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__3);
v___x_41_ = lean_unsigned_to_nat(0u);
v___x_42_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_42_, 0, v___x_41_);
lean_ctor_set(v___x_42_, 1, v___x_40_);
return v___x_42_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__5(void){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_43_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__4, &l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__4);
v___x_44_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_44_, 0, v___x_43_);
lean_ctor_set(v___x_44_, 1, v___x_43_);
lean_ctor_set(v___x_44_, 2, v___x_43_);
lean_ctor_set(v___x_44_, 3, v___x_43_);
return v___x_44_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__7(void){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_47_ = l_Lean_Meta_Tactic_BVDecide_CegarCert_solvedWithPreProcessing;
v___x_48_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_48_, 0, v___x_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_bvDecide_x27(lean_object* v_target_49_, lean_object* v_ctx_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; uint8_t v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v_a_70_; lean_object* v___x_73_; 
lean_inc_ref(v_ctx_50_);
v___x_61_ = l_Lean_Meta_Tactic_BVDecide_TacticContext_preProcessContext(v_ctx_50_);
v___x_62_ = lean_box(0);
v___x_63_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__2, &l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__2);
v___x_64_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__5, &l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__5);
v___x_65_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__6));
v___x_66_ = 0;
v___x_67_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_67_, 0, v___x_63_);
lean_ctor_set(v___x_67_, 1, v___x_64_);
lean_ctor_set(v___x_67_, 2, v_target_49_);
lean_ctor_set(v___x_67_, 3, v___x_65_);
lean_ctor_set_uint8(v___x_67_, sizeof(void*)*4, v___x_66_);
v___x_68_ = lean_st_mk_ref(v___x_67_);
v___x_73_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(v___x_62_, v___x_61_, v___x_68_, v_a_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_, v_a_56_, v_a_57_, v_a_58_, v_a_59_);
lean_dec_ref(v___x_61_);
if (lean_obj_tag(v___x_73_) == 0)
{
lean_object* v_a_74_; uint8_t v___x_75_; 
v_a_74_ = lean_ctor_get(v___x_73_, 0);
lean_inc(v_a_74_);
lean_dec_ref_known(v___x_73_, 1);
v___x_75_ = lean_unbox(v_a_74_);
lean_dec(v_a_74_);
if (v___x_75_ == 0)
{
lean_object* v___x_76_; lean_object* v_target_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v_hypotheses_80_; lean_object* v___x_81_; 
v___x_76_ = lean_st_ref_get(v___x_68_);
v_target_77_ = lean_ctor_get(v___x_76_, 2);
lean_inc_ref(v_target_77_);
lean_dec(v___x_76_);
v___x_78_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_77_);
lean_dec_ref(v_target_77_);
v___x_79_ = lean_st_ref_get(v___x_68_);
v_hypotheses_80_ = lean_ctor_get(v___x_79_, 3);
lean_inc_ref(v_hypotheses_80_);
lean_dec(v___x_79_);
v___x_81_ = l___private_Lean_Meta_Tactic_BVDecide_Main_0__Lean_Meta_Tactic_BVDecide_bvUnsat(v___x_78_, v_hypotheses_80_, v_ctx_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_, v_a_56_, v_a_57_, v_a_58_, v_a_59_);
if (lean_obj_tag(v___x_81_) == 0)
{
lean_object* v_a_82_; 
v_a_82_ = lean_ctor_get(v___x_81_, 0);
lean_inc(v_a_82_);
lean_dec_ref_known(v___x_81_, 1);
if (lean_obj_tag(v_a_82_) == 0)
{
lean_object* v_a_83_; lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_90_; 
v_a_83_ = lean_ctor_get(v_a_82_, 0);
v_isSharedCheck_90_ = !lean_is_exclusive(v_a_82_);
if (v_isSharedCheck_90_ == 0)
{
v___x_85_ = v_a_82_;
v_isShared_86_ = v_isSharedCheck_90_;
goto v_resetjp_84_;
}
else
{
lean_inc(v_a_83_);
lean_dec(v_a_82_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_90_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
lean_object* v___x_88_; 
if (v_isShared_86_ == 0)
{
v___x_88_ = v___x_85_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v_a_83_);
v___x_88_ = v_reuseFailAlloc_89_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
v_a_70_ = v___x_88_;
goto v___jp_69_;
}
}
}
else
{
lean_object* v_a_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_98_; 
v_a_91_ = lean_ctor_get(v_a_82_, 0);
v_isSharedCheck_98_ = !lean_is_exclusive(v_a_82_);
if (v_isSharedCheck_98_ == 0)
{
v___x_93_ = v_a_82_;
v_isShared_94_ = v_isSharedCheck_98_;
goto v_resetjp_92_;
}
else
{
lean_inc(v_a_91_);
lean_dec(v_a_82_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_98_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
lean_object* v___x_96_; 
if (v_isShared_94_ == 0)
{
v___x_96_ = v___x_93_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_97_; 
v_reuseFailAlloc_97_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_97_, 0, v_a_91_);
v___x_96_ = v_reuseFailAlloc_97_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
v_a_70_ = v___x_96_;
goto v___jp_69_;
}
}
}
}
else
{
lean_object* v_a_99_; lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_106_; 
lean_dec(v___x_68_);
v_a_99_ = lean_ctor_get(v___x_81_, 0);
v_isSharedCheck_106_ = !lean_is_exclusive(v___x_81_);
if (v_isSharedCheck_106_ == 0)
{
v___x_101_ = v___x_81_;
v_isShared_102_ = v_isSharedCheck_106_;
goto v_resetjp_100_;
}
else
{
lean_inc(v_a_99_);
lean_dec(v___x_81_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_106_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v___x_104_; 
if (v_isShared_102_ == 0)
{
v___x_104_ = v___x_101_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v_a_99_);
v___x_104_ = v_reuseFailAlloc_105_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
return v___x_104_;
}
}
}
}
else
{
lean_object* v___x_107_; 
lean_dec_ref(v_ctx_50_);
v___x_107_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__7, &l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__7);
v_a_70_ = v___x_107_;
goto v___jp_69_;
}
}
else
{
lean_object* v_a_108_; lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_115_; 
lean_dec(v___x_68_);
lean_dec_ref(v_ctx_50_);
v_a_108_ = lean_ctor_get(v___x_73_, 0);
v_isSharedCheck_115_ = !lean_is_exclusive(v___x_73_);
if (v_isSharedCheck_115_ == 0)
{
v___x_110_ = v___x_73_;
v_isShared_111_ = v_isSharedCheck_115_;
goto v_resetjp_109_;
}
else
{
lean_inc(v_a_108_);
lean_dec(v___x_73_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_115_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
lean_object* v___x_113_; 
if (v_isShared_111_ == 0)
{
v___x_113_ = v___x_110_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v_a_108_);
v___x_113_ = v_reuseFailAlloc_114_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
return v___x_113_;
}
}
}
v___jp_69_:
{
lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_71_ = lean_st_ref_get(v___x_68_);
lean_dec(v___x_68_);
lean_dec(v___x_71_);
v___x_72_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_72_, 0, v_a_70_);
return v___x_72_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___boxed(lean_object* v_target_116_, lean_object* v_ctx_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_Lean_Meta_Tactic_BVDecide_bvDecide_x27(v_target_116_, v_ctx_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_, v_a_125_, v_a_126_);
lean_dec(v_a_126_);
lean_dec_ref(v_a_125_);
lean_dec(v_a_124_);
lean_dec_ref(v_a_123_);
lean_dec(v_a_122_);
lean_dec_ref(v_a_121_);
lean_dec(v_a_120_);
lean_dec_ref(v_a_119_);
lean_dec(v_a_118_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__0___redArg(lean_object* v_msgData_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_){
_start:
{
lean_object* v___x_135_; lean_object* v_env_136_; uint8_t v___x_137_; lean_object* v_env_138_; lean_object* v___x_139_; lean_object* v_toCold_140_; lean_object* v_mctx_141_; lean_object* v_lctx_142_; lean_object* v_options_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_135_ = lean_st_ref_get(v___y_133_);
v_env_136_ = lean_ctor_get(v___x_135_, 0);
lean_inc_ref(v_env_136_);
lean_dec(v___x_135_);
v___x_137_ = 0;
v_env_138_ = l_Lean_Environment_setRecordingDeps(v_env_136_, v___x_137_);
v___x_139_ = lean_st_ref_get(v___y_131_);
v_toCold_140_ = lean_ctor_get(v___y_132_, 0);
v_mctx_141_ = lean_ctor_get(v___x_139_, 0);
lean_inc_ref(v_mctx_141_);
lean_dec(v___x_139_);
v_lctx_142_ = lean_ctor_get(v___y_130_, 2);
v_options_143_ = lean_ctor_get(v_toCold_140_, 2);
lean_inc_ref(v_options_143_);
lean_inc_ref(v_lctx_142_);
v___x_144_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_144_, 0, v_env_138_);
lean_ctor_set(v___x_144_, 1, v_mctx_141_);
lean_ctor_set(v___x_144_, 2, v_lctx_142_);
lean_ctor_set(v___x_144_, 3, v_options_143_);
v___x_145_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_145_, 0, v___x_144_);
lean_ctor_set(v___x_145_, 1, v_msgData_129_);
v___x_146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_146_, 0, v___x_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__0___redArg___boxed(lean_object* v_msgData_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__0___redArg(v_msgData_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_);
lean_dec(v___y_151_);
lean_dec_ref(v___y_150_);
lean_dec(v___y_149_);
lean_dec_ref(v___y_148_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__0(lean_object* v_msgData_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_){
_start:
{
lean_object* v___x_165_; 
v___x_165_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__0___redArg(v_msgData_154_, v___y_160_, v___y_161_, v___y_162_, v___y_163_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__0___boxed(lean_object* v_msgData_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__0(v_msgData_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_);
lean_dec(v___y_175_);
lean_dec_ref(v___y_174_);
lean_dec(v___y_173_);
lean_dec_ref(v___y_172_);
lean_dec(v___y_171_);
lean_dec_ref(v___y_170_);
lean_dec(v___y_169_);
lean_dec_ref(v___y_168_);
lean_dec(v___y_167_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2___redArg___lam__0(lean_object* v_x_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_){
_start:
{
lean_object* v___x_189_; 
lean_inc(v___y_183_);
lean_inc_ref(v___y_182_);
lean_inc(v___y_181_);
lean_inc_ref(v___y_180_);
lean_inc(v___y_179_);
v___x_189_ = lean_apply_10(v_x_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_, v___y_187_, lean_box(0));
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2___redArg___lam__0___boxed(lean_object* v_x_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2___redArg___lam__0(v_x_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
lean_dec(v___y_193_);
lean_dec_ref(v___y_192_);
lean_dec(v___y_191_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2___redArg(lean_object* v_mvarId_202_, lean_object* v_x_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_){
_start:
{
lean_object* v___f_214_; lean_object* v___x_215_; 
lean_inc(v___y_208_);
lean_inc_ref(v___y_207_);
lean_inc(v___y_206_);
lean_inc_ref(v___y_205_);
lean_inc(v___y_204_);
v___f_214_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_214_, 0, v_x_203_);
lean_closure_set(v___f_214_, 1, v___y_204_);
lean_closure_set(v___f_214_, 2, v___y_205_);
lean_closure_set(v___f_214_, 3, v___y_206_);
lean_closure_set(v___f_214_, 4, v___y_207_);
lean_closure_set(v___f_214_, 5, v___y_208_);
v___x_215_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_202_, v___f_214_, v___y_209_, v___y_210_, v___y_211_, v___y_212_);
if (lean_obj_tag(v___x_215_) == 0)
{
return v___x_215_;
}
else
{
lean_object* v_a_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_223_; 
v_a_216_ = lean_ctor_get(v___x_215_, 0);
v_isSharedCheck_223_ = !lean_is_exclusive(v___x_215_);
if (v_isSharedCheck_223_ == 0)
{
v___x_218_ = v___x_215_;
v_isShared_219_ = v_isSharedCheck_223_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_a_216_);
lean_dec(v___x_215_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_223_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___x_221_; 
if (v_isShared_219_ == 0)
{
v___x_221_ = v___x_218_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v_a_216_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2___redArg___boxed(lean_object* v_mvarId_224_, lean_object* v_x_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2___redArg(v_mvarId_224_, v_x_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_);
lean_dec(v___y_234_);
lean_dec_ref(v___y_233_);
lean_dec(v___y_232_);
lean_dec_ref(v___y_231_);
lean_dec(v___y_230_);
lean_dec_ref(v___y_229_);
lean_dec(v___y_228_);
lean_dec_ref(v___y_227_);
lean_dec(v___y_226_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2(lean_object* v_00_u03b1_237_, lean_object* v_mvarId_238_, lean_object* v_x_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2___redArg(v_mvarId_238_, v_x_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2___boxed(lean_object* v_00_u03b1_251_, lean_object* v_mvarId_252_, lean_object* v_x_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2(v_00_u03b1_251_, v_mvarId_252_, v_x_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_);
lean_dec(v___y_262_);
lean_dec_ref(v___y_261_);
lean_dec(v___y_260_);
lean_dec_ref(v___y_259_);
lean_dec(v___y_258_);
lean_dec_ref(v___y_257_);
lean_dec(v___y_256_);
lean_dec_ref(v___y_255_);
lean_dec(v___y_254_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1_spec__1(lean_object* v_msgData_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_){
_start:
{
lean_object* v___x_271_; lean_object* v_env_272_; uint8_t v___x_273_; lean_object* v_env_274_; lean_object* v___x_275_; lean_object* v_toCold_276_; lean_object* v_mctx_277_; lean_object* v_lctx_278_; lean_object* v_options_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_271_ = lean_st_ref_get(v___y_269_);
v_env_272_ = lean_ctor_get(v___x_271_, 0);
lean_inc_ref(v_env_272_);
lean_dec(v___x_271_);
v___x_273_ = 0;
v_env_274_ = l_Lean_Environment_setRecordingDeps(v_env_272_, v___x_273_);
v___x_275_ = lean_st_ref_get(v___y_267_);
v_toCold_276_ = lean_ctor_get(v___y_268_, 0);
v_mctx_277_ = lean_ctor_get(v___x_275_, 0);
lean_inc_ref(v_mctx_277_);
lean_dec(v___x_275_);
v_lctx_278_ = lean_ctor_get(v___y_266_, 2);
v_options_279_ = lean_ctor_get(v_toCold_276_, 2);
lean_inc_ref(v_options_279_);
lean_inc_ref(v_lctx_278_);
v___x_280_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_280_, 0, v_env_274_);
lean_ctor_set(v___x_280_, 1, v_mctx_277_);
lean_ctor_set(v___x_280_, 2, v_lctx_278_);
lean_ctor_set(v___x_280_, 3, v_options_279_);
v___x_281_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_281_, 0, v___x_280_);
lean_ctor_set(v___x_281_, 1, v_msgData_265_);
v___x_282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_282_, 0, v___x_281_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1_spec__1___boxed(lean_object* v_msgData_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1_spec__1(v_msgData_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_);
lean_dec(v___y_287_);
lean_dec_ref(v___y_286_);
lean_dec(v___y_285_);
lean_dec_ref(v___y_284_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1___redArg(lean_object* v_msg_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_){
_start:
{
lean_object* v_ref_296_; lean_object* v___x_297_; lean_object* v_a_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_306_; 
v_ref_296_ = lean_ctor_get(v___y_293_, 2);
v___x_297_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1_spec__1(v_msg_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_);
v_a_298_ = lean_ctor_get(v___x_297_, 0);
v_isSharedCheck_306_ = !lean_is_exclusive(v___x_297_);
if (v_isSharedCheck_306_ == 0)
{
v___x_300_ = v___x_297_;
v_isShared_301_ = v_isSharedCheck_306_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_a_298_);
lean_dec(v___x_297_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_306_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_302_; lean_object* v___x_304_; 
lean_inc(v_ref_296_);
v___x_302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_302_, 0, v_ref_296_);
lean_ctor_set(v___x_302_, 1, v_a_298_);
if (v_isShared_301_ == 0)
{
lean_ctor_set_tag(v___x_300_, 1);
lean_ctor_set(v___x_300_, 0, v___x_302_);
v___x_304_ = v___x_300_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v___x_302_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1___redArg___boxed(lean_object* v_msg_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1___redArg(v_msg_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_);
lean_dec(v___y_311_);
lean_dec_ref(v___y_310_);
lean_dec(v___y_309_);
lean_dec_ref(v___y_308_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_bvDecide___lam__0(lean_object* v_a_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_){
_start:
{
lean_object* v___x_325_; 
v___x_325_ = l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality(v_a_314_, v___y_320_, v___y_321_, v___y_322_, v___y_323_);
if (lean_obj_tag(v___x_325_) == 0)
{
lean_object* v_a_326_; lean_object* v___x_327_; lean_object* v_a_328_; lean_object* v___x_329_; 
v_a_326_ = lean_ctor_get(v___x_325_, 0);
lean_inc(v_a_326_);
lean_dec_ref_known(v___x_325_, 1);
v___x_327_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__0___redArg(v_a_326_, v___y_320_, v___y_321_, v___y_322_, v___y_323_);
v_a_328_ = lean_ctor_get(v___x_327_, 0);
lean_inc(v_a_328_);
lean_dec_ref(v___x_327_);
v___x_329_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1___redArg(v_a_328_, v___y_320_, v___y_321_, v___y_322_, v___y_323_);
return v___x_329_;
}
else
{
lean_object* v_a_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_337_; 
v_a_330_ = lean_ctor_get(v___x_325_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_337_ == 0)
{
v___x_332_ = v___x_325_;
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_a_330_);
lean_dec(v___x_325_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_335_; 
if (v_isShared_333_ == 0)
{
v___x_335_ = v___x_332_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_a_330_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_bvDecide___lam__0___boxed(lean_object* v_a_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Lean_Meta_Tactic_BVDecide_bvDecide___lam__0(v_a_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_);
lean_dec(v___y_347_);
lean_dec_ref(v___y_346_);
lean_dec(v___y_345_);
lean_dec_ref(v___y_344_);
lean_dec(v___y_343_);
lean_dec_ref(v___y_342_);
lean_dec(v___y_341_);
lean_dec_ref(v___y_340_);
lean_dec(v___y_339_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_bvDecide(lean_object* v_target_350_, lean_object* v_ctx_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = l_Lean_Meta_Tactic_BVDecide_bvDecide_x27(v_target_350_, v_ctx_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_);
if (lean_obj_tag(v___x_362_) == 0)
{
lean_object* v_a_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_375_; 
v_a_363_ = lean_ctor_get(v___x_362_, 0);
v_isSharedCheck_375_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_375_ == 0)
{
v___x_365_ = v___x_362_;
v_isShared_366_ = v_isSharedCheck_375_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_a_363_);
lean_dec(v___x_362_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_375_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
if (lean_obj_tag(v_a_363_) == 0)
{
lean_object* v_a_367_; lean_object* v_goal_368_; lean_object* v___f_369_; lean_object* v___x_370_; 
lean_del_object(v___x_365_);
v_a_367_ = lean_ctor_get(v_a_363_, 0);
lean_inc(v_a_367_);
lean_dec_ref_known(v_a_363_, 1);
v_goal_368_ = lean_ctor_get(v_a_367_, 0);
lean_inc(v_goal_368_);
v___f_369_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_bvDecide___lam__0___boxed), 11, 1);
lean_closure_set(v___f_369_, 0, v_a_367_);
v___x_370_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2___redArg(v_goal_368_, v___f_369_, v_a_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_);
return v___x_370_;
}
else
{
lean_object* v_a_371_; lean_object* v___x_373_; 
v_a_371_ = lean_ctor_get(v_a_363_, 0);
lean_inc(v_a_371_);
lean_dec_ref_known(v_a_363_, 1);
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 0, v_a_371_);
v___x_373_ = v___x_365_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v_a_371_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
}
}
else
{
lean_object* v_a_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_383_; 
v_a_376_ = lean_ctor_get(v___x_362_, 0);
v_isSharedCheck_383_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_383_ == 0)
{
v___x_378_ = v___x_362_;
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_a_376_);
lean_dec(v___x_362_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v___x_381_; 
if (v_isShared_379_ == 0)
{
v___x_381_ = v___x_378_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_a_376_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_bvDecide___boxed(lean_object* v_target_384_, lean_object* v_ctx_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Lean_Meta_Tactic_BVDecide_bvDecide(v_target_384_, v_ctx_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_);
lean_dec(v_a_394_);
lean_dec_ref(v_a_393_);
lean_dec(v_a_392_);
lean_dec_ref(v_a_391_);
lean_dec(v_a_390_);
lean_dec_ref(v_a_389_);
lean_dec(v_a_388_);
lean_dec_ref(v_a_387_);
lean_dec(v_a_386_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1(lean_object* v_00_u03b1_397_, lean_object* v_msg_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_){
_start:
{
lean_object* v___x_409_; 
v___x_409_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1___redArg(v_msg_398_, v___y_404_, v___y_405_, v___y_406_, v___y_407_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1___boxed(lean_object* v_00_u03b1_410_, lean_object* v_msg_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1(v_00_u03b1_410_, v_msg_411_, v___y_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_);
lean_dec(v___y_420_);
lean_dec_ref(v___y_419_);
lean_dec(v___y_418_);
lean_dec_ref(v___y_417_);
lean_dec(v___y_416_);
lean_dec_ref(v___y_415_);
lean_dec(v___y_414_);
lean_dec_ref(v___y_413_);
lean_dec(v___y_412_);
return v_res_422_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Bitblast(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar(uint8_t builtin);
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
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar(builtin);
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
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar(uint8_t builtin);
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
res = initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar(builtin);
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

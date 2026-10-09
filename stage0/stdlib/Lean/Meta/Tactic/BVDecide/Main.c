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
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Main_0__Lean_Meta_Tactic_BVDecide_bvUnsat(lean_object* v_g_1_, lean_object* v_hypotheses_2_, lean_object* v_ctx_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_){
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
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Main_0__Lean_Meta_Tactic_BVDecide_bvUnsat_0interp(lean_interpreter_value* stack)
{
lean_object* v_g_1_ = stack[0].m_obj;
lean_object* v_hypotheses_2_ = stack[1].m_obj;
lean_object* v_ctx_3_ = stack[2].m_obj;
lean_object* v_a_4_ = stack[3].m_obj;
lean_object* v_a_5_ = stack[4].m_obj;
lean_object* v_a_6_ = stack[5].m_obj;
lean_object* v_a_7_ = stack[6].m_obj;
lean_object* v_a_8_ = stack[7].m_obj;
lean_object* v_a_9_ = stack[8].m_obj;
lean_object* v_a_10_ = stack[9].m_obj;
lean_object* v_a_11_ = stack[10].m_obj;
lean_object* v_a_12_ = stack[11].m_obj;
lean_object* v_res_18_;
v_res_18_ = l___private_Lean_Meta_Tactic_BVDecide_Main_0__Lean_Meta_Tactic_BVDecide_bvUnsat(v_g_1_, v_hypotheses_2_, v_ctx_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_);
stack->m_obj
 = v_res_18_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Main_0__Lean_Meta_Tactic_BVDecide_bvUnsat___boxed(lean_object* v_g_19_, lean_object* v_hypotheses_20_, lean_object* v_ctx_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_, lean_object* v_a_25_, lean_object* v_a_26_, lean_object* v_a_27_, lean_object* v_a_28_, lean_object* v_a_29_, lean_object* v_a_30_, lean_object* v_a_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l___private_Lean_Meta_Tactic_BVDecide_Main_0__Lean_Meta_Tactic_BVDecide_bvUnsat(v_g_19_, v_hypotheses_20_, v_ctx_21_, v_a_22_, v_a_23_, v_a_24_, v_a_25_, v_a_26_, v_a_27_, v_a_28_, v_a_29_, v_a_30_);
lean_dec(v_a_30_);
lean_dec_ref(v_a_29_);
lean_dec(v_a_28_);
lean_dec_ref(v_a_27_);
lean_dec(v_a_26_);
lean_dec_ref(v_a_25_);
lean_dec(v_a_24_);
lean_dec_ref(v_a_23_);
lean_dec(v_a_22_);
return v_res_32_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__0(void){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_33_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__1(void){
_start:
{
lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_34_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__0, &l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__0);
v___x_35_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_35_, 0, v___x_34_);
return v___x_35_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__2(void){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_36_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__1, &l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__1);
v___x_37_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_37_, 0, v___x_36_);
lean_ctor_set(v___x_37_, 1, v___x_36_);
lean_ctor_set(v___x_37_, 2, v___x_36_);
lean_ctor_set(v___x_37_, 3, v___x_36_);
return v___x_37_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__3(void){
_start:
{
lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_38_ = lean_box(0);
v___x_39_ = lean_unsigned_to_nat(16u);
v___x_40_ = lean_mk_array(v___x_39_, v___x_38_);
return v___x_40_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__4(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_41_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__3, &l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__3);
v___x_42_ = lean_unsigned_to_nat(0u);
v___x_43_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_43_, 0, v___x_42_);
lean_ctor_set(v___x_43_, 1, v___x_41_);
return v___x_43_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__5(void){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_44_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__4, &l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__4);
v___x_45_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_45_, 0, v___x_44_);
lean_ctor_set(v___x_45_, 1, v___x_44_);
lean_ctor_set(v___x_45_, 2, v___x_44_);
lean_ctor_set(v___x_45_, 3, v___x_44_);
return v___x_45_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__7(void){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_48_ = l_Lean_Meta_Tactic_BVDecide_CegarCert_solvedWithPreProcessing;
v___x_49_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_49_, 0, v___x_48_);
return v___x_49_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_bvDecide_x27(lean_object* v_target_50_, lean_object* v_ctx_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; uint8_t v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v_a_71_; lean_object* v___x_74_; 
lean_inc_ref(v_ctx_51_);
v___x_62_ = l_Lean_Meta_Tactic_BVDecide_TacticContext_preProcessContext(v_ctx_51_);
v___x_63_ = lean_box(0);
v___x_64_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__2, &l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__2);
v___x_65_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__5, &l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__5);
v___x_66_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__6));
v___x_67_ = 0;
v___x_68_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_68_, 0, v___x_64_);
lean_ctor_set(v___x_68_, 1, v___x_65_);
lean_ctor_set(v___x_68_, 2, v_target_50_);
lean_ctor_set(v___x_68_, 3, v___x_66_);
lean_ctor_set_uint8(v___x_68_, sizeof(void*)*4, v___x_67_);
v___x_69_ = lean_st_mk_ref(v___x_68_);
v___x_74_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(v___x_63_, v___x_62_, v___x_69_, v_a_52_, v_a_53_, v_a_54_, v_a_55_, v_a_56_, v_a_57_, v_a_58_, v_a_59_, v_a_60_);
lean_dec_ref(v___x_62_);
if (lean_obj_tag(v___x_74_) == 0)
{
lean_object* v_a_75_; uint8_t v___x_76_; 
v_a_75_ = lean_ctor_get(v___x_74_, 0);
lean_inc(v_a_75_);
lean_dec_ref_known(v___x_74_, 1);
v___x_76_ = lean_unbox(v_a_75_);
lean_dec(v_a_75_);
if (v___x_76_ == 0)
{
lean_object* v___x_77_; lean_object* v_target_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v_hypotheses_81_; lean_object* v___x_82_; 
v___x_77_ = lean_st_ref_get(v___x_69_);
v_target_78_ = lean_ctor_get(v___x_77_, 2);
lean_inc_ref(v_target_78_);
lean_dec(v___x_77_);
v___x_79_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_78_);
lean_dec_ref(v_target_78_);
v___x_80_ = lean_st_ref_get(v___x_69_);
v_hypotheses_81_ = lean_ctor_get(v___x_80_, 3);
lean_inc_ref(v_hypotheses_81_);
lean_dec(v___x_80_);
v___x_82_ = l___private_Lean_Meta_Tactic_BVDecide_Main_0__Lean_Meta_Tactic_BVDecide_bvUnsat(v___x_79_, v_hypotheses_81_, v_ctx_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_, v_a_56_, v_a_57_, v_a_58_, v_a_59_, v_a_60_);
if (lean_obj_tag(v___x_82_) == 0)
{
lean_object* v_a_83_; 
v_a_83_ = lean_ctor_get(v___x_82_, 0);
lean_inc(v_a_83_);
lean_dec_ref_known(v___x_82_, 1);
if (lean_obj_tag(v_a_83_) == 0)
{
lean_object* v_a_84_; lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_91_; 
v_a_84_ = lean_ctor_get(v_a_83_, 0);
v_isSharedCheck_91_ = !lean_is_exclusive(v_a_83_);
if (v_isSharedCheck_91_ == 0)
{
v___x_86_ = v_a_83_;
v_isShared_87_ = v_isSharedCheck_91_;
goto v_resetjp_85_;
}
else
{
lean_inc(v_a_84_);
lean_dec(v_a_83_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_91_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
lean_object* v___x_89_; 
if (v_isShared_87_ == 0)
{
v___x_89_ = v___x_86_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_90_; 
v_reuseFailAlloc_90_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_90_, 0, v_a_84_);
v___x_89_ = v_reuseFailAlloc_90_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
v_a_71_ = v___x_89_;
goto v___jp_70_;
}
}
}
else
{
lean_object* v_a_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_99_; 
v_a_92_ = lean_ctor_get(v_a_83_, 0);
v_isSharedCheck_99_ = !lean_is_exclusive(v_a_83_);
if (v_isSharedCheck_99_ == 0)
{
v___x_94_ = v_a_83_;
v_isShared_95_ = v_isSharedCheck_99_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_a_92_);
lean_dec(v_a_83_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_99_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v___x_97_; 
if (v_isShared_95_ == 0)
{
v___x_97_ = v___x_94_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v_a_92_);
v___x_97_ = v_reuseFailAlloc_98_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
v_a_71_ = v___x_97_;
goto v___jp_70_;
}
}
}
}
else
{
lean_object* v_a_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_107_; 
lean_dec(v___x_69_);
v_a_100_ = lean_ctor_get(v___x_82_, 0);
v_isSharedCheck_107_ = !lean_is_exclusive(v___x_82_);
if (v_isSharedCheck_107_ == 0)
{
v___x_102_ = v___x_82_;
v_isShared_103_ = v_isSharedCheck_107_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_a_100_);
lean_dec(v___x_82_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_107_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v___x_105_; 
if (v_isShared_103_ == 0)
{
v___x_105_ = v___x_102_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v_a_100_);
v___x_105_ = v_reuseFailAlloc_106_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
return v___x_105_;
}
}
}
}
else
{
lean_object* v___x_108_; 
lean_dec_ref(v_ctx_51_);
v___x_108_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__7, &l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__7);
v_a_71_ = v___x_108_;
goto v___jp_70_;
}
}
else
{
lean_object* v_a_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_116_; 
lean_dec(v___x_69_);
lean_dec_ref(v_ctx_51_);
v_a_109_ = lean_ctor_get(v___x_74_, 0);
v_isSharedCheck_116_ = !lean_is_exclusive(v___x_74_);
if (v_isSharedCheck_116_ == 0)
{
v___x_111_ = v___x_74_;
v_isShared_112_ = v_isSharedCheck_116_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_a_109_);
lean_dec(v___x_74_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_116_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v___x_114_; 
if (v_isShared_112_ == 0)
{
v___x_114_ = v___x_111_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v_a_109_);
v___x_114_ = v_reuseFailAlloc_115_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
return v___x_114_;
}
}
}
v___jp_70_:
{
lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_72_ = lean_st_ref_get(v___x_69_);
lean_dec(v___x_69_);
lean_dec(v___x_72_);
v___x_73_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_73_, 0, v_a_71_);
return v___x_73_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_bvDecide_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_target_50_ = stack[0].m_obj;
lean_object* v_ctx_51_ = stack[1].m_obj;
lean_object* v_a_52_ = stack[2].m_obj;
lean_object* v_a_53_ = stack[3].m_obj;
lean_object* v_a_54_ = stack[4].m_obj;
lean_object* v_a_55_ = stack[5].m_obj;
lean_object* v_a_56_ = stack[6].m_obj;
lean_object* v_a_57_ = stack[7].m_obj;
lean_object* v_a_58_ = stack[8].m_obj;
lean_object* v_a_59_ = stack[9].m_obj;
lean_object* v_a_60_ = stack[10].m_obj;
lean_object* v_res_117_;
v_res_117_ = l_Lean_Meta_Tactic_BVDecide_bvDecide_x27(v_target_50_, v_ctx_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_, v_a_56_, v_a_57_, v_a_58_, v_a_59_, v_a_60_);
stack->m_obj
 = v_res_117_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___boxed(lean_object* v_target_118_, lean_object* v_ctx_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_Lean_Meta_Tactic_BVDecide_bvDecide_x27(v_target_118_, v_ctx_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_, v_a_128_);
lean_dec(v_a_128_);
lean_dec_ref(v_a_127_);
lean_dec(v_a_126_);
lean_dec_ref(v_a_125_);
lean_dec(v_a_124_);
lean_dec_ref(v_a_123_);
lean_dec(v_a_122_);
lean_dec_ref(v_a_121_);
lean_dec(v_a_120_);
return v_res_130_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__0___redArg(lean_object* v_msgData_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_){
_start:
{
lean_object* v___x_137_; lean_object* v_env_138_; uint8_t v___x_139_; lean_object* v_env_140_; lean_object* v___x_141_; lean_object* v_toCold_142_; lean_object* v_mctx_143_; lean_object* v_lctx_144_; lean_object* v_options_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_137_ = lean_st_ref_get(v___y_135_);
v_env_138_ = lean_ctor_get(v___x_137_, 0);
lean_inc_ref(v_env_138_);
lean_dec(v___x_137_);
v___x_139_ = 0;
v_env_140_ = l_Lean_Environment_setRecordingDeps(v_env_138_, v___x_139_);
v___x_141_ = lean_st_ref_get(v___y_133_);
v_toCold_142_ = lean_ctor_get(v___y_134_, 0);
v_mctx_143_ = lean_ctor_get(v___x_141_, 0);
lean_inc_ref(v_mctx_143_);
lean_dec(v___x_141_);
v_lctx_144_ = lean_ctor_get(v___y_132_, 2);
v_options_145_ = lean_ctor_get(v_toCold_142_, 2);
lean_inc_ref(v_options_145_);
lean_inc_ref(v_lctx_144_);
v___x_146_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_146_, 0, v_env_140_);
lean_ctor_set(v___x_146_, 1, v_mctx_143_);
lean_ctor_set(v___x_146_, 2, v_lctx_144_);
lean_ctor_set(v___x_146_, 3, v_options_145_);
v___x_147_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_147_, 0, v___x_146_);
lean_ctor_set(v___x_147_, 1, v_msgData_131_);
v___x_148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_148_, 0, v___x_147_);
return v___x_148_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_131_ = stack[0].m_obj;
lean_object* v___y_132_ = stack[1].m_obj;
lean_object* v___y_133_ = stack[2].m_obj;
lean_object* v___y_134_ = stack[3].m_obj;
lean_object* v___y_135_ = stack[4].m_obj;
lean_object* v_res_149_;
v_res_149_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__0___redArg(v_msgData_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_);
stack->m_obj
 = v_res_149_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__0___redArg___boxed(lean_object* v_msgData_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__0___redArg(v_msgData_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_);
lean_dec(v___y_154_);
lean_dec_ref(v___y_153_);
lean_dec(v___y_152_);
lean_dec_ref(v___y_151_);
return v_res_156_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__0(lean_object* v_msgData_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__0___redArg(v_msgData_157_, v___y_163_, v___y_164_, v___y_165_, v___y_166_);
return v___x_168_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_157_ = stack[0].m_obj;
lean_object* v___y_158_ = stack[1].m_obj;
lean_object* v___y_159_ = stack[2].m_obj;
lean_object* v___y_160_ = stack[3].m_obj;
lean_object* v___y_161_ = stack[4].m_obj;
lean_object* v___y_162_ = stack[5].m_obj;
lean_object* v___y_163_ = stack[6].m_obj;
lean_object* v___y_164_ = stack[7].m_obj;
lean_object* v___y_165_ = stack[8].m_obj;
lean_object* v___y_166_ = stack[9].m_obj;
lean_object* v_res_169_;
v_res_169_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__0(v_msgData_157_, v___y_158_, v___y_159_, v___y_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_, v___y_166_);
stack->m_obj
 = v_res_169_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__0___boxed(lean_object* v_msgData_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__0(v_msgData_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_);
lean_dec(v___y_179_);
lean_dec_ref(v___y_178_);
lean_dec(v___y_177_);
lean_dec_ref(v___y_176_);
lean_dec(v___y_175_);
lean_dec_ref(v___y_174_);
lean_dec(v___y_173_);
lean_dec_ref(v___y_172_);
lean_dec(v___y_171_);
return v_res_181_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2___redArg___lam__0(lean_object* v_x_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_){
_start:
{
lean_object* v___x_193_; 
lean_inc(v___y_187_);
lean_inc_ref(v___y_186_);
lean_inc(v___y_185_);
lean_inc_ref(v___y_184_);
lean_inc(v___y_183_);
v___x_193_ = lean_apply_10(v_x_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_, lean_box(0));
return v___x_193_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_182_ = stack[0].m_obj;
lean_object* v___y_183_ = stack[1].m_obj;
lean_object* v___y_184_ = stack[2].m_obj;
lean_object* v___y_185_ = stack[3].m_obj;
lean_object* v___y_186_ = stack[4].m_obj;
lean_object* v___y_187_ = stack[5].m_obj;
lean_object* v___y_188_ = stack[6].m_obj;
lean_object* v___y_189_ = stack[7].m_obj;
lean_object* v___y_190_ = stack[8].m_obj;
lean_object* v___y_191_ = stack[9].m_obj;
lean_object* v_res_194_;
v_res_194_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2___redArg___lam__0(v_x_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_);
stack->m_obj
 = v_res_194_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2___redArg___lam__0___boxed(lean_object* v_x_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2___redArg___lam__0(v_x_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_);
lean_dec(v___y_200_);
lean_dec_ref(v___y_199_);
lean_dec(v___y_198_);
lean_dec_ref(v___y_197_);
lean_dec(v___y_196_);
return v_res_206_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2___redArg(lean_object* v_mvarId_207_, lean_object* v_x_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_){
_start:
{
lean_object* v___f_219_; lean_object* v___x_220_; 
lean_inc(v___y_213_);
lean_inc_ref(v___y_212_);
lean_inc(v___y_211_);
lean_inc_ref(v___y_210_);
lean_inc(v___y_209_);
v___f_219_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_219_, 0, v_x_208_);
lean_closure_set(v___f_219_, 1, v___y_209_);
lean_closure_set(v___f_219_, 2, v___y_210_);
lean_closure_set(v___f_219_, 3, v___y_211_);
lean_closure_set(v___f_219_, 4, v___y_212_);
lean_closure_set(v___f_219_, 5, v___y_213_);
v___x_220_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_207_, v___f_219_, v___y_214_, v___y_215_, v___y_216_, v___y_217_);
if (lean_obj_tag(v___x_220_) == 0)
{
return v___x_220_;
}
else
{
lean_object* v_a_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_228_; 
v_a_221_ = lean_ctor_get(v___x_220_, 0);
v_isSharedCheck_228_ = !lean_is_exclusive(v___x_220_);
if (v_isSharedCheck_228_ == 0)
{
v___x_223_ = v___x_220_;
v_isShared_224_ = v_isSharedCheck_228_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_a_221_);
lean_dec(v___x_220_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_228_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___x_226_; 
if (v_isShared_224_ == 0)
{
v___x_226_ = v___x_223_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v_a_221_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
return v___x_226_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_207_ = stack[0].m_obj;
lean_object* v_x_208_ = stack[1].m_obj;
lean_object* v___y_209_ = stack[2].m_obj;
lean_object* v___y_210_ = stack[3].m_obj;
lean_object* v___y_211_ = stack[4].m_obj;
lean_object* v___y_212_ = stack[5].m_obj;
lean_object* v___y_213_ = stack[6].m_obj;
lean_object* v___y_214_ = stack[7].m_obj;
lean_object* v___y_215_ = stack[8].m_obj;
lean_object* v___y_216_ = stack[9].m_obj;
lean_object* v___y_217_ = stack[10].m_obj;
lean_object* v_res_229_;
v_res_229_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2___redArg(v_mvarId_207_, v_x_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_);
stack->m_obj
 = v_res_229_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2___redArg___boxed(lean_object* v_mvarId_230_, lean_object* v_x_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2___redArg(v_mvarId_230_, v_x_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_);
lean_dec(v___y_240_);
lean_dec_ref(v___y_239_);
lean_dec(v___y_238_);
lean_dec_ref(v___y_237_);
lean_dec(v___y_236_);
lean_dec_ref(v___y_235_);
lean_dec(v___y_234_);
lean_dec_ref(v___y_233_);
lean_dec(v___y_232_);
return v_res_242_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2(lean_object* v_00_u03b1_243_, lean_object* v_mvarId_244_, lean_object* v_x_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_){
_start:
{
lean_object* v___x_256_; 
v___x_256_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2___redArg(v_mvarId_244_, v_x_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_);
return v___x_256_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_244_ = stack[1].m_obj;
lean_object* v_x_245_ = stack[2].m_obj;
lean_object* v___y_246_ = stack[3].m_obj;
lean_object* v___y_247_ = stack[4].m_obj;
lean_object* v___y_248_ = stack[5].m_obj;
lean_object* v___y_249_ = stack[6].m_obj;
lean_object* v___y_250_ = stack[7].m_obj;
lean_object* v___y_251_ = stack[8].m_obj;
lean_object* v___y_252_ = stack[9].m_obj;
lean_object* v___y_253_ = stack[10].m_obj;
lean_object* v___y_254_ = stack[11].m_obj;
lean_object* v_res_257_;
v_res_257_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2(lean_box(0), v_mvarId_244_, v_x_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_);
stack->m_obj
 = v_res_257_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2___boxed(lean_object* v_00_u03b1_258_, lean_object* v_mvarId_259_, lean_object* v_x_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2(v_00_u03b1_258_, v_mvarId_259_, v_x_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_);
lean_dec(v___y_269_);
lean_dec_ref(v___y_268_);
lean_dec(v___y_267_);
lean_dec_ref(v___y_266_);
lean_dec(v___y_265_);
lean_dec_ref(v___y_264_);
lean_dec(v___y_263_);
lean_dec_ref(v___y_262_);
lean_dec(v___y_261_);
return v_res_271_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1_spec__1(lean_object* v_msgData_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_){
_start:
{
lean_object* v___x_278_; lean_object* v_env_279_; uint8_t v___x_280_; lean_object* v_env_281_; lean_object* v___x_282_; lean_object* v_toCold_283_; lean_object* v_mctx_284_; lean_object* v_lctx_285_; lean_object* v_options_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_278_ = lean_st_ref_get(v___y_276_);
v_env_279_ = lean_ctor_get(v___x_278_, 0);
lean_inc_ref(v_env_279_);
lean_dec(v___x_278_);
v___x_280_ = 0;
v_env_281_ = l_Lean_Environment_setRecordingDeps(v_env_279_, v___x_280_);
v___x_282_ = lean_st_ref_get(v___y_274_);
v_toCold_283_ = lean_ctor_get(v___y_275_, 0);
v_mctx_284_ = lean_ctor_get(v___x_282_, 0);
lean_inc_ref(v_mctx_284_);
lean_dec(v___x_282_);
v_lctx_285_ = lean_ctor_get(v___y_273_, 2);
v_options_286_ = lean_ctor_get(v_toCold_283_, 2);
lean_inc_ref(v_options_286_);
lean_inc_ref(v_lctx_285_);
v___x_287_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_287_, 0, v_env_281_);
lean_ctor_set(v___x_287_, 1, v_mctx_284_);
lean_ctor_set(v___x_287_, 2, v_lctx_285_);
lean_ctor_set(v___x_287_, 3, v_options_286_);
v___x_288_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_287_);
lean_ctor_set(v___x_288_, 1, v_msgData_272_);
v___x_289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
return v___x_289_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_272_ = stack[0].m_obj;
lean_object* v___y_273_ = stack[1].m_obj;
lean_object* v___y_274_ = stack[2].m_obj;
lean_object* v___y_275_ = stack[3].m_obj;
lean_object* v___y_276_ = stack[4].m_obj;
lean_object* v_res_290_;
v_res_290_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1_spec__1(v_msgData_272_, v___y_273_, v___y_274_, v___y_275_, v___y_276_);
stack->m_obj
 = v_res_290_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1_spec__1___boxed(lean_object* v_msgData_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1_spec__1(v_msgData_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
lean_dec(v___y_293_);
lean_dec_ref(v___y_292_);
return v_res_297_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1___redArg(lean_object* v_msg_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
lean_object* v_ref_304_; lean_object* v___x_305_; lean_object* v_a_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_314_; 
v_ref_304_ = lean_ctor_get(v___y_301_, 2);
v___x_305_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1_spec__1(v_msg_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_);
v_a_306_ = lean_ctor_get(v___x_305_, 0);
v_isSharedCheck_314_ = !lean_is_exclusive(v___x_305_);
if (v_isSharedCheck_314_ == 0)
{
v___x_308_ = v___x_305_;
v_isShared_309_ = v_isSharedCheck_314_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_a_306_);
lean_dec(v___x_305_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_314_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_310_; lean_object* v___x_312_; 
lean_inc(v_ref_304_);
v___x_310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_310_, 0, v_ref_304_);
lean_ctor_set(v___x_310_, 1, v_a_306_);
if (v_isShared_309_ == 0)
{
lean_ctor_set_tag(v___x_308_, 1);
lean_ctor_set(v___x_308_, 0, v___x_310_);
v___x_312_ = v___x_308_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v___x_310_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_298_ = stack[0].m_obj;
lean_object* v___y_299_ = stack[1].m_obj;
lean_object* v___y_300_ = stack[2].m_obj;
lean_object* v___y_301_ = stack[3].m_obj;
lean_object* v___y_302_ = stack[4].m_obj;
lean_object* v_res_315_;
v_res_315_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1___redArg(v_msg_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_);
stack->m_obj
 = v_res_315_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1___redArg___boxed(lean_object* v_msg_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1___redArg(v_msg_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_);
lean_dec(v___y_320_);
lean_dec_ref(v___y_319_);
lean_dec(v___y_318_);
lean_dec_ref(v___y_317_);
return v_res_322_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_bvDecide___lam__0(lean_object* v_a_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality(v_a_323_, v___y_329_, v___y_330_, v___y_331_, v___y_332_);
if (lean_obj_tag(v___x_334_) == 0)
{
lean_object* v_a_335_; lean_object* v___x_336_; lean_object* v_a_337_; lean_object* v___x_338_; 
v_a_335_ = lean_ctor_get(v___x_334_, 0);
lean_inc(v_a_335_);
lean_dec_ref_known(v___x_334_, 1);
v___x_336_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__0___redArg(v_a_335_, v___y_329_, v___y_330_, v___y_331_, v___y_332_);
v_a_337_ = lean_ctor_get(v___x_336_, 0);
lean_inc(v_a_337_);
lean_dec_ref(v___x_336_);
v___x_338_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1___redArg(v_a_337_, v___y_329_, v___y_330_, v___y_331_, v___y_332_);
return v___x_338_;
}
else
{
lean_object* v_a_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_346_; 
v_a_339_ = lean_ctor_get(v___x_334_, 0);
v_isSharedCheck_346_ = !lean_is_exclusive(v___x_334_);
if (v_isSharedCheck_346_ == 0)
{
v___x_341_ = v___x_334_;
v_isShared_342_ = v_isSharedCheck_346_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_a_339_);
lean_dec(v___x_334_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_346_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___x_344_; 
if (v_isShared_342_ == 0)
{
v___x_344_ = v___x_341_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_a_339_);
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
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_bvDecide___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_323_ = stack[0].m_obj;
lean_object* v___y_324_ = stack[1].m_obj;
lean_object* v___y_325_ = stack[2].m_obj;
lean_object* v___y_326_ = stack[3].m_obj;
lean_object* v___y_327_ = stack[4].m_obj;
lean_object* v___y_328_ = stack[5].m_obj;
lean_object* v___y_329_ = stack[6].m_obj;
lean_object* v___y_330_ = stack[7].m_obj;
lean_object* v___y_331_ = stack[8].m_obj;
lean_object* v___y_332_ = stack[9].m_obj;
lean_object* v_res_347_;
v_res_347_ = l_Lean_Meta_Tactic_BVDecide_bvDecide___lam__0(v_a_323_, v___y_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_);
stack->m_obj
 = v_res_347_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_bvDecide___lam__0___boxed(lean_object* v_a_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Lean_Meta_Tactic_BVDecide_bvDecide___lam__0(v_a_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_);
lean_dec(v___y_357_);
lean_dec_ref(v___y_356_);
lean_dec(v___y_355_);
lean_dec_ref(v___y_354_);
lean_dec(v___y_353_);
lean_dec_ref(v___y_352_);
lean_dec(v___y_351_);
lean_dec_ref(v___y_350_);
lean_dec(v___y_349_);
return v_res_359_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_bvDecide(lean_object* v_target_360_, lean_object* v_ctx_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = l_Lean_Meta_Tactic_BVDecide_bvDecide_x27(v_target_360_, v_ctx_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_);
if (lean_obj_tag(v___x_372_) == 0)
{
lean_object* v_a_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_385_; 
v_a_373_ = lean_ctor_get(v___x_372_, 0);
v_isSharedCheck_385_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_385_ == 0)
{
v___x_375_ = v___x_372_;
v_isShared_376_ = v_isSharedCheck_385_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_a_373_);
lean_dec(v___x_372_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_385_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
if (lean_obj_tag(v_a_373_) == 0)
{
lean_object* v_a_377_; lean_object* v_goal_378_; lean_object* v___f_379_; lean_object* v___x_380_; 
lean_del_object(v___x_375_);
v_a_377_ = lean_ctor_get(v_a_373_, 0);
lean_inc(v_a_377_);
lean_dec_ref_known(v_a_373_, 1);
v_goal_378_ = lean_ctor_get(v_a_377_, 0);
lean_inc(v_goal_378_);
v___f_379_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_bvDecide___lam__0___boxed), 11, 1);
lean_closure_set(v___f_379_, 0, v_a_377_);
v___x_380_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2___redArg(v_goal_378_, v___f_379_, v_a_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_);
return v___x_380_;
}
else
{
lean_object* v_a_381_; lean_object* v___x_383_; 
v_a_381_ = lean_ctor_get(v_a_373_, 0);
lean_inc(v_a_381_);
lean_dec_ref_known(v_a_373_, 1);
if (v_isShared_376_ == 0)
{
lean_ctor_set(v___x_375_, 0, v_a_381_);
v___x_383_ = v___x_375_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v_a_381_);
v___x_383_ = v_reuseFailAlloc_384_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
return v___x_383_;
}
}
}
}
else
{
lean_object* v_a_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_393_; 
v_a_386_ = lean_ctor_get(v___x_372_, 0);
v_isSharedCheck_393_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_393_ == 0)
{
v___x_388_ = v___x_372_;
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_a_386_);
lean_dec(v___x_372_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_391_; 
if (v_isShared_389_ == 0)
{
v___x_391_ = v___x_388_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_a_386_);
v___x_391_ = v_reuseFailAlloc_392_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
return v___x_391_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_bvDecide_0interp(lean_interpreter_value* stack)
{
lean_object* v_target_360_ = stack[0].m_obj;
lean_object* v_ctx_361_ = stack[1].m_obj;
lean_object* v_a_362_ = stack[2].m_obj;
lean_object* v_a_363_ = stack[3].m_obj;
lean_object* v_a_364_ = stack[4].m_obj;
lean_object* v_a_365_ = stack[5].m_obj;
lean_object* v_a_366_ = stack[6].m_obj;
lean_object* v_a_367_ = stack[7].m_obj;
lean_object* v_a_368_ = stack[8].m_obj;
lean_object* v_a_369_ = stack[9].m_obj;
lean_object* v_a_370_ = stack[10].m_obj;
lean_object* v_res_394_;
v_res_394_ = l_Lean_Meta_Tactic_BVDecide_bvDecide(v_target_360_, v_ctx_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_);
stack->m_obj
 = v_res_394_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_bvDecide___boxed(lean_object* v_target_395_, lean_object* v_ctx_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_Lean_Meta_Tactic_BVDecide_bvDecide(v_target_395_, v_ctx_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_);
lean_dec(v_a_405_);
lean_dec_ref(v_a_404_);
lean_dec(v_a_403_);
lean_dec_ref(v_a_402_);
lean_dec(v_a_401_);
lean_dec_ref(v_a_400_);
lean_dec(v_a_399_);
lean_dec_ref(v_a_398_);
lean_dec(v_a_397_);
return v_res_407_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1(lean_object* v_00_u03b1_408_, lean_object* v_msg_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_){
_start:
{
lean_object* v___x_420_; 
v___x_420_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1___redArg(v_msg_409_, v___y_415_, v___y_416_, v___y_417_, v___y_418_);
return v___x_420_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_409_ = stack[1].m_obj;
lean_object* v___y_410_ = stack[2].m_obj;
lean_object* v___y_411_ = stack[3].m_obj;
lean_object* v___y_412_ = stack[4].m_obj;
lean_object* v___y_413_ = stack[5].m_obj;
lean_object* v___y_414_ = stack[6].m_obj;
lean_object* v___y_415_ = stack[7].m_obj;
lean_object* v___y_416_ = stack[8].m_obj;
lean_object* v___y_417_ = stack[9].m_obj;
lean_object* v___y_418_ = stack[10].m_obj;
lean_object* v_res_421_;
v_res_421_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1(lean_box(0), v_msg_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_);
stack->m_obj
 = v_res_421_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1___boxed(lean_object* v_00_u03b1_422_, lean_object* v_msg_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1(v_00_u03b1_422_, v_msg_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_);
lean_dec(v___y_432_);
lean_dec_ref(v___y_431_);
lean_dec(v___y_430_);
lean_dec_ref(v___y_429_);
lean_dec(v___y_428_);
lean_dec_ref(v___y_427_);
lean_dec(v___y_426_);
lean_dec_ref(v___y_425_);
lean_dec(v___y_424_);
return v_res_434_;
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

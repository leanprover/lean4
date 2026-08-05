// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Main
// Imports: public import Lean.Meta.Tactic.BVDecide.Prover.Bitblast import Lean.Meta.Tactic.BVDecide.Normalize import Lean.Meta.Sym.Util
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_M_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_SymM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Main_0__Lean_Meta_Tactic_BVDecide_bvUnsat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Main_0__Lean_Meta_Tactic_BVDecide_bvUnsat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___lam__0___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___lam__0___closed__1;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___lam__0___closed__2;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___lam__0___closed__3;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___lam__0___closed__4;
static const lean_array_object l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___lam__0___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___lam__0___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___lam__0___closed__6 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___lam__0___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_bvDecide_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_bvDecide___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_bvDecide___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_bvDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_bvDecide___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Main_0__Lean_Meta_Tactic_BVDecide_bvUnsat(lean_object* v_g_1_, lean_object* v_hypotheses_2_, lean_object* v_ctx_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_, lean_object* v_a_9_){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_11_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___boxed), 9, 1);
lean_closure_set(v___x_11_, 0, v_ctx_3_);
v___x_12_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___boxed), 12, 3);
lean_closure_set(v___x_12_, 0, lean_box(0));
lean_closure_set(v___x_12_, 1, v_g_1_);
lean_closure_set(v___x_12_, 2, v___x_11_);
v___x_13_ = l_Lean_Meta_Tactic_BVDecide_M_run___redArg(v___x_12_, v_hypotheses_2_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Main_0__Lean_Meta_Tactic_BVDecide_bvUnsat___boxed(lean_object* v_g_14_, lean_object* v_hypotheses_15_, lean_object* v_ctx_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l___private_Lean_Meta_Tactic_BVDecide_Main_0__Lean_Meta_Tactic_BVDecide_bvUnsat(v_g_14_, v_hypotheses_15_, v_ctx_16_, v_a_17_, v_a_18_, v_a_19_, v_a_20_, v_a_21_, v_a_22_);
lean_dec(v_a_22_);
lean_dec_ref(v_a_21_);
lean_dec(v_a_20_);
lean_dec_ref(v_a_19_);
lean_dec(v_a_18_);
lean_dec_ref(v_a_17_);
return v_res_24_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___lam__0___closed__0(void){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_25_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___lam__0___closed__1(void){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_26_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___lam__0___closed__0, &l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___lam__0___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___lam__0___closed__0);
v___x_27_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_27_, 0, v___x_26_);
return v___x_27_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___lam__0___closed__2(void){
_start:
{
lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_28_ = lean_box(0);
v___x_29_ = lean_unsigned_to_nat(16u);
v___x_30_ = lean_mk_array(v___x_29_, v___x_28_);
return v___x_30_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___lam__0___closed__3(void){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_31_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___lam__0___closed__2, &l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___lam__0___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___lam__0___closed__2);
v___x_32_ = lean_unsigned_to_nat(0u);
v___x_33_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_33_, 0, v___x_32_);
lean_ctor_set(v___x_33_, 1, v___x_31_);
return v___x_33_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___lam__0___closed__4(void){
_start:
{
lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_34_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___lam__0___closed__3, &l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___lam__0___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___lam__0___closed__3);
v___x_35_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_35_, 0, v___x_34_);
lean_ctor_set(v___x_35_, 1, v___x_34_);
lean_ctor_set(v___x_35_, 2, v___x_34_);
lean_ctor_set(v___x_35_, 3, v___x_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___lam__0(lean_object* v_g_40_, lean_object* v_config_41_, lean_object* v_ctx_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; uint8_t v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v_a_57_; lean_object* v___x_60_; 
v___x_50_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___lam__0___closed__1, &l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___lam__0___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___lam__0___closed__1);
v___x_51_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___lam__0___closed__4, &l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___lam__0___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___lam__0___closed__4);
v___x_52_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___lam__0___closed__5));
v___x_53_ = 0;
v___x_54_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_54_, 0, v___x_50_);
lean_ctor_set(v___x_54_, 1, v___x_50_);
lean_ctor_set(v___x_54_, 2, v___x_50_);
lean_ctor_set(v___x_54_, 3, v___x_51_);
lean_ctor_set(v___x_54_, 4, v_g_40_);
lean_ctor_set(v___x_54_, 5, v___x_52_);
lean_ctor_set_uint8(v___x_54_, sizeof(void*)*6, v___x_53_);
v___x_55_ = lean_st_mk_ref(v___x_54_);
v___x_60_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(v_config_41_, v___x_55_, v___y_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_, v___y_48_);
if (lean_obj_tag(v___x_60_) == 0)
{
lean_object* v_a_61_; uint8_t v___x_62_; 
v_a_61_ = lean_ctor_get(v___x_60_, 0);
lean_inc(v_a_61_);
lean_dec_ref_known(v___x_60_, 1);
v___x_62_ = lean_unbox(v_a_61_);
lean_dec(v_a_61_);
if (v___x_62_ == 0)
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v_goal_65_; lean_object* v_hypotheses_66_; lean_object* v___x_67_; 
v___x_63_ = lean_st_ref_get(v___x_55_);
v___x_64_ = lean_st_ref_get(v___x_55_);
v_goal_65_ = lean_ctor_get(v___x_63_, 4);
lean_inc(v_goal_65_);
lean_dec(v___x_63_);
v_hypotheses_66_ = lean_ctor_get(v___x_64_, 5);
lean_inc_ref(v_hypotheses_66_);
lean_dec(v___x_64_);
v___x_67_ = l___private_Lean_Meta_Tactic_BVDecide_Main_0__Lean_Meta_Tactic_BVDecide_bvUnsat(v_goal_65_, v_hypotheses_66_, v_ctx_42_, v___y_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_, v___y_48_);
if (lean_obj_tag(v___x_67_) == 0)
{
lean_object* v_a_68_; 
v_a_68_ = lean_ctor_get(v___x_67_, 0);
lean_inc(v_a_68_);
lean_dec_ref_known(v___x_67_, 1);
if (lean_obj_tag(v_a_68_) == 0)
{
lean_object* v_a_69_; lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_76_; 
v_a_69_ = lean_ctor_get(v_a_68_, 0);
v_isSharedCheck_76_ = !lean_is_exclusive(v_a_68_);
if (v_isSharedCheck_76_ == 0)
{
v___x_71_ = v_a_68_;
v_isShared_72_ = v_isSharedCheck_76_;
goto v_resetjp_70_;
}
else
{
lean_inc(v_a_69_);
lean_dec(v_a_68_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_76_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
lean_object* v___x_74_; 
if (v_isShared_72_ == 0)
{
v___x_74_ = v___x_71_;
goto v_reusejp_73_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v_a_69_);
v___x_74_ = v_reuseFailAlloc_75_;
goto v_reusejp_73_;
}
v_reusejp_73_:
{
v_a_57_ = v___x_74_;
goto v___jp_56_;
}
}
}
else
{
lean_object* v_a_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_85_; 
v_a_77_ = lean_ctor_get(v_a_68_, 0);
v_isSharedCheck_85_ = !lean_is_exclusive(v_a_68_);
if (v_isSharedCheck_85_ == 0)
{
v___x_79_ = v_a_68_;
v_isShared_80_ = v_isSharedCheck_85_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_a_77_);
lean_dec(v_a_68_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_85_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
lean_object* v___x_81_; lean_object* v___x_83_; 
v___x_81_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_81_, 0, v_a_77_);
if (v_isShared_80_ == 0)
{
lean_ctor_set(v___x_79_, 0, v___x_81_);
v___x_83_ = v___x_79_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_84_; 
v_reuseFailAlloc_84_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_84_, 0, v___x_81_);
v___x_83_ = v_reuseFailAlloc_84_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
v_a_57_ = v___x_83_;
goto v___jp_56_;
}
}
}
}
else
{
lean_object* v_a_86_; lean_object* v___x_88_; uint8_t v_isShared_89_; uint8_t v_isSharedCheck_93_; 
lean_dec(v___x_55_);
v_a_86_ = lean_ctor_get(v___x_67_, 0);
v_isSharedCheck_93_ = !lean_is_exclusive(v___x_67_);
if (v_isSharedCheck_93_ == 0)
{
v___x_88_ = v___x_67_;
v_isShared_89_ = v_isSharedCheck_93_;
goto v_resetjp_87_;
}
else
{
lean_inc(v_a_86_);
lean_dec(v___x_67_);
v___x_88_ = lean_box(0);
v_isShared_89_ = v_isSharedCheck_93_;
goto v_resetjp_87_;
}
v_resetjp_87_:
{
lean_object* v___x_91_; 
if (v_isShared_89_ == 0)
{
v___x_91_ = v___x_88_;
goto v_reusejp_90_;
}
else
{
lean_object* v_reuseFailAlloc_92_; 
v_reuseFailAlloc_92_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_92_, 0, v_a_86_);
v___x_91_ = v_reuseFailAlloc_92_;
goto v_reusejp_90_;
}
v_reusejp_90_:
{
return v___x_91_;
}
}
}
}
else
{
lean_object* v___x_94_; 
lean_dec_ref(v_ctx_42_);
v___x_94_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___lam__0___closed__6));
v_a_57_ = v___x_94_;
goto v___jp_56_;
}
}
else
{
lean_object* v_a_95_; lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_102_; 
lean_dec(v___x_55_);
lean_dec_ref(v_ctx_42_);
v_a_95_ = lean_ctor_get(v___x_60_, 0);
v_isSharedCheck_102_ = !lean_is_exclusive(v___x_60_);
if (v_isSharedCheck_102_ == 0)
{
v___x_97_ = v___x_60_;
v_isShared_98_ = v_isSharedCheck_102_;
goto v_resetjp_96_;
}
else
{
lean_inc(v_a_95_);
lean_dec(v___x_60_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_102_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
lean_object* v___x_100_; 
if (v_isShared_98_ == 0)
{
v___x_100_ = v___x_97_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v_a_95_);
v___x_100_ = v_reuseFailAlloc_101_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
return v___x_100_;
}
}
}
v___jp_56_:
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = lean_st_ref_get(v___x_55_);
lean_dec(v___x_55_);
lean_dec(v___x_58_);
v___x_59_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_59_, 0, v_a_57_);
return v___x_59_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___lam__0___boxed(lean_object* v_g_103_, lean_object* v_config_104_, lean_object* v_ctx_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___lam__0(v_g_103_, v_config_104_, v_ctx_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_);
lean_dec(v___y_111_);
lean_dec_ref(v___y_110_);
lean_dec(v___y_109_);
lean_dec_ref(v___y_108_);
lean_dec(v___y_107_);
lean_dec_ref(v___y_106_);
lean_dec_ref(v_config_104_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_bvDecide_x27(lean_object* v_g_114_, lean_object* v_ctx_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_){
_start:
{
lean_object* v_config_121_; lean_object* v___f_122_; lean_object* v___x_123_; 
v_config_121_ = lean_ctor_get(v_ctx_115_, 5);
lean_inc_ref(v_config_121_);
v___f_122_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___lam__0___boxed), 10, 3);
lean_closure_set(v___f_122_, 0, v_g_114_);
lean_closure_set(v___f_122_, 1, v_config_121_);
lean_closure_set(v___f_122_, 2, v_ctx_115_);
v___x_123_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_122_, v_a_116_, v_a_117_, v_a_118_, v_a_119_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___boxed(lean_object* v_g_124_, lean_object* v_ctx_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_Lean_Meta_Tactic_BVDecide_bvDecide_x27(v_g_124_, v_ctx_125_, v_a_126_, v_a_127_, v_a_128_, v_a_129_);
lean_dec(v_a_129_);
lean_dec_ref(v_a_128_);
lean_dec(v_a_127_);
lean_dec_ref(v_a_126_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__0(lean_object* v_msgData_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_){
_start:
{
lean_object* v___x_138_; lean_object* v_env_139_; lean_object* v___x_140_; lean_object* v_mctx_141_; lean_object* v_lctx_142_; lean_object* v_options_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_138_ = lean_st_ref_get(v___y_136_);
v_env_139_ = lean_ctor_get(v___x_138_, 0);
lean_inc_ref(v_env_139_);
lean_dec(v___x_138_);
v___x_140_ = lean_st_ref_get(v___y_134_);
v_mctx_141_ = lean_ctor_get(v___x_140_, 0);
lean_inc_ref(v_mctx_141_);
lean_dec(v___x_140_);
v_lctx_142_ = lean_ctor_get(v___y_133_, 2);
v_options_143_ = lean_ctor_get(v___y_135_, 2);
lean_inc_ref(v_options_143_);
lean_inc_ref(v_lctx_142_);
v___x_144_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_144_, 0, v_env_139_);
lean_ctor_set(v___x_144_, 1, v_mctx_141_);
lean_ctor_set(v___x_144_, 2, v_lctx_142_);
lean_ctor_set(v___x_144_, 3, v_options_143_);
v___x_145_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_145_, 0, v___x_144_);
lean_ctor_set(v___x_145_, 1, v_msgData_132_);
v___x_146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_146_, 0, v___x_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__0___boxed(lean_object* v_msgData_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__0(v_msgData_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_);
lean_dec(v___y_151_);
lean_dec_ref(v___y_150_);
lean_dec(v___y_149_);
lean_dec_ref(v___y_148_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2___redArg(lean_object* v_mvarId_154_, lean_object* v_x_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_154_, v_x_155_, v___y_156_, v___y_157_, v___y_158_, v___y_159_);
if (lean_obj_tag(v___x_161_) == 0)
{
lean_object* v_a_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_169_; 
v_a_162_ = lean_ctor_get(v___x_161_, 0);
v_isSharedCheck_169_ = !lean_is_exclusive(v___x_161_);
if (v_isSharedCheck_169_ == 0)
{
v___x_164_ = v___x_161_;
v_isShared_165_ = v_isSharedCheck_169_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_a_162_);
lean_dec(v___x_161_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_169_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v___x_167_; 
if (v_isShared_165_ == 0)
{
v___x_167_ = v___x_164_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v_a_162_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
}
else
{
lean_object* v_a_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_177_; 
v_a_170_ = lean_ctor_get(v___x_161_, 0);
v_isSharedCheck_177_ = !lean_is_exclusive(v___x_161_);
if (v_isSharedCheck_177_ == 0)
{
v___x_172_ = v___x_161_;
v_isShared_173_ = v_isSharedCheck_177_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_a_170_);
lean_dec(v___x_161_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_177_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v___x_175_; 
if (v_isShared_173_ == 0)
{
v___x_175_ = v___x_172_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v_a_170_);
v___x_175_ = v_reuseFailAlloc_176_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
return v___x_175_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2___redArg___boxed(lean_object* v_mvarId_178_, lean_object* v_x_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2___redArg(v_mvarId_178_, v_x_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_);
lean_dec(v___y_183_);
lean_dec_ref(v___y_182_);
lean_dec(v___y_181_);
lean_dec_ref(v___y_180_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2(lean_object* v_00_u03b1_186_, lean_object* v_mvarId_187_, lean_object* v_x_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2___redArg(v_mvarId_187_, v_x_188_, v___y_189_, v___y_190_, v___y_191_, v___y_192_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2___boxed(lean_object* v_00_u03b1_195_, lean_object* v_mvarId_196_, lean_object* v_x_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2(v_00_u03b1_195_, v_mvarId_196_, v_x_197_, v___y_198_, v___y_199_, v___y_200_, v___y_201_);
lean_dec(v___y_201_);
lean_dec_ref(v___y_200_);
lean_dec(v___y_199_);
lean_dec_ref(v___y_198_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1___redArg(lean_object* v_msg_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_){
_start:
{
lean_object* v_ref_210_; lean_object* v___x_211_; lean_object* v_a_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_220_; 
v_ref_210_ = lean_ctor_get(v___y_207_, 5);
v___x_211_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__0(v_msg_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_);
v_a_212_ = lean_ctor_get(v___x_211_, 0);
v_isSharedCheck_220_ = !lean_is_exclusive(v___x_211_);
if (v_isSharedCheck_220_ == 0)
{
v___x_214_ = v___x_211_;
v_isShared_215_ = v_isSharedCheck_220_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_a_212_);
lean_dec(v___x_211_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_220_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___x_216_; lean_object* v___x_218_; 
lean_inc(v_ref_210_);
v___x_216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_216_, 0, v_ref_210_);
lean_ctor_set(v___x_216_, 1, v_a_212_);
if (v_isShared_215_ == 0)
{
lean_ctor_set_tag(v___x_214_, 1);
lean_ctor_set(v___x_214_, 0, v___x_216_);
v___x_218_ = v___x_214_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v___x_216_);
v___x_218_ = v_reuseFailAlloc_219_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
return v___x_218_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1___redArg___boxed(lean_object* v_msg_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1___redArg(v_msg_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_);
lean_dec(v___y_225_);
lean_dec_ref(v___y_224_);
lean_dec(v___y_223_);
lean_dec_ref(v___y_222_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_bvDecide___lam__0(lean_object* v_a_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality(v_a_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_);
if (lean_obj_tag(v___x_234_) == 0)
{
lean_object* v_a_235_; lean_object* v___x_236_; lean_object* v_a_237_; lean_object* v___x_238_; 
v_a_235_ = lean_ctor_get(v___x_234_, 0);
lean_inc(v_a_235_);
lean_dec_ref_known(v___x_234_, 1);
v___x_236_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__0(v_a_235_, v___y_229_, v___y_230_, v___y_231_, v___y_232_);
v_a_237_ = lean_ctor_get(v___x_236_, 0);
lean_inc(v_a_237_);
lean_dec_ref(v___x_236_);
v___x_238_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1___redArg(v_a_237_, v___y_229_, v___y_230_, v___y_231_, v___y_232_);
return v___x_238_;
}
else
{
lean_object* v_a_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_246_; 
v_a_239_ = lean_ctor_get(v___x_234_, 0);
v_isSharedCheck_246_ = !lean_is_exclusive(v___x_234_);
if (v_isSharedCheck_246_ == 0)
{
v___x_241_ = v___x_234_;
v_isShared_242_ = v_isSharedCheck_246_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_a_239_);
lean_dec(v___x_234_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_246_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___x_244_; 
if (v_isShared_242_ == 0)
{
v___x_244_ = v___x_241_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v_a_239_);
v___x_244_ = v_reuseFailAlloc_245_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
return v___x_244_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_bvDecide___lam__0___boxed(lean_object* v_a_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_Lean_Meta_Tactic_BVDecide_bvDecide___lam__0(v_a_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_);
lean_dec(v___y_251_);
lean_dec_ref(v___y_250_);
lean_dec(v___y_249_);
lean_dec_ref(v___y_248_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_bvDecide(lean_object* v_g_254_, lean_object* v_ctx_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_){
_start:
{
lean_object* v___x_261_; 
v___x_261_ = l_Lean_Meta_Tactic_BVDecide_bvDecide_x27(v_g_254_, v_ctx_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_);
if (lean_obj_tag(v___x_261_) == 0)
{
lean_object* v_a_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_274_; 
v_a_262_ = lean_ctor_get(v___x_261_, 0);
v_isSharedCheck_274_ = !lean_is_exclusive(v___x_261_);
if (v_isSharedCheck_274_ == 0)
{
v___x_264_ = v___x_261_;
v_isShared_265_ = v_isSharedCheck_274_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_a_262_);
lean_dec(v___x_261_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_274_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
if (lean_obj_tag(v_a_262_) == 0)
{
lean_object* v_a_266_; lean_object* v_goal_267_; lean_object* v___f_268_; lean_object* v___x_269_; 
lean_del_object(v___x_264_);
v_a_266_ = lean_ctor_get(v_a_262_, 0);
lean_inc(v_a_266_);
lean_dec_ref_known(v_a_262_, 1);
v_goal_267_ = lean_ctor_get(v_a_266_, 0);
lean_inc(v_goal_267_);
v___f_268_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_bvDecide___lam__0___boxed), 6, 1);
lean_closure_set(v___f_268_, 0, v_a_266_);
v___x_269_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2___redArg(v_goal_267_, v___f_268_, v_a_256_, v_a_257_, v_a_258_, v_a_259_);
return v___x_269_;
}
else
{
lean_object* v_a_270_; lean_object* v___x_272_; 
v_a_270_ = lean_ctor_get(v_a_262_, 0);
lean_inc(v_a_270_);
lean_dec_ref_known(v_a_262_, 1);
if (v_isShared_265_ == 0)
{
lean_ctor_set(v___x_264_, 0, v_a_270_);
v___x_272_ = v___x_264_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v_a_270_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
return v___x_272_;
}
}
}
}
else
{
lean_object* v_a_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_282_; 
v_a_275_ = lean_ctor_get(v___x_261_, 0);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_261_);
if (v_isSharedCheck_282_ == 0)
{
v___x_277_ = v___x_261_;
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_a_275_);
lean_dec(v___x_261_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v___x_280_; 
if (v_isShared_278_ == 0)
{
v___x_280_ = v___x_277_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_a_275_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_bvDecide___boxed(lean_object* v_g_283_, lean_object* v_ctx_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Lean_Meta_Tactic_BVDecide_bvDecide(v_g_283_, v_ctx_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_);
lean_dec(v_a_288_);
lean_dec_ref(v_a_287_);
lean_dec(v_a_286_);
lean_dec_ref(v_a_285_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1(lean_object* v_00_u03b1_291_, lean_object* v_msg_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_){
_start:
{
lean_object* v___x_298_; 
v___x_298_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1___redArg(v_msg_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1___boxed(lean_object* v_00_u03b1_299_, lean_object* v_msg_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1(v_00_u03b1_299_, v_msg_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_);
lean_dec(v___y_304_);
lean_dec_ref(v___y_303_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
return v_res_306_;
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

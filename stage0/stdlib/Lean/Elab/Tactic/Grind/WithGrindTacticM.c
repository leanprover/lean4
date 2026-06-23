// Lean compiler output
// Module: Lean.Elab.Tactic.Grind.WithGrindTacticM
// Imports: public import Lean.Elab.Tactic.Grind.Basic public import Lean.Elab.Command
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
lean_object* l_Lean_Meta_Grind_mkDefaultParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_GrindM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_GrindTacticM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "registerSymSimp"};
static const lean_object* l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(89, 44, 7, 5, 125, 65, 241, 52)}};
static const lean_object* l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__2;
static lean_once_cell_t l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__3;
static lean_once_cell_t l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__4;
static lean_once_cell_t l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__5;
static lean_once_cell_t l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withGrindTacticM___redArg___lam__1(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withGrindTacticM___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Command_withGrindTacticM___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*13 + 32, .m_other = 13, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(9) << 1) | 1)),((lean_object*)(((size_t)(5) << 1) | 1)),((lean_object*)(((size_t)(8) << 1) | 1)),((lean_object*)(((size_t)(8) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(100000) << 1) | 1)),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(1048576) << 1) | 1)),((lean_object*)(((size_t)(10) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(0, 0, 1, 0, 1, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(1, 0, 1, 1, 1, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 1, 1, 0, 1, 1)}};
static const lean_object* l_Lean_Elab_Command_withGrindTacticM___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Command_withGrindTacticM___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withGrindTacticM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withGrindTacticM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withGrindTacticM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withGrindTacticM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4_;
}
}
static lean_object* _init_l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_obj_once(&l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__2, &l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__2_once, _init_l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__2);
v___x_6_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
static lean_object* _init_l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__4(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_7_ = lean_box(0);
v___x_8_ = lean_unsigned_to_nat(16u);
v___x_9_ = lean_mk_array(v___x_8_, v___x_7_);
return v___x_9_;
}
}
static lean_object* _init_l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_10_ = lean_obj_once(&l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__4, &l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__4_once, _init_l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__4);
v___x_11_ = lean_unsigned_to_nat(0u);
v___x_12_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_12_, 0, v___x_11_);
lean_ctor_set(v___x_12_, 1, v___x_10_);
return v___x_12_;
}
}
static lean_object* _init_l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__6(void){
_start:
{
lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_13_ = lean_obj_once(&l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__5, &l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__5_once, _init_l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__5);
v___x_14_ = lean_obj_once(&l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__3, &l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__3_once, _init_l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__3);
v___x_15_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_15_, 0, v___x_14_);
lean_ctor_set(v___x_15_, 1, v___x_14_);
lean_ctor_set(v___x_15_, 2, v___x_13_);
lean_ctor_set(v___x_15_, 3, v___x_13_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0(uint8_t v___x_16_, lean_object* v_a_17_, uint8_t v___x_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_29_ = lean_st_ref_get(v___y_21_);
v___x_30_ = lean_st_ref_get(v___y_23_);
v___x_31_ = ((lean_object*)(l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__1));
v___x_32_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_32_, 0, v___x_31_);
lean_ctor_set_uint8(v___x_32_, sizeof(void*)*1, v___x_16_);
lean_inc(v___y_19_);
lean_inc_ref(v___y_22_);
lean_inc_ref(v___y_20_);
v___x_33_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_33_, 0, v___x_32_);
lean_ctor_set(v___x_33_, 1, v___y_20_);
lean_ctor_set(v___x_33_, 2, v___y_22_);
lean_ctor_set(v___x_33_, 3, v___y_19_);
lean_ctor_set(v___x_33_, 4, v_a_17_);
lean_ctor_set_uint8(v___x_33_, sizeof(void*)*5, v___x_18_);
v___x_34_ = lean_box(0);
v___x_35_ = lean_obj_once(&l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__6, &l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__6_once, _init_l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__6);
v___x_36_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_36_, 0, v___x_30_);
lean_ctor_set(v___x_36_, 1, v___x_29_);
lean_ctor_set(v___x_36_, 2, v___x_34_);
lean_ctor_set(v___x_36_, 3, v___x_35_);
v___x_37_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_37_, 0, v___x_33_);
lean_ctor_set(v___x_37_, 1, v___x_36_);
v___x_38_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_38_, 0, v___x_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___boxed(lean_object* v___x_39_, lean_object* v_a_40_, lean_object* v___x_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_){
_start:
{
uint8_t v___x_8495__boxed_52_; uint8_t v___x_8497__boxed_53_; lean_object* v_res_54_; 
v___x_8495__boxed_52_ = lean_unbox(v___x_39_);
v___x_8497__boxed_53_ = lean_unbox(v___x_41_);
v_res_54_ = l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0(v___x_8495__boxed_52_, v_a_40_, v___x_8497__boxed_53_, v___y_42_, v___y_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_, v___y_48_, v___y_49_, v___y_50_);
lean_dec(v___y_50_);
lean_dec_ref(v___y_49_);
lean_dec(v___y_48_);
lean_dec_ref(v___y_47_);
lean_dec(v___y_46_);
lean_dec_ref(v___y_45_);
lean_dec(v___y_44_);
lean_dec_ref(v___y_43_);
lean_dec(v___y_42_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withGrindTacticM___redArg___lam__1(lean_object* v___x_55_, uint8_t v___x_56_, uint8_t v___x_57_, lean_object* v_k_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = l_Lean_Meta_Grind_mkDefaultParams(v___x_55_, v___y_61_, v___y_62_, v___y_63_, v___y_64_);
if (lean_obj_tag(v___x_66_) == 0)
{
lean_object* v_a_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___f_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v_a_67_ = lean_ctor_get(v___x_66_, 0);
lean_inc_n(v_a_67_, 2);
lean_dec_ref_known(v___x_66_, 1);
v___x_68_ = lean_box(v___x_56_);
v___x_69_ = lean_box(v___x_57_);
v___f_70_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___boxed), 13, 3);
lean_closure_set(v___f_70_, 0, v___x_68_);
lean_closure_set(v___f_70_, 1, v_a_67_);
lean_closure_set(v___f_70_, 2, v___x_69_);
v___x_71_ = lean_box(0);
v___x_72_ = l_Lean_Meta_Grind_GrindM_run___redArg(v___f_70_, v_a_67_, v___x_71_, v___y_61_, v___y_62_, v___y_63_, v___y_64_);
if (lean_obj_tag(v___x_72_) == 0)
{
lean_object* v_a_73_; lean_object* v_fst_74_; lean_object* v_snd_75_; lean_object* v___x_76_; 
v_a_73_ = lean_ctor_get(v___x_72_, 0);
lean_inc(v_a_73_);
lean_dec_ref_known(v___x_72_, 1);
v_fst_74_ = lean_ctor_get(v_a_73_, 0);
lean_inc(v_fst_74_);
v_snd_75_ = lean_ctor_get(v_a_73_, 1);
lean_inc(v_snd_75_);
lean_dec(v_a_73_);
v___x_76_ = l_Lean_Elab_Tactic_Grind_GrindTacticM_run___redArg(v_k_58_, v_fst_74_, v_snd_75_, v___y_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_);
if (lean_obj_tag(v___x_76_) == 0)
{
lean_object* v_a_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_85_; 
v_a_77_ = lean_ctor_get(v___x_76_, 0);
v_isSharedCheck_85_ = !lean_is_exclusive(v___x_76_);
if (v_isSharedCheck_85_ == 0)
{
v___x_79_ = v___x_76_;
v_isShared_80_ = v_isSharedCheck_85_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_a_77_);
lean_dec(v___x_76_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_85_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
lean_object* v_fst_81_; lean_object* v___x_83_; 
v_fst_81_ = lean_ctor_get(v_a_77_, 0);
lean_inc(v_fst_81_);
lean_dec(v_a_77_);
if (v_isShared_80_ == 0)
{
lean_ctor_set(v___x_79_, 0, v_fst_81_);
v___x_83_ = v___x_79_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_84_; 
v_reuseFailAlloc_84_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_84_, 0, v_fst_81_);
v___x_83_ = v_reuseFailAlloc_84_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
return v___x_83_;
}
}
}
else
{
lean_object* v_a_86_; lean_object* v___x_88_; uint8_t v_isShared_89_; uint8_t v_isSharedCheck_93_; 
v_a_86_ = lean_ctor_get(v___x_76_, 0);
v_isSharedCheck_93_ = !lean_is_exclusive(v___x_76_);
if (v_isSharedCheck_93_ == 0)
{
v___x_88_ = v___x_76_;
v_isShared_89_ = v_isSharedCheck_93_;
goto v_resetjp_87_;
}
else
{
lean_inc(v_a_86_);
lean_dec(v___x_76_);
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
lean_object* v_a_94_; lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_101_; 
lean_dec_ref(v_k_58_);
v_a_94_ = lean_ctor_get(v___x_72_, 0);
v_isSharedCheck_101_ = !lean_is_exclusive(v___x_72_);
if (v_isSharedCheck_101_ == 0)
{
v___x_96_ = v___x_72_;
v_isShared_97_ = v_isSharedCheck_101_;
goto v_resetjp_95_;
}
else
{
lean_inc(v_a_94_);
lean_dec(v___x_72_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_101_;
goto v_resetjp_95_;
}
v_resetjp_95_:
{
lean_object* v___x_99_; 
if (v_isShared_97_ == 0)
{
v___x_99_ = v___x_96_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v_a_94_);
v___x_99_ = v_reuseFailAlloc_100_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
return v___x_99_;
}
}
}
}
else
{
lean_object* v_a_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_109_; 
lean_dec_ref(v_k_58_);
v_a_102_ = lean_ctor_get(v___x_66_, 0);
v_isSharedCheck_109_ = !lean_is_exclusive(v___x_66_);
if (v_isSharedCheck_109_ == 0)
{
v___x_104_ = v___x_66_;
v_isShared_105_ = v_isSharedCheck_109_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_a_102_);
lean_dec(v___x_66_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_109_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v___x_107_; 
if (v_isShared_105_ == 0)
{
v___x_107_ = v___x_104_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v_a_102_);
v___x_107_ = v_reuseFailAlloc_108_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
return v___x_107_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withGrindTacticM___redArg___lam__1___boxed(lean_object* v___x_110_, lean_object* v___x_111_, lean_object* v___x_112_, lean_object* v_k_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_){
_start:
{
uint8_t v___x_8570__boxed_121_; uint8_t v___x_8571__boxed_122_; lean_object* v_res_123_; 
v___x_8570__boxed_121_ = lean_unbox(v___x_111_);
v___x_8571__boxed_122_ = lean_unbox(v___x_112_);
v_res_123_ = l_Lean_Elab_Command_withGrindTacticM___redArg___lam__1(v___x_110_, v___x_8570__boxed_121_, v___x_8571__boxed_122_, v_k_113_, v___y_114_, v___y_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_);
lean_dec(v___y_119_);
lean_dec_ref(v___y_118_);
lean_dec(v___y_117_);
lean_dec_ref(v___y_116_);
lean_dec(v___y_115_);
lean_dec_ref(v___y_114_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withGrindTacticM___redArg(lean_object* v_k_137_, lean_object* v_a_138_, lean_object* v_a_139_){
_start:
{
uint8_t v___x_141_; uint8_t v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___f_146_; lean_object* v___x_147_; 
v___x_141_ = 0;
v___x_142_ = 1;
v___x_143_ = ((lean_object*)(l_Lean_Elab_Command_withGrindTacticM___redArg___closed__0));
v___x_144_ = lean_box(v___x_142_);
v___x_145_ = lean_box(v___x_141_);
v___f_146_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_withGrindTacticM___redArg___lam__1___boxed), 11, 4);
lean_closure_set(v___f_146_, 0, v___x_143_);
lean_closure_set(v___f_146_, 1, v___x_144_);
lean_closure_set(v___f_146_, 2, v___x_145_);
lean_closure_set(v___f_146_, 3, v_k_137_);
v___x_147_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_146_, v_a_138_, v_a_139_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withGrindTacticM___redArg___boxed(lean_object* v_k_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_Lean_Elab_Command_withGrindTacticM___redArg(v_k_148_, v_a_149_, v_a_150_);
lean_dec(v_a_150_);
lean_dec_ref(v_a_149_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withGrindTacticM(lean_object* v_00_u03b1_153_, lean_object* v_k_154_, lean_object* v_a_155_, lean_object* v_a_156_){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = l_Lean_Elab_Command_withGrindTacticM___redArg(v_k_154_, v_a_155_, v_a_156_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withGrindTacticM___boxed(lean_object* v_00_u03b1_159_, lean_object* v_k_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_Lean_Elab_Command_withGrindTacticM(v_00_u03b1_159_, v_k_160_, v_a_161_, v_a_162_);
lean_dec(v_a_162_);
lean_dec_ref(v_a_161_);
return v_res_164_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_WithGrindTacticM(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Tactic_Grind_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Grind_WithGrindTacticM(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Grind_Basic(uint8_t builtin);
lean_object* initialize_Lean_Elab_Command(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Grind_WithGrindTacticM(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Grind_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Grind_WithGrindTacticM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Grind_WithGrindTacticM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Grind_WithGrindTacticM(builtin);
}
#ifdef __cplusplus
}
#endif

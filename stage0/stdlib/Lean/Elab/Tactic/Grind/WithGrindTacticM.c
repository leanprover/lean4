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
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
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
static lean_once_cell_t l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withGrindTacticM___redArg___lam__1(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withGrindTacticM___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Command_withGrindTacticM___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*14 + 40, .m_other = 14, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(9) << 1) | 1)),((lean_object*)(((size_t)(5) << 1) | 1)),((lean_object*)(((size_t)(8) << 1) | 1)),((lean_object*)(((size_t)(8) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(100000) << 1) | 1)),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)(((size_t)(10000) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(1048576) << 1) | 1)),((lean_object*)(((size_t)(10) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(0, 0, 1, 0, 1, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(1, 0, 1, 1, 1, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 1, 1, 1, 0, 1),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
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
lean_object* v_cellCount_7_; lean_object* v___x_8_; 
v_cellCount_7_ = lean_unsigned_to_nat(16u);
v___x_8_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_7_);
return v___x_8_;
}
}
static lean_object* _init_l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__5(void){
_start:
{
lean_object* v_cellCount_9_; lean_object* v___x_10_; 
v_cellCount_9_ = lean_unsigned_to_nat(16u);
v___x_10_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_9_);
return v___x_10_;
}
}
static lean_object* _init_l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__6(void){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_11_ = lean_obj_once(&l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__5, &l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__5_once, _init_l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__5);
v___x_12_ = lean_obj_once(&l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__4, &l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__4_once, _init_l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__4);
v___x_13_ = lean_unsigned_to_nat(0u);
v___x_14_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_14_, 0, v___x_13_);
lean_ctor_set(v___x_14_, 1, v___x_12_);
lean_ctor_set(v___x_14_, 2, v___x_11_);
return v___x_14_;
}
}
static lean_object* _init_l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__7(void){
_start:
{
lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_15_ = lean_obj_once(&l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__6, &l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__6_once, _init_l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__6);
v___x_16_ = lean_obj_once(&l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__3, &l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__3_once, _init_l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__3);
v___x_17_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_17_, 0, v___x_16_);
lean_ctor_set(v___x_17_, 1, v___x_16_);
lean_ctor_set(v___x_17_, 2, v___x_15_);
lean_ctor_set(v___x_17_, 3, v___x_15_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0(uint8_t v___x_18_, lean_object* v_a_19_, uint8_t v___x_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_31_ = lean_st_ref_get(v___y_23_);
v___x_32_ = lean_st_ref_get(v___y_25_);
v___x_33_ = ((lean_object*)(l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__1));
v___x_34_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_34_, 0, v___x_33_);
lean_ctor_set_uint8(v___x_34_, sizeof(void*)*1, v___x_18_);
lean_inc(v___y_21_);
lean_inc_ref(v___y_24_);
lean_inc_ref(v___y_22_);
v___x_35_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_35_, 0, v___x_34_);
lean_ctor_set(v___x_35_, 1, v___y_22_);
lean_ctor_set(v___x_35_, 2, v___y_24_);
lean_ctor_set(v___x_35_, 3, v___y_21_);
lean_ctor_set(v___x_35_, 4, v_a_19_);
lean_ctor_set_uint8(v___x_35_, sizeof(void*)*5, v___x_20_);
v___x_36_ = lean_box(0);
v___x_37_ = lean_obj_once(&l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__7, &l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__7_once, _init_l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__7);
v___x_38_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_38_, 0, v___x_32_);
lean_ctor_set(v___x_38_, 1, v___x_31_);
lean_ctor_set(v___x_38_, 2, v___x_36_);
lean_ctor_set(v___x_38_, 3, v___x_37_);
v___x_39_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_39_, 0, v___x_35_);
lean_ctor_set(v___x_39_, 1, v___x_38_);
v___x_40_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_40_, 0, v___x_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___boxed(lean_object* v___x_41_, lean_object* v_a_42_, lean_object* v___x_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_){
_start:
{
uint8_t v___x_8332__boxed_54_; uint8_t v___x_8334__boxed_55_; lean_object* v_res_56_; 
v___x_8332__boxed_54_ = lean_unbox(v___x_41_);
v___x_8334__boxed_55_ = lean_unbox(v___x_43_);
v_res_56_ = l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0(v___x_8332__boxed_54_, v_a_42_, v___x_8334__boxed_55_, v___y_44_, v___y_45_, v___y_46_, v___y_47_, v___y_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_);
lean_dec(v___y_52_);
lean_dec_ref(v___y_51_);
lean_dec(v___y_50_);
lean_dec_ref(v___y_49_);
lean_dec(v___y_48_);
lean_dec_ref(v___y_47_);
lean_dec(v___y_46_);
lean_dec_ref(v___y_45_);
lean_dec(v___y_44_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withGrindTacticM___redArg___lam__1(lean_object* v___x_57_, uint8_t v___x_58_, uint8_t v___x_59_, lean_object* v_k_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = l_Lean_Meta_Grind_mkDefaultParams(v___x_57_, v___y_63_, v___y_64_, v___y_65_, v___y_66_);
if (lean_obj_tag(v___x_68_) == 0)
{
lean_object* v_a_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___f_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v_a_69_ = lean_ctor_get(v___x_68_, 0);
lean_inc_n(v_a_69_, 2);
lean_dec_ref_known(v___x_68_, 1);
v___x_70_ = lean_box(v___x_58_);
v___x_71_ = lean_box(v___x_59_);
v___f_72_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___boxed), 13, 3);
lean_closure_set(v___f_72_, 0, v___x_70_);
lean_closure_set(v___f_72_, 1, v_a_69_);
lean_closure_set(v___f_72_, 2, v___x_71_);
v___x_73_ = lean_box(0);
v___x_74_ = l_Lean_Meta_Grind_GrindM_run___redArg(v___f_72_, v_a_69_, v___x_73_, v___y_63_, v___y_64_, v___y_65_, v___y_66_);
if (lean_obj_tag(v___x_74_) == 0)
{
lean_object* v_a_75_; lean_object* v_fst_76_; lean_object* v_snd_77_; lean_object* v___x_78_; 
v_a_75_ = lean_ctor_get(v___x_74_, 0);
lean_inc(v_a_75_);
lean_dec_ref_known(v___x_74_, 1);
v_fst_76_ = lean_ctor_get(v_a_75_, 0);
lean_inc(v_fst_76_);
v_snd_77_ = lean_ctor_get(v_a_75_, 1);
lean_inc(v_snd_77_);
lean_dec(v_a_75_);
v___x_78_ = l_Lean_Elab_Tactic_Grind_GrindTacticM_run___redArg(v_k_60_, v_fst_76_, v_snd_77_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_);
if (lean_obj_tag(v___x_78_) == 0)
{
lean_object* v_a_79_; lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_87_; 
v_a_79_ = lean_ctor_get(v___x_78_, 0);
v_isSharedCheck_87_ = !lean_is_exclusive(v___x_78_);
if (v_isSharedCheck_87_ == 0)
{
v___x_81_ = v___x_78_;
v_isShared_82_ = v_isSharedCheck_87_;
goto v_resetjp_80_;
}
else
{
lean_inc(v_a_79_);
lean_dec(v___x_78_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_87_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
lean_object* v_fst_83_; lean_object* v___x_85_; 
v_fst_83_ = lean_ctor_get(v_a_79_, 0);
lean_inc(v_fst_83_);
lean_dec(v_a_79_);
if (v_isShared_82_ == 0)
{
lean_ctor_set(v___x_81_, 0, v_fst_83_);
v___x_85_ = v___x_81_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_86_; 
v_reuseFailAlloc_86_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_86_, 0, v_fst_83_);
v___x_85_ = v_reuseFailAlloc_86_;
goto v_reusejp_84_;
}
v_reusejp_84_:
{
return v___x_85_;
}
}
}
else
{
lean_object* v_a_88_; lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_95_; 
v_a_88_ = lean_ctor_get(v___x_78_, 0);
v_isSharedCheck_95_ = !lean_is_exclusive(v___x_78_);
if (v_isSharedCheck_95_ == 0)
{
v___x_90_ = v___x_78_;
v_isShared_91_ = v_isSharedCheck_95_;
goto v_resetjp_89_;
}
else
{
lean_inc(v_a_88_);
lean_dec(v___x_78_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_95_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
lean_object* v___x_93_; 
if (v_isShared_91_ == 0)
{
v___x_93_ = v___x_90_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v_a_88_);
v___x_93_ = v_reuseFailAlloc_94_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
return v___x_93_;
}
}
}
}
else
{
lean_object* v_a_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_103_; 
lean_dec_ref(v_k_60_);
v_a_96_ = lean_ctor_get(v___x_74_, 0);
v_isSharedCheck_103_ = !lean_is_exclusive(v___x_74_);
if (v_isSharedCheck_103_ == 0)
{
v___x_98_ = v___x_74_;
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_a_96_);
lean_dec(v___x_74_);
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
lean_object* v_a_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_111_; 
lean_dec_ref(v_k_60_);
v_a_104_ = lean_ctor_get(v___x_68_, 0);
v_isSharedCheck_111_ = !lean_is_exclusive(v___x_68_);
if (v_isSharedCheck_111_ == 0)
{
v___x_106_ = v___x_68_;
v_isShared_107_ = v_isSharedCheck_111_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_a_104_);
lean_dec(v___x_68_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_111_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
lean_object* v___x_109_; 
if (v_isShared_107_ == 0)
{
v___x_109_ = v___x_106_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v_a_104_);
v___x_109_ = v_reuseFailAlloc_110_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
return v___x_109_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withGrindTacticM___redArg___lam__1___boxed(lean_object* v___x_112_, lean_object* v___x_113_, lean_object* v___x_114_, lean_object* v_k_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_){
_start:
{
uint8_t v___x_8407__boxed_123_; uint8_t v___x_8408__boxed_124_; lean_object* v_res_125_; 
v___x_8407__boxed_123_ = lean_unbox(v___x_113_);
v___x_8408__boxed_124_ = lean_unbox(v___x_114_);
v_res_125_ = l_Lean_Elab_Command_withGrindTacticM___redArg___lam__1(v___x_112_, v___x_8407__boxed_123_, v___x_8408__boxed_124_, v_k_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_, v___y_120_, v___y_121_);
lean_dec(v___y_121_);
lean_dec_ref(v___y_120_);
lean_dec(v___y_119_);
lean_dec_ref(v___y_118_);
lean_dec(v___y_117_);
lean_dec_ref(v___y_116_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withGrindTacticM___redArg(lean_object* v_k_140_, lean_object* v_a_141_, lean_object* v_a_142_){
_start:
{
uint8_t v___x_144_; uint8_t v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___f_149_; lean_object* v___x_150_; 
v___x_144_ = 0;
v___x_145_ = 1;
v___x_146_ = ((lean_object*)(l_Lean_Elab_Command_withGrindTacticM___redArg___closed__0));
v___x_147_ = lean_box(v___x_145_);
v___x_148_ = lean_box(v___x_144_);
v___f_149_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_withGrindTacticM___redArg___lam__1___boxed), 11, 4);
lean_closure_set(v___f_149_, 0, v___x_146_);
lean_closure_set(v___f_149_, 1, v___x_147_);
lean_closure_set(v___f_149_, 2, v___x_148_);
lean_closure_set(v___f_149_, 3, v_k_140_);
v___x_150_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_149_, v_a_141_, v_a_142_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withGrindTacticM___redArg___boxed(lean_object* v_k_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l_Lean_Elab_Command_withGrindTacticM___redArg(v_k_151_, v_a_152_, v_a_153_);
lean_dec(v_a_153_);
lean_dec_ref(v_a_152_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withGrindTacticM(lean_object* v_00_u03b1_156_, lean_object* v_k_157_, lean_object* v_a_158_, lean_object* v_a_159_){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = l_Lean_Elab_Command_withGrindTacticM___redArg(v_k_157_, v_a_158_, v_a_159_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withGrindTacticM___boxed(lean_object* v_00_u03b1_162_, lean_object* v_k_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_Lean_Elab_Command_withGrindTacticM(v_00_u03b1_162_, v_k_163_, v_a_164_, v_a_165_);
lean_dec(v_a_165_);
lean_dec_ref(v_a_164_);
return v_res_167_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_WithGrindTacticM(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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

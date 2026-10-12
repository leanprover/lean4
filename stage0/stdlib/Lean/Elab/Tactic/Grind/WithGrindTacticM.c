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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
v___x_4_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0(uint8_t v___x_16_, lean_object* v_a_17_, uint8_t v___x_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_){
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
LEAN_EXPORT void l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_16_ = stack[0].m_num;
lean_object* v_a_17_ = stack[1].m_obj;
uint8_t v___x_18_ = stack[2].m_num;
lean_object* v___y_19_ = stack[3].m_obj;
lean_object* v___y_20_ = stack[4].m_obj;
lean_object* v___y_21_ = stack[5].m_obj;
lean_object* v___y_22_ = stack[6].m_obj;
lean_object* v___y_23_ = stack[7].m_obj;
lean_object* v___y_24_ = stack[8].m_obj;
lean_object* v___y_25_ = stack[9].m_obj;
lean_object* v___y_26_ = stack[10].m_obj;
lean_object* v___y_27_ = stack[11].m_obj;
lean_object* v_res_39_;
v_res_39_ = l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0(v___x_16_, v_a_17_, v___x_18_, v___y_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_);
stack->m_obj
 = v_res_39_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___boxed(lean_object* v___x_40_, lean_object* v_a_41_, lean_object* v___x_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_){
_start:
{
uint8_t v___x_8504__boxed_53_; uint8_t v___x_8506__boxed_54_; lean_object* v_res_55_; 
v___x_8504__boxed_53_ = lean_unbox(v___x_40_);
v___x_8506__boxed_54_ = lean_unbox(v___x_42_);
v_res_55_ = l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0(v___x_8504__boxed_53_, v_a_41_, v___x_8506__boxed_54_, v___y_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_, v___y_48_, v___y_49_, v___y_50_, v___y_51_);
lean_dec(v___y_51_);
lean_dec_ref(v___y_50_);
lean_dec(v___y_49_);
lean_dec_ref(v___y_48_);
lean_dec(v___y_47_);
lean_dec_ref(v___y_46_);
lean_dec(v___y_45_);
lean_dec_ref(v___y_44_);
lean_dec(v___y_43_);
return v_res_55_;
}
}
lean_object* l_Lean_Elab_Command_withGrindTacticM___redArg___lam__1(lean_object* v___x_56_, uint8_t v___x_57_, uint8_t v___x_58_, lean_object* v_k_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = l_Lean_Meta_Grind_mkDefaultParams(v___x_56_, v___y_62_, v___y_63_, v___y_64_, v___y_65_);
if (lean_obj_tag(v___x_67_) == 0)
{
lean_object* v_a_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___f_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v_a_68_ = lean_ctor_get(v___x_67_, 0);
lean_inc_n(v_a_68_, 2);
lean_dec_ref_known(v___x_67_, 1);
v___x_69_ = lean_box(v___x_57_);
v___x_70_ = lean_box(v___x_58_);
v___f_71_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___boxed), 13, 3);
lean_closure_set(v___f_71_, 0, v___x_69_);
lean_closure_set(v___f_71_, 1, v_a_68_);
lean_closure_set(v___f_71_, 2, v___x_70_);
v___x_72_ = lean_box(0);
v___x_73_ = l_Lean_Meta_Grind_GrindM_run___redArg(v___f_71_, v_a_68_, v___x_72_, v___y_62_, v___y_63_, v___y_64_, v___y_65_);
if (lean_obj_tag(v___x_73_) == 0)
{
lean_object* v_a_74_; lean_object* v_fst_75_; lean_object* v_snd_76_; lean_object* v___x_77_; 
v_a_74_ = lean_ctor_get(v___x_73_, 0);
lean_inc(v_a_74_);
lean_dec_ref_known(v___x_73_, 1);
v_fst_75_ = lean_ctor_get(v_a_74_, 0);
lean_inc(v_fst_75_);
v_snd_76_ = lean_ctor_get(v_a_74_, 1);
lean_inc(v_snd_76_);
lean_dec(v_a_74_);
v___x_77_ = l_Lean_Elab_Tactic_Grind_GrindTacticM_run___redArg(v_k_59_, v_fst_75_, v_snd_76_, v___y_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_);
if (lean_obj_tag(v___x_77_) == 0)
{
lean_object* v_a_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_86_; 
v_a_78_ = lean_ctor_get(v___x_77_, 0);
v_isSharedCheck_86_ = !lean_is_exclusive(v___x_77_);
if (v_isSharedCheck_86_ == 0)
{
v___x_80_ = v___x_77_;
v_isShared_81_ = v_isSharedCheck_86_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_a_78_);
lean_dec(v___x_77_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_86_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
lean_object* v_fst_82_; lean_object* v___x_84_; 
v_fst_82_ = lean_ctor_get(v_a_78_, 0);
lean_inc(v_fst_82_);
lean_dec(v_a_78_);
if (v_isShared_81_ == 0)
{
lean_ctor_set(v___x_80_, 0, v_fst_82_);
v___x_84_ = v___x_80_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v_fst_82_);
v___x_84_ = v_reuseFailAlloc_85_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
return v___x_84_;
}
}
}
else
{
lean_object* v_a_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_94_; 
v_a_87_ = lean_ctor_get(v___x_77_, 0);
v_isSharedCheck_94_ = !lean_is_exclusive(v___x_77_);
if (v_isSharedCheck_94_ == 0)
{
v___x_89_ = v___x_77_;
v_isShared_90_ = v_isSharedCheck_94_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_a_87_);
lean_dec(v___x_77_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_94_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v___x_92_; 
if (v_isShared_90_ == 0)
{
v___x_92_ = v___x_89_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v_a_87_);
v___x_92_ = v_reuseFailAlloc_93_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
return v___x_92_;
}
}
}
}
else
{
lean_object* v_a_95_; lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_102_; 
lean_dec_ref(v_k_59_);
v_a_95_ = lean_ctor_get(v___x_73_, 0);
v_isSharedCheck_102_ = !lean_is_exclusive(v___x_73_);
if (v_isSharedCheck_102_ == 0)
{
v___x_97_ = v___x_73_;
v_isShared_98_ = v_isSharedCheck_102_;
goto v_resetjp_96_;
}
else
{
lean_inc(v_a_95_);
lean_dec(v___x_73_);
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
}
else
{
lean_object* v_a_103_; lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_110_; 
lean_dec_ref(v_k_59_);
v_a_103_ = lean_ctor_get(v___x_67_, 0);
v_isSharedCheck_110_ = !lean_is_exclusive(v___x_67_);
if (v_isSharedCheck_110_ == 0)
{
v___x_105_ = v___x_67_;
v_isShared_106_ = v_isSharedCheck_110_;
goto v_resetjp_104_;
}
else
{
lean_inc(v_a_103_);
lean_dec(v___x_67_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_110_;
goto v_resetjp_104_;
}
v_resetjp_104_:
{
lean_object* v___x_108_; 
if (v_isShared_106_ == 0)
{
v___x_108_ = v___x_105_;
goto v_reusejp_107_;
}
else
{
lean_object* v_reuseFailAlloc_109_; 
v_reuseFailAlloc_109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_109_, 0, v_a_103_);
v___x_108_ = v_reuseFailAlloc_109_;
goto v_reusejp_107_;
}
v_reusejp_107_:
{
return v___x_108_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Command_withGrindTacticM___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_56_ = stack[0].m_obj;
uint8_t v___x_57_ = stack[1].m_num;
uint8_t v___x_58_ = stack[2].m_num;
lean_object* v_k_59_ = stack[3].m_obj;
lean_object* v___y_60_ = stack[4].m_obj;
lean_object* v___y_61_ = stack[5].m_obj;
lean_object* v___y_62_ = stack[6].m_obj;
lean_object* v___y_63_ = stack[7].m_obj;
lean_object* v___y_64_ = stack[8].m_obj;
lean_object* v___y_65_ = stack[9].m_obj;
lean_object* v_res_111_;
v_res_111_ = l_Lean_Elab_Command_withGrindTacticM___redArg___lam__1(v___x_56_, v___x_57_, v___x_58_, v_k_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_);
stack->m_obj
 = v_res_111_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withGrindTacticM___redArg___lam__1___boxed(lean_object* v___x_112_, lean_object* v___x_113_, lean_object* v___x_114_, lean_object* v_k_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_){
_start:
{
uint8_t v___x_8630__boxed_123_; uint8_t v___x_8631__boxed_124_; lean_object* v_res_125_; 
v___x_8630__boxed_123_ = lean_unbox(v___x_113_);
v___x_8631__boxed_124_ = lean_unbox(v___x_114_);
v_res_125_ = l_Lean_Elab_Command_withGrindTacticM___redArg___lam__1(v___x_112_, v___x_8630__boxed_123_, v___x_8631__boxed_124_, v_k_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_, v___y_120_, v___y_121_);
lean_dec(v___y_121_);
lean_dec_ref(v___y_120_);
lean_dec(v___y_119_);
lean_dec_ref(v___y_118_);
lean_dec(v___y_117_);
lean_dec_ref(v___y_116_);
return v_res_125_;
}
}
lean_object* l_Lean_Elab_Command_withGrindTacticM___redArg(lean_object* v_k_140_, lean_object* v_a_141_, lean_object* v_a_142_){
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
LEAN_EXPORT void l_Lean_Elab_Command_withGrindTacticM___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_140_ = stack[0].m_obj;
lean_object* v_a_141_ = stack[1].m_obj;
lean_object* v_a_142_ = stack[2].m_obj;
lean_object* v_res_151_;
v_res_151_ = l_Lean_Elab_Command_withGrindTacticM___redArg(v_k_140_, v_a_141_, v_a_142_);
stack->m_obj
 = v_res_151_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withGrindTacticM___redArg___boxed(lean_object* v_k_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Lean_Elab_Command_withGrindTacticM___redArg(v_k_152_, v_a_153_, v_a_154_);
lean_dec(v_a_154_);
lean_dec_ref(v_a_153_);
return v_res_156_;
}
}
lean_object* l_Lean_Elab_Command_withGrindTacticM(lean_object* v_00_u03b1_157_, lean_object* v_k_158_, lean_object* v_a_159_, lean_object* v_a_160_){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = l_Lean_Elab_Command_withGrindTacticM___redArg(v_k_158_, v_a_159_, v_a_160_);
return v___x_162_;
}
}
LEAN_EXPORT void l_Lean_Elab_Command_withGrindTacticM_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_158_ = stack[1].m_obj;
lean_object* v_a_159_ = stack[2].m_obj;
lean_object* v_a_160_ = stack[3].m_obj;
lean_object* v_res_163_;
v_res_163_ = l_Lean_Elab_Command_withGrindTacticM(lean_box(0), v_k_158_, v_a_159_, v_a_160_);
stack->m_obj
 = v_res_163_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withGrindTacticM___boxed(lean_object* v_00_u03b1_164_, lean_object* v_k_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Lean_Elab_Command_withGrindTacticM(v_00_u03b1_164_, v_k_165_, v_a_166_, v_a_167_);
lean_dec(v_a_167_);
lean_dec_ref(v_a_166_);
return v_res_169_;
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

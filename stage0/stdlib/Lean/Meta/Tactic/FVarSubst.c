// Lean compiler output
// Module: Lean.Meta.Tactic.FVarSubst
// Imports: public import Lean.Data.AssocList public import Lean.LocalContext public import Lean.Util.ReplaceExpr
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
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
uint8_t l_Lean_AssocList_isEmpty___redArg(lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* lean_replace_expr(lean_object*, lean_object*);
lean_object* l_Lean_Expr_replaceFVarId(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_AssocList_mapVal___redArg(lean_object*, lean_object*);
uint8_t l_Lean_AssocList_any___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedFVarSubst_default;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedFVarSubst;
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_empty;
LEAN_EXPORT uint8_t l_Lean_Meta_FVarSubst_isEmpty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_isEmpty___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at___00Lean_Meta_FVarSubst_contains_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at___00Lean_Meta_FVarSubst_contains_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_FVarSubst_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_contains___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at___00Lean_Meta_FVarSubst_contains_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at___00Lean_Meta_FVarSubst_contains_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_insert___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_insert___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_insert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_erase___at___00Lean_Meta_FVarSubst_erase_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_erase___at___00Lean_Meta_FVarSubst_erase_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_erase(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_erase___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_erase___at___00Lean_Meta_FVarSubst_erase_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_erase___at___00Lean_Meta_FVarSubst_erase_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___00Lean_Meta_FVarSubst_find_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___00Lean_Meta_FVarSubst_find_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_find_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_find_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___00Lean_Meta_FVarSubst_find_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___00Lean_Meta_FVarSubst_find_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_get___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_apply___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_apply___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_apply(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_apply___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at___00Lean_Meta_FVarSubst_domain_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at___00Lean_Meta_FVarSubst_domain_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_domain(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_domain___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_FVarSubst_any(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_any___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at___00Lean_Meta_FVarSubst_append_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_applyFVarSubst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_applyFVarSubst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_applyFVarSubst___boxed(lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_instInhabitedFVarSubst_default(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lean_box(0);
return v___x_1_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedFVarSubst(void){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
static lean_object* _init_l_Lean_Meta_FVarSubst_empty(void){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_box(0);
return v___x_3_;
}
}
uint8_t l_Lean_Meta_FVarSubst_isEmpty(lean_object* v_s_4_){
_start:
{
uint8_t v___x_5_; 
v___x_5_ = l_Lean_AssocList_isEmpty___redArg(v_s_4_);
return v___x_5_;
}
}
LEAN_EXPORT void l_Lean_Meta_FVarSubst_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_4_ = stack[0].m_obj;
uint8_t v_res_6_;
v_res_6_ = l_Lean_Meta_FVarSubst_isEmpty(v_s_4_);
stack->m_num = v_res_6_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_isEmpty___boxed(lean_object* v_s_7_){
_start:
{
uint8_t v_res_8_; lean_object* v_r_9_; 
v_res_8_ = l_Lean_Meta_FVarSubst_isEmpty(v_s_7_);
lean_dec(v_s_7_);
v_r_9_ = lean_box(v_res_8_);
return v_r_9_;
}
}
uint8_t l_Lean_AssocList_contains___at___00Lean_Meta_FVarSubst_contains_spec__0___redArg(lean_object* v_a_10_, lean_object* v_x_11_){
_start:
{
if (lean_obj_tag(v_x_11_) == 0)
{
uint8_t v___x_12_; 
v___x_12_ = 0;
return v___x_12_;
}
else
{
lean_object* v_key_13_; lean_object* v_tail_14_; uint8_t v___x_15_; 
v_key_13_ = lean_ctor_get(v_x_11_, 0);
v_tail_14_ = lean_ctor_get(v_x_11_, 2);
v___x_15_ = l_Lean_instBEqFVarId_beq(v_key_13_, v_a_10_);
if (v___x_15_ == 0)
{
v_x_11_ = v_tail_14_;
goto _start;
}
else
{
return v___x_15_;
}
}
}
}
LEAN_EXPORT void l_Lean_AssocList_contains___at___00Lean_Meta_FVarSubst_contains_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_10_ = stack[0].m_obj;
lean_object* v_x_11_ = stack[1].m_obj;
uint8_t v_res_17_;
v_res_17_ = l_Lean_AssocList_contains___at___00Lean_Meta_FVarSubst_contains_spec__0___redArg(v_a_10_, v_x_11_);
stack->m_num = v_res_17_;
}
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at___00Lean_Meta_FVarSubst_contains_spec__0___redArg___boxed(lean_object* v_a_18_, lean_object* v_x_19_){
_start:
{
uint8_t v_res_20_; lean_object* v_r_21_; 
v_res_20_ = l_Lean_AssocList_contains___at___00Lean_Meta_FVarSubst_contains_spec__0___redArg(v_a_18_, v_x_19_);
lean_dec(v_x_19_);
lean_dec(v_a_18_);
v_r_21_ = lean_box(v_res_20_);
return v_r_21_;
}
}
uint8_t l_Lean_Meta_FVarSubst_contains(lean_object* v_s_22_, lean_object* v_fvarId_23_){
_start:
{
uint8_t v___x_24_; 
v___x_24_ = l_Lean_AssocList_contains___at___00Lean_Meta_FVarSubst_contains_spec__0___redArg(v_fvarId_23_, v_s_22_);
return v___x_24_;
}
}
LEAN_EXPORT void l_Lean_Meta_FVarSubst_contains_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_22_ = stack[0].m_obj;
lean_object* v_fvarId_23_ = stack[1].m_obj;
uint8_t v_res_25_;
v_res_25_ = l_Lean_Meta_FVarSubst_contains(v_s_22_, v_fvarId_23_);
stack->m_num = v_res_25_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_contains___boxed(lean_object* v_s_26_, lean_object* v_fvarId_27_){
_start:
{
uint8_t v_res_28_; lean_object* v_r_29_; 
v_res_28_ = l_Lean_Meta_FVarSubst_contains(v_s_26_, v_fvarId_27_);
lean_dec(v_fvarId_27_);
lean_dec(v_s_26_);
v_r_29_ = lean_box(v_res_28_);
return v_r_29_;
}
}
uint8_t l_Lean_AssocList_contains___at___00Lean_Meta_FVarSubst_contains_spec__0(lean_object* v_00_u03b2_30_, lean_object* v_a_31_, lean_object* v_x_32_){
_start:
{
uint8_t v___x_33_; 
v___x_33_ = l_Lean_AssocList_contains___at___00Lean_Meta_FVarSubst_contains_spec__0___redArg(v_a_31_, v_x_32_);
return v___x_33_;
}
}
LEAN_EXPORT void l_Lean_AssocList_contains___at___00Lean_Meta_FVarSubst_contains_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_31_ = stack[1].m_obj;
lean_object* v_x_32_ = stack[2].m_obj;
uint8_t v_res_34_;
v_res_34_ = l_Lean_AssocList_contains___at___00Lean_Meta_FVarSubst_contains_spec__0(lean_box(0), v_a_31_, v_x_32_);
stack->m_num = v_res_34_;
}
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at___00Lean_Meta_FVarSubst_contains_spec__0___boxed(lean_object* v_00_u03b2_35_, lean_object* v_a_36_, lean_object* v_x_37_){
_start:
{
uint8_t v_res_38_; lean_object* v_r_39_; 
v_res_38_ = l_Lean_AssocList_contains___at___00Lean_Meta_FVarSubst_contains_spec__0(v_00_u03b2_35_, v_a_36_, v_x_37_);
lean_dec(v_x_37_);
lean_dec(v_a_36_);
v_r_39_ = lean_box(v_res_38_);
return v_r_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_insert___lam__0(lean_object* v_fvarId_40_, lean_object* v_v_41_, lean_object* v_e_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = l_Lean_Expr_replaceFVarId(v_e_42_, v_fvarId_40_, v_v_41_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_insert___lam__0___boxed(lean_object* v_fvarId_44_, lean_object* v_v_45_, lean_object* v_e_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_Lean_Meta_FVarSubst_insert___lam__0(v_fvarId_44_, v_v_45_, v_e_46_);
lean_dec_ref(v_e_46_);
lean_dec_ref(v_v_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_insert(lean_object* v_s_48_, lean_object* v_fvarId_49_, lean_object* v_v_50_){
_start:
{
uint8_t v___x_51_; 
v___x_51_ = l_Lean_AssocList_contains___at___00Lean_Meta_FVarSubst_contains_spec__0___redArg(v_fvarId_49_, v_s_48_);
if (v___x_51_ == 0)
{
lean_object* v___f_52_; lean_object* v_map_53_; lean_object* v___x_54_; 
lean_inc_ref(v_v_50_);
lean_inc(v_fvarId_49_);
v___f_52_ = lean_alloc_closure((void*)(l_Lean_Meta_FVarSubst_insert___lam__0___boxed), 3, 2);
lean_closure_set(v___f_52_, 0, v_fvarId_49_);
lean_closure_set(v___f_52_, 1, v_v_50_);
v_map_53_ = l_Lean_AssocList_mapVal___redArg(v___f_52_, v_s_48_);
v___x_54_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_54_, 0, v_fvarId_49_);
lean_ctor_set(v___x_54_, 1, v_v_50_);
lean_ctor_set(v___x_54_, 2, v_map_53_);
return v___x_54_;
}
else
{
lean_dec_ref(v_v_50_);
lean_dec(v_fvarId_49_);
return v_s_48_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_erase___at___00Lean_Meta_FVarSubst_erase_spec__0___redArg(lean_object* v_a_55_, lean_object* v_x_56_){
_start:
{
if (lean_obj_tag(v_x_56_) == 0)
{
return v_x_56_;
}
else
{
lean_object* v_key_57_; lean_object* v_value_58_; lean_object* v_tail_59_; lean_object* v___x_61_; uint8_t v_isShared_62_; uint8_t v_isSharedCheck_68_; 
v_key_57_ = lean_ctor_get(v_x_56_, 0);
v_value_58_ = lean_ctor_get(v_x_56_, 1);
v_tail_59_ = lean_ctor_get(v_x_56_, 2);
v_isSharedCheck_68_ = !lean_is_exclusive(v_x_56_);
if (v_isSharedCheck_68_ == 0)
{
v___x_61_ = v_x_56_;
v_isShared_62_ = v_isSharedCheck_68_;
goto v_resetjp_60_;
}
else
{
lean_inc(v_tail_59_);
lean_inc(v_value_58_);
lean_inc(v_key_57_);
lean_dec(v_x_56_);
v___x_61_ = lean_box(0);
v_isShared_62_ = v_isSharedCheck_68_;
goto v_resetjp_60_;
}
v_resetjp_60_:
{
uint8_t v___x_63_; 
v___x_63_ = l_Lean_instBEqFVarId_beq(v_key_57_, v_a_55_);
if (v___x_63_ == 0)
{
lean_object* v___x_64_; lean_object* v___x_66_; 
v___x_64_ = l_Lean_AssocList_erase___at___00Lean_Meta_FVarSubst_erase_spec__0___redArg(v_a_55_, v_tail_59_);
if (v_isShared_62_ == 0)
{
lean_ctor_set(v___x_61_, 2, v___x_64_);
v___x_66_ = v___x_61_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_67_; 
v_reuseFailAlloc_67_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_67_, 0, v_key_57_);
lean_ctor_set(v_reuseFailAlloc_67_, 1, v_value_58_);
lean_ctor_set(v_reuseFailAlloc_67_, 2, v___x_64_);
v___x_66_ = v_reuseFailAlloc_67_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
return v___x_66_;
}
}
else
{
lean_del_object(v___x_61_);
lean_dec(v_value_58_);
lean_dec(v_key_57_);
return v_tail_59_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_erase___at___00Lean_Meta_FVarSubst_erase_spec__0___redArg___boxed(lean_object* v_a_69_, lean_object* v_x_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l_Lean_AssocList_erase___at___00Lean_Meta_FVarSubst_erase_spec__0___redArg(v_a_69_, v_x_70_);
lean_dec(v_a_69_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_erase(lean_object* v_s_72_, lean_object* v_fvarId_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = l_Lean_AssocList_erase___at___00Lean_Meta_FVarSubst_erase_spec__0___redArg(v_fvarId_73_, v_s_72_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_erase___boxed(lean_object* v_s_75_, lean_object* v_fvarId_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l_Lean_Meta_FVarSubst_erase(v_s_75_, v_fvarId_76_);
lean_dec(v_fvarId_76_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_erase___at___00Lean_Meta_FVarSubst_erase_spec__0(lean_object* v_00_u03b2_78_, lean_object* v_a_79_, lean_object* v_x_80_){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = l_Lean_AssocList_erase___at___00Lean_Meta_FVarSubst_erase_spec__0___redArg(v_a_79_, v_x_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_erase___at___00Lean_Meta_FVarSubst_erase_spec__0___boxed(lean_object* v_00_u03b2_82_, lean_object* v_a_83_, lean_object* v_x_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Lean_AssocList_erase___at___00Lean_Meta_FVarSubst_erase_spec__0(v_00_u03b2_82_, v_a_83_, v_x_84_);
lean_dec(v_a_83_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___00Lean_Meta_FVarSubst_find_x3f_spec__0___redArg(lean_object* v_a_86_, lean_object* v_x_87_){
_start:
{
if (lean_obj_tag(v_x_87_) == 0)
{
lean_object* v___x_88_; 
v___x_88_ = lean_box(0);
return v___x_88_;
}
else
{
lean_object* v_key_89_; lean_object* v_value_90_; lean_object* v_tail_91_; uint8_t v___x_92_; 
v_key_89_ = lean_ctor_get(v_x_87_, 0);
v_value_90_ = lean_ctor_get(v_x_87_, 1);
v_tail_91_ = lean_ctor_get(v_x_87_, 2);
v___x_92_ = l_Lean_instBEqFVarId_beq(v_key_89_, v_a_86_);
if (v___x_92_ == 0)
{
v_x_87_ = v_tail_91_;
goto _start;
}
else
{
lean_object* v___x_94_; 
lean_inc(v_value_90_);
v___x_94_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_94_, 0, v_value_90_);
return v___x_94_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___00Lean_Meta_FVarSubst_find_x3f_spec__0___redArg___boxed(lean_object* v_a_95_, lean_object* v_x_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l_Lean_AssocList_find_x3f___at___00Lean_Meta_FVarSubst_find_x3f_spec__0___redArg(v_a_95_, v_x_96_);
lean_dec(v_x_96_);
lean_dec(v_a_95_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_find_x3f(lean_object* v_s_98_, lean_object* v_fvarId_99_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = l_Lean_AssocList_find_x3f___at___00Lean_Meta_FVarSubst_find_x3f_spec__0___redArg(v_fvarId_99_, v_s_98_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_find_x3f___boxed(lean_object* v_s_101_, lean_object* v_fvarId_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l_Lean_Meta_FVarSubst_find_x3f(v_s_101_, v_fvarId_102_);
lean_dec(v_fvarId_102_);
lean_dec(v_s_101_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___00Lean_Meta_FVarSubst_find_x3f_spec__0(lean_object* v_00_u03b2_104_, lean_object* v_a_105_, lean_object* v_x_106_){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = l_Lean_AssocList_find_x3f___at___00Lean_Meta_FVarSubst_find_x3f_spec__0___redArg(v_a_105_, v_x_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___00Lean_Meta_FVarSubst_find_x3f_spec__0___boxed(lean_object* v_00_u03b2_108_, lean_object* v_a_109_, lean_object* v_x_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l_Lean_AssocList_find_x3f___at___00Lean_Meta_FVarSubst_find_x3f_spec__0(v_00_u03b2_108_, v_a_109_, v_x_110_);
lean_dec(v_x_110_);
lean_dec(v_a_109_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_get(lean_object* v_s_112_, lean_object* v_fvarId_113_){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = l_Lean_AssocList_find_x3f___at___00Lean_Meta_FVarSubst_find_x3f_spec__0___redArg(v_fvarId_113_, v_s_112_);
if (lean_obj_tag(v___x_114_) == 0)
{
lean_object* v___x_115_; 
v___x_115_ = l_Lean_mkFVar(v_fvarId_113_);
return v___x_115_;
}
else
{
lean_object* v_val_116_; 
lean_dec(v_fvarId_113_);
v_val_116_ = lean_ctor_get(v___x_114_, 0);
lean_inc(v_val_116_);
lean_dec_ref_known(v___x_114_, 1);
return v_val_116_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_get___boxed(lean_object* v_s_117_, lean_object* v_fvarId_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Lean_Meta_FVarSubst_get(v_s_117_, v_fvarId_118_);
lean_dec(v_s_117_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_apply___lam__0(lean_object* v_s_120_, lean_object* v_e_121_){
_start:
{
if (lean_obj_tag(v_e_121_) == 1)
{
lean_object* v_fvarId_122_; lean_object* v___x_123_; 
v_fvarId_122_ = lean_ctor_get(v_e_121_, 0);
v___x_123_ = l_Lean_AssocList_find_x3f___at___00Lean_Meta_FVarSubst_find_x3f_spec__0___redArg(v_fvarId_122_, v_s_120_);
if (lean_obj_tag(v___x_123_) == 0)
{
lean_object* v___x_124_; 
v___x_124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_124_, 0, v_e_121_);
return v___x_124_;
}
else
{
lean_dec_ref_known(v_e_121_, 1);
return v___x_123_;
}
}
else
{
lean_object* v___x_125_; 
lean_dec_ref(v_e_121_);
v___x_125_ = lean_box(0);
return v___x_125_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_apply___lam__0___boxed(lean_object* v_s_126_, lean_object* v_e_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_Lean_Meta_FVarSubst_apply___lam__0(v_s_126_, v_e_127_);
lean_dec(v_s_126_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_apply(lean_object* v_s_129_, lean_object* v_e_130_){
_start:
{
uint8_t v___x_131_; 
v___x_131_ = l_Lean_AssocList_isEmpty___redArg(v_s_129_);
if (v___x_131_ == 0)
{
uint8_t v___x_132_; 
v___x_132_ = l_Lean_Expr_hasFVar(v_e_130_);
if (v___x_132_ == 0)
{
lean_dec(v_s_129_);
lean_inc_ref(v_e_130_);
return v_e_130_;
}
else
{
if (v___x_131_ == 0)
{
lean_object* v___f_133_; lean_object* v___x_134_; 
v___f_133_ = lean_alloc_closure((void*)(l_Lean_Meta_FVarSubst_apply___lam__0___boxed), 2, 1);
lean_closure_set(v___f_133_, 0, v_s_129_);
v___x_134_ = lean_replace_expr(v___f_133_, v_e_130_);
lean_dec_ref(v___f_133_);
return v___x_134_;
}
else
{
lean_dec(v_s_129_);
lean_inc_ref(v_e_130_);
return v_e_130_;
}
}
}
else
{
lean_dec(v_s_129_);
lean_inc_ref(v_e_130_);
return v_e_130_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_apply___boxed(lean_object* v_s_135_, lean_object* v_e_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l_Lean_Meta_FVarSubst_apply(v_s_135_, v_e_136_);
lean_dec_ref(v_e_136_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at___00Lean_Meta_FVarSubst_domain_spec__0(lean_object* v_x_138_, lean_object* v_x_139_){
_start:
{
if (lean_obj_tag(v_x_139_) == 0)
{
return v_x_138_;
}
else
{
lean_object* v_key_140_; lean_object* v_tail_141_; lean_object* v___x_142_; 
v_key_140_ = lean_ctor_get(v_x_139_, 0);
v_tail_141_ = lean_ctor_get(v_x_139_, 2);
lean_inc(v_key_140_);
v___x_142_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_142_, 0, v_key_140_);
lean_ctor_set(v___x_142_, 1, v_x_138_);
v_x_138_ = v___x_142_;
v_x_139_ = v_tail_141_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at___00Lean_Meta_FVarSubst_domain_spec__0___boxed(lean_object* v_x_144_, lean_object* v_x_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Lean_AssocList_foldlM___at___00Lean_Meta_FVarSubst_domain_spec__0(v_x_144_, v_x_145_);
lean_dec(v_x_145_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_domain(lean_object* v_s_147_){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_148_ = lean_box(0);
v___x_149_ = l_Lean_AssocList_foldlM___at___00Lean_Meta_FVarSubst_domain_spec__0(v___x_148_, v_s_147_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_domain___boxed(lean_object* v_s_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l_Lean_Meta_FVarSubst_domain(v_s_150_);
lean_dec(v_s_150_);
return v_res_151_;
}
}
uint8_t l_Lean_Meta_FVarSubst_any(lean_object* v_p_152_, lean_object* v_s_153_){
_start:
{
uint8_t v___x_154_; 
v___x_154_ = l_Lean_AssocList_any___redArg(v_p_152_, v_s_153_);
return v___x_154_;
}
}
LEAN_EXPORT void l_Lean_Meta_FVarSubst_any_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_152_ = stack[0].m_obj;
lean_object* v_s_153_ = stack[1].m_obj;
uint8_t v_res_155_;
v_res_155_ = l_Lean_Meta_FVarSubst_any(v_p_152_, v_s_153_);
stack->m_num = v_res_155_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_any___boxed(lean_object* v_p_156_, lean_object* v_s_157_){
_start:
{
uint8_t v_res_158_; lean_object* v_r_159_; 
v_res_158_ = l_Lean_Meta_FVarSubst_any(v_p_156_, v_s_157_);
v_r_159_ = lean_box(v_res_158_);
return v_r_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at___00Lean_Meta_FVarSubst_append_spec__0(lean_object* v_t_160_, lean_object* v_x_161_, lean_object* v_x_162_){
_start:
{
if (lean_obj_tag(v_x_162_) == 0)
{
lean_dec(v_t_160_);
return v_x_161_;
}
else
{
lean_object* v_key_163_; lean_object* v_value_164_; lean_object* v_tail_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v_key_163_ = lean_ctor_get(v_x_162_, 0);
lean_inc(v_key_163_);
v_value_164_ = lean_ctor_get(v_x_162_, 1);
lean_inc(v_value_164_);
v_tail_165_ = lean_ctor_get(v_x_162_, 2);
lean_inc(v_tail_165_);
lean_dec_ref_known(v_x_162_, 3);
lean_inc(v_t_160_);
v___x_166_ = l_Lean_Meta_FVarSubst_apply(v_t_160_, v_value_164_);
lean_dec(v_value_164_);
v___x_167_ = l_Lean_Meta_FVarSubst_insert(v_x_161_, v_key_163_, v___x_166_);
v_x_161_ = v___x_167_;
v_x_162_ = v_tail_165_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_append(lean_object* v_s_169_, lean_object* v_t_170_){
_start:
{
lean_object* v___x_171_; 
lean_inc(v_t_170_);
v___x_171_ = l_Lean_AssocList_foldlM___at___00Lean_Meta_FVarSubst_append_spec__0(v_t_170_, v_t_170_, v_s_169_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_applyFVarSubst(lean_object* v_s_172_, lean_object* v_x_173_){
_start:
{
if (lean_obj_tag(v_x_173_) == 0)
{
lean_object* v_index_174_; lean_object* v_fvarId_175_; lean_object* v_userName_176_; lean_object* v_type_177_; uint8_t v_bi_178_; uint8_t v_kind_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_187_; 
v_index_174_ = lean_ctor_get(v_x_173_, 0);
v_fvarId_175_ = lean_ctor_get(v_x_173_, 1);
v_userName_176_ = lean_ctor_get(v_x_173_, 2);
v_type_177_ = lean_ctor_get(v_x_173_, 3);
v_bi_178_ = lean_ctor_get_uint8(v_x_173_, sizeof(void*)*4);
v_kind_179_ = lean_ctor_get_uint8(v_x_173_, sizeof(void*)*4 + 1);
v_isSharedCheck_187_ = !lean_is_exclusive(v_x_173_);
if (v_isSharedCheck_187_ == 0)
{
v___x_181_ = v_x_173_;
v_isShared_182_ = v_isSharedCheck_187_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_type_177_);
lean_inc(v_userName_176_);
lean_inc(v_fvarId_175_);
lean_inc(v_index_174_);
lean_dec(v_x_173_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_187_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_183_; lean_object* v___x_185_; 
v___x_183_ = l_Lean_Meta_FVarSubst_apply(v_s_172_, v_type_177_);
lean_dec_ref(v_type_177_);
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 3, v___x_183_);
v___x_185_ = v___x_181_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v_index_174_);
lean_ctor_set(v_reuseFailAlloc_186_, 1, v_fvarId_175_);
lean_ctor_set(v_reuseFailAlloc_186_, 2, v_userName_176_);
lean_ctor_set(v_reuseFailAlloc_186_, 3, v___x_183_);
lean_ctor_set_uint8(v_reuseFailAlloc_186_, sizeof(void*)*4, v_bi_178_);
lean_ctor_set_uint8(v_reuseFailAlloc_186_, sizeof(void*)*4 + 1, v_kind_179_);
v___x_185_ = v_reuseFailAlloc_186_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
return v___x_185_;
}
}
}
else
{
lean_object* v_index_188_; lean_object* v_fvarId_189_; lean_object* v_userName_190_; lean_object* v_type_191_; lean_object* v_value_192_; uint8_t v_nondep_193_; uint8_t v_kind_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_203_; 
v_index_188_ = lean_ctor_get(v_x_173_, 0);
v_fvarId_189_ = lean_ctor_get(v_x_173_, 1);
v_userName_190_ = lean_ctor_get(v_x_173_, 2);
v_type_191_ = lean_ctor_get(v_x_173_, 3);
v_value_192_ = lean_ctor_get(v_x_173_, 4);
v_nondep_193_ = lean_ctor_get_uint8(v_x_173_, sizeof(void*)*5);
v_kind_194_ = lean_ctor_get_uint8(v_x_173_, sizeof(void*)*5 + 1);
v_isSharedCheck_203_ = !lean_is_exclusive(v_x_173_);
if (v_isSharedCheck_203_ == 0)
{
v___x_196_ = v_x_173_;
v_isShared_197_ = v_isSharedCheck_203_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_value_192_);
lean_inc(v_type_191_);
lean_inc(v_userName_190_);
lean_inc(v_fvarId_189_);
lean_inc(v_index_188_);
lean_dec(v_x_173_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_203_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_201_; 
lean_inc(v_s_172_);
v___x_198_ = l_Lean_Meta_FVarSubst_apply(v_s_172_, v_type_191_);
lean_dec_ref(v_type_191_);
v___x_199_ = l_Lean_Meta_FVarSubst_apply(v_s_172_, v_value_192_);
lean_dec_ref(v_value_192_);
if (v_isShared_197_ == 0)
{
lean_ctor_set(v___x_196_, 4, v___x_199_);
lean_ctor_set(v___x_196_, 3, v___x_198_);
v___x_201_ = v___x_196_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v_index_188_);
lean_ctor_set(v_reuseFailAlloc_202_, 1, v_fvarId_189_);
lean_ctor_set(v_reuseFailAlloc_202_, 2, v_userName_190_);
lean_ctor_set(v_reuseFailAlloc_202_, 3, v___x_198_);
lean_ctor_set(v_reuseFailAlloc_202_, 4, v___x_199_);
lean_ctor_set_uint8(v_reuseFailAlloc_202_, sizeof(void*)*5, v_nondep_193_);
lean_ctor_set_uint8(v_reuseFailAlloc_202_, sizeof(void*)*5 + 1, v_kind_194_);
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
LEAN_EXPORT lean_object* l_Lean_Expr_applyFVarSubst(lean_object* v_s_204_, lean_object* v_e_205_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = l_Lean_Meta_FVarSubst_apply(v_s_204_, v_e_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_applyFVarSubst___boxed(lean_object* v_s_207_, lean_object* v_e_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Lean_Expr_applyFVarSubst(v_s_207_, v_e_208_);
lean_dec_ref(v_e_208_);
return v_res_209_;
}
}
lean_object* runtime_initialize_Lean_Data_AssocList(uint8_t builtin);
lean_object* runtime_initialize_Lean_LocalContext(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_ReplaceExpr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_FVarSubst(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Data_AssocList(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_LocalContext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_ReplaceExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_instInhabitedFVarSubst_default = _init_l_Lean_Meta_instInhabitedFVarSubst_default();
lean_mark_persistent(l_Lean_Meta_instInhabitedFVarSubst_default);
l_Lean_Meta_instInhabitedFVarSubst = _init_l_Lean_Meta_instInhabitedFVarSubst();
lean_mark_persistent(l_Lean_Meta_instInhabitedFVarSubst);
l_Lean_Meta_FVarSubst_empty = _init_l_Lean_Meta_FVarSubst_empty();
lean_mark_persistent(l_Lean_Meta_FVarSubst_empty);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_FVarSubst(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_AssocList(uint8_t builtin);
lean_object* initialize_Lean_LocalContext(uint8_t builtin);
lean_object* initialize_Lean_Util_ReplaceExpr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_FVarSubst(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_AssocList(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_LocalContext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_ReplaceExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_FVarSubst(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_FVarSubst(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_FVarSubst(builtin);
}
#ifdef __cplusplus
}
#endif

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
LEAN_EXPORT uint8_t l_Lean_Meta_FVarSubst_isEmpty(lean_object* v_s_4_){
_start:
{
uint8_t v___x_5_; 
v___x_5_ = l_Lean_AssocList_isEmpty___redArg(v_s_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_isEmpty___boxed(lean_object* v_s_6_){
_start:
{
uint8_t v_res_7_; lean_object* v_r_8_; 
v_res_7_ = l_Lean_Meta_FVarSubst_isEmpty(v_s_6_);
lean_dec(v_s_6_);
v_r_8_ = lean_box(v_res_7_);
return v_r_8_;
}
}
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at___00Lean_Meta_FVarSubst_contains_spec__0___redArg(lean_object* v_a_9_, lean_object* v_x_10_){
_start:
{
if (lean_obj_tag(v_x_10_) == 0)
{
uint8_t v___x_11_; 
v___x_11_ = 0;
return v___x_11_;
}
else
{
lean_object* v_key_12_; lean_object* v_tail_13_; uint8_t v___x_14_; 
v_key_12_ = lean_ctor_get(v_x_10_, 0);
v_tail_13_ = lean_ctor_get(v_x_10_, 2);
v___x_14_ = l_Lean_instBEqFVarId_beq(v_key_12_, v_a_9_);
if (v___x_14_ == 0)
{
v_x_10_ = v_tail_13_;
goto _start;
}
else
{
return v___x_14_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at___00Lean_Meta_FVarSubst_contains_spec__0___redArg___boxed(lean_object* v_a_16_, lean_object* v_x_17_){
_start:
{
uint8_t v_res_18_; lean_object* v_r_19_; 
v_res_18_ = l_Lean_AssocList_contains___at___00Lean_Meta_FVarSubst_contains_spec__0___redArg(v_a_16_, v_x_17_);
lean_dec(v_x_17_);
lean_dec(v_a_16_);
v_r_19_ = lean_box(v_res_18_);
return v_r_19_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_FVarSubst_contains(lean_object* v_s_20_, lean_object* v_fvarId_21_){
_start:
{
uint8_t v___x_22_; 
v___x_22_ = l_Lean_AssocList_contains___at___00Lean_Meta_FVarSubst_contains_spec__0___redArg(v_fvarId_21_, v_s_20_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_contains___boxed(lean_object* v_s_23_, lean_object* v_fvarId_24_){
_start:
{
uint8_t v_res_25_; lean_object* v_r_26_; 
v_res_25_ = l_Lean_Meta_FVarSubst_contains(v_s_23_, v_fvarId_24_);
lean_dec(v_fvarId_24_);
lean_dec(v_s_23_);
v_r_26_ = lean_box(v_res_25_);
return v_r_26_;
}
}
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at___00Lean_Meta_FVarSubst_contains_spec__0(lean_object* v_00_u03b2_27_, lean_object* v_a_28_, lean_object* v_x_29_){
_start:
{
uint8_t v___x_30_; 
v___x_30_ = l_Lean_AssocList_contains___at___00Lean_Meta_FVarSubst_contains_spec__0___redArg(v_a_28_, v_x_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at___00Lean_Meta_FVarSubst_contains_spec__0___boxed(lean_object* v_00_u03b2_31_, lean_object* v_a_32_, lean_object* v_x_33_){
_start:
{
uint8_t v_res_34_; lean_object* v_r_35_; 
v_res_34_ = l_Lean_AssocList_contains___at___00Lean_Meta_FVarSubst_contains_spec__0(v_00_u03b2_31_, v_a_32_, v_x_33_);
lean_dec(v_x_33_);
lean_dec(v_a_32_);
v_r_35_ = lean_box(v_res_34_);
return v_r_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_insert___lam__0(lean_object* v_fvarId_36_, lean_object* v_v_37_, lean_object* v_e_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Lean_Expr_replaceFVarId(v_e_38_, v_fvarId_36_, v_v_37_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_insert___lam__0___boxed(lean_object* v_fvarId_40_, lean_object* v_v_41_, lean_object* v_e_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_Meta_FVarSubst_insert___lam__0(v_fvarId_40_, v_v_41_, v_e_42_);
lean_dec_ref(v_e_42_);
lean_dec_ref(v_v_41_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_insert(lean_object* v_s_44_, lean_object* v_fvarId_45_, lean_object* v_v_46_){
_start:
{
uint8_t v___x_47_; 
v___x_47_ = l_Lean_AssocList_contains___at___00Lean_Meta_FVarSubst_contains_spec__0___redArg(v_fvarId_45_, v_s_44_);
if (v___x_47_ == 0)
{
lean_object* v___f_48_; lean_object* v_map_49_; lean_object* v___x_50_; 
lean_inc_ref(v_v_46_);
lean_inc(v_fvarId_45_);
v___f_48_ = lean_alloc_closure((void*)(l_Lean_Meta_FVarSubst_insert___lam__0___boxed), 3, 2);
lean_closure_set(v___f_48_, 0, v_fvarId_45_);
lean_closure_set(v___f_48_, 1, v_v_46_);
v_map_49_ = l_Lean_AssocList_mapVal___redArg(v___f_48_, v_s_44_);
v___x_50_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_50_, 0, v_fvarId_45_);
lean_ctor_set(v___x_50_, 1, v_v_46_);
lean_ctor_set(v___x_50_, 2, v_map_49_);
return v___x_50_;
}
else
{
lean_dec_ref(v_v_46_);
lean_dec(v_fvarId_45_);
return v_s_44_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_erase___at___00Lean_Meta_FVarSubst_erase_spec__0___redArg(lean_object* v_a_51_, lean_object* v_x_52_){
_start:
{
if (lean_obj_tag(v_x_52_) == 0)
{
return v_x_52_;
}
else
{
lean_object* v_key_53_; lean_object* v_value_54_; lean_object* v_tail_55_; lean_object* v___x_57_; uint8_t v_isShared_58_; uint8_t v_isSharedCheck_64_; 
v_key_53_ = lean_ctor_get(v_x_52_, 0);
v_value_54_ = lean_ctor_get(v_x_52_, 1);
v_tail_55_ = lean_ctor_get(v_x_52_, 2);
v_isSharedCheck_64_ = !lean_is_exclusive(v_x_52_);
if (v_isSharedCheck_64_ == 0)
{
v___x_57_ = v_x_52_;
v_isShared_58_ = v_isSharedCheck_64_;
goto v_resetjp_56_;
}
else
{
lean_inc(v_tail_55_);
lean_inc(v_value_54_);
lean_inc(v_key_53_);
lean_dec(v_x_52_);
v___x_57_ = lean_box(0);
v_isShared_58_ = v_isSharedCheck_64_;
goto v_resetjp_56_;
}
v_resetjp_56_:
{
uint8_t v___x_59_; 
v___x_59_ = l_Lean_instBEqFVarId_beq(v_key_53_, v_a_51_);
if (v___x_59_ == 0)
{
lean_object* v___x_60_; lean_object* v___x_62_; 
v___x_60_ = l_Lean_AssocList_erase___at___00Lean_Meta_FVarSubst_erase_spec__0___redArg(v_a_51_, v_tail_55_);
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 2, v___x_60_);
v___x_62_ = v___x_57_;
goto v_reusejp_61_;
}
else
{
lean_object* v_reuseFailAlloc_63_; 
v_reuseFailAlloc_63_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_63_, 0, v_key_53_);
lean_ctor_set(v_reuseFailAlloc_63_, 1, v_value_54_);
lean_ctor_set(v_reuseFailAlloc_63_, 2, v___x_60_);
v___x_62_ = v_reuseFailAlloc_63_;
goto v_reusejp_61_;
}
v_reusejp_61_:
{
return v___x_62_;
}
}
else
{
lean_del_object(v___x_57_);
lean_dec(v_value_54_);
lean_dec(v_key_53_);
return v_tail_55_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_erase___at___00Lean_Meta_FVarSubst_erase_spec__0___redArg___boxed(lean_object* v_a_65_, lean_object* v_x_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Lean_AssocList_erase___at___00Lean_Meta_FVarSubst_erase_spec__0___redArg(v_a_65_, v_x_66_);
lean_dec(v_a_65_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_erase(lean_object* v_s_68_, lean_object* v_fvarId_69_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = l_Lean_AssocList_erase___at___00Lean_Meta_FVarSubst_erase_spec__0___redArg(v_fvarId_69_, v_s_68_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_erase___boxed(lean_object* v_s_71_, lean_object* v_fvarId_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l_Lean_Meta_FVarSubst_erase(v_s_71_, v_fvarId_72_);
lean_dec(v_fvarId_72_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_erase___at___00Lean_Meta_FVarSubst_erase_spec__0(lean_object* v_00_u03b2_74_, lean_object* v_a_75_, lean_object* v_x_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = l_Lean_AssocList_erase___at___00Lean_Meta_FVarSubst_erase_spec__0___redArg(v_a_75_, v_x_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_erase___at___00Lean_Meta_FVarSubst_erase_spec__0___boxed(lean_object* v_00_u03b2_78_, lean_object* v_a_79_, lean_object* v_x_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_Lean_AssocList_erase___at___00Lean_Meta_FVarSubst_erase_spec__0(v_00_u03b2_78_, v_a_79_, v_x_80_);
lean_dec(v_a_79_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___00Lean_Meta_FVarSubst_find_x3f_spec__0___redArg(lean_object* v_a_82_, lean_object* v_x_83_){
_start:
{
if (lean_obj_tag(v_x_83_) == 0)
{
lean_object* v___x_84_; 
v___x_84_ = lean_box(0);
return v___x_84_;
}
else
{
lean_object* v_key_85_; lean_object* v_value_86_; lean_object* v_tail_87_; uint8_t v___x_88_; 
v_key_85_ = lean_ctor_get(v_x_83_, 0);
v_value_86_ = lean_ctor_get(v_x_83_, 1);
v_tail_87_ = lean_ctor_get(v_x_83_, 2);
v___x_88_ = l_Lean_instBEqFVarId_beq(v_key_85_, v_a_82_);
if (v___x_88_ == 0)
{
v_x_83_ = v_tail_87_;
goto _start;
}
else
{
lean_object* v___x_90_; 
lean_inc(v_value_86_);
v___x_90_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_90_, 0, v_value_86_);
return v___x_90_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___00Lean_Meta_FVarSubst_find_x3f_spec__0___redArg___boxed(lean_object* v_a_91_, lean_object* v_x_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Lean_AssocList_find_x3f___at___00Lean_Meta_FVarSubst_find_x3f_spec__0___redArg(v_a_91_, v_x_92_);
lean_dec(v_x_92_);
lean_dec(v_a_91_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_find_x3f(lean_object* v_s_94_, lean_object* v_fvarId_95_){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = l_Lean_AssocList_find_x3f___at___00Lean_Meta_FVarSubst_find_x3f_spec__0___redArg(v_fvarId_95_, v_s_94_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_find_x3f___boxed(lean_object* v_s_97_, lean_object* v_fvarId_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_Lean_Meta_FVarSubst_find_x3f(v_s_97_, v_fvarId_98_);
lean_dec(v_fvarId_98_);
lean_dec(v_s_97_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___00Lean_Meta_FVarSubst_find_x3f_spec__0(lean_object* v_00_u03b2_100_, lean_object* v_a_101_, lean_object* v_x_102_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = l_Lean_AssocList_find_x3f___at___00Lean_Meta_FVarSubst_find_x3f_spec__0___redArg(v_a_101_, v_x_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___00Lean_Meta_FVarSubst_find_x3f_spec__0___boxed(lean_object* v_00_u03b2_104_, lean_object* v_a_105_, lean_object* v_x_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l_Lean_AssocList_find_x3f___at___00Lean_Meta_FVarSubst_find_x3f_spec__0(v_00_u03b2_104_, v_a_105_, v_x_106_);
lean_dec(v_x_106_);
lean_dec(v_a_105_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_get(lean_object* v_s_108_, lean_object* v_fvarId_109_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = l_Lean_AssocList_find_x3f___at___00Lean_Meta_FVarSubst_find_x3f_spec__0___redArg(v_fvarId_109_, v_s_108_);
if (lean_obj_tag(v___x_110_) == 0)
{
lean_object* v___x_111_; 
v___x_111_ = l_Lean_mkFVar(v_fvarId_109_);
return v___x_111_;
}
else
{
lean_object* v_val_112_; 
lean_dec(v_fvarId_109_);
v_val_112_ = lean_ctor_get(v___x_110_, 0);
lean_inc(v_val_112_);
lean_dec_ref(v___x_110_);
return v_val_112_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_get___boxed(lean_object* v_s_113_, lean_object* v_fvarId_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Lean_Meta_FVarSubst_get(v_s_113_, v_fvarId_114_);
lean_dec(v_s_113_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_apply___lam__0(lean_object* v_s_116_, lean_object* v_e_117_){
_start:
{
if (lean_obj_tag(v_e_117_) == 1)
{
lean_object* v_fvarId_118_; lean_object* v___x_119_; 
v_fvarId_118_ = lean_ctor_get(v_e_117_, 0);
v___x_119_ = l_Lean_AssocList_find_x3f___at___00Lean_Meta_FVarSubst_find_x3f_spec__0___redArg(v_fvarId_118_, v_s_116_);
if (lean_obj_tag(v___x_119_) == 0)
{
lean_object* v___x_120_; 
v___x_120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_120_, 0, v_e_117_);
return v___x_120_;
}
else
{
lean_dec_ref(v_e_117_);
return v___x_119_;
}
}
else
{
lean_object* v___x_121_; 
lean_dec_ref(v_e_117_);
v___x_121_ = lean_box(0);
return v___x_121_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_apply___lam__0___boxed(lean_object* v_s_122_, lean_object* v_e_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l_Lean_Meta_FVarSubst_apply___lam__0(v_s_122_, v_e_123_);
lean_dec(v_s_122_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_apply(lean_object* v_s_125_, lean_object* v_e_126_){
_start:
{
uint8_t v___x_127_; 
v___x_127_ = l_Lean_AssocList_isEmpty___redArg(v_s_125_);
if (v___x_127_ == 0)
{
uint8_t v___x_128_; 
v___x_128_ = l_Lean_Expr_hasFVar(v_e_126_);
if (v___x_128_ == 0)
{
lean_dec(v_s_125_);
lean_inc_ref(v_e_126_);
return v_e_126_;
}
else
{
if (v___x_127_ == 0)
{
lean_object* v___f_129_; lean_object* v___x_130_; 
v___f_129_ = lean_alloc_closure((void*)(l_Lean_Meta_FVarSubst_apply___lam__0___boxed), 2, 1);
lean_closure_set(v___f_129_, 0, v_s_125_);
v___x_130_ = lean_replace_expr(v___f_129_, v_e_126_);
lean_dec_ref(v___f_129_);
return v___x_130_;
}
else
{
lean_dec(v_s_125_);
lean_inc_ref(v_e_126_);
return v_e_126_;
}
}
}
else
{
lean_dec(v_s_125_);
lean_inc_ref(v_e_126_);
return v_e_126_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_apply___boxed(lean_object* v_s_131_, lean_object* v_e_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l_Lean_Meta_FVarSubst_apply(v_s_131_, v_e_132_);
lean_dec_ref(v_e_132_);
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at___00Lean_Meta_FVarSubst_domain_spec__0(lean_object* v_x_134_, lean_object* v_x_135_){
_start:
{
if (lean_obj_tag(v_x_135_) == 0)
{
return v_x_134_;
}
else
{
lean_object* v_key_136_; lean_object* v_tail_137_; lean_object* v___x_138_; 
v_key_136_ = lean_ctor_get(v_x_135_, 0);
v_tail_137_ = lean_ctor_get(v_x_135_, 2);
lean_inc(v_key_136_);
v___x_138_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_138_, 0, v_key_136_);
lean_ctor_set(v___x_138_, 1, v_x_134_);
v_x_134_ = v___x_138_;
v_x_135_ = v_tail_137_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at___00Lean_Meta_FVarSubst_domain_spec__0___boxed(lean_object* v_x_140_, lean_object* v_x_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_Lean_AssocList_foldlM___at___00Lean_Meta_FVarSubst_domain_spec__0(v_x_140_, v_x_141_);
lean_dec(v_x_141_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_domain(lean_object* v_s_143_){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_144_ = lean_box(0);
v___x_145_ = l_Lean_AssocList_foldlM___at___00Lean_Meta_FVarSubst_domain_spec__0(v___x_144_, v_s_143_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_domain___boxed(lean_object* v_s_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l_Lean_Meta_FVarSubst_domain(v_s_146_);
lean_dec(v_s_146_);
return v_res_147_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_FVarSubst_any(lean_object* v_p_148_, lean_object* v_s_149_){
_start:
{
uint8_t v___x_150_; 
v___x_150_ = l_Lean_AssocList_any___redArg(v_p_148_, v_s_149_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_any___boxed(lean_object* v_p_151_, lean_object* v_s_152_){
_start:
{
uint8_t v_res_153_; lean_object* v_r_154_; 
v_res_153_ = l_Lean_Meta_FVarSubst_any(v_p_151_, v_s_152_);
v_r_154_ = lean_box(v_res_153_);
return v_r_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at___00Lean_Meta_FVarSubst_append_spec__0(lean_object* v_t_155_, lean_object* v_x_156_, lean_object* v_x_157_){
_start:
{
if (lean_obj_tag(v_x_157_) == 0)
{
lean_dec(v_t_155_);
return v_x_156_;
}
else
{
lean_object* v_key_158_; lean_object* v_value_159_; lean_object* v_tail_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v_key_158_ = lean_ctor_get(v_x_157_, 0);
lean_inc(v_key_158_);
v_value_159_ = lean_ctor_get(v_x_157_, 1);
lean_inc(v_value_159_);
v_tail_160_ = lean_ctor_get(v_x_157_, 2);
lean_inc(v_tail_160_);
lean_dec_ref(v_x_157_);
lean_inc(v_t_155_);
v___x_161_ = l_Lean_Meta_FVarSubst_apply(v_t_155_, v_value_159_);
lean_dec(v_value_159_);
v___x_162_ = l_Lean_Meta_FVarSubst_insert(v_x_156_, v_key_158_, v___x_161_);
v_x_156_ = v___x_162_;
v_x_157_ = v_tail_160_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_append(lean_object* v_s_164_, lean_object* v_t_165_){
_start:
{
lean_object* v___x_166_; 
lean_inc(v_t_165_);
v___x_166_ = l_Lean_AssocList_foldlM___at___00Lean_Meta_FVarSubst_append_spec__0(v_t_165_, v_t_165_, v_s_164_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_applyFVarSubst(lean_object* v_s_167_, lean_object* v_x_168_){
_start:
{
if (lean_obj_tag(v_x_168_) == 0)
{
lean_object* v_index_169_; lean_object* v_fvarId_170_; lean_object* v_userName_171_; lean_object* v_type_172_; uint8_t v_bi_173_; uint8_t v_kind_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_182_; 
v_index_169_ = lean_ctor_get(v_x_168_, 0);
v_fvarId_170_ = lean_ctor_get(v_x_168_, 1);
v_userName_171_ = lean_ctor_get(v_x_168_, 2);
v_type_172_ = lean_ctor_get(v_x_168_, 3);
v_bi_173_ = lean_ctor_get_uint8(v_x_168_, sizeof(void*)*4);
v_kind_174_ = lean_ctor_get_uint8(v_x_168_, sizeof(void*)*4 + 1);
v_isSharedCheck_182_ = !lean_is_exclusive(v_x_168_);
if (v_isSharedCheck_182_ == 0)
{
v___x_176_ = v_x_168_;
v_isShared_177_ = v_isSharedCheck_182_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_type_172_);
lean_inc(v_userName_171_);
lean_inc(v_fvarId_170_);
lean_inc(v_index_169_);
lean_dec(v_x_168_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_182_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v___x_178_; lean_object* v___x_180_; 
v___x_178_ = l_Lean_Meta_FVarSubst_apply(v_s_167_, v_type_172_);
lean_dec_ref(v_type_172_);
if (v_isShared_177_ == 0)
{
lean_ctor_set(v___x_176_, 3, v___x_178_);
v___x_180_ = v___x_176_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v_index_169_);
lean_ctor_set(v_reuseFailAlloc_181_, 1, v_fvarId_170_);
lean_ctor_set(v_reuseFailAlloc_181_, 2, v_userName_171_);
lean_ctor_set(v_reuseFailAlloc_181_, 3, v___x_178_);
lean_ctor_set_uint8(v_reuseFailAlloc_181_, sizeof(void*)*4, v_bi_173_);
lean_ctor_set_uint8(v_reuseFailAlloc_181_, sizeof(void*)*4 + 1, v_kind_174_);
v___x_180_ = v_reuseFailAlloc_181_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
return v___x_180_;
}
}
}
else
{
lean_object* v_index_183_; lean_object* v_fvarId_184_; lean_object* v_userName_185_; lean_object* v_type_186_; lean_object* v_value_187_; uint8_t v_nondep_188_; uint8_t v_kind_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_198_; 
v_index_183_ = lean_ctor_get(v_x_168_, 0);
v_fvarId_184_ = lean_ctor_get(v_x_168_, 1);
v_userName_185_ = lean_ctor_get(v_x_168_, 2);
v_type_186_ = lean_ctor_get(v_x_168_, 3);
v_value_187_ = lean_ctor_get(v_x_168_, 4);
v_nondep_188_ = lean_ctor_get_uint8(v_x_168_, sizeof(void*)*5);
v_kind_189_ = lean_ctor_get_uint8(v_x_168_, sizeof(void*)*5 + 1);
v_isSharedCheck_198_ = !lean_is_exclusive(v_x_168_);
if (v_isSharedCheck_198_ == 0)
{
v___x_191_ = v_x_168_;
v_isShared_192_ = v_isSharedCheck_198_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_value_187_);
lean_inc(v_type_186_);
lean_inc(v_userName_185_);
lean_inc(v_fvarId_184_);
lean_inc(v_index_183_);
lean_dec(v_x_168_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_198_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_196_; 
lean_inc(v_s_167_);
v___x_193_ = l_Lean_Meta_FVarSubst_apply(v_s_167_, v_type_186_);
lean_dec_ref(v_type_186_);
v___x_194_ = l_Lean_Meta_FVarSubst_apply(v_s_167_, v_value_187_);
lean_dec_ref(v_value_187_);
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 4, v___x_194_);
lean_ctor_set(v___x_191_, 3, v___x_193_);
v___x_196_ = v___x_191_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v_index_183_);
lean_ctor_set(v_reuseFailAlloc_197_, 1, v_fvarId_184_);
lean_ctor_set(v_reuseFailAlloc_197_, 2, v_userName_185_);
lean_ctor_set(v_reuseFailAlloc_197_, 3, v___x_193_);
lean_ctor_set(v_reuseFailAlloc_197_, 4, v___x_194_);
lean_ctor_set_uint8(v_reuseFailAlloc_197_, sizeof(void*)*5, v_nondep_188_);
lean_ctor_set_uint8(v_reuseFailAlloc_197_, sizeof(void*)*5 + 1, v_kind_189_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
return v___x_196_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_applyFVarSubst(lean_object* v_s_199_, lean_object* v_e_200_){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = l_Lean_Meta_FVarSubst_apply(v_s_199_, v_e_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_applyFVarSubst___boxed(lean_object* v_s_202_, lean_object* v_e_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Lean_Expr_applyFVarSubst(v_s_202_, v_e_203_);
lean_dec_ref(v_e_203_);
return v_res_204_;
}
}
lean_object* runtime_initialize_Lean_Data_AssocList(uint8_t builtin);
lean_object* runtime_initialize_Lean_LocalContext(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_ReplaceExpr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_FVarSubst(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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

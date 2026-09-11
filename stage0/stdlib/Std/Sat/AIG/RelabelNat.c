// Lean compiler output
// Module: Std.Sat.AIG.RelabelNat
// Imports: public import Std.Sat.AIG.Relabel import Init.ByCases import Init.Omega
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
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_relabel___redArg(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Sat_AIG_RelabelNat_State_empty___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_RelabelNat_State_empty___redArg___closed__0;
static lean_once_cell_t l_Std_Sat_AIG_RelabelNat_State_empty___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_RelabelNat_State_empty___redArg___closed__1;
static lean_once_cell_t l_Std_Sat_AIG_RelabelNat_State_empty___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_RelabelNat_State_empty___redArg___closed__2;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_empty___redArg();
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_empty___redArg___boxed(lean_object*);
static lean_once_cell_t l_Std_Sat_AIG_RelabelNat_State_empty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_RelabelNat_State_empty___closed__0;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_empty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_empty___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addAtom___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addAtom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addFalse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addFalse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addGate___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addGate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addGate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_RelabelNat_0__Std_Sat_AIG_RelabelNat_State_ofAIGAux_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_RelabelNat_0__Std_Sat_AIG_RelabelNat_State_ofAIGAux_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIG___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIG___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIG(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIG___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat_x27___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat_x27___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_RelabelNat_0__Std_Sat_AIG_relabelNat_x27_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_RelabelNat_0__Std_Sat_AIG_relabelNat_x27_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Entrypoint_relabelNat_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Entrypoint_relabelNat_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Entrypoint_relabelNat___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Entrypoint_relabelNat(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Std_Sat_AIG_RelabelNat_State_empty___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = lean_box(0);
v___x_2_ = lean_unsigned_to_nat(16u);
v___x_3_ = lean_mk_array(v___x_2_, v___x_1_);
return v___x_3_;
}
}
static lean_object* _init_l_Std_Sat_AIG_RelabelNat_State_empty___redArg___closed__1(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_obj_once(&l_Std_Sat_AIG_RelabelNat_State_empty___redArg___closed__0, &l_Std_Sat_AIG_RelabelNat_State_empty___redArg___closed__0_once, _init_l_Std_Sat_AIG_RelabelNat_State_empty___redArg___closed__0);
v___x_5_ = lean_unsigned_to_nat(0u);
v___x_6_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
lean_ctor_set(v___x_6_, 1, v___x_4_);
return v___x_6_;
}
}
static lean_object* _init_l_Std_Sat_AIG_RelabelNat_State_empty___redArg___closed__2(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_7_ = lean_obj_once(&l_Std_Sat_AIG_RelabelNat_State_empty___redArg___closed__1, &l_Std_Sat_AIG_RelabelNat_State_empty___redArg___closed__1_once, _init_l_Std_Sat_AIG_RelabelNat_State_empty___redArg___closed__1);
v___x_8_ = lean_unsigned_to_nat(0u);
v___x_9_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_9_, 0, v___x_8_);
lean_ctor_set(v___x_9_, 1, v___x_7_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_empty___redArg(){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lean_obj_once(&l_Std_Sat_AIG_RelabelNat_State_empty___redArg___closed__2, &l_Std_Sat_AIG_RelabelNat_State_empty___redArg___closed__2_once, _init_l_Std_Sat_AIG_RelabelNat_State_empty___redArg___closed__2);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_empty___redArg___boxed(lean_object* v___dummy_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l_Std_Sat_AIG_RelabelNat_State_empty___redArg();
return v_res_13_;
}
}
static lean_object* _init_l_Std_Sat_AIG_RelabelNat_State_empty___closed__0(void){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l_Std_Sat_AIG_RelabelNat_State_empty___redArg();
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_empty(lean_object* v_00_u03b1_15_, lean_object* v_inst_16_, lean_object* v_inst_17_, lean_object* v_decls_18_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = lean_obj_once(&l_Std_Sat_AIG_RelabelNat_State_empty___closed__0, &l_Std_Sat_AIG_RelabelNat_State_empty___closed__0_once, _init_l_Std_Sat_AIG_RelabelNat_State_empty___closed__0);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_empty___boxed(lean_object* v_00_u03b1_20_, lean_object* v_inst_21_, lean_object* v_inst_22_, lean_object* v_decls_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Std_Sat_AIG_RelabelNat_State_empty(v_00_u03b1_20_, v_inst_21_, v_inst_22_, v_decls_23_);
lean_dec_ref(v_decls_23_);
lean_dec_ref(v_inst_22_);
lean_dec_ref(v_inst_21_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addAtom___redArg(lean_object* v_inst_25_, lean_object* v_inst_26_, lean_object* v_state_27_, lean_object* v_a_28_){
_start:
{
lean_object* v_max_29_; lean_object* v_map_30_; lean_object* v___x_32_; uint8_t v_isShared_33_; uint8_t v_isSharedCheck_45_; 
v_max_29_ = lean_ctor_get(v_state_27_, 0);
v_map_30_ = lean_ctor_get(v_state_27_, 1);
v_isSharedCheck_45_ = !lean_is_exclusive(v_state_27_);
if (v_isSharedCheck_45_ == 0)
{
v___x_32_ = v_state_27_;
v_isShared_33_ = v_isSharedCheck_45_;
goto v_resetjp_31_;
}
else
{
lean_inc(v_map_30_);
lean_inc(v_max_29_);
lean_dec(v_state_27_);
v___x_32_ = lean_box(0);
v_isShared_33_ = v_isSharedCheck_45_;
goto v_resetjp_31_;
}
v_resetjp_31_:
{
lean_object* v___f_34_; lean_object* v___x_35_; 
v___f_34_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_34_, 0, v_inst_25_);
lean_inc(v_a_28_);
lean_inc_ref(v_inst_26_);
lean_inc_ref(v___f_34_);
v___x_35_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_34_, v_inst_26_, v_map_30_, v_a_28_);
if (lean_obj_tag(v___x_35_) == 0)
{
lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_40_; 
v___x_36_ = lean_unsigned_to_nat(1u);
v___x_37_ = lean_nat_add(v_max_29_, v___x_36_);
v___x_38_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_34_, v_inst_26_, v_map_30_, v_a_28_, v_max_29_);
if (v_isShared_33_ == 0)
{
lean_ctor_set(v___x_32_, 1, v___x_38_);
lean_ctor_set(v___x_32_, 0, v___x_37_);
v___x_40_ = v___x_32_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_41_; 
v_reuseFailAlloc_41_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_41_, 0, v___x_37_);
lean_ctor_set(v_reuseFailAlloc_41_, 1, v___x_38_);
v___x_40_ = v_reuseFailAlloc_41_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
return v___x_40_;
}
}
else
{
lean_object* v___x_43_; 
lean_dec_ref_known(v___x_35_, 1);
lean_dec_ref(v___f_34_);
lean_dec(v_a_28_);
lean_dec_ref(v_inst_26_);
if (v_isShared_33_ == 0)
{
v___x_43_ = v___x_32_;
goto v_reusejp_42_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v_max_29_);
lean_ctor_set(v_reuseFailAlloc_44_, 1, v_map_30_);
v___x_43_ = v_reuseFailAlloc_44_;
goto v_reusejp_42_;
}
v_reusejp_42_:
{
return v___x_43_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addAtom(lean_object* v_00_u03b1_46_, lean_object* v_inst_47_, lean_object* v_inst_48_, lean_object* v_idx_49_, lean_object* v_decls_50_, lean_object* v_hidx_51_, lean_object* v_state_52_, lean_object* v_a_53_, lean_object* v_h_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = l_Std_Sat_AIG_RelabelNat_State_addAtom___redArg(v_inst_47_, v_inst_48_, v_state_52_, v_a_53_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addAtom___boxed(lean_object* v_00_u03b1_56_, lean_object* v_inst_57_, lean_object* v_inst_58_, lean_object* v_idx_59_, lean_object* v_decls_60_, lean_object* v_hidx_61_, lean_object* v_state_62_, lean_object* v_a_63_, lean_object* v_h_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_Std_Sat_AIG_RelabelNat_State_addAtom(v_00_u03b1_56_, v_inst_57_, v_inst_58_, v_idx_59_, v_decls_60_, v_hidx_61_, v_state_62_, v_a_63_, v_h_64_);
lean_dec_ref(v_decls_60_);
lean_dec(v_idx_59_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addFalse___redArg(lean_object* v_state_66_){
_start:
{
lean_object* v_max_67_; lean_object* v_map_68_; lean_object* v___x_70_; uint8_t v_isShared_71_; uint8_t v_isSharedCheck_75_; 
v_max_67_ = lean_ctor_get(v_state_66_, 0);
v_map_68_ = lean_ctor_get(v_state_66_, 1);
v_isSharedCheck_75_ = !lean_is_exclusive(v_state_66_);
if (v_isSharedCheck_75_ == 0)
{
v___x_70_ = v_state_66_;
v_isShared_71_ = v_isSharedCheck_75_;
goto v_resetjp_69_;
}
else
{
lean_inc(v_map_68_);
lean_inc(v_max_67_);
lean_dec(v_state_66_);
v___x_70_ = lean_box(0);
v_isShared_71_ = v_isSharedCheck_75_;
goto v_resetjp_69_;
}
v_resetjp_69_:
{
lean_object* v___x_73_; 
if (v_isShared_71_ == 0)
{
v___x_73_ = v___x_70_;
goto v_reusejp_72_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v_max_67_);
lean_ctor_set(v_reuseFailAlloc_74_, 1, v_map_68_);
v___x_73_ = v_reuseFailAlloc_74_;
goto v_reusejp_72_;
}
v_reusejp_72_:
{
return v___x_73_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addFalse(lean_object* v_00_u03b1_76_, lean_object* v_inst_77_, lean_object* v_inst_78_, lean_object* v_idx_79_, lean_object* v_decls_80_, lean_object* v_hidx_81_, lean_object* v_state_82_, lean_object* v_h_83_){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = l_Std_Sat_AIG_RelabelNat_State_addFalse___redArg(v_state_82_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addFalse___boxed(lean_object* v_00_u03b1_85_, lean_object* v_inst_86_, lean_object* v_inst_87_, lean_object* v_idx_88_, lean_object* v_decls_89_, lean_object* v_hidx_90_, lean_object* v_state_91_, lean_object* v_h_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Std_Sat_AIG_RelabelNat_State_addFalse(v_00_u03b1_85_, v_inst_86_, v_inst_87_, v_idx_88_, v_decls_89_, v_hidx_90_, v_state_91_, v_h_92_);
lean_dec_ref(v_decls_89_);
lean_dec(v_idx_88_);
lean_dec_ref(v_inst_87_);
lean_dec_ref(v_inst_86_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addGate___redArg(lean_object* v_state_94_){
_start:
{
lean_object* v_max_95_; lean_object* v_map_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_103_; 
v_max_95_ = lean_ctor_get(v_state_94_, 0);
v_map_96_ = lean_ctor_get(v_state_94_, 1);
v_isSharedCheck_103_ = !lean_is_exclusive(v_state_94_);
if (v_isSharedCheck_103_ == 0)
{
v___x_98_ = v_state_94_;
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_map_96_);
lean_inc(v_max_95_);
lean_dec(v_state_94_);
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
v_reuseFailAlloc_102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v_max_95_);
lean_ctor_set(v_reuseFailAlloc_102_, 1, v_map_96_);
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addGate(lean_object* v_00_u03b1_104_, lean_object* v_inst_105_, lean_object* v_inst_106_, lean_object* v_idx_107_, lean_object* v_decls_108_, lean_object* v_hidx_109_, lean_object* v_state_110_, lean_object* v_lhs_111_, lean_object* v_rhs_112_, lean_object* v_h_113_){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = l_Std_Sat_AIG_RelabelNat_State_addGate___redArg(v_state_110_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addGate___boxed(lean_object* v_00_u03b1_115_, lean_object* v_inst_116_, lean_object* v_inst_117_, lean_object* v_idx_118_, lean_object* v_decls_119_, lean_object* v_hidx_120_, lean_object* v_state_121_, lean_object* v_lhs_122_, lean_object* v_rhs_123_, lean_object* v_h_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Std_Sat_AIG_RelabelNat_State_addGate(v_00_u03b1_115_, v_inst_116_, v_inst_117_, v_idx_118_, v_decls_119_, v_hidx_120_, v_state_121_, v_lhs_122_, v_rhs_123_, v_h_124_);
lean_dec(v_rhs_123_);
lean_dec(v_lhs_122_);
lean_dec_ref(v_decls_119_);
lean_dec(v_idx_118_);
lean_dec_ref(v_inst_117_);
lean_dec_ref(v_inst_116_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___redArg(lean_object* v_inst_126_, lean_object* v_inst_127_, lean_object* v_decls_128_, lean_object* v_idx_129_, lean_object* v_state_130_){
_start:
{
lean_object* v___x_131_; uint8_t v___x_132_; 
v___x_131_ = lean_array_get_size(v_decls_128_);
v___x_132_ = lean_nat_dec_lt(v_idx_129_, v___x_131_);
if (v___x_132_ == 0)
{
lean_dec(v_idx_129_);
lean_dec_ref(v_inst_127_);
lean_dec_ref(v_inst_126_);
return v_state_130_;
}
else
{
lean_object* v_decl_133_; 
v_decl_133_ = lean_array_fget_borrowed(v_decls_128_, v_idx_129_);
switch(lean_obj_tag(v_decl_133_))
{
case 0:
{
lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_134_ = lean_unsigned_to_nat(1u);
v___x_135_ = lean_nat_add(v_idx_129_, v___x_134_);
lean_dec(v_idx_129_);
v___x_136_ = l_Std_Sat_AIG_RelabelNat_State_addFalse___redArg(v_state_130_);
v_idx_129_ = v___x_135_;
v_state_130_ = v___x_136_;
goto _start;
}
case 1:
{
lean_object* v_idx_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v_idx_138_ = lean_ctor_get(v_decl_133_, 0);
v___x_139_ = lean_unsigned_to_nat(1u);
v___x_140_ = lean_nat_add(v_idx_129_, v___x_139_);
lean_dec(v_idx_129_);
lean_inc(v_idx_138_);
lean_inc_ref(v_inst_127_);
lean_inc_ref(v_inst_126_);
v___x_141_ = l_Std_Sat_AIG_RelabelNat_State_addAtom___redArg(v_inst_126_, v_inst_127_, v_state_130_, v_idx_138_);
v_idx_129_ = v___x_140_;
v_state_130_ = v___x_141_;
goto _start;
}
default: 
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_143_ = lean_unsigned_to_nat(1u);
v___x_144_ = lean_nat_add(v_idx_129_, v___x_143_);
lean_dec(v_idx_129_);
v___x_145_ = l_Std_Sat_AIG_RelabelNat_State_addGate___redArg(v_state_130_);
v_idx_129_ = v___x_144_;
v_state_130_ = v___x_145_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___redArg___boxed(lean_object* v_inst_147_, lean_object* v_inst_148_, lean_object* v_decls_149_, lean_object* v_idx_150_, lean_object* v_state_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___redArg(v_inst_147_, v_inst_148_, v_decls_149_, v_idx_150_, v_state_151_);
lean_dec_ref(v_decls_149_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go(lean_object* v_00_u03b1_153_, lean_object* v_inst_154_, lean_object* v_inst_155_, lean_object* v_decls_156_, lean_object* v_idx_157_, lean_object* v_state_158_){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___redArg(v_inst_154_, v_inst_155_, v_decls_156_, v_idx_157_, v_state_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___boxed(lean_object* v_00_u03b1_160_, lean_object* v_inst_161_, lean_object* v_inst_162_, lean_object* v_decls_163_, lean_object* v_idx_164_, lean_object* v_state_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go(v_00_u03b1_160_, v_inst_161_, v_inst_162_, v_decls_163_, v_idx_164_, v_state_165_);
lean_dec_ref(v_decls_163_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_RelabelNat_0__Std_Sat_AIG_RelabelNat_State_ofAIGAux_go_match__1_splitter___redArg(lean_object* v_decl_167_, lean_object* v_h__1_168_, lean_object* v_h__2_169_, lean_object* v_h__3_170_){
_start:
{
switch(lean_obj_tag(v_decl_167_))
{
case 0:
{
lean_object* v___x_171_; 
lean_dec(v_h__3_170_);
lean_dec(v_h__1_168_);
v___x_171_ = lean_apply_1(v_h__2_169_, lean_box(0));
return v___x_171_;
}
case 1:
{
lean_object* v_idx_172_; lean_object* v___x_173_; 
lean_dec(v_h__3_170_);
lean_dec(v_h__2_169_);
v_idx_172_ = lean_ctor_get(v_decl_167_, 0);
lean_inc(v_idx_172_);
lean_dec_ref_known(v_decl_167_, 1);
v___x_173_ = lean_apply_2(v_h__1_168_, v_idx_172_, lean_box(0));
return v___x_173_;
}
default: 
{
lean_object* v_l_174_; lean_object* v_r_175_; lean_object* v___x_176_; 
lean_dec(v_h__2_169_);
lean_dec(v_h__1_168_);
v_l_174_ = lean_ctor_get(v_decl_167_, 0);
lean_inc(v_l_174_);
v_r_175_ = lean_ctor_get(v_decl_167_, 1);
lean_inc(v_r_175_);
lean_dec_ref_known(v_decl_167_, 2);
v___x_176_ = lean_apply_3(v_h__3_170_, v_l_174_, v_r_175_, lean_box(0));
return v___x_176_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_RelabelNat_0__Std_Sat_AIG_RelabelNat_State_ofAIGAux_go_match__1_splitter(lean_object* v_00_u03b1_177_, lean_object* v_motive_178_, lean_object* v_decl_179_, lean_object* v_h__1_180_, lean_object* v_h__2_181_, lean_object* v_h__3_182_){
_start:
{
switch(lean_obj_tag(v_decl_179_))
{
case 0:
{
lean_object* v___x_183_; 
lean_dec(v_h__3_182_);
lean_dec(v_h__1_180_);
v___x_183_ = lean_apply_1(v_h__2_181_, lean_box(0));
return v___x_183_;
}
case 1:
{
lean_object* v_idx_184_; lean_object* v___x_185_; 
lean_dec(v_h__3_182_);
lean_dec(v_h__2_181_);
v_idx_184_ = lean_ctor_get(v_decl_179_, 0);
lean_inc(v_idx_184_);
lean_dec_ref_known(v_decl_179_, 1);
v___x_185_ = lean_apply_2(v_h__1_180_, v_idx_184_, lean_box(0));
return v___x_185_;
}
default: 
{
lean_object* v_l_186_; lean_object* v_r_187_; lean_object* v___x_188_; 
lean_dec(v_h__2_181_);
lean_dec(v_h__1_180_);
v_l_186_ = lean_ctor_get(v_decl_179_, 0);
lean_inc(v_l_186_);
v_r_187_ = lean_ctor_get(v_decl_179_, 1);
lean_inc(v_r_187_);
lean_dec_ref_known(v_decl_179_, 2);
v___x_188_ = lean_apply_3(v_h__3_182_, v_l_186_, v_r_187_, lean_box(0));
return v___x_188_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___redArg(lean_object* v_inst_189_, lean_object* v_inst_190_, lean_object* v_aig_191_){
_start:
{
lean_object* v_decls_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v_decls_192_ = lean_ctor_get(v_aig_191_, 0);
v___x_193_ = lean_unsigned_to_nat(0u);
v___x_194_ = lean_obj_once(&l_Std_Sat_AIG_RelabelNat_State_empty___closed__0, &l_Std_Sat_AIG_RelabelNat_State_empty___closed__0_once, _init_l_Std_Sat_AIG_RelabelNat_State_empty___closed__0);
v___x_195_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___redArg(v_inst_189_, v_inst_190_, v_decls_192_, v___x_193_, v___x_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___redArg___boxed(lean_object* v_inst_196_, lean_object* v_inst_197_, lean_object* v_aig_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___redArg(v_inst_196_, v_inst_197_, v_aig_198_);
lean_dec_ref(v_aig_198_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux(lean_object* v_00_u03b1_200_, lean_object* v_inst_201_, lean_object* v_inst_202_, lean_object* v_aig_203_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___redArg(v_inst_201_, v_inst_202_, v_aig_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___boxed(lean_object* v_00_u03b1_205_, lean_object* v_inst_206_, lean_object* v_inst_207_, lean_object* v_aig_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux(v_00_u03b1_205_, v_inst_206_, v_inst_207_, v_aig_208_);
lean_dec_ref(v_aig_208_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIG___redArg(lean_object* v_inst_210_, lean_object* v_inst_211_, lean_object* v_aig_212_){
_start:
{
lean_object* v___x_213_; lean_object* v_map_214_; 
v___x_213_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___redArg(v_inst_210_, v_inst_211_, v_aig_212_);
v_map_214_ = lean_ctor_get(v___x_213_, 1);
lean_inc_ref(v_map_214_);
lean_dec_ref(v___x_213_);
return v_map_214_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIG___redArg___boxed(lean_object* v_inst_215_, lean_object* v_inst_216_, lean_object* v_aig_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l_Std_Sat_AIG_RelabelNat_State_ofAIG___redArg(v_inst_215_, v_inst_216_, v_aig_217_);
lean_dec_ref(v_aig_217_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIG(lean_object* v_00_u03b1_219_, lean_object* v_inst_220_, lean_object* v_inst_221_, lean_object* v_aig_222_){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = l_Std_Sat_AIG_RelabelNat_State_ofAIG___redArg(v_inst_220_, v_inst_221_, v_aig_222_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIG___boxed(lean_object* v_00_u03b1_224_, lean_object* v_inst_225_, lean_object* v_inst_226_, lean_object* v_aig_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Std_Sat_AIG_RelabelNat_State_ofAIG(v_00_u03b1_224_, v_inst_225_, v_inst_226_, v_aig_227_);
lean_dec_ref(v_aig_227_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat_x27___redArg___lam__0(lean_object* v___f_229_, lean_object* v_inst_230_, lean_object* v_map_231_, lean_object* v_x_232_){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_229_, v_inst_230_, v_map_231_, v_x_232_);
if (lean_obj_tag(v___x_233_) == 0)
{
lean_object* v___x_234_; 
v___x_234_ = lean_unsigned_to_nat(0u);
return v___x_234_;
}
else
{
lean_object* v_val_235_; 
v_val_235_ = lean_ctor_get(v___x_233_, 0);
lean_inc(v_val_235_);
lean_dec_ref_known(v___x_233_, 1);
return v_val_235_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat_x27___redArg___lam__0___boxed(lean_object* v___f_236_, lean_object* v_inst_237_, lean_object* v_map_238_, lean_object* v_x_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Std_Sat_AIG_relabelNat_x27___redArg___lam__0(v___f_236_, v_inst_237_, v_map_238_, v_x_239_);
lean_dec_ref(v_map_238_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat_x27___redArg(lean_object* v_inst_241_, lean_object* v_inst_242_, lean_object* v_aig_243_){
_start:
{
lean_object* v_map_244_; lean_object* v___f_245_; lean_object* v___f_246_; lean_object* v_aig_247_; lean_object* v___x_248_; 
lean_inc_ref(v_inst_242_);
lean_inc_ref(v_inst_241_);
v_map_244_ = l_Std_Sat_AIG_RelabelNat_State_ofAIG___redArg(v_inst_241_, v_inst_242_, v_aig_243_);
v___f_245_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_245_, 0, v_inst_241_);
lean_inc_ref(v_map_244_);
v___f_246_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_relabelNat_x27___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_246_, 0, v___f_245_);
lean_closure_set(v___f_246_, 1, v_inst_242_);
lean_closure_set(v___f_246_, 2, v_map_244_);
v_aig_247_ = l_Std_Sat_AIG_relabel___redArg(v___f_246_, v_aig_243_);
v___x_248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_248_, 0, v_aig_247_);
lean_ctor_set(v___x_248_, 1, v_map_244_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat_x27(lean_object* v_00_u03b1_249_, lean_object* v_inst_250_, lean_object* v_inst_251_, lean_object* v_aig_252_){
_start:
{
lean_object* v___x_253_; 
v___x_253_ = l_Std_Sat_AIG_relabelNat_x27___redArg(v_inst_250_, v_inst_251_, v_aig_252_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat___redArg(lean_object* v_inst_254_, lean_object* v_inst_255_, lean_object* v_aig_256_){
_start:
{
lean_object* v___x_257_; lean_object* v_fst_258_; 
v___x_257_ = l_Std_Sat_AIG_relabelNat_x27___redArg(v_inst_254_, v_inst_255_, v_aig_256_);
v_fst_258_ = lean_ctor_get(v___x_257_, 0);
lean_inc(v_fst_258_);
lean_dec_ref(v___x_257_);
return v_fst_258_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat(lean_object* v_00_u03b1_259_, lean_object* v_inst_260_, lean_object* v_inst_261_, lean_object* v_aig_262_){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = l_Std_Sat_AIG_relabelNat___redArg(v_inst_260_, v_inst_261_, v_aig_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_RelabelNat_0__Std_Sat_AIG_relabelNat_x27_match__1_splitter___redArg(lean_object* v_x_264_, lean_object* v_h__1_265_, lean_object* v_h__2_266_){
_start:
{
if (lean_obj_tag(v_x_264_) == 0)
{
lean_object* v___x_267_; lean_object* v___x_268_; 
lean_dec(v_h__1_265_);
v___x_267_ = lean_box(0);
v___x_268_ = lean_apply_1(v_h__2_266_, v___x_267_);
return v___x_268_;
}
else
{
lean_object* v_val_269_; lean_object* v___x_270_; 
lean_dec(v_h__2_266_);
v_val_269_ = lean_ctor_get(v_x_264_, 0);
lean_inc(v_val_269_);
lean_dec_ref_known(v_x_264_, 1);
v___x_270_ = lean_apply_1(v_h__1_265_, v_val_269_);
return v___x_270_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_RelabelNat_0__Std_Sat_AIG_relabelNat_x27_match__1_splitter(lean_object* v_motive_271_, lean_object* v_x_272_, lean_object* v_h__1_273_, lean_object* v_h__2_274_){
_start:
{
if (lean_obj_tag(v_x_272_) == 0)
{
lean_object* v___x_275_; lean_object* v___x_276_; 
lean_dec(v_h__1_273_);
v___x_275_ = lean_box(0);
v___x_276_ = lean_apply_1(v_h__2_274_, v___x_275_);
return v___x_276_;
}
else
{
lean_object* v_val_277_; lean_object* v___x_278_; 
lean_dec(v_h__2_274_);
v_val_277_ = lean_ctor_get(v_x_272_, 0);
lean_inc(v_val_277_);
lean_dec_ref_known(v_x_272_, 1);
v___x_278_ = lean_apply_1(v_h__1_273_, v_val_277_);
return v___x_278_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Entrypoint_relabelNat_x27___redArg(lean_object* v_inst_279_, lean_object* v_inst_280_, lean_object* v_entry_281_){
_start:
{
lean_object* v_aig_282_; lean_object* v_ref_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_309_; 
v_aig_282_ = lean_ctor_get(v_entry_281_, 0);
v_ref_283_ = lean_ctor_get(v_entry_281_, 1);
v_isSharedCheck_309_ = !lean_is_exclusive(v_entry_281_);
if (v_isSharedCheck_309_ == 0)
{
v___x_285_ = v_entry_281_;
v_isShared_286_ = v_isSharedCheck_309_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_ref_283_);
lean_inc(v_aig_282_);
lean_dec(v_entry_281_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_309_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v_res_287_; lean_object* v_fst_288_; lean_object* v_snd_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_308_; 
v_res_287_ = l_Std_Sat_AIG_relabelNat_x27___redArg(v_inst_279_, v_inst_280_, v_aig_282_);
v_fst_288_ = lean_ctor_get(v_res_287_, 0);
v_snd_289_ = lean_ctor_get(v_res_287_, 1);
v_isSharedCheck_308_ = !lean_is_exclusive(v_res_287_);
if (v_isSharedCheck_308_ == 0)
{
v___x_291_ = v_res_287_;
v_isShared_292_ = v_isSharedCheck_308_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_snd_289_);
lean_inc(v_fst_288_);
lean_dec(v_res_287_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_308_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v_gate_293_; uint8_t v_invert_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_307_; 
v_gate_293_ = lean_ctor_get(v_ref_283_, 0);
v_invert_294_ = lean_ctor_get_uint8(v_ref_283_, sizeof(void*)*1);
v_isSharedCheck_307_ = !lean_is_exclusive(v_ref_283_);
if (v_isSharedCheck_307_ == 0)
{
v___x_296_ = v_ref_283_;
v_isShared_297_ = v_isSharedCheck_307_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_gate_293_);
lean_dec(v_ref_283_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_307_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___x_299_; 
if (v_isShared_297_ == 0)
{
v___x_299_ = v___x_296_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v_gate_293_);
lean_ctor_set_uint8(v_reuseFailAlloc_306_, sizeof(void*)*1, v_invert_294_);
v___x_299_ = v_reuseFailAlloc_306_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
lean_object* v_entry_301_; 
if (v_isShared_286_ == 0)
{
lean_ctor_set(v___x_285_, 1, v___x_299_);
lean_ctor_set(v___x_285_, 0, v_fst_288_);
v_entry_301_ = v___x_285_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v_fst_288_);
lean_ctor_set(v_reuseFailAlloc_305_, 1, v___x_299_);
v_entry_301_ = v_reuseFailAlloc_305_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
lean_object* v___x_303_; 
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 0, v_entry_301_);
v___x_303_ = v___x_291_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_entry_301_);
lean_ctor_set(v_reuseFailAlloc_304_, 1, v_snd_289_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
return v___x_303_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Entrypoint_relabelNat_x27(lean_object* v_00_u03b1_310_, lean_object* v_inst_311_, lean_object* v_inst_312_, lean_object* v_entry_313_){
_start:
{
lean_object* v___x_314_; 
v___x_314_ = l_Std_Sat_AIG_Entrypoint_relabelNat_x27___redArg(v_inst_311_, v_inst_312_, v_entry_313_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Entrypoint_relabelNat___redArg(lean_object* v_inst_315_, lean_object* v_inst_316_, lean_object* v_entry_317_){
_start:
{
lean_object* v_ref_318_; lean_object* v_aig_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_336_; 
v_ref_318_ = lean_ctor_get(v_entry_317_, 1);
v_aig_319_ = lean_ctor_get(v_entry_317_, 0);
v_isSharedCheck_336_ = !lean_is_exclusive(v_entry_317_);
if (v_isSharedCheck_336_ == 0)
{
v___x_321_ = v_entry_317_;
v_isShared_322_ = v_isSharedCheck_336_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_ref_318_);
lean_inc(v_aig_319_);
lean_dec(v_entry_317_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_336_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v_gate_323_; uint8_t v_invert_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_335_; 
v_gate_323_ = lean_ctor_get(v_ref_318_, 0);
v_invert_324_ = lean_ctor_get_uint8(v_ref_318_, sizeof(void*)*1);
v_isSharedCheck_335_ = !lean_is_exclusive(v_ref_318_);
if (v_isSharedCheck_335_ == 0)
{
v___x_326_ = v_ref_318_;
v_isShared_327_ = v_isSharedCheck_335_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_gate_323_);
lean_dec(v_ref_318_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_335_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_328_; lean_object* v___x_330_; 
v___x_328_ = l_Std_Sat_AIG_relabelNat___redArg(v_inst_315_, v_inst_316_, v_aig_319_);
if (v_isShared_327_ == 0)
{
v___x_330_ = v___x_326_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_gate_323_);
lean_ctor_set_uint8(v_reuseFailAlloc_334_, sizeof(void*)*1, v_invert_324_);
v___x_330_ = v_reuseFailAlloc_334_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
lean_object* v___x_332_; 
if (v_isShared_322_ == 0)
{
lean_ctor_set(v___x_321_, 1, v___x_330_);
lean_ctor_set(v___x_321_, 0, v___x_328_);
v___x_332_ = v___x_321_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v___x_328_);
lean_ctor_set(v_reuseFailAlloc_333_, 1, v___x_330_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Entrypoint_relabelNat(lean_object* v_00_u03b1_337_, lean_object* v_inst_338_, lean_object* v_inst_339_, lean_object* v_entry_340_){
_start:
{
lean_object* v___x_341_; 
v___x_341_ = l_Std_Sat_AIG_Entrypoint_relabelNat___redArg(v_inst_338_, v_inst_339_, v_entry_340_);
return v___x_341_;
}
}
lean_object* runtime_initialize_Std_Sat_AIG_Relabel(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Sat_AIG_RelabelNat(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Sat_AIG_Relabel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Sat_AIG_RelabelNat(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Sat_AIG_Relabel(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sat_AIG_RelabelNat(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sat_AIG_Relabel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sat_AIG_RelabelNat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Sat_AIG_RelabelNat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Sat_AIG_RelabelNat(builtin);
}
#ifdef __cplusplus
}
#endif

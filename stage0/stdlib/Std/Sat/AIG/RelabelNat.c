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
lean_object* l_UInt64_ofNat___boxed(lean_object*);
lean_object* l_instDecidableEqNat___boxed(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_relabel___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat_map___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat_map___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Sat_AIG_relabelNat_x27___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt64_ofNat___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Sat_AIG_relabelNat_x27___redArg___closed__0 = (const lean_object*)&l_Std_Sat_AIG_relabelNat_x27___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat_map___redArg(lean_object* v_inst_229_, lean_object* v_inst_230_, lean_object* v_m_231_, lean_object* v_x_232_){
_start:
{
lean_object* v___x_233_; lean_object* v___f_234_; lean_object* v___x_235_; 
v___x_233_ = lean_unsigned_to_nat(0u);
v___f_234_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_234_, 0, v_inst_229_);
v___x_235_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v___f_234_, v_inst_230_, v___x_233_, v_m_231_, v_x_232_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat_map___redArg___boxed(lean_object* v_inst_236_, lean_object* v_inst_237_, lean_object* v_m_238_, lean_object* v_x_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Std_Sat_AIG_relabelNat_map___redArg(v_inst_236_, v_inst_237_, v_m_238_, v_x_239_);
lean_dec_ref(v_m_238_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat_map(lean_object* v_00_u03b1_241_, lean_object* v_inst_242_, lean_object* v_inst_243_, lean_object* v_m_244_, lean_object* v_x_245_){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = l_Std_Sat_AIG_relabelNat_map___redArg(v_inst_242_, v_inst_243_, v_m_244_, v_x_245_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat_map___boxed(lean_object* v_00_u03b1_247_, lean_object* v_inst_248_, lean_object* v_inst_249_, lean_object* v_m_250_, lean_object* v_x_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Std_Sat_AIG_relabelNat_map(v_00_u03b1_247_, v_inst_248_, v_inst_249_, v_m_250_, v_x_251_);
lean_dec_ref(v_m_250_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat_x27___redArg(lean_object* v_inst_254_, lean_object* v_inst_255_, lean_object* v_aig_256_){
_start:
{
lean_object* v___f_257_; lean_object* v_map_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v___f_257_ = ((lean_object*)(l_Std_Sat_AIG_relabelNat_x27___redArg___closed__0));
lean_inc_ref(v_inst_255_);
lean_inc_ref(v_inst_254_);
v_map_258_ = l_Std_Sat_AIG_RelabelNat_State_ofAIG___redArg(v_inst_254_, v_inst_255_, v_aig_256_);
v___x_259_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
lean_inc_ref(v_map_258_);
v___x_260_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_relabelNat_map___boxed), 5, 4);
lean_closure_set(v___x_260_, 0, lean_box(0));
lean_closure_set(v___x_260_, 1, v_inst_254_);
lean_closure_set(v___x_260_, 2, v_inst_255_);
lean_closure_set(v___x_260_, 3, v_map_258_);
v___x_261_ = l_Std_Sat_AIG_relabel___redArg(v___f_257_, v___x_259_, v___x_260_, v_aig_256_);
v___x_262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_262_, 0, v___x_261_);
lean_ctor_set(v___x_262_, 1, v_map_258_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat_x27(lean_object* v_00_u03b1_263_, lean_object* v_inst_264_, lean_object* v_inst_265_, lean_object* v_aig_266_){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = l_Std_Sat_AIG_relabelNat_x27___redArg(v_inst_264_, v_inst_265_, v_aig_266_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat___redArg(lean_object* v_inst_268_, lean_object* v_inst_269_, lean_object* v_aig_270_){
_start:
{
lean_object* v___x_271_; lean_object* v_fst_272_; 
v___x_271_ = l_Std_Sat_AIG_relabelNat_x27___redArg(v_inst_268_, v_inst_269_, v_aig_270_);
v_fst_272_ = lean_ctor_get(v___x_271_, 0);
lean_inc(v_fst_272_);
lean_dec_ref(v___x_271_);
return v_fst_272_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat(lean_object* v_00_u03b1_273_, lean_object* v_inst_274_, lean_object* v_inst_275_, lean_object* v_aig_276_){
_start:
{
lean_object* v___x_277_; 
v___x_277_ = l_Std_Sat_AIG_relabelNat___redArg(v_inst_274_, v_inst_275_, v_aig_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Entrypoint_relabelNat_x27___redArg(lean_object* v_inst_278_, lean_object* v_inst_279_, lean_object* v_entry_280_){
_start:
{
lean_object* v_aig_281_; lean_object* v_ref_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_308_; 
v_aig_281_ = lean_ctor_get(v_entry_280_, 0);
v_ref_282_ = lean_ctor_get(v_entry_280_, 1);
v_isSharedCheck_308_ = !lean_is_exclusive(v_entry_280_);
if (v_isSharedCheck_308_ == 0)
{
v___x_284_ = v_entry_280_;
v_isShared_285_ = v_isSharedCheck_308_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_ref_282_);
lean_inc(v_aig_281_);
lean_dec(v_entry_280_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_308_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v_res_286_; lean_object* v_fst_287_; lean_object* v_snd_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_307_; 
v_res_286_ = l_Std_Sat_AIG_relabelNat_x27___redArg(v_inst_278_, v_inst_279_, v_aig_281_);
v_fst_287_ = lean_ctor_get(v_res_286_, 0);
v_snd_288_ = lean_ctor_get(v_res_286_, 1);
v_isSharedCheck_307_ = !lean_is_exclusive(v_res_286_);
if (v_isSharedCheck_307_ == 0)
{
v___x_290_ = v_res_286_;
v_isShared_291_ = v_isSharedCheck_307_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_snd_288_);
lean_inc(v_fst_287_);
lean_dec(v_res_286_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_307_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v_gate_292_; uint8_t v_invert_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_306_; 
v_gate_292_ = lean_ctor_get(v_ref_282_, 0);
v_invert_293_ = lean_ctor_get_uint8(v_ref_282_, sizeof(void*)*1);
v_isSharedCheck_306_ = !lean_is_exclusive(v_ref_282_);
if (v_isSharedCheck_306_ == 0)
{
v___x_295_ = v_ref_282_;
v_isShared_296_ = v_isSharedCheck_306_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_gate_292_);
lean_dec(v_ref_282_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_306_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___x_298_; 
if (v_isShared_296_ == 0)
{
v___x_298_ = v___x_295_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v_gate_292_);
lean_ctor_set_uint8(v_reuseFailAlloc_305_, sizeof(void*)*1, v_invert_293_);
v___x_298_ = v_reuseFailAlloc_305_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
lean_object* v_entry_300_; 
if (v_isShared_285_ == 0)
{
lean_ctor_set(v___x_284_, 1, v___x_298_);
lean_ctor_set(v___x_284_, 0, v_fst_287_);
v_entry_300_ = v___x_284_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_fst_287_);
lean_ctor_set(v_reuseFailAlloc_304_, 1, v___x_298_);
v_entry_300_ = v_reuseFailAlloc_304_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
lean_object* v___x_302_; 
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 0, v_entry_300_);
v___x_302_ = v___x_290_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_entry_300_);
lean_ctor_set(v_reuseFailAlloc_303_, 1, v_snd_288_);
v___x_302_ = v_reuseFailAlloc_303_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
return v___x_302_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Entrypoint_relabelNat_x27(lean_object* v_00_u03b1_309_, lean_object* v_inst_310_, lean_object* v_inst_311_, lean_object* v_entry_312_){
_start:
{
lean_object* v___x_313_; 
v___x_313_ = l_Std_Sat_AIG_Entrypoint_relabelNat_x27___redArg(v_inst_310_, v_inst_311_, v_entry_312_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Entrypoint_relabelNat___redArg(lean_object* v_inst_314_, lean_object* v_inst_315_, lean_object* v_entry_316_){
_start:
{
lean_object* v_ref_317_; lean_object* v_aig_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_335_; 
v_ref_317_ = lean_ctor_get(v_entry_316_, 1);
v_aig_318_ = lean_ctor_get(v_entry_316_, 0);
v_isSharedCheck_335_ = !lean_is_exclusive(v_entry_316_);
if (v_isSharedCheck_335_ == 0)
{
v___x_320_ = v_entry_316_;
v_isShared_321_ = v_isSharedCheck_335_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_ref_317_);
lean_inc(v_aig_318_);
lean_dec(v_entry_316_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_335_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v_gate_322_; uint8_t v_invert_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_334_; 
v_gate_322_ = lean_ctor_get(v_ref_317_, 0);
v_invert_323_ = lean_ctor_get_uint8(v_ref_317_, sizeof(void*)*1);
v_isSharedCheck_334_ = !lean_is_exclusive(v_ref_317_);
if (v_isSharedCheck_334_ == 0)
{
v___x_325_ = v_ref_317_;
v_isShared_326_ = v_isSharedCheck_334_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_gate_322_);
lean_dec(v_ref_317_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_334_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v___x_327_; lean_object* v___x_329_; 
v___x_327_ = l_Std_Sat_AIG_relabelNat___redArg(v_inst_314_, v_inst_315_, v_aig_318_);
if (v_isShared_326_ == 0)
{
v___x_329_ = v___x_325_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_gate_322_);
lean_ctor_set_uint8(v_reuseFailAlloc_333_, sizeof(void*)*1, v_invert_323_);
v___x_329_ = v_reuseFailAlloc_333_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
lean_object* v___x_331_; 
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 1, v___x_329_);
lean_ctor_set(v___x_320_, 0, v___x_327_);
v___x_331_ = v___x_320_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v___x_327_);
lean_ctor_set(v_reuseFailAlloc_332_, 1, v___x_329_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Entrypoint_relabelNat(lean_object* v_00_u03b1_336_, lean_object* v_inst_337_, lean_object* v_inst_338_, lean_object* v_entry_339_){
_start:
{
lean_object* v___x_340_; 
v___x_340_ = l_Std_Sat_AIG_Entrypoint_relabelNat___redArg(v_inst_337_, v_inst_338_, v_entry_339_);
return v___x_340_;
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

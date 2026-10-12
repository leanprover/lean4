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
lean_object* l_Std_Sat_AIG_RelabelNat_State_empty___redArg(){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lean_obj_once(&l_Std_Sat_AIG_RelabelNat_State_empty___redArg___closed__2, &l_Std_Sat_AIG_RelabelNat_State_empty___redArg___closed__2_once, _init_l_Std_Sat_AIG_RelabelNat_State_empty___redArg___closed__2);
return v___x_11_;
}
}
LEAN_EXPORT void l_Std_Sat_AIG_RelabelNat_State_empty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_12_;
v_res_12_ = l_Std_Sat_AIG_RelabelNat_State_empty___redArg();
stack->m_obj
 = v_res_12_;
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_empty___redArg___boxed(lean_object* v___dummy_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Std_Sat_AIG_RelabelNat_State_empty___redArg();
return v_res_14_;
}
}
static lean_object* _init_l_Std_Sat_AIG_RelabelNat_State_empty___closed__0(void){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = l_Std_Sat_AIG_RelabelNat_State_empty___redArg();
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_empty(lean_object* v_00_u03b1_16_, lean_object* v_inst_17_, lean_object* v_inst_18_, lean_object* v_decls_19_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = lean_obj_once(&l_Std_Sat_AIG_RelabelNat_State_empty___closed__0, &l_Std_Sat_AIG_RelabelNat_State_empty___closed__0_once, _init_l_Std_Sat_AIG_RelabelNat_State_empty___closed__0);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_empty___boxed(lean_object* v_00_u03b1_21_, lean_object* v_inst_22_, lean_object* v_inst_23_, lean_object* v_decls_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Std_Sat_AIG_RelabelNat_State_empty(v_00_u03b1_21_, v_inst_22_, v_inst_23_, v_decls_24_);
lean_dec_ref(v_decls_24_);
lean_dec_ref(v_inst_23_);
lean_dec_ref(v_inst_22_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addAtom___redArg(lean_object* v_inst_26_, lean_object* v_inst_27_, lean_object* v_state_28_, lean_object* v_a_29_){
_start:
{
lean_object* v_max_30_; lean_object* v_map_31_; lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_46_; 
v_max_30_ = lean_ctor_get(v_state_28_, 0);
v_map_31_ = lean_ctor_get(v_state_28_, 1);
v_isSharedCheck_46_ = !lean_is_exclusive(v_state_28_);
if (v_isSharedCheck_46_ == 0)
{
v___x_33_ = v_state_28_;
v_isShared_34_ = v_isSharedCheck_46_;
goto v_resetjp_32_;
}
else
{
lean_inc(v_map_31_);
lean_inc(v_max_30_);
lean_dec(v_state_28_);
v___x_33_ = lean_box(0);
v_isShared_34_ = v_isSharedCheck_46_;
goto v_resetjp_32_;
}
v_resetjp_32_:
{
lean_object* v___f_35_; lean_object* v___x_36_; 
v___f_35_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_35_, 0, v_inst_26_);
lean_inc(v_a_29_);
lean_inc_ref(v_inst_27_);
lean_inc_ref(v___f_35_);
v___x_36_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_35_, v_inst_27_, v_map_31_, v_a_29_);
if (lean_obj_tag(v___x_36_) == 0)
{
lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_41_; 
v___x_37_ = lean_unsigned_to_nat(1u);
v___x_38_ = lean_nat_add(v_max_30_, v___x_37_);
v___x_39_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_35_, v_inst_27_, v_map_31_, v_a_29_, v_max_30_);
if (v_isShared_34_ == 0)
{
lean_ctor_set(v___x_33_, 1, v___x_39_);
lean_ctor_set(v___x_33_, 0, v___x_38_);
v___x_41_ = v___x_33_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_42_; 
v_reuseFailAlloc_42_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_42_, 0, v___x_38_);
lean_ctor_set(v_reuseFailAlloc_42_, 1, v___x_39_);
v___x_41_ = v_reuseFailAlloc_42_;
goto v_reusejp_40_;
}
v_reusejp_40_:
{
return v___x_41_;
}
}
else
{
lean_object* v___x_44_; 
lean_dec_ref_known(v___x_36_, 1);
lean_dec_ref(v___f_35_);
lean_dec(v_a_29_);
lean_dec_ref(v_inst_27_);
if (v_isShared_34_ == 0)
{
v___x_44_ = v___x_33_;
goto v_reusejp_43_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v_max_30_);
lean_ctor_set(v_reuseFailAlloc_45_, 1, v_map_31_);
v___x_44_ = v_reuseFailAlloc_45_;
goto v_reusejp_43_;
}
v_reusejp_43_:
{
return v___x_44_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addAtom(lean_object* v_00_u03b1_47_, lean_object* v_inst_48_, lean_object* v_inst_49_, lean_object* v_idx_50_, lean_object* v_decls_51_, lean_object* v_hidx_52_, lean_object* v_state_53_, lean_object* v_a_54_, lean_object* v_h_55_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l_Std_Sat_AIG_RelabelNat_State_addAtom___redArg(v_inst_48_, v_inst_49_, v_state_53_, v_a_54_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addAtom___boxed(lean_object* v_00_u03b1_57_, lean_object* v_inst_58_, lean_object* v_inst_59_, lean_object* v_idx_60_, lean_object* v_decls_61_, lean_object* v_hidx_62_, lean_object* v_state_63_, lean_object* v_a_64_, lean_object* v_h_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_Std_Sat_AIG_RelabelNat_State_addAtom(v_00_u03b1_57_, v_inst_58_, v_inst_59_, v_idx_60_, v_decls_61_, v_hidx_62_, v_state_63_, v_a_64_, v_h_65_);
lean_dec_ref(v_decls_61_);
lean_dec(v_idx_60_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addFalse___redArg(lean_object* v_state_67_){
_start:
{
lean_object* v_max_68_; lean_object* v_map_69_; lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_76_; 
v_max_68_ = lean_ctor_get(v_state_67_, 0);
v_map_69_ = lean_ctor_get(v_state_67_, 1);
v_isSharedCheck_76_ = !lean_is_exclusive(v_state_67_);
if (v_isSharedCheck_76_ == 0)
{
v___x_71_ = v_state_67_;
v_isShared_72_ = v_isSharedCheck_76_;
goto v_resetjp_70_;
}
else
{
lean_inc(v_map_69_);
lean_inc(v_max_68_);
lean_dec(v_state_67_);
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
v_reuseFailAlloc_75_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v_max_68_);
lean_ctor_set(v_reuseFailAlloc_75_, 1, v_map_69_);
v___x_74_ = v_reuseFailAlloc_75_;
goto v_reusejp_73_;
}
v_reusejp_73_:
{
return v___x_74_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addFalse(lean_object* v_00_u03b1_77_, lean_object* v_inst_78_, lean_object* v_inst_79_, lean_object* v_idx_80_, lean_object* v_decls_81_, lean_object* v_hidx_82_, lean_object* v_state_83_, lean_object* v_h_84_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = l_Std_Sat_AIG_RelabelNat_State_addFalse___redArg(v_state_83_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addFalse___boxed(lean_object* v_00_u03b1_86_, lean_object* v_inst_87_, lean_object* v_inst_88_, lean_object* v_idx_89_, lean_object* v_decls_90_, lean_object* v_hidx_91_, lean_object* v_state_92_, lean_object* v_h_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_Std_Sat_AIG_RelabelNat_State_addFalse(v_00_u03b1_86_, v_inst_87_, v_inst_88_, v_idx_89_, v_decls_90_, v_hidx_91_, v_state_92_, v_h_93_);
lean_dec_ref(v_decls_90_);
lean_dec(v_idx_89_);
lean_dec_ref(v_inst_88_);
lean_dec_ref(v_inst_87_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addGate___redArg(lean_object* v_state_95_){
_start:
{
lean_object* v_max_96_; lean_object* v_map_97_; lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_104_; 
v_max_96_ = lean_ctor_get(v_state_95_, 0);
v_map_97_ = lean_ctor_get(v_state_95_, 1);
v_isSharedCheck_104_ = !lean_is_exclusive(v_state_95_);
if (v_isSharedCheck_104_ == 0)
{
v___x_99_ = v_state_95_;
v_isShared_100_ = v_isSharedCheck_104_;
goto v_resetjp_98_;
}
else
{
lean_inc(v_map_97_);
lean_inc(v_max_96_);
lean_dec(v_state_95_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_104_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v___x_102_; 
if (v_isShared_100_ == 0)
{
v___x_102_ = v___x_99_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v_max_96_);
lean_ctor_set(v_reuseFailAlloc_103_, 1, v_map_97_);
v___x_102_ = v_reuseFailAlloc_103_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
return v___x_102_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addGate(lean_object* v_00_u03b1_105_, lean_object* v_inst_106_, lean_object* v_inst_107_, lean_object* v_idx_108_, lean_object* v_decls_109_, lean_object* v_hidx_110_, lean_object* v_state_111_, lean_object* v_lhs_112_, lean_object* v_rhs_113_, lean_object* v_h_114_){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = l_Std_Sat_AIG_RelabelNat_State_addGate___redArg(v_state_111_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addGate___boxed(lean_object* v_00_u03b1_116_, lean_object* v_inst_117_, lean_object* v_inst_118_, lean_object* v_idx_119_, lean_object* v_decls_120_, lean_object* v_hidx_121_, lean_object* v_state_122_, lean_object* v_lhs_123_, lean_object* v_rhs_124_, lean_object* v_h_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_Std_Sat_AIG_RelabelNat_State_addGate(v_00_u03b1_116_, v_inst_117_, v_inst_118_, v_idx_119_, v_decls_120_, v_hidx_121_, v_state_122_, v_lhs_123_, v_rhs_124_, v_h_125_);
lean_dec(v_rhs_124_);
lean_dec(v_lhs_123_);
lean_dec_ref(v_decls_120_);
lean_dec(v_idx_119_);
lean_dec_ref(v_inst_118_);
lean_dec_ref(v_inst_117_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___redArg(lean_object* v_inst_127_, lean_object* v_inst_128_, lean_object* v_decls_129_, lean_object* v_idx_130_, lean_object* v_state_131_){
_start:
{
lean_object* v___x_132_; uint8_t v___x_133_; 
v___x_132_ = lean_array_get_size(v_decls_129_);
v___x_133_ = lean_nat_dec_lt(v_idx_130_, v___x_132_);
if (v___x_133_ == 0)
{
lean_dec(v_idx_130_);
lean_dec_ref(v_inst_128_);
lean_dec_ref(v_inst_127_);
return v_state_131_;
}
else
{
lean_object* v_decl_134_; 
v_decl_134_ = lean_array_fget_borrowed(v_decls_129_, v_idx_130_);
switch(lean_obj_tag(v_decl_134_))
{
case 0:
{
lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_135_ = lean_unsigned_to_nat(1u);
v___x_136_ = lean_nat_add(v_idx_130_, v___x_135_);
lean_dec(v_idx_130_);
v___x_137_ = l_Std_Sat_AIG_RelabelNat_State_addFalse___redArg(v_state_131_);
v_idx_130_ = v___x_136_;
v_state_131_ = v___x_137_;
goto _start;
}
case 1:
{
lean_object* v_idx_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v_idx_139_ = lean_ctor_get(v_decl_134_, 0);
v___x_140_ = lean_unsigned_to_nat(1u);
v___x_141_ = lean_nat_add(v_idx_130_, v___x_140_);
lean_dec(v_idx_130_);
lean_inc(v_idx_139_);
lean_inc_ref(v_inst_128_);
lean_inc_ref(v_inst_127_);
v___x_142_ = l_Std_Sat_AIG_RelabelNat_State_addAtom___redArg(v_inst_127_, v_inst_128_, v_state_131_, v_idx_139_);
v_idx_130_ = v___x_141_;
v_state_131_ = v___x_142_;
goto _start;
}
default: 
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_144_ = lean_unsigned_to_nat(1u);
v___x_145_ = lean_nat_add(v_idx_130_, v___x_144_);
lean_dec(v_idx_130_);
v___x_146_ = l_Std_Sat_AIG_RelabelNat_State_addGate___redArg(v_state_131_);
v_idx_130_ = v___x_145_;
v_state_131_ = v___x_146_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___redArg___boxed(lean_object* v_inst_148_, lean_object* v_inst_149_, lean_object* v_decls_150_, lean_object* v_idx_151_, lean_object* v_state_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___redArg(v_inst_148_, v_inst_149_, v_decls_150_, v_idx_151_, v_state_152_);
lean_dec_ref(v_decls_150_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go(lean_object* v_00_u03b1_154_, lean_object* v_inst_155_, lean_object* v_inst_156_, lean_object* v_decls_157_, lean_object* v_idx_158_, lean_object* v_state_159_){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___redArg(v_inst_155_, v_inst_156_, v_decls_157_, v_idx_158_, v_state_159_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___boxed(lean_object* v_00_u03b1_161_, lean_object* v_inst_162_, lean_object* v_inst_163_, lean_object* v_decls_164_, lean_object* v_idx_165_, lean_object* v_state_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go(v_00_u03b1_161_, v_inst_162_, v_inst_163_, v_decls_164_, v_idx_165_, v_state_166_);
lean_dec_ref(v_decls_164_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_RelabelNat_0__Std_Sat_AIG_RelabelNat_State_ofAIGAux_go_match__1_splitter___redArg(lean_object* v_decl_168_, lean_object* v_h__1_169_, lean_object* v_h__2_170_, lean_object* v_h__3_171_){
_start:
{
switch(lean_obj_tag(v_decl_168_))
{
case 0:
{
lean_object* v___x_172_; 
lean_dec(v_h__3_171_);
lean_dec(v_h__1_169_);
v___x_172_ = lean_apply_1(v_h__2_170_, lean_box(0));
return v___x_172_;
}
case 1:
{
lean_object* v_idx_173_; lean_object* v___x_174_; 
lean_dec(v_h__3_171_);
lean_dec(v_h__2_170_);
v_idx_173_ = lean_ctor_get(v_decl_168_, 0);
lean_inc(v_idx_173_);
lean_dec_ref_known(v_decl_168_, 1);
v___x_174_ = lean_apply_2(v_h__1_169_, v_idx_173_, lean_box(0));
return v___x_174_;
}
default: 
{
lean_object* v_l_175_; lean_object* v_r_176_; lean_object* v___x_177_; 
lean_dec(v_h__2_170_);
lean_dec(v_h__1_169_);
v_l_175_ = lean_ctor_get(v_decl_168_, 0);
lean_inc(v_l_175_);
v_r_176_ = lean_ctor_get(v_decl_168_, 1);
lean_inc(v_r_176_);
lean_dec_ref_known(v_decl_168_, 2);
v___x_177_ = lean_apply_3(v_h__3_171_, v_l_175_, v_r_176_, lean_box(0));
return v___x_177_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_RelabelNat_0__Std_Sat_AIG_RelabelNat_State_ofAIGAux_go_match__1_splitter(lean_object* v_00_u03b1_178_, lean_object* v_motive_179_, lean_object* v_decl_180_, lean_object* v_h__1_181_, lean_object* v_h__2_182_, lean_object* v_h__3_183_){
_start:
{
switch(lean_obj_tag(v_decl_180_))
{
case 0:
{
lean_object* v___x_184_; 
lean_dec(v_h__3_183_);
lean_dec(v_h__1_181_);
v___x_184_ = lean_apply_1(v_h__2_182_, lean_box(0));
return v___x_184_;
}
case 1:
{
lean_object* v_idx_185_; lean_object* v___x_186_; 
lean_dec(v_h__3_183_);
lean_dec(v_h__2_182_);
v_idx_185_ = lean_ctor_get(v_decl_180_, 0);
lean_inc(v_idx_185_);
lean_dec_ref_known(v_decl_180_, 1);
v___x_186_ = lean_apply_2(v_h__1_181_, v_idx_185_, lean_box(0));
return v___x_186_;
}
default: 
{
lean_object* v_l_187_; lean_object* v_r_188_; lean_object* v___x_189_; 
lean_dec(v_h__2_182_);
lean_dec(v_h__1_181_);
v_l_187_ = lean_ctor_get(v_decl_180_, 0);
lean_inc(v_l_187_);
v_r_188_ = lean_ctor_get(v_decl_180_, 1);
lean_inc(v_r_188_);
lean_dec_ref_known(v_decl_180_, 2);
v___x_189_ = lean_apply_3(v_h__3_183_, v_l_187_, v_r_188_, lean_box(0));
return v___x_189_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___redArg(lean_object* v_inst_190_, lean_object* v_inst_191_, lean_object* v_aig_192_){
_start:
{
lean_object* v_decls_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v_decls_193_ = lean_ctor_get(v_aig_192_, 0);
v___x_194_ = lean_unsigned_to_nat(0u);
v___x_195_ = lean_obj_once(&l_Std_Sat_AIG_RelabelNat_State_empty___closed__0, &l_Std_Sat_AIG_RelabelNat_State_empty___closed__0_once, _init_l_Std_Sat_AIG_RelabelNat_State_empty___closed__0);
v___x_196_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___redArg(v_inst_190_, v_inst_191_, v_decls_193_, v___x_194_, v___x_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___redArg___boxed(lean_object* v_inst_197_, lean_object* v_inst_198_, lean_object* v_aig_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___redArg(v_inst_197_, v_inst_198_, v_aig_199_);
lean_dec_ref(v_aig_199_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux(lean_object* v_00_u03b1_201_, lean_object* v_inst_202_, lean_object* v_inst_203_, lean_object* v_aig_204_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___redArg(v_inst_202_, v_inst_203_, v_aig_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___boxed(lean_object* v_00_u03b1_206_, lean_object* v_inst_207_, lean_object* v_inst_208_, lean_object* v_aig_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux(v_00_u03b1_206_, v_inst_207_, v_inst_208_, v_aig_209_);
lean_dec_ref(v_aig_209_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIG___redArg(lean_object* v_inst_211_, lean_object* v_inst_212_, lean_object* v_aig_213_){
_start:
{
lean_object* v___x_214_; lean_object* v_map_215_; 
v___x_214_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___redArg(v_inst_211_, v_inst_212_, v_aig_213_);
v_map_215_ = lean_ctor_get(v___x_214_, 1);
lean_inc_ref(v_map_215_);
lean_dec_ref(v___x_214_);
return v_map_215_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIG___redArg___boxed(lean_object* v_inst_216_, lean_object* v_inst_217_, lean_object* v_aig_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Std_Sat_AIG_RelabelNat_State_ofAIG___redArg(v_inst_216_, v_inst_217_, v_aig_218_);
lean_dec_ref(v_aig_218_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIG(lean_object* v_00_u03b1_220_, lean_object* v_inst_221_, lean_object* v_inst_222_, lean_object* v_aig_223_){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = l_Std_Sat_AIG_RelabelNat_State_ofAIG___redArg(v_inst_221_, v_inst_222_, v_aig_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIG___boxed(lean_object* v_00_u03b1_225_, lean_object* v_inst_226_, lean_object* v_inst_227_, lean_object* v_aig_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Std_Sat_AIG_RelabelNat_State_ofAIG(v_00_u03b1_225_, v_inst_226_, v_inst_227_, v_aig_228_);
lean_dec_ref(v_aig_228_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat_map___redArg(lean_object* v_inst_230_, lean_object* v_inst_231_, lean_object* v_m_232_, lean_object* v_x_233_){
_start:
{
lean_object* v___x_234_; lean_object* v___f_235_; lean_object* v___x_236_; 
v___x_234_ = lean_unsigned_to_nat(0u);
v___f_235_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_235_, 0, v_inst_230_);
v___x_236_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v___f_235_, v_inst_231_, v___x_234_, v_m_232_, v_x_233_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat_map___redArg___boxed(lean_object* v_inst_237_, lean_object* v_inst_238_, lean_object* v_m_239_, lean_object* v_x_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Std_Sat_AIG_relabelNat_map___redArg(v_inst_237_, v_inst_238_, v_m_239_, v_x_240_);
lean_dec_ref(v_m_239_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat_map(lean_object* v_00_u03b1_242_, lean_object* v_inst_243_, lean_object* v_inst_244_, lean_object* v_m_245_, lean_object* v_x_246_){
_start:
{
lean_object* v___x_247_; 
v___x_247_ = l_Std_Sat_AIG_relabelNat_map___redArg(v_inst_243_, v_inst_244_, v_m_245_, v_x_246_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat_map___boxed(lean_object* v_00_u03b1_248_, lean_object* v_inst_249_, lean_object* v_inst_250_, lean_object* v_m_251_, lean_object* v_x_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_Std_Sat_AIG_relabelNat_map(v_00_u03b1_248_, v_inst_249_, v_inst_250_, v_m_251_, v_x_252_);
lean_dec_ref(v_m_251_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat_x27___redArg(lean_object* v_inst_255_, lean_object* v_inst_256_, lean_object* v_aig_257_){
_start:
{
lean_object* v___f_258_; lean_object* v_map_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v___f_258_ = ((lean_object*)(l_Std_Sat_AIG_relabelNat_x27___redArg___closed__0));
lean_inc_ref(v_inst_256_);
lean_inc_ref(v_inst_255_);
v_map_259_ = l_Std_Sat_AIG_RelabelNat_State_ofAIG___redArg(v_inst_255_, v_inst_256_, v_aig_257_);
v___x_260_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
lean_inc_ref(v_map_259_);
v___x_261_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_relabelNat_map___boxed), 5, 4);
lean_closure_set(v___x_261_, 0, lean_box(0));
lean_closure_set(v___x_261_, 1, v_inst_255_);
lean_closure_set(v___x_261_, 2, v_inst_256_);
lean_closure_set(v___x_261_, 3, v_map_259_);
v___x_262_ = l_Std_Sat_AIG_relabel___redArg(v___f_258_, v___x_260_, v___x_261_, v_aig_257_);
v___x_263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
lean_ctor_set(v___x_263_, 1, v_map_259_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat_x27(lean_object* v_00_u03b1_264_, lean_object* v_inst_265_, lean_object* v_inst_266_, lean_object* v_aig_267_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = l_Std_Sat_AIG_relabelNat_x27___redArg(v_inst_265_, v_inst_266_, v_aig_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat___redArg(lean_object* v_inst_269_, lean_object* v_inst_270_, lean_object* v_aig_271_){
_start:
{
lean_object* v___x_272_; lean_object* v_fst_273_; 
v___x_272_ = l_Std_Sat_AIG_relabelNat_x27___redArg(v_inst_269_, v_inst_270_, v_aig_271_);
v_fst_273_ = lean_ctor_get(v___x_272_, 0);
lean_inc(v_fst_273_);
lean_dec_ref(v___x_272_);
return v_fst_273_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat(lean_object* v_00_u03b1_274_, lean_object* v_inst_275_, lean_object* v_inst_276_, lean_object* v_aig_277_){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = l_Std_Sat_AIG_relabelNat___redArg(v_inst_275_, v_inst_276_, v_aig_277_);
return v___x_278_;
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

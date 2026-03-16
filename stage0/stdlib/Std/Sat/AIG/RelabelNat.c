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
static lean_once_cell_t l_Std_Sat_AIG_RelabelNat_State_empty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_RelabelNat_State_empty___closed__0;
static lean_once_cell_t l_Std_Sat_AIG_RelabelNat_State_empty___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_RelabelNat_State_empty___closed__1;
static lean_once_cell_t l_Std_Sat_AIG_RelabelNat_State_empty___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_RelabelNat_State_empty___closed__2;
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
static lean_object* _init_l_Std_Sat_AIG_RelabelNat_State_empty___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = lean_box(0);
v___x_2_ = lean_unsigned_to_nat(16u);
v___x_3_ = lean_mk_array(v___x_2_, v___x_1_);
return v___x_3_;
}
}
static lean_object* _init_l_Std_Sat_AIG_RelabelNat_State_empty___closed__1(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_obj_once(&l_Std_Sat_AIG_RelabelNat_State_empty___closed__0, &l_Std_Sat_AIG_RelabelNat_State_empty___closed__0_once, _init_l_Std_Sat_AIG_RelabelNat_State_empty___closed__0);
v___x_5_ = lean_unsigned_to_nat(0u);
v___x_6_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
lean_ctor_set(v___x_6_, 1, v___x_4_);
return v___x_6_;
}
}
static lean_object* _init_l_Std_Sat_AIG_RelabelNat_State_empty___closed__2(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_7_ = lean_obj_once(&l_Std_Sat_AIG_RelabelNat_State_empty___closed__1, &l_Std_Sat_AIG_RelabelNat_State_empty___closed__1_once, _init_l_Std_Sat_AIG_RelabelNat_State_empty___closed__1);
v___x_8_ = lean_unsigned_to_nat(0u);
v___x_9_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_9_, 0, v___x_8_);
lean_ctor_set(v___x_9_, 1, v___x_7_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_empty(lean_object* v_00_u03b1_10_, lean_object* v_inst_11_, lean_object* v_inst_12_, lean_object* v_decls_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = lean_obj_once(&l_Std_Sat_AIG_RelabelNat_State_empty___closed__2, &l_Std_Sat_AIG_RelabelNat_State_empty___closed__2_once, _init_l_Std_Sat_AIG_RelabelNat_State_empty___closed__2);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_empty___boxed(lean_object* v_00_u03b1_15_, lean_object* v_inst_16_, lean_object* v_inst_17_, lean_object* v_decls_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l_Std_Sat_AIG_RelabelNat_State_empty(v_00_u03b1_15_, v_inst_16_, v_inst_17_, v_decls_18_);
lean_dec_ref(v_decls_18_);
lean_dec_ref(v_inst_17_);
lean_dec_ref(v_inst_16_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addAtom___redArg(lean_object* v_inst_20_, lean_object* v_inst_21_, lean_object* v_state_22_, lean_object* v_a_23_){
_start:
{
lean_object* v_max_24_; lean_object* v_map_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_40_; 
v_max_24_ = lean_ctor_get(v_state_22_, 0);
v_map_25_ = lean_ctor_get(v_state_22_, 1);
v_isSharedCheck_40_ = !lean_is_exclusive(v_state_22_);
if (v_isSharedCheck_40_ == 0)
{
v___x_27_ = v_state_22_;
v_isShared_28_ = v_isSharedCheck_40_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_map_25_);
lean_inc(v_max_24_);
lean_dec(v_state_22_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_40_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
lean_object* v___f_29_; lean_object* v___x_30_; 
v___f_29_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_29_, 0, v_inst_20_);
lean_inc(v_a_23_);
lean_inc_ref(v_inst_21_);
lean_inc_ref(v___f_29_);
v___x_30_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_29_, v_inst_21_, v_map_25_, v_a_23_);
if (lean_obj_tag(v___x_30_) == 0)
{
lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_35_; 
v___x_31_ = lean_unsigned_to_nat(1u);
v___x_32_ = lean_nat_add(v_max_24_, v___x_31_);
v___x_33_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_29_, v_inst_21_, v_map_25_, v_a_23_, v_max_24_);
if (v_isShared_28_ == 0)
{
lean_ctor_set(v___x_27_, 1, v___x_33_);
lean_ctor_set(v___x_27_, 0, v___x_32_);
v___x_35_ = v___x_27_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_36_; 
v_reuseFailAlloc_36_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_36_, 0, v___x_32_);
lean_ctor_set(v_reuseFailAlloc_36_, 1, v___x_33_);
v___x_35_ = v_reuseFailAlloc_36_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
return v___x_35_;
}
}
else
{
lean_object* v___x_38_; 
lean_dec_ref(v___x_30_);
lean_dec_ref(v___f_29_);
lean_dec(v_a_23_);
lean_dec_ref(v_inst_21_);
if (v_isShared_28_ == 0)
{
v___x_38_ = v___x_27_;
goto v_reusejp_37_;
}
else
{
lean_object* v_reuseFailAlloc_39_; 
v_reuseFailAlloc_39_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_39_, 0, v_max_24_);
lean_ctor_set(v_reuseFailAlloc_39_, 1, v_map_25_);
v___x_38_ = v_reuseFailAlloc_39_;
goto v_reusejp_37_;
}
v_reusejp_37_:
{
return v___x_38_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addAtom(lean_object* v_00_u03b1_41_, lean_object* v_inst_42_, lean_object* v_inst_43_, lean_object* v_idx_44_, lean_object* v_decls_45_, lean_object* v_hidx_46_, lean_object* v_state_47_, lean_object* v_a_48_, lean_object* v_h_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Std_Sat_AIG_RelabelNat_State_addAtom___redArg(v_inst_42_, v_inst_43_, v_state_47_, v_a_48_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addAtom___boxed(lean_object* v_00_u03b1_51_, lean_object* v_inst_52_, lean_object* v_inst_53_, lean_object* v_idx_54_, lean_object* v_decls_55_, lean_object* v_hidx_56_, lean_object* v_state_57_, lean_object* v_a_58_, lean_object* v_h_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Std_Sat_AIG_RelabelNat_State_addAtom(v_00_u03b1_51_, v_inst_52_, v_inst_53_, v_idx_54_, v_decls_55_, v_hidx_56_, v_state_57_, v_a_58_, v_h_59_);
lean_dec_ref(v_decls_55_);
lean_dec(v_idx_54_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addFalse___redArg(lean_object* v_state_61_){
_start:
{
lean_object* v_max_62_; lean_object* v_map_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_70_; 
v_max_62_ = lean_ctor_get(v_state_61_, 0);
v_map_63_ = lean_ctor_get(v_state_61_, 1);
v_isSharedCheck_70_ = !lean_is_exclusive(v_state_61_);
if (v_isSharedCheck_70_ == 0)
{
v___x_65_ = v_state_61_;
v_isShared_66_ = v_isSharedCheck_70_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_map_63_);
lean_inc(v_max_62_);
lean_dec(v_state_61_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_70_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
lean_object* v___x_68_; 
if (v_isShared_66_ == 0)
{
v___x_68_ = v___x_65_;
goto v_reusejp_67_;
}
else
{
lean_object* v_reuseFailAlloc_69_; 
v_reuseFailAlloc_69_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_69_, 0, v_max_62_);
lean_ctor_set(v_reuseFailAlloc_69_, 1, v_map_63_);
v___x_68_ = v_reuseFailAlloc_69_;
goto v_reusejp_67_;
}
v_reusejp_67_:
{
return v___x_68_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addFalse(lean_object* v_00_u03b1_71_, lean_object* v_inst_72_, lean_object* v_inst_73_, lean_object* v_idx_74_, lean_object* v_decls_75_, lean_object* v_hidx_76_, lean_object* v_state_77_, lean_object* v_h_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = l_Std_Sat_AIG_RelabelNat_State_addFalse___redArg(v_state_77_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addFalse___boxed(lean_object* v_00_u03b1_80_, lean_object* v_inst_81_, lean_object* v_inst_82_, lean_object* v_idx_83_, lean_object* v_decls_84_, lean_object* v_hidx_85_, lean_object* v_state_86_, lean_object* v_h_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Std_Sat_AIG_RelabelNat_State_addFalse(v_00_u03b1_80_, v_inst_81_, v_inst_82_, v_idx_83_, v_decls_84_, v_hidx_85_, v_state_86_, v_h_87_);
lean_dec_ref(v_decls_84_);
lean_dec(v_idx_83_);
lean_dec_ref(v_inst_82_);
lean_dec_ref(v_inst_81_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addGate___redArg(lean_object* v_state_89_){
_start:
{
lean_object* v_max_90_; lean_object* v_map_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_98_; 
v_max_90_ = lean_ctor_get(v_state_89_, 0);
v_map_91_ = lean_ctor_get(v_state_89_, 1);
v_isSharedCheck_98_ = !lean_is_exclusive(v_state_89_);
if (v_isSharedCheck_98_ == 0)
{
v___x_93_ = v_state_89_;
v_isShared_94_ = v_isSharedCheck_98_;
goto v_resetjp_92_;
}
else
{
lean_inc(v_map_91_);
lean_inc(v_max_90_);
lean_dec(v_state_89_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_98_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
lean_object* v___x_96_; 
if (v_isShared_94_ == 0)
{
v___x_96_ = v___x_93_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_97_; 
v_reuseFailAlloc_97_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_97_, 0, v_max_90_);
lean_ctor_set(v_reuseFailAlloc_97_, 1, v_map_91_);
v___x_96_ = v_reuseFailAlloc_97_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
return v___x_96_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addGate(lean_object* v_00_u03b1_99_, lean_object* v_inst_100_, lean_object* v_inst_101_, lean_object* v_idx_102_, lean_object* v_decls_103_, lean_object* v_hidx_104_, lean_object* v_state_105_, lean_object* v_lhs_106_, lean_object* v_rhs_107_, lean_object* v_h_108_){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = l_Std_Sat_AIG_RelabelNat_State_addGate___redArg(v_state_105_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addGate___boxed(lean_object* v_00_u03b1_110_, lean_object* v_inst_111_, lean_object* v_inst_112_, lean_object* v_idx_113_, lean_object* v_decls_114_, lean_object* v_hidx_115_, lean_object* v_state_116_, lean_object* v_lhs_117_, lean_object* v_rhs_118_, lean_object* v_h_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Std_Sat_AIG_RelabelNat_State_addGate(v_00_u03b1_110_, v_inst_111_, v_inst_112_, v_idx_113_, v_decls_114_, v_hidx_115_, v_state_116_, v_lhs_117_, v_rhs_118_, v_h_119_);
lean_dec(v_rhs_118_);
lean_dec(v_lhs_117_);
lean_dec_ref(v_decls_114_);
lean_dec(v_idx_113_);
lean_dec_ref(v_inst_112_);
lean_dec_ref(v_inst_111_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___redArg(lean_object* v_inst_121_, lean_object* v_inst_122_, lean_object* v_decls_123_, lean_object* v_idx_124_, lean_object* v_state_125_){
_start:
{
lean_object* v___x_126_; uint8_t v___x_127_; 
v___x_126_ = lean_array_get_size(v_decls_123_);
v___x_127_ = lean_nat_dec_lt(v_idx_124_, v___x_126_);
if (v___x_127_ == 0)
{
lean_dec(v_idx_124_);
lean_dec_ref(v_inst_122_);
lean_dec_ref(v_inst_121_);
return v_state_125_;
}
else
{
lean_object* v_decl_128_; 
v_decl_128_ = lean_array_fget_borrowed(v_decls_123_, v_idx_124_);
switch(lean_obj_tag(v_decl_128_))
{
case 0:
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_129_ = lean_unsigned_to_nat(1u);
v___x_130_ = lean_nat_add(v_idx_124_, v___x_129_);
lean_dec(v_idx_124_);
v___x_131_ = l_Std_Sat_AIG_RelabelNat_State_addFalse___redArg(v_state_125_);
v_idx_124_ = v___x_130_;
v_state_125_ = v___x_131_;
goto _start;
}
case 1:
{
lean_object* v_idx_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v_idx_133_ = lean_ctor_get(v_decl_128_, 0);
v___x_134_ = lean_unsigned_to_nat(1u);
v___x_135_ = lean_nat_add(v_idx_124_, v___x_134_);
lean_dec(v_idx_124_);
lean_inc(v_idx_133_);
lean_inc_ref(v_inst_122_);
lean_inc_ref(v_inst_121_);
v___x_136_ = l_Std_Sat_AIG_RelabelNat_State_addAtom___redArg(v_inst_121_, v_inst_122_, v_state_125_, v_idx_133_);
v_idx_124_ = v___x_135_;
v_state_125_ = v___x_136_;
goto _start;
}
default: 
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_138_ = lean_unsigned_to_nat(1u);
v___x_139_ = lean_nat_add(v_idx_124_, v___x_138_);
lean_dec(v_idx_124_);
v___x_140_ = l_Std_Sat_AIG_RelabelNat_State_addGate___redArg(v_state_125_);
v_idx_124_ = v___x_139_;
v_state_125_ = v___x_140_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___redArg___boxed(lean_object* v_inst_142_, lean_object* v_inst_143_, lean_object* v_decls_144_, lean_object* v_idx_145_, lean_object* v_state_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___redArg(v_inst_142_, v_inst_143_, v_decls_144_, v_idx_145_, v_state_146_);
lean_dec_ref(v_decls_144_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go(lean_object* v_00_u03b1_148_, lean_object* v_inst_149_, lean_object* v_inst_150_, lean_object* v_decls_151_, lean_object* v_idx_152_, lean_object* v_state_153_){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___redArg(v_inst_149_, v_inst_150_, v_decls_151_, v_idx_152_, v_state_153_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___boxed(lean_object* v_00_u03b1_155_, lean_object* v_inst_156_, lean_object* v_inst_157_, lean_object* v_decls_158_, lean_object* v_idx_159_, lean_object* v_state_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go(v_00_u03b1_155_, v_inst_156_, v_inst_157_, v_decls_158_, v_idx_159_, v_state_160_);
lean_dec_ref(v_decls_158_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_RelabelNat_0__Std_Sat_AIG_RelabelNat_State_ofAIGAux_go_match__1_splitter___redArg(lean_object* v_decl_162_, lean_object* v_h__1_163_, lean_object* v_h__2_164_, lean_object* v_h__3_165_){
_start:
{
switch(lean_obj_tag(v_decl_162_))
{
case 0:
{
lean_object* v___x_166_; 
lean_dec(v_h__3_165_);
lean_dec(v_h__1_163_);
v___x_166_ = lean_apply_1(v_h__2_164_, lean_box(0));
return v___x_166_;
}
case 1:
{
lean_object* v_idx_167_; lean_object* v___x_168_; 
lean_dec(v_h__3_165_);
lean_dec(v_h__2_164_);
v_idx_167_ = lean_ctor_get(v_decl_162_, 0);
lean_inc(v_idx_167_);
lean_dec_ref(v_decl_162_);
v___x_168_ = lean_apply_2(v_h__1_163_, v_idx_167_, lean_box(0));
return v___x_168_;
}
default: 
{
lean_object* v_l_169_; lean_object* v_r_170_; lean_object* v___x_171_; 
lean_dec(v_h__2_164_);
lean_dec(v_h__1_163_);
v_l_169_ = lean_ctor_get(v_decl_162_, 0);
lean_inc(v_l_169_);
v_r_170_ = lean_ctor_get(v_decl_162_, 1);
lean_inc(v_r_170_);
lean_dec_ref(v_decl_162_);
v___x_171_ = lean_apply_3(v_h__3_165_, v_l_169_, v_r_170_, lean_box(0));
return v___x_171_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_RelabelNat_0__Std_Sat_AIG_RelabelNat_State_ofAIGAux_go_match__1_splitter(lean_object* v_00_u03b1_172_, lean_object* v_motive_173_, lean_object* v_decl_174_, lean_object* v_h__1_175_, lean_object* v_h__2_176_, lean_object* v_h__3_177_){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = l___private_Std_Sat_AIG_RelabelNat_0__Std_Sat_AIG_RelabelNat_State_ofAIGAux_go_match__1_splitter___redArg(v_decl_174_, v_h__1_175_, v_h__2_176_, v_h__3_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___redArg(lean_object* v_inst_179_, lean_object* v_inst_180_, lean_object* v_aig_181_){
_start:
{
lean_object* v_decls_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v_decls_182_ = lean_ctor_get(v_aig_181_, 0);
v___x_183_ = lean_unsigned_to_nat(0u);
v___x_184_ = l_Std_Sat_AIG_RelabelNat_State_empty(lean_box(0), v_inst_179_, v_inst_180_, v_decls_182_);
v___x_185_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___redArg(v_inst_179_, v_inst_180_, v_decls_182_, v___x_183_, v___x_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___redArg___boxed(lean_object* v_inst_186_, lean_object* v_inst_187_, lean_object* v_aig_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___redArg(v_inst_186_, v_inst_187_, v_aig_188_);
lean_dec_ref(v_aig_188_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux(lean_object* v_00_u03b1_190_, lean_object* v_inst_191_, lean_object* v_inst_192_, lean_object* v_aig_193_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___redArg(v_inst_191_, v_inst_192_, v_aig_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___boxed(lean_object* v_00_u03b1_195_, lean_object* v_inst_196_, lean_object* v_inst_197_, lean_object* v_aig_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux(v_00_u03b1_195_, v_inst_196_, v_inst_197_, v_aig_198_);
lean_dec_ref(v_aig_198_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIG___redArg(lean_object* v_inst_200_, lean_object* v_inst_201_, lean_object* v_aig_202_){
_start:
{
lean_object* v___x_203_; lean_object* v_map_204_; 
v___x_203_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___redArg(v_inst_200_, v_inst_201_, v_aig_202_);
v_map_204_ = lean_ctor_get(v___x_203_, 1);
lean_inc_ref(v_map_204_);
lean_dec_ref(v___x_203_);
return v_map_204_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIG___redArg___boxed(lean_object* v_inst_205_, lean_object* v_inst_206_, lean_object* v_aig_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Std_Sat_AIG_RelabelNat_State_ofAIG___redArg(v_inst_205_, v_inst_206_, v_aig_207_);
lean_dec_ref(v_aig_207_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIG(lean_object* v_00_u03b1_209_, lean_object* v_inst_210_, lean_object* v_inst_211_, lean_object* v_aig_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l_Std_Sat_AIG_RelabelNat_State_ofAIG___redArg(v_inst_210_, v_inst_211_, v_aig_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIG___boxed(lean_object* v_00_u03b1_214_, lean_object* v_inst_215_, lean_object* v_inst_216_, lean_object* v_aig_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l_Std_Sat_AIG_RelabelNat_State_ofAIG(v_00_u03b1_214_, v_inst_215_, v_inst_216_, v_aig_217_);
lean_dec_ref(v_aig_217_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat_x27___redArg___lam__0(lean_object* v___f_219_, lean_object* v_inst_220_, lean_object* v_map_221_, lean_object* v_x_222_){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_219_, v_inst_220_, v_map_221_, v_x_222_);
if (lean_obj_tag(v___x_223_) == 0)
{
lean_object* v___x_224_; 
v___x_224_ = lean_unsigned_to_nat(0u);
return v___x_224_;
}
else
{
lean_object* v_val_225_; 
v_val_225_ = lean_ctor_get(v___x_223_, 0);
lean_inc(v_val_225_);
lean_dec_ref(v___x_223_);
return v_val_225_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat_x27___redArg___lam__0___boxed(lean_object* v___f_226_, lean_object* v_inst_227_, lean_object* v_map_228_, lean_object* v_x_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_Std_Sat_AIG_relabelNat_x27___redArg___lam__0(v___f_226_, v_inst_227_, v_map_228_, v_x_229_);
lean_dec_ref(v_map_228_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat_x27___redArg(lean_object* v_inst_231_, lean_object* v_inst_232_, lean_object* v_aig_233_){
_start:
{
lean_object* v_map_234_; lean_object* v___f_235_; lean_object* v___f_236_; lean_object* v_aig_237_; lean_object* v___x_238_; 
lean_inc_ref(v_inst_232_);
lean_inc_ref(v_inst_231_);
v_map_234_ = l_Std_Sat_AIG_RelabelNat_State_ofAIG___redArg(v_inst_231_, v_inst_232_, v_aig_233_);
v___f_235_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_235_, 0, v_inst_231_);
lean_inc_ref(v_map_234_);
v___f_236_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_relabelNat_x27___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_236_, 0, v___f_235_);
lean_closure_set(v___f_236_, 1, v_inst_232_);
lean_closure_set(v___f_236_, 2, v_map_234_);
v_aig_237_ = l_Std_Sat_AIG_relabel___redArg(v___f_236_, v_aig_233_);
v___x_238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_238_, 0, v_aig_237_);
lean_ctor_set(v___x_238_, 1, v_map_234_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat_x27(lean_object* v_00_u03b1_239_, lean_object* v_inst_240_, lean_object* v_inst_241_, lean_object* v_aig_242_){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = l_Std_Sat_AIG_relabelNat_x27___redArg(v_inst_240_, v_inst_241_, v_aig_242_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat___redArg(lean_object* v_inst_244_, lean_object* v_inst_245_, lean_object* v_aig_246_){
_start:
{
lean_object* v___x_247_; lean_object* v_fst_248_; 
v___x_247_ = l_Std_Sat_AIG_relabelNat_x27___redArg(v_inst_244_, v_inst_245_, v_aig_246_);
v_fst_248_ = lean_ctor_get(v___x_247_, 0);
lean_inc(v_fst_248_);
lean_dec_ref(v___x_247_);
return v_fst_248_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat(lean_object* v_00_u03b1_249_, lean_object* v_inst_250_, lean_object* v_inst_251_, lean_object* v_aig_252_){
_start:
{
lean_object* v___x_253_; 
v___x_253_ = l_Std_Sat_AIG_relabelNat___redArg(v_inst_250_, v_inst_251_, v_aig_252_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_RelabelNat_0__Std_Sat_AIG_relabelNat_x27_match__1_splitter___redArg(lean_object* v_x_254_, lean_object* v_h__1_255_, lean_object* v_h__2_256_){
_start:
{
if (lean_obj_tag(v_x_254_) == 0)
{
lean_object* v___x_257_; lean_object* v___x_258_; 
lean_dec(v_h__1_255_);
v___x_257_ = lean_box(0);
v___x_258_ = lean_apply_1(v_h__2_256_, v___x_257_);
return v___x_258_;
}
else
{
lean_object* v_val_259_; lean_object* v___x_260_; 
lean_dec(v_h__2_256_);
v_val_259_ = lean_ctor_get(v_x_254_, 0);
lean_inc(v_val_259_);
lean_dec_ref(v_x_254_);
v___x_260_ = lean_apply_1(v_h__1_255_, v_val_259_);
return v___x_260_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_RelabelNat_0__Std_Sat_AIG_relabelNat_x27_match__1_splitter(lean_object* v_motive_261_, lean_object* v_x_262_, lean_object* v_h__1_263_, lean_object* v_h__2_264_){
_start:
{
lean_object* v___x_265_; 
v___x_265_ = l___private_Std_Sat_AIG_RelabelNat_0__Std_Sat_AIG_relabelNat_x27_match__1_splitter___redArg(v_x_262_, v_h__1_263_, v_h__2_264_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Entrypoint_relabelNat_x27___redArg(lean_object* v_inst_266_, lean_object* v_inst_267_, lean_object* v_entry_268_){
_start:
{
lean_object* v_aig_269_; lean_object* v_ref_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_296_; 
v_aig_269_ = lean_ctor_get(v_entry_268_, 0);
v_ref_270_ = lean_ctor_get(v_entry_268_, 1);
v_isSharedCheck_296_ = !lean_is_exclusive(v_entry_268_);
if (v_isSharedCheck_296_ == 0)
{
v___x_272_ = v_entry_268_;
v_isShared_273_ = v_isSharedCheck_296_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_ref_270_);
lean_inc(v_aig_269_);
lean_dec(v_entry_268_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_296_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v_res_274_; lean_object* v_fst_275_; lean_object* v_snd_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_295_; 
v_res_274_ = l_Std_Sat_AIG_relabelNat_x27___redArg(v_inst_266_, v_inst_267_, v_aig_269_);
v_fst_275_ = lean_ctor_get(v_res_274_, 0);
v_snd_276_ = lean_ctor_get(v_res_274_, 1);
v_isSharedCheck_295_ = !lean_is_exclusive(v_res_274_);
if (v_isSharedCheck_295_ == 0)
{
v___x_278_ = v_res_274_;
v_isShared_279_ = v_isSharedCheck_295_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_snd_276_);
lean_inc(v_fst_275_);
lean_dec(v_res_274_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_295_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v_gate_280_; uint8_t v_invert_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_294_; 
v_gate_280_ = lean_ctor_get(v_ref_270_, 0);
v_invert_281_ = lean_ctor_get_uint8(v_ref_270_, sizeof(void*)*1);
v_isSharedCheck_294_ = !lean_is_exclusive(v_ref_270_);
if (v_isSharedCheck_294_ == 0)
{
v___x_283_ = v_ref_270_;
v_isShared_284_ = v_isSharedCheck_294_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_gate_280_);
lean_dec(v_ref_270_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_294_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_286_; 
if (v_isShared_284_ == 0)
{
v___x_286_ = v___x_283_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_gate_280_);
lean_ctor_set_uint8(v_reuseFailAlloc_293_, sizeof(void*)*1, v_invert_281_);
v___x_286_ = v_reuseFailAlloc_293_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
lean_object* v_entry_288_; 
if (v_isShared_273_ == 0)
{
lean_ctor_set(v___x_272_, 1, v___x_286_);
lean_ctor_set(v___x_272_, 0, v_fst_275_);
v_entry_288_ = v___x_272_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v_fst_275_);
lean_ctor_set(v_reuseFailAlloc_292_, 1, v___x_286_);
v_entry_288_ = v_reuseFailAlloc_292_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
lean_object* v___x_290_; 
if (v_isShared_279_ == 0)
{
lean_ctor_set(v___x_278_, 0, v_entry_288_);
v___x_290_ = v___x_278_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v_entry_288_);
lean_ctor_set(v_reuseFailAlloc_291_, 1, v_snd_276_);
v___x_290_ = v_reuseFailAlloc_291_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
return v___x_290_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Entrypoint_relabelNat_x27(lean_object* v_00_u03b1_297_, lean_object* v_inst_298_, lean_object* v_inst_299_, lean_object* v_entry_300_){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = l_Std_Sat_AIG_Entrypoint_relabelNat_x27___redArg(v_inst_298_, v_inst_299_, v_entry_300_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Entrypoint_relabelNat___redArg(lean_object* v_inst_302_, lean_object* v_inst_303_, lean_object* v_entry_304_){
_start:
{
lean_object* v_ref_305_; lean_object* v_aig_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_323_; 
v_ref_305_ = lean_ctor_get(v_entry_304_, 1);
v_aig_306_ = lean_ctor_get(v_entry_304_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v_entry_304_);
if (v_isSharedCheck_323_ == 0)
{
v___x_308_ = v_entry_304_;
v_isShared_309_ = v_isSharedCheck_323_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_ref_305_);
lean_inc(v_aig_306_);
lean_dec(v_entry_304_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_323_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v_gate_310_; uint8_t v_invert_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_322_; 
v_gate_310_ = lean_ctor_get(v_ref_305_, 0);
v_invert_311_ = lean_ctor_get_uint8(v_ref_305_, sizeof(void*)*1);
v_isSharedCheck_322_ = !lean_is_exclusive(v_ref_305_);
if (v_isSharedCheck_322_ == 0)
{
v___x_313_ = v_ref_305_;
v_isShared_314_ = v_isSharedCheck_322_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_gate_310_);
lean_dec(v_ref_305_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_322_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_315_; lean_object* v___x_317_; 
v___x_315_ = l_Std_Sat_AIG_relabelNat___redArg(v_inst_302_, v_inst_303_, v_aig_306_);
if (v_isShared_314_ == 0)
{
v___x_317_ = v___x_313_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v_gate_310_);
lean_ctor_set_uint8(v_reuseFailAlloc_321_, sizeof(void*)*1, v_invert_311_);
v___x_317_ = v_reuseFailAlloc_321_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
lean_object* v___x_319_; 
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 1, v___x_317_);
lean_ctor_set(v___x_308_, 0, v___x_315_);
v___x_319_ = v___x_308_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v___x_315_);
lean_ctor_set(v_reuseFailAlloc_320_, 1, v___x_317_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Entrypoint_relabelNat(lean_object* v_00_u03b1_324_, lean_object* v_inst_325_, lean_object* v_inst_326_, lean_object* v_entry_327_){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = l_Std_Sat_AIG_Entrypoint_relabelNat___redArg(v_inst_325_, v_inst_326_, v_entry_327_);
return v___x_328_;
}
}
lean_object* runtime_initialize_Std_Sat_AIG_Relabel(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Sat_AIG_RelabelNat(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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

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
switch(lean_obj_tag(v_decl_174_))
{
case 0:
{
lean_object* v___x_178_; 
lean_dec(v_h__3_177_);
lean_dec(v_h__1_175_);
v___x_178_ = lean_apply_1(v_h__2_176_, lean_box(0));
return v___x_178_;
}
case 1:
{
lean_object* v_idx_179_; lean_object* v___x_180_; 
lean_dec(v_h__3_177_);
lean_dec(v_h__2_176_);
v_idx_179_ = lean_ctor_get(v_decl_174_, 0);
lean_inc(v_idx_179_);
lean_dec_ref(v_decl_174_);
v___x_180_ = lean_apply_2(v_h__1_175_, v_idx_179_, lean_box(0));
return v___x_180_;
}
default: 
{
lean_object* v_l_181_; lean_object* v_r_182_; lean_object* v___x_183_; 
lean_dec(v_h__2_176_);
lean_dec(v_h__1_175_);
v_l_181_ = lean_ctor_get(v_decl_174_, 0);
lean_inc(v_l_181_);
v_r_182_ = lean_ctor_get(v_decl_174_, 1);
lean_inc(v_r_182_);
lean_dec_ref(v_decl_174_);
v___x_183_ = lean_apply_3(v_h__3_177_, v_l_181_, v_r_182_, lean_box(0));
return v___x_183_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___redArg(lean_object* v_inst_184_, lean_object* v_inst_185_, lean_object* v_aig_186_){
_start:
{
lean_object* v_decls_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v_decls_187_ = lean_ctor_get(v_aig_186_, 0);
v___x_188_ = lean_unsigned_to_nat(0u);
v___x_189_ = l_Std_Sat_AIG_RelabelNat_State_empty(lean_box(0), v_inst_184_, v_inst_185_, v_decls_187_);
v___x_190_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___redArg(v_inst_184_, v_inst_185_, v_decls_187_, v___x_188_, v___x_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___redArg___boxed(lean_object* v_inst_191_, lean_object* v_inst_192_, lean_object* v_aig_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___redArg(v_inst_191_, v_inst_192_, v_aig_193_);
lean_dec_ref(v_aig_193_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux(lean_object* v_00_u03b1_195_, lean_object* v_inst_196_, lean_object* v_inst_197_, lean_object* v_aig_198_){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___redArg(v_inst_196_, v_inst_197_, v_aig_198_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___boxed(lean_object* v_00_u03b1_200_, lean_object* v_inst_201_, lean_object* v_inst_202_, lean_object* v_aig_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux(v_00_u03b1_200_, v_inst_201_, v_inst_202_, v_aig_203_);
lean_dec_ref(v_aig_203_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIG___redArg(lean_object* v_inst_205_, lean_object* v_inst_206_, lean_object* v_aig_207_){
_start:
{
lean_object* v___x_208_; lean_object* v_map_209_; 
v___x_208_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___redArg(v_inst_205_, v_inst_206_, v_aig_207_);
v_map_209_ = lean_ctor_get(v___x_208_, 1);
lean_inc_ref(v_map_209_);
lean_dec_ref(v___x_208_);
return v_map_209_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIG___redArg___boxed(lean_object* v_inst_210_, lean_object* v_inst_211_, lean_object* v_aig_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Std_Sat_AIG_RelabelNat_State_ofAIG___redArg(v_inst_210_, v_inst_211_, v_aig_212_);
lean_dec_ref(v_aig_212_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIG(lean_object* v_00_u03b1_214_, lean_object* v_inst_215_, lean_object* v_inst_216_, lean_object* v_aig_217_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = l_Std_Sat_AIG_RelabelNat_State_ofAIG___redArg(v_inst_215_, v_inst_216_, v_aig_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIG___boxed(lean_object* v_00_u03b1_219_, lean_object* v_inst_220_, lean_object* v_inst_221_, lean_object* v_aig_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l_Std_Sat_AIG_RelabelNat_State_ofAIG(v_00_u03b1_219_, v_inst_220_, v_inst_221_, v_aig_222_);
lean_dec_ref(v_aig_222_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat_x27___redArg___lam__0(lean_object* v___f_224_, lean_object* v_inst_225_, lean_object* v_map_226_, lean_object* v_x_227_){
_start:
{
lean_object* v___x_228_; 
v___x_228_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_224_, v_inst_225_, v_map_226_, v_x_227_);
if (lean_obj_tag(v___x_228_) == 0)
{
lean_object* v___x_229_; 
v___x_229_ = lean_unsigned_to_nat(0u);
return v___x_229_;
}
else
{
lean_object* v_val_230_; 
v_val_230_ = lean_ctor_get(v___x_228_, 0);
lean_inc(v_val_230_);
lean_dec_ref(v___x_228_);
return v_val_230_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat_x27___redArg___lam__0___boxed(lean_object* v___f_231_, lean_object* v_inst_232_, lean_object* v_map_233_, lean_object* v_x_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_Std_Sat_AIG_relabelNat_x27___redArg___lam__0(v___f_231_, v_inst_232_, v_map_233_, v_x_234_);
lean_dec_ref(v_map_233_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat_x27___redArg(lean_object* v_inst_236_, lean_object* v_inst_237_, lean_object* v_aig_238_){
_start:
{
lean_object* v_map_239_; lean_object* v___f_240_; lean_object* v___f_241_; lean_object* v_aig_242_; lean_object* v___x_243_; 
lean_inc_ref(v_inst_237_);
lean_inc_ref(v_inst_236_);
v_map_239_ = l_Std_Sat_AIG_RelabelNat_State_ofAIG___redArg(v_inst_236_, v_inst_237_, v_aig_238_);
v___f_240_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_240_, 0, v_inst_236_);
lean_inc_ref(v_map_239_);
v___f_241_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_relabelNat_x27___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_241_, 0, v___f_240_);
lean_closure_set(v___f_241_, 1, v_inst_237_);
lean_closure_set(v___f_241_, 2, v_map_239_);
v_aig_242_ = l_Std_Sat_AIG_relabel___redArg(v___f_241_, v_aig_238_);
v___x_243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_243_, 0, v_aig_242_);
lean_ctor_set(v___x_243_, 1, v_map_239_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat_x27(lean_object* v_00_u03b1_244_, lean_object* v_inst_245_, lean_object* v_inst_246_, lean_object* v_aig_247_){
_start:
{
lean_object* v___x_248_; 
v___x_248_ = l_Std_Sat_AIG_relabelNat_x27___redArg(v_inst_245_, v_inst_246_, v_aig_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat___redArg(lean_object* v_inst_249_, lean_object* v_inst_250_, lean_object* v_aig_251_){
_start:
{
lean_object* v___x_252_; lean_object* v_fst_253_; 
v___x_252_ = l_Std_Sat_AIG_relabelNat_x27___redArg(v_inst_249_, v_inst_250_, v_aig_251_);
v_fst_253_ = lean_ctor_get(v___x_252_, 0);
lean_inc(v_fst_253_);
lean_dec_ref(v___x_252_);
return v_fst_253_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat(lean_object* v_00_u03b1_254_, lean_object* v_inst_255_, lean_object* v_inst_256_, lean_object* v_aig_257_){
_start:
{
lean_object* v___x_258_; 
v___x_258_ = l_Std_Sat_AIG_relabelNat___redArg(v_inst_255_, v_inst_256_, v_aig_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_RelabelNat_0__Std_Sat_AIG_relabelNat_x27_match__1_splitter___redArg(lean_object* v_x_259_, lean_object* v_h__1_260_, lean_object* v_h__2_261_){
_start:
{
if (lean_obj_tag(v_x_259_) == 0)
{
lean_object* v___x_262_; lean_object* v___x_263_; 
lean_dec(v_h__1_260_);
v___x_262_ = lean_box(0);
v___x_263_ = lean_apply_1(v_h__2_261_, v___x_262_);
return v___x_263_;
}
else
{
lean_object* v_val_264_; lean_object* v___x_265_; 
lean_dec(v_h__2_261_);
v_val_264_ = lean_ctor_get(v_x_259_, 0);
lean_inc(v_val_264_);
lean_dec_ref(v_x_259_);
v___x_265_ = lean_apply_1(v_h__1_260_, v_val_264_);
return v___x_265_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_RelabelNat_0__Std_Sat_AIG_relabelNat_x27_match__1_splitter(lean_object* v_motive_266_, lean_object* v_x_267_, lean_object* v_h__1_268_, lean_object* v_h__2_269_){
_start:
{
if (lean_obj_tag(v_x_267_) == 0)
{
lean_object* v___x_270_; lean_object* v___x_271_; 
lean_dec(v_h__1_268_);
v___x_270_ = lean_box(0);
v___x_271_ = lean_apply_1(v_h__2_269_, v___x_270_);
return v___x_271_;
}
else
{
lean_object* v_val_272_; lean_object* v___x_273_; 
lean_dec(v_h__2_269_);
v_val_272_ = lean_ctor_get(v_x_267_, 0);
lean_inc(v_val_272_);
lean_dec_ref(v_x_267_);
v___x_273_ = lean_apply_1(v_h__1_268_, v_val_272_);
return v___x_273_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Entrypoint_relabelNat_x27___redArg(lean_object* v_inst_274_, lean_object* v_inst_275_, lean_object* v_entry_276_){
_start:
{
lean_object* v_aig_277_; lean_object* v_ref_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_304_; 
v_aig_277_ = lean_ctor_get(v_entry_276_, 0);
v_ref_278_ = lean_ctor_get(v_entry_276_, 1);
v_isSharedCheck_304_ = !lean_is_exclusive(v_entry_276_);
if (v_isSharedCheck_304_ == 0)
{
v___x_280_ = v_entry_276_;
v_isShared_281_ = v_isSharedCheck_304_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_ref_278_);
lean_inc(v_aig_277_);
lean_dec(v_entry_276_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_304_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v_res_282_; lean_object* v_fst_283_; lean_object* v_snd_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_303_; 
v_res_282_ = l_Std_Sat_AIG_relabelNat_x27___redArg(v_inst_274_, v_inst_275_, v_aig_277_);
v_fst_283_ = lean_ctor_get(v_res_282_, 0);
v_snd_284_ = lean_ctor_get(v_res_282_, 1);
v_isSharedCheck_303_ = !lean_is_exclusive(v_res_282_);
if (v_isSharedCheck_303_ == 0)
{
v___x_286_ = v_res_282_;
v_isShared_287_ = v_isSharedCheck_303_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_snd_284_);
lean_inc(v_fst_283_);
lean_dec(v_res_282_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_303_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v_gate_288_; uint8_t v_invert_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_302_; 
v_gate_288_ = lean_ctor_get(v_ref_278_, 0);
v_invert_289_ = lean_ctor_get_uint8(v_ref_278_, sizeof(void*)*1);
v_isSharedCheck_302_ = !lean_is_exclusive(v_ref_278_);
if (v_isSharedCheck_302_ == 0)
{
v___x_291_ = v_ref_278_;
v_isShared_292_ = v_isSharedCheck_302_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_gate_288_);
lean_dec(v_ref_278_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_302_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_294_; 
if (v_isShared_292_ == 0)
{
v___x_294_ = v___x_291_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v_gate_288_);
lean_ctor_set_uint8(v_reuseFailAlloc_301_, sizeof(void*)*1, v_invert_289_);
v___x_294_ = v_reuseFailAlloc_301_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
lean_object* v_entry_296_; 
if (v_isShared_281_ == 0)
{
lean_ctor_set(v___x_280_, 1, v___x_294_);
lean_ctor_set(v___x_280_, 0, v_fst_283_);
v_entry_296_ = v___x_280_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v_fst_283_);
lean_ctor_set(v_reuseFailAlloc_300_, 1, v___x_294_);
v_entry_296_ = v_reuseFailAlloc_300_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
lean_object* v___x_298_; 
if (v_isShared_287_ == 0)
{
lean_ctor_set(v___x_286_, 0, v_entry_296_);
v___x_298_ = v___x_286_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v_entry_296_);
lean_ctor_set(v_reuseFailAlloc_299_, 1, v_snd_284_);
v___x_298_ = v_reuseFailAlloc_299_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
return v___x_298_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Entrypoint_relabelNat_x27(lean_object* v_00_u03b1_305_, lean_object* v_inst_306_, lean_object* v_inst_307_, lean_object* v_entry_308_){
_start:
{
lean_object* v___x_309_; 
v___x_309_ = l_Std_Sat_AIG_Entrypoint_relabelNat_x27___redArg(v_inst_306_, v_inst_307_, v_entry_308_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Entrypoint_relabelNat___redArg(lean_object* v_inst_310_, lean_object* v_inst_311_, lean_object* v_entry_312_){
_start:
{
lean_object* v_ref_313_; lean_object* v_aig_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_331_; 
v_ref_313_ = lean_ctor_get(v_entry_312_, 1);
v_aig_314_ = lean_ctor_get(v_entry_312_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v_entry_312_);
if (v_isSharedCheck_331_ == 0)
{
v___x_316_ = v_entry_312_;
v_isShared_317_ = v_isSharedCheck_331_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_ref_313_);
lean_inc(v_aig_314_);
lean_dec(v_entry_312_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_331_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v_gate_318_; uint8_t v_invert_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_330_; 
v_gate_318_ = lean_ctor_get(v_ref_313_, 0);
v_invert_319_ = lean_ctor_get_uint8(v_ref_313_, sizeof(void*)*1);
v_isSharedCheck_330_ = !lean_is_exclusive(v_ref_313_);
if (v_isSharedCheck_330_ == 0)
{
v___x_321_ = v_ref_313_;
v_isShared_322_ = v_isSharedCheck_330_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_gate_318_);
lean_dec(v_ref_313_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_330_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_323_; lean_object* v___x_325_; 
v___x_323_ = l_Std_Sat_AIG_relabelNat___redArg(v_inst_310_, v_inst_311_, v_aig_314_);
if (v_isShared_322_ == 0)
{
v___x_325_ = v___x_321_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v_gate_318_);
lean_ctor_set_uint8(v_reuseFailAlloc_329_, sizeof(void*)*1, v_invert_319_);
v___x_325_ = v_reuseFailAlloc_329_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
lean_object* v___x_327_; 
if (v_isShared_317_ == 0)
{
lean_ctor_set(v___x_316_, 1, v___x_325_);
lean_ctor_set(v___x_316_, 0, v___x_323_);
v___x_327_ = v___x_316_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v___x_323_);
lean_ctor_set(v_reuseFailAlloc_328_, 1, v___x_325_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Entrypoint_relabelNat(lean_object* v_00_u03b1_332_, lean_object* v_inst_333_, lean_object* v_inst_334_, lean_object* v_entry_335_){
_start:
{
lean_object* v___x_336_; 
v___x_336_ = l_Std_Sat_AIG_Entrypoint_relabelNat___redArg(v_inst_333_, v_inst_334_, v_entry_335_);
return v___x_336_;
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

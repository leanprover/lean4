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
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_relabel___redArg(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Sat_AIG_RelabelNat_State_empty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_RelabelNat_State_empty___closed__0;
static lean_once_cell_t l_Std_Sat_AIG_RelabelNat_State_empty___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_RelabelNat_State_empty___closed__1;
static lean_once_cell_t l_Std_Sat_AIG_RelabelNat_State_empty___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_RelabelNat_State_empty___closed__2;
static lean_once_cell_t l_Std_Sat_AIG_RelabelNat_State_empty___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_RelabelNat_State_empty___closed__3;
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
lean_object* v_cellCount_1_; lean_object* v___x_2_; 
v_cellCount_1_ = lean_unsigned_to_nat(16u);
v___x_2_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1_);
return v___x_2_;
}
}
static lean_object* _init_l_Std_Sat_AIG_RelabelNat_State_empty___closed__1(void){
_start:
{
lean_object* v_cellCount_3_; lean_object* v___x_4_; 
v_cellCount_3_ = lean_unsigned_to_nat(16u);
v___x_4_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_3_);
return v___x_4_;
}
}
static lean_object* _init_l_Std_Sat_AIG_RelabelNat_State_empty___closed__2(void){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_5_ = lean_obj_once(&l_Std_Sat_AIG_RelabelNat_State_empty___closed__1, &l_Std_Sat_AIG_RelabelNat_State_empty___closed__1_once, _init_l_Std_Sat_AIG_RelabelNat_State_empty___closed__1);
v___x_6_ = lean_obj_once(&l_Std_Sat_AIG_RelabelNat_State_empty___closed__0, &l_Std_Sat_AIG_RelabelNat_State_empty___closed__0_once, _init_l_Std_Sat_AIG_RelabelNat_State_empty___closed__0);
v___x_7_ = lean_unsigned_to_nat(0u);
v___x_8_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_8_, 0, v___x_7_);
lean_ctor_set(v___x_8_, 1, v___x_6_);
lean_ctor_set(v___x_8_, 2, v___x_5_);
return v___x_8_;
}
}
static lean_object* _init_l_Std_Sat_AIG_RelabelNat_State_empty___closed__3(void){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_9_ = lean_obj_once(&l_Std_Sat_AIG_RelabelNat_State_empty___closed__2, &l_Std_Sat_AIG_RelabelNat_State_empty___closed__2_once, _init_l_Std_Sat_AIG_RelabelNat_State_empty___closed__2);
v___x_10_ = lean_unsigned_to_nat(0u);
v___x_11_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_11_, 0, v___x_10_);
lean_ctor_set(v___x_11_, 1, v___x_9_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_empty(lean_object* v_00_u03b1_12_, lean_object* v_inst_13_, lean_object* v_inst_14_, lean_object* v_decls_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = lean_obj_once(&l_Std_Sat_AIG_RelabelNat_State_empty___closed__3, &l_Std_Sat_AIG_RelabelNat_State_empty___closed__3_once, _init_l_Std_Sat_AIG_RelabelNat_State_empty___closed__3);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_empty___boxed(lean_object* v_00_u03b1_17_, lean_object* v_inst_18_, lean_object* v_inst_19_, lean_object* v_decls_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l_Std_Sat_AIG_RelabelNat_State_empty(v_00_u03b1_17_, v_inst_18_, v_inst_19_, v_decls_20_);
lean_dec_ref(v_decls_20_);
lean_dec_ref(v_inst_19_);
lean_dec_ref(v_inst_18_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addAtom___redArg(lean_object* v_inst_22_, lean_object* v_inst_23_, lean_object* v_state_24_, lean_object* v_a_25_){
_start:
{
lean_object* v_max_26_; lean_object* v_map_27_; lean_object* v___x_29_; uint8_t v_isShared_30_; uint8_t v_isSharedCheck_108_; 
v_max_26_ = lean_ctor_get(v_state_24_, 0);
v_map_27_ = lean_ctor_get(v_state_24_, 1);
v_isSharedCheck_108_ = !lean_is_exclusive(v_state_24_);
if (v_isSharedCheck_108_ == 0)
{
v___x_29_ = v_state_24_;
v_isShared_30_ = v_isSharedCheck_108_;
goto v_resetjp_28_;
}
else
{
lean_inc(v_map_27_);
lean_inc(v_max_26_);
lean_dec(v_state_24_);
v___x_29_ = lean_box(0);
v_isShared_30_ = v_isSharedCheck_108_;
goto v_resetjp_28_;
}
v_resetjp_28_:
{
lean_object* v___f_31_; lean_object* v___x_32_; 
v___f_31_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_31_, 0, v_inst_22_);
lean_inc(v_a_25_);
lean_inc_ref(v_inst_23_);
lean_inc_ref(v___f_31_);
v___x_32_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_31_, v_inst_23_, v_map_27_, v_a_25_);
if (lean_obj_tag(v___x_32_) == 0)
{
lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___y_36_; lean_object* v_i_37_; lean_object* v___y_45_; lean_object* v___y_57_; lean_object* v_i_58_; lean_object* v___x_75_; 
v___x_33_ = lean_unsigned_to_nat(1u);
v___x_34_ = lean_nat_add(v_max_26_, v___x_33_);
lean_inc(v_a_25_);
lean_inc_ref(v_inst_23_);
lean_inc_ref(v___f_31_);
v___x_75_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_31_, v_inst_23_, v_map_27_, v_a_25_);
switch(lean_obj_tag(v___x_75_))
{
case 0:
{
lean_object* v_index_76_; lean_object* v_size_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
lean_dec_ref(v___f_31_);
lean_del_object(v___x_29_);
lean_dec_ref(v_inst_23_);
v_index_76_ = lean_ctor_get(v___x_75_, 0);
lean_inc(v_index_76_);
lean_dec_ref_known(v___x_75_, 3);
v_size_77_ = lean_ctor_get(v_map_27_, 0);
lean_inc(v_size_77_);
v___x_78_ = l_Std_DHashMap_Raw_setEntry___redArg(v_map_27_, v_size_77_, v_index_76_, v_a_25_, v_max_26_);
lean_dec(v_index_76_);
v___x_79_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_79_, 0, v___x_34_);
lean_ctor_set(v___x_79_, 1, v___x_78_);
return v___x_79_;
}
case 1:
{
lean_object* v_index_80_; lean_object* v_size_81_; lean_object* v_keyArray_82_; lean_object* v___x_83_; lean_object* v___x_84_; uint8_t v___x_85_; 
lean_del_object(v___x_29_);
v_index_80_ = lean_ctor_get(v___x_75_, 0);
lean_inc(v_index_80_);
lean_dec_ref_known(v___x_75_, 1);
v_size_81_ = lean_ctor_get(v_map_27_, 0);
v_keyArray_82_ = lean_ctor_get(v_map_27_, 1);
v___x_83_ = lean_nat_add(v_size_81_, v___x_33_);
v___x_84_ = lean_array_get_size(v_keyArray_82_);
v___x_85_ = lean_nat_dec_lt(v___x_83_, v___x_84_);
if (v___x_85_ == 0)
{
lean_dec(v___x_83_);
lean_dec(v_index_80_);
goto v___jp_63_;
}
else
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; uint8_t v___x_90_; 
v___x_86_ = lean_unsigned_to_nat(4u);
v___x_87_ = lean_nat_mul(v___x_83_, v___x_86_);
v___x_88_ = lean_unsigned_to_nat(3u);
v___x_89_ = lean_nat_mul(v___x_84_, v___x_88_);
v___x_90_ = lean_nat_dec_le(v___x_87_, v___x_89_);
lean_dec(v___x_89_);
lean_dec(v___x_87_);
if (v___x_90_ == 0)
{
lean_dec(v___x_83_);
lean_dec(v_index_80_);
goto v___jp_63_;
}
else
{
lean_object* v___x_91_; lean_object* v___x_92_; 
lean_dec_ref(v___f_31_);
lean_dec_ref(v_inst_23_);
v___x_91_ = l_Std_DHashMap_Raw_setEntry___redArg(v_map_27_, v___x_83_, v_index_80_, v_a_25_, v_max_26_);
lean_dec(v_index_80_);
v___x_92_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_92_, 0, v___x_34_);
lean_ctor_set(v___x_92_, 1, v___x_91_);
return v___x_92_;
}
}
}
default: 
{
lean_object* v_size_93_; lean_object* v_keyArray_94_; lean_object* v___x_95_; lean_object* v___x_96_; uint8_t v___x_97_; 
v_size_93_ = lean_ctor_get(v_map_27_, 0);
v_keyArray_94_ = lean_ctor_get(v_map_27_, 1);
v___x_95_ = lean_nat_add(v_size_93_, v___x_33_);
v___x_96_ = lean_array_get_size(v_keyArray_94_);
v___x_97_ = lean_nat_dec_lt(v___x_95_, v___x_96_);
if (v___x_97_ == 0)
{
lean_object* v___x_98_; 
lean_dec(v___x_95_);
lean_inc_ref(v_inst_23_);
lean_inc_ref(v___f_31_);
v___x_98_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_31_, v_inst_23_, v_map_27_);
v___y_45_ = v___x_98_;
goto v___jp_44_;
}
else
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; uint8_t v___x_103_; 
v___x_99_ = lean_unsigned_to_nat(4u);
v___x_100_ = lean_nat_mul(v___x_95_, v___x_99_);
lean_dec(v___x_95_);
v___x_101_ = lean_unsigned_to_nat(3u);
v___x_102_ = lean_nat_mul(v___x_96_, v___x_101_);
v___x_103_ = lean_nat_dec_le(v___x_100_, v___x_102_);
lean_dec(v___x_102_);
lean_dec(v___x_100_);
if (v___x_103_ == 0)
{
lean_object* v___x_104_; 
lean_inc_ref(v_inst_23_);
lean_inc_ref(v___f_31_);
v___x_104_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_31_, v_inst_23_, v_map_27_);
v___y_45_ = v___x_104_;
goto v___jp_44_;
}
else
{
v___y_45_ = v_map_27_;
goto v___jp_44_;
}
}
}
}
v___jp_35_:
{
lean_object* v_size_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_42_; 
v_size_38_ = lean_ctor_get(v___y_36_, 0);
v___x_39_ = lean_nat_add(v_size_38_, v___x_33_);
v___x_40_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_36_, v___x_39_, v_i_37_, v_a_25_, v_max_26_);
lean_dec(v_i_37_);
if (v_isShared_30_ == 0)
{
lean_ctor_set(v___x_29_, 1, v___x_40_);
lean_ctor_set(v___x_29_, 0, v___x_34_);
v___x_42_ = v___x_29_;
goto v_reusejp_41_;
}
else
{
lean_object* v_reuseFailAlloc_43_; 
v_reuseFailAlloc_43_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_43_, 0, v___x_34_);
lean_ctor_set(v_reuseFailAlloc_43_, 1, v___x_40_);
v___x_42_ = v_reuseFailAlloc_43_;
goto v_reusejp_41_;
}
v_reusejp_41_:
{
return v___x_42_;
}
}
v___jp_44_:
{
lean_object* v___x_46_; 
lean_inc(v_a_25_);
v___x_46_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_31_, v_inst_23_, v___y_45_, v_a_25_);
switch(lean_obj_tag(v___x_46_))
{
case 0:
{
lean_object* v_index_47_; lean_object* v_size_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
lean_del_object(v___x_29_);
v_index_47_ = lean_ctor_get(v___x_46_, 0);
lean_inc(v_index_47_);
lean_dec_ref_known(v___x_46_, 3);
v_size_48_ = lean_ctor_get(v___y_45_, 0);
lean_inc(v_size_48_);
v___x_49_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_45_, v_size_48_, v_index_47_, v_a_25_, v_max_26_);
lean_dec(v_index_47_);
v___x_50_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_50_, 0, v___x_34_);
lean_ctor_set(v___x_50_, 1, v___x_49_);
return v___x_50_;
}
case 1:
{
lean_object* v_index_51_; 
v_index_51_ = lean_ctor_get(v___x_46_, 0);
lean_inc(v_index_51_);
lean_dec_ref_known(v___x_46_, 1);
v___y_36_ = v___y_45_;
v_i_37_ = v_index_51_;
goto v___jp_35_;
}
default: 
{
lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_52_ = lean_unsigned_to_nat(0u);
v___x_53_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_45_, v___x_52_);
if (lean_obj_tag(v___x_53_) == 0)
{
lean_object* v_index_54_; 
v_index_54_ = lean_ctor_get(v___x_53_, 0);
lean_inc(v_index_54_);
lean_dec_ref_known(v___x_53_, 1);
v___y_36_ = v___y_45_;
v_i_37_ = v_index_54_;
goto v___jp_35_;
}
else
{
lean_object* v___x_55_; 
lean_del_object(v___x_29_);
lean_dec(v_max_26_);
lean_dec(v_a_25_);
v___x_55_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_55_, 0, v___x_34_);
lean_ctor_set(v___x_55_, 1, v___y_45_);
return v___x_55_;
}
}
}
}
v___jp_56_:
{
lean_object* v_size_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v_size_59_ = lean_ctor_get(v___y_57_, 0);
v___x_60_ = lean_nat_add(v_size_59_, v___x_33_);
v___x_61_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_57_, v___x_60_, v_i_58_, v_a_25_, v_max_26_);
lean_dec(v_i_58_);
v___x_62_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_62_, 0, v___x_34_);
lean_ctor_set(v___x_62_, 1, v___x_61_);
return v___x_62_;
}
v___jp_63_:
{
lean_object* v___x_64_; lean_object* v___x_65_; 
lean_inc_ref(v_inst_23_);
lean_inc_ref(v___f_31_);
v___x_64_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_31_, v_inst_23_, v_map_27_);
lean_inc(v_a_25_);
v___x_65_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_31_, v_inst_23_, v___x_64_, v_a_25_);
switch(lean_obj_tag(v___x_65_))
{
case 0:
{
lean_object* v_index_66_; lean_object* v_size_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v_index_66_ = lean_ctor_get(v___x_65_, 0);
lean_inc(v_index_66_);
lean_dec_ref_known(v___x_65_, 3);
v_size_67_ = lean_ctor_get(v___x_64_, 0);
lean_inc(v_size_67_);
v___x_68_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_64_, v_size_67_, v_index_66_, v_a_25_, v_max_26_);
lean_dec(v_index_66_);
v___x_69_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_69_, 0, v___x_34_);
lean_ctor_set(v___x_69_, 1, v___x_68_);
return v___x_69_;
}
case 1:
{
lean_object* v_index_70_; 
v_index_70_ = lean_ctor_get(v___x_65_, 0);
lean_inc(v_index_70_);
lean_dec_ref_known(v___x_65_, 1);
v___y_57_ = v___x_64_;
v_i_58_ = v_index_70_;
goto v___jp_56_;
}
default: 
{
lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_71_ = lean_unsigned_to_nat(0u);
v___x_72_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_64_, v___x_71_);
if (lean_obj_tag(v___x_72_) == 0)
{
lean_object* v_index_73_; 
v_index_73_ = lean_ctor_get(v___x_72_, 0);
lean_inc(v_index_73_);
lean_dec_ref_known(v___x_72_, 1);
v___y_57_ = v___x_64_;
v_i_58_ = v_index_73_;
goto v___jp_56_;
}
else
{
lean_object* v___x_74_; 
lean_dec(v_max_26_);
lean_dec(v_a_25_);
v___x_74_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_74_, 0, v___x_34_);
lean_ctor_set(v___x_74_, 1, v___x_64_);
return v___x_74_;
}
}
}
}
}
else
{
lean_object* v___x_106_; 
lean_dec_ref_known(v___x_32_, 1);
lean_dec_ref(v___f_31_);
lean_dec(v_a_25_);
lean_dec_ref(v_inst_23_);
if (v_isShared_30_ == 0)
{
v___x_106_ = v___x_29_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v_max_26_);
lean_ctor_set(v_reuseFailAlloc_107_, 1, v_map_27_);
v___x_106_ = v_reuseFailAlloc_107_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
return v___x_106_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addAtom(lean_object* v_00_u03b1_109_, lean_object* v_inst_110_, lean_object* v_inst_111_, lean_object* v_idx_112_, lean_object* v_decls_113_, lean_object* v_hidx_114_, lean_object* v_state_115_, lean_object* v_a_116_, lean_object* v_h_117_){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = l_Std_Sat_AIG_RelabelNat_State_addAtom___redArg(v_inst_110_, v_inst_111_, v_state_115_, v_a_116_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addAtom___boxed(lean_object* v_00_u03b1_119_, lean_object* v_inst_120_, lean_object* v_inst_121_, lean_object* v_idx_122_, lean_object* v_decls_123_, lean_object* v_hidx_124_, lean_object* v_state_125_, lean_object* v_a_126_, lean_object* v_h_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_Std_Sat_AIG_RelabelNat_State_addAtom(v_00_u03b1_119_, v_inst_120_, v_inst_121_, v_idx_122_, v_decls_123_, v_hidx_124_, v_state_125_, v_a_126_, v_h_127_);
lean_dec_ref(v_decls_123_);
lean_dec(v_idx_122_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addFalse___redArg(lean_object* v_state_129_){
_start:
{
lean_object* v_max_130_; lean_object* v_map_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_138_; 
v_max_130_ = lean_ctor_get(v_state_129_, 0);
v_map_131_ = lean_ctor_get(v_state_129_, 1);
v_isSharedCheck_138_ = !lean_is_exclusive(v_state_129_);
if (v_isSharedCheck_138_ == 0)
{
v___x_133_ = v_state_129_;
v_isShared_134_ = v_isSharedCheck_138_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_map_131_);
lean_inc(v_max_130_);
lean_dec(v_state_129_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_138_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v___x_136_; 
if (v_isShared_134_ == 0)
{
v___x_136_ = v___x_133_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v_max_130_);
lean_ctor_set(v_reuseFailAlloc_137_, 1, v_map_131_);
v___x_136_ = v_reuseFailAlloc_137_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
return v___x_136_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addFalse(lean_object* v_00_u03b1_139_, lean_object* v_inst_140_, lean_object* v_inst_141_, lean_object* v_idx_142_, lean_object* v_decls_143_, lean_object* v_hidx_144_, lean_object* v_state_145_, lean_object* v_h_146_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = l_Std_Sat_AIG_RelabelNat_State_addFalse___redArg(v_state_145_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addFalse___boxed(lean_object* v_00_u03b1_148_, lean_object* v_inst_149_, lean_object* v_inst_150_, lean_object* v_idx_151_, lean_object* v_decls_152_, lean_object* v_hidx_153_, lean_object* v_state_154_, lean_object* v_h_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Std_Sat_AIG_RelabelNat_State_addFalse(v_00_u03b1_148_, v_inst_149_, v_inst_150_, v_idx_151_, v_decls_152_, v_hidx_153_, v_state_154_, v_h_155_);
lean_dec_ref(v_decls_152_);
lean_dec(v_idx_151_);
lean_dec_ref(v_inst_150_);
lean_dec_ref(v_inst_149_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addGate___redArg(lean_object* v_state_157_){
_start:
{
lean_object* v_max_158_; lean_object* v_map_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_166_; 
v_max_158_ = lean_ctor_get(v_state_157_, 0);
v_map_159_ = lean_ctor_get(v_state_157_, 1);
v_isSharedCheck_166_ = !lean_is_exclusive(v_state_157_);
if (v_isSharedCheck_166_ == 0)
{
v___x_161_ = v_state_157_;
v_isShared_162_ = v_isSharedCheck_166_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_map_159_);
lean_inc(v_max_158_);
lean_dec(v_state_157_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_166_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___x_164_; 
if (v_isShared_162_ == 0)
{
v___x_164_ = v___x_161_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v_max_158_);
lean_ctor_set(v_reuseFailAlloc_165_, 1, v_map_159_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addGate(lean_object* v_00_u03b1_167_, lean_object* v_inst_168_, lean_object* v_inst_169_, lean_object* v_idx_170_, lean_object* v_decls_171_, lean_object* v_hidx_172_, lean_object* v_state_173_, lean_object* v_lhs_174_, lean_object* v_rhs_175_, lean_object* v_h_176_){
_start:
{
lean_object* v___x_177_; 
v___x_177_ = l_Std_Sat_AIG_RelabelNat_State_addGate___redArg(v_state_173_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addGate___boxed(lean_object* v_00_u03b1_178_, lean_object* v_inst_179_, lean_object* v_inst_180_, lean_object* v_idx_181_, lean_object* v_decls_182_, lean_object* v_hidx_183_, lean_object* v_state_184_, lean_object* v_lhs_185_, lean_object* v_rhs_186_, lean_object* v_h_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Std_Sat_AIG_RelabelNat_State_addGate(v_00_u03b1_178_, v_inst_179_, v_inst_180_, v_idx_181_, v_decls_182_, v_hidx_183_, v_state_184_, v_lhs_185_, v_rhs_186_, v_h_187_);
lean_dec(v_rhs_186_);
lean_dec(v_lhs_185_);
lean_dec_ref(v_decls_182_);
lean_dec(v_idx_181_);
lean_dec_ref(v_inst_180_);
lean_dec_ref(v_inst_179_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___redArg(lean_object* v_inst_189_, lean_object* v_inst_190_, lean_object* v_decls_191_, lean_object* v_idx_192_, lean_object* v_state_193_){
_start:
{
lean_object* v___x_194_; uint8_t v___x_195_; 
v___x_194_ = lean_array_get_size(v_decls_191_);
v___x_195_ = lean_nat_dec_lt(v_idx_192_, v___x_194_);
if (v___x_195_ == 0)
{
lean_dec(v_idx_192_);
lean_dec_ref(v_inst_190_);
lean_dec_ref(v_inst_189_);
return v_state_193_;
}
else
{
lean_object* v_decl_196_; 
v_decl_196_ = lean_array_fget_borrowed(v_decls_191_, v_idx_192_);
switch(lean_obj_tag(v_decl_196_))
{
case 0:
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_197_ = lean_unsigned_to_nat(1u);
v___x_198_ = lean_nat_add(v_idx_192_, v___x_197_);
lean_dec(v_idx_192_);
v___x_199_ = l_Std_Sat_AIG_RelabelNat_State_addFalse___redArg(v_state_193_);
v_idx_192_ = v___x_198_;
v_state_193_ = v___x_199_;
goto _start;
}
case 1:
{
lean_object* v_idx_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v_idx_201_ = lean_ctor_get(v_decl_196_, 0);
v___x_202_ = lean_unsigned_to_nat(1u);
v___x_203_ = lean_nat_add(v_idx_192_, v___x_202_);
lean_dec(v_idx_192_);
lean_inc(v_idx_201_);
lean_inc_ref(v_inst_190_);
lean_inc_ref(v_inst_189_);
v___x_204_ = l_Std_Sat_AIG_RelabelNat_State_addAtom___redArg(v_inst_189_, v_inst_190_, v_state_193_, v_idx_201_);
v_idx_192_ = v___x_203_;
v_state_193_ = v___x_204_;
goto _start;
}
default: 
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_206_ = lean_unsigned_to_nat(1u);
v___x_207_ = lean_nat_add(v_idx_192_, v___x_206_);
lean_dec(v_idx_192_);
v___x_208_ = l_Std_Sat_AIG_RelabelNat_State_addGate___redArg(v_state_193_);
v_idx_192_ = v___x_207_;
v_state_193_ = v___x_208_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___redArg___boxed(lean_object* v_inst_210_, lean_object* v_inst_211_, lean_object* v_decls_212_, lean_object* v_idx_213_, lean_object* v_state_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___redArg(v_inst_210_, v_inst_211_, v_decls_212_, v_idx_213_, v_state_214_);
lean_dec_ref(v_decls_212_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go(lean_object* v_00_u03b1_216_, lean_object* v_inst_217_, lean_object* v_inst_218_, lean_object* v_decls_219_, lean_object* v_idx_220_, lean_object* v_state_221_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___redArg(v_inst_217_, v_inst_218_, v_decls_219_, v_idx_220_, v_state_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___boxed(lean_object* v_00_u03b1_223_, lean_object* v_inst_224_, lean_object* v_inst_225_, lean_object* v_decls_226_, lean_object* v_idx_227_, lean_object* v_state_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go(v_00_u03b1_223_, v_inst_224_, v_inst_225_, v_decls_226_, v_idx_227_, v_state_228_);
lean_dec_ref(v_decls_226_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_RelabelNat_0__Std_Sat_AIG_RelabelNat_State_ofAIGAux_go_match__1_splitter___redArg(lean_object* v_decl_230_, lean_object* v_h__1_231_, lean_object* v_h__2_232_, lean_object* v_h__3_233_){
_start:
{
switch(lean_obj_tag(v_decl_230_))
{
case 0:
{
lean_object* v___x_234_; 
lean_dec(v_h__3_233_);
lean_dec(v_h__1_231_);
v___x_234_ = lean_apply_1(v_h__2_232_, lean_box(0));
return v___x_234_;
}
case 1:
{
lean_object* v_idx_235_; lean_object* v___x_236_; 
lean_dec(v_h__3_233_);
lean_dec(v_h__2_232_);
v_idx_235_ = lean_ctor_get(v_decl_230_, 0);
lean_inc(v_idx_235_);
lean_dec_ref_known(v_decl_230_, 1);
v___x_236_ = lean_apply_2(v_h__1_231_, v_idx_235_, lean_box(0));
return v___x_236_;
}
default: 
{
lean_object* v_l_237_; lean_object* v_r_238_; lean_object* v___x_239_; 
lean_dec(v_h__2_232_);
lean_dec(v_h__1_231_);
v_l_237_ = lean_ctor_get(v_decl_230_, 0);
lean_inc(v_l_237_);
v_r_238_ = lean_ctor_get(v_decl_230_, 1);
lean_inc(v_r_238_);
lean_dec_ref_known(v_decl_230_, 2);
v___x_239_ = lean_apply_3(v_h__3_233_, v_l_237_, v_r_238_, lean_box(0));
return v___x_239_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_RelabelNat_0__Std_Sat_AIG_RelabelNat_State_ofAIGAux_go_match__1_splitter(lean_object* v_00_u03b1_240_, lean_object* v_motive_241_, lean_object* v_decl_242_, lean_object* v_h__1_243_, lean_object* v_h__2_244_, lean_object* v_h__3_245_){
_start:
{
switch(lean_obj_tag(v_decl_242_))
{
case 0:
{
lean_object* v___x_246_; 
lean_dec(v_h__3_245_);
lean_dec(v_h__1_243_);
v___x_246_ = lean_apply_1(v_h__2_244_, lean_box(0));
return v___x_246_;
}
case 1:
{
lean_object* v_idx_247_; lean_object* v___x_248_; 
lean_dec(v_h__3_245_);
lean_dec(v_h__2_244_);
v_idx_247_ = lean_ctor_get(v_decl_242_, 0);
lean_inc(v_idx_247_);
lean_dec_ref_known(v_decl_242_, 1);
v___x_248_ = lean_apply_2(v_h__1_243_, v_idx_247_, lean_box(0));
return v___x_248_;
}
default: 
{
lean_object* v_l_249_; lean_object* v_r_250_; lean_object* v___x_251_; 
lean_dec(v_h__2_244_);
lean_dec(v_h__1_243_);
v_l_249_ = lean_ctor_get(v_decl_242_, 0);
lean_inc(v_l_249_);
v_r_250_ = lean_ctor_get(v_decl_242_, 1);
lean_inc(v_r_250_);
lean_dec_ref_known(v_decl_242_, 2);
v___x_251_ = lean_apply_3(v_h__3_245_, v_l_249_, v_r_250_, lean_box(0));
return v___x_251_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___redArg(lean_object* v_inst_252_, lean_object* v_inst_253_, lean_object* v_aig_254_){
_start:
{
lean_object* v_decls_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v_decls_255_ = lean_ctor_get(v_aig_254_, 0);
v___x_256_ = lean_unsigned_to_nat(0u);
v___x_257_ = l_Std_Sat_AIG_RelabelNat_State_empty(lean_box(0), v_inst_252_, v_inst_253_, v_decls_255_);
v___x_258_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___redArg(v_inst_252_, v_inst_253_, v_decls_255_, v___x_256_, v___x_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___redArg___boxed(lean_object* v_inst_259_, lean_object* v_inst_260_, lean_object* v_aig_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___redArg(v_inst_259_, v_inst_260_, v_aig_261_);
lean_dec_ref(v_aig_261_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux(lean_object* v_00_u03b1_263_, lean_object* v_inst_264_, lean_object* v_inst_265_, lean_object* v_aig_266_){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___redArg(v_inst_264_, v_inst_265_, v_aig_266_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___boxed(lean_object* v_00_u03b1_268_, lean_object* v_inst_269_, lean_object* v_inst_270_, lean_object* v_aig_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux(v_00_u03b1_268_, v_inst_269_, v_inst_270_, v_aig_271_);
lean_dec_ref(v_aig_271_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIG___redArg(lean_object* v_inst_273_, lean_object* v_inst_274_, lean_object* v_aig_275_){
_start:
{
lean_object* v___x_276_; lean_object* v_map_277_; 
v___x_276_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___redArg(v_inst_273_, v_inst_274_, v_aig_275_);
v_map_277_ = lean_ctor_get(v___x_276_, 1);
lean_inc_ref(v_map_277_);
lean_dec_ref(v___x_276_);
return v_map_277_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIG___redArg___boxed(lean_object* v_inst_278_, lean_object* v_inst_279_, lean_object* v_aig_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_Std_Sat_AIG_RelabelNat_State_ofAIG___redArg(v_inst_278_, v_inst_279_, v_aig_280_);
lean_dec_ref(v_aig_280_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIG(lean_object* v_00_u03b1_282_, lean_object* v_inst_283_, lean_object* v_inst_284_, lean_object* v_aig_285_){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = l_Std_Sat_AIG_RelabelNat_State_ofAIG___redArg(v_inst_283_, v_inst_284_, v_aig_285_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIG___boxed(lean_object* v_00_u03b1_287_, lean_object* v_inst_288_, lean_object* v_inst_289_, lean_object* v_aig_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_Std_Sat_AIG_RelabelNat_State_ofAIG(v_00_u03b1_287_, v_inst_288_, v_inst_289_, v_aig_290_);
lean_dec_ref(v_aig_290_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat_x27___redArg___lam__0(lean_object* v___f_292_, lean_object* v_inst_293_, lean_object* v_map_294_, lean_object* v_x_295_){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_292_, v_inst_293_, v_map_294_, v_x_295_);
if (lean_obj_tag(v___x_296_) == 0)
{
lean_object* v___x_297_; 
v___x_297_ = lean_unsigned_to_nat(0u);
return v___x_297_;
}
else
{
lean_object* v_val_298_; 
v_val_298_ = lean_ctor_get(v___x_296_, 0);
lean_inc(v_val_298_);
lean_dec_ref_known(v___x_296_, 1);
return v_val_298_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat_x27___redArg___lam__0___boxed(lean_object* v___f_299_, lean_object* v_inst_300_, lean_object* v_map_301_, lean_object* v_x_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_Std_Sat_AIG_relabelNat_x27___redArg___lam__0(v___f_299_, v_inst_300_, v_map_301_, v_x_302_);
lean_dec_ref(v_map_301_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat_x27___redArg(lean_object* v_inst_304_, lean_object* v_inst_305_, lean_object* v_aig_306_){
_start:
{
lean_object* v_map_307_; lean_object* v___f_308_; lean_object* v___f_309_; lean_object* v_aig_310_; lean_object* v___x_311_; 
lean_inc_ref(v_inst_305_);
lean_inc_ref(v_inst_304_);
v_map_307_ = l_Std_Sat_AIG_RelabelNat_State_ofAIG___redArg(v_inst_304_, v_inst_305_, v_aig_306_);
v___f_308_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_308_, 0, v_inst_304_);
lean_inc_ref(v_map_307_);
v___f_309_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_relabelNat_x27___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_309_, 0, v___f_308_);
lean_closure_set(v___f_309_, 1, v_inst_305_);
lean_closure_set(v___f_309_, 2, v_map_307_);
v_aig_310_ = l_Std_Sat_AIG_relabel___redArg(v___f_309_, v_aig_306_);
v___x_311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_311_, 0, v_aig_310_);
lean_ctor_set(v___x_311_, 1, v_map_307_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat_x27(lean_object* v_00_u03b1_312_, lean_object* v_inst_313_, lean_object* v_inst_314_, lean_object* v_aig_315_){
_start:
{
lean_object* v___x_316_; 
v___x_316_ = l_Std_Sat_AIG_relabelNat_x27___redArg(v_inst_313_, v_inst_314_, v_aig_315_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat___redArg(lean_object* v_inst_317_, lean_object* v_inst_318_, lean_object* v_aig_319_){
_start:
{
lean_object* v___x_320_; lean_object* v_fst_321_; 
v___x_320_ = l_Std_Sat_AIG_relabelNat_x27___redArg(v_inst_317_, v_inst_318_, v_aig_319_);
v_fst_321_ = lean_ctor_get(v___x_320_, 0);
lean_inc(v_fst_321_);
lean_dec_ref(v___x_320_);
return v_fst_321_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat(lean_object* v_00_u03b1_322_, lean_object* v_inst_323_, lean_object* v_inst_324_, lean_object* v_aig_325_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = l_Std_Sat_AIG_relabelNat___redArg(v_inst_323_, v_inst_324_, v_aig_325_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_RelabelNat_0__Std_Sat_AIG_relabelNat_x27_match__1_splitter___redArg(lean_object* v_x_327_, lean_object* v_h__1_328_, lean_object* v_h__2_329_){
_start:
{
if (lean_obj_tag(v_x_327_) == 0)
{
lean_object* v___x_330_; lean_object* v___x_331_; 
lean_dec(v_h__1_328_);
v___x_330_ = lean_box(0);
v___x_331_ = lean_apply_1(v_h__2_329_, v___x_330_);
return v___x_331_;
}
else
{
lean_object* v_val_332_; lean_object* v___x_333_; 
lean_dec(v_h__2_329_);
v_val_332_ = lean_ctor_get(v_x_327_, 0);
lean_inc(v_val_332_);
lean_dec_ref_known(v_x_327_, 1);
v___x_333_ = lean_apply_1(v_h__1_328_, v_val_332_);
return v___x_333_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_RelabelNat_0__Std_Sat_AIG_relabelNat_x27_match__1_splitter(lean_object* v_motive_334_, lean_object* v_x_335_, lean_object* v_h__1_336_, lean_object* v_h__2_337_){
_start:
{
if (lean_obj_tag(v_x_335_) == 0)
{
lean_object* v___x_338_; lean_object* v___x_339_; 
lean_dec(v_h__1_336_);
v___x_338_ = lean_box(0);
v___x_339_ = lean_apply_1(v_h__2_337_, v___x_338_);
return v___x_339_;
}
else
{
lean_object* v_val_340_; lean_object* v___x_341_; 
lean_dec(v_h__2_337_);
v_val_340_ = lean_ctor_get(v_x_335_, 0);
lean_inc(v_val_340_);
lean_dec_ref_known(v_x_335_, 1);
v___x_341_ = lean_apply_1(v_h__1_336_, v_val_340_);
return v___x_341_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Entrypoint_relabelNat_x27___redArg(lean_object* v_inst_342_, lean_object* v_inst_343_, lean_object* v_entry_344_){
_start:
{
lean_object* v_aig_345_; lean_object* v_ref_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_372_; 
v_aig_345_ = lean_ctor_get(v_entry_344_, 0);
v_ref_346_ = lean_ctor_get(v_entry_344_, 1);
v_isSharedCheck_372_ = !lean_is_exclusive(v_entry_344_);
if (v_isSharedCheck_372_ == 0)
{
v___x_348_ = v_entry_344_;
v_isShared_349_ = v_isSharedCheck_372_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_ref_346_);
lean_inc(v_aig_345_);
lean_dec(v_entry_344_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_372_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v_res_350_; lean_object* v_fst_351_; lean_object* v_snd_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_371_; 
v_res_350_ = l_Std_Sat_AIG_relabelNat_x27___redArg(v_inst_342_, v_inst_343_, v_aig_345_);
v_fst_351_ = lean_ctor_get(v_res_350_, 0);
v_snd_352_ = lean_ctor_get(v_res_350_, 1);
v_isSharedCheck_371_ = !lean_is_exclusive(v_res_350_);
if (v_isSharedCheck_371_ == 0)
{
v___x_354_ = v_res_350_;
v_isShared_355_ = v_isSharedCheck_371_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_snd_352_);
lean_inc(v_fst_351_);
lean_dec(v_res_350_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_371_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v_gate_356_; uint8_t v_invert_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_370_; 
v_gate_356_ = lean_ctor_get(v_ref_346_, 0);
v_invert_357_ = lean_ctor_get_uint8(v_ref_346_, sizeof(void*)*1);
v_isSharedCheck_370_ = !lean_is_exclusive(v_ref_346_);
if (v_isSharedCheck_370_ == 0)
{
v___x_359_ = v_ref_346_;
v_isShared_360_ = v_isSharedCheck_370_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_gate_356_);
lean_dec(v_ref_346_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_370_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_362_; 
if (v_isShared_360_ == 0)
{
v___x_362_ = v___x_359_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v_gate_356_);
lean_ctor_set_uint8(v_reuseFailAlloc_369_, sizeof(void*)*1, v_invert_357_);
v___x_362_ = v_reuseFailAlloc_369_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
lean_object* v_entry_364_; 
if (v_isShared_349_ == 0)
{
lean_ctor_set(v___x_348_, 1, v___x_362_);
lean_ctor_set(v___x_348_, 0, v_fst_351_);
v_entry_364_ = v___x_348_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_fst_351_);
lean_ctor_set(v_reuseFailAlloc_368_, 1, v___x_362_);
v_entry_364_ = v_reuseFailAlloc_368_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
lean_object* v___x_366_; 
if (v_isShared_355_ == 0)
{
lean_ctor_set(v___x_354_, 0, v_entry_364_);
v___x_366_ = v___x_354_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_entry_364_);
lean_ctor_set(v_reuseFailAlloc_367_, 1, v_snd_352_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
return v___x_366_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Entrypoint_relabelNat_x27(lean_object* v_00_u03b1_373_, lean_object* v_inst_374_, lean_object* v_inst_375_, lean_object* v_entry_376_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = l_Std_Sat_AIG_Entrypoint_relabelNat_x27___redArg(v_inst_374_, v_inst_375_, v_entry_376_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Entrypoint_relabelNat___redArg(lean_object* v_inst_378_, lean_object* v_inst_379_, lean_object* v_entry_380_){
_start:
{
lean_object* v_ref_381_; lean_object* v_aig_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_399_; 
v_ref_381_ = lean_ctor_get(v_entry_380_, 1);
v_aig_382_ = lean_ctor_get(v_entry_380_, 0);
v_isSharedCheck_399_ = !lean_is_exclusive(v_entry_380_);
if (v_isSharedCheck_399_ == 0)
{
v___x_384_ = v_entry_380_;
v_isShared_385_ = v_isSharedCheck_399_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_ref_381_);
lean_inc(v_aig_382_);
lean_dec(v_entry_380_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_399_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v_gate_386_; uint8_t v_invert_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_398_; 
v_gate_386_ = lean_ctor_get(v_ref_381_, 0);
v_invert_387_ = lean_ctor_get_uint8(v_ref_381_, sizeof(void*)*1);
v_isSharedCheck_398_ = !lean_is_exclusive(v_ref_381_);
if (v_isSharedCheck_398_ == 0)
{
v___x_389_ = v_ref_381_;
v_isShared_390_ = v_isSharedCheck_398_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_gate_386_);
lean_dec(v_ref_381_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_398_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_391_; lean_object* v___x_393_; 
v___x_391_ = l_Std_Sat_AIG_relabelNat___redArg(v_inst_378_, v_inst_379_, v_aig_382_);
if (v_isShared_390_ == 0)
{
v___x_393_ = v___x_389_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_gate_386_);
lean_ctor_set_uint8(v_reuseFailAlloc_397_, sizeof(void*)*1, v_invert_387_);
v___x_393_ = v_reuseFailAlloc_397_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
lean_object* v___x_395_; 
if (v_isShared_385_ == 0)
{
lean_ctor_set(v___x_384_, 1, v___x_393_);
lean_ctor_set(v___x_384_, 0, v___x_391_);
v___x_395_ = v___x_384_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v___x_391_);
lean_ctor_set(v_reuseFailAlloc_396_, 1, v___x_393_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Entrypoint_relabelNat(lean_object* v_00_u03b1_400_, lean_object* v_inst_401_, lean_object* v_inst_402_, lean_object* v_entry_403_){
_start:
{
lean_object* v___x_404_; 
v___x_404_ = l_Std_Sat_AIG_Entrypoint_relabelNat___redArg(v_inst_401_, v_inst_402_, v_entry_403_);
return v___x_404_;
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

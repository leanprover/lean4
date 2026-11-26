// Lean compiler output
// Module: Init.Grind.Ring.CommSemiringAdapter
// Imports: public import Init.Grind.Ring.Envelope public import Init.Grind.Ring.CommSolver import Init.Data.Int.LemmasAux import Init.Omega
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
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* l_Lean_Grind_CommRing_Mon_denote___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_ofVar(lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_combine(lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_mul__nc(lean_object*, lean_object*);
lean_object* l_Int_pow(lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_ofMon(lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_pow__nc(lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_mul(lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Grind_CommRing_Expr_toPolyS_spec__0(lean_object*);
static lean_once_cell_t l_Lean_Grind_CommRing_Expr_toPolyS___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommRing_Expr_toPolyS___closed__0;
static lean_once_cell_t l_Lean_Grind_CommRing_Expr_toPolyS___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommRing_Expr_toPolyS___closed__1;
static lean_once_cell_t l_Lean_Grind_CommRing_Expr_toPolyS___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommRing_Expr_toPolyS___closed__2;
static lean_once_cell_t l_Lean_Grind_CommRing_Expr_toPolyS___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommRing_Expr_toPolyS___closed__3;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyS(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyS__nc(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Expr_toPolyS_match__4_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Expr_toPolyS_match__4_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Expr_toPolyS_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Expr_toPolyS_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteSInt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteSInt___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteSInt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteSInt___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteS___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteS___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteS(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteS___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_denoteS_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_denoteS_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_denote_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_denote_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Mon_denote_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Mon_denote_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_combine_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_combine_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteSList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteSList___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteSList(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteSList___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_NonnegList_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_NonnegList_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Grind_CommRing_Expr_toPolyS_spec__0(lean_object* v_a_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_nat_to_int(v_a_1_);
return v___x_2_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Expr_toPolyS___closed__0(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_unsigned_to_nat(1u);
v___x_4_ = lean_nat_to_int(v___x_3_);
return v___x_4_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Expr_toPolyS___closed__1(void){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPolyS___closed__0, &l_Lean_Grind_CommRing_Expr_toPolyS___closed__0_once, _init_l_Lean_Grind_CommRing_Expr_toPolyS___closed__0);
v___x_6_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Expr_toPolyS___closed__2(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_7_ = lean_unsigned_to_nat(0u);
v___x_8_ = lean_nat_to_int(v___x_7_);
return v___x_8_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Expr_toPolyS___closed__3(void){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_9_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPolyS___closed__2, &l_Lean_Grind_CommRing_Expr_toPolyS___closed__2_once, _init_l_Lean_Grind_CommRing_Expr_toPolyS___closed__2);
v___x_10_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_10_, 0, v___x_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyS(lean_object* v_x_11_){
_start:
{
switch(lean_obj_tag(v_x_11_))
{
case 0:
{
lean_object* v_k_12_; lean_object* v___x_14_; uint8_t v_isShared_15_; uint8_t v_isSharedCheck_21_; 
v_k_12_ = lean_ctor_get(v_x_11_, 0);
v_isSharedCheck_21_ = !lean_is_exclusive(v_x_11_);
if (v_isSharedCheck_21_ == 0)
{
v___x_14_ = v_x_11_;
v_isShared_15_ = v_isSharedCheck_21_;
goto v_resetjp_13_;
}
else
{
lean_inc(v_k_12_);
lean_dec(v_x_11_);
v___x_14_ = lean_box(0);
v_isShared_15_ = v_isSharedCheck_21_;
goto v_resetjp_13_;
}
v_resetjp_13_:
{
lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_19_; 
v___x_16_ = lean_nat_abs(v_k_12_);
lean_dec(v_k_12_);
v___x_17_ = lean_nat_to_int(v___x_16_);
if (v_isShared_15_ == 0)
{
lean_ctor_set(v___x_14_, 0, v___x_17_);
v___x_19_ = v___x_14_;
goto v_reusejp_18_;
}
else
{
lean_object* v_reuseFailAlloc_20_; 
v_reuseFailAlloc_20_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_20_, 0, v___x_17_);
v___x_19_ = v_reuseFailAlloc_20_;
goto v_reusejp_18_;
}
v_reusejp_18_:
{
return v___x_19_;
}
}
}
case 1:
{
lean_object* v_k_22_; lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_30_; 
v_k_22_ = lean_ctor_get(v_x_11_, 0);
v_isSharedCheck_30_ = !lean_is_exclusive(v_x_11_);
if (v_isSharedCheck_30_ == 0)
{
v___x_24_ = v_x_11_;
v_isShared_25_ = v_isSharedCheck_30_;
goto v_resetjp_23_;
}
else
{
lean_inc(v_k_22_);
lean_dec(v_x_11_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_30_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
lean_object* v___x_26_; lean_object* v___x_28_; 
v___x_26_ = lean_nat_to_int(v_k_22_);
if (v_isShared_25_ == 0)
{
lean_ctor_set_tag(v___x_24_, 0);
lean_ctor_set(v___x_24_, 0, v___x_26_);
v___x_28_ = v___x_24_;
goto v_reusejp_27_;
}
else
{
lean_object* v_reuseFailAlloc_29_; 
v_reuseFailAlloc_29_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_29_, 0, v___x_26_);
v___x_28_ = v_reuseFailAlloc_29_;
goto v_reusejp_27_;
}
v_reusejp_27_:
{
return v___x_28_;
}
}
}
case 3:
{
lean_object* v_i_31_; lean_object* v___x_32_; 
v_i_31_ = lean_ctor_get(v_x_11_, 0);
lean_inc(v_i_31_);
lean_dec_ref_known(v_x_11_, 1);
v___x_32_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_31_);
return v___x_32_;
}
case 5:
{
lean_object* v_a_33_; lean_object* v_b_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
v_a_33_ = lean_ctor_get(v_x_11_, 0);
lean_inc_ref(v_a_33_);
v_b_34_ = lean_ctor_get(v_x_11_, 1);
lean_inc_ref(v_b_34_);
lean_dec_ref_known(v_x_11_, 2);
v___x_35_ = l_Lean_Grind_CommRing_Expr_toPolyS(v_a_33_);
v___x_36_ = l_Lean_Grind_CommRing_Expr_toPolyS(v_b_34_);
v___x_37_ = l_Lean_Grind_CommRing_Poly_combine(v___x_35_, v___x_36_);
return v___x_37_;
}
case 7:
{
lean_object* v_a_38_; lean_object* v_b_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v_a_38_ = lean_ctor_get(v_x_11_, 0);
lean_inc_ref(v_a_38_);
v_b_39_ = lean_ctor_get(v_x_11_, 1);
lean_inc_ref(v_b_39_);
lean_dec_ref_known(v_x_11_, 2);
v___x_40_ = l_Lean_Grind_CommRing_Expr_toPolyS(v_a_38_);
v___x_41_ = l_Lean_Grind_CommRing_Expr_toPolyS(v_b_39_);
v___x_42_ = l_Lean_Grind_CommRing_Poly_mul(v___x_40_, v___x_41_);
return v___x_42_;
}
case 8:
{
lean_object* v_a_43_; lean_object* v_k_44_; lean_object* v___x_46_; uint8_t v_isShared_47_; uint8_t v_isSharedCheck_71_; 
v_a_43_ = lean_ctor_get(v_x_11_, 0);
v_k_44_ = lean_ctor_get(v_x_11_, 1);
v_isSharedCheck_71_ = !lean_is_exclusive(v_x_11_);
if (v_isSharedCheck_71_ == 0)
{
v___x_46_ = v_x_11_;
v_isShared_47_ = v_isSharedCheck_71_;
goto v_resetjp_45_;
}
else
{
lean_inc(v_k_44_);
lean_inc(v_a_43_);
lean_dec(v_x_11_);
v___x_46_ = lean_box(0);
v_isShared_47_ = v_isSharedCheck_71_;
goto v_resetjp_45_;
}
v_resetjp_45_:
{
lean_object* v___x_48_; uint8_t v___x_49_; 
v___x_48_ = lean_unsigned_to_nat(0u);
v___x_49_ = lean_nat_dec_eq(v_k_44_, v___x_48_);
if (v___x_49_ == 0)
{
switch(lean_obj_tag(v_a_43_))
{
case 0:
{
lean_object* v_k_50_; lean_object* v___x_52_; uint8_t v_isShared_53_; uint8_t v_isSharedCheck_60_; 
lean_del_object(v___x_46_);
v_k_50_ = lean_ctor_get(v_a_43_, 0);
v_isSharedCheck_60_ = !lean_is_exclusive(v_a_43_);
if (v_isSharedCheck_60_ == 0)
{
v___x_52_ = v_a_43_;
v_isShared_53_ = v_isSharedCheck_60_;
goto v_resetjp_51_;
}
else
{
lean_inc(v_k_50_);
lean_dec(v_a_43_);
v___x_52_ = lean_box(0);
v_isShared_53_ = v_isSharedCheck_60_;
goto v_resetjp_51_;
}
v_resetjp_51_:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_58_; 
v___x_54_ = lean_nat_abs(v_k_50_);
lean_dec(v_k_50_);
v___x_55_ = lean_nat_to_int(v___x_54_);
v___x_56_ = l_Int_pow(v___x_55_, v_k_44_);
lean_dec(v_k_44_);
lean_dec(v___x_55_);
if (v_isShared_53_ == 0)
{
lean_ctor_set(v___x_52_, 0, v___x_56_);
v___x_58_ = v___x_52_;
goto v_reusejp_57_;
}
else
{
lean_object* v_reuseFailAlloc_59_; 
v_reuseFailAlloc_59_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_59_, 0, v___x_56_);
v___x_58_ = v_reuseFailAlloc_59_;
goto v_reusejp_57_;
}
v_reusejp_57_:
{
return v___x_58_;
}
}
}
case 3:
{
lean_object* v_i_61_; lean_object* v___x_63_; 
v_i_61_ = lean_ctor_get(v_a_43_, 0);
lean_inc(v_i_61_);
lean_dec_ref_known(v_a_43_, 1);
if (v_isShared_47_ == 0)
{
lean_ctor_set_tag(v___x_46_, 0);
lean_ctor_set(v___x_46_, 0, v_i_61_);
v___x_63_ = v___x_46_;
goto v_reusejp_62_;
}
else
{
lean_object* v_reuseFailAlloc_67_; 
v_reuseFailAlloc_67_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_67_, 0, v_i_61_);
lean_ctor_set(v_reuseFailAlloc_67_, 1, v_k_44_);
v___x_63_ = v_reuseFailAlloc_67_;
goto v_reusejp_62_;
}
v_reusejp_62_:
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_64_ = lean_box(0);
v___x_65_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_65_, 0, v___x_63_);
lean_ctor_set(v___x_65_, 1, v___x_64_);
v___x_66_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_65_);
return v___x_66_;
}
}
default: 
{
lean_object* v___x_68_; lean_object* v___x_69_; 
lean_del_object(v___x_46_);
v___x_68_ = l_Lean_Grind_CommRing_Expr_toPolyS(v_a_43_);
v___x_69_ = l_Lean_Grind_CommRing_Poly_pow(v___x_68_, v_k_44_);
lean_dec(v_k_44_);
return v___x_69_;
}
}
}
else
{
lean_object* v___x_70_; 
lean_del_object(v___x_46_);
lean_dec(v_k_44_);
lean_dec_ref(v_a_43_);
v___x_70_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPolyS___closed__1, &l_Lean_Grind_CommRing_Expr_toPolyS___closed__1_once, _init_l_Lean_Grind_CommRing_Expr_toPolyS___closed__1);
return v___x_70_;
}
}
}
default: 
{
lean_object* v___x_72_; 
lean_dec_ref(v_x_11_);
v___x_72_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPolyS___closed__3, &l_Lean_Grind_CommRing_Expr_toPolyS___closed__3_once, _init_l_Lean_Grind_CommRing_Expr_toPolyS___closed__3);
return v___x_72_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyS__nc(lean_object* v_x_73_){
_start:
{
switch(lean_obj_tag(v_x_73_))
{
case 0:
{
lean_object* v_k_74_; lean_object* v___x_76_; uint8_t v_isShared_77_; uint8_t v_isSharedCheck_83_; 
v_k_74_ = lean_ctor_get(v_x_73_, 0);
v_isSharedCheck_83_ = !lean_is_exclusive(v_x_73_);
if (v_isSharedCheck_83_ == 0)
{
v___x_76_ = v_x_73_;
v_isShared_77_ = v_isSharedCheck_83_;
goto v_resetjp_75_;
}
else
{
lean_inc(v_k_74_);
lean_dec(v_x_73_);
v___x_76_ = lean_box(0);
v_isShared_77_ = v_isSharedCheck_83_;
goto v_resetjp_75_;
}
v_resetjp_75_:
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_81_; 
v___x_78_ = lean_nat_abs(v_k_74_);
lean_dec(v_k_74_);
v___x_79_ = lean_nat_to_int(v___x_78_);
if (v_isShared_77_ == 0)
{
lean_ctor_set(v___x_76_, 0, v___x_79_);
v___x_81_ = v___x_76_;
goto v_reusejp_80_;
}
else
{
lean_object* v_reuseFailAlloc_82_; 
v_reuseFailAlloc_82_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_82_, 0, v___x_79_);
v___x_81_ = v_reuseFailAlloc_82_;
goto v_reusejp_80_;
}
v_reusejp_80_:
{
return v___x_81_;
}
}
}
case 1:
{
lean_object* v_k_84_; lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_92_; 
v_k_84_ = lean_ctor_get(v_x_73_, 0);
v_isSharedCheck_92_ = !lean_is_exclusive(v_x_73_);
if (v_isSharedCheck_92_ == 0)
{
v___x_86_ = v_x_73_;
v_isShared_87_ = v_isSharedCheck_92_;
goto v_resetjp_85_;
}
else
{
lean_inc(v_k_84_);
lean_dec(v_x_73_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_92_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
lean_object* v___x_88_; lean_object* v___x_90_; 
v___x_88_ = lean_nat_to_int(v_k_84_);
if (v_isShared_87_ == 0)
{
lean_ctor_set_tag(v___x_86_, 0);
lean_ctor_set(v___x_86_, 0, v___x_88_);
v___x_90_ = v___x_86_;
goto v_reusejp_89_;
}
else
{
lean_object* v_reuseFailAlloc_91_; 
v_reuseFailAlloc_91_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_91_, 0, v___x_88_);
v___x_90_ = v_reuseFailAlloc_91_;
goto v_reusejp_89_;
}
v_reusejp_89_:
{
return v___x_90_;
}
}
}
case 3:
{
lean_object* v_i_93_; lean_object* v___x_94_; 
v_i_93_ = lean_ctor_get(v_x_73_, 0);
lean_inc(v_i_93_);
lean_dec_ref_known(v_x_73_, 1);
v___x_94_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_93_);
return v___x_94_;
}
case 5:
{
lean_object* v_a_95_; lean_object* v_b_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v_a_95_ = lean_ctor_get(v_x_73_, 0);
lean_inc_ref(v_a_95_);
v_b_96_ = lean_ctor_get(v_x_73_, 1);
lean_inc_ref(v_b_96_);
lean_dec_ref_known(v_x_73_, 2);
v___x_97_ = l_Lean_Grind_CommRing_Expr_toPolyS__nc(v_a_95_);
v___x_98_ = l_Lean_Grind_CommRing_Expr_toPolyS__nc(v_b_96_);
v___x_99_ = l_Lean_Grind_CommRing_Poly_combine(v___x_97_, v___x_98_);
return v___x_99_;
}
case 7:
{
lean_object* v_a_100_; lean_object* v_b_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v_a_100_ = lean_ctor_get(v_x_73_, 0);
lean_inc_ref(v_a_100_);
v_b_101_ = lean_ctor_get(v_x_73_, 1);
lean_inc_ref(v_b_101_);
lean_dec_ref_known(v_x_73_, 2);
v___x_102_ = l_Lean_Grind_CommRing_Expr_toPolyS__nc(v_a_100_);
v___x_103_ = l_Lean_Grind_CommRing_Expr_toPolyS__nc(v_b_101_);
v___x_104_ = l_Lean_Grind_CommRing_Poly_mul__nc(v___x_102_, v___x_103_);
return v___x_104_;
}
case 8:
{
lean_object* v_a_105_; lean_object* v_k_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_133_; 
v_a_105_ = lean_ctor_get(v_x_73_, 0);
v_k_106_ = lean_ctor_get(v_x_73_, 1);
v_isSharedCheck_133_ = !lean_is_exclusive(v_x_73_);
if (v_isSharedCheck_133_ == 0)
{
v___x_108_ = v_x_73_;
v_isShared_109_ = v_isSharedCheck_133_;
goto v_resetjp_107_;
}
else
{
lean_inc(v_k_106_);
lean_inc(v_a_105_);
lean_dec(v_x_73_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_133_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
lean_object* v___x_110_; uint8_t v___x_111_; 
v___x_110_ = lean_unsigned_to_nat(0u);
v___x_111_ = lean_nat_dec_eq(v_k_106_, v___x_110_);
if (v___x_111_ == 0)
{
switch(lean_obj_tag(v_a_105_))
{
case 0:
{
lean_object* v_k_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_122_; 
lean_del_object(v___x_108_);
v_k_112_ = lean_ctor_get(v_a_105_, 0);
v_isSharedCheck_122_ = !lean_is_exclusive(v_a_105_);
if (v_isSharedCheck_122_ == 0)
{
v___x_114_ = v_a_105_;
v_isShared_115_ = v_isSharedCheck_122_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_k_112_);
lean_dec(v_a_105_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_122_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_120_; 
v___x_116_ = lean_nat_abs(v_k_112_);
lean_dec(v_k_112_);
v___x_117_ = lean_nat_to_int(v___x_116_);
v___x_118_ = l_Int_pow(v___x_117_, v_k_106_);
lean_dec(v_k_106_);
lean_dec(v___x_117_);
if (v_isShared_115_ == 0)
{
lean_ctor_set(v___x_114_, 0, v___x_118_);
v___x_120_ = v___x_114_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v___x_118_);
v___x_120_ = v_reuseFailAlloc_121_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
return v___x_120_;
}
}
}
case 3:
{
lean_object* v_i_123_; lean_object* v___x_125_; 
v_i_123_ = lean_ctor_get(v_a_105_, 0);
lean_inc(v_i_123_);
lean_dec_ref_known(v_a_105_, 1);
if (v_isShared_109_ == 0)
{
lean_ctor_set_tag(v___x_108_, 0);
lean_ctor_set(v___x_108_, 0, v_i_123_);
v___x_125_ = v___x_108_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v_i_123_);
lean_ctor_set(v_reuseFailAlloc_129_, 1, v_k_106_);
v___x_125_ = v_reuseFailAlloc_129_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_126_ = lean_box(0);
v___x_127_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_127_, 0, v___x_125_);
lean_ctor_set(v___x_127_, 1, v___x_126_);
v___x_128_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_127_);
return v___x_128_;
}
}
default: 
{
lean_object* v___x_130_; lean_object* v___x_131_; 
lean_del_object(v___x_108_);
v___x_130_ = l_Lean_Grind_CommRing_Expr_toPolyS__nc(v_a_105_);
v___x_131_ = l_Lean_Grind_CommRing_Poly_pow__nc(v___x_130_, v_k_106_);
lean_dec(v_k_106_);
return v___x_131_;
}
}
}
else
{
lean_object* v___x_132_; 
lean_del_object(v___x_108_);
lean_dec(v_k_106_);
lean_dec_ref(v_a_105_);
v___x_132_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPolyS___closed__1, &l_Lean_Grind_CommRing_Expr_toPolyS___closed__1_once, _init_l_Lean_Grind_CommRing_Expr_toPolyS___closed__1);
return v___x_132_;
}
}
}
default: 
{
lean_object* v___x_134_; 
lean_dec_ref(v_x_73_);
v___x_134_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPolyS___closed__3, &l_Lean_Grind_CommRing_Expr_toPolyS___closed__3_once, _init_l_Lean_Grind_CommRing_Expr_toPolyS___closed__3);
return v___x_134_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Expr_toPolyS_match__4_splitter___redArg(lean_object* v_x_135_, lean_object* v_h__1_136_, lean_object* v_h__2_137_, lean_object* v_h__3_138_, lean_object* v_h__4_139_, lean_object* v_h__5_140_, lean_object* v_h__6_141_, lean_object* v_h__7_142_, lean_object* v_h__8_143_, lean_object* v_h__9_144_){
_start:
{
switch(lean_obj_tag(v_x_135_))
{
case 0:
{
lean_object* v_k_145_; lean_object* v___x_146_; 
lean_dec(v_h__9_144_);
lean_dec(v_h__8_143_);
lean_dec(v_h__7_142_);
lean_dec(v_h__6_141_);
lean_dec(v_h__5_140_);
lean_dec(v_h__4_139_);
lean_dec(v_h__3_138_);
lean_dec(v_h__2_137_);
v_k_145_ = lean_ctor_get(v_x_135_, 0);
lean_inc(v_k_145_);
lean_dec_ref_known(v_x_135_, 1);
v___x_146_ = lean_apply_1(v_h__1_136_, v_k_145_);
return v___x_146_;
}
case 1:
{
lean_object* v_k_147_; lean_object* v___x_148_; 
lean_dec(v_h__9_144_);
lean_dec(v_h__8_143_);
lean_dec(v_h__7_142_);
lean_dec(v_h__5_140_);
lean_dec(v_h__4_139_);
lean_dec(v_h__3_138_);
lean_dec(v_h__2_137_);
lean_dec(v_h__1_136_);
v_k_147_ = lean_ctor_get(v_x_135_, 0);
lean_inc(v_k_147_);
lean_dec_ref_known(v_x_135_, 1);
v___x_148_ = lean_apply_1(v_h__6_141_, v_k_147_);
return v___x_148_;
}
case 2:
{
lean_object* v_k_149_; lean_object* v___x_150_; 
lean_dec(v_h__8_143_);
lean_dec(v_h__7_142_);
lean_dec(v_h__6_141_);
lean_dec(v_h__5_140_);
lean_dec(v_h__4_139_);
lean_dec(v_h__3_138_);
lean_dec(v_h__2_137_);
lean_dec(v_h__1_136_);
v_k_149_ = lean_ctor_get(v_x_135_, 0);
lean_inc(v_k_149_);
lean_dec_ref_known(v_x_135_, 1);
v___x_150_ = lean_apply_1(v_h__9_144_, v_k_149_);
return v___x_150_;
}
case 3:
{
lean_object* v_i_151_; lean_object* v___x_152_; 
lean_dec(v_h__9_144_);
lean_dec(v_h__8_143_);
lean_dec(v_h__7_142_);
lean_dec(v_h__6_141_);
lean_dec(v_h__5_140_);
lean_dec(v_h__4_139_);
lean_dec(v_h__3_138_);
lean_dec(v_h__1_136_);
v_i_151_ = lean_ctor_get(v_x_135_, 0);
lean_inc(v_i_151_);
lean_dec_ref_known(v_x_135_, 1);
v___x_152_ = lean_apply_1(v_h__2_137_, v_i_151_);
return v___x_152_;
}
case 4:
{
lean_object* v_a_153_; lean_object* v___x_154_; 
lean_dec(v_h__9_144_);
lean_dec(v_h__7_142_);
lean_dec(v_h__6_141_);
lean_dec(v_h__5_140_);
lean_dec(v_h__4_139_);
lean_dec(v_h__3_138_);
lean_dec(v_h__2_137_);
lean_dec(v_h__1_136_);
v_a_153_ = lean_ctor_get(v_x_135_, 0);
lean_inc_ref(v_a_153_);
lean_dec_ref_known(v_x_135_, 1);
v___x_154_ = lean_apply_1(v_h__8_143_, v_a_153_);
return v___x_154_;
}
case 5:
{
lean_object* v_a_155_; lean_object* v_b_156_; lean_object* v___x_157_; 
lean_dec(v_h__9_144_);
lean_dec(v_h__8_143_);
lean_dec(v_h__7_142_);
lean_dec(v_h__6_141_);
lean_dec(v_h__5_140_);
lean_dec(v_h__4_139_);
lean_dec(v_h__2_137_);
lean_dec(v_h__1_136_);
v_a_155_ = lean_ctor_get(v_x_135_, 0);
lean_inc_ref(v_a_155_);
v_b_156_ = lean_ctor_get(v_x_135_, 1);
lean_inc_ref(v_b_156_);
lean_dec_ref_known(v_x_135_, 2);
v___x_157_ = lean_apply_2(v_h__3_138_, v_a_155_, v_b_156_);
return v___x_157_;
}
case 6:
{
lean_object* v_a_158_; lean_object* v_b_159_; lean_object* v___x_160_; 
lean_dec(v_h__9_144_);
lean_dec(v_h__8_143_);
lean_dec(v_h__6_141_);
lean_dec(v_h__5_140_);
lean_dec(v_h__4_139_);
lean_dec(v_h__3_138_);
lean_dec(v_h__2_137_);
lean_dec(v_h__1_136_);
v_a_158_ = lean_ctor_get(v_x_135_, 0);
lean_inc_ref(v_a_158_);
v_b_159_ = lean_ctor_get(v_x_135_, 1);
lean_inc_ref(v_b_159_);
lean_dec_ref_known(v_x_135_, 2);
v___x_160_ = lean_apply_2(v_h__7_142_, v_a_158_, v_b_159_);
return v___x_160_;
}
case 7:
{
lean_object* v_a_161_; lean_object* v_b_162_; lean_object* v___x_163_; 
lean_dec(v_h__9_144_);
lean_dec(v_h__8_143_);
lean_dec(v_h__7_142_);
lean_dec(v_h__6_141_);
lean_dec(v_h__5_140_);
lean_dec(v_h__3_138_);
lean_dec(v_h__2_137_);
lean_dec(v_h__1_136_);
v_a_161_ = lean_ctor_get(v_x_135_, 0);
lean_inc_ref(v_a_161_);
v_b_162_ = lean_ctor_get(v_x_135_, 1);
lean_inc_ref(v_b_162_);
lean_dec_ref_known(v_x_135_, 2);
v___x_163_ = lean_apply_2(v_h__4_139_, v_a_161_, v_b_162_);
return v___x_163_;
}
default: 
{
lean_object* v_a_164_; lean_object* v_k_165_; lean_object* v___x_166_; 
lean_dec(v_h__9_144_);
lean_dec(v_h__8_143_);
lean_dec(v_h__7_142_);
lean_dec(v_h__6_141_);
lean_dec(v_h__4_139_);
lean_dec(v_h__3_138_);
lean_dec(v_h__2_137_);
lean_dec(v_h__1_136_);
v_a_164_ = lean_ctor_get(v_x_135_, 0);
lean_inc_ref(v_a_164_);
v_k_165_ = lean_ctor_get(v_x_135_, 1);
lean_inc(v_k_165_);
lean_dec_ref_known(v_x_135_, 2);
v___x_166_ = lean_apply_2(v_h__5_140_, v_a_164_, v_k_165_);
return v___x_166_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Expr_toPolyS_match__4_splitter(lean_object* v_motive_167_, lean_object* v_x_168_, lean_object* v_h__1_169_, lean_object* v_h__2_170_, lean_object* v_h__3_171_, lean_object* v_h__4_172_, lean_object* v_h__5_173_, lean_object* v_h__6_174_, lean_object* v_h__7_175_, lean_object* v_h__8_176_, lean_object* v_h__9_177_){
_start:
{
switch(lean_obj_tag(v_x_168_))
{
case 0:
{
lean_object* v_k_178_; lean_object* v___x_179_; 
lean_dec(v_h__9_177_);
lean_dec(v_h__8_176_);
lean_dec(v_h__7_175_);
lean_dec(v_h__6_174_);
lean_dec(v_h__5_173_);
lean_dec(v_h__4_172_);
lean_dec(v_h__3_171_);
lean_dec(v_h__2_170_);
v_k_178_ = lean_ctor_get(v_x_168_, 0);
lean_inc(v_k_178_);
lean_dec_ref_known(v_x_168_, 1);
v___x_179_ = lean_apply_1(v_h__1_169_, v_k_178_);
return v___x_179_;
}
case 1:
{
lean_object* v_k_180_; lean_object* v___x_181_; 
lean_dec(v_h__9_177_);
lean_dec(v_h__8_176_);
lean_dec(v_h__7_175_);
lean_dec(v_h__5_173_);
lean_dec(v_h__4_172_);
lean_dec(v_h__3_171_);
lean_dec(v_h__2_170_);
lean_dec(v_h__1_169_);
v_k_180_ = lean_ctor_get(v_x_168_, 0);
lean_inc(v_k_180_);
lean_dec_ref_known(v_x_168_, 1);
v___x_181_ = lean_apply_1(v_h__6_174_, v_k_180_);
return v___x_181_;
}
case 2:
{
lean_object* v_k_182_; lean_object* v___x_183_; 
lean_dec(v_h__8_176_);
lean_dec(v_h__7_175_);
lean_dec(v_h__6_174_);
lean_dec(v_h__5_173_);
lean_dec(v_h__4_172_);
lean_dec(v_h__3_171_);
lean_dec(v_h__2_170_);
lean_dec(v_h__1_169_);
v_k_182_ = lean_ctor_get(v_x_168_, 0);
lean_inc(v_k_182_);
lean_dec_ref_known(v_x_168_, 1);
v___x_183_ = lean_apply_1(v_h__9_177_, v_k_182_);
return v___x_183_;
}
case 3:
{
lean_object* v_i_184_; lean_object* v___x_185_; 
lean_dec(v_h__9_177_);
lean_dec(v_h__8_176_);
lean_dec(v_h__7_175_);
lean_dec(v_h__6_174_);
lean_dec(v_h__5_173_);
lean_dec(v_h__4_172_);
lean_dec(v_h__3_171_);
lean_dec(v_h__1_169_);
v_i_184_ = lean_ctor_get(v_x_168_, 0);
lean_inc(v_i_184_);
lean_dec_ref_known(v_x_168_, 1);
v___x_185_ = lean_apply_1(v_h__2_170_, v_i_184_);
return v___x_185_;
}
case 4:
{
lean_object* v_a_186_; lean_object* v___x_187_; 
lean_dec(v_h__9_177_);
lean_dec(v_h__7_175_);
lean_dec(v_h__6_174_);
lean_dec(v_h__5_173_);
lean_dec(v_h__4_172_);
lean_dec(v_h__3_171_);
lean_dec(v_h__2_170_);
lean_dec(v_h__1_169_);
v_a_186_ = lean_ctor_get(v_x_168_, 0);
lean_inc_ref(v_a_186_);
lean_dec_ref_known(v_x_168_, 1);
v___x_187_ = lean_apply_1(v_h__8_176_, v_a_186_);
return v___x_187_;
}
case 5:
{
lean_object* v_a_188_; lean_object* v_b_189_; lean_object* v___x_190_; 
lean_dec(v_h__9_177_);
lean_dec(v_h__8_176_);
lean_dec(v_h__7_175_);
lean_dec(v_h__6_174_);
lean_dec(v_h__5_173_);
lean_dec(v_h__4_172_);
lean_dec(v_h__2_170_);
lean_dec(v_h__1_169_);
v_a_188_ = lean_ctor_get(v_x_168_, 0);
lean_inc_ref(v_a_188_);
v_b_189_ = lean_ctor_get(v_x_168_, 1);
lean_inc_ref(v_b_189_);
lean_dec_ref_known(v_x_168_, 2);
v___x_190_ = lean_apply_2(v_h__3_171_, v_a_188_, v_b_189_);
return v___x_190_;
}
case 6:
{
lean_object* v_a_191_; lean_object* v_b_192_; lean_object* v___x_193_; 
lean_dec(v_h__9_177_);
lean_dec(v_h__8_176_);
lean_dec(v_h__6_174_);
lean_dec(v_h__5_173_);
lean_dec(v_h__4_172_);
lean_dec(v_h__3_171_);
lean_dec(v_h__2_170_);
lean_dec(v_h__1_169_);
v_a_191_ = lean_ctor_get(v_x_168_, 0);
lean_inc_ref(v_a_191_);
v_b_192_ = lean_ctor_get(v_x_168_, 1);
lean_inc_ref(v_b_192_);
lean_dec_ref_known(v_x_168_, 2);
v___x_193_ = lean_apply_2(v_h__7_175_, v_a_191_, v_b_192_);
return v___x_193_;
}
case 7:
{
lean_object* v_a_194_; lean_object* v_b_195_; lean_object* v___x_196_; 
lean_dec(v_h__9_177_);
lean_dec(v_h__8_176_);
lean_dec(v_h__7_175_);
lean_dec(v_h__6_174_);
lean_dec(v_h__5_173_);
lean_dec(v_h__3_171_);
lean_dec(v_h__2_170_);
lean_dec(v_h__1_169_);
v_a_194_ = lean_ctor_get(v_x_168_, 0);
lean_inc_ref(v_a_194_);
v_b_195_ = lean_ctor_get(v_x_168_, 1);
lean_inc_ref(v_b_195_);
lean_dec_ref_known(v_x_168_, 2);
v___x_196_ = lean_apply_2(v_h__4_172_, v_a_194_, v_b_195_);
return v___x_196_;
}
default: 
{
lean_object* v_a_197_; lean_object* v_k_198_; lean_object* v___x_199_; 
lean_dec(v_h__9_177_);
lean_dec(v_h__8_176_);
lean_dec(v_h__7_175_);
lean_dec(v_h__6_174_);
lean_dec(v_h__4_172_);
lean_dec(v_h__3_171_);
lean_dec(v_h__2_170_);
lean_dec(v_h__1_169_);
v_a_197_ = lean_ctor_get(v_x_168_, 0);
lean_inc_ref(v_a_197_);
v_k_198_ = lean_ctor_get(v_x_168_, 1);
lean_inc(v_k_198_);
lean_dec_ref_known(v_x_168_, 2);
v___x_199_ = lean_apply_2(v_h__5_173_, v_a_197_, v_k_198_);
return v___x_199_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Expr_toPolyS_match__1_splitter___redArg(lean_object* v_a_200_, lean_object* v_h__1_201_, lean_object* v_h__2_202_, lean_object* v_h__3_203_){
_start:
{
switch(lean_obj_tag(v_a_200_))
{
case 0:
{
lean_object* v_k_204_; lean_object* v___x_205_; 
lean_dec(v_h__3_203_);
lean_dec(v_h__2_202_);
v_k_204_ = lean_ctor_get(v_a_200_, 0);
lean_inc(v_k_204_);
lean_dec_ref_known(v_a_200_, 1);
v___x_205_ = lean_apply_1(v_h__1_201_, v_k_204_);
return v___x_205_;
}
case 3:
{
lean_object* v_i_206_; lean_object* v___x_207_; 
lean_dec(v_h__3_203_);
lean_dec(v_h__1_201_);
v_i_206_ = lean_ctor_get(v_a_200_, 0);
lean_inc(v_i_206_);
lean_dec_ref_known(v_a_200_, 1);
v___x_207_ = lean_apply_1(v_h__2_202_, v_i_206_);
return v___x_207_;
}
default: 
{
lean_object* v___x_208_; 
lean_dec(v_h__2_202_);
lean_dec(v_h__1_201_);
v___x_208_ = lean_apply_3(v_h__3_203_, v_a_200_, lean_box(0), lean_box(0));
return v___x_208_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Expr_toPolyS_match__1_splitter(lean_object* v_motive_209_, lean_object* v_a_210_, lean_object* v_h__1_211_, lean_object* v_h__2_212_, lean_object* v_h__3_213_){
_start:
{
switch(lean_obj_tag(v_a_210_))
{
case 0:
{
lean_object* v_k_214_; lean_object* v___x_215_; 
lean_dec(v_h__3_213_);
lean_dec(v_h__2_212_);
v_k_214_ = lean_ctor_get(v_a_210_, 0);
lean_inc(v_k_214_);
lean_dec_ref_known(v_a_210_, 1);
v___x_215_ = lean_apply_1(v_h__1_211_, v_k_214_);
return v___x_215_;
}
case 3:
{
lean_object* v_i_216_; lean_object* v___x_217_; 
lean_dec(v_h__3_213_);
lean_dec(v_h__1_211_);
v_i_216_ = lean_ctor_get(v_a_210_, 0);
lean_inc(v_i_216_);
lean_dec_ref_known(v_a_210_, 1);
v___x_217_ = lean_apply_1(v_h__2_212_, v_i_216_);
return v___x_217_;
}
default: 
{
lean_object* v___x_218_; 
lean_dec(v_h__2_212_);
lean_dec(v_h__1_211_);
v___x_218_ = lean_apply_3(v_h__3_213_, v_a_210_, lean_box(0), lean_box(0));
return v___x_218_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteSInt___redArg(lean_object* v_inst_219_, lean_object* v_k_220_){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; uint8_t v___x_223_; 
v___x_221_ = lean_unsigned_to_nat(0u);
v___x_222_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPolyS___closed__2, &l_Lean_Grind_CommRing_Expr_toPolyS___closed__2_once, _init_l_Lean_Grind_CommRing_Expr_toPolyS___closed__2);
v___x_223_ = lean_int_dec_lt(v_k_220_, v___x_222_);
if (v___x_223_ == 0)
{
lean_object* v_ofNat_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v_ofNat_224_ = lean_ctor_get(v_inst_219_, 3);
lean_inc(v_ofNat_224_);
lean_dec_ref(v_inst_219_);
v___x_225_ = lean_nat_abs(v_k_220_);
v___x_226_ = lean_apply_1(v_ofNat_224_, v___x_225_);
return v___x_226_;
}
else
{
lean_object* v_ofNat_227_; lean_object* v___x_228_; 
v_ofNat_227_ = lean_ctor_get(v_inst_219_, 3);
lean_inc(v_ofNat_227_);
lean_dec_ref(v_inst_219_);
v___x_228_ = lean_apply_1(v_ofNat_227_, v___x_221_);
return v___x_228_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteSInt___redArg___boxed(lean_object* v_inst_229_, lean_object* v_k_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Lean_Grind_CommRing_denoteSInt___redArg(v_inst_229_, v_k_230_);
lean_dec(v_k_230_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteSInt(lean_object* v_00_u03b1_232_, lean_object* v_inst_233_, lean_object* v_k_234_){
_start:
{
lean_object* v___x_235_; 
v___x_235_ = l_Lean_Grind_CommRing_denoteSInt___redArg(v_inst_233_, v_k_234_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteSInt___boxed(lean_object* v_00_u03b1_236_, lean_object* v_inst_237_, lean_object* v_k_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Lean_Grind_CommRing_denoteSInt(v_00_u03b1_236_, v_inst_237_, v_k_238_);
lean_dec(v_k_238_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteS___redArg(lean_object* v_inst_240_, lean_object* v_ctx_241_, lean_object* v_p_242_){
_start:
{
if (lean_obj_tag(v_p_242_) == 0)
{
lean_object* v_k_243_; lean_object* v___x_244_; 
v_k_243_ = lean_ctor_get(v_p_242_, 0);
lean_inc(v_k_243_);
lean_dec_ref_known(v_p_242_, 1);
v___x_244_ = l_Lean_Grind_CommRing_denoteSInt___redArg(v_inst_240_, v_k_243_);
lean_dec(v_k_243_);
return v___x_244_;
}
else
{
lean_object* v_toAdd_245_; lean_object* v_toMul_246_; lean_object* v_k_247_; lean_object* v_v_248_; lean_object* v_p_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v_toAdd_245_ = lean_ctor_get(v_inst_240_, 0);
lean_inc(v_toAdd_245_);
v_toMul_246_ = lean_ctor_get(v_inst_240_, 1);
v_k_247_ = lean_ctor_get(v_p_242_, 0);
lean_inc(v_k_247_);
v_v_248_ = lean_ctor_get(v_p_242_, 1);
lean_inc(v_v_248_);
v_p_249_ = lean_ctor_get(v_p_242_, 2);
lean_inc_ref(v_p_249_);
lean_dec_ref_known(v_p_242_, 3);
lean_inc_ref_n(v_inst_240_, 2);
v___x_250_ = l_Lean_Grind_CommRing_denoteSInt___redArg(v_inst_240_, v_k_247_);
lean_dec(v_k_247_);
v___x_251_ = l_Lean_Grind_CommRing_Mon_denote___redArg(v_inst_240_, v_ctx_241_, v_v_248_);
lean_inc(v_toMul_246_);
v___x_252_ = lean_apply_2(v_toMul_246_, v___x_250_, v___x_251_);
v___x_253_ = l_Lean_Grind_CommRing_Poly_denoteS___redArg(v_inst_240_, v_ctx_241_, v_p_249_);
v___x_254_ = lean_apply_2(v_toAdd_245_, v___x_252_, v___x_253_);
return v___x_254_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteS___redArg___boxed(lean_object* v_inst_255_, lean_object* v_ctx_256_, lean_object* v_p_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Lean_Grind_CommRing_Poly_denoteS___redArg(v_inst_255_, v_ctx_256_, v_p_257_);
lean_dec_ref(v_ctx_256_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteS(lean_object* v_00_u03b1_259_, lean_object* v_inst_260_, lean_object* v_ctx_261_, lean_object* v_p_262_){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = l_Lean_Grind_CommRing_Poly_denoteS___redArg(v_inst_260_, v_ctx_261_, v_p_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteS___boxed(lean_object* v_00_u03b1_264_, lean_object* v_inst_265_, lean_object* v_ctx_266_, lean_object* v_p_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_Lean_Grind_CommRing_Poly_denoteS(v_00_u03b1_264_, v_inst_265_, v_ctx_266_, v_p_267_);
lean_dec_ref(v_ctx_266_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_denoteS_match__1_splitter___redArg(lean_object* v_p_269_, lean_object* v_h__1_270_, lean_object* v_h__2_271_){
_start:
{
if (lean_obj_tag(v_p_269_) == 0)
{
lean_object* v_k_272_; lean_object* v___x_273_; 
lean_dec(v_h__2_271_);
v_k_272_ = lean_ctor_get(v_p_269_, 0);
lean_inc(v_k_272_);
lean_dec_ref_known(v_p_269_, 1);
v___x_273_ = lean_apply_1(v_h__1_270_, v_k_272_);
return v___x_273_;
}
else
{
lean_object* v_k_274_; lean_object* v_v_275_; lean_object* v_p_276_; lean_object* v___x_277_; 
lean_dec(v_h__1_270_);
v_k_274_ = lean_ctor_get(v_p_269_, 0);
lean_inc(v_k_274_);
v_v_275_ = lean_ctor_get(v_p_269_, 1);
lean_inc(v_v_275_);
v_p_276_ = lean_ctor_get(v_p_269_, 2);
lean_inc_ref(v_p_276_);
lean_dec_ref_known(v_p_269_, 3);
v___x_277_ = lean_apply_3(v_h__2_271_, v_k_274_, v_v_275_, v_p_276_);
return v___x_277_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_denoteS_match__1_splitter(lean_object* v_motive_278_, lean_object* v_p_279_, lean_object* v_h__1_280_, lean_object* v_h__2_281_){
_start:
{
if (lean_obj_tag(v_p_279_) == 0)
{
lean_object* v_k_282_; lean_object* v___x_283_; 
lean_dec(v_h__2_281_);
v_k_282_ = lean_ctor_get(v_p_279_, 0);
lean_inc(v_k_282_);
lean_dec_ref_known(v_p_279_, 1);
v___x_283_ = lean_apply_1(v_h__1_280_, v_k_282_);
return v___x_283_;
}
else
{
lean_object* v_k_284_; lean_object* v_v_285_; lean_object* v_p_286_; lean_object* v___x_287_; 
lean_dec(v_h__1_280_);
v_k_284_ = lean_ctor_get(v_p_279_, 0);
lean_inc(v_k_284_);
v_v_285_ = lean_ctor_get(v_p_279_, 1);
lean_inc(v_v_285_);
v_p_286_ = lean_ctor_get(v_p_279_, 2);
lean_inc_ref(v_p_286_);
lean_dec_ref_known(v_p_279_, 3);
v___x_287_ = lean_apply_3(v_h__2_281_, v_k_284_, v_v_285_, v_p_286_);
return v___x_287_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_denote_match__1_splitter___redArg(lean_object* v_p_288_, lean_object* v_h__1_289_, lean_object* v_h__2_290_){
_start:
{
if (lean_obj_tag(v_p_288_) == 0)
{
lean_object* v_k_291_; lean_object* v___x_292_; 
lean_dec(v_h__2_290_);
v_k_291_ = lean_ctor_get(v_p_288_, 0);
lean_inc(v_k_291_);
lean_dec_ref_known(v_p_288_, 1);
v___x_292_ = lean_apply_1(v_h__1_289_, v_k_291_);
return v___x_292_;
}
else
{
lean_object* v_k_293_; lean_object* v_v_294_; lean_object* v_p_295_; lean_object* v___x_296_; 
lean_dec(v_h__1_289_);
v_k_293_ = lean_ctor_get(v_p_288_, 0);
lean_inc(v_k_293_);
v_v_294_ = lean_ctor_get(v_p_288_, 1);
lean_inc(v_v_294_);
v_p_295_ = lean_ctor_get(v_p_288_, 2);
lean_inc_ref(v_p_295_);
lean_dec_ref_known(v_p_288_, 3);
v___x_296_ = lean_apply_3(v_h__2_290_, v_k_293_, v_v_294_, v_p_295_);
return v___x_296_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_denote_match__1_splitter(lean_object* v_motive_297_, lean_object* v_p_298_, lean_object* v_h__1_299_, lean_object* v_h__2_300_){
_start:
{
if (lean_obj_tag(v_p_298_) == 0)
{
lean_object* v_k_301_; lean_object* v___x_302_; 
lean_dec(v_h__2_300_);
v_k_301_ = lean_ctor_get(v_p_298_, 0);
lean_inc(v_k_301_);
lean_dec_ref_known(v_p_298_, 1);
v___x_302_ = lean_apply_1(v_h__1_299_, v_k_301_);
return v___x_302_;
}
else
{
lean_object* v_k_303_; lean_object* v_v_304_; lean_object* v_p_305_; lean_object* v___x_306_; 
lean_dec(v_h__1_299_);
v_k_303_ = lean_ctor_get(v_p_298_, 0);
lean_inc(v_k_303_);
v_v_304_ = lean_ctor_get(v_p_298_, 1);
lean_inc(v_v_304_);
v_p_305_ = lean_ctor_get(v_p_298_, 2);
lean_inc_ref(v_p_305_);
lean_dec_ref_known(v_p_298_, 3);
v___x_306_ = lean_apply_3(v_h__2_300_, v_k_303_, v_v_304_, v_p_305_);
return v___x_306_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Mon_denote_match__1_splitter___redArg(lean_object* v_x_307_, lean_object* v_h__1_308_, lean_object* v_h__2_309_){
_start:
{
if (lean_obj_tag(v_x_307_) == 0)
{
lean_object* v___x_310_; lean_object* v___x_311_; 
lean_dec(v_h__2_309_);
v___x_310_ = lean_box(0);
v___x_311_ = lean_apply_1(v_h__1_308_, v___x_310_);
return v___x_311_;
}
else
{
lean_object* v_p_312_; lean_object* v_m_313_; lean_object* v___x_314_; 
lean_dec(v_h__1_308_);
v_p_312_ = lean_ctor_get(v_x_307_, 0);
lean_inc_ref(v_p_312_);
v_m_313_ = lean_ctor_get(v_x_307_, 1);
lean_inc(v_m_313_);
lean_dec_ref_known(v_x_307_, 2);
v___x_314_ = lean_apply_2(v_h__2_309_, v_p_312_, v_m_313_);
return v___x_314_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Mon_denote_match__1_splitter(lean_object* v_motive_315_, lean_object* v_x_316_, lean_object* v_h__1_317_, lean_object* v_h__2_318_){
_start:
{
if (lean_obj_tag(v_x_316_) == 0)
{
lean_object* v___x_319_; lean_object* v___x_320_; 
lean_dec(v_h__2_318_);
v___x_319_ = lean_box(0);
v___x_320_ = lean_apply_1(v_h__1_317_, v___x_319_);
return v___x_320_;
}
else
{
lean_object* v_p_321_; lean_object* v_m_322_; lean_object* v___x_323_; 
lean_dec(v_h__1_317_);
v_p_321_ = lean_ctor_get(v_x_316_, 0);
lean_inc_ref(v_p_321_);
v_m_322_ = lean_ctor_get(v_x_316_, 1);
lean_inc(v_m_322_);
lean_dec_ref_known(v_x_316_, 2);
v___x_323_ = lean_apply_2(v_h__2_318_, v_p_321_, v_m_322_);
return v___x_323_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter___redArg(uint8_t v_x_324_, lean_object* v_h__1_325_, lean_object* v_h__2_326_, lean_object* v_h__3_327_){
_start:
{
switch(v_x_324_)
{
case 0:
{
lean_object* v___x_328_; lean_object* v___x_329_; 
lean_dec(v_h__2_326_);
lean_dec(v_h__1_325_);
v___x_328_ = lean_box(0);
v___x_329_ = lean_apply_1(v_h__3_327_, v___x_328_);
return v___x_329_;
}
case 1:
{
lean_object* v___x_330_; lean_object* v___x_331_; 
lean_dec(v_h__3_327_);
lean_dec(v_h__2_326_);
v___x_330_ = lean_box(0);
v___x_331_ = lean_apply_1(v_h__1_325_, v___x_330_);
return v___x_331_;
}
default: 
{
lean_object* v___x_332_; lean_object* v___x_333_; 
lean_dec(v_h__3_327_);
lean_dec(v_h__1_325_);
v___x_332_ = lean_box(0);
v___x_333_ = lean_apply_1(v_h__2_326_, v___x_332_);
return v___x_333_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter___redArg___boxed(lean_object* v_x_334_, lean_object* v_h__1_335_, lean_object* v_h__2_336_, lean_object* v_h__3_337_){
_start:
{
uint8_t v_x_33__boxed_338_; lean_object* v_res_339_; 
v_x_33__boxed_338_ = lean_unbox(v_x_334_);
v_res_339_ = l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter___redArg(v_x_33__boxed_338_, v_h__1_335_, v_h__2_336_, v_h__3_337_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter(lean_object* v_motive_340_, uint8_t v_x_341_, lean_object* v_h__1_342_, lean_object* v_h__2_343_, lean_object* v_h__3_344_){
_start:
{
switch(v_x_341_)
{
case 0:
{
lean_object* v___x_345_; lean_object* v___x_346_; 
lean_dec(v_h__2_343_);
lean_dec(v_h__1_342_);
v___x_345_ = lean_box(0);
v___x_346_ = lean_apply_1(v_h__3_344_, v___x_345_);
return v___x_346_;
}
case 1:
{
lean_object* v___x_347_; lean_object* v___x_348_; 
lean_dec(v_h__3_344_);
lean_dec(v_h__2_343_);
v___x_347_ = lean_box(0);
v___x_348_ = lean_apply_1(v_h__1_342_, v___x_347_);
return v___x_348_;
}
default: 
{
lean_object* v___x_349_; lean_object* v___x_350_; 
lean_dec(v_h__3_344_);
lean_dec(v_h__1_342_);
v___x_349_ = lean_box(0);
v___x_350_ = lean_apply_1(v_h__2_343_, v___x_349_);
return v___x_350_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter___boxed(lean_object* v_motive_351_, lean_object* v_x_352_, lean_object* v_h__1_353_, lean_object* v_h__2_354_, lean_object* v_h__3_355_){
_start:
{
uint8_t v_x_48__boxed_356_; lean_object* v_res_357_; 
v_x_48__boxed_356_ = lean_unbox(v_x_352_);
v_res_357_ = l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter(v_motive_351_, v_x_48__boxed_356_, v_h__1_353_, v_h__2_354_, v_h__3_355_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter___redArg(lean_object* v_fuel_358_, lean_object* v_h__1_359_, lean_object* v_h__2_360_){
_start:
{
lean_object* v_zero_361_; uint8_t v_isZero_362_; 
v_zero_361_ = lean_unsigned_to_nat(0u);
v_isZero_362_ = lean_nat_dec_eq(v_fuel_358_, v_zero_361_);
if (v_isZero_362_ == 1)
{
lean_object* v___x_363_; lean_object* v___x_364_; 
lean_dec(v_h__2_360_);
v___x_363_ = lean_box(0);
v___x_364_ = lean_apply_1(v_h__1_359_, v___x_363_);
return v___x_364_;
}
else
{
lean_object* v_one_365_; lean_object* v_n_366_; lean_object* v___x_367_; 
lean_dec(v_h__1_359_);
v_one_365_ = lean_unsigned_to_nat(1u);
v_n_366_ = lean_nat_sub(v_fuel_358_, v_one_365_);
v___x_367_ = lean_apply_1(v_h__2_360_, v_n_366_);
return v___x_367_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter___redArg___boxed(lean_object* v_fuel_368_, lean_object* v_h__1_369_, lean_object* v_h__2_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter___redArg(v_fuel_368_, v_h__1_369_, v_h__2_370_);
lean_dec(v_fuel_368_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter(lean_object* v_motive_372_, lean_object* v_fuel_373_, lean_object* v_h__1_374_, lean_object* v_h__2_375_){
_start:
{
lean_object* v_zero_376_; uint8_t v_isZero_377_; 
v_zero_376_ = lean_unsigned_to_nat(0u);
v_isZero_377_ = lean_nat_dec_eq(v_fuel_373_, v_zero_376_);
if (v_isZero_377_ == 1)
{
lean_object* v___x_378_; lean_object* v___x_379_; 
lean_dec(v_h__2_375_);
v___x_378_ = lean_box(0);
v___x_379_ = lean_apply_1(v_h__1_374_, v___x_378_);
return v___x_379_;
}
else
{
lean_object* v_one_380_; lean_object* v_n_381_; lean_object* v___x_382_; 
lean_dec(v_h__1_374_);
v_one_380_ = lean_unsigned_to_nat(1u);
v_n_381_ = lean_nat_sub(v_fuel_373_, v_one_380_);
v___x_382_ = lean_apply_1(v_h__2_375_, v_n_381_);
return v___x_382_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter___boxed(lean_object* v_motive_383_, lean_object* v_fuel_384_, lean_object* v_h__1_385_, lean_object* v_h__2_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter(v_motive_383_, v_fuel_384_, v_h__1_385_, v_h__2_386_);
lean_dec(v_fuel_384_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_combine_go_match__1_splitter___redArg(lean_object* v_p_u2081_388_, lean_object* v_p_u2082_389_, lean_object* v_h__1_390_, lean_object* v_h__2_391_, lean_object* v_h__3_392_, lean_object* v_h__4_393_){
_start:
{
if (lean_obj_tag(v_p_u2081_388_) == 0)
{
lean_dec(v_h__4_393_);
lean_dec(v_h__3_392_);
if (lean_obj_tag(v_p_u2082_389_) == 0)
{
lean_object* v_k_394_; lean_object* v_k_395_; lean_object* v___x_396_; 
lean_dec(v_h__2_391_);
v_k_394_ = lean_ctor_get(v_p_u2081_388_, 0);
lean_inc(v_k_394_);
lean_dec_ref_known(v_p_u2081_388_, 1);
v_k_395_ = lean_ctor_get(v_p_u2082_389_, 0);
lean_inc(v_k_395_);
lean_dec_ref_known(v_p_u2082_389_, 1);
v___x_396_ = lean_apply_2(v_h__1_390_, v_k_394_, v_k_395_);
return v___x_396_;
}
else
{
lean_object* v_k_397_; lean_object* v_k_398_; lean_object* v_v_399_; lean_object* v_p_400_; lean_object* v___x_401_; 
lean_dec(v_h__1_390_);
v_k_397_ = lean_ctor_get(v_p_u2081_388_, 0);
lean_inc(v_k_397_);
lean_dec_ref_known(v_p_u2081_388_, 1);
v_k_398_ = lean_ctor_get(v_p_u2082_389_, 0);
lean_inc(v_k_398_);
v_v_399_ = lean_ctor_get(v_p_u2082_389_, 1);
lean_inc(v_v_399_);
v_p_400_ = lean_ctor_get(v_p_u2082_389_, 2);
lean_inc_ref(v_p_400_);
lean_dec_ref_known(v_p_u2082_389_, 3);
v___x_401_ = lean_apply_4(v_h__2_391_, v_k_397_, v_k_398_, v_v_399_, v_p_400_);
return v___x_401_;
}
}
else
{
lean_dec(v_h__2_391_);
lean_dec(v_h__1_390_);
if (lean_obj_tag(v_p_u2082_389_) == 0)
{
lean_object* v_k_402_; lean_object* v_v_403_; lean_object* v_p_404_; lean_object* v_k_405_; lean_object* v___x_406_; 
lean_dec(v_h__4_393_);
v_k_402_ = lean_ctor_get(v_p_u2081_388_, 0);
lean_inc(v_k_402_);
v_v_403_ = lean_ctor_get(v_p_u2081_388_, 1);
lean_inc(v_v_403_);
v_p_404_ = lean_ctor_get(v_p_u2081_388_, 2);
lean_inc_ref(v_p_404_);
lean_dec_ref_known(v_p_u2081_388_, 3);
v_k_405_ = lean_ctor_get(v_p_u2082_389_, 0);
lean_inc(v_k_405_);
lean_dec_ref_known(v_p_u2082_389_, 1);
v___x_406_ = lean_apply_4(v_h__3_392_, v_k_402_, v_v_403_, v_p_404_, v_k_405_);
return v___x_406_;
}
else
{
lean_object* v_k_407_; lean_object* v_v_408_; lean_object* v_p_409_; lean_object* v_k_410_; lean_object* v_v_411_; lean_object* v_p_412_; lean_object* v___x_413_; 
lean_dec(v_h__3_392_);
v_k_407_ = lean_ctor_get(v_p_u2081_388_, 0);
lean_inc(v_k_407_);
v_v_408_ = lean_ctor_get(v_p_u2081_388_, 1);
lean_inc(v_v_408_);
v_p_409_ = lean_ctor_get(v_p_u2081_388_, 2);
lean_inc_ref(v_p_409_);
lean_dec_ref_known(v_p_u2081_388_, 3);
v_k_410_ = lean_ctor_get(v_p_u2082_389_, 0);
lean_inc(v_k_410_);
v_v_411_ = lean_ctor_get(v_p_u2082_389_, 1);
lean_inc(v_v_411_);
v_p_412_ = lean_ctor_get(v_p_u2082_389_, 2);
lean_inc_ref(v_p_412_);
lean_dec_ref_known(v_p_u2082_389_, 3);
v___x_413_ = lean_apply_6(v_h__4_393_, v_k_407_, v_v_408_, v_p_409_, v_k_410_, v_v_411_, v_p_412_);
return v___x_413_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_combine_go_match__1_splitter(lean_object* v_motive_414_, lean_object* v_p_u2081_415_, lean_object* v_p_u2082_416_, lean_object* v_h__1_417_, lean_object* v_h__2_418_, lean_object* v_h__3_419_, lean_object* v_h__4_420_){
_start:
{
if (lean_obj_tag(v_p_u2081_415_) == 0)
{
lean_dec(v_h__4_420_);
lean_dec(v_h__3_419_);
if (lean_obj_tag(v_p_u2082_416_) == 0)
{
lean_object* v_k_421_; lean_object* v_k_422_; lean_object* v___x_423_; 
lean_dec(v_h__2_418_);
v_k_421_ = lean_ctor_get(v_p_u2081_415_, 0);
lean_inc(v_k_421_);
lean_dec_ref_known(v_p_u2081_415_, 1);
v_k_422_ = lean_ctor_get(v_p_u2082_416_, 0);
lean_inc(v_k_422_);
lean_dec_ref_known(v_p_u2082_416_, 1);
v___x_423_ = lean_apply_2(v_h__1_417_, v_k_421_, v_k_422_);
return v___x_423_;
}
else
{
lean_object* v_k_424_; lean_object* v_k_425_; lean_object* v_v_426_; lean_object* v_p_427_; lean_object* v___x_428_; 
lean_dec(v_h__1_417_);
v_k_424_ = lean_ctor_get(v_p_u2081_415_, 0);
lean_inc(v_k_424_);
lean_dec_ref_known(v_p_u2081_415_, 1);
v_k_425_ = lean_ctor_get(v_p_u2082_416_, 0);
lean_inc(v_k_425_);
v_v_426_ = lean_ctor_get(v_p_u2082_416_, 1);
lean_inc(v_v_426_);
v_p_427_ = lean_ctor_get(v_p_u2082_416_, 2);
lean_inc_ref(v_p_427_);
lean_dec_ref_known(v_p_u2082_416_, 3);
v___x_428_ = lean_apply_4(v_h__2_418_, v_k_424_, v_k_425_, v_v_426_, v_p_427_);
return v___x_428_;
}
}
else
{
lean_dec(v_h__2_418_);
lean_dec(v_h__1_417_);
if (lean_obj_tag(v_p_u2082_416_) == 0)
{
lean_object* v_k_429_; lean_object* v_v_430_; lean_object* v_p_431_; lean_object* v_k_432_; lean_object* v___x_433_; 
lean_dec(v_h__4_420_);
v_k_429_ = lean_ctor_get(v_p_u2081_415_, 0);
lean_inc(v_k_429_);
v_v_430_ = lean_ctor_get(v_p_u2081_415_, 1);
lean_inc(v_v_430_);
v_p_431_ = lean_ctor_get(v_p_u2081_415_, 2);
lean_inc_ref(v_p_431_);
lean_dec_ref_known(v_p_u2081_415_, 3);
v_k_432_ = lean_ctor_get(v_p_u2082_416_, 0);
lean_inc(v_k_432_);
lean_dec_ref_known(v_p_u2082_416_, 1);
v___x_433_ = lean_apply_4(v_h__3_419_, v_k_429_, v_v_430_, v_p_431_, v_k_432_);
return v___x_433_;
}
else
{
lean_object* v_k_434_; lean_object* v_v_435_; lean_object* v_p_436_; lean_object* v_k_437_; lean_object* v_v_438_; lean_object* v_p_439_; lean_object* v___x_440_; 
lean_dec(v_h__3_419_);
v_k_434_ = lean_ctor_get(v_p_u2081_415_, 0);
lean_inc(v_k_434_);
v_v_435_ = lean_ctor_get(v_p_u2081_415_, 1);
lean_inc(v_v_435_);
v_p_436_ = lean_ctor_get(v_p_u2081_415_, 2);
lean_inc_ref(v_p_436_);
lean_dec_ref_known(v_p_u2081_415_, 3);
v_k_437_ = lean_ctor_get(v_p_u2082_416_, 0);
lean_inc(v_k_437_);
v_v_438_ = lean_ctor_get(v_p_u2082_416_, 1);
lean_inc(v_v_438_);
v_p_439_ = lean_ctor_get(v_p_u2082_416_, 2);
lean_inc_ref(v_p_439_);
lean_dec_ref_known(v_p_u2082_416_, 3);
v___x_440_ = lean_apply_6(v_h__4_420_, v_k_434_, v_v_435_, v_p_436_, v_k_437_, v_v_438_, v_p_439_);
return v___x_440_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter___redArg(lean_object* v_k_441_, lean_object* v_h__1_442_, lean_object* v_h__2_443_, lean_object* v_h__3_444_){
_start:
{
lean_object* v_zero_445_; uint8_t v_isZero_446_; 
v_zero_445_ = lean_unsigned_to_nat(0u);
v_isZero_446_ = lean_nat_dec_eq(v_k_441_, v_zero_445_);
if (v_isZero_446_ == 1)
{
lean_object* v___x_447_; lean_object* v___x_448_; 
lean_dec(v_h__3_444_);
lean_dec(v_h__2_443_);
v___x_447_ = lean_box(0);
v___x_448_ = lean_apply_1(v_h__1_442_, v___x_447_);
return v___x_448_;
}
else
{
lean_object* v_one_449_; lean_object* v_n_450_; uint8_t v___x_451_; 
lean_dec(v_h__1_442_);
v_one_449_ = lean_unsigned_to_nat(1u);
v_n_450_ = lean_nat_sub(v_k_441_, v_one_449_);
v___x_451_ = lean_nat_dec_eq(v_n_450_, v_zero_445_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; 
lean_dec(v_h__2_443_);
v___x_452_ = lean_apply_2(v_h__3_444_, v_n_450_, lean_box(0));
return v___x_452_;
}
else
{
lean_object* v___x_453_; lean_object* v___x_454_; 
lean_dec(v_n_450_);
lean_dec(v_h__3_444_);
v___x_453_ = lean_box(0);
v___x_454_ = lean_apply_1(v_h__2_443_, v___x_453_);
return v___x_454_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter___redArg___boxed(lean_object* v_k_455_, lean_object* v_h__1_456_, lean_object* v_h__2_457_, lean_object* v_h__3_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter___redArg(v_k_455_, v_h__1_456_, v_h__2_457_, v_h__3_458_);
lean_dec(v_k_455_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter(lean_object* v_motive_460_, lean_object* v_k_461_, lean_object* v_h__1_462_, lean_object* v_h__2_463_, lean_object* v_h__3_464_){
_start:
{
lean_object* v_zero_465_; uint8_t v_isZero_466_; 
v_zero_465_ = lean_unsigned_to_nat(0u);
v_isZero_466_ = lean_nat_dec_eq(v_k_461_, v_zero_465_);
if (v_isZero_466_ == 1)
{
lean_object* v___x_467_; lean_object* v___x_468_; 
lean_dec(v_h__3_464_);
lean_dec(v_h__2_463_);
v___x_467_ = lean_box(0);
v___x_468_ = lean_apply_1(v_h__1_462_, v___x_467_);
return v___x_468_;
}
else
{
lean_object* v_one_469_; lean_object* v_n_470_; uint8_t v___x_471_; 
lean_dec(v_h__1_462_);
v_one_469_ = lean_unsigned_to_nat(1u);
v_n_470_ = lean_nat_sub(v_k_461_, v_one_469_);
v___x_471_ = lean_nat_dec_eq(v_n_470_, v_zero_465_);
if (v___x_471_ == 0)
{
lean_object* v___x_472_; 
lean_dec(v_h__2_463_);
v___x_472_ = lean_apply_2(v_h__3_464_, v_n_470_, lean_box(0));
return v___x_472_;
}
else
{
lean_object* v___x_473_; lean_object* v___x_474_; 
lean_dec(v_n_470_);
lean_dec(v_h__3_464_);
v___x_473_ = lean_box(0);
v___x_474_ = lean_apply_1(v_h__2_463_, v___x_473_);
return v___x_474_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter___boxed(lean_object* v_motive_475_, lean_object* v_k_476_, lean_object* v_h__1_477_, lean_object* v_h__2_478_, lean_object* v_h__3_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter(v_motive_475_, v_k_476_, v_h__1_477_, v_h__2_478_, v_h__3_479_);
lean_dec(v_k_476_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteSList___redArg(lean_object* v_inst_481_, lean_object* v_ctx_482_, lean_object* v_x_483_){
_start:
{
if (lean_obj_tag(v_x_483_) == 0)
{
lean_object* v_ofNat_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v_ofNat_484_ = lean_ctor_get(v_inst_481_, 3);
lean_inc(v_ofNat_484_);
lean_dec_ref(v_inst_481_);
v___x_485_ = lean_unsigned_to_nat(0u);
v___x_486_ = lean_apply_1(v_ofNat_484_, v___x_485_);
return v___x_486_;
}
else
{
lean_object* v_toAdd_487_; lean_object* v_head_488_; lean_object* v_tail_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v_toAdd_487_ = lean_ctor_get(v_inst_481_, 0);
lean_inc(v_toAdd_487_);
v_head_488_ = lean_ctor_get(v_x_483_, 0);
lean_inc(v_head_488_);
v_tail_489_ = lean_ctor_get(v_x_483_, 1);
lean_inc(v_tail_489_);
lean_dec_ref_known(v_x_483_, 2);
lean_inc_ref(v_inst_481_);
v___x_490_ = l_Lean_Grind_CommRing_Poly_denoteS___redArg(v_inst_481_, v_ctx_482_, v_head_488_);
v___x_491_ = l_Lean_Grind_CommRing_Poly_denoteSList___redArg(v_inst_481_, v_ctx_482_, v_tail_489_);
v___x_492_ = lean_apply_2(v_toAdd_487_, v___x_490_, v___x_491_);
return v___x_492_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteSList___redArg___boxed(lean_object* v_inst_493_, lean_object* v_ctx_494_, lean_object* v_x_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_Lean_Grind_CommRing_Poly_denoteSList___redArg(v_inst_493_, v_ctx_494_, v_x_495_);
lean_dec_ref(v_ctx_494_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteSList(lean_object* v_00_u03b1_497_, lean_object* v_inst_498_, lean_object* v_ctx_499_, lean_object* v_x_500_){
_start:
{
lean_object* v___x_501_; 
v___x_501_ = l_Lean_Grind_CommRing_Poly_denoteSList___redArg(v_inst_498_, v_ctx_499_, v_x_500_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteSList___boxed(lean_object* v_00_u03b1_502_, lean_object* v_inst_503_, lean_object* v_ctx_504_, lean_object* v_x_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l_Lean_Grind_CommRing_Poly_denoteSList(v_00_u03b1_502_, v_inst_503_, v_ctx_504_, v_x_505_);
lean_dec_ref(v_ctx_504_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_NonnegList_match__1_splitter___redArg(lean_object* v_x_507_, lean_object* v_h__1_508_, lean_object* v_h__2_509_){
_start:
{
if (lean_obj_tag(v_x_507_) == 0)
{
lean_object* v___x_510_; lean_object* v___x_511_; 
lean_dec(v_h__2_509_);
v___x_510_ = lean_box(0);
v___x_511_ = lean_apply_1(v_h__1_508_, v___x_510_);
return v___x_511_;
}
else
{
lean_object* v_head_512_; lean_object* v_tail_513_; lean_object* v___x_514_; 
lean_dec(v_h__1_508_);
v_head_512_ = lean_ctor_get(v_x_507_, 0);
lean_inc(v_head_512_);
v_tail_513_ = lean_ctor_get(v_x_507_, 1);
lean_inc(v_tail_513_);
lean_dec_ref_known(v_x_507_, 2);
v___x_514_ = lean_apply_2(v_h__2_509_, v_head_512_, v_tail_513_);
return v___x_514_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_NonnegList_match__1_splitter(lean_object* v_motive_515_, lean_object* v_x_516_, lean_object* v_h__1_517_, lean_object* v_h__2_518_){
_start:
{
if (lean_obj_tag(v_x_516_) == 0)
{
lean_object* v___x_519_; lean_object* v___x_520_; 
lean_dec(v_h__2_518_);
v___x_519_ = lean_box(0);
v___x_520_ = lean_apply_1(v_h__1_517_, v___x_519_);
return v___x_520_;
}
else
{
lean_object* v_head_521_; lean_object* v_tail_522_; lean_object* v___x_523_; 
lean_dec(v_h__1_517_);
v_head_521_ = lean_ctor_get(v_x_516_, 0);
lean_inc(v_head_521_);
v_tail_522_ = lean_ctor_get(v_x_516_, 1);
lean_inc(v_tail_522_);
lean_dec_ref_known(v_x_516_, 2);
v___x_523_ = lean_apply_2(v_h__2_518_, v_head_521_, v_tail_522_);
return v___x_523_;
}
}
}
lean_object* runtime_initialize_Init_Grind_Ring_Envelope(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Ring_CommSolver(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_LemmasAux(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Grind_Ring_CommSemiringAdapter(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Grind_Ring_Envelope(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Ring_CommSolver(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_LemmasAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Grind_Ring_CommSemiringAdapter(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Grind_Ring_Envelope(uint8_t builtin);
lean_object* initialize_Init_Grind_Ring_CommSolver(uint8_t builtin);
lean_object* initialize_Init_Data_Int_LemmasAux(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Grind_Ring_CommSemiringAdapter(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Ring_Envelope(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Ring_CommSolver(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_LemmasAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Ring_CommSemiringAdapter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Grind_Ring_CommSemiringAdapter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Grind_Ring_CommSemiringAdapter(builtin);
}
#ifdef __cplusplus
}
#endif

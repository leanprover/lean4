// Lean compiler output
// Module: Lean.Elab.Tactic.Omega.MinNatAbs
// Imports: public import Init.Data.Int.Order public import Init.Data.List.MinMax public import Init.Data.Nat.Order import Init.ByCases import Init.Data.Bool import Init.Data.Option.Lemmas import Init.TacticsExtra
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Elab_Tactic_Omega_List_nonzeroMinimum_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_min_x3f___at___00Lean_Elab_Tactic_Omega_List_nonzeroMinimum_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_min_x3f___at___00Lean_Elab_Tactic_Omega_List_nonzeroMinimum_spec__1_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_min_x3f___at___00Lean_Elab_Tactic_Omega_List_nonzeroMinimum_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_min_x3f___at___00Lean_Elab_Tactic_Omega_List_nonzeroMinimum_spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_List_nonzeroMinimum(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_List_minNatAbs_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_List_minNatAbs(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_Tactic_Omega_List_maxNatAbs_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_Tactic_Omega_List_maxNatAbs_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_max_x3f___at___00Lean_Elab_Tactic_Omega_List_maxNatAbs_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_max_x3f___at___00Lean_Elab_Tactic_Omega_List_maxNatAbs_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_List_maxNatAbs(lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Elab_Tactic_Omega_List_nonzeroMinimum_spec__0(lean_object* v_a_1_, lean_object* v_a_2_){
_start:
{
if (lean_obj_tag(v_a_1_) == 0)
{
lean_object* v___x_3_; 
v___x_3_ = l_List_reverse___redArg(v_a_2_);
return v___x_3_;
}
else
{
lean_object* v_head_4_; lean_object* v_tail_5_; lean_object* v___x_7_; uint8_t v_isShared_8_; uint8_t v_isSharedCheck_16_; 
v_head_4_ = lean_ctor_get(v_a_1_, 0);
v_tail_5_ = lean_ctor_get(v_a_1_, 1);
v_isSharedCheck_16_ = !lean_is_exclusive(v_a_1_);
if (v_isSharedCheck_16_ == 0)
{
v___x_7_ = v_a_1_;
v_isShared_8_ = v_isSharedCheck_16_;
goto v_resetjp_6_;
}
else
{
lean_inc(v_tail_5_);
lean_inc(v_head_4_);
lean_dec(v_a_1_);
v___x_7_ = lean_box(0);
v_isShared_8_ = v_isSharedCheck_16_;
goto v_resetjp_6_;
}
v_resetjp_6_:
{
lean_object* v___x_9_; uint8_t v___x_10_; 
v___x_9_ = lean_unsigned_to_nat(0u);
v___x_10_ = lean_nat_dec_eq(v_head_4_, v___x_9_);
if (v___x_10_ == 0)
{
lean_object* v___x_12_; 
if (v_isShared_8_ == 0)
{
lean_ctor_set(v___x_7_, 1, v_a_2_);
v___x_12_ = v___x_7_;
goto v_reusejp_11_;
}
else
{
lean_object* v_reuseFailAlloc_14_; 
v_reuseFailAlloc_14_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_14_, 0, v_head_4_);
lean_ctor_set(v_reuseFailAlloc_14_, 1, v_a_2_);
v___x_12_ = v_reuseFailAlloc_14_;
goto v_reusejp_11_;
}
v_reusejp_11_:
{
v_a_1_ = v_tail_5_;
v_a_2_ = v___x_12_;
goto _start;
}
}
else
{
lean_del_object(v___x_7_);
lean_dec(v_head_4_);
v_a_1_ = v_tail_5_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_min_x3f___at___00Lean_Elab_Tactic_Omega_List_nonzeroMinimum_spec__1_spec__1(lean_object* v_x_17_, lean_object* v_x_18_){
_start:
{
if (lean_obj_tag(v_x_18_) == 0)
{
lean_inc(v_x_17_);
return v_x_17_;
}
else
{
lean_object* v_head_19_; lean_object* v_tail_20_; uint8_t v___x_21_; 
v_head_19_ = lean_ctor_get(v_x_18_, 0);
v_tail_20_ = lean_ctor_get(v_x_18_, 1);
v___x_21_ = lean_nat_dec_le(v_x_17_, v_head_19_);
if (v___x_21_ == 0)
{
v_x_17_ = v_head_19_;
v_x_18_ = v_tail_20_;
goto _start;
}
else
{
v_x_18_ = v_tail_20_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_min_x3f___at___00Lean_Elab_Tactic_Omega_List_nonzeroMinimum_spec__1_spec__1___boxed(lean_object* v_x_24_, lean_object* v_x_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_List_foldl___at___00List_min_x3f___at___00Lean_Elab_Tactic_Omega_List_nonzeroMinimum_spec__1_spec__1(v_x_24_, v_x_25_);
lean_dec(v_x_25_);
lean_dec(v_x_24_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_List_min_x3f___at___00Lean_Elab_Tactic_Omega_List_nonzeroMinimum_spec__1(lean_object* v_x_27_){
_start:
{
if (lean_obj_tag(v_x_27_) == 0)
{
lean_object* v___x_28_; 
v___x_28_ = lean_box(0);
return v___x_28_;
}
else
{
lean_object* v_head_29_; lean_object* v_tail_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v_head_29_ = lean_ctor_get(v_x_27_, 0);
v_tail_30_ = lean_ctor_get(v_x_27_, 1);
v___x_31_ = l_List_foldl___at___00List_min_x3f___at___00Lean_Elab_Tactic_Omega_List_nonzeroMinimum_spec__1_spec__1(v_head_29_, v_tail_30_);
v___x_32_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_32_, 0, v___x_31_);
return v___x_32_;
}
}
}
LEAN_EXPORT lean_object* l_List_min_x3f___at___00Lean_Elab_Tactic_Omega_List_nonzeroMinimum_spec__1___boxed(lean_object* v_x_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_List_min_x3f___at___00Lean_Elab_Tactic_Omega_List_nonzeroMinimum_spec__1(v_x_33_);
lean_dec(v_x_33_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_List_nonzeroMinimum(lean_object* v_xs_35_){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_36_ = lean_box(0);
v___x_37_ = l_List_filterTR_loop___at___00Lean_Elab_Tactic_Omega_List_nonzeroMinimum_spec__0(v_xs_35_, v___x_36_);
v___x_38_ = l_List_min_x3f___at___00Lean_Elab_Tactic_Omega_List_nonzeroMinimum_spec__1(v___x_37_);
lean_dec(v___x_37_);
if (lean_obj_tag(v___x_38_) == 0)
{
lean_object* v___x_39_; 
v___x_39_ = lean_unsigned_to_nat(0u);
return v___x_39_;
}
else
{
lean_object* v_val_40_; 
v_val_40_ = lean_ctor_get(v___x_38_, 0);
lean_inc(v_val_40_);
lean_dec_ref(v___x_38_);
return v_val_40_;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_List_minNatAbs_spec__0(lean_object* v_a_41_, lean_object* v_a_42_){
_start:
{
if (lean_obj_tag(v_a_41_) == 0)
{
lean_object* v___x_43_; 
v___x_43_ = l_List_reverse___redArg(v_a_42_);
return v___x_43_;
}
else
{
lean_object* v_head_44_; lean_object* v_tail_45_; lean_object* v___x_47_; uint8_t v_isShared_48_; uint8_t v_isSharedCheck_54_; 
v_head_44_ = lean_ctor_get(v_a_41_, 0);
v_tail_45_ = lean_ctor_get(v_a_41_, 1);
v_isSharedCheck_54_ = !lean_is_exclusive(v_a_41_);
if (v_isSharedCheck_54_ == 0)
{
v___x_47_ = v_a_41_;
v_isShared_48_ = v_isSharedCheck_54_;
goto v_resetjp_46_;
}
else
{
lean_inc(v_tail_45_);
lean_inc(v_head_44_);
lean_dec(v_a_41_);
v___x_47_ = lean_box(0);
v_isShared_48_ = v_isSharedCheck_54_;
goto v_resetjp_46_;
}
v_resetjp_46_:
{
lean_object* v___x_49_; lean_object* v___x_51_; 
v___x_49_ = lean_nat_abs(v_head_44_);
lean_dec(v_head_44_);
if (v_isShared_48_ == 0)
{
lean_ctor_set(v___x_47_, 1, v_a_42_);
lean_ctor_set(v___x_47_, 0, v___x_49_);
v___x_51_ = v___x_47_;
goto v_reusejp_50_;
}
else
{
lean_object* v_reuseFailAlloc_53_; 
v_reuseFailAlloc_53_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_53_, 0, v___x_49_);
lean_ctor_set(v_reuseFailAlloc_53_, 1, v_a_42_);
v___x_51_ = v_reuseFailAlloc_53_;
goto v_reusejp_50_;
}
v_reusejp_50_:
{
v_a_41_ = v_tail_45_;
v_a_42_ = v___x_51_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_List_minNatAbs(lean_object* v_xs_55_){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_56_ = lean_box(0);
v___x_57_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_List_minNatAbs_spec__0(v_xs_55_, v___x_56_);
v___x_58_ = l_Lean_Elab_Tactic_Omega_List_nonzeroMinimum(v___x_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_Tactic_Omega_List_maxNatAbs_spec__0_spec__0(lean_object* v_x_59_, lean_object* v_x_60_){
_start:
{
if (lean_obj_tag(v_x_60_) == 0)
{
lean_inc(v_x_59_);
return v_x_59_;
}
else
{
lean_object* v_head_61_; lean_object* v_tail_62_; uint8_t v___x_63_; 
v_head_61_ = lean_ctor_get(v_x_60_, 0);
v_tail_62_ = lean_ctor_get(v_x_60_, 1);
v___x_63_ = lean_nat_dec_le(v_x_59_, v_head_61_);
if (v___x_63_ == 0)
{
v_x_60_ = v_tail_62_;
goto _start;
}
else
{
v_x_59_ = v_head_61_;
v_x_60_ = v_tail_62_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_Tactic_Omega_List_maxNatAbs_spec__0_spec__0___boxed(lean_object* v_x_66_, lean_object* v_x_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_Tactic_Omega_List_maxNatAbs_spec__0_spec__0(v_x_66_, v_x_67_);
lean_dec(v_x_67_);
lean_dec(v_x_66_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l_List_max_x3f___at___00Lean_Elab_Tactic_Omega_List_maxNatAbs_spec__0(lean_object* v_x_69_){
_start:
{
if (lean_obj_tag(v_x_69_) == 0)
{
lean_object* v___x_70_; 
v___x_70_ = lean_box(0);
return v___x_70_;
}
else
{
lean_object* v_head_71_; lean_object* v_tail_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v_head_71_ = lean_ctor_get(v_x_69_, 0);
v_tail_72_ = lean_ctor_get(v_x_69_, 1);
v___x_73_ = l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_Tactic_Omega_List_maxNatAbs_spec__0_spec__0(v_head_71_, v_tail_72_);
v___x_74_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_74_, 0, v___x_73_);
return v___x_74_;
}
}
}
LEAN_EXPORT lean_object* l_List_max_x3f___at___00Lean_Elab_Tactic_Omega_List_maxNatAbs_spec__0___boxed(lean_object* v_x_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_List_max_x3f___at___00Lean_Elab_Tactic_Omega_List_maxNatAbs_spec__0(v_x_75_);
lean_dec(v_x_75_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_List_maxNatAbs(lean_object* v_xs_77_){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_78_ = lean_box(0);
v___x_79_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_List_minNatAbs_spec__0(v_xs_77_, v___x_78_);
v___x_80_ = l_List_max_x3f___at___00Lean_Elab_Tactic_Omega_List_maxNatAbs_spec__0(v___x_79_);
lean_dec(v___x_79_);
if (lean_obj_tag(v___x_80_) == 0)
{
lean_object* v___x_81_; 
v___x_81_ = lean_unsigned_to_nat(0u);
return v___x_81_;
}
else
{
lean_object* v_val_82_; 
v_val_82_ = lean_ctor_get(v___x_80_, 0);
lean_inc(v_val_82_);
lean_dec_ref(v___x_80_);
return v_val_82_;
}
}
}
lean_object* runtime_initialize_Init_Data_Int_Order(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_MinMax(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Order(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_TacticsExtra(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Omega_MinNatAbs(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Int_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Omega_MinNatAbs(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Int_Order(uint8_t builtin);
lean_object* initialize_Init_Data_List_MinMax(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Order(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Bool(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* initialize_Init_TacticsExtra(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Omega_MinNatAbs(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Int_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Omega_MinNatAbs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Omega_MinNatAbs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Omega_MinNatAbs(builtin);
}
#ifdef __cplusplus
}
#endif

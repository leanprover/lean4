// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Solve
// Imports: public import Lean.Meta.Tactic.Grind.Types import Lean.Meta.Tactic.Grind.Finish
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
lean_object* l_Lean_Meta_Grind_Action_mkFinish(lean_object*);
lean_object* l_Lean_Meta_Grind_Action_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_solve(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_solve___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_solve(lean_object* v_goal_1_, lean_object* v_a_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_, lean_object* v_a_9_, lean_object* v_a_10_){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_12_ = lean_unsigned_to_nat(10000u);
v___x_13_ = l_Lean_Meta_Grind_Action_mkFinish(v___x_12_);
if (lean_obj_tag(v___x_13_) == 0)
{
lean_object* v_a_14_; lean_object* v___x_15_; 
v_a_14_ = lean_ctor_get(v___x_13_, 0);
lean_inc(v_a_14_);
lean_dec_ref(v___x_13_);
lean_inc_ref(v_goal_1_);
v___x_15_ = l_Lean_Meta_Grind_Action_run(v_goal_1_, v_a_14_, v_a_2_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, v_a_10_);
if (lean_obj_tag(v___x_15_) == 0)
{
lean_object* v_a_16_; lean_object* v___x_18_; uint8_t v_isShared_19_; uint8_t v_isSharedCheck_42_; 
v_a_16_ = lean_ctor_get(v___x_15_, 0);
v_isSharedCheck_42_ = !lean_is_exclusive(v___x_15_);
if (v_isSharedCheck_42_ == 0)
{
v___x_18_ = v___x_15_;
v_isShared_19_ = v_isSharedCheck_42_;
goto v_resetjp_17_;
}
else
{
lean_inc(v_a_16_);
lean_dec(v___x_15_);
v___x_18_ = lean_box(0);
v_isShared_19_ = v_isSharedCheck_42_;
goto v_resetjp_17_;
}
v_resetjp_17_:
{
if (lean_obj_tag(v_a_16_) == 0)
{
lean_object* v___x_20_; lean_object* v___x_22_; 
lean_dec_ref(v_a_16_);
lean_dec_ref(v_goal_1_);
v___x_20_ = lean_box(0);
if (v_isShared_19_ == 0)
{
lean_ctor_set(v___x_18_, 0, v___x_20_);
v___x_22_ = v___x_18_;
goto v_reusejp_21_;
}
else
{
lean_object* v_reuseFailAlloc_23_; 
v_reuseFailAlloc_23_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_23_, 0, v___x_20_);
v___x_22_ = v_reuseFailAlloc_23_;
goto v_reusejp_21_;
}
v_reusejp_21_:
{
return v___x_22_;
}
}
else
{
lean_object* v_gs_24_; lean_object* v___x_26_; uint8_t v_isShared_27_; uint8_t v_isSharedCheck_41_; 
v_gs_24_ = lean_ctor_get(v_a_16_, 0);
v_isSharedCheck_41_ = !lean_is_exclusive(v_a_16_);
if (v_isSharedCheck_41_ == 0)
{
v___x_26_ = v_a_16_;
v_isShared_27_ = v_isSharedCheck_41_;
goto v_resetjp_25_;
}
else
{
lean_inc(v_gs_24_);
lean_dec(v_a_16_);
v___x_26_ = lean_box(0);
v_isShared_27_ = v_isSharedCheck_41_;
goto v_resetjp_25_;
}
v_resetjp_25_:
{
if (lean_obj_tag(v_gs_24_) == 1)
{
lean_object* v_head_28_; lean_object* v___x_30_; 
lean_dec_ref(v_goal_1_);
v_head_28_ = lean_ctor_get(v_gs_24_, 0);
lean_inc(v_head_28_);
lean_dec_ref(v_gs_24_);
if (v_isShared_27_ == 0)
{
lean_ctor_set(v___x_26_, 0, v_head_28_);
v___x_30_ = v___x_26_;
goto v_reusejp_29_;
}
else
{
lean_object* v_reuseFailAlloc_34_; 
v_reuseFailAlloc_34_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_34_, 0, v_head_28_);
v___x_30_ = v_reuseFailAlloc_34_;
goto v_reusejp_29_;
}
v_reusejp_29_:
{
lean_object* v___x_32_; 
if (v_isShared_19_ == 0)
{
lean_ctor_set(v___x_18_, 0, v___x_30_);
v___x_32_ = v___x_18_;
goto v_reusejp_31_;
}
else
{
lean_object* v_reuseFailAlloc_33_; 
v_reuseFailAlloc_33_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_33_, 0, v___x_30_);
v___x_32_ = v_reuseFailAlloc_33_;
goto v_reusejp_31_;
}
v_reusejp_31_:
{
return v___x_32_;
}
}
}
else
{
lean_object* v___x_36_; 
lean_dec(v_gs_24_);
if (v_isShared_27_ == 0)
{
lean_ctor_set(v___x_26_, 0, v_goal_1_);
v___x_36_ = v___x_26_;
goto v_reusejp_35_;
}
else
{
lean_object* v_reuseFailAlloc_40_; 
v_reuseFailAlloc_40_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_40_, 0, v_goal_1_);
v___x_36_ = v_reuseFailAlloc_40_;
goto v_reusejp_35_;
}
v_reusejp_35_:
{
lean_object* v___x_38_; 
if (v_isShared_19_ == 0)
{
lean_ctor_set(v___x_18_, 0, v___x_36_);
v___x_38_ = v___x_18_;
goto v_reusejp_37_;
}
else
{
lean_object* v_reuseFailAlloc_39_; 
v_reuseFailAlloc_39_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_39_, 0, v___x_36_);
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
}
}
else
{
lean_object* v_a_43_; lean_object* v___x_45_; uint8_t v_isShared_46_; uint8_t v_isSharedCheck_50_; 
lean_dec_ref(v_goal_1_);
v_a_43_ = lean_ctor_get(v___x_15_, 0);
v_isSharedCheck_50_ = !lean_is_exclusive(v___x_15_);
if (v_isSharedCheck_50_ == 0)
{
v___x_45_ = v___x_15_;
v_isShared_46_ = v_isSharedCheck_50_;
goto v_resetjp_44_;
}
else
{
lean_inc(v_a_43_);
lean_dec(v___x_15_);
v___x_45_ = lean_box(0);
v_isShared_46_ = v_isSharedCheck_50_;
goto v_resetjp_44_;
}
v_resetjp_44_:
{
lean_object* v___x_48_; 
if (v_isShared_46_ == 0)
{
v___x_48_ = v___x_45_;
goto v_reusejp_47_;
}
else
{
lean_object* v_reuseFailAlloc_49_; 
v_reuseFailAlloc_49_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_49_, 0, v_a_43_);
v___x_48_ = v_reuseFailAlloc_49_;
goto v_reusejp_47_;
}
v_reusejp_47_:
{
return v___x_48_;
}
}
}
}
else
{
lean_object* v_a_51_; lean_object* v___x_53_; uint8_t v_isShared_54_; uint8_t v_isSharedCheck_63_; 
lean_dec_ref(v_goal_1_);
v_a_51_ = lean_ctor_get(v___x_13_, 0);
v_isSharedCheck_63_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_63_ == 0)
{
v___x_53_ = v___x_13_;
v_isShared_54_ = v_isSharedCheck_63_;
goto v_resetjp_52_;
}
else
{
lean_inc(v_a_51_);
lean_dec(v___x_13_);
v___x_53_ = lean_box(0);
v_isShared_54_ = v_isSharedCheck_63_;
goto v_resetjp_52_;
}
v_resetjp_52_:
{
lean_object* v_ref_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_61_; 
v_ref_55_ = lean_ctor_get(v_a_9_, 5);
v___x_56_ = lean_io_error_to_string(v_a_51_);
v___x_57_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_57_, 0, v___x_56_);
v___x_58_ = l_Lean_MessageData_ofFormat(v___x_57_);
lean_inc(v_ref_55_);
v___x_59_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_59_, 0, v_ref_55_);
lean_ctor_set(v___x_59_, 1, v___x_58_);
if (v_isShared_54_ == 0)
{
lean_ctor_set(v___x_53_, 0, v___x_59_);
v___x_61_ = v___x_53_;
goto v_reusejp_60_;
}
else
{
lean_object* v_reuseFailAlloc_62_; 
v_reuseFailAlloc_62_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_62_, 0, v___x_59_);
v___x_61_ = v_reuseFailAlloc_62_;
goto v_reusejp_60_;
}
v_reusejp_60_:
{
return v___x_61_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_solve___boxed(lean_object* v_goal_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l_Lean_Meta_Grind_solve(v_goal_64_, v_a_65_, v_a_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_, v_a_73_);
lean_dec(v_a_73_);
lean_dec_ref(v_a_72_);
lean_dec(v_a_71_);
lean_dec_ref(v_a_70_);
lean_dec(v_a_69_);
lean_dec_ref(v_a_68_);
lean_dec(v_a_67_);
lean_dec_ref(v_a_66_);
lean_dec(v_a_65_);
return v_res_75_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Finish(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Solve(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Finish(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Solve(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Finish(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Solve(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Finish(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Solve(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Solve(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Solve(builtin);
}
#ifdef __cplusplus
}
#endif

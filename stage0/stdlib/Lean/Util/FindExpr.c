// Lean compiler output
// Module: Lean.Util.FindExpr
// Imports: public import Lean.Expr
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
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_findImpl_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_find_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_find_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_occurs___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_occurs___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_occurs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_occurs___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_found_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_found_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_found_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_found_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_visit_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_visit_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_visit_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_visit_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_done_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_done_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_done_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_done_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_find_ext_expr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_findExtImpl_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_findExt_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_findExt_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_findImpl_x3f___boxed(lean_object* v_p_3_, lean_object* v_e_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = lean_find_expr(v_p_3_, v_e_4_);
lean_dec_ref(v_e_4_);
lean_dec_ref(v_p_3_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_find_x3f(lean_object* v_p_6_, lean_object* v_e_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lean_find_expr(v_p_6_, v_e_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_find_x3f___boxed(lean_object* v_p_9_, lean_object* v_e_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_Lean_Expr_find_x3f(v_p_9_, v_e_10_);
lean_dec_ref(v_e_10_);
lean_dec_ref(v_p_9_);
return v_res_11_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_occurs___lam__0(lean_object* v_e_12_, lean_object* v_s_13_){
_start:
{
uint8_t v___x_14_; 
v___x_14_ = lean_expr_eqv(v_s_13_, v_e_12_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_occurs___lam__0___boxed(lean_object* v_e_15_, lean_object* v_s_16_){
_start:
{
uint8_t v_res_17_; lean_object* v_r_18_; 
v_res_17_ = l_Lean_Expr_occurs___lam__0(v_e_15_, v_s_16_);
lean_dec_ref(v_s_16_);
lean_dec_ref(v_e_15_);
v_r_18_ = lean_box(v_res_17_);
return v_r_18_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_occurs(lean_object* v_e_19_, lean_object* v_t_20_){
_start:
{
lean_object* v___f_21_; lean_object* v___x_22_; 
v___f_21_ = lean_alloc_closure((void*)(l_Lean_Expr_occurs___lam__0___boxed), 2, 1);
lean_closure_set(v___f_21_, 0, v_e_19_);
v___x_22_ = lean_find_expr(v___f_21_, v_t_20_);
lean_dec_ref(v___f_21_);
if (lean_obj_tag(v___x_22_) == 0)
{
uint8_t v___x_23_; 
v___x_23_ = 0;
return v___x_23_;
}
else
{
uint8_t v___x_24_; 
lean_dec_ref_known(v___x_22_, 1);
v___x_24_ = 1;
return v___x_24_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_occurs___boxed(lean_object* v_e_25_, lean_object* v_t_26_){
_start:
{
uint8_t v_res_27_; lean_object* v_r_28_; 
v_res_27_ = l_Lean_Expr_occurs(v_e_25_, v_t_26_);
lean_dec_ref(v_t_26_);
v_r_28_ = lean_box(v_res_27_);
return v_r_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_ctorIdx___impl(uint8_t v_x_29_){
_start:
{
lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_30_ = lean_box(v_x_29_);
v___x_31_ = lean_obj_tag_nat(v___x_30_);
lean_dec(v___x_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_ctorIdx___impl___boxed(lean_object* v_x_32_){
_start:
{
uint8_t v_x_4__boxed_33_; lean_object* v_res_34_; 
v_x_4__boxed_33_ = lean_unbox(v_x_32_);
v_res_34_ = l_Lean_Expr_FindStep_ctorIdx___impl(v_x_4__boxed_33_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_ctorElim___redArg(lean_object* v_k_35_){
_start:
{
lean_inc(v_k_35_);
return v_k_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_ctorElim___redArg___boxed(lean_object* v_k_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_Expr_FindStep_ctorElim___redArg(v_k_36_);
lean_dec(v_k_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_ctorElim(lean_object* v_motive_38_, lean_object* v_ctorIdx_39_, uint8_t v_t_40_, lean_object* v_h_41_, lean_object* v_k_42_){
_start:
{
lean_inc(v_k_42_);
return v_k_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_ctorElim___boxed(lean_object* v_motive_43_, lean_object* v_ctorIdx_44_, lean_object* v_t_45_, lean_object* v_h_46_, lean_object* v_k_47_){
_start:
{
uint8_t v_t_boxed_48_; lean_object* v_res_49_; 
v_t_boxed_48_ = lean_unbox(v_t_45_);
v_res_49_ = l_Lean_Expr_FindStep_ctorElim(v_motive_43_, v_ctorIdx_44_, v_t_boxed_48_, v_h_46_, v_k_47_);
lean_dec(v_k_47_);
lean_dec(v_ctorIdx_44_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_found_elim___redArg(lean_object* v_found_50_){
_start:
{
lean_inc(v_found_50_);
return v_found_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_found_elim___redArg___boxed(lean_object* v_found_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Lean_Expr_FindStep_found_elim___redArg(v_found_51_);
lean_dec(v_found_51_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_found_elim(lean_object* v_motive_53_, uint8_t v_t_54_, lean_object* v_h_55_, lean_object* v_found_56_){
_start:
{
lean_inc(v_found_56_);
return v_found_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_found_elim___boxed(lean_object* v_motive_57_, lean_object* v_t_58_, lean_object* v_h_59_, lean_object* v_found_60_){
_start:
{
uint8_t v_t_boxed_61_; lean_object* v_res_62_; 
v_t_boxed_61_ = lean_unbox(v_t_58_);
v_res_62_ = l_Lean_Expr_FindStep_found_elim(v_motive_57_, v_t_boxed_61_, v_h_59_, v_found_60_);
lean_dec(v_found_60_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_visit_elim___redArg(lean_object* v_visit_63_){
_start:
{
lean_inc(v_visit_63_);
return v_visit_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_visit_elim___redArg___boxed(lean_object* v_visit_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_Lean_Expr_FindStep_visit_elim___redArg(v_visit_64_);
lean_dec(v_visit_64_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_visit_elim(lean_object* v_motive_66_, uint8_t v_t_67_, lean_object* v_h_68_, lean_object* v_visit_69_){
_start:
{
lean_inc(v_visit_69_);
return v_visit_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_visit_elim___boxed(lean_object* v_motive_70_, lean_object* v_t_71_, lean_object* v_h_72_, lean_object* v_visit_73_){
_start:
{
uint8_t v_t_boxed_74_; lean_object* v_res_75_; 
v_t_boxed_74_ = lean_unbox(v_t_71_);
v_res_75_ = l_Lean_Expr_FindStep_visit_elim(v_motive_70_, v_t_boxed_74_, v_h_72_, v_visit_73_);
lean_dec(v_visit_73_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_done_elim___redArg(lean_object* v_done_76_){
_start:
{
lean_inc(v_done_76_);
return v_done_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_done_elim___redArg___boxed(lean_object* v_done_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l_Lean_Expr_FindStep_done_elim___redArg(v_done_77_);
lean_dec(v_done_77_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_done_elim(lean_object* v_motive_79_, uint8_t v_t_80_, lean_object* v_h_81_, lean_object* v_done_82_){
_start:
{
lean_inc(v_done_82_);
return v_done_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_done_elim___boxed(lean_object* v_motive_83_, lean_object* v_t_84_, lean_object* v_h_85_, lean_object* v_done_86_){
_start:
{
uint8_t v_t_boxed_87_; lean_object* v_res_88_; 
v_t_boxed_87_ = lean_unbox(v_t_84_);
v_res_88_ = l_Lean_Expr_FindStep_done_elim(v_motive_83_, v_t_boxed_87_, v_h_85_, v_done_86_);
lean_dec(v_done_86_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_findExtImpl_x3f___boxed(lean_object* v_p_91_, lean_object* v_e_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = lean_find_ext_expr(v_p_91_, v_e_92_);
lean_dec_ref(v_e_92_);
lean_dec_ref(v_p_91_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_findExt_x3f(lean_object* v_p_94_, lean_object* v_e_95_){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = lean_find_ext_expr(v_p_94_, v_e_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_findExt_x3f___boxed(lean_object* v_p_97_, lean_object* v_e_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_Lean_Expr_findExt_x3f(v_p_97_, v_e_98_);
lean_dec_ref(v_e_98_);
lean_dec_ref(v_p_97_);
return v_res_99_;
}
}
lean_object* runtime_initialize_Lean_Expr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_FindExpr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Util_FindExpr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Expr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_FindExpr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_FindExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Util_FindExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Util_FindExpr(builtin);
}
#ifdef __cplusplus
}
#endif

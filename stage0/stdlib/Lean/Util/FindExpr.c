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
lean_object* lean_find_expr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_findImpl_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_find_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_find_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_occurs___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_occurs___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_occurs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_occurs___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_ctorIdx(uint8_t v_x_29_){
_start:
{
switch(v_x_29_)
{
case 0:
{
lean_object* v___x_30_; 
v___x_30_ = lean_unsigned_to_nat(0u);
return v___x_30_;
}
case 1:
{
lean_object* v___x_31_; 
v___x_31_ = lean_unsigned_to_nat(1u);
return v___x_31_;
}
default: 
{
lean_object* v___x_32_; 
v___x_32_ = lean_unsigned_to_nat(2u);
return v___x_32_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_ctorIdx___boxed(lean_object* v_x_33_){
_start:
{
uint8_t v_x_boxed_34_; lean_object* v_res_35_; 
v_x_boxed_34_ = lean_unbox(v_x_33_);
v_res_35_ = l_Lean_Expr_FindStep_ctorIdx(v_x_boxed_34_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_ctorElim___redArg(lean_object* v_k_36_){
_start:
{
lean_inc(v_k_36_);
return v_k_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_ctorElim___redArg___boxed(lean_object* v_k_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_Expr_FindStep_ctorElim___redArg(v_k_37_);
lean_dec(v_k_37_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_ctorElim(lean_object* v_motive_39_, lean_object* v_ctorIdx_40_, uint8_t v_t_41_, lean_object* v_h_42_, lean_object* v_k_43_){
_start:
{
lean_inc(v_k_43_);
return v_k_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_ctorElim___boxed(lean_object* v_motive_44_, lean_object* v_ctorIdx_45_, lean_object* v_t_46_, lean_object* v_h_47_, lean_object* v_k_48_){
_start:
{
uint8_t v_t_boxed_49_; lean_object* v_res_50_; 
v_t_boxed_49_ = lean_unbox(v_t_46_);
v_res_50_ = l_Lean_Expr_FindStep_ctorElim(v_motive_44_, v_ctorIdx_45_, v_t_boxed_49_, v_h_47_, v_k_48_);
lean_dec(v_k_48_);
lean_dec(v_ctorIdx_45_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_found_elim___redArg(lean_object* v_found_51_){
_start:
{
lean_inc(v_found_51_);
return v_found_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_found_elim___redArg___boxed(lean_object* v_found_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l_Lean_Expr_FindStep_found_elim___redArg(v_found_52_);
lean_dec(v_found_52_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_found_elim(lean_object* v_motive_54_, uint8_t v_t_55_, lean_object* v_h_56_, lean_object* v_found_57_){
_start:
{
lean_inc(v_found_57_);
return v_found_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_found_elim___boxed(lean_object* v_motive_58_, lean_object* v_t_59_, lean_object* v_h_60_, lean_object* v_found_61_){
_start:
{
uint8_t v_t_boxed_62_; lean_object* v_res_63_; 
v_t_boxed_62_ = lean_unbox(v_t_59_);
v_res_63_ = l_Lean_Expr_FindStep_found_elim(v_motive_58_, v_t_boxed_62_, v_h_60_, v_found_61_);
lean_dec(v_found_61_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_visit_elim___redArg(lean_object* v_visit_64_){
_start:
{
lean_inc(v_visit_64_);
return v_visit_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_visit_elim___redArg___boxed(lean_object* v_visit_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_Lean_Expr_FindStep_visit_elim___redArg(v_visit_65_);
lean_dec(v_visit_65_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_visit_elim(lean_object* v_motive_67_, uint8_t v_t_68_, lean_object* v_h_69_, lean_object* v_visit_70_){
_start:
{
lean_inc(v_visit_70_);
return v_visit_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_visit_elim___boxed(lean_object* v_motive_71_, lean_object* v_t_72_, lean_object* v_h_73_, lean_object* v_visit_74_){
_start:
{
uint8_t v_t_boxed_75_; lean_object* v_res_76_; 
v_t_boxed_75_ = lean_unbox(v_t_72_);
v_res_76_ = l_Lean_Expr_FindStep_visit_elim(v_motive_71_, v_t_boxed_75_, v_h_73_, v_visit_74_);
lean_dec(v_visit_74_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_done_elim___redArg(lean_object* v_done_77_){
_start:
{
lean_inc(v_done_77_);
return v_done_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_done_elim___redArg___boxed(lean_object* v_done_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l_Lean_Expr_FindStep_done_elim___redArg(v_done_78_);
lean_dec(v_done_78_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_done_elim(lean_object* v_motive_80_, uint8_t v_t_81_, lean_object* v_h_82_, lean_object* v_done_83_){
_start:
{
lean_inc(v_done_83_);
return v_done_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_done_elim___boxed(lean_object* v_motive_84_, lean_object* v_t_85_, lean_object* v_h_86_, lean_object* v_done_87_){
_start:
{
uint8_t v_t_boxed_88_; lean_object* v_res_89_; 
v_t_boxed_88_ = lean_unbox(v_t_85_);
v_res_89_ = l_Lean_Expr_FindStep_done_elim(v_motive_84_, v_t_boxed_88_, v_h_86_, v_done_87_);
lean_dec(v_done_87_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_findExtImpl_x3f___boxed(lean_object* v_p_92_, lean_object* v_e_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = lean_find_ext_expr(v_p_92_, v_e_93_);
lean_dec_ref(v_e_93_);
lean_dec_ref(v_p_92_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_findExt_x3f(lean_object* v_p_95_, lean_object* v_e_96_){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = lean_find_ext_expr(v_p_95_, v_e_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_findExt_x3f___boxed(lean_object* v_p_98_, lean_object* v_e_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Lean_Expr_findExt_x3f(v_p_98_, v_e_99_);
lean_dec_ref(v_e_99_);
lean_dec_ref(v_p_98_);
return v_res_100_;
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

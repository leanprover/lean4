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
LEAN_EXPORT void l_Lean_Expr_findImpl_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1_ = stack[0].m_obj;
lean_object* v_e_2_ = stack[1].m_obj;
lean_object* v_res_3_;
v_res_3_ = lean_find_expr(v_p_1_, v_e_2_);
stack->m_obj
 = v_res_3_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_findImpl_x3f___boxed(lean_object* v_p_4_, lean_object* v_e_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = lean_find_expr(v_p_4_, v_e_5_);
lean_dec_ref(v_e_5_);
lean_dec_ref(v_p_4_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_find_x3f(lean_object* v_p_7_, lean_object* v_e_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_find_expr(v_p_7_, v_e_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_find_x3f___boxed(lean_object* v_p_10_, lean_object* v_e_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Lean_Expr_find_x3f(v_p_10_, v_e_11_);
lean_dec_ref(v_e_11_);
lean_dec_ref(v_p_10_);
return v_res_12_;
}
}
uint8_t l_Lean_Expr_occurs___lam__0(lean_object* v_e_13_, lean_object* v_s_14_){
_start:
{
uint8_t v___x_15_; 
v___x_15_ = lean_expr_eqv(v_s_14_, v_e_13_);
return v___x_15_;
}
}
LEAN_EXPORT void l_Lean_Expr_occurs___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_13_ = stack[0].m_obj;
lean_object* v_s_14_ = stack[1].m_obj;
uint8_t v_res_16_;
v_res_16_ = l_Lean_Expr_occurs___lam__0(v_e_13_, v_s_14_);
stack->m_num = v_res_16_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_occurs___lam__0___boxed(lean_object* v_e_17_, lean_object* v_s_18_){
_start:
{
uint8_t v_res_19_; lean_object* v_r_20_; 
v_res_19_ = l_Lean_Expr_occurs___lam__0(v_e_17_, v_s_18_);
lean_dec_ref(v_s_18_);
lean_dec_ref(v_e_17_);
v_r_20_ = lean_box(v_res_19_);
return v_r_20_;
}
}
uint8_t l_Lean_Expr_occurs(lean_object* v_e_21_, lean_object* v_t_22_){
_start:
{
lean_object* v___f_23_; lean_object* v___x_24_; 
v___f_23_ = lean_alloc_closure((void*)(l_Lean_Expr_occurs___lam__0___boxed), 2, 1);
lean_closure_set(v___f_23_, 0, v_e_21_);
v___x_24_ = lean_find_expr(v___f_23_, v_t_22_);
lean_dec_ref(v___f_23_);
if (lean_obj_tag(v___x_24_) == 0)
{
uint8_t v___x_25_; 
v___x_25_ = 0;
return v___x_25_;
}
else
{
uint8_t v___x_26_; 
lean_dec_ref_known(v___x_24_, 1);
v___x_26_ = 1;
return v___x_26_;
}
}
}
LEAN_EXPORT void l_Lean_Expr_occurs_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_21_ = stack[0].m_obj;
lean_object* v_t_22_ = stack[1].m_obj;
uint8_t v_res_27_;
v_res_27_ = l_Lean_Expr_occurs(v_e_21_, v_t_22_);
stack->m_num = v_res_27_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_occurs___boxed(lean_object* v_e_28_, lean_object* v_t_29_){
_start:
{
uint8_t v_res_30_; lean_object* v_r_31_; 
v_res_30_ = l_Lean_Expr_occurs(v_e_28_, v_t_29_);
lean_dec_ref(v_t_29_);
v_r_31_ = lean_box(v_res_30_);
return v_r_31_;
}
}
lean_object* l_Lean_Expr_FindStep_ctorIdx___impl(uint8_t v_x_32_){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_33_ = lean_box(v_x_32_);
v___x_34_ = lean_obj_tag_nat(v___x_33_);
lean_dec(v___x_33_);
return v___x_34_;
}
}
LEAN_EXPORT void l_Lean_Expr_FindStep_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_32_ = stack[0].m_num;
lean_object* v_res_35_;
v_res_35_ = l_Lean_Expr_FindStep_ctorIdx___impl(v_x_32_);
stack->m_obj
 = v_res_35_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_ctorIdx___impl___boxed(lean_object* v_x_36_){
_start:
{
uint8_t v_x_4__boxed_37_; lean_object* v_res_38_; 
v_x_4__boxed_37_ = lean_unbox(v_x_36_);
v_res_38_ = l_Lean_Expr_FindStep_ctorIdx___impl(v_x_4__boxed_37_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_ctorElim___redArg(lean_object* v_k_39_){
_start:
{
lean_inc(v_k_39_);
return v_k_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_ctorElim___redArg___boxed(lean_object* v_k_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l_Lean_Expr_FindStep_ctorElim___redArg(v_k_40_);
lean_dec(v_k_40_);
return v_res_41_;
}
}
lean_object* l_Lean_Expr_FindStep_ctorElim(lean_object* v_motive_42_, lean_object* v_ctorIdx_43_, uint8_t v_t_44_, lean_object* v_h_45_, lean_object* v_k_46_){
_start:
{
lean_inc(v_k_46_);
return v_k_46_;
}
}
LEAN_EXPORT void l_Lean_Expr_FindStep_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_43_ = stack[1].m_obj;
uint8_t v_t_44_ = stack[2].m_num;
lean_object* v_k_46_ = stack[4].m_obj;
lean_object* v_res_47_;
v_res_47_ = l_Lean_Expr_FindStep_ctorElim(lean_box(0), v_ctorIdx_43_, v_t_44_, lean_box(0), v_k_46_);
stack->m_obj
 = v_res_47_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_ctorElim___boxed(lean_object* v_motive_48_, lean_object* v_ctorIdx_49_, lean_object* v_t_50_, lean_object* v_h_51_, lean_object* v_k_52_){
_start:
{
uint8_t v_t_boxed_53_; lean_object* v_res_54_; 
v_t_boxed_53_ = lean_unbox(v_t_50_);
v_res_54_ = l_Lean_Expr_FindStep_ctorElim(v_motive_48_, v_ctorIdx_49_, v_t_boxed_53_, v_h_51_, v_k_52_);
lean_dec(v_k_52_);
lean_dec(v_ctorIdx_49_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_found_elim___redArg(lean_object* v_found_55_){
_start:
{
lean_inc(v_found_55_);
return v_found_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_found_elim___redArg___boxed(lean_object* v_found_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Lean_Expr_FindStep_found_elim___redArg(v_found_56_);
lean_dec(v_found_56_);
return v_res_57_;
}
}
lean_object* l_Lean_Expr_FindStep_found_elim(lean_object* v_motive_58_, uint8_t v_t_59_, lean_object* v_h_60_, lean_object* v_found_61_){
_start:
{
lean_inc(v_found_61_);
return v_found_61_;
}
}
LEAN_EXPORT void l_Lean_Expr_FindStep_found_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_59_ = stack[1].m_num;
lean_object* v_found_61_ = stack[3].m_obj;
lean_object* v_res_62_;
v_res_62_ = l_Lean_Expr_FindStep_found_elim(lean_box(0), v_t_59_, lean_box(0), v_found_61_);
stack->m_obj
 = v_res_62_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_found_elim___boxed(lean_object* v_motive_63_, lean_object* v_t_64_, lean_object* v_h_65_, lean_object* v_found_66_){
_start:
{
uint8_t v_t_boxed_67_; lean_object* v_res_68_; 
v_t_boxed_67_ = lean_unbox(v_t_64_);
v_res_68_ = l_Lean_Expr_FindStep_found_elim(v_motive_63_, v_t_boxed_67_, v_h_65_, v_found_66_);
lean_dec(v_found_66_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_visit_elim___redArg(lean_object* v_visit_69_){
_start:
{
lean_inc(v_visit_69_);
return v_visit_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_visit_elim___redArg___boxed(lean_object* v_visit_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l_Lean_Expr_FindStep_visit_elim___redArg(v_visit_70_);
lean_dec(v_visit_70_);
return v_res_71_;
}
}
lean_object* l_Lean_Expr_FindStep_visit_elim(lean_object* v_motive_72_, uint8_t v_t_73_, lean_object* v_h_74_, lean_object* v_visit_75_){
_start:
{
lean_inc(v_visit_75_);
return v_visit_75_;
}
}
LEAN_EXPORT void l_Lean_Expr_FindStep_visit_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_73_ = stack[1].m_num;
lean_object* v_visit_75_ = stack[3].m_obj;
lean_object* v_res_76_;
v_res_76_ = l_Lean_Expr_FindStep_visit_elim(lean_box(0), v_t_73_, lean_box(0), v_visit_75_);
stack->m_obj
 = v_res_76_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_visit_elim___boxed(lean_object* v_motive_77_, lean_object* v_t_78_, lean_object* v_h_79_, lean_object* v_visit_80_){
_start:
{
uint8_t v_t_boxed_81_; lean_object* v_res_82_; 
v_t_boxed_81_ = lean_unbox(v_t_78_);
v_res_82_ = l_Lean_Expr_FindStep_visit_elim(v_motive_77_, v_t_boxed_81_, v_h_79_, v_visit_80_);
lean_dec(v_visit_80_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_done_elim___redArg(lean_object* v_done_83_){
_start:
{
lean_inc(v_done_83_);
return v_done_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_done_elim___redArg___boxed(lean_object* v_done_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Lean_Expr_FindStep_done_elim___redArg(v_done_84_);
lean_dec(v_done_84_);
return v_res_85_;
}
}
lean_object* l_Lean_Expr_FindStep_done_elim(lean_object* v_motive_86_, uint8_t v_t_87_, lean_object* v_h_88_, lean_object* v_done_89_){
_start:
{
lean_inc(v_done_89_);
return v_done_89_;
}
}
LEAN_EXPORT void l_Lean_Expr_FindStep_done_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_87_ = stack[1].m_num;
lean_object* v_done_89_ = stack[3].m_obj;
lean_object* v_res_90_;
v_res_90_ = l_Lean_Expr_FindStep_done_elim(lean_box(0), v_t_87_, lean_box(0), v_done_89_);
stack->m_obj
 = v_res_90_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_done_elim___boxed(lean_object* v_motive_91_, lean_object* v_t_92_, lean_object* v_h_93_, lean_object* v_done_94_){
_start:
{
uint8_t v_t_boxed_95_; lean_object* v_res_96_; 
v_t_boxed_95_ = lean_unbox(v_t_92_);
v_res_96_ = l_Lean_Expr_FindStep_done_elim(v_motive_91_, v_t_boxed_95_, v_h_93_, v_done_94_);
lean_dec(v_done_94_);
return v_res_96_;
}
}
LEAN_EXPORT void l_Lean_Expr_findExtImpl_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_97_ = stack[0].m_obj;
lean_object* v_e_98_ = stack[1].m_obj;
lean_object* v_res_99_;
v_res_99_ = lean_find_ext_expr(v_p_97_, v_e_98_);
stack->m_obj
 = v_res_99_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_findExtImpl_x3f___boxed(lean_object* v_p_100_, lean_object* v_e_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = lean_find_ext_expr(v_p_100_, v_e_101_);
lean_dec_ref(v_e_101_);
lean_dec_ref(v_p_100_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_findExt_x3f(lean_object* v_p_103_, lean_object* v_e_104_){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = lean_find_ext_expr(v_p_103_, v_e_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_findExt_x3f___boxed(lean_object* v_p_106_, lean_object* v_e_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Lean_Expr_findExt_x3f(v_p_106_, v_e_107_);
lean_dec_ref(v_e_107_);
lean_dec_ref(v_p_106_);
return v_res_108_;
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

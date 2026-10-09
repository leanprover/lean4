// Lean compiler output
// Module: Lean.Meta.Sym.DSimp.App
// Imports: public import Lean.Meta.Sym.DSimp.DSimpM import Lean.Meta.Sym.DSimp.Result import Lean.Meta.Sym.AlphaShareBuilder import Lean.Meta.Sym.ProofInstInfo import Init.Omega
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_sym_dsimp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg();
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Meta_Sym_getProofInstInfoOfExpr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__1___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Meta.Sym.DSimp.App"};
static const lean_object* l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 70, .m_data = "_private.Lean.Meta.Sym.DSimp.App.0.Lean.Meta.Sym.DSimp.dsimpAppArgs.go"};
static const lean_object* l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__3;
static const lean_ctor_object l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__4 = (const lean_object*)&l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpAppArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpAppArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__0___redArg(lean_object* v_f_1_, lean_object* v_a_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_){
_start:
{
lean_object* v___y_11_; lean_object* v___x_14_; uint8_t v_debug_15_; 
v___x_14_ = lean_st_ref_get(v___y_4_);
v_debug_15_ = lean_ctor_get_uint8(v___x_14_, sizeof(void*)*12);
lean_dec(v___x_14_);
if (v_debug_15_ == 0)
{
v___y_11_ = v___y_4_;
goto v___jp_10_;
}
else
{
lean_object* v___x_16_; 
v___x_16_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_1_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_);
if (lean_obj_tag(v___x_16_) == 0)
{
lean_object* v___x_17_; 
lean_dec_ref_known(v___x_16_, 1);
v___x_17_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_);
if (lean_obj_tag(v___x_17_) == 0)
{
lean_dec_ref_known(v___x_17_, 1);
v___y_11_ = v___y_4_;
goto v___jp_10_;
}
else
{
lean_object* v_a_18_; lean_object* v___x_20_; uint8_t v_isShared_21_; uint8_t v_isSharedCheck_25_; 
lean_dec_ref(v_a_2_);
lean_dec_ref(v_f_1_);
v_a_18_ = lean_ctor_get(v___x_17_, 0);
v_isSharedCheck_25_ = !lean_is_exclusive(v___x_17_);
if (v_isSharedCheck_25_ == 0)
{
v___x_20_ = v___x_17_;
v_isShared_21_ = v_isSharedCheck_25_;
goto v_resetjp_19_;
}
else
{
lean_inc(v_a_18_);
lean_dec(v___x_17_);
v___x_20_ = lean_box(0);
v_isShared_21_ = v_isSharedCheck_25_;
goto v_resetjp_19_;
}
v_resetjp_19_:
{
lean_object* v___x_23_; 
if (v_isShared_21_ == 0)
{
v___x_23_ = v___x_20_;
goto v_reusejp_22_;
}
else
{
lean_object* v_reuseFailAlloc_24_; 
v_reuseFailAlloc_24_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_24_, 0, v_a_18_);
v___x_23_ = v_reuseFailAlloc_24_;
goto v_reusejp_22_;
}
v_reusejp_22_:
{
return v___x_23_;
}
}
}
}
else
{
lean_object* v_a_26_; lean_object* v___x_28_; uint8_t v_isShared_29_; uint8_t v_isSharedCheck_33_; 
lean_dec_ref(v_a_2_);
lean_dec_ref(v_f_1_);
v_a_26_ = lean_ctor_get(v___x_16_, 0);
v_isSharedCheck_33_ = !lean_is_exclusive(v___x_16_);
if (v_isSharedCheck_33_ == 0)
{
v___x_28_ = v___x_16_;
v_isShared_29_ = v_isSharedCheck_33_;
goto v_resetjp_27_;
}
else
{
lean_inc(v_a_26_);
lean_dec(v___x_16_);
v___x_28_ = lean_box(0);
v_isShared_29_ = v_isSharedCheck_33_;
goto v_resetjp_27_;
}
v_resetjp_27_:
{
lean_object* v___x_31_; 
if (v_isShared_29_ == 0)
{
v___x_31_ = v___x_28_;
goto v_reusejp_30_;
}
else
{
lean_object* v_reuseFailAlloc_32_; 
v_reuseFailAlloc_32_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_32_, 0, v_a_26_);
v___x_31_ = v_reuseFailAlloc_32_;
goto v_reusejp_30_;
}
v_reusejp_30_:
{
return v___x_31_;
}
}
}
}
v___jp_10_:
{
lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_12_ = l_Lean_Expr_app___override(v_f_1_, v_a_2_);
v___x_13_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_12_, v___y_11_);
return v___x_13_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1_ = stack[0].m_obj;
lean_object* v_a_2_ = stack[1].m_obj;
lean_object* v___y_3_ = stack[2].m_obj;
lean_object* v___y_4_ = stack[3].m_obj;
lean_object* v___y_5_ = stack[4].m_obj;
lean_object* v___y_6_ = stack[5].m_obj;
lean_object* v___y_7_ = stack[6].m_obj;
lean_object* v___y_8_ = stack[7].m_obj;
lean_object* v_res_34_;
v_res_34_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__0___redArg(v_f_1_, v_a_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_);
stack->m_obj
 = v_res_34_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__0___redArg___boxed(lean_object* v_f_35_, lean_object* v_a_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__0___redArg(v_f_35_, v_a_36_, v___y_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_, v___y_42_);
lean_dec(v___y_42_);
lean_dec_ref(v___y_41_);
lean_dec(v___y_40_);
lean_dec_ref(v___y_39_);
lean_dec(v___y_38_);
lean_dec_ref(v___y_37_);
return v_res_44_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__0(lean_object* v_f_45_, lean_object* v_a_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__0___redArg(v_f_45_, v_a_46_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_);
return v___x_57_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_45_ = stack[0].m_obj;
lean_object* v_a_46_ = stack[1].m_obj;
lean_object* v___y_47_ = stack[2].m_obj;
lean_object* v___y_48_ = stack[3].m_obj;
lean_object* v___y_49_ = stack[4].m_obj;
lean_object* v___y_50_ = stack[5].m_obj;
lean_object* v___y_51_ = stack[6].m_obj;
lean_object* v___y_52_ = stack[7].m_obj;
lean_object* v___y_53_ = stack[8].m_obj;
lean_object* v___y_54_ = stack[9].m_obj;
lean_object* v___y_55_ = stack[10].m_obj;
lean_object* v_res_58_;
v_res_58_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__0(v_f_45_, v_a_46_, v___y_47_, v___y_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_);
stack->m_obj
 = v_res_58_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__0___boxed(lean_object* v_f_59_, lean_object* v_a_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__0(v_f_59_, v_a_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_, v___y_67_, v___y_68_, v___y_69_);
lean_dec(v___y_69_);
lean_dec_ref(v___y_68_);
lean_dec(v___y_67_);
lean_dec_ref(v___y_66_);
lean_dec(v___y_65_);
lean_dec_ref(v___y_64_);
lean_dec(v___y_63_);
lean_dec_ref(v___y_62_);
lean_dec(v___y_61_);
return v_res_71_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__1___closed__0(void){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___redArg();
return v___x_72_;
}
}
lean_object* l_panic___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__1(lean_object* v_msg_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_){
_start:
{
lean_object* v___x_84_; lean_object* v___x_15042__overap_85_; lean_object* v___x_86_; 
v___x_84_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__1___closed__0);
v___x_15042__overap_85_ = lean_panic_fn_borrowed(v___x_84_, v_msg_73_);
lean_inc(v___y_82_);
lean_inc_ref(v___y_81_);
lean_inc(v___y_80_);
lean_inc_ref(v___y_79_);
lean_inc(v___y_78_);
lean_inc_ref(v___y_77_);
lean_inc(v___y_76_);
lean_inc_ref(v___y_75_);
lean_inc(v___y_74_);
v___x_86_ = lean_apply_10(v___x_15042__overap_85_, v___y_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, lean_box(0));
return v___x_86_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_73_ = stack[0].m_obj;
lean_object* v___y_74_ = stack[1].m_obj;
lean_object* v___y_75_ = stack[2].m_obj;
lean_object* v___y_76_ = stack[3].m_obj;
lean_object* v___y_77_ = stack[4].m_obj;
lean_object* v___y_78_ = stack[5].m_obj;
lean_object* v___y_79_ = stack[6].m_obj;
lean_object* v___y_80_ = stack[7].m_obj;
lean_object* v___y_81_ = stack[8].m_obj;
lean_object* v___y_82_ = stack[9].m_obj;
lean_object* v_res_87_;
v_res_87_ = l_panic___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__1(v_msg_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_);
stack->m_obj
 = v_res_87_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__1___boxed(lean_object* v_msg_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_panic___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__1(v_msg_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_);
lean_dec(v___y_97_);
lean_dec_ref(v___y_96_);
lean_dec(v___y_95_);
lean_dec_ref(v___y_94_);
lean_dec(v___y_93_);
lean_dec_ref(v___y_92_);
lean_dec(v___y_91_);
lean_dec_ref(v___y_90_);
lean_dec(v___y_89_);
return v_res_99_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__3(void){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_103_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__2));
v___x_104_ = lean_unsigned_to_nat(24u);
v___x_105_ = lean_unsigned_to_nat(52u);
v___x_106_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__1));
v___x_107_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__0));
v___x_108_ = l_mkPanicMessageWithDecl(v___x_107_, v___x_106_, v___x_105_, v___x_104_, v___x_103_);
return v___x_108_;
}
}
lean_object* l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go(lean_object* v_argsInfo_x3f_111_, lean_object* v_i_112_, lean_object* v_e_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_){
_start:
{
lean_object* v___x_124_; uint8_t v___x_125_; lean_object* v_a_127_; lean_object* v___y_131_; lean_object* v_a_142_; lean_object* v___y_146_; lean_object* v_a_157_; lean_object* v___y_161_; 
v___x_124_ = lean_unsigned_to_nat(0u);
v___x_125_ = lean_nat_dec_eq(v_i_112_, v___x_124_);
if (v___x_125_ == 0)
{
if (lean_obj_tag(v_e_113_) == 5)
{
lean_object* v_fn_171_; lean_object* v_arg_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v_fn_171_ = lean_ctor_get(v_e_113_, 0);
v_arg_172_ = lean_ctor_get(v_e_113_, 1);
v___x_173_ = lean_unsigned_to_nat(1u);
v___x_174_ = lean_nat_sub(v_i_112_, v___x_173_);
lean_inc_ref(v_fn_171_);
v___x_175_ = l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go(v_argsInfo_x3f_111_, v___x_174_, v_fn_171_, v_a_114_, v_a_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_);
if (lean_obj_tag(v___x_175_) == 0)
{
lean_object* v_a_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_239_; 
v_a_176_ = lean_ctor_get(v___x_175_, 0);
v_isSharedCheck_239_ = !lean_is_exclusive(v___x_175_);
if (v_isSharedCheck_239_ == 0)
{
v___x_178_ = v___x_175_;
v_isShared_179_ = v_isSharedCheck_239_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_a_176_);
lean_dec(v___x_175_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_239_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v_ar_181_; lean_object* v___y_182_; lean_object* v___y_183_; lean_object* v___y_184_; lean_object* v___y_185_; lean_object* v___y_186_; lean_object* v___y_187_; lean_object* v___y_188_; lean_object* v___y_189_; lean_object* v___y_190_; 
if (lean_obj_tag(v_argsInfo_x3f_111_) == 0)
{
lean_dec(v___x_174_);
goto v___jp_227_;
}
else
{
lean_object* v_val_232_; lean_object* v___x_233_; uint8_t v___x_234_; 
v_val_232_ = lean_ctor_get(v_argsInfo_x3f_111_, 0);
v___x_233_ = lean_array_get_size(v_val_232_);
v___x_234_ = lean_nat_dec_lt(v___x_174_, v___x_233_);
if (v___x_234_ == 0)
{
lean_dec(v___x_174_);
goto v___jp_227_;
}
else
{
lean_object* v___x_235_; uint8_t v_isProof_236_; 
v___x_235_ = lean_array_fget_borrowed(v_val_232_, v___x_174_);
lean_dec(v___x_174_);
v_isProof_236_ = lean_ctor_get_uint8(v___x_235_, 0);
if (v_isProof_236_ == 0)
{
uint8_t v_isInstance_237_; 
v_isInstance_237_ = lean_ctor_get_uint8(v___x_235_, 1);
if (v_isInstance_237_ == 0)
{
goto v___jp_227_;
}
else
{
uint8_t v_instances_238_; 
v_instances_238_ = lean_ctor_get_uint8(v_a_115_, sizeof(void*)*1);
if (v_instances_238_ == 0)
{
goto v___jp_230_;
}
else
{
goto v___jp_227_;
}
}
}
else
{
goto v___jp_230_;
}
}
}
v___jp_180_:
{
if (lean_obj_tag(v_a_176_) == 0)
{
lean_dec_ref_known(v_a_176_, 0);
if (lean_obj_tag(v_ar_181_) == 0)
{
lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_200_; 
lean_dec_ref_known(v_e_113_, 2);
v_isSharedCheck_200_ = !lean_is_exclusive(v_ar_181_);
if (v_isSharedCheck_200_ == 0)
{
v___x_192_ = v_ar_181_;
v_isShared_193_ = v_isSharedCheck_200_;
goto v_resetjp_191_;
}
else
{
lean_dec(v_ar_181_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_200_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v___x_195_; 
if (v_isShared_193_ == 0)
{
v___x_195_ = v___x_192_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(0, 0, 1);
v___x_195_ = v_reuseFailAlloc_199_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
lean_object* v___x_197_; 
lean_ctor_set_uint8(v___x_195_, 0, v___x_125_);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 0, v___x_195_);
v___x_197_ = v___x_178_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v___x_195_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
}
else
{
lean_object* v_e_x27_201_; size_t v___x_202_; uint8_t v___x_203_; 
lean_del_object(v___x_178_);
v_e_x27_201_ = lean_ctor_get(v_ar_181_, 0);
lean_inc_ref(v_e_x27_201_);
lean_dec_ref_known(v_ar_181_, 1);
v___x_202_ = lean_ptr_addr(v_fn_171_);
v___x_203_ = lean_usize_dec_eq(v___x_202_, v___x_202_);
if (v___x_203_ == 0)
{
lean_object* v___x_204_; 
lean_inc_ref(v_fn_171_);
lean_dec_ref_known(v_e_113_, 2);
v___x_204_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__0___redArg(v_fn_171_, v_e_x27_201_, v___y_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_);
v___y_161_ = v___x_204_;
goto v___jp_160_;
}
else
{
size_t v___x_205_; size_t v___x_206_; uint8_t v___x_207_; 
v___x_205_ = lean_ptr_addr(v_arg_172_);
v___x_206_ = lean_ptr_addr(v_e_x27_201_);
v___x_207_ = lean_usize_dec_eq(v___x_205_, v___x_206_);
if (v___x_207_ == 0)
{
lean_object* v___x_208_; 
lean_inc_ref(v_fn_171_);
lean_dec_ref_known(v_e_113_, 2);
v___x_208_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__0___redArg(v_fn_171_, v_e_x27_201_, v___y_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_);
v___y_161_ = v___x_208_;
goto v___jp_160_;
}
else
{
lean_dec_ref(v_e_x27_201_);
v_a_157_ = v_e_113_;
goto v___jp_156_;
}
}
}
}
else
{
lean_del_object(v___x_178_);
if (lean_obj_tag(v_ar_181_) == 0)
{
lean_object* v_e_x27_209_; size_t v___x_210_; size_t v___x_211_; uint8_t v___x_212_; 
lean_dec_ref_known(v_ar_181_, 0);
v_e_x27_209_ = lean_ctor_get(v_a_176_, 0);
lean_inc_ref(v_e_x27_209_);
lean_dec_ref_known(v_a_176_, 1);
v___x_210_ = lean_ptr_addr(v_fn_171_);
v___x_211_ = lean_ptr_addr(v_e_x27_209_);
v___x_212_ = lean_usize_dec_eq(v___x_210_, v___x_211_);
if (v___x_212_ == 0)
{
lean_object* v___x_213_; 
lean_inc_ref(v_arg_172_);
lean_dec_ref_known(v_e_113_, 2);
v___x_213_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__0___redArg(v_e_x27_209_, v_arg_172_, v___y_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_);
v___y_146_ = v___x_213_;
goto v___jp_145_;
}
else
{
size_t v___x_214_; uint8_t v___x_215_; 
v___x_214_ = lean_ptr_addr(v_arg_172_);
v___x_215_ = lean_usize_dec_eq(v___x_214_, v___x_214_);
if (v___x_215_ == 0)
{
lean_object* v___x_216_; 
lean_inc_ref(v_arg_172_);
lean_dec_ref_known(v_e_113_, 2);
v___x_216_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__0___redArg(v_e_x27_209_, v_arg_172_, v___y_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_);
v___y_146_ = v___x_216_;
goto v___jp_145_;
}
else
{
lean_dec_ref(v_e_x27_209_);
v_a_142_ = v_e_113_;
goto v___jp_141_;
}
}
}
else
{
lean_object* v_e_x27_217_; lean_object* v_e_x27_218_; size_t v___x_219_; size_t v___x_220_; uint8_t v___x_221_; 
v_e_x27_217_ = lean_ctor_get(v_a_176_, 0);
lean_inc_ref(v_e_x27_217_);
lean_dec_ref_known(v_a_176_, 1);
v_e_x27_218_ = lean_ctor_get(v_ar_181_, 0);
lean_inc_ref(v_e_x27_218_);
lean_dec_ref_known(v_ar_181_, 1);
v___x_219_ = lean_ptr_addr(v_fn_171_);
v___x_220_ = lean_ptr_addr(v_e_x27_217_);
v___x_221_ = lean_usize_dec_eq(v___x_219_, v___x_220_);
if (v___x_221_ == 0)
{
lean_object* v___x_222_; 
lean_dec_ref_known(v_e_113_, 2);
v___x_222_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__0___redArg(v_e_x27_217_, v_e_x27_218_, v___y_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_);
v___y_131_ = v___x_222_;
goto v___jp_130_;
}
else
{
size_t v___x_223_; size_t v___x_224_; uint8_t v___x_225_; 
v___x_223_ = lean_ptr_addr(v_arg_172_);
v___x_224_ = lean_ptr_addr(v_e_x27_218_);
v___x_225_ = lean_usize_dec_eq(v___x_223_, v___x_224_);
if (v___x_225_ == 0)
{
lean_object* v___x_226_; 
lean_dec_ref_known(v_e_113_, 2);
v___x_226_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__0___redArg(v_e_x27_217_, v_e_x27_218_, v___y_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_);
v___y_131_ = v___x_226_;
goto v___jp_130_;
}
else
{
lean_dec_ref(v_e_x27_218_);
lean_dec_ref(v_e_x27_217_);
v_a_127_ = v_e_113_;
goto v___jp_126_;
}
}
}
}
}
v___jp_227_:
{
lean_object* v___x_228_; 
lean_inc(v_a_122_);
lean_inc_ref(v_a_121_);
lean_inc(v_a_120_);
lean_inc_ref(v_a_119_);
lean_inc(v_a_118_);
lean_inc_ref(v_a_117_);
lean_inc(v_a_116_);
lean_inc_ref(v_a_115_);
lean_inc(v_a_114_);
lean_inc_ref(v_arg_172_);
v___x_228_ = lean_sym_dsimp(v_arg_172_, v_a_114_, v_a_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_);
if (lean_obj_tag(v___x_228_) == 0)
{
lean_object* v_a_229_; 
v_a_229_ = lean_ctor_get(v___x_228_, 0);
lean_inc(v_a_229_);
lean_dec_ref_known(v___x_228_, 1);
v_ar_181_ = v_a_229_;
v___y_182_ = v_a_114_;
v___y_183_ = v_a_115_;
v___y_184_ = v_a_116_;
v___y_185_ = v_a_117_;
v___y_186_ = v_a_118_;
v___y_187_ = v_a_119_;
v___y_188_ = v_a_120_;
v___y_189_ = v_a_121_;
v___y_190_ = v_a_122_;
goto v___jp_180_;
}
else
{
lean_del_object(v___x_178_);
lean_dec(v_a_176_);
lean_dec_ref_known(v_e_113_, 2);
return v___x_228_;
}
}
v___jp_230_:
{
lean_object* v___x_231_; 
v___x_231_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_231_, 0, v___x_125_);
v_ar_181_ = v___x_231_;
v___y_182_ = v_a_114_;
v___y_183_ = v_a_115_;
v___y_184_ = v_a_116_;
v___y_185_ = v_a_117_;
v___y_186_ = v_a_118_;
v___y_187_ = v_a_119_;
v___y_188_ = v_a_120_;
v___y_189_ = v_a_121_;
v___y_190_ = v_a_122_;
goto v___jp_180_;
}
}
}
else
{
lean_dec(v___x_174_);
lean_dec_ref_known(v_e_113_, 2);
return v___x_175_;
}
}
else
{
lean_object* v___x_240_; lean_object* v___x_241_; 
lean_dec_ref(v_e_113_);
v___x_240_ = lean_obj_once(&l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__3, &l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__3_once, _init_l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__3);
v___x_241_ = l_panic___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__1(v___x_240_, v_a_114_, v_a_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_);
return v___x_241_;
}
}
else
{
lean_object* v___x_242_; lean_object* v___x_243_; 
lean_dec_ref(v_e_113_);
v___x_242_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__4));
v___x_243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
return v___x_243_;
}
v___jp_126_:
{
lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_128_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_128_, 0, v_a_127_);
lean_ctor_set_uint8(v___x_128_, sizeof(void*)*1, v___x_125_);
v___x_129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_129_, 0, v___x_128_);
return v___x_129_;
}
v___jp_130_:
{
if (lean_obj_tag(v___y_131_) == 0)
{
lean_object* v_a_132_; 
v_a_132_ = lean_ctor_get(v___y_131_, 0);
lean_inc(v_a_132_);
lean_dec_ref_known(v___y_131_, 1);
v_a_127_ = v_a_132_;
goto v___jp_126_;
}
else
{
lean_object* v_a_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_140_; 
v_a_133_ = lean_ctor_get(v___y_131_, 0);
v_isSharedCheck_140_ = !lean_is_exclusive(v___y_131_);
if (v_isSharedCheck_140_ == 0)
{
v___x_135_ = v___y_131_;
v_isShared_136_ = v_isSharedCheck_140_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_a_133_);
lean_dec(v___y_131_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_140_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v___x_138_; 
if (v_isShared_136_ == 0)
{
v___x_138_ = v___x_135_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v_a_133_);
v___x_138_ = v_reuseFailAlloc_139_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
return v___x_138_;
}
}
}
}
v___jp_141_:
{
lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_143_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_143_, 0, v_a_142_);
lean_ctor_set_uint8(v___x_143_, sizeof(void*)*1, v___x_125_);
v___x_144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
return v___x_144_;
}
v___jp_145_:
{
if (lean_obj_tag(v___y_146_) == 0)
{
lean_object* v_a_147_; 
v_a_147_ = lean_ctor_get(v___y_146_, 0);
lean_inc(v_a_147_);
lean_dec_ref_known(v___y_146_, 1);
v_a_142_ = v_a_147_;
goto v___jp_141_;
}
else
{
lean_object* v_a_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_155_; 
v_a_148_ = lean_ctor_get(v___y_146_, 0);
v_isSharedCheck_155_ = !lean_is_exclusive(v___y_146_);
if (v_isSharedCheck_155_ == 0)
{
v___x_150_ = v___y_146_;
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_a_148_);
lean_dec(v___y_146_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_153_; 
if (v_isShared_151_ == 0)
{
v___x_153_ = v___x_150_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_a_148_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
return v___x_153_;
}
}
}
}
v___jp_156_:
{
lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_158_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_158_, 0, v_a_157_);
lean_ctor_set_uint8(v___x_158_, sizeof(void*)*1, v___x_125_);
v___x_159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_159_, 0, v___x_158_);
return v___x_159_;
}
v___jp_160_:
{
if (lean_obj_tag(v___y_161_) == 0)
{
lean_object* v_a_162_; 
v_a_162_ = lean_ctor_get(v___y_161_, 0);
lean_inc(v_a_162_);
lean_dec_ref_known(v___y_161_, 1);
v_a_157_ = v_a_162_;
goto v___jp_156_;
}
else
{
lean_object* v_a_163_; lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_170_; 
v_a_163_ = lean_ctor_get(v___y_161_, 0);
v_isSharedCheck_170_ = !lean_is_exclusive(v___y_161_);
if (v_isSharedCheck_170_ == 0)
{
v___x_165_ = v___y_161_;
v_isShared_166_ = v_isSharedCheck_170_;
goto v_resetjp_164_;
}
else
{
lean_inc(v_a_163_);
lean_dec(v___y_161_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_170_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
lean_object* v___x_168_; 
if (v_isShared_166_ == 0)
{
v___x_168_ = v___x_165_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v_a_163_);
v___x_168_ = v_reuseFailAlloc_169_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
return v___x_168_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_argsInfo_x3f_111_ = stack[0].m_obj;
lean_object* v_i_112_ = stack[1].m_obj;
lean_object* v_e_113_ = stack[2].m_obj;
lean_object* v_a_114_ = stack[3].m_obj;
lean_object* v_a_115_ = stack[4].m_obj;
lean_object* v_a_116_ = stack[5].m_obj;
lean_object* v_a_117_ = stack[6].m_obj;
lean_object* v_a_118_ = stack[7].m_obj;
lean_object* v_a_119_ = stack[8].m_obj;
lean_object* v_a_120_ = stack[9].m_obj;
lean_object* v_a_121_ = stack[10].m_obj;
lean_object* v_a_122_ = stack[11].m_obj;
lean_object* v_res_244_;
v_res_244_ = l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go(v_argsInfo_x3f_111_, v_i_112_, v_e_113_, v_a_114_, v_a_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_);
stack->m_obj
 = v_res_244_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___boxed(lean_object* v_argsInfo_x3f_245_, lean_object* v_i_246_, lean_object* v_e_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go(v_argsInfo_x3f_245_, v_i_246_, v_e_247_, v_a_248_, v_a_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_, v_a_254_, v_a_255_, v_a_256_);
lean_dec(v_a_256_);
lean_dec_ref(v_a_255_);
lean_dec(v_a_254_);
lean_dec_ref(v_a_253_);
lean_dec(v_a_252_);
lean_dec_ref(v_a_251_);
lean_dec(v_a_250_);
lean_dec_ref(v_a_249_);
lean_dec(v_a_248_);
lean_dec(v_i_246_);
lean_dec(v_argsInfo_x3f_245_);
return v_res_258_;
}
}
lean_object* l_Lean_Meta_Sym_DSimp_dsimpAppArgs(lean_object* v_e_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_){
_start:
{
lean_object* v_numArgs_270_; lean_object* v___x_271_; uint8_t v___x_272_; 
v_numArgs_270_ = l_Lean_Expr_getAppNumArgs(v_e_259_);
v___x_271_ = lean_unsigned_to_nat(0u);
v___x_272_ = lean_nat_dec_eq(v_numArgs_270_, v___x_271_);
if (v___x_272_ == 0)
{
lean_object* v_f_273_; lean_object* v___x_274_; 
v_f_273_ = l_Lean_Expr_getAppFn(v_e_259_);
v___x_274_ = l_Lean_Meta_Sym_getProofInstInfoOfExpr_x3f(v_f_273_, v_a_263_, v_a_264_, v_a_265_, v_a_266_, v_a_267_, v_a_268_);
if (lean_obj_tag(v___x_274_) == 0)
{
lean_object* v_a_275_; 
v_a_275_ = lean_ctor_get(v___x_274_, 0);
lean_inc(v_a_275_);
lean_dec_ref_known(v___x_274_, 1);
if (lean_obj_tag(v_a_275_) == 0)
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = lean_box(0);
v___x_277_ = l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go(v___x_276_, v_numArgs_270_, v_e_259_, v_a_260_, v_a_261_, v_a_262_, v_a_263_, v_a_264_, v_a_265_, v_a_266_, v_a_267_, v_a_268_);
lean_dec(v_numArgs_270_);
return v___x_277_;
}
else
{
lean_object* v_val_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_286_; 
v_val_278_ = lean_ctor_get(v_a_275_, 0);
v_isSharedCheck_286_ = !lean_is_exclusive(v_a_275_);
if (v_isSharedCheck_286_ == 0)
{
v___x_280_ = v_a_275_;
v_isShared_281_ = v_isSharedCheck_286_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_val_278_);
lean_dec(v_a_275_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_286_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_283_; 
if (v_isShared_281_ == 0)
{
v___x_283_ = v___x_280_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v_val_278_);
v___x_283_ = v_reuseFailAlloc_285_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
lean_object* v___x_284_; 
v___x_284_ = l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go(v___x_283_, v_numArgs_270_, v_e_259_, v_a_260_, v_a_261_, v_a_262_, v_a_263_, v_a_264_, v_a_265_, v_a_266_, v_a_267_, v_a_268_);
lean_dec(v_numArgs_270_);
lean_dec_ref(v___x_283_);
return v___x_284_;
}
}
}
}
else
{
lean_object* v_a_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_294_; 
lean_dec(v_numArgs_270_);
lean_dec_ref(v_e_259_);
v_a_287_ = lean_ctor_get(v___x_274_, 0);
v_isSharedCheck_294_ = !lean_is_exclusive(v___x_274_);
if (v_isSharedCheck_294_ == 0)
{
v___x_289_ = v___x_274_;
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_a_287_);
lean_dec(v___x_274_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_292_; 
if (v_isShared_290_ == 0)
{
v___x_292_ = v___x_289_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_a_287_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
}
else
{
lean_object* v___x_295_; lean_object* v___x_296_; 
lean_dec(v_numArgs_270_);
lean_dec_ref(v_e_259_);
v___x_295_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__4));
v___x_296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_296_, 0, v___x_295_);
return v___x_296_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_DSimp_dsimpAppArgs_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_259_ = stack[0].m_obj;
lean_object* v_a_260_ = stack[1].m_obj;
lean_object* v_a_261_ = stack[2].m_obj;
lean_object* v_a_262_ = stack[3].m_obj;
lean_object* v_a_263_ = stack[4].m_obj;
lean_object* v_a_264_ = stack[5].m_obj;
lean_object* v_a_265_ = stack[6].m_obj;
lean_object* v_a_266_ = stack[7].m_obj;
lean_object* v_a_267_ = stack[8].m_obj;
lean_object* v_a_268_ = stack[9].m_obj;
lean_object* v_res_297_;
v_res_297_ = l_Lean_Meta_Sym_DSimp_dsimpAppArgs(v_e_259_, v_a_260_, v_a_261_, v_a_262_, v_a_263_, v_a_264_, v_a_265_, v_a_266_, v_a_267_, v_a_268_);
stack->m_obj
 = v_res_297_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpAppArgs___boxed(lean_object* v_e_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Lean_Meta_Sym_DSimp_dsimpAppArgs(v_e_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_, v_a_304_, v_a_305_, v_a_306_, v_a_307_);
lean_dec(v_a_307_);
lean_dec_ref(v_a_306_);
lean_dec(v_a_305_);
lean_dec_ref(v_a_304_);
lean_dec(v_a_303_);
lean_dec_ref(v_a_302_);
lean_dec(v_a_301_);
lean_dec_ref(v_a_300_);
lean_dec(v_a_299_);
return v_res_309_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_DSimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_Result(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_ProofInstInfo(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_App(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Sym_DSimp_DSimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_DSimp_Result(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_ProofInstInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_DSimp_App(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_DSimp_DSimpM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_DSimp_Result(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_ProofInstInfo(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_DSimp_App(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_DSimp_DSimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_DSimp_Result(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_ProofInstInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_DSimp_App(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_DSimp_App(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_DSimp_App(builtin);
}
#ifdef __cplusplus
}
#endif

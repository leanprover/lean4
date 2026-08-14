// Lean compiler output
// Module: Lean.Elab.Tactic.VCGen.WPApp
// Imports: public import Lean.Meta.Sym.SymM import Std.WP.Basic
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
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_WPApp_Prog(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_WPApp_Prog___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_WPApp_M(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_WPApp_M___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_WPApp_Value(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_WPApp_Value___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_WPApp_Pred(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_WPApp_Pred___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_WPApp_EPred(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_WPApp_EPred___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_WPApp_instWP(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_WPApp_instWP___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_WPApp_prog(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_WPApp_prog___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_WPApp_post(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_WPApp_post___boxed(lean_object*);
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_isWPApp_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_isWPApp_x3f_spec__0___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_isWPApp_x3f_spec__0___closed__0_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_isWPApp_x3f_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "WP"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_isWPApp_x3f_spec__0___closed__1 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_isWPApp_x3f_spec__0___closed__1_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_isWPApp_x3f_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "wp"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_isWPApp_x3f_spec__0___closed__2 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_isWPApp_x3f_spec__0___closed__2_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_isWPApp_x3f_spec__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_isWPApp_x3f_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_isWPApp_x3f_spec__0___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_isWPApp_x3f_spec__0___closed__3_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_isWPApp_x3f_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(193, 201, 27, 53, 82, 85, 158, 17)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_isWPApp_x3f_spec__0___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_isWPApp_x3f_spec__0___closed__3_value_aux_1),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_isWPApp_x3f_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(124, 118, 39, 144, 78, 10, 170, 168)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_isWPApp_x3f_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_isWPApp_x3f_spec__0___closed__3_value_aux_2),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_isWPApp_x3f_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(182, 255, 127, 189, 81, 246, 28, 251)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_isWPApp_x3f_spec__0___closed__3 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_isWPApp_x3f_spec__0___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_isWPApp_x3f_spec__0(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_isWPApp_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_isWPApp_x3f___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_isWPApp_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_WPApp_Prog(lean_object* v_info_1_){
_start:
{
lean_object* v_args_2_; lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; 
v_args_2_ = lean_ctor_get(v_info_1_, 1);
v___x_3_ = l_Lean_instInhabitedExpr;
v___x_4_ = lean_unsigned_to_nat(0u);
v___x_5_ = lean_array_get_borrowed(v___x_3_, v_args_2_, v___x_4_);
lean_inc(v___x_5_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_WPApp_Prog___boxed(lean_object* v_info_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = l_Lean_Elab_Tactic_VCGen_WPApp_Prog(v_info_6_);
lean_dec_ref(v_info_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_WPApp_M(lean_object* v_info_8_){
_start:
{
lean_object* v_args_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; uint8_t v___x_13_; 
v_args_9_ = lean_ctor_get(v_info_8_, 1);
v___x_10_ = l_Lean_instInhabitedExpr;
v___x_11_ = lean_unsigned_to_nat(0u);
v___x_12_ = lean_array_get_borrowed(v___x_10_, v_args_9_, v___x_11_);
v___x_13_ = l_Lean_Expr_isApp(v___x_12_);
if (v___x_13_ == 0)
{
lean_inc(v___x_12_);
return v___x_12_;
}
else
{
lean_object* v___x_14_; 
v___x_14_ = l_Lean_Expr_appFn_x21(v___x_12_);
return v___x_14_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_WPApp_M___boxed(lean_object* v_info_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l_Lean_Elab_Tactic_VCGen_WPApp_M(v_info_15_);
lean_dec_ref(v_info_15_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_WPApp_Value(lean_object* v_info_17_){
_start:
{
lean_object* v_args_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; 
v_args_18_ = lean_ctor_get(v_info_17_, 1);
v___x_19_ = l_Lean_instInhabitedExpr;
v___x_20_ = lean_unsigned_to_nat(1u);
v___x_21_ = lean_array_get_borrowed(v___x_19_, v_args_18_, v___x_20_);
lean_inc(v___x_21_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_WPApp_Value___boxed(lean_object* v_info_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_Lean_Elab_Tactic_VCGen_WPApp_Value(v_info_22_);
lean_dec_ref(v_info_22_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_WPApp_Pred(lean_object* v_info_24_){
_start:
{
lean_object* v_args_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; 
v_args_25_ = lean_ctor_get(v_info_24_, 1);
v___x_26_ = l_Lean_instInhabitedExpr;
v___x_27_ = lean_unsigned_to_nat(2u);
v___x_28_ = lean_array_get_borrowed(v___x_26_, v_args_25_, v___x_27_);
lean_inc(v___x_28_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_WPApp_Pred___boxed(lean_object* v_info_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_Elab_Tactic_VCGen_WPApp_Pred(v_info_29_);
lean_dec_ref(v_info_29_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_WPApp_EPred(lean_object* v_info_31_){
_start:
{
lean_object* v_args_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v_args_32_ = lean_ctor_get(v_info_31_, 1);
v___x_33_ = l_Lean_instInhabitedExpr;
v___x_34_ = lean_unsigned_to_nat(3u);
v___x_35_ = lean_array_get_borrowed(v___x_33_, v_args_32_, v___x_34_);
lean_inc(v___x_35_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_WPApp_EPred___boxed(lean_object* v_info_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_Elab_Tactic_VCGen_WPApp_EPred(v_info_36_);
lean_dec_ref(v_info_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_WPApp_instWP(lean_object* v_info_38_){
_start:
{
lean_object* v_args_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v_args_39_ = lean_ctor_get(v_info_38_, 1);
v___x_40_ = l_Lean_instInhabitedExpr;
v___x_41_ = lean_unsigned_to_nat(6u);
v___x_42_ = lean_array_get_borrowed(v___x_40_, v_args_39_, v___x_41_);
lean_inc(v___x_42_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_WPApp_instWP___boxed(lean_object* v_info_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Lean_Elab_Tactic_VCGen_WPApp_instWP(v_info_43_);
lean_dec_ref(v_info_43_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_WPApp_prog(lean_object* v_info_45_){
_start:
{
lean_object* v_args_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v_args_46_ = lean_ctor_get(v_info_45_, 1);
v___x_47_ = l_Lean_instInhabitedExpr;
v___x_48_ = lean_unsigned_to_nat(7u);
v___x_49_ = lean_array_get_borrowed(v___x_47_, v_args_46_, v___x_48_);
lean_inc(v___x_49_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_WPApp_prog___boxed(lean_object* v_info_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_Elab_Tactic_VCGen_WPApp_prog(v_info_50_);
lean_dec_ref(v_info_50_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_WPApp_post(lean_object* v_info_52_){
_start:
{
lean_object* v_args_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v_args_53_ = lean_ctor_get(v_info_52_, 1);
v___x_54_ = l_Lean_instInhabitedExpr;
v___x_55_ = lean_unsigned_to_nat(8u);
v___x_56_ = lean_array_get_borrowed(v___x_54_, v_args_53_, v___x_55_);
lean_inc(v___x_56_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_WPApp_post___boxed(lean_object* v_info_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Lean_Elab_Tactic_VCGen_WPApp_post(v_info_57_);
lean_dec_ref(v_info_57_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_isWPApp_x3f_spec__0(lean_object* v_x_66_, lean_object* v_x_67_, lean_object* v_x_68_){
_start:
{
uint8_t v___y_70_; 
if (lean_obj_tag(v_x_66_) == 5)
{
lean_object* v_fn_79_; lean_object* v_arg_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v_fn_79_ = lean_ctor_get(v_x_66_, 0);
lean_inc_ref(v_fn_79_);
v_arg_80_ = lean_ctor_get(v_x_66_, 1);
lean_inc_ref(v_arg_80_);
lean_dec_ref_known(v_x_66_, 2);
v___x_81_ = lean_array_set(v_x_67_, v_x_68_, v_arg_80_);
v___x_82_ = lean_unsigned_to_nat(1u);
v___x_83_ = lean_nat_sub(v_x_68_, v___x_82_);
lean_dec(v_x_68_);
v_x_66_ = v_fn_79_;
v_x_67_ = v___x_81_;
v_x_68_ = v___x_83_;
goto _start;
}
else
{
lean_object* v___x_85_; uint8_t v___x_86_; 
lean_dec(v_x_68_);
v___x_85_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_isWPApp_x3f_spec__0___closed__3));
v___x_86_ = l_Lean_Expr_isConstOf(v_x_66_, v___x_85_);
if (v___x_86_ == 0)
{
v___y_70_ = v___x_86_;
goto v___jp_69_;
}
else
{
lean_object* v___x_87_; lean_object* v___x_88_; uint8_t v___x_89_; 
v___x_87_ = lean_unsigned_to_nat(10u);
v___x_88_ = lean_array_get_size(v_x_67_);
v___x_89_ = lean_nat_dec_le(v___x_87_, v___x_88_);
v___y_70_ = v___x_89_;
goto v___jp_69_;
}
}
v___jp_69_:
{
if (v___y_70_ == 0)
{
lean_object* v___x_71_; 
lean_dec_ref(v_x_67_);
lean_dec_ref(v_x_66_);
v___x_71_ = lean_box(0);
return v___x_71_;
}
else
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_72_ = lean_unsigned_to_nat(10u);
v___x_73_ = lean_unsigned_to_nat(0u);
v___x_74_ = l_Array_extract___redArg(v_x_67_, v___x_73_, v___x_72_);
v___x_75_ = lean_array_get_size(v_x_67_);
v___x_76_ = l_Array_extract___redArg(v_x_67_, v___x_72_, v___x_75_);
lean_dec_ref(v_x_67_);
v___x_77_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_77_, 0, v_x_66_);
lean_ctor_set(v___x_77_, 1, v___x_74_);
lean_ctor_set(v___x_77_, 2, v___x_76_);
v___x_78_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_78_, 0, v___x_77_);
return v___x_78_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_isWPApp_x3f___closed__0(void){
_start:
{
lean_object* v___x_90_; lean_object* v_dummy_91_; 
v___x_90_ = lean_box(0);
v_dummy_91_ = l_Lean_Expr_sort___override(v___x_90_);
return v_dummy_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_isWPApp_x3f(lean_object* v_rhs_92_){
_start:
{
lean_object* v_dummy_93_; lean_object* v_nargs_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v_dummy_93_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_isWPApp_x3f___closed__0, &l_Lean_Elab_Tactic_VCGen_isWPApp_x3f___closed__0_once, _init_l_Lean_Elab_Tactic_VCGen_isWPApp_x3f___closed__0);
v_nargs_94_ = l_Lean_Expr_getAppNumArgs(v_rhs_92_);
lean_inc(v_nargs_94_);
v___x_95_ = lean_mk_array(v_nargs_94_, v_dummy_93_);
v___x_96_ = lean_unsigned_to_nat(1u);
v___x_97_ = lean_nat_sub(v_nargs_94_, v___x_96_);
lean_dec(v_nargs_94_);
v___x_98_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_isWPApp_x3f_spec__0(v_rhs_92_, v___x_95_, v___x_97_);
return v___x_98_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* runtime_initialize_Std_WP_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_VCGen_WPApp(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_WP_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_VCGen_WPApp(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* initialize_Std_WP_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_VCGen_WPApp(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_WP_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_VCGen_WPApp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_VCGen_WPApp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_VCGen_WPApp(builtin);
}
#ifdef __cplusplus
}
#endif

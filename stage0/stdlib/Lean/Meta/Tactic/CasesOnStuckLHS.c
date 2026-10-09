// Lean compiler output
// Module: Lean.Meta.Tactic.CasesOnStuckLHS
// Imports: public import Lean.Meta.Basic import Lean.ProjFns import Lean.Meta.Tactic.Cases
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getProjectionFnInfo_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Expr_constName_x21(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_RecursorVal_getMajorIdx(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_consumeMData(lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchEqHEqLHS_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_cases(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_casesOnStuckLHS_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_casesOnStuckLHS_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_casesOnStuckLHS_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_casesOnStuckLHS_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_casesOnStuckLHS_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_casesOnStuckLHS_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_casesOnStuckLHS___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "'casesOnStuckLHS' failed"};
static const lean_object* l_Lean_Meta_casesOnStuckLHS___closed__0 = (const lean_object*)&l_Lean_Meta_casesOnStuckLHS___closed__0_value;
static lean_once_cell_t l_Lean_Meta_casesOnStuckLHS___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_casesOnStuckLHS___closed__1;
static const lean_array_object l_Lean_Meta_casesOnStuckLHS___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_casesOnStuckLHS___closed__2 = (const lean_object*)&l_Lean_Meta_casesOnStuckLHS___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_casesOnStuckLHS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_casesOnStuckLHS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_casesOnStuckLHS_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_casesOnStuckLHS_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_casesOnStuckLHS_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_casesOnStuckLHS_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f_spec__0___redArg(lean_object* v_declName_1_, lean_object* v___y_2_){
_start:
{
lean_object* v___x_4_; lean_object* v_env_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_4_ = lean_st_ref_get(v___y_2_);
v_env_5_ = lean_ctor_get(v___x_4_, 0);
lean_inc_ref(v_env_5_);
lean_dec(v___x_4_);
v___x_6_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_5_, v_declName_1_);
v___x_7_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7_, 0, v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT void l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1_ = stack[0].m_obj;
lean_object* v___y_2_ = stack[1].m_obj;
lean_object* v_res_8_;
v_res_8_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f_spec__0___redArg(v_declName_1_, v___y_2_);
stack->m_obj
 = v_res_8_;
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f_spec__0___redArg___boxed(lean_object* v_declName_9_, lean_object* v___y_10_, lean_object* v___y_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f_spec__0___redArg(v_declName_9_, v___y_10_);
lean_dec(v___y_10_);
return v_res_12_;
}
}
lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f_spec__0(lean_object* v_declName_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f_spec__0___redArg(v_declName_13_, v___y_17_);
return v___x_19_;
}
}
LEAN_EXPORT void l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_13_ = stack[0].m_obj;
lean_object* v___y_14_ = stack[1].m_obj;
lean_object* v___y_15_ = stack[2].m_obj;
lean_object* v___y_16_ = stack[3].m_obj;
lean_object* v___y_17_ = stack[4].m_obj;
lean_object* v_res_20_;
v_res_20_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f_spec__0(v_declName_13_, v___y_14_, v___y_15_, v___y_16_, v___y_17_);
stack->m_obj
 = v_res_20_;
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f_spec__0___boxed(lean_object* v_declName_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f_spec__0(v_declName_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_);
lean_dec(v___y_25_);
lean_dec_ref(v___y_24_);
lean_dec(v___y_23_);
lean_dec_ref(v___y_22_);
return v_res_27_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f___closed__0(void){
_start:
{
lean_object* v___x_28_; lean_object* v_dummy_29_; 
v___x_28_ = lean_box(0);
v_dummy_29_ = l_Lean_Expr_sort___override(v___x_28_);
return v_dummy_29_;
}
}
lean_object* l___private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f(lean_object* v_e_30_, lean_object* v_a_31_, lean_object* v_a_32_, lean_object* v_a_33_, lean_object* v_a_34_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Lean_Expr_getAppFn(v_e_30_);
if (lean_obj_tag(v___x_39_) == 11)
{
lean_object* v_struct_40_; 
lean_dec_ref(v_e_30_);
v_struct_40_ = lean_ctor_get(v___x_39_, 2);
lean_inc_ref(v_struct_40_);
lean_dec_ref_known(v___x_39_, 3);
v_e_30_ = v_struct_40_;
goto _start;
}
else
{
uint8_t v___x_42_; 
v___x_42_ = l_Lean_Expr_isConst(v___x_39_);
if (v___x_42_ == 0)
{
lean_object* v___x_43_; lean_object* v___x_44_; 
lean_dec_ref(v___x_39_);
lean_dec_ref(v_e_30_);
v___x_43_ = lean_box(0);
v___x_44_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_44_, 0, v___x_43_);
return v___x_44_;
}
else
{
lean_object* v___x_45_; uint8_t v___x_46_; lean_object* v_declName_47_; lean_object* v_dummy_48_; lean_object* v_nargs_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v_args_53_; lean_object* v___x_54_; 
v___x_45_ = l_Lean_instInhabitedExpr;
v___x_46_ = 0;
v_declName_47_ = l_Lean_Expr_constName_x21(v___x_39_);
v_dummy_48_ = lean_obj_once(&l___private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f___closed__0, &l___private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f___closed__0);
v_nargs_49_ = l_Lean_Expr_getAppNumArgs(v_e_30_);
lean_inc(v_nargs_49_);
v___x_50_ = lean_mk_array(v_nargs_49_, v_dummy_48_);
v___x_51_ = lean_unsigned_to_nat(1u);
v___x_52_ = lean_nat_sub(v_nargs_49_, v___x_51_);
lean_dec(v_nargs_49_);
v_args_53_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_30_, v___x_50_, v___x_52_);
v___x_54_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f_spec__0___redArg(v_declName_47_, v_a_34_);
if (lean_obj_tag(v___x_54_) == 0)
{
lean_object* v_a_55_; lean_object* v___x_57_; uint8_t v_isShared_58_; uint8_t v_isSharedCheck_100_; 
v_a_55_ = lean_ctor_get(v___x_54_, 0);
v_isSharedCheck_100_ = !lean_is_exclusive(v___x_54_);
if (v_isSharedCheck_100_ == 0)
{
v___x_57_ = v___x_54_;
v_isShared_58_ = v_isSharedCheck_100_;
goto v_resetjp_56_;
}
else
{
lean_inc(v_a_55_);
lean_dec(v___x_54_);
v___x_57_ = lean_box(0);
v_isShared_58_ = v_isSharedCheck_100_;
goto v_resetjp_56_;
}
v_resetjp_56_:
{
if (lean_obj_tag(v_a_55_) == 0)
{
if (lean_obj_tag(v___x_39_) == 4)
{
lean_object* v_declName_59_; lean_object* v___x_60_; lean_object* v_env_61_; lean_object* v___x_62_; 
v_declName_59_ = lean_ctor_get(v___x_39_, 0);
lean_inc(v_declName_59_);
lean_dec_ref_known(v___x_39_, 2);
v___x_60_ = lean_st_ref_get(v_a_34_);
v_env_61_ = lean_ctor_get(v___x_60_, 0);
lean_inc_ref(v_env_61_);
lean_dec(v___x_60_);
v___x_62_ = l_Lean_Environment_find_x3f(v_env_61_, v_declName_59_, v___x_46_);
if (lean_obj_tag(v___x_62_) == 0)
{
lean_del_object(v___x_57_);
lean_dec_ref(v_args_53_);
goto v___jp_36_;
}
else
{
lean_object* v_val_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_89_; 
v_val_63_ = lean_ctor_get(v___x_62_, 0);
v_isSharedCheck_89_ = !lean_is_exclusive(v___x_62_);
if (v_isSharedCheck_89_ == 0)
{
v___x_65_ = v___x_62_;
v_isShared_66_ = v_isSharedCheck_89_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_val_63_);
lean_dec(v___x_62_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_89_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
if (lean_obj_tag(v_val_63_) == 7)
{
lean_object* v_val_67_; lean_object* v___x_68_; lean_object* v___x_69_; uint8_t v___x_70_; 
v_val_67_ = lean_ctor_get(v_val_63_, 0);
lean_inc_ref(v_val_67_);
lean_dec_ref_known(v_val_63_, 1);
v___x_68_ = lean_array_get_size(v_args_53_);
v___x_69_ = l_Lean_RecursorVal_getMajorIdx(v_val_67_);
lean_dec_ref(v_val_67_);
v___x_70_ = lean_nat_dec_le(v___x_68_, v___x_69_);
if (v___x_70_ == 0)
{
lean_object* v___x_71_; lean_object* v___x_72_; uint8_t v___x_73_; 
v___x_71_ = lean_array_get(v___x_45_, v_args_53_, v___x_69_);
lean_dec(v___x_69_);
lean_dec_ref(v_args_53_);
v___x_72_ = l_Lean_Expr_consumeMData(v___x_71_);
lean_dec(v___x_71_);
v___x_73_ = l_Lean_Expr_isFVar(v___x_72_);
if (v___x_73_ == 0)
{
lean_object* v___x_74_; lean_object* v___x_76_; 
lean_dec_ref(v___x_72_);
lean_del_object(v___x_65_);
v___x_74_ = lean_box(0);
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 0, v___x_74_);
v___x_76_ = v___x_57_;
goto v_reusejp_75_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_77_, 0, v___x_74_);
v___x_76_ = v_reuseFailAlloc_77_;
goto v_reusejp_75_;
}
v_reusejp_75_:
{
return v___x_76_;
}
}
else
{
lean_object* v___x_78_; lean_object* v___x_80_; 
v___x_78_ = l_Lean_Expr_fvarId_x21(v___x_72_);
lean_dec_ref(v___x_72_);
if (v_isShared_66_ == 0)
{
lean_ctor_set(v___x_65_, 0, v___x_78_);
v___x_80_ = v___x_65_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_84_; 
v_reuseFailAlloc_84_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_84_, 0, v___x_78_);
v___x_80_ = v_reuseFailAlloc_84_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
lean_object* v___x_82_; 
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 0, v___x_80_);
v___x_82_ = v___x_57_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v___x_80_);
v___x_82_ = v_reuseFailAlloc_83_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
return v___x_82_;
}
}
}
}
else
{
lean_object* v___x_85_; lean_object* v___x_87_; 
lean_dec(v___x_69_);
lean_del_object(v___x_65_);
lean_dec_ref(v_args_53_);
v___x_85_ = lean_box(0);
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 0, v___x_85_);
v___x_87_ = v___x_57_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v___x_85_);
v___x_87_ = v_reuseFailAlloc_88_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
return v___x_87_;
}
}
}
else
{
lean_del_object(v___x_65_);
lean_dec(v_val_63_);
lean_del_object(v___x_57_);
lean_dec_ref(v_args_53_);
goto v___jp_36_;
}
}
}
}
else
{
lean_del_object(v___x_57_);
lean_dec_ref(v_args_53_);
lean_dec_ref(v___x_39_);
goto v___jp_36_;
}
}
else
{
lean_object* v_val_90_; lean_object* v_numParams_91_; lean_object* v___x_92_; uint8_t v___x_93_; 
lean_dec_ref(v___x_39_);
v_val_90_ = lean_ctor_get(v_a_55_, 0);
lean_inc(v_val_90_);
lean_dec_ref_known(v_a_55_, 1);
v_numParams_91_ = lean_ctor_get(v_val_90_, 1);
lean_inc(v_numParams_91_);
lean_dec(v_val_90_);
v___x_92_ = lean_array_get_size(v_args_53_);
v___x_93_ = lean_nat_dec_lt(v_numParams_91_, v___x_92_);
if (v___x_93_ == 0)
{
lean_object* v___x_94_; lean_object* v___x_96_; 
lean_dec(v_numParams_91_);
lean_dec_ref(v_args_53_);
v___x_94_ = lean_box(0);
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 0, v___x_94_);
v___x_96_ = v___x_57_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_97_; 
v_reuseFailAlloc_97_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_97_, 0, v___x_94_);
v___x_96_ = v_reuseFailAlloc_97_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
return v___x_96_;
}
}
else
{
lean_object* v___x_98_; 
lean_del_object(v___x_57_);
v___x_98_ = lean_array_get(v___x_45_, v_args_53_, v_numParams_91_);
lean_dec(v_numParams_91_);
lean_dec_ref(v_args_53_);
v_e_30_ = v___x_98_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_101_; lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_108_; 
lean_dec_ref(v_args_53_);
lean_dec_ref(v___x_39_);
v_a_101_ = lean_ctor_get(v___x_54_, 0);
v_isSharedCheck_108_ = !lean_is_exclusive(v___x_54_);
if (v_isSharedCheck_108_ == 0)
{
v___x_103_ = v___x_54_;
v_isShared_104_ = v_isSharedCheck_108_;
goto v_resetjp_102_;
}
else
{
lean_inc(v_a_101_);
lean_dec(v___x_54_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_108_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
lean_object* v___x_106_; 
if (v_isShared_104_ == 0)
{
v___x_106_ = v___x_103_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v_a_101_);
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
v___jp_36_:
{
lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_37_ = lean_box(0);
v___x_38_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_38_, 0, v___x_37_);
return v___x_38_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_30_ = stack[0].m_obj;
lean_object* v_a_31_ = stack[1].m_obj;
lean_object* v_a_32_ = stack[2].m_obj;
lean_object* v_a_33_ = stack[3].m_obj;
lean_object* v_a_34_ = stack[4].m_obj;
lean_object* v_res_109_;
v_res_109_ = l___private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f(v_e_30_, v_a_31_, v_a_32_, v_a_33_, v_a_34_);
stack->m_obj
 = v_res_109_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f___boxed(lean_object* v_e_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l___private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f(v_e_110_, v_a_111_, v_a_112_, v_a_113_, v_a_114_);
lean_dec(v_a_114_);
lean_dec_ref(v_a_113_);
lean_dec(v_a_112_);
lean_dec_ref(v_a_111_);
return v_res_116_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_casesOnStuckLHS_spec__1(size_t v_sz_117_, size_t v_i_118_, lean_object* v_bs_119_){
_start:
{
uint8_t v___x_120_; 
v___x_120_ = lean_usize_dec_lt(v_i_118_, v_sz_117_);
if (v___x_120_ == 0)
{
return v_bs_119_;
}
else
{
lean_object* v_v_121_; lean_object* v_toInductionSubgoal_122_; lean_object* v_mvarId_123_; lean_object* v___x_124_; lean_object* v_bs_x27_125_; size_t v___x_126_; size_t v___x_127_; lean_object* v___x_128_; 
v_v_121_ = lean_array_uget_borrowed(v_bs_119_, v_i_118_);
v_toInductionSubgoal_122_ = lean_ctor_get(v_v_121_, 0);
v_mvarId_123_ = lean_ctor_get(v_toInductionSubgoal_122_, 0);
lean_inc(v_mvarId_123_);
v___x_124_ = lean_unsigned_to_nat(0u);
v_bs_x27_125_ = lean_array_uset(v_bs_119_, v_i_118_, v___x_124_);
v___x_126_ = ((size_t)1ULL);
v___x_127_ = lean_usize_add(v_i_118_, v___x_126_);
v___x_128_ = lean_array_uset(v_bs_x27_125_, v_i_118_, v_mvarId_123_);
v_i_118_ = v___x_127_;
v_bs_119_ = v___x_128_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_casesOnStuckLHS_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_117_ = stack[0].m_num;
size_t v_i_118_ = stack[1].m_num;
lean_object* v_bs_119_ = stack[2].m_obj;
lean_object* v_res_130_;
v_res_130_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_casesOnStuckLHS_spec__1(v_sz_117_, v_i_118_, v_bs_119_);
stack->m_obj
 = v_res_130_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_casesOnStuckLHS_spec__1___boxed(lean_object* v_sz_131_, lean_object* v_i_132_, lean_object* v_bs_133_){
_start:
{
size_t v_sz_boxed_134_; size_t v_i_boxed_135_; lean_object* v_res_136_; 
v_sz_boxed_134_ = lean_unbox_usize(v_sz_131_);
lean_dec(v_sz_131_);
v_i_boxed_135_ = lean_unbox_usize(v_i_132_);
lean_dec(v_i_132_);
v_res_136_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_casesOnStuckLHS_spec__1(v_sz_boxed_134_, v_i_boxed_135_, v_bs_133_);
return v_res_136_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_casesOnStuckLHS_spec__0_spec__0(lean_object* v_msgData_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_){
_start:
{
lean_object* v___x_143_; lean_object* v_env_144_; uint8_t v___x_145_; lean_object* v_env_146_; lean_object* v___x_147_; lean_object* v_toCold_148_; lean_object* v_mctx_149_; lean_object* v_lctx_150_; lean_object* v_options_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_143_ = lean_st_ref_get(v___y_141_);
v_env_144_ = lean_ctor_get(v___x_143_, 0);
lean_inc_ref(v_env_144_);
lean_dec(v___x_143_);
v___x_145_ = 0;
v_env_146_ = l_Lean_Environment_setRecordingDeps(v_env_144_, v___x_145_);
v___x_147_ = lean_st_ref_get(v___y_139_);
v_toCold_148_ = lean_ctor_get(v___y_140_, 0);
v_mctx_149_ = lean_ctor_get(v___x_147_, 0);
lean_inc_ref(v_mctx_149_);
lean_dec(v___x_147_);
v_lctx_150_ = lean_ctor_get(v___y_138_, 2);
v_options_151_ = lean_ctor_get(v_toCold_148_, 2);
lean_inc_ref(v_options_151_);
lean_inc_ref(v_lctx_150_);
v___x_152_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_152_, 0, v_env_146_);
lean_ctor_set(v___x_152_, 1, v_mctx_149_);
lean_ctor_set(v___x_152_, 2, v_lctx_150_);
lean_ctor_set(v___x_152_, 3, v_options_151_);
v___x_153_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_153_, 0, v___x_152_);
lean_ctor_set(v___x_153_, 1, v_msgData_137_);
v___x_154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_154_, 0, v___x_153_);
return v___x_154_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_casesOnStuckLHS_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_137_ = stack[0].m_obj;
lean_object* v___y_138_ = stack[1].m_obj;
lean_object* v___y_139_ = stack[2].m_obj;
lean_object* v___y_140_ = stack[3].m_obj;
lean_object* v___y_141_ = stack[4].m_obj;
lean_object* v_res_155_;
v_res_155_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_casesOnStuckLHS_spec__0_spec__0(v_msgData_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_);
stack->m_obj
 = v_res_155_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_casesOnStuckLHS_spec__0_spec__0___boxed(lean_object* v_msgData_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_casesOnStuckLHS_spec__0_spec__0(v_msgData_156_, v___y_157_, v___y_158_, v___y_159_, v___y_160_);
lean_dec(v___y_160_);
lean_dec_ref(v___y_159_);
lean_dec(v___y_158_);
lean_dec_ref(v___y_157_);
return v_res_162_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_casesOnStuckLHS_spec__0___redArg(lean_object* v_msg_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_){
_start:
{
lean_object* v_ref_169_; lean_object* v___x_170_; lean_object* v_a_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_179_; 
v_ref_169_ = lean_ctor_get(v___y_166_, 2);
v___x_170_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_casesOnStuckLHS_spec__0_spec__0(v_msg_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_);
v_a_171_ = lean_ctor_get(v___x_170_, 0);
v_isSharedCheck_179_ = !lean_is_exclusive(v___x_170_);
if (v_isSharedCheck_179_ == 0)
{
v___x_173_ = v___x_170_;
v_isShared_174_ = v_isSharedCheck_179_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_a_171_);
lean_dec(v___x_170_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_179_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___x_175_; lean_object* v___x_177_; 
lean_inc(v_ref_169_);
v___x_175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_175_, 0, v_ref_169_);
lean_ctor_set(v___x_175_, 1, v_a_171_);
if (v_isShared_174_ == 0)
{
lean_ctor_set_tag(v___x_173_, 1);
lean_ctor_set(v___x_173_, 0, v___x_175_);
v___x_177_ = v___x_173_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v___x_175_);
v___x_177_ = v_reuseFailAlloc_178_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
return v___x_177_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_casesOnStuckLHS_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_163_ = stack[0].m_obj;
lean_object* v___y_164_ = stack[1].m_obj;
lean_object* v___y_165_ = stack[2].m_obj;
lean_object* v___y_166_ = stack[3].m_obj;
lean_object* v___y_167_ = stack[4].m_obj;
lean_object* v_res_180_;
v_res_180_ = l_Lean_throwError___at___00Lean_Meta_casesOnStuckLHS_spec__0___redArg(v_msg_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_);
stack->m_obj
 = v_res_180_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_casesOnStuckLHS_spec__0___redArg___boxed(lean_object* v_msg_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Lean_throwError___at___00Lean_Meta_casesOnStuckLHS_spec__0___redArg(v_msg_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_);
lean_dec(v___y_185_);
lean_dec_ref(v___y_184_);
lean_dec(v___y_183_);
lean_dec_ref(v___y_182_);
return v_res_187_;
}
}
static lean_object* _init_l_Lean_Meta_casesOnStuckLHS___closed__1(void){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_189_ = ((lean_object*)(l_Lean_Meta_casesOnStuckLHS___closed__0));
v___x_190_ = l_Lean_stringToMessageData(v___x_189_);
return v___x_190_;
}
}
lean_object* l_Lean_Meta_casesOnStuckLHS(lean_object* v_mvarId_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_){
_start:
{
lean_object* v___y_200_; lean_object* v___y_201_; lean_object* v___y_202_; lean_object* v___y_203_; lean_object* v___x_206_; 
lean_inc(v_mvarId_193_);
v___x_206_ = l_Lean_MVarId_getType(v_mvarId_193_, v_a_194_, v_a_195_, v_a_196_, v_a_197_);
if (lean_obj_tag(v___x_206_) == 0)
{
lean_object* v_a_207_; lean_object* v___x_208_; 
v_a_207_ = lean_ctor_get(v___x_206_, 0);
lean_inc(v_a_207_);
lean_dec_ref_known(v___x_206_, 1);
v___x_208_ = l_Lean_Meta_matchEqHEqLHS_x3f(v_a_207_, v_a_194_, v_a_195_, v_a_196_, v_a_197_);
if (lean_obj_tag(v___x_208_) == 0)
{
lean_object* v_a_209_; 
v_a_209_ = lean_ctor_get(v___x_208_, 0);
lean_inc(v_a_209_);
lean_dec_ref_known(v___x_208_, 1);
if (lean_obj_tag(v_a_209_) == 1)
{
lean_object* v_val_210_; lean_object* v_snd_211_; lean_object* v___x_212_; 
v_val_210_ = lean_ctor_get(v_a_209_, 0);
lean_inc(v_val_210_);
lean_dec_ref_known(v_a_209_, 1);
v_snd_211_ = lean_ctor_get(v_val_210_, 1);
lean_inc(v_snd_211_);
lean_dec(v_val_210_);
v___x_212_ = l___private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f(v_snd_211_, v_a_194_, v_a_195_, v_a_196_, v_a_197_);
if (lean_obj_tag(v___x_212_) == 0)
{
lean_object* v_a_213_; 
v_a_213_ = lean_ctor_get(v___x_212_, 0);
lean_inc(v_a_213_);
lean_dec_ref_known(v___x_212_, 1);
if (lean_obj_tag(v_a_213_) == 1)
{
lean_object* v_val_214_; lean_object* v___x_215_; uint8_t v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v_val_214_ = lean_ctor_get(v_a_213_, 0);
lean_inc(v_val_214_);
lean_dec_ref_known(v_a_213_, 1);
v___x_215_ = ((lean_object*)(l_Lean_Meta_casesOnStuckLHS___closed__2));
v___x_216_ = 0;
v___x_217_ = lean_box(0);
v___x_218_ = l_Lean_MVarId_cases(v_mvarId_193_, v_val_214_, v___x_215_, v___x_216_, v___x_217_, v_a_194_, v_a_195_, v_a_196_, v_a_197_);
if (lean_obj_tag(v___x_218_) == 0)
{
lean_object* v_a_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_229_; 
v_a_219_ = lean_ctor_get(v___x_218_, 0);
v_isSharedCheck_229_ = !lean_is_exclusive(v___x_218_);
if (v_isSharedCheck_229_ == 0)
{
v___x_221_ = v___x_218_;
v_isShared_222_ = v_isSharedCheck_229_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_a_219_);
lean_dec(v___x_218_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_229_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
size_t v_sz_223_; size_t v___x_224_; lean_object* v___x_225_; lean_object* v___x_227_; 
v_sz_223_ = lean_array_size(v_a_219_);
v___x_224_ = ((size_t)0ULL);
v___x_225_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_casesOnStuckLHS_spec__1(v_sz_223_, v___x_224_, v_a_219_);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 0, v___x_225_);
v___x_227_ = v___x_221_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v___x_225_);
v___x_227_ = v_reuseFailAlloc_228_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
return v___x_227_;
}
}
}
else
{
lean_object* v_a_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_237_; 
v_a_230_ = lean_ctor_get(v___x_218_, 0);
v_isSharedCheck_237_ = !lean_is_exclusive(v___x_218_);
if (v_isSharedCheck_237_ == 0)
{
v___x_232_ = v___x_218_;
v_isShared_233_ = v_isSharedCheck_237_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_a_230_);
lean_dec(v___x_218_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_237_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v___x_235_; 
if (v_isShared_233_ == 0)
{
v___x_235_ = v___x_232_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v_a_230_);
v___x_235_ = v_reuseFailAlloc_236_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
return v___x_235_;
}
}
}
}
else
{
lean_dec(v_a_213_);
lean_dec(v_mvarId_193_);
v___y_200_ = v_a_194_;
v___y_201_ = v_a_195_;
v___y_202_ = v_a_196_;
v___y_203_ = v_a_197_;
goto v___jp_199_;
}
}
else
{
lean_object* v_a_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_245_; 
lean_dec(v_mvarId_193_);
v_a_238_ = lean_ctor_get(v___x_212_, 0);
v_isSharedCheck_245_ = !lean_is_exclusive(v___x_212_);
if (v_isSharedCheck_245_ == 0)
{
v___x_240_ = v___x_212_;
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_a_238_);
lean_dec(v___x_212_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_243_; 
if (v_isShared_241_ == 0)
{
v___x_243_ = v___x_240_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_a_238_);
v___x_243_ = v_reuseFailAlloc_244_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
return v___x_243_;
}
}
}
}
else
{
lean_dec(v_a_209_);
lean_dec(v_mvarId_193_);
v___y_200_ = v_a_194_;
v___y_201_ = v_a_195_;
v___y_202_ = v_a_196_;
v___y_203_ = v_a_197_;
goto v___jp_199_;
}
}
else
{
lean_object* v_a_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_253_; 
lean_dec(v_mvarId_193_);
v_a_246_ = lean_ctor_get(v___x_208_, 0);
v_isSharedCheck_253_ = !lean_is_exclusive(v___x_208_);
if (v_isSharedCheck_253_ == 0)
{
v___x_248_ = v___x_208_;
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_a_246_);
lean_dec(v___x_208_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_251_; 
if (v_isShared_249_ == 0)
{
v___x_251_ = v___x_248_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v_a_246_);
v___x_251_ = v_reuseFailAlloc_252_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
return v___x_251_;
}
}
}
}
else
{
lean_object* v_a_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_261_; 
lean_dec(v_mvarId_193_);
v_a_254_ = lean_ctor_get(v___x_206_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v___x_206_);
if (v_isSharedCheck_261_ == 0)
{
v___x_256_ = v___x_206_;
v_isShared_257_ = v_isSharedCheck_261_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_a_254_);
lean_dec(v___x_206_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_261_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v___x_259_; 
if (v_isShared_257_ == 0)
{
v___x_259_ = v___x_256_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v_a_254_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
}
v___jp_199_:
{
lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_204_ = lean_obj_once(&l_Lean_Meta_casesOnStuckLHS___closed__1, &l_Lean_Meta_casesOnStuckLHS___closed__1_once, _init_l_Lean_Meta_casesOnStuckLHS___closed__1);
v___x_205_ = l_Lean_throwError___at___00Lean_Meta_casesOnStuckLHS_spec__0___redArg(v___x_204_, v___y_200_, v___y_201_, v___y_202_, v___y_203_);
return v___x_205_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_casesOnStuckLHS_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_193_ = stack[0].m_obj;
lean_object* v_a_194_ = stack[1].m_obj;
lean_object* v_a_195_ = stack[2].m_obj;
lean_object* v_a_196_ = stack[3].m_obj;
lean_object* v_a_197_ = stack[4].m_obj;
lean_object* v_res_262_;
v_res_262_ = l_Lean_Meta_casesOnStuckLHS(v_mvarId_193_, v_a_194_, v_a_195_, v_a_196_, v_a_197_);
stack->m_obj
 = v_res_262_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_casesOnStuckLHS___boxed(lean_object* v_mvarId_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l_Lean_Meta_casesOnStuckLHS(v_mvarId_263_, v_a_264_, v_a_265_, v_a_266_, v_a_267_);
lean_dec(v_a_267_);
lean_dec_ref(v_a_266_);
lean_dec(v_a_265_);
lean_dec_ref(v_a_264_);
return v_res_269_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_casesOnStuckLHS_spec__0(lean_object* v_00_u03b1_270_, lean_object* v_msg_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_){
_start:
{
lean_object* v___x_277_; 
v___x_277_ = l_Lean_throwError___at___00Lean_Meta_casesOnStuckLHS_spec__0___redArg(v_msg_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_);
return v___x_277_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_casesOnStuckLHS_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_271_ = stack[1].m_obj;
lean_object* v___y_272_ = stack[2].m_obj;
lean_object* v___y_273_ = stack[3].m_obj;
lean_object* v___y_274_ = stack[4].m_obj;
lean_object* v___y_275_ = stack[5].m_obj;
lean_object* v_res_278_;
v_res_278_ = l_Lean_throwError___at___00Lean_Meta_casesOnStuckLHS_spec__0(lean_box(0), v_msg_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_);
stack->m_obj
 = v_res_278_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_casesOnStuckLHS_spec__0___boxed(lean_object* v_00_u03b1_279_, lean_object* v_msg_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Lean_throwError___at___00Lean_Meta_casesOnStuckLHS_spec__0(v_00_u03b1_279_, v_msg_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_);
lean_dec(v___y_284_);
lean_dec_ref(v___y_283_);
lean_dec(v___y_282_);
lean_dec_ref(v___y_281_);
return v_res_286_;
}
}
lean_object* l_Lean_Meta_casesOnStuckLHS_x3f(lean_object* v_mvarId_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = l_Lean_Meta_casesOnStuckLHS(v_mvarId_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_);
if (lean_obj_tag(v___x_293_) == 0)
{
lean_object* v_a_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_302_; 
v_a_294_ = lean_ctor_get(v___x_293_, 0);
v_isSharedCheck_302_ = !lean_is_exclusive(v___x_293_);
if (v_isSharedCheck_302_ == 0)
{
v___x_296_ = v___x_293_;
v_isShared_297_ = v_isSharedCheck_302_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_a_294_);
lean_dec(v___x_293_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_302_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___x_298_; lean_object* v___x_300_; 
v___x_298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_298_, 0, v_a_294_);
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 0, v___x_298_);
v___x_300_ = v___x_296_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v___x_298_);
v___x_300_ = v_reuseFailAlloc_301_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
return v___x_300_;
}
}
}
else
{
lean_object* v_a_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_318_; 
v_a_303_ = lean_ctor_get(v___x_293_, 0);
v_isSharedCheck_318_ = !lean_is_exclusive(v___x_293_);
if (v_isSharedCheck_318_ == 0)
{
v___x_305_ = v___x_293_;
v_isShared_306_ = v_isSharedCheck_318_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_a_303_);
lean_dec(v___x_293_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_318_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
uint8_t v___y_308_; uint8_t v___x_316_; 
v___x_316_ = l_Lean_Exception_isInterrupt(v_a_303_);
if (v___x_316_ == 0)
{
uint8_t v___x_317_; 
lean_inc(v_a_303_);
v___x_317_ = l_Lean_Exception_isRuntime(v_a_303_);
v___y_308_ = v___x_317_;
goto v___jp_307_;
}
else
{
v___y_308_ = v___x_316_;
goto v___jp_307_;
}
v___jp_307_:
{
if (v___y_308_ == 0)
{
lean_object* v___x_309_; lean_object* v___x_311_; 
lean_dec(v_a_303_);
v___x_309_ = lean_box(0);
if (v_isShared_306_ == 0)
{
lean_ctor_set_tag(v___x_305_, 0);
lean_ctor_set(v___x_305_, 0, v___x_309_);
v___x_311_ = v___x_305_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v___x_309_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
}
}
else
{
lean_object* v___x_314_; 
if (v_isShared_306_ == 0)
{
v___x_314_ = v___x_305_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_a_303_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_casesOnStuckLHS_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_287_ = stack[0].m_obj;
lean_object* v_a_288_ = stack[1].m_obj;
lean_object* v_a_289_ = stack[2].m_obj;
lean_object* v_a_290_ = stack[3].m_obj;
lean_object* v_a_291_ = stack[4].m_obj;
lean_object* v_res_319_;
v_res_319_ = l_Lean_Meta_casesOnStuckLHS_x3f(v_mvarId_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_);
stack->m_obj
 = v_res_319_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_casesOnStuckLHS_x3f___boxed(lean_object* v_mvarId_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Lean_Meta_casesOnStuckLHS_x3f(v_mvarId_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_);
lean_dec(v_a_324_);
lean_dec_ref(v_a_323_);
lean_dec(v_a_322_);
lean_dec_ref(v_a_321_);
return v_res_326_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_ProjFns(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Cases(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_CasesOnStuckLHS(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_ProjFns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Cases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_CasesOnStuckLHS(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Lean_ProjFns(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Cases(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_CasesOnStuckLHS(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ProjFns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Cases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_CasesOnStuckLHS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_CasesOnStuckLHS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_CasesOnStuckLHS(builtin);
}
#ifdef __cplusplus
}
#endif

// Lean compiler output
// Module: Lean.Meta.CheckTactic
// Imports: public import Lean.Meta.Basic
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
static const lean_string_object l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__0 = (const lean_object*)&l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__0_value;
static const lean_string_object l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__1 = (const lean_object*)&l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__1_value;
static const lean_string_object l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "CheckTactic"};
static const lean_object* l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__2 = (const lean_object*)&l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__2_value;
static const lean_string_object l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "CheckGoalType"};
static const lean_object* l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__3 = (const lean_object*)&l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__3_value;
static const lean_ctor_object l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__2_value),LEAN_SCALAR_PTR_LITERAL(247, 143, 161, 121, 96, 248, 163, 181)}};
static const lean_ctor_object l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4_value_aux_2),((lean_object*)&l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__3_value),LEAN_SCALAR_PTR_LITERAL(163, 32, 18, 100, 143, 172, 116, 158)}};
static const lean_object* l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4 = (const lean_object*)&l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Meta_CheckTactic_mkCheckGoalType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CheckTactic_mkCheckGoalType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Goal"};
static const lean_object* l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__0 = (const lean_object*)&l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__0_value;
static lean_once_cell_t l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__1;
static const lean_string_object l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "\nis expected to match "};
static const lean_object* l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__2 = (const lean_object*)&l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__2_value;
static lean_once_cell_t l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_CheckTactic_matchCheckGoalType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CheckTactic_matchCheckGoalType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_CheckTactic_mkCheckGoalType(lean_object* v_val_10_, lean_object* v_type_11_, lean_object* v_a_12_, lean_object* v_a_13_, lean_object* v_a_14_, lean_object* v_a_15_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = l_Lean_Meta_mkFreshLevelMVar(v_a_12_, v_a_13_, v_a_14_, v_a_15_);
if (lean_obj_tag(v___x_17_) == 0)
{
lean_object* v_a_18_; lean_object* v___x_20_; uint8_t v_isShared_21_; uint8_t v_isSharedCheck_30_; 
v_a_18_ = lean_ctor_get(v___x_17_, 0);
v_isSharedCheck_30_ = !lean_is_exclusive(v___x_17_);
if (v_isSharedCheck_30_ == 0)
{
v___x_20_ = v___x_17_;
v_isShared_21_ = v_isSharedCheck_30_;
goto v_resetjp_19_;
}
else
{
lean_inc(v_a_18_);
lean_dec(v___x_17_);
v___x_20_ = lean_box(0);
v_isShared_21_ = v_isSharedCheck_30_;
goto v_resetjp_19_;
}
v_resetjp_19_:
{
lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_28_; 
v___x_22_ = ((lean_object*)(l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4));
v___x_23_ = lean_box(0);
v___x_24_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_24_, 0, v_a_18_);
lean_ctor_set(v___x_24_, 1, v___x_23_);
v___x_25_ = l_Lean_mkConst(v___x_22_, v___x_24_);
v___x_26_ = l_Lean_mkAppB(v___x_25_, v_type_11_, v_val_10_);
if (v_isShared_21_ == 0)
{
lean_ctor_set(v___x_20_, 0, v___x_26_);
v___x_28_ = v___x_20_;
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
else
{
lean_object* v_a_31_; lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_38_; 
lean_dec_ref(v_type_11_);
lean_dec_ref(v_val_10_);
v_a_31_ = lean_ctor_get(v___x_17_, 0);
v_isSharedCheck_38_ = !lean_is_exclusive(v___x_17_);
if (v_isSharedCheck_38_ == 0)
{
v___x_33_ = v___x_17_;
v_isShared_34_ = v_isSharedCheck_38_;
goto v_resetjp_32_;
}
else
{
lean_inc(v_a_31_);
lean_dec(v___x_17_);
v___x_33_ = lean_box(0);
v_isShared_34_ = v_isSharedCheck_38_;
goto v_resetjp_32_;
}
v_resetjp_32_:
{
lean_object* v___x_36_; 
if (v_isShared_34_ == 0)
{
v___x_36_ = v___x_33_;
goto v_reusejp_35_;
}
else
{
lean_object* v_reuseFailAlloc_37_; 
v_reuseFailAlloc_37_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_37_, 0, v_a_31_);
v___x_36_ = v_reuseFailAlloc_37_;
goto v_reusejp_35_;
}
v_reusejp_35_:
{
return v___x_36_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_CheckTactic_mkCheckGoalType_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_10_ = stack[0].m_obj;
lean_object* v_type_11_ = stack[1].m_obj;
lean_object* v_a_12_ = stack[2].m_obj;
lean_object* v_a_13_ = stack[3].m_obj;
lean_object* v_a_14_ = stack[4].m_obj;
lean_object* v_a_15_ = stack[5].m_obj;
lean_object* v_res_39_;
v_res_39_ = l_Lean_Meta_CheckTactic_mkCheckGoalType(v_val_10_, v_type_11_, v_a_12_, v_a_13_, v_a_14_, v_a_15_);
stack->m_obj
 = v_res_39_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_CheckTactic_mkCheckGoalType___boxed(lean_object* v_val_40_, lean_object* v_type_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_Lean_Meta_CheckTactic_mkCheckGoalType(v_val_40_, v_type_41_, v_a_42_, v_a_43_, v_a_44_, v_a_45_);
lean_dec(v_a_45_);
lean_dec_ref(v_a_44_);
lean_dec(v_a_43_);
lean_dec_ref(v_a_42_);
return v_res_47_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0_spec__1(lean_object* v_msgData_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_){
_start:
{
lean_object* v___x_54_; lean_object* v_env_55_; uint8_t v___x_56_; lean_object* v_env_57_; lean_object* v___x_58_; lean_object* v_toCold_59_; lean_object* v_mctx_60_; lean_object* v_lctx_61_; lean_object* v_options_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_54_ = lean_st_ref_get(v___y_52_);
v_env_55_ = lean_ctor_get(v___x_54_, 0);
lean_inc_ref(v_env_55_);
lean_dec(v___x_54_);
v___x_56_ = 0;
v_env_57_ = l_Lean_Environment_setRecordingDeps(v_env_55_, v___x_56_);
v___x_58_ = lean_st_ref_get(v___y_50_);
v_toCold_59_ = lean_ctor_get(v___y_51_, 0);
v_mctx_60_ = lean_ctor_get(v___x_58_, 0);
lean_inc_ref(v_mctx_60_);
lean_dec(v___x_58_);
v_lctx_61_ = lean_ctor_get(v___y_49_, 2);
v_options_62_ = lean_ctor_get(v_toCold_59_, 2);
lean_inc_ref(v_options_62_);
lean_inc_ref(v_lctx_61_);
v___x_63_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_63_, 0, v_env_57_);
lean_ctor_set(v___x_63_, 1, v_mctx_60_);
lean_ctor_set(v___x_63_, 2, v_lctx_61_);
lean_ctor_set(v___x_63_, 3, v_options_62_);
v___x_64_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_64_, 0, v___x_63_);
lean_ctor_set(v___x_64_, 1, v_msgData_48_);
v___x_65_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_65_, 0, v___x_64_);
return v___x_65_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_48_ = stack[0].m_obj;
lean_object* v___y_49_ = stack[1].m_obj;
lean_object* v___y_50_ = stack[2].m_obj;
lean_object* v___y_51_ = stack[3].m_obj;
lean_object* v___y_52_ = stack[4].m_obj;
lean_object* v_res_66_;
v_res_66_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0_spec__1(v_msgData_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_);
stack->m_obj
 = v_res_66_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0_spec__1(v_msgData_67_, v___y_68_, v___y_69_, v___y_70_, v___y_71_);
lean_dec(v___y_71_);
lean_dec_ref(v___y_70_);
lean_dec(v___y_69_);
lean_dec_ref(v___y_68_);
return v_res_73_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0___redArg(lean_object* v_msg_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_){
_start:
{
lean_object* v_ref_80_; lean_object* v___x_81_; lean_object* v_a_82_; lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_90_; 
v_ref_80_ = lean_ctor_get(v___y_77_, 2);
v___x_81_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0_spec__1(v_msg_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_);
v_a_82_ = lean_ctor_get(v___x_81_, 0);
v_isSharedCheck_90_ = !lean_is_exclusive(v___x_81_);
if (v_isSharedCheck_90_ == 0)
{
v___x_84_ = v___x_81_;
v_isShared_85_ = v_isSharedCheck_90_;
goto v_resetjp_83_;
}
else
{
lean_inc(v_a_82_);
lean_dec(v___x_81_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_90_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
lean_object* v___x_86_; lean_object* v___x_88_; 
lean_inc(v_ref_80_);
v___x_86_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_86_, 0, v_ref_80_);
lean_ctor_set(v___x_86_, 1, v_a_82_);
if (v_isShared_85_ == 0)
{
lean_ctor_set_tag(v___x_84_, 1);
lean_ctor_set(v___x_84_, 0, v___x_86_);
v___x_88_ = v___x_84_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v___x_86_);
v___x_88_ = v_reuseFailAlloc_89_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
return v___x_88_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_74_ = stack[0].m_obj;
lean_object* v___y_75_ = stack[1].m_obj;
lean_object* v___y_76_ = stack[2].m_obj;
lean_object* v___y_77_ = stack[3].m_obj;
lean_object* v___y_78_ = stack[4].m_obj;
lean_object* v_res_91_;
v_res_91_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0___redArg(v_msg_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_);
stack->m_obj
 = v_res_91_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0___redArg___boxed(lean_object* v_msg_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0___redArg(v_msg_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_);
lean_dec(v___y_96_);
lean_dec_ref(v___y_95_);
lean_dec(v___y_94_);
lean_dec_ref(v___y_93_);
return v_res_98_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0___redArg(lean_object* v_ref_99_, lean_object* v_msg_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_){
_start:
{
lean_object* v_toCold_106_; lean_object* v_currRecDepth_107_; lean_object* v_ref_108_; uint16_t v_optionFlags_109_; uint8_t v_suppressElabErrors_110_; uint8_t v_isRecordingDeps_111_; lean_object* v_ref_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v_toCold_106_ = lean_ctor_get(v___y_103_, 0);
v_currRecDepth_107_ = lean_ctor_get(v___y_103_, 1);
v_ref_108_ = lean_ctor_get(v___y_103_, 2);
v_optionFlags_109_ = lean_ctor_get_uint16(v___y_103_, sizeof(void*)*3);
v_suppressElabErrors_110_ = lean_ctor_get_uint8(v___y_103_, sizeof(void*)*3 + 2);
v_isRecordingDeps_111_ = lean_ctor_get_uint8(v___y_103_, sizeof(void*)*3 + 3);
v_ref_112_ = l_Lean_replaceRef(v_ref_99_, v_ref_108_);
lean_inc(v_currRecDepth_107_);
lean_inc_ref(v_toCold_106_);
v___x_113_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_113_, 0, v_toCold_106_);
lean_ctor_set(v___x_113_, 1, v_currRecDepth_107_);
lean_ctor_set(v___x_113_, 2, v_ref_112_);
lean_ctor_set_uint16(v___x_113_, sizeof(void*)*3, v_optionFlags_109_);
lean_ctor_set_uint8(v___x_113_, sizeof(void*)*3 + 2, v_suppressElabErrors_110_);
lean_ctor_set_uint8(v___x_113_, sizeof(void*)*3 + 3, v_isRecordingDeps_111_);
v___x_114_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0___redArg(v_msg_100_, v___y_101_, v___y_102_, v___x_113_, v___y_104_);
lean_dec_ref_known(v___x_113_, 3);
return v___x_114_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_99_ = stack[0].m_obj;
lean_object* v_msg_100_ = stack[1].m_obj;
lean_object* v___y_101_ = stack[2].m_obj;
lean_object* v___y_102_ = stack[3].m_obj;
lean_object* v___y_103_ = stack[4].m_obj;
lean_object* v___y_104_ = stack[5].m_obj;
lean_object* v_res_115_;
v_res_115_ = l_Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0___redArg(v_ref_99_, v_msg_100_, v___y_101_, v___y_102_, v___y_103_, v___y_104_);
stack->m_obj
 = v_res_115_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0___redArg___boxed(lean_object* v_ref_116_, lean_object* v_msg_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l_Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0___redArg(v_ref_116_, v_msg_117_, v___y_118_, v___y_119_, v___y_120_, v___y_121_);
lean_dec(v___y_121_);
lean_dec_ref(v___y_120_);
lean_dec(v___y_119_);
lean_dec_ref(v___y_118_);
lean_dec(v_ref_116_);
return v_res_123_;
}
}
static lean_object* _init_l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__1(void){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_125_ = ((lean_object*)(l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__0));
v___x_126_ = l_Lean_stringToMessageData(v___x_125_);
return v___x_126_;
}
}
static lean_object* _init_l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__3(void){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_128_ = ((lean_object*)(l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__2));
v___x_129_ = l_Lean_stringToMessageData(v___x_128_);
return v___x_129_;
}
}
lean_object* l_Lean_Meta_CheckTactic_matchCheckGoalType(lean_object* v_stx_130_, lean_object* v_goalType_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = l_Lean_Meta_mkFreshLevelMVar(v_a_132_, v_a_133_, v_a_134_, v_a_135_);
if (lean_obj_tag(v___x_137_) == 0)
{
lean_object* v_a_138_; lean_object* v___x_139_; lean_object* v___x_140_; uint8_t v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v_a_138_ = lean_ctor_get(v___x_137_, 0);
lean_inc_n(v_a_138_, 2);
lean_dec_ref_known(v___x_137_, 1);
v___x_139_ = l_Lean_Expr_sort___override(v_a_138_);
v___x_140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_140_, 0, v___x_139_);
v___x_141_ = 0;
v___x_142_ = lean_box(0);
v___x_143_ = l_Lean_Meta_mkFreshExprMVar(v___x_140_, v___x_141_, v___x_142_, v_a_132_, v_a_133_, v_a_134_, v_a_135_);
if (lean_obj_tag(v___x_143_) == 0)
{
lean_object* v_a_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v_a_144_ = lean_ctor_get(v___x_143_, 0);
lean_inc_n(v_a_144_, 2);
lean_dec_ref_known(v___x_143_, 1);
v___x_145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_145_, 0, v_a_144_);
v___x_146_ = l_Lean_Meta_mkFreshExprMVar(v___x_145_, v___x_141_, v___x_142_, v_a_132_, v_a_133_, v_a_134_, v_a_135_);
if (lean_obj_tag(v___x_146_) == 0)
{
lean_object* v_a_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_193_; 
v_a_147_ = lean_ctor_get(v___x_146_, 0);
v_isSharedCheck_193_ = !lean_is_exclusive(v___x_146_);
if (v_isSharedCheck_193_ == 0)
{
v___x_149_ = v___x_146_;
v_isShared_150_ = v_isSharedCheck_193_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_a_147_);
lean_dec(v___x_146_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_193_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_157_ = ((lean_object*)(l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4));
v___x_158_ = lean_box(0);
lean_inc(v_a_138_);
v___x_159_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_159_, 0, v_a_138_);
lean_ctor_set(v___x_159_, 1, v___x_158_);
v___x_160_ = l_Lean_Expr_const___override(v___x_157_, v___x_159_);
v___x_161_ = lean_unsigned_to_nat(2u);
v___x_162_ = lean_mk_empty_array_with_capacity(v___x_161_);
lean_inc(v_a_144_);
v___x_163_ = lean_array_push(v___x_162_, v_a_144_);
lean_inc(v_a_147_);
v___x_164_ = lean_array_push(v___x_163_, v_a_147_);
v___x_165_ = l_Lean_mkAppN(v___x_160_, v___x_164_);
lean_dec_ref(v___x_164_);
lean_inc_ref(v___x_165_);
lean_inc_ref(v_goalType_131_);
v___x_166_ = l_Lean_Meta_isExprDefEq(v_goalType_131_, v___x_165_, v_a_132_, v_a_133_, v_a_134_, v_a_135_);
if (lean_obj_tag(v___x_166_) == 0)
{
lean_object* v_a_167_; uint8_t v___x_168_; 
v_a_167_ = lean_ctor_get(v___x_166_, 0);
lean_inc(v_a_167_);
lean_dec_ref_known(v___x_166_, 1);
v___x_168_ = lean_unbox(v_a_167_);
lean_dec(v_a_167_);
if (v___x_168_ == 0)
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v_a_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_184_; 
lean_del_object(v___x_149_);
lean_dec(v_a_147_);
lean_dec(v_a_144_);
lean_dec(v_a_138_);
v___x_169_ = lean_obj_once(&l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__1, &l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__1_once, _init_l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__1);
v___x_170_ = l_Lean_indentExpr(v_goalType_131_);
v___x_171_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_171_, 0, v___x_169_);
lean_ctor_set(v___x_171_, 1, v___x_170_);
v___x_172_ = lean_obj_once(&l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__3, &l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__3_once, _init_l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__3);
v___x_173_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_173_, 0, v___x_171_);
lean_ctor_set(v___x_173_, 1, v___x_172_);
v___x_174_ = l_Lean_indentExpr(v___x_165_);
v___x_175_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_175_, 0, v___x_173_);
lean_ctor_set(v___x_175_, 1, v___x_174_);
v___x_176_ = l_Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0___redArg(v_stx_130_, v___x_175_, v_a_132_, v_a_133_, v_a_134_, v_a_135_);
v_a_177_ = lean_ctor_get(v___x_176_, 0);
v_isSharedCheck_184_ = !lean_is_exclusive(v___x_176_);
if (v_isSharedCheck_184_ == 0)
{
v___x_179_ = v___x_176_;
v_isShared_180_ = v_isSharedCheck_184_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_a_177_);
lean_dec(v___x_176_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_184_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v___x_182_; 
if (v_isShared_180_ == 0)
{
v___x_182_ = v___x_179_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v_a_177_);
v___x_182_ = v_reuseFailAlloc_183_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
return v___x_182_;
}
}
}
else
{
lean_dec_ref(v___x_165_);
lean_dec_ref(v_goalType_131_);
goto v___jp_151_;
}
}
else
{
lean_object* v_a_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_192_; 
lean_dec_ref(v___x_165_);
lean_del_object(v___x_149_);
lean_dec(v_a_147_);
lean_dec(v_a_144_);
lean_dec(v_a_138_);
lean_dec_ref(v_goalType_131_);
v_a_185_ = lean_ctor_get(v___x_166_, 0);
v_isSharedCheck_192_ = !lean_is_exclusive(v___x_166_);
if (v_isSharedCheck_192_ == 0)
{
v___x_187_ = v___x_166_;
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_a_185_);
lean_dec(v___x_166_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_190_; 
if (v_isShared_188_ == 0)
{
v___x_190_ = v___x_187_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v_a_185_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
}
v___jp_151_:
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_155_; 
v___x_152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_152_, 0, v_a_144_);
lean_ctor_set(v___x_152_, 1, v_a_138_);
v___x_153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_153_, 0, v_a_147_);
lean_ctor_set(v___x_153_, 1, v___x_152_);
if (v_isShared_150_ == 0)
{
lean_ctor_set(v___x_149_, 0, v___x_153_);
v___x_155_ = v___x_149_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v___x_153_);
v___x_155_ = v_reuseFailAlloc_156_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
return v___x_155_;
}
}
}
}
else
{
lean_object* v_a_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_201_; 
lean_dec(v_a_144_);
lean_dec(v_a_138_);
lean_dec_ref(v_goalType_131_);
v_a_194_ = lean_ctor_get(v___x_146_, 0);
v_isSharedCheck_201_ = !lean_is_exclusive(v___x_146_);
if (v_isSharedCheck_201_ == 0)
{
v___x_196_ = v___x_146_;
v_isShared_197_ = v_isSharedCheck_201_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_a_194_);
lean_dec(v___x_146_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_201_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v___x_199_; 
if (v_isShared_197_ == 0)
{
v___x_199_ = v___x_196_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v_a_194_);
v___x_199_ = v_reuseFailAlloc_200_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
return v___x_199_;
}
}
}
}
else
{
lean_object* v_a_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_209_; 
lean_dec(v_a_138_);
lean_dec_ref(v_goalType_131_);
v_a_202_ = lean_ctor_get(v___x_143_, 0);
v_isSharedCheck_209_ = !lean_is_exclusive(v___x_143_);
if (v_isSharedCheck_209_ == 0)
{
v___x_204_ = v___x_143_;
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_a_202_);
lean_dec(v___x_143_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_207_; 
if (v_isShared_205_ == 0)
{
v___x_207_ = v___x_204_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v_a_202_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
return v___x_207_;
}
}
}
}
else
{
lean_object* v_a_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_217_; 
lean_dec_ref(v_goalType_131_);
v_a_210_ = lean_ctor_get(v___x_137_, 0);
v_isSharedCheck_217_ = !lean_is_exclusive(v___x_137_);
if (v_isSharedCheck_217_ == 0)
{
v___x_212_ = v___x_137_;
v_isShared_213_ = v_isSharedCheck_217_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_a_210_);
lean_dec(v___x_137_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_217_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___x_215_; 
if (v_isShared_213_ == 0)
{
v___x_215_ = v___x_212_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v_a_210_);
v___x_215_ = v_reuseFailAlloc_216_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
return v___x_215_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_CheckTactic_matchCheckGoalType_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_130_ = stack[0].m_obj;
lean_object* v_goalType_131_ = stack[1].m_obj;
lean_object* v_a_132_ = stack[2].m_obj;
lean_object* v_a_133_ = stack[3].m_obj;
lean_object* v_a_134_ = stack[4].m_obj;
lean_object* v_a_135_ = stack[5].m_obj;
lean_object* v_res_218_;
v_res_218_ = l_Lean_Meta_CheckTactic_matchCheckGoalType(v_stx_130_, v_goalType_131_, v_a_132_, v_a_133_, v_a_134_, v_a_135_);
stack->m_obj
 = v_res_218_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_CheckTactic_matchCheckGoalType___boxed(lean_object* v_stx_219_, lean_object* v_goalType_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_Lean_Meta_CheckTactic_matchCheckGoalType(v_stx_219_, v_goalType_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_);
lean_dec(v_a_224_);
lean_dec_ref(v_a_223_);
lean_dec(v_a_222_);
lean_dec_ref(v_a_221_);
lean_dec(v_stx_219_);
return v_res_226_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0(lean_object* v_00_u03b1_227_, lean_object* v_ref_228_, lean_object* v_msg_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_){
_start:
{
lean_object* v___x_235_; 
v___x_235_ = l_Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0___redArg(v_ref_228_, v_msg_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_);
return v___x_235_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_228_ = stack[1].m_obj;
lean_object* v_msg_229_ = stack[2].m_obj;
lean_object* v___y_230_ = stack[3].m_obj;
lean_object* v___y_231_ = stack[4].m_obj;
lean_object* v___y_232_ = stack[5].m_obj;
lean_object* v___y_233_ = stack[6].m_obj;
lean_object* v_res_236_;
v_res_236_ = l_Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0(lean_box(0), v_ref_228_, v_msg_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_);
stack->m_obj
 = v_res_236_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0___boxed(lean_object* v_00_u03b1_237_, lean_object* v_ref_238_, lean_object* v_msg_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0(v_00_u03b1_237_, v_ref_238_, v_msg_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_);
lean_dec(v___y_243_);
lean_dec_ref(v___y_242_);
lean_dec(v___y_241_);
lean_dec_ref(v___y_240_);
lean_dec(v_ref_238_);
return v_res_245_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0(lean_object* v_00_u03b1_246_, lean_object* v_msg_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_){
_start:
{
lean_object* v___x_253_; 
v___x_253_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0___redArg(v_msg_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_);
return v___x_253_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_247_ = stack[1].m_obj;
lean_object* v___y_248_ = stack[2].m_obj;
lean_object* v___y_249_ = stack[3].m_obj;
lean_object* v___y_250_ = stack[4].m_obj;
lean_object* v___y_251_ = stack[5].m_obj;
lean_object* v_res_254_;
v_res_254_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0(lean_box(0), v_msg_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_);
stack->m_obj
 = v_res_254_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0___boxed(lean_object* v_00_u03b1_255_, lean_object* v_msg_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0(v_00_u03b1_255_, v_msg_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_);
lean_dec(v___y_260_);
lean_dec_ref(v___y_259_);
lean_dec(v___y_258_);
lean_dec_ref(v___y_257_);
return v_res_262_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_CheckTactic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_CheckTactic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_CheckTactic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_CheckTactic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_CheckTactic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_CheckTactic(builtin);
}
#ifdef __cplusplus
}
#endif

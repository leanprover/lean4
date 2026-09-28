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
LEAN_EXPORT lean_object* l_Lean_Meta_CheckTactic_mkCheckGoalType(lean_object* v_val_10_, lean_object* v_type_11_, lean_object* v_a_12_, lean_object* v_a_13_, lean_object* v_a_14_, lean_object* v_a_15_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_CheckTactic_mkCheckGoalType___boxed(lean_object* v_val_39_, lean_object* v_type_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Lean_Meta_CheckTactic_mkCheckGoalType(v_val_39_, v_type_40_, v_a_41_, v_a_42_, v_a_43_, v_a_44_);
lean_dec(v_a_44_);
lean_dec_ref(v_a_43_);
lean_dec(v_a_42_);
lean_dec_ref(v_a_41_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0_spec__1(lean_object* v_msgData_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_){
_start:
{
lean_object* v___x_53_; lean_object* v_env_54_; lean_object* v___x_55_; lean_object* v_toCold_56_; lean_object* v_mctx_57_; lean_object* v_lctx_58_; lean_object* v_options_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_53_ = lean_st_ref_get(v___y_51_);
v_env_54_ = lean_ctor_get(v___x_53_, 0);
lean_inc_ref(v_env_54_);
lean_dec(v___x_53_);
v___x_55_ = lean_st_ref_get(v___y_49_);
v_toCold_56_ = lean_ctor_get(v___y_50_, 0);
v_mctx_57_ = lean_ctor_get(v___x_55_, 0);
lean_inc_ref(v_mctx_57_);
lean_dec(v___x_55_);
v_lctx_58_ = lean_ctor_get(v___y_48_, 2);
v_options_59_ = lean_ctor_get(v_toCold_56_, 2);
lean_inc_ref(v_options_59_);
lean_inc_ref(v_lctx_58_);
v___x_60_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_60_, 0, v_env_54_);
lean_ctor_set(v___x_60_, 1, v_mctx_57_);
lean_ctor_set(v___x_60_, 2, v_lctx_58_);
lean_ctor_set(v___x_60_, 3, v_options_59_);
v___x_61_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_61_, 0, v___x_60_);
lean_ctor_set(v___x_61_, 1, v_msgData_47_);
v___x_62_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_62_, 0, v___x_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0_spec__1(v_msgData_63_, v___y_64_, v___y_65_, v___y_66_, v___y_67_);
lean_dec(v___y_67_);
lean_dec_ref(v___y_66_);
lean_dec(v___y_65_);
lean_dec_ref(v___y_64_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0___redArg(lean_object* v_msg_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_){
_start:
{
lean_object* v_ref_76_; lean_object* v___x_77_; lean_object* v_a_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_86_; 
v_ref_76_ = lean_ctor_get(v___y_73_, 2);
v___x_77_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0_spec__1(v_msg_70_, v___y_71_, v___y_72_, v___y_73_, v___y_74_);
v_a_78_ = lean_ctor_get(v___x_77_, 0);
v_isSharedCheck_86_ = !lean_is_exclusive(v___x_77_);
if (v_isSharedCheck_86_ == 0)
{
v___x_80_ = v___x_77_;
v_isShared_81_ = v_isSharedCheck_86_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_a_78_);
lean_dec(v___x_77_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_86_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
lean_object* v___x_82_; lean_object* v___x_84_; 
lean_inc(v_ref_76_);
v___x_82_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_82_, 0, v_ref_76_);
lean_ctor_set(v___x_82_, 1, v_a_78_);
if (v_isShared_81_ == 0)
{
lean_ctor_set_tag(v___x_80_, 1);
lean_ctor_set(v___x_80_, 0, v___x_82_);
v___x_84_ = v___x_80_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v___x_82_);
v___x_84_ = v_reuseFailAlloc_85_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
return v___x_84_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0___redArg___boxed(lean_object* v_msg_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0___redArg(v_msg_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_);
lean_dec(v___y_91_);
lean_dec_ref(v___y_90_);
lean_dec(v___y_89_);
lean_dec_ref(v___y_88_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0___redArg(lean_object* v_ref_94_, lean_object* v_msg_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_){
_start:
{
lean_object* v_toCold_101_; lean_object* v_currRecDepth_102_; lean_object* v_ref_103_; uint16_t v_optionFlags_104_; uint8_t v_suppressElabErrors_105_; uint8_t v_isRecordingDeps_106_; lean_object* v_ref_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v_toCold_101_ = lean_ctor_get(v___y_98_, 0);
v_currRecDepth_102_ = lean_ctor_get(v___y_98_, 1);
v_ref_103_ = lean_ctor_get(v___y_98_, 2);
v_optionFlags_104_ = lean_ctor_get_uint16(v___y_98_, sizeof(void*)*3);
v_suppressElabErrors_105_ = lean_ctor_get_uint8(v___y_98_, sizeof(void*)*3 + 2);
v_isRecordingDeps_106_ = lean_ctor_get_uint8(v___y_98_, sizeof(void*)*3 + 3);
v_ref_107_ = l_Lean_replaceRef(v_ref_94_, v_ref_103_);
lean_inc(v_currRecDepth_102_);
lean_inc_ref(v_toCold_101_);
v___x_108_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_108_, 0, v_toCold_101_);
lean_ctor_set(v___x_108_, 1, v_currRecDepth_102_);
lean_ctor_set(v___x_108_, 2, v_ref_107_);
lean_ctor_set_uint16(v___x_108_, sizeof(void*)*3, v_optionFlags_104_);
lean_ctor_set_uint8(v___x_108_, sizeof(void*)*3 + 2, v_suppressElabErrors_105_);
lean_ctor_set_uint8(v___x_108_, sizeof(void*)*3 + 3, v_isRecordingDeps_106_);
v___x_109_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0___redArg(v_msg_95_, v___y_96_, v___y_97_, v___x_108_, v___y_99_);
lean_dec_ref_known(v___x_108_, 3);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0___redArg___boxed(lean_object* v_ref_110_, lean_object* v_msg_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l_Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0___redArg(v_ref_110_, v_msg_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_);
lean_dec(v___y_115_);
lean_dec_ref(v___y_114_);
lean_dec(v___y_113_);
lean_dec_ref(v___y_112_);
lean_dec(v_ref_110_);
return v_res_117_;
}
}
static lean_object* _init_l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__1(void){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_119_ = ((lean_object*)(l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__0));
v___x_120_ = l_Lean_stringToMessageData(v___x_119_);
return v___x_120_;
}
}
static lean_object* _init_l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__3(void){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_122_ = ((lean_object*)(l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__2));
v___x_123_ = l_Lean_stringToMessageData(v___x_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CheckTactic_matchCheckGoalType(lean_object* v_stx_124_, lean_object* v_goalType_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_){
_start:
{
lean_object* v___x_131_; 
v___x_131_ = l_Lean_Meta_mkFreshLevelMVar(v_a_126_, v_a_127_, v_a_128_, v_a_129_);
if (lean_obj_tag(v___x_131_) == 0)
{
lean_object* v_a_132_; lean_object* v___x_133_; lean_object* v___x_134_; uint8_t v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v_a_132_ = lean_ctor_get(v___x_131_, 0);
lean_inc_n(v_a_132_, 2);
lean_dec_ref_known(v___x_131_, 1);
v___x_133_ = l_Lean_Expr_sort___override(v_a_132_);
v___x_134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_134_, 0, v___x_133_);
v___x_135_ = 0;
v___x_136_ = lean_box(0);
v___x_137_ = l_Lean_Meta_mkFreshExprMVar(v___x_134_, v___x_135_, v___x_136_, v_a_126_, v_a_127_, v_a_128_, v_a_129_);
if (lean_obj_tag(v___x_137_) == 0)
{
lean_object* v_a_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v_a_138_ = lean_ctor_get(v___x_137_, 0);
lean_inc_n(v_a_138_, 2);
lean_dec_ref_known(v___x_137_, 1);
v___x_139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_139_, 0, v_a_138_);
v___x_140_ = l_Lean_Meta_mkFreshExprMVar(v___x_139_, v___x_135_, v___x_136_, v_a_126_, v_a_127_, v_a_128_, v_a_129_);
if (lean_obj_tag(v___x_140_) == 0)
{
lean_object* v_a_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_187_; 
v_a_141_ = lean_ctor_get(v___x_140_, 0);
v_isSharedCheck_187_ = !lean_is_exclusive(v___x_140_);
if (v_isSharedCheck_187_ == 0)
{
v___x_143_ = v___x_140_;
v_isShared_144_ = v_isSharedCheck_187_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_a_141_);
lean_dec(v___x_140_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_187_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_151_ = ((lean_object*)(l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4));
v___x_152_ = lean_box(0);
lean_inc(v_a_132_);
v___x_153_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_153_, 0, v_a_132_);
lean_ctor_set(v___x_153_, 1, v___x_152_);
v___x_154_ = l_Lean_Expr_const___override(v___x_151_, v___x_153_);
v___x_155_ = lean_unsigned_to_nat(2u);
v___x_156_ = lean_mk_empty_array_with_capacity(v___x_155_);
lean_inc(v_a_138_);
v___x_157_ = lean_array_push(v___x_156_, v_a_138_);
lean_inc(v_a_141_);
v___x_158_ = lean_array_push(v___x_157_, v_a_141_);
v___x_159_ = l_Lean_mkAppN(v___x_154_, v___x_158_);
lean_dec_ref(v___x_158_);
lean_inc_ref(v___x_159_);
lean_inc_ref(v_goalType_125_);
v___x_160_ = l_Lean_Meta_isExprDefEq(v_goalType_125_, v___x_159_, v_a_126_, v_a_127_, v_a_128_, v_a_129_);
if (lean_obj_tag(v___x_160_) == 0)
{
lean_object* v_a_161_; uint8_t v___x_162_; 
v_a_161_ = lean_ctor_get(v___x_160_, 0);
lean_inc(v_a_161_);
lean_dec_ref_known(v___x_160_, 1);
v___x_162_ = lean_unbox(v_a_161_);
lean_dec(v_a_161_);
if (v___x_162_ == 0)
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v_a_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_178_; 
lean_del_object(v___x_143_);
lean_dec(v_a_141_);
lean_dec(v_a_138_);
lean_dec(v_a_132_);
v___x_163_ = lean_obj_once(&l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__1, &l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__1_once, _init_l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__1);
v___x_164_ = l_Lean_indentExpr(v_goalType_125_);
v___x_165_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_165_, 0, v___x_163_);
lean_ctor_set(v___x_165_, 1, v___x_164_);
v___x_166_ = lean_obj_once(&l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__3, &l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__3_once, _init_l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__3);
v___x_167_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_167_, 0, v___x_165_);
lean_ctor_set(v___x_167_, 1, v___x_166_);
v___x_168_ = l_Lean_indentExpr(v___x_159_);
v___x_169_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_169_, 0, v___x_167_);
lean_ctor_set(v___x_169_, 1, v___x_168_);
v___x_170_ = l_Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0___redArg(v_stx_124_, v___x_169_, v_a_126_, v_a_127_, v_a_128_, v_a_129_);
v_a_171_ = lean_ctor_get(v___x_170_, 0);
v_isSharedCheck_178_ = !lean_is_exclusive(v___x_170_);
if (v_isSharedCheck_178_ == 0)
{
v___x_173_ = v___x_170_;
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_a_171_);
lean_dec(v___x_170_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___x_176_; 
if (v_isShared_174_ == 0)
{
v___x_176_ = v___x_173_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v_a_171_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
}
}
}
else
{
lean_dec_ref(v___x_159_);
lean_dec_ref(v_goalType_125_);
goto v___jp_145_;
}
}
else
{
lean_object* v_a_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_186_; 
lean_dec_ref(v___x_159_);
lean_del_object(v___x_143_);
lean_dec(v_a_141_);
lean_dec(v_a_138_);
lean_dec(v_a_132_);
lean_dec_ref(v_goalType_125_);
v_a_179_ = lean_ctor_get(v___x_160_, 0);
v_isSharedCheck_186_ = !lean_is_exclusive(v___x_160_);
if (v_isSharedCheck_186_ == 0)
{
v___x_181_ = v___x_160_;
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_a_179_);
lean_dec(v___x_160_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_184_; 
if (v_isShared_182_ == 0)
{
v___x_184_ = v___x_181_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v_a_179_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
return v___x_184_;
}
}
}
v___jp_145_:
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_149_; 
v___x_146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_146_, 0, v_a_138_);
lean_ctor_set(v___x_146_, 1, v_a_132_);
v___x_147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_147_, 0, v_a_141_);
lean_ctor_set(v___x_147_, 1, v___x_146_);
if (v_isShared_144_ == 0)
{
lean_ctor_set(v___x_143_, 0, v___x_147_);
v___x_149_ = v___x_143_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v___x_147_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
return v___x_149_;
}
}
}
}
else
{
lean_object* v_a_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_195_; 
lean_dec(v_a_138_);
lean_dec(v_a_132_);
lean_dec_ref(v_goalType_125_);
v_a_188_ = lean_ctor_get(v___x_140_, 0);
v_isSharedCheck_195_ = !lean_is_exclusive(v___x_140_);
if (v_isSharedCheck_195_ == 0)
{
v___x_190_ = v___x_140_;
v_isShared_191_ = v_isSharedCheck_195_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_a_188_);
lean_dec(v___x_140_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_195_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v___x_193_; 
if (v_isShared_191_ == 0)
{
v___x_193_ = v___x_190_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v_a_188_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
}
}
else
{
lean_object* v_a_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_203_; 
lean_dec(v_a_132_);
lean_dec_ref(v_goalType_125_);
v_a_196_ = lean_ctor_get(v___x_137_, 0);
v_isSharedCheck_203_ = !lean_is_exclusive(v___x_137_);
if (v_isSharedCheck_203_ == 0)
{
v___x_198_ = v___x_137_;
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_a_196_);
lean_dec(v___x_137_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_201_; 
if (v_isShared_199_ == 0)
{
v___x_201_ = v___x_198_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v_a_196_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
return v___x_201_;
}
}
}
}
else
{
lean_object* v_a_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_211_; 
lean_dec_ref(v_goalType_125_);
v_a_204_ = lean_ctor_get(v___x_131_, 0);
v_isSharedCheck_211_ = !lean_is_exclusive(v___x_131_);
if (v_isSharedCheck_211_ == 0)
{
v___x_206_ = v___x_131_;
v_isShared_207_ = v_isSharedCheck_211_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_a_204_);
lean_dec(v___x_131_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_211_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v___x_209_; 
if (v_isShared_207_ == 0)
{
v___x_209_ = v___x_206_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v_a_204_);
v___x_209_ = v_reuseFailAlloc_210_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
return v___x_209_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CheckTactic_matchCheckGoalType___boxed(lean_object* v_stx_212_, lean_object* v_goalType_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lean_Meta_CheckTactic_matchCheckGoalType(v_stx_212_, v_goalType_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_);
lean_dec(v_a_217_);
lean_dec_ref(v_a_216_);
lean_dec(v_a_215_);
lean_dec_ref(v_a_214_);
lean_dec(v_stx_212_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0(lean_object* v_00_u03b1_220_, lean_object* v_ref_221_, lean_object* v_msg_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_){
_start:
{
lean_object* v___x_228_; 
v___x_228_ = l_Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0___redArg(v_ref_221_, v_msg_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0___boxed(lean_object* v_00_u03b1_229_, lean_object* v_ref_230_, lean_object* v_msg_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l_Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0(v_00_u03b1_229_, v_ref_230_, v_msg_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_);
lean_dec(v___y_235_);
lean_dec_ref(v___y_234_);
lean_dec(v___y_233_);
lean_dec_ref(v___y_232_);
lean_dec(v_ref_230_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0(lean_object* v_00_u03b1_238_, lean_object* v_msg_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_){
_start:
{
lean_object* v___x_245_; 
v___x_245_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0___redArg(v_msg_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0___boxed(lean_object* v_00_u03b1_246_, lean_object* v_msg_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0(v_00_u03b1_246_, v_msg_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_);
lean_dec(v___y_251_);
lean_dec_ref(v___y_250_);
lean_dec(v___y_249_);
lean_dec_ref(v___y_248_);
return v_res_253_;
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

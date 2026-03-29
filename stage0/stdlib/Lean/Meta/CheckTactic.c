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
lean_object* v___x_53_; lean_object* v_env_54_; lean_object* v___x_55_; lean_object* v_mctx_56_; lean_object* v_lctx_57_; lean_object* v_options_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_53_ = lean_st_ref_get(v___y_51_);
v_env_54_ = lean_ctor_get(v___x_53_, 0);
lean_inc_ref(v_env_54_);
lean_dec(v___x_53_);
v___x_55_ = lean_st_ref_get(v___y_49_);
v_mctx_56_ = lean_ctor_get(v___x_55_, 0);
lean_inc_ref(v_mctx_56_);
lean_dec(v___x_55_);
v_lctx_57_ = lean_ctor_get(v___y_48_, 2);
v_options_58_ = lean_ctor_get(v___y_50_, 2);
lean_inc_ref(v_options_58_);
lean_inc_ref(v_lctx_57_);
v___x_59_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_59_, 0, v_env_54_);
lean_ctor_set(v___x_59_, 1, v_mctx_56_);
lean_ctor_set(v___x_59_, 2, v_lctx_57_);
lean_ctor_set(v___x_59_, 3, v_options_58_);
v___x_60_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_60_, 0, v___x_59_);
lean_ctor_set(v___x_60_, 1, v_msgData_47_);
v___x_61_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_61_, 0, v___x_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0_spec__1(v_msgData_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_);
lean_dec(v___y_66_);
lean_dec_ref(v___y_65_);
lean_dec(v___y_64_);
lean_dec_ref(v___y_63_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0___redArg(lean_object* v_msg_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_){
_start:
{
lean_object* v_ref_75_; lean_object* v___x_76_; lean_object* v_a_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_85_; 
v_ref_75_ = lean_ctor_get(v___y_72_, 5);
v___x_76_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0_spec__1(v_msg_69_, v___y_70_, v___y_71_, v___y_72_, v___y_73_);
v_a_77_ = lean_ctor_get(v___x_76_, 0);
v_isSharedCheck_85_ = !lean_is_exclusive(v___x_76_);
if (v_isSharedCheck_85_ == 0)
{
v___x_79_ = v___x_76_;
v_isShared_80_ = v_isSharedCheck_85_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_a_77_);
lean_dec(v___x_76_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_85_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
lean_object* v___x_81_; lean_object* v___x_83_; 
lean_inc(v_ref_75_);
v___x_81_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_81_, 0, v_ref_75_);
lean_ctor_set(v___x_81_, 1, v_a_77_);
if (v_isShared_80_ == 0)
{
lean_ctor_set_tag(v___x_79_, 1);
lean_ctor_set(v___x_79_, 0, v___x_81_);
v___x_83_ = v___x_79_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_84_; 
v_reuseFailAlloc_84_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_84_, 0, v___x_81_);
v___x_83_ = v_reuseFailAlloc_84_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
return v___x_83_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0___redArg___boxed(lean_object* v_msg_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0___redArg(v_msg_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_);
lean_dec(v___y_90_);
lean_dec_ref(v___y_89_);
lean_dec(v___y_88_);
lean_dec_ref(v___y_87_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0___redArg(lean_object* v_ref_93_, lean_object* v_msg_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_){
_start:
{
lean_object* v_fileName_100_; lean_object* v_fileMap_101_; lean_object* v_options_102_; lean_object* v_currRecDepth_103_; lean_object* v_maxRecDepth_104_; lean_object* v_ref_105_; lean_object* v_currNamespace_106_; lean_object* v_openDecls_107_; lean_object* v_initHeartbeats_108_; lean_object* v_maxHeartbeats_109_; lean_object* v_quotContext_110_; lean_object* v_currMacroScope_111_; uint8_t v_diag_112_; lean_object* v_cancelTk_x3f_113_; uint8_t v_suppressElabErrors_114_; lean_object* v_inheritedTraceOptions_115_; lean_object* v_ref_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v_fileName_100_ = lean_ctor_get(v___y_97_, 0);
v_fileMap_101_ = lean_ctor_get(v___y_97_, 1);
v_options_102_ = lean_ctor_get(v___y_97_, 2);
v_currRecDepth_103_ = lean_ctor_get(v___y_97_, 3);
v_maxRecDepth_104_ = lean_ctor_get(v___y_97_, 4);
v_ref_105_ = lean_ctor_get(v___y_97_, 5);
v_currNamespace_106_ = lean_ctor_get(v___y_97_, 6);
v_openDecls_107_ = lean_ctor_get(v___y_97_, 7);
v_initHeartbeats_108_ = lean_ctor_get(v___y_97_, 8);
v_maxHeartbeats_109_ = lean_ctor_get(v___y_97_, 9);
v_quotContext_110_ = lean_ctor_get(v___y_97_, 10);
v_currMacroScope_111_ = lean_ctor_get(v___y_97_, 11);
v_diag_112_ = lean_ctor_get_uint8(v___y_97_, sizeof(void*)*14);
v_cancelTk_x3f_113_ = lean_ctor_get(v___y_97_, 12);
v_suppressElabErrors_114_ = lean_ctor_get_uint8(v___y_97_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_115_ = lean_ctor_get(v___y_97_, 13);
v_ref_116_ = l_Lean_replaceRef(v_ref_93_, v_ref_105_);
lean_inc_ref(v_inheritedTraceOptions_115_);
lean_inc(v_cancelTk_x3f_113_);
lean_inc(v_currMacroScope_111_);
lean_inc(v_quotContext_110_);
lean_inc(v_maxHeartbeats_109_);
lean_inc(v_initHeartbeats_108_);
lean_inc(v_openDecls_107_);
lean_inc(v_currNamespace_106_);
lean_inc(v_maxRecDepth_104_);
lean_inc(v_currRecDepth_103_);
lean_inc_ref(v_options_102_);
lean_inc_ref(v_fileMap_101_);
lean_inc_ref(v_fileName_100_);
v___x_117_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_117_, 0, v_fileName_100_);
lean_ctor_set(v___x_117_, 1, v_fileMap_101_);
lean_ctor_set(v___x_117_, 2, v_options_102_);
lean_ctor_set(v___x_117_, 3, v_currRecDepth_103_);
lean_ctor_set(v___x_117_, 4, v_maxRecDepth_104_);
lean_ctor_set(v___x_117_, 5, v_ref_116_);
lean_ctor_set(v___x_117_, 6, v_currNamespace_106_);
lean_ctor_set(v___x_117_, 7, v_openDecls_107_);
lean_ctor_set(v___x_117_, 8, v_initHeartbeats_108_);
lean_ctor_set(v___x_117_, 9, v_maxHeartbeats_109_);
lean_ctor_set(v___x_117_, 10, v_quotContext_110_);
lean_ctor_set(v___x_117_, 11, v_currMacroScope_111_);
lean_ctor_set(v___x_117_, 12, v_cancelTk_x3f_113_);
lean_ctor_set(v___x_117_, 13, v_inheritedTraceOptions_115_);
lean_ctor_set_uint8(v___x_117_, sizeof(void*)*14, v_diag_112_);
lean_ctor_set_uint8(v___x_117_, sizeof(void*)*14 + 1, v_suppressElabErrors_114_);
v___x_118_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0___redArg(v_msg_94_, v___y_95_, v___y_96_, v___x_117_, v___y_98_);
lean_dec_ref(v___x_117_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0___redArg___boxed(lean_object* v_ref_119_, lean_object* v_msg_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0___redArg(v_ref_119_, v_msg_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_);
lean_dec(v___y_124_);
lean_dec_ref(v___y_123_);
lean_dec(v___y_122_);
lean_dec_ref(v___y_121_);
lean_dec(v_ref_119_);
return v_res_126_;
}
}
static lean_object* _init_l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__1(void){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_128_ = ((lean_object*)(l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__0));
v___x_129_ = l_Lean_stringToMessageData(v___x_128_);
return v___x_129_;
}
}
static lean_object* _init_l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__3(void){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_131_ = ((lean_object*)(l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__2));
v___x_132_ = l_Lean_stringToMessageData(v___x_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CheckTactic_matchCheckGoalType(lean_object* v_stx_133_, lean_object* v_goalType_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = l_Lean_Meta_mkFreshLevelMVar(v_a_135_, v_a_136_, v_a_137_, v_a_138_);
if (lean_obj_tag(v___x_140_) == 0)
{
lean_object* v_a_141_; lean_object* v___x_142_; lean_object* v___x_143_; uint8_t v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v_a_141_ = lean_ctor_get(v___x_140_, 0);
lean_inc_n(v_a_141_, 2);
lean_dec_ref(v___x_140_);
v___x_142_ = l_Lean_Expr_sort___override(v_a_141_);
v___x_143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_143_, 0, v___x_142_);
v___x_144_ = 0;
v___x_145_ = lean_box(0);
v___x_146_ = l_Lean_Meta_mkFreshExprMVar(v___x_143_, v___x_144_, v___x_145_, v_a_135_, v_a_136_, v_a_137_, v_a_138_);
if (lean_obj_tag(v___x_146_) == 0)
{
lean_object* v_a_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v_a_147_ = lean_ctor_get(v___x_146_, 0);
lean_inc_n(v_a_147_, 2);
lean_dec_ref(v___x_146_);
v___x_148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_148_, 0, v_a_147_);
v___x_149_ = l_Lean_Meta_mkFreshExprMVar(v___x_148_, v___x_144_, v___x_145_, v_a_135_, v_a_136_, v_a_137_, v_a_138_);
if (lean_obj_tag(v___x_149_) == 0)
{
lean_object* v_a_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_196_; 
v_a_150_ = lean_ctor_get(v___x_149_, 0);
v_isSharedCheck_196_ = !lean_is_exclusive(v___x_149_);
if (v_isSharedCheck_196_ == 0)
{
v___x_152_ = v___x_149_;
v_isShared_153_ = v_isSharedCheck_196_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_a_150_);
lean_dec(v___x_149_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_196_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_160_ = ((lean_object*)(l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4));
v___x_161_ = lean_box(0);
lean_inc(v_a_141_);
v___x_162_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_162_, 0, v_a_141_);
lean_ctor_set(v___x_162_, 1, v___x_161_);
v___x_163_ = l_Lean_Expr_const___override(v___x_160_, v___x_162_);
v___x_164_ = lean_unsigned_to_nat(2u);
v___x_165_ = lean_mk_empty_array_with_capacity(v___x_164_);
lean_inc(v_a_147_);
v___x_166_ = lean_array_push(v___x_165_, v_a_147_);
lean_inc(v_a_150_);
v___x_167_ = lean_array_push(v___x_166_, v_a_150_);
v___x_168_ = l_Lean_mkAppN(v___x_163_, v___x_167_);
lean_dec_ref(v___x_167_);
lean_inc_ref(v___x_168_);
lean_inc_ref(v_goalType_134_);
v___x_169_ = l_Lean_Meta_isExprDefEq(v_goalType_134_, v___x_168_, v_a_135_, v_a_136_, v_a_137_, v_a_138_);
if (lean_obj_tag(v___x_169_) == 0)
{
lean_object* v_a_170_; uint8_t v___x_171_; 
v_a_170_ = lean_ctor_get(v___x_169_, 0);
lean_inc(v_a_170_);
lean_dec_ref(v___x_169_);
v___x_171_ = lean_unbox(v_a_170_);
lean_dec(v_a_170_);
if (v___x_171_ == 0)
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v_a_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_187_; 
lean_del_object(v___x_152_);
lean_dec(v_a_150_);
lean_dec(v_a_147_);
lean_dec(v_a_141_);
v___x_172_ = lean_obj_once(&l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__1, &l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__1_once, _init_l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__1);
v___x_173_ = l_Lean_indentExpr(v_goalType_134_);
v___x_174_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_174_, 0, v___x_172_);
lean_ctor_set(v___x_174_, 1, v___x_173_);
v___x_175_ = lean_obj_once(&l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__3, &l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__3_once, _init_l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__3);
v___x_176_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_176_, 0, v___x_174_);
lean_ctor_set(v___x_176_, 1, v___x_175_);
v___x_177_ = l_Lean_indentExpr(v___x_168_);
v___x_178_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_178_, 0, v___x_176_);
lean_ctor_set(v___x_178_, 1, v___x_177_);
v___x_179_ = l_Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0___redArg(v_stx_133_, v___x_178_, v_a_135_, v_a_136_, v_a_137_, v_a_138_);
v_a_180_ = lean_ctor_get(v___x_179_, 0);
v_isSharedCheck_187_ = !lean_is_exclusive(v___x_179_);
if (v_isSharedCheck_187_ == 0)
{
v___x_182_ = v___x_179_;
v_isShared_183_ = v_isSharedCheck_187_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_a_180_);
lean_dec(v___x_179_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_187_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v___x_185_; 
if (v_isShared_183_ == 0)
{
v___x_185_ = v___x_182_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v_a_180_);
v___x_185_ = v_reuseFailAlloc_186_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
return v___x_185_;
}
}
}
else
{
lean_dec_ref(v___x_168_);
lean_dec_ref(v_goalType_134_);
goto v___jp_154_;
}
}
else
{
lean_object* v_a_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_195_; 
lean_dec_ref(v___x_168_);
lean_del_object(v___x_152_);
lean_dec(v_a_150_);
lean_dec(v_a_147_);
lean_dec(v_a_141_);
lean_dec_ref(v_goalType_134_);
v_a_188_ = lean_ctor_get(v___x_169_, 0);
v_isSharedCheck_195_ = !lean_is_exclusive(v___x_169_);
if (v_isSharedCheck_195_ == 0)
{
v___x_190_ = v___x_169_;
v_isShared_191_ = v_isSharedCheck_195_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_a_188_);
lean_dec(v___x_169_);
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
v___jp_154_:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_158_; 
v___x_155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_155_, 0, v_a_147_);
lean_ctor_set(v___x_155_, 1, v_a_141_);
v___x_156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_156_, 0, v_a_150_);
lean_ctor_set(v___x_156_, 1, v___x_155_);
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 0, v___x_156_);
v___x_158_ = v___x_152_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v___x_156_);
v___x_158_ = v_reuseFailAlloc_159_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
return v___x_158_;
}
}
}
}
else
{
lean_object* v_a_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_204_; 
lean_dec(v_a_147_);
lean_dec(v_a_141_);
lean_dec_ref(v_goalType_134_);
v_a_197_ = lean_ctor_get(v___x_149_, 0);
v_isSharedCheck_204_ = !lean_is_exclusive(v___x_149_);
if (v_isSharedCheck_204_ == 0)
{
v___x_199_ = v___x_149_;
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_a_197_);
lean_dec(v___x_149_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___x_202_; 
if (v_isShared_200_ == 0)
{
v___x_202_ = v___x_199_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v_a_197_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
return v___x_202_;
}
}
}
}
else
{
lean_object* v_a_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_212_; 
lean_dec(v_a_141_);
lean_dec_ref(v_goalType_134_);
v_a_205_ = lean_ctor_get(v___x_146_, 0);
v_isSharedCheck_212_ = !lean_is_exclusive(v___x_146_);
if (v_isSharedCheck_212_ == 0)
{
v___x_207_ = v___x_146_;
v_isShared_208_ = v_isSharedCheck_212_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_a_205_);
lean_dec(v___x_146_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_212_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v___x_210_; 
if (v_isShared_208_ == 0)
{
v___x_210_ = v___x_207_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v_a_205_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
return v___x_210_;
}
}
}
}
else
{
lean_object* v_a_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_220_; 
lean_dec_ref(v_goalType_134_);
v_a_213_ = lean_ctor_get(v___x_140_, 0);
v_isSharedCheck_220_ = !lean_is_exclusive(v___x_140_);
if (v_isSharedCheck_220_ == 0)
{
v___x_215_ = v___x_140_;
v_isShared_216_ = v_isSharedCheck_220_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_a_213_);
lean_dec(v___x_140_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_220_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v___x_218_; 
if (v_isShared_216_ == 0)
{
v___x_218_ = v___x_215_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v_a_213_);
v___x_218_ = v_reuseFailAlloc_219_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
return v___x_218_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CheckTactic_matchCheckGoalType___boxed(lean_object* v_stx_221_, lean_object* v_goalType_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Lean_Meta_CheckTactic_matchCheckGoalType(v_stx_221_, v_goalType_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_);
lean_dec(v_a_226_);
lean_dec_ref(v_a_225_);
lean_dec(v_a_224_);
lean_dec_ref(v_a_223_);
lean_dec(v_stx_221_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0(lean_object* v_00_u03b1_229_, lean_object* v_ref_230_, lean_object* v_msg_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = l_Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0___redArg(v_ref_230_, v_msg_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0___boxed(lean_object* v_00_u03b1_238_, lean_object* v_ref_239_, lean_object* v_msg_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0(v_00_u03b1_238_, v_ref_239_, v_msg_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_);
lean_dec(v___y_244_);
lean_dec_ref(v___y_243_);
lean_dec(v___y_242_);
lean_dec_ref(v___y_241_);
lean_dec(v_ref_239_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0(lean_object* v_00_u03b1_247_, lean_object* v_msg_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_){
_start:
{
lean_object* v___x_254_; 
v___x_254_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0___redArg(v_msg_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_);
return v___x_254_;
}
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
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_CheckTactic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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

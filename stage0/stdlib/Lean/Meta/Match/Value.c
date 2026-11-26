// Lean compiler output
// Module: Lean.Meta.Match.Value
// Imports: public import Lean.Meta.LitValues
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
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFloatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
uint64_t lean_float_to_bits(double);
lean_object* lean_uint64_to_nat(uint64_t);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFloat32Value_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_float32_to_bits(float);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFinValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getBitVecValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getStringValue_x3f(lean_object*);
lean_object* l_Lean_Meta_getCharValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getUInt8Value_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getUInt16Value_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getUInt32Value_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getUInt64Value_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getInt8Value_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getInt16Value_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getInt32Value_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getInt64Value_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isMatchValue_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isMatchValue_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isMatchValue_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isMatchValue_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatchValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatchValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_normMatchValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Float"};
static const lean_object* l_Lean_Meta_normMatchValue___closed__0 = (const lean_object*)&l_Lean_Meta_normMatchValue___closed__0_value;
static const lean_string_object l_Lean_Meta_normMatchValue___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ofBits"};
static const lean_object* l_Lean_Meta_normMatchValue___closed__1 = (const lean_object*)&l_Lean_Meta_normMatchValue___closed__1_value;
static const lean_ctor_object l_Lean_Meta_normMatchValue___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_normMatchValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 69, 114, 85, 163, 177, 220, 67)}};
static const lean_ctor_object l_Lean_Meta_normMatchValue___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_normMatchValue___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_normMatchValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(34, 142, 56, 46, 8, 221, 246, 128)}};
static const lean_object* l_Lean_Meta_normMatchValue___closed__2 = (const lean_object*)&l_Lean_Meta_normMatchValue___closed__2_value;
static lean_once_cell_t l_Lean_Meta_normMatchValue___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_normMatchValue___closed__3;
static const lean_string_object l_Lean_Meta_normMatchValue___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Float32"};
static const lean_object* l_Lean_Meta_normMatchValue___closed__4 = (const lean_object*)&l_Lean_Meta_normMatchValue___closed__4_value;
static const lean_ctor_object l_Lean_Meta_normMatchValue___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_normMatchValue___closed__4_value),LEAN_SCALAR_PTR_LITERAL(246, 232, 182, 48, 64, 193, 160, 231)}};
static const lean_ctor_object l_Lean_Meta_normMatchValue___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_normMatchValue___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_normMatchValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(100, 203, 214, 18, 203, 3, 136, 149)}};
static const lean_object* l_Lean_Meta_normMatchValue___closed__5 = (const lean_object*)&l_Lean_Meta_normMatchValue___closed__5_value;
static lean_once_cell_t l_Lean_Meta_normMatchValue___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_normMatchValue___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_normMatchValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_normMatchValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isMatchValue_spec__0___redArg(lean_object* v_e_1_, lean_object* v___y_2_){
_start:
{
uint8_t v___x_4_; 
v___x_4_ = l_Lean_Expr_hasMVar(v_e_1_);
if (v___x_4_ == 0)
{
lean_object* v___x_5_; 
v___x_5_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5_, 0, v_e_1_);
return v___x_5_;
}
else
{
lean_object* v___x_6_; lean_object* v_mctx_7_; lean_object* v___x_8_; lean_object* v_fst_9_; lean_object* v_snd_10_; lean_object* v___x_11_; lean_object* v_cache_12_; lean_object* v_zetaDeltaFVarIds_13_; lean_object* v_postponed_14_; lean_object* v_diag_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_24_; 
v___x_6_ = lean_st_ref_get(v___y_2_);
v_mctx_7_ = lean_ctor_get(v___x_6_, 0);
lean_inc_ref(v_mctx_7_);
lean_dec(v___x_6_);
v___x_8_ = l_Lean_instantiateMVarsCore(v_mctx_7_, v_e_1_);
v_fst_9_ = lean_ctor_get(v___x_8_, 0);
lean_inc(v_fst_9_);
v_snd_10_ = lean_ctor_get(v___x_8_, 1);
lean_inc(v_snd_10_);
lean_dec_ref(v___x_8_);
v___x_11_ = lean_st_ref_take(v___y_2_);
v_cache_12_ = lean_ctor_get(v___x_11_, 1);
v_zetaDeltaFVarIds_13_ = lean_ctor_get(v___x_11_, 2);
v_postponed_14_ = lean_ctor_get(v___x_11_, 3);
v_diag_15_ = lean_ctor_get(v___x_11_, 4);
v_isSharedCheck_24_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_24_ == 0)
{
lean_object* v_unused_25_; 
v_unused_25_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_25_);
v___x_17_ = v___x_11_;
v_isShared_18_ = v_isSharedCheck_24_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_diag_15_);
lean_inc(v_postponed_14_);
lean_inc(v_zetaDeltaFVarIds_13_);
lean_inc(v_cache_12_);
lean_dec(v___x_11_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_24_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
lean_object* v___x_20_; 
if (v_isShared_18_ == 0)
{
lean_ctor_set(v___x_17_, 0, v_snd_10_);
v___x_20_ = v___x_17_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_23_; 
v_reuseFailAlloc_23_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_23_, 0, v_snd_10_);
lean_ctor_set(v_reuseFailAlloc_23_, 1, v_cache_12_);
lean_ctor_set(v_reuseFailAlloc_23_, 2, v_zetaDeltaFVarIds_13_);
lean_ctor_set(v_reuseFailAlloc_23_, 3, v_postponed_14_);
lean_ctor_set(v_reuseFailAlloc_23_, 4, v_diag_15_);
v___x_20_ = v_reuseFailAlloc_23_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_21_ = lean_st_ref_put(v___y_2_, v___x_20_);
v___x_22_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_22_, 0, v_fst_9_);
return v___x_22_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isMatchValue_spec__0___redArg___boxed(lean_object* v_e_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_instantiateMVars___at___00Lean_Meta_isMatchValue_spec__0___redArg(v_e_26_, v___y_27_);
lean_dec(v___y_27_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isMatchValue_spec__0(lean_object* v_e_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_Lean_instantiateMVars___at___00Lean_Meta_isMatchValue_spec__0___redArg(v_e_30_, v___y_32_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isMatchValue_spec__0___boxed(lean_object* v_e_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_instantiateMVars___at___00Lean_Meta_isMatchValue_spec__0(v_e_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_);
lean_dec(v___y_41_);
lean_dec_ref(v___y_40_);
lean_dec(v___y_39_);
lean_dec_ref(v___y_38_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatchValue(lean_object* v_e_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_){
_start:
{
lean_object* v___x_50_; lean_object* v_a_51_; lean_object* v___x_52_; 
v___x_50_ = l_Lean_instantiateMVars___at___00Lean_Meta_isMatchValue_spec__0___redArg(v_e_44_, v_a_46_);
v_a_51_ = lean_ctor_get(v___x_50_, 0);
lean_inc(v_a_51_);
lean_dec_ref(v___x_50_);
v___x_52_ = l_Lean_Meta_getNatValue_x3f(v_a_51_, v_a_45_, v_a_46_, v_a_47_, v_a_48_);
if (lean_obj_tag(v___x_52_) == 0)
{
lean_object* v_a_53_; lean_object* v___x_55_; uint8_t v_isShared_56_; uint8_t v_isSharedCheck_325_; 
v_a_53_ = lean_ctor_get(v___x_52_, 0);
v_isSharedCheck_325_ = !lean_is_exclusive(v___x_52_);
if (v_isSharedCheck_325_ == 0)
{
v___x_55_ = v___x_52_;
v_isShared_56_ = v_isSharedCheck_325_;
goto v_resetjp_54_;
}
else
{
lean_inc(v_a_53_);
lean_dec(v___x_52_);
v___x_55_ = lean_box(0);
v_isShared_56_ = v_isSharedCheck_325_;
goto v_resetjp_54_;
}
v_resetjp_54_:
{
if (lean_obj_tag(v_a_53_) == 0)
{
uint8_t v___x_57_; uint8_t v___x_58_; lean_object* v___x_59_; 
lean_del_object(v___x_55_);
v___x_57_ = 0;
v___x_58_ = 1;
lean_inc(v_a_51_);
v___x_59_ = l_Lean_Meta_getIntValue_x3f(v_a_51_, v_a_45_, v_a_46_, v_a_47_, v_a_48_);
if (lean_obj_tag(v___x_59_) == 0)
{
lean_object* v_a_60_; lean_object* v___x_62_; uint8_t v_isShared_63_; uint8_t v_isSharedCheck_311_; 
v_a_60_ = lean_ctor_get(v___x_59_, 0);
v_isSharedCheck_311_ = !lean_is_exclusive(v___x_59_);
if (v_isSharedCheck_311_ == 0)
{
v___x_62_ = v___x_59_;
v_isShared_63_ = v_isSharedCheck_311_;
goto v_resetjp_61_;
}
else
{
lean_inc(v_a_60_);
lean_dec(v___x_59_);
v___x_62_ = lean_box(0);
v_isShared_63_ = v_isSharedCheck_311_;
goto v_resetjp_61_;
}
v_resetjp_61_:
{
if (lean_obj_tag(v_a_60_) == 0)
{
lean_object* v___x_64_; 
lean_del_object(v___x_62_);
lean_inc(v_a_51_);
v___x_64_ = l_Lean_Meta_getFinValue_x3f(v_a_51_, v_a_45_, v_a_46_, v_a_47_, v_a_48_);
if (lean_obj_tag(v___x_64_) == 0)
{
lean_object* v_a_65_; lean_object* v___x_67_; uint8_t v_isShared_68_; uint8_t v_isSharedCheck_298_; 
v_a_65_ = lean_ctor_get(v___x_64_, 0);
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_64_);
if (v_isSharedCheck_298_ == 0)
{
v___x_67_ = v___x_64_;
v_isShared_68_ = v_isSharedCheck_298_;
goto v_resetjp_66_;
}
else
{
lean_inc(v_a_65_);
lean_dec(v___x_64_);
v___x_67_ = lean_box(0);
v_isShared_68_ = v_isSharedCheck_298_;
goto v_resetjp_66_;
}
v_resetjp_66_:
{
if (lean_obj_tag(v_a_65_) == 0)
{
lean_object* v___x_69_; 
lean_del_object(v___x_67_);
lean_inc(v_a_51_);
v___x_69_ = l_Lean_Meta_getBitVecValue_x3f(v_a_51_, v_a_45_, v_a_46_, v_a_47_, v_a_48_);
if (lean_obj_tag(v___x_69_) == 0)
{
lean_object* v_a_70_; lean_object* v___x_72_; uint8_t v_isShared_73_; uint8_t v_isSharedCheck_285_; 
v_a_70_ = lean_ctor_get(v___x_69_, 0);
v_isSharedCheck_285_ = !lean_is_exclusive(v___x_69_);
if (v_isSharedCheck_285_ == 0)
{
v___x_72_ = v___x_69_;
v_isShared_73_ = v_isSharedCheck_285_;
goto v_resetjp_71_;
}
else
{
lean_inc(v_a_70_);
lean_dec(v___x_69_);
v___x_72_ = lean_box(0);
v_isShared_73_ = v_isSharedCheck_285_;
goto v_resetjp_71_;
}
v_resetjp_71_:
{
if (lean_obj_tag(v_a_70_) == 0)
{
lean_object* v___x_74_; 
lean_inc(v_a_51_);
v___x_74_ = l_Lean_Meta_getStringValue_x3f(v_a_51_);
if (lean_obj_tag(v___x_74_) == 0)
{
lean_object* v___x_75_; 
lean_del_object(v___x_72_);
lean_inc(v_a_51_);
v___x_75_ = l_Lean_Meta_getCharValue_x3f(v_a_51_, v_a_45_, v_a_46_, v_a_47_, v_a_48_);
if (lean_obj_tag(v___x_75_) == 0)
{
lean_object* v_a_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_268_; 
v_a_76_ = lean_ctor_get(v___x_75_, 0);
v_isSharedCheck_268_ = !lean_is_exclusive(v___x_75_);
if (v_isSharedCheck_268_ == 0)
{
v___x_78_ = v___x_75_;
v_isShared_79_ = v_isSharedCheck_268_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_a_76_);
lean_dec(v___x_75_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_268_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
if (lean_obj_tag(v_a_76_) == 0)
{
lean_object* v___x_80_; 
lean_del_object(v___x_78_);
lean_inc(v_a_51_);
v___x_80_ = l_Lean_Meta_getUInt8Value_x3f(v_a_51_, v_a_45_, v_a_46_, v_a_47_, v_a_48_);
if (lean_obj_tag(v___x_80_) == 0)
{
lean_object* v_a_81_; lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_255_; 
v_a_81_ = lean_ctor_get(v___x_80_, 0);
v_isSharedCheck_255_ = !lean_is_exclusive(v___x_80_);
if (v_isSharedCheck_255_ == 0)
{
v___x_83_ = v___x_80_;
v_isShared_84_ = v_isSharedCheck_255_;
goto v_resetjp_82_;
}
else
{
lean_inc(v_a_81_);
lean_dec(v___x_80_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_255_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
if (lean_obj_tag(v_a_81_) == 0)
{
lean_object* v___x_85_; 
lean_del_object(v___x_83_);
lean_inc(v_a_51_);
v___x_85_ = l_Lean_Meta_getUInt16Value_x3f(v_a_51_, v_a_45_, v_a_46_, v_a_47_, v_a_48_);
if (lean_obj_tag(v___x_85_) == 0)
{
lean_object* v_a_86_; lean_object* v___x_88_; uint8_t v_isShared_89_; uint8_t v_isSharedCheck_242_; 
v_a_86_ = lean_ctor_get(v___x_85_, 0);
v_isSharedCheck_242_ = !lean_is_exclusive(v___x_85_);
if (v_isSharedCheck_242_ == 0)
{
v___x_88_ = v___x_85_;
v_isShared_89_ = v_isSharedCheck_242_;
goto v_resetjp_87_;
}
else
{
lean_inc(v_a_86_);
lean_dec(v___x_85_);
v___x_88_ = lean_box(0);
v_isShared_89_ = v_isSharedCheck_242_;
goto v_resetjp_87_;
}
v_resetjp_87_:
{
if (lean_obj_tag(v_a_86_) == 0)
{
lean_object* v___x_90_; 
lean_del_object(v___x_88_);
lean_inc(v_a_51_);
v___x_90_ = l_Lean_Meta_getUInt32Value_x3f(v_a_51_, v_a_45_, v_a_46_, v_a_47_, v_a_48_);
if (lean_obj_tag(v___x_90_) == 0)
{
lean_object* v_a_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_229_; 
v_a_91_ = lean_ctor_get(v___x_90_, 0);
v_isSharedCheck_229_ = !lean_is_exclusive(v___x_90_);
if (v_isSharedCheck_229_ == 0)
{
v___x_93_ = v___x_90_;
v_isShared_94_ = v_isSharedCheck_229_;
goto v_resetjp_92_;
}
else
{
lean_inc(v_a_91_);
lean_dec(v___x_90_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_229_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
if (lean_obj_tag(v_a_91_) == 0)
{
lean_object* v___x_95_; 
lean_del_object(v___x_93_);
lean_inc(v_a_51_);
v___x_95_ = l_Lean_Meta_getUInt64Value_x3f(v_a_51_, v_a_45_, v_a_46_, v_a_47_, v_a_48_);
if (lean_obj_tag(v___x_95_) == 0)
{
lean_object* v_a_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_216_; 
v_a_96_ = lean_ctor_get(v___x_95_, 0);
v_isSharedCheck_216_ = !lean_is_exclusive(v___x_95_);
if (v_isSharedCheck_216_ == 0)
{
v___x_98_ = v___x_95_;
v_isShared_99_ = v_isSharedCheck_216_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_a_96_);
lean_dec(v___x_95_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_216_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
if (lean_obj_tag(v_a_96_) == 0)
{
lean_object* v___x_100_; 
lean_del_object(v___x_98_);
lean_inc(v_a_51_);
v___x_100_ = l_Lean_Meta_getInt8Value_x3f(v_a_51_, v_a_45_, v_a_46_, v_a_47_, v_a_48_);
if (lean_obj_tag(v___x_100_) == 0)
{
lean_object* v_a_101_; lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_203_; 
v_a_101_ = lean_ctor_get(v___x_100_, 0);
v_isSharedCheck_203_ = !lean_is_exclusive(v___x_100_);
if (v_isSharedCheck_203_ == 0)
{
v___x_103_ = v___x_100_;
v_isShared_104_ = v_isSharedCheck_203_;
goto v_resetjp_102_;
}
else
{
lean_inc(v_a_101_);
lean_dec(v___x_100_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_203_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
if (lean_obj_tag(v_a_101_) == 0)
{
lean_object* v___x_105_; 
lean_del_object(v___x_103_);
lean_inc(v_a_51_);
v___x_105_ = l_Lean_Meta_getInt16Value_x3f(v_a_51_, v_a_45_, v_a_46_, v_a_47_, v_a_48_);
if (lean_obj_tag(v___x_105_) == 0)
{
lean_object* v_a_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_190_; 
v_a_106_ = lean_ctor_get(v___x_105_, 0);
v_isSharedCheck_190_ = !lean_is_exclusive(v___x_105_);
if (v_isSharedCheck_190_ == 0)
{
v___x_108_ = v___x_105_;
v_isShared_109_ = v_isSharedCheck_190_;
goto v_resetjp_107_;
}
else
{
lean_inc(v_a_106_);
lean_dec(v___x_105_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_190_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
if (lean_obj_tag(v_a_106_) == 0)
{
lean_object* v___x_110_; 
lean_del_object(v___x_108_);
lean_inc(v_a_51_);
v___x_110_ = l_Lean_Meta_getInt32Value_x3f(v_a_51_, v_a_45_, v_a_46_, v_a_47_, v_a_48_);
if (lean_obj_tag(v___x_110_) == 0)
{
lean_object* v_a_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_177_; 
v_a_111_ = lean_ctor_get(v___x_110_, 0);
v_isSharedCheck_177_ = !lean_is_exclusive(v___x_110_);
if (v_isSharedCheck_177_ == 0)
{
v___x_113_ = v___x_110_;
v_isShared_114_ = v_isSharedCheck_177_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_a_111_);
lean_dec(v___x_110_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_177_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
if (lean_obj_tag(v_a_111_) == 0)
{
lean_object* v___x_115_; 
lean_del_object(v___x_113_);
lean_inc(v_a_51_);
v___x_115_ = l_Lean_Meta_getInt64Value_x3f(v_a_51_, v_a_45_, v_a_46_, v_a_47_, v_a_48_);
if (lean_obj_tag(v___x_115_) == 0)
{
lean_object* v_a_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_164_; 
v_a_116_ = lean_ctor_get(v___x_115_, 0);
v_isSharedCheck_164_ = !lean_is_exclusive(v___x_115_);
if (v_isSharedCheck_164_ == 0)
{
v___x_118_ = v___x_115_;
v_isShared_119_ = v_isSharedCheck_164_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_a_116_);
lean_dec(v___x_115_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_164_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
if (lean_obj_tag(v_a_116_) == 0)
{
lean_object* v___x_120_; 
lean_del_object(v___x_118_);
lean_inc(v_a_51_);
v___x_120_ = l_Lean_Meta_getFloatValue_x3f(v_a_51_, v_a_45_, v_a_46_, v_a_47_, v_a_48_);
if (lean_obj_tag(v___x_120_) == 0)
{
lean_object* v_a_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_151_; 
v_a_121_ = lean_ctor_get(v___x_120_, 0);
v_isSharedCheck_151_ = !lean_is_exclusive(v___x_120_);
if (v_isSharedCheck_151_ == 0)
{
v___x_123_ = v___x_120_;
v_isShared_124_ = v_isSharedCheck_151_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_a_121_);
lean_dec(v___x_120_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_151_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
if (lean_obj_tag(v_a_121_) == 0)
{
lean_object* v___x_125_; 
lean_del_object(v___x_123_);
v___x_125_ = l_Lean_Meta_getFloat32Value_x3f(v_a_51_, v_a_45_, v_a_46_, v_a_47_, v_a_48_);
if (lean_obj_tag(v___x_125_) == 0)
{
lean_object* v_a_126_; lean_object* v___x_128_; uint8_t v_isShared_129_; uint8_t v_isSharedCheck_138_; 
v_a_126_ = lean_ctor_get(v___x_125_, 0);
v_isSharedCheck_138_ = !lean_is_exclusive(v___x_125_);
if (v_isSharedCheck_138_ == 0)
{
v___x_128_ = v___x_125_;
v_isShared_129_ = v_isSharedCheck_138_;
goto v_resetjp_127_;
}
else
{
lean_inc(v_a_126_);
lean_dec(v___x_125_);
v___x_128_ = lean_box(0);
v_isShared_129_ = v_isSharedCheck_138_;
goto v_resetjp_127_;
}
v_resetjp_127_:
{
if (lean_obj_tag(v_a_126_) == 0)
{
lean_object* v___x_130_; lean_object* v___x_132_; 
v___x_130_ = lean_box(v___x_57_);
if (v_isShared_129_ == 0)
{
lean_ctor_set(v___x_128_, 0, v___x_130_);
v___x_132_ = v___x_128_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v___x_130_);
v___x_132_ = v_reuseFailAlloc_133_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
return v___x_132_;
}
}
else
{
lean_object* v___x_134_; lean_object* v___x_136_; 
lean_dec_ref_known(v_a_126_, 1);
v___x_134_ = lean_box(v___x_58_);
if (v_isShared_129_ == 0)
{
lean_ctor_set(v___x_128_, 0, v___x_134_);
v___x_136_ = v___x_128_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v___x_134_);
v___x_136_ = v_reuseFailAlloc_137_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
return v___x_136_;
}
}
}
}
else
{
lean_object* v_a_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_146_; 
v_a_139_ = lean_ctor_get(v___x_125_, 0);
v_isSharedCheck_146_ = !lean_is_exclusive(v___x_125_);
if (v_isSharedCheck_146_ == 0)
{
v___x_141_ = v___x_125_;
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_a_139_);
lean_dec(v___x_125_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v___x_144_; 
if (v_isShared_142_ == 0)
{
v___x_144_ = v___x_141_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v_a_139_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
}
}
else
{
lean_object* v___x_147_; lean_object* v___x_149_; 
lean_dec_ref_known(v_a_121_, 1);
lean_dec(v_a_51_);
v___x_147_ = lean_box(v___x_58_);
if (v_isShared_124_ == 0)
{
lean_ctor_set(v___x_123_, 0, v___x_147_);
v___x_149_ = v___x_123_;
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
lean_object* v_a_152_; lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_159_; 
lean_dec(v_a_51_);
v_a_152_ = lean_ctor_get(v___x_120_, 0);
v_isSharedCheck_159_ = !lean_is_exclusive(v___x_120_);
if (v_isSharedCheck_159_ == 0)
{
v___x_154_ = v___x_120_;
v_isShared_155_ = v_isSharedCheck_159_;
goto v_resetjp_153_;
}
else
{
lean_inc(v_a_152_);
lean_dec(v___x_120_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_159_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
lean_object* v___x_157_; 
if (v_isShared_155_ == 0)
{
v___x_157_ = v___x_154_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v_a_152_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
return v___x_157_;
}
}
}
}
else
{
lean_object* v___x_160_; lean_object* v___x_162_; 
lean_dec_ref_known(v_a_116_, 1);
lean_dec(v_a_51_);
v___x_160_ = lean_box(v___x_58_);
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 0, v___x_160_);
v___x_162_ = v___x_118_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v___x_160_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
}
}
else
{
lean_object* v_a_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_172_; 
lean_dec(v_a_51_);
v_a_165_ = lean_ctor_get(v___x_115_, 0);
v_isSharedCheck_172_ = !lean_is_exclusive(v___x_115_);
if (v_isSharedCheck_172_ == 0)
{
v___x_167_ = v___x_115_;
v_isShared_168_ = v_isSharedCheck_172_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_a_165_);
lean_dec(v___x_115_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_172_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
lean_object* v___x_170_; 
if (v_isShared_168_ == 0)
{
v___x_170_ = v___x_167_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v_a_165_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
}
}
else
{
lean_object* v___x_173_; lean_object* v___x_175_; 
lean_dec_ref_known(v_a_111_, 1);
lean_dec(v_a_51_);
v___x_173_ = lean_box(v___x_58_);
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 0, v___x_173_);
v___x_175_ = v___x_113_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v___x_173_);
v___x_175_ = v_reuseFailAlloc_176_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
return v___x_175_;
}
}
}
}
else
{
lean_object* v_a_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_185_; 
lean_dec(v_a_51_);
v_a_178_ = lean_ctor_get(v___x_110_, 0);
v_isSharedCheck_185_ = !lean_is_exclusive(v___x_110_);
if (v_isSharedCheck_185_ == 0)
{
v___x_180_ = v___x_110_;
v_isShared_181_ = v_isSharedCheck_185_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_a_178_);
lean_dec(v___x_110_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_185_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v___x_183_; 
if (v_isShared_181_ == 0)
{
v___x_183_ = v___x_180_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v_a_178_);
v___x_183_ = v_reuseFailAlloc_184_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
return v___x_183_;
}
}
}
}
else
{
lean_object* v___x_186_; lean_object* v___x_188_; 
lean_dec_ref_known(v_a_106_, 1);
lean_dec(v_a_51_);
v___x_186_ = lean_box(v___x_58_);
if (v_isShared_109_ == 0)
{
lean_ctor_set(v___x_108_, 0, v___x_186_);
v___x_188_ = v___x_108_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v___x_186_);
v___x_188_ = v_reuseFailAlloc_189_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
return v___x_188_;
}
}
}
}
else
{
lean_object* v_a_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_198_; 
lean_dec(v_a_51_);
v_a_191_ = lean_ctor_get(v___x_105_, 0);
v_isSharedCheck_198_ = !lean_is_exclusive(v___x_105_);
if (v_isSharedCheck_198_ == 0)
{
v___x_193_ = v___x_105_;
v_isShared_194_ = v_isSharedCheck_198_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_a_191_);
lean_dec(v___x_105_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_198_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
lean_object* v___x_196_; 
if (v_isShared_194_ == 0)
{
v___x_196_ = v___x_193_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v_a_191_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
return v___x_196_;
}
}
}
}
else
{
lean_object* v___x_199_; lean_object* v___x_201_; 
lean_dec_ref_known(v_a_101_, 1);
lean_dec(v_a_51_);
v___x_199_ = lean_box(v___x_58_);
if (v_isShared_104_ == 0)
{
lean_ctor_set(v___x_103_, 0, v___x_199_);
v___x_201_ = v___x_103_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v___x_199_);
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
lean_dec(v_a_51_);
v_a_204_ = lean_ctor_get(v___x_100_, 0);
v_isSharedCheck_211_ = !lean_is_exclusive(v___x_100_);
if (v_isSharedCheck_211_ == 0)
{
v___x_206_ = v___x_100_;
v_isShared_207_ = v_isSharedCheck_211_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_a_204_);
lean_dec(v___x_100_);
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
else
{
lean_object* v___x_212_; lean_object* v___x_214_; 
lean_dec_ref_known(v_a_96_, 1);
lean_dec(v_a_51_);
v___x_212_ = lean_box(v___x_58_);
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 0, v___x_212_);
v___x_214_ = v___x_98_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v___x_212_);
v___x_214_ = v_reuseFailAlloc_215_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
return v___x_214_;
}
}
}
}
else
{
lean_object* v_a_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_224_; 
lean_dec(v_a_51_);
v_a_217_ = lean_ctor_get(v___x_95_, 0);
v_isSharedCheck_224_ = !lean_is_exclusive(v___x_95_);
if (v_isSharedCheck_224_ == 0)
{
v___x_219_ = v___x_95_;
v_isShared_220_ = v_isSharedCheck_224_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_a_217_);
lean_dec(v___x_95_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_224_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v___x_222_; 
if (v_isShared_220_ == 0)
{
v___x_222_ = v___x_219_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v_a_217_);
v___x_222_ = v_reuseFailAlloc_223_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
return v___x_222_;
}
}
}
}
else
{
lean_object* v___x_225_; lean_object* v___x_227_; 
lean_dec_ref_known(v_a_91_, 1);
lean_dec(v_a_51_);
v___x_225_ = lean_box(v___x_58_);
if (v_isShared_94_ == 0)
{
lean_ctor_set(v___x_93_, 0, v___x_225_);
v___x_227_ = v___x_93_;
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
}
else
{
lean_object* v_a_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_237_; 
lean_dec(v_a_51_);
v_a_230_ = lean_ctor_get(v___x_90_, 0);
v_isSharedCheck_237_ = !lean_is_exclusive(v___x_90_);
if (v_isSharedCheck_237_ == 0)
{
v___x_232_ = v___x_90_;
v_isShared_233_ = v_isSharedCheck_237_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_a_230_);
lean_dec(v___x_90_);
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
lean_object* v___x_238_; lean_object* v___x_240_; 
lean_dec_ref_known(v_a_86_, 1);
lean_dec(v_a_51_);
v___x_238_ = lean_box(v___x_58_);
if (v_isShared_89_ == 0)
{
lean_ctor_set(v___x_88_, 0, v___x_238_);
v___x_240_ = v___x_88_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v___x_238_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
return v___x_240_;
}
}
}
}
else
{
lean_object* v_a_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_250_; 
lean_dec(v_a_51_);
v_a_243_ = lean_ctor_get(v___x_85_, 0);
v_isSharedCheck_250_ = !lean_is_exclusive(v___x_85_);
if (v_isSharedCheck_250_ == 0)
{
v___x_245_ = v___x_85_;
v_isShared_246_ = v_isSharedCheck_250_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_a_243_);
lean_dec(v___x_85_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_250_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_248_; 
if (v_isShared_246_ == 0)
{
v___x_248_ = v___x_245_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v_a_243_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
return v___x_248_;
}
}
}
}
else
{
lean_object* v___x_251_; lean_object* v___x_253_; 
lean_dec_ref_known(v_a_81_, 1);
lean_dec(v_a_51_);
v___x_251_ = lean_box(v___x_58_);
if (v_isShared_84_ == 0)
{
lean_ctor_set(v___x_83_, 0, v___x_251_);
v___x_253_ = v___x_83_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v___x_251_);
v___x_253_ = v_reuseFailAlloc_254_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
return v___x_253_;
}
}
}
}
else
{
lean_object* v_a_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_263_; 
lean_dec(v_a_51_);
v_a_256_ = lean_ctor_get(v___x_80_, 0);
v_isSharedCheck_263_ = !lean_is_exclusive(v___x_80_);
if (v_isSharedCheck_263_ == 0)
{
v___x_258_ = v___x_80_;
v_isShared_259_ = v_isSharedCheck_263_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_a_256_);
lean_dec(v___x_80_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_263_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v___x_261_; 
if (v_isShared_259_ == 0)
{
v___x_261_ = v___x_258_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v_a_256_);
v___x_261_ = v_reuseFailAlloc_262_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
return v___x_261_;
}
}
}
}
else
{
lean_object* v___x_264_; lean_object* v___x_266_; 
lean_dec_ref_known(v_a_76_, 1);
lean_dec(v_a_51_);
v___x_264_ = lean_box(v___x_58_);
if (v_isShared_79_ == 0)
{
lean_ctor_set(v___x_78_, 0, v___x_264_);
v___x_266_ = v___x_78_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v___x_264_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
}
}
else
{
lean_object* v_a_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_276_; 
lean_dec(v_a_51_);
v_a_269_ = lean_ctor_get(v___x_75_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_75_);
if (v_isSharedCheck_276_ == 0)
{
v___x_271_ = v___x_75_;
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_a_269_);
lean_dec(v___x_75_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_274_; 
if (v_isShared_272_ == 0)
{
v___x_274_ = v___x_271_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_a_269_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
}
else
{
lean_object* v___x_277_; lean_object* v___x_279_; 
lean_dec_ref_known(v___x_74_, 1);
lean_dec(v_a_51_);
v___x_277_ = lean_box(v___x_58_);
if (v_isShared_73_ == 0)
{
lean_ctor_set(v___x_72_, 0, v___x_277_);
v___x_279_ = v___x_72_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v___x_277_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
}
else
{
lean_object* v___x_281_; lean_object* v___x_283_; 
lean_dec_ref_known(v_a_70_, 1);
lean_dec(v_a_51_);
v___x_281_ = lean_box(v___x_58_);
if (v_isShared_73_ == 0)
{
lean_ctor_set(v___x_72_, 0, v___x_281_);
v___x_283_ = v___x_72_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v___x_281_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
}
else
{
lean_object* v_a_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_293_; 
lean_dec(v_a_51_);
v_a_286_ = lean_ctor_get(v___x_69_, 0);
v_isSharedCheck_293_ = !lean_is_exclusive(v___x_69_);
if (v_isSharedCheck_293_ == 0)
{
v___x_288_ = v___x_69_;
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_a_286_);
lean_dec(v___x_69_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_291_; 
if (v_isShared_289_ == 0)
{
v___x_291_ = v___x_288_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v_a_286_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
}
else
{
lean_object* v___x_294_; lean_object* v___x_296_; 
lean_dec_ref_known(v_a_65_, 1);
lean_dec(v_a_51_);
v___x_294_ = lean_box(v___x_58_);
if (v_isShared_68_ == 0)
{
lean_ctor_set(v___x_67_, 0, v___x_294_);
v___x_296_ = v___x_67_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v___x_294_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
}
}
else
{
lean_object* v_a_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_306_; 
lean_dec(v_a_51_);
v_a_299_ = lean_ctor_get(v___x_64_, 0);
v_isSharedCheck_306_ = !lean_is_exclusive(v___x_64_);
if (v_isSharedCheck_306_ == 0)
{
v___x_301_ = v___x_64_;
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_a_299_);
lean_dec(v___x_64_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_304_; 
if (v_isShared_302_ == 0)
{
v___x_304_ = v___x_301_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v_a_299_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
}
}
else
{
lean_object* v___x_307_; lean_object* v___x_309_; 
lean_dec_ref_known(v_a_60_, 1);
lean_dec(v_a_51_);
v___x_307_ = lean_box(v___x_58_);
if (v_isShared_63_ == 0)
{
lean_ctor_set(v___x_62_, 0, v___x_307_);
v___x_309_ = v___x_62_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v___x_307_);
v___x_309_ = v_reuseFailAlloc_310_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
return v___x_309_;
}
}
}
}
else
{
lean_object* v_a_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_319_; 
lean_dec(v_a_51_);
v_a_312_ = lean_ctor_get(v___x_59_, 0);
v_isSharedCheck_319_ = !lean_is_exclusive(v___x_59_);
if (v_isSharedCheck_319_ == 0)
{
v___x_314_ = v___x_59_;
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_a_312_);
lean_dec(v___x_59_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_317_; 
if (v_isShared_315_ == 0)
{
v___x_317_ = v___x_314_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_a_312_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
}
}
else
{
uint8_t v___x_320_; lean_object* v___x_321_; lean_object* v___x_323_; 
lean_dec_ref_known(v_a_53_, 1);
lean_dec(v_a_51_);
v___x_320_ = 1;
v___x_321_ = lean_box(v___x_320_);
if (v_isShared_56_ == 0)
{
lean_ctor_set(v___x_55_, 0, v___x_321_);
v___x_323_ = v___x_55_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v___x_321_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
}
}
else
{
lean_object* v_a_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_333_; 
lean_dec(v_a_51_);
v_a_326_ = lean_ctor_get(v___x_52_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v___x_52_);
if (v_isSharedCheck_333_ == 0)
{
v___x_328_ = v___x_52_;
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_a_326_);
lean_dec(v___x_52_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_331_; 
if (v_isShared_329_ == 0)
{
v___x_331_ = v___x_328_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_a_326_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatchValue___boxed(lean_object* v_e_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_Lean_Meta_isMatchValue(v_e_334_, v_a_335_, v_a_336_, v_a_337_, v_a_338_);
lean_dec(v_a_338_);
lean_dec_ref(v_a_337_);
lean_dec(v_a_336_);
lean_dec_ref(v_a_335_);
return v_res_340_;
}
}
static lean_object* _init_l_Lean_Meta_normMatchValue___closed__3(void){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_346_ = lean_box(0);
v___x_347_ = ((lean_object*)(l_Lean_Meta_normMatchValue___closed__2));
v___x_348_ = l_Lean_mkConst(v___x_347_, v___x_346_);
return v___x_348_;
}
}
static lean_object* _init_l_Lean_Meta_normMatchValue___closed__6(void){
_start:
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_353_ = lean_box(0);
v___x_354_ = ((lean_object*)(l_Lean_Meta_normMatchValue___closed__5));
v___x_355_ = l_Lean_mkConst(v___x_354_, v___x_353_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_normMatchValue(lean_object* v_e_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_){
_start:
{
lean_object* v___x_362_; 
lean_inc_ref(v_e_356_);
v___x_362_ = l_Lean_Meta_getFloatValue_x3f(v_e_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_);
if (lean_obj_tag(v___x_362_) == 0)
{
lean_object* v_a_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_404_; 
v_a_363_ = lean_ctor_get(v___x_362_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_404_ == 0)
{
v___x_365_ = v___x_362_;
v_isShared_366_ = v_isSharedCheck_404_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_a_363_);
lean_dec(v___x_362_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_404_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
if (lean_obj_tag(v_a_363_) == 1)
{
lean_object* v_val_367_; lean_object* v___x_368_; double v___x_369_; uint64_t v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_375_; 
lean_dec_ref(v_e_356_);
v_val_367_ = lean_ctor_get(v_a_363_, 0);
lean_inc(v_val_367_);
lean_dec_ref_known(v_a_363_, 1);
v___x_368_ = lean_obj_once(&l_Lean_Meta_normMatchValue___closed__3, &l_Lean_Meta_normMatchValue___closed__3_once, _init_l_Lean_Meta_normMatchValue___closed__3);
v___x_369_ = lean_unbox_float(v_val_367_);
lean_dec(v_val_367_);
v___x_370_ = lean_float_to_bits(v___x_369_);
v___x_371_ = lean_uint64_to_nat(v___x_370_);
v___x_372_ = l_Lean_mkRawNatLit(v___x_371_);
v___x_373_ = l_Lean_Expr_app___override(v___x_368_, v___x_372_);
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 0, v___x_373_);
v___x_375_ = v___x_365_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v___x_373_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
return v___x_375_;
}
}
else
{
lean_object* v___x_377_; 
lean_del_object(v___x_365_);
lean_dec(v_a_363_);
lean_inc_ref(v_e_356_);
v___x_377_ = l_Lean_Meta_getFloat32Value_x3f(v_e_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_);
if (lean_obj_tag(v___x_377_) == 0)
{
lean_object* v_a_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_395_; 
v_a_378_ = lean_ctor_get(v___x_377_, 0);
v_isSharedCheck_395_ = !lean_is_exclusive(v___x_377_);
if (v_isSharedCheck_395_ == 0)
{
v___x_380_ = v___x_377_;
v_isShared_381_ = v_isSharedCheck_395_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_a_378_);
lean_dec(v___x_377_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_395_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
if (lean_obj_tag(v_a_378_) == 1)
{
lean_object* v_val_382_; lean_object* v___x_383_; float v___x_384_; uint32_t v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_390_; 
lean_dec_ref(v_e_356_);
v_val_382_ = lean_ctor_get(v_a_378_, 0);
lean_inc(v_val_382_);
lean_dec_ref_known(v_a_378_, 1);
v___x_383_ = lean_obj_once(&l_Lean_Meta_normMatchValue___closed__6, &l_Lean_Meta_normMatchValue___closed__6_once, _init_l_Lean_Meta_normMatchValue___closed__6);
v___x_384_ = lean_unbox_float32(v_val_382_);
lean_dec(v_val_382_);
v___x_385_ = lean_float32_to_bits(v___x_384_);
v___x_386_ = lean_uint32_to_nat(v___x_385_);
v___x_387_ = l_Lean_mkRawNatLit(v___x_386_);
v___x_388_ = l_Lean_Expr_app___override(v___x_383_, v___x_387_);
if (v_isShared_381_ == 0)
{
lean_ctor_set(v___x_380_, 0, v___x_388_);
v___x_390_ = v___x_380_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v___x_388_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
else
{
lean_object* v___x_393_; 
lean_dec(v_a_378_);
if (v_isShared_381_ == 0)
{
lean_ctor_set(v___x_380_, 0, v_e_356_);
v___x_393_ = v___x_380_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v_e_356_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
return v___x_393_;
}
}
}
}
else
{
lean_object* v_a_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_403_; 
lean_dec_ref(v_e_356_);
v_a_396_ = lean_ctor_get(v___x_377_, 0);
v_isSharedCheck_403_ = !lean_is_exclusive(v___x_377_);
if (v_isSharedCheck_403_ == 0)
{
v___x_398_ = v___x_377_;
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_a_396_);
lean_dec(v___x_377_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_401_; 
if (v_isShared_399_ == 0)
{
v___x_401_ = v___x_398_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_a_396_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
}
}
}
}
else
{
lean_object* v_a_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_412_; 
lean_dec_ref(v_e_356_);
v_a_405_ = lean_ctor_get(v___x_362_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_412_ == 0)
{
v___x_407_ = v___x_362_;
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_a_405_);
lean_dec(v___x_362_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_410_; 
if (v_isShared_408_ == 0)
{
v___x_410_ = v___x_407_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_a_405_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_normMatchValue___boxed(lean_object* v_e_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_Lean_Meta_normMatchValue(v_e_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_);
lean_dec(v_a_417_);
lean_dec_ref(v_a_416_);
lean_dec(v_a_415_);
lean_dec_ref(v_a_414_);
return v_res_419_;
}
}
lean_object* runtime_initialize_Lean_Meta_LitValues(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Match_Value(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_LitValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Match_Value(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_LitValues(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Match_Value(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_LitValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Match_Value(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Match_Value(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Match_Value(builtin);
}
#ifdef __cplusplus
}
#endif

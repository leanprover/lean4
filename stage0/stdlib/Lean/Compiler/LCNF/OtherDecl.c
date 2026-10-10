// Lean compiler output
// Module: Lean.Compiler.LCNF.OtherDecl
// Imports: public import Lean.Compiler.LCNF.CompilerM import Lean.Compiler.LCNF.MonoTypes import Lean.Compiler.LCNF.ToImpureType
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getPurity___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*, uint8_t);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_Compiler_LCNF_getPhase___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getOtherDeclBaseType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getOtherDeclMonoType(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_getOtherDeclType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "getOtherDeclType unsupported for impure"};
static const lean_object* l_Lean_Compiler_LCNF_getOtherDeclType___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_getOtherDeclType___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_getOtherDeclType___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_getOtherDeclType___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getOtherDeclType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getOtherDeclType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1_;
}
}
static lean_object* _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg___closed__0, &l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg___closed__0_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg___closed__0);
v___x_3_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
return v___x_3_;
}
}
static lean_object* _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_4_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_5_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg___closed__1, &l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg___closed__1_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg___closed__1);
v___x_6_ = lean_unsigned_to_nat(0u);
v___x_7_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_7_, 0, v___x_6_);
lean_ctor_set(v___x_7_, 1, v___x_6_);
lean_ctor_set(v___x_7_, 2, v___x_6_);
lean_ctor_set(v___x_7_, 3, v___x_6_);
lean_ctor_set(v___x_7_, 4, v___x_5_);
lean_ctor_set(v___x_7_, 5, v___x_5_);
lean_ctor_set(v___x_7_, 6, v___x_5_);
lean_ctor_set(v___x_7_, 7, v___x_5_);
lean_ctor_set(v___x_7_, 8, v___x_5_);
lean_ctor_set(v___x_7_, 9, v___x_5_);
lean_ctor_set(v___x_7_, 10, v___x_5_);
lean_ctor_set(v___x_7_, 11, v___x_4_);
return v___x_7_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg(lean_object* v_msg_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_){
_start:
{
lean_object* v_ref_14_; lean_object* v___x_15_; lean_object* v_env_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v_ref_14_ = lean_ctor_get(v___y_11_, 2);
v___x_15_ = lean_st_ref_get(v___y_12_);
v_env_16_ = lean_ctor_get(v___x_15_, 0);
lean_inc_ref(v_env_16_);
lean_dec(v___x_15_);
v___x_17_ = lean_st_ref_get(v___y_10_);
v___x_18_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_9_);
if (lean_obj_tag(v___x_18_) == 0)
{
lean_object* v_a_19_; lean_object* v___x_21_; uint8_t v_isShared_22_; uint8_t v_isSharedCheck_41_; 
v_a_19_ = lean_ctor_get(v___x_18_, 0);
v_isSharedCheck_41_ = !lean_is_exclusive(v___x_18_);
if (v_isSharedCheck_41_ == 0)
{
v___x_21_ = v___x_18_;
v_isShared_22_ = v_isSharedCheck_41_;
goto v_resetjp_20_;
}
else
{
lean_inc(v_a_19_);
lean_dec(v___x_18_);
v___x_21_ = lean_box(0);
v_isShared_22_ = v_isSharedCheck_41_;
goto v_resetjp_20_;
}
v_resetjp_20_:
{
lean_object* v_lctx_23_; lean_object* v___x_25_; uint8_t v_isShared_26_; uint8_t v_isSharedCheck_39_; 
v_lctx_23_ = lean_ctor_get(v___x_17_, 0);
v_isSharedCheck_39_ = !lean_is_exclusive(v___x_17_);
if (v_isSharedCheck_39_ == 0)
{
lean_object* v_unused_40_; 
v_unused_40_ = lean_ctor_get(v___x_17_, 1);
lean_dec(v_unused_40_);
v___x_25_ = v___x_17_;
v_isShared_26_ = v_isSharedCheck_39_;
goto v_resetjp_24_;
}
else
{
lean_inc(v_lctx_23_);
lean_dec(v___x_17_);
v___x_25_ = lean_box(0);
v_isShared_26_ = v_isSharedCheck_39_;
goto v_resetjp_24_;
}
v_resetjp_24_:
{
uint8_t v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_33_; 
v___x_27_ = lean_unbox(v_a_19_);
lean_dec(v_a_19_);
v___x_28_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_23_, v___x_27_);
lean_dec_ref(v_lctx_23_);
v___x_29_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_11_);
v___x_30_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg___closed__2, &l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg___closed__2_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg___closed__2);
v___x_31_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_31_, 0, v_env_16_);
lean_ctor_set(v___x_31_, 1, v___x_30_);
lean_ctor_set(v___x_31_, 2, v___x_28_);
lean_ctor_set(v___x_31_, 3, v___x_29_);
if (v_isShared_26_ == 0)
{
lean_ctor_set_tag(v___x_25_, 3);
lean_ctor_set(v___x_25_, 1, v_msg_8_);
lean_ctor_set(v___x_25_, 0, v___x_31_);
v___x_33_ = v___x_25_;
goto v_reusejp_32_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v___x_31_);
lean_ctor_set(v_reuseFailAlloc_38_, 1, v_msg_8_);
v___x_33_ = v_reuseFailAlloc_38_;
goto v_reusejp_32_;
}
v_reusejp_32_:
{
lean_object* v___x_34_; lean_object* v___x_36_; 
lean_inc(v_ref_14_);
v___x_34_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_34_, 0, v_ref_14_);
lean_ctor_set(v___x_34_, 1, v___x_33_);
if (v_isShared_22_ == 0)
{
lean_ctor_set_tag(v___x_21_, 1);
lean_ctor_set(v___x_21_, 0, v___x_34_);
v___x_36_ = v___x_21_;
goto v_reusejp_35_;
}
else
{
lean_object* v_reuseFailAlloc_37_; 
v_reuseFailAlloc_37_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_37_, 0, v___x_34_);
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
else
{
lean_object* v_a_42_; lean_object* v___x_44_; uint8_t v_isShared_45_; uint8_t v_isSharedCheck_49_; 
lean_dec(v___x_17_);
lean_dec_ref(v_env_16_);
lean_dec_ref(v_msg_8_);
v_a_42_ = lean_ctor_get(v___x_18_, 0);
v_isSharedCheck_49_ = !lean_is_exclusive(v___x_18_);
if (v_isSharedCheck_49_ == 0)
{
v___x_44_ = v___x_18_;
v_isShared_45_ = v_isSharedCheck_49_;
goto v_resetjp_43_;
}
else
{
lean_inc(v_a_42_);
lean_dec(v___x_18_);
v___x_44_ = lean_box(0);
v_isShared_45_ = v_isSharedCheck_49_;
goto v_resetjp_43_;
}
v_resetjp_43_:
{
lean_object* v___x_47_; 
if (v_isShared_45_ == 0)
{
v___x_47_ = v___x_44_;
goto v_reusejp_46_;
}
else
{
lean_object* v_reuseFailAlloc_48_; 
v_reuseFailAlloc_48_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_48_, 0, v_a_42_);
v___x_47_ = v_reuseFailAlloc_48_;
goto v_reusejp_46_;
}
v_reusejp_46_:
{
return v___x_47_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_8_ = stack[0].m_obj;
lean_object* v___y_9_ = stack[1].m_obj;
lean_object* v___y_10_ = stack[2].m_obj;
lean_object* v___y_11_ = stack[3].m_obj;
lean_object* v___y_12_ = stack[4].m_obj;
lean_object* v_res_50_;
v_res_50_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg(v_msg_8_, v___y_9_, v___y_10_, v___y_11_, v___y_12_);
stack->m_obj
 = v_res_50_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg___boxed(lean_object* v_msg_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg(v_msg_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_);
lean_dec(v___y_55_);
lean_dec_ref(v___y_54_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
return v_res_57_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0(lean_object* v_00_u03b1_58_, lean_object* v_msg_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg(v_msg_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_);
return v___x_65_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_59_ = stack[1].m_obj;
lean_object* v___y_60_ = stack[2].m_obj;
lean_object* v___y_61_ = stack[3].m_obj;
lean_object* v___y_62_ = stack[4].m_obj;
lean_object* v___y_63_ = stack[5].m_obj;
lean_object* v_res_66_;
v_res_66_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0(lean_box(0), v_msg_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_);
stack->m_obj
 = v_res_66_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___boxed(lean_object* v_00_u03b1_67_, lean_object* v_msg_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0(v_00_u03b1_67_, v_msg_68_, v___y_69_, v___y_70_, v___y_71_, v___y_72_);
lean_dec(v___y_72_);
lean_dec_ref(v___y_71_);
lean_dec(v___y_70_);
lean_dec_ref(v___y_69_);
return v_res_74_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getOtherDeclType___closed__1(void){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_76_ = ((lean_object*)(l_Lean_Compiler_LCNF_getOtherDeclType___closed__0));
v___x_77_ = l_Lean_stringToMessageData(v___x_76_);
return v___x_77_;
}
}
lean_object* l_Lean_Compiler_LCNF_getOtherDeclType(lean_object* v_declName_78_, lean_object* v_us_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_80_);
if (lean_obj_tag(v___x_85_) == 0)
{
lean_object* v_a_86_; uint8_t v___x_87_; 
v_a_86_ = lean_ctor_get(v___x_85_, 0);
lean_inc(v_a_86_);
lean_dec_ref_known(v___x_85_, 1);
v___x_87_ = lean_unbox(v_a_86_);
lean_dec(v_a_86_);
switch(v___x_87_)
{
case 0:
{
lean_object* v___x_88_; 
v___x_88_ = l_Lean_Compiler_LCNF_getOtherDeclBaseType(v_declName_78_, v_us_79_, v_a_82_, v_a_83_);
return v___x_88_;
}
case 1:
{
lean_object* v___x_89_; 
lean_dec(v_us_79_);
v___x_89_ = l_Lean_Compiler_LCNF_getOtherDeclMonoType(v_declName_78_, v_a_82_, v_a_83_);
return v___x_89_;
}
default: 
{
lean_object* v___x_90_; lean_object* v___x_91_; 
lean_dec(v_us_79_);
lean_dec(v_declName_78_);
v___x_90_ = lean_obj_once(&l_Lean_Compiler_LCNF_getOtherDeclType___closed__1, &l_Lean_Compiler_LCNF_getOtherDeclType___closed__1_once, _init_l_Lean_Compiler_LCNF_getOtherDeclType___closed__1);
v___x_91_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg(v___x_90_, v_a_80_, v_a_81_, v_a_82_, v_a_83_);
return v___x_91_;
}
}
}
else
{
lean_object* v_a_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_99_; 
lean_dec(v_us_79_);
lean_dec(v_declName_78_);
v_a_92_ = lean_ctor_get(v___x_85_, 0);
v_isSharedCheck_99_ = !lean_is_exclusive(v___x_85_);
if (v_isSharedCheck_99_ == 0)
{
v___x_94_ = v___x_85_;
v_isShared_95_ = v_isSharedCheck_99_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_a_92_);
lean_dec(v___x_85_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_99_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v___x_97_; 
if (v_isShared_95_ == 0)
{
v___x_97_ = v___x_94_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v_a_92_);
v___x_97_ = v_reuseFailAlloc_98_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
return v___x_97_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_getOtherDeclType_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_78_ = stack[0].m_obj;
lean_object* v_us_79_ = stack[1].m_obj;
lean_object* v_a_80_ = stack[2].m_obj;
lean_object* v_a_81_ = stack[3].m_obj;
lean_object* v_a_82_ = stack[4].m_obj;
lean_object* v_a_83_ = stack[5].m_obj;
lean_object* v_res_100_;
v_res_100_ = l_Lean_Compiler_LCNF_getOtherDeclType(v_declName_78_, v_us_79_, v_a_80_, v_a_81_, v_a_82_, v_a_83_);
stack->m_obj
 = v_res_100_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getOtherDeclType___boxed(lean_object* v_declName_101_, lean_object* v_us_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Lean_Compiler_LCNF_getOtherDeclType(v_declName_101_, v_us_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_);
lean_dec(v_a_106_);
lean_dec_ref(v_a_105_);
lean_dec(v_a_104_);
lean_dec_ref(v_a_103_);
return v_res_108_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_MonoTypes(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_ToImpureType(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_OtherDecl(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_LCNF_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_MonoTypes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_ToImpureType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_OtherDecl(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_MonoTypes(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_ToImpureType(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_OtherDecl(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_MonoTypes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ToImpureType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_OtherDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_OtherDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_OtherDecl(builtin);
}
#ifdef __cplusplus
}
#endif

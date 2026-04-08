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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getPurity___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*, uint8_t);
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
v___x_1_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
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
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg___closed__1, &l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg___closed__1_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg___closed__1);
v___x_5_ = lean_unsigned_to_nat(0u);
v___x_6_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
lean_ctor_set(v___x_6_, 1, v___x_5_);
lean_ctor_set(v___x_6_, 2, v___x_5_);
lean_ctor_set(v___x_6_, 3, v___x_5_);
lean_ctor_set(v___x_6_, 4, v___x_4_);
lean_ctor_set(v___x_6_, 5, v___x_4_);
lean_ctor_set(v___x_6_, 6, v___x_4_);
lean_ctor_set(v___x_6_, 7, v___x_4_);
lean_ctor_set(v___x_6_, 8, v___x_4_);
lean_ctor_set(v___x_6_, 9, v___x_4_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg(lean_object* v_msg_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_){
_start:
{
lean_object* v_options_13_; lean_object* v_ref_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
v_options_13_ = lean_ctor_get(v___y_10_, 2);
v_ref_14_ = lean_ctor_get(v___y_10_, 5);
v___x_15_ = lean_st_ref_get(v___y_11_);
v___x_16_ = lean_st_ref_get(v___y_9_);
v___x_17_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_8_);
if (lean_obj_tag(v___x_17_) == 0)
{
lean_object* v_a_18_; lean_object* v___x_20_; uint8_t v_isShared_21_; uint8_t v_isSharedCheck_40_; 
v_a_18_ = lean_ctor_get(v___x_17_, 0);
v_isSharedCheck_40_ = !lean_is_exclusive(v___x_17_);
if (v_isSharedCheck_40_ == 0)
{
v___x_20_ = v___x_17_;
v_isShared_21_ = v_isSharedCheck_40_;
goto v_resetjp_19_;
}
else
{
lean_inc(v_a_18_);
lean_dec(v___x_17_);
v___x_20_ = lean_box(0);
v_isShared_21_ = v_isSharedCheck_40_;
goto v_resetjp_19_;
}
v_resetjp_19_:
{
lean_object* v_env_22_; lean_object* v_lctx_23_; lean_object* v___x_25_; uint8_t v_isShared_26_; uint8_t v_isSharedCheck_38_; 
v_env_22_ = lean_ctor_get(v___x_15_, 0);
lean_inc_ref(v_env_22_);
lean_dec(v___x_15_);
v_lctx_23_ = lean_ctor_get(v___x_16_, 0);
v_isSharedCheck_38_ = !lean_is_exclusive(v___x_16_);
if (v_isSharedCheck_38_ == 0)
{
lean_object* v_unused_39_; 
v_unused_39_ = lean_ctor_get(v___x_16_, 1);
lean_dec(v_unused_39_);
v___x_25_ = v___x_16_;
v_isShared_26_ = v_isSharedCheck_38_;
goto v_resetjp_24_;
}
else
{
lean_inc(v_lctx_23_);
lean_dec(v___x_16_);
v___x_25_ = lean_box(0);
v_isShared_26_ = v_isSharedCheck_38_;
goto v_resetjp_24_;
}
v_resetjp_24_:
{
uint8_t v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_32_; 
v___x_27_ = lean_unbox(v_a_18_);
lean_dec(v_a_18_);
v___x_28_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_23_, v___x_27_);
lean_dec_ref(v_lctx_23_);
v___x_29_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg___closed__2, &l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg___closed__2_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg___closed__2);
lean_inc_ref(v_options_13_);
v___x_30_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_30_, 0, v_env_22_);
lean_ctor_set(v___x_30_, 1, v___x_29_);
lean_ctor_set(v___x_30_, 2, v___x_28_);
lean_ctor_set(v___x_30_, 3, v_options_13_);
if (v_isShared_26_ == 0)
{
lean_ctor_set_tag(v___x_25_, 3);
lean_ctor_set(v___x_25_, 1, v_msg_7_);
lean_ctor_set(v___x_25_, 0, v___x_30_);
v___x_32_ = v___x_25_;
goto v_reusejp_31_;
}
else
{
lean_object* v_reuseFailAlloc_37_; 
v_reuseFailAlloc_37_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_37_, 0, v___x_30_);
lean_ctor_set(v_reuseFailAlloc_37_, 1, v_msg_7_);
v___x_32_ = v_reuseFailAlloc_37_;
goto v_reusejp_31_;
}
v_reusejp_31_:
{
lean_object* v___x_33_; lean_object* v___x_35_; 
lean_inc(v_ref_14_);
v___x_33_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_33_, 0, v_ref_14_);
lean_ctor_set(v___x_33_, 1, v___x_32_);
if (v_isShared_21_ == 0)
{
lean_ctor_set_tag(v___x_20_, 1);
lean_ctor_set(v___x_20_, 0, v___x_33_);
v___x_35_ = v___x_20_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_36_; 
v_reuseFailAlloc_36_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_36_, 0, v___x_33_);
v___x_35_ = v_reuseFailAlloc_36_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
return v___x_35_;
}
}
}
}
}
else
{
lean_object* v_a_41_; lean_object* v___x_43_; uint8_t v_isShared_44_; uint8_t v_isSharedCheck_48_; 
lean_dec(v___x_16_);
lean_dec(v___x_15_);
lean_dec_ref(v_msg_7_);
v_a_41_ = lean_ctor_get(v___x_17_, 0);
v_isSharedCheck_48_ = !lean_is_exclusive(v___x_17_);
if (v_isSharedCheck_48_ == 0)
{
v___x_43_ = v___x_17_;
v_isShared_44_ = v_isSharedCheck_48_;
goto v_resetjp_42_;
}
else
{
lean_inc(v_a_41_);
lean_dec(v___x_17_);
v___x_43_ = lean_box(0);
v_isShared_44_ = v_isSharedCheck_48_;
goto v_resetjp_42_;
}
v_resetjp_42_:
{
lean_object* v___x_46_; 
if (v_isShared_44_ == 0)
{
v___x_46_ = v___x_43_;
goto v_reusejp_45_;
}
else
{
lean_object* v_reuseFailAlloc_47_; 
v_reuseFailAlloc_47_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_47_, 0, v_a_41_);
v___x_46_ = v_reuseFailAlloc_47_;
goto v_reusejp_45_;
}
v_reusejp_45_:
{
return v___x_46_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg___boxed(lean_object* v_msg_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg(v_msg_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
lean_dec(v___y_51_);
lean_dec_ref(v___y_50_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0(lean_object* v_00_u03b1_56_, lean_object* v_msg_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg(v_msg_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___boxed(lean_object* v_00_u03b1_64_, lean_object* v_msg_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0(v_00_u03b1_64_, v_msg_65_, v___y_66_, v___y_67_, v___y_68_, v___y_69_);
lean_dec(v___y_69_);
lean_dec_ref(v___y_68_);
lean_dec(v___y_67_);
lean_dec_ref(v___y_66_);
return v_res_71_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getOtherDeclType___closed__1(void){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_73_ = ((lean_object*)(l_Lean_Compiler_LCNF_getOtherDeclType___closed__0));
v___x_74_ = l_Lean_stringToMessageData(v___x_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getOtherDeclType(lean_object* v_declName_75_, lean_object* v_us_76_, lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_77_);
if (lean_obj_tag(v___x_82_) == 0)
{
lean_object* v_a_83_; uint8_t v___x_84_; 
v_a_83_ = lean_ctor_get(v___x_82_, 0);
lean_inc(v_a_83_);
lean_dec_ref(v___x_82_);
v___x_84_ = lean_unbox(v_a_83_);
lean_dec(v_a_83_);
switch(v___x_84_)
{
case 0:
{
lean_object* v___x_85_; 
v___x_85_ = l_Lean_Compiler_LCNF_getOtherDeclBaseType(v_declName_75_, v_us_76_, v_a_79_, v_a_80_);
return v___x_85_;
}
case 1:
{
lean_object* v___x_86_; 
lean_dec(v_us_76_);
v___x_86_ = l_Lean_Compiler_LCNF_getOtherDeclMonoType(v_declName_75_, v_a_79_, v_a_80_);
return v___x_86_;
}
default: 
{
lean_object* v___x_87_; lean_object* v___x_88_; 
lean_dec(v_us_76_);
lean_dec(v_declName_75_);
v___x_87_ = lean_obj_once(&l_Lean_Compiler_LCNF_getOtherDeclType___closed__1, &l_Lean_Compiler_LCNF_getOtherDeclType___closed__1_once, _init_l_Lean_Compiler_LCNF_getOtherDeclType___closed__1);
v___x_88_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg(v___x_87_, v_a_77_, v_a_78_, v_a_79_, v_a_80_);
return v___x_88_;
}
}
}
else
{
lean_object* v_a_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_96_; 
lean_dec(v_us_76_);
lean_dec(v_declName_75_);
v_a_89_ = lean_ctor_get(v___x_82_, 0);
v_isSharedCheck_96_ = !lean_is_exclusive(v___x_82_);
if (v_isSharedCheck_96_ == 0)
{
v___x_91_ = v___x_82_;
v_isShared_92_ = v_isSharedCheck_96_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_a_89_);
lean_dec(v___x_82_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_96_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v___x_94_; 
if (v_isShared_92_ == 0)
{
v___x_94_ = v___x_91_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v_a_89_);
v___x_94_ = v_reuseFailAlloc_95_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
return v___x_94_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getOtherDeclType___boxed(lean_object* v_declName_97_, lean_object* v_us_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l_Lean_Compiler_LCNF_getOtherDeclType(v_declName_97_, v_us_98_, v_a_99_, v_a_100_, v_a_101_, v_a_102_);
lean_dec(v_a_102_);
lean_dec_ref(v_a_101_);
lean_dec(v_a_100_);
lean_dec_ref(v_a_99_);
return v_res_104_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_MonoTypes(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_ToImpureType(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_OtherDecl(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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

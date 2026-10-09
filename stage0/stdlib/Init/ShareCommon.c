// Lean compiler output
// Module: Init.ShareCommon
// Imports: public import Init.Data.UInt.Basic public import Init.Control.State
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
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
LEAN_EXPORT uint8_t l_ShareCommon_Object_ptrEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ShareCommon_Object_ptrEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_ShareCommon_Object_ptrHash(lean_object*);
LEAN_EXPORT lean_object* l_ShareCommon_Object_ptrHash___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ShareCommon_StateFactoryPointed;
uint8_t lean_sharecommon_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ShareCommon_Object_eq___boxed(lean_object*, lean_object*);
uint64_t lean_sharecommon_hash(lean_object*);
LEAN_EXPORT lean_object* l_ShareCommon_Object_hash___boxed(lean_object*);
LEAN_EXPORT uint64_t l_ShareCommon_StateFactory_mkImpl___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_ShareCommon_StateFactory_mkImpl___lam__0___boxed(lean_object*);
static const lean_closure_object l_ShareCommon_StateFactory_mkImpl___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ShareCommon_Object_ptrEq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_ShareCommon_StateFactory_mkImpl___lam__2___closed__0 = (const lean_object*)&l_ShareCommon_StateFactory_mkImpl___lam__2___closed__0_value;
static const lean_closure_object l_ShareCommon_StateFactory_mkImpl___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ShareCommon_Object_eq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_ShareCommon_StateFactory_mkImpl___lam__2___closed__1 = (const lean_object*)&l_ShareCommon_StateFactory_mkImpl___lam__2___closed__1_value;
static const lean_closure_object l_ShareCommon_StateFactory_mkImpl___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ShareCommon_Object_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_ShareCommon_StateFactory_mkImpl___lam__2___closed__2 = (const lean_object*)&l_ShareCommon_StateFactory_mkImpl___lam__2___closed__2_value;
LEAN_EXPORT lean_object* l_ShareCommon_StateFactory_mkImpl___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_ShareCommon_StateFactory_mkImpl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ShareCommon_StateFactory_mkImpl___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_ShareCommon_StateFactory_mkImpl___closed__0 = (const lean_object*)&l_ShareCommon_StateFactory_mkImpl___closed__0_value;
LEAN_EXPORT lean_object* l_ShareCommon_StateFactory_mkImpl(lean_object*);
LEAN_EXPORT lean_object* l_ShareCommon_StateFactory_get(lean_object*);
LEAN_EXPORT lean_object* l_ShareCommon_StateFactory_get___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ShareCommon_StatePointed___redArg();
LEAN_EXPORT lean_object* l_ShareCommon_StatePointed___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ShareCommon_StatePointed(lean_object*);
LEAN_EXPORT lean_object* l_ShareCommon_StatePointed___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ShareCommon_mkStateImpl(lean_object*);
LEAN_EXPORT lean_object* l_ShareCommon_instInhabitedState(lean_object*);
lean_object* lean_state_sharecommon(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ShareCommon_State_shareCommon___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_withShareCommon___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_withShareCommon(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_shareCommonM___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_shareCommonM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ShareCommonT_withShareCommon___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ShareCommonT_withShareCommon___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ShareCommonT_withShareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ShareCommonT_withShareCommon___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ShareCommonT_monadShareCommon___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ShareCommonT_monadShareCommon___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ShareCommonT_monadShareCommon___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ShareCommonT_monadShareCommon(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ShareCommonT_run___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_ShareCommonT_run___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_ShareCommonT_run___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ShareCommonT_run___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_ShareCommonT_run___redArg___closed__0 = (const lean_object*)&l_ShareCommonT_run___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_ShareCommonT_run___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ShareCommonT_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ShareCommonM_run___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ShareCommonM_run(lean_object*, lean_object*, lean_object*);
lean_object* lean_sharecommon_quick(lean_object*);
LEAN_EXPORT lean_object* l_ShareCommon_shareCommon_x27___boxed(lean_object*, lean_object*);
uint8_t l_ShareCommon_Object_ptrEq(lean_object* v_a_1_, lean_object* v_b_2_){
_start:
{
size_t v___x_3_; size_t v___x_4_; uint8_t v___x_5_; 
v___x_3_ = lean_ptr_addr(v_a_1_);
v___x_4_ = lean_ptr_addr(v_b_2_);
v___x_5_ = lean_usize_dec_eq(v___x_3_, v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT void l_ShareCommon_Object_ptrEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1_ = stack[0].m_obj;
lean_object* v_b_2_ = stack[1].m_obj;
uint8_t v_res_6_;
v_res_6_ = l_ShareCommon_Object_ptrEq(v_a_1_, v_b_2_);
stack->m_num = v_res_6_;
}
LEAN_EXPORT lean_object* l_ShareCommon_Object_ptrEq___boxed(lean_object* v_a_7_, lean_object* v_b_8_){
_start:
{
uint8_t v_res_9_; lean_object* v_r_10_; 
v_res_9_ = l_ShareCommon_Object_ptrEq(v_a_7_, v_b_8_);
lean_dec(v_b_8_);
lean_dec(v_a_7_);
v_r_10_ = lean_box(v_res_9_);
return v_r_10_;
}
}
uint64_t l_ShareCommon_Object_ptrHash(lean_object* v_a_11_){
_start:
{
size_t v___x_12_; uint64_t v___x_13_; 
v___x_12_ = lean_ptr_addr(v_a_11_);
v___x_13_ = lean_usize_to_uint64(v___x_12_);
return v___x_13_;
}
}
LEAN_EXPORT void l_ShareCommon_Object_ptrHash_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_11_ = stack[0].m_obj;
uint64_t v_res_14_;
v_res_14_ = l_ShareCommon_Object_ptrHash(v_a_11_);
stack->m_num = v_res_14_;
}
LEAN_EXPORT lean_object* l_ShareCommon_Object_ptrHash___boxed(lean_object* v_a_15_){
_start:
{
uint64_t v_res_16_; lean_object* v_r_17_; 
v_res_16_ = l_ShareCommon_Object_ptrHash(v_a_15_);
lean_dec(v_a_15_);
v_r_17_ = lean_box_uint64(v_res_16_);
return v_r_17_;
}
}
static lean_object* _init_l_ShareCommon_StateFactoryPointed(void){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = lean_box(0);
return v___x_18_;
}
}
LEAN_EXPORT void l_ShareCommon_Object_eq_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_19_ = stack[0].m_obj;
lean_object* v_b_20_ = stack[1].m_obj;
uint8_t v_res_21_;
v_res_21_ = lean_sharecommon_eq(v_a_19_, v_b_20_);
stack->m_num = v_res_21_;
}
LEAN_EXPORT lean_object* l_ShareCommon_Object_eq___boxed(lean_object* v_a_22_, lean_object* v_b_23_){
_start:
{
uint8_t v_res_24_; lean_object* v_r_25_; 
v_res_24_ = lean_sharecommon_eq(v_a_22_, v_b_23_);
lean_dec(v_b_23_);
lean_dec(v_a_22_);
v_r_25_ = lean_box(v_res_24_);
return v_r_25_;
}
}
LEAN_EXPORT void l_ShareCommon_Object_hash_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_26_ = stack[0].m_obj;
uint64_t v_res_27_;
v_res_27_ = lean_sharecommon_hash(v_a_26_);
stack->m_num = v_res_27_;
}
LEAN_EXPORT lean_object* l_ShareCommon_Object_hash___boxed(lean_object* v_a_28_){
_start:
{
uint64_t v_res_29_; lean_object* v_r_30_; 
v_res_29_ = lean_sharecommon_hash(v_a_28_);
lean_dec(v_a_28_);
v_r_30_ = lean_box_uint64(v_res_29_);
return v_r_30_;
}
}
uint64_t l_ShareCommon_StateFactory_mkImpl___lam__0(lean_object* v___y_31_){
_start:
{
size_t v___x_32_; uint64_t v___x_33_; 
v___x_32_ = lean_ptr_addr(v___y_31_);
v___x_33_ = lean_usize_to_uint64(v___x_32_);
return v___x_33_;
}
}
LEAN_EXPORT void l_ShareCommon_StateFactory_mkImpl___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_31_ = stack[0].m_obj;
uint64_t v_res_34_;
v_res_34_ = l_ShareCommon_StateFactory_mkImpl___lam__0(v___y_31_);
stack->m_num = v_res_34_;
}
LEAN_EXPORT lean_object* l_ShareCommon_StateFactory_mkImpl___lam__0___boxed(lean_object* v___y_35_){
_start:
{
uint64_t v_res_36_; lean_object* v_r_37_; 
v_res_36_ = l_ShareCommon_StateFactory_mkImpl___lam__0(v___y_35_);
lean_dec(v___y_35_);
v_r_37_ = lean_box_uint64(v_res_36_);
return v_r_37_;
}
}
LEAN_EXPORT lean_object* l_ShareCommon_StateFactory_mkImpl___lam__2(lean_object* v_mkMap_41_, lean_object* v___f_42_, lean_object* v_mkSet_43_, lean_object* v_x_44_){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_45_ = ((lean_object*)(l_ShareCommon_StateFactory_mkImpl___lam__2___closed__0));
v___x_46_ = lean_unsigned_to_nat(1024u);
v___x_47_ = lean_apply_5(v_mkMap_41_, lean_box(0), lean_box(0), v___x_45_, v___f_42_, v___x_46_);
v___x_48_ = ((lean_object*)(l_ShareCommon_StateFactory_mkImpl___lam__2___closed__1));
v___x_49_ = ((lean_object*)(l_ShareCommon_StateFactory_mkImpl___lam__2___closed__2));
v___x_50_ = lean_apply_4(v_mkSet_43_, lean_box(0), v___x_48_, v___x_49_, v___x_46_);
v___x_51_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_51_, 0, v___x_47_);
lean_ctor_set(v___x_51_, 1, v___x_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_ShareCommon_StateFactory_mkImpl(lean_object* v_x_53_){
_start:
{
lean_object* v_mkMap_54_; lean_object* v_mapFind_x3f_55_; lean_object* v_mapInsert_56_; lean_object* v_mkSet_57_; lean_object* v_setFind_x3f_58_; lean_object* v_setInsert_59_; lean_object* v___f_60_; lean_object* v___f_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v_mkMap_54_ = lean_ctor_get(v_x_53_, 0);
lean_inc(v_mkMap_54_);
v_mapFind_x3f_55_ = lean_ctor_get(v_x_53_, 1);
lean_inc_ref(v_mapFind_x3f_55_);
v_mapInsert_56_ = lean_ctor_get(v_x_53_, 2);
lean_inc(v_mapInsert_56_);
v_mkSet_57_ = lean_ctor_get(v_x_53_, 3);
lean_inc(v_mkSet_57_);
v_setFind_x3f_58_ = lean_ctor_get(v_x_53_, 4);
lean_inc_ref(v_setFind_x3f_58_);
v_setInsert_59_ = lean_ctor_get(v_x_53_, 5);
lean_inc(v_setInsert_59_);
lean_dec_ref(v_x_53_);
v___f_60_ = ((lean_object*)(l_ShareCommon_StateFactory_mkImpl___closed__0));
v___f_61_ = lean_alloc_closure((void*)(l_ShareCommon_StateFactory_mkImpl___lam__2), 4, 3);
lean_closure_set(v___f_61_, 0, v_mkMap_54_);
lean_closure_set(v___f_61_, 1, v___f_60_);
lean_closure_set(v___f_61_, 2, v_mkSet_57_);
v___x_62_ = ((lean_object*)(l_ShareCommon_StateFactory_mkImpl___lam__2___closed__0));
v___x_63_ = lean_apply_4(v_mapFind_x3f_55_, lean_box(0), lean_box(0), v___x_62_, v___f_60_);
v___x_64_ = lean_apply_4(v_mapInsert_56_, lean_box(0), lean_box(0), v___x_62_, v___f_60_);
v___x_65_ = ((lean_object*)(l_ShareCommon_StateFactory_mkImpl___lam__2___closed__1));
v___x_66_ = ((lean_object*)(l_ShareCommon_StateFactory_mkImpl___lam__2___closed__2));
v___x_67_ = lean_apply_3(v_setFind_x3f_58_, lean_box(0), v___x_65_, v___x_66_);
v___x_68_ = lean_apply_3(v_setInsert_59_, lean_box(0), v___x_65_, v___x_66_);
v___x_69_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_69_, 0, v___f_61_);
lean_ctor_set(v___x_69_, 1, v___x_63_);
lean_ctor_set(v___x_69_, 2, v___x_64_);
lean_ctor_set(v___x_69_, 3, v___x_67_);
lean_ctor_set(v___x_69_, 4, v___x_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_ShareCommon_StateFactory_get(lean_object* v_a_70_){
_start:
{
lean_inc(v_a_70_);
return v_a_70_;
}
}
LEAN_EXPORT lean_object* l_ShareCommon_StateFactory_get___boxed(lean_object* v_a_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_ShareCommon_StateFactory_get(v_a_71_);
lean_dec(v_a_71_);
return v_res_72_;
}
}
lean_object* l_ShareCommon_StatePointed___redArg(){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = lean_box(0);
return v___x_74_;
}
}
LEAN_EXPORT void l_ShareCommon_StatePointed___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_75_;
v_res_75_ = l_ShareCommon_StatePointed___redArg();
stack->m_obj
 = v_res_75_;
}
LEAN_EXPORT lean_object* l_ShareCommon_StatePointed___redArg___boxed(lean_object* v___dummy_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l_ShareCommon_StatePointed___redArg();
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l_ShareCommon_StatePointed(lean_object* v_00_u03c3_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = lean_box(0);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_ShareCommon_StatePointed___boxed(lean_object* v_00_u03c3_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_ShareCommon_StatePointed(v_00_u03c3_80_);
lean_dec(v_00_u03c3_80_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_ShareCommon_mkStateImpl(lean_object* v_00_u03c3_82_){
_start:
{
lean_object* v_mkState_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v_mkState_83_ = lean_ctor_get(v_00_u03c3_82_, 0);
lean_inc_ref(v_mkState_83_);
lean_dec(v_00_u03c3_82_);
v___x_84_ = lean_box(0);
v___x_85_ = lean_apply_1(v_mkState_83_, v___x_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_ShareCommon_instInhabitedState(lean_object* v_00_u03c3_86_){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = l_ShareCommon_mkStateImpl(v_00_u03c3_86_);
return v___x_87_;
}
}
LEAN_EXPORT void l_ShareCommon_State_shareCommon_0interp(lean_interpreter_value* stack)
{
lean_object* v_00_u03c3_89_ = stack[1].m_obj;
lean_object* v_s_90_ = stack[2].m_obj;
lean_object* v_a_91_ = stack[3].m_obj;
lean_object* v_res_92_;
v_res_92_ = lean_state_sharecommon(v_00_u03c3_89_, v_s_90_, v_a_91_);
stack->m_obj
 = v_res_92_;
}
LEAN_EXPORT lean_object* l_ShareCommon_State_shareCommon___boxed(lean_object* v_00_u03b1_93_, lean_object* v_00_u03c3_94_, lean_object* v_s_95_, lean_object* v_a_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = lean_state_sharecommon(v_00_u03c3_94_, v_s_95_, v_a_96_);
lean_dec(v_00_u03c3_94_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l_withShareCommon___redArg(lean_object* v_self_98_, lean_object* v_a_99_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = lean_apply_2(v_self_98_, lean_box(0), v_a_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_withShareCommon(lean_object* v_m_101_, lean_object* v_self_102_, lean_object* v_00_u03b1_103_, lean_object* v_a_104_){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = lean_apply_2(v_self_102_, lean_box(0), v_a_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_shareCommonM___redArg(lean_object* v_inst_106_, lean_object* v_a_107_){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = lean_apply_2(v_inst_106_, lean_box(0), v_a_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_shareCommonM(lean_object* v_m_109_, lean_object* v_00_u03b1_110_, lean_object* v_inst_111_, lean_object* v_a_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = lean_apply_2(v_inst_111_, lean_box(0), v_a_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_ShareCommonT_withShareCommon___redArg(lean_object* v_00_u03c3_114_, lean_object* v_inst_115_, lean_object* v_a_116_, lean_object* v_a_117_){
_start:
{
lean_object* v_toApplicative_118_; lean_object* v_toPure_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v_toApplicative_118_ = lean_ctor_get(v_inst_115_, 0);
lean_inc_ref(v_toApplicative_118_);
lean_dec_ref(v_inst_115_);
v_toPure_119_ = lean_ctor_get(v_toApplicative_118_, 1);
lean_inc(v_toPure_119_);
lean_dec_ref(v_toApplicative_118_);
v___x_120_ = lean_state_sharecommon(v_00_u03c3_114_, v_a_117_, v_a_116_);
v___x_121_ = lean_apply_2(v_toPure_119_, lean_box(0), v___x_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_ShareCommonT_withShareCommon___redArg___boxed(lean_object* v_00_u03c3_122_, lean_object* v_inst_123_, lean_object* v_a_124_, lean_object* v_a_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_ShareCommonT_withShareCommon___redArg(v_00_u03c3_122_, v_inst_123_, v_a_124_, v_a_125_);
lean_dec(v_00_u03c3_122_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l_ShareCommonT_withShareCommon(lean_object* v_m_127_, lean_object* v_00_u03b1_128_, lean_object* v_00_u03c3_129_, lean_object* v_inst_130_, lean_object* v_a_131_, lean_object* v_a_132_){
_start:
{
lean_object* v___x_133_; 
v___x_133_ = l_ShareCommonT_withShareCommon___redArg(v_00_u03c3_129_, v_inst_130_, v_a_131_, v_a_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_ShareCommonT_withShareCommon___boxed(lean_object* v_m_134_, lean_object* v_00_u03b1_135_, lean_object* v_00_u03c3_136_, lean_object* v_inst_137_, lean_object* v_a_138_, lean_object* v_a_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_ShareCommonT_withShareCommon(v_m_134_, v_00_u03b1_135_, v_00_u03c3_136_, v_inst_137_, v_a_138_, v_a_139_);
lean_dec(v_00_u03c3_136_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_ShareCommonT_monadShareCommon___redArg___lam__0(lean_object* v_00_u03c3_141_, lean_object* v_inst_142_, lean_object* v_00_u03b1_143_, lean_object* v___y_144_, lean_object* v___y_145_){
_start:
{
lean_object* v___x_146_; 
v___x_146_ = l_ShareCommonT_withShareCommon___redArg(v_00_u03c3_141_, v_inst_142_, v___y_144_, v___y_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_ShareCommonT_monadShareCommon___redArg___lam__0___boxed(lean_object* v_00_u03c3_147_, lean_object* v_inst_148_, lean_object* v_00_u03b1_149_, lean_object* v___y_150_, lean_object* v___y_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_ShareCommonT_monadShareCommon___redArg___lam__0(v_00_u03c3_147_, v_inst_148_, v_00_u03b1_149_, v___y_150_, v___y_151_);
lean_dec(v_00_u03c3_147_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l_ShareCommonT_monadShareCommon___redArg(lean_object* v_00_u03c3_153_, lean_object* v_inst_154_){
_start:
{
lean_object* v___f_155_; 
v___f_155_ = lean_alloc_closure((void*)(l_ShareCommonT_monadShareCommon___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_155_, 0, v_00_u03c3_153_);
lean_closure_set(v___f_155_, 1, v_inst_154_);
return v___f_155_;
}
}
LEAN_EXPORT lean_object* l_ShareCommonT_monadShareCommon(lean_object* v_m_156_, lean_object* v_00_u03c3_157_, lean_object* v_inst_158_){
_start:
{
lean_object* v___f_159_; 
v___f_159_ = lean_alloc_closure((void*)(l_ShareCommonT_monadShareCommon___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_159_, 0, v_00_u03c3_157_);
lean_closure_set(v___f_159_, 1, v_inst_158_);
return v___f_159_;
}
}
LEAN_EXPORT lean_object* l_ShareCommonT_run___redArg___lam__0(lean_object* v_x_160_){
_start:
{
lean_object* v_fst_161_; 
v_fst_161_ = lean_ctor_get(v_x_160_, 0);
lean_inc(v_fst_161_);
return v_fst_161_;
}
}
LEAN_EXPORT lean_object* l_ShareCommonT_run___redArg___lam__0___boxed(lean_object* v_x_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l_ShareCommonT_run___redArg___lam__0(v_x_162_);
lean_dec_ref(v_x_162_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l_ShareCommonT_run___redArg(lean_object* v_00_u03c3_165_, lean_object* v_inst_166_, lean_object* v_x_167_){
_start:
{
lean_object* v_toApplicative_168_; lean_object* v_toFunctor_169_; lean_object* v_map_170_; lean_object* v___f_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v_toApplicative_168_ = lean_ctor_get(v_inst_166_, 0);
lean_inc_ref(v_toApplicative_168_);
lean_dec_ref(v_inst_166_);
v_toFunctor_169_ = lean_ctor_get(v_toApplicative_168_, 0);
lean_inc_ref(v_toFunctor_169_);
lean_dec_ref(v_toApplicative_168_);
v_map_170_ = lean_ctor_get(v_toFunctor_169_, 0);
lean_inc(v_map_170_);
lean_dec_ref(v_toFunctor_169_);
v___f_171_ = ((lean_object*)(l_ShareCommonT_run___redArg___closed__0));
v___x_172_ = l_ShareCommon_mkStateImpl(v_00_u03c3_165_);
v___x_173_ = lean_apply_1(v_x_167_, v___x_172_);
v___x_174_ = lean_apply_4(v_map_170_, lean_box(0), lean_box(0), v___f_171_, v___x_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_ShareCommonT_run(lean_object* v_m_175_, lean_object* v_00_u03c3_176_, lean_object* v_00_u03b1_177_, lean_object* v_inst_178_, lean_object* v_x_179_){
_start:
{
lean_object* v_toApplicative_180_; lean_object* v_toFunctor_181_; lean_object* v_map_182_; lean_object* v___f_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v_toApplicative_180_ = lean_ctor_get(v_inst_178_, 0);
lean_inc_ref(v_toApplicative_180_);
lean_dec_ref(v_inst_178_);
v_toFunctor_181_ = lean_ctor_get(v_toApplicative_180_, 0);
lean_inc_ref(v_toFunctor_181_);
lean_dec_ref(v_toApplicative_180_);
v_map_182_ = lean_ctor_get(v_toFunctor_181_, 0);
lean_inc(v_map_182_);
lean_dec_ref(v_toFunctor_181_);
v___f_183_ = ((lean_object*)(l_ShareCommonT_run___redArg___closed__0));
v___x_184_ = l_ShareCommon_mkStateImpl(v_00_u03c3_176_);
v___x_185_ = lean_apply_1(v_x_179_, v___x_184_);
v___x_186_ = lean_apply_4(v_map_182_, lean_box(0), lean_box(0), v___f_183_, v___x_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_ShareCommonM_run___redArg(lean_object* v_00_u03c3_187_, lean_object* v_x_188_){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v_fst_191_; 
v___x_189_ = l_ShareCommon_mkStateImpl(v_00_u03c3_187_);
v___x_190_ = lean_apply_1(v_x_188_, v___x_189_);
v_fst_191_ = lean_ctor_get(v___x_190_, 0);
lean_inc(v_fst_191_);
lean_dec_ref(v___x_190_);
return v_fst_191_;
}
}
LEAN_EXPORT lean_object* l_ShareCommonM_run(lean_object* v_00_u03c3_192_, lean_object* v_00_u03b1_193_, lean_object* v_x_194_){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v_fst_197_; 
v___x_195_ = l_ShareCommon_mkStateImpl(v_00_u03c3_192_);
v___x_196_ = lean_apply_1(v_x_194_, v___x_195_);
v_fst_197_ = lean_ctor_get(v___x_196_, 0);
lean_inc(v_fst_197_);
lean_dec_ref(v___x_196_);
return v_fst_197_;
}
}
LEAN_EXPORT void l_ShareCommon_shareCommon_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_199_ = stack[1].m_obj;
lean_object* v_res_200_;
v_res_200_ = lean_sharecommon_quick(v_a_199_);
stack->m_obj
 = v_res_200_;
}
LEAN_EXPORT lean_object* l_ShareCommon_shareCommon_x27___boxed(lean_object* v_00_u03b1_201_, lean_object* v_a_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = lean_sharecommon_quick(v_a_202_);
lean_dec(v_a_202_);
return v_res_203_;
}
}
lean_object* runtime_initialize_Init_Data_UInt_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_State(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_ShareCommon(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_UInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_State(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_ShareCommon_StateFactoryPointed = _init_l_ShareCommon_StateFactoryPointed();
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_ShareCommon(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_UInt_Basic(uint8_t builtin);
lean_object* initialize_Init_Control_State(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_ShareCommon(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_UInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_State(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ShareCommon(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_ShareCommon(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_ShareCommon(builtin);
}
#ifdef __cplusplus
}
#endif

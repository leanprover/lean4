// Lean compiler output
// Module: Lean.ImportingFlag
// Imports: public import Init.System.IO
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
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t lean_io_initializing();
LEAN_EXPORT lean_object* l___private_Lean_ImportingFlag_0__Lean_initFn_00___x40_Lean_ImportingFlag_1124607303____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_ImportingFlag_0__Lean_initFn_00___x40_Lean_ImportingFlag_1124607303____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ImportingFlag_0__Lean_importingRef;
LEAN_EXPORT lean_object* l___private_Lean_ImportingFlag_0__Lean_initFn_00___x40_Lean_ImportingFlag_2251799370____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_ImportingFlag_0__Lean_initFn_00___x40_Lean_ImportingFlag_2251799370____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ImportingFlag_0__Lean_runInitializersRef;
LEAN_EXPORT lean_object* lean_enable_initializer_execution();
LEAN_EXPORT lean_object* l_Lean_enableInitializersExecution___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_isInitializerExecutionEnabled();
LEAN_EXPORT lean_object* l_Lean_isInitializerExecutionEnabled___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_initializing();
LEAN_EXPORT lean_object* l_Lean_initializing___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withImporting___redArg___lam__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withImporting___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withImporting___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withImporting___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withImporting(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withImporting___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_set_initializing(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_ImportingFlag_0__Lean_setInitializing___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_ImportingFlag_0__Lean_initFn_00___x40_Lean_ImportingFlag_1124607303____hygCtx___hyg_2_(){
_start:
{
uint8_t v___x_2_; lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_2_ = 0;
v___x_3_ = lean_box(v___x_2_);
v___x_4_ = lean_st_mk_ref(v___x_3_);
v___x_5_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5_, 0, v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT void l___private_Lean_ImportingFlag_0__Lean_initFn_00___x40_Lean_ImportingFlag_1124607303____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_6_;
v_res_6_ = l___private_Lean_ImportingFlag_0__Lean_initFn_00___x40_Lean_ImportingFlag_1124607303____hygCtx___hyg_2_();
stack->m_obj
 = v_res_6_;
}
LEAN_EXPORT lean_object* l___private_Lean_ImportingFlag_0__Lean_initFn_00___x40_Lean_ImportingFlag_1124607303____hygCtx___hyg_2____boxed(lean_object* v_a_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l___private_Lean_ImportingFlag_0__Lean_initFn_00___x40_Lean_ImportingFlag_1124607303____hygCtx___hyg_2_();
return v_res_8_;
}
}
lean_object* l___private_Lean_ImportingFlag_0__Lean_initFn_00___x40_Lean_ImportingFlag_2251799370____hygCtx___hyg_2_(){
_start:
{
uint8_t v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_10_ = 0;
v___x_11_ = lean_box(v___x_10_);
v___x_12_ = lean_st_mk_ref(v___x_11_);
v___x_13_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_13_, 0, v___x_12_);
return v___x_13_;
}
}
LEAN_EXPORT void l___private_Lean_ImportingFlag_0__Lean_initFn_00___x40_Lean_ImportingFlag_2251799370____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_14_;
v_res_14_ = l___private_Lean_ImportingFlag_0__Lean_initFn_00___x40_Lean_ImportingFlag_2251799370____hygCtx___hyg_2_();
stack->m_obj
 = v_res_14_;
}
LEAN_EXPORT lean_object* l___private_Lean_ImportingFlag_0__Lean_initFn_00___x40_Lean_ImportingFlag_2251799370____hygCtx___hyg_2____boxed(lean_object* v_a_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l___private_Lean_ImportingFlag_0__Lean_initFn_00___x40_Lean_ImportingFlag_2251799370____hygCtx___hyg_2_();
return v_res_16_;
}
}
lean_object* lean_enable_initializer_execution(){
_start:
{
lean_object* v___x_18_; uint8_t v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_18_ = l___private_Lean_ImportingFlag_0__Lean_runInitializersRef;
v___x_19_ = 1;
v___x_20_ = lean_box(0);
v___x_21_ = lean_box(v___x_19_);
v___x_22_ = lean_st_ref_swap(v___x_18_, v___x_21_);
lean_dec(v___x_22_);
return v___x_20_;
}
}
LEAN_EXPORT void lean_enable_initializer_execution_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_23_;
v_res_23_ = lean_enable_initializer_execution();
stack->m_obj
 = v_res_23_;
}
LEAN_EXPORT lean_object* l_Lean_enableInitializersExecution___boxed(lean_object* v_a_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = lean_enable_initializer_execution();
return v_res_25_;
}
}
uint8_t l_Lean_isInitializerExecutionEnabled(){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; uint8_t v___x_29_; 
v___x_27_ = l___private_Lean_ImportingFlag_0__Lean_runInitializersRef;
v___x_28_ = lean_st_ref_get(v___x_27_);
v___x_29_ = lean_unbox(v___x_28_);
lean_dec(v___x_28_);
return v___x_29_;
}
}
LEAN_EXPORT void l_Lean_isInitializerExecutionEnabled_0interp(lean_interpreter_value* stack)
{
uint8_t v_res_30_;
v_res_30_ = l_Lean_isInitializerExecutionEnabled();
stack->m_num = v_res_30_;
}
LEAN_EXPORT lean_object* l_Lean_isInitializerExecutionEnabled___boxed(lean_object* v_a_31_){
_start:
{
uint8_t v_res_32_; lean_object* v_r_33_; 
v_res_32_ = l_Lean_isInitializerExecutionEnabled();
v_r_33_ = lean_box(v_res_32_);
return v_r_33_;
}
}
uint8_t l_Lean_initializing(){
_start:
{
uint8_t v___x_35_; 
v___x_35_ = lean_io_initializing();
if (v___x_35_ == 0)
{
lean_object* v___x_36_; lean_object* v___x_37_; uint8_t v___x_38_; 
v___x_36_ = l___private_Lean_ImportingFlag_0__Lean_importingRef;
v___x_37_ = lean_st_ref_get(v___x_36_);
v___x_38_ = lean_unbox(v___x_37_);
lean_dec(v___x_37_);
return v___x_38_;
}
else
{
return v___x_35_;
}
}
}
LEAN_EXPORT void l_Lean_initializing_0interp(lean_interpreter_value* stack)
{
uint8_t v_res_39_;
v_res_39_ = l_Lean_initializing();
stack->m_num = v_res_39_;
}
LEAN_EXPORT lean_object* l_Lean_initializing___boxed(lean_object* v_a_40_){
_start:
{
uint8_t v_res_41_; lean_object* v_r_42_; 
v_res_41_ = l_Lean_initializing();
v_r_42_ = lean_box(v_res_41_);
return v_r_42_;
}
}
lean_object* l_Lean_withImporting___redArg___lam__0(lean_object* v___x_43_, uint8_t v___x_44_, lean_object* v_x_45_){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_47_ = lean_box(v___x_44_);
v___x_48_ = lean_st_ref_swap(v___x_43_, v___x_47_);
lean_dec(v___x_48_);
v___x_49_ = l___private_Lean_ImportingFlag_0__Lean_runInitializersRef;
v___x_50_ = lean_box(0);
v___x_51_ = lean_box(v___x_44_);
v___x_52_ = lean_st_ref_swap(v___x_49_, v___x_51_);
lean_dec(v___x_52_);
v___x_53_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_53_, 0, v___x_50_);
return v___x_53_;
}
}
LEAN_EXPORT void l_Lean_withImporting___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_43_ = stack[0].m_obj;
uint8_t v___x_44_ = stack[1].m_num;
lean_object* v_x_45_ = stack[2].m_obj;
lean_object* v_res_54_;
v_res_54_ = l_Lean_withImporting___redArg___lam__0(v___x_43_, v___x_44_, v_x_45_);
stack->m_obj
 = v_res_54_;
}
LEAN_EXPORT lean_object* l_Lean_withImporting___redArg___lam__0___boxed(lean_object* v___x_55_, lean_object* v___x_56_, lean_object* v_x_57_, lean_object* v___y_58_){
_start:
{
uint8_t v___x_371__boxed_59_; lean_object* v_res_60_; 
v___x_371__boxed_59_ = lean_unbox(v___x_56_);
v_res_60_ = l_Lean_withImporting___redArg___lam__0(v___x_55_, v___x_371__boxed_59_, v_x_57_);
lean_dec(v_x_57_);
lean_dec(v___x_55_);
return v_res_60_;
}
}
lean_object* l_Lean_withImporting___redArg(lean_object* v_x_61_){
_start:
{
lean_object* v___x_63_; uint8_t v___x_64_; uint8_t v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v_r_68_; 
v___x_63_ = l___private_Lean_ImportingFlag_0__Lean_importingRef;
v___x_64_ = 1;
v___x_65_ = 0;
v___x_66_ = lean_box(v___x_64_);
v___x_67_ = lean_st_ref_swap(v___x_63_, v___x_66_);
lean_dec(v___x_67_);
v_r_68_ = lean_apply_1(v_x_61_, lean_box(0));
if (lean_obj_tag(v_r_68_) == 0)
{
lean_object* v_a_69_; lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_85_; 
v_a_69_ = lean_ctor_get(v_r_68_, 0);
v_isSharedCheck_85_ = !lean_is_exclusive(v_r_68_);
if (v_isSharedCheck_85_ == 0)
{
v___x_71_ = v_r_68_;
v_isShared_72_ = v_isSharedCheck_85_;
goto v_resetjp_70_;
}
else
{
lean_inc(v_a_69_);
lean_dec(v_r_68_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_85_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
lean_object* v___x_74_; 
lean_inc(v_a_69_);
if (v_isShared_72_ == 0)
{
lean_ctor_set_tag(v___x_71_, 1);
v___x_74_ = v___x_71_;
goto v_reusejp_73_;
}
else
{
lean_object* v_reuseFailAlloc_84_; 
v_reuseFailAlloc_84_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_84_, 0, v_a_69_);
v___x_74_ = v_reuseFailAlloc_84_;
goto v_reusejp_73_;
}
v_reusejp_73_:
{
lean_object* v___x_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_82_; 
v___x_75_ = l_Lean_withImporting___redArg___lam__0(v___x_63_, v___x_65_, v___x_74_);
lean_dec_ref(v___x_74_);
v_isSharedCheck_82_ = !lean_is_exclusive(v___x_75_);
if (v_isSharedCheck_82_ == 0)
{
lean_object* v_unused_83_; 
v_unused_83_ = lean_ctor_get(v___x_75_, 0);
lean_dec(v_unused_83_);
v___x_77_ = v___x_75_;
v_isShared_78_ = v_isSharedCheck_82_;
goto v_resetjp_76_;
}
else
{
lean_dec(v___x_75_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_82_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
lean_object* v___x_80_; 
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 0, v_a_69_);
v___x_80_ = v___x_77_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v_a_69_);
v___x_80_ = v_reuseFailAlloc_81_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
return v___x_80_;
}
}
}
}
}
else
{
lean_object* v_a_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_95_; 
v_a_86_ = lean_ctor_get(v_r_68_, 0);
lean_inc(v_a_86_);
lean_dec_ref_known(v_r_68_, 1);
v___x_87_ = lean_box(0);
v___x_88_ = l_Lean_withImporting___redArg___lam__0(v___x_63_, v___x_65_, v___x_87_);
v_isSharedCheck_95_ = !lean_is_exclusive(v___x_88_);
if (v_isSharedCheck_95_ == 0)
{
lean_object* v_unused_96_; 
v_unused_96_ = lean_ctor_get(v___x_88_, 0);
lean_dec(v_unused_96_);
v___x_90_ = v___x_88_;
v_isShared_91_ = v_isSharedCheck_95_;
goto v_resetjp_89_;
}
else
{
lean_dec(v___x_88_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_95_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
lean_object* v___x_93_; 
if (v_isShared_91_ == 0)
{
lean_ctor_set_tag(v___x_90_, 1);
lean_ctor_set(v___x_90_, 0, v_a_86_);
v___x_93_ = v___x_90_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v_a_86_);
v___x_93_ = v_reuseFailAlloc_94_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
return v___x_93_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_withImporting___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_61_ = stack[0].m_obj;
lean_object* v_res_97_;
v_res_97_ = l_Lean_withImporting___redArg(v_x_61_);
stack->m_obj
 = v_res_97_;
}
LEAN_EXPORT lean_object* l_Lean_withImporting___redArg___boxed(lean_object* v_x_98_, lean_object* v_a_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Lean_withImporting___redArg(v_x_98_);
return v_res_100_;
}
}
lean_object* l_Lean_withImporting(lean_object* v_00_u03b1_101_, lean_object* v_x_102_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = l_Lean_withImporting___redArg(v_x_102_);
return v___x_104_;
}
}
LEAN_EXPORT void l_Lean_withImporting_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_102_ = stack[1].m_obj;
lean_object* v_res_105_;
v_res_105_ = l_Lean_withImporting(lean_box(0), v_x_102_);
stack->m_obj
 = v_res_105_;
}
LEAN_EXPORT lean_object* l_Lean_withImporting___boxed(lean_object* v_00_u03b1_106_, lean_object* v_x_107_, lean_object* v_a_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = l_Lean_withImporting(v_00_u03b1_106_, v_x_107_);
return v_res_109_;
}
}
lean_object* lean_set_initializing(uint8_t v_initializing_110_){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_112_ = l___private_Lean_ImportingFlag_0__Lean_importingRef;
v___x_113_ = lean_box(0);
v___x_114_ = lean_box(v_initializing_110_);
v___x_115_ = lean_st_ref_swap(v___x_112_, v___x_114_);
lean_dec(v___x_115_);
return v___x_113_;
}
}
LEAN_EXPORT void lean_set_initializing_0interp(lean_interpreter_value* stack)
{
uint8_t v_initializing_110_ = stack[0].m_num;
lean_object* v_res_116_;
v_res_116_ = lean_set_initializing(v_initializing_110_);
stack->m_obj
 = v_res_116_;
}
LEAN_EXPORT lean_object* l___private_Lean_ImportingFlag_0__Lean_setInitializing___boxed(lean_object* v_initializing_117_, lean_object* v_a_118_){
_start:
{
uint8_t v_initializing_boxed_119_; lean_object* v_res_120_; 
v_initializing_boxed_119_ = lean_unbox(v_initializing_117_);
v_res_120_ = lean_set_initializing(v_initializing_boxed_119_);
return v_res_120_;
}
}
lean_object* runtime_initialize_Init_System_IO(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_ImportingFlag(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_ImportingFlag_0__Lean_initFn_00___x40_Lean_ImportingFlag_1124607303____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_ImportingFlag_0__Lean_importingRef = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_ImportingFlag_0__Lean_importingRef);
lean_dec_ref(res);
res = l___private_Lean_ImportingFlag_0__Lean_initFn_00___x40_Lean_ImportingFlag_2251799370____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_ImportingFlag_0__Lean_runInitializersRef = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_ImportingFlag_0__Lean_runInitializersRef);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_ImportingFlag(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_System_IO(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_ImportingFlag(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_ImportingFlag(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_ImportingFlag(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_ImportingFlag(builtin);
}
#ifdef __cplusplus
}
#endif

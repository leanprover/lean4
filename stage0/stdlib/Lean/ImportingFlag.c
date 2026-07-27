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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_ImportingFlag_0__Lean_initFn_00___x40_Lean_ImportingFlag_1124607303____hygCtx___hyg_2_(){
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
LEAN_EXPORT lean_object* l___private_Lean_ImportingFlag_0__Lean_initFn_00___x40_Lean_ImportingFlag_1124607303____hygCtx___hyg_2____boxed(lean_object* v_a_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = l___private_Lean_ImportingFlag_0__Lean_initFn_00___x40_Lean_ImportingFlag_1124607303____hygCtx___hyg_2_();
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ImportingFlag_0__Lean_initFn_00___x40_Lean_ImportingFlag_2251799370____hygCtx___hyg_2_(){
_start:
{
uint8_t v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_9_ = 0;
v___x_10_ = lean_box(v___x_9_);
v___x_11_ = lean_st_mk_ref(v___x_10_);
v___x_12_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_12_, 0, v___x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ImportingFlag_0__Lean_initFn_00___x40_Lean_ImportingFlag_2251799370____hygCtx___hyg_2____boxed(lean_object* v_a_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l___private_Lean_ImportingFlag_0__Lean_initFn_00___x40_Lean_ImportingFlag_2251799370____hygCtx___hyg_2_();
return v_res_14_;
}
}
LEAN_EXPORT lean_object* lean_enable_initializer_execution(){
_start:
{
lean_object* v___x_16_; uint8_t v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_16_ = l___private_Lean_ImportingFlag_0__Lean_runInitializersRef;
v___x_17_ = 1;
v___x_18_ = lean_box(v___x_17_);
v___x_19_ = lean_st_ref_set(v___x_16_, v___x_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_enableInitializersExecution___boxed(lean_object* v_a_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = lean_enable_initializer_execution();
return v_res_21_;
}
}
LEAN_EXPORT uint8_t l_Lean_isInitializerExecutionEnabled(){
_start:
{
lean_object* v___x_23_; lean_object* v___x_24_; uint8_t v___x_25_; 
v___x_23_ = l___private_Lean_ImportingFlag_0__Lean_runInitializersRef;
v___x_24_ = lean_st_ref_get(v___x_23_);
v___x_25_ = lean_unbox(v___x_24_);
lean_dec(v___x_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInitializerExecutionEnabled___boxed(lean_object* v_a_26_){
_start:
{
uint8_t v_res_27_; lean_object* v_r_28_; 
v_res_27_ = l_Lean_isInitializerExecutionEnabled();
v_r_28_ = lean_box(v_res_27_);
return v_r_28_;
}
}
LEAN_EXPORT uint8_t l_Lean_initializing(){
_start:
{
uint8_t v___x_30_; 
v___x_30_ = lean_io_initializing();
if (v___x_30_ == 0)
{
lean_object* v___x_31_; lean_object* v___x_32_; uint8_t v___x_33_; 
v___x_31_ = l___private_Lean_ImportingFlag_0__Lean_importingRef;
v___x_32_ = lean_st_ref_get(v___x_31_);
v___x_33_ = lean_unbox(v___x_32_);
lean_dec(v___x_32_);
return v___x_33_;
}
else
{
return v___x_30_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_initializing___boxed(lean_object* v_a_34_){
_start:
{
uint8_t v_res_35_; lean_object* v_r_36_; 
v_res_35_ = l_Lean_initializing();
v_r_36_ = lean_box(v_res_35_);
return v_r_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_withImporting___redArg___lam__0(lean_object* v___x_37_, uint8_t v___x_38_, lean_object* v_x_39_){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_41_ = lean_box(v___x_38_);
v___x_42_ = lean_st_ref_set(v___x_37_, v___x_41_);
v___x_43_ = l___private_Lean_ImportingFlag_0__Lean_runInitializersRef;
v___x_44_ = lean_box(v___x_38_);
v___x_45_ = lean_st_ref_set(v___x_43_, v___x_44_);
v___x_46_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_46_, 0, v___x_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_withImporting___redArg___lam__0___boxed(lean_object* v___x_47_, lean_object* v___x_48_, lean_object* v_x_49_, lean_object* v___y_50_){
_start:
{
uint8_t v___x_331__boxed_51_; lean_object* v_res_52_; 
v___x_331__boxed_51_ = lean_unbox(v___x_48_);
v_res_52_ = l_Lean_withImporting___redArg___lam__0(v___x_47_, v___x_331__boxed_51_, v_x_49_);
lean_dec(v_x_49_);
lean_dec(v___x_47_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_withImporting___redArg(lean_object* v_x_53_){
_start:
{
lean_object* v___x_55_; uint8_t v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; uint8_t v___x_59_; lean_object* v_r_60_; 
v___x_55_ = l___private_Lean_ImportingFlag_0__Lean_importingRef;
v___x_56_ = 1;
v___x_57_ = lean_box(v___x_56_);
v___x_58_ = lean_st_ref_set(v___x_55_, v___x_57_);
v___x_59_ = 0;
v_r_60_ = lean_apply_1(v_x_53_, lean_box(0));
if (lean_obj_tag(v_r_60_) == 0)
{
lean_object* v_a_61_; lean_object* v___x_63_; uint8_t v_isShared_64_; uint8_t v_isSharedCheck_77_; 
v_a_61_ = lean_ctor_get(v_r_60_, 0);
v_isSharedCheck_77_ = !lean_is_exclusive(v_r_60_);
if (v_isSharedCheck_77_ == 0)
{
v___x_63_ = v_r_60_;
v_isShared_64_ = v_isSharedCheck_77_;
goto v_resetjp_62_;
}
else
{
lean_inc(v_a_61_);
lean_dec(v_r_60_);
v___x_63_ = lean_box(0);
v_isShared_64_ = v_isSharedCheck_77_;
goto v_resetjp_62_;
}
v_resetjp_62_:
{
lean_object* v___x_66_; 
lean_inc(v_a_61_);
if (v_isShared_64_ == 0)
{
lean_ctor_set_tag(v___x_63_, 1);
v___x_66_ = v___x_63_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_76_; 
v_reuseFailAlloc_76_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_76_, 0, v_a_61_);
v___x_66_ = v_reuseFailAlloc_76_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
lean_object* v___x_67_; lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_74_; 
v___x_67_ = l_Lean_withImporting___redArg___lam__0(v___x_55_, v___x_59_, v___x_66_);
lean_dec_ref(v___x_66_);
v_isSharedCheck_74_ = !lean_is_exclusive(v___x_67_);
if (v_isSharedCheck_74_ == 0)
{
lean_object* v_unused_75_; 
v_unused_75_ = lean_ctor_get(v___x_67_, 0);
lean_dec(v_unused_75_);
v___x_69_ = v___x_67_;
v_isShared_70_ = v_isSharedCheck_74_;
goto v_resetjp_68_;
}
else
{
lean_dec(v___x_67_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_74_;
goto v_resetjp_68_;
}
v_resetjp_68_:
{
lean_object* v___x_72_; 
if (v_isShared_70_ == 0)
{
lean_ctor_set(v___x_69_, 0, v_a_61_);
v___x_72_ = v___x_69_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v_a_61_);
v___x_72_ = v_reuseFailAlloc_73_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
return v___x_72_;
}
}
}
}
}
else
{
lean_object* v_a_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_82_; uint8_t v_isShared_83_; uint8_t v_isSharedCheck_87_; 
v_a_78_ = lean_ctor_get(v_r_60_, 0);
lean_inc(v_a_78_);
lean_dec_ref_known(v_r_60_, 1);
v___x_79_ = lean_box(0);
v___x_80_ = l_Lean_withImporting___redArg___lam__0(v___x_55_, v___x_59_, v___x_79_);
v_isSharedCheck_87_ = !lean_is_exclusive(v___x_80_);
if (v_isSharedCheck_87_ == 0)
{
lean_object* v_unused_88_; 
v_unused_88_ = lean_ctor_get(v___x_80_, 0);
lean_dec(v_unused_88_);
v___x_82_ = v___x_80_;
v_isShared_83_ = v_isSharedCheck_87_;
goto v_resetjp_81_;
}
else
{
lean_dec(v___x_80_);
v___x_82_ = lean_box(0);
v_isShared_83_ = v_isSharedCheck_87_;
goto v_resetjp_81_;
}
v_resetjp_81_:
{
lean_object* v___x_85_; 
if (v_isShared_83_ == 0)
{
lean_ctor_set_tag(v___x_82_, 1);
lean_ctor_set(v___x_82_, 0, v_a_78_);
v___x_85_ = v___x_82_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_86_; 
v_reuseFailAlloc_86_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_86_, 0, v_a_78_);
v___x_85_ = v_reuseFailAlloc_86_;
goto v_reusejp_84_;
}
v_reusejp_84_:
{
return v___x_85_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withImporting___redArg___boxed(lean_object* v_x_89_, lean_object* v_a_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l_Lean_withImporting___redArg(v_x_89_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_withImporting(lean_object* v_00_u03b1_92_, lean_object* v_x_93_){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = l_Lean_withImporting___redArg(v_x_93_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_withImporting___boxed(lean_object* v_00_u03b1_96_, lean_object* v_x_97_, lean_object* v_a_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_Lean_withImporting(v_00_u03b1_96_, v_x_97_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* lean_set_initializing(uint8_t v_initializing_100_){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_102_ = l___private_Lean_ImportingFlag_0__Lean_importingRef;
v___x_103_ = lean_box(v_initializing_100_);
v___x_104_ = lean_st_ref_set(v___x_102_, v___x_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ImportingFlag_0__Lean_setInitializing___boxed(lean_object* v_initializing_105_, lean_object* v_a_106_){
_start:
{
uint8_t v_initializing_boxed_107_; lean_object* v_res_108_; 
v_initializing_boxed_107_ = lean_unbox(v_initializing_105_);
v_res_108_ = lean_set_initializing(v_initializing_boxed_107_);
return v_res_108_;
}
}
lean_object* runtime_initialize_Init_System_IO(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_ImportingFlag(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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

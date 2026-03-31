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
LEAN_EXPORT lean_object* l_Lean_isInitializerExecutionEnabled();
LEAN_EXPORT lean_object* l_Lean_isInitializerExecutionEnabled___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initializing();
LEAN_EXPORT lean_object* l_Lean_initializing___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withImporting___redArg___lam__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withImporting___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withImporting___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withImporting___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withImporting(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withImporting___boxed(lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_16_; uint8_t v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_16_ = l___private_Lean_ImportingFlag_0__Lean_runInitializersRef;
v___x_17_ = 1;
v___x_18_ = lean_box(v___x_17_);
v___x_19_ = lean_st_ref_set(v___x_16_, v___x_18_);
v___x_20_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_20_, 0, v___x_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_enableInitializersExecution___boxed(lean_object* v_a_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = lean_enable_initializer_execution();
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInitializerExecutionEnabled(){
_start:
{
lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_24_ = l___private_Lean_ImportingFlag_0__Lean_runInitializersRef;
v___x_25_ = lean_st_ref_get(v___x_24_);
v___x_26_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_26_, 0, v___x_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInitializerExecutionEnabled___boxed(lean_object* v_a_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Lean_isInitializerExecutionEnabled();
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_initializing(){
_start:
{
uint8_t v___x_30_; 
v___x_30_ = lean_io_initializing();
if (v___x_30_ == 0)
{
lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_31_ = l___private_Lean_ImportingFlag_0__Lean_importingRef;
v___x_32_ = lean_st_ref_get(v___x_31_);
v___x_33_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_33_, 0, v___x_32_);
return v___x_33_;
}
else
{
lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_34_ = lean_box(v___x_30_);
v___x_35_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_35_, 0, v___x_34_);
return v___x_35_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_initializing___boxed(lean_object* v_a_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_initializing();
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_withImporting___redArg___lam__0(lean_object* v___x_38_, uint8_t v___x_39_, lean_object* v_x_40_){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_42_ = lean_box(v___x_39_);
v___x_43_ = lean_st_ref_set(v___x_38_, v___x_42_);
v___x_44_ = l___private_Lean_ImportingFlag_0__Lean_runInitializersRef;
v___x_45_ = lean_box(v___x_39_);
v___x_46_ = lean_st_ref_set(v___x_44_, v___x_45_);
v___x_47_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_47_, 0, v___x_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_withImporting___redArg___lam__0___boxed(lean_object* v___x_48_, lean_object* v___x_49_, lean_object* v_x_50_, lean_object* v___y_51_){
_start:
{
uint8_t v___x_331__boxed_52_; lean_object* v_res_53_; 
v___x_331__boxed_52_ = lean_unbox(v___x_49_);
v_res_53_ = l_Lean_withImporting___redArg___lam__0(v___x_48_, v___x_331__boxed_52_, v_x_50_);
lean_dec(v_x_50_);
lean_dec(v___x_48_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_withImporting___redArg(lean_object* v_x_54_){
_start:
{
lean_object* v___x_56_; uint8_t v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; uint8_t v___x_60_; lean_object* v_r_61_; 
v___x_56_ = l___private_Lean_ImportingFlag_0__Lean_importingRef;
v___x_57_ = 1;
v___x_58_ = lean_box(v___x_57_);
v___x_59_ = lean_st_ref_set(v___x_56_, v___x_58_);
v___x_60_ = 0;
v_r_61_ = lean_apply_1(v_x_54_, lean_box(0));
if (lean_obj_tag(v_r_61_) == 0)
{
lean_object* v_a_62_; lean_object* v___x_64_; uint8_t v_isShared_65_; uint8_t v_isSharedCheck_78_; 
v_a_62_ = lean_ctor_get(v_r_61_, 0);
v_isSharedCheck_78_ = !lean_is_exclusive(v_r_61_);
if (v_isSharedCheck_78_ == 0)
{
v___x_64_ = v_r_61_;
v_isShared_65_ = v_isSharedCheck_78_;
goto v_resetjp_63_;
}
else
{
lean_inc(v_a_62_);
lean_dec(v_r_61_);
v___x_64_ = lean_box(0);
v_isShared_65_ = v_isSharedCheck_78_;
goto v_resetjp_63_;
}
v_resetjp_63_:
{
lean_object* v___x_67_; 
lean_inc(v_a_62_);
if (v_isShared_65_ == 0)
{
lean_ctor_set_tag(v___x_64_, 1);
v___x_67_ = v___x_64_;
goto v_reusejp_66_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_77_, 0, v_a_62_);
v___x_67_ = v_reuseFailAlloc_77_;
goto v_reusejp_66_;
}
v_reusejp_66_:
{
lean_object* v___x_68_; lean_object* v___x_70_; uint8_t v_isShared_71_; uint8_t v_isSharedCheck_75_; 
v___x_68_ = l_Lean_withImporting___redArg___lam__0(v___x_56_, v___x_60_, v___x_67_);
lean_dec_ref(v___x_67_);
v_isSharedCheck_75_ = !lean_is_exclusive(v___x_68_);
if (v_isSharedCheck_75_ == 0)
{
lean_object* v_unused_76_; 
v_unused_76_ = lean_ctor_get(v___x_68_, 0);
lean_dec(v_unused_76_);
v___x_70_ = v___x_68_;
v_isShared_71_ = v_isSharedCheck_75_;
goto v_resetjp_69_;
}
else
{
lean_dec(v___x_68_);
v___x_70_ = lean_box(0);
v_isShared_71_ = v_isSharedCheck_75_;
goto v_resetjp_69_;
}
v_resetjp_69_:
{
lean_object* v___x_73_; 
if (v_isShared_71_ == 0)
{
lean_ctor_set(v___x_70_, 0, v_a_62_);
v___x_73_ = v___x_70_;
goto v_reusejp_72_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v_a_62_);
v___x_73_ = v_reuseFailAlloc_74_;
goto v_reusejp_72_;
}
v_reusejp_72_:
{
return v___x_73_;
}
}
}
}
}
else
{
lean_object* v_a_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_88_; 
v_a_79_ = lean_ctor_get(v_r_61_, 0);
lean_inc(v_a_79_);
lean_dec_ref(v_r_61_);
v___x_80_ = lean_box(0);
v___x_81_ = l_Lean_withImporting___redArg___lam__0(v___x_56_, v___x_60_, v___x_80_);
v_isSharedCheck_88_ = !lean_is_exclusive(v___x_81_);
if (v_isSharedCheck_88_ == 0)
{
lean_object* v_unused_89_; 
v_unused_89_ = lean_ctor_get(v___x_81_, 0);
lean_dec(v_unused_89_);
v___x_83_ = v___x_81_;
v_isShared_84_ = v_isSharedCheck_88_;
goto v_resetjp_82_;
}
else
{
lean_dec(v___x_81_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_88_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
lean_object* v___x_86_; 
if (v_isShared_84_ == 0)
{
lean_ctor_set_tag(v___x_83_, 1);
lean_ctor_set(v___x_83_, 0, v_a_79_);
v___x_86_ = v___x_83_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v_a_79_);
v___x_86_ = v_reuseFailAlloc_87_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
return v___x_86_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withImporting___redArg___boxed(lean_object* v_x_90_, lean_object* v_a_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l_Lean_withImporting___redArg(v_x_90_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_withImporting(lean_object* v_00_u03b1_93_, lean_object* v_x_94_){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = l_Lean_withImporting___redArg(v_x_94_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_withImporting___boxed(lean_object* v_00_u03b1_97_, lean_object* v_x_98_, lean_object* v_a_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Lean_withImporting(v_00_u03b1_97_, v_x_98_);
return v_res_100_;
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

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
v___x_19_ = lean_st_ref_swap(v___x_16_, v___x_18_);
lean_dec(v___x_19_);
v___x_20_ = lean_box(0);
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
LEAN_EXPORT uint8_t l_Lean_isInitializerExecutionEnabled(){
_start:
{
lean_object* v___x_24_; lean_object* v___x_25_; uint8_t v___x_26_; 
v___x_24_ = l___private_Lean_ImportingFlag_0__Lean_runInitializersRef;
v___x_25_ = lean_st_ref_get(v___x_24_);
v___x_26_ = lean_unbox(v___x_25_);
lean_dec(v___x_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInitializerExecutionEnabled___boxed(lean_object* v_a_27_){
_start:
{
uint8_t v_res_28_; lean_object* v_r_29_; 
v_res_28_ = l_Lean_isInitializerExecutionEnabled();
v_r_29_ = lean_box(v_res_28_);
return v_r_29_;
}
}
LEAN_EXPORT uint8_t l_Lean_initializing(){
_start:
{
uint8_t v___x_31_; 
v___x_31_ = lean_io_initializing();
if (v___x_31_ == 0)
{
lean_object* v___x_32_; lean_object* v___x_33_; uint8_t v___x_34_; 
v___x_32_ = l___private_Lean_ImportingFlag_0__Lean_importingRef;
v___x_33_ = lean_st_ref_get(v___x_32_);
v___x_34_ = lean_unbox(v___x_33_);
lean_dec(v___x_33_);
return v___x_34_;
}
else
{
return v___x_31_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_initializing___boxed(lean_object* v_a_35_){
_start:
{
uint8_t v_res_36_; lean_object* v_r_37_; 
v_res_36_ = l_Lean_initializing();
v_r_37_ = lean_box(v_res_36_);
return v_r_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_withImporting___redArg___lam__0(lean_object* v___x_38_, uint8_t v___x_39_, lean_object* v_x_40_){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_42_ = lean_box(v___x_39_);
v___x_43_ = lean_st_ref_swap(v___x_38_, v___x_42_);
lean_dec(v___x_43_);
v___x_44_ = l___private_Lean_ImportingFlag_0__Lean_runInitializersRef;
v___x_45_ = lean_box(v___x_39_);
v___x_46_ = lean_st_ref_swap(v___x_44_, v___x_45_);
lean_dec(v___x_46_);
v___x_47_ = lean_box(0);
v___x_48_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_48_, 0, v___x_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_withImporting___redArg___lam__0___boxed(lean_object* v___x_49_, lean_object* v___x_50_, lean_object* v_x_51_, lean_object* v___y_52_){
_start:
{
uint8_t v___x_371__boxed_53_; lean_object* v_res_54_; 
v___x_371__boxed_53_ = lean_unbox(v___x_50_);
v_res_54_ = l_Lean_withImporting___redArg___lam__0(v___x_49_, v___x_371__boxed_53_, v_x_51_);
lean_dec(v_x_51_);
lean_dec(v___x_49_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_withImporting___redArg(lean_object* v_x_55_){
_start:
{
lean_object* v___x_57_; uint8_t v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; uint8_t v___x_61_; lean_object* v_r_62_; 
v___x_57_ = l___private_Lean_ImportingFlag_0__Lean_importingRef;
v___x_58_ = 1;
v___x_59_ = lean_box(v___x_58_);
v___x_60_ = lean_st_ref_swap(v___x_57_, v___x_59_);
lean_dec(v___x_60_);
v___x_61_ = 0;
v_r_62_ = lean_apply_1(v_x_55_, lean_box(0));
if (lean_obj_tag(v_r_62_) == 0)
{
lean_object* v_a_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_79_; 
v_a_63_ = lean_ctor_get(v_r_62_, 0);
v_isSharedCheck_79_ = !lean_is_exclusive(v_r_62_);
if (v_isSharedCheck_79_ == 0)
{
v___x_65_ = v_r_62_;
v_isShared_66_ = v_isSharedCheck_79_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_a_63_);
lean_dec(v_r_62_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_79_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
lean_object* v___x_68_; 
lean_inc(v_a_63_);
if (v_isShared_66_ == 0)
{
lean_ctor_set_tag(v___x_65_, 1);
v___x_68_ = v___x_65_;
goto v_reusejp_67_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v_a_63_);
v___x_68_ = v_reuseFailAlloc_78_;
goto v_reusejp_67_;
}
v_reusejp_67_:
{
lean_object* v___x_69_; lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_76_; 
v___x_69_ = l_Lean_withImporting___redArg___lam__0(v___x_57_, v___x_61_, v___x_68_);
lean_dec_ref(v___x_68_);
v_isSharedCheck_76_ = !lean_is_exclusive(v___x_69_);
if (v_isSharedCheck_76_ == 0)
{
lean_object* v_unused_77_; 
v_unused_77_ = lean_ctor_get(v___x_69_, 0);
lean_dec(v_unused_77_);
v___x_71_ = v___x_69_;
v_isShared_72_ = v_isSharedCheck_76_;
goto v_resetjp_70_;
}
else
{
lean_dec(v___x_69_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_76_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
lean_object* v___x_74_; 
if (v_isShared_72_ == 0)
{
lean_ctor_set(v___x_71_, 0, v_a_63_);
v___x_74_ = v___x_71_;
goto v_reusejp_73_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v_a_63_);
v___x_74_ = v_reuseFailAlloc_75_;
goto v_reusejp_73_;
}
v_reusejp_73_:
{
return v___x_74_;
}
}
}
}
}
else
{
lean_object* v_a_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_89_; 
v_a_80_ = lean_ctor_get(v_r_62_, 0);
lean_inc(v_a_80_);
lean_dec_ref_known(v_r_62_, 1);
v___x_81_ = lean_box(0);
v___x_82_ = l_Lean_withImporting___redArg___lam__0(v___x_57_, v___x_61_, v___x_81_);
v_isSharedCheck_89_ = !lean_is_exclusive(v___x_82_);
if (v_isSharedCheck_89_ == 0)
{
lean_object* v_unused_90_; 
v_unused_90_ = lean_ctor_get(v___x_82_, 0);
lean_dec(v_unused_90_);
v___x_84_ = v___x_82_;
v_isShared_85_ = v_isSharedCheck_89_;
goto v_resetjp_83_;
}
else
{
lean_dec(v___x_82_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_89_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
lean_object* v___x_87_; 
if (v_isShared_85_ == 0)
{
lean_ctor_set_tag(v___x_84_, 1);
lean_ctor_set(v___x_84_, 0, v_a_80_);
v___x_87_ = v___x_84_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v_a_80_);
v___x_87_ = v_reuseFailAlloc_88_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
return v___x_87_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withImporting___redArg___boxed(lean_object* v_x_91_, lean_object* v_a_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Lean_withImporting___redArg(v_x_91_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_withImporting(lean_object* v_00_u03b1_94_, lean_object* v_x_95_){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = l_Lean_withImporting___redArg(v_x_95_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_withImporting___boxed(lean_object* v_00_u03b1_98_, lean_object* v_x_99_, lean_object* v_a_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l_Lean_withImporting(v_00_u03b1_98_, v_x_99_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* lean_set_initializing(uint8_t v_initializing_102_){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_104_ = l___private_Lean_ImportingFlag_0__Lean_importingRef;
v___x_105_ = lean_box(v_initializing_102_);
v___x_106_ = lean_st_ref_swap(v___x_104_, v___x_105_);
lean_dec(v___x_106_);
v___x_107_ = lean_box(0);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ImportingFlag_0__Lean_setInitializing___boxed(lean_object* v_initializing_108_, lean_object* v_a_109_){
_start:
{
uint8_t v_initializing_boxed_110_; lean_object* v_res_111_; 
v_initializing_boxed_110_ = lean_unbox(v_initializing_108_);
v_res_111_ = lean_set_initializing(v_initializing_boxed_110_);
return v_res_111_;
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

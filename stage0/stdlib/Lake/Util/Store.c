// Lean compiler output
// Module: Lake.Util.Store
// Imports: public import Init.Prelude
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
LEAN_EXPORT lean_object* l_Lake_instMonadStore1OfMonadStore1Of___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStore1OfMonadStore1Of(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStore1OfMonadStore1Of___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStore1OfOfMonadDStore___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStore1OfOfMonadDStore___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStore1OfOfMonadDStore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreOfMonadLift___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreOfMonadLift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreOfMonadLift(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchOrCreate___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchOrCreate___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchOrCreate___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchOrCreate___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchOrCreate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchOrCreate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStore1OfMonadStore1Of___redArg(lean_object* v_inst_1_){
_start:
{
lean_object* v_fetch_x3f_2_; lean_object* v_store_3_; lean_object* v___x_5_; uint8_t v_isShared_6_; uint8_t v_isSharedCheck_10_; 
v_fetch_x3f_2_ = lean_ctor_get(v_inst_1_, 0);
v_store_3_ = lean_ctor_get(v_inst_1_, 1);
v_isSharedCheck_10_ = !lean_is_exclusive(v_inst_1_);
if (v_isSharedCheck_10_ == 0)
{
v___x_5_ = v_inst_1_;
v_isShared_6_ = v_isSharedCheck_10_;
goto v_resetjp_4_;
}
else
{
lean_inc(v_store_3_);
lean_inc(v_fetch_x3f_2_);
lean_dec(v_inst_1_);
v___x_5_ = lean_box(0);
v_isShared_6_ = v_isSharedCheck_10_;
goto v_resetjp_4_;
}
v_resetjp_4_:
{
lean_object* v___x_8_; 
if (v_isShared_6_ == 0)
{
v___x_8_ = v___x_5_;
goto v_reusejp_7_;
}
else
{
lean_object* v_reuseFailAlloc_9_; 
v_reuseFailAlloc_9_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_9_, 0, v_fetch_x3f_2_);
lean_ctor_set(v_reuseFailAlloc_9_, 1, v_store_3_);
v___x_8_ = v_reuseFailAlloc_9_;
goto v_reusejp_7_;
}
v_reusejp_7_:
{
return v___x_8_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStore1OfMonadStore1Of(lean_object* v_00_u03ba_11_, lean_object* v_k_12_, lean_object* v_00_u03b1_13_, lean_object* v_m_14_, lean_object* v_inst_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = l_Lake_instMonadStore1OfMonadStore1Of___redArg(v_inst_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStore1OfMonadStore1Of___boxed(lean_object* v_00_u03ba_17_, lean_object* v_k_18_, lean_object* v_00_u03b1_19_, lean_object* v_m_20_, lean_object* v_inst_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lake_instMonadStore1OfMonadStore1Of(v_00_u03ba_17_, v_k_18_, v_00_u03b1_19_, v_m_20_, v_inst_21_);
lean_dec(v_k_18_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStore1OfOfMonadDStore___redArg___lam__0(lean_object* v_store_23_, lean_object* v_k_24_, lean_object* v_o_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = lean_apply_2(v_store_23_, v_k_24_, v_o_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStore1OfOfMonadDStore___redArg(lean_object* v_k_27_, lean_object* v_inst_28_){
_start:
{
lean_object* v_fetch_x3f_29_; lean_object* v_store_30_; lean_object* v___x_32_; uint8_t v_isShared_33_; uint8_t v_isSharedCheck_39_; 
v_fetch_x3f_29_ = lean_ctor_get(v_inst_28_, 0);
v_store_30_ = lean_ctor_get(v_inst_28_, 1);
v_isSharedCheck_39_ = !lean_is_exclusive(v_inst_28_);
if (v_isSharedCheck_39_ == 0)
{
v___x_32_ = v_inst_28_;
v_isShared_33_ = v_isSharedCheck_39_;
goto v_resetjp_31_;
}
else
{
lean_inc(v_store_30_);
lean_inc(v_fetch_x3f_29_);
lean_dec(v_inst_28_);
v___x_32_ = lean_box(0);
v_isShared_33_ = v_isSharedCheck_39_;
goto v_resetjp_31_;
}
v_resetjp_31_:
{
lean_object* v___f_34_; lean_object* v___x_35_; lean_object* v___x_37_; 
lean_inc(v_k_27_);
v___f_34_ = lean_alloc_closure((void*)(l_Lake_instMonadStore1OfOfMonadDStore___redArg___lam__0), 3, 2);
lean_closure_set(v___f_34_, 0, v_store_30_);
lean_closure_set(v___f_34_, 1, v_k_27_);
v___x_35_ = lean_apply_1(v_fetch_x3f_29_, v_k_27_);
if (v_isShared_33_ == 0)
{
lean_ctor_set(v___x_32_, 1, v___f_34_);
lean_ctor_set(v___x_32_, 0, v___x_35_);
v___x_37_ = v___x_32_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v___x_35_);
lean_ctor_set(v_reuseFailAlloc_38_, 1, v___f_34_);
v___x_37_ = v_reuseFailAlloc_38_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
return v___x_37_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStore1OfOfMonadDStore(lean_object* v_00_u03ba_40_, lean_object* v_00_u03b2_41_, lean_object* v_m_42_, lean_object* v_k_43_, lean_object* v_inst_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l_Lake_instMonadStore1OfOfMonadDStore___redArg(v_k_43_, v_inst_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreOfMonadLift___redArg___lam__0(lean_object* v_inst_46_, lean_object* v_inst_47_, lean_object* v_k_48_){
_start:
{
lean_object* v_fetch_x3f_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v_fetch_x3f_49_ = lean_ctor_get(v_inst_46_, 0);
lean_inc(v_fetch_x3f_49_);
lean_dec_ref(v_inst_46_);
v___x_50_ = lean_apply_1(v_fetch_x3f_49_, v_k_48_);
v___x_51_ = lean_apply_2(v_inst_47_, lean_box(0), v___x_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreOfMonadLift___redArg___lam__1(lean_object* v_inst_52_, lean_object* v_inst_53_, lean_object* v_k_54_, lean_object* v_a_55_){
_start:
{
lean_object* v_store_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v_store_56_ = lean_ctor_get(v_inst_52_, 1);
lean_inc(v_store_56_);
lean_dec_ref(v_inst_52_);
v___x_57_ = lean_apply_2(v_store_56_, v_k_54_, v_a_55_);
v___x_58_ = lean_apply_2(v_inst_53_, lean_box(0), v___x_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreOfMonadLift___redArg(lean_object* v_inst_59_, lean_object* v_inst_60_){
_start:
{
lean_object* v___f_61_; lean_object* v___f_62_; lean_object* v___x_63_; 
lean_inc(v_inst_59_);
lean_inc_ref(v_inst_60_);
v___f_61_ = lean_alloc_closure((void*)(l_Lake_instMonadDStoreOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_61_, 0, v_inst_60_);
lean_closure_set(v___f_61_, 1, v_inst_59_);
v___f_62_ = lean_alloc_closure((void*)(l_Lake_instMonadDStoreOfMonadLift___redArg___lam__1), 4, 2);
lean_closure_set(v___f_62_, 0, v_inst_60_);
lean_closure_set(v___f_62_, 1, v_inst_59_);
v___x_63_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_63_, 0, v___f_61_);
lean_ctor_set(v___x_63_, 1, v___f_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreOfMonadLift(lean_object* v_m_64_, lean_object* v_n_65_, lean_object* v_00_u03ba_66_, lean_object* v_00_u03b2_67_, lean_object* v_inst_68_, lean_object* v_inst_69_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = l_Lake_instMonadDStoreOfMonadLift___redArg(v_inst_68_, v_inst_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchOrCreate___redArg___lam__0(lean_object* v_toPure_71_, lean_object* v_val_72_, lean_object* v_____r_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = lean_apply_2(v_toPure_71_, lean_box(0), v_val_72_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchOrCreate___redArg___lam__1(lean_object* v_toPure_75_, lean_object* v_store_76_, lean_object* v_toBind_77_, lean_object* v_val_78_){
_start:
{
lean_object* v___f_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
lean_inc(v_val_78_);
v___f_79_ = lean_alloc_closure((void*)(l_Lake_fetchOrCreate___redArg___lam__0), 3, 2);
lean_closure_set(v___f_79_, 0, v_toPure_75_);
lean_closure_set(v___f_79_, 1, v_val_78_);
v___x_80_ = lean_apply_1(v_store_76_, v_val_78_);
v___x_81_ = lean_apply_4(v_toBind_77_, lean_box(0), lean_box(0), v___x_80_, v___f_79_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchOrCreate___redArg___lam__2(lean_object* v_toBind_82_, lean_object* v_create_83_, lean_object* v___f_84_, lean_object* v_toPure_85_, lean_object* v_____do__lift_86_){
_start:
{
if (lean_obj_tag(v_____do__lift_86_) == 0)
{
lean_object* v___x_87_; 
lean_dec(v_toPure_85_);
v___x_87_ = lean_apply_4(v_toBind_82_, lean_box(0), lean_box(0), v_create_83_, v___f_84_);
return v___x_87_;
}
else
{
lean_object* v_val_88_; lean_object* v___x_89_; 
lean_dec(v___f_84_);
lean_dec(v_create_83_);
lean_dec(v_toBind_82_);
v_val_88_ = lean_ctor_get(v_____do__lift_86_, 0);
lean_inc(v_val_88_);
lean_dec_ref(v_____do__lift_86_);
v___x_89_ = lean_apply_2(v_toPure_85_, lean_box(0), v_val_88_);
return v___x_89_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_fetchOrCreate___redArg(lean_object* v_inst_90_, lean_object* v_inst_91_, lean_object* v_create_92_){
_start:
{
lean_object* v_toApplicative_93_; lean_object* v_toBind_94_; lean_object* v_fetch_x3f_95_; lean_object* v_store_96_; lean_object* v_toPure_97_; lean_object* v___f_98_; lean_object* v___f_99_; lean_object* v___x_100_; 
v_toApplicative_93_ = lean_ctor_get(v_inst_90_, 0);
lean_inc_ref(v_toApplicative_93_);
v_toBind_94_ = lean_ctor_get(v_inst_90_, 1);
lean_inc_n(v_toBind_94_, 3);
lean_dec_ref(v_inst_90_);
v_fetch_x3f_95_ = lean_ctor_get(v_inst_91_, 0);
lean_inc(v_fetch_x3f_95_);
v_store_96_ = lean_ctor_get(v_inst_91_, 1);
lean_inc(v_store_96_);
lean_dec_ref(v_inst_91_);
v_toPure_97_ = lean_ctor_get(v_toApplicative_93_, 1);
lean_inc_n(v_toPure_97_, 2);
lean_dec_ref(v_toApplicative_93_);
v___f_98_ = lean_alloc_closure((void*)(l_Lake_fetchOrCreate___redArg___lam__1), 4, 3);
lean_closure_set(v___f_98_, 0, v_toPure_97_);
lean_closure_set(v___f_98_, 1, v_store_96_);
lean_closure_set(v___f_98_, 2, v_toBind_94_);
v___f_99_ = lean_alloc_closure((void*)(l_Lake_fetchOrCreate___redArg___lam__2), 5, 4);
lean_closure_set(v___f_99_, 0, v_toBind_94_);
lean_closure_set(v___f_99_, 1, v_create_92_);
lean_closure_set(v___f_99_, 2, v___f_98_);
lean_closure_set(v___f_99_, 3, v_toPure_97_);
v___x_100_ = lean_apply_4(v_toBind_94_, lean_box(0), lean_box(0), v_fetch_x3f_95_, v___f_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchOrCreate(lean_object* v_m_101_, lean_object* v_00_u03ba_102_, lean_object* v_00_u03b1_103_, lean_object* v_inst_104_, lean_object* v_key_105_, lean_object* v_inst_106_, lean_object* v_create_107_){
_start:
{
lean_object* v_toApplicative_108_; lean_object* v_toBind_109_; lean_object* v_fetch_x3f_110_; lean_object* v_store_111_; lean_object* v_toPure_112_; lean_object* v___f_113_; lean_object* v___f_114_; lean_object* v___x_115_; 
v_toApplicative_108_ = lean_ctor_get(v_inst_104_, 0);
lean_inc_ref(v_toApplicative_108_);
v_toBind_109_ = lean_ctor_get(v_inst_104_, 1);
lean_inc_n(v_toBind_109_, 3);
lean_dec_ref(v_inst_104_);
v_fetch_x3f_110_ = lean_ctor_get(v_inst_106_, 0);
lean_inc(v_fetch_x3f_110_);
v_store_111_ = lean_ctor_get(v_inst_106_, 1);
lean_inc(v_store_111_);
lean_dec_ref(v_inst_106_);
v_toPure_112_ = lean_ctor_get(v_toApplicative_108_, 1);
lean_inc_n(v_toPure_112_, 2);
lean_dec_ref(v_toApplicative_108_);
v___f_113_ = lean_alloc_closure((void*)(l_Lake_fetchOrCreate___redArg___lam__1), 4, 3);
lean_closure_set(v___f_113_, 0, v_toPure_112_);
lean_closure_set(v___f_113_, 1, v_store_111_);
lean_closure_set(v___f_113_, 2, v_toBind_109_);
v___f_114_ = lean_alloc_closure((void*)(l_Lake_fetchOrCreate___redArg___lam__2), 5, 4);
lean_closure_set(v___f_114_, 0, v_toBind_109_);
lean_closure_set(v___f_114_, 1, v_create_107_);
lean_closure_set(v___f_114_, 2, v___f_113_);
lean_closure_set(v___f_114_, 3, v_toPure_112_);
v___x_115_ = lean_apply_4(v_toBind_109_, lean_box(0), lean_box(0), v_fetch_x3f_110_, v___f_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchOrCreate___boxed(lean_object* v_m_116_, lean_object* v_00_u03ba_117_, lean_object* v_00_u03b1_118_, lean_object* v_inst_119_, lean_object* v_key_120_, lean_object* v_inst_121_, lean_object* v_create_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l_Lake_fetchOrCreate(v_m_116_, v_00_u03ba_117_, v_00_u03b1_118_, v_inst_119_, v_key_120_, v_inst_121_, v_create_122_);
lean_dec(v_key_120_);
return v_res_123_;
}
}
lean_object* runtime_initialize_Init_Prelude(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Util_Store(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Prelude(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Util_Store(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Prelude(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_Store(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Prelude(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Store(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Util_Store(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Util_Store(builtin);
}
#ifdef __cplusplus
}
#endif

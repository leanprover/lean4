// Lean compiler output
// Module: Std.Data.HashSet.Iterator
// Imports: public import Std.Data.HashMap.Iterator public import Std.Data.HashSet.Basic public import Std.Data.HashSet.Raw import Init.Data.Iterators.Combinators.FilterMap
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
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_iter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_iter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_iter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_iter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_iter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_iter___redArg(lean_object* v_m_1_){
_start:
{
lean_object* v_buckets_2_; lean_object* v___x_4_; uint8_t v_isShared_5_; uint8_t v_isSharedCheck_12_; 
v_buckets_2_ = lean_ctor_get(v_m_1_, 1);
v_isSharedCheck_12_ = !lean_is_exclusive(v_m_1_);
if (v_isSharedCheck_12_ == 0)
{
lean_object* v_unused_13_; 
v_unused_13_ = lean_ctor_get(v_m_1_, 0);
lean_dec(v_unused_13_);
v___x_4_ = v_m_1_;
v_isShared_5_ = v_isSharedCheck_12_;
goto v_resetjp_3_;
}
else
{
lean_inc(v_buckets_2_);
lean_dec(v_m_1_);
v___x_4_ = lean_box(0);
v_isShared_5_ = v_isSharedCheck_12_;
goto v_resetjp_3_;
}
v_resetjp_3_:
{
lean_object* v___x_6_; lean_object* v___x_8_; 
v___x_6_ = lean_unsigned_to_nat(0u);
if (v_isShared_5_ == 0)
{
lean_ctor_set(v___x_4_, 1, v___x_6_);
lean_ctor_set(v___x_4_, 0, v_buckets_2_);
v___x_8_ = v___x_4_;
goto v_reusejp_7_;
}
else
{
lean_object* v_reuseFailAlloc_11_; 
v_reuseFailAlloc_11_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_11_, 0, v_buckets_2_);
lean_ctor_set(v_reuseFailAlloc_11_, 1, v___x_6_);
v___x_8_ = v_reuseFailAlloc_11_;
goto v_reusejp_7_;
}
v_reusejp_7_:
{
lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_9_ = lean_box(0);
v___x_10_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_10_, 0, v___x_8_);
lean_ctor_set(v___x_10_, 1, v___x_9_);
return v___x_10_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_iter(lean_object* v_00_u03b1_14_, lean_object* v_m_15_){
_start:
{
lean_object* v_buckets_16_; lean_object* v___x_18_; uint8_t v_isShared_19_; uint8_t v_isSharedCheck_26_; 
v_buckets_16_ = lean_ctor_get(v_m_15_, 1);
v_isSharedCheck_26_ = !lean_is_exclusive(v_m_15_);
if (v_isSharedCheck_26_ == 0)
{
lean_object* v_unused_27_; 
v_unused_27_ = lean_ctor_get(v_m_15_, 0);
lean_dec(v_unused_27_);
v___x_18_ = v_m_15_;
v_isShared_19_ = v_isSharedCheck_26_;
goto v_resetjp_17_;
}
else
{
lean_inc(v_buckets_16_);
lean_dec(v_m_15_);
v___x_18_ = lean_box(0);
v_isShared_19_ = v_isSharedCheck_26_;
goto v_resetjp_17_;
}
v_resetjp_17_:
{
lean_object* v___x_20_; lean_object* v___x_22_; 
v___x_20_ = lean_unsigned_to_nat(0u);
if (v_isShared_19_ == 0)
{
lean_ctor_set(v___x_18_, 1, v___x_20_);
lean_ctor_set(v___x_18_, 0, v_buckets_16_);
v___x_22_ = v___x_18_;
goto v_reusejp_21_;
}
else
{
lean_object* v_reuseFailAlloc_25_; 
v_reuseFailAlloc_25_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_25_, 0, v_buckets_16_);
lean_ctor_set(v_reuseFailAlloc_25_, 1, v___x_20_);
v___x_22_ = v_reuseFailAlloc_25_;
goto v_reusejp_21_;
}
v_reusejp_21_:
{
lean_object* v___x_23_; lean_object* v___x_24_; 
v___x_23_ = lean_box(0);
v___x_24_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_24_, 0, v___x_22_);
lean_ctor_set(v___x_24_, 1, v___x_23_);
return v___x_24_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_iter___redArg(lean_object* v_m_28_){
_start:
{
lean_object* v_buckets_29_; lean_object* v___x_31_; uint8_t v_isShared_32_; uint8_t v_isSharedCheck_39_; 
v_buckets_29_ = lean_ctor_get(v_m_28_, 1);
v_isSharedCheck_39_ = !lean_is_exclusive(v_m_28_);
if (v_isSharedCheck_39_ == 0)
{
lean_object* v_unused_40_; 
v_unused_40_ = lean_ctor_get(v_m_28_, 0);
lean_dec(v_unused_40_);
v___x_31_ = v_m_28_;
v_isShared_32_ = v_isSharedCheck_39_;
goto v_resetjp_30_;
}
else
{
lean_inc(v_buckets_29_);
lean_dec(v_m_28_);
v___x_31_ = lean_box(0);
v_isShared_32_ = v_isSharedCheck_39_;
goto v_resetjp_30_;
}
v_resetjp_30_:
{
lean_object* v___x_33_; lean_object* v___x_35_; 
v___x_33_ = lean_unsigned_to_nat(0u);
if (v_isShared_32_ == 0)
{
lean_ctor_set(v___x_31_, 1, v___x_33_);
lean_ctor_set(v___x_31_, 0, v_buckets_29_);
v___x_35_ = v___x_31_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v_buckets_29_);
lean_ctor_set(v_reuseFailAlloc_38_, 1, v___x_33_);
v___x_35_ = v_reuseFailAlloc_38_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_36_ = lean_box(0);
v___x_37_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_37_, 0, v___x_35_);
lean_ctor_set(v___x_37_, 1, v___x_36_);
return v___x_37_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_iter(lean_object* v_00_u03b1_41_, lean_object* v_inst_42_, lean_object* v_inst_43_, lean_object* v_m_44_){
_start:
{
lean_object* v_buckets_45_; lean_object* v___x_47_; uint8_t v_isShared_48_; uint8_t v_isSharedCheck_55_; 
v_buckets_45_ = lean_ctor_get(v_m_44_, 1);
v_isSharedCheck_55_ = !lean_is_exclusive(v_m_44_);
if (v_isSharedCheck_55_ == 0)
{
lean_object* v_unused_56_; 
v_unused_56_ = lean_ctor_get(v_m_44_, 0);
lean_dec(v_unused_56_);
v___x_47_ = v_m_44_;
v_isShared_48_ = v_isSharedCheck_55_;
goto v_resetjp_46_;
}
else
{
lean_inc(v_buckets_45_);
lean_dec(v_m_44_);
v___x_47_ = lean_box(0);
v_isShared_48_ = v_isSharedCheck_55_;
goto v_resetjp_46_;
}
v_resetjp_46_:
{
lean_object* v___x_49_; lean_object* v___x_51_; 
v___x_49_ = lean_unsigned_to_nat(0u);
if (v_isShared_48_ == 0)
{
lean_ctor_set(v___x_47_, 1, v___x_49_);
lean_ctor_set(v___x_47_, 0, v_buckets_45_);
v___x_51_ = v___x_47_;
goto v_reusejp_50_;
}
else
{
lean_object* v_reuseFailAlloc_54_; 
v_reuseFailAlloc_54_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_54_, 0, v_buckets_45_);
lean_ctor_set(v_reuseFailAlloc_54_, 1, v___x_49_);
v___x_51_ = v_reuseFailAlloc_54_;
goto v_reusejp_50_;
}
v_reusejp_50_:
{
lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_52_ = lean_box(0);
v___x_53_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_53_, 0, v___x_51_);
lean_ctor_set(v___x_53_, 1, v___x_52_);
return v___x_53_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_iter___boxed(lean_object* v_00_u03b1_57_, lean_object* v_inst_58_, lean_object* v_inst_59_, lean_object* v_m_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l_Std_HashSet_iter(v_00_u03b1_57_, v_inst_58_, v_inst_59_, v_m_60_);
lean_dec_ref(v_inst_59_);
lean_dec_ref(v_inst_58_);
return v_res_61_;
}
}
lean_object* runtime_initialize_Std_Data_HashMap_Iterator(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_HashSet_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_HashSet_Raw(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Combinators_FilterMap(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_HashSet_Iterator(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Data_HashMap_Iterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_HashSet_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_HashSet_Raw(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Combinators_FilterMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_HashSet_Iterator(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_HashMap_Iterator(uint8_t builtin);
lean_object* initialize_Std_Data_HashSet_Basic(uint8_t builtin);
lean_object* initialize_Std_Data_HashSet_Raw(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Combinators_FilterMap(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_HashSet_Iterator(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_HashMap_Iterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashSet_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashSet_Raw(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Combinators_FilterMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_HashSet_Iterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_HashSet_Iterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_HashSet_Iterator(builtin);
}
#ifdef __cplusplus
}
#endif

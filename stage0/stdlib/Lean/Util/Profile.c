// Lean compiler output
// Module: Lean.Util.Profile
// Imports: public import Init.Data.OfScientific public import Lean.Data.Options
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
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_unsafeBaseIO___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
double lean_float_div(double, double);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Profile_0__Lean_initFn___closed__0_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "profiler"};
static const lean_object* l___private_Lean_Util_Profile_0__Lean_initFn___closed__0_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Profile_0__Lean_initFn___closed__0_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Util_Profile_0__Lean_initFn___closed__1_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Util_Profile_0__Lean_initFn___closed__0_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(55, 199, 104, 147, 160, 34, 129, 33)}};
static const lean_object* l___private_Lean_Util_Profile_0__Lean_initFn___closed__1_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Profile_0__Lean_initFn___closed__1_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Util_Profile_0__Lean_initFn___closed__2_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 145, .m_capacity = 145, .m_length = 144, .m_data = "show exclusive execution times of various Lean components\n\nSee also `trace.profiler` for an alternative profiling system with structured output."};
static const lean_object* l___private_Lean_Util_Profile_0__Lean_initFn___closed__2_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Profile_0__Lean_initFn___closed__2_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Util_Profile_0__Lean_initFn___closed__3_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Util_Profile_0__Lean_initFn___closed__2_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Util_Profile_0__Lean_initFn___closed__3_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Profile_0__Lean_initFn___closed__3_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Util_Profile_0__Lean_initFn___closed__4_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Util_Profile_0__Lean_initFn___closed__4_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Profile_0__Lean_initFn___closed__4_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Util_Profile_0__Lean_initFn___closed__5_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Util_Profile_0__Lean_initFn___closed__4_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_Profile_0__Lean_initFn___closed__5_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Profile_0__Lean_initFn___closed__5_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Util_Profile_0__Lean_initFn___closed__0_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(94, 106, 196, 159, 114, 195, 161, 8)}};
static const lean_object* l___private_Lean_Util_Profile_0__Lean_initFn___closed__5_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Profile_0__Lean_initFn___closed__5_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_profiler;
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Profile_0__Lean_initFn___closed__0_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "threshold"};
static const lean_object* l___private_Lean_Util_Profile_0__Lean_initFn___closed__0_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Profile_0__Lean_initFn___closed__0_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Util_Profile_0__Lean_initFn___closed__1_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Util_Profile_0__Lean_initFn___closed__0_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(55, 199, 104, 147, 160, 34, 129, 33)}};
static const lean_ctor_object l___private_Lean_Util_Profile_0__Lean_initFn___closed__1_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Profile_0__Lean_initFn___closed__1_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Util_Profile_0__Lean_initFn___closed__0_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(199, 19, 199, 178, 13, 14, 236, 251)}};
static const lean_object* l___private_Lean_Util_Profile_0__Lean_initFn___closed__1_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Profile_0__Lean_initFn___closed__1_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Util_Profile_0__Lean_initFn___closed__2_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 93, .m_capacity = 93, .m_length = 92, .m_data = "threshold in milliseconds, profiling times under threshold will not be reported individually"};
static const lean_object* l___private_Lean_Util_Profile_0__Lean_initFn___closed__2_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Profile_0__Lean_initFn___closed__2_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Util_Profile_0__Lean_initFn___closed__3_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(100) << 1) | 1)),((lean_object*)&l___private_Lean_Util_Profile_0__Lean_initFn___closed__2_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Util_Profile_0__Lean_initFn___closed__3_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Profile_0__Lean_initFn___closed__3_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Util_Profile_0__Lean_initFn___closed__4_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Util_Profile_0__Lean_initFn___closed__4_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_Profile_0__Lean_initFn___closed__4_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Profile_0__Lean_initFn___closed__4_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Util_Profile_0__Lean_initFn___closed__0_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(94, 106, 196, 159, 114, 195, 161, 8)}};
static const lean_ctor_object l___private_Lean_Util_Profile_0__Lean_initFn___closed__4_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Profile_0__Lean_initFn___closed__4_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Util_Profile_0__Lean_initFn___closed__0_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(170, 166, 34, 176, 223, 145, 160, 245)}};
static const lean_object* l___private_Lean_Util_Profile_0__Lean_initFn___closed__4_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Profile_0__Lean_initFn___closed__4_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_profiler_threshold;
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Profile_0__Lean_get__profiler_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_get_profiler(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Profile_0__Lean_get__profiler___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_profiler_threshold_getSecs_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_profiler_threshold_getSecs_spec__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_profiler_threshold_getSecs___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_profiler_threshold_getSecs___closed__0;
LEAN_EXPORT double lean_get_profiler_threshold(lean_object*);
LEAN_EXPORT lean_object* l_Lean_profiler_threshold_getSecs___boxed(lean_object*);
lean_object* lean_profileit(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitIOUnsafe___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitIOUnsafe___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitIOUnsafe___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitIOUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitIOUnsafe___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitIOUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitIOUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_display_cumulative_profiling_times();
LEAN_EXPORT lean_object* l_Lean_displayCumulativeProfilingTimes___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v_deprecation_x3f_7_; lean_object* v___x_8_; uint8_t v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_deprecation_x3f_7_ = lean_ctor_get(v_decl_2_, 2);
v___x_8_ = lean_alloc_ctor(1, 0, 1);
v___x_9_ = lean_unbox(v_defValue_5_);
lean_ctor_set_uint8(v___x_8_, 0, v___x_9_);
lean_inc(v_deprecation_x3f_7_);
lean_inc_ref(v_descr_6_);
lean_inc_n(v_name_1_, 2);
v___x_10_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_10_, 0, v_name_1_);
lean_ctor_set(v___x_10_, 1, v_ref_3_);
lean_ctor_set(v___x_10_, 2, v___x_8_);
lean_ctor_set(v___x_10_, 3, v_descr_6_);
lean_ctor_set(v___x_10_, 4, v_deprecation_x3f_7_);
v___x_11_ = lean_register_option(v_name_1_, v___x_10_);
if (lean_obj_tag(v___x_11_) == 0)
{
lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_19_; 
v_isSharedCheck_19_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_19_ == 0)
{
lean_object* v_unused_20_; 
v_unused_20_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_20_);
v___x_13_ = v___x_11_;
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
else
{
lean_dec(v___x_11_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_15_; lean_object* v___x_17_; 
lean_inc(v_defValue_5_);
v___x_15_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_15_, 0, v_name_1_);
lean_ctor_set(v___x_15_, 1, v_defValue_5_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 0, v___x_15_);
v___x_17_ = v___x_13_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v___x_15_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
}
else
{
lean_object* v_a_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_28_; 
lean_dec(v_name_1_);
v_a_21_ = lean_ctor_get(v___x_11_, 0);
v_isSharedCheck_28_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_28_ == 0)
{
v___x_23_ = v___x_11_;
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_a_21_);
lean_dec(v___x_11_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v___x_26_; 
if (v_isShared_24_ == 0)
{
v___x_26_ = v___x_23_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_a_21_);
v___x_26_ = v_reuseFailAlloc_27_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
return v___x_26_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_48_ = ((lean_object*)(l___private_Lean_Util_Profile_0__Lean_initFn___closed__1_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4_));
v___x_49_ = ((lean_object*)(l___private_Lean_Util_Profile_0__Lean_initFn___closed__3_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4_));
v___x_50_ = ((lean_object*)(l___private_Lean_Util_Profile_0__Lean_initFn___closed__5_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4_));
v___x_51_ = l_Lean_Option_register___at___00__private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__spec__0(v___x_48_, v___x_49_, v___x_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4____boxed(lean_object* v_a_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l___private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4_();
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__spec__0(lean_object* v_name_54_, lean_object* v_decl_55_, lean_object* v_ref_56_){
_start:
{
lean_object* v_defValue_58_; lean_object* v_descr_59_; lean_object* v_deprecation_x3f_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v_defValue_58_ = lean_ctor_get(v_decl_55_, 0);
v_descr_59_ = lean_ctor_get(v_decl_55_, 1);
v_deprecation_x3f_60_ = lean_ctor_get(v_decl_55_, 2);
lean_inc(v_defValue_58_);
v___x_61_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_61_, 0, v_defValue_58_);
lean_inc(v_deprecation_x3f_60_);
lean_inc_ref(v_descr_59_);
lean_inc_n(v_name_54_, 2);
v___x_62_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_62_, 0, v_name_54_);
lean_ctor_set(v___x_62_, 1, v_ref_56_);
lean_ctor_set(v___x_62_, 2, v___x_61_);
lean_ctor_set(v___x_62_, 3, v_descr_59_);
lean_ctor_set(v___x_62_, 4, v_deprecation_x3f_60_);
v___x_63_ = lean_register_option(v_name_54_, v___x_62_);
if (lean_obj_tag(v___x_63_) == 0)
{
lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_71_; 
v_isSharedCheck_71_ = !lean_is_exclusive(v___x_63_);
if (v_isSharedCheck_71_ == 0)
{
lean_object* v_unused_72_; 
v_unused_72_ = lean_ctor_get(v___x_63_, 0);
lean_dec(v_unused_72_);
v___x_65_ = v___x_63_;
v_isShared_66_ = v_isSharedCheck_71_;
goto v_resetjp_64_;
}
else
{
lean_dec(v___x_63_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_71_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
lean_object* v___x_67_; lean_object* v___x_69_; 
lean_inc(v_defValue_58_);
v___x_67_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_67_, 0, v_name_54_);
lean_ctor_set(v___x_67_, 1, v_defValue_58_);
if (v_isShared_66_ == 0)
{
lean_ctor_set(v___x_65_, 0, v___x_67_);
v___x_69_ = v___x_65_;
goto v_reusejp_68_;
}
else
{
lean_object* v_reuseFailAlloc_70_; 
v_reuseFailAlloc_70_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_70_, 0, v___x_67_);
v___x_69_ = v_reuseFailAlloc_70_;
goto v_reusejp_68_;
}
v_reusejp_68_:
{
return v___x_69_;
}
}
}
else
{
lean_object* v_a_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_80_; 
lean_dec(v_name_54_);
v_a_73_ = lean_ctor_get(v___x_63_, 0);
v_isSharedCheck_80_ = !lean_is_exclusive(v___x_63_);
if (v_isSharedCheck_80_ == 0)
{
v___x_75_ = v___x_63_;
v_isShared_76_ = v_isSharedCheck_80_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_a_73_);
lean_dec(v___x_63_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_80_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
lean_object* v___x_78_; 
if (v_isShared_76_ == 0)
{
v___x_78_ = v___x_75_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v_a_73_);
v___x_78_ = v_reuseFailAlloc_79_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
return v___x_78_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_81_, lean_object* v_decl_82_, lean_object* v_ref_83_, lean_object* v_a_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Lean_Option_register___at___00__private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__spec__0(v_name_81_, v_decl_82_, v_ref_83_);
lean_dec_ref(v_decl_82_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_100_ = ((lean_object*)(l___private_Lean_Util_Profile_0__Lean_initFn___closed__1_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4_));
v___x_101_ = ((lean_object*)(l___private_Lean_Util_Profile_0__Lean_initFn___closed__3_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4_));
v___x_102_ = ((lean_object*)(l___private_Lean_Util_Profile_0__Lean_initFn___closed__4_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4_));
v___x_103_ = l_Lean_Option_register___at___00__private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__spec__0(v___x_100_, v___x_101_, v___x_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4____boxed(lean_object* v_a_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l___private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4_();
return v_res_105_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(lean_object* v_opts_106_, lean_object* v_opt_107_){
_start:
{
lean_object* v_name_108_; lean_object* v_defValue_109_; lean_object* v_map_110_; lean_object* v___x_111_; 
v_name_108_ = lean_ctor_get(v_opt_107_, 0);
v_defValue_109_ = lean_ctor_get(v_opt_107_, 1);
v_map_110_ = lean_ctor_get(v_opts_106_, 0);
v___x_111_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_110_, v_name_108_);
if (lean_obj_tag(v___x_111_) == 0)
{
uint8_t v___x_112_; 
v___x_112_ = lean_unbox(v_defValue_109_);
return v___x_112_;
}
else
{
lean_object* v_val_113_; 
v_val_113_ = lean_ctor_get(v___x_111_, 0);
lean_inc(v_val_113_);
lean_dec_ref(v___x_111_);
if (lean_obj_tag(v_val_113_) == 1)
{
uint8_t v_v_114_; 
v_v_114_ = lean_ctor_get_uint8(v_val_113_, 0);
lean_dec_ref(v_val_113_);
return v_v_114_;
}
else
{
uint8_t v___x_115_; 
lean_dec(v_val_113_);
v___x_115_ = lean_unbox(v_defValue_109_);
return v___x_115_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Profile_0__Lean_get__profiler_spec__0___boxed(lean_object* v_opts_116_, lean_object* v_opt_117_){
_start:
{
uint8_t v_res_118_; lean_object* v_r_119_; 
v_res_118_ = l_Lean_Option_get___at___00__private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(v_opts_116_, v_opt_117_);
lean_dec_ref(v_opt_117_);
lean_dec_ref(v_opts_116_);
v_r_119_ = lean_box(v_res_118_);
return v_r_119_;
}
}
LEAN_EXPORT uint8_t lean_get_profiler(lean_object* v_o_120_){
_start:
{
lean_object* v___x_121_; uint8_t v___x_122_; 
v___x_121_ = l_Lean_profiler;
v___x_122_ = l_Lean_Option_get___at___00__private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(v_o_120_, v___x_121_);
lean_dec_ref(v_o_120_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Profile_0__Lean_get__profiler___boxed(lean_object* v_o_123_){
_start:
{
uint8_t v_res_124_; lean_object* v_r_125_; 
v_res_124_ = lean_get_profiler(v_o_123_);
v_r_125_ = lean_box(v_res_124_);
return v_r_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_profiler_threshold_getSecs_spec__0(lean_object* v_opts_126_, lean_object* v_opt_127_){
_start:
{
lean_object* v_name_128_; lean_object* v_defValue_129_; lean_object* v_map_130_; lean_object* v___x_131_; 
v_name_128_ = lean_ctor_get(v_opt_127_, 0);
v_defValue_129_ = lean_ctor_get(v_opt_127_, 1);
v_map_130_ = lean_ctor_get(v_opts_126_, 0);
v___x_131_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_130_, v_name_128_);
if (lean_obj_tag(v___x_131_) == 0)
{
lean_inc(v_defValue_129_);
return v_defValue_129_;
}
else
{
lean_object* v_val_132_; 
v_val_132_ = lean_ctor_get(v___x_131_, 0);
lean_inc(v_val_132_);
lean_dec_ref(v___x_131_);
if (lean_obj_tag(v_val_132_) == 3)
{
lean_object* v_v_133_; 
v_v_133_ = lean_ctor_get(v_val_132_, 0);
lean_inc(v_v_133_);
lean_dec_ref(v_val_132_);
return v_v_133_;
}
else
{
lean_dec(v_val_132_);
lean_inc(v_defValue_129_);
return v_defValue_129_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_profiler_threshold_getSecs_spec__0___boxed(lean_object* v_opts_134_, lean_object* v_opt_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l_Lean_Option_get___at___00Lean_profiler_threshold_getSecs_spec__0(v_opts_134_, v_opt_135_);
lean_dec_ref(v_opt_135_);
lean_dec_ref(v_opts_134_);
return v_res_136_;
}
}
static double _init_l_Lean_profiler_threshold_getSecs___closed__0(void){
_start:
{
lean_object* v___x_137_; double v___x_138_; 
v___x_137_ = lean_unsigned_to_nat(1000u);
v___x_138_ = lean_float_of_nat(v___x_137_);
return v___x_138_;
}
}
LEAN_EXPORT double lean_get_profiler_threshold(lean_object* v_o_139_){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; double v___x_142_; double v___x_143_; double v___x_144_; 
v___x_140_ = l_Lean_profiler_threshold;
v___x_141_ = l_Lean_Option_get___at___00Lean_profiler_threshold_getSecs_spec__0(v_o_139_, v___x_140_);
lean_dec_ref(v_o_139_);
v___x_142_ = lean_float_of_nat(v___x_141_);
v___x_143_ = lean_float_once(&l_Lean_profiler_threshold_getSecs___closed__0, &l_Lean_profiler_threshold_getSecs___closed__0_once, _init_l_Lean_profiler_threshold_getSecs___closed__0);
v___x_144_ = lean_float_div(v___x_142_, v___x_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_profiler_threshold_getSecs___boxed(lean_object* v_o_145_){
_start:
{
double v_res_146_; lean_object* v_r_147_; 
v_res_146_ = lean_get_profiler_threshold(v_o_145_);
v_r_147_ = lean_box_float(v_res_146_);
return v_r_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileit___boxed(lean_object* v_00_u03b1_153_, lean_object* v_category_154_, lean_object* v_opts_155_, lean_object* v_fn_156_, lean_object* v_decl_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = lean_profileit(v_category_154_, v_opts_155_, v_fn_156_, v_decl_157_);
lean_dec_ref(v_opts_155_);
lean_dec_ref(v_category_154_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitIOUnsafe___redArg___lam__0(lean_object* v_act_159_){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = lean_apply_1(v_act_159_, lean_box(0));
if (lean_obj_tag(v___x_161_) == 0)
{
lean_object* v_a_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_169_; 
v_a_162_ = lean_ctor_get(v___x_161_, 0);
v_isSharedCheck_169_ = !lean_is_exclusive(v___x_161_);
if (v_isSharedCheck_169_ == 0)
{
v___x_164_ = v___x_161_;
v_isShared_165_ = v_isSharedCheck_169_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_a_162_);
lean_dec(v___x_161_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_169_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v___x_167_; 
if (v_isShared_165_ == 0)
{
lean_ctor_set_tag(v___x_164_, 1);
v___x_167_ = v___x_164_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v_a_162_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
}
else
{
lean_object* v_a_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_177_; 
v_a_170_ = lean_ctor_get(v___x_161_, 0);
v_isSharedCheck_177_ = !lean_is_exclusive(v___x_161_);
if (v_isSharedCheck_177_ == 0)
{
v___x_172_ = v___x_161_;
v_isShared_173_ = v_isSharedCheck_177_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_a_170_);
lean_dec(v___x_161_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_177_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v___x_175_; 
if (v_isShared_173_ == 0)
{
lean_ctor_set_tag(v___x_172_, 0);
v___x_175_ = v___x_172_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v_a_170_);
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
}
LEAN_EXPORT lean_object* l_Lean_profileitIOUnsafe___redArg___lam__0___boxed(lean_object* v_act_178_, lean_object* v___y_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Lean_profileitIOUnsafe___redArg___lam__0(v_act_178_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitIOUnsafe___redArg___lam__1(lean_object* v___f_181_, lean_object* v_x_182_){
_start:
{
lean_object* v___x_183_; 
v___x_183_ = l_unsafeBaseIO___redArg(v___f_181_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitIOUnsafe___redArg(lean_object* v_category_184_, lean_object* v_opts_185_, lean_object* v_act_186_, lean_object* v_decl_187_){
_start:
{
lean_object* v___f_189_; lean_object* v___f_190_; lean_object* v___x_191_; 
v___f_189_ = lean_alloc_closure((void*)(l_Lean_profileitIOUnsafe___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_189_, 0, v_act_186_);
v___f_190_ = lean_alloc_closure((void*)(l_Lean_profileitIOUnsafe___redArg___lam__1), 2, 1);
lean_closure_set(v___f_190_, 0, v___f_189_);
v___x_191_ = lean_profileit(v_category_184_, v_opts_185_, v___f_190_, v_decl_187_);
if (lean_obj_tag(v___x_191_) == 0)
{
lean_object* v_a_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_199_; 
v_a_192_ = lean_ctor_get(v___x_191_, 0);
v_isSharedCheck_199_ = !lean_is_exclusive(v___x_191_);
if (v_isSharedCheck_199_ == 0)
{
v___x_194_ = v___x_191_;
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_a_192_);
lean_dec(v___x_191_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___x_197_; 
if (v_isShared_195_ == 0)
{
lean_ctor_set_tag(v___x_194_, 1);
v___x_197_ = v___x_194_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v_a_192_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
else
{
lean_object* v_a_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_207_; 
v_a_200_ = lean_ctor_get(v___x_191_, 0);
v_isSharedCheck_207_ = !lean_is_exclusive(v___x_191_);
if (v_isSharedCheck_207_ == 0)
{
v___x_202_ = v___x_191_;
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_a_200_);
lean_dec(v___x_191_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_205_; 
if (v_isShared_203_ == 0)
{
lean_ctor_set_tag(v___x_202_, 0);
v___x_205_ = v___x_202_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v_a_200_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_profileitIOUnsafe___redArg___boxed(lean_object* v_category_208_, lean_object* v_opts_209_, lean_object* v_act_210_, lean_object* v_decl_211_, lean_object* v_a_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Lean_profileitIOUnsafe___redArg(v_category_208_, v_opts_209_, v_act_210_, v_decl_211_);
lean_dec_ref(v_opts_209_);
lean_dec_ref(v_category_208_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitIOUnsafe(lean_object* v_00_u03b5_214_, lean_object* v_00_u03b1_215_, lean_object* v_category_216_, lean_object* v_opts_217_, lean_object* v_act_218_, lean_object* v_decl_219_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = l_Lean_profileitIOUnsafe___redArg(v_category_216_, v_opts_217_, v_act_218_, v_decl_219_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitIOUnsafe___boxed(lean_object* v_00_u03b5_222_, lean_object* v_00_u03b1_223_, lean_object* v_category_224_, lean_object* v_opts_225_, lean_object* v_act_226_, lean_object* v_decl_227_, lean_object* v_a_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Lean_profileitIOUnsafe(v_00_u03b5_222_, v_00_u03b1_223_, v_category_224_, v_opts_225_, v_act_226_, v_decl_227_);
lean_dec_ref(v_opts_225_);
lean_dec_ref(v_category_224_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___redArg___lam__0(lean_object* v_category_230_, lean_object* v_opts_231_, lean_object* v_decl_232_, lean_object* v_00_u03b2_233_, lean_object* v_act_234_){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = l_Lean_profileitIOUnsafe___redArg(v_category_230_, v_opts_231_, v_act_234_, v_decl_232_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___redArg___lam__0___boxed(lean_object* v_category_237_, lean_object* v_opts_238_, lean_object* v_decl_239_, lean_object* v_00_u03b2_240_, lean_object* v_act_241_, lean_object* v___y_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_Lean_profileitM___redArg___lam__0(v_category_237_, v_opts_238_, v_decl_239_, v_00_u03b2_240_, v_act_241_);
lean_dec_ref(v_opts_238_);
lean_dec_ref(v_category_237_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___redArg(lean_object* v_inst_244_, lean_object* v_category_245_, lean_object* v_opts_246_, lean_object* v_act_247_, lean_object* v_decl_248_){
_start:
{
lean_object* v___f_249_; lean_object* v___x_250_; 
v___f_249_ = lean_alloc_closure((void*)(l_Lean_profileitM___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_249_, 0, v_category_245_);
lean_closure_set(v___f_249_, 1, v_opts_246_);
lean_closure_set(v___f_249_, 2, v_decl_248_);
v___x_250_ = lean_apply_3(v_inst_244_, lean_box(0), v___f_249_, v_act_247_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM(lean_object* v_m_251_, lean_object* v_00_u03b5_252_, lean_object* v_inst_253_, lean_object* v_00_u03b1_254_, lean_object* v_category_255_, lean_object* v_opts_256_, lean_object* v_act_257_, lean_object* v_decl_258_){
_start:
{
lean_object* v___x_259_; 
v___x_259_ = l_Lean_profileitM___redArg(v_inst_253_, v_category_255_, v_opts_256_, v_act_257_, v_decl_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_displayCumulativeProfilingTimes___boxed(lean_object* v_a_00___x40___internal___hyg_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = lean_display_cumulative_profiling_times();
return v_res_262_;
}
}
lean_object* runtime_initialize_Init_Data_OfScientific(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Options(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_Profile(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_OfScientific(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Options(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_profiler = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_profiler);
lean_dec_ref(res);
res = l___private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_profiler_threshold = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_profiler_threshold);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Util_Profile(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_OfScientific(uint8_t builtin);
lean_object* initialize_Lean_Data_Options(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_Profile(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_OfScientific(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Options(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_Profile(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Util_Profile(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Util_Profile(builtin);
}
#ifdef __cplusplus
}
#endif

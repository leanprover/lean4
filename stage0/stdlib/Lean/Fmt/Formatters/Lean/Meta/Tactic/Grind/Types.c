// Lean compiler output
// Module: Lean.Fmt.Formatters.Lean.Meta.Tactic.Grind.Types
// Imports: public import Lean.Fmt.FmtM.Basic public import Lean.Fmt.Formatters.Lean.Util.Trace meta import Lean.Meta.Tactic.Grind.Types import Init.Data
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
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_bracketed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtTraceTerm(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtDoElemTraceGoal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Fmt_fmtDoElemTraceGoal___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtDoElemTraceGoal___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtDoElemTraceGoal___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Fmt_fmtDoElemTraceGoal___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtDoElemTraceGoal___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtDoElemTraceGoal___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l_Lean_Fmt_fmtDoElemTraceGoal___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtDoElemTraceGoal___closed__2_value;
static const lean_string_object l_Lean_Fmt_fmtDoElemTraceGoal___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "doElemTrace_goal[_]__"};
static const lean_object* l_Lean_Fmt_fmtDoElemTraceGoal___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtDoElemTraceGoal___closed__3_value;
static const lean_ctor_object l_Lean_Fmt_fmtDoElemTraceGoal___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtDoElemTraceGoal___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoElemTraceGoal___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoElemTraceGoal___closed__4_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtDoElemTraceGoal___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoElemTraceGoal___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoElemTraceGoal___closed__4_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtDoElemTraceGoal___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoElemTraceGoal___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoElemTraceGoal___closed__4_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtDoElemTraceGoal___closed__3_value),LEAN_SCALAR_PTR_LITERAL(243, 251, 228, 156, 128, 180, 3, 242)}};
static const lean_object* l_Lean_Fmt_fmtDoElemTraceGoal___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtDoElemTraceGoal___closed__4_value;
static const lean_string_object l_Lean_Fmt_fmtDoElemTraceGoal___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Fmt_fmtDoElemTraceGoal___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtDoElemTraceGoal___closed__5_value;
static const lean_ctor_object l_Lean_Fmt_fmtDoElemTraceGoal___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtDoElemTraceGoal___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Fmt_fmtDoElemTraceGoal___closed__6 = (const lean_object*)&l_Lean_Fmt_fmtDoElemTraceGoal___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoElemTraceGoal(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoElemTraceGoal___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Types_0__Lean_Fmt_fmtDoElemTraceGoal___regBuiltin_Lean_Fmt_fmtDoElemTraceGoal__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Types_0__Lean_Fmt_fmtDoElemTraceGoal___regBuiltin_Lean_Fmt_fmtDoElemTraceGoal__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Types_0__Lean_Fmt_fmtDoElemTraceGoal___regBuiltin_Lean_Fmt_fmtDoElemTraceGoal__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Types_0__Lean_Fmt_fmtDoElemTraceGoal___regBuiltin_Lean_Fmt_fmtDoElemTraceGoal__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "fmtDoElemTraceGoal"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Types_0__Lean_Fmt_fmtDoElemTraceGoal___regBuiltin_Lean_Fmt_fmtDoElemTraceGoal__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Types_0__Lean_Fmt_fmtDoElemTraceGoal___regBuiltin_Lean_Fmt_fmtDoElemTraceGoal__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Types_0__Lean_Fmt_fmtDoElemTraceGoal___regBuiltin_Lean_Fmt_fmtDoElemTraceGoal__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtDoElemTraceGoal___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Types_0__Lean_Fmt_fmtDoElemTraceGoal___regBuiltin_Lean_Fmt_fmtDoElemTraceGoal__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Types_0__Lean_Fmt_fmtDoElemTraceGoal___regBuiltin_Lean_Fmt_fmtDoElemTraceGoal__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Types_0__Lean_Fmt_fmtDoElemTraceGoal___regBuiltin_Lean_Fmt_fmtDoElemTraceGoal__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Types_0__Lean_Fmt_fmtDoElemTraceGoal___regBuiltin_Lean_Fmt_fmtDoElemTraceGoal__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Types_0__Lean_Fmt_fmtDoElemTraceGoal___regBuiltin_Lean_Fmt_fmtDoElemTraceGoal__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Types_0__Lean_Fmt_fmtDoElemTraceGoal___regBuiltin_Lean_Fmt_fmtDoElemTraceGoal__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(130, 156, 41, 153, 110, 124, 163, 128)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Types_0__Lean_Fmt_fmtDoElemTraceGoal___regBuiltin_Lean_Fmt_fmtDoElemTraceGoal__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Types_0__Lean_Fmt_fmtDoElemTraceGoal___regBuiltin_Lean_Fmt_fmtDoElemTraceGoal__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Types_0__Lean_Fmt_fmtDoElemTraceGoal___regBuiltin_Lean_Fmt_fmtDoElemTraceGoal__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Types_0__Lean_Fmt_fmtDoElemTraceGoal___regBuiltin_Lean_Fmt_fmtDoElemTraceGoal__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoElemTraceGoal(lean_object* v_x_13_, lean_object* v_a_14_, lean_object* v_a_15_){
_start:
{
lean_object* v___x_16_; uint8_t v___x_17_; 
v___x_16_ = ((lean_object*)(l_Lean_Fmt_fmtDoElemTraceGoal___closed__4));
lean_inc(v_x_13_);
v___x_17_ = l_Lean_Syntax_isOfKind(v_x_13_, v___x_16_);
if (v___x_17_ == 0)
{
lean_object* v___x_18_; lean_object* v___x_19_; 
lean_dec(v_x_13_);
v___x_18_ = l_Lean_Fmt_Error_partialFormatter;
v___x_19_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_19_, 0, v___x_18_);
lean_ctor_set(v___x_19_, 1, v_a_15_);
return v___x_19_;
}
else
{
lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; uint8_t v___x_23_; 
v___x_20_ = lean_unsigned_to_nat(1u);
v___x_21_ = l_Lean_Syntax_getArg(v_x_13_, v___x_20_);
v___x_22_ = ((lean_object*)(l_Lean_Fmt_fmtDoElemTraceGoal___closed__6));
lean_inc(v___x_21_);
v___x_23_ = l_Lean_Syntax_isOfKind(v___x_21_, v___x_22_);
if (v___x_23_ == 0)
{
lean_object* v___x_24_; lean_object* v___x_25_; 
lean_dec(v___x_21_);
lean_dec(v_x_13_);
v___x_24_ = l_Lean_Fmt_Error_partialFormatter;
v___x_25_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_25_, 0, v___x_24_);
lean_ctor_set(v___x_25_, 1, v_a_15_);
return v___x_25_;
}
else
{
lean_object* v___x_26_; lean_object* v_traceGoalTk_27_; lean_object* v___x_28_; 
v___x_26_ = lean_unsigned_to_nat(0u);
v_traceGoalTk_27_ = l_Lean_Syntax_getArg(v_x_13_, v___x_26_);
v___x_28_ = l_Lean_Fmt_fmt(v_traceGoalTk_27_, v_a_14_, v_a_15_);
if (lean_obj_tag(v___x_28_) == 0)
{
lean_object* v_a_29_; lean_object* v_a_30_; lean_object* v___x_31_; 
v_a_29_ = lean_ctor_get(v___x_28_, 0);
lean_inc(v_a_29_);
v_a_30_ = lean_ctor_get(v___x_28_, 1);
lean_inc(v_a_30_);
lean_dec_ref_known(v___x_28_, 2);
v___x_31_ = l_Lean_Fmt_fmt(v___x_21_, v_a_14_, v_a_30_);
if (lean_obj_tag(v___x_31_) == 0)
{
lean_object* v_a_32_; lean_object* v_a_33_; lean_object* v___x_34_; lean_object* v_rbTk_35_; lean_object* v___x_36_; 
v_a_32_ = lean_ctor_get(v___x_31_, 0);
lean_inc(v_a_32_);
v_a_33_ = lean_ctor_get(v___x_31_, 1);
lean_inc(v_a_33_);
lean_dec_ref_known(v___x_31_, 2);
v___x_34_ = lean_unsigned_to_nat(2u);
v_rbTk_35_ = l_Lean_Syntax_getArg(v_x_13_, v___x_34_);
v___x_36_ = l_Lean_Fmt_fmt(v_rbTk_35_, v_a_14_, v_a_33_);
if (lean_obj_tag(v___x_36_) == 0)
{
lean_object* v_a_37_; lean_object* v_a_38_; lean_object* v___x_39_; lean_object* v___x_40_; uint8_t v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v_a_37_ = lean_ctor_get(v___x_36_, 0);
lean_inc(v_a_37_);
v_a_38_ = lean_ctor_get(v___x_36_, 1);
lean_inc(v_a_38_);
lean_dec_ref_known(v___x_36_, 2);
v___x_39_ = lean_unsigned_to_nat(3u);
v___x_40_ = l_Lean_Syntax_getArg(v_x_13_, v___x_39_);
lean_dec(v_x_13_);
v___x_41_ = 0;
v___x_42_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_42_, 0, v___x_41_);
lean_ctor_set_uint8(v___x_42_, 1, v___x_23_);
v___x_43_ = l_Lean_Fmt_Layouts_bracketed(v_a_29_, v_a_32_, v_a_37_, v___x_42_);
v___x_44_ = l_Lean_Fmt_fmtTraceTerm(v___x_43_, v___x_40_, v_a_14_, v_a_38_);
return v___x_44_;
}
else
{
lean_dec(v_a_32_);
lean_dec(v_a_29_);
lean_dec(v_x_13_);
return v___x_36_;
}
}
else
{
lean_dec(v_a_29_);
lean_dec(v_x_13_);
return v___x_31_;
}
}
else
{
lean_dec(v___x_21_);
lean_dec(v_x_13_);
return v___x_28_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoElemTraceGoal___boxed(lean_object* v_x_45_, lean_object* v_a_46_, lean_object* v_a_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l_Lean_Fmt_fmtDoElemTraceGoal(v_x_45_, v_a_46_, v_a_47_);
lean_dec_ref(v_a_46_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Types_0__Lean_Fmt_fmtDoElemTraceGoal___regBuiltin_Lean_Fmt_fmtDoElemTraceGoal__1(){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_56_ = l_Lean_Fmt_fmtAttribute;
v___x_57_ = ((lean_object*)(l_Lean_Fmt_fmtDoElemTraceGoal___closed__4));
v___x_58_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Types_0__Lean_Fmt_fmtDoElemTraceGoal___regBuiltin_Lean_Fmt_fmtDoElemTraceGoal__1___closed__2));
v___x_59_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtDoElemTraceGoal___boxed), 3, 0);
v___x_60_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_56_, v___x_57_, v___x_58_, v___x_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Types_0__Lean_Fmt_fmtDoElemTraceGoal___regBuiltin_Lean_Fmt_fmtDoElemTraceGoal__1___boxed(lean_object* v_a_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Types_0__Lean_Fmt_fmtDoElemTraceGoal___regBuiltin_Lean_Fmt_fmtDoElemTraceGoal__1();
return v_res_62_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Formatters_Lean_Util_Trace(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Types(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Lean_Util_Trace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Types_0__Lean_Fmt_fmtDoElemTraceGoal___regBuiltin_Lean_Fmt_fmtDoElemTraceGoal__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Types(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Formatters_Lean_Util_Trace(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Types(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Formatters_Lean_Util_Trace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Types(builtin);
}
#ifdef __cplusplus
}
#endif

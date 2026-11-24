// Lean compiler output
// Module: Lean.Fmt.Formatters.Init.MacroTrace
// Imports: public import Lean.Fmt.FmtM.Basic meta import Init.MacroTrace import Init.Data
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_bracketed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_pseudoApplication(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtMacroTrace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Fmt_fmtMacroTrace___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtMacroTrace___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtMacroTrace___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "termMacro.trace[_]_"};
static const lean_object* l_Lean_Fmt_fmtMacroTrace___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtMacroTrace___closed__1_value;
static const lean_ctor_object l_Lean_Fmt_fmtMacroTrace___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMacroTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtMacroTrace___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMacroTrace___closed__2_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtMacroTrace___closed__1_value),LEAN_SCALAR_PTR_LITERAL(43, 106, 148, 90, 66, 246, 255, 117)}};
static const lean_object* l_Lean_Fmt_fmtMacroTrace___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtMacroTrace___closed__2_value;
static const lean_string_object l_Lean_Fmt_fmtMacroTrace___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Fmt_fmtMacroTrace___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtMacroTrace___closed__3_value;
static const lean_ctor_object l_Lean_Fmt_fmtMacroTrace___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMacroTrace___closed__3_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Fmt_fmtMacroTrace___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtMacroTrace___closed__4_value;
static const lean_string_object l_Lean_Fmt_fmtMacroTrace___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "interpolatedStrKind"};
static const lean_object* l_Lean_Fmt_fmtMacroTrace___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtMacroTrace___closed__5_value;
static const lean_ctor_object l_Lean_Fmt_fmtMacroTrace___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMacroTrace___closed__5_value),LEAN_SCALAR_PTR_LITERAL(239, 118, 32, 248, 73, 51, 110, 198)}};
static const lean_object* l_Lean_Fmt_fmtMacroTrace___closed__6 = (const lean_object*)&l_Lean_Fmt_fmtMacroTrace___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMacroTrace(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMacroTrace___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_MacroTrace_0__Lean_Fmt_fmtMacroTrace___regBuiltin_Lean_Fmt_fmtMacroTrace__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_MacroTrace_0__Lean_Fmt_fmtMacroTrace___regBuiltin_Lean_Fmt_fmtMacroTrace__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_MacroTrace_0__Lean_Fmt_fmtMacroTrace___regBuiltin_Lean_Fmt_fmtMacroTrace__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_MacroTrace_0__Lean_Fmt_fmtMacroTrace___regBuiltin_Lean_Fmt_fmtMacroTrace__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtMacroTrace"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_MacroTrace_0__Lean_Fmt_fmtMacroTrace___regBuiltin_Lean_Fmt_fmtMacroTrace__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_MacroTrace_0__Lean_Fmt_fmtMacroTrace___regBuiltin_Lean_Fmt_fmtMacroTrace__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_MacroTrace_0__Lean_Fmt_fmtMacroTrace___regBuiltin_Lean_Fmt_fmtMacroTrace__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMacroTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_MacroTrace_0__Lean_Fmt_fmtMacroTrace___regBuiltin_Lean_Fmt_fmtMacroTrace__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_MacroTrace_0__Lean_Fmt_fmtMacroTrace___regBuiltin_Lean_Fmt_fmtMacroTrace__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_MacroTrace_0__Lean_Fmt_fmtMacroTrace___regBuiltin_Lean_Fmt_fmtMacroTrace__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_MacroTrace_0__Lean_Fmt_fmtMacroTrace___regBuiltin_Lean_Fmt_fmtMacroTrace__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_MacroTrace_0__Lean_Fmt_fmtMacroTrace___regBuiltin_Lean_Fmt_fmtMacroTrace__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_MacroTrace_0__Lean_Fmt_fmtMacroTrace___regBuiltin_Lean_Fmt_fmtMacroTrace__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(39, 56, 225, 200, 22, 200, 14, 0)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_MacroTrace_0__Lean_Fmt_fmtMacroTrace___regBuiltin_Lean_Fmt_fmtMacroTrace__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_MacroTrace_0__Lean_Fmt_fmtMacroTrace___regBuiltin_Lean_Fmt_fmtMacroTrace__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_MacroTrace_0__Lean_Fmt_fmtMacroTrace___regBuiltin_Lean_Fmt_fmtMacroTrace__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_MacroTrace_0__Lean_Fmt_fmtMacroTrace___regBuiltin_Lean_Fmt_fmtMacroTrace__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMacroTrace(lean_object* v_x_12_, lean_object* v_a_13_, lean_object* v_a_14_){
_start:
{
lean_object* v___x_15_; uint8_t v___x_16_; 
v___x_15_ = ((lean_object*)(l_Lean_Fmt_fmtMacroTrace___closed__2));
lean_inc(v_x_12_);
v___x_16_ = l_Lean_Syntax_isOfKind(v_x_12_, v___x_15_);
if (v___x_16_ == 0)
{
lean_object* v___x_17_; lean_object* v___x_18_; 
lean_dec(v_x_12_);
v___x_17_ = l_Lean_Fmt_Error_partialFormatter;
v___x_18_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_18_, 0, v___x_17_);
lean_ctor_set(v___x_18_, 1, v_a_14_);
return v___x_18_;
}
else
{
lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; uint8_t v___x_22_; 
v___x_19_ = lean_unsigned_to_nat(1u);
v___x_20_ = l_Lean_Syntax_getArg(v_x_12_, v___x_19_);
v___x_21_ = ((lean_object*)(l_Lean_Fmt_fmtMacroTrace___closed__4));
lean_inc(v___x_20_);
v___x_22_ = l_Lean_Syntax_isOfKind(v___x_20_, v___x_21_);
if (v___x_22_ == 0)
{
lean_object* v___x_23_; lean_object* v___x_24_; 
lean_dec(v___x_20_);
lean_dec(v_x_12_);
v___x_23_ = l_Lean_Fmt_Error_partialFormatter;
v___x_24_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_24_, 0, v___x_23_);
lean_ctor_set(v___x_24_, 1, v_a_14_);
return v___x_24_;
}
else
{
lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; uint8_t v___x_28_; 
v___x_25_ = lean_unsigned_to_nat(3u);
v___x_26_ = l_Lean_Syntax_getArg(v_x_12_, v___x_25_);
v___x_27_ = ((lean_object*)(l_Lean_Fmt_fmtMacroTrace___closed__6));
lean_inc(v___x_26_);
v___x_28_ = l_Lean_Syntax_isOfKind(v___x_26_, v___x_27_);
if (v___x_28_ == 0)
{
lean_object* v___x_29_; lean_object* v___x_30_; 
lean_dec(v___x_26_);
lean_dec(v___x_20_);
lean_dec(v_x_12_);
v___x_29_ = l_Lean_Fmt_Error_partialFormatter;
v___x_30_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_30_, 0, v___x_29_);
lean_ctor_set(v___x_30_, 1, v_a_14_);
return v___x_30_;
}
else
{
lean_object* v___x_31_; lean_object* v_lbTk_32_; lean_object* v___x_33_; 
v___x_31_ = lean_unsigned_to_nat(0u);
v_lbTk_32_ = l_Lean_Syntax_getArg(v_x_12_, v___x_31_);
v___x_33_ = l_Lean_Fmt_fmt(v_lbTk_32_, v_a_13_, v_a_14_);
if (lean_obj_tag(v___x_33_) == 0)
{
lean_object* v_a_34_; lean_object* v_a_35_; lean_object* v___x_36_; 
v_a_34_ = lean_ctor_get(v___x_33_, 0);
lean_inc(v_a_34_);
v_a_35_ = lean_ctor_get(v___x_33_, 1);
lean_inc(v_a_35_);
lean_dec_ref_known(v___x_33_, 2);
v___x_36_ = l_Lean_Fmt_fmt(v___x_20_, v_a_13_, v_a_35_);
if (lean_obj_tag(v___x_36_) == 0)
{
lean_object* v_a_37_; lean_object* v_a_38_; lean_object* v___x_39_; lean_object* v_rbTk_40_; lean_object* v___x_41_; 
v_a_37_ = lean_ctor_get(v___x_36_, 0);
lean_inc(v_a_37_);
v_a_38_ = lean_ctor_get(v___x_36_, 1);
lean_inc(v_a_38_);
lean_dec_ref_known(v___x_36_, 2);
v___x_39_ = lean_unsigned_to_nat(2u);
v_rbTk_40_ = l_Lean_Syntax_getArg(v_x_12_, v___x_39_);
lean_dec(v_x_12_);
v___x_41_ = l_Lean_Fmt_fmt(v_rbTk_40_, v_a_13_, v_a_38_);
if (lean_obj_tag(v___x_41_) == 0)
{
lean_object* v_a_42_; lean_object* v_a_43_; lean_object* v___x_44_; 
v_a_42_ = lean_ctor_get(v___x_41_, 0);
lean_inc(v_a_42_);
v_a_43_ = lean_ctor_get(v___x_41_, 1);
lean_inc(v_a_43_);
lean_dec_ref_known(v___x_41_, 2);
v___x_44_ = l_Lean_Fmt_fmt(v___x_26_, v_a_13_, v_a_43_);
if (lean_obj_tag(v___x_44_) == 0)
{
lean_object* v_a_45_; lean_object* v_a_46_; lean_object* v___x_48_; uint8_t v_isShared_49_; uint8_t v_isSharedCheck_61_; 
v_a_45_ = lean_ctor_get(v___x_44_, 0);
v_a_46_ = lean_ctor_get(v___x_44_, 1);
v_isSharedCheck_61_ = !lean_is_exclusive(v___x_44_);
if (v_isSharedCheck_61_ == 0)
{
v___x_48_ = v___x_44_;
v_isShared_49_ = v_isSharedCheck_61_;
goto v_resetjp_47_;
}
else
{
lean_inc(v_a_46_);
lean_inc(v_a_45_);
lean_dec(v___x_44_);
v___x_48_ = lean_box(0);
v_isShared_49_ = v_isSharedCheck_61_;
goto v_resetjp_47_;
}
v_resetjp_47_:
{
uint8_t v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_59_; 
v___x_50_ = 0;
v___x_51_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_51_, 0, v___x_50_);
lean_ctor_set_uint8(v___x_51_, 1, v___x_28_);
v___x_52_ = l_Lean_Fmt_Layouts_bracketed(v_a_34_, v_a_37_, v_a_42_, v___x_51_);
v___x_53_ = lean_mk_empty_array_with_capacity(v___x_39_);
v___x_54_ = lean_array_push(v___x_53_, v___x_52_);
v___x_55_ = lean_array_push(v___x_54_, v_a_45_);
v___x_56_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_56_, 0, v___x_28_);
lean_ctor_set_uint8(v___x_56_, 1, v___x_50_);
lean_ctor_set_uint8(v___x_56_, 2, v___x_50_);
lean_ctor_set_uint8(v___x_56_, 3, v___x_50_);
v___x_57_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_55_, v___x_56_);
if (v_isShared_49_ == 0)
{
lean_ctor_set(v___x_48_, 0, v___x_57_);
v___x_59_ = v___x_48_;
goto v_reusejp_58_;
}
else
{
lean_object* v_reuseFailAlloc_60_; 
v_reuseFailAlloc_60_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_60_, 0, v___x_57_);
lean_ctor_set(v_reuseFailAlloc_60_, 1, v_a_46_);
v___x_59_ = v_reuseFailAlloc_60_;
goto v_reusejp_58_;
}
v_reusejp_58_:
{
return v___x_59_;
}
}
}
else
{
lean_dec(v_a_42_);
lean_dec(v_a_37_);
lean_dec(v_a_34_);
return v___x_44_;
}
}
else
{
lean_dec(v_a_37_);
lean_dec(v_a_34_);
lean_dec(v___x_26_);
return v___x_41_;
}
}
else
{
lean_dec(v_a_34_);
lean_dec(v___x_26_);
lean_dec(v_x_12_);
return v___x_36_;
}
}
else
{
lean_dec(v___x_26_);
lean_dec(v___x_20_);
lean_dec(v_x_12_);
return v___x_33_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMacroTrace___boxed(lean_object* v_x_62_, lean_object* v_a_63_, lean_object* v_a_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_Lean_Fmt_fmtMacroTrace(v_x_62_, v_a_63_, v_a_64_);
lean_dec_ref(v_a_63_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_MacroTrace_0__Lean_Fmt_fmtMacroTrace___regBuiltin_Lean_Fmt_fmtMacroTrace__1(){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_73_ = l_Lean_Fmt_fmtAttribute;
v___x_74_ = ((lean_object*)(l_Lean_Fmt_fmtMacroTrace___closed__2));
v___x_75_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_MacroTrace_0__Lean_Fmt_fmtMacroTrace___regBuiltin_Lean_Fmt_fmtMacroTrace__1___closed__2));
v___x_76_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtMacroTrace___boxed), 3, 0);
v___x_77_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_73_, v___x_74_, v___x_75_, v___x_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_MacroTrace_0__Lean_Fmt_fmtMacroTrace___regBuiltin_Lean_Fmt_fmtMacroTrace__1___boxed(lean_object* v_a_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l___private_Lean_Fmt_Formatters_Init_MacroTrace_0__Lean_Fmt_fmtMacroTrace___regBuiltin_Lean_Fmt_fmtMacroTrace__1();
return v_res_79_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_MacroTrace(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_MacroTrace_0__Lean_Fmt_fmtMacroTrace___regBuiltin_Lean_Fmt_fmtMacroTrace__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_MacroTrace(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Init_MacroTrace(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_MacroTrace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Init_MacroTrace(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Init_MacroTrace(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_MacroTrace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Init_MacroTrace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Init_MacroTrace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Init_MacroTrace(builtin);
}
#ifdef __cplusplus
}
#endif

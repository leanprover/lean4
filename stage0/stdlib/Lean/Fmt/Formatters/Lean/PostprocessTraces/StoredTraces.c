// Lean compiler output
// Module: Lean.Fmt.Formatters.Lean.PostprocessTraces.StoredTraces
// Imports: public import Lean.Fmt.FmtM.Basic public import Lean.Fmt.Formatters.Lean.PostprocessTraces.PostprocessTracesCommand meta import Lean.PostprocessTraces.StoredTraces import Init.Data
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_fmtAttribute;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_pseudoApplication(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtTracedCommand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtStoreTracesAsCmd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Fmt_fmtStoreTracesAsCmd___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtStoreTracesAsCmd___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtStoreTracesAsCmd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "PostprocessTraces"};
static const lean_object* l_Lean_Fmt_fmtStoreTracesAsCmd___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtStoreTracesAsCmd___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtStoreTracesAsCmd___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "storeTracesAsCmd"};
static const lean_object* l_Lean_Fmt_fmtStoreTracesAsCmd___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtStoreTracesAsCmd___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtStoreTracesAsCmd___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtStoreTracesAsCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtStoreTracesAsCmd___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtStoreTracesAsCmd___closed__3_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtStoreTracesAsCmd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(169, 31, 168, 57, 105, 170, 97, 138)}};
static const lean_ctor_object l_Lean_Fmt_fmtStoreTracesAsCmd___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtStoreTracesAsCmd___closed__3_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtStoreTracesAsCmd___closed__2_value),LEAN_SCALAR_PTR_LITERAL(234, 198, 145, 81, 140, 195, 110, 227)}};
static const lean_object* l_Lean_Fmt_fmtStoreTracesAsCmd___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtStoreTracesAsCmd___closed__3_value;
static const lean_string_object l_Lean_Fmt_fmtStoreTracesAsCmd___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Fmt_fmtStoreTracesAsCmd___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtStoreTracesAsCmd___closed__4_value;
static const lean_ctor_object l_Lean_Fmt_fmtStoreTracesAsCmd___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtStoreTracesAsCmd___closed__4_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Fmt_fmtStoreTracesAsCmd___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtStoreTracesAsCmd___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtStoreTracesAsCmd(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtStoreTracesAsCmd___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_PostprocessTraces_StoredTraces_0__Lean_Fmt_fmtStoreTracesAsCmd___regBuiltin_Lean_Fmt_fmtStoreTracesAsCmd__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_PostprocessTraces_StoredTraces_0__Lean_Fmt_fmtStoreTracesAsCmd___regBuiltin_Lean_Fmt_fmtStoreTracesAsCmd__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_PostprocessTraces_StoredTraces_0__Lean_Fmt_fmtStoreTracesAsCmd___regBuiltin_Lean_Fmt_fmtStoreTracesAsCmd__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_PostprocessTraces_StoredTraces_0__Lean_Fmt_fmtStoreTracesAsCmd___regBuiltin_Lean_Fmt_fmtStoreTracesAsCmd__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "fmtStoreTracesAsCmd"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_PostprocessTraces_StoredTraces_0__Lean_Fmt_fmtStoreTracesAsCmd___regBuiltin_Lean_Fmt_fmtStoreTracesAsCmd__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_PostprocessTraces_StoredTraces_0__Lean_Fmt_fmtStoreTracesAsCmd___regBuiltin_Lean_Fmt_fmtStoreTracesAsCmd__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_PostprocessTraces_StoredTraces_0__Lean_Fmt_fmtStoreTracesAsCmd___regBuiltin_Lean_Fmt_fmtStoreTracesAsCmd__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtStoreTracesAsCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_PostprocessTraces_StoredTraces_0__Lean_Fmt_fmtStoreTracesAsCmd___regBuiltin_Lean_Fmt_fmtStoreTracesAsCmd__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_PostprocessTraces_StoredTraces_0__Lean_Fmt_fmtStoreTracesAsCmd___regBuiltin_Lean_Fmt_fmtStoreTracesAsCmd__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_PostprocessTraces_StoredTraces_0__Lean_Fmt_fmtStoreTracesAsCmd___regBuiltin_Lean_Fmt_fmtStoreTracesAsCmd__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_PostprocessTraces_StoredTraces_0__Lean_Fmt_fmtStoreTracesAsCmd___regBuiltin_Lean_Fmt_fmtStoreTracesAsCmd__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_PostprocessTraces_StoredTraces_0__Lean_Fmt_fmtStoreTracesAsCmd___regBuiltin_Lean_Fmt_fmtStoreTracesAsCmd__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_PostprocessTraces_StoredTraces_0__Lean_Fmt_fmtStoreTracesAsCmd___regBuiltin_Lean_Fmt_fmtStoreTracesAsCmd__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(158, 18, 9, 82, 110, 158, 81, 155)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_PostprocessTraces_StoredTraces_0__Lean_Fmt_fmtStoreTracesAsCmd___regBuiltin_Lean_Fmt_fmtStoreTracesAsCmd__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_PostprocessTraces_StoredTraces_0__Lean_Fmt_fmtStoreTracesAsCmd___regBuiltin_Lean_Fmt_fmtStoreTracesAsCmd__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_PostprocessTraces_StoredTraces_0__Lean_Fmt_fmtStoreTracesAsCmd___regBuiltin_Lean_Fmt_fmtStoreTracesAsCmd__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_PostprocessTraces_StoredTraces_0__Lean_Fmt_fmtStoreTracesAsCmd___regBuiltin_Lean_Fmt_fmtStoreTracesAsCmd__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtPostprocessStoredTracesCmd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "postprocessStoredTracesCmd"};
static const lean_object* l_Lean_Fmt_fmtPostprocessStoredTracesCmd___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtPostprocessStoredTracesCmd___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtPostprocessStoredTracesCmd___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtStoreTracesAsCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtPostprocessStoredTracesCmd___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtPostprocessStoredTracesCmd___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtStoreTracesAsCmd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(169, 31, 168, 57, 105, 170, 97, 138)}};
static const lean_ctor_object l_Lean_Fmt_fmtPostprocessStoredTracesCmd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtPostprocessStoredTracesCmd___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtPostprocessStoredTracesCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 232, 148, 233, 198, 180, 134, 53)}};
static const lean_object* l_Lean_Fmt_fmtPostprocessStoredTracesCmd___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtPostprocessStoredTracesCmd___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPostprocessStoredTracesCmd(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPostprocessStoredTracesCmd___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_PostprocessTraces_StoredTraces_0__Lean_Fmt_fmtPostprocessStoredTracesCmd___regBuiltin_Lean_Fmt_fmtPostprocessStoredTracesCmd__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "fmtPostprocessStoredTracesCmd"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_PostprocessTraces_StoredTraces_0__Lean_Fmt_fmtPostprocessStoredTracesCmd___regBuiltin_Lean_Fmt_fmtPostprocessStoredTracesCmd__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_PostprocessTraces_StoredTraces_0__Lean_Fmt_fmtPostprocessStoredTracesCmd___regBuiltin_Lean_Fmt_fmtPostprocessStoredTracesCmd__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_PostprocessTraces_StoredTraces_0__Lean_Fmt_fmtPostprocessStoredTracesCmd___regBuiltin_Lean_Fmt_fmtPostprocessStoredTracesCmd__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtStoreTracesAsCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_PostprocessTraces_StoredTraces_0__Lean_Fmt_fmtPostprocessStoredTracesCmd___regBuiltin_Lean_Fmt_fmtPostprocessStoredTracesCmd__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_PostprocessTraces_StoredTraces_0__Lean_Fmt_fmtPostprocessStoredTracesCmd___regBuiltin_Lean_Fmt_fmtPostprocessStoredTracesCmd__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_PostprocessTraces_StoredTraces_0__Lean_Fmt_fmtStoreTracesAsCmd___regBuiltin_Lean_Fmt_fmtStoreTracesAsCmd__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_PostprocessTraces_StoredTraces_0__Lean_Fmt_fmtPostprocessStoredTracesCmd___regBuiltin_Lean_Fmt_fmtPostprocessStoredTracesCmd__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_PostprocessTraces_StoredTraces_0__Lean_Fmt_fmtPostprocessStoredTracesCmd___regBuiltin_Lean_Fmt_fmtPostprocessStoredTracesCmd__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_PostprocessTraces_StoredTraces_0__Lean_Fmt_fmtPostprocessStoredTracesCmd___regBuiltin_Lean_Fmt_fmtPostprocessStoredTracesCmd__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(25, 120, 244, 75, 192, 1, 181, 162)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_PostprocessTraces_StoredTraces_0__Lean_Fmt_fmtPostprocessStoredTracesCmd___regBuiltin_Lean_Fmt_fmtPostprocessStoredTracesCmd__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_PostprocessTraces_StoredTraces_0__Lean_Fmt_fmtPostprocessStoredTracesCmd___regBuiltin_Lean_Fmt_fmtPostprocessStoredTracesCmd__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_PostprocessTraces_StoredTraces_0__Lean_Fmt_fmtPostprocessStoredTracesCmd___regBuiltin_Lean_Fmt_fmtPostprocessStoredTracesCmd__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_PostprocessTraces_StoredTraces_0__Lean_Fmt_fmtPostprocessStoredTracesCmd___regBuiltin_Lean_Fmt_fmtPostprocessStoredTracesCmd__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtStoreTracesAsCmd(lean_object* v_x_11_, lean_object* v_a_12_, lean_object* v_a_13_){
_start:
{
lean_object* v___x_14_; uint8_t v___x_15_; 
v___x_14_ = ((lean_object*)(l_Lean_Fmt_fmtStoreTracesAsCmd___closed__3));
lean_inc(v_x_11_);
v___x_15_ = l_Lean_Syntax_isOfKind(v_x_11_, v___x_14_);
if (v___x_15_ == 0)
{
lean_object* v___x_16_; lean_object* v___x_17_; 
lean_dec(v_x_11_);
v___x_16_ = l_Lean_Fmt_Error_partialFormatter;
v___x_17_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_17_, 0, v___x_16_);
lean_ctor_set(v___x_17_, 1, v_a_13_);
return v___x_17_;
}
else
{
lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; uint8_t v___x_21_; 
v___x_18_ = lean_unsigned_to_nat(1u);
v___x_19_ = l_Lean_Syntax_getArg(v_x_11_, v___x_18_);
v___x_20_ = ((lean_object*)(l_Lean_Fmt_fmtStoreTracesAsCmd___closed__5));
lean_inc(v___x_19_);
v___x_21_ = l_Lean_Syntax_isOfKind(v___x_19_, v___x_20_);
if (v___x_21_ == 0)
{
lean_object* v___x_22_; lean_object* v___x_23_; 
lean_dec(v___x_19_);
lean_dec(v_x_11_);
v___x_22_ = l_Lean_Fmt_Error_partialFormatter;
v___x_23_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_23_, 0, v___x_22_);
lean_ctor_set(v___x_23_, 1, v_a_13_);
return v___x_23_;
}
else
{
lean_object* v___x_24_; lean_object* v_storeTk_25_; lean_object* v___x_26_; lean_object* v_inTk_27_; lean_object* v___x_28_; lean_object* v_cmd_29_; lean_object* v___x_30_; 
v___x_24_ = lean_unsigned_to_nat(0u);
v_storeTk_25_ = l_Lean_Syntax_getArg(v_x_11_, v___x_24_);
v___x_26_ = lean_unsigned_to_nat(2u);
v_inTk_27_ = l_Lean_Syntax_getArg(v_x_11_, v___x_26_);
v___x_28_ = lean_unsigned_to_nat(3u);
v_cmd_29_ = l_Lean_Syntax_getArg(v_x_11_, v___x_28_);
lean_dec(v_x_11_);
v___x_30_ = l_Lean_Fmt_fmtTracedCommand(v_storeTk_25_, v___x_19_, v_inTk_27_, v_cmd_29_, v_a_12_, v_a_13_);
return v___x_30_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtStoreTracesAsCmd___boxed(lean_object* v_x_31_, lean_object* v_a_32_, lean_object* v_a_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lean_Fmt_fmtStoreTracesAsCmd(v_x_31_, v_a_32_, v_a_33_);
lean_dec_ref(v_a_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_PostprocessTraces_StoredTraces_0__Lean_Fmt_fmtStoreTracesAsCmd___regBuiltin_Lean_Fmt_fmtStoreTracesAsCmd__1(){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_42_ = l_Lean_Fmt_fmtAttribute;
v___x_43_ = ((lean_object*)(l_Lean_Fmt_fmtStoreTracesAsCmd___closed__3));
v___x_44_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_PostprocessTraces_StoredTraces_0__Lean_Fmt_fmtStoreTracesAsCmd___regBuiltin_Lean_Fmt_fmtStoreTracesAsCmd__1___closed__2));
v___x_45_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtStoreTracesAsCmd___boxed), 3, 0);
v___x_46_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_42_, v___x_43_, v___x_44_, v___x_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_PostprocessTraces_StoredTraces_0__Lean_Fmt_fmtStoreTracesAsCmd___regBuiltin_Lean_Fmt_fmtStoreTracesAsCmd__1___boxed(lean_object* v_a_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l___private_Lean_Fmt_Formatters_Lean_PostprocessTraces_StoredTraces_0__Lean_Fmt_fmtStoreTracesAsCmd___regBuiltin_Lean_Fmt_fmtStoreTracesAsCmd__1();
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPostprocessStoredTracesCmd(lean_object* v_x_54_, lean_object* v_a_55_, lean_object* v_a_56_){
_start:
{
lean_object* v___x_57_; uint8_t v___x_58_; 
v___x_57_ = ((lean_object*)(l_Lean_Fmt_fmtPostprocessStoredTracesCmd___closed__1));
lean_inc(v_x_54_);
v___x_58_ = l_Lean_Syntax_isOfKind(v_x_54_, v___x_57_);
if (v___x_58_ == 0)
{
lean_object* v___x_59_; lean_object* v___x_60_; 
lean_dec(v_x_54_);
v___x_59_ = l_Lean_Fmt_Error_partialFormatter;
v___x_60_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_60_, 0, v___x_59_);
lean_ctor_set(v___x_60_, 1, v_a_56_);
return v___x_60_;
}
else
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; uint8_t v___x_64_; 
v___x_61_ = lean_unsigned_to_nat(1u);
v___x_62_ = l_Lean_Syntax_getArg(v_x_54_, v___x_61_);
v___x_63_ = ((lean_object*)(l_Lean_Fmt_fmtStoreTracesAsCmd___closed__5));
lean_inc(v___x_62_);
v___x_64_ = l_Lean_Syntax_isOfKind(v___x_62_, v___x_63_);
if (v___x_64_ == 0)
{
lean_object* v___x_65_; lean_object* v___x_66_; 
lean_dec(v___x_62_);
lean_dec(v_x_54_);
v___x_65_ = l_Lean_Fmt_Error_partialFormatter;
v___x_66_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_66_, 0, v___x_65_);
lean_ctor_set(v___x_66_, 1, v_a_56_);
return v___x_66_;
}
else
{
lean_object* v___x_67_; lean_object* v_postprocessTk_68_; lean_object* v___x_69_; 
v___x_67_ = lean_unsigned_to_nat(0u);
v_postprocessTk_68_ = l_Lean_Syntax_getArg(v_x_54_, v___x_67_);
v___x_69_ = l_Lean_Fmt_fmt(v_postprocessTk_68_, v_a_55_, v_a_56_);
if (lean_obj_tag(v___x_69_) == 0)
{
lean_object* v_a_70_; lean_object* v_a_71_; lean_object* v___x_72_; 
v_a_70_ = lean_ctor_get(v___x_69_, 0);
lean_inc(v_a_70_);
v_a_71_ = lean_ctor_get(v___x_69_, 1);
lean_inc(v_a_71_);
lean_dec_ref_known(v___x_69_, 2);
v___x_72_ = l_Lean_Fmt_fmt(v___x_62_, v_a_55_, v_a_71_);
if (lean_obj_tag(v___x_72_) == 0)
{
lean_object* v_a_73_; lean_object* v_a_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v_a_73_ = lean_ctor_get(v___x_72_, 0);
lean_inc(v_a_73_);
v_a_74_ = lean_ctor_get(v___x_72_, 1);
lean_inc(v_a_74_);
lean_dec_ref_known(v___x_72_, 2);
v___x_75_ = lean_unsigned_to_nat(2u);
v___x_76_ = l_Lean_Syntax_getArg(v_x_54_, v___x_75_);
lean_dec(v_x_54_);
v___x_77_ = l_Lean_Fmt_fmt(v___x_76_, v_a_55_, v_a_74_);
if (lean_obj_tag(v___x_77_) == 0)
{
lean_object* v_a_78_; lean_object* v_a_79_; lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_94_; 
v_a_78_ = lean_ctor_get(v___x_77_, 0);
v_a_79_ = lean_ctor_get(v___x_77_, 1);
v_isSharedCheck_94_ = !lean_is_exclusive(v___x_77_);
if (v_isSharedCheck_94_ == 0)
{
v___x_81_ = v___x_77_;
v_isShared_82_ = v_isSharedCheck_94_;
goto v_resetjp_80_;
}
else
{
lean_inc(v_a_79_);
lean_inc(v_a_78_);
lean_dec(v___x_77_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_94_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; uint8_t v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_92_; 
v___x_83_ = lean_unsigned_to_nat(3u);
v___x_84_ = lean_mk_empty_array_with_capacity(v___x_83_);
v___x_85_ = lean_array_push(v___x_84_, v_a_70_);
v___x_86_ = lean_array_push(v___x_85_, v_a_73_);
v___x_87_ = lean_array_push(v___x_86_, v_a_78_);
v___x_88_ = 0;
v___x_89_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_89_, 0, v___x_64_);
lean_ctor_set_uint8(v___x_89_, 1, v___x_88_);
lean_ctor_set_uint8(v___x_89_, 2, v___x_88_);
lean_ctor_set_uint8(v___x_89_, 3, v___x_88_);
v___x_90_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_87_, v___x_89_);
if (v_isShared_82_ == 0)
{
lean_ctor_set(v___x_81_, 0, v___x_90_);
v___x_92_ = v___x_81_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v___x_90_);
lean_ctor_set(v_reuseFailAlloc_93_, 1, v_a_79_);
v___x_92_ = v_reuseFailAlloc_93_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
return v___x_92_;
}
}
}
else
{
lean_dec(v_a_73_);
lean_dec(v_a_70_);
return v___x_77_;
}
}
else
{
lean_dec(v_a_70_);
lean_dec(v_x_54_);
return v___x_72_;
}
}
else
{
lean_dec(v___x_62_);
lean_dec(v_x_54_);
return v___x_69_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPostprocessStoredTracesCmd___boxed(lean_object* v_x_95_, lean_object* v_a_96_, lean_object* v_a_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Lean_Fmt_fmtPostprocessStoredTracesCmd(v_x_95_, v_a_96_, v_a_97_);
lean_dec_ref(v_a_96_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_PostprocessTraces_StoredTraces_0__Lean_Fmt_fmtPostprocessStoredTracesCmd___regBuiltin_Lean_Fmt_fmtPostprocessStoredTracesCmd__1(){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_105_ = l_Lean_Fmt_fmtAttribute;
v___x_106_ = ((lean_object*)(l_Lean_Fmt_fmtPostprocessStoredTracesCmd___closed__1));
v___x_107_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_PostprocessTraces_StoredTraces_0__Lean_Fmt_fmtPostprocessStoredTracesCmd___regBuiltin_Lean_Fmt_fmtPostprocessStoredTracesCmd__1___closed__1));
v___x_108_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtPostprocessStoredTracesCmd___boxed), 3, 0);
v___x_109_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_105_, v___x_106_, v___x_107_, v___x_108_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_PostprocessTraces_StoredTraces_0__Lean_Fmt_fmtPostprocessStoredTracesCmd___regBuiltin_Lean_Fmt_fmtPostprocessStoredTracesCmd__1___boxed(lean_object* v_a_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l___private_Lean_Fmt_Formatters_Lean_PostprocessTraces_StoredTraces_0__Lean_Fmt_fmtPostprocessStoredTracesCmd___regBuiltin_Lean_Fmt_fmtPostprocessStoredTracesCmd__1();
return v_res_111_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Formatters_Lean_PostprocessTraces_PostprocessTracesCommand(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Lean_PostprocessTraces_StoredTraces(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Lean_PostprocessTraces_PostprocessTracesCommand(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_PostprocessTraces_StoredTraces_0__Lean_Fmt_fmtStoreTracesAsCmd___regBuiltin_Lean_Fmt_fmtStoreTracesAsCmd__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_PostprocessTraces_StoredTraces_0__Lean_Fmt_fmtPostprocessStoredTracesCmd___regBuiltin_Lean_Fmt_fmtPostprocessStoredTracesCmd__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_PostprocessTraces_StoredTraces(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Lean_PostprocessTraces_StoredTraces(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_PostprocessTraces_StoredTraces(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Formatters_Lean_PostprocessTraces_PostprocessTracesCommand(uint8_t builtin);
lean_object* initialize_Lean_PostprocessTraces_StoredTraces(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Lean_PostprocessTraces_StoredTraces(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Formatters_Lean_PostprocessTraces_PostprocessTracesCommand(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PostprocessTraces_StoredTraces(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Lean_PostprocessTraces_StoredTraces(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Lean_PostprocessTraces_StoredTraces(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Lean_PostprocessTraces_StoredTraces(builtin);
}
#ifdef __cplusplus
}
#endif

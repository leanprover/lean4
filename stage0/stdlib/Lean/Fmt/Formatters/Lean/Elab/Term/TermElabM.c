// Lean compiler output
// Module: Lean.Fmt.Formatters.Lean.Elab.Term.TermElabM
// Imports: public import Lean.Fmt.FmtM.Basic meta import Lean.Elab.Term.TermElabM import Lean.Fmt.FmtM.CommonFormatters import Init.Data
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
lean_object* l_Lean_Fmt_getStxArg_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtAppLike(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtElabToSyntax___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Fmt_fmtElabToSyntax___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtElabToSyntax___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtElabToSyntax___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Fmt_fmtElabToSyntax___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtElabToSyntax___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtElabToSyntax___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Fmt_fmtElabToSyntax___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtElabToSyntax___closed__2_value;
static const lean_string_object l_Lean_Fmt_fmtElabToSyntax___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "elabToSyntax"};
static const lean_object* l_Lean_Fmt_fmtElabToSyntax___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtElabToSyntax___closed__3_value;
static const lean_ctor_object l_Lean_Fmt_fmtElabToSyntax___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtElabToSyntax___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtElabToSyntax___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtElabToSyntax___closed__4_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtElabToSyntax___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtElabToSyntax___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtElabToSyntax___closed__4_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtElabToSyntax___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtElabToSyntax___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtElabToSyntax___closed__4_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtElabToSyntax___closed__3_value),LEAN_SCALAR_PTR_LITERAL(26, 93, 3, 79, 221, 223, 40, 77)}};
static const lean_object* l_Lean_Fmt_fmtElabToSyntax___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtElabToSyntax___closed__4_value;
static const lean_string_object l_Lean_Fmt_fmtElabToSyntax___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l_Lean_Fmt_fmtElabToSyntax___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtElabToSyntax___closed__5_value;
static const lean_ctor_object l_Lean_Fmt_fmtElabToSyntax___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtElabToSyntax___closed__5_value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
static const lean_object* l_Lean_Fmt_fmtElabToSyntax___closed__6 = (const lean_object*)&l_Lean_Fmt_fmtElabToSyntax___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtElabToSyntax(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtElabToSyntax___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Elab_Term_TermElabM_0__Lean_Fmt_fmtElabToSyntax___regBuiltin_Lean_Fmt_fmtElabToSyntax__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_Term_TermElabM_0__Lean_Fmt_fmtElabToSyntax___regBuiltin_Lean_Fmt_fmtElabToSyntax__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_Term_TermElabM_0__Lean_Fmt_fmtElabToSyntax___regBuiltin_Lean_Fmt_fmtElabToSyntax__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Elab_Term_TermElabM_0__Lean_Fmt_fmtElabToSyntax___regBuiltin_Lean_Fmt_fmtElabToSyntax__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "fmtElabToSyntax"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_Term_TermElabM_0__Lean_Fmt_fmtElabToSyntax___regBuiltin_Lean_Fmt_fmtElabToSyntax__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_Term_TermElabM_0__Lean_Fmt_fmtElabToSyntax___regBuiltin_Lean_Fmt_fmtElabToSyntax__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Elab_Term_TermElabM_0__Lean_Fmt_fmtElabToSyntax___regBuiltin_Lean_Fmt_fmtElabToSyntax__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtElabToSyntax___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Elab_Term_TermElabM_0__Lean_Fmt_fmtElabToSyntax___regBuiltin_Lean_Fmt_fmtElabToSyntax__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_Term_TermElabM_0__Lean_Fmt_fmtElabToSyntax___regBuiltin_Lean_Fmt_fmtElabToSyntax__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_Term_TermElabM_0__Lean_Fmt_fmtElabToSyntax___regBuiltin_Lean_Fmt_fmtElabToSyntax__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Elab_Term_TermElabM_0__Lean_Fmt_fmtElabToSyntax___regBuiltin_Lean_Fmt_fmtElabToSyntax__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_Term_TermElabM_0__Lean_Fmt_fmtElabToSyntax___regBuiltin_Lean_Fmt_fmtElabToSyntax__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_Term_TermElabM_0__Lean_Fmt_fmtElabToSyntax___regBuiltin_Lean_Fmt_fmtElabToSyntax__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(26, 91, 129, 41, 143, 85, 86, 181)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_Term_TermElabM_0__Lean_Fmt_fmtElabToSyntax___regBuiltin_Lean_Fmt_fmtElabToSyntax__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_Term_TermElabM_0__Lean_Fmt_fmtElabToSyntax___regBuiltin_Lean_Fmt_fmtElabToSyntax__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_Term_TermElabM_0__Lean_Fmt_fmtElabToSyntax___regBuiltin_Lean_Fmt_fmtElabToSyntax__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_Term_TermElabM_0__Lean_Fmt_fmtElabToSyntax___regBuiltin_Lean_Fmt_fmtElabToSyntax__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtElabToSyntax(lean_object* v_stx_13_, lean_object* v_a_14_, lean_object* v_a_15_){
_start:
{
lean_object* v___x_16_; uint8_t v___x_17_; 
v___x_16_ = ((lean_object*)(l_Lean_Fmt_fmtElabToSyntax___closed__4));
lean_inc(v_stx_13_);
v___x_17_ = l_Lean_Syntax_isOfKind(v_stx_13_, v___x_16_);
if (v___x_17_ == 0)
{
lean_object* v___x_18_; lean_object* v___x_19_; 
lean_dec(v_stx_13_);
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
v___x_21_ = l_Lean_Syntax_getArg(v_stx_13_, v___x_20_);
v___x_22_ = ((lean_object*)(l_Lean_Fmt_fmtElabToSyntax___closed__6));
lean_inc(v___x_21_);
v___x_23_ = l_Lean_Syntax_isOfKind(v___x_21_, v___x_22_);
if (v___x_23_ == 0)
{
lean_object* v___x_24_; lean_object* v___x_25_; 
lean_dec(v___x_21_);
lean_dec(v_stx_13_);
v___x_24_ = l_Lean_Fmt_Error_partialFormatter;
v___x_25_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_25_, 0, v___x_24_);
lean_ctor_set(v___x_25_, 1, v_a_15_);
return v___x_25_;
}
else
{
lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_26_ = lean_unsigned_to_nat(0u);
v___x_27_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_13_, v___x_26_, v_a_15_);
lean_dec(v_stx_13_);
if (lean_obj_tag(v___x_27_) == 0)
{
lean_object* v_a_28_; lean_object* v_a_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v_a_28_ = lean_ctor_get(v___x_27_, 0);
lean_inc(v_a_28_);
v_a_29_ = lean_ctor_get(v___x_27_, 1);
lean_inc(v_a_29_);
lean_dec_ref_known(v___x_27_, 2);
v___x_30_ = lean_unsigned_to_nat(2u);
v___x_31_ = lean_mk_empty_array_with_capacity(v___x_30_);
v___x_32_ = lean_array_push(v___x_31_, v_a_28_);
v___x_33_ = lean_array_push(v___x_32_, v___x_21_);
v___x_34_ = l_Lean_Fmt_fmtAppLike(v___x_33_, v_a_14_, v_a_29_);
return v___x_34_;
}
else
{
lean_object* v_a_35_; lean_object* v_a_36_; lean_object* v___x_38_; uint8_t v_isShared_39_; uint8_t v_isSharedCheck_43_; 
lean_dec(v___x_21_);
v_a_35_ = lean_ctor_get(v___x_27_, 0);
v_a_36_ = lean_ctor_get(v___x_27_, 1);
v_isSharedCheck_43_ = !lean_is_exclusive(v___x_27_);
if (v_isSharedCheck_43_ == 0)
{
v___x_38_ = v___x_27_;
v_isShared_39_ = v_isSharedCheck_43_;
goto v_resetjp_37_;
}
else
{
lean_inc(v_a_36_);
lean_inc(v_a_35_);
lean_dec(v___x_27_);
v___x_38_ = lean_box(0);
v_isShared_39_ = v_isSharedCheck_43_;
goto v_resetjp_37_;
}
v_resetjp_37_:
{
lean_object* v___x_41_; 
if (v_isShared_39_ == 0)
{
v___x_41_ = v___x_38_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_42_; 
v_reuseFailAlloc_42_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_42_, 0, v_a_35_);
lean_ctor_set(v_reuseFailAlloc_42_, 1, v_a_36_);
v___x_41_ = v_reuseFailAlloc_42_;
goto v_reusejp_40_;
}
v_reusejp_40_:
{
return v___x_41_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtElabToSyntax___boxed(lean_object* v_stx_44_, lean_object* v_a_45_, lean_object* v_a_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_Lean_Fmt_fmtElabToSyntax(v_stx_44_, v_a_45_, v_a_46_);
lean_dec_ref(v_a_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_Term_TermElabM_0__Lean_Fmt_fmtElabToSyntax___regBuiltin_Lean_Fmt_fmtElabToSyntax__1(){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_55_ = l_Lean_Fmt_fmtAttribute;
v___x_56_ = ((lean_object*)(l_Lean_Fmt_fmtElabToSyntax___closed__4));
v___x_57_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Elab_Term_TermElabM_0__Lean_Fmt_fmtElabToSyntax___regBuiltin_Lean_Fmt_fmtElabToSyntax__1___closed__2));
v___x_58_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtElabToSyntax___boxed), 3, 0);
v___x_59_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_55_, v___x_56_, v___x_57_, v___x_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_Term_TermElabM_0__Lean_Fmt_fmtElabToSyntax___regBuiltin_Lean_Fmt_fmtElabToSyntax__1___boxed(lean_object* v_a_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l___private_Lean_Fmt_Formatters_Lean_Elab_Term_TermElabM_0__Lean_Fmt_fmtElabToSyntax___regBuiltin_Lean_Fmt_fmtElabToSyntax__1();
return v_res_61_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Lean_Elab_Term_TermElabM(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Elab_Term_TermElabM_0__Lean_Fmt_fmtElabToSyntax___regBuiltin_Lean_Fmt_fmtElabToSyntax__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Elab_Term_TermElabM(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Lean_Elab_Term_TermElabM(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Elab_Term_TermElabM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Lean_Elab_Term_TermElabM(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Lean_Elab_Term_TermElabM(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Term_TermElabM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Lean_Elab_Term_TermElabM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Lean_Elab_Term_TermElabM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Lean_Elab_Term_TermElabM(builtin);
}
#ifdef __cplusplus
}
#endif

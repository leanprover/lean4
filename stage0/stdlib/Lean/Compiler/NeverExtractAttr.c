// Lean compiler output
// Module: Lean.Compiler.NeverExtractAttr
// Imports: public import Lean.Attributes
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_registerTagAttribute(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t);
uint8_t l_Lean_TagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isInternal(lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "never_extract"};
static const lean_object* l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(130, 198, 141, 201, 137, 39, 134, 37)}};
static const lean_object* l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 236, .m_capacity = 236, .m_length = 235, .m_data = "instruct the compiler that function applications using the tagged declaration should not be extracted when they are closed terms, nor common subexpression should be performed. This is useful for declarations that have implicit effects."};
static const lean_object* l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "neverExtractAttr"};
static const lean_object* l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(35, 132, 46, 132, 107, 130, 7, 53)}};
static const lean_object* l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_neverExtractAttr;
static const lean_string_object l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 511, .m_capacity = 511, .m_length = 510, .m_data = "Instructs the compiler that function applications using the tagged declaration should not be\nextracted when they are closed terms, and that common subexpression elimination should not be\nperformed.\n\nOrdinarily, the Lean compiler identifies closed terms (without free variables) and extracts them\nto top-level definitions. This optimization can prevent unnecessary recomputation of values.\n\nPreventing the extraction of closed terms is useful for declarations that have implicit effects\nthat should be repeated."};
static const lean_object* l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_docString__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(15) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(28) << 1) | 1)),((lean_object*)(((size_t)(275) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__1_value),((lean_object*)(((size_t)(275) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(27) << 1) | 1)),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(27) << 1) | 1)),((lean_object*)(((size_t)(35) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__3_value),((lean_object*)(((size_t)(19) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__4_value),((lean_object*)(((size_t)(35) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_NeverExtractAttr_0__Lean_hasNeverExtractAttribute_visit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NeverExtractAttr_0__Lean_hasNeverExtractAttribute_visit___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_hasNeverExtractAttribute(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasNeverExtractAttribute___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2_(lean_object* v_x_1_, lean_object* v___y_2_, lean_object* v___y_3_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_box(0);
v___x_6_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2____boxed(lean_object* v_x_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2_(v_x_7_, v___y_8_, v___y_9_);
lean_dec(v___y_9_);
lean_dec_ref(v___y_8_);
lean_dec(v_x_7_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; uint8_t v___x_27_; lean_object* v___x_28_; uint8_t v___x_29_; lean_object* v___x_30_; 
v___f_23_ = ((lean_object*)(l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2_));
v___x_24_ = ((lean_object*)(l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2_));
v___x_25_ = ((lean_object*)(l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2_));
v___x_26_ = ((lean_object*)(l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2_));
v___x_27_ = 0;
v___x_28_ = lean_box(2);
v___x_29_ = 0;
v___x_30_ = l_Lean_registerTagAttribute(v___x_24_, v___x_25_, v___f_23_, v___x_26_, v___x_27_, v___x_28_, v___x_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2____boxed(lean_object* v_a_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2_();
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_docString__1(){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_35_ = ((lean_object*)(l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2_));
v___x_36_ = ((lean_object*)(l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_docString__1___closed__0));
v___x_37_ = l_Lean_addBuiltinDocString(v___x_35_, v___x_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_docString__1___boxed(lean_object* v_a_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_docString__1();
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3(){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_66_ = ((lean_object*)(l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2_));
v___x_67_ = ((lean_object*)(l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__6));
v___x_68_ = l_Lean_addBuiltinDeclarationRanges(v___x_66_, v___x_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___boxed(lean_object* v_a_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3();
return v_res_70_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_NeverExtractAttr_0__Lean_hasNeverExtractAttribute_visit(lean_object* v_env_71_, lean_object* v_n_72_){
_start:
{
lean_object* v___x_73_; uint8_t v___x_74_; 
v___x_73_ = l_Lean_neverExtractAttr;
lean_inc(v_n_72_);
lean_inc_ref(v_env_71_);
v___x_74_ = l_Lean_TagAttribute_hasTag(v___x_73_, v_env_71_, v_n_72_);
if (v___x_74_ == 0)
{
uint8_t v___x_75_; 
v___x_75_ = l_Lean_Name_isInternal(v_n_72_);
if (v___x_75_ == 0)
{
lean_dec(v_n_72_);
lean_dec_ref(v_env_71_);
return v___x_75_;
}
else
{
lean_object* v___x_76_; 
v___x_76_ = l_Lean_Name_getPrefix(v_n_72_);
lean_dec(v_n_72_);
v_n_72_ = v___x_76_;
goto _start;
}
}
else
{
lean_dec(v_n_72_);
lean_dec_ref(v_env_71_);
return v___x_74_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NeverExtractAttr_0__Lean_hasNeverExtractAttribute_visit___boxed(lean_object* v_env_78_, lean_object* v_n_79_){
_start:
{
uint8_t v_res_80_; lean_object* v_r_81_; 
v_res_80_ = l___private_Lean_Compiler_NeverExtractAttr_0__Lean_hasNeverExtractAttribute_visit(v_env_78_, v_n_79_);
v_r_81_ = lean_box(v_res_80_);
return v_r_81_;
}
}
LEAN_EXPORT uint8_t l_Lean_hasNeverExtractAttribute(lean_object* v_env_82_, lean_object* v_n_83_){
_start:
{
uint8_t v___x_84_; 
v___x_84_ = l___private_Lean_Compiler_NeverExtractAttr_0__Lean_hasNeverExtractAttribute_visit(v_env_82_, v_n_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasNeverExtractAttribute___boxed(lean_object* v_env_85_, lean_object* v_n_86_){
_start:
{
uint8_t v_res_87_; lean_object* v_r_88_; 
v_res_87_ = l_Lean_hasNeverExtractAttribute(v_env_85_, v_n_86_);
v_r_88_ = lean_box(v_res_87_);
return v_r_88_;
}
}
lean_object* runtime_initialize_Lean_Attributes(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_NeverExtractAttr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Attributes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_neverExtractAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_neverExtractAttr);
lean_dec_ref(res);
res = l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_NeverExtractAttr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Attributes(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_NeverExtractAttr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Attributes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_NeverExtractAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_NeverExtractAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_NeverExtractAttr(builtin);
}
#ifdef __cplusplus
}
#endif

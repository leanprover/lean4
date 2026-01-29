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
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_initFn___closed__0_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__0_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__0_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_initFn___closed__1_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "never_extract"};
static const lean_object* l_Lean_initFn___closed__1_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2__value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_initFn___closed__2_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(130, 198, 141, 201, 137, 39, 134, 37)}};
static const lean_object* l_Lean_initFn___closed__2_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_initFn___closed__3_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 236, .m_capacity = 236, .m_length = 235, .m_data = "instruct the compiler that function applications using the tagged declaration should not be extracted when they are closed terms, nor common subexpression should be performed. This is useful for declarations that have implicit effects."};
static const lean_object* l_Lean_initFn___closed__3_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_initFn___closed__4_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_initFn___closed__4_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_initFn___closed__5_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "neverExtractAttr"};
static const lean_object* l_Lean_initFn___closed__5_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2__value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_initFn___closed__6_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_initFn___closed__6_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__6_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(35, 132, 46, 132, 107, 130, 7, 53)}};
static const lean_object* l_Lean_initFn___closed__6_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__6_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2__value;
lean_object* l_Lean_registerTagAttribute(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_neverExtractAttr;
static const lean_string_object l_Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 512, .m_capacity = 512, .m_length = 511, .m_data = "Instructs the compiler that function applications using the tagged declaration should not be\nextracted when they are closed terms, and that common subexpression elimination should not be\nperformed.\n\nOrdinarily, the Lean compiler identifies closed terms (without free variables) and extracts them\nto top-level definitions. This optimization can prevent unnecessary recomputation of values.\n\nPreventing the extraction of closed terms is useful for declarations that have implicit effects\nthat should be repeated.\n"};
static const lean_object* l_Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_docString__1___closed__0 = (const lean_object*)&l_Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_docString__1___closed__0_value;
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_docString__1();
LEAN_EXPORT lean_object* l_Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_docString__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(15) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__0 = (const lean_object*)&l_Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(28) << 1) | 1)),((lean_object*)(((size_t)(275) << 1) | 1))}};
static const lean_object* l_Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__1 = (const lean_object*)&l_Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__1_value),((lean_object*)(((size_t)(275) << 1) | 1))}};
static const lean_object* l_Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__2 = (const lean_object*)&l_Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(27) << 1) | 1)),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l_Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__3 = (const lean_object*)&l_Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(27) << 1) | 1)),((lean_object*)(((size_t)(35) << 1) | 1))}};
static const lean_object* l_Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__4 = (const lean_object*)&l_Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__3_value),((lean_object*)(((size_t)(19) << 1) | 1)),((lean_object*)&l_Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__4_value),((lean_object*)(((size_t)(35) << 1) | 1))}};
static const lean_object* l_Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__5 = (const lean_object*)&l_Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__2_value),((lean_object*)&l_Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__6 = (const lean_object*)&l_Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__6_value;
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3();
LEAN_EXPORT lean_object* l_Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___boxed(lean_object*);
uint8_t l_Lean_TagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isInternal(lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_NeverExtractAttr_0__Lean_hasNeverExtractAttribute_visit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NeverExtractAttr_0__Lean_hasNeverExtractAttribute_visit___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_hasNeverExtractAttribute(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasNeverExtractAttribute___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_initFn___lam__0_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2_(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_2 = ((lean_object*)(l_Lean_initFn___closed__0_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2_));
x_3 = ((lean_object*)(l_Lean_initFn___closed__2_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2_));
x_4 = ((lean_object*)(l_Lean_initFn___closed__3_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2_));
x_5 = ((lean_object*)(l_Lean_initFn___closed__6_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2_));
x_6 = 0;
x_7 = lean_box(2);
x_8 = l_Lean_registerTagAttribute(x_3, x_4, x_2, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_initFn_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_docString__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_initFn___closed__6_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2_));
x_3 = ((lean_object*)(l_Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_docString__1___closed__0));
x_4 = l_Lean_addBuiltinDocString(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_docString__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_docString__1();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_initFn___closed__6_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2_));
x_3 = ((lean_object*)(l_Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__6));
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3();
return x_2;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_NeverExtractAttr_0__Lean_hasNeverExtractAttribute_visit(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_neverExtractAttr;
lean_inc(x_2);
lean_inc_ref(x_1);
x_4 = l_Lean_TagAttribute_hasTag(x_3, x_1, x_2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = l_Lean_Name_isInternal(x_2);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = l_Lean_Name_getPrefix(x_2);
lean_dec(x_2);
x_2 = x_6;
goto _start;
}
}
else
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NeverExtractAttr_0__Lean_hasNeverExtractAttribute_visit___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Compiler_NeverExtractAttr_0__Lean_hasNeverExtractAttribute_visit(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_hasNeverExtractAttribute(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l___private_Lean_Compiler_NeverExtractAttr_0__Lean_hasNeverExtractAttribute_visit(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_hasNeverExtractAttribute___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_hasNeverExtractAttribute(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
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
if (builtin) {res = l_Lean_initFn_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_neverExtractAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_neverExtractAttr);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

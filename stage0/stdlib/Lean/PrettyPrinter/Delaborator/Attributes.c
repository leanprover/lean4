// Lean compiler output
// Module: Lean.PrettyPrinter.Delaborator.Attributes
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_registerTagAttribute(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
uint8_t l_Lean_TagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "pp_using_anonymous_constructor"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(213, 114, 53, 108, 191, 43, 40, 133)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 65, .m_capacity = 65, .m_length = 60, .m_data = "mark structure to be pretty printed using `⟨a,b,c⟩` notation"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "ppUsingAnonymousConstructorAttr"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 230, 29, 22, 13, 233, 121, 50)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppUsingAnonymousConstructorAttr;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 100, .m_capacity = 100, .m_length = 95, .m_data = "Marks a structure to be pretty printed using the anonymous constructor notation (`⟨a, b, c⟩`). "};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_docString__1___closed__0 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_docString__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(21) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(24) << 1) | 1)),((lean_object*)(((size_t)(117) << 1) | 1))}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3___closed__1_value),((lean_object*)(((size_t)(117) << 1) | 1))}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(23) << 1) | 1)),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(23) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1))}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3___closed__3_value),((lean_object*)(((size_t)(19) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3___closed__4_value),((lean_object*)(((size_t)(50) << 1) | 1))}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3___boxed(lean_object*);
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_2550701167____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "pp_nodot"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_2550701167____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_2550701167____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_2550701167____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_2550701167____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 90, 199, 107, 39, 207, 101, 130)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_2550701167____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_2550701167____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_2550701167____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 65, .m_capacity = 65, .m_length = 64, .m_data = "mark declaration to never be pretty printed using field notation"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_2550701167____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_2550701167____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_2550701167____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "ppNoDotAttr"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_2550701167____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_2550701167____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_2550701167____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_2550701167____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_2550701167____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_2550701167____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(74, 193, 67, 126, 185, 16, 90, 202)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_2550701167____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_2550701167____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_2550701167____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_2550701167____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppNoDotAttr;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 70, .m_capacity = 70, .m_length = 69, .m_data = "Marks a declaration to never be pretty printed using field notation. "};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_docString__1___closed__0 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_docString__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(26) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(29) << 1) | 1)),((lean_object*)(((size_t)(99) << 1) | 1))}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3___closed__1_value),((lean_object*)(((size_t)(99) << 1) | 1))}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(28) << 1) | 1)),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(28) << 1) | 1)),((lean_object*)(((size_t)(30) << 1) | 1))}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3___closed__3_value),((lean_object*)(((size_t)(19) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3___closed__4_value),((lean_object*)(((size_t)(30) << 1) | 1))}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_hasPPUsingAnonymousConstructorAttribute(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasPPUsingAnonymousConstructorAttribute___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_hasPPNoDotAttribute(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasPPNoDotAttribute___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2_(lean_object* v_x_1_, lean_object* v___y_2_, lean_object* v___y_3_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_box(0);
v___x_6_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2____boxed(lean_object* v_x_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2_(v_x_7_, v___y_8_, v___y_9_);
lean_dec(v___y_9_);
lean_dec_ref(v___y_8_);
lean_dec(v_x_7_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; uint8_t v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v___f_23_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2_));
v___x_24_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2_));
v___x_25_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2_));
v___x_26_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2_));
v___x_27_ = 0;
v___x_28_ = lean_box(2);
v___x_29_ = l_Lean_registerTagAttribute(v___x_24_, v___x_25_, v___f_23_, v___x_26_, v___x_27_, v___x_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2____boxed(lean_object* v_a_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2_();
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_docString__1(){
_start:
{
lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_34_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2_));
v___x_35_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_docString__1___closed__0));
v___x_36_ = l_Lean_addBuiltinDocString(v___x_34_, v___x_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_docString__1___boxed(lean_object* v_a_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_docString__1();
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3(){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_65_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2_));
v___x_66_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3___closed__6));
v___x_67_ = l_Lean_addBuiltinDeclarationRanges(v___x_65_, v___x_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3___boxed(lean_object* v_a_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3();
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_2550701167____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; uint8_t v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v___f_79_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2_));
v___x_80_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_2550701167____hygCtx___hyg_2_));
v___x_81_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_2550701167____hygCtx___hyg_2_));
v___x_82_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_2550701167____hygCtx___hyg_2_));
v___x_83_ = 0;
v___x_84_ = lean_box(2);
v___x_85_ = l_Lean_registerTagAttribute(v___x_80_, v___x_81_, v___f_79_, v___x_82_, v___x_83_, v___x_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_2550701167____hygCtx___hyg_2____boxed(lean_object* v_a_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_2550701167____hygCtx___hyg_2_();
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_docString__1(){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_90_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_2550701167____hygCtx___hyg_2_));
v___x_91_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_docString__1___closed__0));
v___x_92_ = l_Lean_addBuiltinDocString(v___x_90_, v___x_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_docString__1___boxed(lean_object* v_a_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_docString__1();
return v_res_94_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3(){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_121_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_2550701167____hygCtx___hyg_2_));
v___x_122_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3___closed__6));
v___x_123_ = l_Lean_addBuiltinDeclarationRanges(v___x_121_, v___x_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3___boxed(lean_object* v_a_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3();
return v_res_125_;
}
}
LEAN_EXPORT uint8_t l_Lean_hasPPUsingAnonymousConstructorAttribute(lean_object* v_env_126_, lean_object* v_declName_127_){
_start:
{
lean_object* v___x_128_; uint8_t v___x_129_; 
v___x_128_ = l_Lean_ppUsingAnonymousConstructorAttr;
v___x_129_ = l_Lean_TagAttribute_hasTag(v___x_128_, v_env_126_, v_declName_127_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasPPUsingAnonymousConstructorAttribute___boxed(lean_object* v_env_130_, lean_object* v_declName_131_){
_start:
{
uint8_t v_res_132_; lean_object* v_r_133_; 
v_res_132_ = l_Lean_hasPPUsingAnonymousConstructorAttribute(v_env_130_, v_declName_131_);
v_r_133_ = lean_box(v_res_132_);
return v_r_133_;
}
}
LEAN_EXPORT uint8_t l_Lean_hasPPNoDotAttribute(lean_object* v_env_134_, lean_object* v_declName_135_){
_start:
{
lean_object* v___x_136_; uint8_t v___x_137_; 
v___x_136_ = l_Lean_ppNoDotAttr;
v___x_137_ = l_Lean_TagAttribute_hasTag(v___x_136_, v_env_134_, v_declName_135_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasPPNoDotAttribute___boxed(lean_object* v_env_138_, lean_object* v_declName_139_){
_start:
{
uint8_t v_res_140_; lean_object* v_r_141_; 
v_res_140_ = l_Lean_hasPPNoDotAttribute(v_env_138_, v_declName_139_);
v_r_141_ = lean_box(v_res_140_);
return v_r_141_;
}
}
lean_object* runtime_initialize_Lean_Attributes(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_PrettyPrinter_Delaborator_Attributes(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Attributes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_ppUsingAnonymousConstructorAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_ppUsingAnonymousConstructorAttr);
lean_dec_ref(res);
res = l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_2550701167____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_ppNoDotAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_ppNoDotAttr);
lean_dec_ref(res);
res = l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_PrettyPrinter_Delaborator_Attributes(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Attributes(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_PrettyPrinter_Delaborator_Attributes(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Attributes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_PrettyPrinter_Delaborator_Attributes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_PrettyPrinter_Delaborator_Attributes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_PrettyPrinter_Delaborator_Attributes(builtin);
}
#ifdef __cplusplus
}
#endif

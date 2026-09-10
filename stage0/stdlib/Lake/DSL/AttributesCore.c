// Lean compiler output
// Module: Lake.DSL.AttributesCore
// Imports: public import Lake.Util.OrderedTagAttribute
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
lean_object* l_Lake_registerOrderedTagAttribute(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_OrderedTagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "package"};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(79, 155, 211, 46, 225, 213, 150, 92)}};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "mark a definition as a Lake package configuration"};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lake"};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "packageAttr"};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__6_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__6_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__6_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(246, 216, 234, 151, 184, 29, 39, 9)}};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__6_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__6_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_packageAttr;
static const lean_string_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "package_dep"};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(237, 25, 56, 91, 184, 179, 188, 66)}};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "mark a definition as a Lake package dependency"};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "packageDepAttr"};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(45, 68, 99, 181, 205, 9, 187, 35)}};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_packageDepAttr;
static const lean_string_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "post_update"};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(27, 22, 136, 29, 51, 248, 173, 13)}};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "mark a definition as a Lake package post-update hook"};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "postUpdateAttr"};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(85, 79, 83, 54, 241, 232, 152, 172)}};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_postUpdateAttr;
static const lean_string_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "script"};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(148, 36, 101, 0, 21, 164, 81, 12)}};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "mark a definition as a Lake script"};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "scriptAttr"};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(26, 29, 82, 124, 109, 105, 242, 204)}};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_scriptAttr;
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__2___closed__0_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "attribute `default_script` can only be used on a `script`"};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__2___closed__0_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__2___closed__0_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__2___closed__1_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__2___closed__1_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__2_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__2_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__2_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "default_script"};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(231, 79, 159, 251, 35, 92, 4, 228)}};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "mark a Lake script as the package's default"};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "defaultScriptAttr"};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__6_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__6_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__6_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(102, 220, 227, 87, 142, 243, 134, 10)}};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__6_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__6_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_defaultScriptAttr;
static const lean_string_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "lean_lib"};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(99, 123, 8, 14, 20, 41, 164, 170)}};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "mark a definition as a Lake Lean library target configuration"};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "leanLibAttr"};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(32, 216, 106, 32, 231, 39, 130, 108)}};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_leanLibAttr;
static const lean_string_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "lean_exe"};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(195, 234, 10, 11, 117, 216, 237, 146)}};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 65, .m_capacity = 65, .m_length = 64, .m_data = "mark a definition as a Lake Lean executable target configuration"};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "leanExeAttr"};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(188, 182, 7, 15, 47, 104, 138, 158)}};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_leanExeAttr;
static const lean_string_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "extern_lib"};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(160, 249, 245, 64, 44, 199, 117, 160)}};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "mark a definition as a Lake external library target"};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "externLibAttr"};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(101, 0, 33, 72, 82, 211, 54, 104)}};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_externLibAttr;
static const lean_string_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "input_file"};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(242, 212, 171, 164, 114, 171, 114, 56)}};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "mark a definition as a Lake input file target"};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "inputFileAttr"};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(205, 143, 246, 45, 132, 126, 54, 248)}};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputFileAttr;
static const lean_string_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "input_dir"};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(120, 20, 59, 254, 237, 234, 192, 134)}};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "mark a definition as a Lake input directory target"};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "inputDirAttr"};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(122, 207, 180, 131, 169, 221, 185, 167)}};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputDirAttr;
static const lean_string_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "target"};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(251, 222, 62, 78, 55, 94, 255, 84)}};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "mark a definition as a Lake target"};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "targetAttr"};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(230, 170, 78, 40, 161, 217, 169, 127)}};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_targetAttr;
LEAN_EXPORT uint8_t l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__0_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 87, .m_capacity = 87, .m_length = 86, .m_data = "attribute `default_target` can only be used on a target (e.g., `lean_lib`, `lean_exe`)"};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__0_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__0_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "default_target"};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(14, 139, 51, 125, 166, 104, 251, 179)}};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "mark a Lake target as the package's default"};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "defaultTargetAttr"};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(136, 50, 195, 92, 10, 179, 138, 115)}};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_defaultTargetAttr;
LEAN_EXPORT uint8_t l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__0_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 82, .m_capacity = 82, .m_length = 81, .m_data = "attribute `test_driver` can only be used on a `script`, `lean_exe`, or `lean_lib`"};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__0_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__0_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "test_driver"};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(211, 1, 67, 247, 67, 232, 139, 37)}};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "mark a Lake script, executable, or library as package's test driver"};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "testDriverAttr"};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(145, 171, 145, 31, 167, 29, 89, 20)}};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_testDriverAttr;
LEAN_EXPORT uint8_t l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__0_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "attribute `lint_driver` can only be used on a `script` or `lean_exe`"};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__0_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__0_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "lint_driver"};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(34, 189, 146, 88, 215, 167, 107, 153)}};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "mark a Lake script or executable as package's linter"};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "lintDriverAttr"};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(162, 200, 112, 121, 111, 252, 78, 167)}};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_lintDriverAttr;
static const lean_string_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "module_facet"};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(25, 251, 211, 5, 220, 66, 32, 131)}};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "mark a definition as a Lake module facet"};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "moduleFacetAttr"};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(184, 177, 55, 179, 152, 236, 7, 155)}};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_moduleFacetAttr;
static const lean_string_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "package_facet"};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(162, 6, 0, 83, 202, 204, 40, 130)}};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "mark a definition as a Lake package facet"};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "packageFacetAttr"};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(30, 214, 121, 146, 170, 223, 202, 251)}};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_packageFacetAttr;
static const lean_string_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "library_facet"};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(110, 231, 35, 150, 227, 95, 59, 240)}};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "mark a definition as a Lake library facet"};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "libraryFacetAttr"};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(68, 159, 200, 109, 254, 124, 216, 54)}};
static const lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_libraryFacetAttr;
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_(lean_object* v_x_1_, lean_object* v___y_2_, lean_object* v___y_3_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_box(0);
v___x_6_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2____boxed(lean_object* v_x_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_(v_x_7_, v___y_8_, v___y_9_);
lean_dec(v___y_9_);
lean_dec_ref(v___y_8_);
lean_dec(v_x_7_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; 
v___f_23_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_));
v___x_24_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_));
v___x_25_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_));
v___x_26_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__6_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_));
v___x_27_ = l_Lake_registerOrderedTagAttribute(v___x_24_, v___x_25_, v___f_23_, v___x_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2____boxed(lean_object* v_a_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_();
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v___f_39_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_));
v___x_40_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2_));
v___x_41_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2_));
v___x_42_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2_));
v___x_43_ = l_Lake_registerOrderedTagAttribute(v___x_40_, v___x_41_, v___f_39_, v___x_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2____boxed(lean_object* v_a_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2_();
return v_res_45_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___f_55_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_));
v___x_56_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2_));
v___x_57_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2_));
v___x_58_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2_));
v___x_59_ = l_Lake_registerOrderedTagAttribute(v___x_56_, v___x_57_, v___f_55_, v___x_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2____boxed(lean_object* v_a_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2_();
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___f_71_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_));
v___x_72_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2_));
v___x_73_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2_));
v___x_74_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2_));
v___x_75_ = l_Lake_registerOrderedTagAttribute(v___x_72_, v___x_73_, v___f_71_, v___x_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2____boxed(lean_object* v_a_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2_();
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__0___redArg(lean_object* v_a_78_, lean_object* v_f_79_, lean_object* v___y_80_, lean_object* v___y_81_){
_start:
{
lean_object* v___x_83_; 
lean_inc(v___y_81_);
lean_inc_ref(v___y_80_);
v___x_83_ = lean_apply_3(v_a_78_, v___y_80_, v___y_81_, lean_box(0));
if (lean_obj_tag(v___x_83_) == 0)
{
lean_object* v_a_84_; lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_92_; 
v_a_84_ = lean_ctor_get(v___x_83_, 0);
v_isSharedCheck_92_ = !lean_is_exclusive(v___x_83_);
if (v_isSharedCheck_92_ == 0)
{
v___x_86_ = v___x_83_;
v_isShared_87_ = v_isSharedCheck_92_;
goto v_resetjp_85_;
}
else
{
lean_inc(v_a_84_);
lean_dec(v___x_83_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_92_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
lean_object* v___x_88_; lean_object* v___x_90_; 
v___x_88_ = lean_apply_1(v_f_79_, v_a_84_);
if (v_isShared_87_ == 0)
{
lean_ctor_set(v___x_86_, 0, v___x_88_);
v___x_90_ = v___x_86_;
goto v_reusejp_89_;
}
else
{
lean_object* v_reuseFailAlloc_91_; 
v_reuseFailAlloc_91_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_91_, 0, v___x_88_);
v___x_90_ = v_reuseFailAlloc_91_;
goto v_reusejp_89_;
}
v_reusejp_89_:
{
return v___x_90_;
}
}
}
else
{
lean_object* v_a_93_; lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_100_; 
lean_dec(v_f_79_);
v_a_93_ = lean_ctor_get(v___x_83_, 0);
v_isSharedCheck_100_ = !lean_is_exclusive(v___x_83_);
if (v_isSharedCheck_100_ == 0)
{
v___x_95_ = v___x_83_;
v_isShared_96_ = v_isSharedCheck_100_;
goto v_resetjp_94_;
}
else
{
lean_inc(v_a_93_);
lean_dec(v___x_83_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_100_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
lean_object* v___x_98_; 
if (v_isShared_96_ == 0)
{
v___x_98_ = v___x_95_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v_a_93_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_a_101_, lean_object* v_f_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_Functor_mapRev___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__0___redArg(v_a_101_, v_f_102_, v___y_103_, v___y_104_);
lean_dec(v___y_104_);
lean_dec_ref(v___y_103_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_107_, lean_object* v_00_u03b2_108_, lean_object* v_a_109_, lean_object* v_f_110_, lean_object* v___y_111_, lean_object* v___y_112_){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = l_Functor_mapRev___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__0___redArg(v_a_109_, v_f_110_, v___y_111_, v___y_112_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_115_, lean_object* v_00_u03b2_116_, lean_object* v_a_117_, lean_object* v_f_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l_Functor_mapRev___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__0(v_00_u03b1_115_, v_00_u03b2_116_, v_a_117_, v_f_118_, v___y_119_, v___y_120_);
lean_dec(v___y_120_);
lean_dec_ref(v___y_119_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_(lean_object* v___y_123_, lean_object* v___y_124_){
_start:
{
lean_object* v___x_126_; lean_object* v_env_127_; lean_object* v___x_128_; 
v___x_126_ = lean_st_ref_get(v___y_124_);
v_env_127_ = lean_ctor_get(v___x_126_, 0);
lean_inc_ref(v_env_127_);
lean_dec(v___x_126_);
v___x_128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_128_, 0, v_env_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2____boxed(lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_(v___y_129_, v___y_130_);
lean_dec(v___y_130_);
lean_dec_ref(v___y_129_);
return v_res_132_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_(lean_object* v_name_133_, lean_object* v_x_134_){
_start:
{
lean_object* v___x_135_; uint8_t v___x_136_; 
v___x_135_ = l_Lake_scriptAttr;
v___x_136_ = l_Lake_OrderedTagAttribute_hasTag(v___x_135_, v_x_134_, v_name_133_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2____boxed(lean_object* v_name_137_, lean_object* v_x_138_){
_start:
{
uint8_t v_res_139_; lean_object* v_r_140_; 
v_res_139_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_(v_name_137_, v_x_138_);
lean_dec(v_name_137_);
v_r_140_ = lean_box(v_res_139_);
return v_r_140_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__0(void){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_141_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__1(void){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_142_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__0);
v___x_143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_143_, 0, v___x_142_);
return v___x_143_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__2(void){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_144_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__1);
v___x_145_ = lean_unsigned_to_nat(0u);
v___x_146_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_146_, 0, v___x_145_);
lean_ctor_set(v___x_146_, 1, v___x_145_);
lean_ctor_set(v___x_146_, 2, v___x_145_);
lean_ctor_set(v___x_146_, 3, v___x_145_);
lean_ctor_set(v___x_146_, 4, v___x_144_);
lean_ctor_set(v___x_146_, 5, v___x_144_);
lean_ctor_set(v___x_146_, 6, v___x_144_);
lean_ctor_set(v___x_146_, 7, v___x_144_);
lean_ctor_set(v___x_146_, 8, v___x_144_);
lean_ctor_set(v___x_146_, 9, v___x_144_);
lean_ctor_set(v___x_146_, 10, v___x_144_);
return v___x_146_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__3(void){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_147_ = lean_unsigned_to_nat(32u);
v___x_148_ = lean_mk_empty_array_with_capacity(v___x_147_);
v___x_149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_149_, 0, v___x_148_);
return v___x_149_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__4(void){
_start:
{
size_t v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_150_ = ((size_t)5ULL);
v___x_151_ = lean_unsigned_to_nat(0u);
v___x_152_ = lean_unsigned_to_nat(32u);
v___x_153_ = lean_mk_empty_array_with_capacity(v___x_152_);
v___x_154_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__3);
v___x_155_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_155_, 0, v___x_154_);
lean_ctor_set(v___x_155_, 1, v___x_153_);
lean_ctor_set(v___x_155_, 2, v___x_151_);
lean_ctor_set(v___x_155_, 3, v___x_151_);
lean_ctor_set_usize(v___x_155_, 4, v___x_150_);
return v___x_155_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__5(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_156_ = lean_box(1);
v___x_157_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__4);
v___x_158_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__1);
v___x_159_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_159_, 0, v___x_158_);
lean_ctor_set(v___x_159_, 1, v___x_157_);
lean_ctor_set(v___x_159_, 2, v___x_156_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1(lean_object* v_msgData_160_, lean_object* v___y_161_, lean_object* v___y_162_){
_start:
{
lean_object* v___x_164_; lean_object* v_toCold_165_; lean_object* v_env_166_; lean_object* v_options_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_164_ = lean_st_ref_get(v___y_162_);
v_toCold_165_ = lean_ctor_get(v___y_161_, 0);
v_env_166_ = lean_ctor_get(v___x_164_, 0);
lean_inc_ref(v_env_166_);
lean_dec(v___x_164_);
v_options_167_ = lean_ctor_get(v_toCold_165_, 2);
v___x_168_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__2);
v___x_169_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__5);
lean_inc_ref(v_options_167_);
v___x_170_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_170_, 0, v_env_166_);
lean_ctor_set(v___x_170_, 1, v___x_168_);
lean_ctor_set(v___x_170_, 2, v___x_169_);
lean_ctor_set(v___x_170_, 3, v_options_167_);
v___x_171_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
lean_ctor_set(v___x_171_, 1, v_msgData_160_);
v___x_172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_172_, 0, v___x_171_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object* v_msgData_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1(v_msgData_173_, v___y_174_, v___y_175_);
lean_dec(v___y_175_);
lean_dec_ref(v___y_174_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1___redArg(lean_object* v_msg_178_, lean_object* v___y_179_, lean_object* v___y_180_){
_start:
{
lean_object* v_ref_182_; lean_object* v___x_183_; lean_object* v_a_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_192_; 
v_ref_182_ = lean_ctor_get(v___y_179_, 2);
v___x_183_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1(v_msg_178_, v___y_179_, v___y_180_);
v_a_184_ = lean_ctor_get(v___x_183_, 0);
v_isSharedCheck_192_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_192_ == 0)
{
v___x_186_ = v___x_183_;
v_isShared_187_ = v_isSharedCheck_192_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_a_184_);
lean_dec(v___x_183_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_192_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___x_188_; lean_object* v___x_190_; 
lean_inc(v_ref_182_);
v___x_188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_188_, 0, v_ref_182_);
lean_ctor_set(v___x_188_, 1, v_a_184_);
if (v_isShared_187_ == 0)
{
lean_ctor_set_tag(v___x_186_, 1);
lean_ctor_set(v___x_186_, 0, v___x_188_);
v___x_190_ = v___x_186_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v___x_188_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_msg_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1___redArg(v_msg_193_, v___y_194_, v___y_195_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
return v_res_197_;
}
}
static lean_object* _init_l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__2___closed__1_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_199_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__2___closed__0_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_));
v___x_200_ = l_Lean_stringToMessageData(v___x_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__2_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_(lean_object* v___f_201_, lean_object* v_name_202_, lean_object* v___y_203_, lean_object* v___y_204_){
_start:
{
lean_object* v___f_206_; lean_object* v___x_207_; 
v___f_206_ = lean_alloc_closure((void*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_206_, 0, v_name_202_);
v___x_207_ = l_Functor_mapRev___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__0___redArg(v___f_201_, v___f_206_, v___y_203_, v___y_204_);
if (lean_obj_tag(v___x_207_) == 0)
{
lean_object* v_a_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_219_; 
v_a_208_ = lean_ctor_get(v___x_207_, 0);
v_isSharedCheck_219_ = !lean_is_exclusive(v___x_207_);
if (v_isSharedCheck_219_ == 0)
{
v___x_210_ = v___x_207_;
v_isShared_211_ = v_isSharedCheck_219_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_a_208_);
lean_dec(v___x_207_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_219_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
uint8_t v___x_212_; 
v___x_212_ = lean_unbox(v_a_208_);
lean_dec(v_a_208_);
if (v___x_212_ == 0)
{
lean_object* v___x_213_; lean_object* v___x_214_; 
lean_del_object(v___x_210_);
v___x_213_ = lean_obj_once(&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__2___closed__1_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_, &l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__2___closed__1_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__once, _init_l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__2___closed__1_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_);
v___x_214_ = l_Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1___redArg(v___x_213_, v___y_203_, v___y_204_);
return v___x_214_;
}
else
{
lean_object* v___x_215_; lean_object* v___x_217_; 
v___x_215_ = lean_box(0);
if (v_isShared_211_ == 0)
{
lean_ctor_set(v___x_210_, 0, v___x_215_);
v___x_217_ = v___x_210_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v___x_215_);
v___x_217_ = v_reuseFailAlloc_218_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
return v___x_217_;
}
}
}
}
else
{
lean_object* v_a_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_227_; 
v_a_220_ = lean_ctor_get(v___x_207_, 0);
v_isSharedCheck_227_ = !lean_is_exclusive(v___x_207_);
if (v_isSharedCheck_227_ == 0)
{
v___x_222_ = v___x_207_;
v_isShared_223_ = v_isSharedCheck_227_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_a_220_);
lean_dec(v___x_207_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_227_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v___x_225_; 
if (v_isShared_223_ == 0)
{
v___x_225_ = v___x_222_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v_a_220_);
v___x_225_ = v_reuseFailAlloc_226_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
return v___x_225_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__2_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2____boxed(lean_object* v___f_228_, lean_object* v_name_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__2_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_(v___f_228_, v_name_229_, v___y_230_, v___y_231_);
lean_dec(v___y_231_);
lean_dec_ref(v___y_230_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v___f_246_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_));
v___x_247_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_));
v___x_248_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_));
v___x_249_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__6_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_));
v___x_250_ = l_Lake_registerOrderedTagAttribute(v___x_247_, v___x_248_, v___f_246_, v___x_249_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2____boxed(lean_object* v_a_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_();
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b1_253_, lean_object* v_msg_254_, lean_object* v___y_255_, lean_object* v___y_256_){
_start:
{
lean_object* v___x_258_; 
v___x_258_ = l_Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1___redArg(v_msg_254_, v___y_255_, v___y_256_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1___boxed(lean_object* v_00_u03b1_259_, lean_object* v_msg_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1(v_00_u03b1_259_, v_msg_260_, v___y_261_, v___y_262_);
lean_dec(v___y_262_);
lean_dec_ref(v___y_261_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___f_274_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_));
v___x_275_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2_));
v___x_276_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2_));
v___x_277_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2_));
v___x_278_ = l_Lake_registerOrderedTagAttribute(v___x_275_, v___x_276_, v___f_274_, v___x_277_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2____boxed(lean_object* v_a_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2_();
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___f_290_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_));
v___x_291_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2_));
v___x_292_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2_));
v___x_293_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2_));
v___x_294_ = l_Lake_registerOrderedTagAttribute(v___x_291_, v___x_292_, v___f_290_, v___x_293_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2____boxed(lean_object* v_a_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2_();
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___f_306_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_));
v___x_307_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2_));
v___x_308_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2_));
v___x_309_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2_));
v___x_310_ = l_Lake_registerOrderedTagAttribute(v___x_307_, v___x_308_, v___f_306_, v___x_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2____boxed(lean_object* v_a_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2_();
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v___f_322_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_));
v___x_323_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2_));
v___x_324_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2_));
v___x_325_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2_));
v___x_326_ = l_Lake_registerOrderedTagAttribute(v___x_323_, v___x_324_, v___f_322_, v___x_325_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2____boxed(lean_object* v_a_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2_();
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v___f_338_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_));
v___x_339_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2_));
v___x_340_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2_));
v___x_341_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2_));
v___x_342_ = l_Lake_registerOrderedTagAttribute(v___x_339_, v___x_340_, v___f_338_, v___x_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2____boxed(lean_object* v_a_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2_();
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v___f_354_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_));
v___x_355_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2_));
v___x_356_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2_));
v___x_357_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2_));
v___x_358_ = l_Lake_registerOrderedTagAttribute(v___x_355_, v___x_356_, v___f_354_, v___x_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2____boxed(lean_object* v_a_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2_();
return v_res_360_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_(lean_object* v_name_361_, lean_object* v_env_362_){
_start:
{
lean_object* v___x_363_; uint8_t v___x_364_; 
v___x_363_ = l_Lake_targetAttr;
v___x_364_ = l_Lake_OrderedTagAttribute_hasTag(v___x_363_, v_env_362_, v_name_361_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2____boxed(lean_object* v_name_365_, lean_object* v_env_366_){
_start:
{
uint8_t v_res_367_; lean_object* v_r_368_; 
v_res_367_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_(v_name_365_, v_env_366_);
lean_dec(v_name_365_);
v_r_368_ = lean_box(v_res_367_);
return v_r_368_;
}
}
static lean_object* _init_l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__0_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_));
v___x_371_ = l_Lean_stringToMessageData(v___x_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_(lean_object* v___f_372_, lean_object* v_name_373_, lean_object* v___y_374_, lean_object* v___y_375_){
_start:
{
lean_object* v___f_377_; lean_object* v___x_378_; 
v___f_377_ = lean_alloc_closure((void*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_377_, 0, v_name_373_);
v___x_378_ = l_Functor_mapRev___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__0___redArg(v___f_372_, v___f_377_, v___y_374_, v___y_375_);
if (lean_obj_tag(v___x_378_) == 0)
{
lean_object* v_a_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_390_; 
v_a_379_ = lean_ctor_get(v___x_378_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_378_);
if (v_isSharedCheck_390_ == 0)
{
v___x_381_ = v___x_378_;
v_isShared_382_ = v_isSharedCheck_390_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_a_379_);
lean_dec(v___x_378_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_390_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
uint8_t v___x_383_; 
v___x_383_ = lean_unbox(v_a_379_);
lean_dec(v_a_379_);
if (v___x_383_ == 0)
{
lean_object* v___x_384_; lean_object* v___x_385_; 
lean_del_object(v___x_381_);
v___x_384_ = lean_obj_once(&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_, &l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2__once, _init_l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_);
v___x_385_ = l_Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1___redArg(v___x_384_, v___y_374_, v___y_375_);
return v___x_385_;
}
else
{
lean_object* v___x_386_; lean_object* v___x_388_; 
v___x_386_ = lean_box(0);
if (v_isShared_382_ == 0)
{
lean_ctor_set(v___x_381_, 0, v___x_386_);
v___x_388_ = v___x_381_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v___x_386_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
}
else
{
lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_398_; 
v_a_391_ = lean_ctor_get(v___x_378_, 0);
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_378_);
if (v_isSharedCheck_398_ == 0)
{
v___x_393_ = v___x_378_;
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_dec(v___x_378_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_396_; 
if (v_isShared_394_ == 0)
{
v___x_396_ = v___x_393_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_a_391_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2____boxed(lean_object* v___f_399_, lean_object* v_name_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_(v___f_399_, v_name_400_, v___y_401_, v___y_402_);
lean_dec(v___y_402_);
lean_dec_ref(v___y_401_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v___f_416_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_));
v___x_417_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_));
v___x_418_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_));
v___x_419_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_));
v___x_420_ = l_Lake_registerOrderedTagAttribute(v___x_417_, v___x_418_, v___f_416_, v___x_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2____boxed(lean_object* v_a_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_();
return v_res_422_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_(lean_object* v_name_423_, lean_object* v_env_424_){
_start:
{
uint8_t v___y_426_; lean_object* v___x_429_; uint8_t v___x_430_; 
v___x_429_ = l_Lake_scriptAttr;
lean_inc_ref(v_env_424_);
v___x_430_ = l_Lake_OrderedTagAttribute_hasTag(v___x_429_, v_env_424_, v_name_423_);
if (v___x_430_ == 0)
{
lean_object* v___x_431_; uint8_t v___x_432_; 
v___x_431_ = l_Lake_leanExeAttr;
lean_inc_ref(v_env_424_);
v___x_432_ = l_Lake_OrderedTagAttribute_hasTag(v___x_431_, v_env_424_, v_name_423_);
v___y_426_ = v___x_432_;
goto v___jp_425_;
}
else
{
v___y_426_ = v___x_430_;
goto v___jp_425_;
}
v___jp_425_:
{
if (v___y_426_ == 0)
{
lean_object* v___x_427_; uint8_t v___x_428_; 
v___x_427_ = l_Lake_leanLibAttr;
v___x_428_ = l_Lake_OrderedTagAttribute_hasTag(v___x_427_, v_env_424_, v_name_423_);
return v___x_428_;
}
else
{
lean_dec_ref(v_env_424_);
return v___y_426_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2____boxed(lean_object* v_name_433_, lean_object* v_env_434_){
_start:
{
uint8_t v_res_435_; lean_object* v_r_436_; 
v_res_435_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_(v_name_433_, v_env_434_);
lean_dec(v_name_433_);
v_r_436_ = lean_box(v_res_435_);
return v_r_436_;
}
}
static lean_object* _init_l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_438_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__0_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_));
v___x_439_ = l_Lean_stringToMessageData(v___x_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_(lean_object* v___f_440_, lean_object* v_name_441_, lean_object* v___y_442_, lean_object* v___y_443_){
_start:
{
lean_object* v___f_445_; lean_object* v___x_446_; 
v___f_445_ = lean_alloc_closure((void*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_445_, 0, v_name_441_);
v___x_446_ = l_Functor_mapRev___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__0___redArg(v___f_440_, v___f_445_, v___y_442_, v___y_443_);
if (lean_obj_tag(v___x_446_) == 0)
{
lean_object* v_a_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_458_; 
v_a_447_ = lean_ctor_get(v___x_446_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_458_ == 0)
{
v___x_449_ = v___x_446_;
v_isShared_450_ = v_isSharedCheck_458_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_a_447_);
lean_dec(v___x_446_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_458_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
uint8_t v___x_451_; 
v___x_451_ = lean_unbox(v_a_447_);
lean_dec(v_a_447_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; lean_object* v___x_453_; 
lean_del_object(v___x_449_);
v___x_452_ = lean_obj_once(&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_, &l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2__once, _init_l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_);
v___x_453_ = l_Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1___redArg(v___x_452_, v___y_442_, v___y_443_);
return v___x_453_;
}
else
{
lean_object* v___x_454_; lean_object* v___x_456_; 
v___x_454_ = lean_box(0);
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 0, v___x_454_);
v___x_456_ = v___x_449_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v___x_454_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
}
else
{
lean_object* v_a_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_466_; 
v_a_459_ = lean_ctor_get(v___x_446_, 0);
v_isSharedCheck_466_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_466_ == 0)
{
v___x_461_ = v___x_446_;
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_a_459_);
lean_dec(v___x_446_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_464_; 
if (v_isShared_462_ == 0)
{
v___x_464_ = v___x_461_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_a_459_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2____boxed(lean_object* v___f_467_, lean_object* v_name_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_(v___f_467_, v_name_468_, v___y_469_, v___y_470_);
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___f_484_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_));
v___x_485_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_));
v___x_486_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_));
v___x_487_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_));
v___x_488_ = l_Lake_registerOrderedTagAttribute(v___x_485_, v___x_486_, v___f_484_, v___x_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2____boxed(lean_object* v_a_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_();
return v_res_490_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_(lean_object* v_name_491_, lean_object* v_env_492_){
_start:
{
lean_object* v___x_493_; uint8_t v___x_494_; 
v___x_493_ = l_Lake_scriptAttr;
lean_inc_ref(v_env_492_);
v___x_494_ = l_Lake_OrderedTagAttribute_hasTag(v___x_493_, v_env_492_, v_name_491_);
if (v___x_494_ == 0)
{
lean_object* v___x_495_; uint8_t v___x_496_; 
v___x_495_ = l_Lake_leanExeAttr;
v___x_496_ = l_Lake_OrderedTagAttribute_hasTag(v___x_495_, v_env_492_, v_name_491_);
return v___x_496_;
}
else
{
lean_dec_ref(v_env_492_);
return v___x_494_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2____boxed(lean_object* v_name_497_, lean_object* v_env_498_){
_start:
{
uint8_t v_res_499_; lean_object* v_r_500_; 
v_res_499_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_(v_name_497_, v_env_498_);
lean_dec(v_name_497_);
v_r_500_ = lean_box(v_res_499_);
return v_r_500_;
}
}
static lean_object* _init_l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_502_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__0_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_));
v___x_503_ = l_Lean_stringToMessageData(v___x_502_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_(lean_object* v___f_504_, lean_object* v_name_505_, lean_object* v___y_506_, lean_object* v___y_507_){
_start:
{
lean_object* v___f_509_; lean_object* v___x_510_; 
v___f_509_ = lean_alloc_closure((void*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_509_, 0, v_name_505_);
v___x_510_ = l_Functor_mapRev___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__0___redArg(v___f_504_, v___f_509_, v___y_506_, v___y_507_);
if (lean_obj_tag(v___x_510_) == 0)
{
lean_object* v_a_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_522_; 
v_a_511_ = lean_ctor_get(v___x_510_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_522_ == 0)
{
v___x_513_ = v___x_510_;
v_isShared_514_ = v_isSharedCheck_522_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_a_511_);
lean_dec(v___x_510_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_522_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
uint8_t v___x_515_; 
v___x_515_ = lean_unbox(v_a_511_);
lean_dec(v_a_511_);
if (v___x_515_ == 0)
{
lean_object* v___x_516_; lean_object* v___x_517_; 
lean_del_object(v___x_513_);
v___x_516_ = lean_obj_once(&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_, &l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2__once, _init_l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_);
v___x_517_ = l_Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1___redArg(v___x_516_, v___y_506_, v___y_507_);
return v___x_517_;
}
else
{
lean_object* v___x_518_; lean_object* v___x_520_; 
v___x_518_ = lean_box(0);
if (v_isShared_514_ == 0)
{
lean_ctor_set(v___x_513_, 0, v___x_518_);
v___x_520_ = v___x_513_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v___x_518_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
}
}
else
{
lean_object* v_a_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_530_; 
v_a_523_ = lean_ctor_get(v___x_510_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_530_ == 0)
{
v___x_525_ = v___x_510_;
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_a_523_);
lean_dec(v___x_510_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_528_; 
if (v_isShared_526_ == 0)
{
v___x_528_ = v___x_525_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_a_523_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2____boxed(lean_object* v___f_531_, lean_object* v_name_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_(v___f_531_, v_name_532_, v___y_533_, v___y_534_);
lean_dec(v___y_534_);
lean_dec_ref(v___y_533_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v___f_548_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_));
v___x_549_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_));
v___x_550_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_));
v___x_551_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_));
v___x_552_ = l_Lake_registerOrderedTagAttribute(v___x_549_, v___x_550_, v___f_548_, v___x_551_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2____boxed(lean_object* v_a_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_();
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v___f_564_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_));
v___x_565_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2_));
v___x_566_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2_));
v___x_567_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2_));
v___x_568_ = l_Lake_registerOrderedTagAttribute(v___x_565_, v___x_566_, v___f_564_, v___x_567_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2____boxed(lean_object* v_a_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2_();
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v___f_580_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_));
v___x_581_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2_));
v___x_582_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2_));
v___x_583_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2_));
v___x_584_ = l_Lake_registerOrderedTagAttribute(v___x_581_, v___x_582_, v___f_580_, v___x_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2____boxed(lean_object* v_a_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2_();
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
v___f_596_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_));
v___x_597_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2_));
v___x_598_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2_));
v___x_599_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2_));
v___x_600_ = l_Lake_registerOrderedTagAttribute(v___x_597_, v___x_598_, v___f_596_, v___x_599_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2____boxed(lean_object* v_a_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2_();
return v_res_602_;
}
}
lean_object* runtime_initialize_Lake_Util_OrderedTagAttribute(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_DSL_AttributesCore(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lake_Util_OrderedTagAttribute(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lake_packageAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lake_packageAttr);
lean_dec_ref(res);
res = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lake_packageDepAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lake_packageDepAttr);
lean_dec_ref(res);
res = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lake_postUpdateAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lake_postUpdateAttr);
lean_dec_ref(res);
res = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lake_scriptAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lake_scriptAttr);
lean_dec_ref(res);
res = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lake_defaultScriptAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lake_defaultScriptAttr);
lean_dec_ref(res);
res = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lake_leanLibAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lake_leanLibAttr);
lean_dec_ref(res);
res = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lake_leanExeAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lake_leanExeAttr);
lean_dec_ref(res);
res = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lake_externLibAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lake_externLibAttr);
lean_dec_ref(res);
res = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lake_inputFileAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lake_inputFileAttr);
lean_dec_ref(res);
res = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lake_inputDirAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lake_inputDirAttr);
lean_dec_ref(res);
res = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lake_targetAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lake_targetAttr);
lean_dec_ref(res);
res = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lake_defaultTargetAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lake_defaultTargetAttr);
lean_dec_ref(res);
res = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lake_testDriverAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lake_testDriverAttr);
lean_dec_ref(res);
res = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lake_lintDriverAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lake_lintDriverAttr);
lean_dec_ref(res);
res = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lake_moduleFacetAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lake_moduleFacetAttr);
lean_dec_ref(res);
res = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lake_packageFacetAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lake_packageFacetAttr);
lean_dec_ref(res);
res = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lake_libraryFacetAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lake_libraryFacetAttr);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_DSL_AttributesCore(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Util_OrderedTagAttribute(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_DSL_AttributesCore(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Util_OrderedTagAttribute(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_DSL_AttributesCore(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_DSL_AttributesCore(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_DSL_AttributesCore(builtin);
}
#ifdef __cplusplus
}
#endif

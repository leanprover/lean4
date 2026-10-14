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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
v___x_141_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_144_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_145_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__1);
v___x_146_ = lean_unsigned_to_nat(0u);
v___x_147_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_147_, 0, v___x_146_);
lean_ctor_set(v___x_147_, 1, v___x_146_);
lean_ctor_set(v___x_147_, 2, v___x_146_);
lean_ctor_set(v___x_147_, 3, v___x_146_);
lean_ctor_set(v___x_147_, 4, v___x_145_);
lean_ctor_set(v___x_147_, 5, v___x_145_);
lean_ctor_set(v___x_147_, 6, v___x_145_);
lean_ctor_set(v___x_147_, 7, v___x_145_);
lean_ctor_set(v___x_147_, 8, v___x_145_);
lean_ctor_set(v___x_147_, 9, v___x_145_);
lean_ctor_set(v___x_147_, 10, v___x_145_);
lean_ctor_set(v___x_147_, 11, v___x_144_);
return v___x_147_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__3(void){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_148_ = lean_unsigned_to_nat(32u);
v___x_149_ = lean_mk_empty_array_with_capacity(v___x_148_);
v___x_150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_150_, 0, v___x_149_);
return v___x_150_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__4(void){
_start:
{
size_t v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_151_ = ((size_t)5ULL);
v___x_152_ = lean_unsigned_to_nat(0u);
v___x_153_ = lean_unsigned_to_nat(32u);
v___x_154_ = lean_mk_empty_array_with_capacity(v___x_153_);
v___x_155_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__3);
v___x_156_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_156_, 0, v___x_155_);
lean_ctor_set(v___x_156_, 1, v___x_154_);
lean_ctor_set(v___x_156_, 2, v___x_152_);
lean_ctor_set(v___x_156_, 3, v___x_152_);
lean_ctor_set_usize(v___x_156_, 4, v___x_151_);
return v___x_156_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__5(void){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_157_ = lean_box(1);
v___x_158_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__4);
v___x_159_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__1);
v___x_160_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
lean_ctor_set(v___x_160_, 1, v___x_158_);
lean_ctor_set(v___x_160_, 2, v___x_157_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1(lean_object* v_msgData_161_, lean_object* v___y_162_, lean_object* v___y_163_){
_start:
{
lean_object* v___x_165_; lean_object* v_toCold_166_; lean_object* v_env_167_; lean_object* v_options_168_; uint8_t v___x_169_; lean_object* v_env_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_165_ = lean_st_ref_get(v___y_163_);
v_toCold_166_ = lean_ctor_get(v___y_162_, 0);
v_env_167_ = lean_ctor_get(v___x_165_, 0);
lean_inc_ref(v_env_167_);
lean_dec(v___x_165_);
v_options_168_ = lean_ctor_get(v_toCold_166_, 2);
v___x_169_ = 0;
v_env_170_ = l_Lean_Environment_setRecordingDeps(v_env_167_, v___x_169_);
v___x_171_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__2);
v___x_172_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__5);
lean_inc_ref(v_options_168_);
v___x_173_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_173_, 0, v_env_170_);
lean_ctor_set(v___x_173_, 1, v___x_171_);
lean_ctor_set(v___x_173_, 2, v___x_172_);
lean_ctor_set(v___x_173_, 3, v_options_168_);
v___x_174_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_174_, 0, v___x_173_);
lean_ctor_set(v___x_174_, 1, v_msgData_161_);
v___x_175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_175_, 0, v___x_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object* v_msgData_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1(v_msgData_176_, v___y_177_, v___y_178_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1___redArg(lean_object* v_msg_181_, lean_object* v___y_182_, lean_object* v___y_183_){
_start:
{
lean_object* v_ref_185_; lean_object* v___x_186_; lean_object* v_a_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_195_; 
v_ref_185_ = lean_ctor_get(v___y_182_, 2);
v___x_186_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1(v_msg_181_, v___y_182_, v___y_183_);
v_a_187_ = lean_ctor_get(v___x_186_, 0);
v_isSharedCheck_195_ = !lean_is_exclusive(v___x_186_);
if (v_isSharedCheck_195_ == 0)
{
v___x_189_ = v___x_186_;
v_isShared_190_ = v_isSharedCheck_195_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_a_187_);
lean_dec(v___x_186_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_195_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v___x_191_; lean_object* v___x_193_; 
lean_inc(v_ref_185_);
v___x_191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_191_, 0, v_ref_185_);
lean_ctor_set(v___x_191_, 1, v_a_187_);
if (v_isShared_190_ == 0)
{
lean_ctor_set_tag(v___x_189_, 1);
lean_ctor_set(v___x_189_, 0, v___x_191_);
v___x_193_ = v___x_189_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v___x_191_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_msg_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1___redArg(v_msg_196_, v___y_197_, v___y_198_);
lean_dec(v___y_198_);
lean_dec_ref(v___y_197_);
return v_res_200_;
}
}
static lean_object* _init_l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__2___closed__1_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_202_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__2___closed__0_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_));
v___x_203_ = l_Lean_stringToMessageData(v___x_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__2_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_(lean_object* v___f_204_, lean_object* v_name_205_, lean_object* v___y_206_, lean_object* v___y_207_){
_start:
{
lean_object* v___f_209_; lean_object* v___x_210_; 
v___f_209_ = lean_alloc_closure((void*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_209_, 0, v_name_205_);
v___x_210_ = l_Functor_mapRev___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__0___redArg(v___f_204_, v___f_209_, v___y_206_, v___y_207_);
if (lean_obj_tag(v___x_210_) == 0)
{
lean_object* v_a_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_222_; 
v_a_211_ = lean_ctor_get(v___x_210_, 0);
v_isSharedCheck_222_ = !lean_is_exclusive(v___x_210_);
if (v_isSharedCheck_222_ == 0)
{
v___x_213_ = v___x_210_;
v_isShared_214_ = v_isSharedCheck_222_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_a_211_);
lean_dec(v___x_210_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_222_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
uint8_t v___x_215_; 
v___x_215_ = lean_unbox(v_a_211_);
lean_dec(v_a_211_);
if (v___x_215_ == 0)
{
lean_object* v___x_216_; lean_object* v___x_217_; 
lean_del_object(v___x_213_);
v___x_216_ = lean_obj_once(&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__2___closed__1_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_, &l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__2___closed__1_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__once, _init_l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__2___closed__1_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_);
v___x_217_ = l_Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1___redArg(v___x_216_, v___y_206_, v___y_207_);
return v___x_217_;
}
else
{
lean_object* v___x_218_; lean_object* v___x_220_; 
v___x_218_ = lean_box(0);
if (v_isShared_214_ == 0)
{
lean_ctor_set(v___x_213_, 0, v___x_218_);
v___x_220_ = v___x_213_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v___x_218_);
v___x_220_ = v_reuseFailAlloc_221_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
return v___x_220_;
}
}
}
}
else
{
lean_object* v_a_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_230_; 
v_a_223_ = lean_ctor_get(v___x_210_, 0);
v_isSharedCheck_230_ = !lean_is_exclusive(v___x_210_);
if (v_isSharedCheck_230_ == 0)
{
v___x_225_ = v___x_210_;
v_isShared_226_ = v_isSharedCheck_230_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_a_223_);
lean_dec(v___x_210_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_230_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v___x_228_; 
if (v_isShared_226_ == 0)
{
v___x_228_ = v___x_225_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v_a_223_);
v___x_228_ = v_reuseFailAlloc_229_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
return v___x_228_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__2_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2____boxed(lean_object* v___f_231_, lean_object* v_name_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__2_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_(v___f_231_, v_name_232_, v___y_233_, v___y_234_);
lean_dec(v___y_234_);
lean_dec_ref(v___y_233_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___f_249_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_));
v___x_250_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_));
v___x_251_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_));
v___x_252_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__6_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_));
v___x_253_ = l_Lake_registerOrderedTagAttribute(v___x_250_, v___x_251_, v___f_249_, v___x_252_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2____boxed(lean_object* v_a_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_();
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b1_256_, lean_object* v_msg_257_, lean_object* v___y_258_, lean_object* v___y_259_){
_start:
{
lean_object* v___x_261_; 
v___x_261_ = l_Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1___redArg(v_msg_257_, v___y_258_, v___y_259_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1___boxed(lean_object* v_00_u03b1_262_, lean_object* v_msg_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l_Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1(v_00_u03b1_262_, v_msg_263_, v___y_264_, v___y_265_);
lean_dec(v___y_265_);
lean_dec_ref(v___y_264_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v___f_277_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_));
v___x_278_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2_));
v___x_279_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2_));
v___x_280_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2_));
v___x_281_ = l_Lake_registerOrderedTagAttribute(v___x_278_, v___x_279_, v___f_277_, v___x_280_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2____boxed(lean_object* v_a_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2_();
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___f_293_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_));
v___x_294_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2_));
v___x_295_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2_));
v___x_296_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2_));
v___x_297_ = l_Lake_registerOrderedTagAttribute(v___x_294_, v___x_295_, v___f_293_, v___x_296_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2____boxed(lean_object* v_a_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2_();
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___f_309_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_));
v___x_310_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2_));
v___x_311_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2_));
v___x_312_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2_));
v___x_313_ = l_Lake_registerOrderedTagAttribute(v___x_310_, v___x_311_, v___f_309_, v___x_312_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2____boxed(lean_object* v_a_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2_();
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v___f_325_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_));
v___x_326_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2_));
v___x_327_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2_));
v___x_328_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2_));
v___x_329_ = l_Lake_registerOrderedTagAttribute(v___x_326_, v___x_327_, v___f_325_, v___x_328_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2____boxed(lean_object* v_a_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2_();
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___f_341_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_));
v___x_342_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2_));
v___x_343_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2_));
v___x_344_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2_));
v___x_345_ = l_Lake_registerOrderedTagAttribute(v___x_342_, v___x_343_, v___f_341_, v___x_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2____boxed(lean_object* v_a_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2_();
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v___f_357_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_));
v___x_358_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2_));
v___x_359_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2_));
v___x_360_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2_));
v___x_361_ = l_Lake_registerOrderedTagAttribute(v___x_358_, v___x_359_, v___f_357_, v___x_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2____boxed(lean_object* v_a_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2_();
return v_res_363_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_(lean_object* v_name_364_, lean_object* v_env_365_){
_start:
{
lean_object* v___x_366_; uint8_t v___x_367_; 
v___x_366_ = l_Lake_targetAttr;
v___x_367_ = l_Lake_OrderedTagAttribute_hasTag(v___x_366_, v_env_365_, v_name_364_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2____boxed(lean_object* v_name_368_, lean_object* v_env_369_){
_start:
{
uint8_t v_res_370_; lean_object* v_r_371_; 
v_res_370_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_(v_name_368_, v_env_369_);
lean_dec(v_name_368_);
v_r_371_ = lean_box(v_res_370_);
return v_r_371_;
}
}
static lean_object* _init_l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__0_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_));
v___x_374_ = l_Lean_stringToMessageData(v___x_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_(lean_object* v___f_375_, lean_object* v_name_376_, lean_object* v___y_377_, lean_object* v___y_378_){
_start:
{
lean_object* v___f_380_; lean_object* v___x_381_; 
v___f_380_ = lean_alloc_closure((void*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_380_, 0, v_name_376_);
v___x_381_ = l_Functor_mapRev___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__0___redArg(v___f_375_, v___f_380_, v___y_377_, v___y_378_);
if (lean_obj_tag(v___x_381_) == 0)
{
lean_object* v_a_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_393_; 
v_a_382_ = lean_ctor_get(v___x_381_, 0);
v_isSharedCheck_393_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_393_ == 0)
{
v___x_384_ = v___x_381_;
v_isShared_385_ = v_isSharedCheck_393_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_a_382_);
lean_dec(v___x_381_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_393_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
uint8_t v___x_386_; 
v___x_386_ = lean_unbox(v_a_382_);
lean_dec(v_a_382_);
if (v___x_386_ == 0)
{
lean_object* v___x_387_; lean_object* v___x_388_; 
lean_del_object(v___x_384_);
v___x_387_ = lean_obj_once(&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_, &l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2__once, _init_l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_);
v___x_388_ = l_Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1___redArg(v___x_387_, v___y_377_, v___y_378_);
return v___x_388_;
}
else
{
lean_object* v___x_389_; lean_object* v___x_391_; 
v___x_389_ = lean_box(0);
if (v_isShared_385_ == 0)
{
lean_ctor_set(v___x_384_, 0, v___x_389_);
v___x_391_ = v___x_384_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v___x_389_);
v___x_391_ = v_reuseFailAlloc_392_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
return v___x_391_;
}
}
}
}
else
{
lean_object* v_a_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_401_; 
v_a_394_ = lean_ctor_get(v___x_381_, 0);
v_isSharedCheck_401_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_401_ == 0)
{
v___x_396_ = v___x_381_;
v_isShared_397_ = v_isSharedCheck_401_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_a_394_);
lean_dec(v___x_381_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_401_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_399_; 
if (v_isShared_397_ == 0)
{
v___x_399_ = v___x_396_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v_a_394_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
return v___x_399_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2____boxed(lean_object* v___f_402_, lean_object* v_name_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_(v___f_402_, v_name_403_, v___y_404_, v___y_405_);
lean_dec(v___y_405_);
lean_dec_ref(v___y_404_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v___f_419_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_));
v___x_420_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_));
v___x_421_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_));
v___x_422_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_));
v___x_423_ = l_Lake_registerOrderedTagAttribute(v___x_420_, v___x_421_, v___f_419_, v___x_422_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2____boxed(lean_object* v_a_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_();
return v_res_425_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_(lean_object* v_name_426_, lean_object* v_env_427_){
_start:
{
uint8_t v___y_429_; lean_object* v___x_432_; uint8_t v___x_433_; 
v___x_432_ = l_Lake_scriptAttr;
lean_inc_ref(v_env_427_);
v___x_433_ = l_Lake_OrderedTagAttribute_hasTag(v___x_432_, v_env_427_, v_name_426_);
if (v___x_433_ == 0)
{
lean_object* v___x_434_; uint8_t v___x_435_; 
v___x_434_ = l_Lake_leanExeAttr;
lean_inc_ref(v_env_427_);
v___x_435_ = l_Lake_OrderedTagAttribute_hasTag(v___x_434_, v_env_427_, v_name_426_);
v___y_429_ = v___x_435_;
goto v___jp_428_;
}
else
{
v___y_429_ = v___x_433_;
goto v___jp_428_;
}
v___jp_428_:
{
if (v___y_429_ == 0)
{
lean_object* v___x_430_; uint8_t v___x_431_; 
v___x_430_ = l_Lake_leanLibAttr;
v___x_431_ = l_Lake_OrderedTagAttribute_hasTag(v___x_430_, v_env_427_, v_name_426_);
return v___x_431_;
}
else
{
lean_dec_ref(v_env_427_);
return v___y_429_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2____boxed(lean_object* v_name_436_, lean_object* v_env_437_){
_start:
{
uint8_t v_res_438_; lean_object* v_r_439_; 
v_res_438_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_(v_name_436_, v_env_437_);
lean_dec(v_name_436_);
v_r_439_ = lean_box(v_res_438_);
return v_r_439_;
}
}
static lean_object* _init_l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_441_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__0_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_));
v___x_442_ = l_Lean_stringToMessageData(v___x_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_(lean_object* v___f_443_, lean_object* v_name_444_, lean_object* v___y_445_, lean_object* v___y_446_){
_start:
{
lean_object* v___f_448_; lean_object* v___x_449_; 
v___f_448_ = lean_alloc_closure((void*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_448_, 0, v_name_444_);
v___x_449_ = l_Functor_mapRev___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__0___redArg(v___f_443_, v___f_448_, v___y_445_, v___y_446_);
if (lean_obj_tag(v___x_449_) == 0)
{
lean_object* v_a_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_461_; 
v_a_450_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_461_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_461_ == 0)
{
v___x_452_ = v___x_449_;
v_isShared_453_ = v_isSharedCheck_461_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_a_450_);
lean_dec(v___x_449_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_461_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
uint8_t v___x_454_; 
v___x_454_ = lean_unbox(v_a_450_);
lean_dec(v_a_450_);
if (v___x_454_ == 0)
{
lean_object* v___x_455_; lean_object* v___x_456_; 
lean_del_object(v___x_452_);
v___x_455_ = lean_obj_once(&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_, &l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2__once, _init_l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_);
v___x_456_ = l_Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1___redArg(v___x_455_, v___y_445_, v___y_446_);
return v___x_456_;
}
else
{
lean_object* v___x_457_; lean_object* v___x_459_; 
v___x_457_ = lean_box(0);
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 0, v___x_457_);
v___x_459_ = v___x_452_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v___x_457_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
}
}
else
{
lean_object* v_a_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_469_; 
v_a_462_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_469_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_469_ == 0)
{
v___x_464_ = v___x_449_;
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_a_462_);
lean_dec(v___x_449_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_467_; 
if (v_isShared_465_ == 0)
{
v___x_467_ = v___x_464_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_a_462_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2____boxed(lean_object* v___f_470_, lean_object* v_name_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_(v___f_470_, v_name_471_, v___y_472_, v___y_473_);
lean_dec(v___y_473_);
lean_dec_ref(v___y_472_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v___f_487_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_));
v___x_488_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_));
v___x_489_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_));
v___x_490_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_));
v___x_491_ = l_Lake_registerOrderedTagAttribute(v___x_488_, v___x_489_, v___f_487_, v___x_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2____boxed(lean_object* v_a_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_();
return v_res_493_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_(lean_object* v_name_494_, lean_object* v_env_495_){
_start:
{
lean_object* v___x_496_; uint8_t v___x_497_; 
v___x_496_ = l_Lake_scriptAttr;
lean_inc_ref(v_env_495_);
v___x_497_ = l_Lake_OrderedTagAttribute_hasTag(v___x_496_, v_env_495_, v_name_494_);
if (v___x_497_ == 0)
{
lean_object* v___x_498_; uint8_t v___x_499_; 
v___x_498_ = l_Lake_leanExeAttr;
v___x_499_ = l_Lake_OrderedTagAttribute_hasTag(v___x_498_, v_env_495_, v_name_494_);
return v___x_499_;
}
else
{
lean_dec_ref(v_env_495_);
return v___x_497_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2____boxed(lean_object* v_name_500_, lean_object* v_env_501_){
_start:
{
uint8_t v_res_502_; lean_object* v_r_503_; 
v_res_502_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_(v_name_500_, v_env_501_);
lean_dec(v_name_500_);
v_r_503_ = lean_box(v_res_502_);
return v_r_503_;
}
}
static lean_object* _init_l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_505_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__0_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_));
v___x_506_ = l_Lean_stringToMessageData(v___x_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_(lean_object* v___f_507_, lean_object* v_name_508_, lean_object* v___y_509_, lean_object* v___y_510_){
_start:
{
lean_object* v___f_512_; lean_object* v___x_513_; 
v___f_512_ = lean_alloc_closure((void*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_512_, 0, v_name_508_);
v___x_513_ = l_Functor_mapRev___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__0___redArg(v___f_507_, v___f_512_, v___y_509_, v___y_510_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v_a_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_525_; 
v_a_514_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_525_ == 0)
{
v___x_516_ = v___x_513_;
v_isShared_517_ = v_isSharedCheck_525_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_a_514_);
lean_dec(v___x_513_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_525_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
uint8_t v___x_518_; 
v___x_518_ = lean_unbox(v_a_514_);
lean_dec(v_a_514_);
if (v___x_518_ == 0)
{
lean_object* v___x_519_; lean_object* v___x_520_; 
lean_del_object(v___x_516_);
v___x_519_ = lean_obj_once(&l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_, &l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2__once, _init_l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_);
v___x_520_ = l_Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1___redArg(v___x_519_, v___y_509_, v___y_510_);
return v___x_520_;
}
else
{
lean_object* v___x_521_; lean_object* v___x_523_; 
v___x_521_ = lean_box(0);
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 0, v___x_521_);
v___x_523_ = v___x_516_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v___x_521_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
}
else
{
lean_object* v_a_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_533_; 
v_a_526_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_533_ == 0)
{
v___x_528_ = v___x_513_;
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_a_526_);
lean_dec(v___x_513_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v___x_531_; 
if (v_isShared_529_ == 0)
{
v___x_531_ = v___x_528_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v_a_526_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2____boxed(lean_object* v___f_534_, lean_object* v_name_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_(v___f_534_, v_name_535_, v___y_536_, v___y_537_);
lean_dec(v___y_537_);
lean_dec_ref(v___y_536_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v___f_551_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_));
v___x_552_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_));
v___x_553_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_));
v___x_554_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_));
v___x_555_ = l_Lake_registerOrderedTagAttribute(v___x_552_, v___x_553_, v___f_551_, v___x_554_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2____boxed(lean_object* v_a_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_();
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v___f_567_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_));
v___x_568_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2_));
v___x_569_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2_));
v___x_570_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2_));
v___x_571_ = l_Lake_registerOrderedTagAttribute(v___x_568_, v___x_569_, v___f_567_, v___x_570_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2____boxed(lean_object* v_a_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2_();
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v___f_583_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_));
v___x_584_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2_));
v___x_585_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2_));
v___x_586_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2_));
v___x_587_ = l_Lake_registerOrderedTagAttribute(v___x_584_, v___x_585_, v___f_583_, v___x_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2____boxed(lean_object* v_a_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2_();
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v___f_599_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_));
v___x_600_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2_));
v___x_601_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2_));
v___x_602_ = ((lean_object*)(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2_));
v___x_603_ = l_Lake_registerOrderedTagAttribute(v___x_600_, v___x_601_, v___f_599_, v___x_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2____boxed(lean_object* v_a_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2_();
return v_res_605_;
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

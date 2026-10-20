// Lean compiler output
// Module: Lean.AuxRecursor
// Imports: public import Lean.EnvExtension import Init.Data.String.TakeDrop
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
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_mkTagDeclarationExtension(lean_object*, lean_object*, uint8_t);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Lean_TagDeclarationExtension_tag(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkMapDeclarationExtension___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
uint8_t l_Lean_MapDeclarationExtension_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
static const lean_string_object l_Lean_casesOnSuffix___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "casesOn"};
static const lean_object* l_Lean_casesOnSuffix___closed__0 = (const lean_object*)&l_Lean_casesOnSuffix___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_casesOnSuffix = (const lean_object*)&l_Lean_casesOnSuffix___closed__0_value;
static const lean_string_object l_Lean_recOnSuffix___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "recOn"};
static const lean_object* l_Lean_recOnSuffix___closed__0 = (const lean_object*)&l_Lean_recOnSuffix___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_recOnSuffix = (const lean_object*)&l_Lean_recOnSuffix___closed__0_value;
static const lean_string_object l_Lean_brecOnSuffix___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "brecOn"};
static const lean_object* l_Lean_brecOnSuffix___closed__0 = (const lean_object*)&l_Lean_brecOnSuffix___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_brecOnSuffix = (const lean_object*)&l_Lean_brecOnSuffix___closed__0_value;
static const lean_string_object l_Lean_belowSuffix___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "below"};
static const lean_object* l_Lean_belowSuffix___closed__0 = (const lean_object*)&l_Lean_belowSuffix___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_belowSuffix = (const lean_object*)&l_Lean_belowSuffix___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_mkCasesOnName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkRecOnName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkBRecOnName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkBelowName(lean_object*);
static const lean_string_object l___private_Lean_AuxRecursor_0__Lean_initFn___closed__0_00___x40_Lean_AuxRecursor_4193738739____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_AuxRecursor_0__Lean_initFn___closed__0_00___x40_Lean_AuxRecursor_4193738739____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_AuxRecursor_0__Lean_initFn___closed__0_00___x40_Lean_AuxRecursor_4193738739____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_AuxRecursor_0__Lean_initFn___closed__1_00___x40_Lean_AuxRecursor_4193738739____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "auxRecExt"};
static const lean_object* l___private_Lean_AuxRecursor_0__Lean_initFn___closed__1_00___x40_Lean_AuxRecursor_4193738739____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_AuxRecursor_0__Lean_initFn___closed__1_00___x40_Lean_AuxRecursor_4193738739____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_AuxRecursor_0__Lean_initFn___closed__2_00___x40_Lean_AuxRecursor_4193738739____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_AuxRecursor_0__Lean_initFn___closed__0_00___x40_Lean_AuxRecursor_4193738739____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_AuxRecursor_0__Lean_initFn___closed__2_00___x40_Lean_AuxRecursor_4193738739____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_AuxRecursor_0__Lean_initFn___closed__2_00___x40_Lean_AuxRecursor_4193738739____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_AuxRecursor_0__Lean_initFn___closed__1_00___x40_Lean_AuxRecursor_4193738739____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(105, 237, 166, 221, 148, 106, 49, 53)}};
static const lean_object* l___private_Lean_AuxRecursor_0__Lean_initFn___closed__2_00___x40_Lean_AuxRecursor_4193738739____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_AuxRecursor_0__Lean_initFn___closed__2_00___x40_Lean_AuxRecursor_4193738739____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_AuxRecursor_0__Lean_initFn___closed__3_00___x40_Lean_AuxRecursor_4193738739____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 3}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_AuxRecursor_0__Lean_initFn___closed__3_00___x40_Lean_AuxRecursor_4193738739____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_AuxRecursor_0__Lean_initFn___closed__3_00___x40_Lean_AuxRecursor_4193738739____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_4193738739____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_4193738739____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_auxRecExt;
LEAN_EXPORT lean_object* l_Lean_markAuxRecursor(lean_object*, lean_object*);
static const lean_string_object l_Lean_isAuxRecursor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_isAuxRecursor___closed__0 = (const lean_object*)&l_Lean_isAuxRecursor___closed__0_value;
static const lean_string_object l_Lean_isAuxRecursor___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ndrec"};
static const lean_object* l_Lean_isAuxRecursor___closed__1 = (const lean_object*)&l_Lean_isAuxRecursor___closed__1_value;
static const lean_ctor_object l_Lean_isAuxRecursor___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isAuxRecursor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_isAuxRecursor___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_isAuxRecursor___closed__2_value_aux_0),((lean_object*)&l_Lean_isAuxRecursor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(115, 164, 251, 202, 217, 58, 77, 179)}};
static const lean_object* l_Lean_isAuxRecursor___closed__2 = (const lean_object*)&l_Lean_isAuxRecursor___closed__2_value;
static const lean_string_object l_Lean_isAuxRecursor___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "ndrec_symm"};
static const lean_object* l_Lean_isAuxRecursor___closed__3 = (const lean_object*)&l_Lean_isAuxRecursor___closed__3_value;
static const lean_ctor_object l_Lean_isAuxRecursor___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isAuxRecursor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_isAuxRecursor___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_isAuxRecursor___closed__4_value_aux_0),((lean_object*)&l_Lean_isAuxRecursor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(71, 160, 179, 99, 219, 64, 47, 167)}};
static const lean_object* l_Lean_isAuxRecursor___closed__4 = (const lean_object*)&l_Lean_isAuxRecursor___closed__4_value;
static const lean_string_object l_Lean_isAuxRecursor___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ndrecOn"};
static const lean_object* l_Lean_isAuxRecursor___closed__5 = (const lean_object*)&l_Lean_isAuxRecursor___closed__5_value;
static const lean_ctor_object l_Lean_isAuxRecursor___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isAuxRecursor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_isAuxRecursor___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_isAuxRecursor___closed__6_value_aux_0),((lean_object*)&l_Lean_isAuxRecursor___closed__5_value),LEAN_SCALAR_PTR_LITERAL(74, 212, 24, 249, 139, 157, 15, 213)}};
static const lean_object* l_Lean_isAuxRecursor___closed__6 = (const lean_object*)&l_Lean_isAuxRecursor___closed__6_value;
LEAN_EXPORT uint8_t l_Lean_isAuxRecursor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isAuxRecursor___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_isAuxRecursorWithSuffix___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Lean_isAuxRecursorWithSuffix___closed__0 = (const lean_object*)&l_Lean_isAuxRecursorWithSuffix___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_isAuxRecursorWithSuffix(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isAuxRecursorWithSuffix___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_isCasesOnRecursor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isCasesOnRecursor___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_isRecOnRecursor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isRecOnRecursor___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_isBRecOnRecursor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isBRecOnRecursor___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_AuxRecursor_0__Lean_initFn___closed__0_00___x40_Lean_AuxRecursor_163548097____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_AuxRecursor_0__Lean_initFn___closed__0_00___x40_Lean_AuxRecursor_163548097____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_AuxRecursor_0__Lean_initFn___closed__0_00___x40_Lean_AuxRecursor_163548097____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_AuxRecursor_0__Lean_initFn___closed__1_00___x40_Lean_AuxRecursor_163548097____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_AuxRecursor_0__Lean_initFn___closed__0_00___x40_Lean_AuxRecursor_163548097____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_AuxRecursor_0__Lean_initFn___closed__1_00___x40_Lean_AuxRecursor_163548097____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_AuxRecursor_0__Lean_initFn___closed__1_00___x40_Lean_AuxRecursor_163548097____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_AuxRecursor_0__Lean_initFn___closed__2_00___x40_Lean_AuxRecursor_163548097____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_AuxRecursor_0__Lean_initFn___closed__1_00___x40_Lean_AuxRecursor_163548097____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_AuxRecursor_0__Lean_initFn___closed__0_00___x40_Lean_AuxRecursor_4193738739____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_AuxRecursor_0__Lean_initFn___closed__2_00___x40_Lean_AuxRecursor_163548097____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_AuxRecursor_0__Lean_initFn___closed__2_00___x40_Lean_AuxRecursor_163548097____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_AuxRecursor_0__Lean_initFn___closed__3_00___x40_Lean_AuxRecursor_163548097____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "AuxRecursor"};
static const lean_object* l___private_Lean_AuxRecursor_0__Lean_initFn___closed__3_00___x40_Lean_AuxRecursor_163548097____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_AuxRecursor_0__Lean_initFn___closed__3_00___x40_Lean_AuxRecursor_163548097____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_AuxRecursor_0__Lean_initFn___closed__4_00___x40_Lean_AuxRecursor_163548097____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_AuxRecursor_0__Lean_initFn___closed__2_00___x40_Lean_AuxRecursor_163548097____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_AuxRecursor_0__Lean_initFn___closed__3_00___x40_Lean_AuxRecursor_163548097____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(243, 71, 92, 208, 56, 190, 224, 113)}};
static const lean_object* l___private_Lean_AuxRecursor_0__Lean_initFn___closed__4_00___x40_Lean_AuxRecursor_163548097____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_AuxRecursor_0__Lean_initFn___closed__4_00___x40_Lean_AuxRecursor_163548097____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_AuxRecursor_0__Lean_initFn___closed__5_00___x40_Lean_AuxRecursor_163548097____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_AuxRecursor_0__Lean_initFn___closed__4_00___x40_Lean_AuxRecursor_163548097____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(94, 87, 119, 208, 23, 13, 32, 194)}};
static const lean_object* l___private_Lean_AuxRecursor_0__Lean_initFn___closed__5_00___x40_Lean_AuxRecursor_163548097____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_AuxRecursor_0__Lean_initFn___closed__5_00___x40_Lean_AuxRecursor_163548097____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_AuxRecursor_0__Lean_initFn___closed__6_00___x40_Lean_AuxRecursor_163548097____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_AuxRecursor_0__Lean_initFn___closed__5_00___x40_Lean_AuxRecursor_163548097____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_AuxRecursor_0__Lean_initFn___closed__0_00___x40_Lean_AuxRecursor_4193738739____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(167, 145, 139, 114, 135, 121, 7, 142)}};
static const lean_object* l___private_Lean_AuxRecursor_0__Lean_initFn___closed__6_00___x40_Lean_AuxRecursor_163548097____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_AuxRecursor_0__Lean_initFn___closed__6_00___x40_Lean_AuxRecursor_163548097____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_AuxRecursor_0__Lean_initFn___closed__7_00___x40_Lean_AuxRecursor_163548097____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "sparseCasesOnExt"};
static const lean_object* l___private_Lean_AuxRecursor_0__Lean_initFn___closed__7_00___x40_Lean_AuxRecursor_163548097____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_AuxRecursor_0__Lean_initFn___closed__7_00___x40_Lean_AuxRecursor_163548097____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_AuxRecursor_0__Lean_initFn___closed__8_00___x40_Lean_AuxRecursor_163548097____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_AuxRecursor_0__Lean_initFn___closed__6_00___x40_Lean_AuxRecursor_163548097____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_AuxRecursor_0__Lean_initFn___closed__7_00___x40_Lean_AuxRecursor_163548097____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(192, 252, 121, 117, 134, 106, 159, 193)}};
static const lean_object* l___private_Lean_AuxRecursor_0__Lean_initFn___closed__8_00___x40_Lean_AuxRecursor_163548097____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_AuxRecursor_0__Lean_initFn___closed__8_00___x40_Lean_AuxRecursor_163548097____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_163548097____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_163548097____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AuxRecursor_0__Lean_sparseCasesOnExt;
LEAN_EXPORT lean_object* l_Lean_markSparseCasesOn(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_isSparseCasesOn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isSparseCasesOn___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_isCasesOnLike(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isCasesOnLike___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NoConfusionInfo_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_NoConfusionInfo_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_NoConfusionInfo_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NoConfusionInfo_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NoConfusionInfo_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NoConfusionInfo_regular_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NoConfusionInfo_regular_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NoConfusionInfo_perCtor_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NoConfusionInfo_perCtor_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_instInhabitedNoConfusionInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_instInhabitedNoConfusionInfo_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedNoConfusionInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedNoConfusionInfo_default = (const lean_object*)&l_Lean_instInhabitedNoConfusionInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedNoConfusionInfo = (const lean_object*)&l_Lean_instInhabitedNoConfusionInfo_default___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_NoConfusionInfo_arity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_NoConfusionInfo_arity___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_AuxRecursor_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_AuxRecursor_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_AuxRecursor_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__value;
static const lean_array_object l___private_Lean_AuxRecursor_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_AuxRecursor_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_AuxRecursor_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_AuxRecursor_0__Lean_initFn___lam__0_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AuxRecursor_0__Lean_initFn___lam__0_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_AuxRecursor_0__Lean_initFn___closed__0_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_AuxRecursor_0__Lean_initFn___lam__0_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_AuxRecursor_0__Lean_initFn___closed__0_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_AuxRecursor_0__Lean_initFn___closed__0_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_AuxRecursor_0__Lean_initFn___closed__1_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "noConfusionExt"};
static const lean_object* l___private_Lean_AuxRecursor_0__Lean_initFn___closed__1_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_AuxRecursor_0__Lean_initFn___closed__1_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_AuxRecursor_0__Lean_initFn___closed__2_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_AuxRecursor_0__Lean_initFn___closed__0_00___x40_Lean_AuxRecursor_4193738739____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_AuxRecursor_0__Lean_initFn___closed__2_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_AuxRecursor_0__Lean_initFn___closed__2_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_AuxRecursor_0__Lean_initFn___closed__1_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(42, 4, 193, 241, 26, 143, 160, 211)}};
static const lean_object* l___private_Lean_AuxRecursor_0__Lean_initFn___closed__2_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_AuxRecursor_0__Lean_initFn___closed__2_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_noConfusionExt;
LEAN_EXPORT lean_object* l_Lean_markNoConfusion(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_isNoConfusion(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isNoConfusion___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getNoConfusionInfo_spec__0(lean_object*);
static const lean_string_object l_Lean_getNoConfusionInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l_Lean_getNoConfusionInfo___closed__0 = (const lean_object*)&l_Lean_getNoConfusionInfo___closed__0_value;
static const lean_string_object l_Lean_getNoConfusionInfo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l_Lean_getNoConfusionInfo___closed__1 = (const lean_object*)&l_Lean_getNoConfusionInfo___closed__1_value;
static const lean_string_object l_Lean_getNoConfusionInfo___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l_Lean_getNoConfusionInfo___closed__2 = (const lean_object*)&l_Lean_getNoConfusionInfo___closed__2_value;
static lean_once_cell_t l_Lean_getNoConfusionInfo___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getNoConfusionInfo___closed__3;
LEAN_EXPORT lean_object* l_Lean_getNoConfusionInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnName(lean_object* v_indDeclName_9_){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_10_ = ((lean_object*)(l_Lean_casesOnSuffix___closed__0));
v___x_11_ = l_Lean_Name_str___override(v_indDeclName_9_, v___x_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRecOnName(lean_object* v_indDeclName_12_){
_start:
{
lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_13_ = ((lean_object*)(l_Lean_recOnSuffix___closed__0));
v___x_14_ = l_Lean_Name_str___override(v_indDeclName_12_, v___x_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBRecOnName(lean_object* v_indDeclName_15_){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_16_ = ((lean_object*)(l_Lean_brecOnSuffix___closed__0));
v___x_17_ = l_Lean_Name_str___override(v_indDeclName_15_, v___x_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBelowName(lean_object* v_indDeclName_18_){
_start:
{
lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_19_ = ((lean_object*)(l_Lean_belowSuffix___closed__0));
v___x_20_ = l_Lean_Name_str___override(v_indDeclName_18_, v___x_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_4193738739____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; uint8_t v___x_31_; lean_object* v___x_32_; 
v___x_29_ = ((lean_object*)(l___private_Lean_AuxRecursor_0__Lean_initFn___closed__2_00___x40_Lean_AuxRecursor_4193738739____hygCtx___hyg_2_));
v___x_30_ = ((lean_object*)(l___private_Lean_AuxRecursor_0__Lean_initFn___closed__3_00___x40_Lean_AuxRecursor_4193738739____hygCtx___hyg_2_));
v___x_31_ = 1;
v___x_32_ = l_Lean_mkTagDeclarationExtension(v___x_29_, v___x_30_, v___x_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_4193738739____hygCtx___hyg_2____boxed(lean_object* v_a_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l___private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_4193738739____hygCtx___hyg_2_();
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_markAuxRecursor(lean_object* v_env_35_, lean_object* v_declName_36_){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_37_ = l_Lean_auxRecExt;
v___x_38_ = l_Lean_TagDeclarationExtension_tag(v___x_37_, v_env_35_, v_declName_36_);
return v___x_38_;
}
}
LEAN_EXPORT uint8_t l_Lean_isAuxRecursor(lean_object* v_env_52_, lean_object* v_declName_53_){
_start:
{
lean_object* v___x_54_; lean_object* v_toEnvExtension_55_; lean_object* v_asyncMode_56_; uint8_t v___x_57_; 
v___x_54_ = l_Lean_auxRecExt;
v_toEnvExtension_55_ = lean_ctor_get(v___x_54_, 0);
v_asyncMode_56_ = lean_ctor_get(v_toEnvExtension_55_, 2);
lean_inc(v_declName_53_);
v___x_57_ = l_Lean_TagDeclarationExtension_isTagged(v___x_54_, v_env_52_, v_declName_53_, v_asyncMode_56_);
if (v___x_57_ == 0)
{
lean_object* v___x_58_; uint8_t v___x_59_; 
v___x_58_ = ((lean_object*)(l_Lean_isAuxRecursor___closed__2));
v___x_59_ = lean_name_eq(v_declName_53_, v___x_58_);
if (v___x_59_ == 0)
{
lean_object* v___x_60_; uint8_t v___x_61_; 
v___x_60_ = ((lean_object*)(l_Lean_isAuxRecursor___closed__4));
v___x_61_ = lean_name_eq(v_declName_53_, v___x_60_);
if (v___x_61_ == 0)
{
lean_object* v___x_62_; uint8_t v___x_63_; 
v___x_62_ = ((lean_object*)(l_Lean_isAuxRecursor___closed__6));
v___x_63_ = lean_name_eq(v_declName_53_, v___x_62_);
lean_dec(v_declName_53_);
return v___x_63_;
}
else
{
lean_dec(v_declName_53_);
return v___x_61_;
}
}
else
{
lean_dec(v_declName_53_);
return v___x_59_;
}
}
else
{
lean_dec(v_declName_53_);
return v___x_57_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isAuxRecursor___boxed(lean_object* v_env_64_, lean_object* v_declName_65_){
_start:
{
uint8_t v_res_66_; lean_object* v_r_67_; 
v_res_66_ = l_Lean_isAuxRecursor(v_env_64_, v_declName_65_);
v_r_67_ = lean_box(v_res_66_);
return v_r_67_;
}
}
LEAN_EXPORT uint8_t l_Lean_isAuxRecursorWithSuffix(lean_object* v_env_69_, lean_object* v_declName_70_, lean_object* v_suffix_71_){
_start:
{
if (lean_obj_tag(v_declName_70_) == 1)
{
lean_object* v_str_72_; uint8_t v___x_73_; 
v_str_72_ = lean_ctor_get(v_declName_70_, 1);
v___x_73_ = lean_string_dec_eq(v_str_72_, v_suffix_71_);
if (v___x_73_ == 0)
{
lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; uint8_t v___x_78_; 
v___x_74_ = ((lean_object*)(l_Lean_isAuxRecursorWithSuffix___closed__0));
v___x_75_ = lean_string_append(v_suffix_71_, v___x_74_);
v___x_76_ = lean_string_utf8_byte_size(v_str_72_);
v___x_77_ = lean_string_utf8_byte_size(v___x_75_);
v___x_78_ = lean_nat_dec_le(v___x_77_, v___x_76_);
if (v___x_78_ == 0)
{
lean_dec_ref(v___x_75_);
lean_dec_ref_known(v_declName_70_, 2);
lean_dec_ref(v_env_69_);
return v___x_78_;
}
else
{
lean_object* v___x_79_; uint8_t v___x_80_; 
v___x_79_ = lean_unsigned_to_nat(0u);
v___x_80_ = lean_string_memcmp(v_str_72_, v___x_75_, v___x_79_, v___x_79_, v___x_77_);
lean_dec_ref(v___x_75_);
if (v___x_80_ == 0)
{
lean_dec_ref_known(v_declName_70_, 2);
lean_dec_ref(v_env_69_);
return v___x_80_;
}
else
{
uint8_t v___x_81_; 
v___x_81_ = l_Lean_isAuxRecursor(v_env_69_, v_declName_70_);
return v___x_81_;
}
}
}
else
{
uint8_t v___x_82_; 
lean_dec_ref(v_suffix_71_);
v___x_82_ = l_Lean_isAuxRecursor(v_env_69_, v_declName_70_);
return v___x_82_;
}
}
else
{
uint8_t v___x_83_; 
lean_dec_ref(v_suffix_71_);
lean_dec(v_declName_70_);
lean_dec_ref(v_env_69_);
v___x_83_ = 0;
return v___x_83_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isAuxRecursorWithSuffix___boxed(lean_object* v_env_84_, lean_object* v_declName_85_, lean_object* v_suffix_86_){
_start:
{
uint8_t v_res_87_; lean_object* v_r_88_; 
v_res_87_ = l_Lean_isAuxRecursorWithSuffix(v_env_84_, v_declName_85_, v_suffix_86_);
v_r_88_ = lean_box(v_res_87_);
return v_r_88_;
}
}
LEAN_EXPORT uint8_t l_Lean_isCasesOnRecursor(lean_object* v_env_89_, lean_object* v_declName_90_){
_start:
{
lean_object* v___x_91_; uint8_t v___x_92_; 
v___x_91_ = ((lean_object*)(l_Lean_casesOnSuffix___closed__0));
v___x_92_ = l_Lean_isAuxRecursorWithSuffix(v_env_89_, v_declName_90_, v___x_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_isCasesOnRecursor___boxed(lean_object* v_env_93_, lean_object* v_declName_94_){
_start:
{
uint8_t v_res_95_; lean_object* v_r_96_; 
v_res_95_ = l_Lean_isCasesOnRecursor(v_env_93_, v_declName_94_);
v_r_96_ = lean_box(v_res_95_);
return v_r_96_;
}
}
LEAN_EXPORT uint8_t l_Lean_isRecOnRecursor(lean_object* v_env_97_, lean_object* v_declName_98_){
_start:
{
lean_object* v___x_99_; uint8_t v___x_100_; 
v___x_99_ = ((lean_object*)(l_Lean_recOnSuffix___closed__0));
v___x_100_ = l_Lean_isAuxRecursorWithSuffix(v_env_97_, v_declName_98_, v___x_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRecOnRecursor___boxed(lean_object* v_env_101_, lean_object* v_declName_102_){
_start:
{
uint8_t v_res_103_; lean_object* v_r_104_; 
v_res_103_ = l_Lean_isRecOnRecursor(v_env_101_, v_declName_102_);
v_r_104_ = lean_box(v_res_103_);
return v_r_104_;
}
}
LEAN_EXPORT uint8_t l_Lean_isBRecOnRecursor(lean_object* v_env_105_, lean_object* v_declName_106_){
_start:
{
lean_object* v___x_107_; uint8_t v___x_108_; 
v___x_107_ = ((lean_object*)(l_Lean_brecOnSuffix___closed__0));
v___x_108_ = l_Lean_isAuxRecursorWithSuffix(v_env_105_, v_declName_106_, v___x_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_isBRecOnRecursor___boxed(lean_object* v_env_109_, lean_object* v_declName_110_){
_start:
{
uint8_t v_res_111_; lean_object* v_r_112_; 
v_res_111_ = l_Lean_isBRecOnRecursor(v_env_109_, v_declName_110_);
v_r_112_ = lean_box(v_res_111_);
return v_r_112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_163548097____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; uint8_t v___x_137_; lean_object* v___x_138_; 
v___x_135_ = ((lean_object*)(l___private_Lean_AuxRecursor_0__Lean_initFn___closed__8_00___x40_Lean_AuxRecursor_163548097____hygCtx___hyg_2_));
v___x_136_ = ((lean_object*)(l___private_Lean_AuxRecursor_0__Lean_initFn___closed__3_00___x40_Lean_AuxRecursor_4193738739____hygCtx___hyg_2_));
v___x_137_ = 1;
v___x_138_ = l_Lean_mkTagDeclarationExtension(v___x_135_, v___x_136_, v___x_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_163548097____hygCtx___hyg_2____boxed(lean_object* v_a_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l___private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_163548097____hygCtx___hyg_2_();
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_markSparseCasesOn(lean_object* v_env_141_, lean_object* v_declName_142_){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_143_ = l___private_Lean_AuxRecursor_0__Lean_sparseCasesOnExt;
v___x_144_ = l_Lean_TagDeclarationExtension_tag(v___x_143_, v_env_141_, v_declName_142_);
return v___x_144_;
}
}
LEAN_EXPORT uint8_t l_Lean_isSparseCasesOn(lean_object* v_env_145_, lean_object* v_declName_146_){
_start:
{
lean_object* v___x_147_; lean_object* v_toEnvExtension_148_; lean_object* v_asyncMode_149_; uint8_t v___x_150_; 
v___x_147_ = l___private_Lean_AuxRecursor_0__Lean_sparseCasesOnExt;
v_toEnvExtension_148_ = lean_ctor_get(v___x_147_, 0);
v_asyncMode_149_ = lean_ctor_get(v_toEnvExtension_148_, 2);
v___x_150_ = l_Lean_TagDeclarationExtension_isTagged(v___x_147_, v_env_145_, v_declName_146_, v_asyncMode_149_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_isSparseCasesOn___boxed(lean_object* v_env_151_, lean_object* v_declName_152_){
_start:
{
uint8_t v_res_153_; lean_object* v_r_154_; 
v_res_153_ = l_Lean_isSparseCasesOn(v_env_151_, v_declName_152_);
v_r_154_ = lean_box(v_res_153_);
return v_r_154_;
}
}
LEAN_EXPORT uint8_t l_Lean_isCasesOnLike(lean_object* v_env_155_, lean_object* v_declName_156_){
_start:
{
uint8_t v___x_157_; 
lean_inc(v_declName_156_);
lean_inc_ref(v_env_155_);
v___x_157_ = l_Lean_isCasesOnRecursor(v_env_155_, v_declName_156_);
if (v___x_157_ == 0)
{
uint8_t v___x_158_; 
v___x_158_ = l_Lean_isSparseCasesOn(v_env_155_, v_declName_156_);
return v___x_158_;
}
else
{
lean_dec(v_declName_156_);
lean_dec_ref(v_env_155_);
return v___x_157_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isCasesOnLike___boxed(lean_object* v_env_159_, lean_object* v_declName_160_){
_start:
{
uint8_t v_res_161_; lean_object* v_r_162_; 
v_res_161_ = l_Lean_isCasesOnLike(v_env_159_, v_declName_160_);
v_r_162_ = lean_box(v_res_161_);
return v_r_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_NoConfusionInfo_ctorIdx___impl(lean_object* v_x_163_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = lean_obj_tag_nat(v_x_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_NoConfusionInfo_ctorIdx___impl___boxed(lean_object* v_x_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Lean_NoConfusionInfo_ctorIdx___impl(v_x_165_);
lean_dec_ref(v_x_165_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_NoConfusionInfo_ctorElim___redArg(lean_object* v_t_167_, lean_object* v_k_168_){
_start:
{
if (lean_obj_tag(v_t_167_) == 0)
{
lean_object* v_arity_169_; lean_object* v_lhs_170_; lean_object* v_rhs_171_; lean_object* v___x_172_; 
v_arity_169_ = lean_ctor_get(v_t_167_, 0);
lean_inc(v_arity_169_);
v_lhs_170_ = lean_ctor_get(v_t_167_, 1);
lean_inc(v_lhs_170_);
v_rhs_171_ = lean_ctor_get(v_t_167_, 2);
lean_inc(v_rhs_171_);
lean_dec_ref_known(v_t_167_, 3);
v___x_172_ = lean_apply_3(v_k_168_, v_arity_169_, v_lhs_170_, v_rhs_171_);
return v___x_172_;
}
else
{
lean_object* v_arity_173_; lean_object* v_fields_174_; lean_object* v___x_175_; 
v_arity_173_ = lean_ctor_get(v_t_167_, 0);
lean_inc(v_arity_173_);
v_fields_174_ = lean_ctor_get(v_t_167_, 1);
lean_inc(v_fields_174_);
lean_dec_ref_known(v_t_167_, 2);
v___x_175_ = lean_apply_2(v_k_168_, v_arity_173_, v_fields_174_);
return v___x_175_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NoConfusionInfo_ctorElim(lean_object* v_motive_176_, lean_object* v_ctorIdx_177_, lean_object* v_t_178_, lean_object* v_h_179_, lean_object* v_k_180_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = l_Lean_NoConfusionInfo_ctorElim___redArg(v_t_178_, v_k_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_NoConfusionInfo_ctorElim___boxed(lean_object* v_motive_182_, lean_object* v_ctorIdx_183_, lean_object* v_t_184_, lean_object* v_h_185_, lean_object* v_k_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Lean_NoConfusionInfo_ctorElim(v_motive_182_, v_ctorIdx_183_, v_t_184_, v_h_185_, v_k_186_);
lean_dec(v_ctorIdx_183_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_NoConfusionInfo_regular_elim___redArg(lean_object* v_t_188_, lean_object* v_regular_189_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = l_Lean_NoConfusionInfo_ctorElim___redArg(v_t_188_, v_regular_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_NoConfusionInfo_regular_elim(lean_object* v_motive_191_, lean_object* v_t_192_, lean_object* v_h_193_, lean_object* v_regular_194_){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = l_Lean_NoConfusionInfo_ctorElim___redArg(v_t_192_, v_regular_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_NoConfusionInfo_perCtor_elim___redArg(lean_object* v_t_196_, lean_object* v_perCtor_197_){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = l_Lean_NoConfusionInfo_ctorElim___redArg(v_t_196_, v_perCtor_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_NoConfusionInfo_perCtor_elim(lean_object* v_motive_199_, lean_object* v_t_200_, lean_object* v_h_201_, lean_object* v_perCtor_202_){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = l_Lean_NoConfusionInfo_ctorElim___redArg(v_t_200_, v_perCtor_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_NoConfusionInfo_arity(lean_object* v_x_208_){
_start:
{
lean_object* v_arity_209_; 
v_arity_209_ = lean_ctor_get(v_x_208_, 0);
lean_inc(v_arity_209_);
return v_arity_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_NoConfusionInfo_arity___boxed(lean_object* v_x_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_Lean_NoConfusionInfo_arity(v_x_210_);
lean_dec_ref(v_x_210_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__2(lean_object* v_env_212_, lean_object* v_as_213_, size_t v_i_214_, size_t v_stop_215_, lean_object* v_b_216_){
_start:
{
lean_object* v___y_218_; uint8_t v___x_222_; 
v___x_222_ = lean_usize_dec_eq(v_i_214_, v_stop_215_);
if (v___x_222_ == 0)
{
lean_object* v___x_223_; lean_object* v_fst_224_; uint8_t v___x_225_; 
v___x_223_ = lean_array_uget_borrowed(v_as_213_, v_i_214_);
v_fst_224_ = lean_ctor_get(v___x_223_, 0);
lean_inc(v_fst_224_);
lean_inc_ref(v_env_212_);
v___x_225_ = l_Lean_Environment_contains(v_env_212_, v_fst_224_, v___x_222_);
if (v___x_225_ == 0)
{
v___y_218_ = v_b_216_;
goto v___jp_217_;
}
else
{
lean_object* v___x_226_; 
lean_inc(v___x_223_);
v___x_226_ = lean_array_push(v_b_216_, v___x_223_);
v___y_218_ = v___x_226_;
goto v___jp_217_;
}
}
else
{
lean_dec_ref(v_env_212_);
return v_b_216_;
}
v___jp_217_:
{
size_t v___x_219_; size_t v___x_220_; 
v___x_219_ = ((size_t)1ULL);
v___x_220_ = lean_usize_add(v_i_214_, v___x_219_);
v_i_214_ = v___x_220_;
v_b_216_ = v___y_218_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__2___boxed(lean_object* v_env_227_, lean_object* v_as_228_, lean_object* v_i_229_, lean_object* v_stop_230_, lean_object* v_b_231_){
_start:
{
size_t v_i_boxed_232_; size_t v_stop_boxed_233_; lean_object* v_res_234_; 
v_i_boxed_232_ = lean_unbox_usize(v_i_229_);
lean_dec(v_i_229_);
v_stop_boxed_233_ = lean_unbox_usize(v_stop_230_);
lean_dec(v_stop_230_);
v_res_234_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__2(v_env_227_, v_as_228_, v_i_boxed_232_, v_stop_boxed_233_, v_b_231_);
lean_dec_ref(v_as_228_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__1(lean_object* v_env_235_, lean_object* v_as_236_, size_t v_i_237_, size_t v_stop_238_, lean_object* v_b_239_){
_start:
{
lean_object* v___y_241_; uint8_t v___x_245_; 
v___x_245_ = lean_usize_dec_eq(v_i_237_, v_stop_238_);
if (v___x_245_ == 0)
{
lean_object* v___x_246_; lean_object* v_fst_247_; uint8_t v___x_248_; lean_object* v___x_249_; uint8_t v___x_250_; 
v___x_246_ = lean_array_uget_borrowed(v_as_236_, v_i_237_);
v_fst_247_ = lean_ctor_get(v___x_246_, 0);
v___x_248_ = 1;
lean_inc_ref(v_env_235_);
v___x_249_ = l_Lean_Environment_setExporting(v_env_235_, v___x_248_);
lean_inc(v_fst_247_);
v___x_250_ = l_Lean_Environment_contains(v___x_249_, v_fst_247_, v___x_245_);
if (v___x_250_ == 0)
{
v___y_241_ = v_b_239_;
goto v___jp_240_;
}
else
{
lean_object* v___x_251_; 
lean_inc(v___x_246_);
v___x_251_ = lean_array_push(v_b_239_, v___x_246_);
v___y_241_ = v___x_251_;
goto v___jp_240_;
}
}
else
{
lean_dec_ref(v_env_235_);
return v_b_239_;
}
v___jp_240_:
{
size_t v___x_242_; size_t v___x_243_; 
v___x_242_ = ((size_t)1ULL);
v___x_243_ = lean_usize_add(v_i_237_, v___x_242_);
v_i_237_ = v___x_243_;
v_b_239_ = v___y_241_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__1___boxed(lean_object* v_env_252_, lean_object* v_as_253_, lean_object* v_i_254_, lean_object* v_stop_255_, lean_object* v_b_256_){
_start:
{
size_t v_i_boxed_257_; size_t v_stop_boxed_258_; lean_object* v_res_259_; 
v_i_boxed_257_ = lean_unbox_usize(v_i_254_);
lean_dec(v_i_254_);
v_stop_boxed_258_ = lean_unbox_usize(v_stop_255_);
lean_dec(v_stop_255_);
v_res_259_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__1(v_env_252_, v_as_253_, v_i_boxed_257_, v_stop_boxed_258_, v_b_256_);
lean_dec_ref(v_as_253_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_260_, lean_object* v_x_261_){
_start:
{
if (lean_obj_tag(v_x_261_) == 0)
{
lean_object* v_k_262_; lean_object* v_v_263_; lean_object* v_l_264_; lean_object* v_r_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v_k_262_ = lean_ctor_get(v_x_261_, 1);
v_v_263_ = lean_ctor_get(v_x_261_, 2);
v_l_264_ = lean_ctor_get(v_x_261_, 3);
v_r_265_ = lean_ctor_get(v_x_261_, 4);
v___x_266_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__0_spec__0(v_init_260_, v_l_264_);
lean_inc(v_v_263_);
lean_inc(v_k_262_);
v___x_267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_267_, 0, v_k_262_);
lean_ctor_set(v___x_267_, 1, v_v_263_);
v___x_268_ = lean_array_push(v___x_266_, v___x_267_);
v_init_260_ = v___x_268_;
v_x_261_ = v_r_265_;
goto _start;
}
else
{
return v_init_260_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_270_, lean_object* v_x_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__0_spec__0(v_init_270_, v_x_271_);
lean_dec(v_x_271_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AuxRecursor_0__Lean_initFn___lam__0_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2_(lean_object* v_env_277_, lean_object* v_s_278_){
_start:
{
lean_object* v___x_279_; lean_object* v___y_281_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; uint8_t v___x_294_; 
v___x_279_ = lean_unsigned_to_nat(0u);
v___x_290_ = ((lean_object*)(l___private_Lean_AuxRecursor_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2_));
v___x_291_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__0_spec__0(v___x_290_, v_s_278_);
v___x_292_ = lean_array_get_size(v___x_291_);
v___x_293_ = ((lean_object*)(l___private_Lean_AuxRecursor_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2_));
v___x_294_ = lean_nat_dec_lt(v___x_279_, v___x_292_);
if (v___x_294_ == 0)
{
lean_dec_ref(v___x_291_);
v___y_281_ = v___x_293_;
goto v___jp_280_;
}
else
{
size_t v___x_295_; size_t v___x_296_; lean_object* v___x_297_; 
v___x_295_ = ((size_t)0ULL);
v___x_296_ = lean_usize_of_nat(v___x_292_);
lean_inc_ref(v_env_277_);
v___x_297_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__2(v_env_277_, v___x_291_, v___x_295_, v___x_296_, v___x_293_);
lean_dec_ref(v___x_291_);
v___y_281_ = v___x_297_;
goto v___jp_280_;
}
v___jp_280_:
{
lean_object* v___x_282_; lean_object* v___x_283_; uint8_t v___x_284_; 
v___x_282_ = lean_array_get_size(v___y_281_);
v___x_283_ = ((lean_object*)(l___private_Lean_AuxRecursor_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2_));
v___x_284_ = lean_nat_dec_lt(v___x_279_, v___x_282_);
if (v___x_284_ == 0)
{
lean_object* v___x_285_; 
lean_dec_ref(v_env_277_);
v___x_285_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_285_, 0, v___x_283_);
lean_ctor_set(v___x_285_, 1, v___x_283_);
lean_ctor_set(v___x_285_, 2, v___y_281_);
return v___x_285_;
}
else
{
size_t v___x_286_; size_t v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_286_ = ((size_t)0ULL);
v___x_287_ = lean_usize_of_nat(v___x_282_);
v___x_288_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__1(v_env_277_, v___y_281_, v___x_286_, v___x_287_, v___x_283_);
lean_inc_ref(v___x_288_);
v___x_289_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
lean_ctor_set(v___x_289_, 1, v___x_288_);
lean_ctor_set(v___x_289_, 2, v___y_281_);
return v___x_289_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AuxRecursor_0__Lean_initFn___lam__0_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2____boxed(lean_object* v_env_298_, lean_object* v_s_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l___private_Lean_AuxRecursor_0__Lean_initFn___lam__0_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2_(v_env_298_, v_s_299_);
lean_dec(v_s_299_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_307_; lean_object* v___x_308_; lean_object* v___x_309_; uint8_t v___x_310_; lean_object* v___x_311_; 
v___f_307_ = ((lean_object*)(l___private_Lean_AuxRecursor_0__Lean_initFn___closed__0_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2_));
v___x_308_ = ((lean_object*)(l___private_Lean_AuxRecursor_0__Lean_initFn___closed__2_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2_));
v___x_309_ = lean_box(2);
v___x_310_ = 1;
v___x_311_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_308_, v___x_309_, v___x_310_, v___f_307_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2____boxed(lean_object* v_a_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l___private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2_();
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__0(lean_object* v_init_314_, lean_object* v_t_315_){
_start:
{
lean_object* v___x_316_; 
v___x_316_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__0_spec__0(v_init_314_, v_t_315_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_317_, lean_object* v_t_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__0(v_init_317_, v_t_318_);
lean_dec(v_t_318_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_markNoConfusion(lean_object* v_env_320_, lean_object* v_n_321_, lean_object* v_info_322_){
_start:
{
lean_object* v___x_323_; uint8_t v___x_324_; lean_object* v___x_325_; 
v___x_323_ = l_Lean_noConfusionExt;
v___x_324_ = 0;
v___x_325_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_323_, v_env_320_, v_n_321_, v_info_322_, v___x_324_);
return v___x_325_;
}
}
LEAN_EXPORT uint8_t l_Lean_isNoConfusion(lean_object* v_env_326_, lean_object* v_n_327_){
_start:
{
lean_object* v___x_328_; lean_object* v_toEnvExtension_329_; lean_object* v_asyncMode_330_; lean_object* v___x_331_; uint8_t v___x_332_; 
v___x_328_ = l_Lean_noConfusionExt;
v_toEnvExtension_329_ = lean_ctor_get(v___x_328_, 0);
v_asyncMode_330_ = lean_ctor_get(v_toEnvExtension_329_, 2);
v___x_331_ = ((lean_object*)(l_Lean_instInhabitedNoConfusionInfo_default));
v___x_332_ = l_Lean_MapDeclarationExtension_contains___redArg(v___x_331_, v___x_328_, v_env_326_, v_n_327_, v_asyncMode_330_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_isNoConfusion___boxed(lean_object* v_env_333_, lean_object* v_n_334_){
_start:
{
uint8_t v_res_335_; lean_object* v_r_336_; 
v_res_335_ = l_Lean_isNoConfusion(v_env_333_, v_n_334_);
v_r_336_ = lean_box(v_res_335_);
return v_r_336_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getNoConfusionInfo_spec__0(lean_object* v_msg_337_){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_338_ = ((lean_object*)(l_Lean_instInhabitedNoConfusionInfo_default));
v___x_339_ = lean_panic_fn_borrowed(v___x_338_, v_msg_337_);
return v___x_339_;
}
}
static lean_object* _init_l_Lean_getNoConfusionInfo___closed__3(void){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_343_ = ((lean_object*)(l_Lean_getNoConfusionInfo___closed__2));
v___x_344_ = lean_unsigned_to_nat(14u);
v___x_345_ = lean_unsigned_to_nat(22u);
v___x_346_ = ((lean_object*)(l_Lean_getNoConfusionInfo___closed__1));
v___x_347_ = ((lean_object*)(l_Lean_getNoConfusionInfo___closed__0));
v___x_348_ = l_mkPanicMessageWithDecl(v___x_347_, v___x_346_, v___x_345_, v___x_344_, v___x_343_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_getNoConfusionInfo(lean_object* v_env_349_, lean_object* v_n_350_){
_start:
{
lean_object* v___x_351_; lean_object* v_toEnvExtension_352_; lean_object* v_asyncMode_353_; lean_object* v___x_354_; uint8_t v___x_355_; lean_object* v___x_356_; 
v___x_351_ = l_Lean_noConfusionExt;
v_toEnvExtension_352_ = lean_ctor_get(v___x_351_, 0);
v_asyncMode_353_ = lean_ctor_get(v_toEnvExtension_352_, 2);
v___x_354_ = ((lean_object*)(l_Lean_instInhabitedNoConfusionInfo_default));
v___x_355_ = 0;
v___x_356_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_354_, v___x_351_, v_env_349_, v_n_350_, v_asyncMode_353_, v___x_355_);
if (lean_obj_tag(v___x_356_) == 0)
{
lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_357_ = lean_obj_once(&l_Lean_getNoConfusionInfo___closed__3, &l_Lean_getNoConfusionInfo___closed__3_once, _init_l_Lean_getNoConfusionInfo___closed__3);
v___x_358_ = l_panic___at___00Lean_getNoConfusionInfo_spec__0(v___x_357_);
return v___x_358_;
}
else
{
lean_object* v_val_359_; 
v_val_359_ = lean_ctor_get(v___x_356_, 0);
lean_inc(v_val_359_);
lean_dec_ref_known(v___x_356_, 1);
return v_val_359_;
}
}
}
lean_object* runtime_initialize_Lean_EnvExtension(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_AuxRecursor(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_EnvExtension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_4193738739____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_auxRecExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_auxRecExt);
lean_dec_ref(res);
res = l___private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_163548097____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_AuxRecursor_0__Lean_sparseCasesOnExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_AuxRecursor_0__Lean_sparseCasesOnExt);
lean_dec_ref(res);
res = l___private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_noConfusionExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_noConfusionExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_AuxRecursor(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_EnvExtension(uint8_t builtin);
lean_object* initialize_Init_Data_String_TakeDrop(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_AuxRecursor(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_EnvExtension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_AuxRecursor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_AuxRecursor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_AuxRecursor(builtin);
}
#ifdef __cplusplus
}
#endif

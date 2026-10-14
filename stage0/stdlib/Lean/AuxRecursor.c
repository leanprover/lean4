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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_isAuxRecursor___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "ndrec_symm"};
static const lean_object* l_Lean_isAuxRecursor___closed__1 = (const lean_object*)&l_Lean_isAuxRecursor___closed__1_value;
static const lean_ctor_object l_Lean_isAuxRecursor___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isAuxRecursor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_isAuxRecursor___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_isAuxRecursor___closed__2_value_aux_0),((lean_object*)&l_Lean_isAuxRecursor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(71, 160, 179, 99, 219, 64, 47, 167)}};
static const lean_object* l_Lean_isAuxRecursor___closed__2 = (const lean_object*)&l_Lean_isAuxRecursor___closed__2_value;
static const lean_string_object l_Lean_isAuxRecursor___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ndrecOn"};
static const lean_object* l_Lean_isAuxRecursor___closed__3 = (const lean_object*)&l_Lean_isAuxRecursor___closed__3_value;
static const lean_ctor_object l_Lean_isAuxRecursor___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isAuxRecursor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_isAuxRecursor___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_isAuxRecursor___closed__4_value_aux_0),((lean_object*)&l_Lean_isAuxRecursor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(74, 212, 24, 249, 139, 157, 15, 213)}};
static const lean_object* l_Lean_isAuxRecursor___closed__4 = (const lean_object*)&l_Lean_isAuxRecursor___closed__4_value;
static const lean_string_object l_Lean_isAuxRecursor___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ndrec"};
static const lean_object* l_Lean_isAuxRecursor___closed__5 = (const lean_object*)&l_Lean_isAuxRecursor___closed__5_value;
static const lean_ctor_object l_Lean_isAuxRecursor___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isAuxRecursor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_isAuxRecursor___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_isAuxRecursor___closed__6_value_aux_0),((lean_object*)&l_Lean_isAuxRecursor___closed__5_value),LEAN_SCALAR_PTR_LITERAL(115, 164, 251, 202, 217, 58, 77, 179)}};
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
uint8_t v___y_55_; lean_object* v___x_60_; lean_object* v_toEnvExtension_61_; lean_object* v_asyncMode_62_; uint8_t v___x_63_; 
v___x_60_ = l_Lean_auxRecExt;
v_toEnvExtension_61_ = lean_ctor_get(v___x_60_, 0);
v_asyncMode_62_ = lean_ctor_get(v_toEnvExtension_61_, 2);
lean_inc(v_declName_53_);
v___x_63_ = l_Lean_TagDeclarationExtension_isTagged(v___x_60_, v_env_52_, v_declName_53_, v_asyncMode_62_);
if (v___x_63_ == 0)
{
lean_object* v___x_64_; uint8_t v___x_65_; 
v___x_64_ = ((lean_object*)(l_Lean_isAuxRecursor___closed__6));
v___x_65_ = lean_name_eq(v_declName_53_, v___x_64_);
v___y_55_ = v___x_65_;
goto v___jp_54_;
}
else
{
v___y_55_ = v___x_63_;
goto v___jp_54_;
}
v___jp_54_:
{
if (v___y_55_ == 0)
{
lean_object* v___x_56_; uint8_t v___x_57_; 
v___x_56_ = ((lean_object*)(l_Lean_isAuxRecursor___closed__2));
v___x_57_ = lean_name_eq(v_declName_53_, v___x_56_);
if (v___x_57_ == 0)
{
lean_object* v___x_58_; uint8_t v___x_59_; 
v___x_58_ = ((lean_object*)(l_Lean_isAuxRecursor___closed__4));
v___x_59_ = lean_name_eq(v_declName_53_, v___x_58_);
lean_dec(v_declName_53_);
return v___x_59_;
}
else
{
lean_dec(v_declName_53_);
return v___x_57_;
}
}
else
{
lean_dec(v_declName_53_);
return v___y_55_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isAuxRecursor___boxed(lean_object* v_env_66_, lean_object* v_declName_67_){
_start:
{
uint8_t v_res_68_; lean_object* v_r_69_; 
v_res_68_ = l_Lean_isAuxRecursor(v_env_66_, v_declName_67_);
v_r_69_ = lean_box(v_res_68_);
return v_r_69_;
}
}
LEAN_EXPORT uint8_t l_Lean_isAuxRecursorWithSuffix(lean_object* v_env_71_, lean_object* v_declName_72_, lean_object* v_suffix_73_){
_start:
{
if (lean_obj_tag(v_declName_72_) == 1)
{
lean_object* v_str_74_; uint8_t v___x_75_; 
v_str_74_ = lean_ctor_get(v_declName_72_, 1);
v___x_75_ = lean_string_dec_eq(v_str_74_, v_suffix_73_);
if (v___x_75_ == 0)
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; uint8_t v___x_80_; 
v___x_76_ = ((lean_object*)(l_Lean_isAuxRecursorWithSuffix___closed__0));
v___x_77_ = lean_string_append(v_suffix_73_, v___x_76_);
v___x_78_ = lean_string_utf8_byte_size(v_str_74_);
v___x_79_ = lean_string_utf8_byte_size(v___x_77_);
v___x_80_ = lean_nat_dec_le(v___x_79_, v___x_78_);
if (v___x_80_ == 0)
{
lean_dec_ref(v___x_77_);
lean_dec_ref_known(v_declName_72_, 2);
lean_dec_ref(v_env_71_);
return v___x_80_;
}
else
{
lean_object* v___x_81_; uint8_t v___x_82_; 
v___x_81_ = lean_unsigned_to_nat(0u);
v___x_82_ = lean_string_memcmp(v_str_74_, v___x_77_, v___x_81_, v___x_81_, v___x_79_);
lean_dec_ref(v___x_77_);
if (v___x_82_ == 0)
{
lean_dec_ref_known(v_declName_72_, 2);
lean_dec_ref(v_env_71_);
return v___x_82_;
}
else
{
uint8_t v___x_83_; 
v___x_83_ = l_Lean_isAuxRecursor(v_env_71_, v_declName_72_);
return v___x_83_;
}
}
}
else
{
uint8_t v___x_84_; 
lean_dec_ref(v_suffix_73_);
v___x_84_ = l_Lean_isAuxRecursor(v_env_71_, v_declName_72_);
return v___x_84_;
}
}
else
{
uint8_t v___x_85_; 
lean_dec_ref(v_suffix_73_);
lean_dec(v_declName_72_);
lean_dec_ref(v_env_71_);
v___x_85_ = 0;
return v___x_85_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isAuxRecursorWithSuffix___boxed(lean_object* v_env_86_, lean_object* v_declName_87_, lean_object* v_suffix_88_){
_start:
{
uint8_t v_res_89_; lean_object* v_r_90_; 
v_res_89_ = l_Lean_isAuxRecursorWithSuffix(v_env_86_, v_declName_87_, v_suffix_88_);
v_r_90_ = lean_box(v_res_89_);
return v_r_90_;
}
}
LEAN_EXPORT uint8_t l_Lean_isCasesOnRecursor(lean_object* v_env_91_, lean_object* v_declName_92_){
_start:
{
lean_object* v___x_93_; uint8_t v___x_94_; 
v___x_93_ = ((lean_object*)(l_Lean_casesOnSuffix___closed__0));
v___x_94_ = l_Lean_isAuxRecursorWithSuffix(v_env_91_, v_declName_92_, v___x_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_isCasesOnRecursor___boxed(lean_object* v_env_95_, lean_object* v_declName_96_){
_start:
{
uint8_t v_res_97_; lean_object* v_r_98_; 
v_res_97_ = l_Lean_isCasesOnRecursor(v_env_95_, v_declName_96_);
v_r_98_ = lean_box(v_res_97_);
return v_r_98_;
}
}
LEAN_EXPORT uint8_t l_Lean_isRecOnRecursor(lean_object* v_env_99_, lean_object* v_declName_100_){
_start:
{
lean_object* v___x_101_; uint8_t v___x_102_; 
v___x_101_ = ((lean_object*)(l_Lean_recOnSuffix___closed__0));
v___x_102_ = l_Lean_isAuxRecursorWithSuffix(v_env_99_, v_declName_100_, v___x_101_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRecOnRecursor___boxed(lean_object* v_env_103_, lean_object* v_declName_104_){
_start:
{
uint8_t v_res_105_; lean_object* v_r_106_; 
v_res_105_ = l_Lean_isRecOnRecursor(v_env_103_, v_declName_104_);
v_r_106_ = lean_box(v_res_105_);
return v_r_106_;
}
}
LEAN_EXPORT uint8_t l_Lean_isBRecOnRecursor(lean_object* v_env_107_, lean_object* v_declName_108_){
_start:
{
lean_object* v___x_109_; uint8_t v___x_110_; 
v___x_109_ = ((lean_object*)(l_Lean_brecOnSuffix___closed__0));
v___x_110_ = l_Lean_isAuxRecursorWithSuffix(v_env_107_, v_declName_108_, v___x_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_isBRecOnRecursor___boxed(lean_object* v_env_111_, lean_object* v_declName_112_){
_start:
{
uint8_t v_res_113_; lean_object* v_r_114_; 
v_res_113_ = l_Lean_isBRecOnRecursor(v_env_111_, v_declName_112_);
v_r_114_ = lean_box(v_res_113_);
return v_r_114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_163548097____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; uint8_t v___x_139_; lean_object* v___x_140_; 
v___x_137_ = ((lean_object*)(l___private_Lean_AuxRecursor_0__Lean_initFn___closed__8_00___x40_Lean_AuxRecursor_163548097____hygCtx___hyg_2_));
v___x_138_ = ((lean_object*)(l___private_Lean_AuxRecursor_0__Lean_initFn___closed__3_00___x40_Lean_AuxRecursor_4193738739____hygCtx___hyg_2_));
v___x_139_ = 1;
v___x_140_ = l_Lean_mkTagDeclarationExtension(v___x_137_, v___x_138_, v___x_139_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_163548097____hygCtx___hyg_2____boxed(lean_object* v_a_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l___private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_163548097____hygCtx___hyg_2_();
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_markSparseCasesOn(lean_object* v_env_143_, lean_object* v_declName_144_){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_145_ = l___private_Lean_AuxRecursor_0__Lean_sparseCasesOnExt;
v___x_146_ = l_Lean_TagDeclarationExtension_tag(v___x_145_, v_env_143_, v_declName_144_);
return v___x_146_;
}
}
LEAN_EXPORT uint8_t l_Lean_isSparseCasesOn(lean_object* v_env_147_, lean_object* v_declName_148_){
_start:
{
lean_object* v___x_149_; lean_object* v_toEnvExtension_150_; lean_object* v_asyncMode_151_; uint8_t v___x_152_; 
v___x_149_ = l___private_Lean_AuxRecursor_0__Lean_sparseCasesOnExt;
v_toEnvExtension_150_ = lean_ctor_get(v___x_149_, 0);
v_asyncMode_151_ = lean_ctor_get(v_toEnvExtension_150_, 2);
v___x_152_ = l_Lean_TagDeclarationExtension_isTagged(v___x_149_, v_env_147_, v_declName_148_, v_asyncMode_151_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_isSparseCasesOn___boxed(lean_object* v_env_153_, lean_object* v_declName_154_){
_start:
{
uint8_t v_res_155_; lean_object* v_r_156_; 
v_res_155_ = l_Lean_isSparseCasesOn(v_env_153_, v_declName_154_);
v_r_156_ = lean_box(v_res_155_);
return v_r_156_;
}
}
LEAN_EXPORT uint8_t l_Lean_isCasesOnLike(lean_object* v_env_157_, lean_object* v_declName_158_){
_start:
{
uint8_t v___x_159_; 
lean_inc(v_declName_158_);
lean_inc_ref(v_env_157_);
v___x_159_ = l_Lean_isCasesOnRecursor(v_env_157_, v_declName_158_);
if (v___x_159_ == 0)
{
uint8_t v___x_160_; 
v___x_160_ = l_Lean_isSparseCasesOn(v_env_157_, v_declName_158_);
return v___x_160_;
}
else
{
lean_dec(v_declName_158_);
lean_dec_ref(v_env_157_);
return v___x_159_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isCasesOnLike___boxed(lean_object* v_env_161_, lean_object* v_declName_162_){
_start:
{
uint8_t v_res_163_; lean_object* v_r_164_; 
v_res_163_ = l_Lean_isCasesOnLike(v_env_161_, v_declName_162_);
v_r_164_ = lean_box(v_res_163_);
return v_r_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_NoConfusionInfo_ctorIdx___impl(lean_object* v_x_165_){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = lean_obj_tag_nat(v_x_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_NoConfusionInfo_ctorIdx___impl___boxed(lean_object* v_x_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Lean_NoConfusionInfo_ctorIdx___impl(v_x_167_);
lean_dec_ref(v_x_167_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_NoConfusionInfo_ctorElim___redArg(lean_object* v_t_169_, lean_object* v_k_170_){
_start:
{
if (lean_obj_tag(v_t_169_) == 0)
{
lean_object* v_arity_171_; lean_object* v_lhs_172_; lean_object* v_rhs_173_; lean_object* v___x_174_; 
v_arity_171_ = lean_ctor_get(v_t_169_, 0);
lean_inc(v_arity_171_);
v_lhs_172_ = lean_ctor_get(v_t_169_, 1);
lean_inc(v_lhs_172_);
v_rhs_173_ = lean_ctor_get(v_t_169_, 2);
lean_inc(v_rhs_173_);
lean_dec_ref_known(v_t_169_, 3);
v___x_174_ = lean_apply_3(v_k_170_, v_arity_171_, v_lhs_172_, v_rhs_173_);
return v___x_174_;
}
else
{
lean_object* v_arity_175_; lean_object* v_fields_176_; lean_object* v___x_177_; 
v_arity_175_ = lean_ctor_get(v_t_169_, 0);
lean_inc(v_arity_175_);
v_fields_176_ = lean_ctor_get(v_t_169_, 1);
lean_inc(v_fields_176_);
lean_dec_ref_known(v_t_169_, 2);
v___x_177_ = lean_apply_2(v_k_170_, v_arity_175_, v_fields_176_);
return v___x_177_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NoConfusionInfo_ctorElim(lean_object* v_motive_178_, lean_object* v_ctorIdx_179_, lean_object* v_t_180_, lean_object* v_h_181_, lean_object* v_k_182_){
_start:
{
lean_object* v___x_183_; 
v___x_183_ = l_Lean_NoConfusionInfo_ctorElim___redArg(v_t_180_, v_k_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_NoConfusionInfo_ctorElim___boxed(lean_object* v_motive_184_, lean_object* v_ctorIdx_185_, lean_object* v_t_186_, lean_object* v_h_187_, lean_object* v_k_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_Lean_NoConfusionInfo_ctorElim(v_motive_184_, v_ctorIdx_185_, v_t_186_, v_h_187_, v_k_188_);
lean_dec(v_ctorIdx_185_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_NoConfusionInfo_regular_elim___redArg(lean_object* v_t_190_, lean_object* v_regular_191_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = l_Lean_NoConfusionInfo_ctorElim___redArg(v_t_190_, v_regular_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_NoConfusionInfo_regular_elim(lean_object* v_motive_193_, lean_object* v_t_194_, lean_object* v_h_195_, lean_object* v_regular_196_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = l_Lean_NoConfusionInfo_ctorElim___redArg(v_t_194_, v_regular_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_NoConfusionInfo_perCtor_elim___redArg(lean_object* v_t_198_, lean_object* v_perCtor_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = l_Lean_NoConfusionInfo_ctorElim___redArg(v_t_198_, v_perCtor_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_NoConfusionInfo_perCtor_elim(lean_object* v_motive_201_, lean_object* v_t_202_, lean_object* v_h_203_, lean_object* v_perCtor_204_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l_Lean_NoConfusionInfo_ctorElim___redArg(v_t_202_, v_perCtor_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_NoConfusionInfo_arity(lean_object* v_x_210_){
_start:
{
lean_object* v_arity_211_; 
v_arity_211_ = lean_ctor_get(v_x_210_, 0);
lean_inc(v_arity_211_);
return v_arity_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_NoConfusionInfo_arity___boxed(lean_object* v_x_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Lean_NoConfusionInfo_arity(v_x_212_);
lean_dec_ref(v_x_212_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__2(lean_object* v_env_214_, lean_object* v_as_215_, size_t v_i_216_, size_t v_stop_217_, lean_object* v_b_218_){
_start:
{
lean_object* v___y_220_; uint8_t v___x_224_; 
v___x_224_ = lean_usize_dec_eq(v_i_216_, v_stop_217_);
if (v___x_224_ == 0)
{
lean_object* v___x_225_; lean_object* v_fst_226_; uint8_t v___x_227_; 
v___x_225_ = lean_array_uget_borrowed(v_as_215_, v_i_216_);
v_fst_226_ = lean_ctor_get(v___x_225_, 0);
lean_inc(v_fst_226_);
lean_inc_ref(v_env_214_);
v___x_227_ = l_Lean_Environment_contains(v_env_214_, v_fst_226_, v___x_224_);
if (v___x_227_ == 0)
{
v___y_220_ = v_b_218_;
goto v___jp_219_;
}
else
{
lean_object* v___x_228_; 
lean_inc(v___x_225_);
v___x_228_ = lean_array_push(v_b_218_, v___x_225_);
v___y_220_ = v___x_228_;
goto v___jp_219_;
}
}
else
{
lean_dec_ref(v_env_214_);
return v_b_218_;
}
v___jp_219_:
{
size_t v___x_221_; size_t v___x_222_; 
v___x_221_ = ((size_t)1ULL);
v___x_222_ = lean_usize_add(v_i_216_, v___x_221_);
v_i_216_ = v___x_222_;
v_b_218_ = v___y_220_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__2___boxed(lean_object* v_env_229_, lean_object* v_as_230_, lean_object* v_i_231_, lean_object* v_stop_232_, lean_object* v_b_233_){
_start:
{
size_t v_i_boxed_234_; size_t v_stop_boxed_235_; lean_object* v_res_236_; 
v_i_boxed_234_ = lean_unbox_usize(v_i_231_);
lean_dec(v_i_231_);
v_stop_boxed_235_ = lean_unbox_usize(v_stop_232_);
lean_dec(v_stop_232_);
v_res_236_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__2(v_env_229_, v_as_230_, v_i_boxed_234_, v_stop_boxed_235_, v_b_233_);
lean_dec_ref(v_as_230_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__1(lean_object* v_env_237_, lean_object* v_as_238_, size_t v_i_239_, size_t v_stop_240_, lean_object* v_b_241_){
_start:
{
lean_object* v___y_243_; uint8_t v___x_247_; 
v___x_247_ = lean_usize_dec_eq(v_i_239_, v_stop_240_);
if (v___x_247_ == 0)
{
lean_object* v___x_248_; lean_object* v_fst_249_; uint8_t v___x_250_; lean_object* v___x_251_; uint8_t v___x_252_; 
v___x_248_ = lean_array_uget_borrowed(v_as_238_, v_i_239_);
v_fst_249_ = lean_ctor_get(v___x_248_, 0);
v___x_250_ = 1;
lean_inc_ref(v_env_237_);
v___x_251_ = l_Lean_Environment_setExporting(v_env_237_, v___x_250_);
lean_inc(v_fst_249_);
v___x_252_ = l_Lean_Environment_contains(v___x_251_, v_fst_249_, v___x_250_);
if (v___x_252_ == 0)
{
v___y_243_ = v_b_241_;
goto v___jp_242_;
}
else
{
lean_object* v___x_253_; 
lean_inc(v___x_248_);
v___x_253_ = lean_array_push(v_b_241_, v___x_248_);
v___y_243_ = v___x_253_;
goto v___jp_242_;
}
}
else
{
lean_dec_ref(v_env_237_);
return v_b_241_;
}
v___jp_242_:
{
size_t v___x_244_; size_t v___x_245_; 
v___x_244_ = ((size_t)1ULL);
v___x_245_ = lean_usize_add(v_i_239_, v___x_244_);
v_i_239_ = v___x_245_;
v_b_241_ = v___y_243_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__1___boxed(lean_object* v_env_254_, lean_object* v_as_255_, lean_object* v_i_256_, lean_object* v_stop_257_, lean_object* v_b_258_){
_start:
{
size_t v_i_boxed_259_; size_t v_stop_boxed_260_; lean_object* v_res_261_; 
v_i_boxed_259_ = lean_unbox_usize(v_i_256_);
lean_dec(v_i_256_);
v_stop_boxed_260_ = lean_unbox_usize(v_stop_257_);
lean_dec(v_stop_257_);
v_res_261_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__1(v_env_254_, v_as_255_, v_i_boxed_259_, v_stop_boxed_260_, v_b_258_);
lean_dec_ref(v_as_255_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_262_, lean_object* v_x_263_){
_start:
{
if (lean_obj_tag(v_x_263_) == 0)
{
lean_object* v_k_264_; lean_object* v_v_265_; lean_object* v_l_266_; lean_object* v_r_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v_k_264_ = lean_ctor_get(v_x_263_, 1);
v_v_265_ = lean_ctor_get(v_x_263_, 2);
v_l_266_ = lean_ctor_get(v_x_263_, 3);
v_r_267_ = lean_ctor_get(v_x_263_, 4);
v___x_268_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__0_spec__0(v_init_262_, v_l_266_);
lean_inc(v_v_265_);
lean_inc(v_k_264_);
v___x_269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_269_, 0, v_k_264_);
lean_ctor_set(v___x_269_, 1, v_v_265_);
v___x_270_ = lean_array_push(v___x_268_, v___x_269_);
v_init_262_ = v___x_270_;
v_x_263_ = v_r_267_;
goto _start;
}
else
{
return v_init_262_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_272_, lean_object* v_x_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__0_spec__0(v_init_272_, v_x_273_);
lean_dec(v_x_273_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AuxRecursor_0__Lean_initFn___lam__0_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2_(lean_object* v_env_279_, lean_object* v_s_280_){
_start:
{
lean_object* v___x_281_; lean_object* v___y_283_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; uint8_t v___x_302_; 
v___x_281_ = lean_unsigned_to_nat(0u);
v___x_298_ = ((lean_object*)(l___private_Lean_AuxRecursor_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2_));
v___x_299_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__0_spec__0(v___x_298_, v_s_280_);
v___x_300_ = lean_array_get_size(v___x_299_);
v___x_301_ = ((lean_object*)(l___private_Lean_AuxRecursor_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2_));
v___x_302_ = lean_nat_dec_lt(v___x_281_, v___x_300_);
if (v___x_302_ == 0)
{
lean_dec_ref(v___x_299_);
v___y_283_ = v___x_301_;
goto v___jp_282_;
}
else
{
uint8_t v___x_303_; 
v___x_303_ = lean_nat_dec_le(v___x_300_, v___x_300_);
if (v___x_303_ == 0)
{
if (v___x_302_ == 0)
{
lean_dec_ref(v___x_299_);
v___y_283_ = v___x_301_;
goto v___jp_282_;
}
else
{
size_t v___x_304_; size_t v___x_305_; lean_object* v___x_306_; 
v___x_304_ = ((size_t)0ULL);
v___x_305_ = lean_usize_of_nat(v___x_300_);
lean_inc_ref(v_env_279_);
v___x_306_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__2(v_env_279_, v___x_299_, v___x_304_, v___x_305_, v___x_301_);
lean_dec_ref(v___x_299_);
v___y_283_ = v___x_306_;
goto v___jp_282_;
}
}
else
{
size_t v___x_307_; size_t v___x_308_; lean_object* v___x_309_; 
v___x_307_ = ((size_t)0ULL);
v___x_308_ = lean_usize_of_nat(v___x_300_);
lean_inc_ref(v_env_279_);
v___x_309_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__2(v_env_279_, v___x_299_, v___x_307_, v___x_308_, v___x_301_);
lean_dec_ref(v___x_299_);
v___y_283_ = v___x_309_;
goto v___jp_282_;
}
}
v___jp_282_:
{
lean_object* v___x_284_; lean_object* v___x_285_; uint8_t v___x_286_; 
v___x_284_ = lean_array_get_size(v___y_283_);
v___x_285_ = ((lean_object*)(l___private_Lean_AuxRecursor_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2_));
v___x_286_ = lean_nat_dec_lt(v___x_281_, v___x_284_);
if (v___x_286_ == 0)
{
lean_object* v___x_287_; 
lean_dec_ref(v_env_279_);
v___x_287_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_287_, 0, v___x_285_);
lean_ctor_set(v___x_287_, 1, v___x_285_);
lean_ctor_set(v___x_287_, 2, v___y_283_);
return v___x_287_;
}
else
{
uint8_t v___x_288_; 
v___x_288_ = lean_nat_dec_le(v___x_284_, v___x_284_);
if (v___x_288_ == 0)
{
if (v___x_286_ == 0)
{
lean_object* v___x_289_; 
lean_dec_ref(v_env_279_);
v___x_289_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_289_, 0, v___x_285_);
lean_ctor_set(v___x_289_, 1, v___x_285_);
lean_ctor_set(v___x_289_, 2, v___y_283_);
return v___x_289_;
}
else
{
size_t v___x_290_; size_t v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_290_ = ((size_t)0ULL);
v___x_291_ = lean_usize_of_nat(v___x_284_);
v___x_292_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__1(v_env_279_, v___y_283_, v___x_290_, v___x_291_, v___x_285_);
lean_inc_ref(v___x_292_);
v___x_293_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_293_, 0, v___x_292_);
lean_ctor_set(v___x_293_, 1, v___x_292_);
lean_ctor_set(v___x_293_, 2, v___y_283_);
return v___x_293_;
}
}
else
{
size_t v___x_294_; size_t v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_294_ = ((size_t)0ULL);
v___x_295_ = lean_usize_of_nat(v___x_284_);
v___x_296_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__1(v_env_279_, v___y_283_, v___x_294_, v___x_295_, v___x_285_);
lean_inc_ref(v___x_296_);
v___x_297_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
lean_ctor_set(v___x_297_, 1, v___x_296_);
lean_ctor_set(v___x_297_, 2, v___y_283_);
return v___x_297_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AuxRecursor_0__Lean_initFn___lam__0_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2____boxed(lean_object* v_env_310_, lean_object* v_s_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l___private_Lean_AuxRecursor_0__Lean_initFn___lam__0_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2_(v_env_310_, v_s_311_);
lean_dec(v_s_311_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_319_; lean_object* v___x_320_; lean_object* v___x_321_; uint8_t v___x_322_; lean_object* v___x_323_; 
v___f_319_ = ((lean_object*)(l___private_Lean_AuxRecursor_0__Lean_initFn___closed__0_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2_));
v___x_320_ = ((lean_object*)(l___private_Lean_AuxRecursor_0__Lean_initFn___closed__2_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2_));
v___x_321_ = lean_box(2);
v___x_322_ = 1;
v___x_323_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_320_, v___x_321_, v___x_322_, v___f_319_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2____boxed(lean_object* v_a_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l___private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2_();
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__0(lean_object* v_init_326_, lean_object* v_t_327_){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__0_spec__0(v_init_326_, v_t_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_329_, lean_object* v_t_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__0(v_init_329_, v_t_330_);
lean_dec(v_t_330_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_markNoConfusion(lean_object* v_env_332_, lean_object* v_n_333_, lean_object* v_info_334_){
_start:
{
lean_object* v___x_335_; uint8_t v___x_336_; lean_object* v___x_337_; 
v___x_335_ = l_Lean_noConfusionExt;
v___x_336_ = 0;
v___x_337_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_335_, v_env_332_, v_n_333_, v_info_334_, v___x_336_);
return v___x_337_;
}
}
LEAN_EXPORT uint8_t l_Lean_isNoConfusion(lean_object* v_env_338_, lean_object* v_n_339_){
_start:
{
lean_object* v___x_340_; lean_object* v_toEnvExtension_341_; lean_object* v_asyncMode_342_; lean_object* v___x_343_; uint8_t v___x_344_; 
v___x_340_ = l_Lean_noConfusionExt;
v_toEnvExtension_341_ = lean_ctor_get(v___x_340_, 0);
v_asyncMode_342_ = lean_ctor_get(v_toEnvExtension_341_, 2);
v___x_343_ = ((lean_object*)(l_Lean_instInhabitedNoConfusionInfo_default));
v___x_344_ = l_Lean_MapDeclarationExtension_contains___redArg(v___x_343_, v___x_340_, v_env_338_, v_n_339_, v_asyncMode_342_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_isNoConfusion___boxed(lean_object* v_env_345_, lean_object* v_n_346_){
_start:
{
uint8_t v_res_347_; lean_object* v_r_348_; 
v_res_347_ = l_Lean_isNoConfusion(v_env_345_, v_n_346_);
v_r_348_ = lean_box(v_res_347_);
return v_r_348_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getNoConfusionInfo_spec__0(lean_object* v_msg_349_){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = ((lean_object*)(l_Lean_instInhabitedNoConfusionInfo_default));
v___x_351_ = lean_panic_fn_borrowed(v___x_350_, v_msg_349_);
return v___x_351_;
}
}
static lean_object* _init_l_Lean_getNoConfusionInfo___closed__3(void){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_355_ = ((lean_object*)(l_Lean_getNoConfusionInfo___closed__2));
v___x_356_ = lean_unsigned_to_nat(14u);
v___x_357_ = lean_unsigned_to_nat(22u);
v___x_358_ = ((lean_object*)(l_Lean_getNoConfusionInfo___closed__1));
v___x_359_ = ((lean_object*)(l_Lean_getNoConfusionInfo___closed__0));
v___x_360_ = l_mkPanicMessageWithDecl(v___x_359_, v___x_358_, v___x_357_, v___x_356_, v___x_355_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_getNoConfusionInfo(lean_object* v_env_361_, lean_object* v_n_362_){
_start:
{
lean_object* v___x_363_; lean_object* v_toEnvExtension_364_; lean_object* v_asyncMode_365_; lean_object* v___x_366_; uint8_t v___x_367_; lean_object* v___x_368_; 
v___x_363_ = l_Lean_noConfusionExt;
v_toEnvExtension_364_ = lean_ctor_get(v___x_363_, 0);
v_asyncMode_365_ = lean_ctor_get(v_toEnvExtension_364_, 2);
v___x_366_ = ((lean_object*)(l_Lean_instInhabitedNoConfusionInfo_default));
v___x_367_ = 0;
v___x_368_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_366_, v___x_363_, v_env_361_, v_n_362_, v_asyncMode_365_, v___x_367_);
if (lean_obj_tag(v___x_368_) == 0)
{
lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_369_ = lean_obj_once(&l_Lean_getNoConfusionInfo___closed__3, &l_Lean_getNoConfusionInfo___closed__3_once, _init_l_Lean_getNoConfusionInfo___closed__3);
v___x_370_ = l_panic___at___00Lean_getNoConfusionInfo_spec__0(v___x_369_);
return v___x_370_;
}
else
{
lean_object* v_val_371_; 
v_val_371_ = lean_ctor_get(v___x_368_, 0);
lean_inc(v_val_371_);
lean_dec_ref_known(v___x_368_, 1);
return v_val_371_;
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

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
lean_object* l___private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_4193738739____hygCtx___hyg_2_(){
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
LEAN_EXPORT void l___private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_4193738739____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_33_;
v_res_33_ = l___private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_4193738739____hygCtx___hyg_2_();
stack->m_obj
 = v_res_33_;
}
LEAN_EXPORT lean_object* l___private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_4193738739____hygCtx___hyg_2____boxed(lean_object* v_a_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l___private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_4193738739____hygCtx___hyg_2_();
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_markAuxRecursor(lean_object* v_env_36_, lean_object* v_declName_37_){
_start:
{
lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_38_ = l_Lean_auxRecExt;
v___x_39_ = l_Lean_TagDeclarationExtension_tag(v___x_38_, v_env_36_, v_declName_37_);
return v___x_39_;
}
}
uint8_t l_Lean_isAuxRecursor(lean_object* v_env_53_, lean_object* v_declName_54_){
_start:
{
uint8_t v___y_56_; lean_object* v___x_61_; lean_object* v_toEnvExtension_62_; lean_object* v_asyncMode_63_; uint8_t v___x_64_; 
v___x_61_ = l_Lean_auxRecExt;
v_toEnvExtension_62_ = lean_ctor_get(v___x_61_, 0);
v_asyncMode_63_ = lean_ctor_get(v_toEnvExtension_62_, 2);
lean_inc(v_declName_54_);
v___x_64_ = l_Lean_TagDeclarationExtension_isTagged(v___x_61_, v_env_53_, v_declName_54_, v_asyncMode_63_);
if (v___x_64_ == 0)
{
lean_object* v___x_65_; uint8_t v___x_66_; 
v___x_65_ = ((lean_object*)(l_Lean_isAuxRecursor___closed__6));
v___x_66_ = lean_name_eq(v_declName_54_, v___x_65_);
v___y_56_ = v___x_66_;
goto v___jp_55_;
}
else
{
v___y_56_ = v___x_64_;
goto v___jp_55_;
}
v___jp_55_:
{
if (v___y_56_ == 0)
{
lean_object* v___x_57_; uint8_t v___x_58_; 
v___x_57_ = ((lean_object*)(l_Lean_isAuxRecursor___closed__2));
v___x_58_ = lean_name_eq(v_declName_54_, v___x_57_);
if (v___x_58_ == 0)
{
lean_object* v___x_59_; uint8_t v___x_60_; 
v___x_59_ = ((lean_object*)(l_Lean_isAuxRecursor___closed__4));
v___x_60_ = lean_name_eq(v_declName_54_, v___x_59_);
lean_dec(v_declName_54_);
return v___x_60_;
}
else
{
lean_dec(v_declName_54_);
return v___x_58_;
}
}
else
{
lean_dec(v_declName_54_);
return v___y_56_;
}
}
}
}
LEAN_EXPORT void l_Lean_isAuxRecursor_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_53_ = stack[0].m_obj;
lean_object* v_declName_54_ = stack[1].m_obj;
uint8_t v_res_67_;
v_res_67_ = l_Lean_isAuxRecursor(v_env_53_, v_declName_54_);
stack->m_num = v_res_67_;
}
LEAN_EXPORT lean_object* l_Lean_isAuxRecursor___boxed(lean_object* v_env_68_, lean_object* v_declName_69_){
_start:
{
uint8_t v_res_70_; lean_object* v_r_71_; 
v_res_70_ = l_Lean_isAuxRecursor(v_env_68_, v_declName_69_);
v_r_71_ = lean_box(v_res_70_);
return v_r_71_;
}
}
uint8_t l_Lean_isAuxRecursorWithSuffix(lean_object* v_env_73_, lean_object* v_declName_74_, lean_object* v_suffix_75_){
_start:
{
if (lean_obj_tag(v_declName_74_) == 1)
{
lean_object* v_str_76_; uint8_t v___x_77_; 
v_str_76_ = lean_ctor_get(v_declName_74_, 1);
v___x_77_ = lean_string_dec_eq(v_str_76_, v_suffix_75_);
if (v___x_77_ == 0)
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; uint8_t v___x_82_; 
v___x_78_ = ((lean_object*)(l_Lean_isAuxRecursorWithSuffix___closed__0));
v___x_79_ = lean_string_append(v_suffix_75_, v___x_78_);
v___x_80_ = lean_string_utf8_byte_size(v_str_76_);
v___x_81_ = lean_string_utf8_byte_size(v___x_79_);
v___x_82_ = lean_nat_dec_le(v___x_81_, v___x_80_);
if (v___x_82_ == 0)
{
lean_dec_ref(v___x_79_);
lean_dec_ref_known(v_declName_74_, 2);
lean_dec_ref(v_env_73_);
return v___x_82_;
}
else
{
lean_object* v___x_83_; uint8_t v___x_84_; 
v___x_83_ = lean_unsigned_to_nat(0u);
v___x_84_ = lean_string_memcmp(v_str_76_, v___x_79_, v___x_83_, v___x_83_, v___x_81_);
lean_dec_ref(v___x_79_);
if (v___x_84_ == 0)
{
lean_dec_ref_known(v_declName_74_, 2);
lean_dec_ref(v_env_73_);
return v___x_84_;
}
else
{
uint8_t v___x_85_; 
v___x_85_ = l_Lean_isAuxRecursor(v_env_73_, v_declName_74_);
return v___x_85_;
}
}
}
else
{
uint8_t v___x_86_; 
lean_dec_ref(v_suffix_75_);
v___x_86_ = l_Lean_isAuxRecursor(v_env_73_, v_declName_74_);
return v___x_86_;
}
}
else
{
uint8_t v___x_87_; 
lean_dec_ref(v_suffix_75_);
lean_dec(v_declName_74_);
lean_dec_ref(v_env_73_);
v___x_87_ = 0;
return v___x_87_;
}
}
}
LEAN_EXPORT void l_Lean_isAuxRecursorWithSuffix_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_73_ = stack[0].m_obj;
lean_object* v_declName_74_ = stack[1].m_obj;
lean_object* v_suffix_75_ = stack[2].m_obj;
uint8_t v_res_88_;
v_res_88_ = l_Lean_isAuxRecursorWithSuffix(v_env_73_, v_declName_74_, v_suffix_75_);
stack->m_num = v_res_88_;
}
LEAN_EXPORT lean_object* l_Lean_isAuxRecursorWithSuffix___boxed(lean_object* v_env_89_, lean_object* v_declName_90_, lean_object* v_suffix_91_){
_start:
{
uint8_t v_res_92_; lean_object* v_r_93_; 
v_res_92_ = l_Lean_isAuxRecursorWithSuffix(v_env_89_, v_declName_90_, v_suffix_91_);
v_r_93_ = lean_box(v_res_92_);
return v_r_93_;
}
}
uint8_t l_Lean_isCasesOnRecursor(lean_object* v_env_94_, lean_object* v_declName_95_){
_start:
{
lean_object* v___x_96_; uint8_t v___x_97_; 
v___x_96_ = ((lean_object*)(l_Lean_casesOnSuffix___closed__0));
v___x_97_ = l_Lean_isAuxRecursorWithSuffix(v_env_94_, v_declName_95_, v___x_96_);
return v___x_97_;
}
}
LEAN_EXPORT void l_Lean_isCasesOnRecursor_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_94_ = stack[0].m_obj;
lean_object* v_declName_95_ = stack[1].m_obj;
uint8_t v_res_98_;
v_res_98_ = l_Lean_isCasesOnRecursor(v_env_94_, v_declName_95_);
stack->m_num = v_res_98_;
}
LEAN_EXPORT lean_object* l_Lean_isCasesOnRecursor___boxed(lean_object* v_env_99_, lean_object* v_declName_100_){
_start:
{
uint8_t v_res_101_; lean_object* v_r_102_; 
v_res_101_ = l_Lean_isCasesOnRecursor(v_env_99_, v_declName_100_);
v_r_102_ = lean_box(v_res_101_);
return v_r_102_;
}
}
uint8_t l_Lean_isRecOnRecursor(lean_object* v_env_103_, lean_object* v_declName_104_){
_start:
{
lean_object* v___x_105_; uint8_t v___x_106_; 
v___x_105_ = ((lean_object*)(l_Lean_recOnSuffix___closed__0));
v___x_106_ = l_Lean_isAuxRecursorWithSuffix(v_env_103_, v_declName_104_, v___x_105_);
return v___x_106_;
}
}
LEAN_EXPORT void l_Lean_isRecOnRecursor_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_103_ = stack[0].m_obj;
lean_object* v_declName_104_ = stack[1].m_obj;
uint8_t v_res_107_;
v_res_107_ = l_Lean_isRecOnRecursor(v_env_103_, v_declName_104_);
stack->m_num = v_res_107_;
}
LEAN_EXPORT lean_object* l_Lean_isRecOnRecursor___boxed(lean_object* v_env_108_, lean_object* v_declName_109_){
_start:
{
uint8_t v_res_110_; lean_object* v_r_111_; 
v_res_110_ = l_Lean_isRecOnRecursor(v_env_108_, v_declName_109_);
v_r_111_ = lean_box(v_res_110_);
return v_r_111_;
}
}
uint8_t l_Lean_isBRecOnRecursor(lean_object* v_env_112_, lean_object* v_declName_113_){
_start:
{
lean_object* v___x_114_; uint8_t v___x_115_; 
v___x_114_ = ((lean_object*)(l_Lean_brecOnSuffix___closed__0));
v___x_115_ = l_Lean_isAuxRecursorWithSuffix(v_env_112_, v_declName_113_, v___x_114_);
return v___x_115_;
}
}
LEAN_EXPORT void l_Lean_isBRecOnRecursor_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_112_ = stack[0].m_obj;
lean_object* v_declName_113_ = stack[1].m_obj;
uint8_t v_res_116_;
v_res_116_ = l_Lean_isBRecOnRecursor(v_env_112_, v_declName_113_);
stack->m_num = v_res_116_;
}
LEAN_EXPORT lean_object* l_Lean_isBRecOnRecursor___boxed(lean_object* v_env_117_, lean_object* v_declName_118_){
_start:
{
uint8_t v_res_119_; lean_object* v_r_120_; 
v_res_119_ = l_Lean_isBRecOnRecursor(v_env_117_, v_declName_118_);
v_r_120_ = lean_box(v_res_119_);
return v_r_120_;
}
}
lean_object* l___private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_163548097____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; uint8_t v___x_145_; lean_object* v___x_146_; 
v___x_143_ = ((lean_object*)(l___private_Lean_AuxRecursor_0__Lean_initFn___closed__8_00___x40_Lean_AuxRecursor_163548097____hygCtx___hyg_2_));
v___x_144_ = ((lean_object*)(l___private_Lean_AuxRecursor_0__Lean_initFn___closed__3_00___x40_Lean_AuxRecursor_4193738739____hygCtx___hyg_2_));
v___x_145_ = 1;
v___x_146_ = l_Lean_mkTagDeclarationExtension(v___x_143_, v___x_144_, v___x_145_);
return v___x_146_;
}
}
LEAN_EXPORT void l___private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_163548097____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_147_;
v_res_147_ = l___private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_163548097____hygCtx___hyg_2_();
stack->m_obj
 = v_res_147_;
}
LEAN_EXPORT lean_object* l___private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_163548097____hygCtx___hyg_2____boxed(lean_object* v_a_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l___private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_163548097____hygCtx___hyg_2_();
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_markSparseCasesOn(lean_object* v_env_150_, lean_object* v_declName_151_){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_152_ = l___private_Lean_AuxRecursor_0__Lean_sparseCasesOnExt;
v___x_153_ = l_Lean_TagDeclarationExtension_tag(v___x_152_, v_env_150_, v_declName_151_);
return v___x_153_;
}
}
uint8_t l_Lean_isSparseCasesOn(lean_object* v_env_154_, lean_object* v_declName_155_){
_start:
{
lean_object* v___x_156_; lean_object* v_toEnvExtension_157_; lean_object* v_asyncMode_158_; uint8_t v___x_159_; 
v___x_156_ = l___private_Lean_AuxRecursor_0__Lean_sparseCasesOnExt;
v_toEnvExtension_157_ = lean_ctor_get(v___x_156_, 0);
v_asyncMode_158_ = lean_ctor_get(v_toEnvExtension_157_, 2);
v___x_159_ = l_Lean_TagDeclarationExtension_isTagged(v___x_156_, v_env_154_, v_declName_155_, v_asyncMode_158_);
return v___x_159_;
}
}
LEAN_EXPORT void l_Lean_isSparseCasesOn_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_154_ = stack[0].m_obj;
lean_object* v_declName_155_ = stack[1].m_obj;
uint8_t v_res_160_;
v_res_160_ = l_Lean_isSparseCasesOn(v_env_154_, v_declName_155_);
stack->m_num = v_res_160_;
}
LEAN_EXPORT lean_object* l_Lean_isSparseCasesOn___boxed(lean_object* v_env_161_, lean_object* v_declName_162_){
_start:
{
uint8_t v_res_163_; lean_object* v_r_164_; 
v_res_163_ = l_Lean_isSparseCasesOn(v_env_161_, v_declName_162_);
v_r_164_ = lean_box(v_res_163_);
return v_r_164_;
}
}
uint8_t l_Lean_isCasesOnLike(lean_object* v_env_165_, lean_object* v_declName_166_){
_start:
{
uint8_t v___x_167_; 
lean_inc(v_declName_166_);
lean_inc_ref(v_env_165_);
v___x_167_ = l_Lean_isCasesOnRecursor(v_env_165_, v_declName_166_);
if (v___x_167_ == 0)
{
uint8_t v___x_168_; 
v___x_168_ = l_Lean_isSparseCasesOn(v_env_165_, v_declName_166_);
return v___x_168_;
}
else
{
lean_dec(v_declName_166_);
lean_dec_ref(v_env_165_);
return v___x_167_;
}
}
}
LEAN_EXPORT void l_Lean_isCasesOnLike_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_165_ = stack[0].m_obj;
lean_object* v_declName_166_ = stack[1].m_obj;
uint8_t v_res_169_;
v_res_169_ = l_Lean_isCasesOnLike(v_env_165_, v_declName_166_);
stack->m_num = v_res_169_;
}
LEAN_EXPORT lean_object* l_Lean_isCasesOnLike___boxed(lean_object* v_env_170_, lean_object* v_declName_171_){
_start:
{
uint8_t v_res_172_; lean_object* v_r_173_; 
v_res_172_ = l_Lean_isCasesOnLike(v_env_170_, v_declName_171_);
v_r_173_ = lean_box(v_res_172_);
return v_r_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_NoConfusionInfo_ctorIdx___impl(lean_object* v_x_174_){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = lean_obj_tag_nat(v_x_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_NoConfusionInfo_ctorIdx___impl___boxed(lean_object* v_x_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_Lean_NoConfusionInfo_ctorIdx___impl(v_x_176_);
lean_dec_ref(v_x_176_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_NoConfusionInfo_ctorElim___redArg(lean_object* v_t_178_, lean_object* v_k_179_){
_start:
{
if (lean_obj_tag(v_t_178_) == 0)
{
lean_object* v_arity_180_; lean_object* v_lhs_181_; lean_object* v_rhs_182_; lean_object* v___x_183_; 
v_arity_180_ = lean_ctor_get(v_t_178_, 0);
lean_inc(v_arity_180_);
v_lhs_181_ = lean_ctor_get(v_t_178_, 1);
lean_inc(v_lhs_181_);
v_rhs_182_ = lean_ctor_get(v_t_178_, 2);
lean_inc(v_rhs_182_);
lean_dec_ref_known(v_t_178_, 3);
v___x_183_ = lean_apply_3(v_k_179_, v_arity_180_, v_lhs_181_, v_rhs_182_);
return v___x_183_;
}
else
{
lean_object* v_arity_184_; lean_object* v_fields_185_; lean_object* v___x_186_; 
v_arity_184_ = lean_ctor_get(v_t_178_, 0);
lean_inc(v_arity_184_);
v_fields_185_ = lean_ctor_get(v_t_178_, 1);
lean_inc(v_fields_185_);
lean_dec_ref_known(v_t_178_, 2);
v___x_186_ = lean_apply_2(v_k_179_, v_arity_184_, v_fields_185_);
return v___x_186_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NoConfusionInfo_ctorElim(lean_object* v_motive_187_, lean_object* v_ctorIdx_188_, lean_object* v_t_189_, lean_object* v_h_190_, lean_object* v_k_191_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = l_Lean_NoConfusionInfo_ctorElim___redArg(v_t_189_, v_k_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_NoConfusionInfo_ctorElim___boxed(lean_object* v_motive_193_, lean_object* v_ctorIdx_194_, lean_object* v_t_195_, lean_object* v_h_196_, lean_object* v_k_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_Lean_NoConfusionInfo_ctorElim(v_motive_193_, v_ctorIdx_194_, v_t_195_, v_h_196_, v_k_197_);
lean_dec(v_ctorIdx_194_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_NoConfusionInfo_regular_elim___redArg(lean_object* v_t_199_, lean_object* v_regular_200_){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = l_Lean_NoConfusionInfo_ctorElim___redArg(v_t_199_, v_regular_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_NoConfusionInfo_regular_elim(lean_object* v_motive_202_, lean_object* v_t_203_, lean_object* v_h_204_, lean_object* v_regular_205_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = l_Lean_NoConfusionInfo_ctorElim___redArg(v_t_203_, v_regular_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_NoConfusionInfo_perCtor_elim___redArg(lean_object* v_t_207_, lean_object* v_perCtor_208_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = l_Lean_NoConfusionInfo_ctorElim___redArg(v_t_207_, v_perCtor_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_NoConfusionInfo_perCtor_elim(lean_object* v_motive_210_, lean_object* v_t_211_, lean_object* v_h_212_, lean_object* v_perCtor_213_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = l_Lean_NoConfusionInfo_ctorElim___redArg(v_t_211_, v_perCtor_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_NoConfusionInfo_arity(lean_object* v_x_219_){
_start:
{
lean_object* v_arity_220_; 
v_arity_220_ = lean_ctor_get(v_x_219_, 0);
lean_inc(v_arity_220_);
return v_arity_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_NoConfusionInfo_arity___boxed(lean_object* v_x_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Lean_NoConfusionInfo_arity(v_x_221_);
lean_dec_ref(v_x_221_);
return v_res_222_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__2(lean_object* v_env_223_, lean_object* v_as_224_, size_t v_i_225_, size_t v_stop_226_, lean_object* v_b_227_){
_start:
{
lean_object* v___y_229_; uint8_t v___x_233_; 
v___x_233_ = lean_usize_dec_eq(v_i_225_, v_stop_226_);
if (v___x_233_ == 0)
{
lean_object* v___x_234_; lean_object* v_fst_235_; uint8_t v___x_236_; 
v___x_234_ = lean_array_uget_borrowed(v_as_224_, v_i_225_);
v_fst_235_ = lean_ctor_get(v___x_234_, 0);
lean_inc(v_fst_235_);
lean_inc_ref(v_env_223_);
v___x_236_ = l_Lean_Environment_contains(v_env_223_, v_fst_235_, v___x_233_);
if (v___x_236_ == 0)
{
v___y_229_ = v_b_227_;
goto v___jp_228_;
}
else
{
lean_object* v___x_237_; 
lean_inc(v___x_234_);
v___x_237_ = lean_array_push(v_b_227_, v___x_234_);
v___y_229_ = v___x_237_;
goto v___jp_228_;
}
}
else
{
lean_dec_ref(v_env_223_);
return v_b_227_;
}
v___jp_228_:
{
size_t v___x_230_; size_t v___x_231_; 
v___x_230_ = ((size_t)1ULL);
v___x_231_ = lean_usize_add(v_i_225_, v___x_230_);
v_i_225_ = v___x_231_;
v_b_227_ = v___y_229_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_223_ = stack[0].m_obj;
lean_object* v_as_224_ = stack[1].m_obj;
size_t v_i_225_ = stack[2].m_num;
size_t v_stop_226_ = stack[3].m_num;
lean_object* v_b_227_ = stack[4].m_obj;
lean_object* v_res_238_;
v_res_238_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__2(v_env_223_, v_as_224_, v_i_225_, v_stop_226_, v_b_227_);
stack->m_obj
 = v_res_238_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__2___boxed(lean_object* v_env_239_, lean_object* v_as_240_, lean_object* v_i_241_, lean_object* v_stop_242_, lean_object* v_b_243_){
_start:
{
size_t v_i_boxed_244_; size_t v_stop_boxed_245_; lean_object* v_res_246_; 
v_i_boxed_244_ = lean_unbox_usize(v_i_241_);
lean_dec(v_i_241_);
v_stop_boxed_245_ = lean_unbox_usize(v_stop_242_);
lean_dec(v_stop_242_);
v_res_246_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__2(v_env_239_, v_as_240_, v_i_boxed_244_, v_stop_boxed_245_, v_b_243_);
lean_dec_ref(v_as_240_);
return v_res_246_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__1(lean_object* v_env_247_, lean_object* v_as_248_, size_t v_i_249_, size_t v_stop_250_, lean_object* v_b_251_){
_start:
{
lean_object* v___y_253_; uint8_t v___x_257_; 
v___x_257_ = lean_usize_dec_eq(v_i_249_, v_stop_250_);
if (v___x_257_ == 0)
{
lean_object* v___x_258_; lean_object* v_fst_259_; uint8_t v___x_260_; lean_object* v___x_261_; uint8_t v___x_262_; 
v___x_258_ = lean_array_uget_borrowed(v_as_248_, v_i_249_);
v_fst_259_ = lean_ctor_get(v___x_258_, 0);
v___x_260_ = 1;
lean_inc_ref(v_env_247_);
v___x_261_ = l_Lean_Environment_setExporting(v_env_247_, v___x_260_);
lean_inc(v_fst_259_);
v___x_262_ = l_Lean_Environment_contains(v___x_261_, v_fst_259_, v___x_260_);
if (v___x_262_ == 0)
{
v___y_253_ = v_b_251_;
goto v___jp_252_;
}
else
{
lean_object* v___x_263_; 
lean_inc(v___x_258_);
v___x_263_ = lean_array_push(v_b_251_, v___x_258_);
v___y_253_ = v___x_263_;
goto v___jp_252_;
}
}
else
{
lean_dec_ref(v_env_247_);
return v_b_251_;
}
v___jp_252_:
{
size_t v___x_254_; size_t v___x_255_; 
v___x_254_ = ((size_t)1ULL);
v___x_255_ = lean_usize_add(v_i_249_, v___x_254_);
v_i_249_ = v___x_255_;
v_b_251_ = v___y_253_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_247_ = stack[0].m_obj;
lean_object* v_as_248_ = stack[1].m_obj;
size_t v_i_249_ = stack[2].m_num;
size_t v_stop_250_ = stack[3].m_num;
lean_object* v_b_251_ = stack[4].m_obj;
lean_object* v_res_264_;
v_res_264_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__1(v_env_247_, v_as_248_, v_i_249_, v_stop_250_, v_b_251_);
stack->m_obj
 = v_res_264_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__1___boxed(lean_object* v_env_265_, lean_object* v_as_266_, lean_object* v_i_267_, lean_object* v_stop_268_, lean_object* v_b_269_){
_start:
{
size_t v_i_boxed_270_; size_t v_stop_boxed_271_; lean_object* v_res_272_; 
v_i_boxed_270_ = lean_unbox_usize(v_i_267_);
lean_dec(v_i_267_);
v_stop_boxed_271_ = lean_unbox_usize(v_stop_268_);
lean_dec(v_stop_268_);
v_res_272_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__1(v_env_265_, v_as_266_, v_i_boxed_270_, v_stop_boxed_271_, v_b_269_);
lean_dec_ref(v_as_266_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_273_, lean_object* v_x_274_){
_start:
{
if (lean_obj_tag(v_x_274_) == 0)
{
lean_object* v_k_275_; lean_object* v_v_276_; lean_object* v_l_277_; lean_object* v_r_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v_k_275_ = lean_ctor_get(v_x_274_, 1);
v_v_276_ = lean_ctor_get(v_x_274_, 2);
v_l_277_ = lean_ctor_get(v_x_274_, 3);
v_r_278_ = lean_ctor_get(v_x_274_, 4);
v___x_279_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__0_spec__0(v_init_273_, v_l_277_);
lean_inc(v_v_276_);
lean_inc(v_k_275_);
v___x_280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_280_, 0, v_k_275_);
lean_ctor_set(v___x_280_, 1, v_v_276_);
v___x_281_ = lean_array_push(v___x_279_, v___x_280_);
v_init_273_ = v___x_281_;
v_x_274_ = v_r_278_;
goto _start;
}
else
{
return v_init_273_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_283_, lean_object* v_x_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__0_spec__0(v_init_283_, v_x_284_);
lean_dec(v_x_284_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AuxRecursor_0__Lean_initFn___lam__0_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2_(lean_object* v_env_290_, lean_object* v_s_291_){
_start:
{
lean_object* v___x_292_; lean_object* v___y_294_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; uint8_t v___x_313_; 
v___x_292_ = lean_unsigned_to_nat(0u);
v___x_309_ = ((lean_object*)(l___private_Lean_AuxRecursor_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2_));
v___x_310_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__0_spec__0(v___x_309_, v_s_291_);
v___x_311_ = lean_array_get_size(v___x_310_);
v___x_312_ = ((lean_object*)(l___private_Lean_AuxRecursor_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2_));
v___x_313_ = lean_nat_dec_lt(v___x_292_, v___x_311_);
if (v___x_313_ == 0)
{
lean_dec_ref(v___x_310_);
v___y_294_ = v___x_312_;
goto v___jp_293_;
}
else
{
uint8_t v___x_314_; 
v___x_314_ = lean_nat_dec_le(v___x_311_, v___x_311_);
if (v___x_314_ == 0)
{
if (v___x_313_ == 0)
{
lean_dec_ref(v___x_310_);
v___y_294_ = v___x_312_;
goto v___jp_293_;
}
else
{
size_t v___x_315_; size_t v___x_316_; lean_object* v___x_317_; 
v___x_315_ = ((size_t)0ULL);
v___x_316_ = lean_usize_of_nat(v___x_311_);
lean_inc_ref(v_env_290_);
v___x_317_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__2(v_env_290_, v___x_310_, v___x_315_, v___x_316_, v___x_312_);
lean_dec_ref(v___x_310_);
v___y_294_ = v___x_317_;
goto v___jp_293_;
}
}
else
{
size_t v___x_318_; size_t v___x_319_; lean_object* v___x_320_; 
v___x_318_ = ((size_t)0ULL);
v___x_319_ = lean_usize_of_nat(v___x_311_);
lean_inc_ref(v_env_290_);
v___x_320_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__2(v_env_290_, v___x_310_, v___x_318_, v___x_319_, v___x_312_);
lean_dec_ref(v___x_310_);
v___y_294_ = v___x_320_;
goto v___jp_293_;
}
}
v___jp_293_:
{
lean_object* v___x_295_; lean_object* v___x_296_; uint8_t v___x_297_; 
v___x_295_ = lean_array_get_size(v___y_294_);
v___x_296_ = ((lean_object*)(l___private_Lean_AuxRecursor_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2_));
v___x_297_ = lean_nat_dec_lt(v___x_292_, v___x_295_);
if (v___x_297_ == 0)
{
lean_object* v___x_298_; 
lean_dec_ref(v_env_290_);
v___x_298_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_298_, 0, v___x_296_);
lean_ctor_set(v___x_298_, 1, v___x_296_);
lean_ctor_set(v___x_298_, 2, v___y_294_);
return v___x_298_;
}
else
{
uint8_t v___x_299_; 
v___x_299_ = lean_nat_dec_le(v___x_295_, v___x_295_);
if (v___x_299_ == 0)
{
if (v___x_297_ == 0)
{
lean_object* v___x_300_; 
lean_dec_ref(v_env_290_);
v___x_300_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_300_, 0, v___x_296_);
lean_ctor_set(v___x_300_, 1, v___x_296_);
lean_ctor_set(v___x_300_, 2, v___y_294_);
return v___x_300_;
}
else
{
size_t v___x_301_; size_t v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_301_ = ((size_t)0ULL);
v___x_302_ = lean_usize_of_nat(v___x_295_);
v___x_303_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__1(v_env_290_, v___y_294_, v___x_301_, v___x_302_, v___x_296_);
lean_inc_ref(v___x_303_);
v___x_304_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_304_, 0, v___x_303_);
lean_ctor_set(v___x_304_, 1, v___x_303_);
lean_ctor_set(v___x_304_, 2, v___y_294_);
return v___x_304_;
}
}
else
{
size_t v___x_305_; size_t v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_305_ = ((size_t)0ULL);
v___x_306_ = lean_usize_of_nat(v___x_295_);
v___x_307_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__1(v_env_290_, v___y_294_, v___x_305_, v___x_306_, v___x_296_);
lean_inc_ref(v___x_307_);
v___x_308_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_308_, 0, v___x_307_);
lean_ctor_set(v___x_308_, 1, v___x_307_);
lean_ctor_set(v___x_308_, 2, v___y_294_);
return v___x_308_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AuxRecursor_0__Lean_initFn___lam__0_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2____boxed(lean_object* v_env_321_, lean_object* v_s_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l___private_Lean_AuxRecursor_0__Lean_initFn___lam__0_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2_(v_env_321_, v_s_322_);
lean_dec(v_s_322_);
return v_res_323_;
}
}
lean_object* l___private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_330_; lean_object* v___x_331_; lean_object* v___x_332_; uint8_t v___x_333_; lean_object* v___x_334_; 
v___f_330_ = ((lean_object*)(l___private_Lean_AuxRecursor_0__Lean_initFn___closed__0_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2_));
v___x_331_ = ((lean_object*)(l___private_Lean_AuxRecursor_0__Lean_initFn___closed__2_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2_));
v___x_332_ = lean_box(2);
v___x_333_ = 1;
v___x_334_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_331_, v___x_332_, v___x_333_, v___f_330_);
return v___x_334_;
}
}
LEAN_EXPORT void l___private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_335_;
v_res_335_ = l___private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2_();
stack->m_obj
 = v_res_335_;
}
LEAN_EXPORT lean_object* l___private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2____boxed(lean_object* v_a_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l___private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2_();
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__0(lean_object* v_init_338_, lean_object* v_t_339_){
_start:
{
lean_object* v___x_340_; 
v___x_340_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__0_spec__0(v_init_338_, v_t_339_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_341_, lean_object* v_t_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3873369295____hygCtx___hyg_2__spec__0(v_init_341_, v_t_342_);
lean_dec(v_t_342_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_markNoConfusion(lean_object* v_env_344_, lean_object* v_n_345_, lean_object* v_info_346_){
_start:
{
lean_object* v___x_347_; uint8_t v___x_348_; lean_object* v___x_349_; 
v___x_347_ = l_Lean_noConfusionExt;
v___x_348_ = 0;
v___x_349_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_347_, v_env_344_, v_n_345_, v_info_346_, v___x_348_);
return v___x_349_;
}
}
uint8_t l_Lean_isNoConfusion(lean_object* v_env_350_, lean_object* v_n_351_){
_start:
{
lean_object* v___x_352_; lean_object* v_toEnvExtension_353_; lean_object* v_asyncMode_354_; lean_object* v___x_355_; uint8_t v___x_356_; 
v___x_352_ = l_Lean_noConfusionExt;
v_toEnvExtension_353_ = lean_ctor_get(v___x_352_, 0);
v_asyncMode_354_ = lean_ctor_get(v_toEnvExtension_353_, 2);
v___x_355_ = ((lean_object*)(l_Lean_instInhabitedNoConfusionInfo_default));
v___x_356_ = l_Lean_MapDeclarationExtension_contains___redArg(v___x_355_, v___x_352_, v_env_350_, v_n_351_, v_asyncMode_354_);
return v___x_356_;
}
}
LEAN_EXPORT void l_Lean_isNoConfusion_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_350_ = stack[0].m_obj;
lean_object* v_n_351_ = stack[1].m_obj;
uint8_t v_res_357_;
v_res_357_ = l_Lean_isNoConfusion(v_env_350_, v_n_351_);
stack->m_num = v_res_357_;
}
LEAN_EXPORT lean_object* l_Lean_isNoConfusion___boxed(lean_object* v_env_358_, lean_object* v_n_359_){
_start:
{
uint8_t v_res_360_; lean_object* v_r_361_; 
v_res_360_ = l_Lean_isNoConfusion(v_env_358_, v_n_359_);
v_r_361_ = lean_box(v_res_360_);
return v_r_361_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getNoConfusionInfo_spec__0(lean_object* v_msg_362_){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_363_ = ((lean_object*)(l_Lean_instInhabitedNoConfusionInfo_default));
v___x_364_ = lean_panic_fn_borrowed(v___x_363_, v_msg_362_);
return v___x_364_;
}
}
static lean_object* _init_l_Lean_getNoConfusionInfo___closed__3(void){
_start:
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_368_ = ((lean_object*)(l_Lean_getNoConfusionInfo___closed__2));
v___x_369_ = lean_unsigned_to_nat(14u);
v___x_370_ = lean_unsigned_to_nat(22u);
v___x_371_ = ((lean_object*)(l_Lean_getNoConfusionInfo___closed__1));
v___x_372_ = ((lean_object*)(l_Lean_getNoConfusionInfo___closed__0));
v___x_373_ = l_mkPanicMessageWithDecl(v___x_372_, v___x_371_, v___x_370_, v___x_369_, v___x_368_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_getNoConfusionInfo(lean_object* v_env_374_, lean_object* v_n_375_){
_start:
{
lean_object* v___x_376_; lean_object* v_toEnvExtension_377_; lean_object* v_asyncMode_378_; lean_object* v___x_379_; uint8_t v___x_380_; lean_object* v___x_381_; 
v___x_376_ = l_Lean_noConfusionExt;
v_toEnvExtension_377_ = lean_ctor_get(v___x_376_, 0);
v_asyncMode_378_ = lean_ctor_get(v_toEnvExtension_377_, 2);
v___x_379_ = ((lean_object*)(l_Lean_instInhabitedNoConfusionInfo_default));
v___x_380_ = 0;
v___x_381_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_379_, v___x_376_, v_env_374_, v_n_375_, v_asyncMode_378_, v___x_380_);
if (lean_obj_tag(v___x_381_) == 0)
{
lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_382_ = lean_obj_once(&l_Lean_getNoConfusionInfo___closed__3, &l_Lean_getNoConfusionInfo___closed__3_once, _init_l_Lean_getNoConfusionInfo___closed__3);
v___x_383_ = l_panic___at___00Lean_getNoConfusionInfo_spec__0(v___x_382_);
return v___x_383_;
}
else
{
lean_object* v_val_384_; 
v_val_384_ = lean_ctor_get(v___x_381_, 0);
lean_inc(v_val_384_);
lean_dec_ref_known(v___x_381_, 1);
return v_val_384_;
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

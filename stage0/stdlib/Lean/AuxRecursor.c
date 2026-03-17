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
lean_object* l_Lean_mkTagDeclarationExtension(lean_object*, lean_object*);
lean_object* l_Lean_TagDeclarationExtension_tag(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkMapDeclarationExtension___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MapDeclarationExtension_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_initFn___closed__0_00___x40_Lean_AuxRecursor_3622182683____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_initFn___closed__0_00___x40_Lean_AuxRecursor_3622182683____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_AuxRecursor_3622182683____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_initFn___closed__1_00___x40_Lean_AuxRecursor_3622182683____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "auxRecExt"};
static const lean_object* l_Lean_initFn___closed__1_00___x40_Lean_AuxRecursor_3622182683____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_AuxRecursor_3622182683____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_initFn___closed__2_00___x40_Lean_AuxRecursor_3622182683____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_AuxRecursor_3622182683____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_initFn___closed__2_00___x40_Lean_AuxRecursor_3622182683____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_AuxRecursor_3622182683____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_AuxRecursor_3622182683____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(105, 237, 166, 221, 148, 106, 49, 53)}};
static const lean_object* l_Lean_initFn___closed__2_00___x40_Lean_AuxRecursor_3622182683____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_AuxRecursor_3622182683____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_AuxRecursor_3622182683____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_AuxRecursor_3622182683____hygCtx___hyg_2____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_AuxRecursor_0__Lean_initFn___closed__0_00___x40_Lean_AuxRecursor_2879463644____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_AuxRecursor_0__Lean_initFn___closed__0_00___x40_Lean_AuxRecursor_2879463644____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_AuxRecursor_0__Lean_initFn___closed__0_00___x40_Lean_AuxRecursor_2879463644____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_AuxRecursor_0__Lean_initFn___closed__1_00___x40_Lean_AuxRecursor_2879463644____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_AuxRecursor_0__Lean_initFn___closed__0_00___x40_Lean_AuxRecursor_2879463644____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_AuxRecursor_0__Lean_initFn___closed__1_00___x40_Lean_AuxRecursor_2879463644____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_AuxRecursor_0__Lean_initFn___closed__1_00___x40_Lean_AuxRecursor_2879463644____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_AuxRecursor_0__Lean_initFn___closed__2_00___x40_Lean_AuxRecursor_2879463644____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_AuxRecursor_0__Lean_initFn___closed__1_00___x40_Lean_AuxRecursor_2879463644____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_AuxRecursor_3622182683____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_AuxRecursor_0__Lean_initFn___closed__2_00___x40_Lean_AuxRecursor_2879463644____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_AuxRecursor_0__Lean_initFn___closed__2_00___x40_Lean_AuxRecursor_2879463644____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_AuxRecursor_0__Lean_initFn___closed__3_00___x40_Lean_AuxRecursor_2879463644____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "AuxRecursor"};
static const lean_object* l___private_Lean_AuxRecursor_0__Lean_initFn___closed__3_00___x40_Lean_AuxRecursor_2879463644____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_AuxRecursor_0__Lean_initFn___closed__3_00___x40_Lean_AuxRecursor_2879463644____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_AuxRecursor_0__Lean_initFn___closed__4_00___x40_Lean_AuxRecursor_2879463644____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_AuxRecursor_0__Lean_initFn___closed__2_00___x40_Lean_AuxRecursor_2879463644____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_AuxRecursor_0__Lean_initFn___closed__3_00___x40_Lean_AuxRecursor_2879463644____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(243, 71, 92, 208, 56, 190, 224, 113)}};
static const lean_object* l___private_Lean_AuxRecursor_0__Lean_initFn___closed__4_00___x40_Lean_AuxRecursor_2879463644____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_AuxRecursor_0__Lean_initFn___closed__4_00___x40_Lean_AuxRecursor_2879463644____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_AuxRecursor_0__Lean_initFn___closed__5_00___x40_Lean_AuxRecursor_2879463644____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_AuxRecursor_0__Lean_initFn___closed__4_00___x40_Lean_AuxRecursor_2879463644____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(94, 87, 119, 208, 23, 13, 32, 194)}};
static const lean_object* l___private_Lean_AuxRecursor_0__Lean_initFn___closed__5_00___x40_Lean_AuxRecursor_2879463644____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_AuxRecursor_0__Lean_initFn___closed__5_00___x40_Lean_AuxRecursor_2879463644____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_AuxRecursor_0__Lean_initFn___closed__6_00___x40_Lean_AuxRecursor_2879463644____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_AuxRecursor_0__Lean_initFn___closed__5_00___x40_Lean_AuxRecursor_2879463644____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_AuxRecursor_3622182683____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(167, 145, 139, 114, 135, 121, 7, 142)}};
static const lean_object* l___private_Lean_AuxRecursor_0__Lean_initFn___closed__6_00___x40_Lean_AuxRecursor_2879463644____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_AuxRecursor_0__Lean_initFn___closed__6_00___x40_Lean_AuxRecursor_2879463644____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_AuxRecursor_0__Lean_initFn___closed__7_00___x40_Lean_AuxRecursor_2879463644____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "sparseCasesOnExt"};
static const lean_object* l___private_Lean_AuxRecursor_0__Lean_initFn___closed__7_00___x40_Lean_AuxRecursor_2879463644____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_AuxRecursor_0__Lean_initFn___closed__7_00___x40_Lean_AuxRecursor_2879463644____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_AuxRecursor_0__Lean_initFn___closed__8_00___x40_Lean_AuxRecursor_2879463644____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_AuxRecursor_0__Lean_initFn___closed__6_00___x40_Lean_AuxRecursor_2879463644____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_AuxRecursor_0__Lean_initFn___closed__7_00___x40_Lean_AuxRecursor_2879463644____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(192, 252, 121, 117, 134, 106, 159, 193)}};
static const lean_object* l___private_Lean_AuxRecursor_0__Lean_initFn___closed__8_00___x40_Lean_AuxRecursor_2879463644____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_AuxRecursor_0__Lean_initFn___closed__8_00___x40_Lean_AuxRecursor_2879463644____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_2879463644____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_2879463644____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AuxRecursor_0__Lean_sparseCasesOnExt;
LEAN_EXPORT lean_object* l_Lean_markSparseCasesOn(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_isSparseCasesOn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isSparseCasesOn___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_isCasesOnLike(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isCasesOnLike___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NoConfusionInfo_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_NoConfusionInfo_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_initFn_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_initFn_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_initFn___lam__0___closed__0_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_initFn___lam__0___closed__0_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___lam__0___closed__0_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__value;
static const lean_array_object l_Lean_initFn___lam__0___closed__1_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_initFn___lam__0___closed__1_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___lam__0___closed__1_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2_(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_initFn___closed__0_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__0_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__0_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_initFn___closed__1_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "noConfusionExt"};
static const lean_object* l_Lean_initFn___closed__1_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_initFn___closed__2_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_AuxRecursor_3622182683____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_initFn___closed__2_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(42, 4, 193, 241, 26, 143, 160, 211)}};
static const lean_object* l_Lean_initFn___closed__2_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_AuxRecursor_3622182683____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_27_ = ((lean_object*)(l_Lean_initFn___closed__2_00___x40_Lean_AuxRecursor_3622182683____hygCtx___hyg_2_));
v___x_28_ = lean_box(1);
v___x_29_ = l_Lean_mkTagDeclarationExtension(v___x_27_, v___x_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_AuxRecursor_3622182683____hygCtx___hyg_2____boxed(lean_object* v_a_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_Lean_initFn_00___x40_Lean_AuxRecursor_3622182683____hygCtx___hyg_2_();
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_markAuxRecursor(lean_object* v_env_32_, lean_object* v_declName_33_){
_start:
{
lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_34_ = l_Lean_auxRecExt;
v___x_35_ = l_Lean_TagDeclarationExtension_tag(v___x_34_, v_env_32_, v_declName_33_);
return v___x_35_;
}
}
LEAN_EXPORT uint8_t l_Lean_isAuxRecursor(lean_object* v_env_49_, lean_object* v_declName_50_){
_start:
{
uint8_t v___y_52_; lean_object* v___x_57_; lean_object* v_toEnvExtension_58_; lean_object* v_asyncMode_59_; uint8_t v___x_60_; 
v___x_57_ = l_Lean_auxRecExt;
v_toEnvExtension_58_ = lean_ctor_get(v___x_57_, 0);
lean_inc_ref(v_toEnvExtension_58_);
v_asyncMode_59_ = lean_ctor_get(v_toEnvExtension_58_, 2);
lean_inc(v_asyncMode_59_);
lean_dec_ref(v_toEnvExtension_58_);
lean_inc(v_declName_50_);
v___x_60_ = l_Lean_TagDeclarationExtension_isTagged(v___x_57_, v_env_49_, v_declName_50_, v_asyncMode_59_);
lean_dec(v_asyncMode_59_);
if (v___x_60_ == 0)
{
lean_object* v___x_61_; uint8_t v___x_62_; 
v___x_61_ = ((lean_object*)(l_Lean_isAuxRecursor___closed__6));
v___x_62_ = lean_name_eq(v_declName_50_, v___x_61_);
v___y_52_ = v___x_62_;
goto v___jp_51_;
}
else
{
v___y_52_ = v___x_60_;
goto v___jp_51_;
}
v___jp_51_:
{
if (v___y_52_ == 0)
{
lean_object* v___x_53_; uint8_t v___x_54_; 
v___x_53_ = ((lean_object*)(l_Lean_isAuxRecursor___closed__2));
v___x_54_ = lean_name_eq(v_declName_50_, v___x_53_);
if (v___x_54_ == 0)
{
lean_object* v___x_55_; uint8_t v___x_56_; 
v___x_55_ = ((lean_object*)(l_Lean_isAuxRecursor___closed__4));
v___x_56_ = lean_name_eq(v_declName_50_, v___x_55_);
lean_dec(v_declName_50_);
return v___x_56_;
}
else
{
lean_dec(v_declName_50_);
return v___x_54_;
}
}
else
{
lean_dec(v_declName_50_);
return v___y_52_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isAuxRecursor___boxed(lean_object* v_env_63_, lean_object* v_declName_64_){
_start:
{
uint8_t v_res_65_; lean_object* v_r_66_; 
v_res_65_ = l_Lean_isAuxRecursor(v_env_63_, v_declName_64_);
v_r_66_ = lean_box(v_res_65_);
return v_r_66_;
}
}
LEAN_EXPORT uint8_t l_Lean_isAuxRecursorWithSuffix(lean_object* v_env_68_, lean_object* v_declName_69_, lean_object* v_suffix_70_){
_start:
{
uint8_t v___y_72_; 
if (lean_obj_tag(v_declName_69_) == 1)
{
lean_object* v_str_74_; uint8_t v___x_75_; 
v_str_74_ = lean_ctor_get(v_declName_69_, 1);
v___x_75_ = lean_string_dec_eq(v_str_74_, v_suffix_70_);
if (v___x_75_ == 0)
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; uint8_t v___x_80_; 
v___x_76_ = ((lean_object*)(l_Lean_isAuxRecursorWithSuffix___closed__0));
v___x_77_ = lean_string_append(v_suffix_70_, v___x_76_);
v___x_78_ = lean_string_utf8_byte_size(v_str_74_);
v___x_79_ = lean_string_utf8_byte_size(v___x_77_);
v___x_80_ = lean_nat_dec_le(v___x_79_, v___x_78_);
if (v___x_80_ == 0)
{
lean_dec_ref(v___x_77_);
v___y_72_ = v___x_75_;
goto v___jp_71_;
}
else
{
lean_object* v___x_81_; uint8_t v___x_82_; 
v___x_81_ = lean_unsigned_to_nat(0u);
v___x_82_ = lean_string_memcmp(v_str_74_, v___x_77_, v___x_81_, v___x_81_, v___x_79_);
lean_dec_ref(v___x_77_);
v___y_72_ = v___x_82_;
goto v___jp_71_;
}
}
else
{
lean_dec_ref(v_suffix_70_);
v___y_72_ = v___x_75_;
goto v___jp_71_;
}
}
else
{
uint8_t v___x_83_; 
lean_dec_ref(v_suffix_70_);
lean_dec(v_declName_69_);
lean_dec_ref(v_env_68_);
v___x_83_ = 0;
return v___x_83_;
}
v___jp_71_:
{
if (v___y_72_ == 0)
{
lean_dec(v_declName_69_);
lean_dec_ref(v_env_68_);
return v___y_72_;
}
else
{
uint8_t v___x_73_; 
v___x_73_ = l_Lean_isAuxRecursor(v_env_68_, v_declName_69_);
return v___x_73_;
}
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
LEAN_EXPORT lean_object* l___private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_2879463644____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_135_ = ((lean_object*)(l___private_Lean_AuxRecursor_0__Lean_initFn___closed__8_00___x40_Lean_AuxRecursor_2879463644____hygCtx___hyg_2_));
v___x_136_ = lean_box(1);
v___x_137_ = l_Lean_mkTagDeclarationExtension(v___x_135_, v___x_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_2879463644____hygCtx___hyg_2____boxed(lean_object* v_a_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l___private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_2879463644____hygCtx___hyg_2_();
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_markSparseCasesOn(lean_object* v_env_140_, lean_object* v_declName_141_){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_142_ = l___private_Lean_AuxRecursor_0__Lean_sparseCasesOnExt;
v___x_143_ = l_Lean_TagDeclarationExtension_tag(v___x_142_, v_env_140_, v_declName_141_);
return v___x_143_;
}
}
LEAN_EXPORT uint8_t l_Lean_isSparseCasesOn(lean_object* v_env_144_, lean_object* v_declName_145_){
_start:
{
lean_object* v___x_146_; lean_object* v_toEnvExtension_147_; lean_object* v_asyncMode_148_; uint8_t v___x_149_; 
v___x_146_ = l___private_Lean_AuxRecursor_0__Lean_sparseCasesOnExt;
v_toEnvExtension_147_ = lean_ctor_get(v___x_146_, 0);
lean_inc_ref(v_toEnvExtension_147_);
v_asyncMode_148_ = lean_ctor_get(v_toEnvExtension_147_, 2);
lean_inc(v_asyncMode_148_);
lean_dec_ref(v_toEnvExtension_147_);
v___x_149_ = l_Lean_TagDeclarationExtension_isTagged(v___x_146_, v_env_144_, v_declName_145_, v_asyncMode_148_);
lean_dec(v_asyncMode_148_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_isSparseCasesOn___boxed(lean_object* v_env_150_, lean_object* v_declName_151_){
_start:
{
uint8_t v_res_152_; lean_object* v_r_153_; 
v_res_152_ = l_Lean_isSparseCasesOn(v_env_150_, v_declName_151_);
v_r_153_ = lean_box(v_res_152_);
return v_r_153_;
}
}
LEAN_EXPORT uint8_t l_Lean_isCasesOnLike(lean_object* v_env_154_, lean_object* v_declName_155_){
_start:
{
uint8_t v___x_156_; 
lean_inc(v_declName_155_);
lean_inc_ref(v_env_154_);
v___x_156_ = l_Lean_isCasesOnRecursor(v_env_154_, v_declName_155_);
if (v___x_156_ == 0)
{
uint8_t v___x_157_; 
v___x_157_ = l_Lean_isSparseCasesOn(v_env_154_, v_declName_155_);
return v___x_157_;
}
else
{
lean_dec(v_declName_155_);
lean_dec_ref(v_env_154_);
return v___x_156_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isCasesOnLike___boxed(lean_object* v_env_158_, lean_object* v_declName_159_){
_start:
{
uint8_t v_res_160_; lean_object* v_r_161_; 
v_res_160_ = l_Lean_isCasesOnLike(v_env_158_, v_declName_159_);
v_r_161_ = lean_box(v_res_160_);
return v_r_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_NoConfusionInfo_ctorIdx(lean_object* v_x_162_){
_start:
{
if (lean_obj_tag(v_x_162_) == 0)
{
lean_object* v___x_163_; 
v___x_163_ = lean_unsigned_to_nat(0u);
return v___x_163_;
}
else
{
lean_object* v___x_164_; 
v___x_164_ = lean_unsigned_to_nat(1u);
return v___x_164_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NoConfusionInfo_ctorIdx___boxed(lean_object* v_x_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Lean_NoConfusionInfo_ctorIdx(v_x_165_);
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
lean_dec_ref(v_t_167_);
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
lean_dec_ref(v_t_167_);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_212_, lean_object* v_x_213_){
_start:
{
if (lean_obj_tag(v_x_213_) == 0)
{
lean_object* v_k_214_; lean_object* v_v_215_; lean_object* v_l_216_; lean_object* v_r_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v_k_214_ = lean_ctor_get(v_x_213_, 1);
v_v_215_ = lean_ctor_get(v_x_213_, 2);
v_l_216_ = lean_ctor_get(v_x_213_, 3);
v_r_217_ = lean_ctor_get(v_x_213_, 4);
v___x_218_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__spec__0_spec__0(v_init_212_, v_l_216_);
lean_inc(v_v_215_);
lean_inc(v_k_214_);
v___x_219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_219_, 0, v_k_214_);
lean_ctor_set(v___x_219_, 1, v_v_215_);
v___x_220_ = lean_array_push(v___x_218_, v___x_219_);
v_init_212_ = v___x_220_;
v_x_213_ = v_r_217_;
goto _start;
}
else
{
return v_init_212_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_222_, lean_object* v_x_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__spec__0_spec__0(v_init_222_, v_x_223_);
lean_dec(v_x_223_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_initFn_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__spec__1(lean_object* v_env_225_, lean_object* v_as_226_, size_t v_i_227_, size_t v_stop_228_, lean_object* v_b_229_){
_start:
{
lean_object* v___y_231_; uint8_t v___x_235_; 
v___x_235_ = lean_usize_dec_eq(v_i_227_, v_stop_228_);
if (v___x_235_ == 0)
{
lean_object* v___x_236_; lean_object* v_fst_237_; uint8_t v___x_238_; 
v___x_236_ = lean_array_uget_borrowed(v_as_226_, v_i_227_);
v_fst_237_ = lean_ctor_get(v___x_236_, 0);
lean_inc(v_fst_237_);
lean_inc_ref(v_env_225_);
v___x_238_ = l_Lean_Environment_contains(v_env_225_, v_fst_237_, v___x_235_);
if (v___x_238_ == 0)
{
v___y_231_ = v_b_229_;
goto v___jp_230_;
}
else
{
lean_object* v___x_239_; 
lean_inc(v___x_236_);
v___x_239_ = lean_array_push(v_b_229_, v___x_236_);
v___y_231_ = v___x_239_;
goto v___jp_230_;
}
}
else
{
lean_dec_ref(v_env_225_);
return v_b_229_;
}
v___jp_230_:
{
size_t v___x_232_; size_t v___x_233_; 
v___x_232_ = ((size_t)1ULL);
v___x_233_ = lean_usize_add(v_i_227_, v___x_232_);
v_i_227_ = v___x_233_;
v_b_229_ = v___y_231_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_initFn_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__spec__1___boxed(lean_object* v_env_240_, lean_object* v_as_241_, lean_object* v_i_242_, lean_object* v_stop_243_, lean_object* v_b_244_){
_start:
{
size_t v_i_boxed_245_; size_t v_stop_boxed_246_; lean_object* v_res_247_; 
v_i_boxed_245_ = lean_unbox_usize(v_i_242_);
lean_dec(v_i_242_);
v_stop_boxed_246_ = lean_unbox_usize(v_stop_243_);
lean_dec(v_stop_243_);
v_res_247_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_initFn_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__spec__1(v_env_240_, v_as_241_, v_i_boxed_245_, v_stop_boxed_246_, v_b_244_);
lean_dec_ref(v_as_241_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2_(lean_object* v_env_252_, lean_object* v_s_253_, uint8_t v_x_254_){
_start:
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; uint8_t v___x_260_; 
v___x_255_ = lean_unsigned_to_nat(0u);
v___x_256_ = ((lean_object*)(l_Lean_initFn___lam__0___closed__0_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2_));
v___x_257_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__spec__0_spec__0(v___x_256_, v_s_253_);
v___x_258_ = lean_array_get_size(v___x_257_);
v___x_259_ = ((lean_object*)(l_Lean_initFn___lam__0___closed__1_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2_));
v___x_260_ = lean_nat_dec_lt(v___x_255_, v___x_258_);
if (v___x_260_ == 0)
{
lean_dec_ref(v___x_257_);
lean_dec_ref(v_env_252_);
return v___x_259_;
}
else
{
uint8_t v___x_261_; 
v___x_261_ = lean_nat_dec_le(v___x_258_, v___x_258_);
if (v___x_261_ == 0)
{
if (v___x_260_ == 0)
{
lean_dec_ref(v___x_257_);
lean_dec_ref(v_env_252_);
return v___x_259_;
}
else
{
size_t v___x_262_; size_t v___x_263_; lean_object* v___x_264_; 
v___x_262_ = ((size_t)0ULL);
v___x_263_ = lean_usize_of_nat(v___x_258_);
v___x_264_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_initFn_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__spec__1(v_env_252_, v___x_257_, v___x_262_, v___x_263_, v___x_259_);
lean_dec_ref(v___x_257_);
return v___x_264_;
}
}
else
{
size_t v___x_265_; size_t v___x_266_; lean_object* v___x_267_; 
v___x_265_ = ((size_t)0ULL);
v___x_266_ = lean_usize_of_nat(v___x_258_);
v___x_267_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_initFn_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__spec__1(v_env_252_, v___x_257_, v___x_265_, v___x_266_, v___x_259_);
lean_dec_ref(v___x_257_);
return v___x_267_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2____boxed(lean_object* v_env_268_, lean_object* v_s_269_, lean_object* v_x_270_){
_start:
{
uint8_t v_x_408__boxed_271_; lean_object* v_res_272_; 
v_x_408__boxed_271_ = lean_unbox(v_x_270_);
v_res_272_ = l_Lean_initFn___lam__0_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2_(v_env_268_, v_s_269_, v_x_408__boxed_271_);
lean_dec(v_s_269_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v___f_279_ = ((lean_object*)(l_Lean_initFn___closed__0_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2_));
v___x_280_ = ((lean_object*)(l_Lean_initFn___closed__2_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2_));
v___x_281_ = lean_box(2);
v___x_282_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_280_, v___x_281_, v___f_279_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2____boxed(lean_object* v_a_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Lean_initFn_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2_();
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__spec__0(lean_object* v_init_285_, lean_object* v_t_286_){
_start:
{
lean_object* v___x_287_; 
v___x_287_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__spec__0_spec__0(v_init_285_, v_t_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_288_, lean_object* v_t_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__spec__0(v_init_288_, v_t_289_);
lean_dec(v_t_289_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_markNoConfusion(lean_object* v_env_291_, lean_object* v_n_292_, lean_object* v_info_293_){
_start:
{
lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_294_ = l_Lean_noConfusionExt;
v___x_295_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_294_, v_env_291_, v_n_292_, v_info_293_);
return v___x_295_;
}
}
LEAN_EXPORT uint8_t l_Lean_isNoConfusion(lean_object* v_env_296_, lean_object* v_n_297_){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; uint8_t v___x_300_; 
v___x_298_ = ((lean_object*)(l_Lean_instInhabitedNoConfusionInfo_default));
v___x_299_ = l_Lean_noConfusionExt;
v___x_300_ = l_Lean_MapDeclarationExtension_contains___redArg(v___x_298_, v___x_299_, v_env_296_, v_n_297_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_isNoConfusion___boxed(lean_object* v_env_301_, lean_object* v_n_302_){
_start:
{
uint8_t v_res_303_; lean_object* v_r_304_; 
v_res_303_ = l_Lean_isNoConfusion(v_env_301_, v_n_302_);
v_r_304_ = lean_box(v_res_303_);
return v_r_304_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getNoConfusionInfo_spec__0(lean_object* v_msg_305_){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_306_ = ((lean_object*)(l_Lean_instInhabitedNoConfusionInfo_default));
v___x_307_ = lean_panic_fn(v___x_306_, v_msg_305_);
return v___x_307_;
}
}
static lean_object* _init_l_Lean_getNoConfusionInfo___closed__3(void){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_311_ = ((lean_object*)(l_Lean_getNoConfusionInfo___closed__2));
v___x_312_ = lean_unsigned_to_nat(14u);
v___x_313_ = lean_unsigned_to_nat(22u);
v___x_314_ = ((lean_object*)(l_Lean_getNoConfusionInfo___closed__1));
v___x_315_ = ((lean_object*)(l_Lean_getNoConfusionInfo___closed__0));
v___x_316_ = l_mkPanicMessageWithDecl(v___x_315_, v___x_314_, v___x_313_, v___x_312_, v___x_311_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_getNoConfusionInfo(lean_object* v_env_317_, lean_object* v_n_318_){
_start:
{
lean_object* v___x_319_; lean_object* v_toEnvExtension_320_; lean_object* v_asyncMode_321_; lean_object* v___x_322_; uint8_t v___x_323_; lean_object* v___x_324_; 
v___x_319_ = l_Lean_noConfusionExt;
v_toEnvExtension_320_ = lean_ctor_get(v___x_319_, 0);
lean_inc_ref(v_toEnvExtension_320_);
v_asyncMode_321_ = lean_ctor_get(v_toEnvExtension_320_, 2);
lean_inc(v_asyncMode_321_);
lean_dec_ref(v_toEnvExtension_320_);
v___x_322_ = ((lean_object*)(l_Lean_instInhabitedNoConfusionInfo_default));
v___x_323_ = 0;
v___x_324_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_322_, v___x_319_, v_env_317_, v_n_318_, v_asyncMode_321_, v___x_323_);
lean_dec(v_asyncMode_321_);
if (lean_obj_tag(v___x_324_) == 0)
{
lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_325_ = lean_obj_once(&l_Lean_getNoConfusionInfo___closed__3, &l_Lean_getNoConfusionInfo___closed__3_once, _init_l_Lean_getNoConfusionInfo___closed__3);
v___x_326_ = l_panic___at___00Lean_getNoConfusionInfo_spec__0(v___x_325_);
return v___x_326_;
}
else
{
lean_object* v_val_327_; 
v_val_327_ = lean_ctor_get(v___x_324_, 0);
lean_inc(v_val_327_);
lean_dec_ref(v___x_324_);
return v_val_327_;
}
}
}
lean_object* runtime_initialize_Lean_EnvExtension(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_AuxRecursor(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_EnvExtension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_initFn_00___x40_Lean_AuxRecursor_3622182683____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_auxRecExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_auxRecExt);
lean_dec_ref(res);
res = l___private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_2879463644____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_AuxRecursor_0__Lean_sparseCasesOnExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_AuxRecursor_0__Lean_sparseCasesOnExt);
lean_dec_ref(res);
res = l_Lean_initFn_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2_();
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

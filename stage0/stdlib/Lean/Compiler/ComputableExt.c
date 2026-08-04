// Lean compiler output
// Module: Lean.Compiler.ComputableExt
// Imports: public import Lean.EnvExtension public import Lean.Meta.Basic import Lean.ProjFns import Lean.AuxRecursor import Lean.Compiler.CSimpAttr import Lean.Compiler.InlineAttrs import Lean.Meta.InferType import Lean.Meta.Match.MatcherInfo
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_mkTagDeclarationExtension(lean_object*, lean_object*);
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_Compiler_CSimp_instInhabitedState_default;
uint8_t l_Lean_Environment_isConstructor(lean_object*, lean_object*);
uint8_t l_Lean_isCasesOnLike(lean_object*, lean_object*);
uint8_t l_Lean_isNoConfusion(lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_CSimp_ext;
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_Compiler_hasMacroInlineAttribute(lean_object*, lean_object*);
uint8_t l_Lean_Meta_isMatcherCore(lean_object*, lean_object*);
uint8_t l_Lean_Meta_isMatcherLikeCore(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
uint8_t l_Lean_Environment_isProjectionFn(lean_object*, lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeFormerType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_ComputableExt_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_ComputableExt_3697054860____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Compiler_ComputableExt_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_ComputableExt_3697054860____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_ComputableExt_3697054860____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_ComputableExt_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_ComputableExt_3697054860____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "computableExt"};
static const lean_object* l___private_Lean_Compiler_ComputableExt_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_ComputableExt_3697054860____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_ComputableExt_3697054860____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_ComputableExt_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_ComputableExt_3697054860____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_ComputableExt_3697054860____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Compiler_ComputableExt_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_ComputableExt_3697054860____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_ComputableExt_3697054860____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_ComputableExt_3697054860____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(215, 71, 92, 78, 135, 64, 1, 51)}};
static const lean_object* l___private_Lean_Compiler_ComputableExt_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_ComputableExt_3697054860____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_ComputableExt_3697054860____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ComputableExt_0__Lean_initFn_00___x40_Lean_Compiler_ComputableExt_3697054860____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ComputableExt_0__Lean_initFn_00___x40_Lean_Compiler_ComputableExt_3697054860____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_computableExt;
LEAN_EXPORT lean_object* l_Lean_addNoncomputable___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addNoncomputable___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addNoncomputable(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addNoncomputable___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addComputable(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Quot"};
static const lean_object* l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__0 = (const lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__0_value;
static const lean_string_object l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lift"};
static const lean_object* l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__1 = (const lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__1_value;
static const lean_ctor_object l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__0_value),LEAN_SCALAR_PTR_LITERAL(91, 127, 250, 116, 111, 99, 160, 200)}};
static const lean_ctor_object l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__1_value),LEAN_SCALAR_PTR_LITERAL(91, 125, 38, 34, 222, 200, 201, 80)}};
static const lean_object* l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__2 = (const lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__2_value;
static const lean_string_object l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__3 = (const lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__3_value;
static const lean_ctor_object l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__0_value),LEAN_SCALAR_PTR_LITERAL(91, 127, 250, 116, 111, 99, 160, 200)}};
static const lean_ctor_object l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__3_value),LEAN_SCALAR_PTR_LITERAL(255, 113, 137, 82, 82, 132, 58, 248)}};
static const lean_object* l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__4 = (const lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__4_value;
static const lean_string_object l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__5 = (const lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__5_value;
static const lean_string_object l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rec"};
static const lean_object* l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__6 = (const lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__6_value;
static const lean_ctor_object l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__5_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__6_value),LEAN_SCALAR_PTR_LITERAL(86, 17, 7, 2, 233, 148, 36, 75)}};
static const lean_object* l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__7 = (const lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__7_value;
static const lean_string_object l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "recOn"};
static const lean_object* l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__8 = (const lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__8_value;
static const lean_ctor_object l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__5_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__8_value),LEAN_SCALAR_PTR_LITERAL(207, 56, 58, 111, 136, 71, 194, 11)}};
static const lean_object* l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__9 = (const lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__9_value;
static const lean_string_object l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ndrec"};
static const lean_object* l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__10 = (const lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__10_value;
static const lean_ctor_object l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__5_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__10_value),LEAN_SCALAR_PTR_LITERAL(115, 164, 251, 202, 217, 58, 77, 179)}};
static const lean_object* l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__11 = (const lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__11_value;
static const lean_string_object l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "HEq"};
static const lean_object* l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__12 = (const lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__12_value;
static const lean_ctor_object l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__12_value),LEAN_SCALAR_PTR_LITERAL(67, 180, 169, 191, 74, 196, 152, 188)}};
static const lean_ctor_object l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__13_value_aux_0),((lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__6_value),LEAN_SCALAR_PTR_LITERAL(154, 72, 177, 37, 35, 66, 175, 127)}};
static const lean_object* l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__13 = (const lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__13_value;
static const lean_ctor_object l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__12_value),LEAN_SCALAR_PTR_LITERAL(67, 180, 169, 191, 74, 196, 152, 188)}};
static const lean_ctor_object l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__10_value),LEAN_SCALAR_PTR_LITERAL(7, 86, 165, 32, 90, 213, 176, 216)}};
static const lean_object* l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__14 = (const lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__14_value;
static const lean_string_object l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "And"};
static const lean_object* l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__15 = (const lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__15_value;
static const lean_ctor_object l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__15_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_ctor_object l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__16_value_aux_0),((lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__6_value),LEAN_SCALAR_PTR_LITERAL(192, 86, 186, 46, 229, 41, 245, 36)}};
static const lean_object* l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__16 = (const lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__16_value;
static const lean_string_object l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Iff"};
static const lean_object* l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__17 = (const lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__17_value;
static const lean_ctor_object l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__17_value),LEAN_SCALAR_PTR_LITERAL(19, 54, 203, 28, 77, 25, 163, 137)}};
static const lean_ctor_object l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__18_value_aux_0),((lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__6_value),LEAN_SCALAR_PTR_LITERAL(138, 106, 229, 132, 85, 98, 57, 253)}};
static const lean_object* l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__18 = (const lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__18_value;
static const lean_string_object l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "False"};
static const lean_object* l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__19 = (const lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__19_value;
static const lean_ctor_object l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__19_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_ctor_object l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__20_value_aux_0),((lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__6_value),LEAN_SCALAR_PTR_LITERAL(122, 221, 252, 198, 56, 59, 37, 193)}};
static const lean_object* l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__20 = (const lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__20_value;
static const lean_string_object l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Empty"};
static const lean_object* l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__21 = (const lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__21_value;
static const lean_ctor_object l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__21_value),LEAN_SCALAR_PTR_LITERAL(145, 208, 51, 224, 197, 14, 63, 134)}};
static const lean_ctor_object l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__22_value_aux_0),((lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__6_value),LEAN_SCALAR_PTR_LITERAL(224, 106, 251, 72, 254, 34, 118, 241)}};
static const lean_object* l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__22 = (const lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__22_value;
static const lean_string_object l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "lcUnreachable"};
static const lean_object* l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__23 = (const lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__23_value;
static const lean_ctor_object l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__23_value),LEAN_SCALAR_PTR_LITERAL(244, 152, 7, 242, 102, 125, 47, 175)}};
static const lean_object* l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__24 = (const lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__24_value;
static const lean_array_object l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*12, .m_other = 0, .m_tag = 246}, .m_size = 12, .m_capacity = 12, .m_data = {((lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__2_value),((lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__4_value),((lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__7_value),((lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__9_value),((lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__11_value),((lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__13_value),((lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__14_value),((lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__16_value),((lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__18_value),((lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__20_value),((lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__22_value),((lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__24_value)}};
static const lean_object* l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__25 = (const lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__25_value;
LEAN_EXPORT const lean_object* l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases = (const lean_object*)&l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases___closed__25_value;
LEAN_EXPORT uint8_t l_Lean_isDirectlyComputable(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isDirectlyComputable___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_isComputable_spec__0_spec__1_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_isComputable_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_isComputable_spec__0_spec__1_spec__3___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_isComputable_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_isComputable_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_isComputable_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_isComputable_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_isComputable_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_isComputable_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_isComputable_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_SMap_contains___at___00Lean_isComputable_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_contains___at___00Lean_isComputable_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_isComputable_spec__1_spec__3(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_isComputable_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_isComputable_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_isComputable_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_isComputable(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isComputable___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_SMap_contains___at___00Lean_isComputable_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_contains___at___00Lean_isComputable_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_isComputable_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_isComputable_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_isComputable_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_isComputable_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_isComputable_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_isComputable_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_isComputable_spec__0_spec__1_spec__3(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_isComputable_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_isComputable_spec__0_spec__1_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_isComputable_spec__0_spec__1_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isComputableOrIrrelevant(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isComputableOrIrrelevant___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_isNoncomputable(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isNoncomputable___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ComputableExt_0__Lean_initFn_00___x40_Lean_Compiler_ComputableExt_3697054860____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_7_ = ((lean_object*)(l___private_Lean_Compiler_ComputableExt_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_ComputableExt_3697054860____hygCtx___hyg_2_));
v___x_8_ = lean_box(0);
v___x_9_ = l_Lean_mkTagDeclarationExtension(v___x_7_, v___x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ComputableExt_0__Lean_initFn_00___x40_Lean_Compiler_ComputableExt_3697054860____hygCtx___hyg_2____boxed(lean_object* v_a_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l___private_Lean_Compiler_ComputableExt_0__Lean_initFn_00___x40_Lean_Compiler_ComputableExt_3697054860____hygCtx___hyg_2_();
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_addNoncomputable___redArg(lean_object* v_env_12_){
_start:
{
lean_inc_ref(v_env_12_);
return v_env_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_addNoncomputable___redArg___boxed(lean_object* v_env_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Lean_addNoncomputable___redArg(v_env_13_);
lean_dec_ref(v_env_13_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_addNoncomputable(lean_object* v_env_15_, lean_object* v___declName_16_){
_start:
{
lean_inc_ref(v_env_15_);
return v_env_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_addNoncomputable___boxed(lean_object* v_env_17_, lean_object* v___declName_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l_Lean_addNoncomputable(v_env_17_, v___declName_18_);
lean_dec(v___declName_18_);
lean_dec_ref(v_env_17_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_addComputable(lean_object* v_env_20_, lean_object* v_declName_21_){
_start:
{
lean_object* v___x_22_; lean_object* v_toEnvExtension_23_; lean_object* v_asyncMode_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_22_ = l_Lean_computableExt;
v_toEnvExtension_23_ = lean_ctor_get(v___x_22_, 0);
v_asyncMode_24_ = lean_ctor_get(v_toEnvExtension_23_, 2);
v___x_25_ = lean_box(0);
v___x_26_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_22_, v_env_20_, v_declName_21_, v_asyncMode_24_, v___x_25_);
return v___x_26_;
}
}
LEAN_EXPORT uint8_t l_Lean_isDirectlyComputable(lean_object* v_env_102_, lean_object* v_declName_103_, lean_object* v_asyncMode_104_){
_start:
{
lean_object* v___x_105_; uint8_t v___x_106_; 
v___x_105_ = l_Lean_computableExt;
v___x_106_ = l_Lean_TagDeclarationExtension_isTagged(v___x_105_, v_env_102_, v_declName_103_, v_asyncMode_104_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_isDirectlyComputable___boxed(lean_object* v_env_107_, lean_object* v_declName_108_, lean_object* v_asyncMode_109_){
_start:
{
uint8_t v_res_110_; lean_object* v_r_111_; 
v_res_110_ = l_Lean_isDirectlyComputable(v_env_107_, v_declName_108_, v_asyncMode_109_);
lean_dec(v_asyncMode_109_);
v_r_111_ = lean_box(v_res_110_);
return v_r_111_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_isComputable_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_keys_112_, lean_object* v_i_113_, lean_object* v_k_114_){
_start:
{
lean_object* v___x_115_; uint8_t v___x_116_; 
v___x_115_ = lean_array_get_size(v_keys_112_);
v___x_116_ = lean_nat_dec_lt(v_i_113_, v___x_115_);
if (v___x_116_ == 0)
{
lean_dec(v_i_113_);
return v___x_116_;
}
else
{
lean_object* v_k_x27_117_; uint8_t v___x_118_; 
v_k_x27_117_ = lean_array_fget_borrowed(v_keys_112_, v_i_113_);
v___x_118_ = lean_name_eq(v_k_114_, v_k_x27_117_);
if (v___x_118_ == 0)
{
lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_119_ = lean_unsigned_to_nat(1u);
v___x_120_ = lean_nat_add(v_i_113_, v___x_119_);
lean_dec(v_i_113_);
v_i_113_ = v___x_120_;
goto _start;
}
else
{
lean_dec(v_i_113_);
return v___x_118_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_isComputable_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_keys_122_, lean_object* v_i_123_, lean_object* v_k_124_){
_start:
{
uint8_t v_res_125_; lean_object* v_r_126_; 
v_res_125_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_isComputable_spec__0_spec__1_spec__3_spec__5___redArg(v_keys_122_, v_i_123_, v_k_124_);
lean_dec(v_k_124_);
lean_dec_ref(v_keys_122_);
v_r_126_ = lean_box(v_res_125_);
return v_r_126_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_isComputable_spec__0_spec__1_spec__3___redArg(lean_object* v_x_127_, size_t v_x_128_, lean_object* v_x_129_){
_start:
{
if (lean_obj_tag(v_x_127_) == 0)
{
lean_object* v_es_130_; lean_object* v___x_131_; size_t v___x_132_; size_t v___x_133_; lean_object* v_j_134_; lean_object* v___x_135_; 
v_es_130_ = lean_ctor_get(v_x_127_, 0);
v___x_131_ = lean_box(2);
v___x_132_ = ((size_t)31ULL);
v___x_133_ = lean_usize_land(v_x_128_, v___x_132_);
v_j_134_ = lean_usize_to_nat(v___x_133_);
v___x_135_ = lean_array_get_borrowed(v___x_131_, v_es_130_, v_j_134_);
lean_dec(v_j_134_);
switch(lean_obj_tag(v___x_135_))
{
case 0:
{
lean_object* v_key_136_; uint8_t v___x_137_; 
v_key_136_ = lean_ctor_get(v___x_135_, 0);
v___x_137_ = lean_name_eq(v_x_129_, v_key_136_);
return v___x_137_;
}
case 1:
{
lean_object* v_node_138_; size_t v___x_139_; size_t v___x_140_; 
v_node_138_ = lean_ctor_get(v___x_135_, 0);
v___x_139_ = ((size_t)5ULL);
v___x_140_ = lean_usize_shift_right(v_x_128_, v___x_139_);
v_x_127_ = v_node_138_;
v_x_128_ = v___x_140_;
goto _start;
}
default: 
{
uint8_t v___x_142_; 
v___x_142_ = 0;
return v___x_142_;
}
}
}
else
{
lean_object* v_ks_143_; lean_object* v___x_144_; uint8_t v___x_145_; 
v_ks_143_ = lean_ctor_get(v_x_127_, 0);
v___x_144_ = lean_unsigned_to_nat(0u);
v___x_145_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_isComputable_spec__0_spec__1_spec__3_spec__5___redArg(v_ks_143_, v___x_144_, v_x_129_);
return v___x_145_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_isComputable_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_x_146_, lean_object* v_x_147_, lean_object* v_x_148_){
_start:
{
size_t v_x_729__boxed_149_; uint8_t v_res_150_; lean_object* v_r_151_; 
v_x_729__boxed_149_ = lean_unbox_usize(v_x_147_);
lean_dec(v_x_147_);
v_res_150_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_isComputable_spec__0_spec__1_spec__3___redArg(v_x_146_, v_x_729__boxed_149_, v_x_148_);
lean_dec(v_x_148_);
lean_dec_ref(v_x_146_);
v_r_151_ = lean_box(v_res_150_);
return v_r_151_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_isComputable_spec__0_spec__1___redArg(lean_object* v_x_152_, lean_object* v_x_153_){
_start:
{
uint64_t v___y_155_; 
if (lean_obj_tag(v_x_153_) == 0)
{
uint64_t v___x_158_; 
v___x_158_ = 1723ULL;
v___y_155_ = v___x_158_;
goto v___jp_154_;
}
else
{
uint64_t v_hash_159_; 
v_hash_159_ = lean_ctor_get_uint64(v_x_153_, sizeof(void*)*2);
v___y_155_ = v_hash_159_;
goto v___jp_154_;
}
v___jp_154_:
{
size_t v___x_156_; uint8_t v___x_157_; 
v___x_156_ = lean_uint64_to_usize(v___y_155_);
v___x_157_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_isComputable_spec__0_spec__1_spec__3___redArg(v_x_152_, v___x_156_, v_x_153_);
return v___x_157_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_isComputable_spec__0_spec__1___redArg___boxed(lean_object* v_x_160_, lean_object* v_x_161_){
_start:
{
uint8_t v_res_162_; lean_object* v_r_163_; 
v_res_162_ = l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_isComputable_spec__0_spec__1___redArg(v_x_160_, v_x_161_);
lean_dec(v_x_161_);
lean_dec_ref(v_x_160_);
v_r_163_ = lean_box(v_res_162_);
return v_r_163_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_isComputable_spec__0_spec__0_spec__1___redArg(lean_object* v_a_164_, lean_object* v_x_165_){
_start:
{
if (lean_obj_tag(v_x_165_) == 0)
{
uint8_t v___x_166_; 
v___x_166_ = 0;
return v___x_166_;
}
else
{
lean_object* v_key_167_; lean_object* v_tail_168_; uint8_t v___x_169_; 
v_key_167_ = lean_ctor_get(v_x_165_, 0);
v_tail_168_ = lean_ctor_get(v_x_165_, 2);
v___x_169_ = lean_name_eq(v_key_167_, v_a_164_);
if (v___x_169_ == 0)
{
v_x_165_ = v_tail_168_;
goto _start;
}
else
{
return v___x_169_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_isComputable_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_a_171_, lean_object* v_x_172_){
_start:
{
uint8_t v_res_173_; lean_object* v_r_174_; 
v_res_173_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_isComputable_spec__0_spec__0_spec__1___redArg(v_a_171_, v_x_172_);
lean_dec(v_x_172_);
lean_dec(v_a_171_);
v_r_174_ = lean_box(v_res_173_);
return v_r_174_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_isComputable_spec__0_spec__0___redArg(lean_object* v_m_175_, lean_object* v_a_176_){
_start:
{
lean_object* v_buckets_177_; lean_object* v___x_178_; uint64_t v___y_180_; 
v_buckets_177_ = lean_ctor_get(v_m_175_, 1);
v___x_178_ = lean_array_get_size(v_buckets_177_);
if (lean_obj_tag(v_a_176_) == 0)
{
uint64_t v___x_194_; 
v___x_194_ = 1723ULL;
v___y_180_ = v___x_194_;
goto v___jp_179_;
}
else
{
uint64_t v_hash_195_; 
v_hash_195_ = lean_ctor_get_uint64(v_a_176_, sizeof(void*)*2);
v___y_180_ = v_hash_195_;
goto v___jp_179_;
}
v___jp_179_:
{
uint64_t v___x_181_; uint64_t v___x_182_; uint64_t v_fold_183_; uint64_t v___x_184_; uint64_t v___x_185_; uint64_t v___x_186_; size_t v___x_187_; size_t v___x_188_; size_t v___x_189_; size_t v___x_190_; size_t v___x_191_; lean_object* v___x_192_; uint8_t v___x_193_; 
v___x_181_ = 32ULL;
v___x_182_ = lean_uint64_shift_right(v___y_180_, v___x_181_);
v_fold_183_ = lean_uint64_xor(v___y_180_, v___x_182_);
v___x_184_ = 16ULL;
v___x_185_ = lean_uint64_shift_right(v_fold_183_, v___x_184_);
v___x_186_ = lean_uint64_xor(v_fold_183_, v___x_185_);
v___x_187_ = lean_uint64_to_usize(v___x_186_);
v___x_188_ = lean_usize_of_nat(v___x_178_);
v___x_189_ = ((size_t)1ULL);
v___x_190_ = lean_usize_sub(v___x_188_, v___x_189_);
v___x_191_ = lean_usize_land(v___x_187_, v___x_190_);
v___x_192_ = lean_array_uget_borrowed(v_buckets_177_, v___x_191_);
v___x_193_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_isComputable_spec__0_spec__0_spec__1___redArg(v_a_176_, v___x_192_);
return v___x_193_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_isComputable_spec__0_spec__0___redArg___boxed(lean_object* v_m_196_, lean_object* v_a_197_){
_start:
{
uint8_t v_res_198_; lean_object* v_r_199_; 
v_res_198_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_isComputable_spec__0_spec__0___redArg(v_m_196_, v_a_197_);
lean_dec(v_a_197_);
lean_dec_ref(v_m_196_);
v_r_199_ = lean_box(v_res_198_);
return v_r_199_;
}
}
LEAN_EXPORT uint8_t l_Lean_SMap_contains___at___00Lean_isComputable_spec__0___redArg(lean_object* v_x_200_, lean_object* v_x_201_){
_start:
{
uint8_t v_stage_u2081_202_; 
v_stage_u2081_202_ = lean_ctor_get_uint8(v_x_200_, sizeof(void*)*2);
if (v_stage_u2081_202_ == 0)
{
lean_object* v_map_u2081_203_; lean_object* v_map_u2082_204_; uint8_t v___x_205_; 
v_map_u2081_203_ = lean_ctor_get(v_x_200_, 0);
v_map_u2082_204_ = lean_ctor_get(v_x_200_, 1);
v___x_205_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_isComputable_spec__0_spec__0___redArg(v_map_u2081_203_, v_x_201_);
if (v___x_205_ == 0)
{
uint8_t v___x_206_; 
v___x_206_ = l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_isComputable_spec__0_spec__1___redArg(v_map_u2082_204_, v_x_201_);
return v___x_206_;
}
else
{
return v___x_205_;
}
}
else
{
lean_object* v_map_u2081_207_; uint8_t v___x_208_; 
v_map_u2081_207_ = lean_ctor_get(v_x_200_, 0);
v___x_208_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_isComputable_spec__0_spec__0___redArg(v_map_u2081_207_, v_x_201_);
return v___x_208_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_contains___at___00Lean_isComputable_spec__0___redArg___boxed(lean_object* v_x_209_, lean_object* v_x_210_){
_start:
{
uint8_t v_res_211_; lean_object* v_r_212_; 
v_res_211_ = l_Lean_SMap_contains___at___00Lean_isComputable_spec__0___redArg(v_x_209_, v_x_210_);
lean_dec(v_x_210_);
lean_dec_ref(v_x_209_);
v_r_212_ = lean_box(v_res_211_);
return v_r_212_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_isComputable_spec__1_spec__3(lean_object* v_a_213_, lean_object* v_as_214_, size_t v_i_215_, size_t v_stop_216_){
_start:
{
uint8_t v___x_217_; 
v___x_217_ = lean_usize_dec_eq(v_i_215_, v_stop_216_);
if (v___x_217_ == 0)
{
lean_object* v___x_218_; uint8_t v___x_219_; 
v___x_218_ = lean_array_uget_borrowed(v_as_214_, v_i_215_);
v___x_219_ = lean_name_eq(v_a_213_, v___x_218_);
if (v___x_219_ == 0)
{
size_t v___x_220_; size_t v___x_221_; 
v___x_220_ = ((size_t)1ULL);
v___x_221_ = lean_usize_add(v_i_215_, v___x_220_);
v_i_215_ = v___x_221_;
goto _start;
}
else
{
return v___x_219_;
}
}
else
{
uint8_t v___x_223_; 
v___x_223_ = 0;
return v___x_223_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_isComputable_spec__1_spec__3___boxed(lean_object* v_a_224_, lean_object* v_as_225_, lean_object* v_i_226_, lean_object* v_stop_227_){
_start:
{
size_t v_i_boxed_228_; size_t v_stop_boxed_229_; uint8_t v_res_230_; lean_object* v_r_231_; 
v_i_boxed_228_ = lean_unbox_usize(v_i_226_);
lean_dec(v_i_226_);
v_stop_boxed_229_ = lean_unbox_usize(v_stop_227_);
lean_dec(v_stop_227_);
v_res_230_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_isComputable_spec__1_spec__3(v_a_224_, v_as_225_, v_i_boxed_228_, v_stop_boxed_229_);
lean_dec_ref(v_as_225_);
lean_dec(v_a_224_);
v_r_231_ = lean_box(v_res_230_);
return v_r_231_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_isComputable_spec__1(lean_object* v_as_232_, lean_object* v_a_233_){
_start:
{
lean_object* v___x_234_; lean_object* v___x_235_; uint8_t v___x_236_; 
v___x_234_ = lean_unsigned_to_nat(0u);
v___x_235_ = lean_array_get_size(v_as_232_);
v___x_236_ = lean_nat_dec_lt(v___x_234_, v___x_235_);
if (v___x_236_ == 0)
{
return v___x_236_;
}
else
{
if (v___x_236_ == 0)
{
return v___x_236_;
}
else
{
size_t v___x_237_; size_t v___x_238_; uint8_t v___x_239_; 
v___x_237_ = ((size_t)0ULL);
v___x_238_ = lean_usize_of_nat(v___x_235_);
v___x_239_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_isComputable_spec__1_spec__3(v_a_233_, v_as_232_, v___x_237_, v___x_238_);
return v___x_239_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_isComputable_spec__1___boxed(lean_object* v_as_240_, lean_object* v_a_241_){
_start:
{
uint8_t v_res_242_; lean_object* v_r_243_; 
v_res_242_ = l_Array_contains___at___00Lean_isComputable_spec__1(v_as_240_, v_a_241_);
lean_dec(v_a_241_);
lean_dec_ref(v_as_240_);
v_r_243_ = lean_box(v_res_242_);
return v_r_243_;
}
}
LEAN_EXPORT uint8_t l_Lean_isComputable(lean_object* v_env_244_, lean_object* v_declName_245_, lean_object* v_asyncMode_246_){
_start:
{
lean_object* v___x_247_; uint8_t v___y_249_; uint8_t v___x_265_; 
v___x_247_ = l_Lean_Compiler_CSimp_instInhabitedState_default;
lean_inc(v_declName_245_);
lean_inc_ref(v_env_244_);
v___x_265_ = l_Lean_isDirectlyComputable(v_env_244_, v_declName_245_, v_asyncMode_246_);
if (v___x_265_ == 0)
{
uint8_t v___x_266_; 
lean_inc(v_declName_245_);
lean_inc_ref(v_env_244_);
v___x_266_ = l_Lean_Environment_isProjectionFn(v_env_244_, v_declName_245_);
v___y_249_ = v___x_266_;
goto v___jp_248_;
}
else
{
v___y_249_ = v___x_265_;
goto v___jp_248_;
}
v___jp_248_:
{
if (v___y_249_ == 0)
{
uint8_t v___x_250_; 
lean_inc(v_declName_245_);
lean_inc_ref(v_env_244_);
v___x_250_ = l_Lean_Environment_isConstructor(v_env_244_, v_declName_245_);
if (v___x_250_ == 0)
{
uint8_t v___x_251_; 
lean_inc(v_declName_245_);
lean_inc_ref(v_env_244_);
v___x_251_ = l_Lean_isCasesOnLike(v_env_244_, v_declName_245_);
if (v___x_251_ == 0)
{
uint8_t v___x_252_; 
lean_inc(v_declName_245_);
lean_inc_ref(v_env_244_);
v___x_252_ = l_Lean_isNoConfusion(v_env_244_, v_declName_245_);
if (v___x_252_ == 0)
{
lean_object* v___x_253_; lean_object* v_ext_254_; lean_object* v_toEnvExtension_255_; lean_object* v_asyncMode_256_; lean_object* v___x_257_; lean_object* v_map_258_; uint8_t v___x_259_; 
v___x_253_ = l_Lean_Compiler_CSimp_ext;
v_ext_254_ = lean_ctor_get(v___x_253_, 1);
v_toEnvExtension_255_ = lean_ctor_get(v_ext_254_, 0);
v_asyncMode_256_ = lean_ctor_get(v_toEnvExtension_255_, 2);
lean_inc_ref(v_env_244_);
v___x_257_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_247_, v___x_253_, v_env_244_, v_asyncMode_256_);
v_map_258_ = lean_ctor_get(v___x_257_, 0);
lean_inc_ref(v_map_258_);
lean_dec(v___x_257_);
v___x_259_ = l_Lean_SMap_contains___at___00Lean_isComputable_spec__0___redArg(v_map_258_, v_declName_245_);
lean_dec_ref(v_map_258_);
if (v___x_259_ == 0)
{
uint8_t v___x_260_; 
lean_inc(v_declName_245_);
lean_inc_ref(v_env_244_);
v___x_260_ = l_Lean_Compiler_hasMacroInlineAttribute(v_env_244_, v_declName_245_);
if (v___x_260_ == 0)
{
uint8_t v___x_261_; 
lean_inc(v_declName_245_);
lean_inc_ref(v_env_244_);
v___x_261_ = l_Lean_Meta_isMatcherCore(v_env_244_, v_declName_245_);
if (v___x_261_ == 0)
{
uint8_t v___x_262_; 
lean_inc(v_declName_245_);
v___x_262_ = l_Lean_Meta_isMatcherLikeCore(v_env_244_, v_declName_245_);
if (v___x_262_ == 0)
{
lean_object* v___x_263_; uint8_t v___x_264_; 
v___x_263_ = ((lean_object*)(l___private_Lean_Compiler_ComputableExt_0__Lean_hardcodedSpecialCases));
v___x_264_ = l_Array_contains___at___00Lean_isComputable_spec__1(v___x_263_, v_declName_245_);
lean_dec(v_declName_245_);
return v___x_264_;
}
else
{
lean_dec(v_declName_245_);
return v___x_262_;
}
}
else
{
lean_dec(v_declName_245_);
lean_dec_ref(v_env_244_);
return v___x_261_;
}
}
else
{
lean_dec(v_declName_245_);
lean_dec_ref(v_env_244_);
return v___x_260_;
}
}
else
{
lean_dec(v_declName_245_);
lean_dec_ref(v_env_244_);
return v___x_259_;
}
}
else
{
lean_dec(v_declName_245_);
lean_dec_ref(v_env_244_);
return v___x_252_;
}
}
else
{
lean_dec(v_declName_245_);
lean_dec_ref(v_env_244_);
return v___x_251_;
}
}
else
{
lean_dec(v_declName_245_);
lean_dec_ref(v_env_244_);
return v___x_250_;
}
}
else
{
lean_dec(v_declName_245_);
lean_dec_ref(v_env_244_);
return v___y_249_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isComputable___boxed(lean_object* v_env_267_, lean_object* v_declName_268_, lean_object* v_asyncMode_269_){
_start:
{
uint8_t v_res_270_; lean_object* v_r_271_; 
v_res_270_ = l_Lean_isComputable(v_env_267_, v_declName_268_, v_asyncMode_269_);
lean_dec(v_asyncMode_269_);
v_r_271_ = lean_box(v_res_270_);
return v_r_271_;
}
}
LEAN_EXPORT uint8_t l_Lean_SMap_contains___at___00Lean_isComputable_spec__0(lean_object* v_00_u03b2_272_, lean_object* v_x_273_, lean_object* v_x_274_){
_start:
{
uint8_t v___x_275_; 
v___x_275_ = l_Lean_SMap_contains___at___00Lean_isComputable_spec__0___redArg(v_x_273_, v_x_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_contains___at___00Lean_isComputable_spec__0___boxed(lean_object* v_00_u03b2_276_, lean_object* v_x_277_, lean_object* v_x_278_){
_start:
{
uint8_t v_res_279_; lean_object* v_r_280_; 
v_res_279_ = l_Lean_SMap_contains___at___00Lean_isComputable_spec__0(v_00_u03b2_276_, v_x_277_, v_x_278_);
lean_dec(v_x_278_);
lean_dec_ref(v_x_277_);
v_r_280_ = lean_box(v_res_279_);
return v_r_280_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_isComputable_spec__0_spec__0(lean_object* v_00_u03b2_281_, lean_object* v_m_282_, lean_object* v_a_283_){
_start:
{
uint8_t v___x_284_; 
v___x_284_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_isComputable_spec__0_spec__0___redArg(v_m_282_, v_a_283_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_isComputable_spec__0_spec__0___boxed(lean_object* v_00_u03b2_285_, lean_object* v_m_286_, lean_object* v_a_287_){
_start:
{
uint8_t v_res_288_; lean_object* v_r_289_; 
v_res_288_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_isComputable_spec__0_spec__0(v_00_u03b2_285_, v_m_286_, v_a_287_);
lean_dec(v_a_287_);
lean_dec_ref(v_m_286_);
v_r_289_ = lean_box(v_res_288_);
return v_r_289_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_isComputable_spec__0_spec__1(lean_object* v_00_u03b2_290_, lean_object* v_x_291_, lean_object* v_x_292_){
_start:
{
uint8_t v___x_293_; 
v___x_293_ = l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_isComputable_spec__0_spec__1___redArg(v_x_291_, v_x_292_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_isComputable_spec__0_spec__1___boxed(lean_object* v_00_u03b2_294_, lean_object* v_x_295_, lean_object* v_x_296_){
_start:
{
uint8_t v_res_297_; lean_object* v_r_298_; 
v_res_297_ = l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_isComputable_spec__0_spec__1(v_00_u03b2_294_, v_x_295_, v_x_296_);
lean_dec(v_x_296_);
lean_dec_ref(v_x_295_);
v_r_298_ = lean_box(v_res_297_);
return v_r_298_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_isComputable_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_299_, lean_object* v_a_300_, lean_object* v_x_301_){
_start:
{
uint8_t v___x_302_; 
v___x_302_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_isComputable_spec__0_spec__0_spec__1___redArg(v_a_300_, v_x_301_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_isComputable_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_303_, lean_object* v_a_304_, lean_object* v_x_305_){
_start:
{
uint8_t v_res_306_; lean_object* v_r_307_; 
v_res_306_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_isComputable_spec__0_spec__0_spec__1(v_00_u03b2_303_, v_a_304_, v_x_305_);
lean_dec(v_x_305_);
lean_dec(v_a_304_);
v_r_307_ = lean_box(v_res_306_);
return v_r_307_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_isComputable_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_308_, lean_object* v_x_309_, size_t v_x_310_, lean_object* v_x_311_){
_start:
{
uint8_t v___x_312_; 
v___x_312_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_isComputable_spec__0_spec__1_spec__3___redArg(v_x_309_, v_x_310_, v_x_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_isComputable_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_313_, lean_object* v_x_314_, lean_object* v_x_315_, lean_object* v_x_316_){
_start:
{
size_t v_x_936__boxed_317_; uint8_t v_res_318_; lean_object* v_r_319_; 
v_x_936__boxed_317_ = lean_unbox_usize(v_x_315_);
lean_dec(v_x_315_);
v_res_318_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_isComputable_spec__0_spec__1_spec__3(v_00_u03b2_313_, v_x_314_, v_x_936__boxed_317_, v_x_316_);
lean_dec(v_x_316_);
lean_dec_ref(v_x_314_);
v_r_319_ = lean_box(v_res_318_);
return v_r_319_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_isComputable_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_320_, lean_object* v_keys_321_, lean_object* v_vals_322_, lean_object* v_heq_323_, lean_object* v_i_324_, lean_object* v_k_325_){
_start:
{
uint8_t v___x_326_; 
v___x_326_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_isComputable_spec__0_spec__1_spec__3_spec__5___redArg(v_keys_321_, v_i_324_, v_k_325_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_isComputable_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b2_327_, lean_object* v_keys_328_, lean_object* v_vals_329_, lean_object* v_heq_330_, lean_object* v_i_331_, lean_object* v_k_332_){
_start:
{
uint8_t v_res_333_; lean_object* v_r_334_; 
v_res_333_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_isComputable_spec__0_spec__1_spec__3_spec__5(v_00_u03b2_327_, v_keys_328_, v_vals_329_, v_heq_330_, v_i_331_, v_k_332_);
lean_dec(v_k_332_);
lean_dec_ref(v_vals_329_);
lean_dec_ref(v_keys_328_);
v_r_334_ = lean_box(v_res_333_);
return v_r_334_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_335_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_336_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
return v___x_337_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_338_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_339_ = lean_unsigned_to_nat(0u);
v___x_340_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
lean_ctor_set(v___x_340_, 1, v___x_339_);
lean_ctor_set(v___x_340_, 2, v___x_339_);
lean_ctor_set(v___x_340_, 3, v___x_339_);
lean_ctor_set(v___x_340_, 4, v___x_338_);
lean_ctor_set(v___x_340_, 5, v___x_338_);
lean_ctor_set(v___x_340_, 6, v___x_338_);
lean_ctor_set(v___x_340_, 7, v___x_338_);
lean_ctor_set(v___x_340_, 8, v___x_338_);
lean_ctor_set(v___x_340_, 9, v___x_338_);
return v___x_340_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_341_ = lean_unsigned_to_nat(32u);
v___x_342_ = lean_mk_empty_array_with_capacity(v___x_341_);
v___x_343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
return v___x_343_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_344_ = ((size_t)5ULL);
v___x_345_ = lean_unsigned_to_nat(0u);
v___x_346_ = lean_unsigned_to_nat(32u);
v___x_347_ = lean_mk_empty_array_with_capacity(v___x_346_);
v___x_348_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_349_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_349_, 0, v___x_348_);
lean_ctor_set(v___x_349_, 1, v___x_347_);
lean_ctor_set(v___x_349_, 2, v___x_345_);
lean_ctor_set(v___x_349_, 3, v___x_345_);
lean_ctor_set_usize(v___x_349_, 4, v___x_344_);
return v___x_349_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_350_ = lean_box(1);
v___x_351_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
v___x_352_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_353_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_353_, 0, v___x_352_);
lean_ctor_set(v___x_353_, 1, v___x_351_);
lean_ctor_set(v___x_353_, 2, v___x_350_);
return v___x_353_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7(void){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_355_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6));
v___x_356_ = l_Lean_stringToMessageData(v___x_355_);
return v___x_356_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9(void){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_358_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8));
v___x_359_ = l_Lean_stringToMessageData(v___x_358_);
return v___x_359_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11(void){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_361_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10));
v___x_362_ = l_Lean_stringToMessageData(v___x_361_);
return v___x_362_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13(void){
_start:
{
lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_364_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12));
v___x_365_ = l_Lean_stringToMessageData(v___x_364_);
return v___x_365_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15(void){
_start:
{
lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_367_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14));
v___x_368_ = l_Lean_stringToMessageData(v___x_367_);
return v___x_368_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17(void){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16));
v___x_371_ = l_Lean_stringToMessageData(v___x_370_);
return v___x_371_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19(void){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18));
v___x_374_ = l_Lean_stringToMessageData(v___x_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_msg_375_, lean_object* v_declHint_376_, lean_object* v___y_377_){
_start:
{
lean_object* v___x_379_; lean_object* v_env_380_; uint8_t v___x_381_; 
v___x_379_ = lean_st_ref_get(v___y_377_);
v_env_380_ = lean_ctor_get(v___x_379_, 0);
lean_inc_ref(v_env_380_);
lean_dec(v___x_379_);
v___x_381_ = l_Lean_Name_isAnonymous(v_declHint_376_);
if (v___x_381_ == 0)
{
uint8_t v_isExporting_382_; 
v_isExporting_382_ = lean_ctor_get_uint8(v_env_380_, sizeof(void*)*8);
if (v_isExporting_382_ == 0)
{
lean_object* v___x_383_; 
lean_dec_ref(v_env_380_);
lean_dec(v_declHint_376_);
v___x_383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_383_, 0, v_msg_375_);
return v___x_383_;
}
else
{
lean_object* v___x_384_; uint8_t v___x_385_; 
lean_inc_ref(v_env_380_);
v___x_384_ = l_Lean_Environment_setExporting(v_env_380_, v___x_381_);
lean_inc(v_declHint_376_);
lean_inc_ref(v___x_384_);
v___x_385_ = l_Lean_Environment_contains(v___x_384_, v_declHint_376_, v_isExporting_382_);
if (v___x_385_ == 0)
{
lean_object* v___x_386_; 
lean_dec_ref(v___x_384_);
lean_dec_ref(v_env_380_);
lean_dec(v_declHint_376_);
v___x_386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_386_, 0, v_msg_375_);
return v___x_386_;
}
else
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v_c_392_; lean_object* v___x_393_; 
v___x_387_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_388_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
v___x_389_ = l_Lean_Options_empty;
v___x_390_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_390_, 0, v___x_384_);
lean_ctor_set(v___x_390_, 1, v___x_387_);
lean_ctor_set(v___x_390_, 2, v___x_388_);
lean_ctor_set(v___x_390_, 3, v___x_389_);
lean_inc(v_declHint_376_);
v___x_391_ = l_Lean_MessageData_ofConstName(v_declHint_376_, v___x_381_);
v_c_392_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_392_, 0, v___x_390_);
lean_ctor_set(v_c_392_, 1, v___x_391_);
v___x_393_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_380_, v_declHint_376_);
if (lean_obj_tag(v___x_393_) == 0)
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
lean_dec_ref(v_env_380_);
lean_dec(v_declHint_376_);
v___x_394_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_395_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_395_, 0, v___x_394_);
lean_ctor_set(v___x_395_, 1, v_c_392_);
v___x_396_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
v___x_397_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_397_, 0, v___x_395_);
lean_ctor_set(v___x_397_, 1, v___x_396_);
v___x_398_ = l_Lean_MessageData_note(v___x_397_);
v___x_399_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_399_, 0, v_msg_375_);
lean_ctor_set(v___x_399_, 1, v___x_398_);
v___x_400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_400_, 0, v___x_399_);
return v___x_400_;
}
else
{
lean_object* v_val_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_436_; 
v_val_401_ = lean_ctor_get(v___x_393_, 0);
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_436_ == 0)
{
v___x_403_ = v___x_393_;
v_isShared_404_ = v_isSharedCheck_436_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_val_401_);
lean_dec(v___x_393_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_436_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v_mod_408_; uint8_t v___x_409_; 
v___x_405_ = lean_box(0);
v___x_406_ = l_Lean_Environment_header(v_env_380_);
lean_dec_ref(v_env_380_);
v___x_407_ = l_Lean_EnvironmentHeader_moduleNames(v___x_406_);
v_mod_408_ = lean_array_get(v___x_405_, v___x_407_, v_val_401_);
lean_dec(v_val_401_);
lean_dec_ref(v___x_407_);
v___x_409_ = l_Lean_isPrivateName(v_declHint_376_);
lean_dec(v_declHint_376_);
if (v___x_409_ == 0)
{
lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_421_; 
v___x_410_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
v___x_411_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_411_, 0, v___x_410_);
lean_ctor_set(v___x_411_, 1, v_c_392_);
v___x_412_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
v___x_413_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_413_, 0, v___x_411_);
lean_ctor_set(v___x_413_, 1, v___x_412_);
v___x_414_ = l_Lean_MessageData_ofName(v_mod_408_);
v___x_415_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_415_, 0, v___x_413_);
lean_ctor_set(v___x_415_, 1, v___x_414_);
v___x_416_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_417_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_417_, 0, v___x_415_);
lean_ctor_set(v___x_417_, 1, v___x_416_);
v___x_418_ = l_Lean_MessageData_note(v___x_417_);
v___x_419_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_419_, 0, v_msg_375_);
lean_ctor_set(v___x_419_, 1, v___x_418_);
if (v_isShared_404_ == 0)
{
lean_ctor_set_tag(v___x_403_, 0);
lean_ctor_set(v___x_403_, 0, v___x_419_);
v___x_421_ = v___x_403_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v___x_419_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
return v___x_421_;
}
}
else
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_434_; 
v___x_423_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_424_, 0, v___x_423_);
lean_ctor_set(v___x_424_, 1, v_c_392_);
v___x_425_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
v___x_426_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_426_, 0, v___x_424_);
lean_ctor_set(v___x_426_, 1, v___x_425_);
v___x_427_ = l_Lean_MessageData_ofName(v_mod_408_);
v___x_428_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_428_, 0, v___x_426_);
lean_ctor_set(v___x_428_, 1, v___x_427_);
v___x_429_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
v___x_430_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_430_, 0, v___x_428_);
lean_ctor_set(v___x_430_, 1, v___x_429_);
v___x_431_ = l_Lean_MessageData_note(v___x_430_);
v___x_432_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_432_, 0, v_msg_375_);
lean_ctor_set(v___x_432_, 1, v___x_431_);
if (v_isShared_404_ == 0)
{
lean_ctor_set_tag(v___x_403_, 0);
lean_ctor_set(v___x_403_, 0, v___x_432_);
v___x_434_ = v___x_403_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v___x_432_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_437_; 
lean_dec_ref(v_env_380_);
lean_dec(v_declHint_376_);
v___x_437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_437_, 0, v_msg_375_);
return v___x_437_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_msg_438_, lean_object* v_declHint_439_, lean_object* v___y_440_, lean_object* v___y_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_438_, v_declHint_439_, v___y_440_);
lean_dec(v___y_440_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_msg_443_, lean_object* v_declHint_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_){
_start:
{
lean_object* v___x_450_; lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_460_; 
v___x_450_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_443_, v_declHint_444_, v___y_448_);
v_a_451_ = lean_ctor_get(v___x_450_, 0);
v_isSharedCheck_460_ = !lean_is_exclusive(v___x_450_);
if (v_isSharedCheck_460_ == 0)
{
v___x_453_ = v___x_450_;
v_isShared_454_ = v_isSharedCheck_460_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_dec(v___x_450_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_460_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_458_; 
v___x_455_ = l_Lean_unknownIdentifierMessageTag;
v___x_456_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_456_, 0, v___x_455_);
lean_ctor_set(v___x_456_, 1, v_a_451_);
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 0, v___x_456_);
v___x_458_ = v___x_453_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v___x_456_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
return v___x_458_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_msg_461_, lean_object* v_declHint_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_461_, v_declHint_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
lean_dec(v___y_464_);
lean_dec_ref(v___y_463_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(lean_object* v_msgData_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_){
_start:
{
lean_object* v___x_475_; lean_object* v_env_476_; lean_object* v___x_477_; lean_object* v_mctx_478_; lean_object* v_lctx_479_; lean_object* v_options_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_475_ = lean_st_ref_get(v___y_473_);
v_env_476_ = lean_ctor_get(v___x_475_, 0);
lean_inc_ref(v_env_476_);
lean_dec(v___x_475_);
v___x_477_ = lean_st_ref_get(v___y_471_);
v_mctx_478_ = lean_ctor_get(v___x_477_, 0);
lean_inc_ref(v_mctx_478_);
lean_dec(v___x_477_);
v_lctx_479_ = lean_ctor_get(v___y_470_, 2);
v_options_480_ = lean_ctor_get(v___y_472_, 2);
lean_inc_ref(v_options_480_);
lean_inc_ref(v_lctx_479_);
v___x_481_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_481_, 0, v_env_476_);
lean_ctor_set(v___x_481_, 1, v_mctx_478_);
lean_ctor_set(v___x_481_, 2, v_lctx_479_);
lean_ctor_set(v___x_481_, 3, v_options_480_);
v___x_482_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_482_, 0, v___x_481_);
lean_ctor_set(v___x_482_, 1, v_msgData_469_);
v___x_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___boxed(lean_object* v_msgData_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msgData_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_);
lean_dec(v___y_488_);
lean_dec_ref(v___y_487_);
lean_dec(v___y_486_);
lean_dec_ref(v___y_485_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_msg_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_){
_start:
{
lean_object* v_ref_497_; lean_object* v___x_498_; lean_object* v_a_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_507_; 
v_ref_497_ = lean_ctor_get(v___y_494_, 5);
v___x_498_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msg_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_);
v_a_499_ = lean_ctor_get(v___x_498_, 0);
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_507_ == 0)
{
v___x_501_ = v___x_498_;
v_isShared_502_ = v_isSharedCheck_507_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_a_499_);
lean_dec(v___x_498_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_507_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_503_; lean_object* v___x_505_; 
lean_inc(v_ref_497_);
v___x_503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_503_, 0, v_ref_497_);
lean_ctor_set(v___x_503_, 1, v_a_499_);
if (v_isShared_502_ == 0)
{
lean_ctor_set_tag(v___x_501_, 1);
lean_ctor_set(v___x_501_, 0, v___x_503_);
v___x_505_ = v___x_501_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v___x_503_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_msg_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_ref_515_, lean_object* v_msg_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_){
_start:
{
lean_object* v_fileName_522_; lean_object* v_fileMap_523_; lean_object* v_options_524_; lean_object* v_currRecDepth_525_; lean_object* v_maxRecDepth_526_; lean_object* v_ref_527_; lean_object* v_currNamespace_528_; lean_object* v_openDecls_529_; lean_object* v_initHeartbeats_530_; lean_object* v_maxHeartbeats_531_; lean_object* v_quotContext_532_; lean_object* v_currMacroScope_533_; uint8_t v_diag_534_; lean_object* v_cancelTk_x3f_535_; uint8_t v_suppressElabErrors_536_; lean_object* v_inheritedTraceOptions_537_; lean_object* v_ref_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v_fileName_522_ = lean_ctor_get(v___y_519_, 0);
v_fileMap_523_ = lean_ctor_get(v___y_519_, 1);
v_options_524_ = lean_ctor_get(v___y_519_, 2);
v_currRecDepth_525_ = lean_ctor_get(v___y_519_, 3);
v_maxRecDepth_526_ = lean_ctor_get(v___y_519_, 4);
v_ref_527_ = lean_ctor_get(v___y_519_, 5);
v_currNamespace_528_ = lean_ctor_get(v___y_519_, 6);
v_openDecls_529_ = lean_ctor_get(v___y_519_, 7);
v_initHeartbeats_530_ = lean_ctor_get(v___y_519_, 8);
v_maxHeartbeats_531_ = lean_ctor_get(v___y_519_, 9);
v_quotContext_532_ = lean_ctor_get(v___y_519_, 10);
v_currMacroScope_533_ = lean_ctor_get(v___y_519_, 11);
v_diag_534_ = lean_ctor_get_uint8(v___y_519_, sizeof(void*)*14);
v_cancelTk_x3f_535_ = lean_ctor_get(v___y_519_, 12);
v_suppressElabErrors_536_ = lean_ctor_get_uint8(v___y_519_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_537_ = lean_ctor_get(v___y_519_, 13);
v_ref_538_ = l_Lean_replaceRef(v_ref_515_, v_ref_527_);
lean_inc_ref(v_inheritedTraceOptions_537_);
lean_inc(v_cancelTk_x3f_535_);
lean_inc(v_currMacroScope_533_);
lean_inc(v_quotContext_532_);
lean_inc(v_maxHeartbeats_531_);
lean_inc(v_initHeartbeats_530_);
lean_inc(v_openDecls_529_);
lean_inc(v_currNamespace_528_);
lean_inc(v_maxRecDepth_526_);
lean_inc(v_currRecDepth_525_);
lean_inc_ref(v_options_524_);
lean_inc_ref(v_fileMap_523_);
lean_inc_ref(v_fileName_522_);
v___x_539_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_539_, 0, v_fileName_522_);
lean_ctor_set(v___x_539_, 1, v_fileMap_523_);
lean_ctor_set(v___x_539_, 2, v_options_524_);
lean_ctor_set(v___x_539_, 3, v_currRecDepth_525_);
lean_ctor_set(v___x_539_, 4, v_maxRecDepth_526_);
lean_ctor_set(v___x_539_, 5, v_ref_538_);
lean_ctor_set(v___x_539_, 6, v_currNamespace_528_);
lean_ctor_set(v___x_539_, 7, v_openDecls_529_);
lean_ctor_set(v___x_539_, 8, v_initHeartbeats_530_);
lean_ctor_set(v___x_539_, 9, v_maxHeartbeats_531_);
lean_ctor_set(v___x_539_, 10, v_quotContext_532_);
lean_ctor_set(v___x_539_, 11, v_currMacroScope_533_);
lean_ctor_set(v___x_539_, 12, v_cancelTk_x3f_535_);
lean_ctor_set(v___x_539_, 13, v_inheritedTraceOptions_537_);
lean_ctor_set_uint8(v___x_539_, sizeof(void*)*14, v_diag_534_);
lean_ctor_set_uint8(v___x_539_, sizeof(void*)*14 + 1, v_suppressElabErrors_536_);
v___x_540_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_516_, v___y_517_, v___y_518_, v___x_539_, v___y_520_);
lean_dec_ref_known(v___x_539_, 14);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_541_, lean_object* v_msg_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_541_, v_msg_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_);
lean_dec(v___y_546_);
lean_dec_ref(v___y_545_);
lean_dec(v___y_544_);
lean_dec_ref(v___y_543_);
lean_dec(v_ref_541_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_549_, lean_object* v_msg_550_, lean_object* v_declHint_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_){
_start:
{
lean_object* v___x_557_; lean_object* v_a_558_; lean_object* v___x_559_; 
v___x_557_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_550_, v_declHint_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_);
v_a_558_ = lean_ctor_get(v___x_557_, 0);
lean_inc(v_a_558_);
lean_dec_ref(v___x_557_);
v___x_559_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_549_, v_a_558_, v___y_552_, v___y_553_, v___y_554_, v___y_555_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_560_, lean_object* v_msg_561_, lean_object* v_declHint_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_560_, v_msg_561_, v_declHint_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_);
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
lean_dec(v_ref_560_);
return v_res_568_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_571_ = l_Lean_stringToMessageData(v___x_570_);
return v___x_571_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_573_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_574_ = l_Lean_stringToMessageData(v___x_573_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_575_, lean_object* v_constName_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
lean_object* v___x_582_; uint8_t v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_582_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_583_ = 0;
lean_inc(v_constName_576_);
v___x_584_ = l_Lean_MessageData_ofConstName(v_constName_576_, v___x_583_);
v___x_585_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_585_, 0, v___x_582_);
lean_ctor_set(v___x_585_, 1, v___x_584_);
v___x_586_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_587_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_587_, 0, v___x_585_);
lean_ctor_set(v___x_587_, 1, v___x_586_);
v___x_588_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_575_, v___x_587_, v_constName_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_589_, lean_object* v_constName_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1___redArg(v_ref_589_, v_constName_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_);
lean_dec(v___y_594_);
lean_dec_ref(v___y_593_);
lean_dec(v___y_592_);
lean_dec_ref(v___y_591_);
lean_dec(v_ref_589_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0___redArg(lean_object* v_constName_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_){
_start:
{
lean_object* v_ref_603_; lean_object* v___x_604_; 
v_ref_603_ = lean_ctor_get(v___y_600_, 5);
v___x_604_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1___redArg(v_ref_603_, v_constName_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0___redArg___boxed(lean_object* v_constName_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0___redArg(v_constName_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
lean_dec(v___y_607_);
lean_dec_ref(v___y_606_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0(lean_object* v_constName_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_){
_start:
{
lean_object* v___x_618_; lean_object* v_env_619_; uint8_t v___x_620_; lean_object* v___x_621_; 
v___x_618_ = lean_st_ref_get(v___y_616_);
v_env_619_ = lean_ctor_get(v___x_618_, 0);
lean_inc_ref(v_env_619_);
lean_dec(v___x_618_);
v___x_620_ = 0;
lean_inc(v_constName_612_);
v___x_621_ = l_Lean_Environment_findConstVal_x3f(v_env_619_, v_constName_612_, v___x_620_);
if (lean_obj_tag(v___x_621_) == 0)
{
lean_object* v___x_622_; 
v___x_622_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0___redArg(v_constName_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_);
return v___x_622_;
}
else
{
lean_object* v_val_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_630_; 
lean_dec(v_constName_612_);
v_val_623_ = lean_ctor_get(v___x_621_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_630_ == 0)
{
v___x_625_ = v___x_621_;
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_val_623_);
lean_dec(v___x_621_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_628_; 
if (v_isShared_626_ == 0)
{
lean_ctor_set_tag(v___x_625_, 0);
v___x_628_ = v___x_625_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_val_623_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0___boxed(lean_object* v_constName_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l_Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0(v_constName_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
lean_dec(v___y_633_);
lean_dec_ref(v___y_632_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_isComputableOrIrrelevant(lean_object* v_declName_638_, lean_object* v_asyncMode_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_){
_start:
{
lean_object* v___x_645_; lean_object* v_env_646_; uint8_t v___x_647_; 
v___x_645_ = lean_st_ref_get(v_a_643_);
v_env_646_ = lean_ctor_get(v___x_645_, 0);
lean_inc_ref(v_env_646_);
lean_dec(v___x_645_);
lean_inc(v_declName_638_);
v___x_647_ = l_Lean_isComputable(v_env_646_, v_declName_638_, v_asyncMode_639_);
if (v___x_647_ == 0)
{
lean_object* v___x_648_; 
v___x_648_ = l_Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0(v_declName_638_, v_a_640_, v_a_641_, v_a_642_, v_a_643_);
if (lean_obj_tag(v___x_648_) == 0)
{
lean_object* v_a_649_; lean_object* v_type_650_; lean_object* v___x_651_; 
v_a_649_ = lean_ctor_get(v___x_648_, 0);
lean_inc(v_a_649_);
lean_dec_ref_known(v___x_648_, 1);
v_type_650_ = lean_ctor_get(v_a_649_, 2);
lean_inc_ref_n(v_type_650_, 2);
lean_dec(v_a_649_);
v___x_651_ = l_Lean_Meta_isProp(v_type_650_, v_a_640_, v_a_641_, v_a_642_, v_a_643_);
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v_a_652_; uint8_t v___x_653_; 
v_a_652_ = lean_ctor_get(v___x_651_, 0);
lean_inc(v_a_652_);
v___x_653_ = lean_unbox(v_a_652_);
lean_dec(v_a_652_);
if (v___x_653_ == 0)
{
lean_object* v___x_654_; 
lean_dec_ref_known(v___x_651_, 1);
v___x_654_ = l_Lean_Meta_isTypeFormerType(v_type_650_, v_a_640_, v_a_641_, v_a_642_, v_a_643_);
return v___x_654_;
}
else
{
lean_dec_ref(v_type_650_);
return v___x_651_;
}
}
else
{
lean_dec_ref(v_type_650_);
return v___x_651_;
}
}
else
{
lean_object* v_a_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_662_; 
v_a_655_ = lean_ctor_get(v___x_648_, 0);
v_isSharedCheck_662_ = !lean_is_exclusive(v___x_648_);
if (v_isSharedCheck_662_ == 0)
{
v___x_657_ = v___x_648_;
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_a_655_);
lean_dec(v___x_648_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_660_; 
if (v_isShared_658_ == 0)
{
v___x_660_ = v___x_657_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_a_655_);
v___x_660_ = v_reuseFailAlloc_661_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
return v___x_660_;
}
}
}
}
else
{
lean_object* v___x_663_; lean_object* v___x_664_; 
lean_dec(v_declName_638_);
v___x_663_ = lean_box(v___x_647_);
v___x_664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_664_, 0, v___x_663_);
return v___x_664_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isComputableOrIrrelevant___boxed(lean_object* v_declName_665_, lean_object* v_asyncMode_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l_Lean_isComputableOrIrrelevant(v_declName_665_, v_asyncMode_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_);
lean_dec(v_a_670_);
lean_dec_ref(v_a_669_);
lean_dec(v_a_668_);
lean_dec_ref(v_a_667_);
lean_dec(v_asyncMode_666_);
return v_res_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0(lean_object* v_00_u03b1_673_, lean_object* v_constName_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_){
_start:
{
lean_object* v___x_680_; 
v___x_680_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0___redArg(v_constName_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0___boxed(lean_object* v_00_u03b1_681_, lean_object* v_constName_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0(v_00_u03b1_681_, v_constName_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
lean_dec(v___y_684_);
lean_dec_ref(v___y_683_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_689_, lean_object* v_ref_690_, lean_object* v_constName_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_){
_start:
{
lean_object* v___x_697_; 
v___x_697_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1___redArg(v_ref_690_, v_constName_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_698_, lean_object* v_ref_699_, lean_object* v_constName_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1(v_00_u03b1_698_, v_ref_699_, v_constName_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
lean_dec(v___y_704_);
lean_dec_ref(v___y_703_);
lean_dec(v___y_702_);
lean_dec_ref(v___y_701_);
lean_dec(v_ref_699_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_707_, lean_object* v_ref_708_, lean_object* v_msg_709_, lean_object* v_declHint_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_){
_start:
{
lean_object* v___x_716_; 
v___x_716_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_708_, v_msg_709_, v_declHint_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_717_, lean_object* v_ref_718_, lean_object* v_msg_719_, lean_object* v_declHint_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_){
_start:
{
lean_object* v_res_726_; 
v_res_726_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_717_, v_ref_718_, v_msg_719_, v_declHint_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
lean_dec(v_ref_718_);
return v_res_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_msg_727_, lean_object* v_declHint_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_727_, v_declHint_728_, v___y_732_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_735_, lean_object* v_declHint_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_735_, v_declHint_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_743_, lean_object* v_ref_744_, lean_object* v_msg_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_744_, v_msg_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_752_, lean_object* v_ref_753_, lean_object* v_msg_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_752_, v_ref_753_, v_msg_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_);
lean_dec(v___y_758_);
lean_dec_ref(v___y_757_);
lean_dec(v___y_756_);
lean_dec_ref(v___y_755_);
lean_dec(v_ref_753_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b1_761_, lean_object* v_msg_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_){
_start:
{
lean_object* v___x_768_; 
v___x_768_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b1_769_, lean_object* v_msg_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_isComputableOrIrrelevant_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(v_00_u03b1_769_, v_msg_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_);
lean_dec(v___y_774_);
lean_dec_ref(v___y_773_);
lean_dec(v___y_772_);
lean_dec_ref(v___y_771_);
return v_res_776_;
}
}
LEAN_EXPORT uint8_t l_Lean_isNoncomputable(lean_object* v_env_777_, lean_object* v_declName_778_, lean_object* v_asyncMode_779_){
_start:
{
uint8_t v___x_780_; 
v___x_780_ = l_Lean_isComputable(v_env_777_, v_declName_778_, v_asyncMode_779_);
if (v___x_780_ == 0)
{
uint8_t v___x_781_; 
v___x_781_ = 1;
return v___x_781_;
}
else
{
uint8_t v___x_782_; 
v___x_782_ = 0;
return v___x_782_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isNoncomputable___boxed(lean_object* v_env_783_, lean_object* v_declName_784_, lean_object* v_asyncMode_785_){
_start:
{
uint8_t v_res_786_; lean_object* v_r_787_; 
v_res_786_ = l_Lean_isNoncomputable(v_env_783_, v_declName_784_, v_asyncMode_785_);
lean_dec(v_asyncMode_785_);
v_r_787_ = lean_box(v_res_786_);
return v_r_787_;
}
}
lean_object* runtime_initialize_Lean_EnvExtension(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_ProjFns(uint8_t builtin);
lean_object* runtime_initialize_Lean_AuxRecursor(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_CSimpAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_InlineAttrs(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_InferType(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Match_MatcherInfo(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_ComputableExt(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_EnvExtension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_ProjFns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_AuxRecursor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_CSimpAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_InlineAttrs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Match_MatcherInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Compiler_ComputableExt_0__Lean_initFn_00___x40_Lean_Compiler_ComputableExt_3697054860____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_computableExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_computableExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_ComputableExt(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_EnvExtension(uint8_t builtin);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Lean_ProjFns(uint8_t builtin);
lean_object* initialize_Lean_AuxRecursor(uint8_t builtin);
lean_object* initialize_Lean_Compiler_CSimpAttr(uint8_t builtin);
lean_object* initialize_Lean_Compiler_InlineAttrs(uint8_t builtin);
lean_object* initialize_Lean_Meta_InferType(uint8_t builtin);
lean_object* initialize_Lean_Meta_Match_MatcherInfo(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_ComputableExt(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_EnvExtension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ProjFns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_AuxRecursor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_CSimpAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_InlineAttrs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_MatcherInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_ComputableExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_ComputableExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_ComputableExt(builtin);
}
#ifdef __cplusplus
}
#endif

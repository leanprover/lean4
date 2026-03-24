// Lean compiler output
// Module: Lean.Elab.AutoBound
// Imports: public import Lean.Meta.Hint
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
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArray_default(lean_object*);
extern lean_object* l_String_instInhabitedSlice;
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_String_instDecidableLtRaw___aux__1(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t l_Lean_isSubScriptAlnum(uint32_t);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Substring_Raw_nextn(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_is_valid_pos(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Elab_initFn_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Elab_initFn_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "autoImplicit"};
static const lean_object* l_Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(116, 133, 197, 206, 105, 86, 94, 221)}};
static const lean_object* l_Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 323, .m_capacity = 323, .m_length = 319, .m_data = "Unbound local variables in declaration headers become implicit arguments. In \"relaxed\" mode (default), any atomic identifier is eligible, otherwise only single character followed by numeric digits are eligible. For example, `def f (x : Vector α n) : Vector α n :=` automatically introduces the implicit variables {α n}."};
static const lean_object* l_Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(7, 67, 153, 210, 133, 79, 100, 198)}};
static const lean_object* l_Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Elab_initFn_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Elab_initFn_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_autoImplicit;
static const lean_string_object l_Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "relaxedAutoImplicit"};
static const lean_object* l_Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(143, 7, 64, 249, 212, 66, 225, 166)}};
static const lean_object* l_Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 135, .m_capacity = 135, .m_length = 134, .m_data = "When \"relaxed\" mode is enabled, any atomic nonempty identifier is eligible for auto bound implicit locals (see option `autoImplicit`)."};
static const lean_object* l_Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(76, 142, 225, 45, 175, 203, 153, 200)}};
static const lean_object* l_Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Elab_initFn_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Elab_initFn_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_relaxedAutoImplicit;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___closed__0 = (const lean_object*)&l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___closed__0_value;
static const lean_string_object l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___closed__1 = (const lean_object*)&l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___closed__1_value;
static const lean_string_object l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___closed__2 = (const lean_object*)&l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___closed__3;
LEAN_EXPORT uint8_t l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_checkValidAutoBoundImplicitName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_checkValidAutoBoundImplicitName___closed__0 = (const lean_object*)&l_Lean_Elab_checkValidAutoBoundImplicitName___closed__0_value;
static const lean_string_object l_Lean_Elab_checkValidAutoBoundImplicitName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "It is not possible to treat `"};
static const lean_object* l_Lean_Elab_checkValidAutoBoundImplicitName___closed__1 = (const lean_object*)&l_Lean_Elab_checkValidAutoBoundImplicitName___closed__1_value;
static lean_once_cell_t l_Lean_Elab_checkValidAutoBoundImplicitName___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkValidAutoBoundImplicitName___closed__2;
static const lean_string_object l_Lean_Elab_checkValidAutoBoundImplicitName___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 85, .m_capacity = 85, .m_length = 84, .m_data = "` as an implicitly bound variable here because the `autoImplicit` option is set to `"};
static const lean_object* l_Lean_Elab_checkValidAutoBoundImplicitName___closed__3 = (const lean_object*)&l_Lean_Elab_checkValidAutoBoundImplicitName___closed__3_value;
static lean_once_cell_t l_Lean_Elab_checkValidAutoBoundImplicitName___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkValidAutoBoundImplicitName___closed__4;
static const lean_string_object l_Lean_Elab_checkValidAutoBoundImplicitName___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Lean_Elab_checkValidAutoBoundImplicitName___closed__5 = (const lean_object*)&l_Lean_Elab_checkValidAutoBoundImplicitName___closed__5_value;
static const lean_string_object l_Lean_Elab_checkValidAutoBoundImplicitName___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_Elab_checkValidAutoBoundImplicitName___closed__6 = (const lean_object*)&l_Lean_Elab_checkValidAutoBoundImplicitName___closed__6_value;
static const lean_ctor_object l_Lean_Elab_checkValidAutoBoundImplicitName___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_checkValidAutoBoundImplicitName___closed__5_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Elab_checkValidAutoBoundImplicitName___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_checkValidAutoBoundImplicitName___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_checkValidAutoBoundImplicitName___closed__6_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l_Lean_Elab_checkValidAutoBoundImplicitName___closed__7 = (const lean_object*)&l_Lean_Elab_checkValidAutoBoundImplicitName___closed__7_value;
static const lean_string_object l_Lean_Elab_checkValidAutoBoundImplicitName___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_Elab_checkValidAutoBoundImplicitName___closed__8 = (const lean_object*)&l_Lean_Elab_checkValidAutoBoundImplicitName___closed__8_value;
static lean_once_cell_t l_Lean_Elab_checkValidAutoBoundImplicitName___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkValidAutoBoundImplicitName___closed__9;
static const lean_string_object l_Lean_Elab_checkValidAutoBoundImplicitName___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 125, .m_capacity = 125, .m_length = 124, .m_data = "` as an implicitly bound variable here because it has multiple characters while the `relaxedAutoImplicit` option is set to `"};
static const lean_object* l_Lean_Elab_checkValidAutoBoundImplicitName___closed__10 = (const lean_object*)&l_Lean_Elab_checkValidAutoBoundImplicitName___closed__10_value;
static lean_once_cell_t l_Lean_Elab_checkValidAutoBoundImplicitName___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkValidAutoBoundImplicitName___closed__11;
LEAN_EXPORT lean_object* l_Lean_Elab_checkValidAutoBoundImplicitName(lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_checkValidAutoBoundImplicitName___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_isValidAutoBoundLevelName(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_isValidAutoBoundLevelName___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default___closed__0;
static lean_once_cell_t l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default;
LEAN_EXPORT lean_object* l_Lean_Elab_instInhabitedAutoBoundImplicitContext;
static lean_once_cell_t l_Lean_Elab_instEmptyCollectionAutoBoundImplicitContext___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_instEmptyCollectionAutoBoundImplicitContext___closed__0;
static lean_once_cell_t l_Lean_Elab_instEmptyCollectionAutoBoundImplicitContext___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_instEmptyCollectionAutoBoundImplicitContext___closed__1;
static lean_once_cell_t l_Lean_Elab_instEmptyCollectionAutoBoundImplicitContext___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_instEmptyCollectionAutoBoundImplicitContext___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_instEmptyCollectionAutoBoundImplicitContext;
LEAN_EXPORT lean_object* l_Lean_Elab_AutoBoundImplicitContext_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Elab_initFn_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v___x_8_; uint8_t v_isShared_9_; uint8_t v_isSharedCheck_33_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_isSharedCheck_33_ = !lean_is_exclusive(v_decl_2_);
if (v_isSharedCheck_33_ == 0)
{
v___x_8_ = v_decl_2_;
v_isShared_9_ = v_isSharedCheck_33_;
goto v_resetjp_7_;
}
else
{
lean_inc(v_descr_6_);
lean_inc(v_defValue_5_);
lean_dec(v_decl_2_);
v___x_8_ = lean_box(0);
v_isShared_9_ = v_isSharedCheck_33_;
goto v_resetjp_7_;
}
v_resetjp_7_:
{
lean_object* v___x_10_; uint8_t v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_10_ = lean_alloc_ctor(1, 0, 1);
v___x_11_ = lean_unbox(v_defValue_5_);
lean_ctor_set_uint8(v___x_10_, 0, v___x_11_);
lean_inc(v_name_1_);
v___x_12_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_12_, 0, v_name_1_);
lean_ctor_set(v___x_12_, 1, v_ref_3_);
lean_ctor_set(v___x_12_, 2, v___x_10_);
lean_ctor_set(v___x_12_, 3, v_descr_6_);
lean_inc(v_name_1_);
v___x_13_ = lean_register_option(v_name_1_, v___x_12_);
if (lean_obj_tag(v___x_13_) == 0)
{
lean_object* v___x_15_; uint8_t v_isShared_16_; uint8_t v_isSharedCheck_23_; 
v_isSharedCheck_23_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_23_ == 0)
{
lean_object* v_unused_24_; 
v_unused_24_ = lean_ctor_get(v___x_13_, 0);
lean_dec(v_unused_24_);
v___x_15_ = v___x_13_;
v_isShared_16_ = v_isSharedCheck_23_;
goto v_resetjp_14_;
}
else
{
lean_dec(v___x_13_);
v___x_15_ = lean_box(0);
v_isShared_16_ = v_isSharedCheck_23_;
goto v_resetjp_14_;
}
v_resetjp_14_:
{
lean_object* v___x_18_; 
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 1, v_defValue_5_);
lean_ctor_set(v___x_8_, 0, v_name_1_);
v___x_18_ = v___x_8_;
goto v_reusejp_17_;
}
else
{
lean_object* v_reuseFailAlloc_22_; 
v_reuseFailAlloc_22_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_22_, 0, v_name_1_);
lean_ctor_set(v_reuseFailAlloc_22_, 1, v_defValue_5_);
v___x_18_ = v_reuseFailAlloc_22_;
goto v_reusejp_17_;
}
v_reusejp_17_:
{
lean_object* v___x_20_; 
if (v_isShared_16_ == 0)
{
lean_ctor_set(v___x_15_, 0, v___x_18_);
v___x_20_ = v___x_15_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_21_; 
v_reuseFailAlloc_21_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_21_, 0, v___x_18_);
v___x_20_ = v_reuseFailAlloc_21_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
return v___x_20_;
}
}
}
}
else
{
lean_object* v_a_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_32_; 
lean_del_object(v___x_8_);
lean_dec(v_defValue_5_);
lean_dec(v_name_1_);
v_a_25_ = lean_ctor_get(v___x_13_, 0);
v_isSharedCheck_32_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_32_ == 0)
{
v___x_27_ = v___x_13_;
v_isShared_28_ = v_isSharedCheck_32_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_a_25_);
lean_dec(v___x_13_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_32_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
lean_object* v___x_30_; 
if (v_isShared_28_ == 0)
{
v___x_30_ = v___x_27_;
goto v_reusejp_29_;
}
else
{
lean_object* v_reuseFailAlloc_31_; 
v_reuseFailAlloc_31_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_31_, 0, v_a_25_);
v___x_30_ = v_reuseFailAlloc_31_;
goto v_reusejp_29_;
}
v_reusejp_29_:
{
return v___x_30_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Elab_initFn_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_34_, lean_object* v_decl_35_, lean_object* v_ref_36_, lean_object* v_a_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_Option_register___at___00Lean_Elab_initFn_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__spec__0(v_name_34_, v_decl_35_, v_ref_36_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_initFn_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_54_ = ((lean_object*)(l_Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4_));
v___x_55_ = ((lean_object*)(l_Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4_));
v___x_56_ = ((lean_object*)(l_Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4_));
v___x_57_ = l_Lean_Option_register___at___00Lean_Elab_initFn_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__spec__0(v___x_54_, v___x_55_, v___x_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_initFn_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4____boxed(lean_object* v_a_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Lean_Elab_initFn_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4_();
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_initFn_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_73_ = ((lean_object*)(l_Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4_));
v___x_74_ = ((lean_object*)(l_Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4_));
v___x_75_ = ((lean_object*)(l_Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4_));
v___x_76_ = l_Lean_Option_register___at___00Lean_Elab_initFn_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__spec__0(v___x_73_, v___x_74_, v___x_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_initFn_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4____boxed(lean_object* v_a_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l_Lean_Elab_initFn_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4_();
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix_spec__1(lean_object* v_msg_79_){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_80_ = l_String_instInhabitedSlice;
v___x_81_ = lean_panic_fn(v___x_80_, v_msg_79_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix_spec__0(lean_object* v_s_82_, lean_object* v_pos_83_){
_start:
{
lean_object* v_str_84_; lean_object* v_startInclusive_85_; lean_object* v_endExclusive_86_; lean_object* v___x_87_; uint8_t v___y_95_; lean_object* v___x_96_; lean_object* v___x_97_; uint8_t v___x_98_; 
v_str_84_ = lean_ctor_get(v_s_82_, 0);
v_startInclusive_85_ = lean_ctor_get(v_s_82_, 1);
v_endExclusive_86_ = lean_ctor_get(v_s_82_, 2);
v___x_87_ = lean_nat_add(v_startInclusive_85_, v_pos_83_);
v___x_96_ = lean_unsigned_to_nat(0u);
v___x_97_ = lean_nat_sub(v_endExclusive_86_, v___x_87_);
v___x_98_ = lean_nat_dec_eq(v___x_96_, v___x_97_);
lean_dec(v___x_97_);
if (v___x_98_ == 0)
{
uint32_t v___x_99_; uint8_t v___y_101_; uint32_t v___x_107_; uint8_t v___x_108_; 
v___x_99_ = lean_string_utf8_get_fast(v_str_84_, v___x_87_);
v___x_107_ = 48;
v___x_108_ = lean_uint32_dec_le(v___x_107_, v___x_99_);
if (v___x_108_ == 0)
{
v___y_101_ = v___x_108_;
goto v___jp_100_;
}
else
{
uint32_t v___x_109_; uint8_t v___x_110_; 
v___x_109_ = 57;
v___x_110_ = lean_uint32_dec_le(v___x_99_, v___x_109_);
v___y_101_ = v___x_110_;
goto v___jp_100_;
}
v___jp_100_:
{
if (v___y_101_ == 0)
{
uint8_t v___x_102_; 
v___x_102_ = l_Lean_isSubScriptAlnum(v___x_99_);
if (v___x_102_ == 0)
{
uint32_t v___x_103_; uint8_t v___x_104_; 
v___x_103_ = 95;
v___x_104_ = lean_uint32_dec_eq(v___x_99_, v___x_103_);
if (v___x_104_ == 0)
{
uint32_t v___x_105_; uint8_t v___x_106_; 
v___x_105_ = 39;
v___x_106_ = lean_uint32_dec_eq(v___x_99_, v___x_105_);
v___y_95_ = v___x_106_;
goto v___jp_94_;
}
else
{
v___y_95_ = v___x_104_;
goto v___jp_94_;
}
}
else
{
v___y_95_ = v___x_102_;
goto v___jp_94_;
}
}
else
{
goto v___jp_88_;
}
}
}
else
{
lean_dec(v___x_87_);
return v_pos_83_;
}
v___jp_88_:
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; uint8_t v___x_92_; 
v___x_89_ = lean_string_utf8_next_fast(v_str_84_, v___x_87_);
v___x_90_ = lean_nat_sub(v___x_89_, v___x_87_);
lean_dec(v___x_87_);
v___x_91_ = lean_nat_add(v_pos_83_, v___x_90_);
lean_dec(v___x_90_);
v___x_92_ = l_String_instDecidableLtRaw___aux__1(v_pos_83_, v___x_91_);
if (v___x_92_ == 0)
{
lean_dec(v___x_91_);
return v_pos_83_;
}
else
{
lean_dec(v_pos_83_);
v_pos_83_ = v___x_91_;
goto _start;
}
}
v___jp_94_:
{
if (v___y_95_ == 0)
{
lean_dec(v___x_87_);
return v_pos_83_;
}
else
{
goto v___jp_88_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix_spec__0___boxed(lean_object* v_s_111_, lean_object* v_pos_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix_spec__0(v_s_111_, v_pos_112_);
lean_dec_ref(v_s_111_);
return v_res_113_;
}
}
static lean_object* _init_l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___closed__3(void){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_117_ = ((lean_object*)(l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___closed__2));
v___x_118_ = lean_unsigned_to_nat(14u);
v___x_119_ = lean_unsigned_to_nat(22u);
v___x_120_ = ((lean_object*)(l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___closed__1));
v___x_121_ = ((lean_object*)(l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___closed__0));
v___x_122_ = l_mkPanicMessageWithDecl(v___x_121_, v___x_120_, v___x_119_, v___x_118_, v___x_117_);
return v___x_122_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix(lean_object* v_s_123_){
_start:
{
lean_object* v___y_125_; lean_object* v_startInclusive_126_; lean_object* v_endExclusive_127_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; uint8_t v___x_143_; 
v___x_138_ = lean_unsigned_to_nat(0u);
v___x_139_ = lean_string_utf8_byte_size(v_s_123_);
lean_inc_ref(v_s_123_);
v___x_140_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_140_, 0, v_s_123_);
lean_ctor_set(v___x_140_, 1, v___x_138_);
lean_ctor_set(v___x_140_, 2, v___x_139_);
v___x_141_ = lean_unsigned_to_nat(1u);
v___x_142_ = l_Substring_Raw_nextn(v___x_140_, v___x_141_, v___x_138_);
lean_dec_ref(v___x_140_);
v___x_143_ = lean_string_is_valid_pos(v_s_123_, v___x_142_);
if (v___x_143_ == 0)
{
lean_dec(v___x_142_);
lean_dec_ref(v_s_123_);
goto v___jp_133_;
}
else
{
uint8_t v___x_144_; 
v___x_144_ = lean_string_is_valid_pos(v_s_123_, v___x_139_);
if (v___x_144_ == 0)
{
lean_dec(v___x_142_);
lean_dec_ref(v_s_123_);
goto v___jp_133_;
}
else
{
uint8_t v___x_145_; 
v___x_145_ = lean_nat_dec_le(v___x_142_, v___x_139_);
if (v___x_145_ == 0)
{
lean_dec(v___x_142_);
lean_dec_ref(v_s_123_);
goto v___jp_133_;
}
else
{
lean_object* v___x_146_; 
lean_inc(v___x_142_);
v___x_146_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_146_, 0, v_s_123_);
lean_ctor_set(v___x_146_, 1, v___x_142_);
lean_ctor_set(v___x_146_, 2, v___x_139_);
v___y_125_ = v___x_146_;
v_startInclusive_126_ = v___x_142_;
v_endExclusive_127_ = v___x_139_;
goto v___jp_124_;
}
}
}
v___jp_124_:
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; uint8_t v___x_132_; 
v___x_128_ = lean_unsigned_to_nat(0u);
v___x_129_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix_spec__0(v___y_125_, v___x_128_);
lean_dec_ref(v___y_125_);
v___x_130_ = lean_nat_add(v_startInclusive_126_, v___x_129_);
lean_dec(v___x_129_);
lean_dec(v_startInclusive_126_);
v___x_131_ = lean_nat_sub(v_endExclusive_127_, v___x_130_);
lean_dec(v___x_130_);
lean_dec(v_endExclusive_127_);
v___x_132_ = lean_nat_dec_eq(v___x_131_, v___x_128_);
lean_dec(v___x_131_);
return v___x_132_;
}
v___jp_133_:
{
lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v_startInclusive_136_; lean_object* v_endExclusive_137_; 
v___x_134_ = lean_obj_once(&l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___closed__3, &l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___closed__3_once, _init_l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___closed__3);
v___x_135_ = l_panic___at___00__private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix_spec__1(v___x_134_);
v_startInclusive_136_ = lean_ctor_get(v___x_135_, 1);
lean_inc(v_startInclusive_136_);
v_endExclusive_137_ = lean_ctor_get(v___x_135_, 2);
lean_inc(v_endExclusive_137_);
v___y_125_ = v___x_135_;
v_startInclusive_126_ = v_startInclusive_136_;
v_endExclusive_127_ = v_endExclusive_137_;
goto v___jp_124_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___boxed(lean_object* v_s_147_){
_start:
{
uint8_t v_res_148_; lean_object* v_r_149_; 
v_res_148_ = l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix(v_s_147_);
v_r_149_ = lean_box(v_res_148_);
return v_r_149_;
}
}
static lean_object* _init_l_Lean_Elab_checkValidAutoBoundImplicitName___closed__2(void){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_154_ = ((lean_object*)(l_Lean_Elab_checkValidAutoBoundImplicitName___closed__1));
v___x_155_ = l_Lean_stringToMessageData(v___x_154_);
return v___x_155_;
}
}
static lean_object* _init_l_Lean_Elab_checkValidAutoBoundImplicitName___closed__4(void){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_157_ = ((lean_object*)(l_Lean_Elab_checkValidAutoBoundImplicitName___closed__3));
v___x_158_ = l_Lean_stringToMessageData(v___x_157_);
return v___x_158_;
}
}
static lean_object* _init_l_Lean_Elab_checkValidAutoBoundImplicitName___closed__9(void){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_165_ = ((lean_object*)(l_Lean_Elab_checkValidAutoBoundImplicitName___closed__8));
v___x_166_ = l_Lean_stringToMessageData(v___x_165_);
return v___x_166_;
}
}
static lean_object* _init_l_Lean_Elab_checkValidAutoBoundImplicitName___closed__11(void){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_168_ = ((lean_object*)(l_Lean_Elab_checkValidAutoBoundImplicitName___closed__10));
v___x_169_ = l_Lean_stringToMessageData(v___x_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkValidAutoBoundImplicitName(lean_object* v_n_170_, uint8_t v_allowed_171_, uint8_t v_relaxed_172_){
_start:
{
uint8_t v___y_176_; 
if (lean_obj_tag(v_n_170_) == 1)
{
lean_object* v_pre_201_; 
v_pre_201_ = lean_ctor_get(v_n_170_, 0);
if (lean_obj_tag(v_pre_201_) == 0)
{
lean_object* v_str_202_; lean_object* v___x_203_; lean_object* v___x_204_; uint8_t v___x_205_; 
v_str_202_ = lean_ctor_get(v_n_170_, 1);
v___x_203_ = lean_string_length(v_str_202_);
v___x_204_ = lean_unsigned_to_nat(0u);
v___x_205_ = lean_nat_dec_eq(v___x_203_, v___x_204_);
if (v___x_205_ == 0)
{
if (v_allowed_171_ == 0)
{
v___y_176_ = v_allowed_171_;
goto v___jp_175_;
}
else
{
if (v_relaxed_172_ == 0)
{
uint8_t v___x_206_; 
lean_inc_ref(v_str_202_);
v___x_206_ = l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix(v_str_202_);
if (v___x_206_ == 0)
{
v___y_176_ = v___x_206_;
goto v___jp_175_;
}
else
{
lean_object* v___x_207_; lean_object* v___x_208_; 
lean_dec_ref(v_n_170_);
v___x_207_ = lean_box(v_allowed_171_);
v___x_208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_208_, 0, v___x_207_);
return v___x_208_;
}
}
else
{
lean_object* v___x_209_; lean_object* v___x_210_; 
lean_dec_ref(v_n_170_);
v___x_209_ = lean_box(v_allowed_171_);
v___x_210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_210_, 0, v___x_209_);
return v___x_210_;
}
}
}
else
{
lean_object* v___x_211_; 
lean_dec_ref(v_n_170_);
v___x_211_ = ((lean_object*)(l_Lean_Elab_checkValidAutoBoundImplicitName___closed__0));
return v___x_211_;
}
}
else
{
lean_dec_ref(v_n_170_);
goto v___jp_173_;
}
}
else
{
lean_dec(v_n_170_);
goto v___jp_173_;
}
v___jp_173_:
{
lean_object* v___x_174_; 
v___x_174_ = ((lean_object*)(l_Lean_Elab_checkValidAutoBoundImplicitName___closed__0));
return v___x_174_;
}
v___jp_175_:
{
if (v_allowed_171_ == 0)
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_177_ = lean_obj_once(&l_Lean_Elab_checkValidAutoBoundImplicitName___closed__2, &l_Lean_Elab_checkValidAutoBoundImplicitName___closed__2_once, _init_l_Lean_Elab_checkValidAutoBoundImplicitName___closed__2);
v___x_178_ = l_Lean_MessageData_ofConstName(v_n_170_, v___y_176_);
v___x_179_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_179_, 0, v___x_177_);
lean_ctor_set(v___x_179_, 1, v___x_178_);
v___x_180_ = lean_obj_once(&l_Lean_Elab_checkValidAutoBoundImplicitName___closed__4, &l_Lean_Elab_checkValidAutoBoundImplicitName___closed__4_once, _init_l_Lean_Elab_checkValidAutoBoundImplicitName___closed__4);
v___x_181_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_181_, 0, v___x_179_);
lean_ctor_set(v___x_181_, 1, v___x_180_);
v___x_182_ = ((lean_object*)(l_Lean_Elab_checkValidAutoBoundImplicitName___closed__7));
v___x_183_ = l_Lean_MessageData_ofConstName(v___x_182_, v___y_176_);
v___x_184_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_184_, 0, v___x_181_);
lean_ctor_set(v___x_184_, 1, v___x_183_);
v___x_185_ = lean_obj_once(&l_Lean_Elab_checkValidAutoBoundImplicitName___closed__9, &l_Lean_Elab_checkValidAutoBoundImplicitName___closed__9_once, _init_l_Lean_Elab_checkValidAutoBoundImplicitName___closed__9);
v___x_186_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_186_, 0, v___x_184_);
lean_ctor_set(v___x_186_, 1, v___x_185_);
v___x_187_ = l_Lean_MessageData_note(v___x_186_);
v___x_188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_188_, 0, v___x_187_);
return v___x_188_;
}
else
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_189_ = lean_obj_once(&l_Lean_Elab_checkValidAutoBoundImplicitName___closed__2, &l_Lean_Elab_checkValidAutoBoundImplicitName___closed__2_once, _init_l_Lean_Elab_checkValidAutoBoundImplicitName___closed__2);
v___x_190_ = l_Lean_MessageData_ofConstName(v_n_170_, v___y_176_);
v___x_191_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_191_, 0, v___x_189_);
lean_ctor_set(v___x_191_, 1, v___x_190_);
v___x_192_ = lean_obj_once(&l_Lean_Elab_checkValidAutoBoundImplicitName___closed__11, &l_Lean_Elab_checkValidAutoBoundImplicitName___closed__11_once, _init_l_Lean_Elab_checkValidAutoBoundImplicitName___closed__11);
v___x_193_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_193_, 0, v___x_191_);
lean_ctor_set(v___x_193_, 1, v___x_192_);
v___x_194_ = ((lean_object*)(l_Lean_Elab_checkValidAutoBoundImplicitName___closed__7));
v___x_195_ = l_Lean_MessageData_ofConstName(v___x_194_, v___y_176_);
v___x_196_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_196_, 0, v___x_193_);
lean_ctor_set(v___x_196_, 1, v___x_195_);
v___x_197_ = lean_obj_once(&l_Lean_Elab_checkValidAutoBoundImplicitName___closed__9, &l_Lean_Elab_checkValidAutoBoundImplicitName___closed__9_once, _init_l_Lean_Elab_checkValidAutoBoundImplicitName___closed__9);
v___x_198_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_198_, 0, v___x_196_);
lean_ctor_set(v___x_198_, 1, v___x_197_);
v___x_199_ = l_Lean_MessageData_note(v___x_198_);
v___x_200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_200_, 0, v___x_199_);
return v___x_200_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkValidAutoBoundImplicitName___boxed(lean_object* v_n_212_, lean_object* v_allowed_213_, lean_object* v_relaxed_214_){
_start:
{
uint8_t v_allowed_boxed_215_; uint8_t v_relaxed_boxed_216_; lean_object* v_res_217_; 
v_allowed_boxed_215_ = lean_unbox(v_allowed_213_);
v_relaxed_boxed_216_ = lean_unbox(v_relaxed_214_);
v_res_217_ = l_Lean_Elab_checkValidAutoBoundImplicitName(v_n_212_, v_allowed_boxed_215_, v_relaxed_boxed_216_);
return v_res_217_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_isValidAutoBoundLevelName(lean_object* v_n_218_, uint8_t v_relaxed_219_){
_start:
{
if (lean_obj_tag(v_n_218_) == 1)
{
lean_object* v_pre_220_; lean_object* v_str_221_; uint8_t v___y_223_; uint32_t v___y_226_; 
v_pre_220_ = lean_ctor_get(v_n_218_, 0);
lean_inc(v_pre_220_);
v_str_221_ = lean_ctor_get(v_n_218_, 1);
lean_inc_ref(v_str_221_);
lean_dec_ref(v_n_218_);
if (lean_obj_tag(v_pre_220_) == 0)
{
lean_object* v___x_231_; lean_object* v___x_232_; uint8_t v___x_233_; 
v___x_231_ = lean_unsigned_to_nat(0u);
v___x_232_ = lean_string_length(v_str_221_);
v___x_233_ = lean_nat_dec_lt(v___x_231_, v___x_232_);
if (v___x_233_ == 0)
{
lean_dec_ref(v_str_221_);
return v___x_233_;
}
else
{
if (v_relaxed_219_ == 0)
{
lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_234_ = lean_string_utf8_byte_size(v_str_221_);
lean_inc_ref(v_str_221_);
v___x_235_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_235_, 0, v_str_221_);
lean_ctor_set(v___x_235_, 1, v___x_231_);
lean_ctor_set(v___x_235_, 2, v___x_234_);
v___x_236_ = l_String_Slice_Pos_get_x3f(v___x_235_, v___x_231_);
lean_dec_ref(v___x_235_);
if (lean_obj_tag(v___x_236_) == 0)
{
uint32_t v___x_237_; 
v___x_237_ = 65;
v___y_226_ = v___x_237_;
goto v___jp_225_;
}
else
{
lean_object* v_val_238_; uint32_t v___x_239_; 
v_val_238_ = lean_ctor_get(v___x_236_, 0);
lean_inc(v_val_238_);
lean_dec_ref(v___x_236_);
v___x_239_ = lean_unbox_uint32(v_val_238_);
lean_dec(v_val_238_);
v___y_226_ = v___x_239_;
goto v___jp_225_;
}
}
else
{
lean_dec_ref(v_str_221_);
return v_relaxed_219_;
}
}
}
else
{
uint8_t v___x_240_; 
lean_dec_ref(v_str_221_);
lean_dec(v_pre_220_);
v___x_240_ = 0;
return v___x_240_;
}
v___jp_222_:
{
if (v___y_223_ == 0)
{
lean_dec_ref(v_str_221_);
return v___y_223_;
}
else
{
uint8_t v___x_224_; 
v___x_224_ = l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix(v_str_221_);
return v___x_224_;
}
}
v___jp_225_:
{
uint32_t v___x_227_; uint8_t v___x_228_; 
v___x_227_ = 97;
v___x_228_ = lean_uint32_dec_le(v___x_227_, v___y_226_);
if (v___x_228_ == 0)
{
v___y_223_ = v___x_228_;
goto v___jp_222_;
}
else
{
uint32_t v___x_229_; uint8_t v___x_230_; 
v___x_229_ = 122;
v___x_230_ = lean_uint32_dec_le(v___y_226_, v___x_229_);
v___y_223_ = v___x_230_;
goto v___jp_222_;
}
}
}
else
{
uint8_t v___x_241_; 
lean_dec(v_n_218_);
v___x_241_ = 0;
return v___x_241_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_isValidAutoBoundLevelName___boxed(lean_object* v_n_242_, lean_object* v_relaxed_243_){
_start:
{
uint8_t v_relaxed_boxed_244_; uint8_t v_res_245_; lean_object* v_r_246_; 
v_relaxed_boxed_244_ = lean_unbox(v_relaxed_243_);
v_res_245_ = l_Lean_Elab_isValidAutoBoundLevelName(v_n_242_, v_relaxed_boxed_244_);
v_r_246_ = lean_box(v_res_245_);
return v_r_246_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default___closed__0(void){
_start:
{
lean_object* v___x_247_; 
v___x_247_ = l_Lean_instInhabitedPersistentArray_default(lean_box(0));
return v___x_247_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default___closed__1(void){
_start:
{
lean_object* v___x_248_; uint8_t v___x_249_; lean_object* v___x_250_; 
v___x_248_ = lean_obj_once(&l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default___closed__0, &l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default___closed__0_once, _init_l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default___closed__0);
v___x_249_ = 0;
v___x_250_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_250_, 0, v___x_248_);
lean_ctor_set_uint8(v___x_250_, sizeof(void*)*1, v___x_249_);
return v___x_250_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default(void){
_start:
{
lean_object* v___x_251_; 
v___x_251_ = lean_obj_once(&l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default___closed__1, &l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default___closed__1_once, _init_l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default___closed__1);
return v___x_251_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedAutoBoundImplicitContext(void){
_start:
{
lean_object* v___x_252_; 
v___x_252_ = l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default;
return v___x_252_;
}
}
static lean_object* _init_l_Lean_Elab_instEmptyCollectionAutoBoundImplicitContext___closed__0(void){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_253_ = lean_unsigned_to_nat(32u);
v___x_254_ = lean_mk_empty_array_with_capacity(v___x_253_);
v___x_255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
return v___x_255_;
}
}
static lean_object* _init_l_Lean_Elab_instEmptyCollectionAutoBoundImplicitContext___closed__1(void){
_start:
{
size_t v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_256_ = ((size_t)5ULL);
v___x_257_ = lean_unsigned_to_nat(0u);
v___x_258_ = lean_unsigned_to_nat(32u);
v___x_259_ = lean_mk_empty_array_with_capacity(v___x_258_);
v___x_260_ = lean_obj_once(&l_Lean_Elab_instEmptyCollectionAutoBoundImplicitContext___closed__0, &l_Lean_Elab_instEmptyCollectionAutoBoundImplicitContext___closed__0_once, _init_l_Lean_Elab_instEmptyCollectionAutoBoundImplicitContext___closed__0);
v___x_261_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_261_, 0, v___x_260_);
lean_ctor_set(v___x_261_, 1, v___x_259_);
lean_ctor_set(v___x_261_, 2, v___x_257_);
lean_ctor_set(v___x_261_, 3, v___x_257_);
lean_ctor_set_usize(v___x_261_, 4, v___x_256_);
return v___x_261_;
}
}
static lean_object* _init_l_Lean_Elab_instEmptyCollectionAutoBoundImplicitContext___closed__2(void){
_start:
{
lean_object* v___x_262_; uint8_t v___x_263_; lean_object* v___x_264_; 
v___x_262_ = lean_obj_once(&l_Lean_Elab_instEmptyCollectionAutoBoundImplicitContext___closed__1, &l_Lean_Elab_instEmptyCollectionAutoBoundImplicitContext___closed__1_once, _init_l_Lean_Elab_instEmptyCollectionAutoBoundImplicitContext___closed__1);
v___x_263_ = 0;
v___x_264_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_264_, 0, v___x_262_);
lean_ctor_set_uint8(v___x_264_, sizeof(void*)*1, v___x_263_);
return v___x_264_;
}
}
static lean_object* _init_l_Lean_Elab_instEmptyCollectionAutoBoundImplicitContext(void){
_start:
{
lean_object* v___x_265_; 
v___x_265_ = lean_obj_once(&l_Lean_Elab_instEmptyCollectionAutoBoundImplicitContext___closed__2, &l_Lean_Elab_instEmptyCollectionAutoBoundImplicitContext___closed__2_once, _init_l_Lean_Elab_instEmptyCollectionAutoBoundImplicitContext___closed__2);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_AutoBoundImplicitContext_push(lean_object* v_ctx_266_, lean_object* v_x_267_){
_start:
{
uint8_t v_autoImplicitEnabled_268_; lean_object* v_boundVariables_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_277_; 
v_autoImplicitEnabled_268_ = lean_ctor_get_uint8(v_ctx_266_, sizeof(void*)*1);
v_boundVariables_269_ = lean_ctor_get(v_ctx_266_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v_ctx_266_);
if (v_isSharedCheck_277_ == 0)
{
v___x_271_ = v_ctx_266_;
v_isShared_272_ = v_isSharedCheck_277_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_boundVariables_269_);
lean_dec(v_ctx_266_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_277_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_273_; lean_object* v___x_275_; 
v___x_273_ = l_Lean_PersistentArray_push___redArg(v_boundVariables_269_, v_x_267_);
if (v_isShared_272_ == 0)
{
lean_ctor_set(v___x_271_, 0, v___x_273_);
v___x_275_ = v___x_271_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v___x_273_);
lean_ctor_set_uint8(v_reuseFailAlloc_276_, sizeof(void*)*1, v_autoImplicitEnabled_268_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
}
lean_object* runtime_initialize_Lean_Meta_Hint(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_AutoBound(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Hint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_initFn_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_autoImplicit = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_autoImplicit);
lean_dec_ref(res);
res = l_Lean_Elab_initFn_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_relaxedAutoImplicit = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_relaxedAutoImplicit);
lean_dec_ref(res);
l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default = _init_l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default();
lean_mark_persistent(l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default);
l_Lean_Elab_instInhabitedAutoBoundImplicitContext = _init_l_Lean_Elab_instInhabitedAutoBoundImplicitContext();
lean_mark_persistent(l_Lean_Elab_instInhabitedAutoBoundImplicitContext);
l_Lean_Elab_instEmptyCollectionAutoBoundImplicitContext = _init_l_Lean_Elab_instEmptyCollectionAutoBoundImplicitContext();
lean_mark_persistent(l_Lean_Elab_instEmptyCollectionAutoBoundImplicitContext);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_AutoBound(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Hint(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_AutoBound(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Hint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_AutoBound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_AutoBound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_AutoBound(builtin);
}
#ifdef __cplusplus
}
#endif

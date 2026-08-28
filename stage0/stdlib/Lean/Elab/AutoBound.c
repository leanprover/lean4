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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_String_instInhabitedSlice;
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t l_Lean_isSubScriptAlnum(uint32_t);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Substring_Raw_nextn(lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_is_valid_pos(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_AutoBound_0__Lean_Elab_initFn_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_AutoBound_0__Lean_Elab_initFn_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "autoImplicit"};
static const lean_object* l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(116, 133, 197, 206, 105, 86, 94, 221)}};
static const lean_object* l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 323, .m_capacity = 323, .m_length = 319, .m_data = "Unbound local variables in declaration headers become implicit arguments. In \"relaxed\" mode (default), any atomic identifier is eligible, otherwise only single character followed by numeric digits are eligible. For example, `def f (x : Vector α n) : Vector α n :=` automatically introduces the implicit variables {α n}."};
static const lean_object* l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(7, 67, 153, 210, 133, 79, 100, 198)}};
static const lean_object* l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_autoImplicit;
static const lean_string_object l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "relaxedAutoImplicit"};
static const lean_object* l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(143, 7, 64, 249, 212, 66, 225, 166)}};
static const lean_object* l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 135, .m_capacity = 135, .m_length = 134, .m_data = "When \"relaxed\" mode is enabled, any atomic nonempty identifier is eligible for auto bound implicit locals (see option `autoImplicit`)."};
static const lean_object* l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(76, 142, 225, 45, 175, 203, 153, 200)}};
static const lean_object* l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4____boxed(lean_object*);
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
static lean_once_cell_t l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default;
LEAN_EXPORT lean_object* l_Lean_Elab_instInhabitedAutoBoundImplicitContext;
LEAN_EXPORT lean_object* l_Lean_Elab_instEmptyCollectionAutoBoundImplicitContext;
LEAN_EXPORT lean_object* l_Lean_Elab_AutoBoundImplicitContext_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_AutoBound_0__Lean_Elab_initFn_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v_deprecation_x3f_7_; lean_object* v___x_8_; uint8_t v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_deprecation_x3f_7_ = lean_ctor_get(v_decl_2_, 2);
v___x_8_ = lean_alloc_ctor(1, 0, 1);
v___x_9_ = lean_unbox(v_defValue_5_);
lean_ctor_set_uint8(v___x_8_, 0, v___x_9_);
lean_inc(v_deprecation_x3f_7_);
lean_inc_ref(v_descr_6_);
lean_inc_n(v_name_1_, 2);
v___x_10_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_10_, 0, v_name_1_);
lean_ctor_set(v___x_10_, 1, v_ref_3_);
lean_ctor_set(v___x_10_, 2, v___x_8_);
lean_ctor_set(v___x_10_, 3, v_descr_6_);
lean_ctor_set(v___x_10_, 4, v_deprecation_x3f_7_);
v___x_11_ = lean_register_option(v_name_1_, v___x_10_);
if (lean_obj_tag(v___x_11_) == 0)
{
lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_19_; 
v_isSharedCheck_19_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_19_ == 0)
{
lean_object* v_unused_20_; 
v_unused_20_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_20_);
v___x_13_ = v___x_11_;
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
else
{
lean_dec(v___x_11_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_15_; lean_object* v___x_17_; 
lean_inc(v_defValue_5_);
v___x_15_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_15_, 0, v_name_1_);
lean_ctor_set(v___x_15_, 1, v_defValue_5_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 0, v___x_15_);
v___x_17_ = v___x_13_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v___x_15_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
}
else
{
lean_object* v_a_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_28_; 
lean_dec(v_name_1_);
v_a_21_ = lean_ctor_get(v___x_11_, 0);
v_isSharedCheck_28_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_28_ == 0)
{
v___x_23_ = v___x_11_;
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_a_21_);
lean_dec(v___x_11_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v___x_26_; 
if (v_isShared_24_ == 0)
{
v___x_26_ = v___x_23_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_a_21_);
v___x_26_ = v_reuseFailAlloc_27_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
return v___x_26_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_AutoBound_0__Lean_Elab_initFn_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Elab_AutoBound_0__Lean_Elab_initFn_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_50_ = ((lean_object*)(l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4_));
v___x_51_ = ((lean_object*)(l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4_));
v___x_52_ = ((lean_object*)(l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4_));
v___x_53_ = l_Lean_Option_register___at___00__private_Lean_Elab_AutoBound_0__Lean_Elab_initFn_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__spec__0(v___x_50_, v___x_51_, v___x_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4____boxed(lean_object* v_a_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4_();
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_70_ = ((lean_object*)(l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4_));
v___x_71_ = ((lean_object*)(l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4_));
v___x_72_ = ((lean_object*)(l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4_));
v___x_73_ = l_Lean_Option_register___at___00__private_Lean_Elab_AutoBound_0__Lean_Elab_initFn_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__spec__0(v___x_70_, v___x_71_, v___x_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4____boxed(lean_object* v_a_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4_();
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix_spec__1(lean_object* v_msg_76_){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_77_ = l_String_instInhabitedSlice;
v___x_78_ = lean_panic_fn_borrowed(v___x_77_, v_msg_76_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix_spec__0(lean_object* v_s_79_, lean_object* v_pos_80_){
_start:
{
lean_object* v_str_81_; lean_object* v_startInclusive_82_; lean_object* v_endExclusive_83_; lean_object* v___x_84_; uint8_t v___y_94_; lean_object* v___x_95_; lean_object* v___x_96_; uint8_t v_decide_97_; 
v_str_81_ = lean_ctor_get(v_s_79_, 0);
v_startInclusive_82_ = lean_ctor_get(v_s_79_, 1);
v_endExclusive_83_ = lean_ctor_get(v_s_79_, 2);
v___x_84_ = lean_nat_add(v_startInclusive_82_, v_pos_80_);
v___x_95_ = lean_unsigned_to_nat(0u);
v___x_96_ = lean_nat_sub(v_endExclusive_83_, v___x_84_);
v_decide_97_ = lean_nat_dec_eq(v___x_95_, v___x_96_);
lean_dec(v___x_96_);
if (v_decide_97_ == 0)
{
uint32_t v___x_98_; uint32_t v___x_105_; uint8_t v___x_106_; 
v___x_98_ = lean_string_utf8_get_fast(v_str_81_, v___x_84_);
v___x_105_ = 48;
v___x_106_ = lean_uint32_dec_le(v___x_105_, v___x_98_);
if (v___x_106_ == 0)
{
goto v___jp_99_;
}
else
{
uint32_t v___x_107_; uint8_t v___x_108_; 
v___x_107_ = 57;
v___x_108_ = lean_uint32_dec_le(v___x_98_, v___x_107_);
if (v___x_108_ == 0)
{
goto v___jp_99_;
}
else
{
goto v___jp_85_;
}
}
v___jp_99_:
{
uint8_t v___x_100_; 
v___x_100_ = l_Lean_isSubScriptAlnum(v___x_98_);
if (v___x_100_ == 0)
{
uint32_t v___x_101_; uint8_t v___x_102_; 
v___x_101_ = 95;
v___x_102_ = lean_uint32_dec_eq(v___x_98_, v___x_101_);
if (v___x_102_ == 0)
{
uint32_t v___x_103_; uint8_t v___x_104_; 
v___x_103_ = 39;
v___x_104_ = lean_uint32_dec_eq(v___x_98_, v___x_103_);
v___y_94_ = v___x_104_;
goto v___jp_93_;
}
else
{
goto v___jp_85_;
}
}
else
{
v___y_94_ = v___x_100_;
goto v___jp_93_;
}
}
}
else
{
lean_dec(v___x_84_);
return v_pos_80_;
}
v___jp_85_:
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; uint8_t v___x_91_; 
v___x_86_ = lean_string_utf8_next_fast(v_str_81_, v___x_84_);
v___x_87_ = lean_nat_sub(v___x_86_, v___x_84_);
lean_dec(v___x_84_);
v___x_88_ = lean_nat_add(v_pos_80_, v___x_87_);
lean_dec(v___x_87_);
v___x_89_ = lean_unsigned_to_nat(1u);
v___x_90_ = lean_nat_add(v_pos_80_, v___x_89_);
v___x_91_ = lean_nat_dec_le(v___x_90_, v___x_88_);
lean_dec(v___x_90_);
if (v___x_91_ == 0)
{
lean_dec(v___x_88_);
return v_pos_80_;
}
else
{
lean_dec(v_pos_80_);
v_pos_80_ = v___x_88_;
goto _start;
}
}
v___jp_93_:
{
if (v___y_94_ == 0)
{
lean_dec(v___x_84_);
return v_pos_80_;
}
else
{
goto v___jp_85_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix_spec__0___boxed(lean_object* v_s_109_, lean_object* v_pos_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix_spec__0(v_s_109_, v_pos_110_);
lean_dec_ref(v_s_109_);
return v_res_111_;
}
}
static lean_object* _init_l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___closed__3(void){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_115_ = ((lean_object*)(l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___closed__2));
v___x_116_ = lean_unsigned_to_nat(14u);
v___x_117_ = lean_unsigned_to_nat(22u);
v___x_118_ = ((lean_object*)(l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___closed__1));
v___x_119_ = ((lean_object*)(l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___closed__0));
v___x_120_ = l_mkPanicMessageWithDecl(v___x_119_, v___x_118_, v___x_117_, v___x_116_, v___x_115_);
return v___x_120_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix(lean_object* v_s_121_){
_start:
{
lean_object* v___y_123_; lean_object* v_startInclusive_124_; lean_object* v_endExclusive_125_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; uint8_t v___y_136_; uint8_t v___x_142_; uint8_t v___y_144_; uint8_t v___x_145_; 
v___x_130_ = lean_unsigned_to_nat(0u);
v___x_131_ = lean_string_utf8_byte_size(v_s_121_);
lean_inc_ref(v_s_121_);
v___x_132_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_132_, 0, v_s_121_);
lean_ctor_set(v___x_132_, 1, v___x_130_);
lean_ctor_set(v___x_132_, 2, v___x_131_);
v___x_133_ = lean_unsigned_to_nat(1u);
v___x_134_ = l_Substring_Raw_nextn(v___x_132_, v___x_133_, v___x_130_);
lean_dec_ref_known(v___x_132_, 3);
v___x_142_ = lean_string_is_valid_pos(v_s_121_, v___x_134_);
v___x_145_ = lean_string_is_valid_pos(v_s_121_, v___x_131_);
if (v___x_145_ == 0)
{
v___y_144_ = v___x_145_;
goto v___jp_143_;
}
else
{
uint8_t v___x_146_; 
v___x_146_ = lean_nat_dec_le(v___x_134_, v___x_131_);
v___y_144_ = v___x_146_;
goto v___jp_143_;
}
v___jp_122_:
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; uint8_t v_decide_129_; 
v___x_126_ = lean_unsigned_to_nat(0u);
v___x_127_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix_spec__0(v___y_123_, v___x_126_);
lean_dec_ref(v___y_123_);
v___x_128_ = lean_nat_sub(v_endExclusive_125_, v_startInclusive_124_);
lean_dec(v_startInclusive_124_);
lean_dec(v_endExclusive_125_);
v_decide_129_ = lean_nat_dec_eq(v___x_127_, v___x_128_);
lean_dec(v___x_128_);
lean_dec(v___x_127_);
return v_decide_129_;
}
v___jp_135_:
{
if (v___y_136_ == 0)
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v_startInclusive_139_; lean_object* v_endExclusive_140_; 
lean_dec(v___x_134_);
lean_dec_ref(v_s_121_);
v___x_137_ = lean_obj_once(&l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___closed__3, &l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___closed__3_once, _init_l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___closed__3);
v___x_138_ = l_panic___at___00__private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix_spec__1(v___x_137_);
v_startInclusive_139_ = lean_ctor_get(v___x_138_, 1);
lean_inc(v_startInclusive_139_);
v_endExclusive_140_ = lean_ctor_get(v___x_138_, 2);
lean_inc(v_endExclusive_140_);
v___y_123_ = v___x_138_;
v_startInclusive_124_ = v_startInclusive_139_;
v_endExclusive_125_ = v_endExclusive_140_;
goto v___jp_122_;
}
else
{
lean_object* v___x_141_; 
lean_inc(v___x_134_);
v___x_141_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_141_, 0, v_s_121_);
lean_ctor_set(v___x_141_, 1, v___x_134_);
lean_ctor_set(v___x_141_, 2, v___x_131_);
v___y_123_ = v___x_141_;
v_startInclusive_124_ = v___x_134_;
v_endExclusive_125_ = v___x_131_;
goto v___jp_122_;
}
}
v___jp_143_:
{
if (v___x_142_ == 0)
{
v___y_136_ = v___x_142_;
goto v___jp_135_;
}
else
{
v___y_136_ = v___y_144_;
goto v___jp_135_;
}
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
v___x_203_ = lean_string_utf8_byte_size(v_str_202_);
v___x_204_ = lean_unsigned_to_nat(0u);
v___x_205_ = lean_nat_dec_eq(v___x_203_, v___x_204_);
if (v___x_205_ == 0)
{
if (v_allowed_171_ == 0)
{
v___y_176_ = v___x_205_;
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
lean_dec_ref_known(v_n_170_, 2);
v___x_207_ = lean_box(v_allowed_171_);
v___x_208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_208_, 0, v___x_207_);
return v___x_208_;
}
}
else
{
lean_object* v___x_209_; lean_object* v___x_210_; 
lean_dec_ref_known(v_n_170_, 2);
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
lean_dec_ref_known(v_n_170_, 2);
v___x_211_ = ((lean_object*)(l_Lean_Elab_checkValidAutoBoundImplicitName___closed__0));
return v___x_211_;
}
}
else
{
lean_dec_ref_known(v_n_170_, 2);
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
lean_object* v_pre_220_; lean_object* v_str_221_; uint32_t v___y_223_; 
v_pre_220_ = lean_ctor_get(v_n_218_, 0);
lean_inc(v_pre_220_);
v_str_221_ = lean_ctor_get(v_n_218_, 1);
lean_inc_ref(v_str_221_);
lean_dec_ref_known(v_n_218_, 2);
if (lean_obj_tag(v_pre_220_) == 0)
{
lean_object* v___x_229_; lean_object* v___x_230_; uint8_t v___x_231_; 
v___x_229_ = lean_string_utf8_byte_size(v_str_221_);
v___x_230_ = lean_unsigned_to_nat(0u);
v___x_231_ = lean_nat_dec_eq(v___x_229_, v___x_230_);
if (v___x_231_ == 0)
{
if (v_relaxed_219_ == 0)
{
lean_object* v___x_232_; lean_object* v___x_233_; 
lean_inc_ref(v_str_221_);
v___x_232_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_232_, 0, v_str_221_);
lean_ctor_set(v___x_232_, 1, v___x_230_);
lean_ctor_set(v___x_232_, 2, v___x_229_);
v___x_233_ = l_String_Slice_Pos_get_x3f(v___x_232_, v___x_230_);
lean_dec_ref_known(v___x_232_, 3);
if (lean_obj_tag(v___x_233_) == 0)
{
uint32_t v___x_234_; 
v___x_234_ = 65;
v___y_223_ = v___x_234_;
goto v___jp_222_;
}
else
{
lean_object* v_val_235_; uint32_t v___x_236_; 
v_val_235_ = lean_ctor_get(v___x_233_, 0);
lean_inc(v_val_235_);
lean_dec_ref_known(v___x_233_, 1);
v___x_236_ = lean_unbox_uint32(v_val_235_);
lean_dec(v_val_235_);
v___y_223_ = v___x_236_;
goto v___jp_222_;
}
}
else
{
lean_dec_ref(v_str_221_);
return v_relaxed_219_;
}
}
else
{
uint8_t v___x_237_; 
lean_dec_ref(v_str_221_);
v___x_237_ = 0;
return v___x_237_;
}
}
else
{
uint8_t v___x_238_; 
lean_dec_ref(v_str_221_);
lean_dec(v_pre_220_);
v___x_238_ = 0;
return v___x_238_;
}
v___jp_222_:
{
uint32_t v___x_224_; uint8_t v___x_225_; 
v___x_224_ = 97;
v___x_225_ = lean_uint32_dec_le(v___x_224_, v___y_223_);
if (v___x_225_ == 0)
{
lean_dec_ref(v_str_221_);
return v___x_225_;
}
else
{
uint32_t v___x_226_; uint8_t v___x_227_; 
v___x_226_ = 122;
v___x_227_ = lean_uint32_dec_le(v___y_223_, v___x_226_);
if (v___x_227_ == 0)
{
lean_dec_ref(v_str_221_);
return v___x_227_;
}
else
{
uint8_t v___x_228_; 
v___x_228_ = l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix(v_str_221_);
return v___x_228_;
}
}
}
}
else
{
uint8_t v___x_239_; 
lean_dec(v_n_218_);
v___x_239_ = 0;
return v___x_239_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_isValidAutoBoundLevelName___boxed(lean_object* v_n_240_, lean_object* v_relaxed_241_){
_start:
{
uint8_t v_relaxed_boxed_242_; uint8_t v_res_243_; lean_object* v_r_244_; 
v_relaxed_boxed_242_ = lean_unbox(v_relaxed_241_);
v_res_243_ = l_Lean_Elab_isValidAutoBoundLevelName(v_n_240_, v_relaxed_boxed_242_);
v_r_244_ = lean_box(v_res_243_);
return v_r_244_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default___closed__0(void){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_245_ = lean_unsigned_to_nat(32u);
v___x_246_ = lean_mk_empty_array_with_capacity(v___x_245_);
v___x_247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_247_, 0, v___x_246_);
return v___x_247_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default___closed__1(void){
_start:
{
size_t v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_248_ = ((size_t)5ULL);
v___x_249_ = lean_unsigned_to_nat(0u);
v___x_250_ = lean_unsigned_to_nat(32u);
v___x_251_ = lean_mk_empty_array_with_capacity(v___x_250_);
v___x_252_ = lean_obj_once(&l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default___closed__0, &l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default___closed__0_once, _init_l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default___closed__0);
v___x_253_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_253_, 0, v___x_252_);
lean_ctor_set(v___x_253_, 1, v___x_251_);
lean_ctor_set(v___x_253_, 2, v___x_249_);
lean_ctor_set(v___x_253_, 3, v___x_249_);
lean_ctor_set_usize(v___x_253_, 4, v___x_248_);
return v___x_253_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default___closed__2(void){
_start:
{
lean_object* v___x_254_; uint8_t v___x_255_; lean_object* v___x_256_; 
v___x_254_ = lean_obj_once(&l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default___closed__1, &l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default___closed__1_once, _init_l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default___closed__1);
v___x_255_ = 0;
v___x_256_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_256_, 0, v___x_254_);
lean_ctor_set_uint8(v___x_256_, sizeof(void*)*1, v___x_255_);
return v___x_256_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default(void){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = lean_obj_once(&l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default___closed__2, &l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default___closed__2_once, _init_l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default___closed__2);
return v___x_257_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedAutoBoundImplicitContext(void){
_start:
{
lean_object* v___x_258_; 
v___x_258_ = l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default;
return v___x_258_;
}
}
static lean_object* _init_l_Lean_Elab_instEmptyCollectionAutoBoundImplicitContext(void){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_259_ = lean_unsigned_to_nat(32u);
v___x_260_ = lean_mk_empty_array_with_capacity(v___x_259_);
lean_dec_ref(v___x_260_);
v___x_261_ = lean_obj_once(&l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default___closed__2, &l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default___closed__2_once, _init_l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default___closed__2);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_AutoBoundImplicitContext_push(lean_object* v_ctx_262_, lean_object* v_x_263_){
_start:
{
uint8_t v_autoImplicitEnabled_264_; lean_object* v_boundVariables_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_273_; 
v_autoImplicitEnabled_264_ = lean_ctor_get_uint8(v_ctx_262_, sizeof(void*)*1);
v_boundVariables_265_ = lean_ctor_get(v_ctx_262_, 0);
v_isSharedCheck_273_ = !lean_is_exclusive(v_ctx_262_);
if (v_isSharedCheck_273_ == 0)
{
v___x_267_ = v_ctx_262_;
v_isShared_268_ = v_isSharedCheck_273_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_boundVariables_265_);
lean_dec(v_ctx_262_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_273_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_269_; lean_object* v___x_271_; 
v___x_269_ = l_Lean_PersistentArray_push___redArg(v_boundVariables_265_, v_x_263_);
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 0, v___x_269_);
v___x_271_ = v___x_267_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v___x_269_);
lean_ctor_set_uint8(v_reuseFailAlloc_272_, sizeof(void*)*1, v_autoImplicitEnabled_264_);
v___x_271_ = v_reuseFailAlloc_272_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
return v___x_271_;
}
}
}
}
lean_object* runtime_initialize_Lean_Meta_Hint(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_AutoBound(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Hint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_autoImplicit = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_autoImplicit);
lean_dec_ref(res);
res = l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4_();
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

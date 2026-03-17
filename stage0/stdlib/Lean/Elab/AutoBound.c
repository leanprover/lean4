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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t l_Lean_isSubScriptAlnum(uint32_t);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Substring_Raw_nextn(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_is_valid_pos(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00__private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00__private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix_spec__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00__private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix_spec__0(lean_object* v_s_82_, lean_object* v_curr_83_){
_start:
{
lean_object* v_str_84_; lean_object* v_startInclusive_85_; lean_object* v_endExclusive_86_; lean_object* v___x_87_; lean_object* v___x_88_; uint8_t v___y_96_; lean_object* v___x_97_; lean_object* v___x_98_; uint8_t v___x_99_; 
v_str_84_ = lean_ctor_get(v_s_82_, 0);
v_startInclusive_85_ = lean_ctor_get(v_s_82_, 1);
v_endExclusive_86_ = lean_ctor_get(v_s_82_, 2);
v___x_87_ = lean_nat_add(v_startInclusive_85_, v_curr_83_);
lean_inc(v_endExclusive_86_);
lean_inc(v___x_87_);
lean_inc_ref(v_str_84_);
v___x_88_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_88_, 0, v_str_84_);
lean_ctor_set(v___x_88_, 1, v___x_87_);
lean_ctor_set(v___x_88_, 2, v_endExclusive_86_);
v___x_97_ = lean_unsigned_to_nat(0u);
v___x_98_ = lean_nat_sub(v_endExclusive_86_, v___x_87_);
v___x_99_ = lean_nat_dec_eq(v___x_97_, v___x_98_);
lean_dec(v___x_98_);
if (v___x_99_ == 0)
{
uint32_t v___x_100_; uint8_t v___y_102_; uint32_t v___x_108_; uint8_t v___x_109_; 
v___x_100_ = lean_string_utf8_get_fast(v_str_84_, v___x_87_);
v___x_108_ = 48;
v___x_109_ = lean_uint32_dec_le(v___x_108_, v___x_100_);
if (v___x_109_ == 0)
{
v___y_102_ = v___x_109_;
goto v___jp_101_;
}
else
{
uint32_t v___x_110_; uint8_t v___x_111_; 
v___x_110_ = 57;
v___x_111_ = lean_uint32_dec_le(v___x_100_, v___x_110_);
v___y_102_ = v___x_111_;
goto v___jp_101_;
}
v___jp_101_:
{
if (v___y_102_ == 0)
{
uint8_t v___x_103_; 
v___x_103_ = l_Lean_isSubScriptAlnum(v___x_100_);
if (v___x_103_ == 0)
{
uint32_t v___x_104_; uint8_t v___x_105_; 
v___x_104_ = 95;
v___x_105_ = lean_uint32_dec_eq(v___x_100_, v___x_104_);
if (v___x_105_ == 0)
{
uint32_t v___x_106_; uint8_t v___x_107_; 
v___x_106_ = 39;
v___x_107_ = lean_uint32_dec_eq(v___x_100_, v___x_106_);
v___y_96_ = v___x_107_;
goto v___jp_95_;
}
else
{
v___y_96_ = v___x_105_;
goto v___jp_95_;
}
}
else
{
v___y_96_ = v___x_103_;
goto v___jp_95_;
}
}
else
{
goto v___jp_89_;
}
}
}
else
{
lean_dec(v___x_87_);
lean_dec(v_curr_83_);
return v___x_88_;
}
v___jp_89_:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; uint8_t v___x_93_; 
v___x_90_ = lean_string_utf8_next_fast(v_str_84_, v___x_87_);
v___x_91_ = lean_nat_sub(v___x_90_, v___x_87_);
lean_dec(v___x_87_);
v___x_92_ = lean_nat_add(v_curr_83_, v___x_91_);
lean_dec(v___x_91_);
v___x_93_ = lean_nat_dec_lt(v_curr_83_, v___x_92_);
lean_dec(v_curr_83_);
if (v___x_93_ == 0)
{
lean_dec(v___x_92_);
return v___x_88_;
}
else
{
lean_dec_ref(v___x_88_);
v_curr_83_ = v___x_92_;
goto _start;
}
}
v___jp_95_:
{
if (v___y_96_ == 0)
{
lean_dec(v___x_87_);
lean_dec(v_curr_83_);
return v___x_88_;
}
else
{
goto v___jp_89_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00__private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix_spec__0___boxed(lean_object* v_s_112_, lean_object* v_curr_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00__private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix_spec__0(v_s_112_, v_curr_113_);
lean_dec_ref(v_s_112_);
return v_res_114_;
}
}
static lean_object* _init_l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___closed__3(void){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_118_ = ((lean_object*)(l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___closed__2));
v___x_119_ = lean_unsigned_to_nat(14u);
v___x_120_ = lean_unsigned_to_nat(22u);
v___x_121_ = ((lean_object*)(l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___closed__1));
v___x_122_ = ((lean_object*)(l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___closed__0));
v___x_123_ = l_mkPanicMessageWithDecl(v___x_122_, v___x_121_, v___x_120_, v___x_119_, v___x_118_);
return v___x_123_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix(lean_object* v_s_124_){
_start:
{
lean_object* v___y_126_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; uint8_t v___x_141_; 
v___x_136_ = lean_unsigned_to_nat(0u);
v___x_137_ = lean_string_utf8_byte_size(v_s_124_);
lean_inc_ref(v_s_124_);
v___x_138_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_138_, 0, v_s_124_);
lean_ctor_set(v___x_138_, 1, v___x_136_);
lean_ctor_set(v___x_138_, 2, v___x_137_);
v___x_139_ = lean_unsigned_to_nat(1u);
v___x_140_ = l_Substring_Raw_nextn(v___x_138_, v___x_139_, v___x_136_);
lean_dec_ref(v___x_138_);
v___x_141_ = lean_string_is_valid_pos(v_s_124_, v___x_140_);
if (v___x_141_ == 0)
{
lean_dec(v___x_140_);
lean_dec_ref(v_s_124_);
goto v___jp_133_;
}
else
{
uint8_t v___x_142_; 
v___x_142_ = lean_string_is_valid_pos(v_s_124_, v___x_137_);
if (v___x_142_ == 0)
{
lean_dec(v___x_140_);
lean_dec_ref(v_s_124_);
goto v___jp_133_;
}
else
{
uint8_t v___x_143_; 
v___x_143_ = lean_nat_dec_le(v___x_140_, v___x_137_);
if (v___x_143_ == 0)
{
lean_dec(v___x_140_);
lean_dec_ref(v_s_124_);
goto v___jp_133_;
}
else
{
lean_object* v___x_144_; 
v___x_144_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_144_, 0, v_s_124_);
lean_ctor_set(v___x_144_, 1, v___x_140_);
lean_ctor_set(v___x_144_, 2, v___x_137_);
v___y_126_ = v___x_144_;
goto v___jp_125_;
}
}
}
v___jp_125_:
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v_startInclusive_129_; lean_object* v_endExclusive_130_; lean_object* v___x_131_; uint8_t v___x_132_; 
v___x_127_ = lean_unsigned_to_nat(0u);
v___x_128_ = l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00__private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix_spec__0(v___y_126_, v___x_127_);
lean_dec_ref(v___y_126_);
v_startInclusive_129_ = lean_ctor_get(v___x_128_, 1);
lean_inc(v_startInclusive_129_);
v_endExclusive_130_ = lean_ctor_get(v___x_128_, 2);
lean_inc(v_endExclusive_130_);
lean_dec_ref(v___x_128_);
v___x_131_ = lean_nat_sub(v_endExclusive_130_, v_startInclusive_129_);
lean_dec(v_startInclusive_129_);
lean_dec(v_endExclusive_130_);
v___x_132_ = lean_nat_dec_eq(v___x_131_, v___x_127_);
lean_dec(v___x_131_);
return v___x_132_;
}
v___jp_133_:
{
lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_134_ = lean_obj_once(&l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___closed__3, &l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___closed__3_once, _init_l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___closed__3);
v___x_135_ = l_panic___at___00__private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix_spec__1(v___x_134_);
v___y_126_ = v___x_135_;
goto v___jp_125_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___boxed(lean_object* v_s_145_){
_start:
{
uint8_t v_res_146_; lean_object* v_r_147_; 
v_res_146_ = l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix(v_s_145_);
v_r_147_ = lean_box(v_res_146_);
return v_r_147_;
}
}
static lean_object* _init_l_Lean_Elab_checkValidAutoBoundImplicitName___closed__2(void){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_152_ = ((lean_object*)(l_Lean_Elab_checkValidAutoBoundImplicitName___closed__1));
v___x_153_ = l_Lean_stringToMessageData(v___x_152_);
return v___x_153_;
}
}
static lean_object* _init_l_Lean_Elab_checkValidAutoBoundImplicitName___closed__4(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_155_ = ((lean_object*)(l_Lean_Elab_checkValidAutoBoundImplicitName___closed__3));
v___x_156_ = l_Lean_stringToMessageData(v___x_155_);
return v___x_156_;
}
}
static lean_object* _init_l_Lean_Elab_checkValidAutoBoundImplicitName___closed__9(void){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_163_ = ((lean_object*)(l_Lean_Elab_checkValidAutoBoundImplicitName___closed__8));
v___x_164_ = l_Lean_stringToMessageData(v___x_163_);
return v___x_164_;
}
}
static lean_object* _init_l_Lean_Elab_checkValidAutoBoundImplicitName___closed__11(void){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_166_ = ((lean_object*)(l_Lean_Elab_checkValidAutoBoundImplicitName___closed__10));
v___x_167_ = l_Lean_stringToMessageData(v___x_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkValidAutoBoundImplicitName(lean_object* v_n_168_, uint8_t v_allowed_169_, uint8_t v_relaxed_170_){
_start:
{
uint8_t v___y_174_; 
if (lean_obj_tag(v_n_168_) == 1)
{
lean_object* v_pre_199_; 
v_pre_199_ = lean_ctor_get(v_n_168_, 0);
if (lean_obj_tag(v_pre_199_) == 0)
{
lean_object* v_str_200_; lean_object* v___x_201_; lean_object* v___x_202_; uint8_t v___x_203_; 
v_str_200_ = lean_ctor_get(v_n_168_, 1);
v___x_201_ = lean_string_length(v_str_200_);
v___x_202_ = lean_unsigned_to_nat(0u);
v___x_203_ = lean_nat_dec_eq(v___x_201_, v___x_202_);
if (v___x_203_ == 0)
{
if (v_allowed_169_ == 0)
{
v___y_174_ = v_allowed_169_;
goto v___jp_173_;
}
else
{
if (v_relaxed_170_ == 0)
{
uint8_t v___x_204_; 
lean_inc_ref(v_str_200_);
v___x_204_ = l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix(v_str_200_);
if (v___x_204_ == 0)
{
v___y_174_ = v___x_204_;
goto v___jp_173_;
}
else
{
lean_object* v___x_205_; lean_object* v___x_206_; 
lean_dec_ref(v_n_168_);
v___x_205_ = lean_box(v_allowed_169_);
v___x_206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_206_, 0, v___x_205_);
return v___x_206_;
}
}
else
{
lean_object* v___x_207_; lean_object* v___x_208_; 
lean_dec_ref(v_n_168_);
v___x_207_ = lean_box(v_allowed_169_);
v___x_208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_208_, 0, v___x_207_);
return v___x_208_;
}
}
}
else
{
lean_object* v___x_209_; 
lean_dec_ref(v_n_168_);
v___x_209_ = ((lean_object*)(l_Lean_Elab_checkValidAutoBoundImplicitName___closed__0));
return v___x_209_;
}
}
else
{
lean_dec_ref(v_n_168_);
goto v___jp_171_;
}
}
else
{
lean_dec(v_n_168_);
goto v___jp_171_;
}
v___jp_171_:
{
lean_object* v___x_172_; 
v___x_172_ = ((lean_object*)(l_Lean_Elab_checkValidAutoBoundImplicitName___closed__0));
return v___x_172_;
}
v___jp_173_:
{
if (v_allowed_169_ == 0)
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_175_ = lean_obj_once(&l_Lean_Elab_checkValidAutoBoundImplicitName___closed__2, &l_Lean_Elab_checkValidAutoBoundImplicitName___closed__2_once, _init_l_Lean_Elab_checkValidAutoBoundImplicitName___closed__2);
v___x_176_ = l_Lean_MessageData_ofConstName(v_n_168_, v___y_174_);
v___x_177_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_177_, 0, v___x_175_);
lean_ctor_set(v___x_177_, 1, v___x_176_);
v___x_178_ = lean_obj_once(&l_Lean_Elab_checkValidAutoBoundImplicitName___closed__4, &l_Lean_Elab_checkValidAutoBoundImplicitName___closed__4_once, _init_l_Lean_Elab_checkValidAutoBoundImplicitName___closed__4);
v___x_179_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_179_, 0, v___x_177_);
lean_ctor_set(v___x_179_, 1, v___x_178_);
v___x_180_ = ((lean_object*)(l_Lean_Elab_checkValidAutoBoundImplicitName___closed__7));
v___x_181_ = l_Lean_MessageData_ofConstName(v___x_180_, v___y_174_);
v___x_182_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_179_);
lean_ctor_set(v___x_182_, 1, v___x_181_);
v___x_183_ = lean_obj_once(&l_Lean_Elab_checkValidAutoBoundImplicitName___closed__9, &l_Lean_Elab_checkValidAutoBoundImplicitName___closed__9_once, _init_l_Lean_Elab_checkValidAutoBoundImplicitName___closed__9);
v___x_184_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_184_, 0, v___x_182_);
lean_ctor_set(v___x_184_, 1, v___x_183_);
v___x_185_ = l_Lean_MessageData_note(v___x_184_);
v___x_186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_186_, 0, v___x_185_);
return v___x_186_;
}
else
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_187_ = lean_obj_once(&l_Lean_Elab_checkValidAutoBoundImplicitName___closed__2, &l_Lean_Elab_checkValidAutoBoundImplicitName___closed__2_once, _init_l_Lean_Elab_checkValidAutoBoundImplicitName___closed__2);
v___x_188_ = l_Lean_MessageData_ofConstName(v_n_168_, v___y_174_);
v___x_189_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_189_, 0, v___x_187_);
lean_ctor_set(v___x_189_, 1, v___x_188_);
v___x_190_ = lean_obj_once(&l_Lean_Elab_checkValidAutoBoundImplicitName___closed__11, &l_Lean_Elab_checkValidAutoBoundImplicitName___closed__11_once, _init_l_Lean_Elab_checkValidAutoBoundImplicitName___closed__11);
v___x_191_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_191_, 0, v___x_189_);
lean_ctor_set(v___x_191_, 1, v___x_190_);
v___x_192_ = ((lean_object*)(l_Lean_Elab_checkValidAutoBoundImplicitName___closed__7));
v___x_193_ = l_Lean_MessageData_ofConstName(v___x_192_, v___y_174_);
v___x_194_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_194_, 0, v___x_191_);
lean_ctor_set(v___x_194_, 1, v___x_193_);
v___x_195_ = lean_obj_once(&l_Lean_Elab_checkValidAutoBoundImplicitName___closed__9, &l_Lean_Elab_checkValidAutoBoundImplicitName___closed__9_once, _init_l_Lean_Elab_checkValidAutoBoundImplicitName___closed__9);
v___x_196_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_196_, 0, v___x_194_);
lean_ctor_set(v___x_196_, 1, v___x_195_);
v___x_197_ = l_Lean_MessageData_note(v___x_196_);
v___x_198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_198_, 0, v___x_197_);
return v___x_198_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkValidAutoBoundImplicitName___boxed(lean_object* v_n_210_, lean_object* v_allowed_211_, lean_object* v_relaxed_212_){
_start:
{
uint8_t v_allowed_boxed_213_; uint8_t v_relaxed_boxed_214_; lean_object* v_res_215_; 
v_allowed_boxed_213_ = lean_unbox(v_allowed_211_);
v_relaxed_boxed_214_ = lean_unbox(v_relaxed_212_);
v_res_215_ = l_Lean_Elab_checkValidAutoBoundImplicitName(v_n_210_, v_allowed_boxed_213_, v_relaxed_boxed_214_);
return v_res_215_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_isValidAutoBoundLevelName(lean_object* v_n_216_, uint8_t v_relaxed_217_){
_start:
{
if (lean_obj_tag(v_n_216_) == 1)
{
lean_object* v_pre_218_; lean_object* v_str_219_; uint8_t v___y_221_; uint32_t v___y_224_; 
v_pre_218_ = lean_ctor_get(v_n_216_, 0);
lean_inc(v_pre_218_);
v_str_219_ = lean_ctor_get(v_n_216_, 1);
lean_inc_ref(v_str_219_);
lean_dec_ref(v_n_216_);
if (lean_obj_tag(v_pre_218_) == 0)
{
lean_object* v___x_229_; lean_object* v___x_230_; uint8_t v___x_231_; 
v___x_229_ = lean_unsigned_to_nat(0u);
v___x_230_ = lean_string_length(v_str_219_);
v___x_231_ = lean_nat_dec_lt(v___x_229_, v___x_230_);
if (v___x_231_ == 0)
{
lean_dec_ref(v_str_219_);
return v___x_231_;
}
else
{
if (v_relaxed_217_ == 0)
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_232_ = lean_string_utf8_byte_size(v_str_219_);
lean_inc_ref(v_str_219_);
v___x_233_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_233_, 0, v_str_219_);
lean_ctor_set(v___x_233_, 1, v___x_229_);
lean_ctor_set(v___x_233_, 2, v___x_232_);
v___x_234_ = l_String_Slice_Pos_get_x3f(v___x_233_, v___x_229_);
lean_dec_ref(v___x_233_);
if (lean_obj_tag(v___x_234_) == 0)
{
uint32_t v___x_235_; 
v___x_235_ = 65;
v___y_224_ = v___x_235_;
goto v___jp_223_;
}
else
{
lean_object* v_val_236_; uint32_t v___x_237_; 
v_val_236_ = lean_ctor_get(v___x_234_, 0);
lean_inc(v_val_236_);
lean_dec_ref(v___x_234_);
v___x_237_ = lean_unbox_uint32(v_val_236_);
lean_dec(v_val_236_);
v___y_224_ = v___x_237_;
goto v___jp_223_;
}
}
else
{
lean_dec_ref(v_str_219_);
return v_relaxed_217_;
}
}
}
else
{
uint8_t v___x_238_; 
lean_dec_ref(v_str_219_);
lean_dec(v_pre_218_);
v___x_238_ = 0;
return v___x_238_;
}
v___jp_220_:
{
if (v___y_221_ == 0)
{
lean_dec_ref(v_str_219_);
return v___y_221_;
}
else
{
uint8_t v___x_222_; 
v___x_222_ = l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix(v_str_219_);
return v___x_222_;
}
}
v___jp_223_:
{
uint32_t v___x_225_; uint8_t v___x_226_; 
v___x_225_ = 97;
v___x_226_ = lean_uint32_dec_le(v___x_225_, v___y_224_);
if (v___x_226_ == 0)
{
v___y_221_ = v___x_226_;
goto v___jp_220_;
}
else
{
uint32_t v___x_227_; uint8_t v___x_228_; 
v___x_227_ = 122;
v___x_228_ = lean_uint32_dec_le(v___y_224_, v___x_227_);
v___y_221_ = v___x_228_;
goto v___jp_220_;
}
}
}
else
{
uint8_t v___x_239_; 
lean_dec(v_n_216_);
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
lean_object* v___x_245_; 
v___x_245_ = l_Lean_instInhabitedPersistentArray_default(lean_box(0));
return v___x_245_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default___closed__1(void){
_start:
{
lean_object* v___x_246_; uint8_t v___x_247_; lean_object* v___x_248_; 
v___x_246_ = lean_obj_once(&l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default___closed__0, &l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default___closed__0_once, _init_l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default___closed__0);
v___x_247_ = 0;
v___x_248_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_248_, 0, v___x_246_);
lean_ctor_set_uint8(v___x_248_, sizeof(void*)*1, v___x_247_);
return v___x_248_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default(void){
_start:
{
lean_object* v___x_249_; 
v___x_249_ = lean_obj_once(&l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default___closed__1, &l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default___closed__1_once, _init_l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default___closed__1);
return v___x_249_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedAutoBoundImplicitContext(void){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default;
return v___x_250_;
}
}
static lean_object* _init_l_Lean_Elab_instEmptyCollectionAutoBoundImplicitContext___closed__0(void){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_251_ = lean_unsigned_to_nat(32u);
v___x_252_ = lean_mk_empty_array_with_capacity(v___x_251_);
v___x_253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_253_, 0, v___x_252_);
return v___x_253_;
}
}
static lean_object* _init_l_Lean_Elab_instEmptyCollectionAutoBoundImplicitContext___closed__1(void){
_start:
{
size_t v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_254_ = ((size_t)5ULL);
v___x_255_ = lean_unsigned_to_nat(0u);
v___x_256_ = lean_unsigned_to_nat(32u);
v___x_257_ = lean_mk_empty_array_with_capacity(v___x_256_);
v___x_258_ = lean_obj_once(&l_Lean_Elab_instEmptyCollectionAutoBoundImplicitContext___closed__0, &l_Lean_Elab_instEmptyCollectionAutoBoundImplicitContext___closed__0_once, _init_l_Lean_Elab_instEmptyCollectionAutoBoundImplicitContext___closed__0);
v___x_259_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_259_, 0, v___x_258_);
lean_ctor_set(v___x_259_, 1, v___x_257_);
lean_ctor_set(v___x_259_, 2, v___x_255_);
lean_ctor_set(v___x_259_, 3, v___x_255_);
lean_ctor_set_usize(v___x_259_, 4, v___x_254_);
return v___x_259_;
}
}
static lean_object* _init_l_Lean_Elab_instEmptyCollectionAutoBoundImplicitContext___closed__2(void){
_start:
{
lean_object* v___x_260_; uint8_t v___x_261_; lean_object* v___x_262_; 
v___x_260_ = lean_obj_once(&l_Lean_Elab_instEmptyCollectionAutoBoundImplicitContext___closed__1, &l_Lean_Elab_instEmptyCollectionAutoBoundImplicitContext___closed__1_once, _init_l_Lean_Elab_instEmptyCollectionAutoBoundImplicitContext___closed__1);
v___x_261_ = 0;
v___x_262_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_262_, 0, v___x_260_);
lean_ctor_set_uint8(v___x_262_, sizeof(void*)*1, v___x_261_);
return v___x_262_;
}
}
static lean_object* _init_l_Lean_Elab_instEmptyCollectionAutoBoundImplicitContext(void){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = lean_obj_once(&l_Lean_Elab_instEmptyCollectionAutoBoundImplicitContext___closed__2, &l_Lean_Elab_instEmptyCollectionAutoBoundImplicitContext___closed__2_once, _init_l_Lean_Elab_instEmptyCollectionAutoBoundImplicitContext___closed__2);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_AutoBoundImplicitContext_push(lean_object* v_ctx_264_, lean_object* v_x_265_){
_start:
{
uint8_t v_autoImplicitEnabled_266_; lean_object* v_boundVariables_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_275_; 
v_autoImplicitEnabled_266_ = lean_ctor_get_uint8(v_ctx_264_, sizeof(void*)*1);
v_boundVariables_267_ = lean_ctor_get(v_ctx_264_, 0);
v_isSharedCheck_275_ = !lean_is_exclusive(v_ctx_264_);
if (v_isSharedCheck_275_ == 0)
{
v___x_269_ = v_ctx_264_;
v_isShared_270_ = v_isSharedCheck_275_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_boundVariables_267_);
lean_dec(v_ctx_264_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_275_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_271_; lean_object* v___x_273_; 
v___x_271_ = l_Lean_PersistentArray_push___redArg(v_boundVariables_267_, v_x_265_);
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 0, v___x_271_);
v___x_273_ = v___x_269_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v___x_271_);
lean_ctor_set_uint8(v_reuseFailAlloc_274_, sizeof(void*)*1, v_autoImplicitEnabled_266_);
v___x_273_ = v_reuseFailAlloc_274_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
return v___x_273_;
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

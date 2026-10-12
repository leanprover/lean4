// Lean compiler output
// Module: Lean.Compiler.ExportAttr
// Imports: public import Lean.Attributes
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
lean_object* l_Lean_Attribute_Builtin_getId(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_String_instInhabitedSlice;
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Substring_Raw_nextn(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_is_valid_pos(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
lean_object* l_Lean_registerParametricAttribute___redArg(lean_object*);
lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId___closed__0 = (const lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId___closed__0_value;
static const lean_string_object l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId___closed__1 = (const lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId___closed__2 = (const lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId___closed__2_value;
static lean_once_cell_t l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId___closed__3;
LEAN_EXPORT uint8_t l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppName(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppName___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Invalid `export` function name: `"};
static const lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__2___closed__2_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "` is not a valid C++ identifier"};
static const lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__2___closed__2_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__2___closed__2_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "exportAttr"};
static const lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(105, 101, 238, 215, 35, 66, 156, 98)}};
static const lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "export"};
static const lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__7_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(191, 25, 157, 3, 50, 244, 45, 226)}};
static const lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__7_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__7_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__8_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "name to be used by code generators"};
static const lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__8_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__8_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__9_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__7_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__8_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__9_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__9_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 8, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__9_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exportAttr;
static const lean_string_object l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 741, .m_capacity = 741, .m_length = 740, .m_data = "Exports a function under the provided unmangled symbol name. This can be used to refer to Lean\nfunctions from other programming languages like C.\n\nExample:\n```\n@[export lean_color_from_map]\ndef colorValue (properties : @& Std.HashMap String String) : UInt32 :=\n  match properties[\"color\"]\? with\n  | some \"red\" => 0xff0000\n  | some \"green\" => 0x00ff00\n  | some \"blue\" => 0x0000ff\n  | _ => -1\n```\nC code:\n```c\n#include <lean/lean.h>\n\nuint32_t lean_color_from_map(b_lean_obj_arg properties);\n\nvoid fill_rectangle_from_map(b_lean_obj_arg properties) {\n    uint32_t color = lean_color_from_map(properties);\n    // ...\n}\n```\n\nThe opposite of this is `@[extern]`, which allows Lean functions to refer to functions from other\nprogramming languages."};
static const lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_docString__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(24) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(63) << 1) | 1)),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__1_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(54) << 1) | 1)),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(54) << 1) | 1)),((lean_object*)(((size_t)(29) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__3_value),((lean_object*)(((size_t)(19) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__4_value),((lean_object*)(((size_t)(29) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* lean_get_export_name_for(lean_object*, lean_object*);
static const lean_string_object l_Lean_isExport___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "main"};
static const lean_object* l_Lean_isExport___closed__0 = (const lean_object*)&l_Lean_isExport___closed__0_value;
static const lean_ctor_object l_Lean_isExport___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isExport___closed__0_value),LEAN_SCALAR_PTR_LITERAL(167, 14, 67, 68, 149, 142, 182, 10)}};
static const lean_object* l_Lean_isExport___closed__1 = (const lean_object*)&l_Lean_isExport___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_isExport(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isExport___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId_spec__1(lean_object* v_msg_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = l_String_instInhabitedSlice;
v___x_3_ = lean_panic_fn_borrowed(v___x_2_, v_msg_1_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId_spec__0(lean_object* v_s_4_, lean_object* v_pos_5_){
_start:
{
lean_object* v_str_6_; lean_object* v_startInclusive_7_; lean_object* v_endExclusive_8_; lean_object* v___x_9_; lean_object* v___x_18_; lean_object* v___x_19_; uint8_t v_decide_20_; 
v_str_6_ = lean_ctor_get(v_s_4_, 0);
v_startInclusive_7_ = lean_ctor_get(v_s_4_, 1);
v_endExclusive_8_ = lean_ctor_get(v_s_4_, 2);
v___x_9_ = lean_nat_add(v_startInclusive_7_, v_pos_5_);
v___x_18_ = lean_unsigned_to_nat(0u);
v___x_19_ = lean_nat_sub(v_endExclusive_8_, v___x_9_);
v_decide_20_ = lean_nat_dec_eq(v___x_18_, v___x_19_);
lean_dec(v___x_19_);
if (v_decide_20_ == 0)
{
uint32_t v___x_21_; uint32_t v___x_35_; uint8_t v___x_36_; 
v___x_21_ = lean_string_utf8_get_fast(v_str_6_, v___x_9_);
v___x_35_ = 65;
v___x_36_ = lean_uint32_dec_le(v___x_35_, v___x_21_);
if (v___x_36_ == 0)
{
goto v___jp_30_;
}
else
{
uint32_t v___x_37_; uint8_t v___x_38_; 
v___x_37_ = 90;
v___x_38_ = lean_uint32_dec_le(v___x_21_, v___x_37_);
if (v___x_38_ == 0)
{
goto v___jp_30_;
}
else
{
goto v___jp_10_;
}
}
v___jp_22_:
{
uint32_t v___x_23_; uint8_t v___x_24_; 
v___x_23_ = 95;
v___x_24_ = lean_uint32_dec_eq(v___x_21_, v___x_23_);
if (v___x_24_ == 0)
{
lean_dec(v___x_9_);
return v_pos_5_;
}
else
{
goto v___jp_10_;
}
}
v___jp_25_:
{
uint32_t v___x_26_; uint8_t v___x_27_; 
v___x_26_ = 48;
v___x_27_ = lean_uint32_dec_le(v___x_26_, v___x_21_);
if (v___x_27_ == 0)
{
goto v___jp_22_;
}
else
{
uint32_t v___x_28_; uint8_t v___x_29_; 
v___x_28_ = 57;
v___x_29_ = lean_uint32_dec_le(v___x_21_, v___x_28_);
if (v___x_29_ == 0)
{
goto v___jp_22_;
}
else
{
goto v___jp_10_;
}
}
}
v___jp_30_:
{
uint32_t v___x_31_; uint8_t v___x_32_; 
v___x_31_ = 97;
v___x_32_ = lean_uint32_dec_le(v___x_31_, v___x_21_);
if (v___x_32_ == 0)
{
goto v___jp_25_;
}
else
{
uint32_t v___x_33_; uint8_t v___x_34_; 
v___x_33_ = 122;
v___x_34_ = lean_uint32_dec_le(v___x_21_, v___x_33_);
if (v___x_34_ == 0)
{
goto v___jp_25_;
}
else
{
goto v___jp_10_;
}
}
}
}
else
{
lean_dec(v___x_9_);
return v_pos_5_;
}
v___jp_10_:
{
lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; uint8_t v___x_16_; 
v___x_11_ = lean_string_utf8_next_fast(v_str_6_, v___x_9_);
v___x_12_ = lean_nat_sub(v___x_11_, v___x_9_);
lean_dec(v___x_9_);
v___x_13_ = lean_nat_add(v_pos_5_, v___x_12_);
lean_dec(v___x_12_);
v___x_14_ = lean_unsigned_to_nat(1u);
v___x_15_ = lean_nat_add(v_pos_5_, v___x_14_);
v___x_16_ = lean_nat_dec_le(v___x_15_, v___x_13_);
lean_dec(v___x_15_);
if (v___x_16_ == 0)
{
lean_dec(v___x_13_);
return v_pos_5_;
}
else
{
lean_dec(v_pos_5_);
v_pos_5_ = v___x_13_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId_spec__0___boxed(lean_object* v_s_39_, lean_object* v_pos_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId_spec__0(v_s_39_, v_pos_40_);
lean_dec_ref(v_s_39_);
return v_res_41_;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId___closed__3(void){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_45_ = ((lean_object*)(l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId___closed__2));
v___x_46_ = lean_unsigned_to_nat(14u);
v___x_47_ = lean_unsigned_to_nat(22u);
v___x_48_ = ((lean_object*)(l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId___closed__1));
v___x_49_ = ((lean_object*)(l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId___closed__0));
v___x_50_ = l_mkPanicMessageWithDecl(v___x_49_, v___x_48_, v___x_47_, v___x_46_, v___x_45_);
return v___x_50_;
}
}
uint8_t l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId(lean_object* v_id_51_){
_start:
{
lean_object* v___y_53_; lean_object* v_startInclusive_54_; lean_object* v_endExclusive_55_; lean_object* v___y_61_; lean_object* v___y_62_; uint8_t v___y_63_; uint32_t v___y_79_; uint32_t v___y_85_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_90_ = lean_unsigned_to_nat(0u);
v___x_91_ = lean_string_utf8_byte_size(v_id_51_);
lean_inc_ref(v_id_51_);
v___x_92_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_92_, 0, v_id_51_);
lean_ctor_set(v___x_92_, 1, v___x_90_);
lean_ctor_set(v___x_92_, 2, v___x_91_);
v___x_93_ = l_String_Slice_Pos_get_x3f(v___x_92_, v___x_90_);
lean_dec_ref_known(v___x_92_, 3);
if (lean_obj_tag(v___x_93_) == 0)
{
uint32_t v___x_94_; 
v___x_94_ = 65;
v___y_85_ = v___x_94_;
goto v___jp_84_;
}
else
{
lean_object* v_val_95_; uint32_t v___x_96_; 
v_val_95_ = lean_ctor_get(v___x_93_, 0);
lean_inc(v_val_95_);
lean_dec_ref_known(v___x_93_, 1);
v___x_96_ = lean_unbox_uint32(v_val_95_);
lean_dec(v_val_95_);
v___y_85_ = v___x_96_;
goto v___jp_84_;
}
v___jp_52_:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; uint8_t v_decide_59_; 
v___x_56_ = lean_unsigned_to_nat(0u);
v___x_57_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId_spec__0(v___y_53_, v___x_56_);
lean_dec_ref(v___y_53_);
v___x_58_ = lean_nat_sub(v_endExclusive_55_, v_startInclusive_54_);
lean_dec(v_startInclusive_54_);
lean_dec(v_endExclusive_55_);
v_decide_59_ = lean_nat_dec_eq(v___x_57_, v___x_58_);
lean_dec(v___x_58_);
lean_dec(v___x_57_);
return v_decide_59_;
}
v___jp_60_:
{
if (v___y_63_ == 0)
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v_startInclusive_66_; lean_object* v_endExclusive_67_; 
lean_dec(v___y_62_);
lean_dec(v___y_61_);
lean_dec_ref(v_id_51_);
v___x_64_ = lean_obj_once(&l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId___closed__3, &l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId___closed__3_once, _init_l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId___closed__3);
v___x_65_ = l_panic___at___00__private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId_spec__1(v___x_64_);
v_startInclusive_66_ = lean_ctor_get(v___x_65_, 1);
lean_inc(v_startInclusive_66_);
v_endExclusive_67_ = lean_ctor_get(v___x_65_, 2);
lean_inc(v_endExclusive_67_);
v___y_53_ = v___x_65_;
v_startInclusive_54_ = v_startInclusive_66_;
v_endExclusive_55_ = v_endExclusive_67_;
goto v___jp_52_;
}
else
{
lean_object* v___x_68_; 
lean_inc(v___y_62_);
lean_inc(v___y_61_);
v___x_68_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_68_, 0, v_id_51_);
lean_ctor_set(v___x_68_, 1, v___y_61_);
lean_ctor_set(v___x_68_, 2, v___y_62_);
v___y_53_ = v___x_68_;
v_startInclusive_54_ = v___y_61_;
v_endExclusive_55_ = v___y_62_;
goto v___jp_52_;
}
}
v___jp_69_:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; uint8_t v___x_75_; 
v___x_70_ = lean_unsigned_to_nat(0u);
v___x_71_ = lean_string_utf8_byte_size(v_id_51_);
lean_inc_ref(v_id_51_);
v___x_72_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_72_, 0, v_id_51_);
lean_ctor_set(v___x_72_, 1, v___x_70_);
lean_ctor_set(v___x_72_, 2, v___x_71_);
v___x_73_ = lean_unsigned_to_nat(1u);
v___x_74_ = l_Substring_Raw_nextn(v___x_72_, v___x_73_, v___x_70_);
lean_dec_ref_known(v___x_72_, 3);
v___x_75_ = lean_string_is_valid_pos(v_id_51_, v___x_74_);
if (v___x_75_ == 0)
{
v___y_61_ = v___x_74_;
v___y_62_ = v___x_71_;
v___y_63_ = v___x_75_;
goto v___jp_60_;
}
else
{
uint8_t v___x_76_; 
v___x_76_ = lean_string_is_valid_pos(v_id_51_, v___x_71_);
if (v___x_76_ == 0)
{
v___y_61_ = v___x_74_;
v___y_62_ = v___x_71_;
v___y_63_ = v___x_76_;
goto v___jp_60_;
}
else
{
uint8_t v___x_77_; 
v___x_77_ = lean_nat_dec_le(v___x_74_, v___x_71_);
v___y_61_ = v___x_74_;
v___y_62_ = v___x_71_;
v___y_63_ = v___x_77_;
goto v___jp_60_;
}
}
}
v___jp_78_:
{
uint32_t v___x_80_; uint8_t v___x_81_; 
v___x_80_ = 97;
v___x_81_ = lean_uint32_dec_le(v___x_80_, v___y_79_);
if (v___x_81_ == 0)
{
lean_dec_ref(v_id_51_);
return v___x_81_;
}
else
{
uint32_t v___x_82_; uint8_t v___x_83_; 
v___x_82_ = 122;
v___x_83_ = lean_uint32_dec_le(v___y_79_, v___x_82_);
if (v___x_83_ == 0)
{
lean_dec_ref(v_id_51_);
return v___x_83_;
}
else
{
goto v___jp_69_;
}
}
}
v___jp_84_:
{
uint32_t v___x_86_; uint8_t v___x_87_; 
v___x_86_ = 65;
v___x_87_ = lean_uint32_dec_le(v___x_86_, v___y_85_);
if (v___x_87_ == 0)
{
v___y_79_ = v___y_85_;
goto v___jp_78_;
}
else
{
uint32_t v___x_88_; uint8_t v___x_89_; 
v___x_88_ = 90;
v___x_89_ = lean_uint32_dec_le(v___y_85_, v___x_88_);
if (v___x_89_ == 0)
{
v___y_79_ = v___y_85_;
goto v___jp_78_;
}
else
{
goto v___jp_69_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId_0interp(lean_interpreter_value* stack)
{
lean_object* v_id_51_ = stack[0].m_obj;
uint8_t v_res_97_;
v_res_97_ = l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId(v_id_51_);
stack->m_num = v_res_97_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId___boxed(lean_object* v_id_98_){
_start:
{
uint8_t v_res_99_; lean_object* v_r_100_; 
v_res_99_ = l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId(v_id_98_);
v_r_100_ = lean_box(v_res_99_);
return v_r_100_;
}
}
uint8_t l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppName(lean_object* v_x_101_){
_start:
{
if (lean_obj_tag(v_x_101_) == 1)
{
lean_object* v_pre_102_; 
v_pre_102_ = lean_ctor_get(v_x_101_, 0);
if (lean_obj_tag(v_pre_102_) == 0)
{
lean_object* v_str_103_; uint8_t v___x_104_; 
v_str_103_ = lean_ctor_get(v_x_101_, 1);
lean_inc_ref(v_str_103_);
lean_dec_ref_known(v_x_101_, 2);
v___x_104_ = l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId(v_str_103_);
return v___x_104_;
}
else
{
lean_object* v_str_105_; uint8_t v___x_106_; 
lean_inc(v_pre_102_);
v_str_105_ = lean_ctor_get(v_x_101_, 1);
lean_inc_ref(v_str_105_);
lean_dec_ref_known(v_x_101_, 2);
v___x_106_ = l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId(v_str_105_);
if (v___x_106_ == 0)
{
lean_dec(v_pre_102_);
return v___x_106_;
}
else
{
v_x_101_ = v_pre_102_;
goto _start;
}
}
}
else
{
uint8_t v___x_108_; 
lean_dec(v_x_101_);
v___x_108_ = 0;
return v___x_108_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppName_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_101_ = stack[0].m_obj;
uint8_t v_res_109_;
v_res_109_ = l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppName(v_x_101_);
stack->m_num = v_res_109_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppName___boxed(lean_object* v_x_110_){
_start:
{
uint8_t v_res_111_; lean_object* v_r_112_; 
v_res_111_ = l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppName(v_x_110_);
v_r_112_ = lean_box(v_res_111_);
return v_r_112_;
}
}
uint8_t l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_(lean_object* v_env_113_, lean_object* v_n_114_, lean_object* v_x_115_){
_start:
{
uint8_t v___x_116_; uint8_t v___x_117_; 
v___x_116_ = 1;
v___x_117_ = l_Lean_Environment_contains(v_env_113_, v_n_114_, v___x_116_);
return v___x_117_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_env_113_ = stack[0].m_obj;
lean_object* v_n_114_ = stack[1].m_obj;
lean_object* v_x_115_ = stack[2].m_obj;
uint8_t v_res_118_;
v_res_118_ = l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_(v_env_113_, v_n_114_, v_x_115_);
stack->m_num = v_res_118_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2____boxed(lean_object* v_env_119_, lean_object* v_n_120_, lean_object* v_x_121_){
_start:
{
uint8_t v_res_122_; lean_object* v_r_123_; 
v_res_122_ = l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_(v_env_119_, v_n_120_, v_x_121_);
lean_dec(v_x_121_);
v_r_123_ = lean_box(v_res_122_);
return v_r_123_;
}
}
lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_(lean_object* v_x_124_, lean_object* v_x_125_, lean_object* v_x_126_, lean_object* v___y_127_){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_129_ = lean_box(0);
v___x_130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_130_, 0, v___x_129_);
return v___x_130_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_x_124_ = stack[0].m_obj;
lean_object* v_x_125_ = stack[1].m_obj;
lean_object* v_x_126_ = stack[2].m_obj;
lean_object* v___y_127_ = stack[3].m_obj;
lean_object* v_res_131_;
v_res_131_ = l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_(v_x_124_, v_x_125_, v_x_126_, v___y_127_);
stack->m_obj
 = v_res_131_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2____boxed(lean_object* v_x_132_, lean_object* v_x_133_, lean_object* v_x_134_, lean_object* v___y_135_, lean_object* v___y_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_(v_x_132_, v_x_133_, v_x_134_, v___y_135_);
lean_dec(v___y_135_);
lean_dec_ref(v_x_134_);
lean_dec(v_x_133_);
lean_dec(v_x_132_);
return v_res_137_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_138_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_139_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_140_, 0, v___x_139_);
return v___x_140_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_141_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_142_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_143_ = lean_unsigned_to_nat(0u);
v___x_144_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
lean_ctor_set(v___x_144_, 1, v___x_143_);
lean_ctor_set(v___x_144_, 2, v___x_143_);
lean_ctor_set(v___x_144_, 3, v___x_143_);
lean_ctor_set(v___x_144_, 4, v___x_142_);
lean_ctor_set(v___x_144_, 5, v___x_142_);
lean_ctor_set(v___x_144_, 6, v___x_142_);
lean_ctor_set(v___x_144_, 7, v___x_142_);
lean_ctor_set(v___x_144_, 8, v___x_142_);
lean_ctor_set(v___x_144_, 9, v___x_142_);
lean_ctor_set(v___x_144_, 10, v___x_142_);
lean_ctor_set(v___x_144_, 11, v___x_141_);
return v___x_144_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_145_ = lean_unsigned_to_nat(32u);
v___x_146_ = lean_mk_empty_array_with_capacity(v___x_145_);
v___x_147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_147_, 0, v___x_146_);
return v___x_147_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_148_ = ((size_t)5ULL);
v___x_149_ = lean_unsigned_to_nat(0u);
v___x_150_ = lean_unsigned_to_nat(32u);
v___x_151_ = lean_mk_empty_array_with_capacity(v___x_150_);
v___x_152_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_153_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_153_, 0, v___x_152_);
lean_ctor_set(v___x_153_, 1, v___x_151_);
lean_ctor_set(v___x_153_, 2, v___x_149_);
lean_ctor_set(v___x_153_, 3, v___x_149_);
lean_ctor_set_usize(v___x_153_, 4, v___x_148_);
return v___x_153_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_154_ = lean_box(1);
v___x_155_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_156_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_157_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
lean_ctor_set(v___x_157_, 1, v___x_155_);
lean_ctor_set(v___x_157_, 2, v___x_154_);
return v___x_157_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_158_, lean_object* v___y_159_, lean_object* v___y_160_){
_start:
{
lean_object* v___x_162_; lean_object* v_toCold_163_; lean_object* v_env_164_; lean_object* v_options_165_; uint8_t v___x_166_; lean_object* v_env_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_162_ = lean_st_ref_get(v___y_160_);
v_toCold_163_ = lean_ctor_get(v___y_159_, 0);
v_env_164_ = lean_ctor_get(v___x_162_, 0);
lean_inc_ref(v_env_164_);
lean_dec(v___x_162_);
v_options_165_ = lean_ctor_get(v_toCold_163_, 2);
v___x_166_ = 0;
v_env_167_ = l_Lean_Environment_setRecordingDeps(v_env_164_, v___x_166_);
v___x_168_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_169_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__5);
lean_inc_ref(v_options_165_);
v___x_170_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_170_, 0, v_env_167_);
lean_ctor_set(v___x_170_, 1, v___x_168_);
lean_ctor_set(v___x_170_, 2, v___x_169_);
lean_ctor_set(v___x_170_, 3, v_options_165_);
v___x_171_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
lean_ctor_set(v___x_171_, 1, v_msgData_158_);
v___x_172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_172_, 0, v___x_171_);
return v___x_172_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_158_ = stack[0].m_obj;
lean_object* v___y_159_ = stack[1].m_obj;
lean_object* v___y_160_ = stack[2].m_obj;
lean_object* v_res_173_;
v_res_173_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0(v_msgData_158_, v___y_159_, v___y_160_);
stack->m_obj
 = v_res_173_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0(v_msgData_174_, v___y_175_, v___y_176_);
lean_dec(v___y_176_);
lean_dec_ref(v___y_175_);
return v_res_178_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_179_, lean_object* v___y_180_, lean_object* v___y_181_){
_start:
{
lean_object* v_ref_183_; lean_object* v___x_184_; lean_object* v_a_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_193_; 
v_ref_183_ = lean_ctor_get(v___y_180_, 2);
v___x_184_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0(v_msg_179_, v___y_180_, v___y_181_);
v_a_185_ = lean_ctor_get(v___x_184_, 0);
v_isSharedCheck_193_ = !lean_is_exclusive(v___x_184_);
if (v_isSharedCheck_193_ == 0)
{
v___x_187_ = v___x_184_;
v_isShared_188_ = v_isSharedCheck_193_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_a_185_);
lean_dec(v___x_184_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_193_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_189_; lean_object* v___x_191_; 
lean_inc(v_ref_183_);
v___x_189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_189_, 0, v_ref_183_);
lean_ctor_set(v___x_189_, 1, v_a_185_);
if (v_isShared_188_ == 0)
{
lean_ctor_set_tag(v___x_187_, 1);
lean_ctor_set(v___x_187_, 0, v___x_189_);
v___x_191_ = v___x_187_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v___x_189_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
return v___x_191_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_179_ = stack[0].m_obj;
lean_object* v___y_180_ = stack[1].m_obj;
lean_object* v___y_181_ = stack[2].m_obj;
lean_object* v_res_194_;
v_res_194_ = l_Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0___redArg(v_msg_179_, v___y_180_, v___y_181_);
stack->m_obj
 = v_res_194_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l_Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0___redArg(v_msg_195_, v___y_196_, v___y_197_);
lean_dec(v___y_197_);
lean_dec_ref(v___y_196_);
return v_res_199_;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_201_ = ((lean_object*)(l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_));
v___x_202_ = l_Lean_stringToMessageData(v___x_201_);
return v___x_202_;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_204_ = ((lean_object*)(l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__2___closed__2_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_));
v___x_205_ = l_Lean_stringToMessageData(v___x_204_);
return v___x_205_;
}
}
lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_(lean_object* v_x_206_, lean_object* v_stx_207_, lean_object* v___y_208_, lean_object* v___y_209_){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = l_Lean_Attribute_Builtin_getId(v_stx_207_, v___y_208_, v___y_209_);
if (lean_obj_tag(v___x_211_) == 0)
{
lean_object* v_a_212_; uint8_t v___x_213_; 
v_a_212_ = lean_ctor_get(v___x_211_, 0);
lean_inc(v_a_212_);
v___x_213_ = l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppName(v_a_212_);
if (v___x_213_ == 0)
{
lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v_a_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_227_; 
lean_inc(v_a_212_);
lean_dec_ref_known(v___x_211_, 1);
v___x_214_ = lean_obj_once(&l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_, &l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_);
v___x_215_ = l_Lean_MessageData_ofName(v_a_212_);
v___x_216_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_216_, 0, v___x_214_);
lean_ctor_set(v___x_216_, 1, v___x_215_);
v___x_217_ = lean_obj_once(&l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_, &l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_);
v___x_218_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_218_, 0, v___x_216_);
lean_ctor_set(v___x_218_, 1, v___x_217_);
v___x_219_ = l_Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0___redArg(v___x_218_, v___y_208_, v___y_209_);
v_a_220_ = lean_ctor_get(v___x_219_, 0);
v_isSharedCheck_227_ = !lean_is_exclusive(v___x_219_);
if (v_isSharedCheck_227_ == 0)
{
v___x_222_ = v___x_219_;
v_isShared_223_ = v_isSharedCheck_227_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_a_220_);
lean_dec(v___x_219_);
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
else
{
return v___x_211_;
}
}
else
{
return v___x_211_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_x_206_ = stack[0].m_obj;
lean_object* v_stx_207_ = stack[1].m_obj;
lean_object* v___y_208_ = stack[2].m_obj;
lean_object* v___y_209_ = stack[3].m_obj;
lean_object* v_res_228_;
v_res_228_ = l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_(v_x_206_, v_stx_207_, v___y_208_, v___y_209_);
stack->m_obj
 = v_res_228_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2____boxed(lean_object* v_x_229_, lean_object* v_stx_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_(v_x_229_, v_stx_230_, v___y_231_, v___y_232_);
lean_dec(v___y_232_);
lean_dec_ref(v___y_231_);
lean_dec(v_x_229_);
return v_res_234_;
}
}
lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_259_ = ((lean_object*)(l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_));
v___x_260_ = l_Lean_registerParametricAttribute___redArg(v___x_259_);
return v___x_260_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_261_;
v_res_261_ = l___private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_();
stack->m_obj
 = v_res_261_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2____boxed(lean_object* v_a_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l___private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_();
return v_res_263_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_264_, lean_object* v_msg_265_, lean_object* v___y_266_, lean_object* v___y_267_){
_start:
{
lean_object* v___x_269_; 
v___x_269_ = l_Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0___redArg(v_msg_265_, v___y_266_, v___y_267_);
return v___x_269_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_265_ = stack[1].m_obj;
lean_object* v___y_266_ = stack[2].m_obj;
lean_object* v___y_267_ = stack[3].m_obj;
lean_object* v_res_270_;
v_res_270_ = l_Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0(lean_box(0), v_msg_265_, v___y_266_, v___y_267_);
stack->m_obj
 = v_res_270_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_271_, lean_object* v_msg_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0(v_00_u03b1_271_, v_msg_272_, v___y_273_, v___y_274_);
lean_dec(v___y_274_);
lean_dec_ref(v___y_273_);
return v_res_276_;
}
}
lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_docString__1(){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_279_ = ((lean_object*)(l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_));
v___x_280_ = ((lean_object*)(l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_docString__1___closed__0));
v___x_281_ = l_Lean_addBuiltinDocString(v___x_279_, v___x_280_);
return v___x_281_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_282_;
v_res_282_ = l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_docString__1();
stack->m_obj
 = v_res_282_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_docString__1___boxed(lean_object* v_a_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_docString__1();
return v_res_284_;
}
}
lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3(){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_311_ = ((lean_object*)(l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_));
v___x_312_ = ((lean_object*)(l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__6));
v___x_313_ = l_Lean_addBuiltinDeclarationRanges(v___x_311_, v___x_312_);
return v___x_313_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_314_;
v_res_314_ = l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3();
stack->m_obj
 = v_res_314_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___boxed(lean_object* v_a_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3();
return v_res_316_;
}
}
LEAN_EXPORT lean_object* lean_get_export_name_for(lean_object* v_env_317_, lean_object* v_n_318_){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_319_ = lean_box(0);
v___x_320_ = l_Lean_exportAttr;
v___x_321_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_319_, v___x_320_, v_env_317_, v_n_318_);
return v___x_321_;
}
}
uint8_t l_Lean_isExport(lean_object* v_env_325_, lean_object* v_n_326_){
_start:
{
lean_object* v___x_327_; 
lean_inc(v_n_326_);
v___x_327_ = lean_get_export_name_for(v_env_325_, v_n_326_);
if (lean_obj_tag(v___x_327_) == 0)
{
lean_object* v___x_328_; uint8_t v___x_329_; 
v___x_328_ = ((lean_object*)(l_Lean_isExport___closed__1));
v___x_329_ = lean_name_eq(v_n_326_, v___x_328_);
lean_dec(v_n_326_);
return v___x_329_;
}
else
{
uint8_t v___x_330_; 
lean_dec_ref_known(v___x_327_, 1);
lean_dec(v_n_326_);
v___x_330_ = 1;
return v___x_330_;
}
}
}
LEAN_EXPORT void l_Lean_isExport_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_325_ = stack[0].m_obj;
lean_object* v_n_326_ = stack[1].m_obj;
uint8_t v_res_331_;
v_res_331_ = l_Lean_isExport(v_env_325_, v_n_326_);
stack->m_num = v_res_331_;
}
LEAN_EXPORT lean_object* l_Lean_isExport___boxed(lean_object* v_env_332_, lean_object* v_n_333_){
_start:
{
uint8_t v_res_334_; lean_object* v_r_335_; 
v_res_334_ = l_Lean_isExport(v_env_332_, v_n_333_);
v_r_335_ = lean_box(v_res_334_);
return v_r_335_;
}
}
lean_object* runtime_initialize_Lean_Attributes(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_ExportAttr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Attributes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_exportAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_exportAttr);
lean_dec_ref(res);
res = l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_ExportAttr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Attributes(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_ExportAttr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Attributes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_ExportAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_ExportAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_ExportAttr(builtin);
}
#ifdef __cplusplus
}
#endif

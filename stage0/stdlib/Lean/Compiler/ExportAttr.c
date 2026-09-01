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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
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
static const lean_string_object l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Invalid `export` function name: `"};
static const lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "` is not a valid C++ identifier"};
static const lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "exportAttr"};
static const lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(105, 101, 238, 215, 35, 66, 156, 98)}};
static const lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "export"};
static const lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(191, 25, 157, 3, 50, 244, 45, 226)}};
static const lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__7_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "name to be used by code generators"};
static const lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__7_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__7_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__8_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__7_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__8_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__8_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__9_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__9_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__9_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 8, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__8_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__9_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exportAttr;
static const lean_string_object l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 742, .m_capacity = 742, .m_length = 741, .m_data = "Exports a function under the provided unmangled symbol name. This can be used to refer to Lean\nfunctions from other programming languages like C.\n\nExample:\n```\n@[export lean_color_from_map]\ndef colorValue (properties : @& Std.HashMap String String) : UInt32 :=\n  match properties[\"color\"]\? with\n  | some \"red\" => 0xff0000\n  | some \"green\" => 0x00ff00\n  | some \"blue\" => 0x0000ff\n  | _ => -1\n```\nC code:\n```c\n#include <lean/lean.h>\n\nuint32_t lean_color_from_map(b_lean_obj_arg properties);\n\nvoid fill_rectangle_from_map(b_lean_obj_arg properties) {\n    uint32_t color = lean_color_from_map(properties);\n    // ...\n}\n```\n\nThe opposite of this is `@[extern]`, which allows Lean functions to refer to functions from other\nprogramming languages.\n"};
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
uint32_t v___x_21_; uint8_t v___y_31_; uint32_t v___x_36_; uint8_t v___x_37_; 
v___x_21_ = lean_string_utf8_get_fast(v_str_6_, v___x_9_);
v___x_36_ = 65;
v___x_37_ = lean_uint32_dec_le(v___x_36_, v___x_21_);
if (v___x_37_ == 0)
{
v___y_31_ = v___x_37_;
goto v___jp_30_;
}
else
{
uint32_t v___x_38_; uint8_t v___x_39_; 
v___x_38_ = 90;
v___x_39_ = lean_uint32_dec_le(v___x_21_, v___x_38_);
v___y_31_ = v___x_39_;
goto v___jp_30_;
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
if (v___y_31_ == 0)
{
uint32_t v___x_32_; uint8_t v___x_33_; 
v___x_32_ = 97;
v___x_33_ = lean_uint32_dec_le(v___x_32_, v___x_21_);
if (v___x_33_ == 0)
{
goto v___jp_25_;
}
else
{
uint32_t v___x_34_; uint8_t v___x_35_; 
v___x_34_ = 122;
v___x_35_ = lean_uint32_dec_le(v___x_21_, v___x_34_);
if (v___x_35_ == 0)
{
goto v___jp_25_;
}
else
{
goto v___jp_10_;
}
}
}
else
{
goto v___jp_10_;
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
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId_spec__0___boxed(lean_object* v_s_40_, lean_object* v_pos_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId_spec__0(v_s_40_, v_pos_41_);
lean_dec_ref(v_s_40_);
return v_res_42_;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId___closed__3(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_46_ = ((lean_object*)(l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId___closed__2));
v___x_47_ = lean_unsigned_to_nat(14u);
v___x_48_ = lean_unsigned_to_nat(22u);
v___x_49_ = ((lean_object*)(l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId___closed__1));
v___x_50_ = ((lean_object*)(l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId___closed__0));
v___x_51_ = l_mkPanicMessageWithDecl(v___x_50_, v___x_49_, v___x_48_, v___x_47_, v___x_46_);
return v___x_51_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId(lean_object* v_id_52_){
_start:
{
lean_object* v___y_54_; lean_object* v_startInclusive_55_; lean_object* v_endExclusive_56_; lean_object* v___y_67_; lean_object* v___y_68_; uint8_t v___y_69_; uint8_t v___y_70_; uint32_t v___y_82_; uint8_t v___y_83_; uint32_t v___y_89_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_94_ = lean_unsigned_to_nat(0u);
v___x_95_ = lean_string_utf8_byte_size(v_id_52_);
lean_inc_ref(v_id_52_);
v___x_96_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_96_, 0, v_id_52_);
lean_ctor_set(v___x_96_, 1, v___x_94_);
lean_ctor_set(v___x_96_, 2, v___x_95_);
v___x_97_ = l_String_Slice_Pos_get_x3f(v___x_96_, v___x_94_);
lean_dec_ref_known(v___x_96_, 3);
if (lean_obj_tag(v___x_97_) == 0)
{
uint32_t v___x_98_; 
v___x_98_ = 65;
v___y_89_ = v___x_98_;
goto v___jp_88_;
}
else
{
lean_object* v_val_99_; uint32_t v___x_100_; 
v_val_99_ = lean_ctor_get(v___x_97_, 0);
lean_inc(v_val_99_);
lean_dec_ref_known(v___x_97_, 1);
v___x_100_ = lean_unbox_uint32(v_val_99_);
lean_dec(v_val_99_);
v___y_89_ = v___x_100_;
goto v___jp_88_;
}
v___jp_53_:
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; uint8_t v_decide_60_; 
v___x_57_ = lean_unsigned_to_nat(0u);
v___x_58_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId_spec__0(v___y_54_, v___x_57_);
lean_dec_ref(v___y_54_);
v___x_59_ = lean_nat_sub(v_endExclusive_56_, v_startInclusive_55_);
lean_dec(v_startInclusive_55_);
lean_dec(v_endExclusive_56_);
v_decide_60_ = lean_nat_dec_eq(v___x_58_, v___x_59_);
lean_dec(v___x_59_);
lean_dec(v___x_58_);
return v_decide_60_;
}
v___jp_61_:
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v_startInclusive_64_; lean_object* v_endExclusive_65_; 
v___x_62_ = lean_obj_once(&l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId___closed__3, &l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId___closed__3_once, _init_l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId___closed__3);
v___x_63_ = l_panic___at___00__private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId_spec__1(v___x_62_);
v_startInclusive_64_ = lean_ctor_get(v___x_63_, 1);
lean_inc(v_startInclusive_64_);
v_endExclusive_65_ = lean_ctor_get(v___x_63_, 2);
lean_inc(v_endExclusive_65_);
v___y_54_ = v___x_63_;
v_startInclusive_55_ = v_startInclusive_64_;
v_endExclusive_56_ = v_endExclusive_65_;
goto v___jp_53_;
}
v___jp_66_:
{
if (v___y_69_ == 0)
{
lean_dec(v___y_68_);
lean_dec(v___y_67_);
lean_dec_ref(v_id_52_);
goto v___jp_61_;
}
else
{
if (v___y_70_ == 0)
{
lean_dec(v___y_68_);
lean_dec(v___y_67_);
lean_dec_ref(v_id_52_);
goto v___jp_61_;
}
else
{
lean_object* v___x_71_; 
lean_inc(v___y_68_);
lean_inc(v___y_67_);
v___x_71_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_71_, 0, v_id_52_);
lean_ctor_set(v___x_71_, 1, v___y_67_);
lean_ctor_set(v___x_71_, 2, v___y_68_);
v___y_54_ = v___x_71_;
v_startInclusive_55_ = v___y_67_;
v_endExclusive_56_ = v___y_68_;
goto v___jp_53_;
}
}
}
v___jp_72_:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; uint8_t v___x_78_; uint8_t v___x_79_; 
v___x_73_ = lean_unsigned_to_nat(0u);
v___x_74_ = lean_string_utf8_byte_size(v_id_52_);
lean_inc_ref(v_id_52_);
v___x_75_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_75_, 0, v_id_52_);
lean_ctor_set(v___x_75_, 1, v___x_73_);
lean_ctor_set(v___x_75_, 2, v___x_74_);
v___x_76_ = lean_unsigned_to_nat(1u);
v___x_77_ = l_Substring_Raw_nextn(v___x_75_, v___x_76_, v___x_73_);
lean_dec_ref_known(v___x_75_, 3);
v___x_78_ = lean_string_is_valid_pos(v_id_52_, v___x_77_);
v___x_79_ = lean_string_is_valid_pos(v_id_52_, v___x_74_);
if (v___x_79_ == 0)
{
v___y_67_ = v___x_77_;
v___y_68_ = v___x_74_;
v___y_69_ = v___x_78_;
v___y_70_ = v___x_79_;
goto v___jp_66_;
}
else
{
uint8_t v___x_80_; 
v___x_80_ = lean_nat_dec_le(v___x_77_, v___x_74_);
v___y_67_ = v___x_77_;
v___y_68_ = v___x_74_;
v___y_69_ = v___x_78_;
v___y_70_ = v___x_80_;
goto v___jp_66_;
}
}
v___jp_81_:
{
if (v___y_83_ == 0)
{
uint32_t v___x_84_; uint8_t v___x_85_; 
v___x_84_ = 97;
v___x_85_ = lean_uint32_dec_le(v___x_84_, v___y_82_);
if (v___x_85_ == 0)
{
lean_dec_ref(v_id_52_);
return v___x_85_;
}
else
{
uint32_t v___x_86_; uint8_t v___x_87_; 
v___x_86_ = 122;
v___x_87_ = lean_uint32_dec_le(v___y_82_, v___x_86_);
if (v___x_87_ == 0)
{
lean_dec_ref(v_id_52_);
return v___x_87_;
}
else
{
goto v___jp_72_;
}
}
}
else
{
goto v___jp_72_;
}
}
v___jp_88_:
{
uint32_t v___x_90_; uint8_t v___x_91_; 
v___x_90_ = 65;
v___x_91_ = lean_uint32_dec_le(v___x_90_, v___y_89_);
if (v___x_91_ == 0)
{
v___y_82_ = v___y_89_;
v___y_83_ = v___x_91_;
goto v___jp_81_;
}
else
{
uint32_t v___x_92_; uint8_t v___x_93_; 
v___x_92_ = 90;
v___x_93_ = lean_uint32_dec_le(v___y_89_, v___x_92_);
v___y_82_ = v___y_89_;
v___y_83_ = v___x_93_;
goto v___jp_81_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId___boxed(lean_object* v_id_101_){
_start:
{
uint8_t v_res_102_; lean_object* v_r_103_; 
v_res_102_ = l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId(v_id_101_);
v_r_103_ = lean_box(v_res_102_);
return v_r_103_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppName(lean_object* v_x_104_){
_start:
{
if (lean_obj_tag(v_x_104_) == 1)
{
lean_object* v_pre_105_; 
v_pre_105_ = lean_ctor_get(v_x_104_, 0);
if (lean_obj_tag(v_pre_105_) == 0)
{
lean_object* v_str_106_; uint8_t v___x_107_; 
v_str_106_ = lean_ctor_get(v_x_104_, 1);
lean_inc_ref(v_str_106_);
lean_dec_ref_known(v_x_104_, 2);
v___x_107_ = l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId(v_str_106_);
return v___x_107_;
}
else
{
lean_object* v_str_108_; uint8_t v___x_109_; 
lean_inc(v_pre_105_);
v_str_108_ = lean_ctor_get(v_x_104_, 1);
lean_inc_ref(v_str_108_);
lean_dec_ref_known(v_x_104_, 2);
v___x_109_ = l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId(v_str_108_);
if (v___x_109_ == 0)
{
lean_dec(v_pre_105_);
return v___x_109_;
}
else
{
v_x_104_ = v_pre_105_;
goto _start;
}
}
}
else
{
uint8_t v___x_111_; 
lean_dec(v_x_104_);
v___x_111_ = 0;
return v___x_111_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppName___boxed(lean_object* v_x_112_){
_start:
{
uint8_t v_res_113_; lean_object* v_r_114_; 
v_res_113_ = l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppName(v_x_112_);
v_r_114_ = lean_box(v_res_113_);
return v_r_114_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_115_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_116_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_117_, 0, v___x_116_);
return v___x_117_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_118_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_119_ = lean_unsigned_to_nat(0u);
v___x_120_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_120_, 0, v___x_119_);
lean_ctor_set(v___x_120_, 1, v___x_119_);
lean_ctor_set(v___x_120_, 2, v___x_119_);
lean_ctor_set(v___x_120_, 3, v___x_119_);
lean_ctor_set(v___x_120_, 4, v___x_118_);
lean_ctor_set(v___x_120_, 5, v___x_118_);
lean_ctor_set(v___x_120_, 6, v___x_118_);
lean_ctor_set(v___x_120_, 7, v___x_118_);
lean_ctor_set(v___x_120_, 8, v___x_118_);
lean_ctor_set(v___x_120_, 9, v___x_118_);
lean_ctor_set(v___x_120_, 10, v___x_118_);
return v___x_120_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_121_ = lean_unsigned_to_nat(32u);
v___x_122_ = lean_mk_empty_array_with_capacity(v___x_121_);
v___x_123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_123_, 0, v___x_122_);
return v___x_123_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_124_ = ((size_t)5ULL);
v___x_125_ = lean_unsigned_to_nat(0u);
v___x_126_ = lean_unsigned_to_nat(32u);
v___x_127_ = lean_mk_empty_array_with_capacity(v___x_126_);
v___x_128_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_129_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_129_, 0, v___x_128_);
lean_ctor_set(v___x_129_, 1, v___x_127_);
lean_ctor_set(v___x_129_, 2, v___x_125_);
lean_ctor_set(v___x_129_, 3, v___x_125_);
lean_ctor_set_usize(v___x_129_, 4, v___x_124_);
return v___x_129_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_130_ = lean_box(1);
v___x_131_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_132_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_133_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_133_, 0, v___x_132_);
lean_ctor_set(v___x_133_, 1, v___x_131_);
lean_ctor_set(v___x_133_, 2, v___x_130_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_134_, lean_object* v___y_135_, lean_object* v___y_136_){
_start:
{
lean_object* v___x_138_; lean_object* v_env_139_; lean_object* v_options_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_138_ = lean_st_ref_get(v___y_136_);
v_env_139_ = lean_ctor_get(v___x_138_, 0);
lean_inc_ref(v_env_139_);
lean_dec(v___x_138_);
v_options_140_ = lean_ctor_get(v___y_135_, 1);
v___x_141_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_142_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__5);
lean_inc_ref(v_options_140_);
v___x_143_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_143_, 0, v_env_139_);
lean_ctor_set(v___x_143_, 1, v___x_141_);
lean_ctor_set(v___x_143_, 2, v___x_142_);
lean_ctor_set(v___x_143_, 3, v_options_140_);
v___x_144_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
lean_ctor_set(v___x_144_, 1, v_msgData_134_);
v___x_145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_145_, 0, v___x_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0(v_msgData_146_, v___y_147_, v___y_148_);
lean_dec(v___y_148_);
lean_dec_ref(v___y_147_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_151_, lean_object* v___y_152_, lean_object* v___y_153_){
_start:
{
lean_object* v_ref_155_; lean_object* v___x_156_; lean_object* v_a_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_165_; 
v_ref_155_ = lean_ctor_get(v___y_152_, 4);
v___x_156_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0(v_msg_151_, v___y_152_, v___y_153_);
v_a_157_ = lean_ctor_get(v___x_156_, 0);
v_isSharedCheck_165_ = !lean_is_exclusive(v___x_156_);
if (v_isSharedCheck_165_ == 0)
{
v___x_159_ = v___x_156_;
v_isShared_160_ = v_isSharedCheck_165_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_a_157_);
lean_dec(v___x_156_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_165_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
lean_object* v___x_161_; lean_object* v___x_163_; 
lean_inc(v_ref_155_);
v___x_161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_161_, 0, v_ref_155_);
lean_ctor_set(v___x_161_, 1, v_a_157_);
if (v_isShared_160_ == 0)
{
lean_ctor_set_tag(v___x_159_, 1);
lean_ctor_set(v___x_159_, 0, v___x_161_);
v___x_163_ = v___x_159_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v___x_161_);
v___x_163_ = v_reuseFailAlloc_164_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
return v___x_163_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0___redArg(v_msg_166_, v___y_167_, v___y_168_);
lean_dec(v___y_168_);
lean_dec_ref(v___y_167_);
return v_res_170_;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_172_ = ((lean_object*)(l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_));
v___x_173_ = l_Lean_stringToMessageData(v___x_172_);
return v___x_173_;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_175_ = ((lean_object*)(l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_));
v___x_176_ = l_Lean_stringToMessageData(v___x_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_(lean_object* v_x_177_, lean_object* v_stx_178_, lean_object* v___y_179_, lean_object* v___y_180_){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = l_Lean_Attribute_Builtin_getId(v_stx_178_, v___y_179_, v___y_180_);
if (lean_obj_tag(v___x_182_) == 0)
{
lean_object* v_a_183_; uint8_t v___x_184_; 
v_a_183_ = lean_ctor_get(v___x_182_, 0);
lean_inc_n(v_a_183_, 2);
v___x_184_ = l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppName(v_a_183_);
if (v___x_184_ == 0)
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v_a_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_198_; 
lean_dec_ref_known(v___x_182_, 1);
v___x_185_ = lean_obj_once(&l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_, &l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_);
v___x_186_ = l_Lean_MessageData_ofName(v_a_183_);
v___x_187_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_187_, 0, v___x_185_);
lean_ctor_set(v___x_187_, 1, v___x_186_);
v___x_188_ = lean_obj_once(&l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_, &l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_);
v___x_189_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_189_, 0, v___x_187_);
lean_ctor_set(v___x_189_, 1, v___x_188_);
v___x_190_ = l_Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0___redArg(v___x_189_, v___y_179_, v___y_180_);
v_a_191_ = lean_ctor_get(v___x_190_, 0);
v_isSharedCheck_198_ = !lean_is_exclusive(v___x_190_);
if (v_isSharedCheck_198_ == 0)
{
v___x_193_ = v___x_190_;
v_isShared_194_ = v_isSharedCheck_198_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_a_191_);
lean_dec(v___x_190_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_198_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
lean_object* v___x_196_; 
if (v_isShared_194_ == 0)
{
v___x_196_ = v___x_193_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v_a_191_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
return v___x_196_;
}
}
}
else
{
lean_dec(v_a_183_);
return v___x_182_;
}
}
else
{
return v___x_182_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2____boxed(lean_object* v_x_199_, lean_object* v_stx_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_(v_x_199_, v_stx_200_, v___y_201_, v___y_202_);
lean_dec(v___y_202_);
lean_dec_ref(v___y_201_);
lean_dec(v_x_199_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_(lean_object* v_x_205_, lean_object* v_x_206_, lean_object* v_x_207_, lean_object* v___y_208_){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_210_ = lean_box(0);
v___x_211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_211_, 0, v___x_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2____boxed(lean_object* v_x_212_, lean_object* v_x_213_, lean_object* v_x_214_, lean_object* v___y_215_, lean_object* v___y_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_(v_x_212_, v_x_213_, v_x_214_, v___y_215_);
lean_dec(v___y_215_);
lean_dec_ref(v_x_214_);
lean_dec(v_x_213_);
lean_dec(v_x_212_);
return v_res_217_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_(uint8_t v___x_218_, lean_object* v_env_219_, lean_object* v_n_220_, lean_object* v_x_221_){
_start:
{
uint8_t v___x_222_; 
v___x_222_ = l_Lean_Environment_contains(v_env_219_, v_n_220_, v___x_218_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2____boxed(lean_object* v___x_223_, lean_object* v_env_224_, lean_object* v_n_225_, lean_object* v_x_226_){
_start:
{
uint8_t v___x_1474__boxed_227_; uint8_t v_res_228_; lean_object* v_r_229_; 
v___x_1474__boxed_227_ = lean_unbox(v___x_223_);
v_res_228_ = l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_(v___x_1474__boxed_227_, v_env_224_, v_n_225_, v_x_226_);
lean_dec(v_x_226_);
v_r_229_ = lean_box(v_res_228_);
return v_r_229_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_256_ = ((lean_object*)(l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_));
v___x_257_ = l_Lean_registerParametricAttribute___redArg(v___x_256_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2____boxed(lean_object* v_a_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l___private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_();
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_260_, lean_object* v_msg_261_, lean_object* v___y_262_, lean_object* v___y_263_){
_start:
{
lean_object* v___x_265_; 
v___x_265_ = l_Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0___redArg(v_msg_261_, v___y_262_, v___y_263_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_266_, lean_object* v_msg_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0(v_00_u03b1_266_, v_msg_267_, v___y_268_, v___y_269_);
lean_dec(v___y_269_);
lean_dec_ref(v___y_268_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_docString__1(){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_274_ = ((lean_object*)(l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_));
v___x_275_ = ((lean_object*)(l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_docString__1___closed__0));
v___x_276_ = l_Lean_addBuiltinDocString(v___x_274_, v___x_275_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_docString__1___boxed(lean_object* v_a_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_docString__1();
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3(){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_305_ = ((lean_object*)(l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_));
v___x_306_ = ((lean_object*)(l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__6));
v___x_307_ = l_Lean_addBuiltinDeclarationRanges(v___x_305_, v___x_306_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___boxed(lean_object* v_a_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3();
return v_res_309_;
}
}
LEAN_EXPORT lean_object* lean_get_export_name_for(lean_object* v_env_310_, lean_object* v_n_311_){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_312_ = lean_box(0);
v___x_313_ = l_Lean_exportAttr;
v___x_314_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_312_, v___x_313_, v_env_310_, v_n_311_);
return v___x_314_;
}
}
LEAN_EXPORT uint8_t l_Lean_isExport(lean_object* v_env_318_, lean_object* v_n_319_){
_start:
{
lean_object* v___x_320_; 
lean_inc(v_n_319_);
v___x_320_ = lean_get_export_name_for(v_env_318_, v_n_319_);
if (lean_obj_tag(v___x_320_) == 0)
{
lean_object* v___x_321_; uint8_t v___x_322_; 
v___x_321_ = ((lean_object*)(l_Lean_isExport___closed__1));
v___x_322_ = lean_name_eq(v_n_319_, v___x_321_);
lean_dec(v_n_319_);
return v___x_322_;
}
else
{
uint8_t v___x_323_; 
lean_dec_ref_known(v___x_320_, 1);
lean_dec(v_n_319_);
v___x_323_ = 1;
return v___x_323_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isExport___boxed(lean_object* v_env_324_, lean_object* v_n_325_){
_start:
{
uint8_t v_res_326_; lean_object* v_r_327_; 
v_res_326_ = l_Lean_isExport(v_env_324_, v_n_325_);
v_r_327_ = lean_box(v_res_326_);
return v_r_327_;
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

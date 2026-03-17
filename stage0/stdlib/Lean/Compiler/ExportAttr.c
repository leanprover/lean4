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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Attribute_Builtin_getId(lean_object*, lean_object*, lean_object*);
extern lean_object* l_String_instInhabitedSlice;
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Substring_Raw_nextn(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_is_valid_pos(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_registerParametricAttribute___redArg(lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId_spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00__private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00__private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId_spec__0___boxed(lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_initFn___lam__0___closed__0_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Invalid `export` function name: `"};
static const lean_object* l_Lean_initFn___lam__0___closed__0_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___lam__0___closed__0_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value;
static lean_once_cell_t l_Lean_initFn___lam__0___closed__1_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_initFn___lam__0___closed__1_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_;
static const lean_string_object l_Lean_initFn___lam__0___closed__2_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "` is not a valid C++ identifier"};
static const lean_object* l_Lean_initFn___lam__0___closed__2_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___lam__0___closed__2_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value;
static lean_once_cell_t l_Lean_initFn___lam__0___closed__3_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_initFn___lam__0___closed__3_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_initFn___lam__2_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__2_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_initFn___closed__0_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__0_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__0_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_initFn___closed__1_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__1_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__1_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_initFn___closed__2_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_initFn___closed__2_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_initFn___closed__3_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "exportAttr"};
static const lean_object* l_Lean_initFn___closed__3_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(105, 101, 238, 215, 35, 66, 156, 98)}};
static const lean_object* l_Lean_initFn___closed__4_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_initFn___closed__5_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "export"};
static const lean_object* l_Lean_initFn___closed__5_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_initFn___closed__6_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(191, 25, 157, 3, 50, 244, 45, 226)}};
static const lean_object* l_Lean_initFn___closed__6_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__6_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_initFn___closed__7_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "name to be used by code generators"};
static const lean_object* l_Lean_initFn___closed__7_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__7_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_initFn___closed__8_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__6_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__7_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_initFn___closed__8_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__8_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_initFn___closed__9_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__2_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_initFn___closed__9_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__9_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_initFn___closed__10_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 8, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__8_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__9_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_initFn___closed__10_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__10_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exportAttr;
static const lean_string_object l_Lean_exportAttr___regBuiltin_Lean_exportAttr_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 742, .m_capacity = 742, .m_length = 741, .m_data = "Exports a function under the provided unmangled symbol name. This can be used to refer to Lean\nfunctions from other programming languages like C.\n\nExample:\n```\n@[export lean_color_from_map]\ndef colorValue (properties : @& Std.HashMap String String) : UInt32 :=\n  match properties[\"color\"]\? with\n  | some \"red\" => 0xff0000\n  | some \"green\" => 0x00ff00\n  | some \"blue\" => 0x0000ff\n  | _ => -1\n```\nC code:\n```c\n#include <lean/lean.h>\n\nuint32_t lean_color_from_map(b_lean_obj_arg properties);\n\nvoid fill_rectangle_from_map(b_lean_obj_arg properties) {\n    uint32_t color = lean_color_from_map(properties);\n    // ...\n}\n```\n\nThe opposite of this is `@[extern]`, which allows Lean functions to refer to functions from other\nprogramming languages.\n"};
static const lean_object* l_Lean_exportAttr___regBuiltin_Lean_exportAttr_docString__1___closed__0 = (const lean_object*)&l_Lean_exportAttr___regBuiltin_Lean_exportAttr_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_exportAttr___regBuiltin_Lean_exportAttr_docString__1();
LEAN_EXPORT lean_object* l_Lean_exportAttr___regBuiltin_Lean_exportAttr_docString__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(24) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__0 = (const lean_object*)&l_Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(63) << 1) | 1)),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l_Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__1 = (const lean_object*)&l_Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__1_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l_Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__2 = (const lean_object*)&l_Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(54) << 1) | 1)),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l_Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__3 = (const lean_object*)&l_Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(54) << 1) | 1)),((lean_object*)(((size_t)(29) << 1) | 1))}};
static const lean_object* l_Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__4 = (const lean_object*)&l_Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__3_value),((lean_object*)(((size_t)(19) << 1) | 1)),((lean_object*)&l_Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__4_value),((lean_object*)(((size_t)(29) << 1) | 1))}};
static const lean_object* l_Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__5 = (const lean_object*)&l_Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__2_value),((lean_object*)&l_Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__6 = (const lean_object*)&l_Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3();
LEAN_EXPORT lean_object* l_Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___boxed(lean_object*);
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
v___x_3_ = lean_panic_fn(v___x_2_, v_msg_1_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00__private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId_spec__0(lean_object* v_s_4_, lean_object* v_curr_5_){
_start:
{
lean_object* v_str_6_; lean_object* v_startInclusive_7_; lean_object* v_endExclusive_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_17_; lean_object* v___x_18_; uint8_t v___x_19_; 
v_str_6_ = lean_ctor_get(v_s_4_, 0);
v_startInclusive_7_ = lean_ctor_get(v_s_4_, 1);
v_endExclusive_8_ = lean_ctor_get(v_s_4_, 2);
v___x_9_ = lean_nat_add(v_startInclusive_7_, v_curr_5_);
lean_inc(v_endExclusive_8_);
lean_inc(v___x_9_);
lean_inc_ref(v_str_6_);
v___x_10_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_10_, 0, v_str_6_);
lean_ctor_set(v___x_10_, 1, v___x_9_);
lean_ctor_set(v___x_10_, 2, v_endExclusive_8_);
v___x_17_ = lean_unsigned_to_nat(0u);
v___x_18_ = lean_nat_sub(v_endExclusive_8_, v___x_9_);
v___x_19_ = lean_nat_dec_eq(v___x_17_, v___x_18_);
lean_dec(v___x_18_);
if (v___x_19_ == 0)
{
uint32_t v___x_20_; uint8_t v___y_22_; uint8_t v___y_26_; uint32_t v___x_36_; uint8_t v___x_37_; 
v___x_20_ = lean_string_utf8_get_fast(v_str_6_, v___x_9_);
v___x_36_ = 65;
v___x_37_ = lean_uint32_dec_le(v___x_36_, v___x_20_);
if (v___x_37_ == 0)
{
goto v___jp_31_;
}
else
{
uint32_t v___x_38_; uint8_t v___x_39_; 
v___x_38_ = 90;
v___x_39_ = lean_uint32_dec_le(v___x_20_, v___x_38_);
if (v___x_39_ == 0)
{
goto v___jp_31_;
}
else
{
goto v___jp_11_;
}
}
v___jp_21_:
{
if (v___y_22_ == 0)
{
uint32_t v___x_23_; uint8_t v___x_24_; 
v___x_23_ = 95;
v___x_24_ = lean_uint32_dec_eq(v___x_20_, v___x_23_);
if (v___x_24_ == 0)
{
lean_dec(v___x_9_);
lean_dec(v_curr_5_);
return v___x_10_;
}
else
{
goto v___jp_11_;
}
}
else
{
goto v___jp_11_;
}
}
v___jp_25_:
{
if (v___y_26_ == 0)
{
uint32_t v___x_27_; uint8_t v___x_28_; 
v___x_27_ = 48;
v___x_28_ = lean_uint32_dec_le(v___x_27_, v___x_20_);
if (v___x_28_ == 0)
{
v___y_22_ = v___x_28_;
goto v___jp_21_;
}
else
{
uint32_t v___x_29_; uint8_t v___x_30_; 
v___x_29_ = 57;
v___x_30_ = lean_uint32_dec_le(v___x_20_, v___x_29_);
v___y_22_ = v___x_30_;
goto v___jp_21_;
}
}
else
{
goto v___jp_11_;
}
}
v___jp_31_:
{
uint32_t v___x_32_; uint8_t v___x_33_; 
v___x_32_ = 97;
v___x_33_ = lean_uint32_dec_le(v___x_32_, v___x_20_);
if (v___x_33_ == 0)
{
v___y_26_ = v___x_33_;
goto v___jp_25_;
}
else
{
uint32_t v___x_34_; uint8_t v___x_35_; 
v___x_34_ = 122;
v___x_35_ = lean_uint32_dec_le(v___x_20_, v___x_34_);
v___y_26_ = v___x_35_;
goto v___jp_25_;
}
}
}
else
{
lean_dec(v___x_9_);
lean_dec(v_curr_5_);
return v___x_10_;
}
v___jp_11_:
{
lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; uint8_t v___x_15_; 
v___x_12_ = lean_string_utf8_next_fast(v_str_6_, v___x_9_);
v___x_13_ = lean_nat_sub(v___x_12_, v___x_9_);
lean_dec(v___x_9_);
v___x_14_ = lean_nat_add(v_curr_5_, v___x_13_);
lean_dec(v___x_13_);
v___x_15_ = lean_nat_dec_lt(v_curr_5_, v___x_14_);
lean_dec(v_curr_5_);
if (v___x_15_ == 0)
{
lean_dec(v___x_14_);
return v___x_10_;
}
else
{
lean_dec_ref(v___x_10_);
v_curr_5_ = v___x_14_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00__private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId_spec__0___boxed(lean_object* v_s_40_, lean_object* v_curr_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00__private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId_spec__0(v_s_40_, v_curr_41_);
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
lean_object* v___y_54_; uint8_t v___y_75_; uint32_t v___y_77_; uint32_t v___y_83_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_88_ = lean_unsigned_to_nat(0u);
v___x_89_ = lean_string_utf8_byte_size(v_id_52_);
lean_inc_ref(v_id_52_);
v___x_90_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_90_, 0, v_id_52_);
lean_ctor_set(v___x_90_, 1, v___x_88_);
lean_ctor_set(v___x_90_, 2, v___x_89_);
v___x_91_ = l_String_Slice_Pos_get_x3f(v___x_90_, v___x_88_);
lean_dec_ref(v___x_90_);
if (lean_obj_tag(v___x_91_) == 0)
{
uint32_t v___x_92_; 
v___x_92_ = 65;
v___y_83_ = v___x_92_;
goto v___jp_82_;
}
else
{
lean_object* v_val_93_; uint32_t v___x_94_; 
v_val_93_ = lean_ctor_get(v___x_91_, 0);
lean_inc(v_val_93_);
lean_dec_ref(v___x_91_);
v___x_94_ = lean_unbox_uint32(v_val_93_);
lean_dec(v_val_93_);
v___y_83_ = v___x_94_;
goto v___jp_82_;
}
v___jp_53_:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v_startInclusive_57_; lean_object* v_endExclusive_58_; lean_object* v___x_59_; uint8_t v___x_60_; 
v___x_55_ = lean_unsigned_to_nat(0u);
v___x_56_ = l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00__private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId_spec__0(v___y_54_, v___x_55_);
lean_dec_ref(v___y_54_);
v_startInclusive_57_ = lean_ctor_get(v___x_56_, 1);
lean_inc(v_startInclusive_57_);
v_endExclusive_58_ = lean_ctor_get(v___x_56_, 2);
lean_inc(v_endExclusive_58_);
lean_dec_ref(v___x_56_);
v___x_59_ = lean_nat_sub(v_endExclusive_58_, v_startInclusive_57_);
lean_dec(v_startInclusive_57_);
lean_dec(v_endExclusive_58_);
v___x_60_ = lean_nat_dec_eq(v___x_59_, v___x_55_);
lean_dec(v___x_59_);
return v___x_60_;
}
v___jp_61_:
{
lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_62_ = lean_obj_once(&l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId___closed__3, &l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId___closed__3_once, _init_l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId___closed__3);
v___x_63_ = l_panic___at___00__private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId_spec__1(v___x_62_);
v___y_54_ = v___x_63_;
goto v___jp_53_;
}
v___jp_64_:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; uint8_t v___x_70_; 
v___x_65_ = lean_unsigned_to_nat(0u);
v___x_66_ = lean_string_utf8_byte_size(v_id_52_);
lean_inc_ref(v_id_52_);
v___x_67_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_67_, 0, v_id_52_);
lean_ctor_set(v___x_67_, 1, v___x_65_);
lean_ctor_set(v___x_67_, 2, v___x_66_);
v___x_68_ = lean_unsigned_to_nat(1u);
v___x_69_ = l_Substring_Raw_nextn(v___x_67_, v___x_68_, v___x_65_);
lean_dec_ref(v___x_67_);
v___x_70_ = lean_string_is_valid_pos(v_id_52_, v___x_69_);
if (v___x_70_ == 0)
{
lean_dec(v___x_69_);
lean_dec_ref(v_id_52_);
goto v___jp_61_;
}
else
{
uint8_t v___x_71_; 
v___x_71_ = lean_string_is_valid_pos(v_id_52_, v___x_66_);
if (v___x_71_ == 0)
{
lean_dec(v___x_69_);
lean_dec_ref(v_id_52_);
goto v___jp_61_;
}
else
{
uint8_t v___x_72_; 
v___x_72_ = lean_nat_dec_le(v___x_69_, v___x_66_);
if (v___x_72_ == 0)
{
lean_dec(v___x_69_);
lean_dec_ref(v_id_52_);
goto v___jp_61_;
}
else
{
lean_object* v___x_73_; 
v___x_73_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_73_, 0, v_id_52_);
lean_ctor_set(v___x_73_, 1, v___x_69_);
lean_ctor_set(v___x_73_, 2, v___x_66_);
v___y_54_ = v___x_73_;
goto v___jp_53_;
}
}
}
}
v___jp_74_:
{
if (v___y_75_ == 0)
{
lean_dec_ref(v_id_52_);
return v___y_75_;
}
else
{
goto v___jp_64_;
}
}
v___jp_76_:
{
uint32_t v___x_78_; uint8_t v___x_79_; 
v___x_78_ = 97;
v___x_79_ = lean_uint32_dec_le(v___x_78_, v___y_77_);
if (v___x_79_ == 0)
{
v___y_75_ = v___x_79_;
goto v___jp_74_;
}
else
{
uint32_t v___x_80_; uint8_t v___x_81_; 
v___x_80_ = 122;
v___x_81_ = lean_uint32_dec_le(v___y_77_, v___x_80_);
v___y_75_ = v___x_81_;
goto v___jp_74_;
}
}
v___jp_82_:
{
uint32_t v___x_84_; uint8_t v___x_85_; 
v___x_84_ = 65;
v___x_85_ = lean_uint32_dec_le(v___x_84_, v___y_83_);
if (v___x_85_ == 0)
{
v___y_77_ = v___y_83_;
goto v___jp_76_;
}
else
{
uint32_t v___x_86_; uint8_t v___x_87_; 
v___x_86_ = 90;
v___x_87_ = lean_uint32_dec_le(v___y_83_, v___x_86_);
if (v___x_87_ == 0)
{
v___y_77_ = v___y_83_;
goto v___jp_76_;
}
else
{
goto v___jp_64_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId___boxed(lean_object* v_id_95_){
_start:
{
uint8_t v_res_96_; lean_object* v_r_97_; 
v_res_96_ = l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId(v_id_95_);
v_r_97_ = lean_box(v_res_96_);
return v_r_97_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppName(lean_object* v_x_98_){
_start:
{
if (lean_obj_tag(v_x_98_) == 1)
{
lean_object* v_pre_99_; 
v_pre_99_ = lean_ctor_get(v_x_98_, 0);
if (lean_obj_tag(v_pre_99_) == 0)
{
lean_object* v_str_100_; uint8_t v___x_101_; 
v_str_100_ = lean_ctor_get(v_x_98_, 1);
lean_inc_ref(v_str_100_);
lean_dec_ref(v_x_98_);
v___x_101_ = l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId(v_str_100_);
return v___x_101_;
}
else
{
lean_object* v_str_102_; uint8_t v___x_103_; 
lean_inc(v_pre_99_);
v_str_102_ = lean_ctor_get(v_x_98_, 1);
lean_inc_ref(v_str_102_);
lean_dec_ref(v_x_98_);
v___x_103_ = l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId(v_str_102_);
if (v___x_103_ == 0)
{
lean_dec(v_pre_99_);
return v___x_103_;
}
else
{
v_x_98_ = v_pre_99_;
goto _start;
}
}
}
else
{
uint8_t v___x_105_; 
lean_dec(v_x_98_);
v___x_105_ = 0;
return v___x_105_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppName___boxed(lean_object* v_x_106_){
_start:
{
uint8_t v_res_107_; lean_object* v_r_108_; 
v_res_107_ = l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppName(v_x_106_);
v_r_108_ = lean_box(v_res_107_);
return v_r_108_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_109_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_110_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_111_, 0, v___x_110_);
return v___x_111_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_112_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_113_ = lean_unsigned_to_nat(0u);
v___x_114_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
lean_ctor_set(v___x_114_, 1, v___x_113_);
lean_ctor_set(v___x_114_, 2, v___x_113_);
lean_ctor_set(v___x_114_, 3, v___x_112_);
lean_ctor_set(v___x_114_, 4, v___x_112_);
lean_ctor_set(v___x_114_, 5, v___x_112_);
lean_ctor_set(v___x_114_, 6, v___x_112_);
lean_ctor_set(v___x_114_, 7, v___x_112_);
lean_ctor_set(v___x_114_, 8, v___x_112_);
return v___x_114_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_115_ = lean_unsigned_to_nat(32u);
v___x_116_ = lean_mk_empty_array_with_capacity(v___x_115_);
v___x_117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_117_, 0, v___x_116_);
return v___x_117_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_118_ = ((size_t)5ULL);
v___x_119_ = lean_unsigned_to_nat(0u);
v___x_120_ = lean_unsigned_to_nat(32u);
v___x_121_ = lean_mk_empty_array_with_capacity(v___x_120_);
v___x_122_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_123_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_123_, 0, v___x_122_);
lean_ctor_set(v___x_123_, 1, v___x_121_);
lean_ctor_set(v___x_123_, 2, v___x_119_);
lean_ctor_set(v___x_123_, 3, v___x_119_);
lean_ctor_set_usize(v___x_123_, 4, v___x_118_);
return v___x_123_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_124_ = lean_box(1);
v___x_125_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_126_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_127_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_127_, 0, v___x_126_);
lean_ctor_set(v___x_127_, 1, v___x_125_);
lean_ctor_set(v___x_127_, 2, v___x_124_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_128_, lean_object* v___y_129_, lean_object* v___y_130_){
_start:
{
lean_object* v___x_132_; lean_object* v_env_133_; lean_object* v_options_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_132_ = lean_st_ref_get(v___y_130_);
v_env_133_ = lean_ctor_get(v___x_132_, 0);
lean_inc_ref(v_env_133_);
lean_dec(v___x_132_);
v_options_134_ = lean_ctor_get(v___y_129_, 2);
v___x_135_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_136_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__5);
lean_inc_ref(v_options_134_);
v___x_137_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_137_, 0, v_env_133_);
lean_ctor_set(v___x_137_, 1, v___x_135_);
lean_ctor_set(v___x_137_, 2, v___x_136_);
lean_ctor_set(v___x_137_, 3, v_options_134_);
v___x_138_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_138_, 0, v___x_137_);
lean_ctor_set(v___x_138_, 1, v_msgData_128_);
v___x_139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_139_, 0, v___x_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0(v_msgData_140_, v___y_141_, v___y_142_);
lean_dec(v___y_142_);
lean_dec_ref(v___y_141_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_145_, lean_object* v___y_146_, lean_object* v___y_147_){
_start:
{
lean_object* v_ref_149_; lean_object* v___x_150_; lean_object* v_a_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_159_; 
v_ref_149_ = lean_ctor_get(v___y_146_, 5);
v___x_150_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0(v_msg_145_, v___y_146_, v___y_147_);
v_a_151_ = lean_ctor_get(v___x_150_, 0);
v_isSharedCheck_159_ = !lean_is_exclusive(v___x_150_);
if (v_isSharedCheck_159_ == 0)
{
v___x_153_ = v___x_150_;
v_isShared_154_ = v_isSharedCheck_159_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_a_151_);
lean_dec(v___x_150_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_159_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_155_; lean_object* v___x_157_; 
lean_inc(v_ref_149_);
v___x_155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_155_, 0, v_ref_149_);
lean_ctor_set(v___x_155_, 1, v_a_151_);
if (v_isShared_154_ == 0)
{
lean_ctor_set_tag(v___x_153_, 1);
lean_ctor_set(v___x_153_, 0, v___x_155_);
v___x_157_ = v___x_153_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v___x_155_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
return v___x_157_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_Lean_throwError___at___00Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0___redArg(v_msg_160_, v___y_161_, v___y_162_);
lean_dec(v___y_162_);
lean_dec_ref(v___y_161_);
return v_res_164_;
}
}
static lean_object* _init_l_Lean_initFn___lam__0___closed__1_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_166_ = ((lean_object*)(l_Lean_initFn___lam__0___closed__0_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_));
v___x_167_ = l_Lean_stringToMessageData(v___x_166_);
return v___x_167_;
}
}
static lean_object* _init_l_Lean_initFn___lam__0___closed__3_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_169_ = ((lean_object*)(l_Lean_initFn___lam__0___closed__2_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_));
v___x_170_ = l_Lean_stringToMessageData(v___x_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_(lean_object* v_x_171_, lean_object* v_stx_172_, lean_object* v___y_173_, lean_object* v___y_174_){
_start:
{
lean_object* v___x_176_; 
lean_inc_ref(v___y_173_);
v___x_176_ = l_Lean_Attribute_Builtin_getId(v_stx_172_, v___y_173_, v___y_174_);
if (lean_obj_tag(v___x_176_) == 0)
{
lean_object* v_a_177_; uint8_t v___x_178_; 
v_a_177_ = lean_ctor_get(v___x_176_, 0);
lean_inc(v_a_177_);
lean_inc(v_a_177_);
v___x_178_ = l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppName(v_a_177_);
if (v___x_178_ == 0)
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v_a_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_192_; 
lean_dec_ref(v___x_176_);
v___x_179_ = lean_obj_once(&l_Lean_initFn___lam__0___closed__1_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_, &l_Lean_initFn___lam__0___closed__1_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__once, _init_l_Lean_initFn___lam__0___closed__1_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_);
v___x_180_ = l_Lean_MessageData_ofName(v_a_177_);
v___x_181_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_181_, 0, v___x_179_);
lean_ctor_set(v___x_181_, 1, v___x_180_);
v___x_182_ = lean_obj_once(&l_Lean_initFn___lam__0___closed__3_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_, &l_Lean_initFn___lam__0___closed__3_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__once, _init_l_Lean_initFn___lam__0___closed__3_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_);
v___x_183_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_183_, 0, v___x_181_);
lean_ctor_set(v___x_183_, 1, v___x_182_);
v___x_184_ = l_Lean_throwError___at___00Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0___redArg(v___x_183_, v___y_173_, v___y_174_);
lean_dec_ref(v___y_173_);
v_a_185_ = lean_ctor_get(v___x_184_, 0);
v_isSharedCheck_192_ = !lean_is_exclusive(v___x_184_);
if (v_isSharedCheck_192_ == 0)
{
v___x_187_ = v___x_184_;
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_a_185_);
lean_dec(v___x_184_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_190_; 
if (v_isShared_188_ == 0)
{
v___x_190_ = v___x_187_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v_a_185_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
}
else
{
lean_dec(v_a_177_);
lean_dec_ref(v___y_173_);
return v___x_176_;
}
}
else
{
lean_dec_ref(v___y_173_);
return v___x_176_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2____boxed(lean_object* v_x_193_, lean_object* v_stx_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_Lean_initFn___lam__0_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_(v_x_193_, v_stx_194_, v___y_195_, v___y_196_);
lean_dec(v___y_196_);
lean_dec(v_x_193_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_(lean_object* v_x_199_, lean_object* v_x_200_, lean_object* v_x_201_, lean_object* v___y_202_){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_204_ = lean_box(0);
v___x_205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_205_, 0, v___x_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2____boxed(lean_object* v_x_206_, lean_object* v_x_207_, lean_object* v_x_208_, lean_object* v___y_209_, lean_object* v___y_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_Lean_initFn___lam__1_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_(v_x_206_, v_x_207_, v_x_208_, v___y_209_);
lean_dec(v___y_209_);
lean_dec_ref(v_x_208_);
lean_dec(v_x_207_);
lean_dec(v_x_206_);
return v_res_211_;
}
}
LEAN_EXPORT uint8_t l_Lean_initFn___lam__2_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_(uint8_t v___x_212_, lean_object* v_env_213_, lean_object* v_n_214_, lean_object* v_x_215_){
_start:
{
uint8_t v___x_216_; 
v___x_216_ = l_Lean_Environment_contains(v_env_213_, v_n_214_, v___x_212_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__2_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2____boxed(lean_object* v___x_217_, lean_object* v_env_218_, lean_object* v_n_219_, lean_object* v_x_220_){
_start:
{
uint8_t v___x_1739__boxed_221_; uint8_t v_res_222_; lean_object* v_r_223_; 
v___x_1739__boxed_221_ = lean_unbox(v___x_217_);
v_res_222_ = l_Lean_initFn___lam__2_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_(v___x_1739__boxed_221_, v_env_218_, v_n_219_, v_x_220_);
lean_dec(v_x_220_);
v_r_223_ = lean_box(v_res_222_);
return v_r_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_250_ = ((lean_object*)(l_Lean_initFn___closed__10_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_));
v___x_251_ = l_Lean_registerParametricAttribute___redArg(v___x_250_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2____boxed(lean_object* v_a_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_();
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_254_, lean_object* v_msg_255_, lean_object* v___y_256_, lean_object* v___y_257_){
_start:
{
lean_object* v___x_259_; 
v___x_259_ = l_Lean_throwError___at___00Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0___redArg(v_msg_255_, v___y_256_, v___y_257_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_260_, lean_object* v_msg_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_Lean_throwError___at___00Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0(v_00_u03b1_260_, v_msg_261_, v___y_262_, v___y_263_);
lean_dec(v___y_263_);
lean_dec_ref(v___y_262_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_exportAttr___regBuiltin_Lean_exportAttr_docString__1(){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_268_ = ((lean_object*)(l_Lean_initFn___closed__4_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_));
v___x_269_ = ((lean_object*)(l_Lean_exportAttr___regBuiltin_Lean_exportAttr_docString__1___closed__0));
v___x_270_ = l_Lean_addBuiltinDocString(v___x_268_, v___x_269_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_exportAttr___regBuiltin_Lean_exportAttr_docString__1___boxed(lean_object* v_a_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Lean_exportAttr___regBuiltin_Lean_exportAttr_docString__1();
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3(){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_299_ = ((lean_object*)(l_Lean_initFn___closed__4_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_));
v___x_300_ = ((lean_object*)(l_Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__6));
v___x_301_ = l_Lean_addBuiltinDeclarationRanges(v___x_299_, v___x_300_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___boxed(lean_object* v_a_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3();
return v_res_303_;
}
}
LEAN_EXPORT lean_object* lean_get_export_name_for(lean_object* v_env_304_, lean_object* v_n_305_){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_306_ = lean_box(0);
v___x_307_ = l_Lean_exportAttr;
v___x_308_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_306_, v___x_307_, v_env_304_, v_n_305_);
return v___x_308_;
}
}
LEAN_EXPORT uint8_t l_Lean_isExport(lean_object* v_env_312_, lean_object* v_n_313_){
_start:
{
lean_object* v___x_314_; 
lean_inc(v_n_313_);
v___x_314_ = lean_get_export_name_for(v_env_312_, v_n_313_);
if (lean_obj_tag(v___x_314_) == 0)
{
lean_object* v___x_315_; uint8_t v___x_316_; 
v___x_315_ = ((lean_object*)(l_Lean_isExport___closed__1));
v___x_316_ = lean_name_eq(v_n_313_, v___x_315_);
lean_dec(v_n_313_);
return v___x_316_;
}
else
{
uint8_t v___x_317_; 
lean_dec_ref(v___x_314_);
lean_dec(v_n_313_);
v___x_317_ = 1;
return v___x_317_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isExport___boxed(lean_object* v_env_318_, lean_object* v_n_319_){
_start:
{
uint8_t v_res_320_; lean_object* v_r_321_; 
v_res_320_ = l_Lean_isExport(v_env_318_, v_n_319_);
v_r_321_ = lean_box(v_res_320_);
return v_r_321_;
}
}
lean_object* runtime_initialize_Lean_Attributes(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_ExportAttr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Attributes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_exportAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_exportAttr);
lean_dec_ref(res);
res = l_Lean_exportAttr___regBuiltin_Lean_exportAttr_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3();
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

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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
LEAN_EXPORT uint8_t l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId(lean_object* v_id_51_){
_start:
{
lean_object* v___y_53_; lean_object* v_startInclusive_54_; lean_object* v_endExclusive_55_; uint32_t v___y_76_; uint32_t v___y_82_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_87_ = lean_unsigned_to_nat(0u);
v___x_88_ = lean_string_utf8_byte_size(v_id_51_);
lean_inc_ref(v_id_51_);
v___x_89_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_89_, 0, v_id_51_);
lean_ctor_set(v___x_89_, 1, v___x_87_);
lean_ctor_set(v___x_89_, 2, v___x_88_);
v___x_90_ = l_String_Slice_Pos_get_x3f(v___x_89_, v___x_87_);
lean_dec_ref_known(v___x_89_, 3);
if (lean_obj_tag(v___x_90_) == 0)
{
uint32_t v___x_91_; 
v___x_91_ = 65;
v___y_82_ = v___x_91_;
goto v___jp_81_;
}
else
{
lean_object* v_val_92_; uint32_t v___x_93_; 
v_val_92_ = lean_ctor_get(v___x_90_, 0);
lean_inc(v_val_92_);
lean_dec_ref_known(v___x_90_, 1);
v___x_93_ = lean_unbox_uint32(v_val_92_);
lean_dec(v_val_92_);
v___y_82_ = v___x_93_;
goto v___jp_81_;
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
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v_startInclusive_63_; lean_object* v_endExclusive_64_; 
v___x_61_ = lean_obj_once(&l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId___closed__3, &l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId___closed__3_once, _init_l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId___closed__3);
v___x_62_ = l_panic___at___00__private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId_spec__1(v___x_61_);
v_startInclusive_63_ = lean_ctor_get(v___x_62_, 1);
lean_inc(v_startInclusive_63_);
v_endExclusive_64_ = lean_ctor_get(v___x_62_, 2);
lean_inc(v_endExclusive_64_);
v___y_53_ = v___x_62_;
v_startInclusive_54_ = v_startInclusive_63_;
v_endExclusive_55_ = v_endExclusive_64_;
goto v___jp_52_;
}
v___jp_65_:
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; uint8_t v___x_71_; 
v___x_66_ = lean_unsigned_to_nat(0u);
v___x_67_ = lean_string_utf8_byte_size(v_id_51_);
lean_inc_ref(v_id_51_);
v___x_68_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_68_, 0, v_id_51_);
lean_ctor_set(v___x_68_, 1, v___x_66_);
lean_ctor_set(v___x_68_, 2, v___x_67_);
v___x_69_ = lean_unsigned_to_nat(1u);
v___x_70_ = l_Substring_Raw_nextn(v___x_68_, v___x_69_, v___x_66_);
lean_dec_ref_known(v___x_68_, 3);
v___x_71_ = lean_string_is_valid_pos(v_id_51_, v___x_70_);
if (v___x_71_ == 0)
{
lean_dec(v___x_70_);
lean_dec_ref(v_id_51_);
goto v___jp_60_;
}
else
{
uint8_t v___x_72_; 
v___x_72_ = lean_string_is_valid_pos(v_id_51_, v___x_67_);
if (v___x_72_ == 0)
{
lean_dec(v___x_70_);
lean_dec_ref(v_id_51_);
goto v___jp_60_;
}
else
{
uint8_t v___x_73_; 
v___x_73_ = lean_nat_dec_le(v___x_70_, v___x_67_);
if (v___x_73_ == 0)
{
lean_dec(v___x_70_);
lean_dec_ref(v_id_51_);
goto v___jp_60_;
}
else
{
lean_object* v___x_74_; 
lean_inc(v___x_70_);
v___x_74_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_74_, 0, v_id_51_);
lean_ctor_set(v___x_74_, 1, v___x_70_);
lean_ctor_set(v___x_74_, 2, v___x_67_);
v___y_53_ = v___x_74_;
v_startInclusive_54_ = v___x_70_;
v_endExclusive_55_ = v___x_67_;
goto v___jp_52_;
}
}
}
}
v___jp_75_:
{
uint32_t v___x_77_; uint8_t v___x_78_; 
v___x_77_ = 97;
v___x_78_ = lean_uint32_dec_le(v___x_77_, v___y_76_);
if (v___x_78_ == 0)
{
lean_dec_ref(v_id_51_);
return v___x_78_;
}
else
{
uint32_t v___x_79_; uint8_t v___x_80_; 
v___x_79_ = 122;
v___x_80_ = lean_uint32_dec_le(v___y_76_, v___x_79_);
if (v___x_80_ == 0)
{
lean_dec_ref(v_id_51_);
return v___x_80_;
}
else
{
goto v___jp_65_;
}
}
}
v___jp_81_:
{
uint32_t v___x_83_; uint8_t v___x_84_; 
v___x_83_ = 65;
v___x_84_ = lean_uint32_dec_le(v___x_83_, v___y_82_);
if (v___x_84_ == 0)
{
v___y_76_ = v___y_82_;
goto v___jp_75_;
}
else
{
uint32_t v___x_85_; uint8_t v___x_86_; 
v___x_85_ = 90;
v___x_86_ = lean_uint32_dec_le(v___y_82_, v___x_85_);
if (v___x_86_ == 0)
{
v___y_76_ = v___y_82_;
goto v___jp_75_;
}
else
{
goto v___jp_65_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId___boxed(lean_object* v_id_94_){
_start:
{
uint8_t v_res_95_; lean_object* v_r_96_; 
v_res_95_ = l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId(v_id_94_);
v_r_96_ = lean_box(v_res_95_);
return v_r_96_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppName(lean_object* v_x_97_){
_start:
{
if (lean_obj_tag(v_x_97_) == 1)
{
lean_object* v_pre_98_; 
v_pre_98_ = lean_ctor_get(v_x_97_, 0);
if (lean_obj_tag(v_pre_98_) == 0)
{
lean_object* v_str_99_; uint8_t v___x_100_; 
v_str_99_ = lean_ctor_get(v_x_97_, 1);
lean_inc_ref(v_str_99_);
lean_dec_ref_known(v_x_97_, 2);
v___x_100_ = l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId(v_str_99_);
return v___x_100_;
}
else
{
lean_object* v_str_101_; uint8_t v___x_102_; 
lean_inc(v_pre_98_);
v_str_101_ = lean_ctor_get(v_x_97_, 1);
lean_inc_ref(v_str_101_);
lean_dec_ref_known(v_x_97_, 2);
v___x_102_ = l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId(v_str_101_);
if (v___x_102_ == 0)
{
lean_dec(v_pre_98_);
return v___x_102_;
}
else
{
v_x_97_ = v_pre_98_;
goto _start;
}
}
}
else
{
uint8_t v___x_104_; 
lean_dec(v_x_97_);
v___x_104_ = 0;
return v___x_104_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppName___boxed(lean_object* v_x_105_){
_start:
{
uint8_t v_res_106_; lean_object* v_r_107_; 
v_res_106_ = l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppName(v_x_105_);
v_r_107_ = lean_box(v_res_106_);
return v_r_107_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_108_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_109_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_110_, 0, v___x_109_);
return v___x_110_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_111_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_112_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_113_ = lean_unsigned_to_nat(0u);
v___x_114_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
lean_ctor_set(v___x_114_, 1, v___x_113_);
lean_ctor_set(v___x_114_, 2, v___x_113_);
lean_ctor_set(v___x_114_, 3, v___x_113_);
lean_ctor_set(v___x_114_, 4, v___x_112_);
lean_ctor_set(v___x_114_, 5, v___x_112_);
lean_ctor_set(v___x_114_, 6, v___x_112_);
lean_ctor_set(v___x_114_, 7, v___x_112_);
lean_ctor_set(v___x_114_, 8, v___x_112_);
lean_ctor_set(v___x_114_, 9, v___x_112_);
lean_ctor_set(v___x_114_, 10, v___x_112_);
lean_ctor_set(v___x_114_, 11, v___x_111_);
return v___x_114_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
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
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_118_ = ((size_t)5ULL);
v___x_119_ = lean_unsigned_to_nat(0u);
v___x_120_ = lean_unsigned_to_nat(32u);
v___x_121_ = lean_mk_empty_array_with_capacity(v___x_120_);
v___x_122_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_123_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_123_, 0, v___x_122_);
lean_ctor_set(v___x_123_, 1, v___x_121_);
lean_ctor_set(v___x_123_, 2, v___x_119_);
lean_ctor_set(v___x_123_, 3, v___x_119_);
lean_ctor_set_usize(v___x_123_, 4, v___x_118_);
return v___x_123_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_124_ = lean_box(1);
v___x_125_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_126_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_127_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_127_, 0, v___x_126_);
lean_ctor_set(v___x_127_, 1, v___x_125_);
lean_ctor_set(v___x_127_, 2, v___x_124_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_128_, lean_object* v___y_129_, lean_object* v___y_130_){
_start:
{
lean_object* v___x_132_; lean_object* v_toCold_133_; lean_object* v_env_134_; lean_object* v_options_135_; uint8_t v___x_136_; lean_object* v_env_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_132_ = lean_st_ref_get(v___y_130_);
v_toCold_133_ = lean_ctor_get(v___y_129_, 0);
v_env_134_ = lean_ctor_get(v___x_132_, 0);
lean_inc_ref(v_env_134_);
lean_dec(v___x_132_);
v_options_135_ = lean_ctor_get(v_toCold_133_, 2);
v___x_136_ = 0;
v_env_137_ = l_Lean_Environment_setRecordingDeps(v_env_134_, v___x_136_);
v___x_138_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_139_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___closed__5);
lean_inc_ref(v_options_135_);
v___x_140_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_140_, 0, v_env_137_);
lean_ctor_set(v___x_140_, 1, v___x_138_);
lean_ctor_set(v___x_140_, 2, v___x_139_);
lean_ctor_set(v___x_140_, 3, v_options_135_);
v___x_141_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_141_, 0, v___x_140_);
lean_ctor_set(v___x_141_, 1, v_msgData_128_);
v___x_142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_142_, 0, v___x_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0(v_msgData_143_, v___y_144_, v___y_145_);
lean_dec(v___y_145_);
lean_dec_ref(v___y_144_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_148_, lean_object* v___y_149_, lean_object* v___y_150_){
_start:
{
lean_object* v_ref_152_; lean_object* v___x_153_; lean_object* v_a_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_162_; 
v_ref_152_ = lean_ctor_get(v___y_149_, 2);
v___x_153_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0_spec__0(v_msg_148_, v___y_149_, v___y_150_);
v_a_154_ = lean_ctor_get(v___x_153_, 0);
v_isSharedCheck_162_ = !lean_is_exclusive(v___x_153_);
if (v_isSharedCheck_162_ == 0)
{
v___x_156_ = v___x_153_;
v_isShared_157_ = v_isSharedCheck_162_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_a_154_);
lean_dec(v___x_153_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_162_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_158_; lean_object* v___x_160_; 
lean_inc(v_ref_152_);
v___x_158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_158_, 0, v_ref_152_);
lean_ctor_set(v___x_158_, 1, v_a_154_);
if (v_isShared_157_ == 0)
{
lean_ctor_set_tag(v___x_156_, 1);
lean_ctor_set(v___x_156_, 0, v___x_158_);
v___x_160_ = v___x_156_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v___x_158_);
v___x_160_ = v_reuseFailAlloc_161_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
return v___x_160_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0___redArg(v_msg_163_, v___y_164_, v___y_165_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
return v_res_167_;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_169_ = ((lean_object*)(l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_));
v___x_170_ = l_Lean_stringToMessageData(v___x_169_);
return v___x_170_;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_172_ = ((lean_object*)(l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_));
v___x_173_ = l_Lean_stringToMessageData(v___x_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_(lean_object* v_x_174_, lean_object* v_stx_175_, lean_object* v___y_176_, lean_object* v___y_177_){
_start:
{
lean_object* v___x_179_; 
v___x_179_ = l_Lean_Attribute_Builtin_getId(v_stx_175_, v___y_176_, v___y_177_);
if (lean_obj_tag(v___x_179_) == 0)
{
lean_object* v_a_180_; uint8_t v___x_181_; 
v_a_180_ = lean_ctor_get(v___x_179_, 0);
lean_inc(v_a_180_);
v___x_181_ = l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppName(v_a_180_);
if (v___x_181_ == 0)
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v_a_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_195_; 
lean_inc(v_a_180_);
lean_dec_ref_known(v___x_179_, 1);
v___x_182_ = lean_obj_once(&l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_, &l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_);
v___x_183_ = l_Lean_MessageData_ofName(v_a_180_);
v___x_184_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_184_, 0, v___x_182_);
lean_ctor_set(v___x_184_, 1, v___x_183_);
v___x_185_ = lean_obj_once(&l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_, &l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_);
v___x_186_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_186_, 0, v___x_184_);
lean_ctor_set(v___x_186_, 1, v___x_185_);
v___x_187_ = l_Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0___redArg(v___x_186_, v___y_176_, v___y_177_);
v_a_188_ = lean_ctor_get(v___x_187_, 0);
v_isSharedCheck_195_ = !lean_is_exclusive(v___x_187_);
if (v_isSharedCheck_195_ == 0)
{
v___x_190_ = v___x_187_;
v_isShared_191_ = v_isSharedCheck_195_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_a_188_);
lean_dec(v___x_187_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_195_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v___x_193_; 
if (v_isShared_191_ == 0)
{
v___x_193_ = v___x_190_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v_a_188_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
}
else
{
return v___x_179_;
}
}
else
{
return v___x_179_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2____boxed(lean_object* v_x_196_, lean_object* v_stx_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_(v_x_196_, v_stx_197_, v___y_198_, v___y_199_);
lean_dec(v___y_199_);
lean_dec_ref(v___y_198_);
lean_dec(v_x_196_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_(lean_object* v_x_202_, lean_object* v_x_203_, lean_object* v_x_204_, lean_object* v___y_205_){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_207_ = lean_box(0);
v___x_208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_208_, 0, v___x_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2____boxed(lean_object* v_x_209_, lean_object* v_x_210_, lean_object* v_x_211_, lean_object* v___y_212_, lean_object* v___y_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_(v_x_209_, v_x_210_, v_x_211_, v___y_212_);
lean_dec(v___y_212_);
lean_dec_ref(v_x_211_);
lean_dec(v_x_210_);
lean_dec(v_x_209_);
return v_res_214_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_(uint8_t v___x_215_, lean_object* v_env_216_, lean_object* v_n_217_, lean_object* v_x_218_){
_start:
{
uint8_t v___x_219_; 
v___x_219_ = l_Lean_Environment_contains(v_env_216_, v_n_217_, v___x_215_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2____boxed(lean_object* v___x_220_, lean_object* v_env_221_, lean_object* v_n_222_, lean_object* v_x_223_){
_start:
{
uint8_t v___x_1506__boxed_224_; uint8_t v_res_225_; lean_object* v_r_226_; 
v___x_1506__boxed_224_ = lean_unbox(v___x_220_);
v_res_225_ = l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_(v___x_1506__boxed_224_, v_env_221_, v_n_222_, v_x_223_);
lean_dec(v_x_223_);
v_r_226_ = lean_box(v_res_225_);
return v_r_226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_253_ = ((lean_object*)(l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_));
v___x_254_ = l_Lean_registerParametricAttribute___redArg(v___x_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2____boxed(lean_object* v_a_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l___private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_();
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_257_, lean_object* v_msg_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
lean_object* v___x_262_; 
v___x_262_ = l_Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0___redArg(v_msg_258_, v___y_259_, v___y_260_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_263_, lean_object* v_msg_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2__spec__0(v_00_u03b1_263_, v_msg_264_, v___y_265_, v___y_266_);
lean_dec(v___y_266_);
lean_dec_ref(v___y_265_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_docString__1(){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_271_ = ((lean_object*)(l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_));
v___x_272_ = ((lean_object*)(l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_docString__1___closed__0));
v___x_273_ = l_Lean_addBuiltinDocString(v___x_271_, v___x_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_docString__1___boxed(lean_object* v_a_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_docString__1();
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3(){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_302_ = ((lean_object*)(l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_ExportAttr_1307678936____hygCtx___hyg_2_));
v___x_303_ = ((lean_object*)(l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__6));
v___x_304_ = l_Lean_addBuiltinDeclarationRanges(v___x_302_, v___x_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___boxed(lean_object* v_a_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3();
return v_res_306_;
}
}
LEAN_EXPORT lean_object* lean_get_export_name_for(lean_object* v_env_307_, lean_object* v_n_308_){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_309_ = lean_box(0);
v___x_310_ = l_Lean_exportAttr;
v___x_311_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_309_, v___x_310_, v_env_307_, v_n_308_);
return v___x_311_;
}
}
LEAN_EXPORT uint8_t l_Lean_isExport(lean_object* v_env_315_, lean_object* v_n_316_){
_start:
{
lean_object* v___x_317_; 
lean_inc(v_n_316_);
v___x_317_ = lean_get_export_name_for(v_env_315_, v_n_316_);
if (lean_obj_tag(v___x_317_) == 0)
{
lean_object* v___x_318_; uint8_t v___x_319_; 
v___x_318_ = ((lean_object*)(l_Lean_isExport___closed__1));
v___x_319_ = lean_name_eq(v_n_316_, v___x_318_);
lean_dec(v_n_316_);
return v___x_319_;
}
else
{
uint8_t v___x_320_; 
lean_dec_ref_known(v___x_317_, 1);
lean_dec(v_n_316_);
v___x_320_ = 1;
return v___x_320_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isExport___boxed(lean_object* v_env_321_, lean_object* v_n_322_){
_start:
{
uint8_t v_res_323_; lean_object* v_r_324_; 
v_res_323_ = l_Lean_isExport(v_env_321_, v_n_322_);
v_r_324_ = lean_box(v_res_323_);
return v_r_324_;
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

// Lean compiler output
// Module: Lean.Elab.SetOption
// Imports: public import Lean.Elab.InfoTree public import Init.Syntax
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Syntax_isStrLit_x3f(lean_object*);
lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_KVMap_instValueDataValue;
uint8_t l_Lean_DataValue_sameCtor(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Int_repr(lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Options_set___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_pushInfoLeaf___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getOptionDecl___boxed(lean_object*, lean_object*);
lean_object* l_IO_toEIO___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Lean_Syntax_setArgs(lean_object*, lean_object*);
lean_object* l_Lean_Elab_addCompletionInfo___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_logWarning___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_get___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_KVMap_instValueBool;
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_initFn_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_initFn_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "linter"};
static const lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "deprecated"};
static const lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "options"};
static const lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(227, 99, 57, 49, 46, 156, 253, 187)}};
static const lean_ctor_object l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(167, 164, 118, 146, 51, 197, 202, 62)}};
static const lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "if true, generate deprecation warnings for deprecated options"};
static const lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(161, 137, 139, 132, 156, 105, 17, 87)}};
static const lean_ctor_object l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(124, 255, 51, 83, 51, 207, 102, 168)}};
static const lean_ctor_object l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value_aux_3),((lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(100, 217, 247, 135, 107, 189, 47, 78)}};
static const lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_linter_deprecated_options;
static const lean_string_object l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Invalid `set_option` command: The option `"};
static const lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg___closed__1;
static const lean_string_object l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "` cannot be configured using `set_option`"};
static const lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "String"};
static const lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__0 = (const lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__1 = (const lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__2;
static lean_once_cell_t l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__3;
static const lean_string_object l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__4 = (const lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__5 = (const lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__5_value;
static lean_once_cell_t l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__6;
static lean_once_cell_t l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__7;
static const lean_string_object l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__8 = (const lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__8_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__9 = (const lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__9_value;
static lean_once_cell_t l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__10;
static lean_once_cell_t l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__11;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___boxed(lean_object*);
static const lean_string_object l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "\nhas type"};
static const lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__1;
static const lean_string_object l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "\nbut the option `"};
static const lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__3;
static const lean_string_object l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "` expects a value of type"};
static const lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__4 = (const lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__5;
static const lean_string_object l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "set_option value type mismatch: The value"};
static const lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__6 = (const lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__7;
static const lean_string_object l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__8 = (const lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__8_value)}};
static const lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__9 = (const lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__9_value;
static const lean_string_object l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__10 = (const lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__10_value)}};
static const lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__11 = (const lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__11_value;
static const lean_string_object l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__12 = (const lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__12_value;
static const lean_ctor_object l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__12_value)}};
static const lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__13 = (const lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__13_value;
static const lean_string_object l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__14 = (const lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__14_value;
static const lean_string_object l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__15 = (const lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__15_value;
static const lean_string_object l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__16 = (const lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__16_value;
static lean_once_cell_t l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__17;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_validateOptionValue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_validateOptionValue___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_validateOptionValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_validateOptionValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg___lam__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_elabSetOption___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Unexpected set_option value `"};
static const lean_object* l_Lean_Elab_elabSetOption___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_elabSetOption___redArg___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_Elab_elabSetOption___redArg___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_elabSetOption___redArg___lam__1___closed__1;
static const lean_string_object l_Lean_Elab_elabSetOption___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "`; expected a literal of type `"};
static const lean_object* l_Lean_Elab_elabSetOption___redArg___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_elabSetOption___redArg___lam__1___closed__2_value;
static lean_once_cell_t l_Lean_Elab_elabSetOption___redArg___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_elabSetOption___redArg___lam__1___closed__3;
static lean_once_cell_t l_Lean_Elab_elabSetOption___redArg___lam__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_elabSetOption___redArg___lam__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "` has been deprecated"};
static const lean_object* l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__1;
static const lean_string_object l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__3;
static const lean_string_object l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__4_value;
static lean_once_cell_t l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedOption___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedOption___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedOption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_initFn_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_initFn_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_initFn_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_56_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4_));
v___x_57_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4_));
v___x_58_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4_));
v___x_59_ = l_Lean_Option_register___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_initFn_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__spec__0(v___x_56_, v___x_57_, v___x_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4____boxed(lean_object* v_a_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4_();
return v_res_61_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg___closed__1(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_63_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg___closed__0));
v___x_64_ = l_Lean_stringToMessageData(v___x_63_);
return v___x_64_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg___closed__3(void){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_66_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg___closed__2));
v___x_67_ = l_Lean_stringToMessageData(v___x_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg(lean_object* v_inst_68_, lean_object* v_inst_69_, lean_object* v_optionName_70_){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_71_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg___closed__1, &l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg___closed__1_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg___closed__1);
v___x_72_ = l_Lean_MessageData_ofName(v_optionName_70_);
v___x_73_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_73_, 0, v___x_71_);
lean_ctor_set(v___x_73_, 1, v___x_72_);
v___x_74_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg___closed__3, &l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg___closed__3_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg___closed__3);
v___x_75_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_75_, 0, v___x_73_);
lean_ctor_set(v___x_75_, 1, v___x_74_);
v___x_76_ = l_Lean_throwError___redArg(v_inst_68_, v_inst_69_, v___x_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable(lean_object* v_m_77_, lean_object* v_inst_78_, lean_object* v_inst_79_, lean_object* v_00_u03b1_80_, lean_object* v_optionName_81_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg(v_inst_78_, v_inst_79_, v_optionName_81_);
return v___x_82_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__2(void){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_86_ = lean_box(0);
v___x_87_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__1));
v___x_88_ = l_Lean_mkConst(v___x_87_, v___x_86_);
return v___x_88_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__3(void){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_89_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__2, &l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__2_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__2);
v___x_90_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_90_, 0, v___x_89_);
return v___x_90_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__6(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_94_ = lean_box(0);
v___x_95_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__5));
v___x_96_ = l_Lean_mkConst(v___x_95_, v___x_94_);
return v___x_96_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__7(void){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_97_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__6, &l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__6_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__6);
v___x_98_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_98_, 0, v___x_97_);
return v___x_98_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__10(void){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_102_ = lean_box(0);
v___x_103_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__9));
v___x_104_ = l_Lean_mkConst(v___x_103_, v___x_102_);
return v___x_104_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__11(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_105_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__10, &l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__10_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__10);
v___x_106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_106_, 0, v___x_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f(lean_object* v_x_107_){
_start:
{
switch(lean_obj_tag(v_x_107_))
{
case 0:
{
lean_object* v___x_108_; 
v___x_108_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__3, &l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__3_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__3);
return v___x_108_;
}
case 1:
{
lean_object* v___x_109_; 
v___x_109_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__7, &l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__7_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__7);
return v___x_109_;
}
case 3:
{
lean_object* v___x_110_; 
v___x_110_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__11, &l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__11_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__11);
return v___x_110_;
}
default: 
{
lean_object* v___x_111_; 
v___x_111_ = lean_box(0);
return v___x_111_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___boxed(lean_object* v_x_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f(v_x_112_);
lean_dec_ref(v_x_112_);
return v_res_113_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__1(void){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_115_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__0));
v___x_116_ = l_Lean_stringToMessageData(v___x_115_);
return v___x_116_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__3(void){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_118_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__2));
v___x_119_ = l_Lean_stringToMessageData(v___x_118_);
return v___x_119_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__5(void){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_121_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__4));
v___x_122_ = l_Lean_stringToMessageData(v___x_121_);
return v___x_122_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__7(void){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_124_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__6));
v___x_125_ = l_Lean_stringToMessageData(v___x_124_);
return v___x_125_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__17(void){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_138_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__16));
v___x_139_ = lean_unsigned_to_nat(14u);
v___x_140_ = lean_unsigned_to_nat(22u);
v___x_141_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__15));
v___x_142_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__14));
v___x_143_ = l_mkPanicMessageWithDecl(v___x_142_, v___x_141_, v___x_140_, v___x_139_, v___x_138_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg(lean_object* v_inst_144_, lean_object* v_inst_145_, lean_object* v_optionName_146_, lean_object* v_found_147_, lean_object* v_defVal_148_){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f(v_defVal_148_);
if (lean_obj_tag(v___x_149_) == 1)
{
lean_object* v_val_150_; lean_object* v___y_152_; lean_object* v___y_153_; lean_object* v___y_154_; lean_object* v___y_173_; lean_object* v___x_221_; 
v_val_150_ = lean_ctor_get(v___x_149_, 0);
lean_inc(v_val_150_);
lean_dec_ref(v___x_149_);
v___x_221_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f(v_found_147_);
if (lean_obj_tag(v___x_221_) == 0)
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_222_ = l_Lean_instInhabitedExpr;
v___x_223_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__17, &l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__17_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__17);
v___x_224_ = l_panic___redArg(v___x_222_, v___x_223_);
v___y_173_ = v___x_224_;
goto v___jp_172_;
}
else
{
lean_object* v_val_225_; 
v_val_225_ = lean_ctor_get(v___x_221_, 0);
lean_inc(v_val_225_);
lean_dec_ref(v___x_221_);
v___y_173_ = v_val_225_;
goto v___jp_172_;
}
v___jp_151_:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_155_ = l_Lean_MessageData_ofFormat(v___y_154_);
v___x_156_ = l_Lean_indentD(v___x_155_);
lean_inc_ref(v___y_152_);
v___x_157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_157_, 0, v___y_152_);
lean_ctor_set(v___x_157_, 1, v___x_156_);
v___x_158_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__1, &l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__1_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__1);
v___x_159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_159_, 0, v___x_157_);
lean_ctor_set(v___x_159_, 1, v___x_158_);
v___x_160_ = l_Lean_MessageData_ofExpr(v___y_153_);
v___x_161_ = l_Lean_indentD(v___x_160_);
v___x_162_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_162_, 0, v___x_159_);
lean_ctor_set(v___x_162_, 1, v___x_161_);
v___x_163_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__3, &l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__3_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__3);
v___x_164_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_164_, 0, v___x_162_);
lean_ctor_set(v___x_164_, 1, v___x_163_);
v___x_165_ = l_Lean_MessageData_ofName(v_optionName_146_);
v___x_166_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_166_, 0, v___x_164_);
lean_ctor_set(v___x_166_, 1, v___x_165_);
v___x_167_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__5, &l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__5_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__5);
v___x_168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_168_, 0, v___x_166_);
lean_ctor_set(v___x_168_, 1, v___x_167_);
v___x_169_ = l_Lean_indentExpr(v_val_150_);
v___x_170_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_170_, 0, v___x_168_);
lean_ctor_set(v___x_170_, 1, v___x_169_);
v___x_171_ = l_Lean_throwError___redArg(v_inst_144_, v_inst_145_, v___x_170_);
return v___x_171_;
}
v___jp_172_:
{
lean_object* v___x_174_; 
v___x_174_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__7, &l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__7_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__7);
switch(lean_obj_tag(v_found_147_))
{
case 0:
{
lean_object* v_v_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_183_; 
v_v_175_ = lean_ctor_get(v_found_147_, 0);
v_isSharedCheck_183_ = !lean_is_exclusive(v_found_147_);
if (v_isSharedCheck_183_ == 0)
{
v___x_177_ = v_found_147_;
v_isShared_178_ = v_isSharedCheck_183_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_v_175_);
lean_dec(v_found_147_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_183_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_179_; lean_object* v___x_181_; 
v___x_179_ = l_String_quote(v_v_175_);
if (v_isShared_178_ == 0)
{
lean_ctor_set_tag(v___x_177_, 3);
lean_ctor_set(v___x_177_, 0, v___x_179_);
v___x_181_ = v___x_177_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v___x_179_);
v___x_181_ = v_reuseFailAlloc_182_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
v___y_152_ = v___x_174_;
v___y_153_ = v___y_173_;
v___y_154_ = v___x_181_;
goto v___jp_151_;
}
}
}
case 1:
{
uint8_t v_v_184_; 
v_v_184_ = lean_ctor_get_uint8(v_found_147_, 0);
lean_dec_ref(v_found_147_);
if (v_v_184_ == 0)
{
lean_object* v___x_185_; 
v___x_185_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__9));
v___y_152_ = v___x_174_;
v___y_153_ = v___y_173_;
v___y_154_ = v___x_185_;
goto v___jp_151_;
}
else
{
lean_object* v___x_186_; 
v___x_186_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__11));
v___y_152_ = v___x_174_;
v___y_153_ = v___y_173_;
v___y_154_ = v___x_186_;
goto v___jp_151_;
}
}
case 2:
{
lean_object* v_v_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_198_; 
v_v_187_ = lean_ctor_get(v_found_147_, 0);
v_isSharedCheck_198_ = !lean_is_exclusive(v_found_147_);
if (v_isSharedCheck_198_ == 0)
{
v___x_189_ = v_found_147_;
v_isShared_190_ = v_isSharedCheck_198_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_v_187_);
lean_dec(v_found_147_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_198_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v___x_191_; uint8_t v___x_192_; lean_object* v___x_193_; lean_object* v___x_195_; 
v___x_191_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__13));
v___x_192_ = 1;
v___x_193_ = l_Lean_Name_toString(v_v_187_, v___x_192_);
if (v_isShared_190_ == 0)
{
lean_ctor_set_tag(v___x_189_, 3);
lean_ctor_set(v___x_189_, 0, v___x_193_);
v___x_195_ = v___x_189_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v___x_193_);
v___x_195_ = v_reuseFailAlloc_197_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
lean_object* v___x_196_; 
v___x_196_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_196_, 0, v___x_191_);
lean_ctor_set(v___x_196_, 1, v___x_195_);
v___y_152_ = v___x_174_;
v___y_153_ = v___y_173_;
v___y_154_ = v___x_196_;
goto v___jp_151_;
}
}
}
case 3:
{
lean_object* v_v_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_207_; 
v_v_199_ = lean_ctor_get(v_found_147_, 0);
v_isSharedCheck_207_ = !lean_is_exclusive(v_found_147_);
if (v_isSharedCheck_207_ == 0)
{
v___x_201_ = v_found_147_;
v_isShared_202_ = v_isSharedCheck_207_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_v_199_);
lean_dec(v_found_147_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_207_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___x_203_; lean_object* v___x_205_; 
v___x_203_ = l_Nat_reprFast(v_v_199_);
if (v_isShared_202_ == 0)
{
lean_ctor_set(v___x_201_, 0, v___x_203_);
v___x_205_ = v___x_201_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v___x_203_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
v___y_152_ = v___x_174_;
v___y_153_ = v___y_173_;
v___y_154_ = v___x_205_;
goto v___jp_151_;
}
}
}
case 4:
{
lean_object* v_v_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_216_; 
v_v_208_ = lean_ctor_get(v_found_147_, 0);
v_isSharedCheck_216_ = !lean_is_exclusive(v_found_147_);
if (v_isSharedCheck_216_ == 0)
{
v___x_210_ = v_found_147_;
v_isShared_211_ = v_isSharedCheck_216_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_v_208_);
lean_dec(v_found_147_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_216_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___x_212_; lean_object* v___x_214_; 
v___x_212_ = l_Int_repr(v_v_208_);
lean_dec(v_v_208_);
if (v_isShared_211_ == 0)
{
lean_ctor_set_tag(v___x_210_, 3);
lean_ctor_set(v___x_210_, 0, v___x_212_);
v___x_214_ = v___x_210_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v___x_212_);
v___x_214_ = v_reuseFailAlloc_215_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
v___y_152_ = v___x_174_;
v___y_153_ = v___y_173_;
v___y_154_ = v___x_214_;
goto v___jp_151_;
}
}
}
default: 
{
lean_object* v_v_217_; lean_object* v___x_218_; uint8_t v___x_219_; lean_object* v___x_220_; 
v_v_217_ = lean_ctor_get(v_found_147_, 0);
lean_inc(v_v_217_);
lean_dec_ref(v_found_147_);
v___x_218_ = lean_box(0);
v___x_219_ = 0;
v___x_220_ = l_Lean_Syntax_formatStx(v_v_217_, v___x_218_, v___x_219_);
v___y_152_ = v___x_174_;
v___y_153_ = v___y_173_;
v___y_154_ = v___x_220_;
goto v___jp_151_;
}
}
}
}
else
{
lean_object* v___x_226_; 
lean_dec(v___x_149_);
lean_dec_ref(v_found_147_);
v___x_226_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg(v_inst_144_, v_inst_145_, v_optionName_146_);
return v___x_226_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___boxed(lean_object* v_inst_227_, lean_object* v_inst_228_, lean_object* v_optionName_229_, lean_object* v_found_230_, lean_object* v_defVal_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg(v_inst_227_, v_inst_228_, v_optionName_229_, v_found_230_, v_defVal_231_);
lean_dec_ref(v_defVal_231_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue(lean_object* v_m_233_, lean_object* v_inst_234_, lean_object* v_inst_235_, lean_object* v_optionName_236_, lean_object* v_found_237_, lean_object* v_defVal_238_){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg(v_inst_234_, v_inst_235_, v_optionName_236_, v_found_237_, v_defVal_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___boxed(lean_object* v_m_240_, lean_object* v_inst_241_, lean_object* v_inst_242_, lean_object* v_optionName_243_, lean_object* v_found_244_, lean_object* v_defVal_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue(v_m_240_, v_inst_241_, v_inst_242_, v_optionName_243_, v_found_244_, v_defVal_245_);
lean_dec_ref(v_defVal_245_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_validateOptionValue___redArg(lean_object* v_inst_247_, lean_object* v_inst_248_, lean_object* v_optionName_249_, lean_object* v_decl_250_, lean_object* v_val_251_){
_start:
{
lean_object* v_defValue_252_; uint8_t v___x_253_; 
v_defValue_252_ = lean_ctor_get(v_decl_250_, 2);
v___x_253_ = l_Lean_DataValue_sameCtor(v_defValue_252_, v_val_251_);
if (v___x_253_ == 0)
{
lean_object* v___x_254_; 
v___x_254_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg(v_inst_247_, v_inst_248_, v_optionName_249_, v_val_251_, v_defValue_252_);
return v___x_254_;
}
else
{
lean_object* v_toApplicative_255_; lean_object* v_toPure_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
lean_dec_ref(v_val_251_);
lean_dec(v_optionName_249_);
lean_dec_ref(v_inst_248_);
v_toApplicative_255_ = lean_ctor_get(v_inst_247_, 0);
lean_inc_ref(v_toApplicative_255_);
lean_dec_ref(v_inst_247_);
v_toPure_256_ = lean_ctor_get(v_toApplicative_255_, 1);
lean_inc(v_toPure_256_);
lean_dec_ref(v_toApplicative_255_);
v___x_257_ = lean_box(0);
v___x_258_ = lean_apply_2(v_toPure_256_, lean_box(0), v___x_257_);
return v___x_258_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_validateOptionValue___redArg___boxed(lean_object* v_inst_259_, lean_object* v_inst_260_, lean_object* v_optionName_261_, lean_object* v_decl_262_, lean_object* v_val_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Lean_Elab_validateOptionValue___redArg(v_inst_259_, v_inst_260_, v_optionName_261_, v_decl_262_, v_val_263_);
lean_dec_ref(v_decl_262_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_validateOptionValue(lean_object* v_m_265_, lean_object* v_inst_266_, lean_object* v_inst_267_, lean_object* v_optionName_268_, lean_object* v_decl_269_, lean_object* v_val_270_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = l_Lean_Elab_validateOptionValue___redArg(v_inst_266_, v_inst_267_, v_optionName_268_, v_decl_269_, v_val_270_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_validateOptionValue___boxed(lean_object* v_m_272_, lean_object* v_inst_273_, lean_object* v_inst_274_, lean_object* v_optionName_275_, lean_object* v_decl_276_, lean_object* v_val_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_Lean_Elab_validateOptionValue(v_m_272_, v_inst_273_, v_inst_274_, v_optionName_275_, v_decl_276_, v_val_277_);
lean_dec_ref(v_decl_276_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___redArg___lam__0(lean_object* v___x_279_, lean_object* v_optionName_280_, lean_object* v_val_281_, lean_object* v_decl_282_, lean_object* v_toPure_283_, lean_object* v_____do__lift_284_){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_285_ = l_Lean_Options_set___redArg(v___x_279_, v_____do__lift_284_, v_optionName_280_, v_val_281_);
v___x_286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_285_);
lean_ctor_set(v___x_286_, 1, v_decl_282_);
v___x_287_ = lean_apply_2(v_toPure_283_, lean_box(0), v___x_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___redArg___lam__1(lean_object* v_toBind_288_, lean_object* v_inst_289_, lean_object* v___f_290_, lean_object* v_____r_291_){
_start:
{
lean_object* v___x_292_; 
v___x_292_ = lean_apply_4(v_toBind_288_, lean_box(0), lean_box(0), v_inst_289_, v___f_290_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___redArg(lean_object* v_inst_293_, lean_object* v_inst_294_, lean_object* v_inst_295_, lean_object* v_optionName_296_, lean_object* v_decl_297_, lean_object* v_val_298_){
_start:
{
lean_object* v___x_299_; lean_object* v_toApplicative_300_; lean_object* v_toBind_301_; lean_object* v_toPure_302_; lean_object* v___x_303_; lean_object* v___f_304_; lean_object* v___f_305_; lean_object* v___x_306_; 
v___x_299_ = l_Lean_KVMap_instValueDataValue;
v_toApplicative_300_ = lean_ctor_get(v_inst_293_, 0);
v_toBind_301_ = lean_ctor_get(v_inst_293_, 1);
lean_inc_n(v_toBind_301_, 2);
v_toPure_302_ = lean_ctor_get(v_toApplicative_300_, 1);
lean_inc(v_toPure_302_);
lean_inc_ref(v_val_298_);
lean_inc(v_optionName_296_);
v___x_303_ = l_Lean_Elab_validateOptionValue___redArg(v_inst_293_, v_inst_295_, v_optionName_296_, v_decl_297_, v_val_298_);
v___f_304_ = lean_alloc_closure((void*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___redArg___lam__0), 6, 5);
lean_closure_set(v___f_304_, 0, v___x_299_);
lean_closure_set(v___f_304_, 1, v_optionName_296_);
lean_closure_set(v___f_304_, 2, v_val_298_);
lean_closure_set(v___f_304_, 3, v_decl_297_);
lean_closure_set(v___f_304_, 4, v_toPure_302_);
v___f_305_ = lean_alloc_closure((void*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___redArg___lam__1), 4, 3);
lean_closure_set(v___f_305_, 0, v_toBind_301_);
lean_closure_set(v___f_305_, 1, v_inst_294_);
lean_closure_set(v___f_305_, 2, v___f_304_);
v___x_306_ = lean_apply_4(v_toBind_301_, lean_box(0), lean_box(0), v___x_303_, v___f_305_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption(lean_object* v_m_307_, lean_object* v_inst_308_, lean_object* v_inst_309_, lean_object* v_inst_310_, lean_object* v_optionName_311_, lean_object* v_decl_312_, lean_object* v_val_313_){
_start:
{
lean_object* v___x_314_; 
v___x_314_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___redArg(v_inst_308_, v_inst_309_, v_inst_310_, v_optionName_311_, v_decl_312_, v_val_313_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg___lam__0(lean_object* v_ref_315_, lean_object* v_ex_316_){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_317_ = lean_io_error_to_string(v_ex_316_);
v___x_318_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
v___x_319_ = l_Lean_MessageData_ofFormat(v___x_318_);
v___x_320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_320_, 0, v_ref_315_);
lean_ctor_set(v___x_320_, 1, v___x_319_);
return v___x_320_;
}
}
static lean_object* _init_l_Lean_Elab_elabSetOption___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_322_ = ((lean_object*)(l_Lean_Elab_elabSetOption___redArg___lam__1___closed__0));
v___x_323_ = l_Lean_stringToMessageData(v___x_322_);
return v___x_323_;
}
}
static lean_object* _init_l_Lean_Elab_elabSetOption___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_325_ = ((lean_object*)(l_Lean_Elab_elabSetOption___redArg___lam__1___closed__2));
v___x_326_ = l_Lean_stringToMessageData(v___x_325_);
return v___x_326_;
}
}
static lean_object* _init_l_Lean_Elab_elabSetOption___redArg___lam__1___closed__4(void){
_start:
{
lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_327_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__12));
v___x_328_ = l_Lean_stringToMessageData(v___x_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg___lam__1(lean_object* v_val_329_, lean_object* v_decl_330_, lean_object* v_inst_331_, lean_object* v_inst_332_, lean_object* v_optionName_333_, lean_object* v_inst_334_, lean_object* v_____r_335_){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = l_Lean_Syntax_isStrLit_x3f(v_val_329_);
if (lean_obj_tag(v___x_351_) == 0)
{
lean_object* v___x_352_; 
v___x_352_ = l_Lean_Syntax_isNatLit_x3f(v_val_329_);
if (lean_obj_tag(v___x_352_) == 0)
{
if (lean_obj_tag(v_val_329_) == 2)
{
lean_object* v_val_353_; lean_object* v___x_354_; uint8_t v___x_355_; 
v_val_353_ = lean_ctor_get(v_val_329_, 1);
v___x_354_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__10));
v___x_355_ = lean_string_dec_eq(v_val_353_, v___x_354_);
if (v___x_355_ == 0)
{
lean_object* v___x_356_; uint8_t v___x_357_; 
v___x_356_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__8));
v___x_357_ = lean_string_dec_eq(v_val_353_, v___x_356_);
if (v___x_357_ == 0)
{
lean_dec(v_inst_334_);
goto v___jp_336_;
}
else
{
lean_object* v___x_358_; lean_object* v___x_359_; 
lean_dec_ref(v_val_329_);
v___x_358_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_358_, 0, v___x_355_);
v___x_359_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___redArg(v_inst_331_, v_inst_334_, v_inst_332_, v_optionName_333_, v_decl_330_, v___x_358_);
return v___x_359_;
}
}
else
{
lean_object* v___x_360_; lean_object* v___x_361_; 
lean_dec_ref(v_val_329_);
v___x_360_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_360_, 0, v___x_355_);
v___x_361_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___redArg(v_inst_331_, v_inst_334_, v_inst_332_, v_optionName_333_, v_decl_330_, v___x_360_);
return v___x_361_;
}
}
else
{
lean_dec(v_inst_334_);
goto v___jp_336_;
}
}
else
{
lean_object* v_val_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_370_; 
lean_dec(v_val_329_);
v_val_362_ = lean_ctor_get(v___x_352_, 0);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_352_);
if (v_isSharedCheck_370_ == 0)
{
v___x_364_ = v___x_352_;
v_isShared_365_ = v_isSharedCheck_370_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_val_362_);
lean_dec(v___x_352_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_370_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_367_; 
if (v_isShared_365_ == 0)
{
lean_ctor_set_tag(v___x_364_, 3);
v___x_367_ = v___x_364_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v_val_362_);
v___x_367_ = v_reuseFailAlloc_369_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
lean_object* v___x_368_; 
v___x_368_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___redArg(v_inst_331_, v_inst_334_, v_inst_332_, v_optionName_333_, v_decl_330_, v___x_367_);
return v___x_368_;
}
}
}
}
else
{
lean_object* v_val_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_379_; 
lean_dec(v_val_329_);
v_val_371_ = lean_ctor_get(v___x_351_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_351_);
if (v_isSharedCheck_379_ == 0)
{
v___x_373_ = v___x_351_;
v_isShared_374_ = v_isSharedCheck_379_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_val_371_);
lean_dec(v___x_351_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_379_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_376_; 
if (v_isShared_374_ == 0)
{
lean_ctor_set_tag(v___x_373_, 0);
v___x_376_ = v___x_373_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_val_371_);
v___x_376_ = v_reuseFailAlloc_378_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
lean_object* v___x_377_; 
v___x_377_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___redArg(v_inst_331_, v_inst_334_, v_inst_332_, v_optionName_333_, v_decl_330_, v___x_376_);
return v___x_377_;
}
}
}
v___jp_336_:
{
lean_object* v_defValue_337_; lean_object* v___x_338_; 
v_defValue_337_ = lean_ctor_get(v_decl_330_, 2);
lean_inc_ref(v_defValue_337_);
lean_dec_ref(v_decl_330_);
v___x_338_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f(v_defValue_337_);
lean_dec_ref(v_defValue_337_);
if (lean_obj_tag(v___x_338_) == 1)
{
lean_object* v_val_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
lean_dec(v_optionName_333_);
v_val_339_ = lean_ctor_get(v___x_338_, 0);
lean_inc(v_val_339_);
lean_dec_ref(v___x_338_);
v___x_340_ = lean_obj_once(&l_Lean_Elab_elabSetOption___redArg___lam__1___closed__1, &l_Lean_Elab_elabSetOption___redArg___lam__1___closed__1_once, _init_l_Lean_Elab_elabSetOption___redArg___lam__1___closed__1);
v___x_341_ = l_Lean_MessageData_ofSyntax(v_val_329_);
v___x_342_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_342_, 0, v___x_340_);
lean_ctor_set(v___x_342_, 1, v___x_341_);
v___x_343_ = lean_obj_once(&l_Lean_Elab_elabSetOption___redArg___lam__1___closed__3, &l_Lean_Elab_elabSetOption___redArg___lam__1___closed__3_once, _init_l_Lean_Elab_elabSetOption___redArg___lam__1___closed__3);
v___x_344_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_344_, 0, v___x_342_);
lean_ctor_set(v___x_344_, 1, v___x_343_);
v___x_345_ = l_Lean_MessageData_ofExpr(v_val_339_);
v___x_346_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_346_, 0, v___x_344_);
lean_ctor_set(v___x_346_, 1, v___x_345_);
v___x_347_ = lean_obj_once(&l_Lean_Elab_elabSetOption___redArg___lam__1___closed__4, &l_Lean_Elab_elabSetOption___redArg___lam__1___closed__4_once, _init_l_Lean_Elab_elabSetOption___redArg___lam__1___closed__4);
v___x_348_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_348_, 0, v___x_346_);
lean_ctor_set(v___x_348_, 1, v___x_347_);
v___x_349_ = l_Lean_throwError___redArg(v_inst_331_, v_inst_332_, v___x_348_);
return v___x_349_;
}
else
{
lean_object* v___x_350_; 
lean_dec(v___x_338_);
lean_dec(v_val_329_);
v___x_350_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg(v_inst_331_, v_inst_332_, v_optionName_333_);
return v___x_350_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg___lam__2(lean_object* v___f_380_, lean_object* v_____r_381_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = lean_apply_1(v___f_380_, v_____r_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg___lam__3(lean_object* v_val_383_, lean_object* v_inst_384_, lean_object* v_inst_385_, lean_object* v_optionName_386_, lean_object* v_inst_387_, uint8_t v_addInfo_388_, lean_object* v_id_389_, lean_object* v_inst_390_, lean_object* v_toBind_391_, lean_object* v_decl_392_){
_start:
{
lean_object* v___f_393_; 
lean_inc(v_inst_387_);
lean_inc(v_optionName_386_);
lean_inc_ref(v_inst_385_);
lean_inc_ref(v_inst_384_);
lean_inc_ref(v_decl_392_);
lean_inc(v_val_383_);
v___f_393_ = lean_alloc_closure((void*)(l_Lean_Elab_elabSetOption___redArg___lam__1), 7, 6);
lean_closure_set(v___f_393_, 0, v_val_383_);
lean_closure_set(v___f_393_, 1, v_decl_392_);
lean_closure_set(v___f_393_, 2, v_inst_384_);
lean_closure_set(v___f_393_, 3, v_inst_385_);
lean_closure_set(v___f_393_, 4, v_optionName_386_);
lean_closure_set(v___f_393_, 5, v_inst_387_);
if (v_addInfo_388_ == 0)
{
lean_object* v___x_394_; lean_object* v___x_395_; 
lean_dec_ref(v___f_393_);
lean_dec(v_toBind_391_);
lean_dec_ref(v_inst_390_);
lean_dec(v_id_389_);
v___x_394_ = lean_box(0);
v___x_395_ = l_Lean_Elab_elabSetOption___redArg___lam__1(v_val_383_, v_decl_392_, v_inst_384_, v_inst_385_, v_optionName_386_, v_inst_387_, v___x_394_);
return v___x_395_;
}
else
{
lean_object* v_declName_396_; lean_object* v___f_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
lean_dec(v_inst_387_);
lean_dec_ref(v_inst_385_);
lean_dec(v_val_383_);
v_declName_396_ = lean_ctor_get(v_decl_392_, 1);
lean_inc(v_declName_396_);
lean_dec_ref(v_decl_392_);
v___f_397_ = lean_alloc_closure((void*)(l_Lean_Elab_elabSetOption___redArg___lam__2), 2, 1);
lean_closure_set(v___f_397_, 0, v___f_393_);
v___x_398_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_398_, 0, v_id_389_);
lean_ctor_set(v___x_398_, 1, v_optionName_386_);
lean_ctor_set(v___x_398_, 2, v_declName_396_);
v___x_399_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_399_, 0, v___x_398_);
v___x_400_ = l_Lean_Elab_pushInfoLeaf___redArg(v_inst_384_, v_inst_390_, v___x_399_);
v___x_401_ = lean_apply_4(v_toBind_391_, lean_box(0), lean_box(0), v___x_400_, v___f_397_);
return v___x_401_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg___lam__3___boxed(lean_object* v_val_402_, lean_object* v_inst_403_, lean_object* v_inst_404_, lean_object* v_optionName_405_, lean_object* v_inst_406_, lean_object* v_addInfo_407_, lean_object* v_id_408_, lean_object* v_inst_409_, lean_object* v_toBind_410_, lean_object* v_decl_411_){
_start:
{
uint8_t v_addInfo_boxed_412_; lean_object* v_res_413_; 
v_addInfo_boxed_412_ = lean_unbox(v_addInfo_407_);
v_res_413_ = l_Lean_Elab_elabSetOption___redArg___lam__3(v_val_402_, v_inst_403_, v_inst_404_, v_optionName_405_, v_inst_406_, v_addInfo_boxed_412_, v_id_408_, v_inst_409_, v_toBind_410_, v_decl_411_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg___lam__4(lean_object* v_id_414_, lean_object* v_val_415_, lean_object* v_inst_416_, lean_object* v_inst_417_, lean_object* v_inst_418_, uint8_t v_addInfo_419_, lean_object* v_inst_420_, lean_object* v_toBind_421_, lean_object* v___f_422_, lean_object* v_inst_423_, lean_object* v_____r_424_){
_start:
{
lean_object* v___x_425_; lean_object* v_optionName_426_; lean_object* v___x_427_; lean_object* v___f_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_425_ = l_Lean_Syntax_getId(v_id_414_);
v_optionName_426_ = lean_erase_macro_scopes(v___x_425_);
v___x_427_ = lean_box(v_addInfo_419_);
lean_inc(v_toBind_421_);
lean_inc(v_optionName_426_);
v___f_428_ = lean_alloc_closure((void*)(l_Lean_Elab_elabSetOption___redArg___lam__3___boxed), 10, 9);
lean_closure_set(v___f_428_, 0, v_val_415_);
lean_closure_set(v___f_428_, 1, v_inst_416_);
lean_closure_set(v___f_428_, 2, v_inst_417_);
lean_closure_set(v___f_428_, 3, v_optionName_426_);
lean_closure_set(v___f_428_, 4, v_inst_418_);
lean_closure_set(v___f_428_, 5, v___x_427_);
lean_closure_set(v___f_428_, 6, v_id_414_);
lean_closure_set(v___f_428_, 7, v_inst_420_);
lean_closure_set(v___f_428_, 8, v_toBind_421_);
v___x_429_ = lean_alloc_closure((void*)(l_Lean_getOptionDecl___boxed), 2, 1);
lean_closure_set(v___x_429_, 0, v_optionName_426_);
v___x_430_ = lean_alloc_closure((void*)(l_IO_toEIO___boxed), 5, 4);
lean_closure_set(v___x_430_, 0, lean_box(0));
lean_closure_set(v___x_430_, 1, lean_box(0));
lean_closure_set(v___x_430_, 2, v___f_422_);
lean_closure_set(v___x_430_, 3, v___x_429_);
v___x_431_ = lean_apply_2(v_inst_423_, lean_box(0), v___x_430_);
v___x_432_ = lean_apply_4(v_toBind_421_, lean_box(0), lean_box(0), v___x_431_, v___f_428_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg___lam__4___boxed(lean_object* v_id_433_, lean_object* v_val_434_, lean_object* v_inst_435_, lean_object* v_inst_436_, lean_object* v_inst_437_, lean_object* v_addInfo_438_, lean_object* v_inst_439_, lean_object* v_toBind_440_, lean_object* v___f_441_, lean_object* v_inst_442_, lean_object* v_____r_443_){
_start:
{
uint8_t v_addInfo_boxed_444_; lean_object* v_res_445_; 
v_addInfo_boxed_444_ = lean_unbox(v_addInfo_438_);
v_res_445_ = l_Lean_Elab_elabSetOption___redArg___lam__4(v_id_433_, v_val_434_, v_inst_435_, v_inst_436_, v_inst_437_, v_addInfo_boxed_444_, v_inst_439_, v_toBind_440_, v___f_441_, v_inst_442_, v_____r_443_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg___lam__6(lean_object* v_id_446_, lean_object* v_val_447_, lean_object* v_inst_448_, lean_object* v_inst_449_, lean_object* v_inst_450_, uint8_t v_addInfo_451_, lean_object* v_inst_452_, lean_object* v_toBind_453_, lean_object* v_inst_454_, lean_object* v_ref_455_){
_start:
{
lean_object* v___f_456_; lean_object* v___x_457_; lean_object* v___f_458_; 
lean_inc(v_ref_455_);
v___f_456_ = lean_alloc_closure((void*)(l_Lean_Elab_elabSetOption___redArg___lam__0), 2, 1);
lean_closure_set(v___f_456_, 0, v_ref_455_);
v___x_457_ = lean_box(v_addInfo_451_);
lean_inc(v_inst_454_);
lean_inc_ref(v___f_456_);
lean_inc(v_toBind_453_);
lean_inc_ref(v_inst_452_);
lean_inc(v_inst_450_);
lean_inc_ref(v_inst_449_);
lean_inc_ref(v_inst_448_);
lean_inc(v_val_447_);
lean_inc(v_id_446_);
v___f_458_ = lean_alloc_closure((void*)(l_Lean_Elab_elabSetOption___redArg___lam__4___boxed), 11, 10);
lean_closure_set(v___f_458_, 0, v_id_446_);
lean_closure_set(v___f_458_, 1, v_val_447_);
lean_closure_set(v___f_458_, 2, v_inst_448_);
lean_closure_set(v___f_458_, 3, v_inst_449_);
lean_closure_set(v___f_458_, 4, v_inst_450_);
lean_closure_set(v___f_458_, 5, v___x_457_);
lean_closure_set(v___f_458_, 6, v_inst_452_);
lean_closure_set(v___f_458_, 7, v_toBind_453_);
lean_closure_set(v___f_458_, 8, v___f_456_);
lean_closure_set(v___f_458_, 9, v_inst_454_);
if (v_addInfo_451_ == 0)
{
lean_object* v___x_459_; lean_object* v___x_460_; 
lean_dec_ref(v___f_458_);
lean_dec(v_ref_455_);
v___x_459_ = lean_box(0);
v___x_460_ = l_Lean_Elab_elabSetOption___redArg___lam__4(v_id_446_, v_val_447_, v_inst_448_, v_inst_449_, v_inst_450_, v_addInfo_451_, v_inst_452_, v_toBind_453_, v___f_456_, v_inst_454_, v___x_459_);
return v___x_460_;
}
else
{
lean_object* v___f_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
lean_dec_ref(v___f_456_);
lean_dec(v_inst_454_);
lean_dec(v_inst_450_);
lean_dec_ref(v_inst_449_);
lean_dec(v_val_447_);
lean_dec(v_id_446_);
v___f_461_ = lean_alloc_closure((void*)(l_Lean_Elab_elabSetOption___redArg___lam__2), 2, 1);
lean_closure_set(v___f_461_, 0, v___f_458_);
v___x_462_ = l_Lean_Syntax_getArgs(v_ref_455_);
v___x_463_ = lean_unsigned_to_nat(3u);
v___x_464_ = lean_unsigned_to_nat(0u);
v___x_465_ = l_Array_toSubarray___redArg(v___x_462_, v___x_464_, v___x_463_);
v___x_466_ = l_Subarray_copy___redArg(v___x_465_);
v___x_467_ = l_Lean_Syntax_setArgs(v_ref_455_, v___x_466_);
v___x_468_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_468_, 0, v___x_467_);
v___x_469_ = l_Lean_Elab_addCompletionInfo___redArg(v_inst_448_, v_inst_452_, v___x_468_);
v___x_470_ = lean_apply_4(v_toBind_453_, lean_box(0), lean_box(0), v___x_469_, v___f_461_);
return v___x_470_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg___lam__6___boxed(lean_object* v_id_471_, lean_object* v_val_472_, lean_object* v_inst_473_, lean_object* v_inst_474_, lean_object* v_inst_475_, lean_object* v_addInfo_476_, lean_object* v_inst_477_, lean_object* v_toBind_478_, lean_object* v_inst_479_, lean_object* v_ref_480_){
_start:
{
uint8_t v_addInfo_boxed_481_; lean_object* v_res_482_; 
v_addInfo_boxed_481_ = lean_unbox(v_addInfo_476_);
v_res_482_ = l_Lean_Elab_elabSetOption___redArg___lam__6(v_id_471_, v_val_472_, v_inst_473_, v_inst_474_, v_inst_475_, v_addInfo_boxed_481_, v_inst_477_, v_toBind_478_, v_inst_479_, v_ref_480_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg(lean_object* v_inst_483_, lean_object* v_inst_484_, lean_object* v_inst_485_, lean_object* v_inst_486_, lean_object* v_inst_487_, lean_object* v_id_488_, lean_object* v_val_489_, uint8_t v_addInfo_490_){
_start:
{
lean_object* v_toMonadRef_491_; lean_object* v_toBind_492_; lean_object* v_getRef_493_; lean_object* v___x_494_; lean_object* v___f_495_; lean_object* v___x_496_; 
v_toMonadRef_491_ = lean_ctor_get(v_inst_485_, 1);
v_toBind_492_ = lean_ctor_get(v_inst_483_, 1);
lean_inc_n(v_toBind_492_, 2);
v_getRef_493_ = lean_ctor_get(v_toMonadRef_491_, 0);
lean_inc(v_getRef_493_);
v___x_494_ = lean_box(v_addInfo_490_);
v___f_495_ = lean_alloc_closure((void*)(l_Lean_Elab_elabSetOption___redArg___lam__6___boxed), 10, 9);
lean_closure_set(v___f_495_, 0, v_id_488_);
lean_closure_set(v___f_495_, 1, v_val_489_);
lean_closure_set(v___f_495_, 2, v_inst_483_);
lean_closure_set(v___f_495_, 3, v_inst_485_);
lean_closure_set(v___f_495_, 4, v_inst_484_);
lean_closure_set(v___f_495_, 5, v___x_494_);
lean_closure_set(v___f_495_, 6, v_inst_487_);
lean_closure_set(v___f_495_, 7, v_toBind_492_);
lean_closure_set(v___f_495_, 8, v_inst_486_);
v___x_496_ = lean_apply_4(v_toBind_492_, lean_box(0), lean_box(0), v_getRef_493_, v___f_495_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg___boxed(lean_object* v_inst_497_, lean_object* v_inst_498_, lean_object* v_inst_499_, lean_object* v_inst_500_, lean_object* v_inst_501_, lean_object* v_id_502_, lean_object* v_val_503_, lean_object* v_addInfo_504_){
_start:
{
uint8_t v_addInfo_boxed_505_; lean_object* v_res_506_; 
v_addInfo_boxed_505_ = lean_unbox(v_addInfo_504_);
v_res_506_ = l_Lean_Elab_elabSetOption___redArg(v_inst_497_, v_inst_498_, v_inst_499_, v_inst_500_, v_inst_501_, v_id_502_, v_val_503_, v_addInfo_boxed_505_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption(lean_object* v_m_507_, lean_object* v_inst_508_, lean_object* v_inst_509_, lean_object* v_inst_510_, lean_object* v_inst_511_, lean_object* v_inst_512_, lean_object* v_id_513_, lean_object* v_val_514_, uint8_t v_addInfo_515_){
_start:
{
lean_object* v___x_516_; 
v___x_516_ = l_Lean_Elab_elabSetOption___redArg(v_inst_508_, v_inst_509_, v_inst_510_, v_inst_511_, v_inst_512_, v_id_513_, v_val_514_, v_addInfo_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___boxed(lean_object* v_m_517_, lean_object* v_inst_518_, lean_object* v_inst_519_, lean_object* v_inst_520_, lean_object* v_inst_521_, lean_object* v_inst_522_, lean_object* v_id_523_, lean_object* v_val_524_, lean_object* v_addInfo_525_){
_start:
{
uint8_t v_addInfo_boxed_526_; lean_object* v_res_527_; 
v_addInfo_boxed_526_ = lean_unbox(v_addInfo_525_);
v_res_527_ = l_Lean_Elab_elabSetOption(v_m_517_, v_inst_518_, v_inst_519_, v_inst_520_, v_inst_521_, v_inst_522_, v_id_523_, v_val_524_, v_addInfo_boxed_526_);
return v_res_527_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_529_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__0));
v___x_530_ = l_Lean_stringToMessageData(v___x_529_);
return v___x_530_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_532_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__2));
v___x_533_ = l_Lean_stringToMessageData(v___x_532_);
return v___x_533_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_535_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__4));
v___x_536_ = l_Lean_stringToMessageData(v___x_535_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedOption___redArg___lam__0(lean_object* v___x_537_, lean_object* v_toApplicative_538_, lean_object* v_decl_539_, lean_object* v_optionName_540_, lean_object* v_inst_541_, lean_object* v_inst_542_, lean_object* v_inst_543_, lean_object* v_inst_544_, lean_object* v_____do__lift_545_){
_start:
{
lean_object* v___y_547_; lean_object* v___x_555_; lean_object* v___x_556_; uint8_t v___x_557_; 
v___x_555_ = l_Lean_Elab_linter_deprecated_options;
v___x_556_ = l_Lean_Option_get___redArg(v___x_537_, v_____do__lift_545_, v___x_555_);
v___x_557_ = lean_unbox(v___x_556_);
lean_dec(v___x_556_);
if (v___x_557_ == 0)
{
lean_object* v_toPure_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
lean_dec(v_inst_544_);
lean_dec(v_inst_543_);
lean_dec_ref(v_inst_542_);
lean_dec_ref(v_inst_541_);
lean_dec(v_optionName_540_);
lean_dec_ref(v_decl_539_);
v_toPure_558_ = lean_ctor_get(v_toApplicative_538_, 1);
lean_inc(v_toPure_558_);
lean_dec_ref(v_toApplicative_538_);
v___x_559_ = lean_box(0);
v___x_560_ = lean_apply_2(v_toPure_558_, lean_box(0), v___x_559_);
return v___x_560_;
}
else
{
lean_object* v_deprecation_x3f_561_; 
v_deprecation_x3f_561_ = lean_ctor_get(v_decl_539_, 4);
lean_inc(v_deprecation_x3f_561_);
lean_dec_ref(v_decl_539_);
if (lean_obj_tag(v_deprecation_x3f_561_) == 1)
{
lean_object* v_val_562_; lean_object* v_text_x3f_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_574_; 
lean_dec_ref(v_toApplicative_538_);
v_val_562_ = lean_ctor_get(v_deprecation_x3f_561_, 0);
lean_inc(v_val_562_);
lean_dec_ref(v_deprecation_x3f_561_);
v_text_x3f_563_ = lean_ctor_get(v_val_562_, 1);
v_isSharedCheck_574_ = !lean_is_exclusive(v_val_562_);
if (v_isSharedCheck_574_ == 0)
{
lean_object* v_unused_575_; 
v_unused_575_ = lean_ctor_get(v_val_562_, 0);
lean_dec(v_unused_575_);
v___x_565_ = v_val_562_;
v_isShared_566_ = v_isSharedCheck_574_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_text_x3f_563_);
lean_dec(v_val_562_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_574_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
if (lean_obj_tag(v_text_x3f_563_) == 0)
{
lean_object* v___x_567_; 
lean_del_object(v___x_565_);
v___x_567_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__3, &l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__3_once, _init_l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__3);
v___y_547_ = v___x_567_;
goto v___jp_546_;
}
else
{
lean_object* v_val_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_572_; 
v_val_568_ = lean_ctor_get(v_text_x3f_563_, 0);
lean_inc(v_val_568_);
lean_dec_ref(v_text_x3f_563_);
v___x_569_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__5, &l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__5_once, _init_l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__5);
v___x_570_ = l_Lean_stringToMessageData(v_val_568_);
if (v_isShared_566_ == 0)
{
lean_ctor_set_tag(v___x_565_, 7);
lean_ctor_set(v___x_565_, 1, v___x_570_);
lean_ctor_set(v___x_565_, 0, v___x_569_);
v___x_572_ = v___x_565_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v___x_569_);
lean_ctor_set(v_reuseFailAlloc_573_, 1, v___x_570_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
v___y_547_ = v___x_572_;
goto v___jp_546_;
}
}
}
}
else
{
lean_object* v_toPure_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
lean_dec(v_deprecation_x3f_561_);
lean_dec(v_inst_544_);
lean_dec(v_inst_543_);
lean_dec_ref(v_inst_542_);
lean_dec_ref(v_inst_541_);
lean_dec(v_optionName_540_);
v_toPure_576_ = lean_ctor_get(v_toApplicative_538_, 1);
lean_inc(v_toPure_576_);
lean_dec_ref(v_toApplicative_538_);
v___x_577_ = lean_box(0);
v___x_578_ = lean_apply_2(v_toPure_576_, lean_box(0), v___x_577_);
return v___x_578_;
}
}
v___jp_546_:
{
lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_548_ = lean_obj_once(&l_Lean_Elab_elabSetOption___redArg___lam__1___closed__4, &l_Lean_Elab_elabSetOption___redArg___lam__1___closed__4_once, _init_l_Lean_Elab_elabSetOption___redArg___lam__1___closed__4);
v___x_549_ = l_Lean_MessageData_ofName(v_optionName_540_);
v___x_550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_550_, 0, v___x_548_);
lean_ctor_set(v___x_550_, 1, v___x_549_);
v___x_551_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__1, &l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__1);
v___x_552_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_552_, 0, v___x_550_);
lean_ctor_set(v___x_552_, 1, v___x_551_);
v___x_553_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_553_, 0, v___x_552_);
lean_ctor_set(v___x_553_, 1, v___y_547_);
v___x_554_ = l_Lean_logWarning___redArg(v_inst_541_, v_inst_542_, v_inst_543_, v_inst_544_, v___x_553_);
return v___x_554_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___boxed(lean_object* v___x_579_, lean_object* v_toApplicative_580_, lean_object* v_decl_581_, lean_object* v_optionName_582_, lean_object* v_inst_583_, lean_object* v_inst_584_, lean_object* v_inst_585_, lean_object* v_inst_586_, lean_object* v_____do__lift_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l_Lean_Elab_checkDeprecatedOption___redArg___lam__0(v___x_579_, v_toApplicative_580_, v_decl_581_, v_optionName_582_, v_inst_583_, v_inst_584_, v_inst_585_, v_inst_586_, v_____do__lift_587_);
lean_dec_ref(v_____do__lift_587_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedOption___redArg(lean_object* v_inst_589_, lean_object* v_inst_590_, lean_object* v_inst_591_, lean_object* v_inst_592_, lean_object* v_optionName_593_, lean_object* v_decl_594_){
_start:
{
lean_object* v___x_595_; lean_object* v_toApplicative_596_; lean_object* v_toBind_597_; lean_object* v___f_598_; lean_object* v___x_599_; 
v___x_595_ = l_Lean_KVMap_instValueBool;
v_toApplicative_596_ = lean_ctor_get(v_inst_589_, 0);
lean_inc_ref(v_toApplicative_596_);
v_toBind_597_ = lean_ctor_get(v_inst_589_, 1);
lean_inc(v_toBind_597_);
lean_inc(v_inst_590_);
v___f_598_ = lean_alloc_closure((void*)(l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___boxed), 9, 8);
lean_closure_set(v___f_598_, 0, v___x_595_);
lean_closure_set(v___f_598_, 1, v_toApplicative_596_);
lean_closure_set(v___f_598_, 2, v_decl_594_);
lean_closure_set(v___f_598_, 3, v_optionName_593_);
lean_closure_set(v___f_598_, 4, v_inst_589_);
lean_closure_set(v___f_598_, 5, v_inst_591_);
lean_closure_set(v___f_598_, 6, v_inst_592_);
lean_closure_set(v___f_598_, 7, v_inst_590_);
v___x_599_ = lean_apply_4(v_toBind_597_, lean_box(0), lean_box(0), v_inst_590_, v___f_598_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedOption(lean_object* v_m_600_, lean_object* v_inst_601_, lean_object* v_inst_602_, lean_object* v_inst_603_, lean_object* v_inst_604_, lean_object* v_optionName_605_, lean_object* v_decl_606_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = l_Lean_Elab_checkDeprecatedOption___redArg(v_inst_601_, v_inst_602_, v_inst_603_, v_inst_604_, v_optionName_605_, v_decl_606_);
return v___x_607_;
}
}
lean_object* runtime_initialize_Lean_Elab_InfoTree(uint8_t builtin);
lean_object* runtime_initialize_Init_Syntax(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_SetOption(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_InfoTree(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_linter_deprecated_options = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_linter_deprecated_options);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_SetOption(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_InfoTree(uint8_t builtin);
lean_object* initialize_Init_Syntax(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_SetOption(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_InfoTree(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_SetOption(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_SetOption(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_SetOption(builtin);
}
#ifdef __cplusplus
}
#endif

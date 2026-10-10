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
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Int_repr(lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
uint8_t l_Lean_DataValue_sameCtor(lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_Syntax_isStrLit_x3f(lean_object*);
lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_KVMap_instValueDataValue;
lean_object* l_Lean_Options_set___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_pushInfoLeaf___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* l_Lean_getOptionDecl___boxed(lean_object*, lean_object*);
lean_object* l_IO_toEIO___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "` has been deprecated"};
static const lean_object* l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__1;
static const lean_string_object l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__3;
static const lean_string_object l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = ": Use `"};
static const lean_object* l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__4_value;
static lean_once_cell_t l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__5;
static const lean_string_object l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` instead"};
static const lean_object* l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__6 = (const lean_object*)&l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__6_value;
static lean_once_cell_t l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__7;
static const lean_string_object l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__8 = (const lean_object*)&l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__8_value;
static lean_once_cell_t l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__9;
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedOption___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedOption___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedOption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_initFn_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
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
LEAN_EXPORT void l_Lean_Option_register___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_initFn_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1_ = stack[0].m_obj;
lean_object* v_decl_2_ = stack[1].m_obj;
lean_object* v_ref_3_ = stack[2].m_obj;
lean_object* v_res_29_;
v_res_29_ = l_Lean_Option_register___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_initFn_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__spec__0(v_name_1_, v_decl_2_, v_ref_3_);
stack->m_obj
 = v_res_29_;
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_initFn_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_30_, lean_object* v_decl_31_, lean_object* v_ref_32_, lean_object* v_a_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lean_Option_register___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_initFn_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__spec__0(v_name_30_, v_decl_31_, v_ref_32_);
lean_dec_ref(v_decl_31_);
return v_res_34_;
}
}
lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_57_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4_));
v___x_58_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4_));
v___x_59_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4_));
v___x_60_ = l_Lean_Option_register___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_initFn_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__spec__0(v___x_57_, v___x_58_, v___x_59_);
return v___x_60_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_61_;
v_res_61_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4_();
stack->m_obj
 = v_res_61_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4____boxed(lean_object* v_a_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4_();
return v_res_63_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg___closed__1(void){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_65_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg___closed__0));
v___x_66_ = l_Lean_stringToMessageData(v___x_65_);
return v___x_66_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg___closed__3(void){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_68_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg___closed__2));
v___x_69_ = l_Lean_stringToMessageData(v___x_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg(lean_object* v_inst_70_, lean_object* v_inst_71_, lean_object* v_optionName_72_){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_73_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg___closed__1, &l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg___closed__1_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg___closed__1);
v___x_74_ = l_Lean_MessageData_ofName(v_optionName_72_);
v___x_75_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_75_, 0, v___x_73_);
lean_ctor_set(v___x_75_, 1, v___x_74_);
v___x_76_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg___closed__3, &l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg___closed__3_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg___closed__3);
v___x_77_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_77_, 0, v___x_75_);
lean_ctor_set(v___x_77_, 1, v___x_76_);
v___x_78_ = l_Lean_throwError___redArg(v_inst_70_, v_inst_71_, v___x_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable(lean_object* v_m_79_, lean_object* v_inst_80_, lean_object* v_inst_81_, lean_object* v_00_u03b1_82_, lean_object* v_optionName_83_){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg(v_inst_80_, v_inst_81_, v_optionName_83_);
return v___x_84_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__2(void){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_88_ = lean_box(0);
v___x_89_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__1));
v___x_90_ = l_Lean_mkConst(v___x_89_, v___x_88_);
return v___x_90_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__3(void){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_91_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__2, &l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__2_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__2);
v___x_92_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_92_, 0, v___x_91_);
return v___x_92_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__6(void){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_96_ = lean_box(0);
v___x_97_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__5));
v___x_98_ = l_Lean_mkConst(v___x_97_, v___x_96_);
return v___x_98_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__7(void){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_99_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__6, &l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__6_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__6);
v___x_100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_100_, 0, v___x_99_);
return v___x_100_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__10(void){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_104_ = lean_box(0);
v___x_105_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__9));
v___x_106_ = l_Lean_mkConst(v___x_105_, v___x_104_);
return v___x_106_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__11(void){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_107_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__10, &l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__10_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__10);
v___x_108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_108_, 0, v___x_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f(lean_object* v_x_109_){
_start:
{
switch(lean_obj_tag(v_x_109_))
{
case 0:
{
lean_object* v___x_110_; 
v___x_110_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__3, &l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__3_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__3);
return v___x_110_;
}
case 1:
{
lean_object* v___x_111_; 
v___x_111_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__7, &l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__7_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__7);
return v___x_111_;
}
case 3:
{
lean_object* v___x_112_; 
v___x_112_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__11, &l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__11_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__11);
return v___x_112_;
}
default: 
{
lean_object* v___x_113_; 
v___x_113_ = lean_box(0);
return v___x_113_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___boxed(lean_object* v_x_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f(v_x_114_);
lean_dec_ref(v_x_114_);
return v_res_115_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__1(void){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_117_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__0));
v___x_118_ = l_Lean_stringToMessageData(v___x_117_);
return v___x_118_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__3(void){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_120_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__2));
v___x_121_ = l_Lean_stringToMessageData(v___x_120_);
return v___x_121_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__5(void){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_123_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__4));
v___x_124_ = l_Lean_stringToMessageData(v___x_123_);
return v___x_124_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__7(void){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_126_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__6));
v___x_127_ = l_Lean_stringToMessageData(v___x_126_);
return v___x_127_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__17(void){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_140_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__16));
v___x_141_ = lean_unsigned_to_nat(14u);
v___x_142_ = lean_unsigned_to_nat(22u);
v___x_143_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__15));
v___x_144_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__14));
v___x_145_ = l_mkPanicMessageWithDecl(v___x_144_, v___x_143_, v___x_142_, v___x_141_, v___x_140_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg(lean_object* v_inst_146_, lean_object* v_inst_147_, lean_object* v_optionName_148_, lean_object* v_found_149_, lean_object* v_defVal_150_){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f(v_defVal_150_);
if (lean_obj_tag(v___x_151_) == 1)
{
lean_object* v_val_152_; lean_object* v___y_154_; lean_object* v___y_155_; lean_object* v___y_156_; lean_object* v___y_175_; lean_object* v___x_223_; 
v_val_152_ = lean_ctor_get(v___x_151_, 0);
lean_inc(v_val_152_);
lean_dec_ref_known(v___x_151_, 1);
v___x_223_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f(v_found_149_);
if (lean_obj_tag(v___x_223_) == 0)
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_224_ = l_Lean_instInhabitedExpr;
v___x_225_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__17, &l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__17_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__17);
v___x_226_ = l_panic___redArg(v___x_224_, v___x_225_);
v___y_175_ = v___x_226_;
goto v___jp_174_;
}
else
{
lean_object* v_val_227_; 
v_val_227_ = lean_ctor_get(v___x_223_, 0);
lean_inc(v_val_227_);
lean_dec_ref_known(v___x_223_, 1);
v___y_175_ = v_val_227_;
goto v___jp_174_;
}
v___jp_153_:
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_157_ = l_Lean_MessageData_ofFormat(v___y_156_);
v___x_158_ = l_Lean_indentD(v___x_157_);
lean_inc_ref(v___y_155_);
v___x_159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_159_, 0, v___y_155_);
lean_ctor_set(v___x_159_, 1, v___x_158_);
v___x_160_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__1, &l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__1_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__1);
v___x_161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_161_, 0, v___x_159_);
lean_ctor_set(v___x_161_, 1, v___x_160_);
v___x_162_ = l_Lean_MessageData_ofExpr(v___y_154_);
v___x_163_ = l_Lean_indentD(v___x_162_);
v___x_164_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_164_, 0, v___x_161_);
lean_ctor_set(v___x_164_, 1, v___x_163_);
v___x_165_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__3, &l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__3_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__3);
v___x_166_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_166_, 0, v___x_164_);
lean_ctor_set(v___x_166_, 1, v___x_165_);
v___x_167_ = l_Lean_MessageData_ofName(v_optionName_148_);
v___x_168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_168_, 0, v___x_166_);
lean_ctor_set(v___x_168_, 1, v___x_167_);
v___x_169_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__5, &l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__5_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__5);
v___x_170_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_170_, 0, v___x_168_);
lean_ctor_set(v___x_170_, 1, v___x_169_);
v___x_171_ = l_Lean_indentExpr(v_val_152_);
v___x_172_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_172_, 0, v___x_170_);
lean_ctor_set(v___x_172_, 1, v___x_171_);
v___x_173_ = l_Lean_throwError___redArg(v_inst_146_, v_inst_147_, v___x_172_);
return v___x_173_;
}
v___jp_174_:
{
lean_object* v___x_176_; 
v___x_176_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__7, &l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__7_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__7);
switch(lean_obj_tag(v_found_149_))
{
case 0:
{
lean_object* v_v_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_185_; 
v_v_177_ = lean_ctor_get(v_found_149_, 0);
v_isSharedCheck_185_ = !lean_is_exclusive(v_found_149_);
if (v_isSharedCheck_185_ == 0)
{
v___x_179_ = v_found_149_;
v_isShared_180_ = v_isSharedCheck_185_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_v_177_);
lean_dec(v_found_149_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_185_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v___x_181_; lean_object* v___x_183_; 
v___x_181_ = l_String_quote(v_v_177_);
if (v_isShared_180_ == 0)
{
lean_ctor_set_tag(v___x_179_, 3);
lean_ctor_set(v___x_179_, 0, v___x_181_);
v___x_183_ = v___x_179_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v___x_181_);
v___x_183_ = v_reuseFailAlloc_184_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
v___y_154_ = v___y_175_;
v___y_155_ = v___x_176_;
v___y_156_ = v___x_183_;
goto v___jp_153_;
}
}
}
case 1:
{
uint8_t v_v_186_; 
v_v_186_ = lean_ctor_get_uint8(v_found_149_, 0);
lean_dec_ref_known(v_found_149_, 0);
if (v_v_186_ == 0)
{
lean_object* v___x_187_; 
v___x_187_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__9));
v___y_154_ = v___y_175_;
v___y_155_ = v___x_176_;
v___y_156_ = v___x_187_;
goto v___jp_153_;
}
else
{
lean_object* v___x_188_; 
v___x_188_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__11));
v___y_154_ = v___y_175_;
v___y_155_ = v___x_176_;
v___y_156_ = v___x_188_;
goto v___jp_153_;
}
}
case 2:
{
lean_object* v_v_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_200_; 
v_v_189_ = lean_ctor_get(v_found_149_, 0);
v_isSharedCheck_200_ = !lean_is_exclusive(v_found_149_);
if (v_isSharedCheck_200_ == 0)
{
v___x_191_ = v_found_149_;
v_isShared_192_ = v_isSharedCheck_200_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_v_189_);
lean_dec(v_found_149_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_200_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_193_; uint8_t v___x_194_; lean_object* v___x_195_; lean_object* v___x_197_; 
v___x_193_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__13));
v___x_194_ = 1;
v___x_195_ = l_Lean_Name_toString(v_v_189_, v___x_194_);
if (v_isShared_192_ == 0)
{
lean_ctor_set_tag(v___x_191_, 3);
lean_ctor_set(v___x_191_, 0, v___x_195_);
v___x_197_ = v___x_191_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v___x_195_);
v___x_197_ = v_reuseFailAlloc_199_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
lean_object* v___x_198_; 
v___x_198_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_198_, 0, v___x_193_);
lean_ctor_set(v___x_198_, 1, v___x_197_);
v___y_154_ = v___y_175_;
v___y_155_ = v___x_176_;
v___y_156_ = v___x_198_;
goto v___jp_153_;
}
}
}
case 3:
{
lean_object* v_v_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_209_; 
v_v_201_ = lean_ctor_get(v_found_149_, 0);
v_isSharedCheck_209_ = !lean_is_exclusive(v_found_149_);
if (v_isSharedCheck_209_ == 0)
{
v___x_203_ = v_found_149_;
v_isShared_204_ = v_isSharedCheck_209_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_v_201_);
lean_dec(v_found_149_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_209_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_205_; lean_object* v___x_207_; 
v___x_205_ = l_Nat_reprFast(v_v_201_);
if (v_isShared_204_ == 0)
{
lean_ctor_set(v___x_203_, 0, v___x_205_);
v___x_207_ = v___x_203_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v___x_205_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
v___y_154_ = v___y_175_;
v___y_155_ = v___x_176_;
v___y_156_ = v___x_207_;
goto v___jp_153_;
}
}
}
case 4:
{
lean_object* v_v_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_218_; 
v_v_210_ = lean_ctor_get(v_found_149_, 0);
v_isSharedCheck_218_ = !lean_is_exclusive(v_found_149_);
if (v_isSharedCheck_218_ == 0)
{
v___x_212_ = v_found_149_;
v_isShared_213_ = v_isSharedCheck_218_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_v_210_);
lean_dec(v_found_149_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_218_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___x_214_; lean_object* v___x_216_; 
v___x_214_ = l_Int_repr(v_v_210_);
lean_dec(v_v_210_);
if (v_isShared_213_ == 0)
{
lean_ctor_set_tag(v___x_212_, 3);
lean_ctor_set(v___x_212_, 0, v___x_214_);
v___x_216_ = v___x_212_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v___x_214_);
v___x_216_ = v_reuseFailAlloc_217_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
v___y_154_ = v___y_175_;
v___y_155_ = v___x_176_;
v___y_156_ = v___x_216_;
goto v___jp_153_;
}
}
}
default: 
{
lean_object* v_v_219_; lean_object* v___x_220_; uint8_t v___x_221_; lean_object* v___x_222_; 
v_v_219_ = lean_ctor_get(v_found_149_, 0);
lean_inc(v_v_219_);
lean_dec_ref_known(v_found_149_, 1);
v___x_220_ = lean_box(0);
v___x_221_ = 0;
v___x_222_ = l_Lean_Syntax_formatStx(v_v_219_, v___x_220_, v___x_221_);
v___y_154_ = v___y_175_;
v___y_155_ = v___x_176_;
v___y_156_ = v___x_222_;
goto v___jp_153_;
}
}
}
}
else
{
lean_object* v___x_228_; 
lean_dec(v___x_151_);
lean_dec_ref(v_found_149_);
v___x_228_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg(v_inst_146_, v_inst_147_, v_optionName_148_);
return v___x_228_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___boxed(lean_object* v_inst_229_, lean_object* v_inst_230_, lean_object* v_optionName_231_, lean_object* v_found_232_, lean_object* v_defVal_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg(v_inst_229_, v_inst_230_, v_optionName_231_, v_found_232_, v_defVal_233_);
lean_dec_ref(v_defVal_233_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue(lean_object* v_m_235_, lean_object* v_inst_236_, lean_object* v_inst_237_, lean_object* v_optionName_238_, lean_object* v_found_239_, lean_object* v_defVal_240_){
_start:
{
lean_object* v___x_241_; 
v___x_241_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg(v_inst_236_, v_inst_237_, v_optionName_238_, v_found_239_, v_defVal_240_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___boxed(lean_object* v_m_242_, lean_object* v_inst_243_, lean_object* v_inst_244_, lean_object* v_optionName_245_, lean_object* v_found_246_, lean_object* v_defVal_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue(v_m_242_, v_inst_243_, v_inst_244_, v_optionName_245_, v_found_246_, v_defVal_247_);
lean_dec_ref(v_defVal_247_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_validateOptionValue___redArg(lean_object* v_inst_249_, lean_object* v_inst_250_, lean_object* v_optionName_251_, lean_object* v_decl_252_, lean_object* v_val_253_){
_start:
{
lean_object* v_toApplicative_254_; lean_object* v_defValue_255_; lean_object* v_toPure_256_; uint8_t v___x_257_; 
v_toApplicative_254_ = lean_ctor_get(v_inst_249_, 0);
v_defValue_255_ = lean_ctor_get(v_decl_252_, 2);
v_toPure_256_ = lean_ctor_get(v_toApplicative_254_, 1);
v___x_257_ = l_Lean_DataValue_sameCtor(v_defValue_255_, v_val_253_);
if (v___x_257_ == 0)
{
lean_object* v___x_258_; 
v___x_258_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg(v_inst_249_, v_inst_250_, v_optionName_251_, v_val_253_, v_defValue_255_);
return v___x_258_;
}
else
{
lean_object* v___x_259_; lean_object* v___x_260_; 
lean_inc(v_toPure_256_);
lean_dec_ref(v_val_253_);
lean_dec(v_optionName_251_);
lean_dec_ref(v_inst_250_);
lean_dec_ref(v_inst_249_);
v___x_259_ = lean_box(0);
v___x_260_ = lean_apply_2(v_toPure_256_, lean_box(0), v___x_259_);
return v___x_260_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_validateOptionValue___redArg___boxed(lean_object* v_inst_261_, lean_object* v_inst_262_, lean_object* v_optionName_263_, lean_object* v_decl_264_, lean_object* v_val_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Lean_Elab_validateOptionValue___redArg(v_inst_261_, v_inst_262_, v_optionName_263_, v_decl_264_, v_val_265_);
lean_dec_ref(v_decl_264_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_validateOptionValue(lean_object* v_m_267_, lean_object* v_inst_268_, lean_object* v_inst_269_, lean_object* v_optionName_270_, lean_object* v_decl_271_, lean_object* v_val_272_){
_start:
{
lean_object* v___x_273_; 
v___x_273_ = l_Lean_Elab_validateOptionValue___redArg(v_inst_268_, v_inst_269_, v_optionName_270_, v_decl_271_, v_val_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_validateOptionValue___boxed(lean_object* v_m_274_, lean_object* v_inst_275_, lean_object* v_inst_276_, lean_object* v_optionName_277_, lean_object* v_decl_278_, lean_object* v_val_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Lean_Elab_validateOptionValue(v_m_274_, v_inst_275_, v_inst_276_, v_optionName_277_, v_decl_278_, v_val_279_);
lean_dec_ref(v_decl_278_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___redArg___lam__0(lean_object* v___x_281_, lean_object* v_optionName_282_, lean_object* v_val_283_, lean_object* v_decl_284_, lean_object* v_toPure_285_, lean_object* v_____do__lift_286_){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_287_ = l_Lean_Options_set___redArg(v___x_281_, v_____do__lift_286_, v_optionName_282_, v_val_283_);
v___x_288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_287_);
lean_ctor_set(v___x_288_, 1, v_decl_284_);
v___x_289_ = lean_apply_2(v_toPure_285_, lean_box(0), v___x_288_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___redArg___lam__1(lean_object* v_inst_290_, lean_object* v_toBind_291_, lean_object* v___f_292_, lean_object* v_____r_293_){
_start:
{
lean_object* v_getOptions_294_; lean_object* v___x_295_; 
v_getOptions_294_ = lean_ctor_get(v_inst_290_, 0);
lean_inc(v_getOptions_294_);
lean_dec_ref(v_inst_290_);
v___x_295_ = lean_apply_4(v_toBind_291_, lean_box(0), lean_box(0), v_getOptions_294_, v___f_292_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___redArg(lean_object* v_inst_296_, lean_object* v_inst_297_, lean_object* v_inst_298_, lean_object* v_optionName_299_, lean_object* v_decl_300_, lean_object* v_val_301_){
_start:
{
lean_object* v___x_302_; lean_object* v_toApplicative_303_; lean_object* v_toBind_304_; lean_object* v_toPure_305_; lean_object* v___x_306_; lean_object* v___f_307_; lean_object* v___f_308_; lean_object* v___x_309_; 
v___x_302_ = l_Lean_KVMap_instValueDataValue;
v_toApplicative_303_ = lean_ctor_get(v_inst_296_, 0);
v_toBind_304_ = lean_ctor_get(v_inst_296_, 1);
lean_inc_n(v_toBind_304_, 2);
v_toPure_305_ = lean_ctor_get(v_toApplicative_303_, 1);
lean_inc(v_toPure_305_);
lean_inc_ref(v_val_301_);
lean_inc(v_optionName_299_);
v___x_306_ = l_Lean_Elab_validateOptionValue___redArg(v_inst_296_, v_inst_298_, v_optionName_299_, v_decl_300_, v_val_301_);
v___f_307_ = lean_alloc_closure((void*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___redArg___lam__0), 6, 5);
lean_closure_set(v___f_307_, 0, v___x_302_);
lean_closure_set(v___f_307_, 1, v_optionName_299_);
lean_closure_set(v___f_307_, 2, v_val_301_);
lean_closure_set(v___f_307_, 3, v_decl_300_);
lean_closure_set(v___f_307_, 4, v_toPure_305_);
v___f_308_ = lean_alloc_closure((void*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___redArg___lam__1), 4, 3);
lean_closure_set(v___f_308_, 0, v_inst_297_);
lean_closure_set(v___f_308_, 1, v_toBind_304_);
lean_closure_set(v___f_308_, 2, v___f_307_);
v___x_309_ = lean_apply_4(v_toBind_304_, lean_box(0), lean_box(0), v___x_306_, v___f_308_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption(lean_object* v_m_310_, lean_object* v_inst_311_, lean_object* v_inst_312_, lean_object* v_inst_313_, lean_object* v_optionName_314_, lean_object* v_decl_315_, lean_object* v_val_316_){
_start:
{
lean_object* v___x_317_; 
v___x_317_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___redArg(v_inst_311_, v_inst_312_, v_inst_313_, v_optionName_314_, v_decl_315_, v_val_316_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg___lam__0(lean_object* v_ref_318_, lean_object* v_ex_319_){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_320_ = lean_io_error_to_string(v_ex_319_);
v___x_321_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_321_, 0, v___x_320_);
v___x_322_ = l_Lean_MessageData_ofFormat(v___x_321_);
v___x_323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_323_, 0, v_ref_318_);
lean_ctor_set(v___x_323_, 1, v___x_322_);
return v___x_323_;
}
}
static lean_object* _init_l_Lean_Elab_elabSetOption___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_325_ = ((lean_object*)(l_Lean_Elab_elabSetOption___redArg___lam__1___closed__0));
v___x_326_ = l_Lean_stringToMessageData(v___x_325_);
return v___x_326_;
}
}
static lean_object* _init_l_Lean_Elab_elabSetOption___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_328_ = ((lean_object*)(l_Lean_Elab_elabSetOption___redArg___lam__1___closed__2));
v___x_329_ = l_Lean_stringToMessageData(v___x_328_);
return v___x_329_;
}
}
static lean_object* _init_l_Lean_Elab_elabSetOption___redArg___lam__1___closed__4(void){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_330_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__12));
v___x_331_ = l_Lean_stringToMessageData(v___x_330_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg___lam__1(lean_object* v_val_332_, lean_object* v_defValue_333_, lean_object* v_inst_334_, lean_object* v_inst_335_, lean_object* v_optionName_336_, lean_object* v_inst_337_, lean_object* v_decl_338_, lean_object* v_____r_339_){
_start:
{
lean_object* v___x_354_; 
v___x_354_ = l_Lean_Syntax_isStrLit_x3f(v_val_332_);
if (lean_obj_tag(v___x_354_) == 0)
{
lean_object* v___x_355_; 
v___x_355_ = l_Lean_Syntax_isNatLit_x3f(v_val_332_);
if (lean_obj_tag(v___x_355_) == 0)
{
if (lean_obj_tag(v_val_332_) == 2)
{
lean_object* v_val_356_; lean_object* v___x_357_; uint8_t v___x_358_; 
v_val_356_ = lean_ctor_get(v_val_332_, 1);
v___x_357_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__10));
v___x_358_ = lean_string_dec_eq(v_val_356_, v___x_357_);
if (v___x_358_ == 0)
{
lean_object* v___x_359_; uint8_t v___x_360_; 
v___x_359_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__8));
v___x_360_ = lean_string_dec_eq(v_val_356_, v___x_359_);
if (v___x_360_ == 0)
{
lean_dec_ref(v_decl_338_);
lean_dec_ref(v_inst_337_);
goto v___jp_340_;
}
else
{
lean_object* v___x_361_; lean_object* v___x_362_; 
lean_dec_ref_known(v_val_332_, 2);
v___x_361_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_361_, 0, v___x_358_);
v___x_362_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___redArg(v_inst_334_, v_inst_337_, v_inst_335_, v_optionName_336_, v_decl_338_, v___x_361_);
return v___x_362_;
}
}
else
{
lean_object* v___x_363_; lean_object* v___x_364_; 
lean_dec_ref_known(v_val_332_, 2);
v___x_363_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_363_, 0, v___x_358_);
v___x_364_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___redArg(v_inst_334_, v_inst_337_, v_inst_335_, v_optionName_336_, v_decl_338_, v___x_363_);
return v___x_364_;
}
}
else
{
lean_dec_ref(v_decl_338_);
lean_dec_ref(v_inst_337_);
goto v___jp_340_;
}
}
else
{
lean_object* v_val_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_373_; 
lean_dec(v_val_332_);
v_val_365_ = lean_ctor_get(v___x_355_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_373_ == 0)
{
v___x_367_ = v___x_355_;
v_isShared_368_ = v_isSharedCheck_373_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_val_365_);
lean_dec(v___x_355_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_373_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v___x_370_; 
if (v_isShared_368_ == 0)
{
lean_ctor_set_tag(v___x_367_, 3);
v___x_370_ = v___x_367_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_val_365_);
v___x_370_ = v_reuseFailAlloc_372_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
lean_object* v___x_371_; 
v___x_371_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___redArg(v_inst_334_, v_inst_337_, v_inst_335_, v_optionName_336_, v_decl_338_, v___x_370_);
return v___x_371_;
}
}
}
}
else
{
lean_object* v_val_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_382_; 
lean_dec(v_val_332_);
v_val_374_ = lean_ctor_get(v___x_354_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_354_);
if (v_isSharedCheck_382_ == 0)
{
v___x_376_ = v___x_354_;
v_isShared_377_ = v_isSharedCheck_382_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_val_374_);
lean_dec(v___x_354_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_382_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_379_; 
if (v_isShared_377_ == 0)
{
lean_ctor_set_tag(v___x_376_, 0);
v___x_379_ = v___x_376_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_val_374_);
v___x_379_ = v_reuseFailAlloc_381_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
lean_object* v___x_380_; 
v___x_380_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___redArg(v_inst_334_, v_inst_337_, v_inst_335_, v_optionName_336_, v_decl_338_, v___x_379_);
return v___x_380_;
}
}
}
v___jp_340_:
{
lean_object* v___x_341_; 
v___x_341_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f(v_defValue_333_);
if (lean_obj_tag(v___x_341_) == 1)
{
lean_object* v_val_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
lean_dec(v_optionName_336_);
v_val_342_ = lean_ctor_get(v___x_341_, 0);
lean_inc(v_val_342_);
lean_dec_ref_known(v___x_341_, 1);
v___x_343_ = lean_obj_once(&l_Lean_Elab_elabSetOption___redArg___lam__1___closed__1, &l_Lean_Elab_elabSetOption___redArg___lam__1___closed__1_once, _init_l_Lean_Elab_elabSetOption___redArg___lam__1___closed__1);
v___x_344_ = l_Lean_MessageData_ofSyntax(v_val_332_);
v___x_345_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_343_);
lean_ctor_set(v___x_345_, 1, v___x_344_);
v___x_346_ = lean_obj_once(&l_Lean_Elab_elabSetOption___redArg___lam__1___closed__3, &l_Lean_Elab_elabSetOption___redArg___lam__1___closed__3_once, _init_l_Lean_Elab_elabSetOption___redArg___lam__1___closed__3);
v___x_347_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_347_, 0, v___x_345_);
lean_ctor_set(v___x_347_, 1, v___x_346_);
v___x_348_ = l_Lean_MessageData_ofExpr(v_val_342_);
v___x_349_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_349_, 0, v___x_347_);
lean_ctor_set(v___x_349_, 1, v___x_348_);
v___x_350_ = lean_obj_once(&l_Lean_Elab_elabSetOption___redArg___lam__1___closed__4, &l_Lean_Elab_elabSetOption___redArg___lam__1___closed__4_once, _init_l_Lean_Elab_elabSetOption___redArg___lam__1___closed__4);
v___x_351_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_351_, 0, v___x_349_);
lean_ctor_set(v___x_351_, 1, v___x_350_);
v___x_352_ = l_Lean_throwError___redArg(v_inst_334_, v_inst_335_, v___x_351_);
return v___x_352_;
}
else
{
lean_object* v___x_353_; 
lean_dec(v___x_341_);
lean_dec(v_val_332_);
v___x_353_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg(v_inst_334_, v_inst_335_, v_optionName_336_);
return v___x_353_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg___lam__1___boxed(lean_object* v_val_383_, lean_object* v_defValue_384_, lean_object* v_inst_385_, lean_object* v_inst_386_, lean_object* v_optionName_387_, lean_object* v_inst_388_, lean_object* v_decl_389_, lean_object* v_____r_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l_Lean_Elab_elabSetOption___redArg___lam__1(v_val_383_, v_defValue_384_, v_inst_385_, v_inst_386_, v_optionName_387_, v_inst_388_, v_decl_389_, v_____r_390_);
lean_dec_ref(v_defValue_384_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg___lam__2(lean_object* v_val_392_, lean_object* v_inst_393_, lean_object* v_inst_394_, lean_object* v_optionName_395_, lean_object* v_inst_396_, lean_object* v_id_397_, lean_object* v_inst_398_, lean_object* v_toBind_399_, lean_object* v_decl_400_){
_start:
{
lean_object* v_declName_401_; lean_object* v_defValue_402_; lean_object* v___f_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v_declName_401_ = lean_ctor_get(v_decl_400_, 1);
lean_inc(v_declName_401_);
v_defValue_402_ = lean_ctor_get(v_decl_400_, 2);
lean_inc_ref(v_defValue_402_);
lean_inc(v_optionName_395_);
lean_inc_ref(v_inst_393_);
v___f_403_ = lean_alloc_closure((void*)(l_Lean_Elab_elabSetOption___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_403_, 0, v_val_392_);
lean_closure_set(v___f_403_, 1, v_defValue_402_);
lean_closure_set(v___f_403_, 2, v_inst_393_);
lean_closure_set(v___f_403_, 3, v_inst_394_);
lean_closure_set(v___f_403_, 4, v_optionName_395_);
lean_closure_set(v___f_403_, 5, v_inst_396_);
lean_closure_set(v___f_403_, 6, v_decl_400_);
v___x_404_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_404_, 0, v_id_397_);
lean_ctor_set(v___x_404_, 1, v_optionName_395_);
lean_ctor_set(v___x_404_, 2, v_declName_401_);
v___x_405_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_405_, 0, v___x_404_);
v___x_406_ = l_Lean_Elab_pushInfoLeaf___redArg(v_inst_393_, v_inst_398_, v___x_405_);
v___x_407_ = lean_apply_4(v_toBind_399_, lean_box(0), lean_box(0), v___x_406_, v___f_403_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg___lam__3(lean_object* v_id_408_, lean_object* v_val_409_, lean_object* v_inst_410_, lean_object* v_inst_411_, lean_object* v_inst_412_, lean_object* v_inst_413_, lean_object* v_toBind_414_, lean_object* v___f_415_, lean_object* v_inst_416_, lean_object* v_____r_417_){
_start:
{
lean_object* v___x_418_; lean_object* v_optionName_419_; lean_object* v___f_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_418_ = l_Lean_Syntax_getId(v_id_408_);
v_optionName_419_ = l_Lean_Name_eraseMacroScopes(v___x_418_);
lean_dec(v___x_418_);
lean_inc(v_toBind_414_);
lean_inc(v_optionName_419_);
v___f_420_ = lean_alloc_closure((void*)(l_Lean_Elab_elabSetOption___redArg___lam__2), 9, 8);
lean_closure_set(v___f_420_, 0, v_val_409_);
lean_closure_set(v___f_420_, 1, v_inst_410_);
lean_closure_set(v___f_420_, 2, v_inst_411_);
lean_closure_set(v___f_420_, 3, v_optionName_419_);
lean_closure_set(v___f_420_, 4, v_inst_412_);
lean_closure_set(v___f_420_, 5, v_id_408_);
lean_closure_set(v___f_420_, 6, v_inst_413_);
lean_closure_set(v___f_420_, 7, v_toBind_414_);
v___x_421_ = lean_alloc_closure((void*)(l_Lean_getOptionDecl___boxed), 2, 1);
lean_closure_set(v___x_421_, 0, v_optionName_419_);
v___x_422_ = lean_alloc_closure((void*)(l_IO_toEIO___boxed), 5, 4);
lean_closure_set(v___x_422_, 0, lean_box(0));
lean_closure_set(v___x_422_, 1, lean_box(0));
lean_closure_set(v___x_422_, 2, v___f_415_);
lean_closure_set(v___x_422_, 3, v___x_421_);
v___x_423_ = lean_apply_2(v_inst_416_, lean_box(0), v___x_422_);
v___x_424_ = lean_apply_4(v_toBind_414_, lean_box(0), lean_box(0), v___x_423_, v___f_420_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg___lam__4(lean_object* v_id_425_, lean_object* v_val_426_, lean_object* v_inst_427_, lean_object* v_inst_428_, lean_object* v_inst_429_, lean_object* v_inst_430_, lean_object* v_toBind_431_, lean_object* v_inst_432_, lean_object* v_ref_433_){
_start:
{
lean_object* v___f_434_; lean_object* v___f_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
lean_inc(v_ref_433_);
v___f_434_ = lean_alloc_closure((void*)(l_Lean_Elab_elabSetOption___redArg___lam__0), 2, 1);
lean_closure_set(v___f_434_, 0, v_ref_433_);
lean_inc(v_toBind_431_);
lean_inc_ref(v_inst_430_);
lean_inc_ref(v_inst_427_);
v___f_435_ = lean_alloc_closure((void*)(l_Lean_Elab_elabSetOption___redArg___lam__3), 10, 9);
lean_closure_set(v___f_435_, 0, v_id_425_);
lean_closure_set(v___f_435_, 1, v_val_426_);
lean_closure_set(v___f_435_, 2, v_inst_427_);
lean_closure_set(v___f_435_, 3, v_inst_428_);
lean_closure_set(v___f_435_, 4, v_inst_429_);
lean_closure_set(v___f_435_, 5, v_inst_430_);
lean_closure_set(v___f_435_, 6, v_toBind_431_);
lean_closure_set(v___f_435_, 7, v___f_434_);
lean_closure_set(v___f_435_, 8, v_inst_432_);
v___x_436_ = l_Lean_Syntax_getArgs(v_ref_433_);
v___x_437_ = lean_unsigned_to_nat(3u);
v___x_438_ = lean_unsigned_to_nat(0u);
v___x_439_ = l_Array_toSubarray___redArg(v___x_436_, v___x_438_, v___x_437_);
v___x_440_ = l_Subarray_copy___redArg(v___x_439_);
v___x_441_ = l_Lean_Syntax_setArgs(v_ref_433_, v___x_440_);
v___x_442_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_442_, 0, v___x_441_);
v___x_443_ = l_Lean_Elab_addCompletionInfo___redArg(v_inst_427_, v_inst_430_, v___x_442_);
v___x_444_ = lean_apply_4(v_toBind_431_, lean_box(0), lean_box(0), v___x_443_, v___f_435_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg(lean_object* v_inst_445_, lean_object* v_inst_446_, lean_object* v_inst_447_, lean_object* v_inst_448_, lean_object* v_inst_449_, lean_object* v_id_450_, lean_object* v_val_451_){
_start:
{
lean_object* v_toMonadRef_452_; lean_object* v_toBind_453_; lean_object* v_getRef_454_; lean_object* v___f_455_; lean_object* v___x_456_; 
v_toMonadRef_452_ = lean_ctor_get(v_inst_447_, 1);
v_toBind_453_ = lean_ctor_get(v_inst_445_, 1);
lean_inc_n(v_toBind_453_, 2);
v_getRef_454_ = lean_ctor_get(v_toMonadRef_452_, 0);
lean_inc(v_getRef_454_);
v___f_455_ = lean_alloc_closure((void*)(l_Lean_Elab_elabSetOption___redArg___lam__4), 9, 8);
lean_closure_set(v___f_455_, 0, v_id_450_);
lean_closure_set(v___f_455_, 1, v_val_451_);
lean_closure_set(v___f_455_, 2, v_inst_445_);
lean_closure_set(v___f_455_, 3, v_inst_447_);
lean_closure_set(v___f_455_, 4, v_inst_446_);
lean_closure_set(v___f_455_, 5, v_inst_449_);
lean_closure_set(v___f_455_, 6, v_toBind_453_);
lean_closure_set(v___f_455_, 7, v_inst_448_);
v___x_456_ = lean_apply_4(v_toBind_453_, lean_box(0), lean_box(0), v_getRef_454_, v___f_455_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption(lean_object* v_m_457_, lean_object* v_inst_458_, lean_object* v_inst_459_, lean_object* v_inst_460_, lean_object* v_inst_461_, lean_object* v_inst_462_, lean_object* v_id_463_, lean_object* v_val_464_){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = l_Lean_Elab_elabSetOption___redArg(v_inst_458_, v_inst_459_, v_inst_460_, v_inst_461_, v_inst_462_, v_id_463_, v_val_464_);
return v___x_465_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_467_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__0));
v___x_468_ = l_Lean_stringToMessageData(v___x_467_);
return v___x_468_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_470_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__2));
v___x_471_ = l_Lean_stringToMessageData(v___x_470_);
return v___x_471_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_473_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__4));
v___x_474_ = l_Lean_stringToMessageData(v___x_473_);
return v___x_474_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__7(void){
_start:
{
lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_476_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__6));
v___x_477_ = l_Lean_stringToMessageData(v___x_476_);
return v___x_477_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__9(void){
_start:
{
lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_479_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__8));
v___x_480_ = l_Lean_stringToMessageData(v___x_479_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedOption___redArg___lam__0(lean_object* v___x_481_, lean_object* v_toPure_482_, lean_object* v_decl_483_, lean_object* v_optionName_484_, lean_object* v_inst_485_, lean_object* v_inst_486_, lean_object* v_inst_487_, lean_object* v_inst_488_, lean_object* v_____do__lift_489_){
_start:
{
lean_object* v___y_491_; lean_object* v___x_499_; lean_object* v___x_500_; uint8_t v___x_501_; 
v___x_499_ = l_Lean_Elab_linter_deprecated_options;
v___x_500_ = l_Lean_Option_get___redArg(v___x_481_, v_____do__lift_489_, v___x_499_);
v___x_501_ = lean_unbox(v___x_500_);
lean_dec(v___x_500_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; lean_object* v___x_503_; 
lean_dec_ref(v_inst_488_);
lean_dec(v_inst_487_);
lean_dec_ref(v_inst_486_);
lean_dec_ref(v_inst_485_);
lean_dec(v_optionName_484_);
lean_dec_ref(v_decl_483_);
v___x_502_ = lean_box(0);
v___x_503_ = lean_apply_2(v_toPure_482_, lean_box(0), v___x_502_);
return v___x_503_;
}
else
{
lean_object* v_deprecation_x3f_504_; 
v_deprecation_x3f_504_ = lean_ctor_get(v_decl_483_, 4);
lean_inc(v_deprecation_x3f_504_);
lean_dec_ref(v_decl_483_);
if (lean_obj_tag(v_deprecation_x3f_504_) == 1)
{
lean_object* v_val_505_; lean_object* v_text_x3f_506_; 
lean_dec(v_toPure_482_);
v_val_505_ = lean_ctor_get(v_deprecation_x3f_504_, 0);
lean_inc(v_val_505_);
lean_dec_ref_known(v_deprecation_x3f_504_, 1);
v_text_x3f_506_ = lean_ctor_get(v_val_505_, 1);
if (lean_obj_tag(v_text_x3f_506_) == 0)
{
lean_object* v_newName_x3f_507_; 
v_newName_x3f_507_ = lean_ctor_get(v_val_505_, 2);
lean_inc(v_newName_x3f_507_);
lean_dec(v_val_505_);
if (lean_obj_tag(v_newName_x3f_507_) == 0)
{
lean_object* v___x_508_; 
v___x_508_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__3, &l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__3_once, _init_l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__3);
v___y_491_ = v___x_508_;
goto v___jp_490_;
}
else
{
lean_object* v_val_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v_val_509_ = lean_ctor_get(v_newName_x3f_507_, 0);
lean_inc(v_val_509_);
lean_dec_ref_known(v_newName_x3f_507_, 1);
v___x_510_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__5, &l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__5_once, _init_l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__5);
v___x_511_ = l_Lean_MessageData_ofName(v_val_509_);
v___x_512_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_512_, 0, v___x_510_);
lean_ctor_set(v___x_512_, 1, v___x_511_);
v___x_513_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__7, &l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__7_once, _init_l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__7);
v___x_514_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_514_, 0, v___x_512_);
lean_ctor_set(v___x_514_, 1, v___x_513_);
v___y_491_ = v___x_514_;
goto v___jp_490_;
}
}
else
{
lean_object* v_val_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
lean_inc_ref(v_text_x3f_506_);
lean_dec(v_val_505_);
v_val_515_ = lean_ctor_get(v_text_x3f_506_, 0);
lean_inc(v_val_515_);
lean_dec_ref_known(v_text_x3f_506_, 1);
v___x_516_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__9, &l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__9_once, _init_l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__9);
v___x_517_ = l_Lean_stringToMessageData(v_val_515_);
v___x_518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_518_, 0, v___x_516_);
lean_ctor_set(v___x_518_, 1, v___x_517_);
v___y_491_ = v___x_518_;
goto v___jp_490_;
}
}
else
{
lean_object* v___x_519_; lean_object* v___x_520_; 
lean_dec(v_deprecation_x3f_504_);
lean_dec_ref(v_inst_488_);
lean_dec(v_inst_487_);
lean_dec_ref(v_inst_486_);
lean_dec_ref(v_inst_485_);
lean_dec(v_optionName_484_);
v___x_519_ = lean_box(0);
v___x_520_ = lean_apply_2(v_toPure_482_, lean_box(0), v___x_519_);
return v___x_520_;
}
}
v___jp_490_:
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_492_ = lean_obj_once(&l_Lean_Elab_elabSetOption___redArg___lam__1___closed__4, &l_Lean_Elab_elabSetOption___redArg___lam__1___closed__4_once, _init_l_Lean_Elab_elabSetOption___redArg___lam__1___closed__4);
v___x_493_ = l_Lean_MessageData_ofName(v_optionName_484_);
v___x_494_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_494_, 0, v___x_492_);
lean_ctor_set(v___x_494_, 1, v___x_493_);
v___x_495_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__1, &l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__1);
v___x_496_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_496_, 0, v___x_494_);
lean_ctor_set(v___x_496_, 1, v___x_495_);
v___x_497_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_497_, 0, v___x_496_);
lean_ctor_set(v___x_497_, 1, v___y_491_);
v___x_498_ = l_Lean_logWarning___redArg(v_inst_485_, v_inst_486_, v_inst_487_, v_inst_488_, v___x_497_);
return v___x_498_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___boxed(lean_object* v___x_521_, lean_object* v_toPure_522_, lean_object* v_decl_523_, lean_object* v_optionName_524_, lean_object* v_inst_525_, lean_object* v_inst_526_, lean_object* v_inst_527_, lean_object* v_inst_528_, lean_object* v_____do__lift_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_Lean_Elab_checkDeprecatedOption___redArg___lam__0(v___x_521_, v_toPure_522_, v_decl_523_, v_optionName_524_, v_inst_525_, v_inst_526_, v_inst_527_, v_inst_528_, v_____do__lift_529_);
lean_dec_ref(v_____do__lift_529_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedOption___redArg(lean_object* v_inst_531_, lean_object* v_inst_532_, lean_object* v_inst_533_, lean_object* v_inst_534_, lean_object* v_optionName_535_, lean_object* v_decl_536_){
_start:
{
lean_object* v___x_537_; lean_object* v_toApplicative_538_; lean_object* v_toBind_539_; lean_object* v_getOptions_540_; lean_object* v_toPure_541_; lean_object* v___f_542_; lean_object* v___x_543_; 
v___x_537_ = l_Lean_KVMap_instValueBool;
v_toApplicative_538_ = lean_ctor_get(v_inst_531_, 0);
v_toBind_539_ = lean_ctor_get(v_inst_531_, 1);
lean_inc(v_toBind_539_);
v_getOptions_540_ = lean_ctor_get(v_inst_532_, 0);
lean_inc(v_getOptions_540_);
v_toPure_541_ = lean_ctor_get(v_toApplicative_538_, 1);
lean_inc(v_toPure_541_);
v___f_542_ = lean_alloc_closure((void*)(l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___boxed), 9, 8);
lean_closure_set(v___f_542_, 0, v___x_537_);
lean_closure_set(v___f_542_, 1, v_toPure_541_);
lean_closure_set(v___f_542_, 2, v_decl_536_);
lean_closure_set(v___f_542_, 3, v_optionName_535_);
lean_closure_set(v___f_542_, 4, v_inst_531_);
lean_closure_set(v___f_542_, 5, v_inst_533_);
lean_closure_set(v___f_542_, 6, v_inst_534_);
lean_closure_set(v___f_542_, 7, v_inst_532_);
v___x_543_ = lean_apply_4(v_toBind_539_, lean_box(0), lean_box(0), v_getOptions_540_, v___f_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedOption(lean_object* v_m_544_, lean_object* v_inst_545_, lean_object* v_inst_546_, lean_object* v_inst_547_, lean_object* v_inst_548_, lean_object* v_optionName_549_, lean_object* v_decl_550_){
_start:
{
lean_object* v___x_551_; 
v___x_551_ = l_Lean_Elab_checkDeprecatedOption___redArg(v_inst_545_, v_inst_546_, v_inst_547_, v_inst_548_, v_optionName_549_, v_decl_550_);
return v___x_551_;
}
}
lean_object* runtime_initialize_Lean_Elab_InfoTree(uint8_t builtin);
lean_object* runtime_initialize_Init_Syntax(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_SetOption(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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

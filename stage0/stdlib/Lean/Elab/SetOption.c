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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
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
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_Syntax_isStrLit_x3f(lean_object*);
lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_KVMap_instValueDataValue;
lean_object* l_Lean_Options_set___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_pushInfoLeaf___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* l_Lean_getOptionDecl___boxed(lean_object*, lean_object*);
lean_object* l_IO_toEIO___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Lean_Syntax_setArgs(lean_object*, lean_object*);
lean_object* l_Lean_Elab_addCompletionInfo___redArg(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg___closed__0));
v___x_3_ = l_Lean_stringToMessageData(v___x_2_);
return v___x_3_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg___closed__3(void){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg___closed__2));
v___x_6_ = l_Lean_stringToMessageData(v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg(lean_object* v_inst_7_, lean_object* v_inst_8_, lean_object* v_optionName_9_){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_10_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg___closed__1, &l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg___closed__1_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg___closed__1);
v___x_11_ = l_Lean_MessageData_ofName(v_optionName_9_);
v___x_12_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_12_, 0, v___x_10_);
lean_ctor_set(v___x_12_, 1, v___x_11_);
v___x_13_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg___closed__3, &l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg___closed__3_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg___closed__3);
v___x_14_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_14_, 0, v___x_12_);
lean_ctor_set(v___x_14_, 1, v___x_13_);
v___x_15_ = l_Lean_throwError___redArg(v_inst_7_, v_inst_8_, v___x_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable(lean_object* v_m_16_, lean_object* v_inst_17_, lean_object* v_inst_18_, lean_object* v_00_u03b1_19_, lean_object* v_optionName_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg(v_inst_17_, v_inst_18_, v_optionName_20_);
return v___x_21_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__2(void){
_start:
{
lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_25_ = lean_box(0);
v___x_26_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__1));
v___x_27_ = l_Lean_mkConst(v___x_26_, v___x_25_);
return v___x_27_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__3(void){
_start:
{
lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_28_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__2, &l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__2_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__2);
v___x_29_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_29_, 0, v___x_28_);
return v___x_29_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__6(void){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_33_ = lean_box(0);
v___x_34_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__5));
v___x_35_ = l_Lean_mkConst(v___x_34_, v___x_33_);
return v___x_35_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__7(void){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_36_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__6, &l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__6_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__6);
v___x_37_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_37_, 0, v___x_36_);
return v___x_37_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__10(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_41_ = lean_box(0);
v___x_42_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__9));
v___x_43_ = l_Lean_mkConst(v___x_42_, v___x_41_);
return v___x_43_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__11(void){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_44_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__10, &l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__10_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__10);
v___x_45_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_45_, 0, v___x_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f(lean_object* v_x_46_){
_start:
{
switch(lean_obj_tag(v_x_46_))
{
case 0:
{
lean_object* v___x_47_; 
v___x_47_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__3, &l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__3_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__3);
return v___x_47_;
}
case 1:
{
lean_object* v___x_48_; 
v___x_48_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__7, &l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__7_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__7);
return v___x_48_;
}
case 3:
{
lean_object* v___x_49_; 
v___x_49_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__11, &l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__11_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__11);
return v___x_49_;
}
default: 
{
lean_object* v___x_50_; 
v___x_50_ = lean_box(0);
return v___x_50_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___boxed(lean_object* v_x_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f(v_x_51_);
lean_dec_ref(v_x_51_);
return v_res_52_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__1(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_54_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__0));
v___x_55_ = l_Lean_stringToMessageData(v___x_54_);
return v___x_55_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__3(void){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_57_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__2));
v___x_58_ = l_Lean_stringToMessageData(v___x_57_);
return v___x_58_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__5(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_60_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__4));
v___x_61_ = l_Lean_stringToMessageData(v___x_60_);
return v___x_61_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__7(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_63_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__6));
v___x_64_ = l_Lean_stringToMessageData(v___x_63_);
return v___x_64_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__17(void){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_77_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__16));
v___x_78_ = lean_unsigned_to_nat(14u);
v___x_79_ = lean_unsigned_to_nat(22u);
v___x_80_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__15));
v___x_81_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__14));
v___x_82_ = l_mkPanicMessageWithDecl(v___x_81_, v___x_80_, v___x_79_, v___x_78_, v___x_77_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg(lean_object* v_inst_83_, lean_object* v_inst_84_, lean_object* v_optionName_85_, lean_object* v_found_86_, lean_object* v_defVal_87_){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f(v_defVal_87_);
if (lean_obj_tag(v___x_88_) == 1)
{
lean_object* v_val_89_; lean_object* v___y_91_; lean_object* v___y_92_; lean_object* v___y_93_; lean_object* v___y_112_; lean_object* v___x_160_; 
v_val_89_ = lean_ctor_get(v___x_88_, 0);
lean_inc(v_val_89_);
lean_dec_ref(v___x_88_);
v___x_160_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f(v_found_86_);
if (lean_obj_tag(v___x_160_) == 0)
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_161_ = l_Lean_instInhabitedExpr;
v___x_162_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__17, &l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__17_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__17);
v___x_163_ = l_panic___redArg(v___x_161_, v___x_162_);
v___y_112_ = v___x_163_;
goto v___jp_111_;
}
else
{
lean_object* v_val_164_; 
v_val_164_ = lean_ctor_get(v___x_160_, 0);
lean_inc(v_val_164_);
lean_dec_ref(v___x_160_);
v___y_112_ = v_val_164_;
goto v___jp_111_;
}
v___jp_90_:
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_94_ = l_Lean_MessageData_ofFormat(v___y_93_);
v___x_95_ = l_Lean_indentD(v___x_94_);
lean_inc_ref(v___y_92_);
v___x_96_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_96_, 0, v___y_92_);
lean_ctor_set(v___x_96_, 1, v___x_95_);
v___x_97_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__1, &l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__1_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__1);
v___x_98_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_98_, 0, v___x_96_);
lean_ctor_set(v___x_98_, 1, v___x_97_);
v___x_99_ = l_Lean_MessageData_ofExpr(v___y_91_);
v___x_100_ = l_Lean_indentD(v___x_99_);
v___x_101_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_101_, 0, v___x_98_);
lean_ctor_set(v___x_101_, 1, v___x_100_);
v___x_102_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__3, &l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__3_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__3);
v___x_103_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_103_, 0, v___x_101_);
lean_ctor_set(v___x_103_, 1, v___x_102_);
v___x_104_ = l_Lean_MessageData_ofName(v_optionName_85_);
v___x_105_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_105_, 0, v___x_103_);
lean_ctor_set(v___x_105_, 1, v___x_104_);
v___x_106_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__5, &l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__5_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__5);
v___x_107_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_107_, 0, v___x_105_);
lean_ctor_set(v___x_107_, 1, v___x_106_);
v___x_108_ = l_Lean_indentExpr(v_val_89_);
v___x_109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_109_, 0, v___x_107_);
lean_ctor_set(v___x_109_, 1, v___x_108_);
v___x_110_ = l_Lean_throwError___redArg(v_inst_83_, v_inst_84_, v___x_109_);
return v___x_110_;
}
v___jp_111_:
{
lean_object* v___x_113_; 
v___x_113_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__7, &l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__7_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__7);
switch(lean_obj_tag(v_found_86_))
{
case 0:
{
lean_object* v_v_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_122_; 
v_v_114_ = lean_ctor_get(v_found_86_, 0);
v_isSharedCheck_122_ = !lean_is_exclusive(v_found_86_);
if (v_isSharedCheck_122_ == 0)
{
v___x_116_ = v_found_86_;
v_isShared_117_ = v_isSharedCheck_122_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_v_114_);
lean_dec(v_found_86_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_122_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
lean_object* v___x_118_; lean_object* v___x_120_; 
v___x_118_ = l_String_quote(v_v_114_);
if (v_isShared_117_ == 0)
{
lean_ctor_set_tag(v___x_116_, 3);
lean_ctor_set(v___x_116_, 0, v___x_118_);
v___x_120_ = v___x_116_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v___x_118_);
v___x_120_ = v_reuseFailAlloc_121_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
v___y_91_ = v___y_112_;
v___y_92_ = v___x_113_;
v___y_93_ = v___x_120_;
goto v___jp_90_;
}
}
}
case 1:
{
uint8_t v_v_123_; 
v_v_123_ = lean_ctor_get_uint8(v_found_86_, 0);
lean_dec_ref(v_found_86_);
if (v_v_123_ == 0)
{
lean_object* v___x_124_; 
v___x_124_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__9));
v___y_91_ = v___y_112_;
v___y_92_ = v___x_113_;
v___y_93_ = v___x_124_;
goto v___jp_90_;
}
else
{
lean_object* v___x_125_; 
v___x_125_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__11));
v___y_91_ = v___y_112_;
v___y_92_ = v___x_113_;
v___y_93_ = v___x_125_;
goto v___jp_90_;
}
}
case 2:
{
lean_object* v_v_126_; lean_object* v___x_128_; uint8_t v_isShared_129_; uint8_t v_isSharedCheck_137_; 
v_v_126_ = lean_ctor_get(v_found_86_, 0);
v_isSharedCheck_137_ = !lean_is_exclusive(v_found_86_);
if (v_isSharedCheck_137_ == 0)
{
v___x_128_ = v_found_86_;
v_isShared_129_ = v_isSharedCheck_137_;
goto v_resetjp_127_;
}
else
{
lean_inc(v_v_126_);
lean_dec(v_found_86_);
v___x_128_ = lean_box(0);
v_isShared_129_ = v_isSharedCheck_137_;
goto v_resetjp_127_;
}
v_resetjp_127_:
{
lean_object* v___x_130_; uint8_t v___x_131_; lean_object* v___x_132_; lean_object* v___x_134_; 
v___x_130_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__13));
v___x_131_ = 1;
v___x_132_ = l_Lean_Name_toString(v_v_126_, v___x_131_);
if (v_isShared_129_ == 0)
{
lean_ctor_set_tag(v___x_128_, 3);
lean_ctor_set(v___x_128_, 0, v___x_132_);
v___x_134_ = v___x_128_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v___x_132_);
v___x_134_ = v_reuseFailAlloc_136_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
lean_object* v___x_135_; 
v___x_135_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_135_, 0, v___x_130_);
lean_ctor_set(v___x_135_, 1, v___x_134_);
v___y_91_ = v___y_112_;
v___y_92_ = v___x_113_;
v___y_93_ = v___x_135_;
goto v___jp_90_;
}
}
}
case 3:
{
lean_object* v_v_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_146_; 
v_v_138_ = lean_ctor_get(v_found_86_, 0);
v_isSharedCheck_146_ = !lean_is_exclusive(v_found_86_);
if (v_isSharedCheck_146_ == 0)
{
v___x_140_ = v_found_86_;
v_isShared_141_ = v_isSharedCheck_146_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_v_138_);
lean_dec(v_found_86_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_146_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_142_; lean_object* v___x_144_; 
v___x_142_ = l_Nat_reprFast(v_v_138_);
if (v_isShared_141_ == 0)
{
lean_ctor_set(v___x_140_, 0, v___x_142_);
v___x_144_ = v___x_140_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v___x_142_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
v___y_91_ = v___y_112_;
v___y_92_ = v___x_113_;
v___y_93_ = v___x_144_;
goto v___jp_90_;
}
}
}
case 4:
{
lean_object* v_v_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_155_; 
v_v_147_ = lean_ctor_get(v_found_86_, 0);
v_isSharedCheck_155_ = !lean_is_exclusive(v_found_86_);
if (v_isSharedCheck_155_ == 0)
{
v___x_149_ = v_found_86_;
v_isShared_150_ = v_isSharedCheck_155_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_v_147_);
lean_dec(v_found_86_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_155_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v___x_151_; lean_object* v___x_153_; 
v___x_151_ = l_Int_repr(v_v_147_);
lean_dec(v_v_147_);
if (v_isShared_150_ == 0)
{
lean_ctor_set_tag(v___x_149_, 3);
lean_ctor_set(v___x_149_, 0, v___x_151_);
v___x_153_ = v___x_149_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v___x_151_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
v___y_91_ = v___y_112_;
v___y_92_ = v___x_113_;
v___y_93_ = v___x_153_;
goto v___jp_90_;
}
}
}
default: 
{
lean_object* v_v_156_; lean_object* v___x_157_; uint8_t v___x_158_; lean_object* v___x_159_; 
v_v_156_ = lean_ctor_get(v_found_86_, 0);
lean_inc(v_v_156_);
lean_dec_ref(v_found_86_);
v___x_157_ = lean_box(0);
v___x_158_ = 0;
v___x_159_ = l_Lean_Syntax_formatStx(v_v_156_, v___x_157_, v___x_158_);
v___y_91_ = v___y_112_;
v___y_92_ = v___x_113_;
v___y_93_ = v___x_159_;
goto v___jp_90_;
}
}
}
}
else
{
lean_object* v___x_165_; 
lean_dec(v___x_88_);
lean_dec_ref(v_found_86_);
v___x_165_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg(v_inst_83_, v_inst_84_, v_optionName_85_);
return v___x_165_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___boxed(lean_object* v_inst_166_, lean_object* v_inst_167_, lean_object* v_optionName_168_, lean_object* v_found_169_, lean_object* v_defVal_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg(v_inst_166_, v_inst_167_, v_optionName_168_, v_found_169_, v_defVal_170_);
lean_dec_ref(v_defVal_170_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue(lean_object* v_m_172_, lean_object* v_inst_173_, lean_object* v_inst_174_, lean_object* v_optionName_175_, lean_object* v_found_176_, lean_object* v_defVal_177_){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg(v_inst_173_, v_inst_174_, v_optionName_175_, v_found_176_, v_defVal_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___boxed(lean_object* v_m_179_, lean_object* v_inst_180_, lean_object* v_inst_181_, lean_object* v_optionName_182_, lean_object* v_found_183_, lean_object* v_defVal_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue(v_m_179_, v_inst_180_, v_inst_181_, v_optionName_182_, v_found_183_, v_defVal_184_);
lean_dec_ref(v_defVal_184_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_validateOptionValue___redArg(lean_object* v_inst_186_, lean_object* v_inst_187_, lean_object* v_optionName_188_, lean_object* v_decl_189_, lean_object* v_val_190_){
_start:
{
lean_object* v_defValue_191_; uint8_t v___x_192_; 
v_defValue_191_ = lean_ctor_get(v_decl_189_, 2);
v___x_192_ = l_Lean_DataValue_sameCtor(v_defValue_191_, v_val_190_);
if (v___x_192_ == 0)
{
lean_object* v___x_193_; 
v___x_193_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg(v_inst_186_, v_inst_187_, v_optionName_188_, v_val_190_, v_defValue_191_);
return v___x_193_;
}
else
{
lean_object* v_toApplicative_194_; lean_object* v_toPure_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
lean_dec_ref(v_val_190_);
lean_dec(v_optionName_188_);
lean_dec_ref(v_inst_187_);
v_toApplicative_194_ = lean_ctor_get(v_inst_186_, 0);
lean_inc_ref(v_toApplicative_194_);
lean_dec_ref(v_inst_186_);
v_toPure_195_ = lean_ctor_get(v_toApplicative_194_, 1);
lean_inc(v_toPure_195_);
lean_dec_ref(v_toApplicative_194_);
v___x_196_ = lean_box(0);
v___x_197_ = lean_apply_2(v_toPure_195_, lean_box(0), v___x_196_);
return v___x_197_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_validateOptionValue___redArg___boxed(lean_object* v_inst_198_, lean_object* v_inst_199_, lean_object* v_optionName_200_, lean_object* v_decl_201_, lean_object* v_val_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l_Lean_Elab_validateOptionValue___redArg(v_inst_198_, v_inst_199_, v_optionName_200_, v_decl_201_, v_val_202_);
lean_dec_ref(v_decl_201_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_validateOptionValue(lean_object* v_m_204_, lean_object* v_inst_205_, lean_object* v_inst_206_, lean_object* v_optionName_207_, lean_object* v_decl_208_, lean_object* v_val_209_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l_Lean_Elab_validateOptionValue___redArg(v_inst_205_, v_inst_206_, v_optionName_207_, v_decl_208_, v_val_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_validateOptionValue___boxed(lean_object* v_m_211_, lean_object* v_inst_212_, lean_object* v_inst_213_, lean_object* v_optionName_214_, lean_object* v_decl_215_, lean_object* v_val_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_Lean_Elab_validateOptionValue(v_m_211_, v_inst_212_, v_inst_213_, v_optionName_214_, v_decl_215_, v_val_216_);
lean_dec_ref(v_decl_215_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___redArg___lam__0(lean_object* v___x_218_, lean_object* v_optionName_219_, lean_object* v_val_220_, lean_object* v_toPure_221_, lean_object* v_____do__lift_222_){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_223_ = l_Lean_Options_set___redArg(v___x_218_, v_____do__lift_222_, v_optionName_219_, v_val_220_);
v___x_224_ = lean_apply_2(v_toPure_221_, lean_box(0), v___x_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___redArg___lam__1(lean_object* v_toBind_225_, lean_object* v_inst_226_, lean_object* v___f_227_, lean_object* v_____r_228_){
_start:
{
lean_object* v___x_229_; 
v___x_229_ = lean_apply_4(v_toBind_225_, lean_box(0), lean_box(0), v_inst_226_, v___f_227_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___redArg(lean_object* v_inst_230_, lean_object* v_inst_231_, lean_object* v_inst_232_, lean_object* v_optionName_233_, lean_object* v_decl_234_, lean_object* v_val_235_){
_start:
{
lean_object* v___x_236_; lean_object* v_toApplicative_237_; lean_object* v_toBind_238_; lean_object* v_toPure_239_; lean_object* v___x_240_; lean_object* v___f_241_; lean_object* v___f_242_; lean_object* v___x_243_; 
v___x_236_ = l_Lean_KVMap_instValueDataValue;
v_toApplicative_237_ = lean_ctor_get(v_inst_230_, 0);
v_toBind_238_ = lean_ctor_get(v_inst_230_, 1);
lean_inc_n(v_toBind_238_, 2);
v_toPure_239_ = lean_ctor_get(v_toApplicative_237_, 1);
lean_inc(v_toPure_239_);
lean_inc_ref(v_val_235_);
lean_inc(v_optionName_233_);
v___x_240_ = l_Lean_Elab_validateOptionValue___redArg(v_inst_230_, v_inst_232_, v_optionName_233_, v_decl_234_, v_val_235_);
v___f_241_ = lean_alloc_closure((void*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___redArg___lam__0), 5, 4);
lean_closure_set(v___f_241_, 0, v___x_236_);
lean_closure_set(v___f_241_, 1, v_optionName_233_);
lean_closure_set(v___f_241_, 2, v_val_235_);
lean_closure_set(v___f_241_, 3, v_toPure_239_);
v___f_242_ = lean_alloc_closure((void*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___redArg___lam__1), 4, 3);
lean_closure_set(v___f_242_, 0, v_toBind_238_);
lean_closure_set(v___f_242_, 1, v_inst_231_);
lean_closure_set(v___f_242_, 2, v___f_241_);
v___x_243_ = lean_apply_4(v_toBind_238_, lean_box(0), lean_box(0), v___x_240_, v___f_242_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___redArg___boxed(lean_object* v_inst_244_, lean_object* v_inst_245_, lean_object* v_inst_246_, lean_object* v_optionName_247_, lean_object* v_decl_248_, lean_object* v_val_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___redArg(v_inst_244_, v_inst_245_, v_inst_246_, v_optionName_247_, v_decl_248_, v_val_249_);
lean_dec_ref(v_decl_248_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption(lean_object* v_m_251_, lean_object* v_inst_252_, lean_object* v_inst_253_, lean_object* v_inst_254_, lean_object* v_optionName_255_, lean_object* v_decl_256_, lean_object* v_val_257_){
_start:
{
lean_object* v___x_258_; 
v___x_258_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___redArg(v_inst_252_, v_inst_253_, v_inst_254_, v_optionName_255_, v_decl_256_, v_val_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___boxed(lean_object* v_m_259_, lean_object* v_inst_260_, lean_object* v_inst_261_, lean_object* v_inst_262_, lean_object* v_optionName_263_, lean_object* v_decl_264_, lean_object* v_val_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption(v_m_259_, v_inst_260_, v_inst_261_, v_inst_262_, v_optionName_263_, v_decl_264_, v_val_265_);
lean_dec_ref(v_decl_264_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg___lam__0(lean_object* v_ref_267_, lean_object* v_ex_268_){
_start:
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_269_ = lean_io_error_to_string(v_ex_268_);
v___x_270_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_270_, 0, v___x_269_);
v___x_271_ = l_Lean_MessageData_ofFormat(v___x_270_);
v___x_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_272_, 0, v_ref_267_);
lean_ctor_set(v___x_272_, 1, v___x_271_);
return v___x_272_;
}
}
static lean_object* _init_l_Lean_Elab_elabSetOption___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_274_ = ((lean_object*)(l_Lean_Elab_elabSetOption___redArg___lam__1___closed__0));
v___x_275_ = l_Lean_stringToMessageData(v___x_274_);
return v___x_275_;
}
}
static lean_object* _init_l_Lean_Elab_elabSetOption___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_277_ = ((lean_object*)(l_Lean_Elab_elabSetOption___redArg___lam__1___closed__2));
v___x_278_ = l_Lean_stringToMessageData(v___x_277_);
return v___x_278_;
}
}
static lean_object* _init_l_Lean_Elab_elabSetOption___redArg___lam__1___closed__4(void){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_279_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__12));
v___x_280_ = l_Lean_stringToMessageData(v___x_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg___lam__1(lean_object* v_val_281_, lean_object* v_defValue_282_, lean_object* v_inst_283_, lean_object* v_inst_284_, lean_object* v_optionName_285_, lean_object* v_inst_286_, lean_object* v_decl_287_, lean_object* v_____r_288_){
_start:
{
lean_object* v___x_303_; 
v___x_303_ = l_Lean_Syntax_isStrLit_x3f(v_val_281_);
if (lean_obj_tag(v___x_303_) == 0)
{
lean_object* v___x_304_; 
v___x_304_ = l_Lean_Syntax_isNatLit_x3f(v_val_281_);
if (lean_obj_tag(v___x_304_) == 0)
{
if (lean_obj_tag(v_val_281_) == 2)
{
lean_object* v_val_305_; lean_object* v___x_306_; uint8_t v___x_307_; 
v_val_305_ = lean_ctor_get(v_val_281_, 1);
v___x_306_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__10));
v___x_307_ = lean_string_dec_eq(v_val_305_, v___x_306_);
if (v___x_307_ == 0)
{
lean_object* v___x_308_; uint8_t v___x_309_; 
v___x_308_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__8));
v___x_309_ = lean_string_dec_eq(v_val_305_, v___x_308_);
if (v___x_309_ == 0)
{
lean_dec(v_inst_286_);
goto v___jp_289_;
}
else
{
lean_object* v___x_310_; lean_object* v___x_311_; 
lean_dec_ref(v_val_281_);
v___x_310_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_310_, 0, v___x_307_);
v___x_311_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___redArg(v_inst_283_, v_inst_286_, v_inst_284_, v_optionName_285_, v_decl_287_, v___x_310_);
return v___x_311_;
}
}
else
{
lean_object* v___x_312_; lean_object* v___x_313_; 
lean_dec_ref(v_val_281_);
v___x_312_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_312_, 0, v___x_307_);
v___x_313_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___redArg(v_inst_283_, v_inst_286_, v_inst_284_, v_optionName_285_, v_decl_287_, v___x_312_);
return v___x_313_;
}
}
else
{
lean_dec(v_inst_286_);
goto v___jp_289_;
}
}
else
{
lean_object* v_val_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_322_; 
lean_dec(v_val_281_);
v_val_314_ = lean_ctor_get(v___x_304_, 0);
v_isSharedCheck_322_ = !lean_is_exclusive(v___x_304_);
if (v_isSharedCheck_322_ == 0)
{
v___x_316_ = v___x_304_;
v_isShared_317_ = v_isSharedCheck_322_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_val_314_);
lean_dec(v___x_304_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_322_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_319_; 
if (v_isShared_317_ == 0)
{
lean_ctor_set_tag(v___x_316_, 3);
v___x_319_ = v___x_316_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v_val_314_);
v___x_319_ = v_reuseFailAlloc_321_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
lean_object* v___x_320_; 
v___x_320_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___redArg(v_inst_283_, v_inst_286_, v_inst_284_, v_optionName_285_, v_decl_287_, v___x_319_);
return v___x_320_;
}
}
}
}
else
{
lean_object* v_val_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_331_; 
lean_dec(v_val_281_);
v_val_323_ = lean_ctor_get(v___x_303_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_303_);
if (v_isSharedCheck_331_ == 0)
{
v___x_325_ = v___x_303_;
v_isShared_326_ = v_isSharedCheck_331_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_val_323_);
lean_dec(v___x_303_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_331_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v___x_328_; 
if (v_isShared_326_ == 0)
{
lean_ctor_set_tag(v___x_325_, 0);
v___x_328_ = v___x_325_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_val_323_);
v___x_328_ = v_reuseFailAlloc_330_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
lean_object* v___x_329_; 
v___x_329_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___redArg(v_inst_283_, v_inst_286_, v_inst_284_, v_optionName_285_, v_decl_287_, v___x_328_);
return v___x_329_;
}
}
}
v___jp_289_:
{
lean_object* v___x_290_; 
v___x_290_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f(v_defValue_282_);
if (lean_obj_tag(v___x_290_) == 1)
{
lean_object* v_val_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
lean_dec(v_optionName_285_);
v_val_291_ = lean_ctor_get(v___x_290_, 0);
lean_inc(v_val_291_);
lean_dec_ref(v___x_290_);
v___x_292_ = lean_obj_once(&l_Lean_Elab_elabSetOption___redArg___lam__1___closed__1, &l_Lean_Elab_elabSetOption___redArg___lam__1___closed__1_once, _init_l_Lean_Elab_elabSetOption___redArg___lam__1___closed__1);
v___x_293_ = l_Lean_MessageData_ofSyntax(v_val_281_);
v___x_294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_294_, 0, v___x_292_);
lean_ctor_set(v___x_294_, 1, v___x_293_);
v___x_295_ = lean_obj_once(&l_Lean_Elab_elabSetOption___redArg___lam__1___closed__3, &l_Lean_Elab_elabSetOption___redArg___lam__1___closed__3_once, _init_l_Lean_Elab_elabSetOption___redArg___lam__1___closed__3);
v___x_296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_296_, 0, v___x_294_);
lean_ctor_set(v___x_296_, 1, v___x_295_);
v___x_297_ = l_Lean_MessageData_ofExpr(v_val_291_);
v___x_298_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_298_, 0, v___x_296_);
lean_ctor_set(v___x_298_, 1, v___x_297_);
v___x_299_ = lean_obj_once(&l_Lean_Elab_elabSetOption___redArg___lam__1___closed__4, &l_Lean_Elab_elabSetOption___redArg___lam__1___closed__4_once, _init_l_Lean_Elab_elabSetOption___redArg___lam__1___closed__4);
v___x_300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_300_, 0, v___x_298_);
lean_ctor_set(v___x_300_, 1, v___x_299_);
v___x_301_ = l_Lean_throwError___redArg(v_inst_283_, v_inst_284_, v___x_300_);
return v___x_301_;
}
else
{
lean_object* v___x_302_; 
lean_dec(v___x_290_);
lean_dec(v_val_281_);
v___x_302_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg(v_inst_283_, v_inst_284_, v_optionName_285_);
return v___x_302_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg___lam__1___boxed(lean_object* v_val_332_, lean_object* v_defValue_333_, lean_object* v_inst_334_, lean_object* v_inst_335_, lean_object* v_optionName_336_, lean_object* v_inst_337_, lean_object* v_decl_338_, lean_object* v_____r_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_Lean_Elab_elabSetOption___redArg___lam__1(v_val_332_, v_defValue_333_, v_inst_334_, v_inst_335_, v_optionName_336_, v_inst_337_, v_decl_338_, v_____r_339_);
lean_dec_ref(v_decl_338_);
lean_dec_ref(v_defValue_333_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg___lam__2(lean_object* v_val_341_, lean_object* v_inst_342_, lean_object* v_inst_343_, lean_object* v_optionName_344_, lean_object* v_inst_345_, lean_object* v_id_346_, lean_object* v_inst_347_, lean_object* v_toBind_348_, lean_object* v_decl_349_){
_start:
{
lean_object* v_declName_350_; lean_object* v_defValue_351_; lean_object* v___f_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v_declName_350_ = lean_ctor_get(v_decl_349_, 1);
lean_inc(v_declName_350_);
v_defValue_351_ = lean_ctor_get(v_decl_349_, 2);
lean_inc_ref(v_defValue_351_);
lean_inc(v_optionName_344_);
lean_inc_ref(v_inst_342_);
v___f_352_ = lean_alloc_closure((void*)(l_Lean_Elab_elabSetOption___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_352_, 0, v_val_341_);
lean_closure_set(v___f_352_, 1, v_defValue_351_);
lean_closure_set(v___f_352_, 2, v_inst_342_);
lean_closure_set(v___f_352_, 3, v_inst_343_);
lean_closure_set(v___f_352_, 4, v_optionName_344_);
lean_closure_set(v___f_352_, 5, v_inst_345_);
lean_closure_set(v___f_352_, 6, v_decl_349_);
v___x_353_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_353_, 0, v_id_346_);
lean_ctor_set(v___x_353_, 1, v_optionName_344_);
lean_ctor_set(v___x_353_, 2, v_declName_350_);
v___x_354_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_354_, 0, v___x_353_);
v___x_355_ = l_Lean_Elab_pushInfoLeaf___redArg(v_inst_342_, v_inst_347_, v___x_354_);
v___x_356_ = lean_apply_4(v_toBind_348_, lean_box(0), lean_box(0), v___x_355_, v___f_352_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg___lam__3(lean_object* v_id_357_, lean_object* v_val_358_, lean_object* v_inst_359_, lean_object* v_inst_360_, lean_object* v_inst_361_, lean_object* v_inst_362_, lean_object* v_toBind_363_, lean_object* v___f_364_, lean_object* v_inst_365_, lean_object* v_____r_366_){
_start:
{
lean_object* v___x_367_; lean_object* v_optionName_368_; lean_object* v___f_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_367_ = l_Lean_Syntax_getId(v_id_357_);
v_optionName_368_ = lean_erase_macro_scopes(v___x_367_);
lean_inc(v_toBind_363_);
lean_inc(v_optionName_368_);
v___f_369_ = lean_alloc_closure((void*)(l_Lean_Elab_elabSetOption___redArg___lam__2), 9, 8);
lean_closure_set(v___f_369_, 0, v_val_358_);
lean_closure_set(v___f_369_, 1, v_inst_359_);
lean_closure_set(v___f_369_, 2, v_inst_360_);
lean_closure_set(v___f_369_, 3, v_optionName_368_);
lean_closure_set(v___f_369_, 4, v_inst_361_);
lean_closure_set(v___f_369_, 5, v_id_357_);
lean_closure_set(v___f_369_, 6, v_inst_362_);
lean_closure_set(v___f_369_, 7, v_toBind_363_);
v___x_370_ = lean_alloc_closure((void*)(l_Lean_getOptionDecl___boxed), 2, 1);
lean_closure_set(v___x_370_, 0, v_optionName_368_);
v___x_371_ = lean_alloc_closure((void*)(l_IO_toEIO___boxed), 5, 4);
lean_closure_set(v___x_371_, 0, lean_box(0));
lean_closure_set(v___x_371_, 1, lean_box(0));
lean_closure_set(v___x_371_, 2, v___f_364_);
lean_closure_set(v___x_371_, 3, v___x_370_);
v___x_372_ = lean_apply_2(v_inst_365_, lean_box(0), v___x_371_);
v___x_373_ = lean_apply_4(v_toBind_363_, lean_box(0), lean_box(0), v___x_372_, v___f_369_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg___lam__4(lean_object* v_id_374_, lean_object* v_val_375_, lean_object* v_inst_376_, lean_object* v_inst_377_, lean_object* v_inst_378_, lean_object* v_inst_379_, lean_object* v_toBind_380_, lean_object* v_inst_381_, lean_object* v_ref_382_){
_start:
{
lean_object* v___f_383_; lean_object* v___f_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
lean_inc(v_ref_382_);
v___f_383_ = lean_alloc_closure((void*)(l_Lean_Elab_elabSetOption___redArg___lam__0), 2, 1);
lean_closure_set(v___f_383_, 0, v_ref_382_);
lean_inc(v_toBind_380_);
lean_inc_ref(v_inst_379_);
lean_inc_ref(v_inst_376_);
v___f_384_ = lean_alloc_closure((void*)(l_Lean_Elab_elabSetOption___redArg___lam__3), 10, 9);
lean_closure_set(v___f_384_, 0, v_id_374_);
lean_closure_set(v___f_384_, 1, v_val_375_);
lean_closure_set(v___f_384_, 2, v_inst_376_);
lean_closure_set(v___f_384_, 3, v_inst_377_);
lean_closure_set(v___f_384_, 4, v_inst_378_);
lean_closure_set(v___f_384_, 5, v_inst_379_);
lean_closure_set(v___f_384_, 6, v_toBind_380_);
lean_closure_set(v___f_384_, 7, v___f_383_);
lean_closure_set(v___f_384_, 8, v_inst_381_);
v___x_385_ = l_Lean_Syntax_getArgs(v_ref_382_);
v___x_386_ = lean_unsigned_to_nat(3u);
v___x_387_ = lean_unsigned_to_nat(0u);
v___x_388_ = l_Array_toSubarray___redArg(v___x_385_, v___x_387_, v___x_386_);
v___x_389_ = l_Subarray_copy___redArg(v___x_388_);
v___x_390_ = l_Lean_Syntax_setArgs(v_ref_382_, v___x_389_);
v___x_391_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_391_, 0, v___x_390_);
v___x_392_ = l_Lean_Elab_addCompletionInfo___redArg(v_inst_376_, v_inst_379_, v___x_391_);
v___x_393_ = lean_apply_4(v_toBind_380_, lean_box(0), lean_box(0), v___x_392_, v___f_384_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg(lean_object* v_inst_394_, lean_object* v_inst_395_, lean_object* v_inst_396_, lean_object* v_inst_397_, lean_object* v_inst_398_, lean_object* v_id_399_, lean_object* v_val_400_){
_start:
{
lean_object* v_toMonadRef_401_; lean_object* v_toBind_402_; lean_object* v_getRef_403_; lean_object* v___f_404_; lean_object* v___x_405_; 
v_toMonadRef_401_ = lean_ctor_get(v_inst_396_, 1);
v_toBind_402_ = lean_ctor_get(v_inst_394_, 1);
lean_inc_n(v_toBind_402_, 2);
v_getRef_403_ = lean_ctor_get(v_toMonadRef_401_, 0);
lean_inc(v_getRef_403_);
v___f_404_ = lean_alloc_closure((void*)(l_Lean_Elab_elabSetOption___redArg___lam__4), 9, 8);
lean_closure_set(v___f_404_, 0, v_id_399_);
lean_closure_set(v___f_404_, 1, v_val_400_);
lean_closure_set(v___f_404_, 2, v_inst_394_);
lean_closure_set(v___f_404_, 3, v_inst_396_);
lean_closure_set(v___f_404_, 4, v_inst_395_);
lean_closure_set(v___f_404_, 5, v_inst_398_);
lean_closure_set(v___f_404_, 6, v_toBind_402_);
lean_closure_set(v___f_404_, 7, v_inst_397_);
v___x_405_ = lean_apply_4(v_toBind_402_, lean_box(0), lean_box(0), v_getRef_403_, v___f_404_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption(lean_object* v_m_406_, lean_object* v_inst_407_, lean_object* v_inst_408_, lean_object* v_inst_409_, lean_object* v_inst_410_, lean_object* v_inst_411_, lean_object* v_id_412_, lean_object* v_val_413_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = l_Lean_Elab_elabSetOption___redArg(v_inst_407_, v_inst_408_, v_inst_409_, v_inst_410_, v_inst_411_, v_id_412_, v_val_413_);
return v___x_414_;
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

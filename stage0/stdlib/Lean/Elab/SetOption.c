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
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__14;
static const lean_string_object l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__15 = (const lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__15_value;
static const lean_string_object l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__16 = (const lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__16_value;
static const lean_string_object l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__17 = (const lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__17_value;
static const lean_string_object l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__18 = (const lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__18_value;
static lean_once_cell_t l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__19;
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
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__14(void){
_start:
{
lean_object* v_natZero_74_; lean_object* v_intZero_75_; 
v_natZero_74_ = lean_unsigned_to_nat(0u);
v_intZero_75_ = lean_nat_to_int(v_natZero_74_);
return v_intZero_75_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__19(void){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_80_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__18));
v___x_81_ = lean_unsigned_to_nat(14u);
v___x_82_ = lean_unsigned_to_nat(22u);
v___x_83_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__17));
v___x_84_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__16));
v___x_85_ = l_mkPanicMessageWithDecl(v___x_84_, v___x_83_, v___x_82_, v___x_81_, v___x_80_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg(lean_object* v_inst_86_, lean_object* v_inst_87_, lean_object* v_optionName_88_, lean_object* v_found_89_, lean_object* v_defVal_90_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f(v_defVal_90_);
if (lean_obj_tag(v___x_91_) == 1)
{
lean_object* v_val_92_; lean_object* v___y_94_; lean_object* v___y_95_; lean_object* v___y_96_; lean_object* v___y_115_; lean_object* v___x_176_; 
v_val_92_ = lean_ctor_get(v___x_91_, 0);
lean_inc(v_val_92_);
lean_dec_ref(v___x_91_);
v___x_176_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f(v_found_89_);
if (lean_obj_tag(v___x_176_) == 0)
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_177_ = l_Lean_instInhabitedExpr;
v___x_178_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__19, &l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__19_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__19);
v___x_179_ = l_panic___redArg(v___x_177_, v___x_178_);
v___y_115_ = v___x_179_;
goto v___jp_114_;
}
else
{
lean_object* v_val_180_; 
v_val_180_ = lean_ctor_get(v___x_176_, 0);
lean_inc(v_val_180_);
lean_dec_ref(v___x_176_);
v___y_115_ = v_val_180_;
goto v___jp_114_;
}
v___jp_93_:
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_97_ = l_Lean_MessageData_ofFormat(v___y_96_);
v___x_98_ = l_Lean_indentD(v___x_97_);
v___x_99_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_99_, 0, v___y_95_);
lean_ctor_set(v___x_99_, 1, v___x_98_);
v___x_100_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__1, &l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__1_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__1);
v___x_101_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_101_, 0, v___x_99_);
lean_ctor_set(v___x_101_, 1, v___x_100_);
v___x_102_ = l_Lean_MessageData_ofExpr(v___y_94_);
v___x_103_ = l_Lean_indentD(v___x_102_);
v___x_104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_104_, 0, v___x_101_);
lean_ctor_set(v___x_104_, 1, v___x_103_);
v___x_105_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__3, &l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__3_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__3);
v___x_106_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_106_, 0, v___x_104_);
lean_ctor_set(v___x_106_, 1, v___x_105_);
v___x_107_ = l_Lean_MessageData_ofName(v_optionName_88_);
v___x_108_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_108_, 0, v___x_106_);
lean_ctor_set(v___x_108_, 1, v___x_107_);
v___x_109_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__5, &l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__5_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__5);
v___x_110_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_110_, 0, v___x_108_);
lean_ctor_set(v___x_110_, 1, v___x_109_);
v___x_111_ = l_Lean_indentExpr(v_val_92_);
v___x_112_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_112_, 0, v___x_110_);
lean_ctor_set(v___x_112_, 1, v___x_111_);
v___x_113_ = l_Lean_throwError___redArg(v_inst_86_, v_inst_87_, v___x_112_);
return v___x_113_;
}
v___jp_114_:
{
lean_object* v___x_116_; 
v___x_116_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__7, &l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__7_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__7);
switch(lean_obj_tag(v_found_89_))
{
case 0:
{
lean_object* v_v_117_; lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_125_; 
v_v_117_ = lean_ctor_get(v_found_89_, 0);
v_isSharedCheck_125_ = !lean_is_exclusive(v_found_89_);
if (v_isSharedCheck_125_ == 0)
{
v___x_119_ = v_found_89_;
v_isShared_120_ = v_isSharedCheck_125_;
goto v_resetjp_118_;
}
else
{
lean_inc(v_v_117_);
lean_dec(v_found_89_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_125_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
lean_object* v___x_121_; lean_object* v___x_123_; 
v___x_121_ = l_String_quote(v_v_117_);
if (v_isShared_120_ == 0)
{
lean_ctor_set_tag(v___x_119_, 3);
lean_ctor_set(v___x_119_, 0, v___x_121_);
v___x_123_ = v___x_119_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v___x_121_);
v___x_123_ = v_reuseFailAlloc_124_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
v___y_94_ = v___y_115_;
v___y_95_ = v___x_116_;
v___y_96_ = v___x_123_;
goto v___jp_93_;
}
}
}
case 1:
{
uint8_t v_v_126_; 
v_v_126_ = lean_ctor_get_uint8(v_found_89_, 0);
lean_dec_ref(v_found_89_);
if (v_v_126_ == 0)
{
lean_object* v___x_127_; 
v___x_127_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__9));
v___y_94_ = v___y_115_;
v___y_95_ = v___x_116_;
v___y_96_ = v___x_127_;
goto v___jp_93_;
}
else
{
lean_object* v___x_128_; 
v___x_128_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__11));
v___y_94_ = v___y_115_;
v___y_95_ = v___x_116_;
v___y_96_ = v___x_128_;
goto v___jp_93_;
}
}
case 2:
{
lean_object* v_v_129_; lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_140_; 
v_v_129_ = lean_ctor_get(v_found_89_, 0);
v_isSharedCheck_140_ = !lean_is_exclusive(v_found_89_);
if (v_isSharedCheck_140_ == 0)
{
v___x_131_ = v_found_89_;
v_isShared_132_ = v_isSharedCheck_140_;
goto v_resetjp_130_;
}
else
{
lean_inc(v_v_129_);
lean_dec(v_found_89_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_140_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
lean_object* v___x_133_; uint8_t v___x_134_; lean_object* v___x_135_; lean_object* v___x_137_; 
v___x_133_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__13));
v___x_134_ = 1;
v___x_135_ = l_Lean_Name_toString(v_v_129_, v___x_134_);
if (v_isShared_132_ == 0)
{
lean_ctor_set_tag(v___x_131_, 3);
lean_ctor_set(v___x_131_, 0, v___x_135_);
v___x_137_ = v___x_131_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v___x_135_);
v___x_137_ = v_reuseFailAlloc_139_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
lean_object* v___x_138_; 
v___x_138_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_138_, 0, v___x_133_);
lean_ctor_set(v___x_138_, 1, v___x_137_);
v___y_94_ = v___y_115_;
v___y_95_ = v___x_116_;
v___y_96_ = v___x_138_;
goto v___jp_93_;
}
}
}
case 3:
{
lean_object* v_v_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_149_; 
v_v_141_ = lean_ctor_get(v_found_89_, 0);
v_isSharedCheck_149_ = !lean_is_exclusive(v_found_89_);
if (v_isSharedCheck_149_ == 0)
{
v___x_143_ = v_found_89_;
v_isShared_144_ = v_isSharedCheck_149_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_v_141_);
lean_dec(v_found_89_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_149_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___x_145_; lean_object* v___x_147_; 
v___x_145_ = l_Nat_reprFast(v_v_141_);
if (v_isShared_144_ == 0)
{
lean_ctor_set(v___x_143_, 0, v___x_145_);
v___x_147_ = v___x_143_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v___x_145_);
v___x_147_ = v_reuseFailAlloc_148_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
v___y_94_ = v___y_115_;
v___y_95_ = v___x_116_;
v___y_96_ = v___x_147_;
goto v___jp_93_;
}
}
}
case 4:
{
lean_object* v_v_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_171_; 
v_v_150_ = lean_ctor_get(v_found_89_, 0);
v_isSharedCheck_171_ = !lean_is_exclusive(v_found_89_);
if (v_isSharedCheck_171_ == 0)
{
v___x_152_ = v_found_89_;
v_isShared_153_ = v_isSharedCheck_171_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_v_150_);
lean_dec(v_found_89_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_171_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v_intZero_154_; uint8_t v_isNeg_155_; 
v_intZero_154_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__14, &l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__14_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__14);
v_isNeg_155_ = lean_int_dec_lt(v_v_150_, v_intZero_154_);
if (v_isNeg_155_ == 0)
{
lean_object* v_a_156_; lean_object* v___x_157_; lean_object* v___x_159_; 
v_a_156_ = lean_nat_abs(v_v_150_);
lean_dec(v_v_150_);
v___x_157_ = l_Nat_reprFast(v_a_156_);
if (v_isShared_153_ == 0)
{
lean_ctor_set_tag(v___x_152_, 3);
lean_ctor_set(v___x_152_, 0, v___x_157_);
v___x_159_ = v___x_152_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v___x_157_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
v___y_94_ = v___y_115_;
v___y_95_ = v___x_116_;
v___y_96_ = v___x_159_;
goto v___jp_93_;
}
}
else
{
lean_object* v_abs_161_; lean_object* v_one_162_; lean_object* v_a_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_169_; 
v_abs_161_ = lean_nat_abs(v_v_150_);
lean_dec(v_v_150_);
v_one_162_ = lean_unsigned_to_nat(1u);
v_a_163_ = lean_nat_sub(v_abs_161_, v_one_162_);
lean_dec(v_abs_161_);
v___x_164_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__15));
v___x_165_ = lean_nat_add(v_a_163_, v_one_162_);
lean_dec(v_a_163_);
v___x_166_ = l_Nat_reprFast(v___x_165_);
v___x_167_ = lean_string_append(v___x_164_, v___x_166_);
lean_dec_ref(v___x_166_);
if (v_isShared_153_ == 0)
{
lean_ctor_set_tag(v___x_152_, 3);
lean_ctor_set(v___x_152_, 0, v___x_167_);
v___x_169_ = v___x_152_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v___x_167_);
v___x_169_ = v_reuseFailAlloc_170_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
v___y_94_ = v___y_115_;
v___y_95_ = v___x_116_;
v___y_96_ = v___x_169_;
goto v___jp_93_;
}
}
}
}
default: 
{
lean_object* v_v_172_; lean_object* v___x_173_; uint8_t v___x_174_; lean_object* v___x_175_; 
v_v_172_ = lean_ctor_get(v_found_89_, 0);
lean_inc(v_v_172_);
lean_dec_ref(v_found_89_);
v___x_173_ = lean_box(0);
v___x_174_ = 0;
v___x_175_ = l_Lean_Syntax_formatStx(v_v_172_, v___x_173_, v___x_174_);
v___y_94_ = v___y_115_;
v___y_95_ = v___x_116_;
v___y_96_ = v___x_175_;
goto v___jp_93_;
}
}
}
}
else
{
lean_object* v___x_181_; 
lean_dec(v___x_91_);
lean_dec_ref(v_found_89_);
v___x_181_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg(v_inst_86_, v_inst_87_, v_optionName_88_);
return v___x_181_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___boxed(lean_object* v_inst_182_, lean_object* v_inst_183_, lean_object* v_optionName_184_, lean_object* v_found_185_, lean_object* v_defVal_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg(v_inst_182_, v_inst_183_, v_optionName_184_, v_found_185_, v_defVal_186_);
lean_dec_ref(v_defVal_186_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue(lean_object* v_m_188_, lean_object* v_inst_189_, lean_object* v_inst_190_, lean_object* v_optionName_191_, lean_object* v_found_192_, lean_object* v_defVal_193_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg(v_inst_189_, v_inst_190_, v_optionName_191_, v_found_192_, v_defVal_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___boxed(lean_object* v_m_195_, lean_object* v_inst_196_, lean_object* v_inst_197_, lean_object* v_optionName_198_, lean_object* v_found_199_, lean_object* v_defVal_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue(v_m_195_, v_inst_196_, v_inst_197_, v_optionName_198_, v_found_199_, v_defVal_200_);
lean_dec_ref(v_defVal_200_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_validateOptionValue___redArg(lean_object* v_inst_202_, lean_object* v_inst_203_, lean_object* v_optionName_204_, lean_object* v_decl_205_, lean_object* v_val_206_){
_start:
{
lean_object* v_defValue_207_; uint8_t v___x_208_; 
v_defValue_207_ = lean_ctor_get(v_decl_205_, 2);
v___x_208_ = l_Lean_DataValue_sameCtor(v_defValue_207_, v_val_206_);
if (v___x_208_ == 0)
{
lean_object* v___x_209_; 
v___x_209_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg(v_inst_202_, v_inst_203_, v_optionName_204_, v_val_206_, v_defValue_207_);
return v___x_209_;
}
else
{
lean_object* v_toApplicative_210_; lean_object* v_toPure_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
lean_dec_ref(v_val_206_);
lean_dec(v_optionName_204_);
lean_dec_ref(v_inst_203_);
v_toApplicative_210_ = lean_ctor_get(v_inst_202_, 0);
lean_inc_ref(v_toApplicative_210_);
lean_dec_ref(v_inst_202_);
v_toPure_211_ = lean_ctor_get(v_toApplicative_210_, 1);
lean_inc(v_toPure_211_);
lean_dec_ref(v_toApplicative_210_);
v___x_212_ = lean_box(0);
v___x_213_ = lean_apply_2(v_toPure_211_, lean_box(0), v___x_212_);
return v___x_213_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_validateOptionValue___redArg___boxed(lean_object* v_inst_214_, lean_object* v_inst_215_, lean_object* v_optionName_216_, lean_object* v_decl_217_, lean_object* v_val_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lean_Elab_validateOptionValue___redArg(v_inst_214_, v_inst_215_, v_optionName_216_, v_decl_217_, v_val_218_);
lean_dec_ref(v_decl_217_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_validateOptionValue(lean_object* v_m_220_, lean_object* v_inst_221_, lean_object* v_inst_222_, lean_object* v_optionName_223_, lean_object* v_decl_224_, lean_object* v_val_225_){
_start:
{
lean_object* v___x_226_; 
v___x_226_ = l_Lean_Elab_validateOptionValue___redArg(v_inst_221_, v_inst_222_, v_optionName_223_, v_decl_224_, v_val_225_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_validateOptionValue___boxed(lean_object* v_m_227_, lean_object* v_inst_228_, lean_object* v_inst_229_, lean_object* v_optionName_230_, lean_object* v_decl_231_, lean_object* v_val_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_Lean_Elab_validateOptionValue(v_m_227_, v_inst_228_, v_inst_229_, v_optionName_230_, v_decl_231_, v_val_232_);
lean_dec_ref(v_decl_231_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___redArg___lam__0(lean_object* v___x_234_, lean_object* v_optionName_235_, lean_object* v_val_236_, lean_object* v_toPure_237_, lean_object* v_____do__lift_238_){
_start:
{
lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_239_ = l_Lean_Options_set___redArg(v___x_234_, v_____do__lift_238_, v_optionName_235_, v_val_236_);
v___x_240_ = lean_apply_2(v_toPure_237_, lean_box(0), v___x_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___redArg___lam__1(lean_object* v_toBind_241_, lean_object* v_inst_242_, lean_object* v___f_243_, lean_object* v_____r_244_){
_start:
{
lean_object* v___x_245_; 
v___x_245_ = lean_apply_4(v_toBind_241_, lean_box(0), lean_box(0), v_inst_242_, v___f_243_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___redArg(lean_object* v_inst_246_, lean_object* v_inst_247_, lean_object* v_inst_248_, lean_object* v_optionName_249_, lean_object* v_decl_250_, lean_object* v_val_251_){
_start:
{
lean_object* v___x_252_; lean_object* v_toApplicative_253_; lean_object* v_toBind_254_; lean_object* v_toPure_255_; lean_object* v___x_256_; lean_object* v___f_257_; lean_object* v___f_258_; lean_object* v___x_259_; 
v___x_252_ = l_Lean_KVMap_instValueDataValue;
v_toApplicative_253_ = lean_ctor_get(v_inst_246_, 0);
v_toBind_254_ = lean_ctor_get(v_inst_246_, 1);
lean_inc(v_toBind_254_);
v_toPure_255_ = lean_ctor_get(v_toApplicative_253_, 1);
lean_inc(v_toPure_255_);
lean_inc_ref(v_val_251_);
lean_inc(v_optionName_249_);
v___x_256_ = l_Lean_Elab_validateOptionValue___redArg(v_inst_246_, v_inst_248_, v_optionName_249_, v_decl_250_, v_val_251_);
v___f_257_ = lean_alloc_closure((void*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___redArg___lam__0), 5, 4);
lean_closure_set(v___f_257_, 0, v___x_252_);
lean_closure_set(v___f_257_, 1, v_optionName_249_);
lean_closure_set(v___f_257_, 2, v_val_251_);
lean_closure_set(v___f_257_, 3, v_toPure_255_);
lean_inc(v_toBind_254_);
v___f_258_ = lean_alloc_closure((void*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___redArg___lam__1), 4, 3);
lean_closure_set(v___f_258_, 0, v_toBind_254_);
lean_closure_set(v___f_258_, 1, v_inst_247_);
lean_closure_set(v___f_258_, 2, v___f_257_);
v___x_259_ = lean_apply_4(v_toBind_254_, lean_box(0), lean_box(0), v___x_256_, v___f_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___redArg___boxed(lean_object* v_inst_260_, lean_object* v_inst_261_, lean_object* v_inst_262_, lean_object* v_optionName_263_, lean_object* v_decl_264_, lean_object* v_val_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___redArg(v_inst_260_, v_inst_261_, v_inst_262_, v_optionName_263_, v_decl_264_, v_val_265_);
lean_dec_ref(v_decl_264_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption(lean_object* v_m_267_, lean_object* v_inst_268_, lean_object* v_inst_269_, lean_object* v_inst_270_, lean_object* v_optionName_271_, lean_object* v_decl_272_, lean_object* v_val_273_){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___redArg(v_inst_268_, v_inst_269_, v_inst_270_, v_optionName_271_, v_decl_272_, v_val_273_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___boxed(lean_object* v_m_275_, lean_object* v_inst_276_, lean_object* v_inst_277_, lean_object* v_inst_278_, lean_object* v_optionName_279_, lean_object* v_decl_280_, lean_object* v_val_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption(v_m_275_, v_inst_276_, v_inst_277_, v_inst_278_, v_optionName_279_, v_decl_280_, v_val_281_);
lean_dec_ref(v_decl_280_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg___lam__0(lean_object* v_ref_283_, lean_object* v_ex_284_){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_285_ = lean_io_error_to_string(v_ex_284_);
v___x_286_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_286_, 0, v___x_285_);
v___x_287_ = l_Lean_MessageData_ofFormat(v___x_286_);
v___x_288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_288_, 0, v_ref_283_);
lean_ctor_set(v___x_288_, 1, v___x_287_);
return v___x_288_;
}
}
static lean_object* _init_l_Lean_Elab_elabSetOption___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_290_ = ((lean_object*)(l_Lean_Elab_elabSetOption___redArg___lam__1___closed__0));
v___x_291_ = l_Lean_stringToMessageData(v___x_290_);
return v___x_291_;
}
}
static lean_object* _init_l_Lean_Elab_elabSetOption___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_293_ = ((lean_object*)(l_Lean_Elab_elabSetOption___redArg___lam__1___closed__2));
v___x_294_ = l_Lean_stringToMessageData(v___x_293_);
return v___x_294_;
}
}
static lean_object* _init_l_Lean_Elab_elabSetOption___redArg___lam__1___closed__4(void){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_295_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__12));
v___x_296_ = l_Lean_stringToMessageData(v___x_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg___lam__1(lean_object* v_val_297_, lean_object* v_defValue_298_, lean_object* v_inst_299_, lean_object* v_inst_300_, lean_object* v_optionName_301_, lean_object* v_inst_302_, lean_object* v_decl_303_, lean_object* v_____r_304_){
_start:
{
lean_object* v___x_319_; 
v___x_319_ = l_Lean_Syntax_isStrLit_x3f(v_val_297_);
if (lean_obj_tag(v___x_319_) == 0)
{
lean_object* v___x_320_; 
v___x_320_ = l_Lean_Syntax_isNatLit_x3f(v_val_297_);
if (lean_obj_tag(v___x_320_) == 0)
{
if (lean_obj_tag(v_val_297_) == 2)
{
lean_object* v_val_321_; lean_object* v___x_322_; uint8_t v___x_323_; 
v_val_321_ = lean_ctor_get(v_val_297_, 1);
v___x_322_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__10));
v___x_323_ = lean_string_dec_eq(v_val_321_, v___x_322_);
if (v___x_323_ == 0)
{
lean_object* v___x_324_; uint8_t v___x_325_; 
v___x_324_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__8));
v___x_325_ = lean_string_dec_eq(v_val_321_, v___x_324_);
if (v___x_325_ == 0)
{
lean_dec(v_inst_302_);
goto v___jp_305_;
}
else
{
lean_object* v___x_326_; lean_object* v___x_327_; 
lean_dec_ref(v_val_297_);
v___x_326_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_326_, 0, v___x_323_);
v___x_327_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___redArg(v_inst_299_, v_inst_302_, v_inst_300_, v_optionName_301_, v_decl_303_, v___x_326_);
return v___x_327_;
}
}
else
{
lean_object* v___x_328_; lean_object* v___x_329_; 
lean_dec_ref(v_val_297_);
v___x_328_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_328_, 0, v___x_323_);
v___x_329_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___redArg(v_inst_299_, v_inst_302_, v_inst_300_, v_optionName_301_, v_decl_303_, v___x_328_);
return v___x_329_;
}
}
else
{
lean_dec(v_inst_302_);
goto v___jp_305_;
}
}
else
{
lean_object* v_val_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_338_; 
lean_dec(v_val_297_);
v_val_330_ = lean_ctor_get(v___x_320_, 0);
v_isSharedCheck_338_ = !lean_is_exclusive(v___x_320_);
if (v_isSharedCheck_338_ == 0)
{
v___x_332_ = v___x_320_;
v_isShared_333_ = v_isSharedCheck_338_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_val_330_);
lean_dec(v___x_320_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_338_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_335_; 
if (v_isShared_333_ == 0)
{
lean_ctor_set_tag(v___x_332_, 3);
v___x_335_ = v___x_332_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v_val_330_);
v___x_335_ = v_reuseFailAlloc_337_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
lean_object* v___x_336_; 
v___x_336_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___redArg(v_inst_299_, v_inst_302_, v_inst_300_, v_optionName_301_, v_decl_303_, v___x_335_);
return v___x_336_;
}
}
}
}
else
{
lean_object* v_val_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_347_; 
lean_dec(v_val_297_);
v_val_339_ = lean_ctor_get(v___x_319_, 0);
v_isSharedCheck_347_ = !lean_is_exclusive(v___x_319_);
if (v_isSharedCheck_347_ == 0)
{
v___x_341_ = v___x_319_;
v_isShared_342_ = v_isSharedCheck_347_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_val_339_);
lean_dec(v___x_319_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_347_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___x_344_; 
if (v_isShared_342_ == 0)
{
lean_ctor_set_tag(v___x_341_, 0);
v___x_344_ = v___x_341_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v_val_339_);
v___x_344_ = v_reuseFailAlloc_346_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
lean_object* v___x_345_; 
v___x_345_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___redArg(v_inst_299_, v_inst_302_, v_inst_300_, v_optionName_301_, v_decl_303_, v___x_344_);
return v___x_345_;
}
}
}
v___jp_305_:
{
lean_object* v___x_306_; 
v___x_306_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f(v_defValue_298_);
if (lean_obj_tag(v___x_306_) == 1)
{
lean_object* v_val_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
lean_dec(v_optionName_301_);
v_val_307_ = lean_ctor_get(v___x_306_, 0);
lean_inc(v_val_307_);
lean_dec_ref(v___x_306_);
v___x_308_ = lean_obj_once(&l_Lean_Elab_elabSetOption___redArg___lam__1___closed__1, &l_Lean_Elab_elabSetOption___redArg___lam__1___closed__1_once, _init_l_Lean_Elab_elabSetOption___redArg___lam__1___closed__1);
v___x_309_ = l_Lean_MessageData_ofSyntax(v_val_297_);
v___x_310_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_310_, 0, v___x_308_);
lean_ctor_set(v___x_310_, 1, v___x_309_);
v___x_311_ = lean_obj_once(&l_Lean_Elab_elabSetOption___redArg___lam__1___closed__3, &l_Lean_Elab_elabSetOption___redArg___lam__1___closed__3_once, _init_l_Lean_Elab_elabSetOption___redArg___lam__1___closed__3);
v___x_312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_312_, 0, v___x_310_);
lean_ctor_set(v___x_312_, 1, v___x_311_);
v___x_313_ = l_Lean_MessageData_ofExpr(v_val_307_);
v___x_314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_314_, 0, v___x_312_);
lean_ctor_set(v___x_314_, 1, v___x_313_);
v___x_315_ = lean_obj_once(&l_Lean_Elab_elabSetOption___redArg___lam__1___closed__4, &l_Lean_Elab_elabSetOption___redArg___lam__1___closed__4_once, _init_l_Lean_Elab_elabSetOption___redArg___lam__1___closed__4);
v___x_316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_316_, 0, v___x_314_);
lean_ctor_set(v___x_316_, 1, v___x_315_);
v___x_317_ = l_Lean_throwError___redArg(v_inst_299_, v_inst_300_, v___x_316_);
return v___x_317_;
}
else
{
lean_object* v___x_318_; 
lean_dec(v___x_306_);
lean_dec(v_val_297_);
v___x_318_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg(v_inst_299_, v_inst_300_, v_optionName_301_);
return v___x_318_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg___lam__1___boxed(lean_object* v_val_348_, lean_object* v_defValue_349_, lean_object* v_inst_350_, lean_object* v_inst_351_, lean_object* v_optionName_352_, lean_object* v_inst_353_, lean_object* v_decl_354_, lean_object* v_____r_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Lean_Elab_elabSetOption___redArg___lam__1(v_val_348_, v_defValue_349_, v_inst_350_, v_inst_351_, v_optionName_352_, v_inst_353_, v_decl_354_, v_____r_355_);
lean_dec_ref(v_decl_354_);
lean_dec_ref(v_defValue_349_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg___lam__2(lean_object* v_val_357_, lean_object* v_inst_358_, lean_object* v_inst_359_, lean_object* v_optionName_360_, lean_object* v_inst_361_, lean_object* v_id_362_, lean_object* v_inst_363_, lean_object* v_toBind_364_, lean_object* v_decl_365_){
_start:
{
lean_object* v_declName_366_; lean_object* v_defValue_367_; lean_object* v___f_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v_declName_366_ = lean_ctor_get(v_decl_365_, 1);
lean_inc(v_declName_366_);
v_defValue_367_ = lean_ctor_get(v_decl_365_, 2);
lean_inc_ref(v_defValue_367_);
lean_inc(v_optionName_360_);
lean_inc_ref(v_inst_358_);
v___f_368_ = lean_alloc_closure((void*)(l_Lean_Elab_elabSetOption___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_368_, 0, v_val_357_);
lean_closure_set(v___f_368_, 1, v_defValue_367_);
lean_closure_set(v___f_368_, 2, v_inst_358_);
lean_closure_set(v___f_368_, 3, v_inst_359_);
lean_closure_set(v___f_368_, 4, v_optionName_360_);
lean_closure_set(v___f_368_, 5, v_inst_361_);
lean_closure_set(v___f_368_, 6, v_decl_365_);
v___x_369_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_369_, 0, v_id_362_);
lean_ctor_set(v___x_369_, 1, v_optionName_360_);
lean_ctor_set(v___x_369_, 2, v_declName_366_);
v___x_370_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_370_, 0, v___x_369_);
v___x_371_ = l_Lean_Elab_pushInfoLeaf___redArg(v_inst_358_, v_inst_363_, v___x_370_);
v___x_372_ = lean_apply_4(v_toBind_364_, lean_box(0), lean_box(0), v___x_371_, v___f_368_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg___lam__3(lean_object* v_id_373_, lean_object* v_val_374_, lean_object* v_inst_375_, lean_object* v_inst_376_, lean_object* v_inst_377_, lean_object* v_inst_378_, lean_object* v_toBind_379_, lean_object* v___f_380_, lean_object* v_inst_381_, lean_object* v_____r_382_){
_start:
{
lean_object* v___x_383_; lean_object* v_optionName_384_; lean_object* v___f_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_383_ = l_Lean_Syntax_getId(v_id_373_);
v_optionName_384_ = lean_erase_macro_scopes(v___x_383_);
lean_inc(v_toBind_379_);
lean_inc(v_optionName_384_);
v___f_385_ = lean_alloc_closure((void*)(l_Lean_Elab_elabSetOption___redArg___lam__2), 9, 8);
lean_closure_set(v___f_385_, 0, v_val_374_);
lean_closure_set(v___f_385_, 1, v_inst_375_);
lean_closure_set(v___f_385_, 2, v_inst_376_);
lean_closure_set(v___f_385_, 3, v_optionName_384_);
lean_closure_set(v___f_385_, 4, v_inst_377_);
lean_closure_set(v___f_385_, 5, v_id_373_);
lean_closure_set(v___f_385_, 6, v_inst_378_);
lean_closure_set(v___f_385_, 7, v_toBind_379_);
v___x_386_ = lean_alloc_closure((void*)(l_Lean_getOptionDecl___boxed), 2, 1);
lean_closure_set(v___x_386_, 0, v_optionName_384_);
v___x_387_ = lean_alloc_closure((void*)(l_IO_toEIO___boxed), 5, 4);
lean_closure_set(v___x_387_, 0, lean_box(0));
lean_closure_set(v___x_387_, 1, lean_box(0));
lean_closure_set(v___x_387_, 2, v___f_380_);
lean_closure_set(v___x_387_, 3, v___x_386_);
v___x_388_ = lean_apply_2(v_inst_381_, lean_box(0), v___x_387_);
v___x_389_ = lean_apply_4(v_toBind_379_, lean_box(0), lean_box(0), v___x_388_, v___f_385_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg___lam__4(lean_object* v_id_390_, lean_object* v_val_391_, lean_object* v_inst_392_, lean_object* v_inst_393_, lean_object* v_inst_394_, lean_object* v_inst_395_, lean_object* v_toBind_396_, lean_object* v_inst_397_, lean_object* v_ref_398_){
_start:
{
lean_object* v___f_399_; lean_object* v___f_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
lean_inc(v_ref_398_);
v___f_399_ = lean_alloc_closure((void*)(l_Lean_Elab_elabSetOption___redArg___lam__0), 2, 1);
lean_closure_set(v___f_399_, 0, v_ref_398_);
lean_inc(v_toBind_396_);
lean_inc_ref(v_inst_395_);
lean_inc_ref(v_inst_392_);
v___f_400_ = lean_alloc_closure((void*)(l_Lean_Elab_elabSetOption___redArg___lam__3), 10, 9);
lean_closure_set(v___f_400_, 0, v_id_390_);
lean_closure_set(v___f_400_, 1, v_val_391_);
lean_closure_set(v___f_400_, 2, v_inst_392_);
lean_closure_set(v___f_400_, 3, v_inst_393_);
lean_closure_set(v___f_400_, 4, v_inst_394_);
lean_closure_set(v___f_400_, 5, v_inst_395_);
lean_closure_set(v___f_400_, 6, v_toBind_396_);
lean_closure_set(v___f_400_, 7, v___f_399_);
lean_closure_set(v___f_400_, 8, v_inst_397_);
v___x_401_ = l_Lean_Syntax_getArgs(v_ref_398_);
v___x_402_ = lean_unsigned_to_nat(3u);
v___x_403_ = lean_unsigned_to_nat(0u);
v___x_404_ = l_Array_toSubarray___redArg(v___x_401_, v___x_403_, v___x_402_);
v___x_405_ = l_Subarray_copy___redArg(v___x_404_);
v___x_406_ = l_Lean_Syntax_setArgs(v_ref_398_, v___x_405_);
v___x_407_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
v___x_408_ = l_Lean_Elab_addCompletionInfo___redArg(v_inst_392_, v_inst_395_, v___x_407_);
v___x_409_ = lean_apply_4(v_toBind_396_, lean_box(0), lean_box(0), v___x_408_, v___f_400_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg(lean_object* v_inst_410_, lean_object* v_inst_411_, lean_object* v_inst_412_, lean_object* v_inst_413_, lean_object* v_inst_414_, lean_object* v_id_415_, lean_object* v_val_416_){
_start:
{
lean_object* v_toMonadRef_417_; lean_object* v_toBind_418_; lean_object* v_getRef_419_; lean_object* v___f_420_; lean_object* v___x_421_; 
v_toMonadRef_417_ = lean_ctor_get(v_inst_412_, 1);
v_toBind_418_ = lean_ctor_get(v_inst_410_, 1);
lean_inc(v_toBind_418_);
v_getRef_419_ = lean_ctor_get(v_toMonadRef_417_, 0);
lean_inc(v_getRef_419_);
lean_inc(v_toBind_418_);
v___f_420_ = lean_alloc_closure((void*)(l_Lean_Elab_elabSetOption___redArg___lam__4), 9, 8);
lean_closure_set(v___f_420_, 0, v_id_415_);
lean_closure_set(v___f_420_, 1, v_val_416_);
lean_closure_set(v___f_420_, 2, v_inst_410_);
lean_closure_set(v___f_420_, 3, v_inst_412_);
lean_closure_set(v___f_420_, 4, v_inst_411_);
lean_closure_set(v___f_420_, 5, v_inst_414_);
lean_closure_set(v___f_420_, 6, v_toBind_418_);
lean_closure_set(v___f_420_, 7, v_inst_413_);
v___x_421_ = lean_apply_4(v_toBind_418_, lean_box(0), lean_box(0), v_getRef_419_, v___f_420_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption(lean_object* v_m_422_, lean_object* v_inst_423_, lean_object* v_inst_424_, lean_object* v_inst_425_, lean_object* v_inst_426_, lean_object* v_inst_427_, lean_object* v_id_428_, lean_object* v_val_429_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = l_Lean_Elab_elabSetOption___redArg(v_inst_423_, v_inst_424_, v_inst_425_, v_inst_426_, v_inst_427_, v_id_428_, v_val_429_);
return v___x_430_;
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

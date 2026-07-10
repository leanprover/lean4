// Lean compiler output
// Module: Lean.Elab.Import
// Imports: public import Lean.Parser.Module meta import Lean.Parser.Module import Lean.Compiler.ModPkgExt public import Lean.DeprecatedModule import Init.Data.String.Modify
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
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_Parser_mkInputContext___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Parser_parseHeader(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lean_instInhabitedImport_default;
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t lean_bool_not(uint8_t);
extern lean_object* l_Lean_linter_deprecated_module;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdx_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Environment_getDeprecatedModuleByIdx_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_formatDeprecatedModuleWarning(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_Syntax_getTrailing_x3f(lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_String_Slice_posGE___redArg(lean_object*, lean_object*);
lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_get_stdout();
lean_object* l_Lean_findOLean(lean_object*);
lean_object* l_Lean_Environment_setMainModule(lean_object*, lean_object*);
extern lean_object* l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
lean_object* l_Lean_PersistentEnvExtension_setState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
lean_object* l_Char_utf8Size(uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_importModules(lean_object*, lean_object*, uint32_t, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_mkEmptyEnvironment(uint32_t);
lean_object* lean_io_error_to_string(lean_object*);
extern lean_object* l_Lean_Elab_inServer;
lean_object* l_Lean_getSrcSearchPath();
lean_object* l_Lean_findLean(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_HeaderSyntax_startPos(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_HeaderSyntax_startPos___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_HeaderSyntax_isModule(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_HeaderSyntax_isModule___boxed(lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__1(lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Module"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "import"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__4_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__4_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__3_value),LEAN_SCALAR_PTR_LITERAL(177, 219, 158, 40, 50, 143, 61, 44)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Lean.Elab.Import"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Lean.Elab.HeaderSyntax.imports"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__6_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__7_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "all"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__9_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__10_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__10_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__10_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__9_value),LEAN_SCALAR_PTR_LITERAL(107, 73, 92, 3, 207, 252, 164, 131)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__10_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__11_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__12_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__12_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__12_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__11_value),LEAN_SCALAR_PTR_LITERAL(89, 228, 64, 55, 26, 167, 248, 235)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__12_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__13 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__13_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__14_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__14_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__14_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__13_value),LEAN_SCALAR_PTR_LITERAL(198, 166, 14, 39, 152, 190, 236, 172)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__14 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__14_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2(lean_object*, uint8_t, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_HeaderSyntax_imports___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "header"};
static const lean_object* l_Lean_Elab_HeaderSyntax_imports___closed__0 = (const lean_object*)&l_Lean_Elab_HeaderSyntax_imports___closed__0_value;
static const lean_ctor_object l_Lean_Elab_HeaderSyntax_imports___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_HeaderSyntax_imports___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_HeaderSyntax_imports___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_HeaderSyntax_imports___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_HeaderSyntax_imports___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l_Lean_Elab_HeaderSyntax_imports___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_HeaderSyntax_imports___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_HeaderSyntax_imports___closed__0_value),LEAN_SCALAR_PTR_LITERAL(40, 173, 92, 3, 94, 219, 131, 202)}};
static const lean_object* l_Lean_Elab_HeaderSyntax_imports___closed__1 = (const lean_object*)&l_Lean_Elab_HeaderSyntax_imports___closed__1_value;
static lean_once_cell_t l_Lean_Elab_HeaderSyntax_imports___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_HeaderSyntax_imports___closed__2;
static const lean_array_object l_Lean_Elab_HeaderSyntax_imports___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_HeaderSyntax_imports___closed__3 = (const lean_object*)&l_Lean_Elab_HeaderSyntax_imports___closed__3_value;
static const lean_string_object l_Lean_Elab_HeaderSyntax_imports___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Init"};
static const lean_object* l_Lean_Elab_HeaderSyntax_imports___closed__4 = (const lean_object*)&l_Lean_Elab_HeaderSyntax_imports___closed__4_value;
static const lean_ctor_object l_Lean_Elab_HeaderSyntax_imports___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_HeaderSyntax_imports___closed__4_value),LEAN_SCALAR_PTR_LITERAL(152, 102, 12, 179, 200, 220, 30, 26)}};
static const lean_object* l_Lean_Elab_HeaderSyntax_imports___closed__5 = (const lean_object*)&l_Lean_Elab_HeaderSyntax_imports___closed__5_value;
static const lean_string_object l_Lean_Elab_HeaderSyntax_imports___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "prelude"};
static const lean_object* l_Lean_Elab_HeaderSyntax_imports___closed__6 = (const lean_object*)&l_Lean_Elab_HeaderSyntax_imports___closed__6_value;
static const lean_ctor_object l_Lean_Elab_HeaderSyntax_imports___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_HeaderSyntax_imports___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_HeaderSyntax_imports___closed__7_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_HeaderSyntax_imports___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_HeaderSyntax_imports___closed__7_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l_Lean_Elab_HeaderSyntax_imports___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_HeaderSyntax_imports___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_HeaderSyntax_imports___closed__6_value),LEAN_SCALAR_PTR_LITERAL(182, 6, 18, 235, 50, 88, 101, 248)}};
static const lean_object* l_Lean_Elab_HeaderSyntax_imports___closed__7 = (const lean_object*)&l_Lean_Elab_HeaderSyntax_imports___closed__7_value;
static const lean_string_object l_Lean_Elab_HeaderSyntax_imports___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "moduleTk"};
static const lean_object* l_Lean_Elab_HeaderSyntax_imports___closed__8 = (const lean_object*)&l_Lean_Elab_HeaderSyntax_imports___closed__8_value;
static const lean_ctor_object l_Lean_Elab_HeaderSyntax_imports___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_HeaderSyntax_imports___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_HeaderSyntax_imports___closed__9_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_HeaderSyntax_imports___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_HeaderSyntax_imports___closed__9_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l_Lean_Elab_HeaderSyntax_imports___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_HeaderSyntax_imports___closed__9_value_aux_2),((lean_object*)&l_Lean_Elab_HeaderSyntax_imports___closed__8_value),LEAN_SCALAR_PTR_LITERAL(198, 239, 28, 252, 21, 233, 71, 221)}};
static const lean_object* l_Lean_Elab_HeaderSyntax_imports___closed__9 = (const lean_object*)&l_Lean_Elab_HeaderSyntax_imports___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Elab_HeaderSyntax_imports(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_HeaderSyntax_imports___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_HeaderSyntax_toModuleHeader(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_headerToImports(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_headerToImports___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_checkDeprecatedImports_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_checkDeprecatedImports_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_spec__2___redArg(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "deprecated_module: ignore"};
static const lean_object* l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__0 = (const lean_object*)&l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__0_value;
static lean_once_cell_t l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__1;
static lean_once_cell_t l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__2;
static lean_once_cell_t l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__3;
static lean_once_cell_t l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__4;
static lean_once_cell_t l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__5;
static const lean_ctor_object l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__6 = (const lean_object*)&l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__6_value;
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkDeprecatedImports_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkDeprecatedImports_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4_spec__5___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4_spec__5___closed__0_value;
static const lean_ctor_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4_spec__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4_spec__5___closed__1 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4_spec__5___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4_spec__5(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "deprecatedModuleExt"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___closed__2_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(112, 167, 11, 228, 166, 253, 145, 197)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedImports(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedImports___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__5;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__6;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__7;
static lean_once_cell_t l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars;
static const lean_string_object l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "CON"};
static const lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__0 = (const lean_object*)&l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "PRN"};
static const lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__1 = (const lean_object*)&l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "AUX"};
static const lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__2 = (const lean_object*)&l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "NUL"};
static const lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__3 = (const lean_object*)&l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "COM1"};
static const lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__4 = (const lean_object*)&l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "COM2"};
static const lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__5 = (const lean_object*)&l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "COM3"};
static const lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__6 = (const lean_object*)&l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__6_value;
static const lean_string_object l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "COM4"};
static const lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__7 = (const lean_object*)&l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__7_value;
static const lean_string_object l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "COM5"};
static const lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__8 = (const lean_object*)&l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__8_value;
static const lean_string_object l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "COM6"};
static const lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__9 = (const lean_object*)&l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__9_value;
static const lean_string_object l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "COM7"};
static const lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__10 = (const lean_object*)&l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__10_value;
static const lean_string_object l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "COM8"};
static const lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__11 = (const lean_object*)&l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__11_value;
static const lean_string_object l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "COM9"};
static const lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__12 = (const lean_object*)&l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__12_value;
static const lean_string_object l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 4, .m_data = "COM¹"};
static const lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__13 = (const lean_object*)&l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__13_value;
static const lean_string_object l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 4, .m_data = "COM²"};
static const lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__14 = (const lean_object*)&l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__14_value;
static const lean_string_object l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 4, .m_data = "COM³"};
static const lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__15 = (const lean_object*)&l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__15_value;
static const lean_string_object l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LPT1"};
static const lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__16 = (const lean_object*)&l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__16_value;
static const lean_string_object l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LPT2"};
static const lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__17 = (const lean_object*)&l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__17_value;
static const lean_string_object l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LPT3"};
static const lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__18 = (const lean_object*)&l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__18_value;
static const lean_string_object l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LPT4"};
static const lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__19 = (const lean_object*)&l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__19_value;
static const lean_string_object l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LPT5"};
static const lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__20 = (const lean_object*)&l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__20_value;
static const lean_string_object l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LPT6"};
static const lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__21 = (const lean_object*)&l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__21_value;
static const lean_string_object l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LPT7"};
static const lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__22 = (const lean_object*)&l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__22_value;
static const lean_string_object l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LPT8"};
static const lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__23 = (const lean_object*)&l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__23_value;
static const lean_string_object l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LPT9"};
static const lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__24 = (const lean_object*)&l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__24_value;
static const lean_string_object l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 4, .m_data = "LPT¹"};
static const lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__25 = (const lean_object*)&l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__25_value;
static const lean_string_object l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 4, .m_data = "LPT²"};
static const lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__26 = (const lean_object*)&l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__26_value;
static const lean_string_object l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 4, .m_data = "LPT³"};
static const lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__27 = (const lean_object*)&l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__27_value;
static const lean_array_object l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*28, .m_other = 0, .m_tag = 246}, .m_size = 28, .m_capacity = 28, .m_data = {((lean_object*)&l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__0_value),((lean_object*)&l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__1_value),((lean_object*)&l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__2_value),((lean_object*)&l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__3_value),((lean_object*)&l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__4_value),((lean_object*)&l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__5_value),((lean_object*)&l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__6_value),((lean_object*)&l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__7_value),((lean_object*)&l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__8_value),((lean_object*)&l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__9_value),((lean_object*)&l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__10_value),((lean_object*)&l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__11_value),((lean_object*)&l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__12_value),((lean_object*)&l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__13_value),((lean_object*)&l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__14_value),((lean_object*)&l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__15_value),((lean_object*)&l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__16_value),((lean_object*)&l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__17_value),((lean_object*)&l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__18_value),((lean_object*)&l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__19_value),((lean_object*)&l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__20_value),((lean_object*)&l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__21_value),((lean_object*)&l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__22_value),((lean_object*)&l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__23_value),((lean_object*)&l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__24_value),((lean_object*)&l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__25_value),((lean_object*)&l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__26_value),((lean_object*)&l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__27_value)}};
static const lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__28 = (const lean_object*)&l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__28_value;
LEAN_EXPORT const lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames = (const lean_object*)&l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__28_value;
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__0(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2_spec__3___redArg(lean_object*, uint32_t, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__1_spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__1___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__0;
static const lean_string_object l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "contains character '"};
static const lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__1 = (const lean_object*)&l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "' which is forbidden on some operating systems"};
static const lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__2 = (const lean_object*)&l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__3 = (const lean_object*)&l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "' is a reserved file name on some operating systems"};
static const lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__4 = (const lean_object*)&l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability(lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2_spec__3(lean_object*, uint32_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Import_0__Lean_Elab_checkModuleNamePortability_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "module name '"};
static const lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_checkModuleNamePortability_go___closed__0 = (const lean_object*)&l___private_Lean_Elab_Import_0__Lean_Elab_checkModuleNamePortability_go___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Import_0__Lean_Elab_checkModuleNamePortability_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "' is not portable: "};
static const lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_checkModuleNamePortability_go___closed__1 = (const lean_object*)&l___private_Lean_Elab_Import_0__Lean_Elab_checkModuleNamePortability_go___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_checkModuleNamePortability_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_checkModuleNamePortability_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkModuleNamePortability(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkModuleNamePortability___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_processHeaderCore(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_processHeaderCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_processHeader(lean_object*, lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_processHeader___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_parseImports___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "<input>"};
static const lean_object* l_Lean_Elab_parseImports___closed__0 = (const lean_object*)&l_Lean_Elab_parseImports___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_parseImports(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_parseImports___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00Lean_Elab_printImports_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00Lean_Elab_printImports_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_println___at___00Lean_Elab_printImports_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_IO_println___at___00Lean_Elab_printImports_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImports_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImports_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_printImports(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_printImports___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImportSrcs_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImportSrcs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_printImportSrcs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_printImportSrcs___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_HeaderSyntax_startPos(lean_object* v_header_1_){
_start:
{
uint8_t v___x_2_; lean_object* v___x_3_; 
v___x_2_ = 0;
v___x_3_ = l_Lean_Syntax_getPos_x3f(v_header_1_, v___x_2_);
if (lean_obj_tag(v___x_3_) == 0)
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(0u);
return v___x_4_;
}
else
{
lean_object* v_val_5_; 
v_val_5_ = lean_ctor_get(v___x_3_, 0);
lean_inc(v_val_5_);
lean_dec_ref_known(v___x_3_, 1);
return v_val_5_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_HeaderSyntax_startPos___boxed(lean_object* v_header_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = l_Lean_Elab_HeaderSyntax_startPos(v_header_6_);
lean_dec(v_header_6_);
return v_res_7_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_HeaderSyntax_isModule(lean_object* v_header_8_){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; uint8_t v___x_11_; uint8_t v___x_12_; 
v___x_9_ = lean_unsigned_to_nat(0u);
v___x_10_ = l_Lean_Syntax_getArg(v_header_8_, v___x_9_);
v___x_11_ = l_Lean_Syntax_isNone(v___x_10_);
lean_dec(v___x_10_);
v___x_12_ = lean_bool_not(v___x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_HeaderSyntax_isModule___boxed(lean_object* v_header_13_){
_start:
{
uint8_t v_res_14_; lean_object* v_r_15_; 
v_res_14_ = l_Lean_Elab_HeaderSyntax_isModule(v_header_13_);
lean_dec(v_header_13_);
v_r_15_ = lean_box(v_res_14_);
return v_r_15_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__0___closed__0(void){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = l_Array_instInhabited(lean_box(0));
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__0(lean_object* v_msg_17_){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_18_ = lean_obj_once(&l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__0___closed__0, &l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__0___closed__0_once, _init_l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__0___closed__0);
v___x_19_ = lean_panic_fn_borrowed(v___x_18_, v_msg_17_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__1(lean_object* v_msg_20_){
_start:
{
lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_21_ = l_Lean_instInhabitedImport_default;
v___x_22_ = lean_panic_fn_borrowed(v___x_21_, v_msg_20_);
return v___x_22_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8(void){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_35_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__7));
v___x_36_ = lean_unsigned_to_nat(13u);
v___x_37_ = lean_unsigned_to_nat(40u);
v___x_38_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__6));
v___x_39_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__5));
v___x_40_ = l_mkPanicMessageWithDecl(v___x_39_, v___x_38_, v___x_37_, v___x_36_, v___x_35_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2(lean_object* v_moduleTk_59_, uint8_t v___x_60_, size_t v_sz_61_, size_t v_i_62_, lean_object* v_bs_63_){
_start:
{
uint8_t v___x_64_; 
v___x_64_ = lean_usize_dec_lt(v_i_62_, v_sz_61_);
if (v___x_64_ == 0)
{
return v_bs_63_;
}
else
{
lean_object* v___x_65_; lean_object* v_v_66_; lean_object* v___x_67_; lean_object* v_bs_x27_68_; lean_object* v___y_70_; uint8_t v___y_76_; lean_object* v___y_77_; uint8_t v___y_78_; lean_object* v___y_79_; uint8_t v___y_80_; lean_object* v___y_85_; uint8_t v___y_86_; uint8_t v___y_87_; lean_object* v___y_88_; uint8_t v___y_89_; lean_object* v___y_91_; lean_object* v___y_92_; uint8_t v___y_93_; lean_object* v___y_94_; uint8_t v___y_95_; uint8_t v___x_97_; 
v___x_65_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__4));
v_v_66_ = lean_array_uget(v_bs_63_, v_i_62_);
v___x_67_ = lean_unsigned_to_nat(0u);
v_bs_x27_68_ = lean_array_uset(v_bs_63_, v_i_62_, v___x_67_);
lean_inc(v_v_66_);
v___x_97_ = l_Lean_Syntax_isOfKind(v_v_66_, v___x_65_);
if (v___x_97_ == 0)
{
lean_object* v___x_98_; lean_object* v___x_99_; 
lean_dec(v_v_66_);
v___x_98_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8);
v___x_99_ = l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__1(v___x_98_);
v___y_70_ = v___x_99_;
goto v___jp_69_;
}
else
{
lean_object* v___y_101_; lean_object* v___y_102_; lean_object* v_allTk_103_; lean_object* v___x_113_; lean_object* v___y_115_; lean_object* v_metaTk_116_; lean_object* v_publicTk_132_; lean_object* v___x_146_; uint8_t v___x_147_; 
v___x_113_ = lean_unsigned_to_nat(1u);
v___x_146_ = l_Lean_Syntax_getArg(v_v_66_, v___x_67_);
v___x_147_ = l_Lean_Syntax_isNone(v___x_146_);
if (v___x_147_ == 0)
{
uint8_t v___x_148_; 
lean_inc(v___x_146_);
v___x_148_ = l_Lean_Syntax_matchesNull(v___x_146_, v___x_113_);
if (v___x_148_ == 0)
{
lean_object* v___x_149_; lean_object* v___x_150_; 
lean_dec(v___x_146_);
lean_dec(v_v_66_);
v___x_149_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8);
v___x_150_ = l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__1(v___x_149_);
v___y_70_ = v___x_150_;
goto v___jp_69_;
}
else
{
lean_object* v___x_151_; lean_object* v___x_152_; uint8_t v___x_153_; 
v___x_151_ = l_Lean_Syntax_getArg(v___x_146_, v___x_67_);
lean_dec(v___x_146_);
v___x_152_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__14));
lean_inc(v___x_151_);
v___x_153_ = l_Lean_Syntax_isOfKind(v___x_151_, v___x_152_);
if (v___x_153_ == 0)
{
lean_object* v___x_154_; lean_object* v___x_155_; 
lean_dec(v___x_151_);
lean_dec(v_v_66_);
v___x_154_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8);
v___x_155_ = l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__1(v___x_154_);
v___y_70_ = v___x_155_;
goto v___jp_69_;
}
else
{
lean_object* v_publicTk_156_; lean_object* v___x_157_; 
v_publicTk_156_ = l_Lean_Syntax_getArg(v___x_151_, v___x_67_);
lean_dec(v___x_151_);
v___x_157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_157_, 0, v_publicTk_156_);
v_publicTk_132_ = v___x_157_;
goto v___jp_131_;
}
}
}
else
{
lean_object* v___x_158_; 
lean_dec(v___x_146_);
v___x_158_ = lean_box(0);
v_publicTk_132_ = v___x_158_;
goto v___jp_131_;
}
v___jp_100_:
{
lean_object* v___x_104_; lean_object* v___x_105_; uint8_t v___x_106_; 
v___x_104_ = lean_unsigned_to_nat(5u);
v___x_105_ = l_Lean_Syntax_getArg(v_v_66_, v___x_104_);
v___x_106_ = l_Lean_Syntax_matchesNull(v___x_105_, v___x_67_);
if (v___x_106_ == 0)
{
lean_object* v___x_107_; lean_object* v___x_108_; 
lean_dec(v_allTk_103_);
lean_dec(v___y_102_);
lean_dec(v___y_101_);
lean_dec(v_v_66_);
v___x_107_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8);
v___x_108_ = l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__1(v___x_107_);
v___y_70_ = v___x_108_;
goto v___jp_69_;
}
else
{
lean_object* v___x_109_; lean_object* v_n_110_; lean_object* v___x_111_; 
v___x_109_ = lean_unsigned_to_nat(4u);
v_n_110_ = l_Lean_Syntax_getArg(v_v_66_, v___x_109_);
lean_dec(v_v_66_);
v___x_111_ = l_Lean_TSyntax_getId(v_n_110_);
lean_dec(v_n_110_);
if (lean_obj_tag(v_allTk_103_) == 0)
{
uint8_t v___x_112_; 
v___x_112_ = 0;
v___y_91_ = v___y_101_;
v___y_92_ = v___x_111_;
v___y_93_ = v___x_106_;
v___y_94_ = v___y_102_;
v___y_95_ = v___x_112_;
goto v___jp_90_;
}
else
{
lean_dec_ref_known(v_allTk_103_, 1);
v___y_91_ = v___y_101_;
v___y_92_ = v___x_111_;
v___y_93_ = v___x_106_;
v___y_94_ = v___y_102_;
v___y_95_ = v___x_106_;
goto v___jp_90_;
}
}
}
v___jp_114_:
{
lean_object* v___x_117_; lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_117_ = lean_unsigned_to_nat(3u);
v___x_118_ = l_Lean_Syntax_getArg(v_v_66_, v___x_117_);
v___x_119_ = l_Lean_Syntax_isNone(v___x_118_);
if (v___x_119_ == 0)
{
uint8_t v___x_120_; 
lean_inc(v___x_118_);
v___x_120_ = l_Lean_Syntax_matchesNull(v___x_118_, v___x_113_);
if (v___x_120_ == 0)
{
lean_object* v___x_121_; lean_object* v___x_122_; 
lean_dec(v___x_118_);
lean_dec(v_metaTk_116_);
lean_dec(v___y_115_);
lean_dec(v_v_66_);
v___x_121_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8);
v___x_122_ = l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__1(v___x_121_);
v___y_70_ = v___x_122_;
goto v___jp_69_;
}
else
{
lean_object* v___x_123_; lean_object* v___x_124_; uint8_t v___x_125_; 
v___x_123_ = l_Lean_Syntax_getArg(v___x_118_, v___x_67_);
lean_dec(v___x_118_);
v___x_124_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__10));
lean_inc(v___x_123_);
v___x_125_ = l_Lean_Syntax_isOfKind(v___x_123_, v___x_124_);
if (v___x_125_ == 0)
{
lean_object* v___x_126_; lean_object* v___x_127_; 
lean_dec(v___x_123_);
lean_dec(v_metaTk_116_);
lean_dec(v___y_115_);
lean_dec(v_v_66_);
v___x_126_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8);
v___x_127_ = l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__1(v___x_126_);
v___y_70_ = v___x_127_;
goto v___jp_69_;
}
else
{
lean_object* v_allTk_128_; lean_object* v___x_129_; 
v_allTk_128_ = l_Lean_Syntax_getArg(v___x_123_, v___x_67_);
lean_dec(v___x_123_);
v___x_129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_129_, 0, v_allTk_128_);
v___y_101_ = v___y_115_;
v___y_102_ = v_metaTk_116_;
v_allTk_103_ = v___x_129_;
goto v___jp_100_;
}
}
}
else
{
lean_object* v___x_130_; 
lean_dec(v___x_118_);
v___x_130_ = lean_box(0);
v___y_101_ = v___y_115_;
v___y_102_ = v_metaTk_116_;
v_allTk_103_ = v___x_130_;
goto v___jp_100_;
}
}
v___jp_131_:
{
lean_object* v___x_133_; uint8_t v___x_134_; 
v___x_133_ = l_Lean_Syntax_getArg(v_v_66_, v___x_113_);
v___x_134_ = l_Lean_Syntax_isNone(v___x_133_);
if (v___x_134_ == 0)
{
uint8_t v___x_135_; 
lean_inc(v___x_133_);
v___x_135_ = l_Lean_Syntax_matchesNull(v___x_133_, v___x_113_);
if (v___x_135_ == 0)
{
lean_object* v___x_136_; lean_object* v___x_137_; 
lean_dec(v___x_133_);
lean_dec(v_publicTk_132_);
lean_dec(v_v_66_);
v___x_136_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8);
v___x_137_ = l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__1(v___x_136_);
v___y_70_ = v___x_137_;
goto v___jp_69_;
}
else
{
lean_object* v___x_138_; lean_object* v___x_139_; uint8_t v___x_140_; 
v___x_138_ = l_Lean_Syntax_getArg(v___x_133_, v___x_67_);
lean_dec(v___x_133_);
v___x_139_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__12));
lean_inc(v___x_138_);
v___x_140_ = l_Lean_Syntax_isOfKind(v___x_138_, v___x_139_);
if (v___x_140_ == 0)
{
lean_object* v___x_141_; lean_object* v___x_142_; 
lean_dec(v___x_138_);
lean_dec(v_publicTk_132_);
lean_dec(v_v_66_);
v___x_141_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8);
v___x_142_ = l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__1(v___x_141_);
v___y_70_ = v___x_142_;
goto v___jp_69_;
}
else
{
lean_object* v_metaTk_143_; lean_object* v___x_144_; 
v_metaTk_143_ = l_Lean_Syntax_getArg(v___x_138_, v___x_67_);
lean_dec(v___x_138_);
v___x_144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_144_, 0, v_metaTk_143_);
v___y_115_ = v_publicTk_132_;
v_metaTk_116_ = v___x_144_;
goto v___jp_114_;
}
}
}
else
{
lean_object* v___x_145_; 
lean_dec(v___x_133_);
v___x_145_ = lean_box(0);
v___y_115_ = v_publicTk_132_;
v_metaTk_116_ = v___x_145_;
goto v___jp_114_;
}
}
}
v___jp_69_:
{
size_t v___x_71_; size_t v___x_72_; lean_object* v___x_73_; 
v___x_71_ = ((size_t)1ULL);
v___x_72_ = lean_usize_add(v_i_62_, v___x_71_);
v___x_73_ = lean_array_uset(v_bs_x27_68_, v_i_62_, v___y_70_);
v_i_62_ = v___x_72_;
v_bs_63_ = v___x_73_;
goto _start;
}
v___jp_75_:
{
if (lean_obj_tag(v___y_79_) == 0)
{
uint8_t v___x_81_; lean_object* v___x_82_; 
v___x_81_ = 0;
v___x_82_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_82_, 0, v___y_77_);
lean_ctor_set_uint8(v___x_82_, sizeof(void*)*1, v___y_76_);
lean_ctor_set_uint8(v___x_82_, sizeof(void*)*1 + 1, v___y_80_);
lean_ctor_set_uint8(v___x_82_, sizeof(void*)*1 + 2, v___x_81_);
v___y_70_ = v___x_82_;
goto v___jp_69_;
}
else
{
lean_object* v___x_83_; 
lean_dec_ref_known(v___y_79_, 1);
v___x_83_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_83_, 0, v___y_77_);
lean_ctor_set_uint8(v___x_83_, sizeof(void*)*1, v___y_76_);
lean_ctor_set_uint8(v___x_83_, sizeof(void*)*1 + 1, v___y_80_);
lean_ctor_set_uint8(v___x_83_, sizeof(void*)*1 + 2, v___y_78_);
v___y_70_ = v___x_83_;
goto v___jp_69_;
}
}
v___jp_84_:
{
if (lean_obj_tag(v_moduleTk_59_) == 0)
{
v___y_76_ = v___y_86_;
v___y_77_ = v___y_85_;
v___y_78_ = v___y_87_;
v___y_79_ = v___y_88_;
v___y_80_ = v___y_87_;
goto v___jp_75_;
}
else
{
v___y_76_ = v___y_86_;
v___y_77_ = v___y_85_;
v___y_78_ = v___y_87_;
v___y_79_ = v___y_88_;
v___y_80_ = v___y_89_;
goto v___jp_75_;
}
}
v___jp_90_:
{
if (lean_obj_tag(v___y_91_) == 0)
{
uint8_t v___x_96_; 
v___x_96_ = 0;
v___y_85_ = v___y_92_;
v___y_86_ = v___y_95_;
v___y_87_ = v___y_93_;
v___y_88_ = v___y_94_;
v___y_89_ = v___x_96_;
goto v___jp_84_;
}
else
{
lean_dec_ref_known(v___y_91_, 1);
if (v___y_93_ == 0)
{
v___y_85_ = v___y_92_;
v___y_86_ = v___y_95_;
v___y_87_ = v___y_93_;
v___y_88_ = v___y_94_;
v___y_89_ = v___y_93_;
goto v___jp_84_;
}
else
{
v___y_76_ = v___y_95_;
v___y_77_ = v___y_92_;
v___y_78_ = v___y_93_;
v___y_79_ = v___y_94_;
v___y_80_ = v___x_60_;
goto v___jp_75_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___boxed(lean_object* v_moduleTk_159_, lean_object* v___x_160_, lean_object* v_sz_161_, lean_object* v_i_162_, lean_object* v_bs_163_){
_start:
{
uint8_t v___x_3706__boxed_164_; size_t v_sz_boxed_165_; size_t v_i_boxed_166_; lean_object* v_res_167_; 
v___x_3706__boxed_164_ = lean_unbox(v___x_160_);
v_sz_boxed_165_ = lean_unbox_usize(v_sz_161_);
lean_dec(v_sz_161_);
v_i_boxed_166_ = lean_unbox_usize(v_i_162_);
lean_dec(v_i_162_);
v_res_167_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2(v_moduleTk_159_, v___x_3706__boxed_164_, v_sz_boxed_165_, v_i_boxed_166_, v_bs_163_);
lean_dec(v_moduleTk_159_);
return v_res_167_;
}
}
static lean_object* _init_l_Lean_Elab_HeaderSyntax_imports___closed__2(void){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_174_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__7));
v___x_175_ = lean_unsigned_to_nat(9u);
v___x_176_ = lean_unsigned_to_nat(41u);
v___x_177_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__6));
v___x_178_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__5));
v___x_179_ = l_mkPanicMessageWithDecl(v___x_178_, v___x_177_, v___x_176_, v___x_175_, v___x_174_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_HeaderSyntax_imports(lean_object* v_stx_197_, uint8_t v_includeInit_198_){
_start:
{
lean_object* v___x_199_; uint8_t v___x_200_; lean_object* v___y_202_; lean_object* v___y_203_; lean_object* v___y_204_; 
v___x_199_ = ((lean_object*)(l_Lean_Elab_HeaderSyntax_imports___closed__1));
lean_inc(v_stx_197_);
v___x_200_ = l_Lean_Syntax_isOfKind(v_stx_197_, v___x_199_);
if (v___x_200_ == 0)
{
lean_object* v___x_209_; lean_object* v___x_210_; 
lean_dec(v_stx_197_);
v___x_209_ = lean_obj_once(&l_Lean_Elab_HeaderSyntax_imports___closed__2, &l_Lean_Elab_HeaderSyntax_imports___closed__2_once, _init_l_Lean_Elab_HeaderSyntax_imports___closed__2);
v___x_210_ = l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__0(v___x_209_);
return v___x_210_;
}
else
{
lean_object* v___x_211_; lean_object* v___y_213_; lean_object* v___y_214_; lean_object* v___y_217_; lean_object* v_preludeTk_218_; lean_object* v_moduleTk_230_; lean_object* v___x_245_; uint8_t v___x_246_; 
v___x_211_ = lean_unsigned_to_nat(0u);
v___x_245_ = l_Lean_Syntax_getArg(v_stx_197_, v___x_211_);
v___x_246_ = l_Lean_Syntax_isNone(v___x_245_);
if (v___x_246_ == 0)
{
lean_object* v___x_247_; uint8_t v___x_248_; 
v___x_247_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_245_);
v___x_248_ = l_Lean_Syntax_matchesNull(v___x_245_, v___x_247_);
if (v___x_248_ == 0)
{
lean_object* v___x_249_; lean_object* v___x_250_; 
lean_dec(v___x_245_);
lean_dec(v_stx_197_);
v___x_249_ = lean_obj_once(&l_Lean_Elab_HeaderSyntax_imports___closed__2, &l_Lean_Elab_HeaderSyntax_imports___closed__2_once, _init_l_Lean_Elab_HeaderSyntax_imports___closed__2);
v___x_250_ = l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__0(v___x_249_);
return v___x_250_;
}
else
{
lean_object* v___x_251_; lean_object* v___x_252_; uint8_t v___x_253_; 
v___x_251_ = l_Lean_Syntax_getArg(v___x_245_, v___x_211_);
lean_dec(v___x_245_);
v___x_252_ = ((lean_object*)(l_Lean_Elab_HeaderSyntax_imports___closed__9));
lean_inc(v___x_251_);
v___x_253_ = l_Lean_Syntax_isOfKind(v___x_251_, v___x_252_);
if (v___x_253_ == 0)
{
lean_object* v___x_254_; lean_object* v___x_255_; 
lean_dec(v___x_251_);
lean_dec(v_stx_197_);
v___x_254_ = lean_obj_once(&l_Lean_Elab_HeaderSyntax_imports___closed__2, &l_Lean_Elab_HeaderSyntax_imports___closed__2_once, _init_l_Lean_Elab_HeaderSyntax_imports___closed__2);
v___x_255_ = l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__0(v___x_254_);
return v___x_255_;
}
else
{
lean_object* v_moduleTk_256_; lean_object* v___x_257_; 
v_moduleTk_256_ = l_Lean_Syntax_getArg(v___x_251_, v___x_211_);
lean_dec(v___x_251_);
v___x_257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_257_, 0, v_moduleTk_256_);
v_moduleTk_230_ = v___x_257_;
goto v___jp_229_;
}
}
}
else
{
lean_object* v___x_258_; 
lean_dec(v___x_245_);
v___x_258_ = lean_box(0);
v_moduleTk_230_ = v___x_258_;
goto v___jp_229_;
}
v___jp_212_:
{
lean_object* v___x_215_; 
v___x_215_ = ((lean_object*)(l_Lean_Elab_HeaderSyntax_imports___closed__3));
v___y_202_ = v___y_213_;
v___y_203_ = v___y_214_;
v___y_204_ = v___x_215_;
goto v___jp_201_;
}
v___jp_216_:
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v_importsStx_221_; 
v___x_219_ = lean_unsigned_to_nat(2u);
v___x_220_ = l_Lean_Syntax_getArg(v_stx_197_, v___x_219_);
lean_dec(v_stx_197_);
v_importsStx_221_ = l_Lean_Syntax_getArgs(v___x_220_);
lean_dec(v___x_220_);
if (lean_obj_tag(v_preludeTk_218_) == 0)
{
if (v___x_200_ == 0)
{
v___y_213_ = v_importsStx_221_;
v___y_214_ = v___y_217_;
goto v___jp_212_;
}
else
{
if (v_includeInit_198_ == 0)
{
v___y_213_ = v_importsStx_221_;
v___y_214_ = v___y_217_;
goto v___jp_212_;
}
else
{
lean_object* v___x_222_; uint8_t v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_222_ = ((lean_object*)(l_Lean_Elab_HeaderSyntax_imports___closed__5));
v___x_223_ = 0;
v___x_224_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_224_, 0, v___x_222_);
lean_ctor_set_uint8(v___x_224_, sizeof(void*)*1, v___x_223_);
lean_ctor_set_uint8(v___x_224_, sizeof(void*)*1 + 1, v___x_200_);
lean_ctor_set_uint8(v___x_224_, sizeof(void*)*1 + 2, v___x_223_);
v___x_225_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_225_, 0, v___x_222_);
lean_ctor_set_uint8(v___x_225_, sizeof(void*)*1, v___x_223_);
lean_ctor_set_uint8(v___x_225_, sizeof(void*)*1 + 1, v___x_200_);
lean_ctor_set_uint8(v___x_225_, sizeof(void*)*1 + 2, v___x_200_);
v___x_226_ = lean_mk_empty_array_with_capacity(v___x_219_);
v___x_227_ = lean_array_push(v___x_226_, v___x_224_);
v___x_228_ = lean_array_push(v___x_227_, v___x_225_);
v___y_202_ = v_importsStx_221_;
v___y_203_ = v___y_217_;
v___y_204_ = v___x_228_;
goto v___jp_201_;
}
}
}
else
{
lean_dec_ref_known(v_preludeTk_218_, 1);
v___y_213_ = v_importsStx_221_;
v___y_214_ = v___y_217_;
goto v___jp_212_;
}
}
v___jp_229_:
{
lean_object* v___x_231_; lean_object* v___x_232_; uint8_t v___x_233_; 
v___x_231_ = lean_unsigned_to_nat(1u);
v___x_232_ = l_Lean_Syntax_getArg(v_stx_197_, v___x_231_);
v___x_233_ = l_Lean_Syntax_isNone(v___x_232_);
if (v___x_233_ == 0)
{
uint8_t v___x_234_; 
lean_inc(v___x_232_);
v___x_234_ = l_Lean_Syntax_matchesNull(v___x_232_, v___x_231_);
if (v___x_234_ == 0)
{
lean_object* v___x_235_; lean_object* v___x_236_; 
lean_dec(v___x_232_);
lean_dec(v_moduleTk_230_);
lean_dec(v_stx_197_);
v___x_235_ = lean_obj_once(&l_Lean_Elab_HeaderSyntax_imports___closed__2, &l_Lean_Elab_HeaderSyntax_imports___closed__2_once, _init_l_Lean_Elab_HeaderSyntax_imports___closed__2);
v___x_236_ = l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__0(v___x_235_);
return v___x_236_;
}
else
{
lean_object* v___x_237_; lean_object* v___x_238_; uint8_t v___x_239_; 
v___x_237_ = l_Lean_Syntax_getArg(v___x_232_, v___x_211_);
lean_dec(v___x_232_);
v___x_238_ = ((lean_object*)(l_Lean_Elab_HeaderSyntax_imports___closed__7));
lean_inc(v___x_237_);
v___x_239_ = l_Lean_Syntax_isOfKind(v___x_237_, v___x_238_);
if (v___x_239_ == 0)
{
lean_object* v___x_240_; lean_object* v___x_241_; 
lean_dec(v___x_237_);
lean_dec(v_moduleTk_230_);
lean_dec(v_stx_197_);
v___x_240_ = lean_obj_once(&l_Lean_Elab_HeaderSyntax_imports___closed__2, &l_Lean_Elab_HeaderSyntax_imports___closed__2_once, _init_l_Lean_Elab_HeaderSyntax_imports___closed__2);
v___x_241_ = l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__0(v___x_240_);
return v___x_241_;
}
else
{
lean_object* v_preludeTk_242_; lean_object* v___x_243_; 
v_preludeTk_242_ = l_Lean_Syntax_getArg(v___x_237_, v___x_211_);
lean_dec(v___x_237_);
v___x_243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_243_, 0, v_preludeTk_242_);
v___y_217_ = v_moduleTk_230_;
v_preludeTk_218_ = v___x_243_;
goto v___jp_216_;
}
}
}
else
{
lean_object* v___x_244_; 
lean_dec(v___x_232_);
v___x_244_ = lean_box(0);
v___y_217_ = v_moduleTk_230_;
v_preludeTk_218_ = v___x_244_;
goto v___jp_216_;
}
}
}
v___jp_201_:
{
size_t v_sz_205_; size_t v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v_sz_205_ = lean_array_size(v___y_202_);
v___x_206_ = ((size_t)0ULL);
v___x_207_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2(v___y_203_, v___x_200_, v_sz_205_, v___x_206_, v___y_202_);
lean_dec(v___y_203_);
v___x_208_ = l_Array_append___redArg(v___y_204_, v___x_207_);
lean_dec_ref(v___x_207_);
return v___x_208_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_HeaderSyntax_imports___boxed(lean_object* v_stx_259_, lean_object* v_includeInit_260_){
_start:
{
uint8_t v_includeInit_boxed_261_; lean_object* v_res_262_; 
v_includeInit_boxed_261_ = lean_unbox(v_includeInit_260_);
v_res_262_ = l_Lean_Elab_HeaderSyntax_imports(v_stx_259_, v_includeInit_boxed_261_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_HeaderSyntax_toModuleHeader(lean_object* v_stx_263_){
_start:
{
uint8_t v___x_264_; lean_object* v___x_265_; uint8_t v___x_266_; lean_object* v___x_267_; 
v___x_264_ = 1;
lean_inc(v_stx_263_);
v___x_265_ = l_Lean_Elab_HeaderSyntax_imports(v_stx_263_, v___x_264_);
v___x_266_ = l_Lean_Elab_HeaderSyntax_isModule(v_stx_263_);
lean_dec(v_stx_263_);
v___x_267_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_267_, 0, v___x_265_);
lean_ctor_set_uint8(v___x_267_, sizeof(void*)*1, v___x_266_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_headerToImports(lean_object* v_stx_268_, uint8_t v_includeInit_269_){
_start:
{
lean_object* v___x_270_; 
v___x_270_ = l_Lean_Elab_HeaderSyntax_imports(v_stx_268_, v_includeInit_269_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_headerToImports___boxed(lean_object* v_stx_271_, lean_object* v_includeInit_272_){
_start:
{
uint8_t v_includeInit_boxed_273_; lean_object* v_res_274_; 
v_includeInit_boxed_273_ = lean_unbox(v_includeInit_272_);
v_res_274_ = l_Lean_Elab_headerToImports(v_stx_271_, v_includeInit_boxed_273_);
return v_res_274_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_checkDeprecatedImports_spec__0(lean_object* v_opts_275_, lean_object* v_opt_276_){
_start:
{
lean_object* v_name_277_; lean_object* v_defValue_278_; lean_object* v_map_279_; lean_object* v___x_280_; 
v_name_277_ = lean_ctor_get(v_opt_276_, 0);
v_defValue_278_ = lean_ctor_get(v_opt_276_, 1);
v_map_279_ = lean_ctor_get(v_opts_275_, 0);
v___x_280_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_279_, v_name_277_);
if (lean_obj_tag(v___x_280_) == 0)
{
uint8_t v___x_281_; 
v___x_281_ = lean_unbox(v_defValue_278_);
return v___x_281_;
}
else
{
lean_object* v_val_282_; 
v_val_282_ = lean_ctor_get(v___x_280_, 0);
lean_inc(v_val_282_);
lean_dec_ref_known(v___x_280_, 1);
if (lean_obj_tag(v_val_282_) == 1)
{
uint8_t v_v_283_; 
v_v_283_ = lean_ctor_get_uint8(v_val_282_, 0);
lean_dec_ref_known(v_val_282_, 0);
return v_v_283_;
}
else
{
uint8_t v___x_284_; 
lean_dec(v_val_282_);
v___x_284_ = lean_unbox(v_defValue_278_);
return v___x_284_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_checkDeprecatedImports_spec__0___boxed(lean_object* v_opts_285_, lean_object* v_opt_286_){
_start:
{
uint8_t v_res_287_; lean_object* v_r_288_; 
v_res_287_ = l_Lean_Option_get___at___00Lean_Elab_checkDeprecatedImports_spec__0(v_opts_285_, v_opt_286_);
lean_dec_ref(v_opt_286_);
lean_dec_ref(v_opts_285_);
v_r_288_ = lean_box(v_res_287_);
return v_r_288_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_spec__2___redArg(lean_object* v_s_289_, lean_object* v_a_290_, uint8_t v_b_291_){
_start:
{
uint8_t v___x_292_; 
v___x_292_ = 0;
switch(lean_obj_tag(v_a_290_))
{
case 0:
{
uint8_t v___x_293_; 
lean_dec_ref_known(v_a_290_, 1);
v___x_293_ = 1;
return v___x_293_;
}
case 1:
{
lean_object* v_pos_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_307_; 
v_pos_294_ = lean_ctor_get(v_a_290_, 0);
v_isSharedCheck_307_ = !lean_is_exclusive(v_a_290_);
if (v_isSharedCheck_307_ == 0)
{
v___x_296_ = v_a_290_;
v_isShared_297_ = v_isSharedCheck_307_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_pos_294_);
lean_dec(v_a_290_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_307_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v_str_298_; lean_object* v_startInclusive_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_304_; 
v_str_298_ = lean_ctor_get(v_s_289_, 0);
v_startInclusive_299_ = lean_ctor_get(v_s_289_, 1);
v___x_300_ = lean_nat_add(v_startInclusive_299_, v_pos_294_);
lean_dec(v_pos_294_);
v___x_301_ = lean_string_utf8_next_fast(v_str_298_, v___x_300_);
lean_dec(v___x_300_);
v___x_302_ = lean_nat_sub(v___x_301_, v_startInclusive_299_);
if (v_isShared_297_ == 0)
{
lean_ctor_set_tag(v___x_296_, 0);
lean_ctor_set(v___x_296_, 0, v___x_302_);
v___x_304_ = v___x_296_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v___x_302_);
v___x_304_ = v_reuseFailAlloc_306_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
v_a_290_ = v___x_304_;
v_b_291_ = v___x_292_;
goto _start;
}
}
}
case 2:
{
lean_object* v_needle_308_; lean_object* v_table_309_; lean_object* v_stackPos_310_; lean_object* v_needlePos_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_364_; 
v_needle_308_ = lean_ctor_get(v_a_290_, 0);
v_table_309_ = lean_ctor_get(v_a_290_, 1);
v_stackPos_310_ = lean_ctor_get(v_a_290_, 2);
v_needlePos_311_ = lean_ctor_get(v_a_290_, 3);
v_isSharedCheck_364_ = !lean_is_exclusive(v_a_290_);
if (v_isSharedCheck_364_ == 0)
{
v___x_313_ = v_a_290_;
v_isShared_314_ = v_isSharedCheck_364_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_needlePos_311_);
lean_inc(v_stackPos_310_);
lean_inc(v_table_309_);
lean_inc(v_needle_308_);
lean_dec(v_a_290_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_364_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v_str_315_; lean_object* v_startInclusive_316_; lean_object* v_endExclusive_317_; lean_object* v_str_318_; lean_object* v_startInclusive_319_; lean_object* v_endExclusive_320_; lean_object* v_basePos_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; uint8_t v___x_325_; 
v_str_315_ = lean_ctor_get(v_needle_308_, 0);
v_startInclusive_316_ = lean_ctor_get(v_needle_308_, 1);
v_endExclusive_317_ = lean_ctor_get(v_needle_308_, 2);
v_str_318_ = lean_ctor_get(v_s_289_, 0);
v_startInclusive_319_ = lean_ctor_get(v_s_289_, 1);
v_endExclusive_320_ = lean_ctor_get(v_s_289_, 2);
v_basePos_321_ = lean_nat_sub(v_stackPos_310_, v_needlePos_311_);
v___x_322_ = lean_nat_sub(v_endExclusive_317_, v_startInclusive_316_);
v___x_323_ = lean_nat_add(v_basePos_321_, v___x_322_);
v___x_324_ = lean_nat_sub(v_endExclusive_320_, v_startInclusive_319_);
v___x_325_ = lean_nat_dec_le(v___x_323_, v___x_324_);
lean_dec(v___x_323_);
if (v___x_325_ == 0)
{
uint8_t v___x_326_; 
lean_dec(v___x_322_);
lean_del_object(v___x_313_);
lean_dec(v_needlePos_311_);
lean_dec(v_stackPos_310_);
lean_dec_ref(v_table_309_);
lean_dec_ref(v_needle_308_);
v___x_326_ = lean_nat_dec_lt(v_basePos_321_, v___x_324_);
lean_dec(v___x_324_);
lean_dec(v_basePos_321_);
if (v___x_326_ == 0)
{
return v_b_291_;
}
else
{
lean_object* v___x_327_; 
v___x_327_ = lean_box(3);
v_a_290_ = v___x_327_;
v_b_291_ = v___x_292_;
goto _start;
}
}
else
{
lean_object* v___x_329_; uint8_t v_stackByte_330_; lean_object* v___x_331_; uint8_t v_patByte_332_; uint8_t v___x_333_; 
lean_dec(v___x_324_);
lean_dec(v_basePos_321_);
v___x_329_ = lean_nat_add(v_startInclusive_319_, v_stackPos_310_);
v_stackByte_330_ = lean_string_get_byte_fast(v_str_318_, v___x_329_);
v___x_331_ = lean_nat_add(v_startInclusive_316_, v_needlePos_311_);
v_patByte_332_ = lean_string_get_byte_fast(v_str_315_, v___x_331_);
v___x_333_ = lean_uint8_dec_eq(v_stackByte_330_, v_patByte_332_);
if (v___x_333_ == 0)
{
lean_object* v___x_334_; uint8_t v___x_335_; 
lean_dec(v___x_322_);
v___x_334_ = lean_unsigned_to_nat(0u);
v___x_335_ = lean_nat_dec_eq(v_needlePos_311_, v___x_334_);
if (v___x_335_ == 0)
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v_newNeedlePos_338_; uint8_t v___x_339_; 
v___x_336_ = lean_unsigned_to_nat(1u);
v___x_337_ = lean_nat_sub(v_needlePos_311_, v___x_336_);
lean_dec(v_needlePos_311_);
v_newNeedlePos_338_ = lean_array_fget_borrowed(v_table_309_, v___x_337_);
lean_dec(v___x_337_);
v___x_339_ = lean_nat_dec_eq(v_newNeedlePos_338_, v___x_334_);
if (v___x_339_ == 0)
{
lean_object* v___x_341_; 
lean_inc(v_newNeedlePos_338_);
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 3, v_newNeedlePos_338_);
v___x_341_ = v___x_313_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v_needle_308_);
lean_ctor_set(v_reuseFailAlloc_343_, 1, v_table_309_);
lean_ctor_set(v_reuseFailAlloc_343_, 2, v_stackPos_310_);
lean_ctor_set(v_reuseFailAlloc_343_, 3, v_newNeedlePos_338_);
v___x_341_ = v_reuseFailAlloc_343_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
v_a_290_ = v___x_341_;
v_b_291_ = v___x_292_;
goto _start;
}
}
else
{
lean_object* v_nextStackPos_344_; lean_object* v___x_346_; 
v_nextStackPos_344_ = l_String_Slice_posGE___redArg(v_s_289_, v_stackPos_310_);
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 3, v___x_334_);
lean_ctor_set(v___x_313_, 2, v_nextStackPos_344_);
v___x_346_ = v___x_313_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v_needle_308_);
lean_ctor_set(v_reuseFailAlloc_348_, 1, v_table_309_);
lean_ctor_set(v_reuseFailAlloc_348_, 2, v_nextStackPos_344_);
lean_ctor_set(v_reuseFailAlloc_348_, 3, v___x_334_);
v___x_346_ = v_reuseFailAlloc_348_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
v_a_290_ = v___x_346_;
v_b_291_ = v___x_292_;
goto _start;
}
}
}
else
{
lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v_nextStackPos_351_; lean_object* v___x_353_; 
lean_dec(v_needlePos_311_);
v___x_349_ = lean_unsigned_to_nat(1u);
v___x_350_ = lean_nat_add(v_stackPos_310_, v___x_349_);
lean_dec(v_stackPos_310_);
v_nextStackPos_351_ = l_String_Slice_posGE___redArg(v_s_289_, v___x_350_);
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 3, v___x_334_);
lean_ctor_set(v___x_313_, 2, v_nextStackPos_351_);
v___x_353_ = v___x_313_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_needle_308_);
lean_ctor_set(v_reuseFailAlloc_355_, 1, v_table_309_);
lean_ctor_set(v_reuseFailAlloc_355_, 2, v_nextStackPos_351_);
lean_ctor_set(v_reuseFailAlloc_355_, 3, v___x_334_);
v___x_353_ = v_reuseFailAlloc_355_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
v_a_290_ = v___x_353_;
v_b_291_ = v___x_292_;
goto _start;
}
}
}
else
{
lean_object* v___x_356_; lean_object* v_nextNeedlePos_357_; uint8_t v___x_358_; 
v___x_356_ = lean_unsigned_to_nat(1u);
v_nextNeedlePos_357_ = lean_nat_add(v_needlePos_311_, v___x_356_);
lean_dec(v_needlePos_311_);
v___x_358_ = lean_nat_dec_eq(v_nextNeedlePos_357_, v___x_322_);
lean_dec(v___x_322_);
if (v___x_358_ == 0)
{
lean_object* v_nextStackPos_359_; lean_object* v___x_361_; 
v_nextStackPos_359_ = lean_nat_add(v_stackPos_310_, v___x_356_);
lean_dec(v_stackPos_310_);
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 3, v_nextNeedlePos_357_);
lean_ctor_set(v___x_313_, 2, v_nextStackPos_359_);
v___x_361_ = v___x_313_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v_needle_308_);
lean_ctor_set(v_reuseFailAlloc_363_, 1, v_table_309_);
lean_ctor_set(v_reuseFailAlloc_363_, 2, v_nextStackPos_359_);
lean_ctor_set(v_reuseFailAlloc_363_, 3, v_nextNeedlePos_357_);
v___x_361_ = v_reuseFailAlloc_363_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
v_a_290_ = v___x_361_;
goto _start;
}
}
else
{
lean_dec(v_nextNeedlePos_357_);
lean_del_object(v___x_313_);
lean_dec(v_stackPos_310_);
lean_dec_ref(v_table_309_);
lean_dec_ref(v_needle_308_);
return v___x_358_;
}
}
}
}
}
default: 
{
return v_b_291_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_spec__2___redArg___boxed(lean_object* v_s_365_, lean_object* v_a_366_, lean_object* v_b_367_){
_start:
{
uint8_t v_b_boxed_368_; uint8_t v_res_369_; lean_object* v_r_370_; 
v_b_boxed_368_ = lean_unbox(v_b_367_);
v_res_369_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_spec__2___redArg(v_s_365_, v_a_366_, v_b_boxed_368_);
lean_dec_ref(v_s_365_);
v_r_370_ = lean_box(v_res_369_);
return v_r_370_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__1(void){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_372_ = ((lean_object*)(l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__0));
v___x_373_ = lean_string_utf8_byte_size(v___x_372_);
return v___x_373_;
}
}
static uint8_t _init_l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__2(void){
_start:
{
lean_object* v___x_374_; lean_object* v___x_375_; uint8_t v___x_376_; 
v___x_374_ = lean_unsigned_to_nat(0u);
v___x_375_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__1, &l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__1_once, _init_l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__1);
v___x_376_ = lean_nat_dec_eq(v___x_375_, v___x_374_);
return v___x_376_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__3(void){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_377_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__1, &l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__1_once, _init_l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__1);
v___x_378_ = lean_unsigned_to_nat(0u);
v___x_379_ = ((lean_object*)(l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__0));
v___x_380_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_380_, 0, v___x_379_);
lean_ctor_set(v___x_380_, 1, v___x_378_);
lean_ctor_set(v___x_380_, 2, v___x_377_);
return v___x_380_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__4(void){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_381_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__3, &l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__3_once, _init_l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__3);
v___x_382_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_381_);
return v___x_382_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__5(void){
_start:
{
lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_383_ = lean_unsigned_to_nat(0u);
v___x_384_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__4, &l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__4_once, _init_l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__4);
v___x_385_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__3, &l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__3_once, _init_l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__3);
v___x_386_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
lean_ctor_set(v___x_386_, 1, v___x_384_);
lean_ctor_set(v___x_386_, 2, v___x_383_);
lean_ctor_set(v___x_386_, 3, v___x_383_);
return v___x_386_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2(lean_object* v_s_389_){
_start:
{
lean_object* v___y_391_; uint8_t v___x_394_; 
v___x_394_ = lean_uint8_once(&l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__2, &l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__2_once, _init_l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__2);
if (v___x_394_ == 0)
{
lean_object* v___x_395_; 
v___x_395_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__5, &l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__5_once, _init_l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__5);
v___y_391_ = v___x_395_;
goto v___jp_390_;
}
else
{
lean_object* v___x_396_; 
v___x_396_ = ((lean_object*)(l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__6));
v___y_391_ = v___x_396_;
goto v___jp_390_;
}
v___jp_390_:
{
uint8_t v___x_392_; uint8_t v___x_393_; 
v___x_392_ = 0;
lean_inc(v___y_391_);
v___x_393_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_spec__2___redArg(v_s_389_, v___y_391_, v___x_392_);
return v___x_393_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___boxed(lean_object* v_s_397_){
_start:
{
uint8_t v_res_398_; lean_object* v_r_399_; 
v_res_398_ = l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2(v_s_397_);
lean_dec_ref(v_s_397_);
v_r_399_ = lean_box(v_res_398_);
return v_r_399_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkDeprecatedImports_spec__3(lean_object* v_as_400_, size_t v_sz_401_, size_t v_i_402_, lean_object* v_b_403_){
_start:
{
lean_object* v_a_405_; uint8_t v___x_409_; 
v___x_409_ = lean_usize_dec_lt(v_i_402_, v_sz_401_);
if (v___x_409_ == 0)
{
return v_b_403_;
}
else
{
lean_object* v_a_410_; lean_object* v___x_411_; 
v_a_410_ = lean_array_uget_borrowed(v_as_400_, v_i_402_);
v___x_411_ = l_Lean_Syntax_getTrailing_x3f(v_a_410_);
if (lean_obj_tag(v___x_411_) == 0)
{
v_a_405_ = v_b_403_;
goto v___jp_404_;
}
else
{
lean_object* v_val_412_; lean_object* v_str_413_; lean_object* v_startPos_414_; lean_object* v_stopPos_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_458_; 
v_val_412_ = lean_ctor_get(v___x_411_, 0);
lean_inc(v_val_412_);
lean_dec_ref_known(v___x_411_, 1);
v_str_413_ = lean_ctor_get(v_val_412_, 0);
v_startPos_414_ = lean_ctor_get(v_val_412_, 1);
v_stopPos_415_ = lean_ctor_get(v_val_412_, 2);
v_isSharedCheck_458_ = !lean_is_exclusive(v_val_412_);
if (v_isSharedCheck_458_ == 0)
{
v___x_417_ = v_val_412_;
v_isShared_418_ = v_isSharedCheck_458_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_stopPos_415_);
lean_inc(v_startPos_414_);
lean_inc(v_str_413_);
lean_dec(v_val_412_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_458_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_419_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_431_; 
v___x_419_ = lean_unsigned_to_nat(0u);
v___x_428_ = lean_string_utf8_extract(v_str_413_, v_startPos_414_, v_stopPos_415_);
lean_dec(v_stopPos_415_);
lean_dec(v_startPos_414_);
lean_dec_ref(v_str_413_);
v___x_429_ = lean_string_utf8_byte_size(v___x_428_);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 2, v___x_429_);
lean_ctor_set(v___x_417_, 1, v___x_419_);
lean_ctor_set(v___x_417_, 0, v___x_428_);
v___x_431_ = v___x_417_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v___x_428_);
lean_ctor_set(v_reuseFailAlloc_457_, 1, v___x_419_);
lean_ctor_set(v_reuseFailAlloc_457_, 2, v___x_429_);
v___x_431_ = v_reuseFailAlloc_457_;
goto v_reusejp_430_;
}
v___jp_420_:
{
lean_object* v___x_421_; lean_object* v___x_422_; uint8_t v___x_423_; 
v___x_421_ = lean_unsigned_to_nat(5u);
v___x_422_ = l_Lean_Syntax_getArg(v_a_410_, v___x_421_);
v___x_423_ = l_Lean_Syntax_matchesNull(v___x_422_, v___x_419_);
if (v___x_423_ == 0)
{
v_a_405_ = v_b_403_;
goto v___jp_404_;
}
else
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_424_ = lean_unsigned_to_nat(4u);
v___x_425_ = l_Lean_Syntax_getArg(v_a_410_, v___x_424_);
v___x_426_ = l_Lean_TSyntax_getId(v___x_425_);
lean_dec(v___x_425_);
v___x_427_ = l_Lean_NameSet_insert(v_b_403_, v___x_426_);
v_a_405_ = v___x_427_;
goto v___jp_404_;
}
}
v_reusejp_430_:
{
uint8_t v___x_432_; 
v___x_432_ = l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2(v___x_431_);
lean_dec_ref(v___x_431_);
if (v___x_432_ == 0)
{
v_a_405_ = v_b_403_;
goto v___jp_404_;
}
else
{
lean_object* v___x_433_; uint8_t v___x_434_; 
v___x_433_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__4));
lean_inc(v_a_410_);
v___x_434_ = l_Lean_Syntax_isOfKind(v_a_410_, v___x_433_);
if (v___x_434_ == 0)
{
v_a_405_ = v_b_403_;
goto v___jp_404_;
}
else
{
lean_object* v___x_435_; lean_object* v___x_451_; uint8_t v___x_452_; 
v___x_435_ = lean_unsigned_to_nat(1u);
v___x_451_ = l_Lean_Syntax_getArg(v_a_410_, v___x_419_);
v___x_452_ = l_Lean_Syntax_isNone(v___x_451_);
if (v___x_452_ == 0)
{
uint8_t v___x_453_; 
lean_inc(v___x_451_);
v___x_453_ = l_Lean_Syntax_matchesNull(v___x_451_, v___x_435_);
if (v___x_453_ == 0)
{
lean_dec(v___x_451_);
v_a_405_ = v_b_403_;
goto v___jp_404_;
}
else
{
lean_object* v___x_454_; lean_object* v___x_455_; uint8_t v___x_456_; 
v___x_454_ = l_Lean_Syntax_getArg(v___x_451_, v___x_419_);
lean_dec(v___x_451_);
v___x_455_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__14));
v___x_456_ = l_Lean_Syntax_isOfKind(v___x_454_, v___x_455_);
if (v___x_456_ == 0)
{
v_a_405_ = v_b_403_;
goto v___jp_404_;
}
else
{
goto v___jp_444_;
}
}
}
else
{
lean_dec(v___x_451_);
goto v___jp_444_;
}
v___jp_436_:
{
lean_object* v___x_437_; lean_object* v___x_438_; uint8_t v___x_439_; 
v___x_437_ = lean_unsigned_to_nat(3u);
v___x_438_ = l_Lean_Syntax_getArg(v_a_410_, v___x_437_);
v___x_439_ = l_Lean_Syntax_isNone(v___x_438_);
if (v___x_439_ == 0)
{
uint8_t v___x_440_; 
lean_inc(v___x_438_);
v___x_440_ = l_Lean_Syntax_matchesNull(v___x_438_, v___x_435_);
if (v___x_440_ == 0)
{
lean_dec(v___x_438_);
v_a_405_ = v_b_403_;
goto v___jp_404_;
}
else
{
lean_object* v___x_441_; lean_object* v___x_442_; uint8_t v___x_443_; 
v___x_441_ = l_Lean_Syntax_getArg(v___x_438_, v___x_419_);
lean_dec(v___x_438_);
v___x_442_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__10));
v___x_443_ = l_Lean_Syntax_isOfKind(v___x_441_, v___x_442_);
if (v___x_443_ == 0)
{
v_a_405_ = v_b_403_;
goto v___jp_404_;
}
else
{
goto v___jp_420_;
}
}
}
else
{
lean_dec(v___x_438_);
goto v___jp_420_;
}
}
v___jp_444_:
{
lean_object* v___x_445_; uint8_t v___x_446_; 
v___x_445_ = l_Lean_Syntax_getArg(v_a_410_, v___x_435_);
v___x_446_ = l_Lean_Syntax_isNone(v___x_445_);
if (v___x_446_ == 0)
{
uint8_t v___x_447_; 
lean_inc(v___x_445_);
v___x_447_ = l_Lean_Syntax_matchesNull(v___x_445_, v___x_435_);
if (v___x_447_ == 0)
{
lean_dec(v___x_445_);
v_a_405_ = v_b_403_;
goto v___jp_404_;
}
else
{
lean_object* v___x_448_; lean_object* v___x_449_; uint8_t v___x_450_; 
v___x_448_ = l_Lean_Syntax_getArg(v___x_445_, v___x_419_);
lean_dec(v___x_445_);
v___x_449_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__12));
v___x_450_ = l_Lean_Syntax_isOfKind(v___x_448_, v___x_449_);
if (v___x_450_ == 0)
{
v_a_405_ = v_b_403_;
goto v___jp_404_;
}
else
{
goto v___jp_436_;
}
}
}
else
{
lean_dec(v___x_445_);
goto v___jp_436_;
}
}
}
}
}
}
}
}
v___jp_404_:
{
size_t v___x_406_; size_t v___x_407_; 
v___x_406_ = ((size_t)1ULL);
v___x_407_ = lean_usize_add(v_i_402_, v___x_406_);
v_i_402_ = v___x_407_;
v_b_403_ = v_a_405_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkDeprecatedImports_spec__3___boxed(lean_object* v_as_459_, lean_object* v_sz_460_, lean_object* v_i_461_, lean_object* v_b_462_){
_start:
{
size_t v_sz_boxed_463_; size_t v_i_boxed_464_; lean_object* v_res_465_; 
v_sz_boxed_463_ = lean_unbox_usize(v_sz_460_);
lean_dec(v_sz_460_);
v_i_boxed_464_ = lean_unbox_usize(v_i_461_);
lean_dec(v_i_461_);
v_res_465_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkDeprecatedImports_spec__3(v_as_459_, v_sz_boxed_463_, v_i_boxed_464_, v_b_462_);
lean_dec_ref(v_as_459_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4_spec__5(lean_object* v_o_469_, lean_object* v_k_470_, uint8_t v_v_471_){
_start:
{
lean_object* v_map_472_; uint8_t v_hasTrace_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_487_; 
v_map_472_ = lean_ctor_get(v_o_469_, 0);
v_hasTrace_473_ = lean_ctor_get_uint8(v_o_469_, sizeof(void*)*1);
v_isSharedCheck_487_ = !lean_is_exclusive(v_o_469_);
if (v_isSharedCheck_487_ == 0)
{
v___x_475_ = v_o_469_;
v_isShared_476_ = v_isSharedCheck_487_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_map_472_);
lean_dec(v_o_469_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_487_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_477_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_477_, 0, v_v_471_);
lean_inc(v_k_470_);
v___x_478_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_470_, v___x_477_, v_map_472_);
if (v_hasTrace_473_ == 0)
{
lean_object* v___x_479_; uint8_t v___x_480_; lean_object* v___x_482_; 
v___x_479_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4_spec__5___closed__1));
v___x_480_ = l_Lean_Name_isPrefixOf(v___x_479_, v_k_470_);
lean_dec(v_k_470_);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 0, v___x_478_);
v___x_482_ = v___x_475_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v___x_478_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
lean_ctor_set_uint8(v___x_482_, sizeof(void*)*1, v___x_480_);
return v___x_482_;
}
}
else
{
lean_object* v___x_485_; 
lean_dec(v_k_470_);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 0, v___x_478_);
v___x_485_ = v___x_475_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v___x_478_);
lean_ctor_set_uint8(v_reuseFailAlloc_486_, sizeof(void*)*1, v_hasTrace_473_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4_spec__5___boxed(lean_object* v_o_488_, lean_object* v_k_489_, lean_object* v_v_490_){
_start:
{
uint8_t v_v_boxed_491_; lean_object* v_res_492_; 
v_v_boxed_491_ = lean_unbox(v_v_490_);
v_res_492_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4_spec__5(v_o_488_, v_k_489_, v_v_boxed_491_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4(lean_object* v_opts_493_, lean_object* v_opt_494_, uint8_t v_val_495_){
_start:
{
lean_object* v_name_496_; lean_object* v___x_497_; 
v_name_496_ = lean_ctor_get(v_opt_494_, 0);
lean_inc(v_name_496_);
lean_dec_ref(v_opt_494_);
v___x_497_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4_spec__5(v_opts_493_, v_name_496_, v_val_495_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4___boxed(lean_object* v_opts_498_, lean_object* v_opt_499_, lean_object* v_val_500_){
_start:
{
uint8_t v_val_boxed_501_; lean_object* v_res_502_; 
v_val_boxed_501_ = lean_unbox(v_val_500_);
v_res_502_ = l_Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4(v_opts_498_, v_opt_499_, v_val_boxed_501_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1(lean_object* v_ignoreDeprecatedImports_508_, lean_object* v_env_509_, lean_object* v_inputCtx_510_, lean_object* v_startPos_511_, lean_object* v_as_512_, size_t v_i_513_, size_t v_stop_514_, lean_object* v_b_515_){
_start:
{
lean_object* v___y_517_; uint8_t v___x_521_; 
v___x_521_ = lean_usize_dec_eq(v_i_513_, v_stop_514_);
if (v___x_521_ == 0)
{
lean_object* v___x_522_; lean_object* v_module_523_; uint8_t v___x_524_; 
v___x_522_ = lean_array_uget_borrowed(v_as_512_, v_i_513_);
v_module_523_ = lean_ctor_get(v___x_522_, 0);
v___x_524_ = l_Lean_NameSet_contains(v_ignoreDeprecatedImports_508_, v_module_523_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; 
v___x_525_ = l_Lean_Environment_getModuleIdx_x3f(v_env_509_, v_module_523_);
if (lean_obj_tag(v___x_525_) == 0)
{
v___y_517_ = v_b_515_;
goto v___jp_516_;
}
else
{
lean_object* v_val_526_; lean_object* v___x_527_; 
v_val_526_ = lean_ctor_get(v___x_525_, 0);
lean_inc(v_val_526_);
lean_dec_ref_known(v___x_525_, 1);
v___x_527_ = l_Lean_Environment_getDeprecatedModuleByIdx_x3f(v_env_509_, v_val_526_);
if (lean_obj_tag(v___x_527_) == 0)
{
lean_dec(v_val_526_);
v___y_517_ = v_b_515_;
goto v___jp_516_;
}
else
{
lean_object* v_val_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_547_; 
v_val_528_ = lean_ctor_get(v___x_527_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_547_ == 0)
{
v___x_530_ = v___x_527_;
v_isShared_531_ = v_isSharedCheck_547_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_val_528_);
lean_dec(v___x_527_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_547_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v_fileName_532_; lean_object* v_fileMap_533_; lean_object* v_pos_534_; lean_object* v___x_535_; uint8_t v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_541_; 
v_fileName_532_ = lean_ctor_get(v_inputCtx_510_, 1);
v_fileMap_533_ = lean_ctor_get(v_inputCtx_510_, 2);
lean_inc_ref(v_fileMap_533_);
v_pos_534_ = l_Lean_FileMap_toPosition(v_fileMap_533_, v_startPos_511_);
v___x_535_ = lean_box(0);
v___x_536_ = 1;
v___x_537_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___closed__0));
v___x_538_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___closed__2));
lean_inc(v_module_523_);
v___x_539_ = l_Lean_formatDeprecatedModuleWarning(v_env_509_, v_val_526_, v_module_523_, v_val_528_);
lean_dec(v_val_526_);
if (v_isShared_531_ == 0)
{
lean_ctor_set_tag(v___x_530_, 3);
lean_ctor_set(v___x_530_, 0, v___x_539_);
v___x_541_ = v___x_530_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v___x_539_);
v___x_541_ = v_reuseFailAlloc_546_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_542_ = l_Lean_MessageData_ofFormat(v___x_541_);
v___x_543_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_543_, 0, v___x_538_);
lean_ctor_set(v___x_543_, 1, v___x_542_);
lean_inc_ref(v_fileName_532_);
v___x_544_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_544_, 0, v_fileName_532_);
lean_ctor_set(v___x_544_, 1, v_pos_534_);
lean_ctor_set(v___x_544_, 2, v___x_535_);
lean_ctor_set(v___x_544_, 3, v___x_537_);
lean_ctor_set(v___x_544_, 4, v___x_543_);
lean_ctor_set_uint8(v___x_544_, sizeof(void*)*5, v___x_524_);
lean_ctor_set_uint8(v___x_544_, sizeof(void*)*5 + 1, v___x_536_);
lean_ctor_set_uint8(v___x_544_, sizeof(void*)*5 + 2, v___x_524_);
v___x_545_ = l_Lean_MessageLog_add(v___x_544_, v_b_515_);
v___y_517_ = v___x_545_;
goto v___jp_516_;
}
}
}
}
}
else
{
v___y_517_ = v_b_515_;
goto v___jp_516_;
}
}
else
{
lean_dec_ref(v_inputCtx_510_);
return v_b_515_;
}
v___jp_516_:
{
size_t v___x_518_; size_t v___x_519_; 
v___x_518_ = ((size_t)1ULL);
v___x_519_ = lean_usize_add(v_i_513_, v___x_518_);
v_i_513_ = v___x_519_;
v_b_515_ = v___y_517_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___boxed(lean_object* v_ignoreDeprecatedImports_548_, lean_object* v_env_549_, lean_object* v_inputCtx_550_, lean_object* v_startPos_551_, lean_object* v_as_552_, lean_object* v_i_553_, lean_object* v_stop_554_, lean_object* v_b_555_){
_start:
{
size_t v_i_boxed_556_; size_t v_stop_boxed_557_; lean_object* v_res_558_; 
v_i_boxed_556_ = lean_unbox_usize(v_i_553_);
lean_dec(v_i_553_);
v_stop_boxed_557_ = lean_unbox_usize(v_stop_554_);
lean_dec(v_stop_554_);
v_res_558_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1(v_ignoreDeprecatedImports_548_, v_env_549_, v_inputCtx_550_, v_startPos_551_, v_as_552_, v_i_boxed_556_, v_stop_boxed_557_, v_b_555_);
lean_dec_ref(v_as_552_);
lean_dec(v_startPos_551_);
lean_dec_ref(v_env_549_);
lean_dec(v_ignoreDeprecatedImports_548_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedImports(lean_object* v_env_559_, lean_object* v_imports_560_, lean_object* v_opts_561_, lean_object* v_inputCtx_562_, lean_object* v_startPos_563_, lean_object* v_messages_564_, lean_object* v_headerStx_x3f_565_, lean_object* v_origHeaderStx_x3f_566_){
_start:
{
lean_object* v_opts_568_; lean_object* v_ignoreDeprecatedImports_569_; lean_object* v_ignoreDeprecatedImports_583_; lean_object* v___y_585_; lean_object* v_opts_586_; lean_object* v___y_591_; lean_object* v___y_592_; lean_object* v___y_593_; lean_object* v___y_617_; lean_object* v___y_618_; lean_object* v___y_619_; lean_object* v___y_620_; lean_object* v___y_621_; lean_object* v_moduleTk_622_; lean_object* v_val_632_; 
v_ignoreDeprecatedImports_583_ = l_Lean_NameSet_empty;
if (lean_obj_tag(v_origHeaderStx_x3f_566_) == 0)
{
if (lean_obj_tag(v_headerStx_x3f_565_) == 1)
{
lean_object* v_val_649_; 
v_val_649_ = lean_ctor_get(v_headerStx_x3f_565_, 0);
lean_inc(v_val_649_);
lean_dec_ref_known(v_headerStx_x3f_565_, 1);
v_val_632_ = v_val_649_;
goto v___jp_631_;
}
else
{
lean_dec(v_headerStx_x3f_565_);
v_opts_568_ = v_opts_561_;
v_ignoreDeprecatedImports_569_ = v_ignoreDeprecatedImports_583_;
goto v___jp_567_;
}
}
else
{
lean_object* v_val_650_; 
lean_dec(v_headerStx_x3f_565_);
v_val_650_ = lean_ctor_get(v_origHeaderStx_x3f_566_, 0);
lean_inc(v_val_650_);
lean_dec_ref_known(v_origHeaderStx_x3f_566_, 1);
v_val_632_ = v_val_650_;
goto v___jp_631_;
}
v___jp_567_:
{
lean_object* v___x_570_; uint8_t v___x_571_; uint8_t v___x_572_; 
v___x_570_ = l_Lean_linter_deprecated_module;
v___x_571_ = l_Lean_Option_get___at___00Lean_Elab_checkDeprecatedImports_spec__0(v_opts_568_, v___x_570_);
lean_dec_ref(v_opts_568_);
v___x_572_ = lean_bool_not(v___x_571_);
if (v___x_572_ == 0)
{
lean_object* v___x_573_; lean_object* v___x_574_; uint8_t v___x_575_; 
v___x_573_ = lean_unsigned_to_nat(0u);
v___x_574_ = lean_array_get_size(v_imports_560_);
v___x_575_ = lean_nat_dec_lt(v___x_573_, v___x_574_);
if (v___x_575_ == 0)
{
lean_dec(v_ignoreDeprecatedImports_569_);
lean_dec_ref(v_inputCtx_562_);
return v_messages_564_;
}
else
{
uint8_t v___x_576_; 
v___x_576_ = lean_nat_dec_le(v___x_574_, v___x_574_);
if (v___x_576_ == 0)
{
if (v___x_575_ == 0)
{
lean_dec(v_ignoreDeprecatedImports_569_);
lean_dec_ref(v_inputCtx_562_);
return v_messages_564_;
}
else
{
size_t v___x_577_; size_t v___x_578_; lean_object* v___x_579_; 
v___x_577_ = ((size_t)0ULL);
v___x_578_ = lean_usize_of_nat(v___x_574_);
v___x_579_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1(v_ignoreDeprecatedImports_569_, v_env_559_, v_inputCtx_562_, v_startPos_563_, v_imports_560_, v___x_577_, v___x_578_, v_messages_564_);
lean_dec(v_ignoreDeprecatedImports_569_);
return v___x_579_;
}
}
else
{
size_t v___x_580_; size_t v___x_581_; lean_object* v___x_582_; 
v___x_580_ = ((size_t)0ULL);
v___x_581_ = lean_usize_of_nat(v___x_574_);
v___x_582_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1(v_ignoreDeprecatedImports_569_, v_env_559_, v_inputCtx_562_, v_startPos_563_, v_imports_560_, v___x_580_, v___x_581_, v_messages_564_);
lean_dec(v_ignoreDeprecatedImports_569_);
return v___x_582_;
}
}
}
else
{
lean_dec(v_ignoreDeprecatedImports_569_);
lean_dec_ref(v_inputCtx_562_);
return v_messages_564_;
}
}
v___jp_584_:
{
size_t v_sz_587_; size_t v___x_588_; lean_object* v___x_589_; 
v_sz_587_ = lean_array_size(v___y_585_);
v___x_588_ = ((size_t)0ULL);
v___x_589_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkDeprecatedImports_spec__3(v___y_585_, v_sz_587_, v___x_588_, v_ignoreDeprecatedImports_583_);
lean_dec_ref(v___y_585_);
v_opts_568_ = v_opts_586_;
v_ignoreDeprecatedImports_569_ = v___x_589_;
goto v___jp_567_;
}
v___jp_590_:
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v_importsStx_596_; 
v___x_594_ = lean_unsigned_to_nat(2u);
v___x_595_ = l_Lean_Syntax_getArg(v___y_591_, v___x_594_);
lean_dec(v___y_591_);
v_importsStx_596_ = l_Lean_Syntax_getArgs(v___x_595_);
lean_dec(v___x_595_);
if (lean_obj_tag(v___y_592_) == 0)
{
lean_dec(v___y_593_);
v___y_585_ = v_importsStx_596_;
v_opts_586_ = v_opts_561_;
goto v___jp_584_;
}
else
{
lean_object* v_val_597_; lean_object* v___x_598_; 
v_val_597_ = lean_ctor_get(v___y_592_, 0);
lean_inc(v_val_597_);
lean_dec_ref_known(v___y_592_, 1);
v___x_598_ = l_Lean_Syntax_getTrailing_x3f(v_val_597_);
lean_dec(v_val_597_);
if (lean_obj_tag(v___x_598_) == 0)
{
lean_dec(v___y_593_);
v___y_585_ = v_importsStx_596_;
v_opts_586_ = v_opts_561_;
goto v___jp_584_;
}
else
{
lean_object* v_val_599_; lean_object* v_str_600_; lean_object* v_startPos_601_; lean_object* v_stopPos_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_615_; 
v_val_599_ = lean_ctor_get(v___x_598_, 0);
lean_inc(v_val_599_);
lean_dec_ref_known(v___x_598_, 1);
v_str_600_ = lean_ctor_get(v_val_599_, 0);
v_startPos_601_ = lean_ctor_get(v_val_599_, 1);
v_stopPos_602_ = lean_ctor_get(v_val_599_, 2);
v_isSharedCheck_615_ = !lean_is_exclusive(v_val_599_);
if (v_isSharedCheck_615_ == 0)
{
v___x_604_ = v_val_599_;
v_isShared_605_ = v_isSharedCheck_615_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_stopPos_602_);
lean_inc(v_startPos_601_);
lean_inc(v_str_600_);
lean_dec(v_val_599_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_615_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_609_; 
v___x_606_ = lean_string_utf8_extract(v_str_600_, v_startPos_601_, v_stopPos_602_);
lean_dec(v_stopPos_602_);
lean_dec(v_startPos_601_);
lean_dec_ref(v_str_600_);
v___x_607_ = lean_string_utf8_byte_size(v___x_606_);
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 2, v___x_607_);
lean_ctor_set(v___x_604_, 1, v___y_593_);
lean_ctor_set(v___x_604_, 0, v___x_606_);
v___x_609_ = v___x_604_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v___x_606_);
lean_ctor_set(v_reuseFailAlloc_614_, 1, v___y_593_);
lean_ctor_set(v_reuseFailAlloc_614_, 2, v___x_607_);
v___x_609_ = v_reuseFailAlloc_614_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
uint8_t v___x_610_; 
v___x_610_ = l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2(v___x_609_);
lean_dec_ref(v___x_609_);
if (v___x_610_ == 0)
{
v___y_585_ = v_importsStx_596_;
v_opts_586_ = v_opts_561_;
goto v___jp_584_;
}
else
{
lean_object* v___x_611_; uint8_t v___x_612_; lean_object* v_opts_613_; 
v___x_611_ = l_Lean_linter_deprecated_module;
v___x_612_ = 0;
v_opts_613_ = l_Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4(v_opts_561_, v___x_611_, v___x_612_);
v___y_585_ = v_importsStx_596_;
v_opts_586_ = v_opts_613_;
goto v___jp_584_;
}
}
}
}
}
}
v___jp_616_:
{
lean_object* v___x_623_; lean_object* v___x_624_; uint8_t v___x_625_; 
v___x_623_ = lean_unsigned_to_nat(1u);
v___x_624_ = l_Lean_Syntax_getArg(v___y_617_, v___x_623_);
v___x_625_ = l_Lean_Syntax_isNone(v___x_624_);
if (v___x_625_ == 0)
{
uint8_t v___x_626_; 
lean_inc(v___x_624_);
v___x_626_ = l_Lean_Syntax_matchesNull(v___x_624_, v___x_623_);
if (v___x_626_ == 0)
{
lean_dec(v___x_624_);
lean_dec(v_moduleTk_622_);
lean_dec(v___y_618_);
lean_dec(v___y_617_);
v_opts_568_ = v_opts_561_;
v_ignoreDeprecatedImports_569_ = v_ignoreDeprecatedImports_583_;
goto v___jp_567_;
}
else
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; uint8_t v___x_630_; 
v___x_627_ = l_Lean_Syntax_getArg(v___x_624_, v___y_618_);
lean_dec(v___x_624_);
v___x_628_ = ((lean_object*)(l_Lean_Elab_HeaderSyntax_imports___closed__6));
lean_inc_ref(v___y_620_);
lean_inc_ref(v___y_619_);
lean_inc_ref(v___y_621_);
v___x_629_ = l_Lean_Name_mkStr4(v___y_621_, v___y_619_, v___y_620_, v___x_628_);
v___x_630_ = l_Lean_Syntax_isOfKind(v___x_627_, v___x_629_);
lean_dec(v___x_629_);
if (v___x_630_ == 0)
{
lean_dec(v_moduleTk_622_);
lean_dec(v___y_618_);
lean_dec(v___y_617_);
v_opts_568_ = v_opts_561_;
v_ignoreDeprecatedImports_569_ = v_ignoreDeprecatedImports_583_;
goto v___jp_567_;
}
else
{
v___y_591_ = v___y_617_;
v___y_592_ = v_moduleTk_622_;
v___y_593_ = v___y_618_;
goto v___jp_590_;
}
}
}
else
{
lean_dec(v___x_624_);
v___y_591_ = v___y_617_;
v___y_592_ = v_moduleTk_622_;
v___y_593_ = v___y_618_;
goto v___jp_590_;
}
}
v___jp_631_:
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; uint8_t v___x_637_; 
v___x_633_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__0));
v___x_634_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__1));
v___x_635_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__2));
v___x_636_ = ((lean_object*)(l_Lean_Elab_HeaderSyntax_imports___closed__1));
lean_inc(v_val_632_);
v___x_637_ = l_Lean_Syntax_isOfKind(v_val_632_, v___x_636_);
if (v___x_637_ == 0)
{
lean_dec(v_val_632_);
v_opts_568_ = v_opts_561_;
v_ignoreDeprecatedImports_569_ = v_ignoreDeprecatedImports_583_;
goto v___jp_567_;
}
else
{
lean_object* v___x_638_; lean_object* v___x_639_; uint8_t v___x_640_; 
v___x_638_ = lean_unsigned_to_nat(0u);
v___x_639_ = l_Lean_Syntax_getArg(v_val_632_, v___x_638_);
v___x_640_ = l_Lean_Syntax_isNone(v___x_639_);
if (v___x_640_ == 0)
{
lean_object* v___x_641_; uint8_t v___x_642_; 
v___x_641_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_639_);
v___x_642_ = l_Lean_Syntax_matchesNull(v___x_639_, v___x_641_);
if (v___x_642_ == 0)
{
lean_dec(v___x_639_);
lean_dec(v_val_632_);
v_opts_568_ = v_opts_561_;
v_ignoreDeprecatedImports_569_ = v_ignoreDeprecatedImports_583_;
goto v___jp_567_;
}
else
{
lean_object* v___x_643_; lean_object* v___x_644_; uint8_t v___x_645_; 
v___x_643_ = l_Lean_Syntax_getArg(v___x_639_, v___x_638_);
lean_dec(v___x_639_);
v___x_644_ = ((lean_object*)(l_Lean_Elab_HeaderSyntax_imports___closed__9));
lean_inc(v___x_643_);
v___x_645_ = l_Lean_Syntax_isOfKind(v___x_643_, v___x_644_);
if (v___x_645_ == 0)
{
lean_dec(v___x_643_);
lean_dec(v_val_632_);
v_opts_568_ = v_opts_561_;
v_ignoreDeprecatedImports_569_ = v_ignoreDeprecatedImports_583_;
goto v___jp_567_;
}
else
{
lean_object* v_moduleTk_646_; lean_object* v___x_647_; 
v_moduleTk_646_ = l_Lean_Syntax_getArg(v___x_643_, v___x_638_);
lean_dec(v___x_643_);
v___x_647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_647_, 0, v_moduleTk_646_);
v___y_617_ = v_val_632_;
v___y_618_ = v___x_638_;
v___y_619_ = v___x_634_;
v___y_620_ = v___x_635_;
v___y_621_ = v___x_633_;
v_moduleTk_622_ = v___x_647_;
goto v___jp_616_;
}
}
}
else
{
lean_object* v___x_648_; 
lean_dec(v___x_639_);
v___x_648_ = lean_box(0);
v___y_617_ = v_val_632_;
v___y_618_ = v___x_638_;
v___y_619_ = v___x_634_;
v___y_620_ = v___x_635_;
v___y_621_ = v___x_633_;
v_moduleTk_622_ = v___x_648_;
goto v___jp_616_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedImports___boxed(lean_object* v_env_651_, lean_object* v_imports_652_, lean_object* v_opts_653_, lean_object* v_inputCtx_654_, lean_object* v_startPos_655_, lean_object* v_messages_656_, lean_object* v_headerStx_x3f_657_, lean_object* v_origHeaderStx_x3f_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_Lean_Elab_checkDeprecatedImports(v_env_651_, v_imports_652_, v_opts_653_, v_inputCtx_654_, v_startPos_655_, v_messages_656_, v_headerStx_x3f_657_, v_origHeaderStx_x3f_658_);
lean_dec(v_startPos_655_);
lean_dec_ref(v_imports_652_);
lean_dec_ref(v_env_651_);
return v_res_659_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_spec__2(lean_object* v_s_660_, lean_object* v_inst_661_, lean_object* v_R_662_, lean_object* v_a_663_, uint8_t v_b_664_, lean_object* v_c_665_){
_start:
{
uint8_t v___x_666_; 
v___x_666_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_spec__2___redArg(v_s_660_, v_a_663_, v_b_664_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_spec__2___boxed(lean_object* v_s_667_, lean_object* v_inst_668_, lean_object* v_R_669_, lean_object* v_a_670_, lean_object* v_b_671_, lean_object* v_c_672_){
_start:
{
uint8_t v_b_boxed_673_; uint8_t v_res_674_; lean_object* v_r_675_; 
v_b_boxed_673_ = lean_unbox(v_b_671_);
v_res_674_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_spec__2(v_s_667_, v_inst_668_, v_R_669_, v_a_670_, v_b_boxed_673_, v_c_672_);
lean_dec_ref(v_s_667_);
v_r_675_ = lean_box(v_res_674_);
return v_r_675_;
}
}
static lean_object* _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_676_; lean_object* v___x_677_; 
v___x_676_ = 33;
v___x_677_ = lean_box_uint32(v___x_676_);
return v___x_677_;
}
}
static lean_object* _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__2(void){
_start:
{
uint32_t v___x_678_; lean_object* v___x_679_; 
v___x_678_ = 42;
v___x_679_ = lean_box_uint32(v___x_678_);
return v___x_679_;
}
}
static lean_object* _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__3(void){
_start:
{
uint32_t v___x_680_; lean_object* v___x_681_; 
v___x_680_ = 63;
v___x_681_ = lean_box_uint32(v___x_680_);
return v___x_681_;
}
}
static lean_object* _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__4(void){
_start:
{
uint32_t v___x_682_; lean_object* v___x_683_; 
v___x_682_ = 124;
v___x_683_ = lean_box_uint32(v___x_682_);
return v___x_683_;
}
}
static lean_object* _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__5(void){
_start:
{
uint32_t v___x_684_; lean_object* v___x_685_; 
v___x_684_ = 34;
v___x_685_ = lean_box_uint32(v___x_684_);
return v___x_685_;
}
}
static lean_object* _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__6(void){
_start:
{
uint32_t v___x_686_; lean_object* v___x_687_; 
v___x_686_ = 62;
v___x_687_ = lean_box_uint32(v___x_686_);
return v___x_687_;
}
}
static lean_object* _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__7(void){
_start:
{
uint32_t v___x_688_; lean_object* v___x_689_; 
v___x_688_ = 60;
v___x_689_ = lean_box_uint32(v___x_688_);
return v___x_689_;
}
}
static lean_object* _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0(void){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_690_ = lean_unsigned_to_nat(7u);
v___x_691_ = lean_mk_empty_array_with_capacity(v___x_690_);
v___x_692_ = l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__7;
v___x_693_ = lean_array_push(v___x_691_, v___x_692_);
v___x_694_ = l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__6;
v___x_695_ = lean_array_push(v___x_693_, v___x_694_);
v___x_696_ = l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__5;
v___x_697_ = lean_array_push(v___x_695_, v___x_696_);
v___x_698_ = l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__4;
v___x_699_ = lean_array_push(v___x_697_, v___x_698_);
v___x_700_ = l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__3;
v___x_701_ = lean_array_push(v___x_699_, v___x_700_);
v___x_702_ = l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__2;
v___x_703_ = lean_array_push(v___x_701_, v___x_702_);
v___x_704_ = l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__1;
v___x_705_ = lean_array_push(v___x_703_, v___x_704_);
return v___x_705_;
}
}
static lean_object* _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars(void){
_start:
{
lean_object* v___x_706_; 
v___x_706_ = lean_obj_once(&l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0, &l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0_once, _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__0(lean_object* v_s_794_, lean_object* v_p_795_){
_start:
{
uint32_t v___y_797_; lean_object* v___x_802_; uint8_t v___x_803_; 
v___x_802_ = lean_string_utf8_byte_size(v_s_794_);
v___x_803_ = lean_nat_dec_eq(v_p_795_, v___x_802_);
if (v___x_803_ == 0)
{
uint32_t v___x_804_; uint32_t v___x_805_; uint8_t v___x_806_; 
v___x_804_ = lean_string_utf8_get_fast(v_s_794_, v_p_795_);
v___x_805_ = 97;
v___x_806_ = lean_uint32_dec_le(v___x_805_, v___x_804_);
if (v___x_806_ == 0)
{
v___y_797_ = v___x_804_;
goto v___jp_796_;
}
else
{
uint32_t v___x_807_; uint8_t v___x_808_; 
v___x_807_ = 122;
v___x_808_ = lean_uint32_dec_le(v___x_804_, v___x_807_);
if (v___x_808_ == 0)
{
v___y_797_ = v___x_804_;
goto v___jp_796_;
}
else
{
uint32_t v___x_809_; uint32_t v___x_810_; 
v___x_809_ = 4294967264;
v___x_810_ = lean_uint32_add(v___x_804_, v___x_809_);
v___y_797_ = v___x_810_;
goto v___jp_796_;
}
}
}
else
{
lean_dec(v_p_795_);
return v_s_794_;
}
v___jp_796_:
{
lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
lean_inc(v_p_795_);
v___x_798_ = lean_string_utf8_set(v_s_794_, v_p_795_, v___y_797_);
v___x_799_ = l_Char_utf8Size(v___y_797_);
v___x_800_ = lean_nat_add(v_p_795_, v___x_799_);
lean_dec(v___x_799_);
lean_dec(v_p_795_);
v_s_794_ = v___x_798_;
v_p_795_ = v___x_800_;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2_spec__3___redArg(lean_object* v_s_811_, uint32_t v_a_812_, lean_object* v_a_813_, uint8_t v_b_814_){
_start:
{
lean_object* v_str_815_; lean_object* v_startInclusive_816_; lean_object* v_endExclusive_817_; lean_object* v___x_818_; uint8_t v___x_819_; 
v_str_815_ = lean_ctor_get(v_s_811_, 0);
v_startInclusive_816_ = lean_ctor_get(v_s_811_, 1);
v_endExclusive_817_ = lean_ctor_get(v_s_811_, 2);
v___x_818_ = lean_nat_sub(v_endExclusive_817_, v_startInclusive_816_);
v___x_819_ = lean_nat_dec_eq(v_a_813_, v___x_818_);
lean_dec(v___x_818_);
if (v___x_819_ == 0)
{
lean_object* v___x_820_; uint32_t v___x_821_; uint8_t v___x_822_; 
v___x_820_ = lean_nat_add(v_startInclusive_816_, v_a_813_);
lean_dec(v_a_813_);
v___x_821_ = lean_string_utf8_get_fast(v_str_815_, v___x_820_);
v___x_822_ = lean_uint32_dec_eq(v___x_821_, v_a_812_);
if (v___x_822_ == 0)
{
lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_823_ = lean_string_utf8_next_fast(v_str_815_, v___x_820_);
lean_dec(v___x_820_);
v___x_824_ = lean_nat_sub(v___x_823_, v_startInclusive_816_);
v_a_813_ = v___x_824_;
v_b_814_ = v___x_822_;
goto _start;
}
else
{
lean_dec(v___x_820_);
return v___x_822_;
}
}
else
{
lean_dec(v_a_813_);
return v_b_814_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2_spec__3___redArg___boxed(lean_object* v_s_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_b_829_){
_start:
{
uint32_t v_a_boxed_830_; uint8_t v_b_boxed_831_; uint8_t v_res_832_; lean_object* v_r_833_; 
v_a_boxed_830_ = lean_unbox_uint32(v_a_827_);
lean_dec(v_a_827_);
v_b_boxed_831_ = lean_unbox(v_b_829_);
v_res_832_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2_spec__3___redArg(v_s_826_, v_a_boxed_830_, v_a_828_, v_b_boxed_831_);
lean_dec_ref(v_s_826_);
v_r_833_ = lean_box(v_res_832_);
return v_r_833_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2(uint32_t v_a_834_, lean_object* v_s_835_){
_start:
{
lean_object* v_searcher_836_; uint8_t v___x_837_; uint8_t v___x_838_; 
v_searcher_836_ = lean_unsigned_to_nat(0u);
v___x_837_ = 0;
v___x_838_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2_spec__3___redArg(v_s_835_, v_a_834_, v_searcher_836_, v___x_837_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2___boxed(lean_object* v_a_839_, lean_object* v_s_840_){
_start:
{
uint32_t v_a_boxed_841_; uint8_t v_res_842_; lean_object* v_r_843_; 
v_a_boxed_841_ = lean_unbox_uint32(v_a_839_);
lean_dec(v_a_839_);
v_res_842_ = l_String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2(v_a_boxed_841_, v_s_840_);
lean_dec_ref(v_s_840_);
v_r_843_ = lean_box(v_res_842_);
return v_r_843_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__3(lean_object* v_comp_847_, lean_object* v_as_848_, size_t v_sz_849_, size_t v_i_850_, lean_object* v_b_851_){
_start:
{
uint8_t v___x_852_; 
v___x_852_ = lean_usize_dec_lt(v_i_850_, v_sz_849_);
if (v___x_852_ == 0)
{
lean_dec_ref(v_comp_847_);
lean_inc_ref(v_b_851_);
return v_b_851_;
}
else
{
lean_object* v___x_853_; lean_object* v_a_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; uint32_t v___x_858_; uint8_t v___x_859_; 
v___x_853_ = lean_box(0);
v_a_854_ = lean_array_uget_borrowed(v_as_848_, v_i_850_);
v___x_855_ = lean_unsigned_to_nat(0u);
v___x_856_ = lean_string_utf8_byte_size(v_comp_847_);
lean_inc_ref(v_comp_847_);
v___x_857_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_857_, 0, v_comp_847_);
lean_ctor_set(v___x_857_, 1, v___x_855_);
lean_ctor_set(v___x_857_, 2, v___x_856_);
v___x_858_ = lean_unbox_uint32(v_a_854_);
v___x_859_ = l_String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2(v___x_858_, v___x_857_);
lean_dec_ref_known(v___x_857_, 3);
if (v___x_859_ == 0)
{
lean_object* v___x_860_; size_t v___x_861_; size_t v___x_862_; 
v___x_860_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__3___closed__0));
v___x_861_ = ((size_t)1ULL);
v___x_862_ = lean_usize_add(v_i_850_, v___x_861_);
v_i_850_ = v___x_862_;
v_b_851_ = v___x_860_;
goto _start;
}
else
{
lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
lean_dec_ref(v_comp_847_);
lean_inc(v_a_854_);
v___x_864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_864_, 0, v_a_854_);
v___x_865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_865_, 0, v___x_864_);
v___x_866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_866_, 0, v___x_865_);
lean_ctor_set(v___x_866_, 1, v___x_853_);
return v___x_866_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__3___boxed(lean_object* v_comp_867_, lean_object* v_as_868_, lean_object* v_sz_869_, lean_object* v_i_870_, lean_object* v_b_871_){
_start:
{
size_t v_sz_boxed_872_; size_t v_i_boxed_873_; lean_object* v_res_874_; 
v_sz_boxed_872_ = lean_unbox_usize(v_sz_869_);
lean_dec(v_sz_869_);
v_i_boxed_873_ = lean_unbox_usize(v_i_870_);
lean_dec(v_i_870_);
v_res_874_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__3(v_comp_867_, v_as_868_, v_sz_boxed_872_, v_i_boxed_873_, v_b_871_);
lean_dec_ref(v_b_871_);
lean_dec_ref(v_as_868_);
return v_res_874_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__1_spec__1(lean_object* v_a_875_, lean_object* v_as_876_, size_t v_i_877_, size_t v_stop_878_){
_start:
{
uint8_t v___x_879_; 
v___x_879_ = lean_usize_dec_eq(v_i_877_, v_stop_878_);
if (v___x_879_ == 0)
{
lean_object* v___x_880_; uint8_t v___x_881_; 
v___x_880_ = lean_array_uget_borrowed(v_as_876_, v_i_877_);
v___x_881_ = lean_string_dec_eq(v_a_875_, v___x_880_);
if (v___x_881_ == 0)
{
size_t v___x_882_; size_t v___x_883_; 
v___x_882_ = ((size_t)1ULL);
v___x_883_ = lean_usize_add(v_i_877_, v___x_882_);
v_i_877_ = v___x_883_;
goto _start;
}
else
{
return v___x_881_;
}
}
else
{
uint8_t v___x_885_; 
v___x_885_ = 0;
return v___x_885_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__1_spec__1___boxed(lean_object* v_a_886_, lean_object* v_as_887_, lean_object* v_i_888_, lean_object* v_stop_889_){
_start:
{
size_t v_i_boxed_890_; size_t v_stop_boxed_891_; uint8_t v_res_892_; lean_object* v_r_893_; 
v_i_boxed_890_ = lean_unbox_usize(v_i_888_);
lean_dec(v_i_888_);
v_stop_boxed_891_ = lean_unbox_usize(v_stop_889_);
lean_dec(v_stop_889_);
v_res_892_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__1_spec__1(v_a_886_, v_as_887_, v_i_boxed_890_, v_stop_boxed_891_);
lean_dec_ref(v_as_887_);
lean_dec_ref(v_a_886_);
v_r_893_ = lean_box(v_res_892_);
return v_r_893_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__1(lean_object* v_as_894_, lean_object* v_a_895_){
_start:
{
lean_object* v___x_896_; lean_object* v___x_897_; uint8_t v___x_898_; 
v___x_896_ = lean_unsigned_to_nat(0u);
v___x_897_ = lean_array_get_size(v_as_894_);
v___x_898_ = lean_nat_dec_lt(v___x_896_, v___x_897_);
if (v___x_898_ == 0)
{
return v___x_898_;
}
else
{
if (v___x_898_ == 0)
{
return v___x_898_;
}
else
{
size_t v___x_899_; size_t v___x_900_; uint8_t v___x_901_; 
v___x_899_ = ((size_t)0ULL);
v___x_900_ = lean_usize_of_nat(v___x_897_);
v___x_901_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__1_spec__1(v_a_895_, v_as_894_, v___x_899_, v___x_900_);
return v___x_901_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__1___boxed(lean_object* v_as_902_, lean_object* v_a_903_){
_start:
{
uint8_t v_res_904_; lean_object* v_r_905_; 
v_res_904_ = l_Array_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__1(v_as_902_, v_a_903_);
lean_dec_ref(v_a_903_);
lean_dec_ref(v_as_902_);
v_r_905_ = lean_box(v_res_904_);
return v_r_905_;
}
}
static size_t _init_l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__0(void){
_start:
{
lean_object* v___x_906_; size_t v_sz_907_; 
v___x_906_ = l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars;
v_sz_907_ = lean_array_size(v___x_906_);
return v_sz_907_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability(lean_object* v_comp_912_){
_start:
{
lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; uint8_t v___x_916_; 
v___x_913_ = ((lean_object*)(l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames));
v___x_914_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_comp_912_);
v___x_915_ = l_String_mapAux___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__0(v_comp_912_, v___x_914_);
v___x_916_ = l_Array_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__1(v___x_913_, v___x_915_);
lean_dec_ref(v___x_915_);
if (v___x_916_ == 0)
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; size_t v_sz_920_; size_t v___x_921_; lean_object* v___x_922_; lean_object* v_fst_923_; 
v___x_917_ = l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars;
v___x_918_ = lean_box(0);
v___x_919_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__3___closed__0));
v_sz_920_ = lean_usize_once(&l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__0, &l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__0_once, _init_l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__0);
v___x_921_ = ((size_t)0ULL);
v___x_922_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__3(v_comp_912_, v___x_917_, v_sz_920_, v___x_921_, v___x_919_);
v_fst_923_ = lean_ctor_get(v___x_922_, 0);
lean_inc(v_fst_923_);
lean_dec_ref(v___x_922_);
if (lean_obj_tag(v_fst_923_) == 0)
{
return v___x_918_;
}
else
{
lean_object* v_val_924_; 
v_val_924_ = lean_ctor_get(v_fst_923_, 0);
lean_inc(v_val_924_);
lean_dec_ref_known(v_fst_923_, 1);
if (lean_obj_tag(v_val_924_) == 1)
{
lean_object* v_val_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_939_; 
v_val_925_ = lean_ctor_get(v_val_924_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v_val_924_);
if (v_isSharedCheck_939_ == 0)
{
v___x_927_ = v_val_924_;
v_isShared_928_ = v_isSharedCheck_939_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_val_925_);
lean_dec(v_val_924_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_939_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_929_; lean_object* v___x_930_; uint32_t v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_937_; 
v___x_929_ = ((lean_object*)(l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__1));
v___x_930_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___closed__0));
v___x_931_ = lean_unbox_uint32(v_val_925_);
lean_dec(v_val_925_);
v___x_932_ = lean_string_push(v___x_930_, v___x_931_);
v___x_933_ = lean_string_append(v___x_929_, v___x_932_);
lean_dec_ref(v___x_932_);
v___x_934_ = ((lean_object*)(l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__2));
v___x_935_ = lean_string_append(v___x_933_, v___x_934_);
if (v_isShared_928_ == 0)
{
lean_ctor_set(v___x_927_, 0, v___x_935_);
v___x_937_ = v___x_927_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v___x_935_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
}
else
{
lean_dec(v_val_924_);
return v___x_918_;
}
}
}
else
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_940_ = ((lean_object*)(l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__3));
v___x_941_ = lean_string_append(v___x_940_, v_comp_912_);
lean_dec_ref(v_comp_912_);
v___x_942_ = ((lean_object*)(l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__4));
v___x_943_ = lean_string_append(v___x_941_, v___x_942_);
v___x_944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_944_, 0, v___x_943_);
return v___x_944_;
}
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2_spec__3(lean_object* v_s_945_, uint32_t v_a_946_, lean_object* v_inst_947_, lean_object* v_R_948_, lean_object* v_a_949_, uint8_t v_b_950_, lean_object* v_c_951_){
_start:
{
uint8_t v___x_952_; 
v___x_952_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2_spec__3___redArg(v_s_945_, v_a_946_, v_a_949_, v_b_950_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2_spec__3___boxed(lean_object* v_s_953_, lean_object* v_a_954_, lean_object* v_inst_955_, lean_object* v_R_956_, lean_object* v_a_957_, lean_object* v_b_958_, lean_object* v_c_959_){
_start:
{
uint32_t v_a_boxed_960_; uint8_t v_b_boxed_961_; uint8_t v_res_962_; lean_object* v_r_963_; 
v_a_boxed_960_ = lean_unbox_uint32(v_a_954_);
lean_dec(v_a_954_);
v_b_boxed_961_ = lean_unbox(v_b_958_);
v_res_962_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2_spec__3(v_s_953_, v_a_boxed_960_, v_inst_955_, v_R_956_, v_a_957_, v_b_boxed_961_, v_c_959_);
lean_dec_ref(v_s_953_);
v_r_963_ = lean_box(v_res_962_);
return v_r_963_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_checkModuleNamePortability_go(lean_object* v_mainModule_966_, lean_object* v_inputCtx_967_, lean_object* v_startPos_968_, lean_object* v_a_969_, lean_object* v_a_970_){
_start:
{
switch(lean_obj_tag(v_a_969_))
{
case 0:
{
lean_dec_ref(v_inputCtx_967_);
lean_dec(v_mainModule_966_);
return v_a_970_;
}
case 1:
{
lean_object* v_pre_971_; lean_object* v_str_972_; lean_object* v___x_973_; 
v_pre_971_ = lean_ctor_get(v_a_969_, 0);
lean_inc(v_pre_971_);
v_str_972_ = lean_ctor_get(v_a_969_, 1);
lean_inc_ref(v_str_972_);
lean_dec_ref_known(v_a_969_, 2);
v___x_973_ = l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability(v_str_972_);
if (lean_obj_tag(v___x_973_) == 0)
{
v_a_969_ = v_pre_971_;
goto _start;
}
else
{
lean_object* v_val_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_1000_; 
v_val_975_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_977_ = v___x_973_;
v_isShared_978_ = v_isSharedCheck_1000_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_val_975_);
lean_dec(v___x_973_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_1000_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v_fileName_979_; lean_object* v_fileMap_980_; lean_object* v___x_981_; lean_object* v___x_982_; uint8_t v___x_983_; uint8_t v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; uint8_t v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_994_; 
v_fileName_979_ = lean_ctor_get(v_inputCtx_967_, 1);
v_fileMap_980_ = lean_ctor_get(v_inputCtx_967_, 2);
lean_inc_ref(v_fileMap_980_);
v___x_981_ = l_Lean_FileMap_toPosition(v_fileMap_980_, v_startPos_968_);
v___x_982_ = lean_box(0);
v___x_983_ = 0;
v___x_984_ = 2;
v___x_985_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___closed__0));
v___x_986_ = ((lean_object*)(l___private_Lean_Elab_Import_0__Lean_Elab_checkModuleNamePortability_go___closed__0));
v___x_987_ = 1;
lean_inc(v_mainModule_966_);
v___x_988_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mainModule_966_, v___x_987_);
v___x_989_ = lean_string_append(v___x_986_, v___x_988_);
lean_dec_ref(v___x_988_);
v___x_990_ = ((lean_object*)(l___private_Lean_Elab_Import_0__Lean_Elab_checkModuleNamePortability_go___closed__1));
v___x_991_ = lean_string_append(v___x_989_, v___x_990_);
v___x_992_ = lean_string_append(v___x_991_, v_val_975_);
lean_dec(v_val_975_);
if (v_isShared_978_ == 0)
{
lean_ctor_set_tag(v___x_977_, 3);
lean_ctor_set(v___x_977_, 0, v___x_992_);
v___x_994_ = v___x_977_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v___x_992_);
v___x_994_ = v_reuseFailAlloc_999_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_995_ = l_Lean_MessageData_ofFormat(v___x_994_);
lean_inc_ref(v_fileName_979_);
v___x_996_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_996_, 0, v_fileName_979_);
lean_ctor_set(v___x_996_, 1, v___x_981_);
lean_ctor_set(v___x_996_, 2, v___x_982_);
lean_ctor_set(v___x_996_, 3, v___x_985_);
lean_ctor_set(v___x_996_, 4, v___x_995_);
lean_ctor_set_uint8(v___x_996_, sizeof(void*)*5, v___x_983_);
lean_ctor_set_uint8(v___x_996_, sizeof(void*)*5 + 1, v___x_984_);
lean_ctor_set_uint8(v___x_996_, sizeof(void*)*5 + 2, v___x_983_);
v___x_997_ = l_Lean_MessageLog_add(v___x_996_, v_a_970_);
v_a_969_ = v_pre_971_;
v_a_970_ = v___x_997_;
goto _start;
}
}
}
}
default: 
{
lean_object* v_pre_1001_; 
v_pre_1001_ = lean_ctor_get(v_a_969_, 0);
lean_inc(v_pre_1001_);
lean_dec_ref_known(v_a_969_, 2);
v_a_969_ = v_pre_1001_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_checkModuleNamePortability_go___boxed(lean_object* v_mainModule_1003_, lean_object* v_inputCtx_1004_, lean_object* v_startPos_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_){
_start:
{
lean_object* v_res_1008_; 
v_res_1008_ = l___private_Lean_Elab_Import_0__Lean_Elab_checkModuleNamePortability_go(v_mainModule_1003_, v_inputCtx_1004_, v_startPos_1005_, v_a_1006_, v_a_1007_);
lean_dec(v_startPos_1005_);
return v_res_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkModuleNamePortability(lean_object* v_mainModule_1009_, lean_object* v_inputCtx_1010_, lean_object* v_startPos_1011_, lean_object* v_messages_1012_){
_start:
{
lean_object* v___x_1013_; 
lean_inc(v_mainModule_1009_);
v___x_1013_ = l___private_Lean_Elab_Import_0__Lean_Elab_checkModuleNamePortability_go(v_mainModule_1009_, v_inputCtx_1010_, v_startPos_1011_, v_mainModule_1009_, v_messages_1012_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkModuleNamePortability___boxed(lean_object* v_mainModule_1014_, lean_object* v_inputCtx_1015_, lean_object* v_startPos_1016_, lean_object* v_messages_1017_){
_start:
{
lean_object* v_res_1018_; 
v_res_1018_ = l_Lean_Elab_checkModuleNamePortability(v_mainModule_1014_, v_inputCtx_1015_, v_startPos_1016_, v_messages_1017_);
lean_dec(v_startPos_1016_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_processHeaderCore(lean_object* v_startPos_1019_, lean_object* v_imports_1020_, uint8_t v_isModule_1021_, lean_object* v_opts_1022_, lean_object* v_messages_1023_, lean_object* v_inputCtx_1024_, uint32_t v_trustLevel_1025_, lean_object* v_plugins_1026_, uint8_t v_leakEnv_1027_, lean_object* v_mainModule_1028_, lean_object* v_package_x3f_1029_, lean_object* v_arts_1030_, lean_object* v_headerStx_x3f_1031_, lean_object* v_origHeaderStx_x3f_1032_){
_start:
{
lean_object* v_fst_1035_; lean_object* v_snd_1036_; uint8_t v___x_1044_; uint8_t v___y_1046_; 
v___x_1044_ = 1;
if (v_isModule_1021_ == 0)
{
uint8_t v___x_1079_; 
v___x_1079_ = 2;
v___y_1046_ = v___x_1079_;
goto v___jp_1045_;
}
else
{
lean_object* v___x_1080_; uint8_t v___x_1081_; 
v___x_1080_ = l_Lean_Elab_inServer;
v___x_1081_ = l_Lean_Option_get___at___00Lean_Elab_checkDeprecatedImports_spec__0(v_opts_1022_, v___x_1080_);
if (v___x_1081_ == 0)
{
uint8_t v___x_1082_; 
v___x_1082_ = 0;
v___y_1046_ = v___x_1082_;
goto v___jp_1045_;
}
else
{
uint8_t v___x_1083_; 
v___x_1083_ = 1;
v___y_1046_ = v___x_1083_;
goto v___jp_1045_;
}
}
v___jp_1034_:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; 
lean_inc_n(v_mainModule_1028_, 2);
v___x_1037_ = l_Lean_Environment_setMainModule(v_fst_1035_, v_mainModule_1028_);
v___x_1038_ = l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
v___x_1039_ = l_Lean_PersistentEnvExtension_setState___redArg(v___x_1038_, v___x_1037_, v_package_x3f_1029_);
lean_inc_ref(v_inputCtx_1024_);
v___x_1040_ = l_Lean_Elab_checkDeprecatedImports(v___x_1039_, v_imports_1020_, v_opts_1022_, v_inputCtx_1024_, v_startPos_1019_, v_snd_1036_, v_headerStx_x3f_1031_, v_origHeaderStx_x3f_1032_);
lean_dec_ref(v_imports_1020_);
v___x_1041_ = l___private_Lean_Elab_Import_0__Lean_Elab_checkModuleNamePortability_go(v_mainModule_1028_, v_inputCtx_1024_, v_startPos_1019_, v_mainModule_1028_, v___x_1040_);
v___x_1042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1039_);
lean_ctor_set(v___x_1042_, 1, v___x_1041_);
v___x_1043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1042_);
return v___x_1043_;
}
v___jp_1045_:
{
lean_object* v___x_1047_; 
lean_inc_ref(v_opts_1022_);
lean_inc_ref(v_imports_1020_);
v___x_1047_ = l_Lean_importModules(v_imports_1020_, v_opts_1022_, v_trustLevel_1025_, v_plugins_1026_, v_leakEnv_1027_, v___x_1044_, v___y_1046_, v_arts_1030_);
if (lean_obj_tag(v___x_1047_) == 0)
{
lean_object* v_a_1048_; 
v_a_1048_ = lean_ctor_get(v___x_1047_, 0);
lean_inc(v_a_1048_);
lean_dec_ref_known(v___x_1047_, 1);
v_fst_1035_ = v_a_1048_;
v_snd_1036_ = v_messages_1023_;
goto v___jp_1034_;
}
else
{
lean_object* v_a_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1078_; 
v_a_1049_ = lean_ctor_get(v___x_1047_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v___x_1047_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1051_ = v___x_1047_;
v_isShared_1052_ = v_isSharedCheck_1078_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_a_1049_);
lean_dec(v___x_1047_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1078_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
uint32_t v___x_1053_; lean_object* v___x_1054_; 
v___x_1053_ = 0;
v___x_1054_ = l_Lean_mkEmptyEnvironment(v___x_1053_);
if (lean_obj_tag(v___x_1054_) == 0)
{
lean_object* v_a_1055_; lean_object* v_fileName_1056_; lean_object* v_fileMap_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; uint8_t v___x_1060_; uint8_t v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1065_; 
v_a_1055_ = lean_ctor_get(v___x_1054_, 0);
lean_inc(v_a_1055_);
lean_dec_ref_known(v___x_1054_, 1);
v_fileName_1056_ = lean_ctor_get(v_inputCtx_1024_, 1);
v_fileMap_1057_ = lean_ctor_get(v_inputCtx_1024_, 2);
lean_inc_ref(v_fileMap_1057_);
v___x_1058_ = l_Lean_FileMap_toPosition(v_fileMap_1057_, v_startPos_1019_);
v___x_1059_ = lean_box(0);
v___x_1060_ = 0;
v___x_1061_ = 2;
v___x_1062_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___closed__0));
v___x_1063_ = lean_io_error_to_string(v_a_1049_);
if (v_isShared_1052_ == 0)
{
lean_ctor_set_tag(v___x_1051_, 3);
lean_ctor_set(v___x_1051_, 0, v___x_1063_);
v___x_1065_ = v___x_1051_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v___x_1063_);
v___x_1065_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1066_ = l_Lean_MessageData_ofFormat(v___x_1065_);
lean_inc_ref(v_fileName_1056_);
v___x_1067_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1067_, 0, v_fileName_1056_);
lean_ctor_set(v___x_1067_, 1, v___x_1058_);
lean_ctor_set(v___x_1067_, 2, v___x_1059_);
lean_ctor_set(v___x_1067_, 3, v___x_1062_);
lean_ctor_set(v___x_1067_, 4, v___x_1066_);
lean_ctor_set_uint8(v___x_1067_, sizeof(void*)*5, v___x_1060_);
lean_ctor_set_uint8(v___x_1067_, sizeof(void*)*5 + 1, v___x_1061_);
lean_ctor_set_uint8(v___x_1067_, sizeof(void*)*5 + 2, v___x_1060_);
v___x_1068_ = l_Lean_MessageLog_add(v___x_1067_, v_messages_1023_);
v_fst_1035_ = v_a_1055_;
v_snd_1036_ = v___x_1068_;
goto v___jp_1034_;
}
}
else
{
lean_object* v_a_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1077_; 
lean_del_object(v___x_1051_);
lean_dec(v_a_1049_);
lean_dec(v_origHeaderStx_x3f_1032_);
lean_dec(v_headerStx_x3f_1031_);
lean_dec(v_package_x3f_1029_);
lean_dec(v_mainModule_1028_);
lean_dec_ref(v_inputCtx_1024_);
lean_dec_ref(v_messages_1023_);
lean_dec_ref(v_opts_1022_);
lean_dec_ref(v_imports_1020_);
v_a_1070_ = lean_ctor_get(v___x_1054_, 0);
v_isSharedCheck_1077_ = !lean_is_exclusive(v___x_1054_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1072_ = v___x_1054_;
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_a_1070_);
lean_dec(v___x_1054_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1075_; 
if (v_isShared_1073_ == 0)
{
v___x_1075_ = v___x_1072_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v_a_1070_);
v___x_1075_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
return v___x_1075_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_processHeaderCore___boxed(lean_object* v_startPos_1084_, lean_object* v_imports_1085_, lean_object* v_isModule_1086_, lean_object* v_opts_1087_, lean_object* v_messages_1088_, lean_object* v_inputCtx_1089_, lean_object* v_trustLevel_1090_, lean_object* v_plugins_1091_, lean_object* v_leakEnv_1092_, lean_object* v_mainModule_1093_, lean_object* v_package_x3f_1094_, lean_object* v_arts_1095_, lean_object* v_headerStx_x3f_1096_, lean_object* v_origHeaderStx_x3f_1097_, lean_object* v_a_1098_){
_start:
{
uint8_t v_isModule_boxed_1099_; uint32_t v_trustLevel_boxed_1100_; uint8_t v_leakEnv_boxed_1101_; lean_object* v_res_1102_; 
v_isModule_boxed_1099_ = lean_unbox(v_isModule_1086_);
v_trustLevel_boxed_1100_ = lean_unbox_uint32(v_trustLevel_1090_);
lean_dec(v_trustLevel_1090_);
v_leakEnv_boxed_1101_ = lean_unbox(v_leakEnv_1092_);
v_res_1102_ = l_Lean_Elab_processHeaderCore(v_startPos_1084_, v_imports_1085_, v_isModule_boxed_1099_, v_opts_1087_, v_messages_1088_, v_inputCtx_1089_, v_trustLevel_boxed_1100_, v_plugins_1091_, v_leakEnv_boxed_1101_, v_mainModule_1093_, v_package_x3f_1094_, v_arts_1095_, v_headerStx_x3f_1096_, v_origHeaderStx_x3f_1097_);
lean_dec(v_startPos_1084_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_processHeader(lean_object* v_header_1103_, lean_object* v_opts_1104_, lean_object* v_messages_1105_, lean_object* v_inputCtx_1106_, uint32_t v_trustLevel_1107_, lean_object* v_plugins_1108_, uint8_t v_leakEnv_1109_, lean_object* v_mainModule_1110_){
_start:
{
lean_object* v___x_1112_; uint8_t v___x_1113_; lean_object* v___x_1114_; uint8_t v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1112_ = l_Lean_Elab_HeaderSyntax_startPos(v_header_1103_);
v___x_1113_ = 1;
lean_inc(v_header_1103_);
v___x_1114_ = l_Lean_Elab_HeaderSyntax_imports(v_header_1103_, v___x_1113_);
v___x_1115_ = l_Lean_Elab_HeaderSyntax_isModule(v_header_1103_);
v___x_1116_ = lean_box(0);
v___x_1117_ = lean_box(1);
v___x_1118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1118_, 0, v_header_1103_);
v___x_1119_ = l_Lean_Elab_processHeaderCore(v___x_1112_, v___x_1114_, v___x_1115_, v_opts_1104_, v_messages_1105_, v_inputCtx_1106_, v_trustLevel_1107_, v_plugins_1108_, v_leakEnv_1109_, v_mainModule_1110_, v___x_1116_, v___x_1117_, v___x_1118_, v___x_1116_);
lean_dec(v___x_1112_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_processHeader___boxed(lean_object* v_header_1120_, lean_object* v_opts_1121_, lean_object* v_messages_1122_, lean_object* v_inputCtx_1123_, lean_object* v_trustLevel_1124_, lean_object* v_plugins_1125_, lean_object* v_leakEnv_1126_, lean_object* v_mainModule_1127_, lean_object* v_a_1128_){
_start:
{
uint32_t v_trustLevel_boxed_1129_; uint8_t v_leakEnv_boxed_1130_; lean_object* v_res_1131_; 
v_trustLevel_boxed_1129_ = lean_unbox_uint32(v_trustLevel_1124_);
lean_dec(v_trustLevel_1124_);
v_leakEnv_boxed_1130_ = lean_unbox(v_leakEnv_1126_);
v_res_1131_ = l_Lean_Elab_processHeader(v_header_1120_, v_opts_1121_, v_messages_1122_, v_inputCtx_1123_, v_trustLevel_boxed_1129_, v_plugins_1125_, v_leakEnv_boxed_1130_, v_mainModule_1127_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_parseImports(lean_object* v_input_1133_, lean_object* v_fileName_1134_){
_start:
{
lean_object* v___y_1137_; 
if (lean_obj_tag(v_fileName_1134_) == 0)
{
lean_object* v___x_1182_; 
v___x_1182_ = ((lean_object*)(l_Lean_Elab_parseImports___closed__0));
v___y_1137_ = v___x_1182_;
goto v___jp_1136_;
}
else
{
lean_object* v_val_1183_; 
v_val_1183_ = lean_ctor_get(v_fileName_1134_, 0);
lean_inc(v_val_1183_);
lean_dec_ref_known(v_fileName_1134_, 1);
v___y_1137_ = v_val_1183_;
goto v___jp_1136_;
}
v___jp_1136_:
{
uint8_t v___x_1138_; lean_object* v___x_1139_; lean_object* v_inputCtx_1140_; lean_object* v___x_1141_; 
v___x_1138_ = 1;
v___x_1139_ = lean_string_utf8_byte_size(v_input_1133_);
v_inputCtx_1140_ = l_Lean_Parser_mkInputContext___redArg(v_input_1133_, v___y_1137_, v___x_1138_, v___x_1139_);
lean_inc_ref(v_inputCtx_1140_);
v___x_1141_ = l_Lean_Parser_parseHeader(v_inputCtx_1140_);
if (lean_obj_tag(v___x_1141_) == 0)
{
lean_object* v_a_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1173_; 
v_a_1142_ = lean_ctor_get(v___x_1141_, 0);
v_isSharedCheck_1173_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_1144_ = v___x_1141_;
v_isShared_1145_ = v_isSharedCheck_1173_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_a_1142_);
lean_dec(v___x_1141_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1173_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v_snd_1146_; lean_object* v_fst_1147_; lean_object* v_fst_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1171_; 
v_snd_1146_ = lean_ctor_get(v_a_1142_, 1);
lean_inc(v_snd_1146_);
v_fst_1147_ = lean_ctor_get(v_snd_1146_, 0);
lean_inc(v_fst_1147_);
v_fst_1148_ = lean_ctor_get(v_a_1142_, 0);
v_isSharedCheck_1171_ = !lean_is_exclusive(v_a_1142_);
if (v_isSharedCheck_1171_ == 0)
{
lean_object* v_unused_1172_; 
v_unused_1172_ = lean_ctor_get(v_a_1142_, 1);
lean_dec(v_unused_1172_);
v___x_1150_ = v_a_1142_;
v_isShared_1151_ = v_isSharedCheck_1171_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_fst_1148_);
lean_dec(v_a_1142_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1171_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v_snd_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1169_; 
v_snd_1152_ = lean_ctor_get(v_snd_1146_, 1);
v_isSharedCheck_1169_ = !lean_is_exclusive(v_snd_1146_);
if (v_isSharedCheck_1169_ == 0)
{
lean_object* v_unused_1170_; 
v_unused_1170_ = lean_ctor_get(v_snd_1146_, 0);
lean_dec(v_unused_1170_);
v___x_1154_ = v_snd_1146_;
v_isShared_1155_ = v_isSharedCheck_1169_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_snd_1152_);
lean_dec(v_snd_1146_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1169_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v_fileMap_1156_; lean_object* v_pos_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1161_; 
v_fileMap_1156_ = lean_ctor_get(v_inputCtx_1140_, 2);
lean_inc_ref(v_fileMap_1156_);
lean_dec_ref(v_inputCtx_1140_);
v_pos_1157_ = lean_ctor_get(v_fst_1147_, 0);
lean_inc(v_pos_1157_);
lean_dec(v_fst_1147_);
v___x_1158_ = l_Lean_Elab_HeaderSyntax_imports(v_fst_1148_, v___x_1138_);
v___x_1159_ = l_Lean_FileMap_toPosition(v_fileMap_1156_, v_pos_1157_);
lean_dec(v_pos_1157_);
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 0, v___x_1159_);
v___x_1161_ = v___x_1154_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v___x_1159_);
lean_ctor_set(v_reuseFailAlloc_1168_, 1, v_snd_1152_);
v___x_1161_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
lean_object* v___x_1163_; 
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 1, v___x_1161_);
lean_ctor_set(v___x_1150_, 0, v___x_1158_);
v___x_1163_ = v___x_1150_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v___x_1158_);
lean_ctor_set(v_reuseFailAlloc_1167_, 1, v___x_1161_);
v___x_1163_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
lean_object* v___x_1165_; 
if (v_isShared_1145_ == 0)
{
lean_ctor_set(v___x_1144_, 0, v___x_1163_);
v___x_1165_ = v___x_1144_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v___x_1163_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1181_; 
lean_dec_ref(v_inputCtx_1140_);
v_a_1174_ = lean_ctor_get(v___x_1141_, 0);
v_isSharedCheck_1181_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1176_ = v___x_1141_;
v_isShared_1177_ = v_isSharedCheck_1181_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_a_1174_);
lean_dec(v___x_1141_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1181_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
lean_object* v___x_1179_; 
if (v_isShared_1177_ == 0)
{
v___x_1179_ = v___x_1176_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_a_1174_);
v___x_1179_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
return v___x_1179_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_parseImports___boxed(lean_object* v_input_1184_, lean_object* v_fileName_1185_, lean_object* v_a_1186_){
_start:
{
lean_object* v_res_1187_; 
v_res_1187_ = l_Lean_Elab_parseImports(v_input_1184_, v_fileName_1185_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00Lean_Elab_printImports_spec__0_spec__0(lean_object* v_s_1188_){
_start:
{
lean_object* v___x_1190_; lean_object* v_putStr_1191_; lean_object* v___x_1192_; 
v___x_1190_ = lean_get_stdout();
v_putStr_1191_ = lean_ctor_get(v___x_1190_, 4);
lean_inc_ref(v_putStr_1191_);
lean_dec_ref(v___x_1190_);
v___x_1192_ = lean_apply_2(v_putStr_1191_, v_s_1188_, lean_box(0));
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00Lean_Elab_printImports_spec__0_spec__0___boxed(lean_object* v_s_1193_, lean_object* v_a_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l_IO_print___at___00IO_println___at___00Lean_Elab_printImports_spec__0_spec__0(v_s_1193_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00Lean_Elab_printImports_spec__0(lean_object* v_s_1196_){
_start:
{
uint32_t v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1198_ = 10;
v___x_1199_ = lean_string_push(v_s_1196_, v___x_1198_);
v___x_1200_ = l_IO_print___at___00IO_println___at___00Lean_Elab_printImports_spec__0_spec__0(v___x_1199_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00Lean_Elab_printImports_spec__0___boxed(lean_object* v_s_1201_, lean_object* v_a_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l_IO_println___at___00Lean_Elab_printImports_spec__0(v_s_1201_);
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImports_spec__1(lean_object* v_as_1204_, size_t v_sz_1205_, size_t v_i_1206_, lean_object* v_b_1207_){
_start:
{
uint8_t v___x_1209_; 
v___x_1209_ = lean_usize_dec_lt(v_i_1206_, v_sz_1205_);
if (v___x_1209_ == 0)
{
lean_object* v___x_1210_; 
v___x_1210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1210_, 0, v_b_1207_);
return v___x_1210_;
}
else
{
lean_object* v_a_1211_; lean_object* v_module_1212_; lean_object* v___x_1213_; 
v_a_1211_ = lean_array_uget_borrowed(v_as_1204_, v_i_1206_);
v_module_1212_ = lean_ctor_get(v_a_1211_, 0);
lean_inc(v_module_1212_);
v___x_1213_ = l_Lean_findOLean(v_module_1212_);
if (lean_obj_tag(v___x_1213_) == 0)
{
lean_object* v_a_1214_; lean_object* v___x_1215_; 
v_a_1214_ = lean_ctor_get(v___x_1213_, 0);
lean_inc(v_a_1214_);
lean_dec_ref_known(v___x_1213_, 1);
v___x_1215_ = l_IO_println___at___00Lean_Elab_printImports_spec__0(v_a_1214_);
if (lean_obj_tag(v___x_1215_) == 0)
{
lean_object* v___x_1216_; size_t v___x_1217_; size_t v___x_1218_; 
lean_dec_ref_known(v___x_1215_, 1);
v___x_1216_ = lean_box(0);
v___x_1217_ = ((size_t)1ULL);
v___x_1218_ = lean_usize_add(v_i_1206_, v___x_1217_);
v_i_1206_ = v___x_1218_;
v_b_1207_ = v___x_1216_;
goto _start;
}
else
{
return v___x_1215_;
}
}
else
{
lean_object* v_a_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1227_; 
v_a_1220_ = lean_ctor_get(v___x_1213_, 0);
v_isSharedCheck_1227_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1222_ = v___x_1213_;
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_a_1220_);
lean_dec(v___x_1213_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1225_; 
if (v_isShared_1223_ == 0)
{
v___x_1225_ = v___x_1222_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_a_1220_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
return v___x_1225_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImports_spec__1___boxed(lean_object* v_as_1228_, lean_object* v_sz_1229_, lean_object* v_i_1230_, lean_object* v_b_1231_, lean_object* v___y_1232_){
_start:
{
size_t v_sz_boxed_1233_; size_t v_i_boxed_1234_; lean_object* v_res_1235_; 
v_sz_boxed_1233_ = lean_unbox_usize(v_sz_1229_);
lean_dec(v_sz_1229_);
v_i_boxed_1234_ = lean_unbox_usize(v_i_1230_);
lean_dec(v_i_1230_);
v_res_1235_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImports_spec__1(v_as_1228_, v_sz_boxed_1233_, v_i_boxed_1234_, v_b_1231_);
lean_dec_ref(v_as_1228_);
return v_res_1235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_printImports(lean_object* v_input_1236_, lean_object* v_fileName_1237_){
_start:
{
lean_object* v___x_1239_; 
v___x_1239_ = l_Lean_Elab_parseImports(v_input_1236_, v_fileName_1237_);
if (lean_obj_tag(v___x_1239_) == 0)
{
lean_object* v_a_1240_; lean_object* v_fst_1241_; lean_object* v___x_1242_; size_t v_sz_1243_; size_t v___x_1244_; lean_object* v___x_1245_; 
v_a_1240_ = lean_ctor_get(v___x_1239_, 0);
lean_inc(v_a_1240_);
lean_dec_ref_known(v___x_1239_, 1);
v_fst_1241_ = lean_ctor_get(v_a_1240_, 0);
lean_inc(v_fst_1241_);
lean_dec(v_a_1240_);
v___x_1242_ = lean_box(0);
v_sz_1243_ = lean_array_size(v_fst_1241_);
v___x_1244_ = ((size_t)0ULL);
v___x_1245_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImports_spec__1(v_fst_1241_, v_sz_1243_, v___x_1244_, v___x_1242_);
lean_dec(v_fst_1241_);
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1252_; 
v_isSharedCheck_1252_ = !lean_is_exclusive(v___x_1245_);
if (v_isSharedCheck_1252_ == 0)
{
lean_object* v_unused_1253_; 
v_unused_1253_ = lean_ctor_get(v___x_1245_, 0);
lean_dec(v_unused_1253_);
v___x_1247_ = v___x_1245_;
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
else
{
lean_dec(v___x_1245_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1250_; 
if (v_isShared_1248_ == 0)
{
lean_ctor_set(v___x_1247_, 0, v___x_1242_);
v___x_1250_ = v___x_1247_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v___x_1242_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
}
else
{
return v___x_1245_;
}
}
else
{
lean_object* v_a_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1261_; 
v_a_1254_ = lean_ctor_get(v___x_1239_, 0);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1256_ = v___x_1239_;
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_a_1254_);
lean_dec(v___x_1239_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1259_; 
if (v_isShared_1257_ == 0)
{
v___x_1259_ = v___x_1256_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_a_1254_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_printImports___boxed(lean_object* v_input_1262_, lean_object* v_fileName_1263_, lean_object* v_a_1264_){
_start:
{
lean_object* v_res_1265_; 
v_res_1265_ = l_Lean_Elab_printImports(v_input_1262_, v_fileName_1263_);
return v_res_1265_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImportSrcs_spec__0(lean_object* v_a_1266_, lean_object* v_as_1267_, size_t v_sz_1268_, size_t v_i_1269_, lean_object* v_b_1270_){
_start:
{
uint8_t v___x_1272_; 
v___x_1272_ = lean_usize_dec_lt(v_i_1269_, v_sz_1268_);
if (v___x_1272_ == 0)
{
lean_object* v___x_1273_; 
lean_dec(v_a_1266_);
v___x_1273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1273_, 0, v_b_1270_);
return v___x_1273_;
}
else
{
lean_object* v_a_1274_; lean_object* v_module_1275_; lean_object* v___x_1276_; 
v_a_1274_ = lean_array_uget_borrowed(v_as_1267_, v_i_1269_);
v_module_1275_ = lean_ctor_get(v_a_1274_, 0);
lean_inc(v_module_1275_);
lean_inc(v_a_1266_);
v___x_1276_ = l_Lean_findLean(v_a_1266_, v_module_1275_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v_a_1277_; lean_object* v___x_1278_; 
v_a_1277_ = lean_ctor_get(v___x_1276_, 0);
lean_inc(v_a_1277_);
lean_dec_ref_known(v___x_1276_, 1);
v___x_1278_ = l_IO_println___at___00Lean_Elab_printImports_spec__0(v_a_1277_);
if (lean_obj_tag(v___x_1278_) == 0)
{
lean_object* v___x_1279_; size_t v___x_1280_; size_t v___x_1281_; 
lean_dec_ref_known(v___x_1278_, 1);
v___x_1279_ = lean_box(0);
v___x_1280_ = ((size_t)1ULL);
v___x_1281_ = lean_usize_add(v_i_1269_, v___x_1280_);
v_i_1269_ = v___x_1281_;
v_b_1270_ = v___x_1279_;
goto _start;
}
else
{
lean_dec(v_a_1266_);
return v___x_1278_;
}
}
else
{
lean_object* v_a_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1290_; 
lean_dec(v_a_1266_);
v_a_1283_ = lean_ctor_get(v___x_1276_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1285_ = v___x_1276_;
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_a_1283_);
lean_dec(v___x_1276_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1288_; 
if (v_isShared_1286_ == 0)
{
v___x_1288_ = v___x_1285_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_a_1283_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImportSrcs_spec__0___boxed(lean_object* v_a_1291_, lean_object* v_as_1292_, lean_object* v_sz_1293_, lean_object* v_i_1294_, lean_object* v_b_1295_, lean_object* v___y_1296_){
_start:
{
size_t v_sz_boxed_1297_; size_t v_i_boxed_1298_; lean_object* v_res_1299_; 
v_sz_boxed_1297_ = lean_unbox_usize(v_sz_1293_);
lean_dec(v_sz_1293_);
v_i_boxed_1298_ = lean_unbox_usize(v_i_1294_);
lean_dec(v_i_1294_);
v_res_1299_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImportSrcs_spec__0(v_a_1291_, v_as_1292_, v_sz_boxed_1297_, v_i_boxed_1298_, v_b_1295_);
lean_dec_ref(v_as_1292_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_printImportSrcs(lean_object* v_input_1300_, lean_object* v_fileName_1301_){
_start:
{
lean_object* v___x_1303_; 
v___x_1303_ = l_Lean_getSrcSearchPath();
if (lean_obj_tag(v___x_1303_) == 0)
{
lean_object* v_a_1304_; lean_object* v___x_1305_; 
v_a_1304_ = lean_ctor_get(v___x_1303_, 0);
lean_inc(v_a_1304_);
lean_dec_ref_known(v___x_1303_, 1);
v___x_1305_ = l_Lean_Elab_parseImports(v_input_1300_, v_fileName_1301_);
if (lean_obj_tag(v___x_1305_) == 0)
{
lean_object* v_a_1306_; lean_object* v_fst_1307_; lean_object* v___x_1308_; size_t v_sz_1309_; size_t v___x_1310_; lean_object* v___x_1311_; 
v_a_1306_ = lean_ctor_get(v___x_1305_, 0);
lean_inc(v_a_1306_);
lean_dec_ref_known(v___x_1305_, 1);
v_fst_1307_ = lean_ctor_get(v_a_1306_, 0);
lean_inc(v_fst_1307_);
lean_dec(v_a_1306_);
v___x_1308_ = lean_box(0);
v_sz_1309_ = lean_array_size(v_fst_1307_);
v___x_1310_ = ((size_t)0ULL);
v___x_1311_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImportSrcs_spec__0(v_a_1304_, v_fst_1307_, v_sz_1309_, v___x_1310_, v___x_1308_);
lean_dec(v_fst_1307_);
if (lean_obj_tag(v___x_1311_) == 0)
{
lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1318_; 
v_isSharedCheck_1318_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1318_ == 0)
{
lean_object* v_unused_1319_; 
v_unused_1319_ = lean_ctor_get(v___x_1311_, 0);
lean_dec(v_unused_1319_);
v___x_1313_ = v___x_1311_;
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
else
{
lean_dec(v___x_1311_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1316_; 
if (v_isShared_1314_ == 0)
{
lean_ctor_set(v___x_1313_, 0, v___x_1308_);
v___x_1316_ = v___x_1313_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v___x_1308_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
}
else
{
return v___x_1311_;
}
}
else
{
lean_object* v_a_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1327_; 
lean_dec(v_a_1304_);
v_a_1320_ = lean_ctor_get(v___x_1305_, 0);
v_isSharedCheck_1327_ = !lean_is_exclusive(v___x_1305_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1322_ = v___x_1305_;
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_a_1320_);
lean_dec(v___x_1305_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v___x_1325_; 
if (v_isShared_1323_ == 0)
{
v___x_1325_ = v___x_1322_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_a_1320_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
}
}
}
}
else
{
lean_object* v_a_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1335_; 
lean_dec(v_fileName_1301_);
lean_dec_ref(v_input_1300_);
v_a_1328_ = lean_ctor_get(v___x_1303_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1303_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1330_ = v___x_1303_;
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_a_1328_);
lean_dec(v___x_1303_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1333_; 
if (v_isShared_1331_ == 0)
{
v___x_1333_ = v___x_1330_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_a_1328_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_printImportSrcs___boxed(lean_object* v_input_1336_, lean_object* v_fileName_1337_, lean_object* v_a_1338_){
_start:
{
lean_object* v_res_1339_; 
v_res_1339_ = l_Lean_Elab_printImportSrcs(v_input_1336_, v_fileName_1337_);
return v_res_1339_;
}
}
lean_object* runtime_initialize_Lean_Parser_Module(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_ModPkgExt(uint8_t builtin);
lean_object* runtime_initialize_Lean_DeprecatedModule(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Modify(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Import(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Parser_Module(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_ModPkgExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DeprecatedModule(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Modify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__1 = _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__1();
lean_mark_persistent(l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__1);
l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__2 = _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__2();
lean_mark_persistent(l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__2);
l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__3 = _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__3();
lean_mark_persistent(l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__3);
l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__4 = _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__4();
lean_mark_persistent(l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__4);
l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__5 = _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__5();
lean_mark_persistent(l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__5);
l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__6 = _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__6();
lean_mark_persistent(l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__6);
l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__7 = _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__7();
lean_mark_persistent(l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__7);
l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars = _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars();
lean_mark_persistent(l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Parser_Module(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Import(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Parser_Module(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Parser_Module(uint8_t builtin);
lean_object* initialize_Lean_Parser_Module(uint8_t builtin);
lean_object* initialize_Lean_Compiler_ModPkgExt(uint8_t builtin);
lean_object* initialize_Lean_DeprecatedModule(uint8_t builtin);
lean_object* initialize_Init_Data_String_Modify(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Import(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Module(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Module(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_ModPkgExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DeprecatedModule(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Modify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Import(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Import(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Import(builtin);
}
#ifdef __cplusplus
}
#endif

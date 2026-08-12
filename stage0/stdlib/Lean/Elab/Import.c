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
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTrailing_x3f(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_String_Slice_posGE___redArg(lean_object*, lean_object*);
lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_checkDeprecatedImports___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkDeprecatedImports___closed__0;
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
lean_object* v___x_9_; lean_object* v___x_10_; uint8_t v___x_11_; 
v___x_9_ = lean_unsigned_to_nat(0u);
v___x_10_ = l_Lean_Syntax_getArg(v_header_8_, v___x_9_);
v___x_11_ = l_Lean_Syntax_isNone(v___x_10_);
lean_dec(v___x_10_);
if (v___x_11_ == 0)
{
uint8_t v___x_12_; 
v___x_12_ = 1;
return v___x_12_;
}
else
{
uint8_t v___x_13_; 
v___x_13_ = 0;
return v___x_13_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_HeaderSyntax_isModule___boxed(lean_object* v_header_14_){
_start:
{
uint8_t v_res_15_; lean_object* v_r_16_; 
v_res_15_ = l_Lean_Elab_HeaderSyntax_isModule(v_header_14_);
lean_dec(v_header_14_);
v_r_16_ = lean_box(v_res_15_);
return v_r_16_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__0___closed__0(void){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = l_Array_instInhabited(lean_box(0));
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__0(lean_object* v_msg_18_){
_start:
{
lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_19_ = lean_obj_once(&l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__0___closed__0, &l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__0___closed__0_once, _init_l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__0___closed__0);
v___x_20_ = lean_panic_fn_borrowed(v___x_19_, v_msg_18_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__1(lean_object* v_msg_21_){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_22_ = l_Lean_instInhabitedImport_default;
v___x_23_ = lean_panic_fn_borrowed(v___x_22_, v_msg_21_);
return v___x_23_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8(void){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_36_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__7));
v___x_37_ = lean_unsigned_to_nat(13u);
v___x_38_ = lean_unsigned_to_nat(40u);
v___x_39_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__6));
v___x_40_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__5));
v___x_41_ = l_mkPanicMessageWithDecl(v___x_40_, v___x_39_, v___x_38_, v___x_37_, v___x_36_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2(lean_object* v_moduleTk_60_, uint8_t v___x_61_, size_t v_sz_62_, size_t v_i_63_, lean_object* v_bs_64_){
_start:
{
uint8_t v___x_65_; 
v___x_65_ = lean_usize_dec_lt(v_i_63_, v_sz_62_);
if (v___x_65_ == 0)
{
return v_bs_64_;
}
else
{
lean_object* v___x_66_; lean_object* v_v_67_; lean_object* v___x_68_; lean_object* v_bs_x27_69_; lean_object* v___y_71_; lean_object* v___y_77_; uint8_t v___y_78_; uint8_t v___y_79_; lean_object* v___y_80_; uint8_t v___y_81_; lean_object* v___y_86_; uint8_t v___y_87_; lean_object* v___y_88_; uint8_t v___y_89_; uint8_t v___y_90_; lean_object* v___y_92_; uint8_t v___y_93_; lean_object* v___y_94_; lean_object* v___y_95_; uint8_t v___y_96_; uint8_t v___x_98_; 
v___x_66_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__4));
v_v_67_ = lean_array_uget(v_bs_64_, v_i_63_);
v___x_68_ = lean_unsigned_to_nat(0u);
v_bs_x27_69_ = lean_array_uset(v_bs_64_, v_i_63_, v___x_68_);
lean_inc(v_v_67_);
v___x_98_ = l_Lean_Syntax_isOfKind(v_v_67_, v___x_66_);
if (v___x_98_ == 0)
{
lean_object* v___x_99_; lean_object* v___x_100_; 
lean_dec(v_v_67_);
v___x_99_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8);
v___x_100_ = l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__1(v___x_99_);
v___y_71_ = v___x_100_;
goto v___jp_70_;
}
else
{
lean_object* v___y_102_; lean_object* v___y_103_; lean_object* v_allTk_104_; lean_object* v___x_114_; lean_object* v___y_116_; lean_object* v_metaTk_117_; lean_object* v_publicTk_133_; lean_object* v___x_147_; uint8_t v___x_148_; 
v___x_114_ = lean_unsigned_to_nat(1u);
v___x_147_ = l_Lean_Syntax_getArg(v_v_67_, v___x_68_);
v___x_148_ = l_Lean_Syntax_isNone(v___x_147_);
if (v___x_148_ == 0)
{
uint8_t v___x_149_; 
lean_inc(v___x_147_);
v___x_149_ = l_Lean_Syntax_matchesNull(v___x_147_, v___x_114_);
if (v___x_149_ == 0)
{
lean_object* v___x_150_; lean_object* v___x_151_; 
lean_dec(v___x_147_);
lean_dec(v_v_67_);
v___x_150_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8);
v___x_151_ = l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__1(v___x_150_);
v___y_71_ = v___x_151_;
goto v___jp_70_;
}
else
{
lean_object* v___x_152_; lean_object* v___x_153_; uint8_t v___x_154_; 
v___x_152_ = l_Lean_Syntax_getArg(v___x_147_, v___x_68_);
lean_dec(v___x_147_);
v___x_153_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__14));
lean_inc(v___x_152_);
v___x_154_ = l_Lean_Syntax_isOfKind(v___x_152_, v___x_153_);
if (v___x_154_ == 0)
{
lean_object* v___x_155_; lean_object* v___x_156_; 
lean_dec(v___x_152_);
lean_dec(v_v_67_);
v___x_155_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8);
v___x_156_ = l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__1(v___x_155_);
v___y_71_ = v___x_156_;
goto v___jp_70_;
}
else
{
lean_object* v_publicTk_157_; lean_object* v___x_158_; 
v_publicTk_157_ = l_Lean_Syntax_getArg(v___x_152_, v___x_68_);
lean_dec(v___x_152_);
v___x_158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_158_, 0, v_publicTk_157_);
v_publicTk_133_ = v___x_158_;
goto v___jp_132_;
}
}
}
else
{
lean_object* v___x_159_; 
lean_dec(v___x_147_);
v___x_159_ = lean_box(0);
v_publicTk_133_ = v___x_159_;
goto v___jp_132_;
}
v___jp_101_:
{
lean_object* v___x_105_; lean_object* v___x_106_; uint8_t v___x_107_; 
v___x_105_ = lean_unsigned_to_nat(5u);
v___x_106_ = l_Lean_Syntax_getArg(v_v_67_, v___x_105_);
v___x_107_ = l_Lean_Syntax_matchesNull(v___x_106_, v___x_68_);
if (v___x_107_ == 0)
{
lean_object* v___x_108_; lean_object* v___x_109_; 
lean_dec(v_allTk_104_);
lean_dec(v___y_103_);
lean_dec(v___y_102_);
lean_dec(v_v_67_);
v___x_108_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8);
v___x_109_ = l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__1(v___x_108_);
v___y_71_ = v___x_109_;
goto v___jp_70_;
}
else
{
lean_object* v___x_110_; lean_object* v_n_111_; lean_object* v___x_112_; 
v___x_110_ = lean_unsigned_to_nat(4u);
v_n_111_ = l_Lean_Syntax_getArg(v_v_67_, v___x_110_);
lean_dec(v_v_67_);
v___x_112_ = l_Lean_TSyntax_getId(v_n_111_);
lean_dec(v_n_111_);
if (lean_obj_tag(v_allTk_104_) == 0)
{
uint8_t v___x_113_; 
v___x_113_ = 0;
v___y_92_ = v___y_102_;
v___y_93_ = v___x_107_;
v___y_94_ = v___y_103_;
v___y_95_ = v___x_112_;
v___y_96_ = v___x_113_;
goto v___jp_91_;
}
else
{
lean_dec_ref_known(v_allTk_104_, 1);
v___y_92_ = v___y_102_;
v___y_93_ = v___x_107_;
v___y_94_ = v___y_103_;
v___y_95_ = v___x_112_;
v___y_96_ = v___x_107_;
goto v___jp_91_;
}
}
}
v___jp_115_:
{
lean_object* v___x_118_; lean_object* v___x_119_; uint8_t v___x_120_; 
v___x_118_ = lean_unsigned_to_nat(3u);
v___x_119_ = l_Lean_Syntax_getArg(v_v_67_, v___x_118_);
v___x_120_ = l_Lean_Syntax_isNone(v___x_119_);
if (v___x_120_ == 0)
{
uint8_t v___x_121_; 
lean_inc(v___x_119_);
v___x_121_ = l_Lean_Syntax_matchesNull(v___x_119_, v___x_114_);
if (v___x_121_ == 0)
{
lean_object* v___x_122_; lean_object* v___x_123_; 
lean_dec(v___x_119_);
lean_dec(v_metaTk_117_);
lean_dec(v___y_116_);
lean_dec(v_v_67_);
v___x_122_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8);
v___x_123_ = l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__1(v___x_122_);
v___y_71_ = v___x_123_;
goto v___jp_70_;
}
else
{
lean_object* v___x_124_; lean_object* v___x_125_; uint8_t v___x_126_; 
v___x_124_ = l_Lean_Syntax_getArg(v___x_119_, v___x_68_);
lean_dec(v___x_119_);
v___x_125_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__10));
lean_inc(v___x_124_);
v___x_126_ = l_Lean_Syntax_isOfKind(v___x_124_, v___x_125_);
if (v___x_126_ == 0)
{
lean_object* v___x_127_; lean_object* v___x_128_; 
lean_dec(v___x_124_);
lean_dec(v_metaTk_117_);
lean_dec(v___y_116_);
lean_dec(v_v_67_);
v___x_127_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8);
v___x_128_ = l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__1(v___x_127_);
v___y_71_ = v___x_128_;
goto v___jp_70_;
}
else
{
lean_object* v_allTk_129_; lean_object* v___x_130_; 
v_allTk_129_ = l_Lean_Syntax_getArg(v___x_124_, v___x_68_);
lean_dec(v___x_124_);
v___x_130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_130_, 0, v_allTk_129_);
v___y_102_ = v_metaTk_117_;
v___y_103_ = v___y_116_;
v_allTk_104_ = v___x_130_;
goto v___jp_101_;
}
}
}
else
{
lean_object* v___x_131_; 
lean_dec(v___x_119_);
v___x_131_ = lean_box(0);
v___y_102_ = v_metaTk_117_;
v___y_103_ = v___y_116_;
v_allTk_104_ = v___x_131_;
goto v___jp_101_;
}
}
v___jp_132_:
{
lean_object* v___x_134_; uint8_t v___x_135_; 
v___x_134_ = l_Lean_Syntax_getArg(v_v_67_, v___x_114_);
v___x_135_ = l_Lean_Syntax_isNone(v___x_134_);
if (v___x_135_ == 0)
{
uint8_t v___x_136_; 
lean_inc(v___x_134_);
v___x_136_ = l_Lean_Syntax_matchesNull(v___x_134_, v___x_114_);
if (v___x_136_ == 0)
{
lean_object* v___x_137_; lean_object* v___x_138_; 
lean_dec(v___x_134_);
lean_dec(v_publicTk_133_);
lean_dec(v_v_67_);
v___x_137_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8);
v___x_138_ = l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__1(v___x_137_);
v___y_71_ = v___x_138_;
goto v___jp_70_;
}
else
{
lean_object* v___x_139_; lean_object* v___x_140_; uint8_t v___x_141_; 
v___x_139_ = l_Lean_Syntax_getArg(v___x_134_, v___x_68_);
lean_dec(v___x_134_);
v___x_140_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__12));
lean_inc(v___x_139_);
v___x_141_ = l_Lean_Syntax_isOfKind(v___x_139_, v___x_140_);
if (v___x_141_ == 0)
{
lean_object* v___x_142_; lean_object* v___x_143_; 
lean_dec(v___x_139_);
lean_dec(v_publicTk_133_);
lean_dec(v_v_67_);
v___x_142_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8);
v___x_143_ = l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__1(v___x_142_);
v___y_71_ = v___x_143_;
goto v___jp_70_;
}
else
{
lean_object* v_metaTk_144_; lean_object* v___x_145_; 
v_metaTk_144_ = l_Lean_Syntax_getArg(v___x_139_, v___x_68_);
lean_dec(v___x_139_);
v___x_145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_145_, 0, v_metaTk_144_);
v___y_116_ = v_publicTk_133_;
v_metaTk_117_ = v___x_145_;
goto v___jp_115_;
}
}
}
else
{
lean_object* v___x_146_; 
lean_dec(v___x_134_);
v___x_146_ = lean_box(0);
v___y_116_ = v_publicTk_133_;
v_metaTk_117_ = v___x_146_;
goto v___jp_115_;
}
}
}
v___jp_70_:
{
size_t v___x_72_; size_t v___x_73_; lean_object* v___x_74_; 
v___x_72_ = ((size_t)1ULL);
v___x_73_ = lean_usize_add(v_i_63_, v___x_72_);
v___x_74_ = lean_array_uset(v_bs_x27_69_, v_i_63_, v___y_71_);
v_i_63_ = v___x_73_;
v_bs_64_ = v___x_74_;
goto _start;
}
v___jp_76_:
{
if (lean_obj_tag(v___y_77_) == 0)
{
uint8_t v___x_82_; lean_object* v___x_83_; 
v___x_82_ = 0;
v___x_83_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_83_, 0, v___y_80_);
lean_ctor_set_uint8(v___x_83_, sizeof(void*)*1, v___y_79_);
lean_ctor_set_uint8(v___x_83_, sizeof(void*)*1 + 1, v___y_81_);
lean_ctor_set_uint8(v___x_83_, sizeof(void*)*1 + 2, v___x_82_);
v___y_71_ = v___x_83_;
goto v___jp_70_;
}
else
{
lean_object* v___x_84_; 
lean_dec_ref_known(v___y_77_, 1);
v___x_84_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_84_, 0, v___y_80_);
lean_ctor_set_uint8(v___x_84_, sizeof(void*)*1, v___y_79_);
lean_ctor_set_uint8(v___x_84_, sizeof(void*)*1 + 1, v___y_81_);
lean_ctor_set_uint8(v___x_84_, sizeof(void*)*1 + 2, v___y_78_);
v___y_71_ = v___x_84_;
goto v___jp_70_;
}
}
v___jp_85_:
{
if (lean_obj_tag(v_moduleTk_60_) == 0)
{
v___y_77_ = v___y_86_;
v___y_78_ = v___y_87_;
v___y_79_ = v___y_89_;
v___y_80_ = v___y_88_;
v___y_81_ = v___y_87_;
goto v___jp_76_;
}
else
{
v___y_77_ = v___y_86_;
v___y_78_ = v___y_87_;
v___y_79_ = v___y_89_;
v___y_80_ = v___y_88_;
v___y_81_ = v___y_90_;
goto v___jp_76_;
}
}
v___jp_91_:
{
if (lean_obj_tag(v___y_94_) == 0)
{
uint8_t v___x_97_; 
v___x_97_ = 0;
v___y_86_ = v___y_92_;
v___y_87_ = v___y_93_;
v___y_88_ = v___y_95_;
v___y_89_ = v___y_96_;
v___y_90_ = v___x_97_;
goto v___jp_85_;
}
else
{
lean_dec_ref_known(v___y_94_, 1);
if (v___y_93_ == 0)
{
v___y_86_ = v___y_92_;
v___y_87_ = v___y_93_;
v___y_88_ = v___y_95_;
v___y_89_ = v___y_96_;
v___y_90_ = v___y_93_;
goto v___jp_85_;
}
else
{
v___y_77_ = v___y_92_;
v___y_78_ = v___y_93_;
v___y_79_ = v___y_96_;
v___y_80_ = v___y_95_;
v___y_81_ = v___x_61_;
goto v___jp_76_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___boxed(lean_object* v_moduleTk_160_, lean_object* v___x_161_, lean_object* v_sz_162_, lean_object* v_i_163_, lean_object* v_bs_164_){
_start:
{
uint8_t v___x_3706__boxed_165_; size_t v_sz_boxed_166_; size_t v_i_boxed_167_; lean_object* v_res_168_; 
v___x_3706__boxed_165_ = lean_unbox(v___x_161_);
v_sz_boxed_166_ = lean_unbox_usize(v_sz_162_);
lean_dec(v_sz_162_);
v_i_boxed_167_ = lean_unbox_usize(v_i_163_);
lean_dec(v_i_163_);
v_res_168_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2(v_moduleTk_160_, v___x_3706__boxed_165_, v_sz_boxed_166_, v_i_boxed_167_, v_bs_164_);
lean_dec(v_moduleTk_160_);
return v_res_168_;
}
}
static lean_object* _init_l_Lean_Elab_HeaderSyntax_imports___closed__2(void){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_175_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__7));
v___x_176_ = lean_unsigned_to_nat(9u);
v___x_177_ = lean_unsigned_to_nat(41u);
v___x_178_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__6));
v___x_179_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__5));
v___x_180_ = l_mkPanicMessageWithDecl(v___x_179_, v___x_178_, v___x_177_, v___x_176_, v___x_175_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_HeaderSyntax_imports(lean_object* v_stx_198_, uint8_t v_includeInit_199_){
_start:
{
lean_object* v___x_200_; uint8_t v___x_201_; lean_object* v___y_203_; lean_object* v___y_204_; lean_object* v___y_205_; 
v___x_200_ = ((lean_object*)(l_Lean_Elab_HeaderSyntax_imports___closed__1));
lean_inc(v_stx_198_);
v___x_201_ = l_Lean_Syntax_isOfKind(v_stx_198_, v___x_200_);
if (v___x_201_ == 0)
{
lean_object* v___x_210_; lean_object* v___x_211_; 
lean_dec(v_stx_198_);
v___x_210_ = lean_obj_once(&l_Lean_Elab_HeaderSyntax_imports___closed__2, &l_Lean_Elab_HeaderSyntax_imports___closed__2_once, _init_l_Lean_Elab_HeaderSyntax_imports___closed__2);
v___x_211_ = l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__0(v___x_210_);
return v___x_211_;
}
else
{
lean_object* v___x_212_; lean_object* v___y_214_; lean_object* v___y_215_; lean_object* v___y_218_; lean_object* v_preludeTk_219_; lean_object* v_moduleTk_231_; lean_object* v___x_246_; uint8_t v___x_247_; 
v___x_212_ = lean_unsigned_to_nat(0u);
v___x_246_ = l_Lean_Syntax_getArg(v_stx_198_, v___x_212_);
v___x_247_ = l_Lean_Syntax_isNone(v___x_246_);
if (v___x_247_ == 0)
{
lean_object* v___x_248_; uint8_t v___x_249_; 
v___x_248_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_246_);
v___x_249_ = l_Lean_Syntax_matchesNull(v___x_246_, v___x_248_);
if (v___x_249_ == 0)
{
lean_object* v___x_250_; lean_object* v___x_251_; 
lean_dec(v___x_246_);
lean_dec(v_stx_198_);
v___x_250_ = lean_obj_once(&l_Lean_Elab_HeaderSyntax_imports___closed__2, &l_Lean_Elab_HeaderSyntax_imports___closed__2_once, _init_l_Lean_Elab_HeaderSyntax_imports___closed__2);
v___x_251_ = l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__0(v___x_250_);
return v___x_251_;
}
else
{
lean_object* v___x_252_; lean_object* v___x_253_; uint8_t v___x_254_; 
v___x_252_ = l_Lean_Syntax_getArg(v___x_246_, v___x_212_);
lean_dec(v___x_246_);
v___x_253_ = ((lean_object*)(l_Lean_Elab_HeaderSyntax_imports___closed__9));
lean_inc(v___x_252_);
v___x_254_ = l_Lean_Syntax_isOfKind(v___x_252_, v___x_253_);
if (v___x_254_ == 0)
{
lean_object* v___x_255_; lean_object* v___x_256_; 
lean_dec(v___x_252_);
lean_dec(v_stx_198_);
v___x_255_ = lean_obj_once(&l_Lean_Elab_HeaderSyntax_imports___closed__2, &l_Lean_Elab_HeaderSyntax_imports___closed__2_once, _init_l_Lean_Elab_HeaderSyntax_imports___closed__2);
v___x_256_ = l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__0(v___x_255_);
return v___x_256_;
}
else
{
lean_object* v_moduleTk_257_; lean_object* v___x_258_; 
v_moduleTk_257_ = l_Lean_Syntax_getArg(v___x_252_, v___x_212_);
lean_dec(v___x_252_);
v___x_258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_258_, 0, v_moduleTk_257_);
v_moduleTk_231_ = v___x_258_;
goto v___jp_230_;
}
}
}
else
{
lean_object* v___x_259_; 
lean_dec(v___x_246_);
v___x_259_ = lean_box(0);
v_moduleTk_231_ = v___x_259_;
goto v___jp_230_;
}
v___jp_213_:
{
lean_object* v___x_216_; 
v___x_216_ = ((lean_object*)(l_Lean_Elab_HeaderSyntax_imports___closed__3));
v___y_203_ = v___y_214_;
v___y_204_ = v___y_215_;
v___y_205_ = v___x_216_;
goto v___jp_202_;
}
v___jp_217_:
{
lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v_importsStx_222_; 
v___x_220_ = lean_unsigned_to_nat(2u);
v___x_221_ = l_Lean_Syntax_getArg(v_stx_198_, v___x_220_);
lean_dec(v_stx_198_);
v_importsStx_222_ = l_Lean_Syntax_getArgs(v___x_221_);
lean_dec(v___x_221_);
if (lean_obj_tag(v_preludeTk_219_) == 0)
{
if (v___x_201_ == 0)
{
v___y_214_ = v___y_218_;
v___y_215_ = v_importsStx_222_;
goto v___jp_213_;
}
else
{
if (v_includeInit_199_ == 0)
{
v___y_214_ = v___y_218_;
v___y_215_ = v_importsStx_222_;
goto v___jp_213_;
}
else
{
lean_object* v___x_223_; uint8_t v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_223_ = ((lean_object*)(l_Lean_Elab_HeaderSyntax_imports___closed__5));
v___x_224_ = 0;
v___x_225_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_225_, 0, v___x_223_);
lean_ctor_set_uint8(v___x_225_, sizeof(void*)*1, v___x_224_);
lean_ctor_set_uint8(v___x_225_, sizeof(void*)*1 + 1, v___x_201_);
lean_ctor_set_uint8(v___x_225_, sizeof(void*)*1 + 2, v___x_224_);
v___x_226_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_226_, 0, v___x_223_);
lean_ctor_set_uint8(v___x_226_, sizeof(void*)*1, v___x_224_);
lean_ctor_set_uint8(v___x_226_, sizeof(void*)*1 + 1, v___x_201_);
lean_ctor_set_uint8(v___x_226_, sizeof(void*)*1 + 2, v___x_201_);
v___x_227_ = lean_mk_empty_array_with_capacity(v___x_220_);
v___x_228_ = lean_array_push(v___x_227_, v___x_225_);
v___x_229_ = lean_array_push(v___x_228_, v___x_226_);
v___y_203_ = v___y_218_;
v___y_204_ = v_importsStx_222_;
v___y_205_ = v___x_229_;
goto v___jp_202_;
}
}
}
else
{
lean_dec_ref_known(v_preludeTk_219_, 1);
v___y_214_ = v___y_218_;
v___y_215_ = v_importsStx_222_;
goto v___jp_213_;
}
}
v___jp_230_:
{
lean_object* v___x_232_; lean_object* v___x_233_; uint8_t v___x_234_; 
v___x_232_ = lean_unsigned_to_nat(1u);
v___x_233_ = l_Lean_Syntax_getArg(v_stx_198_, v___x_232_);
v___x_234_ = l_Lean_Syntax_isNone(v___x_233_);
if (v___x_234_ == 0)
{
uint8_t v___x_235_; 
lean_inc(v___x_233_);
v___x_235_ = l_Lean_Syntax_matchesNull(v___x_233_, v___x_232_);
if (v___x_235_ == 0)
{
lean_object* v___x_236_; lean_object* v___x_237_; 
lean_dec(v___x_233_);
lean_dec(v_moduleTk_231_);
lean_dec(v_stx_198_);
v___x_236_ = lean_obj_once(&l_Lean_Elab_HeaderSyntax_imports___closed__2, &l_Lean_Elab_HeaderSyntax_imports___closed__2_once, _init_l_Lean_Elab_HeaderSyntax_imports___closed__2);
v___x_237_ = l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__0(v___x_236_);
return v___x_237_;
}
else
{
lean_object* v___x_238_; lean_object* v___x_239_; uint8_t v___x_240_; 
v___x_238_ = l_Lean_Syntax_getArg(v___x_233_, v___x_212_);
lean_dec(v___x_233_);
v___x_239_ = ((lean_object*)(l_Lean_Elab_HeaderSyntax_imports___closed__7));
lean_inc(v___x_238_);
v___x_240_ = l_Lean_Syntax_isOfKind(v___x_238_, v___x_239_);
if (v___x_240_ == 0)
{
lean_object* v___x_241_; lean_object* v___x_242_; 
lean_dec(v___x_238_);
lean_dec(v_moduleTk_231_);
lean_dec(v_stx_198_);
v___x_241_ = lean_obj_once(&l_Lean_Elab_HeaderSyntax_imports___closed__2, &l_Lean_Elab_HeaderSyntax_imports___closed__2_once, _init_l_Lean_Elab_HeaderSyntax_imports___closed__2);
v___x_242_ = l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__0(v___x_241_);
return v___x_242_;
}
else
{
lean_object* v_preludeTk_243_; lean_object* v___x_244_; 
v_preludeTk_243_ = l_Lean_Syntax_getArg(v___x_238_, v___x_212_);
lean_dec(v___x_238_);
v___x_244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_244_, 0, v_preludeTk_243_);
v___y_218_ = v_moduleTk_231_;
v_preludeTk_219_ = v___x_244_;
goto v___jp_217_;
}
}
}
else
{
lean_object* v___x_245_; 
lean_dec(v___x_233_);
v___x_245_ = lean_box(0);
v___y_218_ = v_moduleTk_231_;
v_preludeTk_219_ = v___x_245_;
goto v___jp_217_;
}
}
}
v___jp_202_:
{
size_t v_sz_206_; size_t v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v_sz_206_ = lean_array_size(v___y_204_);
v___x_207_ = ((size_t)0ULL);
v___x_208_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2(v___y_203_, v___x_201_, v_sz_206_, v___x_207_, v___y_204_);
lean_dec(v___y_203_);
v___x_209_ = l_Array_append___redArg(v___y_205_, v___x_208_);
lean_dec_ref(v___x_208_);
return v___x_209_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_HeaderSyntax_imports___boxed(lean_object* v_stx_260_, lean_object* v_includeInit_261_){
_start:
{
uint8_t v_includeInit_boxed_262_; lean_object* v_res_263_; 
v_includeInit_boxed_262_ = lean_unbox(v_includeInit_261_);
v_res_263_ = l_Lean_Elab_HeaderSyntax_imports(v_stx_260_, v_includeInit_boxed_262_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_HeaderSyntax_toModuleHeader(lean_object* v_stx_264_){
_start:
{
uint8_t v___x_265_; lean_object* v___x_266_; uint8_t v___x_267_; lean_object* v___x_268_; 
v___x_265_ = 1;
lean_inc(v_stx_264_);
v___x_266_ = l_Lean_Elab_HeaderSyntax_imports(v_stx_264_, v___x_265_);
v___x_267_ = l_Lean_Elab_HeaderSyntax_isModule(v_stx_264_);
lean_dec(v_stx_264_);
v___x_268_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_268_, 0, v___x_266_);
lean_ctor_set_uint8(v___x_268_, sizeof(void*)*1, v___x_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_headerToImports(lean_object* v_stx_269_, uint8_t v_includeInit_270_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = l_Lean_Elab_HeaderSyntax_imports(v_stx_269_, v_includeInit_270_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_headerToImports___boxed(lean_object* v_stx_272_, lean_object* v_includeInit_273_){
_start:
{
uint8_t v_includeInit_boxed_274_; lean_object* v_res_275_; 
v_includeInit_boxed_274_ = lean_unbox(v_includeInit_273_);
v_res_275_ = l_Lean_Elab_headerToImports(v_stx_272_, v_includeInit_boxed_274_);
return v_res_275_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_checkDeprecatedImports_spec__0(lean_object* v_opts_276_, lean_object* v_opt_277_){
_start:
{
lean_object* v_name_278_; lean_object* v_defValue_279_; lean_object* v_map_280_; lean_object* v___x_281_; 
v_name_278_ = lean_ctor_get(v_opt_277_, 0);
v_defValue_279_ = lean_ctor_get(v_opt_277_, 1);
v_map_280_ = lean_ctor_get(v_opts_276_, 0);
v___x_281_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_280_, v_name_278_);
if (lean_obj_tag(v___x_281_) == 0)
{
uint8_t v___x_282_; 
v___x_282_ = lean_unbox(v_defValue_279_);
return v___x_282_;
}
else
{
lean_object* v_val_283_; 
v_val_283_ = lean_ctor_get(v___x_281_, 0);
lean_inc(v_val_283_);
lean_dec_ref_known(v___x_281_, 1);
if (lean_obj_tag(v_val_283_) == 1)
{
uint8_t v_v_284_; 
v_v_284_ = lean_ctor_get_uint8(v_val_283_, 0);
lean_dec_ref_known(v_val_283_, 0);
return v_v_284_;
}
else
{
uint8_t v___x_285_; 
lean_dec(v_val_283_);
v___x_285_ = lean_unbox(v_defValue_279_);
return v___x_285_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_checkDeprecatedImports_spec__0___boxed(lean_object* v_opts_286_, lean_object* v_opt_287_){
_start:
{
uint8_t v_res_288_; lean_object* v_r_289_; 
v_res_288_ = l_Lean_Option_get___at___00Lean_Elab_checkDeprecatedImports_spec__0(v_opts_286_, v_opt_287_);
lean_dec_ref(v_opt_287_);
lean_dec_ref(v_opts_286_);
v_r_289_ = lean_box(v_res_288_);
return v_r_289_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_spec__2___redArg(lean_object* v_s_290_, lean_object* v_a_291_, uint8_t v_b_292_){
_start:
{
uint8_t v___x_293_; 
v___x_293_ = 0;
switch(lean_obj_tag(v_a_291_))
{
case 0:
{
uint8_t v___x_294_; 
lean_dec_ref_known(v_a_291_, 1);
v___x_294_ = 1;
return v___x_294_;
}
case 1:
{
lean_object* v_pos_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_308_; 
v_pos_295_ = lean_ctor_get(v_a_291_, 0);
v_isSharedCheck_308_ = !lean_is_exclusive(v_a_291_);
if (v_isSharedCheck_308_ == 0)
{
v___x_297_ = v_a_291_;
v_isShared_298_ = v_isSharedCheck_308_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_pos_295_);
lean_dec(v_a_291_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_308_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v_str_299_; lean_object* v_startInclusive_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_305_; 
v_str_299_ = lean_ctor_get(v_s_290_, 0);
v_startInclusive_300_ = lean_ctor_get(v_s_290_, 1);
v___x_301_ = lean_nat_add(v_startInclusive_300_, v_pos_295_);
lean_dec(v_pos_295_);
v___x_302_ = lean_string_utf8_next_fast(v_str_299_, v___x_301_);
lean_dec(v___x_301_);
v___x_303_ = lean_nat_sub(v___x_302_, v_startInclusive_300_);
if (v_isShared_298_ == 0)
{
lean_ctor_set_tag(v___x_297_, 0);
lean_ctor_set(v___x_297_, 0, v___x_303_);
v___x_305_ = v___x_297_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v___x_303_);
v___x_305_ = v_reuseFailAlloc_307_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
v_a_291_ = v___x_305_;
v_b_292_ = v___x_293_;
goto _start;
}
}
}
case 2:
{
lean_object* v_needle_309_; lean_object* v_table_310_; lean_object* v_stackPos_311_; lean_object* v_needlePos_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_365_; 
v_needle_309_ = lean_ctor_get(v_a_291_, 0);
v_table_310_ = lean_ctor_get(v_a_291_, 1);
v_stackPos_311_ = lean_ctor_get(v_a_291_, 2);
v_needlePos_312_ = lean_ctor_get(v_a_291_, 3);
v_isSharedCheck_365_ = !lean_is_exclusive(v_a_291_);
if (v_isSharedCheck_365_ == 0)
{
v___x_314_ = v_a_291_;
v_isShared_315_ = v_isSharedCheck_365_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_needlePos_312_);
lean_inc(v_stackPos_311_);
lean_inc(v_table_310_);
lean_inc(v_needle_309_);
lean_dec(v_a_291_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_365_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v_str_316_; lean_object* v_startInclusive_317_; lean_object* v_endExclusive_318_; lean_object* v_str_319_; lean_object* v_startInclusive_320_; lean_object* v_endExclusive_321_; lean_object* v_basePos_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; uint8_t v___x_326_; 
v_str_316_ = lean_ctor_get(v_needle_309_, 0);
v_startInclusive_317_ = lean_ctor_get(v_needle_309_, 1);
v_endExclusive_318_ = lean_ctor_get(v_needle_309_, 2);
v_str_319_ = lean_ctor_get(v_s_290_, 0);
v_startInclusive_320_ = lean_ctor_get(v_s_290_, 1);
v_endExclusive_321_ = lean_ctor_get(v_s_290_, 2);
v_basePos_322_ = lean_nat_sub(v_stackPos_311_, v_needlePos_312_);
v___x_323_ = lean_nat_sub(v_endExclusive_318_, v_startInclusive_317_);
v___x_324_ = lean_nat_add(v_basePos_322_, v___x_323_);
v___x_325_ = lean_nat_sub(v_endExclusive_321_, v_startInclusive_320_);
v___x_326_ = lean_nat_dec_le(v___x_324_, v___x_325_);
lean_dec(v___x_324_);
if (v___x_326_ == 0)
{
uint8_t v___x_327_; 
lean_dec(v___x_323_);
lean_del_object(v___x_314_);
lean_dec(v_needlePos_312_);
lean_dec(v_stackPos_311_);
lean_dec_ref(v_table_310_);
lean_dec_ref(v_needle_309_);
v___x_327_ = lean_nat_dec_lt(v_basePos_322_, v___x_325_);
lean_dec(v___x_325_);
lean_dec(v_basePos_322_);
if (v___x_327_ == 0)
{
return v_b_292_;
}
else
{
lean_object* v___x_328_; 
v___x_328_ = lean_box(3);
v_a_291_ = v___x_328_;
v_b_292_ = v___x_293_;
goto _start;
}
}
else
{
lean_object* v___x_330_; uint8_t v_stackByte_331_; lean_object* v___x_332_; uint8_t v_patByte_333_; uint8_t v___x_334_; 
lean_dec(v___x_325_);
lean_dec(v_basePos_322_);
v___x_330_ = lean_nat_add(v_startInclusive_320_, v_stackPos_311_);
v_stackByte_331_ = lean_string_get_byte_fast(v_str_319_, v___x_330_);
v___x_332_ = lean_nat_add(v_startInclusive_317_, v_needlePos_312_);
v_patByte_333_ = lean_string_get_byte_fast(v_str_316_, v___x_332_);
v___x_334_ = lean_uint8_dec_eq(v_stackByte_331_, v_patByte_333_);
if (v___x_334_ == 0)
{
lean_object* v___x_335_; uint8_t v___x_336_; 
lean_dec(v___x_323_);
v___x_335_ = lean_unsigned_to_nat(0u);
v___x_336_ = lean_nat_dec_eq(v_needlePos_312_, v___x_335_);
if (v___x_336_ == 0)
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v_newNeedlePos_339_; uint8_t v___x_340_; 
v___x_337_ = lean_unsigned_to_nat(1u);
v___x_338_ = lean_nat_sub(v_needlePos_312_, v___x_337_);
lean_dec(v_needlePos_312_);
v_newNeedlePos_339_ = lean_array_fget_borrowed(v_table_310_, v___x_338_);
lean_dec(v___x_338_);
v___x_340_ = lean_nat_dec_eq(v_newNeedlePos_339_, v___x_335_);
if (v___x_340_ == 0)
{
lean_object* v___x_342_; 
lean_inc(v_newNeedlePos_339_);
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 3, v_newNeedlePos_339_);
v___x_342_ = v___x_314_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v_needle_309_);
lean_ctor_set(v_reuseFailAlloc_344_, 1, v_table_310_);
lean_ctor_set(v_reuseFailAlloc_344_, 2, v_stackPos_311_);
lean_ctor_set(v_reuseFailAlloc_344_, 3, v_newNeedlePos_339_);
v___x_342_ = v_reuseFailAlloc_344_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
v_a_291_ = v___x_342_;
v_b_292_ = v___x_293_;
goto _start;
}
}
else
{
lean_object* v_nextStackPos_345_; lean_object* v___x_347_; 
v_nextStackPos_345_ = l_String_Slice_posGE___redArg(v_s_290_, v_stackPos_311_);
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 3, v___x_335_);
lean_ctor_set(v___x_314_, 2, v_nextStackPos_345_);
v___x_347_ = v___x_314_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v_needle_309_);
lean_ctor_set(v_reuseFailAlloc_349_, 1, v_table_310_);
lean_ctor_set(v_reuseFailAlloc_349_, 2, v_nextStackPos_345_);
lean_ctor_set(v_reuseFailAlloc_349_, 3, v___x_335_);
v___x_347_ = v_reuseFailAlloc_349_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
v_a_291_ = v___x_347_;
v_b_292_ = v___x_293_;
goto _start;
}
}
}
else
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v_nextStackPos_352_; lean_object* v___x_354_; 
lean_dec(v_needlePos_312_);
v___x_350_ = lean_unsigned_to_nat(1u);
v___x_351_ = lean_nat_add(v_stackPos_311_, v___x_350_);
lean_dec(v_stackPos_311_);
v_nextStackPos_352_ = l_String_Slice_posGE___redArg(v_s_290_, v___x_351_);
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 3, v___x_335_);
lean_ctor_set(v___x_314_, 2, v_nextStackPos_352_);
v___x_354_ = v___x_314_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_needle_309_);
lean_ctor_set(v_reuseFailAlloc_356_, 1, v_table_310_);
lean_ctor_set(v_reuseFailAlloc_356_, 2, v_nextStackPos_352_);
lean_ctor_set(v_reuseFailAlloc_356_, 3, v___x_335_);
v___x_354_ = v_reuseFailAlloc_356_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
v_a_291_ = v___x_354_;
v_b_292_ = v___x_293_;
goto _start;
}
}
}
else
{
lean_object* v___x_357_; lean_object* v_nextNeedlePos_358_; uint8_t v___x_359_; 
v___x_357_ = lean_unsigned_to_nat(1u);
v_nextNeedlePos_358_ = lean_nat_add(v_needlePos_312_, v___x_357_);
lean_dec(v_needlePos_312_);
v___x_359_ = lean_nat_dec_eq(v_nextNeedlePos_358_, v___x_323_);
lean_dec(v___x_323_);
if (v___x_359_ == 0)
{
lean_object* v_nextStackPos_360_; lean_object* v___x_362_; 
v_nextStackPos_360_ = lean_nat_add(v_stackPos_311_, v___x_357_);
lean_dec(v_stackPos_311_);
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 3, v_nextNeedlePos_358_);
lean_ctor_set(v___x_314_, 2, v_nextStackPos_360_);
v___x_362_ = v___x_314_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v_needle_309_);
lean_ctor_set(v_reuseFailAlloc_364_, 1, v_table_310_);
lean_ctor_set(v_reuseFailAlloc_364_, 2, v_nextStackPos_360_);
lean_ctor_set(v_reuseFailAlloc_364_, 3, v_nextNeedlePos_358_);
v___x_362_ = v_reuseFailAlloc_364_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
v_a_291_ = v___x_362_;
goto _start;
}
}
else
{
lean_dec(v_nextNeedlePos_358_);
lean_del_object(v___x_314_);
lean_dec(v_stackPos_311_);
lean_dec_ref(v_table_310_);
lean_dec_ref(v_needle_309_);
return v___x_359_;
}
}
}
}
}
default: 
{
return v_b_292_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_spec__2___redArg___boxed(lean_object* v_s_366_, lean_object* v_a_367_, lean_object* v_b_368_){
_start:
{
uint8_t v_b_boxed_369_; uint8_t v_res_370_; lean_object* v_r_371_; 
v_b_boxed_369_ = lean_unbox(v_b_368_);
v_res_370_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_spec__2___redArg(v_s_366_, v_a_367_, v_b_boxed_369_);
lean_dec_ref(v_s_366_);
v_r_371_ = lean_box(v_res_370_);
return v_r_371_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__1(void){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = ((lean_object*)(l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__0));
v___x_374_ = lean_string_utf8_byte_size(v___x_373_);
return v___x_374_;
}
}
static uint8_t _init_l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__2(void){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; uint8_t v___x_377_; 
v___x_375_ = lean_unsigned_to_nat(0u);
v___x_376_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__1, &l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__1_once, _init_l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__1);
v___x_377_ = lean_nat_dec_eq(v___x_376_, v___x_375_);
return v___x_377_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__3(void){
_start:
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_378_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__1, &l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__1_once, _init_l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__1);
v___x_379_ = lean_unsigned_to_nat(0u);
v___x_380_ = ((lean_object*)(l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__0));
v___x_381_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
lean_ctor_set(v___x_381_, 1, v___x_379_);
lean_ctor_set(v___x_381_, 2, v___x_378_);
return v___x_381_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__4(void){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_382_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__3, &l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__3_once, _init_l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__3);
v___x_383_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_382_);
return v___x_383_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__5(void){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_384_ = lean_unsigned_to_nat(0u);
v___x_385_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__4, &l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__4_once, _init_l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__4);
v___x_386_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__3, &l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__3_once, _init_l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__3);
v___x_387_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_387_, 0, v___x_386_);
lean_ctor_set(v___x_387_, 1, v___x_385_);
lean_ctor_set(v___x_387_, 2, v___x_384_);
lean_ctor_set(v___x_387_, 3, v___x_384_);
return v___x_387_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2(lean_object* v_s_390_){
_start:
{
lean_object* v___y_392_; uint8_t v___x_395_; 
v___x_395_ = lean_uint8_once(&l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__2, &l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__2_once, _init_l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__2);
if (v___x_395_ == 0)
{
lean_object* v___x_396_; 
v___x_396_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__5, &l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__5_once, _init_l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__5);
v___y_392_ = v___x_396_;
goto v___jp_391_;
}
else
{
lean_object* v___x_397_; 
v___x_397_ = ((lean_object*)(l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__6));
v___y_392_ = v___x_397_;
goto v___jp_391_;
}
v___jp_391_:
{
uint8_t v___x_393_; uint8_t v___x_394_; 
v___x_393_ = 0;
lean_inc(v___y_392_);
v___x_394_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_spec__2___redArg(v_s_390_, v___y_392_, v___x_393_);
return v___x_394_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___boxed(lean_object* v_s_398_){
_start:
{
uint8_t v_res_399_; lean_object* v_r_400_; 
v_res_399_ = l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2(v_s_398_);
lean_dec_ref(v_s_398_);
v_r_400_ = lean_box(v_res_399_);
return v_r_400_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkDeprecatedImports_spec__3(lean_object* v_as_401_, size_t v_sz_402_, size_t v_i_403_, lean_object* v_b_404_){
_start:
{
lean_object* v_a_406_; uint8_t v___x_410_; 
v___x_410_ = lean_usize_dec_lt(v_i_403_, v_sz_402_);
if (v___x_410_ == 0)
{
return v_b_404_;
}
else
{
lean_object* v_fst_411_; lean_object* v_snd_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_487_; 
v_fst_411_ = lean_ctor_get(v_b_404_, 0);
v_snd_412_ = lean_ctor_get(v_b_404_, 1);
v_isSharedCheck_487_ = !lean_is_exclusive(v_b_404_);
if (v_isSharedCheck_487_ == 0)
{
v___x_414_ = v_b_404_;
v_isShared_415_ = v_isSharedCheck_487_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_snd_412_);
lean_inc(v_fst_411_);
lean_dec(v_b_404_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_487_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_416_; lean_object* v_a_417_; lean_object* v___y_419_; lean_object* v_ignoreDeprecatedImports_420_; uint8_t v___x_432_; 
v___x_416_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__4));
v_a_417_ = lean_array_uget_borrowed(v_as_401_, v_i_403_);
lean_inc(v_a_417_);
v___x_432_ = l_Lean_Syntax_isOfKind(v_a_417_, v___x_416_);
if (v___x_432_ == 0)
{
lean_object* v___x_433_; 
lean_del_object(v___x_414_);
v___x_433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_433_, 0, v_fst_411_);
lean_ctor_set(v___x_433_, 1, v_snd_412_);
v_a_406_ = v___x_433_;
goto v___jp_405_;
}
else
{
lean_object* v___x_434_; lean_object* v___x_459_; lean_object* v___x_479_; uint8_t v___x_480_; 
v___x_434_ = lean_unsigned_to_nat(0u);
v___x_459_ = lean_unsigned_to_nat(1u);
v___x_479_ = l_Lean_Syntax_getArg(v_a_417_, v___x_434_);
v___x_480_ = l_Lean_Syntax_isNone(v___x_479_);
if (v___x_480_ == 0)
{
uint8_t v___x_481_; 
lean_inc(v___x_479_);
v___x_481_ = l_Lean_Syntax_matchesNull(v___x_479_, v___x_459_);
if (v___x_481_ == 0)
{
lean_object* v___x_482_; 
lean_dec(v___x_479_);
lean_del_object(v___x_414_);
v___x_482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_482_, 0, v_fst_411_);
lean_ctor_set(v___x_482_, 1, v_snd_412_);
v_a_406_ = v___x_482_;
goto v___jp_405_;
}
else
{
lean_object* v___x_483_; lean_object* v___x_484_; uint8_t v___x_485_; 
v___x_483_ = l_Lean_Syntax_getArg(v___x_479_, v___x_434_);
lean_dec(v___x_479_);
v___x_484_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__14));
v___x_485_ = l_Lean_Syntax_isOfKind(v___x_483_, v___x_484_);
if (v___x_485_ == 0)
{
lean_object* v___x_486_; 
lean_del_object(v___x_414_);
v___x_486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_486_, 0, v_fst_411_);
lean_ctor_set(v___x_486_, 1, v_snd_412_);
v_a_406_ = v___x_486_;
goto v___jp_405_;
}
else
{
goto v___jp_470_;
}
}
}
else
{
lean_dec(v___x_479_);
goto v___jp_470_;
}
v___jp_435_:
{
lean_object* v___x_436_; lean_object* v___x_437_; uint8_t v___x_438_; 
v___x_436_ = lean_unsigned_to_nat(5u);
v___x_437_ = l_Lean_Syntax_getArg(v_a_417_, v___x_436_);
v___x_438_ = l_Lean_Syntax_matchesNull(v___x_437_, v___x_434_);
if (v___x_438_ == 0)
{
lean_object* v___x_439_; 
lean_del_object(v___x_414_);
v___x_439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_439_, 0, v_fst_411_);
lean_ctor_set(v___x_439_, 1, v_snd_412_);
v_a_406_ = v___x_439_;
goto v___jp_405_;
}
else
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_440_ = lean_unsigned_to_nat(4u);
v___x_441_ = l_Lean_Syntax_getArg(v_a_417_, v___x_440_);
v___x_442_ = l_Lean_Syntax_getTrailing_x3f(v_a_417_);
if (lean_obj_tag(v___x_442_) == 0)
{
v___y_419_ = v___x_441_;
v_ignoreDeprecatedImports_420_ = v_fst_411_;
goto v___jp_418_;
}
else
{
lean_object* v_val_443_; lean_object* v_str_444_; lean_object* v_startPos_445_; lean_object* v_stopPos_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_458_; 
v_val_443_ = lean_ctor_get(v___x_442_, 0);
lean_inc(v_val_443_);
lean_dec_ref_known(v___x_442_, 1);
v_str_444_ = lean_ctor_get(v_val_443_, 0);
v_startPos_445_ = lean_ctor_get(v_val_443_, 1);
v_stopPos_446_ = lean_ctor_get(v_val_443_, 2);
v_isSharedCheck_458_ = !lean_is_exclusive(v_val_443_);
if (v_isSharedCheck_458_ == 0)
{
v___x_448_ = v_val_443_;
v_isShared_449_ = v_isSharedCheck_458_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_stopPos_446_);
lean_inc(v_startPos_445_);
lean_inc(v_str_444_);
lean_dec(v_val_443_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_458_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_453_; 
v___x_450_ = lean_string_utf8_extract(v_str_444_, v_startPos_445_, v_stopPos_446_);
lean_dec(v_stopPos_446_);
lean_dec(v_startPos_445_);
lean_dec_ref(v_str_444_);
v___x_451_ = lean_string_utf8_byte_size(v___x_450_);
if (v_isShared_449_ == 0)
{
lean_ctor_set(v___x_448_, 2, v___x_451_);
lean_ctor_set(v___x_448_, 1, v___x_434_);
lean_ctor_set(v___x_448_, 0, v___x_450_);
v___x_453_ = v___x_448_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v___x_450_);
lean_ctor_set(v_reuseFailAlloc_457_, 1, v___x_434_);
lean_ctor_set(v_reuseFailAlloc_457_, 2, v___x_451_);
v___x_453_ = v_reuseFailAlloc_457_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
uint8_t v___x_454_; 
v___x_454_ = l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2(v___x_453_);
lean_dec_ref(v___x_453_);
if (v___x_454_ == 0)
{
v___y_419_ = v___x_441_;
v_ignoreDeprecatedImports_420_ = v_fst_411_;
goto v___jp_418_;
}
else
{
lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_455_ = l_Lean_TSyntax_getId(v___x_441_);
v___x_456_ = l_Lean_NameSet_insert(v_fst_411_, v___x_455_);
v___y_419_ = v___x_441_;
v_ignoreDeprecatedImports_420_ = v___x_456_;
goto v___jp_418_;
}
}
}
}
}
}
v___jp_460_:
{
lean_object* v___x_461_; lean_object* v___x_462_; uint8_t v___x_463_; 
v___x_461_ = lean_unsigned_to_nat(3u);
v___x_462_ = l_Lean_Syntax_getArg(v_a_417_, v___x_461_);
v___x_463_ = l_Lean_Syntax_isNone(v___x_462_);
if (v___x_463_ == 0)
{
uint8_t v___x_464_; 
lean_inc(v___x_462_);
v___x_464_ = l_Lean_Syntax_matchesNull(v___x_462_, v___x_459_);
if (v___x_464_ == 0)
{
lean_object* v___x_465_; 
lean_dec(v___x_462_);
lean_del_object(v___x_414_);
v___x_465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_465_, 0, v_fst_411_);
lean_ctor_set(v___x_465_, 1, v_snd_412_);
v_a_406_ = v___x_465_;
goto v___jp_405_;
}
else
{
lean_object* v___x_466_; lean_object* v___x_467_; uint8_t v___x_468_; 
v___x_466_ = l_Lean_Syntax_getArg(v___x_462_, v___x_434_);
lean_dec(v___x_462_);
v___x_467_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__10));
v___x_468_ = l_Lean_Syntax_isOfKind(v___x_466_, v___x_467_);
if (v___x_468_ == 0)
{
lean_object* v___x_469_; 
lean_del_object(v___x_414_);
v___x_469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_469_, 0, v_fst_411_);
lean_ctor_set(v___x_469_, 1, v_snd_412_);
v_a_406_ = v___x_469_;
goto v___jp_405_;
}
else
{
goto v___jp_435_;
}
}
}
else
{
lean_dec(v___x_462_);
goto v___jp_435_;
}
}
v___jp_470_:
{
lean_object* v___x_471_; uint8_t v___x_472_; 
v___x_471_ = l_Lean_Syntax_getArg(v_a_417_, v___x_459_);
v___x_472_ = l_Lean_Syntax_isNone(v___x_471_);
if (v___x_472_ == 0)
{
uint8_t v___x_473_; 
lean_inc(v___x_471_);
v___x_473_ = l_Lean_Syntax_matchesNull(v___x_471_, v___x_459_);
if (v___x_473_ == 0)
{
lean_object* v___x_474_; 
lean_dec(v___x_471_);
lean_del_object(v___x_414_);
v___x_474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_474_, 0, v_fst_411_);
lean_ctor_set(v___x_474_, 1, v_snd_412_);
v_a_406_ = v___x_474_;
goto v___jp_405_;
}
else
{
lean_object* v___x_475_; lean_object* v___x_476_; uint8_t v___x_477_; 
v___x_475_ = l_Lean_Syntax_getArg(v___x_471_, v___x_434_);
lean_dec(v___x_471_);
v___x_476_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__12));
v___x_477_ = l_Lean_Syntax_isOfKind(v___x_475_, v___x_476_);
if (v___x_477_ == 0)
{
lean_object* v___x_478_; 
lean_del_object(v___x_414_);
v___x_478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_478_, 0, v_fst_411_);
lean_ctor_set(v___x_478_, 1, v_snd_412_);
v_a_406_ = v___x_478_;
goto v___jp_405_;
}
else
{
goto v___jp_460_;
}
}
}
else
{
lean_dec(v___x_471_);
goto v___jp_460_;
}
}
}
v___jp_418_:
{
uint8_t v___x_421_; lean_object* v___x_422_; 
v___x_421_ = 0;
v___x_422_ = l_Lean_Syntax_getPos_x3f(v_a_417_, v___x_421_);
if (lean_obj_tag(v___x_422_) == 1)
{
lean_object* v_val_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_427_; 
v_val_423_ = lean_ctor_get(v___x_422_, 0);
lean_inc(v_val_423_);
lean_dec_ref_known(v___x_422_, 1);
v___x_424_ = l_Lean_TSyntax_getId(v___y_419_);
lean_dec(v___y_419_);
v___x_425_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_424_, v_val_423_, v_snd_412_);
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 1, v___x_425_);
lean_ctor_set(v___x_414_, 0, v_ignoreDeprecatedImports_420_);
v___x_427_ = v___x_414_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_ignoreDeprecatedImports_420_);
lean_ctor_set(v_reuseFailAlloc_428_, 1, v___x_425_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
v_a_406_ = v___x_427_;
goto v___jp_405_;
}
}
else
{
lean_object* v___x_430_; 
lean_dec(v___x_422_);
lean_dec(v___y_419_);
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 0, v_ignoreDeprecatedImports_420_);
v___x_430_ = v___x_414_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_ignoreDeprecatedImports_420_);
lean_ctor_set(v_reuseFailAlloc_431_, 1, v_snd_412_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
v_a_406_ = v___x_430_;
goto v___jp_405_;
}
}
}
}
}
v___jp_405_:
{
size_t v___x_407_; size_t v___x_408_; 
v___x_407_ = ((size_t)1ULL);
v___x_408_ = lean_usize_add(v_i_403_, v___x_407_);
v_i_403_ = v___x_408_;
v_b_404_ = v_a_406_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkDeprecatedImports_spec__3___boxed(lean_object* v_as_488_, lean_object* v_sz_489_, lean_object* v_i_490_, lean_object* v_b_491_){
_start:
{
size_t v_sz_boxed_492_; size_t v_i_boxed_493_; lean_object* v_res_494_; 
v_sz_boxed_492_ = lean_unbox_usize(v_sz_489_);
lean_dec(v_sz_489_);
v_i_boxed_493_ = lean_unbox_usize(v_i_490_);
lean_dec(v_i_490_);
v_res_494_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkDeprecatedImports_spec__3(v_as_488_, v_sz_boxed_492_, v_i_boxed_493_, v_b_491_);
lean_dec_ref(v_as_488_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4_spec__5(lean_object* v_o_498_, lean_object* v_k_499_, uint8_t v_v_500_){
_start:
{
lean_object* v_map_501_; uint8_t v_hasTrace_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_516_; 
v_map_501_ = lean_ctor_get(v_o_498_, 0);
v_hasTrace_502_ = lean_ctor_get_uint8(v_o_498_, sizeof(void*)*1);
v_isSharedCheck_516_ = !lean_is_exclusive(v_o_498_);
if (v_isSharedCheck_516_ == 0)
{
v___x_504_ = v_o_498_;
v_isShared_505_ = v_isSharedCheck_516_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_map_501_);
lean_dec(v_o_498_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_516_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_506_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_506_, 0, v_v_500_);
lean_inc(v_k_499_);
v___x_507_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_499_, v___x_506_, v_map_501_);
if (v_hasTrace_502_ == 0)
{
lean_object* v___x_508_; uint8_t v___x_509_; lean_object* v___x_511_; 
v___x_508_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4_spec__5___closed__1));
v___x_509_ = l_Lean_Name_isPrefixOf(v___x_508_, v_k_499_);
lean_dec(v_k_499_);
if (v_isShared_505_ == 0)
{
lean_ctor_set(v___x_504_, 0, v___x_507_);
v___x_511_ = v___x_504_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v___x_507_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
lean_ctor_set_uint8(v___x_511_, sizeof(void*)*1, v___x_509_);
return v___x_511_;
}
}
else
{
lean_object* v___x_514_; 
lean_dec(v_k_499_);
if (v_isShared_505_ == 0)
{
lean_ctor_set(v___x_504_, 0, v___x_507_);
v___x_514_ = v___x_504_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v___x_507_);
lean_ctor_set_uint8(v_reuseFailAlloc_515_, sizeof(void*)*1, v_hasTrace_502_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4_spec__5___boxed(lean_object* v_o_517_, lean_object* v_k_518_, lean_object* v_v_519_){
_start:
{
uint8_t v_v_boxed_520_; lean_object* v_res_521_; 
v_v_boxed_520_ = lean_unbox(v_v_519_);
v_res_521_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4_spec__5(v_o_517_, v_k_518_, v_v_boxed_520_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4(lean_object* v_opts_522_, lean_object* v_opt_523_, uint8_t v_val_524_){
_start:
{
lean_object* v_name_525_; lean_object* v___x_526_; 
v_name_525_ = lean_ctor_get(v_opt_523_, 0);
lean_inc(v_name_525_);
lean_dec_ref(v_opt_523_);
v___x_526_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4_spec__5(v_opts_522_, v_name_525_, v_val_524_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4___boxed(lean_object* v_opts_527_, lean_object* v_opt_528_, lean_object* v_val_529_){
_start:
{
uint8_t v_val_boxed_530_; lean_object* v_res_531_; 
v_val_boxed_530_ = lean_unbox(v_val_529_);
v_res_531_ = l_Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4(v_opts_527_, v_opt_528_, v_val_boxed_530_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1(lean_object* v_ignoreDeprecatedImports_537_, lean_object* v_env_538_, lean_object* v_inputCtx_539_, lean_object* v_importPositions_540_, lean_object* v_startPos_541_, lean_object* v_as_542_, size_t v_i_543_, size_t v_stop_544_, lean_object* v_b_545_){
_start:
{
lean_object* v___y_547_; uint8_t v___x_551_; 
v___x_551_ = lean_usize_dec_eq(v_i_543_, v_stop_544_);
if (v___x_551_ == 0)
{
lean_object* v___x_552_; lean_object* v_module_553_; uint8_t v___x_554_; 
v___x_552_ = lean_array_uget_borrowed(v_as_542_, v_i_543_);
v_module_553_ = lean_ctor_get(v___x_552_, 0);
v___x_554_ = l_Lean_NameSet_contains(v_ignoreDeprecatedImports_537_, v_module_553_);
if (v___x_554_ == 0)
{
lean_object* v___x_555_; 
v___x_555_ = l_Lean_Environment_getModuleIdx_x3f(v_env_538_, v_module_553_);
if (lean_obj_tag(v___x_555_) == 0)
{
v___y_547_ = v_b_545_;
goto v___jp_546_;
}
else
{
lean_object* v_val_556_; lean_object* v___x_557_; 
v_val_556_ = lean_ctor_get(v___x_555_, 0);
lean_inc(v_val_556_);
lean_dec_ref_known(v___x_555_, 1);
v___x_557_ = l_Lean_Environment_getDeprecatedModuleByIdx_x3f(v_env_538_, v_val_556_);
if (lean_obj_tag(v___x_557_) == 0)
{
lean_dec(v_val_556_);
v___y_547_ = v_b_545_;
goto v___jp_546_;
}
else
{
lean_object* v_val_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_581_; 
v_val_558_ = lean_ctor_get(v___x_557_, 0);
v_isSharedCheck_581_ = !lean_is_exclusive(v___x_557_);
if (v_isSharedCheck_581_ == 0)
{
v___x_560_ = v___x_557_;
v_isShared_561_ = v_isSharedCheck_581_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_val_558_);
lean_dec(v___x_557_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_581_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v___y_563_; lean_object* v___x_579_; 
v___x_579_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_importPositions_540_, v_module_553_);
if (lean_obj_tag(v___x_579_) == 0)
{
lean_inc(v_startPos_541_);
v___y_563_ = v_startPos_541_;
goto v___jp_562_;
}
else
{
lean_object* v_val_580_; 
v_val_580_ = lean_ctor_get(v___x_579_, 0);
lean_inc(v_val_580_);
lean_dec_ref_known(v___x_579_, 1);
v___y_563_ = v_val_580_;
goto v___jp_562_;
}
v___jp_562_:
{
lean_object* v_fileName_564_; lean_object* v_fileMap_565_; lean_object* v___x_566_; lean_object* v___x_567_; uint8_t v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_573_; 
v_fileName_564_ = lean_ctor_get(v_inputCtx_539_, 1);
v_fileMap_565_ = lean_ctor_get(v_inputCtx_539_, 2);
lean_inc_ref(v_fileMap_565_);
v___x_566_ = l_Lean_FileMap_toPosition(v_fileMap_565_, v___y_563_);
lean_dec(v___y_563_);
v___x_567_ = lean_box(0);
v___x_568_ = 1;
v___x_569_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___closed__0));
v___x_570_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___closed__2));
lean_inc(v_module_553_);
v___x_571_ = l_Lean_formatDeprecatedModuleWarning(v_env_538_, v_val_556_, v_module_553_, v_val_558_);
lean_dec(v_val_556_);
if (v_isShared_561_ == 0)
{
lean_ctor_set_tag(v___x_560_, 3);
lean_ctor_set(v___x_560_, 0, v___x_571_);
v___x_573_ = v___x_560_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v___x_571_);
v___x_573_ = v_reuseFailAlloc_578_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_574_ = l_Lean_MessageData_ofFormat(v___x_573_);
v___x_575_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_575_, 0, v___x_570_);
lean_ctor_set(v___x_575_, 1, v___x_574_);
lean_inc_ref(v_fileName_564_);
v___x_576_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_576_, 0, v_fileName_564_);
lean_ctor_set(v___x_576_, 1, v___x_566_);
lean_ctor_set(v___x_576_, 2, v___x_567_);
lean_ctor_set(v___x_576_, 3, v___x_569_);
lean_ctor_set(v___x_576_, 4, v___x_575_);
lean_ctor_set_uint8(v___x_576_, sizeof(void*)*5, v___x_554_);
lean_ctor_set_uint8(v___x_576_, sizeof(void*)*5 + 1, v___x_568_);
lean_ctor_set_uint8(v___x_576_, sizeof(void*)*5 + 2, v___x_554_);
v___x_577_ = l_Lean_MessageLog_add(v___x_576_, v_b_545_);
v___y_547_ = v___x_577_;
goto v___jp_546_;
}
}
}
}
}
}
else
{
v___y_547_ = v_b_545_;
goto v___jp_546_;
}
}
else
{
lean_dec(v_startPos_541_);
lean_dec_ref(v_inputCtx_539_);
return v_b_545_;
}
v___jp_546_:
{
size_t v___x_548_; size_t v___x_549_; 
v___x_548_ = ((size_t)1ULL);
v___x_549_ = lean_usize_add(v_i_543_, v___x_548_);
v_i_543_ = v___x_549_;
v_b_545_ = v___y_547_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___boxed(lean_object* v_ignoreDeprecatedImports_582_, lean_object* v_env_583_, lean_object* v_inputCtx_584_, lean_object* v_importPositions_585_, lean_object* v_startPos_586_, lean_object* v_as_587_, lean_object* v_i_588_, lean_object* v_stop_589_, lean_object* v_b_590_){
_start:
{
size_t v_i_boxed_591_; size_t v_stop_boxed_592_; lean_object* v_res_593_; 
v_i_boxed_591_ = lean_unbox_usize(v_i_588_);
lean_dec(v_i_588_);
v_stop_boxed_592_ = lean_unbox_usize(v_stop_589_);
lean_dec(v_stop_589_);
v_res_593_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1(v_ignoreDeprecatedImports_582_, v_env_583_, v_inputCtx_584_, v_importPositions_585_, v_startPos_586_, v_as_587_, v_i_boxed_591_, v_stop_boxed_592_, v_b_590_);
lean_dec_ref(v_as_587_);
lean_dec(v_importPositions_585_);
lean_dec_ref(v_env_583_);
lean_dec(v_ignoreDeprecatedImports_582_);
return v_res_593_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedImports___closed__0(void){
_start:
{
lean_object* v_importPositions_594_; lean_object* v_ignoreDeprecatedImports_595_; lean_object* v___x_596_; 
v_importPositions_594_ = lean_box(1);
v_ignoreDeprecatedImports_595_ = l_Lean_NameSet_empty;
v___x_596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_596_, 0, v_ignoreDeprecatedImports_595_);
lean_ctor_set(v___x_596_, 1, v_importPositions_594_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedImports(lean_object* v_env_597_, lean_object* v_imports_598_, lean_object* v_opts_599_, lean_object* v_inputCtx_600_, lean_object* v_startPos_601_, lean_object* v_messages_602_, lean_object* v_headerStx_x3f_603_, lean_object* v_origHeaderStx_x3f_604_){
_start:
{
lean_object* v_opts_606_; lean_object* v_ignoreDeprecatedImports_607_; lean_object* v_importPositions_608_; lean_object* v_ignoreDeprecatedImports_621_; lean_object* v_importPositions_622_; lean_object* v___y_624_; lean_object* v_opts_625_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_659_; lean_object* v___y_660_; lean_object* v___y_661_; lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v_moduleTk_664_; lean_object* v_val_674_; 
v_ignoreDeprecatedImports_621_ = l_Lean_NameSet_empty;
v_importPositions_622_ = lean_box(1);
if (lean_obj_tag(v_origHeaderStx_x3f_604_) == 0)
{
if (lean_obj_tag(v_headerStx_x3f_603_) == 1)
{
lean_object* v_val_691_; 
v_val_691_ = lean_ctor_get(v_headerStx_x3f_603_, 0);
lean_inc(v_val_691_);
lean_dec_ref_known(v_headerStx_x3f_603_, 1);
v_val_674_ = v_val_691_;
goto v___jp_673_;
}
else
{
lean_dec(v_headerStx_x3f_603_);
v_opts_606_ = v_opts_599_;
v_ignoreDeprecatedImports_607_ = v_ignoreDeprecatedImports_621_;
v_importPositions_608_ = v_importPositions_622_;
goto v___jp_605_;
}
}
else
{
lean_object* v_val_692_; 
lean_dec(v_headerStx_x3f_603_);
v_val_692_ = lean_ctor_get(v_origHeaderStx_x3f_604_, 0);
lean_inc(v_val_692_);
lean_dec_ref_known(v_origHeaderStx_x3f_604_, 1);
v_val_674_ = v_val_692_;
goto v___jp_673_;
}
v___jp_605_:
{
lean_object* v___x_609_; uint8_t v___x_610_; 
v___x_609_ = l_Lean_linter_deprecated_module;
v___x_610_ = l_Lean_Option_get___at___00Lean_Elab_checkDeprecatedImports_spec__0(v_opts_606_, v___x_609_);
lean_dec_ref(v_opts_606_);
if (v___x_610_ == 0)
{
lean_dec(v_importPositions_608_);
lean_dec(v_ignoreDeprecatedImports_607_);
lean_dec(v_startPos_601_);
lean_dec_ref(v_inputCtx_600_);
return v_messages_602_;
}
else
{
lean_object* v___x_611_; lean_object* v___x_612_; uint8_t v___x_613_; 
v___x_611_ = lean_unsigned_to_nat(0u);
v___x_612_ = lean_array_get_size(v_imports_598_);
v___x_613_ = lean_nat_dec_lt(v___x_611_, v___x_612_);
if (v___x_613_ == 0)
{
lean_dec(v_importPositions_608_);
lean_dec(v_ignoreDeprecatedImports_607_);
lean_dec(v_startPos_601_);
lean_dec_ref(v_inputCtx_600_);
return v_messages_602_;
}
else
{
uint8_t v___x_614_; 
v___x_614_ = lean_nat_dec_le(v___x_612_, v___x_612_);
if (v___x_614_ == 0)
{
if (v___x_613_ == 0)
{
lean_dec(v_importPositions_608_);
lean_dec(v_ignoreDeprecatedImports_607_);
lean_dec(v_startPos_601_);
lean_dec_ref(v_inputCtx_600_);
return v_messages_602_;
}
else
{
size_t v___x_615_; size_t v___x_616_; lean_object* v___x_617_; 
v___x_615_ = ((size_t)0ULL);
v___x_616_ = lean_usize_of_nat(v___x_612_);
v___x_617_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1(v_ignoreDeprecatedImports_607_, v_env_597_, v_inputCtx_600_, v_importPositions_608_, v_startPos_601_, v_imports_598_, v___x_615_, v___x_616_, v_messages_602_);
lean_dec(v_importPositions_608_);
lean_dec(v_ignoreDeprecatedImports_607_);
return v___x_617_;
}
}
else
{
size_t v___x_618_; size_t v___x_619_; lean_object* v___x_620_; 
v___x_618_ = ((size_t)0ULL);
v___x_619_ = lean_usize_of_nat(v___x_612_);
v___x_620_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1(v_ignoreDeprecatedImports_607_, v_env_597_, v_inputCtx_600_, v_importPositions_608_, v_startPos_601_, v_imports_598_, v___x_618_, v___x_619_, v_messages_602_);
lean_dec(v_importPositions_608_);
lean_dec(v_ignoreDeprecatedImports_607_);
return v___x_620_;
}
}
}
}
v___jp_623_:
{
lean_object* v___x_626_; size_t v_sz_627_; size_t v___x_628_; lean_object* v___x_629_; lean_object* v_fst_630_; lean_object* v_snd_631_; 
v___x_626_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedImports___closed__0, &l_Lean_Elab_checkDeprecatedImports___closed__0_once, _init_l_Lean_Elab_checkDeprecatedImports___closed__0);
v_sz_627_ = lean_array_size(v___y_624_);
v___x_628_ = ((size_t)0ULL);
v___x_629_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkDeprecatedImports_spec__3(v___y_624_, v_sz_627_, v___x_628_, v___x_626_);
lean_dec_ref(v___y_624_);
v_fst_630_ = lean_ctor_get(v___x_629_, 0);
lean_inc(v_fst_630_);
v_snd_631_ = lean_ctor_get(v___x_629_, 1);
lean_inc(v_snd_631_);
lean_dec_ref(v___x_629_);
v_opts_606_ = v_opts_625_;
v_ignoreDeprecatedImports_607_ = v_fst_630_;
v_importPositions_608_ = v_snd_631_;
goto v___jp_605_;
}
v___jp_632_:
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v_importsStx_638_; 
v___x_636_ = lean_unsigned_to_nat(2u);
v___x_637_ = l_Lean_Syntax_getArg(v___y_633_, v___x_636_);
lean_dec(v___y_633_);
v_importsStx_638_ = l_Lean_Syntax_getArgs(v___x_637_);
lean_dec(v___x_637_);
if (lean_obj_tag(v___y_635_) == 0)
{
lean_dec(v___y_634_);
v___y_624_ = v_importsStx_638_;
v_opts_625_ = v_opts_599_;
goto v___jp_623_;
}
else
{
lean_object* v_val_639_; lean_object* v___x_640_; 
v_val_639_ = lean_ctor_get(v___y_635_, 0);
lean_inc(v_val_639_);
lean_dec_ref_known(v___y_635_, 1);
v___x_640_ = l_Lean_Syntax_getTrailing_x3f(v_val_639_);
lean_dec(v_val_639_);
if (lean_obj_tag(v___x_640_) == 0)
{
lean_dec(v___y_634_);
v___y_624_ = v_importsStx_638_;
v_opts_625_ = v_opts_599_;
goto v___jp_623_;
}
else
{
lean_object* v_val_641_; lean_object* v_str_642_; lean_object* v_startPos_643_; lean_object* v_stopPos_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_657_; 
v_val_641_ = lean_ctor_get(v___x_640_, 0);
lean_inc(v_val_641_);
lean_dec_ref_known(v___x_640_, 1);
v_str_642_ = lean_ctor_get(v_val_641_, 0);
v_startPos_643_ = lean_ctor_get(v_val_641_, 1);
v_stopPos_644_ = lean_ctor_get(v_val_641_, 2);
v_isSharedCheck_657_ = !lean_is_exclusive(v_val_641_);
if (v_isSharedCheck_657_ == 0)
{
v___x_646_ = v_val_641_;
v_isShared_647_ = v_isSharedCheck_657_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_stopPos_644_);
lean_inc(v_startPos_643_);
lean_inc(v_str_642_);
lean_dec(v_val_641_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_657_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_651_; 
v___x_648_ = lean_string_utf8_extract(v_str_642_, v_startPos_643_, v_stopPos_644_);
lean_dec(v_stopPos_644_);
lean_dec(v_startPos_643_);
lean_dec_ref(v_str_642_);
v___x_649_ = lean_string_utf8_byte_size(v___x_648_);
if (v_isShared_647_ == 0)
{
lean_ctor_set(v___x_646_, 2, v___x_649_);
lean_ctor_set(v___x_646_, 1, v___y_634_);
lean_ctor_set(v___x_646_, 0, v___x_648_);
v___x_651_ = v___x_646_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v___x_648_);
lean_ctor_set(v_reuseFailAlloc_656_, 1, v___y_634_);
lean_ctor_set(v_reuseFailAlloc_656_, 2, v___x_649_);
v___x_651_ = v_reuseFailAlloc_656_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
uint8_t v___x_652_; 
v___x_652_ = l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2(v___x_651_);
lean_dec_ref(v___x_651_);
if (v___x_652_ == 0)
{
v___y_624_ = v_importsStx_638_;
v_opts_625_ = v_opts_599_;
goto v___jp_623_;
}
else
{
lean_object* v___x_653_; uint8_t v___x_654_; lean_object* v_opts_655_; 
v___x_653_ = l_Lean_linter_deprecated_module;
v___x_654_ = 0;
v_opts_655_ = l_Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4(v_opts_599_, v___x_653_, v___x_654_);
v___y_624_ = v_importsStx_638_;
v_opts_625_ = v_opts_655_;
goto v___jp_623_;
}
}
}
}
}
}
v___jp_658_:
{
lean_object* v___x_665_; lean_object* v___x_666_; uint8_t v___x_667_; 
v___x_665_ = lean_unsigned_to_nat(1u);
v___x_666_ = l_Lean_Syntax_getArg(v___y_661_, v___x_665_);
v___x_667_ = l_Lean_Syntax_isNone(v___x_666_);
if (v___x_667_ == 0)
{
uint8_t v___x_668_; 
lean_inc(v___x_666_);
v___x_668_ = l_Lean_Syntax_matchesNull(v___x_666_, v___x_665_);
if (v___x_668_ == 0)
{
lean_dec(v___x_666_);
lean_dec(v_moduleTk_664_);
lean_dec(v___y_662_);
lean_dec(v___y_661_);
v_opts_606_ = v_opts_599_;
v_ignoreDeprecatedImports_607_ = v_ignoreDeprecatedImports_621_;
v_importPositions_608_ = v_importPositions_622_;
goto v___jp_605_;
}
else
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; uint8_t v___x_672_; 
v___x_669_ = l_Lean_Syntax_getArg(v___x_666_, v___y_662_);
lean_dec(v___x_666_);
v___x_670_ = ((lean_object*)(l_Lean_Elab_HeaderSyntax_imports___closed__6));
lean_inc_ref(v___y_663_);
lean_inc_ref(v___y_659_);
lean_inc_ref(v___y_660_);
v___x_671_ = l_Lean_Name_mkStr4(v___y_660_, v___y_659_, v___y_663_, v___x_670_);
v___x_672_ = l_Lean_Syntax_isOfKind(v___x_669_, v___x_671_);
lean_dec(v___x_671_);
if (v___x_672_ == 0)
{
lean_dec(v_moduleTk_664_);
lean_dec(v___y_662_);
lean_dec(v___y_661_);
v_opts_606_ = v_opts_599_;
v_ignoreDeprecatedImports_607_ = v_ignoreDeprecatedImports_621_;
v_importPositions_608_ = v_importPositions_622_;
goto v___jp_605_;
}
else
{
v___y_633_ = v___y_661_;
v___y_634_ = v___y_662_;
v___y_635_ = v_moduleTk_664_;
goto v___jp_632_;
}
}
}
else
{
lean_dec(v___x_666_);
v___y_633_ = v___y_661_;
v___y_634_ = v___y_662_;
v___y_635_ = v_moduleTk_664_;
goto v___jp_632_;
}
}
v___jp_673_:
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; uint8_t v___x_679_; 
v___x_675_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__0));
v___x_676_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__1));
v___x_677_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__2));
v___x_678_ = ((lean_object*)(l_Lean_Elab_HeaderSyntax_imports___closed__1));
lean_inc(v_val_674_);
v___x_679_ = l_Lean_Syntax_isOfKind(v_val_674_, v___x_678_);
if (v___x_679_ == 0)
{
lean_dec(v_val_674_);
v_opts_606_ = v_opts_599_;
v_ignoreDeprecatedImports_607_ = v_ignoreDeprecatedImports_621_;
v_importPositions_608_ = v_importPositions_622_;
goto v___jp_605_;
}
else
{
lean_object* v___x_680_; lean_object* v___x_681_; uint8_t v___x_682_; 
v___x_680_ = lean_unsigned_to_nat(0u);
v___x_681_ = l_Lean_Syntax_getArg(v_val_674_, v___x_680_);
v___x_682_ = l_Lean_Syntax_isNone(v___x_681_);
if (v___x_682_ == 0)
{
lean_object* v___x_683_; uint8_t v___x_684_; 
v___x_683_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_681_);
v___x_684_ = l_Lean_Syntax_matchesNull(v___x_681_, v___x_683_);
if (v___x_684_ == 0)
{
lean_dec(v___x_681_);
lean_dec(v_val_674_);
v_opts_606_ = v_opts_599_;
v_ignoreDeprecatedImports_607_ = v_ignoreDeprecatedImports_621_;
v_importPositions_608_ = v_importPositions_622_;
goto v___jp_605_;
}
else
{
lean_object* v___x_685_; lean_object* v___x_686_; uint8_t v___x_687_; 
v___x_685_ = l_Lean_Syntax_getArg(v___x_681_, v___x_680_);
lean_dec(v___x_681_);
v___x_686_ = ((lean_object*)(l_Lean_Elab_HeaderSyntax_imports___closed__9));
lean_inc(v___x_685_);
v___x_687_ = l_Lean_Syntax_isOfKind(v___x_685_, v___x_686_);
if (v___x_687_ == 0)
{
lean_dec(v___x_685_);
lean_dec(v_val_674_);
v_opts_606_ = v_opts_599_;
v_ignoreDeprecatedImports_607_ = v_ignoreDeprecatedImports_621_;
v_importPositions_608_ = v_importPositions_622_;
goto v___jp_605_;
}
else
{
lean_object* v_moduleTk_688_; lean_object* v___x_689_; 
v_moduleTk_688_ = l_Lean_Syntax_getArg(v___x_685_, v___x_680_);
lean_dec(v___x_685_);
v___x_689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_689_, 0, v_moduleTk_688_);
v___y_659_ = v___x_676_;
v___y_660_ = v___x_675_;
v___y_661_ = v_val_674_;
v___y_662_ = v___x_680_;
v___y_663_ = v___x_677_;
v_moduleTk_664_ = v___x_689_;
goto v___jp_658_;
}
}
}
else
{
lean_object* v___x_690_; 
lean_dec(v___x_681_);
v___x_690_ = lean_box(0);
v___y_659_ = v___x_676_;
v___y_660_ = v___x_675_;
v___y_661_ = v_val_674_;
v___y_662_ = v___x_680_;
v___y_663_ = v___x_677_;
v_moduleTk_664_ = v___x_690_;
goto v___jp_658_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedImports___boxed(lean_object* v_env_693_, lean_object* v_imports_694_, lean_object* v_opts_695_, lean_object* v_inputCtx_696_, lean_object* v_startPos_697_, lean_object* v_messages_698_, lean_object* v_headerStx_x3f_699_, lean_object* v_origHeaderStx_x3f_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l_Lean_Elab_checkDeprecatedImports(v_env_693_, v_imports_694_, v_opts_695_, v_inputCtx_696_, v_startPos_697_, v_messages_698_, v_headerStx_x3f_699_, v_origHeaderStx_x3f_700_);
lean_dec_ref(v_imports_694_);
lean_dec_ref(v_env_693_);
return v_res_701_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_spec__2(lean_object* v_s_702_, lean_object* v_inst_703_, lean_object* v_R_704_, lean_object* v_a_705_, uint8_t v_b_706_, lean_object* v_c_707_){
_start:
{
uint8_t v___x_708_; 
v___x_708_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_spec__2___redArg(v_s_702_, v_a_705_, v_b_706_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_spec__2___boxed(lean_object* v_s_709_, lean_object* v_inst_710_, lean_object* v_R_711_, lean_object* v_a_712_, lean_object* v_b_713_, lean_object* v_c_714_){
_start:
{
uint8_t v_b_boxed_715_; uint8_t v_res_716_; lean_object* v_r_717_; 
v_b_boxed_715_ = lean_unbox(v_b_713_);
v_res_716_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_spec__2(v_s_709_, v_inst_710_, v_R_711_, v_a_712_, v_b_boxed_715_, v_c_714_);
lean_dec_ref(v_s_709_);
v_r_717_ = lean_box(v_res_716_);
return v_r_717_;
}
}
static lean_object* _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_718_; lean_object* v___x_719_; 
v___x_718_ = 33;
v___x_719_ = lean_box_uint32(v___x_718_);
return v___x_719_;
}
}
static lean_object* _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__2(void){
_start:
{
uint32_t v___x_720_; lean_object* v___x_721_; 
v___x_720_ = 42;
v___x_721_ = lean_box_uint32(v___x_720_);
return v___x_721_;
}
}
static lean_object* _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__3(void){
_start:
{
uint32_t v___x_722_; lean_object* v___x_723_; 
v___x_722_ = 63;
v___x_723_ = lean_box_uint32(v___x_722_);
return v___x_723_;
}
}
static lean_object* _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__4(void){
_start:
{
uint32_t v___x_724_; lean_object* v___x_725_; 
v___x_724_ = 124;
v___x_725_ = lean_box_uint32(v___x_724_);
return v___x_725_;
}
}
static lean_object* _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__5(void){
_start:
{
uint32_t v___x_726_; lean_object* v___x_727_; 
v___x_726_ = 34;
v___x_727_ = lean_box_uint32(v___x_726_);
return v___x_727_;
}
}
static lean_object* _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__6(void){
_start:
{
uint32_t v___x_728_; lean_object* v___x_729_; 
v___x_728_ = 62;
v___x_729_ = lean_box_uint32(v___x_728_);
return v___x_729_;
}
}
static lean_object* _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__7(void){
_start:
{
uint32_t v___x_730_; lean_object* v___x_731_; 
v___x_730_ = 60;
v___x_731_ = lean_box_uint32(v___x_730_);
return v___x_731_;
}
}
static lean_object* _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0(void){
_start:
{
lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_732_ = lean_unsigned_to_nat(7u);
v___x_733_ = lean_mk_empty_array_with_capacity(v___x_732_);
v___x_734_ = l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__7;
v___x_735_ = lean_array_push(v___x_733_, v___x_734_);
v___x_736_ = l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__6;
v___x_737_ = lean_array_push(v___x_735_, v___x_736_);
v___x_738_ = l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__5;
v___x_739_ = lean_array_push(v___x_737_, v___x_738_);
v___x_740_ = l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__4;
v___x_741_ = lean_array_push(v___x_739_, v___x_740_);
v___x_742_ = l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__3;
v___x_743_ = lean_array_push(v___x_741_, v___x_742_);
v___x_744_ = l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__2;
v___x_745_ = lean_array_push(v___x_743_, v___x_744_);
v___x_746_ = l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__1;
v___x_747_ = lean_array_push(v___x_745_, v___x_746_);
return v___x_747_;
}
}
static lean_object* _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars(void){
_start:
{
lean_object* v___x_748_; 
v___x_748_ = lean_obj_once(&l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0, &l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0_once, _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__0(lean_object* v_s_836_, lean_object* v_p_837_){
_start:
{
uint32_t v___y_839_; lean_object* v___x_844_; uint8_t v___x_845_; 
v___x_844_ = lean_string_utf8_byte_size(v_s_836_);
v___x_845_ = lean_nat_dec_eq(v_p_837_, v___x_844_);
if (v___x_845_ == 0)
{
uint32_t v___x_846_; uint32_t v___x_847_; uint8_t v___x_848_; 
v___x_846_ = lean_string_utf8_get_fast(v_s_836_, v_p_837_);
v___x_847_ = 97;
v___x_848_ = lean_uint32_dec_le(v___x_847_, v___x_846_);
if (v___x_848_ == 0)
{
v___y_839_ = v___x_846_;
goto v___jp_838_;
}
else
{
uint32_t v___x_849_; uint8_t v___x_850_; 
v___x_849_ = 122;
v___x_850_ = lean_uint32_dec_le(v___x_846_, v___x_849_);
if (v___x_850_ == 0)
{
v___y_839_ = v___x_846_;
goto v___jp_838_;
}
else
{
uint32_t v___x_851_; uint32_t v___x_852_; 
v___x_851_ = 4294967264;
v___x_852_ = lean_uint32_add(v___x_846_, v___x_851_);
v___y_839_ = v___x_852_;
goto v___jp_838_;
}
}
}
else
{
lean_dec(v_p_837_);
return v_s_836_;
}
v___jp_838_:
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
lean_inc(v_p_837_);
v___x_840_ = lean_string_utf8_set(v_s_836_, v_p_837_, v___y_839_);
v___x_841_ = l_Char_utf8Size(v___y_839_);
v___x_842_ = lean_nat_add(v_p_837_, v___x_841_);
lean_dec(v___x_841_);
lean_dec(v_p_837_);
v_s_836_ = v___x_840_;
v_p_837_ = v___x_842_;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2_spec__3___redArg(lean_object* v_s_853_, uint32_t v_a_854_, lean_object* v_a_855_, uint8_t v_b_856_){
_start:
{
lean_object* v_str_857_; lean_object* v_startInclusive_858_; lean_object* v_endExclusive_859_; lean_object* v___x_860_; uint8_t v___x_861_; 
v_str_857_ = lean_ctor_get(v_s_853_, 0);
v_startInclusive_858_ = lean_ctor_get(v_s_853_, 1);
v_endExclusive_859_ = lean_ctor_get(v_s_853_, 2);
v___x_860_ = lean_nat_sub(v_endExclusive_859_, v_startInclusive_858_);
v___x_861_ = lean_nat_dec_eq(v_a_855_, v___x_860_);
lean_dec(v___x_860_);
if (v___x_861_ == 0)
{
lean_object* v___x_862_; uint32_t v___x_863_; uint8_t v___x_864_; 
v___x_862_ = lean_nat_add(v_startInclusive_858_, v_a_855_);
lean_dec(v_a_855_);
v___x_863_ = lean_string_utf8_get_fast(v_str_857_, v___x_862_);
v___x_864_ = lean_uint32_dec_eq(v___x_863_, v_a_854_);
if (v___x_864_ == 0)
{
lean_object* v___x_865_; lean_object* v___x_866_; 
v___x_865_ = lean_string_utf8_next_fast(v_str_857_, v___x_862_);
lean_dec(v___x_862_);
v___x_866_ = lean_nat_sub(v___x_865_, v_startInclusive_858_);
v_a_855_ = v___x_866_;
v_b_856_ = v___x_864_;
goto _start;
}
else
{
lean_dec(v___x_862_);
return v___x_864_;
}
}
else
{
lean_dec(v_a_855_);
return v_b_856_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2_spec__3___redArg___boxed(lean_object* v_s_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_b_871_){
_start:
{
uint32_t v_a_boxed_872_; uint8_t v_b_boxed_873_; uint8_t v_res_874_; lean_object* v_r_875_; 
v_a_boxed_872_ = lean_unbox_uint32(v_a_869_);
lean_dec(v_a_869_);
v_b_boxed_873_ = lean_unbox(v_b_871_);
v_res_874_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2_spec__3___redArg(v_s_868_, v_a_boxed_872_, v_a_870_, v_b_boxed_873_);
lean_dec_ref(v_s_868_);
v_r_875_ = lean_box(v_res_874_);
return v_r_875_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2(uint32_t v_a_876_, lean_object* v_s_877_){
_start:
{
lean_object* v_searcher_878_; uint8_t v___x_879_; uint8_t v___x_880_; 
v_searcher_878_ = lean_unsigned_to_nat(0u);
v___x_879_ = 0;
v___x_880_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2_spec__3___redArg(v_s_877_, v_a_876_, v_searcher_878_, v___x_879_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2___boxed(lean_object* v_a_881_, lean_object* v_s_882_){
_start:
{
uint32_t v_a_boxed_883_; uint8_t v_res_884_; lean_object* v_r_885_; 
v_a_boxed_883_ = lean_unbox_uint32(v_a_881_);
lean_dec(v_a_881_);
v_res_884_ = l_String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2(v_a_boxed_883_, v_s_882_);
lean_dec_ref(v_s_882_);
v_r_885_ = lean_box(v_res_884_);
return v_r_885_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__3(lean_object* v_comp_889_, lean_object* v_as_890_, size_t v_sz_891_, size_t v_i_892_, lean_object* v_b_893_){
_start:
{
uint8_t v___x_894_; 
v___x_894_ = lean_usize_dec_lt(v_i_892_, v_sz_891_);
if (v___x_894_ == 0)
{
lean_dec_ref(v_comp_889_);
lean_inc_ref(v_b_893_);
return v_b_893_;
}
else
{
lean_object* v___x_895_; lean_object* v_a_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; uint32_t v___x_900_; uint8_t v___x_901_; 
v___x_895_ = lean_box(0);
v_a_896_ = lean_array_uget_borrowed(v_as_890_, v_i_892_);
v___x_897_ = lean_unsigned_to_nat(0u);
v___x_898_ = lean_string_utf8_byte_size(v_comp_889_);
lean_inc_ref(v_comp_889_);
v___x_899_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_899_, 0, v_comp_889_);
lean_ctor_set(v___x_899_, 1, v___x_897_);
lean_ctor_set(v___x_899_, 2, v___x_898_);
v___x_900_ = lean_unbox_uint32(v_a_896_);
v___x_901_ = l_String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2(v___x_900_, v___x_899_);
lean_dec_ref_known(v___x_899_, 3);
if (v___x_901_ == 0)
{
lean_object* v___x_902_; size_t v___x_903_; size_t v___x_904_; 
v___x_902_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__3___closed__0));
v___x_903_ = ((size_t)1ULL);
v___x_904_ = lean_usize_add(v_i_892_, v___x_903_);
v_i_892_ = v___x_904_;
v_b_893_ = v___x_902_;
goto _start;
}
else
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
lean_dec_ref(v_comp_889_);
lean_inc(v_a_896_);
v___x_906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_906_, 0, v_a_896_);
v___x_907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_907_, 0, v___x_906_);
v___x_908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_908_, 0, v___x_907_);
lean_ctor_set(v___x_908_, 1, v___x_895_);
return v___x_908_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__3___boxed(lean_object* v_comp_909_, lean_object* v_as_910_, lean_object* v_sz_911_, lean_object* v_i_912_, lean_object* v_b_913_){
_start:
{
size_t v_sz_boxed_914_; size_t v_i_boxed_915_; lean_object* v_res_916_; 
v_sz_boxed_914_ = lean_unbox_usize(v_sz_911_);
lean_dec(v_sz_911_);
v_i_boxed_915_ = lean_unbox_usize(v_i_912_);
lean_dec(v_i_912_);
v_res_916_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__3(v_comp_909_, v_as_910_, v_sz_boxed_914_, v_i_boxed_915_, v_b_913_);
lean_dec_ref(v_b_913_);
lean_dec_ref(v_as_910_);
return v_res_916_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__1_spec__1(lean_object* v_a_917_, lean_object* v_as_918_, size_t v_i_919_, size_t v_stop_920_){
_start:
{
uint8_t v___x_921_; 
v___x_921_ = lean_usize_dec_eq(v_i_919_, v_stop_920_);
if (v___x_921_ == 0)
{
lean_object* v___x_922_; uint8_t v___x_923_; 
v___x_922_ = lean_array_uget_borrowed(v_as_918_, v_i_919_);
v___x_923_ = lean_string_dec_eq(v_a_917_, v___x_922_);
if (v___x_923_ == 0)
{
size_t v___x_924_; size_t v___x_925_; 
v___x_924_ = ((size_t)1ULL);
v___x_925_ = lean_usize_add(v_i_919_, v___x_924_);
v_i_919_ = v___x_925_;
goto _start;
}
else
{
return v___x_923_;
}
}
else
{
uint8_t v___x_927_; 
v___x_927_ = 0;
return v___x_927_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__1_spec__1___boxed(lean_object* v_a_928_, lean_object* v_as_929_, lean_object* v_i_930_, lean_object* v_stop_931_){
_start:
{
size_t v_i_boxed_932_; size_t v_stop_boxed_933_; uint8_t v_res_934_; lean_object* v_r_935_; 
v_i_boxed_932_ = lean_unbox_usize(v_i_930_);
lean_dec(v_i_930_);
v_stop_boxed_933_ = lean_unbox_usize(v_stop_931_);
lean_dec(v_stop_931_);
v_res_934_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__1_spec__1(v_a_928_, v_as_929_, v_i_boxed_932_, v_stop_boxed_933_);
lean_dec_ref(v_as_929_);
lean_dec_ref(v_a_928_);
v_r_935_ = lean_box(v_res_934_);
return v_r_935_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__1(lean_object* v_as_936_, lean_object* v_a_937_){
_start:
{
lean_object* v___x_938_; lean_object* v___x_939_; uint8_t v___x_940_; 
v___x_938_ = lean_unsigned_to_nat(0u);
v___x_939_ = lean_array_get_size(v_as_936_);
v___x_940_ = lean_nat_dec_lt(v___x_938_, v___x_939_);
if (v___x_940_ == 0)
{
return v___x_940_;
}
else
{
if (v___x_940_ == 0)
{
return v___x_940_;
}
else
{
size_t v___x_941_; size_t v___x_942_; uint8_t v___x_943_; 
v___x_941_ = ((size_t)0ULL);
v___x_942_ = lean_usize_of_nat(v___x_939_);
v___x_943_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__1_spec__1(v_a_937_, v_as_936_, v___x_941_, v___x_942_);
return v___x_943_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__1___boxed(lean_object* v_as_944_, lean_object* v_a_945_){
_start:
{
uint8_t v_res_946_; lean_object* v_r_947_; 
v_res_946_ = l_Array_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__1(v_as_944_, v_a_945_);
lean_dec_ref(v_a_945_);
lean_dec_ref(v_as_944_);
v_r_947_ = lean_box(v_res_946_);
return v_r_947_;
}
}
static size_t _init_l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__0(void){
_start:
{
lean_object* v___x_948_; size_t v_sz_949_; 
v___x_948_ = l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars;
v_sz_949_ = lean_array_size(v___x_948_);
return v_sz_949_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability(lean_object* v_comp_954_){
_start:
{
lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; uint8_t v___x_958_; 
v___x_955_ = ((lean_object*)(l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames));
v___x_956_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_comp_954_);
v___x_957_ = l_String_mapAux___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__0(v_comp_954_, v___x_956_);
v___x_958_ = l_Array_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__1(v___x_955_, v___x_957_);
lean_dec_ref(v___x_957_);
if (v___x_958_ == 0)
{
lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; size_t v_sz_962_; size_t v___x_963_; lean_object* v___x_964_; lean_object* v_fst_965_; 
v___x_959_ = l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars;
v___x_960_ = lean_box(0);
v___x_961_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__3___closed__0));
v_sz_962_ = lean_usize_once(&l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__0, &l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__0_once, _init_l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__0);
v___x_963_ = ((size_t)0ULL);
v___x_964_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__3(v_comp_954_, v___x_959_, v_sz_962_, v___x_963_, v___x_961_);
v_fst_965_ = lean_ctor_get(v___x_964_, 0);
lean_inc(v_fst_965_);
lean_dec_ref(v___x_964_);
if (lean_obj_tag(v_fst_965_) == 0)
{
return v___x_960_;
}
else
{
lean_object* v_val_966_; 
v_val_966_ = lean_ctor_get(v_fst_965_, 0);
lean_inc(v_val_966_);
lean_dec_ref_known(v_fst_965_, 1);
if (lean_obj_tag(v_val_966_) == 1)
{
lean_object* v_val_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_981_; 
v_val_967_ = lean_ctor_get(v_val_966_, 0);
v_isSharedCheck_981_ = !lean_is_exclusive(v_val_966_);
if (v_isSharedCheck_981_ == 0)
{
v___x_969_ = v_val_966_;
v_isShared_970_ = v_isSharedCheck_981_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_val_967_);
lean_dec(v_val_966_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_981_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_971_; lean_object* v___x_972_; uint32_t v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_979_; 
v___x_971_ = ((lean_object*)(l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__1));
v___x_972_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___closed__0));
v___x_973_ = lean_unbox_uint32(v_val_967_);
lean_dec(v_val_967_);
v___x_974_ = lean_string_push(v___x_972_, v___x_973_);
v___x_975_ = lean_string_append(v___x_971_, v___x_974_);
lean_dec_ref(v___x_974_);
v___x_976_ = ((lean_object*)(l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__2));
v___x_977_ = lean_string_append(v___x_975_, v___x_976_);
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 0, v___x_977_);
v___x_979_ = v___x_969_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v___x_977_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
else
{
lean_dec(v_val_966_);
return v___x_960_;
}
}
}
else
{
lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_982_ = ((lean_object*)(l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__3));
v___x_983_ = lean_string_append(v___x_982_, v_comp_954_);
lean_dec_ref(v_comp_954_);
v___x_984_ = ((lean_object*)(l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__4));
v___x_985_ = lean_string_append(v___x_983_, v___x_984_);
v___x_986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_986_, 0, v___x_985_);
return v___x_986_;
}
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2_spec__3(lean_object* v_s_987_, uint32_t v_a_988_, lean_object* v_inst_989_, lean_object* v_R_990_, lean_object* v_a_991_, uint8_t v_b_992_, lean_object* v_c_993_){
_start:
{
uint8_t v___x_994_; 
v___x_994_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2_spec__3___redArg(v_s_987_, v_a_988_, v_a_991_, v_b_992_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2_spec__3___boxed(lean_object* v_s_995_, lean_object* v_a_996_, lean_object* v_inst_997_, lean_object* v_R_998_, lean_object* v_a_999_, lean_object* v_b_1000_, lean_object* v_c_1001_){
_start:
{
uint32_t v_a_boxed_1002_; uint8_t v_b_boxed_1003_; uint8_t v_res_1004_; lean_object* v_r_1005_; 
v_a_boxed_1002_ = lean_unbox_uint32(v_a_996_);
lean_dec(v_a_996_);
v_b_boxed_1003_ = lean_unbox(v_b_1000_);
v_res_1004_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2_spec__3(v_s_995_, v_a_boxed_1002_, v_inst_997_, v_R_998_, v_a_999_, v_b_boxed_1003_, v_c_1001_);
lean_dec_ref(v_s_995_);
v_r_1005_ = lean_box(v_res_1004_);
return v_r_1005_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_checkModuleNamePortability_go(lean_object* v_mainModule_1008_, lean_object* v_inputCtx_1009_, lean_object* v_startPos_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_){
_start:
{
switch(lean_obj_tag(v_a_1011_))
{
case 0:
{
lean_dec_ref(v_inputCtx_1009_);
lean_dec(v_mainModule_1008_);
return v_a_1012_;
}
case 1:
{
lean_object* v_pre_1013_; lean_object* v_str_1014_; lean_object* v___x_1015_; 
v_pre_1013_ = lean_ctor_get(v_a_1011_, 0);
lean_inc(v_pre_1013_);
v_str_1014_ = lean_ctor_get(v_a_1011_, 1);
lean_inc_ref(v_str_1014_);
lean_dec_ref_known(v_a_1011_, 2);
v___x_1015_ = l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability(v_str_1014_);
if (lean_obj_tag(v___x_1015_) == 0)
{
v_a_1011_ = v_pre_1013_;
goto _start;
}
else
{
lean_object* v_val_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1042_; 
v_val_1017_ = lean_ctor_get(v___x_1015_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_1015_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1019_ = v___x_1015_;
v_isShared_1020_ = v_isSharedCheck_1042_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_val_1017_);
lean_dec(v___x_1015_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1042_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v_fileName_1021_; lean_object* v_fileMap_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; uint8_t v___x_1025_; uint8_t v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; uint8_t v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1036_; 
v_fileName_1021_ = lean_ctor_get(v_inputCtx_1009_, 1);
v_fileMap_1022_ = lean_ctor_get(v_inputCtx_1009_, 2);
lean_inc_ref(v_fileMap_1022_);
v___x_1023_ = l_Lean_FileMap_toPosition(v_fileMap_1022_, v_startPos_1010_);
v___x_1024_ = lean_box(0);
v___x_1025_ = 0;
v___x_1026_ = 2;
v___x_1027_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___closed__0));
v___x_1028_ = ((lean_object*)(l___private_Lean_Elab_Import_0__Lean_Elab_checkModuleNamePortability_go___closed__0));
v___x_1029_ = 1;
lean_inc(v_mainModule_1008_);
v___x_1030_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mainModule_1008_, v___x_1029_);
v___x_1031_ = lean_string_append(v___x_1028_, v___x_1030_);
lean_dec_ref(v___x_1030_);
v___x_1032_ = ((lean_object*)(l___private_Lean_Elab_Import_0__Lean_Elab_checkModuleNamePortability_go___closed__1));
v___x_1033_ = lean_string_append(v___x_1031_, v___x_1032_);
v___x_1034_ = lean_string_append(v___x_1033_, v_val_1017_);
lean_dec(v_val_1017_);
if (v_isShared_1020_ == 0)
{
lean_ctor_set_tag(v___x_1019_, 3);
lean_ctor_set(v___x_1019_, 0, v___x_1034_);
v___x_1036_ = v___x_1019_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v___x_1034_);
v___x_1036_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1037_ = l_Lean_MessageData_ofFormat(v___x_1036_);
lean_inc_ref(v_fileName_1021_);
v___x_1038_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1038_, 0, v_fileName_1021_);
lean_ctor_set(v___x_1038_, 1, v___x_1023_);
lean_ctor_set(v___x_1038_, 2, v___x_1024_);
lean_ctor_set(v___x_1038_, 3, v___x_1027_);
lean_ctor_set(v___x_1038_, 4, v___x_1037_);
lean_ctor_set_uint8(v___x_1038_, sizeof(void*)*5, v___x_1025_);
lean_ctor_set_uint8(v___x_1038_, sizeof(void*)*5 + 1, v___x_1026_);
lean_ctor_set_uint8(v___x_1038_, sizeof(void*)*5 + 2, v___x_1025_);
v___x_1039_ = l_Lean_MessageLog_add(v___x_1038_, v_a_1012_);
v_a_1011_ = v_pre_1013_;
v_a_1012_ = v___x_1039_;
goto _start;
}
}
}
}
default: 
{
lean_object* v_pre_1043_; 
v_pre_1043_ = lean_ctor_get(v_a_1011_, 0);
lean_inc(v_pre_1043_);
lean_dec_ref_known(v_a_1011_, 2);
v_a_1011_ = v_pre_1043_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_checkModuleNamePortability_go___boxed(lean_object* v_mainModule_1045_, lean_object* v_inputCtx_1046_, lean_object* v_startPos_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l___private_Lean_Elab_Import_0__Lean_Elab_checkModuleNamePortability_go(v_mainModule_1045_, v_inputCtx_1046_, v_startPos_1047_, v_a_1048_, v_a_1049_);
lean_dec(v_startPos_1047_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkModuleNamePortability(lean_object* v_mainModule_1051_, lean_object* v_inputCtx_1052_, lean_object* v_startPos_1053_, lean_object* v_messages_1054_){
_start:
{
lean_object* v___x_1055_; 
lean_inc(v_mainModule_1051_);
v___x_1055_ = l___private_Lean_Elab_Import_0__Lean_Elab_checkModuleNamePortability_go(v_mainModule_1051_, v_inputCtx_1052_, v_startPos_1053_, v_mainModule_1051_, v_messages_1054_);
return v___x_1055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkModuleNamePortability___boxed(lean_object* v_mainModule_1056_, lean_object* v_inputCtx_1057_, lean_object* v_startPos_1058_, lean_object* v_messages_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l_Lean_Elab_checkModuleNamePortability(v_mainModule_1056_, v_inputCtx_1057_, v_startPos_1058_, v_messages_1059_);
lean_dec(v_startPos_1058_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_processHeaderCore(lean_object* v_startPos_1061_, lean_object* v_imports_1062_, uint8_t v_isModule_1063_, lean_object* v_opts_1064_, lean_object* v_messages_1065_, lean_object* v_inputCtx_1066_, uint32_t v_trustLevel_1067_, lean_object* v_plugins_1068_, uint8_t v_leakEnv_1069_, lean_object* v_mainModule_1070_, lean_object* v_package_x3f_1071_, lean_object* v_arts_1072_, lean_object* v_headerStx_x3f_1073_, lean_object* v_origHeaderStx_x3f_1074_){
_start:
{
lean_object* v_fst_1077_; lean_object* v_snd_1078_; uint8_t v___x_1086_; uint8_t v___y_1088_; 
v___x_1086_ = 1;
if (v_isModule_1063_ == 0)
{
uint8_t v___x_1121_; 
v___x_1121_ = 2;
v___y_1088_ = v___x_1121_;
goto v___jp_1087_;
}
else
{
lean_object* v___x_1122_; uint8_t v___x_1123_; 
v___x_1122_ = l_Lean_Elab_inServer;
v___x_1123_ = l_Lean_Option_get___at___00Lean_Elab_checkDeprecatedImports_spec__0(v_opts_1064_, v___x_1122_);
if (v___x_1123_ == 0)
{
uint8_t v___x_1124_; 
v___x_1124_ = 0;
v___y_1088_ = v___x_1124_;
goto v___jp_1087_;
}
else
{
uint8_t v___x_1125_; 
v___x_1125_ = 1;
v___y_1088_ = v___x_1125_;
goto v___jp_1087_;
}
}
v___jp_1076_:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; 
lean_inc_n(v_mainModule_1070_, 2);
v___x_1079_ = l_Lean_Environment_setMainModule(v_fst_1077_, v_mainModule_1070_);
v___x_1080_ = l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
v___x_1081_ = l_Lean_PersistentEnvExtension_setState___redArg(v___x_1080_, v___x_1079_, v_package_x3f_1071_);
lean_inc(v_startPos_1061_);
lean_inc_ref(v_inputCtx_1066_);
v___x_1082_ = l_Lean_Elab_checkDeprecatedImports(v___x_1081_, v_imports_1062_, v_opts_1064_, v_inputCtx_1066_, v_startPos_1061_, v_snd_1078_, v_headerStx_x3f_1073_, v_origHeaderStx_x3f_1074_);
lean_dec_ref(v_imports_1062_);
v___x_1083_ = l___private_Lean_Elab_Import_0__Lean_Elab_checkModuleNamePortability_go(v_mainModule_1070_, v_inputCtx_1066_, v_startPos_1061_, v_mainModule_1070_, v___x_1082_);
lean_dec(v_startPos_1061_);
v___x_1084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1081_);
lean_ctor_set(v___x_1084_, 1, v___x_1083_);
v___x_1085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1084_);
return v___x_1085_;
}
v___jp_1087_:
{
lean_object* v___x_1089_; 
lean_inc_ref(v_opts_1064_);
lean_inc_ref(v_imports_1062_);
v___x_1089_ = l_Lean_importModules(v_imports_1062_, v_opts_1064_, v_trustLevel_1067_, v_plugins_1068_, v_leakEnv_1069_, v___x_1086_, v___y_1088_, v_arts_1072_);
if (lean_obj_tag(v___x_1089_) == 0)
{
lean_object* v_a_1090_; 
v_a_1090_ = lean_ctor_get(v___x_1089_, 0);
lean_inc(v_a_1090_);
lean_dec_ref_known(v___x_1089_, 1);
v_fst_1077_ = v_a_1090_;
v_snd_1078_ = v_messages_1065_;
goto v___jp_1076_;
}
else
{
lean_object* v_a_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1120_; 
v_a_1091_ = lean_ctor_get(v___x_1089_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1093_ = v___x_1089_;
v_isShared_1094_ = v_isSharedCheck_1120_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_a_1091_);
lean_dec(v___x_1089_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1120_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
uint32_t v___x_1095_; lean_object* v___x_1096_; 
v___x_1095_ = 0;
v___x_1096_ = l_Lean_mkEmptyEnvironment(v___x_1095_);
if (lean_obj_tag(v___x_1096_) == 0)
{
lean_object* v_a_1097_; lean_object* v_fileName_1098_; lean_object* v_fileMap_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; uint8_t v___x_1102_; uint8_t v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1107_; 
v_a_1097_ = lean_ctor_get(v___x_1096_, 0);
lean_inc(v_a_1097_);
lean_dec_ref_known(v___x_1096_, 1);
v_fileName_1098_ = lean_ctor_get(v_inputCtx_1066_, 1);
v_fileMap_1099_ = lean_ctor_get(v_inputCtx_1066_, 2);
lean_inc_ref(v_fileMap_1099_);
v___x_1100_ = l_Lean_FileMap_toPosition(v_fileMap_1099_, v_startPos_1061_);
v___x_1101_ = lean_box(0);
v___x_1102_ = 0;
v___x_1103_ = 2;
v___x_1104_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___closed__0));
v___x_1105_ = lean_io_error_to_string(v_a_1091_);
if (v_isShared_1094_ == 0)
{
lean_ctor_set_tag(v___x_1093_, 3);
lean_ctor_set(v___x_1093_, 0, v___x_1105_);
v___x_1107_ = v___x_1093_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v___x_1105_);
v___x_1107_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1108_ = l_Lean_MessageData_ofFormat(v___x_1107_);
lean_inc_ref(v_fileName_1098_);
v___x_1109_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1109_, 0, v_fileName_1098_);
lean_ctor_set(v___x_1109_, 1, v___x_1100_);
lean_ctor_set(v___x_1109_, 2, v___x_1101_);
lean_ctor_set(v___x_1109_, 3, v___x_1104_);
lean_ctor_set(v___x_1109_, 4, v___x_1108_);
lean_ctor_set_uint8(v___x_1109_, sizeof(void*)*5, v___x_1102_);
lean_ctor_set_uint8(v___x_1109_, sizeof(void*)*5 + 1, v___x_1103_);
lean_ctor_set_uint8(v___x_1109_, sizeof(void*)*5 + 2, v___x_1102_);
v___x_1110_ = l_Lean_MessageLog_add(v___x_1109_, v_messages_1065_);
v_fst_1077_ = v_a_1097_;
v_snd_1078_ = v___x_1110_;
goto v___jp_1076_;
}
}
else
{
lean_object* v_a_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1119_; 
lean_del_object(v___x_1093_);
lean_dec(v_a_1091_);
lean_dec(v_origHeaderStx_x3f_1074_);
lean_dec(v_headerStx_x3f_1073_);
lean_dec(v_package_x3f_1071_);
lean_dec(v_mainModule_1070_);
lean_dec_ref(v_inputCtx_1066_);
lean_dec_ref(v_messages_1065_);
lean_dec_ref(v_opts_1064_);
lean_dec_ref(v_imports_1062_);
lean_dec(v_startPos_1061_);
v_a_1112_ = lean_ctor_get(v___x_1096_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_1096_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1114_ = v___x_1096_;
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_a_1112_);
lean_dec(v___x_1096_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1117_; 
if (v_isShared_1115_ == 0)
{
v___x_1117_ = v___x_1114_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_a_1112_);
v___x_1117_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
return v___x_1117_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_processHeaderCore___boxed(lean_object* v_startPos_1126_, lean_object* v_imports_1127_, lean_object* v_isModule_1128_, lean_object* v_opts_1129_, lean_object* v_messages_1130_, lean_object* v_inputCtx_1131_, lean_object* v_trustLevel_1132_, lean_object* v_plugins_1133_, lean_object* v_leakEnv_1134_, lean_object* v_mainModule_1135_, lean_object* v_package_x3f_1136_, lean_object* v_arts_1137_, lean_object* v_headerStx_x3f_1138_, lean_object* v_origHeaderStx_x3f_1139_, lean_object* v_a_1140_){
_start:
{
uint8_t v_isModule_boxed_1141_; uint32_t v_trustLevel_boxed_1142_; uint8_t v_leakEnv_boxed_1143_; lean_object* v_res_1144_; 
v_isModule_boxed_1141_ = lean_unbox(v_isModule_1128_);
v_trustLevel_boxed_1142_ = lean_unbox_uint32(v_trustLevel_1132_);
lean_dec(v_trustLevel_1132_);
v_leakEnv_boxed_1143_ = lean_unbox(v_leakEnv_1134_);
v_res_1144_ = l_Lean_Elab_processHeaderCore(v_startPos_1126_, v_imports_1127_, v_isModule_boxed_1141_, v_opts_1129_, v_messages_1130_, v_inputCtx_1131_, v_trustLevel_boxed_1142_, v_plugins_1133_, v_leakEnv_boxed_1143_, v_mainModule_1135_, v_package_x3f_1136_, v_arts_1137_, v_headerStx_x3f_1138_, v_origHeaderStx_x3f_1139_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_processHeader(lean_object* v_header_1145_, lean_object* v_opts_1146_, lean_object* v_messages_1147_, lean_object* v_inputCtx_1148_, uint32_t v_trustLevel_1149_, lean_object* v_plugins_1150_, uint8_t v_leakEnv_1151_, lean_object* v_mainModule_1152_){
_start:
{
lean_object* v___x_1154_; uint8_t v___x_1155_; lean_object* v___x_1156_; uint8_t v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1154_ = l_Lean_Elab_HeaderSyntax_startPos(v_header_1145_);
v___x_1155_ = 1;
lean_inc(v_header_1145_);
v___x_1156_ = l_Lean_Elab_HeaderSyntax_imports(v_header_1145_, v___x_1155_);
v___x_1157_ = l_Lean_Elab_HeaderSyntax_isModule(v_header_1145_);
v___x_1158_ = lean_box(0);
v___x_1159_ = lean_box(1);
v___x_1160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1160_, 0, v_header_1145_);
v___x_1161_ = l_Lean_Elab_processHeaderCore(v___x_1154_, v___x_1156_, v___x_1157_, v_opts_1146_, v_messages_1147_, v_inputCtx_1148_, v_trustLevel_1149_, v_plugins_1150_, v_leakEnv_1151_, v_mainModule_1152_, v___x_1158_, v___x_1159_, v___x_1160_, v___x_1158_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_processHeader___boxed(lean_object* v_header_1162_, lean_object* v_opts_1163_, lean_object* v_messages_1164_, lean_object* v_inputCtx_1165_, lean_object* v_trustLevel_1166_, lean_object* v_plugins_1167_, lean_object* v_leakEnv_1168_, lean_object* v_mainModule_1169_, lean_object* v_a_1170_){
_start:
{
uint32_t v_trustLevel_boxed_1171_; uint8_t v_leakEnv_boxed_1172_; lean_object* v_res_1173_; 
v_trustLevel_boxed_1171_ = lean_unbox_uint32(v_trustLevel_1166_);
lean_dec(v_trustLevel_1166_);
v_leakEnv_boxed_1172_ = lean_unbox(v_leakEnv_1168_);
v_res_1173_ = l_Lean_Elab_processHeader(v_header_1162_, v_opts_1163_, v_messages_1164_, v_inputCtx_1165_, v_trustLevel_boxed_1171_, v_plugins_1167_, v_leakEnv_boxed_1172_, v_mainModule_1169_);
return v_res_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_parseImports(lean_object* v_input_1175_, lean_object* v_fileName_1176_){
_start:
{
lean_object* v___y_1179_; 
if (lean_obj_tag(v_fileName_1176_) == 0)
{
lean_object* v___x_1224_; 
v___x_1224_ = ((lean_object*)(l_Lean_Elab_parseImports___closed__0));
v___y_1179_ = v___x_1224_;
goto v___jp_1178_;
}
else
{
lean_object* v_val_1225_; 
v_val_1225_ = lean_ctor_get(v_fileName_1176_, 0);
lean_inc(v_val_1225_);
lean_dec_ref_known(v_fileName_1176_, 1);
v___y_1179_ = v_val_1225_;
goto v___jp_1178_;
}
v___jp_1178_:
{
uint8_t v___x_1180_; lean_object* v___x_1181_; lean_object* v_inputCtx_1182_; lean_object* v___x_1183_; 
v___x_1180_ = 1;
v___x_1181_ = lean_string_utf8_byte_size(v_input_1175_);
v_inputCtx_1182_ = l_Lean_Parser_mkInputContext___redArg(v_input_1175_, v___y_1179_, v___x_1180_, v___x_1181_);
lean_inc_ref(v_inputCtx_1182_);
v___x_1183_ = l_Lean_Parser_parseHeader(v_inputCtx_1182_);
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_object* v_a_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1215_; 
v_a_1184_ = lean_ctor_get(v___x_1183_, 0);
v_isSharedCheck_1215_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1186_ = v___x_1183_;
v_isShared_1187_ = v_isSharedCheck_1215_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_a_1184_);
lean_dec(v___x_1183_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1215_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v_snd_1188_; lean_object* v_fst_1189_; lean_object* v_fst_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1213_; 
v_snd_1188_ = lean_ctor_get(v_a_1184_, 1);
lean_inc(v_snd_1188_);
v_fst_1189_ = lean_ctor_get(v_snd_1188_, 0);
lean_inc(v_fst_1189_);
v_fst_1190_ = lean_ctor_get(v_a_1184_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v_a_1184_);
if (v_isSharedCheck_1213_ == 0)
{
lean_object* v_unused_1214_; 
v_unused_1214_ = lean_ctor_get(v_a_1184_, 1);
lean_dec(v_unused_1214_);
v___x_1192_ = v_a_1184_;
v_isShared_1193_ = v_isSharedCheck_1213_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_fst_1190_);
lean_dec(v_a_1184_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1213_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v_snd_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1211_; 
v_snd_1194_ = lean_ctor_get(v_snd_1188_, 1);
v_isSharedCheck_1211_ = !lean_is_exclusive(v_snd_1188_);
if (v_isSharedCheck_1211_ == 0)
{
lean_object* v_unused_1212_; 
v_unused_1212_ = lean_ctor_get(v_snd_1188_, 0);
lean_dec(v_unused_1212_);
v___x_1196_ = v_snd_1188_;
v_isShared_1197_ = v_isSharedCheck_1211_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_snd_1194_);
lean_dec(v_snd_1188_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1211_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v_fileMap_1198_; lean_object* v_pos_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1203_; 
v_fileMap_1198_ = lean_ctor_get(v_inputCtx_1182_, 2);
lean_inc_ref(v_fileMap_1198_);
lean_dec_ref(v_inputCtx_1182_);
v_pos_1199_ = lean_ctor_get(v_fst_1189_, 0);
lean_inc(v_pos_1199_);
lean_dec(v_fst_1189_);
v___x_1200_ = l_Lean_Elab_HeaderSyntax_imports(v_fst_1190_, v___x_1180_);
v___x_1201_ = l_Lean_FileMap_toPosition(v_fileMap_1198_, v_pos_1199_);
lean_dec(v_pos_1199_);
if (v_isShared_1197_ == 0)
{
lean_ctor_set(v___x_1196_, 0, v___x_1201_);
v___x_1203_ = v___x_1196_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v___x_1201_);
lean_ctor_set(v_reuseFailAlloc_1210_, 1, v_snd_1194_);
v___x_1203_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
lean_object* v___x_1205_; 
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 1, v___x_1203_);
lean_ctor_set(v___x_1192_, 0, v___x_1200_);
v___x_1205_ = v___x_1192_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v___x_1200_);
lean_ctor_set(v_reuseFailAlloc_1209_, 1, v___x_1203_);
v___x_1205_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
lean_object* v___x_1207_; 
if (v_isShared_1187_ == 0)
{
lean_ctor_set(v___x_1186_, 0, v___x_1205_);
v___x_1207_ = v___x_1186_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v___x_1205_);
v___x_1207_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
return v___x_1207_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1223_; 
lean_dec_ref(v_inputCtx_1182_);
v_a_1216_ = lean_ctor_get(v___x_1183_, 0);
v_isSharedCheck_1223_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1218_ = v___x_1183_;
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_a_1216_);
lean_dec(v___x_1183_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1221_; 
if (v_isShared_1219_ == 0)
{
v___x_1221_ = v___x_1218_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_a_1216_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
return v___x_1221_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_parseImports___boxed(lean_object* v_input_1226_, lean_object* v_fileName_1227_, lean_object* v_a_1228_){
_start:
{
lean_object* v_res_1229_; 
v_res_1229_ = l_Lean_Elab_parseImports(v_input_1226_, v_fileName_1227_);
return v_res_1229_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00Lean_Elab_printImports_spec__0_spec__0(lean_object* v_s_1230_){
_start:
{
lean_object* v___x_1232_; lean_object* v_putStr_1233_; lean_object* v___x_1234_; 
v___x_1232_ = lean_get_stdout();
v_putStr_1233_ = lean_ctor_get(v___x_1232_, 4);
lean_inc_ref(v_putStr_1233_);
lean_dec_ref(v___x_1232_);
v___x_1234_ = lean_apply_2(v_putStr_1233_, v_s_1230_, lean_box(0));
return v___x_1234_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00Lean_Elab_printImports_spec__0_spec__0___boxed(lean_object* v_s_1235_, lean_object* v_a_1236_){
_start:
{
lean_object* v_res_1237_; 
v_res_1237_ = l_IO_print___at___00IO_println___at___00Lean_Elab_printImports_spec__0_spec__0(v_s_1235_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00Lean_Elab_printImports_spec__0(lean_object* v_s_1238_){
_start:
{
uint32_t v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1240_ = 10;
v___x_1241_ = lean_string_push(v_s_1238_, v___x_1240_);
v___x_1242_ = l_IO_print___at___00IO_println___at___00Lean_Elab_printImports_spec__0_spec__0(v___x_1241_);
return v___x_1242_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00Lean_Elab_printImports_spec__0___boxed(lean_object* v_s_1243_, lean_object* v_a_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l_IO_println___at___00Lean_Elab_printImports_spec__0(v_s_1243_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImports_spec__1(lean_object* v_as_1246_, size_t v_sz_1247_, size_t v_i_1248_, lean_object* v_b_1249_){
_start:
{
uint8_t v___x_1251_; 
v___x_1251_ = lean_usize_dec_lt(v_i_1248_, v_sz_1247_);
if (v___x_1251_ == 0)
{
lean_object* v___x_1252_; 
v___x_1252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1252_, 0, v_b_1249_);
return v___x_1252_;
}
else
{
lean_object* v_a_1253_; lean_object* v_module_1254_; lean_object* v___x_1255_; 
v_a_1253_ = lean_array_uget_borrowed(v_as_1246_, v_i_1248_);
v_module_1254_ = lean_ctor_get(v_a_1253_, 0);
lean_inc(v_module_1254_);
v___x_1255_ = l_Lean_findOLean(v_module_1254_);
if (lean_obj_tag(v___x_1255_) == 0)
{
lean_object* v_a_1256_; lean_object* v___x_1257_; 
v_a_1256_ = lean_ctor_get(v___x_1255_, 0);
lean_inc(v_a_1256_);
lean_dec_ref_known(v___x_1255_, 1);
v___x_1257_ = l_IO_println___at___00Lean_Elab_printImports_spec__0(v_a_1256_);
if (lean_obj_tag(v___x_1257_) == 0)
{
lean_object* v___x_1258_; size_t v___x_1259_; size_t v___x_1260_; 
lean_dec_ref_known(v___x_1257_, 1);
v___x_1258_ = lean_box(0);
v___x_1259_ = ((size_t)1ULL);
v___x_1260_ = lean_usize_add(v_i_1248_, v___x_1259_);
v_i_1248_ = v___x_1260_;
v_b_1249_ = v___x_1258_;
goto _start;
}
else
{
return v___x_1257_;
}
}
else
{
lean_object* v_a_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1269_; 
v_a_1262_ = lean_ctor_get(v___x_1255_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_1255_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1264_ = v___x_1255_;
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_a_1262_);
lean_dec(v___x_1255_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1267_; 
if (v_isShared_1265_ == 0)
{
v___x_1267_ = v___x_1264_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_a_1262_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImports_spec__1___boxed(lean_object* v_as_1270_, lean_object* v_sz_1271_, lean_object* v_i_1272_, lean_object* v_b_1273_, lean_object* v___y_1274_){
_start:
{
size_t v_sz_boxed_1275_; size_t v_i_boxed_1276_; lean_object* v_res_1277_; 
v_sz_boxed_1275_ = lean_unbox_usize(v_sz_1271_);
lean_dec(v_sz_1271_);
v_i_boxed_1276_ = lean_unbox_usize(v_i_1272_);
lean_dec(v_i_1272_);
v_res_1277_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImports_spec__1(v_as_1270_, v_sz_boxed_1275_, v_i_boxed_1276_, v_b_1273_);
lean_dec_ref(v_as_1270_);
return v_res_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_printImports(lean_object* v_input_1278_, lean_object* v_fileName_1279_){
_start:
{
lean_object* v___x_1281_; 
v___x_1281_ = l_Lean_Elab_parseImports(v_input_1278_, v_fileName_1279_);
if (lean_obj_tag(v___x_1281_) == 0)
{
lean_object* v_a_1282_; lean_object* v_fst_1283_; lean_object* v___x_1284_; size_t v_sz_1285_; size_t v___x_1286_; lean_object* v___x_1287_; 
v_a_1282_ = lean_ctor_get(v___x_1281_, 0);
lean_inc(v_a_1282_);
lean_dec_ref_known(v___x_1281_, 1);
v_fst_1283_ = lean_ctor_get(v_a_1282_, 0);
lean_inc(v_fst_1283_);
lean_dec(v_a_1282_);
v___x_1284_ = lean_box(0);
v_sz_1285_ = lean_array_size(v_fst_1283_);
v___x_1286_ = ((size_t)0ULL);
v___x_1287_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImports_spec__1(v_fst_1283_, v_sz_1285_, v___x_1286_, v___x_1284_);
lean_dec(v_fst_1283_);
if (lean_obj_tag(v___x_1287_) == 0)
{
lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1294_; 
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1294_ == 0)
{
lean_object* v_unused_1295_; 
v_unused_1295_ = lean_ctor_get(v___x_1287_, 0);
lean_dec(v_unused_1295_);
v___x_1289_ = v___x_1287_;
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
else
{
lean_dec(v___x_1287_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1292_; 
if (v_isShared_1290_ == 0)
{
lean_ctor_set(v___x_1289_, 0, v___x_1284_);
v___x_1292_ = v___x_1289_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v___x_1284_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
}
else
{
return v___x_1287_;
}
}
else
{
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1303_; 
v_a_1296_ = lean_ctor_get(v___x_1281_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1298_ = v___x_1281_;
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1281_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1301_; 
if (v_isShared_1299_ == 0)
{
v___x_1301_ = v___x_1298_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_a_1296_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_printImports___boxed(lean_object* v_input_1304_, lean_object* v_fileName_1305_, lean_object* v_a_1306_){
_start:
{
lean_object* v_res_1307_; 
v_res_1307_ = l_Lean_Elab_printImports(v_input_1304_, v_fileName_1305_);
return v_res_1307_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImportSrcs_spec__0(lean_object* v_a_1308_, lean_object* v_as_1309_, size_t v_sz_1310_, size_t v_i_1311_, lean_object* v_b_1312_){
_start:
{
uint8_t v___x_1314_; 
v___x_1314_ = lean_usize_dec_lt(v_i_1311_, v_sz_1310_);
if (v___x_1314_ == 0)
{
lean_object* v___x_1315_; 
lean_dec(v_a_1308_);
v___x_1315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1315_, 0, v_b_1312_);
return v___x_1315_;
}
else
{
lean_object* v_a_1316_; lean_object* v_module_1317_; lean_object* v___x_1318_; 
v_a_1316_ = lean_array_uget_borrowed(v_as_1309_, v_i_1311_);
v_module_1317_ = lean_ctor_get(v_a_1316_, 0);
lean_inc(v_module_1317_);
lean_inc(v_a_1308_);
v___x_1318_ = l_Lean_findLean(v_a_1308_, v_module_1317_);
if (lean_obj_tag(v___x_1318_) == 0)
{
lean_object* v_a_1319_; lean_object* v___x_1320_; 
v_a_1319_ = lean_ctor_get(v___x_1318_, 0);
lean_inc(v_a_1319_);
lean_dec_ref_known(v___x_1318_, 1);
v___x_1320_ = l_IO_println___at___00Lean_Elab_printImports_spec__0(v_a_1319_);
if (lean_obj_tag(v___x_1320_) == 0)
{
lean_object* v___x_1321_; size_t v___x_1322_; size_t v___x_1323_; 
lean_dec_ref_known(v___x_1320_, 1);
v___x_1321_ = lean_box(0);
v___x_1322_ = ((size_t)1ULL);
v___x_1323_ = lean_usize_add(v_i_1311_, v___x_1322_);
v_i_1311_ = v___x_1323_;
v_b_1312_ = v___x_1321_;
goto _start;
}
else
{
lean_dec(v_a_1308_);
return v___x_1320_;
}
}
else
{
lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1332_; 
lean_dec(v_a_1308_);
v_a_1325_ = lean_ctor_get(v___x_1318_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1327_ = v___x_1318_;
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_a_1325_);
lean_dec(v___x_1318_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1330_; 
if (v_isShared_1328_ == 0)
{
v___x_1330_ = v___x_1327_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_a_1325_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImportSrcs_spec__0___boxed(lean_object* v_a_1333_, lean_object* v_as_1334_, lean_object* v_sz_1335_, lean_object* v_i_1336_, lean_object* v_b_1337_, lean_object* v___y_1338_){
_start:
{
size_t v_sz_boxed_1339_; size_t v_i_boxed_1340_; lean_object* v_res_1341_; 
v_sz_boxed_1339_ = lean_unbox_usize(v_sz_1335_);
lean_dec(v_sz_1335_);
v_i_boxed_1340_ = lean_unbox_usize(v_i_1336_);
lean_dec(v_i_1336_);
v_res_1341_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImportSrcs_spec__0(v_a_1333_, v_as_1334_, v_sz_boxed_1339_, v_i_boxed_1340_, v_b_1337_);
lean_dec_ref(v_as_1334_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_printImportSrcs(lean_object* v_input_1342_, lean_object* v_fileName_1343_){
_start:
{
lean_object* v___x_1345_; 
v___x_1345_ = l_Lean_getSrcSearchPath();
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_object* v_a_1346_; lean_object* v___x_1347_; 
v_a_1346_ = lean_ctor_get(v___x_1345_, 0);
lean_inc(v_a_1346_);
lean_dec_ref_known(v___x_1345_, 1);
v___x_1347_ = l_Lean_Elab_parseImports(v_input_1342_, v_fileName_1343_);
if (lean_obj_tag(v___x_1347_) == 0)
{
lean_object* v_a_1348_; lean_object* v_fst_1349_; lean_object* v___x_1350_; size_t v_sz_1351_; size_t v___x_1352_; lean_object* v___x_1353_; 
v_a_1348_ = lean_ctor_get(v___x_1347_, 0);
lean_inc(v_a_1348_);
lean_dec_ref_known(v___x_1347_, 1);
v_fst_1349_ = lean_ctor_get(v_a_1348_, 0);
lean_inc(v_fst_1349_);
lean_dec(v_a_1348_);
v___x_1350_ = lean_box(0);
v_sz_1351_ = lean_array_size(v_fst_1349_);
v___x_1352_ = ((size_t)0ULL);
v___x_1353_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImportSrcs_spec__0(v_a_1346_, v_fst_1349_, v_sz_1351_, v___x_1352_, v___x_1350_);
lean_dec(v_fst_1349_);
if (lean_obj_tag(v___x_1353_) == 0)
{
lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1360_; 
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1353_);
if (v_isSharedCheck_1360_ == 0)
{
lean_object* v_unused_1361_; 
v_unused_1361_ = lean_ctor_get(v___x_1353_, 0);
lean_dec(v_unused_1361_);
v___x_1355_ = v___x_1353_;
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
else
{
lean_dec(v___x_1353_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1358_; 
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 0, v___x_1350_);
v___x_1358_ = v___x_1355_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v___x_1350_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
else
{
return v___x_1353_;
}
}
else
{
lean_object* v_a_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1369_; 
lean_dec(v_a_1346_);
v_a_1362_ = lean_ctor_get(v___x_1347_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1364_ = v___x_1347_;
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_a_1362_);
lean_dec(v___x_1347_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1367_; 
if (v_isShared_1365_ == 0)
{
v___x_1367_ = v___x_1364_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_a_1362_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
}
else
{
lean_object* v_a_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1377_; 
lean_dec(v_fileName_1343_);
lean_dec_ref(v_input_1342_);
v_a_1370_ = lean_ctor_get(v___x_1345_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1372_ = v___x_1345_;
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_a_1370_);
lean_dec(v___x_1345_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1375_; 
if (v_isShared_1373_ == 0)
{
v___x_1375_ = v___x_1372_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_a_1370_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_printImportSrcs___boxed(lean_object* v_input_1378_, lean_object* v_fileName_1379_, lean_object* v_a_1380_){
_start:
{
lean_object* v_res_1381_; 
v_res_1381_ = l_Lean_Elab_printImportSrcs(v_input_1378_, v_fileName_1379_);
return v_res_1381_;
}
}
lean_object* runtime_initialize_Lean_Parser_Module(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_ModPkgExt(uint8_t builtin);
lean_object* runtime_initialize_Lean_DeprecatedModule(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Modify(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Import(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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

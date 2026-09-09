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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
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
lean_object* v___x_66_; lean_object* v_v_67_; lean_object* v___x_68_; lean_object* v_bs_x27_69_; lean_object* v___y_71_; lean_object* v___y_77_; lean_object* v___y_78_; uint8_t v___y_79_; uint8_t v___y_80_; uint8_t v___y_81_; lean_object* v___y_86_; lean_object* v___y_87_; uint8_t v___y_88_; uint8_t v___y_89_; uint8_t v___y_90_; lean_object* v___y_92_; lean_object* v___y_93_; uint8_t v___y_94_; lean_object* v___y_95_; uint8_t v___y_96_; uint8_t v___x_98_; 
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
v___y_93_ = v___x_112_;
v___y_94_ = v___x_107_;
v___y_95_ = v___y_103_;
v___y_96_ = v___x_113_;
goto v___jp_91_;
}
else
{
lean_dec_ref_known(v_allTk_104_, 1);
v___y_92_ = v___y_102_;
v___y_93_ = v___x_112_;
v___y_94_ = v___x_107_;
v___y_95_ = v___y_103_;
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
lean_ctor_set(v___x_83_, 0, v___y_78_);
lean_ctor_set_uint8(v___x_83_, sizeof(void*)*1, v___y_80_);
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
lean_ctor_set(v___x_84_, 0, v___y_78_);
lean_ctor_set_uint8(v___x_84_, sizeof(void*)*1, v___y_80_);
lean_ctor_set_uint8(v___x_84_, sizeof(void*)*1 + 1, v___y_81_);
lean_ctor_set_uint8(v___x_84_, sizeof(void*)*1 + 2, v___y_79_);
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
v___y_79_ = v___y_88_;
v___y_80_ = v___y_89_;
v___y_81_ = v___y_88_;
goto v___jp_76_;
}
else
{
v___y_77_ = v___y_86_;
v___y_78_ = v___y_87_;
v___y_79_ = v___y_88_;
v___y_80_ = v___y_89_;
v___y_81_ = v___y_90_;
goto v___jp_76_;
}
}
v___jp_91_:
{
if (lean_obj_tag(v___y_95_) == 0)
{
uint8_t v___x_97_; 
v___x_97_ = 0;
v___y_86_ = v___y_92_;
v___y_87_ = v___y_93_;
v___y_88_ = v___y_94_;
v___y_89_ = v___y_96_;
v___y_90_ = v___x_97_;
goto v___jp_85_;
}
else
{
lean_dec_ref_known(v___y_95_, 1);
if (v___y_94_ == 0)
{
v___y_86_ = v___y_92_;
v___y_87_ = v___y_93_;
v___y_88_ = v___y_94_;
v___y_89_ = v___y_96_;
v___y_90_ = v___y_94_;
goto v___jp_85_;
}
else
{
v___y_77_ = v___y_92_;
v___y_78_ = v___y_93_;
v___y_79_ = v___y_94_;
v___y_80_ = v___y_96_;
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
uint8_t v___x_1473__boxed_165_; size_t v_sz_boxed_166_; size_t v_i_boxed_167_; lean_object* v_res_168_; 
v___x_1473__boxed_165_ = lean_unbox(v___x_161_);
v_sz_boxed_166_ = lean_unbox_usize(v_sz_162_);
lean_dec(v_sz_162_);
v_i_boxed_167_ = lean_unbox_usize(v_i_163_);
lean_dec(v_i_163_);
v_res_168_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2(v_moduleTk_160_, v___x_1473__boxed_165_, v_sz_boxed_166_, v_i_boxed_167_, v_bs_164_);
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
lean_object* v_pos_294_; lean_object* v_startInclusive_295_; lean_object* v_endExclusive_296_; lean_object* v___x_297_; uint8_t v_decide_298_; 
v_pos_294_ = lean_ctor_get(v_a_291_, 0);
lean_inc(v_pos_294_);
lean_dec_ref_known(v_a_291_, 1);
v_startInclusive_295_ = lean_ctor_get(v_s_290_, 1);
v_endExclusive_296_ = lean_ctor_get(v_s_290_, 2);
v___x_297_ = lean_nat_sub(v_endExclusive_296_, v_startInclusive_295_);
v_decide_298_ = lean_nat_dec_eq(v_pos_294_, v___x_297_);
lean_dec(v___x_297_);
lean_dec(v_pos_294_);
if (v_decide_298_ == 0)
{
uint8_t v___x_299_; 
v___x_299_ = 1;
return v___x_299_;
}
else
{
return v_decide_298_;
}
}
case 1:
{
lean_object* v_pos_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_313_; 
v_pos_300_ = lean_ctor_get(v_a_291_, 0);
v_isSharedCheck_313_ = !lean_is_exclusive(v_a_291_);
if (v_isSharedCheck_313_ == 0)
{
v___x_302_ = v_a_291_;
v_isShared_303_ = v_isSharedCheck_313_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_pos_300_);
lean_dec(v_a_291_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_313_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v_str_304_; lean_object* v_startInclusive_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_310_; 
v_str_304_ = lean_ctor_get(v_s_290_, 0);
v_startInclusive_305_ = lean_ctor_get(v_s_290_, 1);
v___x_306_ = lean_nat_add(v_startInclusive_305_, v_pos_300_);
lean_dec(v_pos_300_);
v___x_307_ = lean_string_utf8_next_fast(v_str_304_, v___x_306_);
lean_dec(v___x_306_);
v___x_308_ = lean_nat_sub(v___x_307_, v_startInclusive_305_);
if (v_isShared_303_ == 0)
{
lean_ctor_set_tag(v___x_302_, 0);
lean_ctor_set(v___x_302_, 0, v___x_308_);
v___x_310_ = v___x_302_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v___x_308_);
v___x_310_ = v_reuseFailAlloc_312_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
v_a_291_ = v___x_310_;
v_b_292_ = v___x_293_;
goto _start;
}
}
}
case 2:
{
lean_object* v_needle_314_; lean_object* v_table_315_; lean_object* v_stackPos_316_; lean_object* v_needlePos_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_372_; 
v_needle_314_ = lean_ctor_get(v_a_291_, 0);
v_table_315_ = lean_ctor_get(v_a_291_, 1);
v_stackPos_316_ = lean_ctor_get(v_a_291_, 2);
v_needlePos_317_ = lean_ctor_get(v_a_291_, 3);
v_isSharedCheck_372_ = !lean_is_exclusive(v_a_291_);
if (v_isSharedCheck_372_ == 0)
{
v___x_319_ = v_a_291_;
v_isShared_320_ = v_isSharedCheck_372_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_needlePos_317_);
lean_inc(v_stackPos_316_);
lean_inc(v_table_315_);
lean_inc(v_needle_314_);
lean_dec(v_a_291_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_372_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v_str_321_; lean_object* v_startInclusive_322_; lean_object* v_endExclusive_323_; lean_object* v_str_324_; lean_object* v_startInclusive_325_; lean_object* v_endExclusive_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; uint8_t v___x_331_; 
v_str_321_ = lean_ctor_get(v_needle_314_, 0);
v_startInclusive_322_ = lean_ctor_get(v_needle_314_, 1);
v_endExclusive_323_ = lean_ctor_get(v_needle_314_, 2);
v_str_324_ = lean_ctor_get(v_s_290_, 0);
v_startInclusive_325_ = lean_ctor_get(v_s_290_, 1);
v_endExclusive_326_ = lean_ctor_get(v_s_290_, 2);
v___x_327_ = lean_nat_sub(v_stackPos_316_, v_needlePos_317_);
v___x_328_ = lean_nat_sub(v_endExclusive_323_, v_startInclusive_322_);
v___x_329_ = lean_nat_add(v___x_327_, v___x_328_);
v___x_330_ = lean_nat_sub(v_endExclusive_326_, v_startInclusive_325_);
v___x_331_ = lean_nat_dec_le(v___x_329_, v___x_330_);
lean_dec(v___x_329_);
if (v___x_331_ == 0)
{
lean_object* v___x_332_; lean_object* v___x_333_; uint8_t v___x_334_; 
lean_dec(v___x_328_);
lean_del_object(v___x_319_);
lean_dec(v_needlePos_317_);
lean_dec(v_stackPos_316_);
lean_dec_ref(v_table_315_);
lean_dec_ref(v_needle_314_);
v___x_332_ = lean_unsigned_to_nat(1u);
v___x_333_ = lean_nat_add(v___x_327_, v___x_332_);
lean_dec(v___x_327_);
v___x_334_ = lean_nat_dec_le(v___x_333_, v___x_330_);
lean_dec(v___x_330_);
lean_dec(v___x_333_);
if (v___x_334_ == 0)
{
return v_b_292_;
}
else
{
lean_object* v___x_335_; 
v___x_335_ = lean_box(3);
v_a_291_ = v___x_335_;
v_b_292_ = v___x_293_;
goto _start;
}
}
else
{
lean_object* v___x_337_; uint8_t v_stackByte_338_; lean_object* v___x_339_; uint8_t v_patByte_340_; uint8_t v___x_341_; 
lean_dec(v___x_330_);
lean_dec(v___x_327_);
v___x_337_ = lean_nat_add(v_startInclusive_325_, v_stackPos_316_);
v_stackByte_338_ = lean_string_get_byte_fast(v_str_324_, v___x_337_);
v___x_339_ = lean_nat_add(v_startInclusive_322_, v_needlePos_317_);
v_patByte_340_ = lean_string_get_byte_fast(v_str_321_, v___x_339_);
v___x_341_ = lean_uint8_dec_eq(v_stackByte_338_, v_patByte_340_);
if (v___x_341_ == 0)
{
lean_object* v___x_342_; uint8_t v_decide_343_; 
lean_dec(v___x_328_);
v___x_342_ = lean_unsigned_to_nat(0u);
v_decide_343_ = lean_nat_dec_eq(v_needlePos_317_, v___x_342_);
if (v_decide_343_ == 0)
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v_newNeedlePos_346_; uint8_t v___x_347_; 
v___x_344_ = lean_unsigned_to_nat(1u);
v___x_345_ = lean_nat_sub(v_needlePos_317_, v___x_344_);
lean_dec(v_needlePos_317_);
v_newNeedlePos_346_ = lean_array_fget_borrowed(v_table_315_, v___x_345_);
lean_dec(v___x_345_);
v___x_347_ = lean_nat_dec_eq(v_newNeedlePos_346_, v___x_342_);
if (v___x_347_ == 0)
{
lean_object* v___x_349_; 
lean_inc(v_newNeedlePos_346_);
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 3, v_newNeedlePos_346_);
v___x_349_ = v___x_319_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v_needle_314_);
lean_ctor_set(v_reuseFailAlloc_351_, 1, v_table_315_);
lean_ctor_set(v_reuseFailAlloc_351_, 2, v_stackPos_316_);
lean_ctor_set(v_reuseFailAlloc_351_, 3, v_newNeedlePos_346_);
v___x_349_ = v_reuseFailAlloc_351_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
v_a_291_ = v___x_349_;
v_b_292_ = v___x_293_;
goto _start;
}
}
else
{
lean_object* v_nextStackPos_352_; lean_object* v___x_354_; 
v_nextStackPos_352_ = l_String_Slice_posGE___redArg(v_s_290_, v_stackPos_316_);
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 3, v___x_342_);
lean_ctor_set(v___x_319_, 2, v_nextStackPos_352_);
v___x_354_ = v___x_319_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_needle_314_);
lean_ctor_set(v_reuseFailAlloc_356_, 1, v_table_315_);
lean_ctor_set(v_reuseFailAlloc_356_, 2, v_nextStackPos_352_);
lean_ctor_set(v_reuseFailAlloc_356_, 3, v___x_342_);
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
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v_nextStackPos_359_; lean_object* v___x_361_; 
lean_dec(v_needlePos_317_);
v___x_357_ = lean_unsigned_to_nat(1u);
v___x_358_ = lean_nat_add(v_stackPos_316_, v___x_357_);
lean_dec(v_stackPos_316_);
v_nextStackPos_359_ = l_String_Slice_posGE___redArg(v_s_290_, v___x_358_);
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 3, v___x_342_);
lean_ctor_set(v___x_319_, 2, v_nextStackPos_359_);
v___x_361_ = v___x_319_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v_needle_314_);
lean_ctor_set(v_reuseFailAlloc_363_, 1, v_table_315_);
lean_ctor_set(v_reuseFailAlloc_363_, 2, v_nextStackPos_359_);
lean_ctor_set(v_reuseFailAlloc_363_, 3, v___x_342_);
v___x_361_ = v_reuseFailAlloc_363_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
v_a_291_ = v___x_361_;
v_b_292_ = v___x_293_;
goto _start;
}
}
}
else
{
lean_object* v___x_364_; lean_object* v_nextNeedlePos_365_; uint8_t v_decide_366_; 
v___x_364_ = lean_unsigned_to_nat(1u);
v_nextNeedlePos_365_ = lean_nat_add(v_needlePos_317_, v___x_364_);
lean_dec(v_needlePos_317_);
v_decide_366_ = lean_nat_dec_eq(v_nextNeedlePos_365_, v___x_328_);
lean_dec(v___x_328_);
if (v_decide_366_ == 0)
{
lean_object* v_nextStackPos_367_; lean_object* v___x_369_; 
v_nextStackPos_367_ = lean_nat_add(v_stackPos_316_, v___x_364_);
lean_dec(v_stackPos_316_);
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 3, v_nextNeedlePos_365_);
lean_ctor_set(v___x_319_, 2, v_nextStackPos_367_);
v___x_369_ = v___x_319_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v_needle_314_);
lean_ctor_set(v_reuseFailAlloc_371_, 1, v_table_315_);
lean_ctor_set(v_reuseFailAlloc_371_, 2, v_nextStackPos_367_);
lean_ctor_set(v_reuseFailAlloc_371_, 3, v_nextNeedlePos_365_);
v___x_369_ = v_reuseFailAlloc_371_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
v_a_291_ = v___x_369_;
goto _start;
}
}
else
{
lean_dec(v_nextNeedlePos_365_);
lean_del_object(v___x_319_);
lean_dec(v_stackPos_316_);
lean_dec_ref(v_table_315_);
lean_dec_ref(v_needle_314_);
return v_decide_366_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_spec__2___redArg___boxed(lean_object* v_s_373_, lean_object* v_a_374_, lean_object* v_b_375_){
_start:
{
uint8_t v_b_boxed_376_; uint8_t v_res_377_; lean_object* v_r_378_; 
v_b_boxed_376_ = lean_unbox(v_b_375_);
v_res_377_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_spec__2___redArg(v_s_373_, v_a_374_, v_b_boxed_376_);
lean_dec_ref(v_s_373_);
v_r_378_ = lean_box(v_res_377_);
return v_r_378_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__1(void){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_380_ = ((lean_object*)(l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__0));
v___x_381_ = lean_string_utf8_byte_size(v___x_380_);
return v___x_381_;
}
}
static uint8_t _init_l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__2(void){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; uint8_t v___x_384_; 
v___x_382_ = lean_unsigned_to_nat(0u);
v___x_383_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__1, &l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__1_once, _init_l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__1);
v___x_384_ = lean_nat_dec_eq(v___x_383_, v___x_382_);
return v___x_384_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__3(void){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_385_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__1, &l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__1_once, _init_l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__1);
v___x_386_ = lean_unsigned_to_nat(0u);
v___x_387_ = ((lean_object*)(l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__0));
v___x_388_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_388_, 0, v___x_387_);
lean_ctor_set(v___x_388_, 1, v___x_386_);
lean_ctor_set(v___x_388_, 2, v___x_385_);
return v___x_388_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__4(void){
_start:
{
lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_389_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__3, &l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__3_once, _init_l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__3);
v___x_390_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_389_);
return v___x_390_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__5(void){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_391_ = lean_unsigned_to_nat(0u);
v___x_392_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__4, &l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__4_once, _init_l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__4);
v___x_393_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__3, &l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__3_once, _init_l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__3);
v___x_394_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_394_, 0, v___x_393_);
lean_ctor_set(v___x_394_, 1, v___x_392_);
lean_ctor_set(v___x_394_, 2, v___x_391_);
lean_ctor_set(v___x_394_, 3, v___x_391_);
return v___x_394_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2(lean_object* v_s_397_){
_start:
{
lean_object* v___y_399_; uint8_t v___x_402_; 
v___x_402_ = lean_uint8_once(&l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__2, &l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__2_once, _init_l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__2);
if (v___x_402_ == 0)
{
lean_object* v___x_403_; 
v___x_403_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__5, &l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__5_once, _init_l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__5);
v___y_399_ = v___x_403_;
goto v___jp_398_;
}
else
{
lean_object* v___x_404_; 
v___x_404_ = ((lean_object*)(l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__6));
v___y_399_ = v___x_404_;
goto v___jp_398_;
}
v___jp_398_:
{
uint8_t v___x_400_; uint8_t v___x_401_; 
v___x_400_ = 0;
lean_inc(v___y_399_);
v___x_401_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_spec__2___redArg(v_s_397_, v___y_399_, v___x_400_);
return v___x_401_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___boxed(lean_object* v_s_405_){
_start:
{
uint8_t v_res_406_; lean_object* v_r_407_; 
v_res_406_ = l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2(v_s_405_);
lean_dec_ref(v_s_405_);
v_r_407_ = lean_box(v_res_406_);
return v_r_407_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkDeprecatedImports_spec__3(lean_object* v_as_408_, size_t v_sz_409_, size_t v_i_410_, lean_object* v_b_411_){
_start:
{
lean_object* v_a_413_; uint8_t v___x_417_; 
v___x_417_ = lean_usize_dec_lt(v_i_410_, v_sz_409_);
if (v___x_417_ == 0)
{
return v_b_411_;
}
else
{
lean_object* v_fst_418_; lean_object* v_snd_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_494_; 
v_fst_418_ = lean_ctor_get(v_b_411_, 0);
v_snd_419_ = lean_ctor_get(v_b_411_, 1);
v_isSharedCheck_494_ = !lean_is_exclusive(v_b_411_);
if (v_isSharedCheck_494_ == 0)
{
v___x_421_ = v_b_411_;
v_isShared_422_ = v_isSharedCheck_494_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_snd_419_);
lean_inc(v_fst_418_);
lean_dec(v_b_411_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_494_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_423_; lean_object* v_a_424_; lean_object* v___y_426_; lean_object* v_ignoreDeprecatedImports_427_; uint8_t v___x_439_; 
v___x_423_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__4));
v_a_424_ = lean_array_uget_borrowed(v_as_408_, v_i_410_);
lean_inc(v_a_424_);
v___x_439_ = l_Lean_Syntax_isOfKind(v_a_424_, v___x_423_);
if (v___x_439_ == 0)
{
lean_object* v___x_440_; 
lean_del_object(v___x_421_);
v___x_440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_440_, 0, v_fst_418_);
lean_ctor_set(v___x_440_, 1, v_snd_419_);
v_a_413_ = v___x_440_;
goto v___jp_412_;
}
else
{
lean_object* v___x_441_; lean_object* v___x_466_; lean_object* v___x_486_; uint8_t v___x_487_; 
v___x_441_ = lean_unsigned_to_nat(0u);
v___x_466_ = lean_unsigned_to_nat(1u);
v___x_486_ = l_Lean_Syntax_getArg(v_a_424_, v___x_441_);
v___x_487_ = l_Lean_Syntax_isNone(v___x_486_);
if (v___x_487_ == 0)
{
uint8_t v___x_488_; 
lean_inc(v___x_486_);
v___x_488_ = l_Lean_Syntax_matchesNull(v___x_486_, v___x_466_);
if (v___x_488_ == 0)
{
lean_object* v___x_489_; 
lean_dec(v___x_486_);
lean_del_object(v___x_421_);
v___x_489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_489_, 0, v_fst_418_);
lean_ctor_set(v___x_489_, 1, v_snd_419_);
v_a_413_ = v___x_489_;
goto v___jp_412_;
}
else
{
lean_object* v___x_490_; lean_object* v___x_491_; uint8_t v___x_492_; 
v___x_490_ = l_Lean_Syntax_getArg(v___x_486_, v___x_441_);
lean_dec(v___x_486_);
v___x_491_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__14));
v___x_492_ = l_Lean_Syntax_isOfKind(v___x_490_, v___x_491_);
if (v___x_492_ == 0)
{
lean_object* v___x_493_; 
lean_del_object(v___x_421_);
v___x_493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_493_, 0, v_fst_418_);
lean_ctor_set(v___x_493_, 1, v_snd_419_);
v_a_413_ = v___x_493_;
goto v___jp_412_;
}
else
{
goto v___jp_477_;
}
}
}
else
{
lean_dec(v___x_486_);
goto v___jp_477_;
}
v___jp_442_:
{
lean_object* v___x_443_; lean_object* v___x_444_; uint8_t v___x_445_; 
v___x_443_ = lean_unsigned_to_nat(5u);
v___x_444_ = l_Lean_Syntax_getArg(v_a_424_, v___x_443_);
v___x_445_ = l_Lean_Syntax_matchesNull(v___x_444_, v___x_441_);
if (v___x_445_ == 0)
{
lean_object* v___x_446_; 
lean_del_object(v___x_421_);
v___x_446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_446_, 0, v_fst_418_);
lean_ctor_set(v___x_446_, 1, v_snd_419_);
v_a_413_ = v___x_446_;
goto v___jp_412_;
}
else
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_447_ = lean_unsigned_to_nat(4u);
v___x_448_ = l_Lean_Syntax_getArg(v_a_424_, v___x_447_);
v___x_449_ = l_Lean_Syntax_getTrailing_x3f(v_a_424_);
if (lean_obj_tag(v___x_449_) == 0)
{
v___y_426_ = v___x_448_;
v_ignoreDeprecatedImports_427_ = v_fst_418_;
goto v___jp_425_;
}
else
{
lean_object* v_val_450_; lean_object* v_str_451_; lean_object* v_startPos_452_; lean_object* v_stopPos_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_465_; 
v_val_450_ = lean_ctor_get(v___x_449_, 0);
lean_inc(v_val_450_);
lean_dec_ref_known(v___x_449_, 1);
v_str_451_ = lean_ctor_get(v_val_450_, 0);
v_startPos_452_ = lean_ctor_get(v_val_450_, 1);
v_stopPos_453_ = lean_ctor_get(v_val_450_, 2);
v_isSharedCheck_465_ = !lean_is_exclusive(v_val_450_);
if (v_isSharedCheck_465_ == 0)
{
v___x_455_ = v_val_450_;
v_isShared_456_ = v_isSharedCheck_465_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_stopPos_453_);
lean_inc(v_startPos_452_);
lean_inc(v_str_451_);
lean_dec(v_val_450_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_465_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_460_; 
v___x_457_ = lean_string_utf8_extract(v_str_451_, v_startPos_452_, v_stopPos_453_);
lean_dec(v_stopPos_453_);
lean_dec(v_startPos_452_);
lean_dec_ref(v_str_451_);
v___x_458_ = lean_string_utf8_byte_size(v___x_457_);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 2, v___x_458_);
lean_ctor_set(v___x_455_, 1, v___x_441_);
lean_ctor_set(v___x_455_, 0, v___x_457_);
v___x_460_ = v___x_455_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v___x_457_);
lean_ctor_set(v_reuseFailAlloc_464_, 1, v___x_441_);
lean_ctor_set(v_reuseFailAlloc_464_, 2, v___x_458_);
v___x_460_ = v_reuseFailAlloc_464_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
uint8_t v___x_461_; 
v___x_461_ = l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2(v___x_460_);
lean_dec_ref(v___x_460_);
if (v___x_461_ == 0)
{
v___y_426_ = v___x_448_;
v_ignoreDeprecatedImports_427_ = v_fst_418_;
goto v___jp_425_;
}
else
{
lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_462_ = l_Lean_TSyntax_getId(v___x_448_);
v___x_463_ = l_Lean_NameSet_insert(v_fst_418_, v___x_462_);
v___y_426_ = v___x_448_;
v_ignoreDeprecatedImports_427_ = v___x_463_;
goto v___jp_425_;
}
}
}
}
}
}
v___jp_467_:
{
lean_object* v___x_468_; lean_object* v___x_469_; uint8_t v___x_470_; 
v___x_468_ = lean_unsigned_to_nat(3u);
v___x_469_ = l_Lean_Syntax_getArg(v_a_424_, v___x_468_);
v___x_470_ = l_Lean_Syntax_isNone(v___x_469_);
if (v___x_470_ == 0)
{
uint8_t v___x_471_; 
lean_inc(v___x_469_);
v___x_471_ = l_Lean_Syntax_matchesNull(v___x_469_, v___x_466_);
if (v___x_471_ == 0)
{
lean_object* v___x_472_; 
lean_dec(v___x_469_);
lean_del_object(v___x_421_);
v___x_472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_472_, 0, v_fst_418_);
lean_ctor_set(v___x_472_, 1, v_snd_419_);
v_a_413_ = v___x_472_;
goto v___jp_412_;
}
else
{
lean_object* v___x_473_; lean_object* v___x_474_; uint8_t v___x_475_; 
v___x_473_ = l_Lean_Syntax_getArg(v___x_469_, v___x_441_);
lean_dec(v___x_469_);
v___x_474_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__10));
v___x_475_ = l_Lean_Syntax_isOfKind(v___x_473_, v___x_474_);
if (v___x_475_ == 0)
{
lean_object* v___x_476_; 
lean_del_object(v___x_421_);
v___x_476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_476_, 0, v_fst_418_);
lean_ctor_set(v___x_476_, 1, v_snd_419_);
v_a_413_ = v___x_476_;
goto v___jp_412_;
}
else
{
goto v___jp_442_;
}
}
}
else
{
lean_dec(v___x_469_);
goto v___jp_442_;
}
}
v___jp_477_:
{
lean_object* v___x_478_; uint8_t v___x_479_; 
v___x_478_ = l_Lean_Syntax_getArg(v_a_424_, v___x_466_);
v___x_479_ = l_Lean_Syntax_isNone(v___x_478_);
if (v___x_479_ == 0)
{
uint8_t v___x_480_; 
lean_inc(v___x_478_);
v___x_480_ = l_Lean_Syntax_matchesNull(v___x_478_, v___x_466_);
if (v___x_480_ == 0)
{
lean_object* v___x_481_; 
lean_dec(v___x_478_);
lean_del_object(v___x_421_);
v___x_481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_481_, 0, v_fst_418_);
lean_ctor_set(v___x_481_, 1, v_snd_419_);
v_a_413_ = v___x_481_;
goto v___jp_412_;
}
else
{
lean_object* v___x_482_; lean_object* v___x_483_; uint8_t v___x_484_; 
v___x_482_ = l_Lean_Syntax_getArg(v___x_478_, v___x_441_);
lean_dec(v___x_478_);
v___x_483_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__12));
v___x_484_ = l_Lean_Syntax_isOfKind(v___x_482_, v___x_483_);
if (v___x_484_ == 0)
{
lean_object* v___x_485_; 
lean_del_object(v___x_421_);
v___x_485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_485_, 0, v_fst_418_);
lean_ctor_set(v___x_485_, 1, v_snd_419_);
v_a_413_ = v___x_485_;
goto v___jp_412_;
}
else
{
goto v___jp_467_;
}
}
}
else
{
lean_dec(v___x_478_);
goto v___jp_467_;
}
}
}
v___jp_425_:
{
uint8_t v___x_428_; lean_object* v___x_429_; 
v___x_428_ = 0;
v___x_429_ = l_Lean_Syntax_getPos_x3f(v_a_424_, v___x_428_);
if (lean_obj_tag(v___x_429_) == 1)
{
lean_object* v_val_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_434_; 
v_val_430_ = lean_ctor_get(v___x_429_, 0);
lean_inc(v_val_430_);
lean_dec_ref_known(v___x_429_, 1);
v___x_431_ = l_Lean_TSyntax_getId(v___y_426_);
lean_dec(v___y_426_);
v___x_432_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_431_, v_val_430_, v_snd_419_);
if (v_isShared_422_ == 0)
{
lean_ctor_set(v___x_421_, 1, v___x_432_);
lean_ctor_set(v___x_421_, 0, v_ignoreDeprecatedImports_427_);
v___x_434_ = v___x_421_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_ignoreDeprecatedImports_427_);
lean_ctor_set(v_reuseFailAlloc_435_, 1, v___x_432_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
v_a_413_ = v___x_434_;
goto v___jp_412_;
}
}
else
{
lean_object* v___x_437_; 
lean_dec(v___x_429_);
lean_dec(v___y_426_);
if (v_isShared_422_ == 0)
{
lean_ctor_set(v___x_421_, 0, v_ignoreDeprecatedImports_427_);
v___x_437_ = v___x_421_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_ignoreDeprecatedImports_427_);
lean_ctor_set(v_reuseFailAlloc_438_, 1, v_snd_419_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
v_a_413_ = v___x_437_;
goto v___jp_412_;
}
}
}
}
}
v___jp_412_:
{
size_t v___x_414_; size_t v___x_415_; 
v___x_414_ = ((size_t)1ULL);
v___x_415_ = lean_usize_add(v_i_410_, v___x_414_);
v_i_410_ = v___x_415_;
v_b_411_ = v_a_413_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkDeprecatedImports_spec__3___boxed(lean_object* v_as_495_, lean_object* v_sz_496_, lean_object* v_i_497_, lean_object* v_b_498_){
_start:
{
size_t v_sz_boxed_499_; size_t v_i_boxed_500_; lean_object* v_res_501_; 
v_sz_boxed_499_ = lean_unbox_usize(v_sz_496_);
lean_dec(v_sz_496_);
v_i_boxed_500_ = lean_unbox_usize(v_i_497_);
lean_dec(v_i_497_);
v_res_501_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkDeprecatedImports_spec__3(v_as_495_, v_sz_boxed_499_, v_i_boxed_500_, v_b_498_);
lean_dec_ref(v_as_495_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4_spec__5(lean_object* v_o_505_, lean_object* v_k_506_, uint8_t v_v_507_){
_start:
{
lean_object* v_map_508_; uint8_t v_hasTrace_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_523_; 
v_map_508_ = lean_ctor_get(v_o_505_, 0);
v_hasTrace_509_ = lean_ctor_get_uint8(v_o_505_, sizeof(void*)*1);
v_isSharedCheck_523_ = !lean_is_exclusive(v_o_505_);
if (v_isSharedCheck_523_ == 0)
{
v___x_511_ = v_o_505_;
v_isShared_512_ = v_isSharedCheck_523_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_map_508_);
lean_dec(v_o_505_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_523_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_513_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_513_, 0, v_v_507_);
lean_inc(v_k_506_);
v___x_514_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_506_, v___x_513_, v_map_508_);
if (v_hasTrace_509_ == 0)
{
lean_object* v___x_515_; uint8_t v___x_516_; lean_object* v___x_518_; 
v___x_515_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4_spec__5___closed__1));
v___x_516_ = l_Lean_Name_isPrefixOf(v___x_515_, v_k_506_);
lean_dec(v_k_506_);
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 0, v___x_514_);
v___x_518_ = v___x_511_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v___x_514_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
lean_ctor_set_uint8(v___x_518_, sizeof(void*)*1, v___x_516_);
return v___x_518_;
}
}
else
{
lean_object* v___x_521_; 
lean_dec(v_k_506_);
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 0, v___x_514_);
v___x_521_ = v___x_511_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v___x_514_);
lean_ctor_set_uint8(v_reuseFailAlloc_522_, sizeof(void*)*1, v_hasTrace_509_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4_spec__5___boxed(lean_object* v_o_524_, lean_object* v_k_525_, lean_object* v_v_526_){
_start:
{
uint8_t v_v_boxed_527_; lean_object* v_res_528_; 
v_v_boxed_527_ = lean_unbox(v_v_526_);
v_res_528_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4_spec__5(v_o_524_, v_k_525_, v_v_boxed_527_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4(lean_object* v_opts_529_, lean_object* v_opt_530_, uint8_t v_val_531_){
_start:
{
lean_object* v_name_532_; lean_object* v___x_533_; 
v_name_532_ = lean_ctor_get(v_opt_530_, 0);
lean_inc(v_name_532_);
lean_dec_ref(v_opt_530_);
v___x_533_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4_spec__5(v_opts_529_, v_name_532_, v_val_531_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4___boxed(lean_object* v_opts_534_, lean_object* v_opt_535_, lean_object* v_val_536_){
_start:
{
uint8_t v_val_boxed_537_; lean_object* v_res_538_; 
v_val_boxed_537_ = lean_unbox(v_val_536_);
v_res_538_ = l_Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4(v_opts_534_, v_opt_535_, v_val_boxed_537_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1(lean_object* v_ignoreDeprecatedImports_544_, lean_object* v_env_545_, lean_object* v_inputCtx_546_, lean_object* v_importPositions_547_, lean_object* v_startPos_548_, lean_object* v_as_549_, size_t v_i_550_, size_t v_stop_551_, lean_object* v_b_552_){
_start:
{
lean_object* v___y_554_; uint8_t v___x_558_; 
v___x_558_ = lean_usize_dec_eq(v_i_550_, v_stop_551_);
if (v___x_558_ == 0)
{
lean_object* v___x_559_; lean_object* v_module_560_; uint8_t v___x_561_; 
v___x_559_ = lean_array_uget_borrowed(v_as_549_, v_i_550_);
v_module_560_ = lean_ctor_get(v___x_559_, 0);
v___x_561_ = l_Lean_NameSet_contains(v_ignoreDeprecatedImports_544_, v_module_560_);
if (v___x_561_ == 0)
{
lean_object* v___x_562_; 
v___x_562_ = l_Lean_Environment_getModuleIdx_x3f(v_env_545_, v_module_560_);
if (lean_obj_tag(v___x_562_) == 0)
{
v___y_554_ = v_b_552_;
goto v___jp_553_;
}
else
{
lean_object* v_val_563_; lean_object* v___x_564_; 
v_val_563_ = lean_ctor_get(v___x_562_, 0);
lean_inc(v_val_563_);
lean_dec_ref_known(v___x_562_, 1);
v___x_564_ = l_Lean_Environment_getDeprecatedModuleByIdx_x3f(v_env_545_, v_val_563_);
if (lean_obj_tag(v___x_564_) == 0)
{
lean_dec(v_val_563_);
v___y_554_ = v_b_552_;
goto v___jp_553_;
}
else
{
lean_object* v_val_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_588_; 
v_val_565_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_588_ == 0)
{
v___x_567_ = v___x_564_;
v_isShared_568_ = v_isSharedCheck_588_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_val_565_);
lean_dec(v___x_564_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_588_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___y_570_; lean_object* v___x_586_; 
v___x_586_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_importPositions_547_, v_module_560_);
if (lean_obj_tag(v___x_586_) == 0)
{
lean_inc(v_startPos_548_);
v___y_570_ = v_startPos_548_;
goto v___jp_569_;
}
else
{
lean_object* v_val_587_; 
v_val_587_ = lean_ctor_get(v___x_586_, 0);
lean_inc(v_val_587_);
lean_dec_ref_known(v___x_586_, 1);
v___y_570_ = v_val_587_;
goto v___jp_569_;
}
v___jp_569_:
{
lean_object* v_fileName_571_; lean_object* v_fileMap_572_; lean_object* v___x_573_; lean_object* v___x_574_; uint8_t v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_580_; 
v_fileName_571_ = lean_ctor_get(v_inputCtx_546_, 1);
v_fileMap_572_ = lean_ctor_get(v_inputCtx_546_, 2);
lean_inc_ref(v_fileMap_572_);
v___x_573_ = l_Lean_FileMap_toPosition(v_fileMap_572_, v___y_570_);
lean_dec(v___y_570_);
v___x_574_ = lean_box(0);
v___x_575_ = 1;
v___x_576_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___closed__0));
v___x_577_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___closed__2));
lean_inc(v_module_560_);
v___x_578_ = l_Lean_formatDeprecatedModuleWarning(v_env_545_, v_val_563_, v_module_560_, v_val_565_);
lean_dec(v_val_563_);
if (v_isShared_568_ == 0)
{
lean_ctor_set_tag(v___x_567_, 3);
lean_ctor_set(v___x_567_, 0, v___x_578_);
v___x_580_ = v___x_567_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v___x_578_);
v___x_580_ = v_reuseFailAlloc_585_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_581_ = l_Lean_MessageData_ofFormat(v___x_580_);
v___x_582_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_582_, 0, v___x_577_);
lean_ctor_set(v___x_582_, 1, v___x_581_);
lean_inc_ref(v_fileName_571_);
v___x_583_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_583_, 0, v_fileName_571_);
lean_ctor_set(v___x_583_, 1, v___x_573_);
lean_ctor_set(v___x_583_, 2, v___x_574_);
lean_ctor_set(v___x_583_, 3, v___x_576_);
lean_ctor_set(v___x_583_, 4, v___x_582_);
lean_ctor_set_uint8(v___x_583_, sizeof(void*)*5, v___x_561_);
lean_ctor_set_uint8(v___x_583_, sizeof(void*)*5 + 1, v___x_575_);
lean_ctor_set_uint8(v___x_583_, sizeof(void*)*5 + 2, v___x_561_);
v___x_584_ = l_Lean_MessageLog_add(v___x_583_, v_b_552_);
v___y_554_ = v___x_584_;
goto v___jp_553_;
}
}
}
}
}
}
else
{
v___y_554_ = v_b_552_;
goto v___jp_553_;
}
}
else
{
lean_dec(v_startPos_548_);
lean_dec_ref(v_inputCtx_546_);
return v_b_552_;
}
v___jp_553_:
{
size_t v___x_555_; size_t v___x_556_; 
v___x_555_ = ((size_t)1ULL);
v___x_556_ = lean_usize_add(v_i_550_, v___x_555_);
v_i_550_ = v___x_556_;
v_b_552_ = v___y_554_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___boxed(lean_object* v_ignoreDeprecatedImports_589_, lean_object* v_env_590_, lean_object* v_inputCtx_591_, lean_object* v_importPositions_592_, lean_object* v_startPos_593_, lean_object* v_as_594_, lean_object* v_i_595_, lean_object* v_stop_596_, lean_object* v_b_597_){
_start:
{
size_t v_i_boxed_598_; size_t v_stop_boxed_599_; lean_object* v_res_600_; 
v_i_boxed_598_ = lean_unbox_usize(v_i_595_);
lean_dec(v_i_595_);
v_stop_boxed_599_ = lean_unbox_usize(v_stop_596_);
lean_dec(v_stop_596_);
v_res_600_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1(v_ignoreDeprecatedImports_589_, v_env_590_, v_inputCtx_591_, v_importPositions_592_, v_startPos_593_, v_as_594_, v_i_boxed_598_, v_stop_boxed_599_, v_b_597_);
lean_dec_ref(v_as_594_);
lean_dec(v_importPositions_592_);
lean_dec_ref(v_env_590_);
lean_dec(v_ignoreDeprecatedImports_589_);
return v_res_600_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedImports___closed__0(void){
_start:
{
lean_object* v_importPositions_601_; lean_object* v_ignoreDeprecatedImports_602_; lean_object* v___x_603_; 
v_importPositions_601_ = lean_box(1);
v_ignoreDeprecatedImports_602_ = l_Lean_NameSet_empty;
v___x_603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_603_, 0, v_ignoreDeprecatedImports_602_);
lean_ctor_set(v___x_603_, 1, v_importPositions_601_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedImports(lean_object* v_env_604_, lean_object* v_imports_605_, lean_object* v_opts_606_, lean_object* v_inputCtx_607_, lean_object* v_startPos_608_, lean_object* v_messages_609_, lean_object* v_headerStx_x3f_610_, lean_object* v_origHeaderStx_x3f_611_){
_start:
{
lean_object* v_opts_613_; lean_object* v_ignoreDeprecatedImports_614_; lean_object* v_importPositions_615_; lean_object* v_ignoreDeprecatedImports_628_; lean_object* v_importPositions_629_; lean_object* v___y_631_; lean_object* v_opts_632_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_666_; lean_object* v___y_667_; lean_object* v___y_668_; lean_object* v___y_669_; lean_object* v___y_670_; lean_object* v_moduleTk_671_; lean_object* v_val_681_; 
v_ignoreDeprecatedImports_628_ = l_Lean_NameSet_empty;
v_importPositions_629_ = lean_box(1);
if (lean_obj_tag(v_origHeaderStx_x3f_611_) == 0)
{
if (lean_obj_tag(v_headerStx_x3f_610_) == 1)
{
lean_object* v_val_698_; 
v_val_698_ = lean_ctor_get(v_headerStx_x3f_610_, 0);
lean_inc(v_val_698_);
lean_dec_ref_known(v_headerStx_x3f_610_, 1);
v_val_681_ = v_val_698_;
goto v___jp_680_;
}
else
{
lean_dec(v_headerStx_x3f_610_);
v_opts_613_ = v_opts_606_;
v_ignoreDeprecatedImports_614_ = v_ignoreDeprecatedImports_628_;
v_importPositions_615_ = v_importPositions_629_;
goto v___jp_612_;
}
}
else
{
lean_object* v_val_699_; 
lean_dec(v_headerStx_x3f_610_);
v_val_699_ = lean_ctor_get(v_origHeaderStx_x3f_611_, 0);
lean_inc(v_val_699_);
lean_dec_ref_known(v_origHeaderStx_x3f_611_, 1);
v_val_681_ = v_val_699_;
goto v___jp_680_;
}
v___jp_612_:
{
lean_object* v___x_616_; uint8_t v___x_617_; 
v___x_616_ = l_Lean_linter_deprecated_module;
v___x_617_ = l_Lean_Option_get___at___00Lean_Elab_checkDeprecatedImports_spec__0(v_opts_613_, v___x_616_);
lean_dec_ref(v_opts_613_);
if (v___x_617_ == 0)
{
lean_dec(v_importPositions_615_);
lean_dec(v_ignoreDeprecatedImports_614_);
lean_dec(v_startPos_608_);
lean_dec_ref(v_inputCtx_607_);
return v_messages_609_;
}
else
{
lean_object* v___x_618_; lean_object* v___x_619_; uint8_t v___x_620_; 
v___x_618_ = lean_unsigned_to_nat(0u);
v___x_619_ = lean_array_get_size(v_imports_605_);
v___x_620_ = lean_nat_dec_lt(v___x_618_, v___x_619_);
if (v___x_620_ == 0)
{
lean_dec(v_importPositions_615_);
lean_dec(v_ignoreDeprecatedImports_614_);
lean_dec(v_startPos_608_);
lean_dec_ref(v_inputCtx_607_);
return v_messages_609_;
}
else
{
uint8_t v___x_621_; 
v___x_621_ = lean_nat_dec_le(v___x_619_, v___x_619_);
if (v___x_621_ == 0)
{
if (v___x_620_ == 0)
{
lean_dec(v_importPositions_615_);
lean_dec(v_ignoreDeprecatedImports_614_);
lean_dec(v_startPos_608_);
lean_dec_ref(v_inputCtx_607_);
return v_messages_609_;
}
else
{
size_t v___x_622_; size_t v___x_623_; lean_object* v___x_624_; 
v___x_622_ = ((size_t)0ULL);
v___x_623_ = lean_usize_of_nat(v___x_619_);
v___x_624_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1(v_ignoreDeprecatedImports_614_, v_env_604_, v_inputCtx_607_, v_importPositions_615_, v_startPos_608_, v_imports_605_, v___x_622_, v___x_623_, v_messages_609_);
lean_dec(v_importPositions_615_);
lean_dec(v_ignoreDeprecatedImports_614_);
return v___x_624_;
}
}
else
{
size_t v___x_625_; size_t v___x_626_; lean_object* v___x_627_; 
v___x_625_ = ((size_t)0ULL);
v___x_626_ = lean_usize_of_nat(v___x_619_);
v___x_627_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1(v_ignoreDeprecatedImports_614_, v_env_604_, v_inputCtx_607_, v_importPositions_615_, v_startPos_608_, v_imports_605_, v___x_625_, v___x_626_, v_messages_609_);
lean_dec(v_importPositions_615_);
lean_dec(v_ignoreDeprecatedImports_614_);
return v___x_627_;
}
}
}
}
v___jp_630_:
{
lean_object* v___x_633_; size_t v_sz_634_; size_t v___x_635_; lean_object* v___x_636_; lean_object* v_fst_637_; lean_object* v_snd_638_; 
v___x_633_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedImports___closed__0, &l_Lean_Elab_checkDeprecatedImports___closed__0_once, _init_l_Lean_Elab_checkDeprecatedImports___closed__0);
v_sz_634_ = lean_array_size(v___y_631_);
v___x_635_ = ((size_t)0ULL);
v___x_636_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkDeprecatedImports_spec__3(v___y_631_, v_sz_634_, v___x_635_, v___x_633_);
lean_dec_ref(v___y_631_);
v_fst_637_ = lean_ctor_get(v___x_636_, 0);
lean_inc(v_fst_637_);
v_snd_638_ = lean_ctor_get(v___x_636_, 1);
lean_inc(v_snd_638_);
lean_dec_ref(v___x_636_);
v_opts_613_ = v_opts_632_;
v_ignoreDeprecatedImports_614_ = v_fst_637_;
v_importPositions_615_ = v_snd_638_;
goto v___jp_612_;
}
v___jp_639_:
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v_importsStx_645_; 
v___x_643_ = lean_unsigned_to_nat(2u);
v___x_644_ = l_Lean_Syntax_getArg(v___y_640_, v___x_643_);
lean_dec(v___y_640_);
v_importsStx_645_ = l_Lean_Syntax_getArgs(v___x_644_);
lean_dec(v___x_644_);
if (lean_obj_tag(v___y_641_) == 0)
{
lean_dec(v___y_642_);
v___y_631_ = v_importsStx_645_;
v_opts_632_ = v_opts_606_;
goto v___jp_630_;
}
else
{
lean_object* v_val_646_; lean_object* v___x_647_; 
v_val_646_ = lean_ctor_get(v___y_641_, 0);
lean_inc(v_val_646_);
lean_dec_ref_known(v___y_641_, 1);
v___x_647_ = l_Lean_Syntax_getTrailing_x3f(v_val_646_);
lean_dec(v_val_646_);
if (lean_obj_tag(v___x_647_) == 0)
{
lean_dec(v___y_642_);
v___y_631_ = v_importsStx_645_;
v_opts_632_ = v_opts_606_;
goto v___jp_630_;
}
else
{
lean_object* v_val_648_; lean_object* v_str_649_; lean_object* v_startPos_650_; lean_object* v_stopPos_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_664_; 
v_val_648_ = lean_ctor_get(v___x_647_, 0);
lean_inc(v_val_648_);
lean_dec_ref_known(v___x_647_, 1);
v_str_649_ = lean_ctor_get(v_val_648_, 0);
v_startPos_650_ = lean_ctor_get(v_val_648_, 1);
v_stopPos_651_ = lean_ctor_get(v_val_648_, 2);
v_isSharedCheck_664_ = !lean_is_exclusive(v_val_648_);
if (v_isSharedCheck_664_ == 0)
{
v___x_653_ = v_val_648_;
v_isShared_654_ = v_isSharedCheck_664_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_stopPos_651_);
lean_inc(v_startPos_650_);
lean_inc(v_str_649_);
lean_dec(v_val_648_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_664_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_658_; 
v___x_655_ = lean_string_utf8_extract(v_str_649_, v_startPos_650_, v_stopPos_651_);
lean_dec(v_stopPos_651_);
lean_dec(v_startPos_650_);
lean_dec_ref(v_str_649_);
v___x_656_ = lean_string_utf8_byte_size(v___x_655_);
if (v_isShared_654_ == 0)
{
lean_ctor_set(v___x_653_, 2, v___x_656_);
lean_ctor_set(v___x_653_, 1, v___y_642_);
lean_ctor_set(v___x_653_, 0, v___x_655_);
v___x_658_ = v___x_653_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v___x_655_);
lean_ctor_set(v_reuseFailAlloc_663_, 1, v___y_642_);
lean_ctor_set(v_reuseFailAlloc_663_, 2, v___x_656_);
v___x_658_ = v_reuseFailAlloc_663_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
uint8_t v___x_659_; 
v___x_659_ = l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2(v___x_658_);
lean_dec_ref(v___x_658_);
if (v___x_659_ == 0)
{
v___y_631_ = v_importsStx_645_;
v_opts_632_ = v_opts_606_;
goto v___jp_630_;
}
else
{
lean_object* v___x_660_; uint8_t v___x_661_; lean_object* v_opts_662_; 
v___x_660_ = l_Lean_linter_deprecated_module;
v___x_661_ = 0;
v_opts_662_ = l_Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4(v_opts_606_, v___x_660_, v___x_661_);
v___y_631_ = v_importsStx_645_;
v_opts_632_ = v_opts_662_;
goto v___jp_630_;
}
}
}
}
}
}
v___jp_665_:
{
lean_object* v___x_672_; lean_object* v___x_673_; uint8_t v___x_674_; 
v___x_672_ = lean_unsigned_to_nat(1u);
v___x_673_ = l_Lean_Syntax_getArg(v___y_668_, v___x_672_);
v___x_674_ = l_Lean_Syntax_isNone(v___x_673_);
if (v___x_674_ == 0)
{
uint8_t v___x_675_; 
lean_inc(v___x_673_);
v___x_675_ = l_Lean_Syntax_matchesNull(v___x_673_, v___x_672_);
if (v___x_675_ == 0)
{
lean_dec(v___x_673_);
lean_dec(v_moduleTk_671_);
lean_dec(v___y_670_);
lean_dec(v___y_668_);
v_opts_613_ = v_opts_606_;
v_ignoreDeprecatedImports_614_ = v_ignoreDeprecatedImports_628_;
v_importPositions_615_ = v_importPositions_629_;
goto v___jp_612_;
}
else
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; uint8_t v___x_679_; 
v___x_676_ = l_Lean_Syntax_getArg(v___x_673_, v___y_670_);
lean_dec(v___x_673_);
v___x_677_ = ((lean_object*)(l_Lean_Elab_HeaderSyntax_imports___closed__6));
lean_inc_ref(v___y_666_);
lean_inc_ref(v___y_667_);
lean_inc_ref(v___y_669_);
v___x_678_ = l_Lean_Name_mkStr4(v___y_669_, v___y_667_, v___y_666_, v___x_677_);
v___x_679_ = l_Lean_Syntax_isOfKind(v___x_676_, v___x_678_);
lean_dec(v___x_678_);
if (v___x_679_ == 0)
{
lean_dec(v_moduleTk_671_);
lean_dec(v___y_670_);
lean_dec(v___y_668_);
v_opts_613_ = v_opts_606_;
v_ignoreDeprecatedImports_614_ = v_ignoreDeprecatedImports_628_;
v_importPositions_615_ = v_importPositions_629_;
goto v___jp_612_;
}
else
{
v___y_640_ = v___y_668_;
v___y_641_ = v_moduleTk_671_;
v___y_642_ = v___y_670_;
goto v___jp_639_;
}
}
}
else
{
lean_dec(v___x_673_);
v___y_640_ = v___y_668_;
v___y_641_ = v_moduleTk_671_;
v___y_642_ = v___y_670_;
goto v___jp_639_;
}
}
v___jp_680_:
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; uint8_t v___x_686_; 
v___x_682_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__0));
v___x_683_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__1));
v___x_684_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__2));
v___x_685_ = ((lean_object*)(l_Lean_Elab_HeaderSyntax_imports___closed__1));
lean_inc(v_val_681_);
v___x_686_ = l_Lean_Syntax_isOfKind(v_val_681_, v___x_685_);
if (v___x_686_ == 0)
{
lean_dec(v_val_681_);
v_opts_613_ = v_opts_606_;
v_ignoreDeprecatedImports_614_ = v_ignoreDeprecatedImports_628_;
v_importPositions_615_ = v_importPositions_629_;
goto v___jp_612_;
}
else
{
lean_object* v___x_687_; lean_object* v___x_688_; uint8_t v___x_689_; 
v___x_687_ = lean_unsigned_to_nat(0u);
v___x_688_ = l_Lean_Syntax_getArg(v_val_681_, v___x_687_);
v___x_689_ = l_Lean_Syntax_isNone(v___x_688_);
if (v___x_689_ == 0)
{
lean_object* v___x_690_; uint8_t v___x_691_; 
v___x_690_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_688_);
v___x_691_ = l_Lean_Syntax_matchesNull(v___x_688_, v___x_690_);
if (v___x_691_ == 0)
{
lean_dec(v___x_688_);
lean_dec(v_val_681_);
v_opts_613_ = v_opts_606_;
v_ignoreDeprecatedImports_614_ = v_ignoreDeprecatedImports_628_;
v_importPositions_615_ = v_importPositions_629_;
goto v___jp_612_;
}
else
{
lean_object* v___x_692_; lean_object* v___x_693_; uint8_t v___x_694_; 
v___x_692_ = l_Lean_Syntax_getArg(v___x_688_, v___x_687_);
lean_dec(v___x_688_);
v___x_693_ = ((lean_object*)(l_Lean_Elab_HeaderSyntax_imports___closed__9));
lean_inc(v___x_692_);
v___x_694_ = l_Lean_Syntax_isOfKind(v___x_692_, v___x_693_);
if (v___x_694_ == 0)
{
lean_dec(v___x_692_);
lean_dec(v_val_681_);
v_opts_613_ = v_opts_606_;
v_ignoreDeprecatedImports_614_ = v_ignoreDeprecatedImports_628_;
v_importPositions_615_ = v_importPositions_629_;
goto v___jp_612_;
}
else
{
lean_object* v_moduleTk_695_; lean_object* v___x_696_; 
v_moduleTk_695_ = l_Lean_Syntax_getArg(v___x_692_, v___x_687_);
lean_dec(v___x_692_);
v___x_696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_696_, 0, v_moduleTk_695_);
v___y_666_ = v___x_684_;
v___y_667_ = v___x_683_;
v___y_668_ = v_val_681_;
v___y_669_ = v___x_682_;
v___y_670_ = v___x_687_;
v_moduleTk_671_ = v___x_696_;
goto v___jp_665_;
}
}
}
else
{
lean_object* v___x_697_; 
lean_dec(v___x_688_);
v___x_697_ = lean_box(0);
v___y_666_ = v___x_684_;
v___y_667_ = v___x_683_;
v___y_668_ = v_val_681_;
v___y_669_ = v___x_682_;
v___y_670_ = v___x_687_;
v_moduleTk_671_ = v___x_697_;
goto v___jp_665_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedImports___boxed(lean_object* v_env_700_, lean_object* v_imports_701_, lean_object* v_opts_702_, lean_object* v_inputCtx_703_, lean_object* v_startPos_704_, lean_object* v_messages_705_, lean_object* v_headerStx_x3f_706_, lean_object* v_origHeaderStx_x3f_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l_Lean_Elab_checkDeprecatedImports(v_env_700_, v_imports_701_, v_opts_702_, v_inputCtx_703_, v_startPos_704_, v_messages_705_, v_headerStx_x3f_706_, v_origHeaderStx_x3f_707_);
lean_dec_ref(v_imports_701_);
lean_dec_ref(v_env_700_);
return v_res_708_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_spec__2(lean_object* v_s_709_, lean_object* v_inst_710_, lean_object* v_R_711_, lean_object* v_a_712_, uint8_t v_b_713_, lean_object* v_c_714_){
_start:
{
uint8_t v___x_715_; 
v___x_715_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_spec__2___redArg(v_s_709_, v_a_712_, v_b_713_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_spec__2___boxed(lean_object* v_s_716_, lean_object* v_inst_717_, lean_object* v_R_718_, lean_object* v_a_719_, lean_object* v_b_720_, lean_object* v_c_721_){
_start:
{
uint8_t v_b_boxed_722_; uint8_t v_res_723_; lean_object* v_r_724_; 
v_b_boxed_722_ = lean_unbox(v_b_720_);
v_res_723_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_spec__2(v_s_716_, v_inst_717_, v_R_718_, v_a_719_, v_b_boxed_722_, v_c_721_);
lean_dec_ref(v_s_716_);
v_r_724_ = lean_box(v_res_723_);
return v_r_724_;
}
}
static lean_object* _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_725_; lean_object* v___x_726_; 
v___x_725_ = 33;
v___x_726_ = lean_box_uint32(v___x_725_);
return v___x_726_;
}
}
static lean_object* _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__2(void){
_start:
{
uint32_t v___x_727_; lean_object* v___x_728_; 
v___x_727_ = 42;
v___x_728_ = lean_box_uint32(v___x_727_);
return v___x_728_;
}
}
static lean_object* _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__3(void){
_start:
{
uint32_t v___x_729_; lean_object* v___x_730_; 
v___x_729_ = 63;
v___x_730_ = lean_box_uint32(v___x_729_);
return v___x_730_;
}
}
static lean_object* _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__4(void){
_start:
{
uint32_t v___x_731_; lean_object* v___x_732_; 
v___x_731_ = 124;
v___x_732_ = lean_box_uint32(v___x_731_);
return v___x_732_;
}
}
static lean_object* _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__5(void){
_start:
{
uint32_t v___x_733_; lean_object* v___x_734_; 
v___x_733_ = 34;
v___x_734_ = lean_box_uint32(v___x_733_);
return v___x_734_;
}
}
static lean_object* _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__6(void){
_start:
{
uint32_t v___x_735_; lean_object* v___x_736_; 
v___x_735_ = 62;
v___x_736_ = lean_box_uint32(v___x_735_);
return v___x_736_;
}
}
static lean_object* _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__7(void){
_start:
{
uint32_t v___x_737_; lean_object* v___x_738_; 
v___x_737_ = 60;
v___x_738_ = lean_box_uint32(v___x_737_);
return v___x_738_;
}
}
static lean_object* _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0(void){
_start:
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_739_ = lean_unsigned_to_nat(7u);
v___x_740_ = lean_mk_empty_array_with_capacity(v___x_739_);
v___x_741_ = l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__7;
v___x_742_ = lean_array_push(v___x_740_, v___x_741_);
v___x_743_ = l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__6;
v___x_744_ = lean_array_push(v___x_742_, v___x_743_);
v___x_745_ = l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__5;
v___x_746_ = lean_array_push(v___x_744_, v___x_745_);
v___x_747_ = l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__4;
v___x_748_ = lean_array_push(v___x_746_, v___x_747_);
v___x_749_ = l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__3;
v___x_750_ = lean_array_push(v___x_748_, v___x_749_);
v___x_751_ = l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__2;
v___x_752_ = lean_array_push(v___x_750_, v___x_751_);
v___x_753_ = l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__1;
v___x_754_ = lean_array_push(v___x_752_, v___x_753_);
return v___x_754_;
}
}
static lean_object* _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars(void){
_start:
{
lean_object* v___x_755_; 
v___x_755_ = lean_obj_once(&l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0, &l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0_once, _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__0(lean_object* v_s_843_, lean_object* v_p_844_){
_start:
{
uint32_t v___y_846_; lean_object* v___x_851_; uint8_t v_decide_852_; 
v___x_851_ = lean_string_utf8_byte_size(v_s_843_);
v_decide_852_ = lean_nat_dec_eq(v_p_844_, v___x_851_);
if (v_decide_852_ == 0)
{
uint32_t v___x_853_; uint8_t v___y_855_; uint32_t v___x_858_; uint8_t v___x_859_; 
v___x_853_ = lean_string_utf8_get_fast(v_s_843_, v_p_844_);
v___x_858_ = 97;
v___x_859_ = lean_uint32_dec_le(v___x_858_, v___x_853_);
if (v___x_859_ == 0)
{
v___y_855_ = v___x_859_;
goto v___jp_854_;
}
else
{
uint32_t v___x_860_; uint8_t v___x_861_; 
v___x_860_ = 122;
v___x_861_ = lean_uint32_dec_le(v___x_853_, v___x_860_);
v___y_855_ = v___x_861_;
goto v___jp_854_;
}
v___jp_854_:
{
if (v___y_855_ == 0)
{
v___y_846_ = v___x_853_;
goto v___jp_845_;
}
else
{
uint32_t v___x_856_; uint32_t v___x_857_; 
v___x_856_ = 4294967264;
v___x_857_ = lean_uint32_add(v___x_853_, v___x_856_);
v___y_846_ = v___x_857_;
goto v___jp_845_;
}
}
}
else
{
lean_dec(v_p_844_);
return v_s_843_;
}
v___jp_845_:
{
lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
lean_inc(v_p_844_);
v___x_847_ = lean_string_utf8_set(v_s_843_, v_p_844_, v___y_846_);
v___x_848_ = l_Char_utf8Size(v___y_846_);
v___x_849_ = lean_nat_add(v_p_844_, v___x_848_);
lean_dec(v___x_848_);
lean_dec(v_p_844_);
v_s_843_ = v___x_847_;
v_p_844_ = v___x_849_;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2_spec__3___redArg(lean_object* v_s_862_, uint32_t v_a_863_, lean_object* v_a_864_, uint8_t v_b_865_){
_start:
{
lean_object* v_str_866_; lean_object* v_startInclusive_867_; lean_object* v_endExclusive_868_; lean_object* v___x_869_; uint8_t v_decide_870_; 
v_str_866_ = lean_ctor_get(v_s_862_, 0);
v_startInclusive_867_ = lean_ctor_get(v_s_862_, 1);
v_endExclusive_868_ = lean_ctor_get(v_s_862_, 2);
v___x_869_ = lean_nat_sub(v_endExclusive_868_, v_startInclusive_867_);
v_decide_870_ = lean_nat_dec_eq(v_a_864_, v___x_869_);
lean_dec(v___x_869_);
if (v_decide_870_ == 0)
{
lean_object* v___x_871_; uint32_t v___x_872_; uint8_t v___x_873_; 
v___x_871_ = lean_nat_add(v_startInclusive_867_, v_a_864_);
lean_dec(v_a_864_);
v___x_872_ = lean_string_utf8_get_fast(v_str_866_, v___x_871_);
v___x_873_ = lean_uint32_dec_eq(v___x_872_, v_a_863_);
if (v___x_873_ == 0)
{
lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_874_ = lean_string_utf8_next_fast(v_str_866_, v___x_871_);
lean_dec(v___x_871_);
v___x_875_ = lean_nat_sub(v___x_874_, v_startInclusive_867_);
v_a_864_ = v___x_875_;
v_b_865_ = v___x_873_;
goto _start;
}
else
{
lean_dec(v___x_871_);
return v___x_873_;
}
}
else
{
lean_dec(v_a_864_);
return v_b_865_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2_spec__3___redArg___boxed(lean_object* v_s_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_b_880_){
_start:
{
uint32_t v_a_boxed_881_; uint8_t v_b_boxed_882_; uint8_t v_res_883_; lean_object* v_r_884_; 
v_a_boxed_881_ = lean_unbox_uint32(v_a_878_);
lean_dec(v_a_878_);
v_b_boxed_882_ = lean_unbox(v_b_880_);
v_res_883_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2_spec__3___redArg(v_s_877_, v_a_boxed_881_, v_a_879_, v_b_boxed_882_);
lean_dec_ref(v_s_877_);
v_r_884_ = lean_box(v_res_883_);
return v_r_884_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2(uint32_t v_a_885_, lean_object* v_s_886_){
_start:
{
lean_object* v_searcher_887_; uint8_t v___x_888_; uint8_t v___x_889_; 
v_searcher_887_ = lean_unsigned_to_nat(0u);
v___x_888_ = 0;
v___x_889_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2_spec__3___redArg(v_s_886_, v_a_885_, v_searcher_887_, v___x_888_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2___boxed(lean_object* v_a_890_, lean_object* v_s_891_){
_start:
{
uint32_t v_a_boxed_892_; uint8_t v_res_893_; lean_object* v_r_894_; 
v_a_boxed_892_ = lean_unbox_uint32(v_a_890_);
lean_dec(v_a_890_);
v_res_893_ = l_String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2(v_a_boxed_892_, v_s_891_);
lean_dec_ref(v_s_891_);
v_r_894_ = lean_box(v_res_893_);
return v_r_894_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__3(lean_object* v_comp_898_, lean_object* v_as_899_, size_t v_sz_900_, size_t v_i_901_, lean_object* v_b_902_){
_start:
{
uint8_t v___x_903_; 
v___x_903_ = lean_usize_dec_lt(v_i_901_, v_sz_900_);
if (v___x_903_ == 0)
{
lean_dec_ref(v_comp_898_);
lean_inc_ref(v_b_902_);
return v_b_902_;
}
else
{
lean_object* v___x_904_; lean_object* v_a_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; uint32_t v___x_909_; uint8_t v___x_910_; 
v___x_904_ = lean_box(0);
v_a_905_ = lean_array_uget_borrowed(v_as_899_, v_i_901_);
v___x_906_ = lean_unsigned_to_nat(0u);
v___x_907_ = lean_string_utf8_byte_size(v_comp_898_);
lean_inc_ref(v_comp_898_);
v___x_908_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_908_, 0, v_comp_898_);
lean_ctor_set(v___x_908_, 1, v___x_906_);
lean_ctor_set(v___x_908_, 2, v___x_907_);
v___x_909_ = lean_unbox_uint32(v_a_905_);
v___x_910_ = l_String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2(v___x_909_, v___x_908_);
lean_dec_ref_known(v___x_908_, 3);
if (v___x_910_ == 0)
{
lean_object* v___x_911_; size_t v___x_912_; size_t v___x_913_; 
v___x_911_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__3___closed__0));
v___x_912_ = ((size_t)1ULL);
v___x_913_ = lean_usize_add(v_i_901_, v___x_912_);
v_i_901_ = v___x_913_;
v_b_902_ = v___x_911_;
goto _start;
}
else
{
lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
lean_dec_ref(v_comp_898_);
lean_inc(v_a_905_);
v___x_915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_915_, 0, v_a_905_);
v___x_916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_916_, 0, v___x_915_);
v___x_917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_917_, 0, v___x_916_);
lean_ctor_set(v___x_917_, 1, v___x_904_);
return v___x_917_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__3___boxed(lean_object* v_comp_918_, lean_object* v_as_919_, lean_object* v_sz_920_, lean_object* v_i_921_, lean_object* v_b_922_){
_start:
{
size_t v_sz_boxed_923_; size_t v_i_boxed_924_; lean_object* v_res_925_; 
v_sz_boxed_923_ = lean_unbox_usize(v_sz_920_);
lean_dec(v_sz_920_);
v_i_boxed_924_ = lean_unbox_usize(v_i_921_);
lean_dec(v_i_921_);
v_res_925_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__3(v_comp_918_, v_as_919_, v_sz_boxed_923_, v_i_boxed_924_, v_b_922_);
lean_dec_ref(v_b_922_);
lean_dec_ref(v_as_919_);
return v_res_925_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__1_spec__1(lean_object* v_a_926_, lean_object* v_as_927_, size_t v_i_928_, size_t v_stop_929_){
_start:
{
uint8_t v___x_930_; 
v___x_930_ = lean_usize_dec_eq(v_i_928_, v_stop_929_);
if (v___x_930_ == 0)
{
lean_object* v___x_931_; uint8_t v___x_932_; 
v___x_931_ = lean_array_uget_borrowed(v_as_927_, v_i_928_);
v___x_932_ = lean_string_dec_eq(v_a_926_, v___x_931_);
if (v___x_932_ == 0)
{
size_t v___x_933_; size_t v___x_934_; 
v___x_933_ = ((size_t)1ULL);
v___x_934_ = lean_usize_add(v_i_928_, v___x_933_);
v_i_928_ = v___x_934_;
goto _start;
}
else
{
return v___x_932_;
}
}
else
{
uint8_t v___x_936_; 
v___x_936_ = 0;
return v___x_936_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__1_spec__1___boxed(lean_object* v_a_937_, lean_object* v_as_938_, lean_object* v_i_939_, lean_object* v_stop_940_){
_start:
{
size_t v_i_boxed_941_; size_t v_stop_boxed_942_; uint8_t v_res_943_; lean_object* v_r_944_; 
v_i_boxed_941_ = lean_unbox_usize(v_i_939_);
lean_dec(v_i_939_);
v_stop_boxed_942_ = lean_unbox_usize(v_stop_940_);
lean_dec(v_stop_940_);
v_res_943_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__1_spec__1(v_a_937_, v_as_938_, v_i_boxed_941_, v_stop_boxed_942_);
lean_dec_ref(v_as_938_);
lean_dec_ref(v_a_937_);
v_r_944_ = lean_box(v_res_943_);
return v_r_944_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__1(lean_object* v_as_945_, lean_object* v_a_946_){
_start:
{
lean_object* v___x_947_; lean_object* v___x_948_; uint8_t v___x_949_; 
v___x_947_ = lean_unsigned_to_nat(0u);
v___x_948_ = lean_array_get_size(v_as_945_);
v___x_949_ = lean_nat_dec_lt(v___x_947_, v___x_948_);
if (v___x_949_ == 0)
{
return v___x_949_;
}
else
{
if (v___x_949_ == 0)
{
return v___x_949_;
}
else
{
size_t v___x_950_; size_t v___x_951_; uint8_t v___x_952_; 
v___x_950_ = ((size_t)0ULL);
v___x_951_ = lean_usize_of_nat(v___x_948_);
v___x_952_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__1_spec__1(v_a_946_, v_as_945_, v___x_950_, v___x_951_);
return v___x_952_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__1___boxed(lean_object* v_as_953_, lean_object* v_a_954_){
_start:
{
uint8_t v_res_955_; lean_object* v_r_956_; 
v_res_955_ = l_Array_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__1(v_as_953_, v_a_954_);
lean_dec_ref(v_a_954_);
lean_dec_ref(v_as_953_);
v_r_956_ = lean_box(v_res_955_);
return v_r_956_;
}
}
static size_t _init_l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__0(void){
_start:
{
lean_object* v___x_957_; size_t v_sz_958_; 
v___x_957_ = l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars;
v_sz_958_ = lean_array_size(v___x_957_);
return v_sz_958_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability(lean_object* v_comp_963_){
_start:
{
lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; uint8_t v___x_967_; 
v___x_964_ = ((lean_object*)(l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames));
v___x_965_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_comp_963_);
v___x_966_ = l_String_mapAux___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__0(v_comp_963_, v___x_965_);
v___x_967_ = l_Array_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__1(v___x_964_, v___x_966_);
lean_dec_ref(v___x_966_);
if (v___x_967_ == 0)
{
lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; size_t v_sz_971_; size_t v___x_972_; lean_object* v___x_973_; lean_object* v_fst_974_; 
v___x_968_ = l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars;
v___x_969_ = lean_box(0);
v___x_970_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__3___closed__0));
v_sz_971_ = lean_usize_once(&l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__0, &l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__0_once, _init_l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__0);
v___x_972_ = ((size_t)0ULL);
v___x_973_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__3(v_comp_963_, v___x_968_, v_sz_971_, v___x_972_, v___x_970_);
v_fst_974_ = lean_ctor_get(v___x_973_, 0);
lean_inc(v_fst_974_);
lean_dec_ref(v___x_973_);
if (lean_obj_tag(v_fst_974_) == 0)
{
return v___x_969_;
}
else
{
lean_object* v_val_975_; 
v_val_975_ = lean_ctor_get(v_fst_974_, 0);
lean_inc(v_val_975_);
lean_dec_ref_known(v_fst_974_, 1);
if (lean_obj_tag(v_val_975_) == 1)
{
lean_object* v_val_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_990_; 
v_val_976_ = lean_ctor_get(v_val_975_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v_val_975_);
if (v_isSharedCheck_990_ == 0)
{
v___x_978_ = v_val_975_;
v_isShared_979_ = v_isSharedCheck_990_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_val_976_);
lean_dec(v_val_975_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_990_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_980_; lean_object* v___x_981_; uint32_t v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_988_; 
v___x_980_ = ((lean_object*)(l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__1));
v___x_981_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___closed__0));
v___x_982_ = lean_unbox_uint32(v_val_976_);
lean_dec(v_val_976_);
v___x_983_ = lean_string_push(v___x_981_, v___x_982_);
v___x_984_ = lean_string_append(v___x_980_, v___x_983_);
lean_dec_ref(v___x_983_);
v___x_985_ = ((lean_object*)(l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__2));
v___x_986_ = lean_string_append(v___x_984_, v___x_985_);
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 0, v___x_986_);
v___x_988_ = v___x_978_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v___x_986_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
}
else
{
lean_dec(v_val_975_);
return v___x_969_;
}
}
}
else
{
lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_991_ = ((lean_object*)(l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__3));
v___x_992_ = lean_string_append(v___x_991_, v_comp_963_);
lean_dec_ref(v_comp_963_);
v___x_993_ = ((lean_object*)(l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__4));
v___x_994_ = lean_string_append(v___x_992_, v___x_993_);
v___x_995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_995_, 0, v___x_994_);
return v___x_995_;
}
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2_spec__3(lean_object* v_s_996_, uint32_t v_a_997_, lean_object* v_inst_998_, lean_object* v_R_999_, lean_object* v_a_1000_, uint8_t v_b_1001_, lean_object* v_c_1002_){
_start:
{
uint8_t v___x_1003_; 
v___x_1003_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2_spec__3___redArg(v_s_996_, v_a_997_, v_a_1000_, v_b_1001_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2_spec__3___boxed(lean_object* v_s_1004_, lean_object* v_a_1005_, lean_object* v_inst_1006_, lean_object* v_R_1007_, lean_object* v_a_1008_, lean_object* v_b_1009_, lean_object* v_c_1010_){
_start:
{
uint32_t v_a_boxed_1011_; uint8_t v_b_boxed_1012_; uint8_t v_res_1013_; lean_object* v_r_1014_; 
v_a_boxed_1011_ = lean_unbox_uint32(v_a_1005_);
lean_dec(v_a_1005_);
v_b_boxed_1012_ = lean_unbox(v_b_1009_);
v_res_1013_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2_spec__3(v_s_1004_, v_a_boxed_1011_, v_inst_1006_, v_R_1007_, v_a_1008_, v_b_boxed_1012_, v_c_1010_);
lean_dec_ref(v_s_1004_);
v_r_1014_ = lean_box(v_res_1013_);
return v_r_1014_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_checkModuleNamePortability_go(lean_object* v_mainModule_1017_, lean_object* v_inputCtx_1018_, lean_object* v_startPos_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_){
_start:
{
switch(lean_obj_tag(v_a_1020_))
{
case 0:
{
lean_dec_ref(v_inputCtx_1018_);
lean_dec(v_mainModule_1017_);
return v_a_1021_;
}
case 1:
{
lean_object* v_pre_1022_; lean_object* v_str_1023_; lean_object* v___x_1024_; 
v_pre_1022_ = lean_ctor_get(v_a_1020_, 0);
lean_inc(v_pre_1022_);
v_str_1023_ = lean_ctor_get(v_a_1020_, 1);
lean_inc_ref(v_str_1023_);
lean_dec_ref_known(v_a_1020_, 2);
v___x_1024_ = l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability(v_str_1023_);
if (lean_obj_tag(v___x_1024_) == 0)
{
v_a_1020_ = v_pre_1022_;
goto _start;
}
else
{
lean_object* v_val_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1051_; 
v_val_1026_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1028_ = v___x_1024_;
v_isShared_1029_ = v_isSharedCheck_1051_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_val_1026_);
lean_dec(v___x_1024_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1051_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v_fileName_1030_; lean_object* v_fileMap_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; uint8_t v___x_1034_; uint8_t v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; uint8_t v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1045_; 
v_fileName_1030_ = lean_ctor_get(v_inputCtx_1018_, 1);
v_fileMap_1031_ = lean_ctor_get(v_inputCtx_1018_, 2);
lean_inc_ref(v_fileMap_1031_);
v___x_1032_ = l_Lean_FileMap_toPosition(v_fileMap_1031_, v_startPos_1019_);
v___x_1033_ = lean_box(0);
v___x_1034_ = 0;
v___x_1035_ = 2;
v___x_1036_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___closed__0));
v___x_1037_ = ((lean_object*)(l___private_Lean_Elab_Import_0__Lean_Elab_checkModuleNamePortability_go___closed__0));
v___x_1038_ = 1;
lean_inc(v_mainModule_1017_);
v___x_1039_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mainModule_1017_, v___x_1038_);
v___x_1040_ = lean_string_append(v___x_1037_, v___x_1039_);
lean_dec_ref(v___x_1039_);
v___x_1041_ = ((lean_object*)(l___private_Lean_Elab_Import_0__Lean_Elab_checkModuleNamePortability_go___closed__1));
v___x_1042_ = lean_string_append(v___x_1040_, v___x_1041_);
v___x_1043_ = lean_string_append(v___x_1042_, v_val_1026_);
lean_dec(v_val_1026_);
if (v_isShared_1029_ == 0)
{
lean_ctor_set_tag(v___x_1028_, 3);
lean_ctor_set(v___x_1028_, 0, v___x_1043_);
v___x_1045_ = v___x_1028_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v___x_1043_);
v___x_1045_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1046_ = l_Lean_MessageData_ofFormat(v___x_1045_);
lean_inc_ref(v_fileName_1030_);
v___x_1047_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1047_, 0, v_fileName_1030_);
lean_ctor_set(v___x_1047_, 1, v___x_1032_);
lean_ctor_set(v___x_1047_, 2, v___x_1033_);
lean_ctor_set(v___x_1047_, 3, v___x_1036_);
lean_ctor_set(v___x_1047_, 4, v___x_1046_);
lean_ctor_set_uint8(v___x_1047_, sizeof(void*)*5, v___x_1034_);
lean_ctor_set_uint8(v___x_1047_, sizeof(void*)*5 + 1, v___x_1035_);
lean_ctor_set_uint8(v___x_1047_, sizeof(void*)*5 + 2, v___x_1034_);
v___x_1048_ = l_Lean_MessageLog_add(v___x_1047_, v_a_1021_);
v_a_1020_ = v_pre_1022_;
v_a_1021_ = v___x_1048_;
goto _start;
}
}
}
}
default: 
{
lean_object* v_pre_1052_; 
v_pre_1052_ = lean_ctor_get(v_a_1020_, 0);
lean_inc(v_pre_1052_);
lean_dec_ref_known(v_a_1020_, 2);
v_a_1020_ = v_pre_1052_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_checkModuleNamePortability_go___boxed(lean_object* v_mainModule_1054_, lean_object* v_inputCtx_1055_, lean_object* v_startPos_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l___private_Lean_Elab_Import_0__Lean_Elab_checkModuleNamePortability_go(v_mainModule_1054_, v_inputCtx_1055_, v_startPos_1056_, v_a_1057_, v_a_1058_);
lean_dec(v_startPos_1056_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkModuleNamePortability(lean_object* v_mainModule_1060_, lean_object* v_inputCtx_1061_, lean_object* v_startPos_1062_, lean_object* v_messages_1063_){
_start:
{
lean_object* v___x_1064_; 
lean_inc(v_mainModule_1060_);
v___x_1064_ = l___private_Lean_Elab_Import_0__Lean_Elab_checkModuleNamePortability_go(v_mainModule_1060_, v_inputCtx_1061_, v_startPos_1062_, v_mainModule_1060_, v_messages_1063_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkModuleNamePortability___boxed(lean_object* v_mainModule_1065_, lean_object* v_inputCtx_1066_, lean_object* v_startPos_1067_, lean_object* v_messages_1068_){
_start:
{
lean_object* v_res_1069_; 
v_res_1069_ = l_Lean_Elab_checkModuleNamePortability(v_mainModule_1065_, v_inputCtx_1066_, v_startPos_1067_, v_messages_1068_);
lean_dec(v_startPos_1067_);
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_processHeaderCore(lean_object* v_startPos_1070_, lean_object* v_imports_1071_, uint8_t v_isModule_1072_, lean_object* v_opts_1073_, lean_object* v_messages_1074_, lean_object* v_inputCtx_1075_, uint32_t v_trustLevel_1076_, lean_object* v_plugins_1077_, uint8_t v_leakEnv_1078_, lean_object* v_mainModule_1079_, lean_object* v_package_x3f_1080_, lean_object* v_arts_1081_, lean_object* v_headerStx_x3f_1082_, lean_object* v_origHeaderStx_x3f_1083_){
_start:
{
lean_object* v_fst_1086_; lean_object* v_snd_1087_; uint8_t v___x_1095_; uint8_t v___y_1097_; 
v___x_1095_ = 1;
if (v_isModule_1072_ == 0)
{
uint8_t v___x_1130_; 
v___x_1130_ = 2;
v___y_1097_ = v___x_1130_;
goto v___jp_1096_;
}
else
{
lean_object* v___x_1131_; uint8_t v___x_1132_; 
v___x_1131_ = l_Lean_Elab_inServer;
v___x_1132_ = l_Lean_Option_get___at___00Lean_Elab_checkDeprecatedImports_spec__0(v_opts_1073_, v___x_1131_);
if (v___x_1132_ == 0)
{
uint8_t v___x_1133_; 
v___x_1133_ = 0;
v___y_1097_ = v___x_1133_;
goto v___jp_1096_;
}
else
{
uint8_t v___x_1134_; 
v___x_1134_ = 1;
v___y_1097_ = v___x_1134_;
goto v___jp_1096_;
}
}
v___jp_1085_:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; 
lean_inc_n(v_mainModule_1079_, 2);
v___x_1088_ = l_Lean_Environment_setMainModule(v_fst_1086_, v_mainModule_1079_);
v___x_1089_ = l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
v___x_1090_ = l_Lean_PersistentEnvExtension_setState___redArg(v___x_1089_, v___x_1088_, v_package_x3f_1080_);
lean_inc(v_startPos_1070_);
lean_inc_ref(v_inputCtx_1075_);
v___x_1091_ = l_Lean_Elab_checkDeprecatedImports(v___x_1090_, v_imports_1071_, v_opts_1073_, v_inputCtx_1075_, v_startPos_1070_, v_snd_1087_, v_headerStx_x3f_1082_, v_origHeaderStx_x3f_1083_);
lean_dec_ref(v_imports_1071_);
v___x_1092_ = l___private_Lean_Elab_Import_0__Lean_Elab_checkModuleNamePortability_go(v_mainModule_1079_, v_inputCtx_1075_, v_startPos_1070_, v_mainModule_1079_, v___x_1091_);
lean_dec(v_startPos_1070_);
v___x_1093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1090_);
lean_ctor_set(v___x_1093_, 1, v___x_1092_);
v___x_1094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1093_);
return v___x_1094_;
}
v___jp_1096_:
{
lean_object* v___x_1098_; 
lean_inc_ref(v_opts_1073_);
lean_inc_ref(v_imports_1071_);
v___x_1098_ = l_Lean_importModules(v_imports_1071_, v_opts_1073_, v_trustLevel_1076_, v_plugins_1077_, v_leakEnv_1078_, v___x_1095_, v___y_1097_, v_arts_1081_);
if (lean_obj_tag(v___x_1098_) == 0)
{
lean_object* v_a_1099_; 
v_a_1099_ = lean_ctor_get(v___x_1098_, 0);
lean_inc(v_a_1099_);
lean_dec_ref_known(v___x_1098_, 1);
v_fst_1086_ = v_a_1099_;
v_snd_1087_ = v_messages_1074_;
goto v___jp_1085_;
}
else
{
lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1129_; 
v_a_1100_ = lean_ctor_get(v___x_1098_, 0);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1102_ = v___x_1098_;
v_isShared_1103_ = v_isSharedCheck_1129_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___x_1098_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1129_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
uint32_t v___x_1104_; lean_object* v___x_1105_; 
v___x_1104_ = 0;
v___x_1105_ = l_Lean_mkEmptyEnvironment(v___x_1104_);
if (lean_obj_tag(v___x_1105_) == 0)
{
lean_object* v_a_1106_; lean_object* v_fileName_1107_; lean_object* v_fileMap_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; uint8_t v___x_1111_; uint8_t v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1116_; 
v_a_1106_ = lean_ctor_get(v___x_1105_, 0);
lean_inc(v_a_1106_);
lean_dec_ref_known(v___x_1105_, 1);
v_fileName_1107_ = lean_ctor_get(v_inputCtx_1075_, 1);
v_fileMap_1108_ = lean_ctor_get(v_inputCtx_1075_, 2);
lean_inc_ref(v_fileMap_1108_);
v___x_1109_ = l_Lean_FileMap_toPosition(v_fileMap_1108_, v_startPos_1070_);
v___x_1110_ = lean_box(0);
v___x_1111_ = 0;
v___x_1112_ = 2;
v___x_1113_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___closed__0));
v___x_1114_ = lean_io_error_to_string(v_a_1100_);
if (v_isShared_1103_ == 0)
{
lean_ctor_set_tag(v___x_1102_, 3);
lean_ctor_set(v___x_1102_, 0, v___x_1114_);
v___x_1116_ = v___x_1102_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v___x_1114_);
v___x_1116_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1117_ = l_Lean_MessageData_ofFormat(v___x_1116_);
lean_inc_ref(v_fileName_1107_);
v___x_1118_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1118_, 0, v_fileName_1107_);
lean_ctor_set(v___x_1118_, 1, v___x_1109_);
lean_ctor_set(v___x_1118_, 2, v___x_1110_);
lean_ctor_set(v___x_1118_, 3, v___x_1113_);
lean_ctor_set(v___x_1118_, 4, v___x_1117_);
lean_ctor_set_uint8(v___x_1118_, sizeof(void*)*5, v___x_1111_);
lean_ctor_set_uint8(v___x_1118_, sizeof(void*)*5 + 1, v___x_1112_);
lean_ctor_set_uint8(v___x_1118_, sizeof(void*)*5 + 2, v___x_1111_);
v___x_1119_ = l_Lean_MessageLog_add(v___x_1118_, v_messages_1074_);
v_fst_1086_ = v_a_1106_;
v_snd_1087_ = v___x_1119_;
goto v___jp_1085_;
}
}
else
{
lean_object* v_a_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1128_; 
lean_del_object(v___x_1102_);
lean_dec(v_a_1100_);
lean_dec(v_origHeaderStx_x3f_1083_);
lean_dec(v_headerStx_x3f_1082_);
lean_dec(v_package_x3f_1080_);
lean_dec(v_mainModule_1079_);
lean_dec_ref(v_inputCtx_1075_);
lean_dec_ref(v_messages_1074_);
lean_dec_ref(v_opts_1073_);
lean_dec_ref(v_imports_1071_);
lean_dec(v_startPos_1070_);
v_a_1121_ = lean_ctor_get(v___x_1105_, 0);
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1123_ = v___x_1105_;
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_a_1121_);
lean_dec(v___x_1105_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1126_; 
if (v_isShared_1124_ == 0)
{
v___x_1126_ = v___x_1123_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_a_1121_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_processHeaderCore___boxed(lean_object* v_startPos_1135_, lean_object* v_imports_1136_, lean_object* v_isModule_1137_, lean_object* v_opts_1138_, lean_object* v_messages_1139_, lean_object* v_inputCtx_1140_, lean_object* v_trustLevel_1141_, lean_object* v_plugins_1142_, lean_object* v_leakEnv_1143_, lean_object* v_mainModule_1144_, lean_object* v_package_x3f_1145_, lean_object* v_arts_1146_, lean_object* v_headerStx_x3f_1147_, lean_object* v_origHeaderStx_x3f_1148_, lean_object* v_a_1149_){
_start:
{
uint8_t v_isModule_boxed_1150_; uint32_t v_trustLevel_boxed_1151_; uint8_t v_leakEnv_boxed_1152_; lean_object* v_res_1153_; 
v_isModule_boxed_1150_ = lean_unbox(v_isModule_1137_);
v_trustLevel_boxed_1151_ = lean_unbox_uint32(v_trustLevel_1141_);
lean_dec(v_trustLevel_1141_);
v_leakEnv_boxed_1152_ = lean_unbox(v_leakEnv_1143_);
v_res_1153_ = l_Lean_Elab_processHeaderCore(v_startPos_1135_, v_imports_1136_, v_isModule_boxed_1150_, v_opts_1138_, v_messages_1139_, v_inputCtx_1140_, v_trustLevel_boxed_1151_, v_plugins_1142_, v_leakEnv_boxed_1152_, v_mainModule_1144_, v_package_x3f_1145_, v_arts_1146_, v_headerStx_x3f_1147_, v_origHeaderStx_x3f_1148_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_processHeader(lean_object* v_header_1154_, lean_object* v_opts_1155_, lean_object* v_messages_1156_, lean_object* v_inputCtx_1157_, uint32_t v_trustLevel_1158_, lean_object* v_plugins_1159_, uint8_t v_leakEnv_1160_, lean_object* v_mainModule_1161_){
_start:
{
lean_object* v___x_1163_; uint8_t v___x_1164_; lean_object* v___x_1165_; uint8_t v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1163_ = l_Lean_Elab_HeaderSyntax_startPos(v_header_1154_);
v___x_1164_ = 1;
lean_inc(v_header_1154_);
v___x_1165_ = l_Lean_Elab_HeaderSyntax_imports(v_header_1154_, v___x_1164_);
v___x_1166_ = l_Lean_Elab_HeaderSyntax_isModule(v_header_1154_);
v___x_1167_ = lean_box(0);
v___x_1168_ = lean_box(1);
v___x_1169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1169_, 0, v_header_1154_);
v___x_1170_ = l_Lean_Elab_processHeaderCore(v___x_1163_, v___x_1165_, v___x_1166_, v_opts_1155_, v_messages_1156_, v_inputCtx_1157_, v_trustLevel_1158_, v_plugins_1159_, v_leakEnv_1160_, v_mainModule_1161_, v___x_1167_, v___x_1168_, v___x_1169_, v___x_1167_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_processHeader___boxed(lean_object* v_header_1171_, lean_object* v_opts_1172_, lean_object* v_messages_1173_, lean_object* v_inputCtx_1174_, lean_object* v_trustLevel_1175_, lean_object* v_plugins_1176_, lean_object* v_leakEnv_1177_, lean_object* v_mainModule_1178_, lean_object* v_a_1179_){
_start:
{
uint32_t v_trustLevel_boxed_1180_; uint8_t v_leakEnv_boxed_1181_; lean_object* v_res_1182_; 
v_trustLevel_boxed_1180_ = lean_unbox_uint32(v_trustLevel_1175_);
lean_dec(v_trustLevel_1175_);
v_leakEnv_boxed_1181_ = lean_unbox(v_leakEnv_1177_);
v_res_1182_ = l_Lean_Elab_processHeader(v_header_1171_, v_opts_1172_, v_messages_1173_, v_inputCtx_1174_, v_trustLevel_boxed_1180_, v_plugins_1176_, v_leakEnv_boxed_1181_, v_mainModule_1178_);
return v_res_1182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_parseImports(lean_object* v_input_1184_, lean_object* v_fileName_1185_){
_start:
{
lean_object* v___y_1188_; 
if (lean_obj_tag(v_fileName_1185_) == 0)
{
lean_object* v___x_1233_; 
v___x_1233_ = ((lean_object*)(l_Lean_Elab_parseImports___closed__0));
v___y_1188_ = v___x_1233_;
goto v___jp_1187_;
}
else
{
lean_object* v_val_1234_; 
v_val_1234_ = lean_ctor_get(v_fileName_1185_, 0);
lean_inc(v_val_1234_);
lean_dec_ref_known(v_fileName_1185_, 1);
v___y_1188_ = v_val_1234_;
goto v___jp_1187_;
}
v___jp_1187_:
{
uint8_t v___x_1189_; lean_object* v___x_1190_; lean_object* v_inputCtx_1191_; lean_object* v___x_1192_; 
v___x_1189_ = 1;
v___x_1190_ = lean_string_utf8_byte_size(v_input_1184_);
v_inputCtx_1191_ = l_Lean_Parser_mkInputContext___redArg(v_input_1184_, v___y_1188_, v___x_1189_, v___x_1190_);
lean_inc_ref(v_inputCtx_1191_);
v___x_1192_ = l_Lean_Parser_parseHeader(v_inputCtx_1191_);
if (lean_obj_tag(v___x_1192_) == 0)
{
lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1224_; 
v_a_1193_ = lean_ctor_get(v___x_1192_, 0);
v_isSharedCheck_1224_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1195_ = v___x_1192_;
v_isShared_1196_ = v_isSharedCheck_1224_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_dec(v___x_1192_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1224_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v_snd_1197_; lean_object* v_fst_1198_; lean_object* v_fst_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1222_; 
v_snd_1197_ = lean_ctor_get(v_a_1193_, 1);
lean_inc(v_snd_1197_);
v_fst_1198_ = lean_ctor_get(v_snd_1197_, 0);
lean_inc(v_fst_1198_);
v_fst_1199_ = lean_ctor_get(v_a_1193_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v_a_1193_);
if (v_isSharedCheck_1222_ == 0)
{
lean_object* v_unused_1223_; 
v_unused_1223_ = lean_ctor_get(v_a_1193_, 1);
lean_dec(v_unused_1223_);
v___x_1201_ = v_a_1193_;
v_isShared_1202_ = v_isSharedCheck_1222_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_fst_1199_);
lean_dec(v_a_1193_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1222_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v_snd_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1220_; 
v_snd_1203_ = lean_ctor_get(v_snd_1197_, 1);
v_isSharedCheck_1220_ = !lean_is_exclusive(v_snd_1197_);
if (v_isSharedCheck_1220_ == 0)
{
lean_object* v_unused_1221_; 
v_unused_1221_ = lean_ctor_get(v_snd_1197_, 0);
lean_dec(v_unused_1221_);
v___x_1205_ = v_snd_1197_;
v_isShared_1206_ = v_isSharedCheck_1220_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_snd_1203_);
lean_dec(v_snd_1197_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1220_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v_fileMap_1207_; lean_object* v_pos_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1212_; 
v_fileMap_1207_ = lean_ctor_get(v_inputCtx_1191_, 2);
lean_inc_ref(v_fileMap_1207_);
lean_dec_ref(v_inputCtx_1191_);
v_pos_1208_ = lean_ctor_get(v_fst_1198_, 0);
lean_inc(v_pos_1208_);
lean_dec(v_fst_1198_);
v___x_1209_ = l_Lean_Elab_HeaderSyntax_imports(v_fst_1199_, v___x_1189_);
v___x_1210_ = l_Lean_FileMap_toPosition(v_fileMap_1207_, v_pos_1208_);
lean_dec(v_pos_1208_);
if (v_isShared_1206_ == 0)
{
lean_ctor_set(v___x_1205_, 0, v___x_1210_);
v___x_1212_ = v___x_1205_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v___x_1210_);
lean_ctor_set(v_reuseFailAlloc_1219_, 1, v_snd_1203_);
v___x_1212_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
lean_object* v___x_1214_; 
if (v_isShared_1202_ == 0)
{
lean_ctor_set(v___x_1201_, 1, v___x_1212_);
lean_ctor_set(v___x_1201_, 0, v___x_1209_);
v___x_1214_ = v___x_1201_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v___x_1209_);
lean_ctor_set(v_reuseFailAlloc_1218_, 1, v___x_1212_);
v___x_1214_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
lean_object* v___x_1216_; 
if (v_isShared_1196_ == 0)
{
lean_ctor_set(v___x_1195_, 0, v___x_1214_);
v___x_1216_ = v___x_1195_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v___x_1214_);
v___x_1216_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
return v___x_1216_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1232_; 
lean_dec_ref(v_inputCtx_1191_);
v_a_1225_ = lean_ctor_get(v___x_1192_, 0);
v_isSharedCheck_1232_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1227_ = v___x_1192_;
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_a_1225_);
lean_dec(v___x_1192_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1230_; 
if (v_isShared_1228_ == 0)
{
v___x_1230_ = v___x_1227_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v_a_1225_);
v___x_1230_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
return v___x_1230_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_parseImports___boxed(lean_object* v_input_1235_, lean_object* v_fileName_1236_, lean_object* v_a_1237_){
_start:
{
lean_object* v_res_1238_; 
v_res_1238_ = l_Lean_Elab_parseImports(v_input_1235_, v_fileName_1236_);
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00Lean_Elab_printImports_spec__0_spec__0(lean_object* v_s_1239_){
_start:
{
lean_object* v___x_1241_; lean_object* v_putStr_1242_; lean_object* v___x_1243_; 
v___x_1241_ = lean_get_stdout();
v_putStr_1242_ = lean_ctor_get(v___x_1241_, 4);
lean_inc_ref(v_putStr_1242_);
lean_dec_ref(v___x_1241_);
v___x_1243_ = lean_apply_2(v_putStr_1242_, v_s_1239_, lean_box(0));
return v___x_1243_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00Lean_Elab_printImports_spec__0_spec__0___boxed(lean_object* v_s_1244_, lean_object* v_a_1245_){
_start:
{
lean_object* v_res_1246_; 
v_res_1246_ = l_IO_print___at___00IO_println___at___00Lean_Elab_printImports_spec__0_spec__0(v_s_1244_);
return v_res_1246_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00Lean_Elab_printImports_spec__0(lean_object* v_s_1247_){
_start:
{
uint32_t v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1249_ = 10;
v___x_1250_ = lean_string_push(v_s_1247_, v___x_1249_);
v___x_1251_ = l_IO_print___at___00IO_println___at___00Lean_Elab_printImports_spec__0_spec__0(v___x_1250_);
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00Lean_Elab_printImports_spec__0___boxed(lean_object* v_s_1252_, lean_object* v_a_1253_){
_start:
{
lean_object* v_res_1254_; 
v_res_1254_ = l_IO_println___at___00Lean_Elab_printImports_spec__0(v_s_1252_);
return v_res_1254_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImports_spec__1(lean_object* v_as_1255_, size_t v_sz_1256_, size_t v_i_1257_, lean_object* v_b_1258_){
_start:
{
uint8_t v___x_1260_; 
v___x_1260_ = lean_usize_dec_lt(v_i_1257_, v_sz_1256_);
if (v___x_1260_ == 0)
{
lean_object* v___x_1261_; 
v___x_1261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1261_, 0, v_b_1258_);
return v___x_1261_;
}
else
{
lean_object* v_a_1262_; lean_object* v_module_1263_; lean_object* v___x_1264_; 
v_a_1262_ = lean_array_uget_borrowed(v_as_1255_, v_i_1257_);
v_module_1263_ = lean_ctor_get(v_a_1262_, 0);
lean_inc(v_module_1263_);
v___x_1264_ = l_Lean_findOLean(v_module_1263_);
if (lean_obj_tag(v___x_1264_) == 0)
{
lean_object* v_a_1265_; lean_object* v___x_1266_; 
v_a_1265_ = lean_ctor_get(v___x_1264_, 0);
lean_inc(v_a_1265_);
lean_dec_ref_known(v___x_1264_, 1);
v___x_1266_ = l_IO_println___at___00Lean_Elab_printImports_spec__0(v_a_1265_);
if (lean_obj_tag(v___x_1266_) == 0)
{
lean_object* v___x_1267_; size_t v___x_1268_; size_t v___x_1269_; 
lean_dec_ref_known(v___x_1266_, 1);
v___x_1267_ = lean_box(0);
v___x_1268_ = ((size_t)1ULL);
v___x_1269_ = lean_usize_add(v_i_1257_, v___x_1268_);
v_i_1257_ = v___x_1269_;
v_b_1258_ = v___x_1267_;
goto _start;
}
else
{
return v___x_1266_;
}
}
else
{
lean_object* v_a_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1278_; 
v_a_1271_ = lean_ctor_get(v___x_1264_, 0);
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1264_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1273_ = v___x_1264_;
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_a_1271_);
lean_dec(v___x_1264_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1276_; 
if (v_isShared_1274_ == 0)
{
v___x_1276_ = v___x_1273_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_a_1271_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImports_spec__1___boxed(lean_object* v_as_1279_, lean_object* v_sz_1280_, lean_object* v_i_1281_, lean_object* v_b_1282_, lean_object* v___y_1283_){
_start:
{
size_t v_sz_boxed_1284_; size_t v_i_boxed_1285_; lean_object* v_res_1286_; 
v_sz_boxed_1284_ = lean_unbox_usize(v_sz_1280_);
lean_dec(v_sz_1280_);
v_i_boxed_1285_ = lean_unbox_usize(v_i_1281_);
lean_dec(v_i_1281_);
v_res_1286_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImports_spec__1(v_as_1279_, v_sz_boxed_1284_, v_i_boxed_1285_, v_b_1282_);
lean_dec_ref(v_as_1279_);
return v_res_1286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_printImports(lean_object* v_input_1287_, lean_object* v_fileName_1288_){
_start:
{
lean_object* v___x_1290_; 
v___x_1290_ = l_Lean_Elab_parseImports(v_input_1287_, v_fileName_1288_);
if (lean_obj_tag(v___x_1290_) == 0)
{
lean_object* v_a_1291_; lean_object* v_fst_1292_; lean_object* v___x_1293_; size_t v_sz_1294_; size_t v___x_1295_; lean_object* v___x_1296_; 
v_a_1291_ = lean_ctor_get(v___x_1290_, 0);
lean_inc(v_a_1291_);
lean_dec_ref_known(v___x_1290_, 1);
v_fst_1292_ = lean_ctor_get(v_a_1291_, 0);
lean_inc(v_fst_1292_);
lean_dec(v_a_1291_);
v___x_1293_ = lean_box(0);
v_sz_1294_ = lean_array_size(v_fst_1292_);
v___x_1295_ = ((size_t)0ULL);
v___x_1296_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImports_spec__1(v_fst_1292_, v_sz_1294_, v___x_1295_, v___x_1293_);
lean_dec(v_fst_1292_);
if (lean_obj_tag(v___x_1296_) == 0)
{
lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1303_; 
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1303_ == 0)
{
lean_object* v_unused_1304_; 
v_unused_1304_ = lean_ctor_get(v___x_1296_, 0);
lean_dec(v_unused_1304_);
v___x_1298_ = v___x_1296_;
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
else
{
lean_dec(v___x_1296_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1301_; 
if (v_isShared_1299_ == 0)
{
lean_ctor_set(v___x_1298_, 0, v___x_1293_);
v___x_1301_ = v___x_1298_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v___x_1293_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
else
{
return v___x_1296_;
}
}
else
{
lean_object* v_a_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1312_; 
v_a_1305_ = lean_ctor_get(v___x_1290_, 0);
v_isSharedCheck_1312_ = !lean_is_exclusive(v___x_1290_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1307_ = v___x_1290_;
v_isShared_1308_ = v_isSharedCheck_1312_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_a_1305_);
lean_dec(v___x_1290_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1312_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v___x_1310_; 
if (v_isShared_1308_ == 0)
{
v___x_1310_ = v___x_1307_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_a_1305_);
v___x_1310_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
return v___x_1310_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_printImports___boxed(lean_object* v_input_1313_, lean_object* v_fileName_1314_, lean_object* v_a_1315_){
_start:
{
lean_object* v_res_1316_; 
v_res_1316_ = l_Lean_Elab_printImports(v_input_1313_, v_fileName_1314_);
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImportSrcs_spec__0(lean_object* v_a_1317_, lean_object* v_as_1318_, size_t v_sz_1319_, size_t v_i_1320_, lean_object* v_b_1321_){
_start:
{
uint8_t v___x_1323_; 
v___x_1323_ = lean_usize_dec_lt(v_i_1320_, v_sz_1319_);
if (v___x_1323_ == 0)
{
lean_object* v___x_1324_; 
lean_dec(v_a_1317_);
v___x_1324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1324_, 0, v_b_1321_);
return v___x_1324_;
}
else
{
lean_object* v_a_1325_; lean_object* v_module_1326_; lean_object* v___x_1327_; 
v_a_1325_ = lean_array_uget_borrowed(v_as_1318_, v_i_1320_);
v_module_1326_ = lean_ctor_get(v_a_1325_, 0);
lean_inc(v_module_1326_);
lean_inc(v_a_1317_);
v___x_1327_ = l_Lean_findLean(v_a_1317_, v_module_1326_);
if (lean_obj_tag(v___x_1327_) == 0)
{
lean_object* v_a_1328_; lean_object* v___x_1329_; 
v_a_1328_ = lean_ctor_get(v___x_1327_, 0);
lean_inc(v_a_1328_);
lean_dec_ref_known(v___x_1327_, 1);
v___x_1329_ = l_IO_println___at___00Lean_Elab_printImports_spec__0(v_a_1328_);
if (lean_obj_tag(v___x_1329_) == 0)
{
lean_object* v___x_1330_; size_t v___x_1331_; size_t v___x_1332_; 
lean_dec_ref_known(v___x_1329_, 1);
v___x_1330_ = lean_box(0);
v___x_1331_ = ((size_t)1ULL);
v___x_1332_ = lean_usize_add(v_i_1320_, v___x_1331_);
v_i_1320_ = v___x_1332_;
v_b_1321_ = v___x_1330_;
goto _start;
}
else
{
lean_dec(v_a_1317_);
return v___x_1329_;
}
}
else
{
lean_object* v_a_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1341_; 
lean_dec(v_a_1317_);
v_a_1334_ = lean_ctor_get(v___x_1327_, 0);
v_isSharedCheck_1341_ = !lean_is_exclusive(v___x_1327_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1336_ = v___x_1327_;
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_a_1334_);
lean_dec(v___x_1327_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v___x_1339_; 
if (v_isShared_1337_ == 0)
{
v___x_1339_ = v___x_1336_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_a_1334_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImportSrcs_spec__0___boxed(lean_object* v_a_1342_, lean_object* v_as_1343_, lean_object* v_sz_1344_, lean_object* v_i_1345_, lean_object* v_b_1346_, lean_object* v___y_1347_){
_start:
{
size_t v_sz_boxed_1348_; size_t v_i_boxed_1349_; lean_object* v_res_1350_; 
v_sz_boxed_1348_ = lean_unbox_usize(v_sz_1344_);
lean_dec(v_sz_1344_);
v_i_boxed_1349_ = lean_unbox_usize(v_i_1345_);
lean_dec(v_i_1345_);
v_res_1350_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImportSrcs_spec__0(v_a_1342_, v_as_1343_, v_sz_boxed_1348_, v_i_boxed_1349_, v_b_1346_);
lean_dec_ref(v_as_1343_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_printImportSrcs(lean_object* v_input_1351_, lean_object* v_fileName_1352_){
_start:
{
lean_object* v___x_1354_; 
v___x_1354_ = l_Lean_getSrcSearchPath();
if (lean_obj_tag(v___x_1354_) == 0)
{
lean_object* v_a_1355_; lean_object* v___x_1356_; 
v_a_1355_ = lean_ctor_get(v___x_1354_, 0);
lean_inc(v_a_1355_);
lean_dec_ref_known(v___x_1354_, 1);
v___x_1356_ = l_Lean_Elab_parseImports(v_input_1351_, v_fileName_1352_);
if (lean_obj_tag(v___x_1356_) == 0)
{
lean_object* v_a_1357_; lean_object* v_fst_1358_; lean_object* v___x_1359_; size_t v_sz_1360_; size_t v___x_1361_; lean_object* v___x_1362_; 
v_a_1357_ = lean_ctor_get(v___x_1356_, 0);
lean_inc(v_a_1357_);
lean_dec_ref_known(v___x_1356_, 1);
v_fst_1358_ = lean_ctor_get(v_a_1357_, 0);
lean_inc(v_fst_1358_);
lean_dec(v_a_1357_);
v___x_1359_ = lean_box(0);
v_sz_1360_ = lean_array_size(v_fst_1358_);
v___x_1361_ = ((size_t)0ULL);
v___x_1362_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImportSrcs_spec__0(v_a_1355_, v_fst_1358_, v_sz_1360_, v___x_1361_, v___x_1359_);
lean_dec(v_fst_1358_);
if (lean_obj_tag(v___x_1362_) == 0)
{
lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1369_; 
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1362_);
if (v_isSharedCheck_1369_ == 0)
{
lean_object* v_unused_1370_; 
v_unused_1370_ = lean_ctor_get(v___x_1362_, 0);
lean_dec(v_unused_1370_);
v___x_1364_ = v___x_1362_;
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
else
{
lean_dec(v___x_1362_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1367_; 
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 0, v___x_1359_);
v___x_1367_ = v___x_1364_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v___x_1359_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
else
{
return v___x_1362_;
}
}
else
{
lean_object* v_a_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1378_; 
lean_dec(v_a_1355_);
v_a_1371_ = lean_ctor_get(v___x_1356_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1373_ = v___x_1356_;
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_a_1371_);
lean_dec(v___x_1356_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1376_; 
if (v_isShared_1374_ == 0)
{
v___x_1376_ = v___x_1373_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_a_1371_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
}
else
{
lean_object* v_a_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1386_; 
lean_dec(v_fileName_1352_);
lean_dec_ref(v_input_1351_);
v_a_1379_ = lean_ctor_get(v___x_1354_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1381_ = v___x_1354_;
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_a_1379_);
lean_dec(v___x_1354_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1384_; 
if (v_isShared_1382_ == 0)
{
v___x_1384_ = v___x_1381_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v_a_1379_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_printImportSrcs___boxed(lean_object* v_input_1387_, lean_object* v_fileName_1388_, lean_object* v_a_1389_){
_start:
{
lean_object* v_res_1390_; 
v_res_1390_ = l_Lean_Elab_printImportSrcs(v_input_1387_, v_fileName_1388_);
return v_res_1390_;
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

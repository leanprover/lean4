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
lean_object* l_Array_instInhabited___redArg();
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
lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_String_Slice_posGE___redArg(lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_get_stdout();
lean_object* l_Lean_findOLean(lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
lean_object* l_Char_utf8Size(uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
extern lean_object* l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
lean_object* l_Lean_Environment_setMainModule(lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(25) << 1) | 1))}};
static const lean_object* l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__1 = (const lean_object*)&l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__1_value;
static lean_once_cell_t l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__2;
static lean_once_cell_t l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__3;
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
LEAN_EXPORT lean_object* l_Lean_Elab_processHeaderCore___lam__0(lean_object*, lean_object*);
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
uint8_t l_Lean_Elab_HeaderSyntax_isModule(lean_object* v_header_8_){
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
LEAN_EXPORT void l_Lean_Elab_HeaderSyntax_isModule_0interp(lean_interpreter_value* stack)
{
lean_object* v_header_8_ = stack[0].m_obj;
uint8_t v_res_14_;
v_res_14_ = l_Lean_Elab_HeaderSyntax_isModule(v_header_8_);
stack->m_num = v_res_14_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_HeaderSyntax_isModule___boxed(lean_object* v_header_15_){
_start:
{
uint8_t v_res_16_; lean_object* v_r_17_; 
v_res_16_ = l_Lean_Elab_HeaderSyntax_isModule(v_header_15_);
lean_dec(v_header_15_);
v_r_17_ = lean_box(v_res_16_);
return v_r_17_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__0___closed__0(void){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = l_Array_instInhabited___redArg();
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__0(lean_object* v_msg_19_){
_start:
{
lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_20_ = lean_obj_once(&l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__0___closed__0, &l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__0___closed__0_once, _init_l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__0___closed__0);
v___x_21_ = lean_panic_fn_borrowed(v___x_20_, v_msg_19_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__1(lean_object* v_msg_22_){
_start:
{
lean_object* v___x_23_; lean_object* v___x_24_; 
v___x_23_ = l_Lean_instInhabitedImport_default;
v___x_24_ = lean_panic_fn_borrowed(v___x_23_, v_msg_22_);
return v___x_24_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8(void){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_37_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__7));
v___x_38_ = lean_unsigned_to_nat(13u);
v___x_39_ = lean_unsigned_to_nat(40u);
v___x_40_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__6));
v___x_41_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__5));
v___x_42_ = l_mkPanicMessageWithDecl(v___x_41_, v___x_40_, v___x_39_, v___x_38_, v___x_37_);
return v___x_42_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2(lean_object* v_moduleTk_61_, uint8_t v___x_62_, size_t v_sz_63_, size_t v_i_64_, lean_object* v_bs_65_){
_start:
{
uint8_t v___x_66_; 
v___x_66_ = lean_usize_dec_lt(v_i_64_, v_sz_63_);
if (v___x_66_ == 0)
{
return v_bs_65_;
}
else
{
lean_object* v___x_67_; lean_object* v_v_68_; lean_object* v___x_69_; lean_object* v_bs_x27_70_; lean_object* v___y_72_; lean_object* v___y_78_; lean_object* v___y_79_; uint8_t v___y_80_; uint8_t v___y_81_; uint8_t v___y_82_; lean_object* v___y_87_; lean_object* v___y_88_; uint8_t v___y_89_; uint8_t v___y_90_; uint8_t v___y_91_; lean_object* v___y_93_; lean_object* v___y_94_; lean_object* v___y_95_; uint8_t v___y_96_; uint8_t v___y_97_; uint8_t v___x_99_; 
v___x_67_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__4));
v_v_68_ = lean_array_uget(v_bs_65_, v_i_64_);
v___x_69_ = lean_unsigned_to_nat(0u);
v_bs_x27_70_ = lean_array_uset(v_bs_65_, v_i_64_, v___x_69_);
lean_inc(v_v_68_);
v___x_99_ = l_Lean_Syntax_isOfKind(v_v_68_, v___x_67_);
if (v___x_99_ == 0)
{
lean_object* v___x_100_; lean_object* v___x_101_; 
lean_dec(v_v_68_);
v___x_100_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8);
v___x_101_ = l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__1(v___x_100_);
v___y_72_ = v___x_101_;
goto v___jp_71_;
}
else
{
lean_object* v___y_103_; lean_object* v___y_104_; lean_object* v_allTk_105_; lean_object* v___x_115_; lean_object* v___y_117_; lean_object* v_metaTk_118_; lean_object* v_publicTk_134_; lean_object* v___x_148_; uint8_t v___x_149_; 
v___x_115_ = lean_unsigned_to_nat(1u);
v___x_148_ = l_Lean_Syntax_getArg(v_v_68_, v___x_69_);
v___x_149_ = l_Lean_Syntax_isNone(v___x_148_);
if (v___x_149_ == 0)
{
uint8_t v___x_150_; 
lean_inc(v___x_148_);
v___x_150_ = l_Lean_Syntax_matchesNull(v___x_148_, v___x_115_);
if (v___x_150_ == 0)
{
lean_object* v___x_151_; lean_object* v___x_152_; 
lean_dec(v___x_148_);
lean_dec(v_v_68_);
v___x_151_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8);
v___x_152_ = l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__1(v___x_151_);
v___y_72_ = v___x_152_;
goto v___jp_71_;
}
else
{
lean_object* v___x_153_; lean_object* v___x_154_; uint8_t v___x_155_; 
v___x_153_ = l_Lean_Syntax_getArg(v___x_148_, v___x_69_);
lean_dec(v___x_148_);
v___x_154_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__14));
lean_inc(v___x_153_);
v___x_155_ = l_Lean_Syntax_isOfKind(v___x_153_, v___x_154_);
if (v___x_155_ == 0)
{
lean_object* v___x_156_; lean_object* v___x_157_; 
lean_dec(v___x_153_);
lean_dec(v_v_68_);
v___x_156_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8);
v___x_157_ = l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__1(v___x_156_);
v___y_72_ = v___x_157_;
goto v___jp_71_;
}
else
{
lean_object* v_publicTk_158_; lean_object* v___x_159_; 
v_publicTk_158_ = l_Lean_Syntax_getArg(v___x_153_, v___x_69_);
lean_dec(v___x_153_);
v___x_159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_159_, 0, v_publicTk_158_);
v_publicTk_134_ = v___x_159_;
goto v___jp_133_;
}
}
}
else
{
lean_object* v___x_160_; 
lean_dec(v___x_148_);
v___x_160_ = lean_box(0);
v_publicTk_134_ = v___x_160_;
goto v___jp_133_;
}
v___jp_102_:
{
lean_object* v___x_106_; lean_object* v___x_107_; uint8_t v___x_108_; 
v___x_106_ = lean_unsigned_to_nat(5u);
v___x_107_ = l_Lean_Syntax_getArg(v_v_68_, v___x_106_);
v___x_108_ = l_Lean_Syntax_matchesNull(v___x_107_, v___x_69_);
if (v___x_108_ == 0)
{
lean_object* v___x_109_; lean_object* v___x_110_; 
lean_dec(v_allTk_105_);
lean_dec(v___y_104_);
lean_dec(v___y_103_);
lean_dec(v_v_68_);
v___x_109_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8);
v___x_110_ = l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__1(v___x_109_);
v___y_72_ = v___x_110_;
goto v___jp_71_;
}
else
{
lean_object* v___x_111_; lean_object* v_n_112_; lean_object* v___x_113_; 
v___x_111_ = lean_unsigned_to_nat(4u);
v_n_112_ = l_Lean_Syntax_getArg(v_v_68_, v___x_111_);
lean_dec(v_v_68_);
v___x_113_ = l_Lean_TSyntax_getId(v_n_112_);
lean_dec(v_n_112_);
if (lean_obj_tag(v_allTk_105_) == 0)
{
uint8_t v___x_114_; 
v___x_114_ = 0;
v___y_93_ = v___x_113_;
v___y_94_ = v___y_103_;
v___y_95_ = v___y_104_;
v___y_96_ = v___x_108_;
v___y_97_ = v___x_114_;
goto v___jp_92_;
}
else
{
lean_dec_ref_known(v_allTk_105_, 1);
v___y_93_ = v___x_113_;
v___y_94_ = v___y_103_;
v___y_95_ = v___y_104_;
v___y_96_ = v___x_108_;
v___y_97_ = v___x_108_;
goto v___jp_92_;
}
}
}
v___jp_116_:
{
lean_object* v___x_119_; lean_object* v___x_120_; uint8_t v___x_121_; 
v___x_119_ = lean_unsigned_to_nat(3u);
v___x_120_ = l_Lean_Syntax_getArg(v_v_68_, v___x_119_);
v___x_121_ = l_Lean_Syntax_isNone(v___x_120_);
if (v___x_121_ == 0)
{
uint8_t v___x_122_; 
lean_inc(v___x_120_);
v___x_122_ = l_Lean_Syntax_matchesNull(v___x_120_, v___x_115_);
if (v___x_122_ == 0)
{
lean_object* v___x_123_; lean_object* v___x_124_; 
lean_dec(v___x_120_);
lean_dec(v_metaTk_118_);
lean_dec(v___y_117_);
lean_dec(v_v_68_);
v___x_123_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8);
v___x_124_ = l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__1(v___x_123_);
v___y_72_ = v___x_124_;
goto v___jp_71_;
}
else
{
lean_object* v___x_125_; lean_object* v___x_126_; uint8_t v___x_127_; 
v___x_125_ = l_Lean_Syntax_getArg(v___x_120_, v___x_69_);
lean_dec(v___x_120_);
v___x_126_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__10));
lean_inc(v___x_125_);
v___x_127_ = l_Lean_Syntax_isOfKind(v___x_125_, v___x_126_);
if (v___x_127_ == 0)
{
lean_object* v___x_128_; lean_object* v___x_129_; 
lean_dec(v___x_125_);
lean_dec(v_metaTk_118_);
lean_dec(v___y_117_);
lean_dec(v_v_68_);
v___x_128_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8);
v___x_129_ = l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__1(v___x_128_);
v___y_72_ = v___x_129_;
goto v___jp_71_;
}
else
{
lean_object* v_allTk_130_; lean_object* v___x_131_; 
v_allTk_130_ = l_Lean_Syntax_getArg(v___x_125_, v___x_69_);
lean_dec(v___x_125_);
v___x_131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_131_, 0, v_allTk_130_);
v___y_103_ = v_metaTk_118_;
v___y_104_ = v___y_117_;
v_allTk_105_ = v___x_131_;
goto v___jp_102_;
}
}
}
else
{
lean_object* v___x_132_; 
lean_dec(v___x_120_);
v___x_132_ = lean_box(0);
v___y_103_ = v_metaTk_118_;
v___y_104_ = v___y_117_;
v_allTk_105_ = v___x_132_;
goto v___jp_102_;
}
}
v___jp_133_:
{
lean_object* v___x_135_; uint8_t v___x_136_; 
v___x_135_ = l_Lean_Syntax_getArg(v_v_68_, v___x_115_);
v___x_136_ = l_Lean_Syntax_isNone(v___x_135_);
if (v___x_136_ == 0)
{
uint8_t v___x_137_; 
lean_inc(v___x_135_);
v___x_137_ = l_Lean_Syntax_matchesNull(v___x_135_, v___x_115_);
if (v___x_137_ == 0)
{
lean_object* v___x_138_; lean_object* v___x_139_; 
lean_dec(v___x_135_);
lean_dec(v_publicTk_134_);
lean_dec(v_v_68_);
v___x_138_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8);
v___x_139_ = l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__1(v___x_138_);
v___y_72_ = v___x_139_;
goto v___jp_71_;
}
else
{
lean_object* v___x_140_; lean_object* v___x_141_; uint8_t v___x_142_; 
v___x_140_ = l_Lean_Syntax_getArg(v___x_135_, v___x_69_);
lean_dec(v___x_135_);
v___x_141_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__12));
lean_inc(v___x_140_);
v___x_142_ = l_Lean_Syntax_isOfKind(v___x_140_, v___x_141_);
if (v___x_142_ == 0)
{
lean_object* v___x_143_; lean_object* v___x_144_; 
lean_dec(v___x_140_);
lean_dec(v_publicTk_134_);
lean_dec(v_v_68_);
v___x_143_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8);
v___x_144_ = l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__1(v___x_143_);
v___y_72_ = v___x_144_;
goto v___jp_71_;
}
else
{
lean_object* v_metaTk_145_; lean_object* v___x_146_; 
v_metaTk_145_ = l_Lean_Syntax_getArg(v___x_140_, v___x_69_);
lean_dec(v___x_140_);
v___x_146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_146_, 0, v_metaTk_145_);
v___y_117_ = v_publicTk_134_;
v_metaTk_118_ = v___x_146_;
goto v___jp_116_;
}
}
}
else
{
lean_object* v___x_147_; 
lean_dec(v___x_135_);
v___x_147_ = lean_box(0);
v___y_117_ = v_publicTk_134_;
v_metaTk_118_ = v___x_147_;
goto v___jp_116_;
}
}
}
v___jp_71_:
{
size_t v___x_73_; size_t v___x_74_; lean_object* v___x_75_; 
v___x_73_ = ((size_t)1ULL);
v___x_74_ = lean_usize_add(v_i_64_, v___x_73_);
v___x_75_ = lean_array_uset(v_bs_x27_70_, v_i_64_, v___y_72_);
v_i_64_ = v___x_74_;
v_bs_65_ = v___x_75_;
goto _start;
}
v___jp_77_:
{
if (lean_obj_tag(v___y_79_) == 0)
{
uint8_t v___x_83_; lean_object* v___x_84_; 
v___x_83_ = 0;
v___x_84_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_84_, 0, v___y_78_);
lean_ctor_set_uint8(v___x_84_, sizeof(void*)*1, v___y_80_);
lean_ctor_set_uint8(v___x_84_, sizeof(void*)*1 + 1, v___y_82_);
lean_ctor_set_uint8(v___x_84_, sizeof(void*)*1 + 2, v___x_83_);
v___y_72_ = v___x_84_;
goto v___jp_71_;
}
else
{
lean_object* v___x_85_; 
lean_dec_ref_known(v___y_79_, 1);
v___x_85_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_85_, 0, v___y_78_);
lean_ctor_set_uint8(v___x_85_, sizeof(void*)*1, v___y_80_);
lean_ctor_set_uint8(v___x_85_, sizeof(void*)*1 + 1, v___y_82_);
lean_ctor_set_uint8(v___x_85_, sizeof(void*)*1 + 2, v___y_81_);
v___y_72_ = v___x_85_;
goto v___jp_71_;
}
}
v___jp_86_:
{
if (lean_obj_tag(v_moduleTk_61_) == 0)
{
v___y_78_ = v___y_87_;
v___y_79_ = v___y_88_;
v___y_80_ = v___y_89_;
v___y_81_ = v___y_90_;
v___y_82_ = v___y_90_;
goto v___jp_77_;
}
else
{
v___y_78_ = v___y_87_;
v___y_79_ = v___y_88_;
v___y_80_ = v___y_89_;
v___y_81_ = v___y_90_;
v___y_82_ = v___y_91_;
goto v___jp_77_;
}
}
v___jp_92_:
{
if (lean_obj_tag(v___y_95_) == 0)
{
uint8_t v___x_98_; 
v___x_98_ = 0;
v___y_87_ = v___y_93_;
v___y_88_ = v___y_94_;
v___y_89_ = v___y_97_;
v___y_90_ = v___y_96_;
v___y_91_ = v___x_98_;
goto v___jp_86_;
}
else
{
lean_dec_ref_known(v___y_95_, 1);
if (v___y_96_ == 0)
{
v___y_87_ = v___y_93_;
v___y_88_ = v___y_94_;
v___y_89_ = v___y_97_;
v___y_90_ = v___y_96_;
v___y_91_ = v___y_96_;
goto v___jp_86_;
}
else
{
v___y_78_ = v___y_93_;
v___y_79_ = v___y_94_;
v___y_80_ = v___y_97_;
v___y_81_ = v___y_96_;
v___y_82_ = v___x_62_;
goto v___jp_77_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_moduleTk_61_ = stack[0].m_obj;
uint8_t v___x_62_ = stack[1].m_num;
size_t v_sz_63_ = stack[2].m_num;
size_t v_i_64_ = stack[3].m_num;
lean_object* v_bs_65_ = stack[4].m_obj;
lean_object* v_res_161_;
v_res_161_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2(v_moduleTk_61_, v___x_62_, v_sz_63_, v_i_64_, v_bs_65_);
stack->m_obj
 = v_res_161_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___boxed(lean_object* v_moduleTk_162_, lean_object* v___x_163_, lean_object* v_sz_164_, lean_object* v_i_165_, lean_object* v_bs_166_){
_start:
{
uint8_t v___x_1480__boxed_167_; size_t v_sz_boxed_168_; size_t v_i_boxed_169_; lean_object* v_res_170_; 
v___x_1480__boxed_167_ = lean_unbox(v___x_163_);
v_sz_boxed_168_ = lean_unbox_usize(v_sz_164_);
lean_dec(v_sz_164_);
v_i_boxed_169_ = lean_unbox_usize(v_i_165_);
lean_dec(v_i_165_);
v_res_170_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2(v_moduleTk_162_, v___x_1480__boxed_167_, v_sz_boxed_168_, v_i_boxed_169_, v_bs_166_);
lean_dec(v_moduleTk_162_);
return v_res_170_;
}
}
static lean_object* _init_l_Lean_Elab_HeaderSyntax_imports___closed__2(void){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_177_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__7));
v___x_178_ = lean_unsigned_to_nat(9u);
v___x_179_ = lean_unsigned_to_nat(41u);
v___x_180_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__6));
v___x_181_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__5));
v___x_182_ = l_mkPanicMessageWithDecl(v___x_181_, v___x_180_, v___x_179_, v___x_178_, v___x_177_);
return v___x_182_;
}
}
lean_object* l_Lean_Elab_HeaderSyntax_imports(lean_object* v_stx_200_, uint8_t v_includeInit_201_){
_start:
{
lean_object* v___x_202_; uint8_t v___x_203_; lean_object* v___y_205_; lean_object* v___y_206_; lean_object* v___y_207_; 
v___x_202_ = ((lean_object*)(l_Lean_Elab_HeaderSyntax_imports___closed__1));
lean_inc(v_stx_200_);
v___x_203_ = l_Lean_Syntax_isOfKind(v_stx_200_, v___x_202_);
if (v___x_203_ == 0)
{
lean_object* v___x_212_; lean_object* v___x_213_; 
lean_dec(v_stx_200_);
v___x_212_ = lean_obj_once(&l_Lean_Elab_HeaderSyntax_imports___closed__2, &l_Lean_Elab_HeaderSyntax_imports___closed__2_once, _init_l_Lean_Elab_HeaderSyntax_imports___closed__2);
v___x_213_ = l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__0(v___x_212_);
return v___x_213_;
}
else
{
lean_object* v___x_214_; lean_object* v___y_216_; lean_object* v___y_217_; lean_object* v___y_220_; lean_object* v_preludeTk_221_; lean_object* v_moduleTk_233_; lean_object* v___x_248_; uint8_t v___x_249_; 
v___x_214_ = lean_unsigned_to_nat(0u);
v___x_248_ = l_Lean_Syntax_getArg(v_stx_200_, v___x_214_);
v___x_249_ = l_Lean_Syntax_isNone(v___x_248_);
if (v___x_249_ == 0)
{
lean_object* v___x_250_; uint8_t v___x_251_; 
v___x_250_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_248_);
v___x_251_ = l_Lean_Syntax_matchesNull(v___x_248_, v___x_250_);
if (v___x_251_ == 0)
{
lean_object* v___x_252_; lean_object* v___x_253_; 
lean_dec(v___x_248_);
lean_dec(v_stx_200_);
v___x_252_ = lean_obj_once(&l_Lean_Elab_HeaderSyntax_imports___closed__2, &l_Lean_Elab_HeaderSyntax_imports___closed__2_once, _init_l_Lean_Elab_HeaderSyntax_imports___closed__2);
v___x_253_ = l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__0(v___x_252_);
return v___x_253_;
}
else
{
lean_object* v___x_254_; lean_object* v___x_255_; uint8_t v___x_256_; 
v___x_254_ = l_Lean_Syntax_getArg(v___x_248_, v___x_214_);
lean_dec(v___x_248_);
v___x_255_ = ((lean_object*)(l_Lean_Elab_HeaderSyntax_imports___closed__9));
lean_inc(v___x_254_);
v___x_256_ = l_Lean_Syntax_isOfKind(v___x_254_, v___x_255_);
if (v___x_256_ == 0)
{
lean_object* v___x_257_; lean_object* v___x_258_; 
lean_dec(v___x_254_);
lean_dec(v_stx_200_);
v___x_257_ = lean_obj_once(&l_Lean_Elab_HeaderSyntax_imports___closed__2, &l_Lean_Elab_HeaderSyntax_imports___closed__2_once, _init_l_Lean_Elab_HeaderSyntax_imports___closed__2);
v___x_258_ = l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__0(v___x_257_);
return v___x_258_;
}
else
{
lean_object* v_moduleTk_259_; lean_object* v___x_260_; 
v_moduleTk_259_ = l_Lean_Syntax_getArg(v___x_254_, v___x_214_);
lean_dec(v___x_254_);
v___x_260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_260_, 0, v_moduleTk_259_);
v_moduleTk_233_ = v___x_260_;
goto v___jp_232_;
}
}
}
else
{
lean_object* v___x_261_; 
lean_dec(v___x_248_);
v___x_261_ = lean_box(0);
v_moduleTk_233_ = v___x_261_;
goto v___jp_232_;
}
v___jp_215_:
{
lean_object* v___x_218_; 
v___x_218_ = ((lean_object*)(l_Lean_Elab_HeaderSyntax_imports___closed__3));
v___y_205_ = v___y_216_;
v___y_206_ = v___y_217_;
v___y_207_ = v___x_218_;
goto v___jp_204_;
}
v___jp_219_:
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v_importsStx_224_; 
v___x_222_ = lean_unsigned_to_nat(2u);
v___x_223_ = l_Lean_Syntax_getArg(v_stx_200_, v___x_222_);
lean_dec(v_stx_200_);
v_importsStx_224_ = l_Lean_Syntax_getArgs(v___x_223_);
lean_dec(v___x_223_);
if (lean_obj_tag(v_preludeTk_221_) == 0)
{
if (v___x_203_ == 0)
{
v___y_216_ = v_importsStx_224_;
v___y_217_ = v___y_220_;
goto v___jp_215_;
}
else
{
if (v_includeInit_201_ == 0)
{
v___y_216_ = v_importsStx_224_;
v___y_217_ = v___y_220_;
goto v___jp_215_;
}
else
{
lean_object* v___x_225_; uint8_t v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_225_ = ((lean_object*)(l_Lean_Elab_HeaderSyntax_imports___closed__5));
v___x_226_ = 0;
v___x_227_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_227_, 0, v___x_225_);
lean_ctor_set_uint8(v___x_227_, sizeof(void*)*1, v___x_226_);
lean_ctor_set_uint8(v___x_227_, sizeof(void*)*1 + 1, v___x_203_);
lean_ctor_set_uint8(v___x_227_, sizeof(void*)*1 + 2, v___x_226_);
v___x_228_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_228_, 0, v___x_225_);
lean_ctor_set_uint8(v___x_228_, sizeof(void*)*1, v___x_226_);
lean_ctor_set_uint8(v___x_228_, sizeof(void*)*1 + 1, v___x_203_);
lean_ctor_set_uint8(v___x_228_, sizeof(void*)*1 + 2, v___x_203_);
v___x_229_ = lean_mk_empty_array_with_capacity(v___x_222_);
v___x_230_ = lean_array_push(v___x_229_, v___x_227_);
v___x_231_ = lean_array_push(v___x_230_, v___x_228_);
v___y_205_ = v_importsStx_224_;
v___y_206_ = v___y_220_;
v___y_207_ = v___x_231_;
goto v___jp_204_;
}
}
}
else
{
lean_dec_ref_known(v_preludeTk_221_, 1);
v___y_216_ = v_importsStx_224_;
v___y_217_ = v___y_220_;
goto v___jp_215_;
}
}
v___jp_232_:
{
lean_object* v___x_234_; lean_object* v___x_235_; uint8_t v___x_236_; 
v___x_234_ = lean_unsigned_to_nat(1u);
v___x_235_ = l_Lean_Syntax_getArg(v_stx_200_, v___x_234_);
v___x_236_ = l_Lean_Syntax_isNone(v___x_235_);
if (v___x_236_ == 0)
{
uint8_t v___x_237_; 
lean_inc(v___x_235_);
v___x_237_ = l_Lean_Syntax_matchesNull(v___x_235_, v___x_234_);
if (v___x_237_ == 0)
{
lean_object* v___x_238_; lean_object* v___x_239_; 
lean_dec(v___x_235_);
lean_dec(v_moduleTk_233_);
lean_dec(v_stx_200_);
v___x_238_ = lean_obj_once(&l_Lean_Elab_HeaderSyntax_imports___closed__2, &l_Lean_Elab_HeaderSyntax_imports___closed__2_once, _init_l_Lean_Elab_HeaderSyntax_imports___closed__2);
v___x_239_ = l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__0(v___x_238_);
return v___x_239_;
}
else
{
lean_object* v___x_240_; lean_object* v___x_241_; uint8_t v___x_242_; 
v___x_240_ = l_Lean_Syntax_getArg(v___x_235_, v___x_214_);
lean_dec(v___x_235_);
v___x_241_ = ((lean_object*)(l_Lean_Elab_HeaderSyntax_imports___closed__7));
lean_inc(v___x_240_);
v___x_242_ = l_Lean_Syntax_isOfKind(v___x_240_, v___x_241_);
if (v___x_242_ == 0)
{
lean_object* v___x_243_; lean_object* v___x_244_; 
lean_dec(v___x_240_);
lean_dec(v_moduleTk_233_);
lean_dec(v_stx_200_);
v___x_243_ = lean_obj_once(&l_Lean_Elab_HeaderSyntax_imports___closed__2, &l_Lean_Elab_HeaderSyntax_imports___closed__2_once, _init_l_Lean_Elab_HeaderSyntax_imports___closed__2);
v___x_244_ = l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__0(v___x_243_);
return v___x_244_;
}
else
{
lean_object* v_preludeTk_245_; lean_object* v___x_246_; 
v_preludeTk_245_ = l_Lean_Syntax_getArg(v___x_240_, v___x_214_);
lean_dec(v___x_240_);
v___x_246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_246_, 0, v_preludeTk_245_);
v___y_220_ = v_moduleTk_233_;
v_preludeTk_221_ = v___x_246_;
goto v___jp_219_;
}
}
}
else
{
lean_object* v___x_247_; 
lean_dec(v___x_235_);
v___x_247_ = lean_box(0);
v___y_220_ = v_moduleTk_233_;
v_preludeTk_221_ = v___x_247_;
goto v___jp_219_;
}
}
}
v___jp_204_:
{
size_t v_sz_208_; size_t v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v_sz_208_ = lean_array_size(v___y_205_);
v___x_209_ = ((size_t)0ULL);
v___x_210_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2(v___y_206_, v___x_203_, v_sz_208_, v___x_209_, v___y_205_);
lean_dec(v___y_206_);
v___x_211_ = l_Array_append___redArg(v___y_207_, v___x_210_);
lean_dec_ref(v___x_210_);
return v___x_211_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_HeaderSyntax_imports_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_200_ = stack[0].m_obj;
uint8_t v_includeInit_201_ = stack[1].m_num;
lean_object* v_res_262_;
v_res_262_ = l_Lean_Elab_HeaderSyntax_imports(v_stx_200_, v_includeInit_201_);
stack->m_obj
 = v_res_262_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_HeaderSyntax_imports___boxed(lean_object* v_stx_263_, lean_object* v_includeInit_264_){
_start:
{
uint8_t v_includeInit_boxed_265_; lean_object* v_res_266_; 
v_includeInit_boxed_265_ = lean_unbox(v_includeInit_264_);
v_res_266_ = l_Lean_Elab_HeaderSyntax_imports(v_stx_263_, v_includeInit_boxed_265_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_HeaderSyntax_toModuleHeader(lean_object* v_stx_267_){
_start:
{
uint8_t v___x_268_; lean_object* v___x_269_; uint8_t v___x_270_; lean_object* v___x_271_; 
v___x_268_ = 1;
lean_inc(v_stx_267_);
v___x_269_ = l_Lean_Elab_HeaderSyntax_imports(v_stx_267_, v___x_268_);
v___x_270_ = l_Lean_Elab_HeaderSyntax_isModule(v_stx_267_);
lean_dec(v_stx_267_);
v___x_271_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_271_, 0, v___x_269_);
lean_ctor_set_uint8(v___x_271_, sizeof(void*)*1, v___x_270_);
return v___x_271_;
}
}
lean_object* l_Lean_Elab_headerToImports(lean_object* v_stx_272_, uint8_t v_includeInit_273_){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = l_Lean_Elab_HeaderSyntax_imports(v_stx_272_, v_includeInit_273_);
return v___x_274_;
}
}
LEAN_EXPORT void l_Lean_Elab_headerToImports_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_272_ = stack[0].m_obj;
uint8_t v_includeInit_273_ = stack[1].m_num;
lean_object* v_res_275_;
v_res_275_ = l_Lean_Elab_headerToImports(v_stx_272_, v_includeInit_273_);
stack->m_obj
 = v_res_275_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_headerToImports___boxed(lean_object* v_stx_276_, lean_object* v_includeInit_277_){
_start:
{
uint8_t v_includeInit_boxed_278_; lean_object* v_res_279_; 
v_includeInit_boxed_278_ = lean_unbox(v_includeInit_277_);
v_res_279_ = l_Lean_Elab_headerToImports(v_stx_276_, v_includeInit_boxed_278_);
return v_res_279_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_Elab_checkDeprecatedImports_spec__0(lean_object* v_opts_280_, lean_object* v_opt_281_){
_start:
{
lean_object* v_name_282_; lean_object* v_defValue_283_; lean_object* v_map_284_; lean_object* v___x_285_; 
v_name_282_ = lean_ctor_get(v_opt_281_, 0);
v_defValue_283_ = lean_ctor_get(v_opt_281_, 1);
v_map_284_ = lean_ctor_get(v_opts_280_, 0);
v___x_285_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_284_, v_name_282_);
if (lean_obj_tag(v___x_285_) == 0)
{
uint8_t v___x_286_; 
v___x_286_ = lean_unbox(v_defValue_283_);
return v___x_286_;
}
else
{
lean_object* v_val_287_; 
v_val_287_ = lean_ctor_get(v___x_285_, 0);
lean_inc(v_val_287_);
lean_dec_ref_known(v___x_285_, 1);
if (lean_obj_tag(v_val_287_) == 1)
{
uint8_t v_v_288_; 
v_v_288_ = lean_ctor_get_uint8(v_val_287_, 0);
lean_dec_ref_known(v_val_287_, 0);
return v_v_288_;
}
else
{
uint8_t v___x_289_; 
lean_dec(v_val_287_);
v___x_289_ = lean_unbox(v_defValue_283_);
return v___x_289_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Elab_checkDeprecatedImports_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_280_ = stack[0].m_obj;
lean_object* v_opt_281_ = stack[1].m_obj;
uint8_t v_res_290_;
v_res_290_ = l_Lean_Option_get___at___00Lean_Elab_checkDeprecatedImports_spec__0(v_opts_280_, v_opt_281_);
stack->m_num = v_res_290_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_checkDeprecatedImports_spec__0___boxed(lean_object* v_opts_291_, lean_object* v_opt_292_){
_start:
{
uint8_t v_res_293_; lean_object* v_r_294_; 
v_res_293_ = l_Lean_Option_get___at___00Lean_Elab_checkDeprecatedImports_spec__0(v_opts_291_, v_opt_292_);
lean_dec_ref(v_opt_292_);
lean_dec_ref(v_opts_291_);
v_r_294_ = lean_box(v_res_293_);
return v_r_294_;
}
}
uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_spec__2___redArg(lean_object* v_s_295_, lean_object* v_a_296_, uint8_t v_b_297_){
_start:
{
uint8_t v___x_298_; 
v___x_298_ = 0;
switch(lean_obj_tag(v_a_296_))
{
case 0:
{
lean_object* v_pos_299_; lean_object* v_startInclusive_300_; lean_object* v_endExclusive_301_; lean_object* v___x_302_; uint8_t v_decide_303_; 
v_pos_299_ = lean_ctor_get(v_a_296_, 0);
lean_inc(v_pos_299_);
lean_dec_ref_known(v_a_296_, 1);
v_startInclusive_300_ = lean_ctor_get(v_s_295_, 1);
v_endExclusive_301_ = lean_ctor_get(v_s_295_, 2);
v___x_302_ = lean_nat_sub(v_endExclusive_301_, v_startInclusive_300_);
v_decide_303_ = lean_nat_dec_eq(v_pos_299_, v___x_302_);
lean_dec(v___x_302_);
lean_dec(v_pos_299_);
if (v_decide_303_ == 0)
{
uint8_t v___x_304_; 
v___x_304_ = 1;
return v___x_304_;
}
else
{
return v_decide_303_;
}
}
case 1:
{
lean_object* v_pos_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_318_; 
v_pos_305_ = lean_ctor_get(v_a_296_, 0);
v_isSharedCheck_318_ = !lean_is_exclusive(v_a_296_);
if (v_isSharedCheck_318_ == 0)
{
v___x_307_ = v_a_296_;
v_isShared_308_ = v_isSharedCheck_318_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_pos_305_);
lean_dec(v_a_296_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_318_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v_str_309_; lean_object* v_startInclusive_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_315_; 
v_str_309_ = lean_ctor_get(v_s_295_, 0);
v_startInclusive_310_ = lean_ctor_get(v_s_295_, 1);
v___x_311_ = lean_nat_add(v_startInclusive_310_, v_pos_305_);
lean_dec(v_pos_305_);
v___x_312_ = lean_string_utf8_next_fast(v_str_309_, v___x_311_);
lean_dec(v___x_311_);
v___x_313_ = lean_nat_sub(v___x_312_, v_startInclusive_310_);
if (v_isShared_308_ == 0)
{
lean_ctor_set_tag(v___x_307_, 0);
lean_ctor_set(v___x_307_, 0, v___x_313_);
v___x_315_ = v___x_307_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v___x_313_);
v___x_315_ = v_reuseFailAlloc_317_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
v_a_296_ = v___x_315_;
v_b_297_ = v___x_298_;
goto _start;
}
}
}
case 2:
{
lean_object* v_needle_319_; lean_object* v_table_320_; lean_object* v_stackPos_321_; lean_object* v_needlePos_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_377_; 
v_needle_319_ = lean_ctor_get(v_a_296_, 0);
v_table_320_ = lean_ctor_get(v_a_296_, 1);
v_stackPos_321_ = lean_ctor_get(v_a_296_, 2);
v_needlePos_322_ = lean_ctor_get(v_a_296_, 3);
v_isSharedCheck_377_ = !lean_is_exclusive(v_a_296_);
if (v_isSharedCheck_377_ == 0)
{
v___x_324_ = v_a_296_;
v_isShared_325_ = v_isSharedCheck_377_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_needlePos_322_);
lean_inc(v_stackPos_321_);
lean_inc(v_table_320_);
lean_inc(v_needle_319_);
lean_dec(v_a_296_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_377_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v_str_326_; lean_object* v_startInclusive_327_; lean_object* v_endExclusive_328_; lean_object* v_str_329_; lean_object* v_startInclusive_330_; lean_object* v_endExclusive_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; uint8_t v___x_336_; 
v_str_326_ = lean_ctor_get(v_needle_319_, 0);
v_startInclusive_327_ = lean_ctor_get(v_needle_319_, 1);
v_endExclusive_328_ = lean_ctor_get(v_needle_319_, 2);
v_str_329_ = lean_ctor_get(v_s_295_, 0);
v_startInclusive_330_ = lean_ctor_get(v_s_295_, 1);
v_endExclusive_331_ = lean_ctor_get(v_s_295_, 2);
v___x_332_ = lean_nat_sub(v_stackPos_321_, v_needlePos_322_);
v___x_333_ = lean_nat_sub(v_endExclusive_328_, v_startInclusive_327_);
v___x_334_ = lean_nat_add(v___x_332_, v___x_333_);
v___x_335_ = lean_nat_sub(v_endExclusive_331_, v_startInclusive_330_);
v___x_336_ = lean_nat_dec_le(v___x_334_, v___x_335_);
lean_dec(v___x_334_);
if (v___x_336_ == 0)
{
lean_object* v___x_337_; lean_object* v___x_338_; uint8_t v___x_339_; 
lean_dec(v___x_333_);
lean_del_object(v___x_324_);
lean_dec(v_needlePos_322_);
lean_dec(v_stackPos_321_);
lean_dec_ref(v_table_320_);
lean_dec_ref(v_needle_319_);
v___x_337_ = lean_unsigned_to_nat(1u);
v___x_338_ = lean_nat_add(v___x_332_, v___x_337_);
lean_dec(v___x_332_);
v___x_339_ = lean_nat_dec_le(v___x_338_, v___x_335_);
lean_dec(v___x_335_);
lean_dec(v___x_338_);
if (v___x_339_ == 0)
{
return v_b_297_;
}
else
{
lean_object* v___x_340_; 
v___x_340_ = lean_box(3);
v_a_296_ = v___x_340_;
v_b_297_ = v___x_298_;
goto _start;
}
}
else
{
lean_object* v___x_342_; uint8_t v_stackByte_343_; lean_object* v___x_344_; uint8_t v_patByte_345_; uint8_t v___x_346_; 
lean_dec(v___x_335_);
lean_dec(v___x_332_);
v___x_342_ = lean_nat_add(v_startInclusive_330_, v_stackPos_321_);
v_stackByte_343_ = lean_string_get_byte_fast(v_str_329_, v___x_342_);
v___x_344_ = lean_nat_add(v_startInclusive_327_, v_needlePos_322_);
v_patByte_345_ = lean_string_get_byte_fast(v_str_326_, v___x_344_);
v___x_346_ = lean_uint8_dec_eq(v_stackByte_343_, v_patByte_345_);
if (v___x_346_ == 0)
{
lean_object* v___x_347_; uint8_t v_decide_348_; 
lean_dec(v___x_333_);
v___x_347_ = lean_unsigned_to_nat(0u);
v_decide_348_ = lean_nat_dec_eq(v_needlePos_322_, v___x_347_);
if (v_decide_348_ == 0)
{
lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v_newNeedlePos_351_; uint8_t v___x_352_; 
v___x_349_ = lean_unsigned_to_nat(1u);
v___x_350_ = lean_nat_sub(v_needlePos_322_, v___x_349_);
lean_dec(v_needlePos_322_);
v_newNeedlePos_351_ = lean_array_fget_borrowed(v_table_320_, v___x_350_);
lean_dec(v___x_350_);
v___x_352_ = lean_nat_dec_eq(v_newNeedlePos_351_, v___x_347_);
if (v___x_352_ == 0)
{
lean_object* v___x_354_; 
lean_inc(v_newNeedlePos_351_);
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 3, v_newNeedlePos_351_);
v___x_354_ = v___x_324_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_needle_319_);
lean_ctor_set(v_reuseFailAlloc_356_, 1, v_table_320_);
lean_ctor_set(v_reuseFailAlloc_356_, 2, v_stackPos_321_);
lean_ctor_set(v_reuseFailAlloc_356_, 3, v_newNeedlePos_351_);
v___x_354_ = v_reuseFailAlloc_356_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
v_a_296_ = v___x_354_;
v_b_297_ = v___x_298_;
goto _start;
}
}
else
{
lean_object* v_nextStackPos_357_; lean_object* v___x_359_; 
v_nextStackPos_357_ = l_String_Slice_posGE___redArg(v_s_295_, v_stackPos_321_);
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 3, v___x_347_);
lean_ctor_set(v___x_324_, 2, v_nextStackPos_357_);
v___x_359_ = v___x_324_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_needle_319_);
lean_ctor_set(v_reuseFailAlloc_361_, 1, v_table_320_);
lean_ctor_set(v_reuseFailAlloc_361_, 2, v_nextStackPos_357_);
lean_ctor_set(v_reuseFailAlloc_361_, 3, v___x_347_);
v___x_359_ = v_reuseFailAlloc_361_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
v_a_296_ = v___x_359_;
v_b_297_ = v___x_298_;
goto _start;
}
}
}
else
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v_nextStackPos_364_; lean_object* v___x_366_; 
lean_dec(v_needlePos_322_);
v___x_362_ = lean_unsigned_to_nat(1u);
v___x_363_ = lean_nat_add(v_stackPos_321_, v___x_362_);
lean_dec(v_stackPos_321_);
v_nextStackPos_364_ = l_String_Slice_posGE___redArg(v_s_295_, v___x_363_);
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 3, v___x_347_);
lean_ctor_set(v___x_324_, 2, v_nextStackPos_364_);
v___x_366_ = v___x_324_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_needle_319_);
lean_ctor_set(v_reuseFailAlloc_368_, 1, v_table_320_);
lean_ctor_set(v_reuseFailAlloc_368_, 2, v_nextStackPos_364_);
lean_ctor_set(v_reuseFailAlloc_368_, 3, v___x_347_);
v___x_366_ = v_reuseFailAlloc_368_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
v_a_296_ = v___x_366_;
v_b_297_ = v___x_298_;
goto _start;
}
}
}
else
{
lean_object* v___x_369_; lean_object* v_nextNeedlePos_370_; uint8_t v_decide_371_; 
v___x_369_ = lean_unsigned_to_nat(1u);
v_nextNeedlePos_370_ = lean_nat_add(v_needlePos_322_, v___x_369_);
lean_dec(v_needlePos_322_);
v_decide_371_ = lean_nat_dec_eq(v_nextNeedlePos_370_, v___x_333_);
lean_dec(v___x_333_);
if (v_decide_371_ == 0)
{
lean_object* v_nextStackPos_372_; lean_object* v___x_374_; 
v_nextStackPos_372_ = lean_nat_add(v_stackPos_321_, v___x_369_);
lean_dec(v_stackPos_321_);
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 3, v_nextNeedlePos_370_);
lean_ctor_set(v___x_324_, 2, v_nextStackPos_372_);
v___x_374_ = v___x_324_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_needle_319_);
lean_ctor_set(v_reuseFailAlloc_376_, 1, v_table_320_);
lean_ctor_set(v_reuseFailAlloc_376_, 2, v_nextStackPos_372_);
lean_ctor_set(v_reuseFailAlloc_376_, 3, v_nextNeedlePos_370_);
v___x_374_ = v_reuseFailAlloc_376_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
v_a_296_ = v___x_374_;
goto _start;
}
}
else
{
lean_dec(v_nextNeedlePos_370_);
lean_del_object(v___x_324_);
lean_dec(v_stackPos_321_);
lean_dec_ref(v_table_320_);
lean_dec_ref(v_needle_319_);
return v_decide_371_;
}
}
}
}
}
default: 
{
return v_b_297_;
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_295_ = stack[0].m_obj;
lean_object* v_a_296_ = stack[1].m_obj;
uint8_t v_b_297_ = stack[2].m_num;
uint8_t v_res_378_;
v_res_378_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_spec__2___redArg(v_s_295_, v_a_296_, v_b_297_);
stack->m_num = v_res_378_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_spec__2___redArg___boxed(lean_object* v_s_379_, lean_object* v_a_380_, lean_object* v_b_381_){
_start:
{
uint8_t v_b_boxed_382_; uint8_t v_res_383_; lean_object* v_r_384_; 
v_b_boxed_382_ = lean_unbox(v_b_381_);
v_res_383_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_spec__2___redArg(v_s_379_, v_a_380_, v_b_boxed_382_);
lean_dec_ref(v_s_379_);
v_r_384_ = lean_box(v_res_383_);
return v_r_384_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__2(void){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_390_ = ((lean_object*)(l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__1));
v___x_391_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_390_);
return v___x_391_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__3(void){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_392_ = lean_unsigned_to_nat(0u);
v___x_393_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__2, &l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__2_once, _init_l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__2);
v___x_394_ = ((lean_object*)(l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__1));
v___x_395_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_395_, 0, v___x_394_);
lean_ctor_set(v___x_395_, 1, v___x_393_);
lean_ctor_set(v___x_395_, 2, v___x_392_);
lean_ctor_set(v___x_395_, 3, v___x_392_);
return v___x_395_;
}
}
uint8_t l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2(lean_object* v_s_396_){
_start:
{
lean_object* v___x_397_; uint8_t v___x_398_; uint8_t v___x_399_; 
v___x_397_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__3, &l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__3_once, _init_l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__3);
v___x_398_ = 0;
v___x_399_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_spec__2___redArg(v_s_396_, v___x_397_, v___x_398_);
return v___x_399_;
}
}
LEAN_EXPORT void l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_396_ = stack[0].m_obj;
uint8_t v_res_400_;
v_res_400_ = l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2(v_s_396_);
stack->m_num = v_res_400_;
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___boxed(lean_object* v_s_401_){
_start:
{
uint8_t v_res_402_; lean_object* v_r_403_; 
v_res_402_ = l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2(v_s_401_);
lean_dec_ref(v_s_401_);
v_r_403_ = lean_box(v_res_402_);
return v_r_403_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkDeprecatedImports_spec__3(lean_object* v_as_404_, size_t v_sz_405_, size_t v_i_406_, lean_object* v_b_407_){
_start:
{
lean_object* v_a_409_; uint8_t v___x_413_; 
v___x_413_ = lean_usize_dec_lt(v_i_406_, v_sz_405_);
if (v___x_413_ == 0)
{
return v_b_407_;
}
else
{
lean_object* v_fst_414_; lean_object* v_snd_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_490_; 
v_fst_414_ = lean_ctor_get(v_b_407_, 0);
v_snd_415_ = lean_ctor_get(v_b_407_, 1);
v_isSharedCheck_490_ = !lean_is_exclusive(v_b_407_);
if (v_isSharedCheck_490_ == 0)
{
v___x_417_ = v_b_407_;
v_isShared_418_ = v_isSharedCheck_490_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_snd_415_);
lean_inc(v_fst_414_);
lean_dec(v_b_407_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_490_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_419_; lean_object* v_a_420_; lean_object* v___y_422_; lean_object* v_ignoreDeprecatedImports_423_; uint8_t v___x_435_; 
v___x_419_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__4));
v_a_420_ = lean_array_uget_borrowed(v_as_404_, v_i_406_);
lean_inc(v_a_420_);
v___x_435_ = l_Lean_Syntax_isOfKind(v_a_420_, v___x_419_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; 
lean_del_object(v___x_417_);
v___x_436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_436_, 0, v_fst_414_);
lean_ctor_set(v___x_436_, 1, v_snd_415_);
v_a_409_ = v___x_436_;
goto v___jp_408_;
}
else
{
lean_object* v___x_437_; lean_object* v___x_462_; lean_object* v___x_482_; uint8_t v___x_483_; 
v___x_437_ = lean_unsigned_to_nat(0u);
v___x_462_ = lean_unsigned_to_nat(1u);
v___x_482_ = l_Lean_Syntax_getArg(v_a_420_, v___x_437_);
v___x_483_ = l_Lean_Syntax_isNone(v___x_482_);
if (v___x_483_ == 0)
{
uint8_t v___x_484_; 
lean_inc(v___x_482_);
v___x_484_ = l_Lean_Syntax_matchesNull(v___x_482_, v___x_462_);
if (v___x_484_ == 0)
{
lean_object* v___x_485_; 
lean_dec(v___x_482_);
lean_del_object(v___x_417_);
v___x_485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_485_, 0, v_fst_414_);
lean_ctor_set(v___x_485_, 1, v_snd_415_);
v_a_409_ = v___x_485_;
goto v___jp_408_;
}
else
{
lean_object* v___x_486_; lean_object* v___x_487_; uint8_t v___x_488_; 
v___x_486_ = l_Lean_Syntax_getArg(v___x_482_, v___x_437_);
lean_dec(v___x_482_);
v___x_487_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__14));
v___x_488_ = l_Lean_Syntax_isOfKind(v___x_486_, v___x_487_);
if (v___x_488_ == 0)
{
lean_object* v___x_489_; 
lean_del_object(v___x_417_);
v___x_489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_489_, 0, v_fst_414_);
lean_ctor_set(v___x_489_, 1, v_snd_415_);
v_a_409_ = v___x_489_;
goto v___jp_408_;
}
else
{
goto v___jp_473_;
}
}
}
else
{
lean_dec(v___x_482_);
goto v___jp_473_;
}
v___jp_438_:
{
lean_object* v___x_439_; lean_object* v___x_440_; uint8_t v___x_441_; 
v___x_439_ = lean_unsigned_to_nat(5u);
v___x_440_ = l_Lean_Syntax_getArg(v_a_420_, v___x_439_);
v___x_441_ = l_Lean_Syntax_matchesNull(v___x_440_, v___x_437_);
if (v___x_441_ == 0)
{
lean_object* v___x_442_; 
lean_del_object(v___x_417_);
v___x_442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_442_, 0, v_fst_414_);
lean_ctor_set(v___x_442_, 1, v_snd_415_);
v_a_409_ = v___x_442_;
goto v___jp_408_;
}
else
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_443_ = lean_unsigned_to_nat(4u);
v___x_444_ = l_Lean_Syntax_getArg(v_a_420_, v___x_443_);
v___x_445_ = l_Lean_Syntax_getTrailing_x3f(v_a_420_);
if (lean_obj_tag(v___x_445_) == 0)
{
v___y_422_ = v___x_444_;
v_ignoreDeprecatedImports_423_ = v_fst_414_;
goto v___jp_421_;
}
else
{
lean_object* v_val_446_; lean_object* v_str_447_; lean_object* v_startPos_448_; lean_object* v_stopPos_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_461_; 
v_val_446_ = lean_ctor_get(v___x_445_, 0);
lean_inc(v_val_446_);
lean_dec_ref_known(v___x_445_, 1);
v_str_447_ = lean_ctor_get(v_val_446_, 0);
v_startPos_448_ = lean_ctor_get(v_val_446_, 1);
v_stopPos_449_ = lean_ctor_get(v_val_446_, 2);
v_isSharedCheck_461_ = !lean_is_exclusive(v_val_446_);
if (v_isSharedCheck_461_ == 0)
{
v___x_451_ = v_val_446_;
v_isShared_452_ = v_isSharedCheck_461_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_stopPos_449_);
lean_inc(v_startPos_448_);
lean_inc(v_str_447_);
lean_dec(v_val_446_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_461_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_456_; 
v___x_453_ = lean_string_utf8_extract(v_str_447_, v_startPos_448_, v_stopPos_449_);
lean_dec(v_stopPos_449_);
lean_dec(v_startPos_448_);
lean_dec_ref(v_str_447_);
v___x_454_ = lean_string_utf8_byte_size(v___x_453_);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 2, v___x_454_);
lean_ctor_set(v___x_451_, 1, v___x_437_);
lean_ctor_set(v___x_451_, 0, v___x_453_);
v___x_456_ = v___x_451_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v___x_453_);
lean_ctor_set(v_reuseFailAlloc_460_, 1, v___x_437_);
lean_ctor_set(v_reuseFailAlloc_460_, 2, v___x_454_);
v___x_456_ = v_reuseFailAlloc_460_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
uint8_t v___x_457_; 
v___x_457_ = l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2(v___x_456_);
lean_dec_ref(v___x_456_);
if (v___x_457_ == 0)
{
v___y_422_ = v___x_444_;
v_ignoreDeprecatedImports_423_ = v_fst_414_;
goto v___jp_421_;
}
else
{
lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_458_ = l_Lean_TSyntax_getId(v___x_444_);
v___x_459_ = l_Lean_NameSet_insert(v_fst_414_, v___x_458_);
v___y_422_ = v___x_444_;
v_ignoreDeprecatedImports_423_ = v___x_459_;
goto v___jp_421_;
}
}
}
}
}
}
v___jp_463_:
{
lean_object* v___x_464_; lean_object* v___x_465_; uint8_t v___x_466_; 
v___x_464_ = lean_unsigned_to_nat(3u);
v___x_465_ = l_Lean_Syntax_getArg(v_a_420_, v___x_464_);
v___x_466_ = l_Lean_Syntax_isNone(v___x_465_);
if (v___x_466_ == 0)
{
uint8_t v___x_467_; 
lean_inc(v___x_465_);
v___x_467_ = l_Lean_Syntax_matchesNull(v___x_465_, v___x_462_);
if (v___x_467_ == 0)
{
lean_object* v___x_468_; 
lean_dec(v___x_465_);
lean_del_object(v___x_417_);
v___x_468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_468_, 0, v_fst_414_);
lean_ctor_set(v___x_468_, 1, v_snd_415_);
v_a_409_ = v___x_468_;
goto v___jp_408_;
}
else
{
lean_object* v___x_469_; lean_object* v___x_470_; uint8_t v___x_471_; 
v___x_469_ = l_Lean_Syntax_getArg(v___x_465_, v___x_437_);
lean_dec(v___x_465_);
v___x_470_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__10));
v___x_471_ = l_Lean_Syntax_isOfKind(v___x_469_, v___x_470_);
if (v___x_471_ == 0)
{
lean_object* v___x_472_; 
lean_del_object(v___x_417_);
v___x_472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_472_, 0, v_fst_414_);
lean_ctor_set(v___x_472_, 1, v_snd_415_);
v_a_409_ = v___x_472_;
goto v___jp_408_;
}
else
{
goto v___jp_438_;
}
}
}
else
{
lean_dec(v___x_465_);
goto v___jp_438_;
}
}
v___jp_473_:
{
lean_object* v___x_474_; uint8_t v___x_475_; 
v___x_474_ = l_Lean_Syntax_getArg(v_a_420_, v___x_462_);
v___x_475_ = l_Lean_Syntax_isNone(v___x_474_);
if (v___x_475_ == 0)
{
uint8_t v___x_476_; 
lean_inc(v___x_474_);
v___x_476_ = l_Lean_Syntax_matchesNull(v___x_474_, v___x_462_);
if (v___x_476_ == 0)
{
lean_object* v___x_477_; 
lean_dec(v___x_474_);
lean_del_object(v___x_417_);
v___x_477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_477_, 0, v_fst_414_);
lean_ctor_set(v___x_477_, 1, v_snd_415_);
v_a_409_ = v___x_477_;
goto v___jp_408_;
}
else
{
lean_object* v___x_478_; lean_object* v___x_479_; uint8_t v___x_480_; 
v___x_478_ = l_Lean_Syntax_getArg(v___x_474_, v___x_437_);
lean_dec(v___x_474_);
v___x_479_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__12));
v___x_480_ = l_Lean_Syntax_isOfKind(v___x_478_, v___x_479_);
if (v___x_480_ == 0)
{
lean_object* v___x_481_; 
lean_del_object(v___x_417_);
v___x_481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_481_, 0, v_fst_414_);
lean_ctor_set(v___x_481_, 1, v_snd_415_);
v_a_409_ = v___x_481_;
goto v___jp_408_;
}
else
{
goto v___jp_463_;
}
}
}
else
{
lean_dec(v___x_474_);
goto v___jp_463_;
}
}
}
v___jp_421_:
{
uint8_t v___x_424_; lean_object* v___x_425_; 
v___x_424_ = 0;
v___x_425_ = l_Lean_Syntax_getPos_x3f(v_a_420_, v___x_424_);
if (lean_obj_tag(v___x_425_) == 1)
{
lean_object* v_val_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_430_; 
v_val_426_ = lean_ctor_get(v___x_425_, 0);
lean_inc(v_val_426_);
lean_dec_ref_known(v___x_425_, 1);
v___x_427_ = l_Lean_TSyntax_getId(v___y_422_);
lean_dec(v___y_422_);
v___x_428_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_427_, v_val_426_, v_snd_415_);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 1, v___x_428_);
lean_ctor_set(v___x_417_, 0, v_ignoreDeprecatedImports_423_);
v___x_430_ = v___x_417_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_ignoreDeprecatedImports_423_);
lean_ctor_set(v_reuseFailAlloc_431_, 1, v___x_428_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
v_a_409_ = v___x_430_;
goto v___jp_408_;
}
}
else
{
lean_object* v___x_433_; 
lean_dec(v___x_425_);
lean_dec(v___y_422_);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 0, v_ignoreDeprecatedImports_423_);
v___x_433_ = v___x_417_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_ignoreDeprecatedImports_423_);
lean_ctor_set(v_reuseFailAlloc_434_, 1, v_snd_415_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
v_a_409_ = v___x_433_;
goto v___jp_408_;
}
}
}
}
}
v___jp_408_:
{
size_t v___x_410_; size_t v___x_411_; 
v___x_410_ = ((size_t)1ULL);
v___x_411_ = lean_usize_add(v_i_406_, v___x_410_);
v_i_406_ = v___x_411_;
v_b_407_ = v_a_409_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkDeprecatedImports_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_404_ = stack[0].m_obj;
size_t v_sz_405_ = stack[1].m_num;
size_t v_i_406_ = stack[2].m_num;
lean_object* v_b_407_ = stack[3].m_obj;
lean_object* v_res_491_;
v_res_491_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkDeprecatedImports_spec__3(v_as_404_, v_sz_405_, v_i_406_, v_b_407_);
stack->m_obj
 = v_res_491_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkDeprecatedImports_spec__3___boxed(lean_object* v_as_492_, lean_object* v_sz_493_, lean_object* v_i_494_, lean_object* v_b_495_){
_start:
{
size_t v_sz_boxed_496_; size_t v_i_boxed_497_; lean_object* v_res_498_; 
v_sz_boxed_496_ = lean_unbox_usize(v_sz_493_);
lean_dec(v_sz_493_);
v_i_boxed_497_ = lean_unbox_usize(v_i_494_);
lean_dec(v_i_494_);
v_res_498_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkDeprecatedImports_spec__3(v_as_492_, v_sz_boxed_496_, v_i_boxed_497_, v_b_495_);
lean_dec_ref(v_as_492_);
return v_res_498_;
}
}
lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4_spec__5(lean_object* v_o_502_, lean_object* v_k_503_, uint8_t v_v_504_){
_start:
{
lean_object* v_map_505_; uint8_t v_hasTrace_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_520_; 
v_map_505_ = lean_ctor_get(v_o_502_, 0);
v_hasTrace_506_ = lean_ctor_get_uint8(v_o_502_, sizeof(void*)*1);
v_isSharedCheck_520_ = !lean_is_exclusive(v_o_502_);
if (v_isSharedCheck_520_ == 0)
{
v___x_508_ = v_o_502_;
v_isShared_509_ = v_isSharedCheck_520_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_map_505_);
lean_dec(v_o_502_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_520_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_510_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_510_, 0, v_v_504_);
lean_inc(v_k_503_);
v___x_511_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_503_, v___x_510_, v_map_505_);
if (v_hasTrace_506_ == 0)
{
lean_object* v___x_512_; uint8_t v___x_513_; lean_object* v___x_515_; 
v___x_512_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4_spec__5___closed__1));
v___x_513_ = l_Lean_Name_isPrefixOf(v___x_512_, v_k_503_);
lean_dec(v_k_503_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 0, v___x_511_);
v___x_515_ = v___x_508_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v___x_511_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
lean_ctor_set_uint8(v___x_515_, sizeof(void*)*1, v___x_513_);
return v___x_515_;
}
}
else
{
lean_object* v___x_518_; 
lean_dec(v_k_503_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 0, v___x_511_);
v___x_518_ = v___x_508_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v___x_511_);
lean_ctor_set_uint8(v_reuseFailAlloc_519_, sizeof(void*)*1, v_hasTrace_506_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_502_ = stack[0].m_obj;
lean_object* v_k_503_ = stack[1].m_obj;
uint8_t v_v_504_ = stack[2].m_num;
lean_object* v_res_521_;
v_res_521_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4_spec__5(v_o_502_, v_k_503_, v_v_504_);
stack->m_obj
 = v_res_521_;
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4_spec__5___boxed(lean_object* v_o_522_, lean_object* v_k_523_, lean_object* v_v_524_){
_start:
{
uint8_t v_v_boxed_525_; lean_object* v_res_526_; 
v_v_boxed_525_ = lean_unbox(v_v_524_);
v_res_526_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4_spec__5(v_o_522_, v_k_523_, v_v_boxed_525_);
return v_res_526_;
}
}
lean_object* l_Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4(lean_object* v_opts_527_, lean_object* v_opt_528_, uint8_t v_val_529_){
_start:
{
lean_object* v_name_530_; lean_object* v___x_531_; 
v_name_530_ = lean_ctor_get(v_opt_528_, 0);
lean_inc(v_name_530_);
lean_dec_ref(v_opt_528_);
v___x_531_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4_spec__5(v_opts_527_, v_name_530_, v_val_529_);
return v___x_531_;
}
}
LEAN_EXPORT void l_Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_527_ = stack[0].m_obj;
lean_object* v_opt_528_ = stack[1].m_obj;
uint8_t v_val_529_ = stack[2].m_num;
lean_object* v_res_532_;
v_res_532_ = l_Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4(v_opts_527_, v_opt_528_, v_val_529_);
stack->m_obj
 = v_res_532_;
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4___boxed(lean_object* v_opts_533_, lean_object* v_opt_534_, lean_object* v_val_535_){
_start:
{
uint8_t v_val_boxed_536_; lean_object* v_res_537_; 
v_val_boxed_536_ = lean_unbox(v_val_535_);
v_res_537_ = l_Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4(v_opts_533_, v_opt_534_, v_val_boxed_536_);
return v_res_537_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1(lean_object* v_ignoreDeprecatedImports_543_, lean_object* v_env_544_, lean_object* v_inputCtx_545_, lean_object* v_importPositions_546_, lean_object* v_startPos_547_, lean_object* v_as_548_, size_t v_i_549_, size_t v_stop_550_, lean_object* v_b_551_){
_start:
{
lean_object* v___y_553_; uint8_t v___x_557_; 
v___x_557_ = lean_usize_dec_eq(v_i_549_, v_stop_550_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; lean_object* v_module_559_; uint8_t v___x_560_; 
v___x_558_ = lean_array_uget_borrowed(v_as_548_, v_i_549_);
v_module_559_ = lean_ctor_get(v___x_558_, 0);
v___x_560_ = l_Lean_NameSet_contains(v_ignoreDeprecatedImports_543_, v_module_559_);
if (v___x_560_ == 0)
{
lean_object* v___x_561_; 
v___x_561_ = l_Lean_Environment_getModuleIdx_x3f(v_env_544_, v_module_559_);
if (lean_obj_tag(v___x_561_) == 0)
{
v___y_553_ = v_b_551_;
goto v___jp_552_;
}
else
{
lean_object* v_val_562_; lean_object* v___x_563_; 
v_val_562_ = lean_ctor_get(v___x_561_, 0);
lean_inc(v_val_562_);
lean_dec_ref_known(v___x_561_, 1);
v___x_563_ = l_Lean_Environment_getDeprecatedModuleByIdx_x3f(v_env_544_, v_val_562_);
if (lean_obj_tag(v___x_563_) == 0)
{
lean_dec(v_val_562_);
v___y_553_ = v_b_551_;
goto v___jp_552_;
}
else
{
lean_object* v_val_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_587_; 
v_val_564_ = lean_ctor_get(v___x_563_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_563_);
if (v_isSharedCheck_587_ == 0)
{
v___x_566_ = v___x_563_;
v_isShared_567_ = v_isSharedCheck_587_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_val_564_);
lean_dec(v___x_563_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_587_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___y_569_; lean_object* v___x_585_; 
v___x_585_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_importPositions_546_, v_module_559_);
if (lean_obj_tag(v___x_585_) == 0)
{
lean_inc(v_startPos_547_);
v___y_569_ = v_startPos_547_;
goto v___jp_568_;
}
else
{
lean_object* v_val_586_; 
v_val_586_ = lean_ctor_get(v___x_585_, 0);
lean_inc(v_val_586_);
lean_dec_ref_known(v___x_585_, 1);
v___y_569_ = v_val_586_;
goto v___jp_568_;
}
v___jp_568_:
{
lean_object* v_fileName_570_; lean_object* v_fileMap_571_; lean_object* v___x_572_; lean_object* v___x_573_; uint8_t v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_579_; 
v_fileName_570_ = lean_ctor_get(v_inputCtx_545_, 1);
v_fileMap_571_ = lean_ctor_get(v_inputCtx_545_, 2);
lean_inc_ref(v_fileMap_571_);
v___x_572_ = l_Lean_FileMap_toPosition(v_fileMap_571_, v___y_569_);
lean_dec(v___y_569_);
v___x_573_ = lean_box(0);
v___x_574_ = 1;
v___x_575_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___closed__0));
v___x_576_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___closed__2));
lean_inc(v_module_559_);
v___x_577_ = l_Lean_formatDeprecatedModuleWarning(v_env_544_, v_val_562_, v_module_559_, v_val_564_);
lean_dec(v_val_562_);
if (v_isShared_567_ == 0)
{
lean_ctor_set_tag(v___x_566_, 3);
lean_ctor_set(v___x_566_, 0, v___x_577_);
v___x_579_ = v___x_566_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v___x_577_);
v___x_579_ = v_reuseFailAlloc_584_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_580_ = l_Lean_MessageData_ofFormat(v___x_579_);
v___x_581_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_581_, 0, v___x_576_);
lean_ctor_set(v___x_581_, 1, v___x_580_);
lean_inc_ref(v_fileName_570_);
v___x_582_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_582_, 0, v_fileName_570_);
lean_ctor_set(v___x_582_, 1, v___x_572_);
lean_ctor_set(v___x_582_, 2, v___x_573_);
lean_ctor_set(v___x_582_, 3, v___x_575_);
lean_ctor_set(v___x_582_, 4, v___x_581_);
lean_ctor_set_uint8(v___x_582_, sizeof(void*)*5, v___x_560_);
lean_ctor_set_uint8(v___x_582_, sizeof(void*)*5 + 1, v___x_574_);
lean_ctor_set_uint8(v___x_582_, sizeof(void*)*5 + 2, v___x_560_);
v___x_583_ = l_Lean_MessageLog_add(v___x_582_, v_b_551_);
v___y_553_ = v___x_583_;
goto v___jp_552_;
}
}
}
}
}
}
else
{
v___y_553_ = v_b_551_;
goto v___jp_552_;
}
}
else
{
lean_dec(v_startPos_547_);
lean_dec_ref(v_inputCtx_545_);
return v_b_551_;
}
v___jp_552_:
{
size_t v___x_554_; size_t v___x_555_; 
v___x_554_ = ((size_t)1ULL);
v___x_555_ = lean_usize_add(v_i_549_, v___x_554_);
v_i_549_ = v___x_555_;
v_b_551_ = v___y_553_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_ignoreDeprecatedImports_543_ = stack[0].m_obj;
lean_object* v_env_544_ = stack[1].m_obj;
lean_object* v_inputCtx_545_ = stack[2].m_obj;
lean_object* v_importPositions_546_ = stack[3].m_obj;
lean_object* v_startPos_547_ = stack[4].m_obj;
lean_object* v_as_548_ = stack[5].m_obj;
size_t v_i_549_ = stack[6].m_num;
size_t v_stop_550_ = stack[7].m_num;
lean_object* v_b_551_ = stack[8].m_obj;
lean_object* v_res_588_;
v_res_588_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1(v_ignoreDeprecatedImports_543_, v_env_544_, v_inputCtx_545_, v_importPositions_546_, v_startPos_547_, v_as_548_, v_i_549_, v_stop_550_, v_b_551_);
stack->m_obj
 = v_res_588_;
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
if (lean_obj_tag(v___y_642_) == 0)
{
lean_dec(v___y_641_);
v___y_631_ = v_importsStx_645_;
v_opts_632_ = v_opts_606_;
goto v___jp_630_;
}
else
{
lean_object* v_val_646_; lean_object* v___x_647_; 
v_val_646_ = lean_ctor_get(v___y_642_, 0);
lean_inc(v_val_646_);
lean_dec_ref_known(v___y_642_, 1);
v___x_647_ = l_Lean_Syntax_getTrailing_x3f(v_val_646_);
lean_dec(v_val_646_);
if (lean_obj_tag(v___x_647_) == 0)
{
lean_dec(v___y_641_);
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
lean_ctor_set(v___x_653_, 1, v___y_641_);
lean_ctor_set(v___x_653_, 0, v___x_655_);
v___x_658_ = v___x_653_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v___x_655_);
lean_ctor_set(v_reuseFailAlloc_663_, 1, v___y_641_);
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
lean_dec(v___y_669_);
lean_dec(v___y_668_);
v_opts_613_ = v_opts_606_;
v_ignoreDeprecatedImports_614_ = v_ignoreDeprecatedImports_628_;
v_importPositions_615_ = v_importPositions_629_;
goto v___jp_612_;
}
else
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; uint8_t v___x_679_; 
v___x_676_ = l_Lean_Syntax_getArg(v___x_673_, v___y_669_);
lean_dec(v___x_673_);
v___x_677_ = ((lean_object*)(l_Lean_Elab_HeaderSyntax_imports___closed__6));
lean_inc_ref(v___y_670_);
lean_inc_ref(v___y_667_);
lean_inc_ref(v___y_666_);
v___x_678_ = l_Lean_Name_mkStr4(v___y_666_, v___y_667_, v___y_670_, v___x_677_);
v___x_679_ = l_Lean_Syntax_isOfKind(v___x_676_, v___x_678_);
lean_dec(v___x_678_);
if (v___x_679_ == 0)
{
lean_dec(v_moduleTk_671_);
lean_dec(v___y_669_);
lean_dec(v___y_668_);
v_opts_613_ = v_opts_606_;
v_ignoreDeprecatedImports_614_ = v_ignoreDeprecatedImports_628_;
v_importPositions_615_ = v_importPositions_629_;
goto v___jp_612_;
}
else
{
v___y_640_ = v___y_668_;
v___y_641_ = v___y_669_;
v___y_642_ = v_moduleTk_671_;
goto v___jp_639_;
}
}
}
else
{
lean_dec(v___x_673_);
v___y_640_ = v___y_668_;
v___y_641_ = v___y_669_;
v___y_642_ = v_moduleTk_671_;
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
v___y_666_ = v___x_682_;
v___y_667_ = v___x_683_;
v___y_668_ = v_val_681_;
v___y_669_ = v___x_687_;
v___y_670_ = v___x_684_;
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
v___y_666_ = v___x_682_;
v___y_667_ = v___x_683_;
v___y_668_ = v_val_681_;
v___y_669_ = v___x_687_;
v___y_670_ = v___x_684_;
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
uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_spec__2(lean_object* v_s_709_, lean_object* v_inst_710_, lean_object* v_R_711_, lean_object* v_a_712_, uint8_t v_b_713_, lean_object* v_c_714_){
_start:
{
uint8_t v___x_715_; 
v___x_715_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_spec__2___redArg(v_s_709_, v_a_712_, v_b_713_);
return v___x_715_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_709_ = stack[0].m_obj;
lean_object* v_a_712_ = stack[3].m_obj;
uint8_t v_b_713_ = stack[4].m_num;
uint8_t v_res_716_;
v_res_716_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_spec__2(v_s_709_, lean_box(0), lean_box(0), v_a_712_, v_b_713_, lean_box(0));
stack->m_num = v_res_716_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_spec__2___boxed(lean_object* v_s_717_, lean_object* v_inst_718_, lean_object* v_R_719_, lean_object* v_a_720_, lean_object* v_b_721_, lean_object* v_c_722_){
_start:
{
uint8_t v_b_boxed_723_; uint8_t v_res_724_; lean_object* v_r_725_; 
v_b_boxed_723_ = lean_unbox(v_b_721_);
v_res_724_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_spec__2(v_s_717_, v_inst_718_, v_R_719_, v_a_720_, v_b_boxed_723_, v_c_722_);
lean_dec_ref(v_s_717_);
v_r_725_ = lean_box(v_res_724_);
return v_r_725_;
}
}
static lean_object* _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_726_; lean_object* v___x_727_; 
v___x_726_ = 33;
v___x_727_ = lean_box_uint32(v___x_726_);
return v___x_727_;
}
}
static lean_object* _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__2(void){
_start:
{
uint32_t v___x_728_; lean_object* v___x_729_; 
v___x_728_ = 42;
v___x_729_ = lean_box_uint32(v___x_728_);
return v___x_729_;
}
}
static lean_object* _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__3(void){
_start:
{
uint32_t v___x_730_; lean_object* v___x_731_; 
v___x_730_ = 63;
v___x_731_ = lean_box_uint32(v___x_730_);
return v___x_731_;
}
}
static lean_object* _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__4(void){
_start:
{
uint32_t v___x_732_; lean_object* v___x_733_; 
v___x_732_ = 124;
v___x_733_ = lean_box_uint32(v___x_732_);
return v___x_733_;
}
}
static lean_object* _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__5(void){
_start:
{
uint32_t v___x_734_; lean_object* v___x_735_; 
v___x_734_ = 34;
v___x_735_ = lean_box_uint32(v___x_734_);
return v___x_735_;
}
}
static lean_object* _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__6(void){
_start:
{
uint32_t v___x_736_; lean_object* v___x_737_; 
v___x_736_ = 62;
v___x_737_ = lean_box_uint32(v___x_736_);
return v___x_737_;
}
}
static lean_object* _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__7(void){
_start:
{
uint32_t v___x_738_; lean_object* v___x_739_; 
v___x_738_ = 60;
v___x_739_ = lean_box_uint32(v___x_738_);
return v___x_739_;
}
}
static lean_object* _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0(void){
_start:
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_740_ = lean_unsigned_to_nat(7u);
v___x_741_ = lean_mk_empty_array_with_capacity(v___x_740_);
v___x_742_ = l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__7;
v___x_743_ = lean_array_push(v___x_741_, v___x_742_);
v___x_744_ = l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__6;
v___x_745_ = lean_array_push(v___x_743_, v___x_744_);
v___x_746_ = l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__5;
v___x_747_ = lean_array_push(v___x_745_, v___x_746_);
v___x_748_ = l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__4;
v___x_749_ = lean_array_push(v___x_747_, v___x_748_);
v___x_750_ = l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__3;
v___x_751_ = lean_array_push(v___x_749_, v___x_750_);
v___x_752_ = l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__2;
v___x_753_ = lean_array_push(v___x_751_, v___x_752_);
v___x_754_ = l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__1;
v___x_755_ = lean_array_push(v___x_753_, v___x_754_);
return v___x_755_;
}
}
static lean_object* _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars(void){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = lean_obj_once(&l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0, &l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0_once, _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__0(lean_object* v_s_844_, lean_object* v_p_845_){
_start:
{
uint32_t v___y_847_; lean_object* v___x_852_; uint8_t v_decide_853_; 
v___x_852_ = lean_string_utf8_byte_size(v_s_844_);
v_decide_853_ = lean_nat_dec_eq(v_p_845_, v___x_852_);
if (v_decide_853_ == 0)
{
uint32_t v___x_854_; uint32_t v___x_855_; uint8_t v___x_856_; 
v___x_854_ = lean_string_utf8_get_fast(v_s_844_, v_p_845_);
v___x_855_ = 97;
v___x_856_ = lean_uint32_dec_le(v___x_855_, v___x_854_);
if (v___x_856_ == 0)
{
v___y_847_ = v___x_854_;
goto v___jp_846_;
}
else
{
uint32_t v___x_857_; uint8_t v___x_858_; 
v___x_857_ = 122;
v___x_858_ = lean_uint32_dec_le(v___x_854_, v___x_857_);
if (v___x_858_ == 0)
{
v___y_847_ = v___x_854_;
goto v___jp_846_;
}
else
{
uint32_t v___x_859_; uint32_t v___x_860_; 
v___x_859_ = 4294967264;
v___x_860_ = lean_uint32_add(v___x_854_, v___x_859_);
v___y_847_ = v___x_860_;
goto v___jp_846_;
}
}
}
else
{
lean_dec(v_p_845_);
return v_s_844_;
}
v___jp_846_:
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
lean_inc(v_p_845_);
v___x_848_ = lean_string_utf8_set(v_s_844_, v_p_845_, v___y_847_);
v___x_849_ = l_Char_utf8Size(v___y_847_);
v___x_850_ = lean_nat_add(v_p_845_, v___x_849_);
lean_dec(v___x_849_);
lean_dec(v_p_845_);
v_s_844_ = v___x_848_;
v_p_845_ = v___x_850_;
goto _start;
}
}
}
uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2_spec__3___redArg(lean_object* v_s_861_, uint32_t v_a_862_, lean_object* v_a_863_, uint8_t v_b_864_){
_start:
{
lean_object* v_str_865_; lean_object* v_startInclusive_866_; lean_object* v_endExclusive_867_; lean_object* v___x_868_; uint8_t v_decide_869_; 
v_str_865_ = lean_ctor_get(v_s_861_, 0);
v_startInclusive_866_ = lean_ctor_get(v_s_861_, 1);
v_endExclusive_867_ = lean_ctor_get(v_s_861_, 2);
v___x_868_ = lean_nat_sub(v_endExclusive_867_, v_startInclusive_866_);
v_decide_869_ = lean_nat_dec_eq(v_a_863_, v___x_868_);
lean_dec(v___x_868_);
if (v_decide_869_ == 0)
{
lean_object* v___x_870_; uint32_t v___x_871_; uint8_t v___x_872_; 
v___x_870_ = lean_nat_add(v_startInclusive_866_, v_a_863_);
lean_dec(v_a_863_);
v___x_871_ = lean_string_utf8_get_fast(v_str_865_, v___x_870_);
v___x_872_ = lean_uint32_dec_eq(v___x_871_, v_a_862_);
if (v___x_872_ == 0)
{
lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_873_ = lean_string_utf8_next_fast(v_str_865_, v___x_870_);
lean_dec(v___x_870_);
v___x_874_ = lean_nat_sub(v___x_873_, v_startInclusive_866_);
v_a_863_ = v___x_874_;
v_b_864_ = v___x_872_;
goto _start;
}
else
{
lean_dec(v___x_870_);
return v___x_872_;
}
}
else
{
lean_dec(v_a_863_);
return v_b_864_;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_861_ = stack[0].m_obj;
uint32_t v_a_862_ = stack[1].m_num;
lean_object* v_a_863_ = stack[2].m_obj;
uint8_t v_b_864_ = stack[3].m_num;
uint8_t v_res_876_;
v_res_876_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2_spec__3___redArg(v_s_861_, v_a_862_, v_a_863_, v_b_864_);
stack->m_num = v_res_876_;
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
uint8_t l_String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2(uint32_t v_a_885_, lean_object* v_s_886_){
_start:
{
lean_object* v_searcher_887_; uint8_t v___x_888_; uint8_t v___x_889_; 
v_searcher_887_ = lean_unsigned_to_nat(0u);
v___x_888_ = 0;
v___x_889_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2_spec__3___redArg(v_s_886_, v_a_885_, v_searcher_887_, v___x_888_);
return v___x_889_;
}
}
LEAN_EXPORT void l_String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_885_ = stack[0].m_num;
lean_object* v_s_886_ = stack[1].m_obj;
uint8_t v_res_890_;
v_res_890_ = l_String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2(v_a_885_, v_s_886_);
stack->m_num = v_res_890_;
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2___boxed(lean_object* v_a_891_, lean_object* v_s_892_){
_start:
{
uint32_t v_a_boxed_893_; uint8_t v_res_894_; lean_object* v_r_895_; 
v_a_boxed_893_ = lean_unbox_uint32(v_a_891_);
lean_dec(v_a_891_);
v_res_894_ = l_String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2(v_a_boxed_893_, v_s_892_);
lean_dec_ref(v_s_892_);
v_r_895_ = lean_box(v_res_894_);
return v_r_895_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__3(lean_object* v_comp_899_, lean_object* v_as_900_, size_t v_sz_901_, size_t v_i_902_, lean_object* v_b_903_){
_start:
{
uint8_t v___x_904_; 
v___x_904_ = lean_usize_dec_lt(v_i_902_, v_sz_901_);
if (v___x_904_ == 0)
{
lean_dec_ref(v_comp_899_);
lean_inc_ref(v_b_903_);
return v_b_903_;
}
else
{
lean_object* v___x_905_; lean_object* v_a_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; uint32_t v___x_910_; uint8_t v___x_911_; 
v___x_905_ = lean_box(0);
v_a_906_ = lean_array_uget_borrowed(v_as_900_, v_i_902_);
v___x_907_ = lean_unsigned_to_nat(0u);
v___x_908_ = lean_string_utf8_byte_size(v_comp_899_);
lean_inc_ref(v_comp_899_);
v___x_909_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_909_, 0, v_comp_899_);
lean_ctor_set(v___x_909_, 1, v___x_907_);
lean_ctor_set(v___x_909_, 2, v___x_908_);
v___x_910_ = lean_unbox_uint32(v_a_906_);
v___x_911_ = l_String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2(v___x_910_, v___x_909_);
lean_dec_ref_known(v___x_909_, 3);
if (v___x_911_ == 0)
{
lean_object* v___x_912_; size_t v___x_913_; size_t v___x_914_; 
v___x_912_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__3___closed__0));
v___x_913_ = ((size_t)1ULL);
v___x_914_ = lean_usize_add(v_i_902_, v___x_913_);
v_i_902_ = v___x_914_;
v_b_903_ = v___x_912_;
goto _start;
}
else
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
lean_dec_ref(v_comp_899_);
lean_inc(v_a_906_);
v___x_916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_916_, 0, v_a_906_);
v___x_917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_917_, 0, v___x_916_);
v___x_918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_918_, 0, v___x_917_);
lean_ctor_set(v___x_918_, 1, v___x_905_);
return v___x_918_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_comp_899_ = stack[0].m_obj;
lean_object* v_as_900_ = stack[1].m_obj;
size_t v_sz_901_ = stack[2].m_num;
size_t v_i_902_ = stack[3].m_num;
lean_object* v_b_903_ = stack[4].m_obj;
lean_object* v_res_919_;
v_res_919_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__3(v_comp_899_, v_as_900_, v_sz_901_, v_i_902_, v_b_903_);
stack->m_obj
 = v_res_919_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__3___boxed(lean_object* v_comp_920_, lean_object* v_as_921_, lean_object* v_sz_922_, lean_object* v_i_923_, lean_object* v_b_924_){
_start:
{
size_t v_sz_boxed_925_; size_t v_i_boxed_926_; lean_object* v_res_927_; 
v_sz_boxed_925_ = lean_unbox_usize(v_sz_922_);
lean_dec(v_sz_922_);
v_i_boxed_926_ = lean_unbox_usize(v_i_923_);
lean_dec(v_i_923_);
v_res_927_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__3(v_comp_920_, v_as_921_, v_sz_boxed_925_, v_i_boxed_926_, v_b_924_);
lean_dec_ref(v_b_924_);
lean_dec_ref(v_as_921_);
return v_res_927_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__1_spec__1(lean_object* v_a_928_, lean_object* v_as_929_, size_t v_i_930_, size_t v_stop_931_){
_start:
{
uint8_t v___x_932_; 
v___x_932_ = lean_usize_dec_eq(v_i_930_, v_stop_931_);
if (v___x_932_ == 0)
{
lean_object* v___x_933_; uint8_t v___x_934_; 
v___x_933_ = lean_array_uget_borrowed(v_as_929_, v_i_930_);
v___x_934_ = lean_string_dec_eq(v_a_928_, v___x_933_);
if (v___x_934_ == 0)
{
size_t v___x_935_; size_t v___x_936_; 
v___x_935_ = ((size_t)1ULL);
v___x_936_ = lean_usize_add(v_i_930_, v___x_935_);
v_i_930_ = v___x_936_;
goto _start;
}
else
{
return v___x_934_;
}
}
else
{
uint8_t v___x_938_; 
v___x_938_ = 0;
return v___x_938_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_928_ = stack[0].m_obj;
lean_object* v_as_929_ = stack[1].m_obj;
size_t v_i_930_ = stack[2].m_num;
size_t v_stop_931_ = stack[3].m_num;
uint8_t v_res_939_;
v_res_939_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__1_spec__1(v_a_928_, v_as_929_, v_i_930_, v_stop_931_);
stack->m_num = v_res_939_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__1_spec__1___boxed(lean_object* v_a_940_, lean_object* v_as_941_, lean_object* v_i_942_, lean_object* v_stop_943_){
_start:
{
size_t v_i_boxed_944_; size_t v_stop_boxed_945_; uint8_t v_res_946_; lean_object* v_r_947_; 
v_i_boxed_944_ = lean_unbox_usize(v_i_942_);
lean_dec(v_i_942_);
v_stop_boxed_945_ = lean_unbox_usize(v_stop_943_);
lean_dec(v_stop_943_);
v_res_946_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__1_spec__1(v_a_940_, v_as_941_, v_i_boxed_944_, v_stop_boxed_945_);
lean_dec_ref(v_as_941_);
lean_dec_ref(v_a_940_);
v_r_947_ = lean_box(v_res_946_);
return v_r_947_;
}
}
uint8_t l_Array_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__1(lean_object* v_as_948_, lean_object* v_a_949_){
_start:
{
lean_object* v___x_950_; lean_object* v___x_951_; uint8_t v___x_952_; 
v___x_950_ = lean_unsigned_to_nat(0u);
v___x_951_ = lean_array_get_size(v_as_948_);
v___x_952_ = lean_nat_dec_lt(v___x_950_, v___x_951_);
if (v___x_952_ == 0)
{
return v___x_952_;
}
else
{
if (v___x_952_ == 0)
{
return v___x_952_;
}
else
{
size_t v___x_953_; size_t v___x_954_; uint8_t v___x_955_; 
v___x_953_ = ((size_t)0ULL);
v___x_954_ = lean_usize_of_nat(v___x_951_);
v___x_955_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__1_spec__1(v_a_949_, v_as_948_, v___x_953_, v___x_954_);
return v___x_955_;
}
}
}
}
LEAN_EXPORT void l_Array_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_948_ = stack[0].m_obj;
lean_object* v_a_949_ = stack[1].m_obj;
uint8_t v_res_956_;
v_res_956_ = l_Array_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__1(v_as_948_, v_a_949_);
stack->m_num = v_res_956_;
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__1___boxed(lean_object* v_as_957_, lean_object* v_a_958_){
_start:
{
uint8_t v_res_959_; lean_object* v_r_960_; 
v_res_959_ = l_Array_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__1(v_as_957_, v_a_958_);
lean_dec_ref(v_a_958_);
lean_dec_ref(v_as_957_);
v_r_960_ = lean_box(v_res_959_);
return v_r_960_;
}
}
static size_t _init_l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__0(void){
_start:
{
lean_object* v___x_961_; size_t v_sz_962_; 
v___x_961_ = l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars;
v_sz_962_ = lean_array_size(v___x_961_);
return v_sz_962_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability(lean_object* v_comp_967_){
_start:
{
lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; uint8_t v___x_971_; 
v___x_968_ = ((lean_object*)(l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames));
v___x_969_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_comp_967_);
v___x_970_ = l_String_mapAux___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__0(v_comp_967_, v___x_969_);
v___x_971_ = l_Array_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__1(v___x_968_, v___x_970_);
lean_dec_ref(v___x_970_);
if (v___x_971_ == 0)
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; size_t v_sz_975_; size_t v___x_976_; lean_object* v___x_977_; lean_object* v_fst_978_; 
v___x_972_ = l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars;
v___x_973_ = lean_box(0);
v___x_974_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__3___closed__0));
v_sz_975_ = lean_usize_once(&l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__0, &l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__0_once, _init_l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__0);
v___x_976_ = ((size_t)0ULL);
v___x_977_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__3(v_comp_967_, v___x_972_, v_sz_975_, v___x_976_, v___x_974_);
v_fst_978_ = lean_ctor_get(v___x_977_, 0);
lean_inc(v_fst_978_);
lean_dec_ref(v___x_977_);
if (lean_obj_tag(v_fst_978_) == 0)
{
return v___x_973_;
}
else
{
lean_object* v_val_979_; 
v_val_979_ = lean_ctor_get(v_fst_978_, 0);
lean_inc(v_val_979_);
lean_dec_ref_known(v_fst_978_, 1);
if (lean_obj_tag(v_val_979_) == 1)
{
lean_object* v_val_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_994_; 
v_val_980_ = lean_ctor_get(v_val_979_, 0);
v_isSharedCheck_994_ = !lean_is_exclusive(v_val_979_);
if (v_isSharedCheck_994_ == 0)
{
v___x_982_ = v_val_979_;
v_isShared_983_ = v_isSharedCheck_994_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_val_980_);
lean_dec(v_val_979_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_994_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_984_; lean_object* v___x_985_; uint32_t v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_992_; 
v___x_984_ = ((lean_object*)(l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__1));
v___x_985_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___closed__0));
v___x_986_ = lean_unbox_uint32(v_val_980_);
lean_dec(v_val_980_);
v___x_987_ = lean_string_push(v___x_985_, v___x_986_);
v___x_988_ = lean_string_append(v___x_984_, v___x_987_);
lean_dec_ref(v___x_987_);
v___x_989_ = ((lean_object*)(l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__2));
v___x_990_ = lean_string_append(v___x_988_, v___x_989_);
if (v_isShared_983_ == 0)
{
lean_ctor_set(v___x_982_, 0, v___x_990_);
v___x_992_ = v___x_982_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v___x_990_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
}
else
{
lean_dec(v_val_979_);
return v___x_973_;
}
}
}
else
{
lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_995_ = ((lean_object*)(l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__3));
v___x_996_ = lean_string_append(v___x_995_, v_comp_967_);
lean_dec_ref(v_comp_967_);
v___x_997_ = ((lean_object*)(l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__4));
v___x_998_ = lean_string_append(v___x_996_, v___x_997_);
v___x_999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_999_, 0, v___x_998_);
return v___x_999_;
}
}
}
uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2_spec__3(lean_object* v_s_1000_, uint32_t v_a_1001_, lean_object* v_inst_1002_, lean_object* v_R_1003_, lean_object* v_a_1004_, uint8_t v_b_1005_, lean_object* v_c_1006_){
_start:
{
uint8_t v___x_1007_; 
v___x_1007_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2_spec__3___redArg(v_s_1000_, v_a_1001_, v_a_1004_, v_b_1005_);
return v___x_1007_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1000_ = stack[0].m_obj;
uint32_t v_a_1001_ = stack[1].m_num;
lean_object* v_a_1004_ = stack[4].m_obj;
uint8_t v_b_1005_ = stack[5].m_num;
uint8_t v_res_1008_;
v_res_1008_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2_spec__3(v_s_1000_, v_a_1001_, lean_box(0), lean_box(0), v_a_1004_, v_b_1005_, lean_box(0));
stack->m_num = v_res_1008_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2_spec__3___boxed(lean_object* v_s_1009_, lean_object* v_a_1010_, lean_object* v_inst_1011_, lean_object* v_R_1012_, lean_object* v_a_1013_, lean_object* v_b_1014_, lean_object* v_c_1015_){
_start:
{
uint32_t v_a_boxed_1016_; uint8_t v_b_boxed_1017_; uint8_t v_res_1018_; lean_object* v_r_1019_; 
v_a_boxed_1016_ = lean_unbox_uint32(v_a_1010_);
lean_dec(v_a_1010_);
v_b_boxed_1017_ = lean_unbox(v_b_1014_);
v_res_1018_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2_spec__3(v_s_1009_, v_a_boxed_1016_, v_inst_1011_, v_R_1012_, v_a_1013_, v_b_boxed_1017_, v_c_1015_);
lean_dec_ref(v_s_1009_);
v_r_1019_ = lean_box(v_res_1018_);
return v_r_1019_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_checkModuleNamePortability_go(lean_object* v_mainModule_1022_, lean_object* v_inputCtx_1023_, lean_object* v_startPos_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_){
_start:
{
switch(lean_obj_tag(v_a_1025_))
{
case 0:
{
lean_dec_ref(v_inputCtx_1023_);
lean_dec(v_mainModule_1022_);
return v_a_1026_;
}
case 1:
{
lean_object* v_pre_1027_; lean_object* v_str_1028_; lean_object* v___x_1029_; 
v_pre_1027_ = lean_ctor_get(v_a_1025_, 0);
lean_inc(v_pre_1027_);
v_str_1028_ = lean_ctor_get(v_a_1025_, 1);
lean_inc_ref(v_str_1028_);
lean_dec_ref_known(v_a_1025_, 2);
v___x_1029_ = l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability(v_str_1028_);
if (lean_obj_tag(v___x_1029_) == 0)
{
v_a_1025_ = v_pre_1027_;
goto _start;
}
else
{
lean_object* v_val_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1056_; 
v_val_1031_ = lean_ctor_get(v___x_1029_, 0);
v_isSharedCheck_1056_ = !lean_is_exclusive(v___x_1029_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1033_ = v___x_1029_;
v_isShared_1034_ = v_isSharedCheck_1056_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_val_1031_);
lean_dec(v___x_1029_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1056_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v_fileName_1035_; lean_object* v_fileMap_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; uint8_t v___x_1039_; uint8_t v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; uint8_t v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1050_; 
v_fileName_1035_ = lean_ctor_get(v_inputCtx_1023_, 1);
v_fileMap_1036_ = lean_ctor_get(v_inputCtx_1023_, 2);
lean_inc_ref(v_fileMap_1036_);
v___x_1037_ = l_Lean_FileMap_toPosition(v_fileMap_1036_, v_startPos_1024_);
v___x_1038_ = lean_box(0);
v___x_1039_ = 0;
v___x_1040_ = 2;
v___x_1041_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___closed__0));
v___x_1042_ = ((lean_object*)(l___private_Lean_Elab_Import_0__Lean_Elab_checkModuleNamePortability_go___closed__0));
v___x_1043_ = 1;
lean_inc(v_mainModule_1022_);
v___x_1044_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mainModule_1022_, v___x_1043_);
v___x_1045_ = lean_string_append(v___x_1042_, v___x_1044_);
lean_dec_ref(v___x_1044_);
v___x_1046_ = ((lean_object*)(l___private_Lean_Elab_Import_0__Lean_Elab_checkModuleNamePortability_go___closed__1));
v___x_1047_ = lean_string_append(v___x_1045_, v___x_1046_);
v___x_1048_ = lean_string_append(v___x_1047_, v_val_1031_);
lean_dec(v_val_1031_);
if (v_isShared_1034_ == 0)
{
lean_ctor_set_tag(v___x_1033_, 3);
lean_ctor_set(v___x_1033_, 0, v___x_1048_);
v___x_1050_ = v___x_1033_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v___x_1048_);
v___x_1050_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1051_ = l_Lean_MessageData_ofFormat(v___x_1050_);
lean_inc_ref(v_fileName_1035_);
v___x_1052_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1052_, 0, v_fileName_1035_);
lean_ctor_set(v___x_1052_, 1, v___x_1037_);
lean_ctor_set(v___x_1052_, 2, v___x_1038_);
lean_ctor_set(v___x_1052_, 3, v___x_1041_);
lean_ctor_set(v___x_1052_, 4, v___x_1051_);
lean_ctor_set_uint8(v___x_1052_, sizeof(void*)*5, v___x_1039_);
lean_ctor_set_uint8(v___x_1052_, sizeof(void*)*5 + 1, v___x_1040_);
lean_ctor_set_uint8(v___x_1052_, sizeof(void*)*5 + 2, v___x_1039_);
v___x_1053_ = l_Lean_MessageLog_add(v___x_1052_, v_a_1026_);
v_a_1025_ = v_pre_1027_;
v_a_1026_ = v___x_1053_;
goto _start;
}
}
}
}
default: 
{
lean_object* v_pre_1057_; 
v_pre_1057_ = lean_ctor_get(v_a_1025_, 0);
lean_inc(v_pre_1057_);
lean_dec_ref_known(v_a_1025_, 2);
v_a_1025_ = v_pre_1057_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_checkModuleNamePortability_go___boxed(lean_object* v_mainModule_1059_, lean_object* v_inputCtx_1060_, lean_object* v_startPos_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l___private_Lean_Elab_Import_0__Lean_Elab_checkModuleNamePortability_go(v_mainModule_1059_, v_inputCtx_1060_, v_startPos_1061_, v_a_1062_, v_a_1063_);
lean_dec(v_startPos_1061_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkModuleNamePortability(lean_object* v_mainModule_1065_, lean_object* v_inputCtx_1066_, lean_object* v_startPos_1067_, lean_object* v_messages_1068_){
_start:
{
lean_object* v___x_1069_; 
lean_inc(v_mainModule_1065_);
v___x_1069_ = l___private_Lean_Elab_Import_0__Lean_Elab_checkModuleNamePortability_go(v_mainModule_1065_, v_inputCtx_1066_, v_startPos_1067_, v_mainModule_1065_, v_messages_1068_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkModuleNamePortability___boxed(lean_object* v_mainModule_1070_, lean_object* v_inputCtx_1071_, lean_object* v_startPos_1072_, lean_object* v_messages_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l_Lean_Elab_checkModuleNamePortability(v_mainModule_1070_, v_inputCtx_1071_, v_startPos_1072_, v_messages_1073_);
lean_dec(v_startPos_1072_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_processHeaderCore___lam__0(lean_object* v_package_x3f_1075_, lean_object* v_ps_1076_){
_start:
{
lean_object* v_importedEntries_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1084_; 
v_importedEntries_1077_ = lean_ctor_get(v_ps_1076_, 0);
v_isSharedCheck_1084_ = !lean_is_exclusive(v_ps_1076_);
if (v_isSharedCheck_1084_ == 0)
{
lean_object* v_unused_1085_; 
v_unused_1085_ = lean_ctor_get(v_ps_1076_, 1);
lean_dec(v_unused_1085_);
v___x_1079_ = v_ps_1076_;
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_importedEntries_1077_);
lean_dec(v_ps_1076_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v___x_1082_; 
if (v_isShared_1080_ == 0)
{
lean_ctor_set(v___x_1079_, 1, v_package_x3f_1075_);
v___x_1082_ = v___x_1079_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_importedEntries_1077_);
lean_ctor_set(v_reuseFailAlloc_1083_, 1, v_package_x3f_1075_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
}
}
lean_object* l_Lean_Elab_processHeaderCore(lean_object* v_startPos_1086_, lean_object* v_imports_1087_, uint8_t v_isModule_1088_, lean_object* v_opts_1089_, lean_object* v_messages_1090_, lean_object* v_inputCtx_1091_, uint32_t v_trustLevel_1092_, lean_object* v_plugins_1093_, uint8_t v_leakEnv_1094_, lean_object* v_mainModule_1095_, lean_object* v_package_x3f_1096_, lean_object* v_arts_1097_, lean_object* v_headerStx_x3f_1098_, lean_object* v_origHeaderStx_x3f_1099_){
_start:
{
lean_object* v___y_1102_; lean_object* v___y_1103_; lean_object* v___f_1108_; lean_object* v_fst_1110_; lean_object* v_snd_1111_; uint8_t v___x_1122_; uint8_t v___y_1124_; 
v___f_1108_ = lean_alloc_closure((void*)(l_Lean_Elab_processHeaderCore___lam__0), 2, 1);
lean_closure_set(v___f_1108_, 0, v_package_x3f_1096_);
v___x_1122_ = 1;
if (v_isModule_1088_ == 0)
{
uint8_t v___x_1157_; 
v___x_1157_ = 2;
v___y_1124_ = v___x_1157_;
goto v___jp_1123_;
}
else
{
lean_object* v___x_1158_; uint8_t v___x_1159_; 
v___x_1158_ = l_Lean_Elab_inServer;
v___x_1159_ = l_Lean_Option_get___at___00Lean_Elab_checkDeprecatedImports_spec__0(v_opts_1089_, v___x_1158_);
if (v___x_1159_ == 0)
{
uint8_t v___x_1160_; 
v___x_1160_ = 0;
v___y_1124_ = v___x_1160_;
goto v___jp_1123_;
}
else
{
uint8_t v___x_1161_; 
v___x_1161_ = 1;
v___y_1124_ = v___x_1161_;
goto v___jp_1123_;
}
}
v___jp_1101_:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
lean_inc(v_startPos_1086_);
lean_inc_ref(v_inputCtx_1091_);
v___x_1104_ = l_Lean_Elab_checkDeprecatedImports(v___y_1103_, v_imports_1087_, v_opts_1089_, v_inputCtx_1091_, v_startPos_1086_, v___y_1102_, v_headerStx_x3f_1098_, v_origHeaderStx_x3f_1099_);
lean_dec_ref(v_imports_1087_);
lean_inc(v_mainModule_1095_);
v___x_1105_ = l___private_Lean_Elab_Import_0__Lean_Elab_checkModuleNamePortability_go(v_mainModule_1095_, v_inputCtx_1091_, v_startPos_1086_, v_mainModule_1095_, v___x_1104_);
lean_dec(v_startPos_1086_);
v___x_1106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1106_, 0, v___y_1103_);
lean_ctor_set(v___x_1106_, 1, v___x_1105_);
v___x_1107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1106_);
return v___x_1107_;
}
v___jp_1109_:
{
lean_object* v___x_1112_; lean_object* v_toEnvExtension_1113_; lean_object* v_asyncMode_1114_; uint8_t v_logWrites_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; uint8_t v___x_1118_; 
v___x_1112_ = l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
v_toEnvExtension_1113_ = lean_ctor_get(v___x_1112_, 0);
v_asyncMode_1114_ = lean_ctor_get(v_toEnvExtension_1113_, 2);
v_logWrites_1115_ = lean_ctor_get_uint8(v_toEnvExtension_1113_, sizeof(void*)*6);
lean_inc(v_mainModule_1095_);
v___x_1116_ = l_Lean_Environment_setMainModule(v_fst_1110_, v_mainModule_1095_);
v___x_1117_ = lean_box(0);
v___x_1118_ = 1;
if (v_logWrites_1115_ == 0)
{
lean_object* v___x_1119_; 
lean_inc_ref(v_toEnvExtension_1113_);
v___x_1119_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1113_, v___x_1116_, v___f_1108_, v_asyncMode_1114_, v___x_1117_, v___x_1118_);
v___y_1102_ = v_snd_1111_;
v___y_1103_ = v___x_1119_;
goto v___jp_1101_;
}
else
{
lean_object* v___x_1120_; lean_object* v___x_1121_; 
lean_inc_ref_n(v_toEnvExtension_1113_, 2);
v___x_1120_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1113_, v___x_1116_);
lean_dec_ref(v___x_1116_);
v___x_1121_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1113_, v___x_1120_, v___f_1108_, v_asyncMode_1114_, v___x_1117_, v___x_1118_);
v___y_1102_ = v_snd_1111_;
v___y_1103_ = v___x_1121_;
goto v___jp_1101_;
}
}
v___jp_1123_:
{
lean_object* v___x_1125_; 
lean_inc_ref(v_opts_1089_);
lean_inc_ref(v_imports_1087_);
v___x_1125_ = l_Lean_importModules(v_imports_1087_, v_opts_1089_, v_trustLevel_1092_, v_plugins_1093_, v_leakEnv_1094_, v___x_1122_, v___y_1124_, v_arts_1097_);
if (lean_obj_tag(v___x_1125_) == 0)
{
lean_object* v_a_1126_; 
v_a_1126_ = lean_ctor_get(v___x_1125_, 0);
lean_inc(v_a_1126_);
lean_dec_ref_known(v___x_1125_, 1);
v_fst_1110_ = v_a_1126_;
v_snd_1111_ = v_messages_1090_;
goto v___jp_1109_;
}
else
{
lean_object* v_a_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1156_; 
v_a_1127_ = lean_ctor_get(v___x_1125_, 0);
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_1125_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1129_ = v___x_1125_;
v_isShared_1130_ = v_isSharedCheck_1156_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_a_1127_);
lean_dec(v___x_1125_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1156_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
uint32_t v___x_1131_; lean_object* v___x_1132_; 
v___x_1131_ = 0;
v___x_1132_ = l_Lean_mkEmptyEnvironment(v___x_1131_);
if (lean_obj_tag(v___x_1132_) == 0)
{
lean_object* v_a_1133_; lean_object* v_fileName_1134_; lean_object* v_fileMap_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; uint8_t v___x_1138_; uint8_t v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1143_; 
v_a_1133_ = lean_ctor_get(v___x_1132_, 0);
lean_inc(v_a_1133_);
lean_dec_ref_known(v___x_1132_, 1);
v_fileName_1134_ = lean_ctor_get(v_inputCtx_1091_, 1);
v_fileMap_1135_ = lean_ctor_get(v_inputCtx_1091_, 2);
lean_inc_ref(v_fileMap_1135_);
v___x_1136_ = l_Lean_FileMap_toPosition(v_fileMap_1135_, v_startPos_1086_);
v___x_1137_ = lean_box(0);
v___x_1138_ = 0;
v___x_1139_ = 2;
v___x_1140_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___closed__0));
v___x_1141_ = lean_io_error_to_string(v_a_1127_);
if (v_isShared_1130_ == 0)
{
lean_ctor_set_tag(v___x_1129_, 3);
lean_ctor_set(v___x_1129_, 0, v___x_1141_);
v___x_1143_ = v___x_1129_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v___x_1141_);
v___x_1143_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1144_ = l_Lean_MessageData_ofFormat(v___x_1143_);
lean_inc_ref(v_fileName_1134_);
v___x_1145_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1145_, 0, v_fileName_1134_);
lean_ctor_set(v___x_1145_, 1, v___x_1136_);
lean_ctor_set(v___x_1145_, 2, v___x_1137_);
lean_ctor_set(v___x_1145_, 3, v___x_1140_);
lean_ctor_set(v___x_1145_, 4, v___x_1144_);
lean_ctor_set_uint8(v___x_1145_, sizeof(void*)*5, v___x_1138_);
lean_ctor_set_uint8(v___x_1145_, sizeof(void*)*5 + 1, v___x_1139_);
lean_ctor_set_uint8(v___x_1145_, sizeof(void*)*5 + 2, v___x_1138_);
v___x_1146_ = l_Lean_MessageLog_add(v___x_1145_, v_messages_1090_);
v_fst_1110_ = v_a_1133_;
v_snd_1111_ = v___x_1146_;
goto v___jp_1109_;
}
}
else
{
lean_object* v_a_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1155_; 
lean_del_object(v___x_1129_);
lean_dec(v_a_1127_);
lean_dec_ref(v___f_1108_);
lean_dec(v_origHeaderStx_x3f_1099_);
lean_dec(v_headerStx_x3f_1098_);
lean_dec(v_mainModule_1095_);
lean_dec_ref(v_inputCtx_1091_);
lean_dec_ref(v_messages_1090_);
lean_dec_ref(v_opts_1089_);
lean_dec_ref(v_imports_1087_);
lean_dec(v_startPos_1086_);
v_a_1148_ = lean_ctor_get(v___x_1132_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1150_ = v___x_1132_;
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_a_1148_);
lean_dec(v___x_1132_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1153_; 
if (v_isShared_1151_ == 0)
{
v___x_1153_ = v___x_1150_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_a_1148_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_processHeaderCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_startPos_1086_ = stack[0].m_obj;
lean_object* v_imports_1087_ = stack[1].m_obj;
uint8_t v_isModule_1088_ = stack[2].m_num;
lean_object* v_opts_1089_ = stack[3].m_obj;
lean_object* v_messages_1090_ = stack[4].m_obj;
lean_object* v_inputCtx_1091_ = stack[5].m_obj;
uint32_t v_trustLevel_1092_ = stack[6].m_num;
lean_object* v_plugins_1093_ = stack[7].m_obj;
uint8_t v_leakEnv_1094_ = stack[8].m_num;
lean_object* v_mainModule_1095_ = stack[9].m_obj;
lean_object* v_package_x3f_1096_ = stack[10].m_obj;
lean_object* v_arts_1097_ = stack[11].m_obj;
lean_object* v_headerStx_x3f_1098_ = stack[12].m_obj;
lean_object* v_origHeaderStx_x3f_1099_ = stack[13].m_obj;
lean_object* v_res_1162_;
v_res_1162_ = l_Lean_Elab_processHeaderCore(v_startPos_1086_, v_imports_1087_, v_isModule_1088_, v_opts_1089_, v_messages_1090_, v_inputCtx_1091_, v_trustLevel_1092_, v_plugins_1093_, v_leakEnv_1094_, v_mainModule_1095_, v_package_x3f_1096_, v_arts_1097_, v_headerStx_x3f_1098_, v_origHeaderStx_x3f_1099_);
stack->m_obj
 = v_res_1162_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_processHeaderCore___boxed(lean_object* v_startPos_1163_, lean_object* v_imports_1164_, lean_object* v_isModule_1165_, lean_object* v_opts_1166_, lean_object* v_messages_1167_, lean_object* v_inputCtx_1168_, lean_object* v_trustLevel_1169_, lean_object* v_plugins_1170_, lean_object* v_leakEnv_1171_, lean_object* v_mainModule_1172_, lean_object* v_package_x3f_1173_, lean_object* v_arts_1174_, lean_object* v_headerStx_x3f_1175_, lean_object* v_origHeaderStx_x3f_1176_, lean_object* v_a_1177_){
_start:
{
uint8_t v_isModule_boxed_1178_; uint32_t v_trustLevel_boxed_1179_; uint8_t v_leakEnv_boxed_1180_; lean_object* v_res_1181_; 
v_isModule_boxed_1178_ = lean_unbox(v_isModule_1165_);
v_trustLevel_boxed_1179_ = lean_unbox_uint32(v_trustLevel_1169_);
lean_dec(v_trustLevel_1169_);
v_leakEnv_boxed_1180_ = lean_unbox(v_leakEnv_1171_);
v_res_1181_ = l_Lean_Elab_processHeaderCore(v_startPos_1163_, v_imports_1164_, v_isModule_boxed_1178_, v_opts_1166_, v_messages_1167_, v_inputCtx_1168_, v_trustLevel_boxed_1179_, v_plugins_1170_, v_leakEnv_boxed_1180_, v_mainModule_1172_, v_package_x3f_1173_, v_arts_1174_, v_headerStx_x3f_1175_, v_origHeaderStx_x3f_1176_);
return v_res_1181_;
}
}
lean_object* l_Lean_Elab_processHeader(lean_object* v_header_1182_, lean_object* v_opts_1183_, lean_object* v_messages_1184_, lean_object* v_inputCtx_1185_, uint32_t v_trustLevel_1186_, lean_object* v_plugins_1187_, uint8_t v_leakEnv_1188_, lean_object* v_mainModule_1189_){
_start:
{
lean_object* v___x_1191_; uint8_t v___x_1192_; lean_object* v___x_1193_; uint8_t v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1191_ = l_Lean_Elab_HeaderSyntax_startPos(v_header_1182_);
v___x_1192_ = 1;
lean_inc(v_header_1182_);
v___x_1193_ = l_Lean_Elab_HeaderSyntax_imports(v_header_1182_, v___x_1192_);
v___x_1194_ = l_Lean_Elab_HeaderSyntax_isModule(v_header_1182_);
v___x_1195_ = lean_box(0);
v___x_1196_ = lean_box(1);
v___x_1197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1197_, 0, v_header_1182_);
v___x_1198_ = l_Lean_Elab_processHeaderCore(v___x_1191_, v___x_1193_, v___x_1194_, v_opts_1183_, v_messages_1184_, v_inputCtx_1185_, v_trustLevel_1186_, v_plugins_1187_, v_leakEnv_1188_, v_mainModule_1189_, v___x_1195_, v___x_1196_, v___x_1197_, v___x_1195_);
return v___x_1198_;
}
}
LEAN_EXPORT void l_Lean_Elab_processHeader_0interp(lean_interpreter_value* stack)
{
lean_object* v_header_1182_ = stack[0].m_obj;
lean_object* v_opts_1183_ = stack[1].m_obj;
lean_object* v_messages_1184_ = stack[2].m_obj;
lean_object* v_inputCtx_1185_ = stack[3].m_obj;
uint32_t v_trustLevel_1186_ = stack[4].m_num;
lean_object* v_plugins_1187_ = stack[5].m_obj;
uint8_t v_leakEnv_1188_ = stack[6].m_num;
lean_object* v_mainModule_1189_ = stack[7].m_obj;
lean_object* v_res_1199_;
v_res_1199_ = l_Lean_Elab_processHeader(v_header_1182_, v_opts_1183_, v_messages_1184_, v_inputCtx_1185_, v_trustLevel_1186_, v_plugins_1187_, v_leakEnv_1188_, v_mainModule_1189_);
stack->m_obj
 = v_res_1199_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_processHeader___boxed(lean_object* v_header_1200_, lean_object* v_opts_1201_, lean_object* v_messages_1202_, lean_object* v_inputCtx_1203_, lean_object* v_trustLevel_1204_, lean_object* v_plugins_1205_, lean_object* v_leakEnv_1206_, lean_object* v_mainModule_1207_, lean_object* v_a_1208_){
_start:
{
uint32_t v_trustLevel_boxed_1209_; uint8_t v_leakEnv_boxed_1210_; lean_object* v_res_1211_; 
v_trustLevel_boxed_1209_ = lean_unbox_uint32(v_trustLevel_1204_);
lean_dec(v_trustLevel_1204_);
v_leakEnv_boxed_1210_ = lean_unbox(v_leakEnv_1206_);
v_res_1211_ = l_Lean_Elab_processHeader(v_header_1200_, v_opts_1201_, v_messages_1202_, v_inputCtx_1203_, v_trustLevel_boxed_1209_, v_plugins_1205_, v_leakEnv_boxed_1210_, v_mainModule_1207_);
return v_res_1211_;
}
}
lean_object* l_Lean_Elab_parseImports(lean_object* v_input_1213_, lean_object* v_fileName_1214_){
_start:
{
lean_object* v___y_1217_; 
if (lean_obj_tag(v_fileName_1214_) == 0)
{
lean_object* v___x_1262_; 
v___x_1262_ = ((lean_object*)(l_Lean_Elab_parseImports___closed__0));
v___y_1217_ = v___x_1262_;
goto v___jp_1216_;
}
else
{
lean_object* v_val_1263_; 
v_val_1263_ = lean_ctor_get(v_fileName_1214_, 0);
lean_inc(v_val_1263_);
lean_dec_ref_known(v_fileName_1214_, 1);
v___y_1217_ = v_val_1263_;
goto v___jp_1216_;
}
v___jp_1216_:
{
uint8_t v___x_1218_; lean_object* v___x_1219_; lean_object* v_inputCtx_1220_; lean_object* v___x_1221_; 
v___x_1218_ = 1;
v___x_1219_ = lean_string_utf8_byte_size(v_input_1213_);
v_inputCtx_1220_ = l_Lean_Parser_mkInputContext___redArg(v_input_1213_, v___y_1217_, v___x_1218_, v___x_1219_);
lean_inc_ref(v_inputCtx_1220_);
v___x_1221_ = l_Lean_Parser_parseHeader(v_inputCtx_1220_);
if (lean_obj_tag(v___x_1221_) == 0)
{
lean_object* v_a_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1253_; 
v_a_1222_ = lean_ctor_get(v___x_1221_, 0);
v_isSharedCheck_1253_ = !lean_is_exclusive(v___x_1221_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1224_ = v___x_1221_;
v_isShared_1225_ = v_isSharedCheck_1253_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_a_1222_);
lean_dec(v___x_1221_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1253_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v_snd_1226_; lean_object* v_fst_1227_; lean_object* v_fst_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1251_; 
v_snd_1226_ = lean_ctor_get(v_a_1222_, 1);
lean_inc(v_snd_1226_);
v_fst_1227_ = lean_ctor_get(v_snd_1226_, 0);
lean_inc(v_fst_1227_);
v_fst_1228_ = lean_ctor_get(v_a_1222_, 0);
v_isSharedCheck_1251_ = !lean_is_exclusive(v_a_1222_);
if (v_isSharedCheck_1251_ == 0)
{
lean_object* v_unused_1252_; 
v_unused_1252_ = lean_ctor_get(v_a_1222_, 1);
lean_dec(v_unused_1252_);
v___x_1230_ = v_a_1222_;
v_isShared_1231_ = v_isSharedCheck_1251_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_fst_1228_);
lean_dec(v_a_1222_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1251_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v_snd_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1249_; 
v_snd_1232_ = lean_ctor_get(v_snd_1226_, 1);
v_isSharedCheck_1249_ = !lean_is_exclusive(v_snd_1226_);
if (v_isSharedCheck_1249_ == 0)
{
lean_object* v_unused_1250_; 
v_unused_1250_ = lean_ctor_get(v_snd_1226_, 0);
lean_dec(v_unused_1250_);
v___x_1234_ = v_snd_1226_;
v_isShared_1235_ = v_isSharedCheck_1249_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_snd_1232_);
lean_dec(v_snd_1226_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1249_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v_fileMap_1236_; lean_object* v_pos_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1241_; 
v_fileMap_1236_ = lean_ctor_get(v_inputCtx_1220_, 2);
lean_inc_ref(v_fileMap_1236_);
lean_dec_ref(v_inputCtx_1220_);
v_pos_1237_ = lean_ctor_get(v_fst_1227_, 0);
lean_inc(v_pos_1237_);
lean_dec(v_fst_1227_);
v___x_1238_ = l_Lean_Elab_HeaderSyntax_imports(v_fst_1228_, v___x_1218_);
v___x_1239_ = l_Lean_FileMap_toPosition(v_fileMap_1236_, v_pos_1237_);
lean_dec(v_pos_1237_);
if (v_isShared_1235_ == 0)
{
lean_ctor_set(v___x_1234_, 0, v___x_1239_);
v___x_1241_ = v___x_1234_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v___x_1239_);
lean_ctor_set(v_reuseFailAlloc_1248_, 1, v_snd_1232_);
v___x_1241_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
lean_object* v___x_1243_; 
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 1, v___x_1241_);
lean_ctor_set(v___x_1230_, 0, v___x_1238_);
v___x_1243_ = v___x_1230_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v___x_1238_);
lean_ctor_set(v_reuseFailAlloc_1247_, 1, v___x_1241_);
v___x_1243_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
lean_object* v___x_1245_; 
if (v_isShared_1225_ == 0)
{
lean_ctor_set(v___x_1224_, 0, v___x_1243_);
v___x_1245_ = v___x_1224_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v___x_1243_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1261_; 
lean_dec_ref(v_inputCtx_1220_);
v_a_1254_ = lean_ctor_get(v___x_1221_, 0);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1221_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1256_ = v___x_1221_;
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_a_1254_);
lean_dec(v___x_1221_);
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
}
LEAN_EXPORT void l_Lean_Elab_parseImports_0interp(lean_interpreter_value* stack)
{
lean_object* v_input_1213_ = stack[0].m_obj;
lean_object* v_fileName_1214_ = stack[1].m_obj;
lean_object* v_res_1264_;
v_res_1264_ = l_Lean_Elab_parseImports(v_input_1213_, v_fileName_1214_);
stack->m_obj
 = v_res_1264_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_parseImports___boxed(lean_object* v_input_1265_, lean_object* v_fileName_1266_, lean_object* v_a_1267_){
_start:
{
lean_object* v_res_1268_; 
v_res_1268_ = l_Lean_Elab_parseImports(v_input_1265_, v_fileName_1266_);
return v_res_1268_;
}
}
lean_object* l_IO_print___at___00IO_println___at___00Lean_Elab_printImports_spec__0_spec__0(lean_object* v_s_1269_){
_start:
{
lean_object* v___x_1271_; lean_object* v_putStr_1272_; lean_object* v___x_1273_; 
v___x_1271_ = lean_get_stdout();
v_putStr_1272_ = lean_ctor_get(v___x_1271_, 4);
lean_inc_ref(v_putStr_1272_);
lean_dec_ref(v___x_1271_);
v___x_1273_ = lean_apply_2(v_putStr_1272_, v_s_1269_, lean_box(0));
return v___x_1273_;
}
}
LEAN_EXPORT void l_IO_print___at___00IO_println___at___00Lean_Elab_printImports_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1269_ = stack[0].m_obj;
lean_object* v_res_1274_;
v_res_1274_ = l_IO_print___at___00IO_println___at___00Lean_Elab_printImports_spec__0_spec__0(v_s_1269_);
stack->m_obj
 = v_res_1274_;
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00Lean_Elab_printImports_spec__0_spec__0___boxed(lean_object* v_s_1275_, lean_object* v_a_1276_){
_start:
{
lean_object* v_res_1277_; 
v_res_1277_ = l_IO_print___at___00IO_println___at___00Lean_Elab_printImports_spec__0_spec__0(v_s_1275_);
return v_res_1277_;
}
}
lean_object* l_IO_println___at___00Lean_Elab_printImports_spec__0(lean_object* v_s_1278_){
_start:
{
uint32_t v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1280_ = 10;
v___x_1281_ = lean_string_push(v_s_1278_, v___x_1280_);
v___x_1282_ = l_IO_print___at___00IO_println___at___00Lean_Elab_printImports_spec__0_spec__0(v___x_1281_);
return v___x_1282_;
}
}
LEAN_EXPORT void l_IO_println___at___00Lean_Elab_printImports_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1278_ = stack[0].m_obj;
lean_object* v_res_1283_;
v_res_1283_ = l_IO_println___at___00Lean_Elab_printImports_spec__0(v_s_1278_);
stack->m_obj
 = v_res_1283_;
}
LEAN_EXPORT lean_object* l_IO_println___at___00Lean_Elab_printImports_spec__0___boxed(lean_object* v_s_1284_, lean_object* v_a_1285_){
_start:
{
lean_object* v_res_1286_; 
v_res_1286_ = l_IO_println___at___00Lean_Elab_printImports_spec__0(v_s_1284_);
return v_res_1286_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImports_spec__1(lean_object* v_as_1287_, size_t v_sz_1288_, size_t v_i_1289_, lean_object* v_b_1290_){
_start:
{
uint8_t v___x_1292_; 
v___x_1292_ = lean_usize_dec_lt(v_i_1289_, v_sz_1288_);
if (v___x_1292_ == 0)
{
lean_object* v___x_1293_; 
v___x_1293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1293_, 0, v_b_1290_);
return v___x_1293_;
}
else
{
lean_object* v_a_1294_; lean_object* v_module_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; 
v_a_1294_ = lean_array_uget_borrowed(v_as_1287_, v_i_1289_);
v_module_1295_ = lean_ctor_get(v_a_1294_, 0);
v___x_1296_ = lean_box(0);
lean_inc(v_module_1295_);
v___x_1297_ = l_Lean_findOLean(v_module_1295_);
if (lean_obj_tag(v___x_1297_) == 0)
{
lean_object* v_a_1298_; lean_object* v___x_1299_; 
v_a_1298_ = lean_ctor_get(v___x_1297_, 0);
lean_inc(v_a_1298_);
lean_dec_ref_known(v___x_1297_, 1);
v___x_1299_ = l_IO_println___at___00Lean_Elab_printImports_spec__0(v_a_1298_);
if (lean_obj_tag(v___x_1299_) == 0)
{
size_t v___x_1300_; size_t v___x_1301_; 
lean_dec_ref_known(v___x_1299_, 1);
v___x_1300_ = ((size_t)1ULL);
v___x_1301_ = lean_usize_add(v_i_1289_, v___x_1300_);
v_i_1289_ = v___x_1301_;
v_b_1290_ = v___x_1296_;
goto _start;
}
else
{
return v___x_1299_;
}
}
else
{
lean_object* v_a_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1310_; 
v_a_1303_ = lean_ctor_get(v___x_1297_, 0);
v_isSharedCheck_1310_ = !lean_is_exclusive(v___x_1297_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1305_ = v___x_1297_;
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_a_1303_);
lean_dec(v___x_1297_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v___x_1308_; 
if (v_isShared_1306_ == 0)
{
v___x_1308_ = v___x_1305_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v_a_1303_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImports_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1287_ = stack[0].m_obj;
size_t v_sz_1288_ = stack[1].m_num;
size_t v_i_1289_ = stack[2].m_num;
lean_object* v_b_1290_ = stack[3].m_obj;
lean_object* v_res_1311_;
v_res_1311_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImports_spec__1(v_as_1287_, v_sz_1288_, v_i_1289_, v_b_1290_);
stack->m_obj
 = v_res_1311_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImports_spec__1___boxed(lean_object* v_as_1312_, lean_object* v_sz_1313_, lean_object* v_i_1314_, lean_object* v_b_1315_, lean_object* v___y_1316_){
_start:
{
size_t v_sz_boxed_1317_; size_t v_i_boxed_1318_; lean_object* v_res_1319_; 
v_sz_boxed_1317_ = lean_unbox_usize(v_sz_1313_);
lean_dec(v_sz_1313_);
v_i_boxed_1318_ = lean_unbox_usize(v_i_1314_);
lean_dec(v_i_1314_);
v_res_1319_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImports_spec__1(v_as_1312_, v_sz_boxed_1317_, v_i_boxed_1318_, v_b_1315_);
lean_dec_ref(v_as_1312_);
return v_res_1319_;
}
}
lean_object* l_Lean_Elab_printImports(lean_object* v_input_1320_, lean_object* v_fileName_1321_){
_start:
{
lean_object* v___x_1323_; 
v___x_1323_ = l_Lean_Elab_parseImports(v_input_1320_, v_fileName_1321_);
if (lean_obj_tag(v___x_1323_) == 0)
{
lean_object* v_a_1324_; lean_object* v_fst_1325_; lean_object* v___x_1326_; size_t v_sz_1327_; size_t v___x_1328_; lean_object* v___x_1329_; 
v_a_1324_ = lean_ctor_get(v___x_1323_, 0);
lean_inc(v_a_1324_);
lean_dec_ref_known(v___x_1323_, 1);
v_fst_1325_ = lean_ctor_get(v_a_1324_, 0);
lean_inc(v_fst_1325_);
lean_dec(v_a_1324_);
v___x_1326_ = lean_box(0);
v_sz_1327_ = lean_array_size(v_fst_1325_);
v___x_1328_ = ((size_t)0ULL);
v___x_1329_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImports_spec__1(v_fst_1325_, v_sz_1327_, v___x_1328_, v___x_1326_);
lean_dec(v_fst_1325_);
if (lean_obj_tag(v___x_1329_) == 0)
{
lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1336_; 
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1336_ == 0)
{
lean_object* v_unused_1337_; 
v_unused_1337_ = lean_ctor_get(v___x_1329_, 0);
lean_dec(v_unused_1337_);
v___x_1331_ = v___x_1329_;
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
else
{
lean_dec(v___x_1329_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1334_; 
if (v_isShared_1332_ == 0)
{
lean_ctor_set(v___x_1331_, 0, v___x_1326_);
v___x_1334_ = v___x_1331_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v___x_1326_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
}
else
{
return v___x_1329_;
}
}
else
{
lean_object* v_a_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1345_; 
v_a_1338_ = lean_ctor_get(v___x_1323_, 0);
v_isSharedCheck_1345_ = !lean_is_exclusive(v___x_1323_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1340_ = v___x_1323_;
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_a_1338_);
lean_dec(v___x_1323_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v___x_1343_; 
if (v_isShared_1341_ == 0)
{
v___x_1343_ = v___x_1340_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v_a_1338_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_printImports_0interp(lean_interpreter_value* stack)
{
lean_object* v_input_1320_ = stack[0].m_obj;
lean_object* v_fileName_1321_ = stack[1].m_obj;
lean_object* v_res_1346_;
v_res_1346_ = l_Lean_Elab_printImports(v_input_1320_, v_fileName_1321_);
stack->m_obj
 = v_res_1346_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_printImports___boxed(lean_object* v_input_1347_, lean_object* v_fileName_1348_, lean_object* v_a_1349_){
_start:
{
lean_object* v_res_1350_; 
v_res_1350_ = l_Lean_Elab_printImports(v_input_1347_, v_fileName_1348_);
return v_res_1350_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImportSrcs_spec__0(lean_object* v_a_1351_, lean_object* v_as_1352_, size_t v_sz_1353_, size_t v_i_1354_, lean_object* v_b_1355_){
_start:
{
uint8_t v___x_1357_; 
v___x_1357_ = lean_usize_dec_lt(v_i_1354_, v_sz_1353_);
if (v___x_1357_ == 0)
{
lean_object* v___x_1358_; 
lean_dec(v_a_1351_);
v___x_1358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1358_, 0, v_b_1355_);
return v___x_1358_;
}
else
{
lean_object* v_a_1359_; lean_object* v_module_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; 
v_a_1359_ = lean_array_uget_borrowed(v_as_1352_, v_i_1354_);
v_module_1360_ = lean_ctor_get(v_a_1359_, 0);
v___x_1361_ = lean_box(0);
lean_inc(v_module_1360_);
lean_inc(v_a_1351_);
v___x_1362_ = l_Lean_findLean(v_a_1351_, v_module_1360_);
if (lean_obj_tag(v___x_1362_) == 0)
{
lean_object* v_a_1363_; lean_object* v___x_1364_; 
v_a_1363_ = lean_ctor_get(v___x_1362_, 0);
lean_inc(v_a_1363_);
lean_dec_ref_known(v___x_1362_, 1);
v___x_1364_ = l_IO_println___at___00Lean_Elab_printImports_spec__0(v_a_1363_);
if (lean_obj_tag(v___x_1364_) == 0)
{
size_t v___x_1365_; size_t v___x_1366_; 
lean_dec_ref_known(v___x_1364_, 1);
v___x_1365_ = ((size_t)1ULL);
v___x_1366_ = lean_usize_add(v_i_1354_, v___x_1365_);
v_i_1354_ = v___x_1366_;
v_b_1355_ = v___x_1361_;
goto _start;
}
else
{
lean_dec(v_a_1351_);
return v___x_1364_;
}
}
else
{
lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1375_; 
lean_dec(v_a_1351_);
v_a_1368_ = lean_ctor_get(v___x_1362_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1362_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1370_ = v___x_1362_;
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_dec(v___x_1362_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1373_; 
if (v_isShared_1371_ == 0)
{
v___x_1373_ = v___x_1370_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_a_1368_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImportSrcs_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1351_ = stack[0].m_obj;
lean_object* v_as_1352_ = stack[1].m_obj;
size_t v_sz_1353_ = stack[2].m_num;
size_t v_i_1354_ = stack[3].m_num;
lean_object* v_b_1355_ = stack[4].m_obj;
lean_object* v_res_1376_;
v_res_1376_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImportSrcs_spec__0(v_a_1351_, v_as_1352_, v_sz_1353_, v_i_1354_, v_b_1355_);
stack->m_obj
 = v_res_1376_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImportSrcs_spec__0___boxed(lean_object* v_a_1377_, lean_object* v_as_1378_, lean_object* v_sz_1379_, lean_object* v_i_1380_, lean_object* v_b_1381_, lean_object* v___y_1382_){
_start:
{
size_t v_sz_boxed_1383_; size_t v_i_boxed_1384_; lean_object* v_res_1385_; 
v_sz_boxed_1383_ = lean_unbox_usize(v_sz_1379_);
lean_dec(v_sz_1379_);
v_i_boxed_1384_ = lean_unbox_usize(v_i_1380_);
lean_dec(v_i_1380_);
v_res_1385_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImportSrcs_spec__0(v_a_1377_, v_as_1378_, v_sz_boxed_1383_, v_i_boxed_1384_, v_b_1381_);
lean_dec_ref(v_as_1378_);
return v_res_1385_;
}
}
lean_object* l_Lean_Elab_printImportSrcs(lean_object* v_input_1386_, lean_object* v_fileName_1387_){
_start:
{
lean_object* v___x_1389_; 
v___x_1389_ = l_Lean_getSrcSearchPath();
if (lean_obj_tag(v___x_1389_) == 0)
{
lean_object* v_a_1390_; lean_object* v___x_1391_; 
v_a_1390_ = lean_ctor_get(v___x_1389_, 0);
lean_inc(v_a_1390_);
lean_dec_ref_known(v___x_1389_, 1);
v___x_1391_ = l_Lean_Elab_parseImports(v_input_1386_, v_fileName_1387_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v_a_1392_; lean_object* v_fst_1393_; lean_object* v___x_1394_; size_t v_sz_1395_; size_t v___x_1396_; lean_object* v___x_1397_; 
v_a_1392_ = lean_ctor_get(v___x_1391_, 0);
lean_inc(v_a_1392_);
lean_dec_ref_known(v___x_1391_, 1);
v_fst_1393_ = lean_ctor_get(v_a_1392_, 0);
lean_inc(v_fst_1393_);
lean_dec(v_a_1392_);
v___x_1394_ = lean_box(0);
v_sz_1395_ = lean_array_size(v_fst_1393_);
v___x_1396_ = ((size_t)0ULL);
v___x_1397_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImportSrcs_spec__0(v_a_1390_, v_fst_1393_, v_sz_1395_, v___x_1396_, v___x_1394_);
lean_dec(v_fst_1393_);
if (lean_obj_tag(v___x_1397_) == 0)
{
lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1404_; 
v_isSharedCheck_1404_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1404_ == 0)
{
lean_object* v_unused_1405_; 
v_unused_1405_ = lean_ctor_get(v___x_1397_, 0);
lean_dec(v_unused_1405_);
v___x_1399_ = v___x_1397_;
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
else
{
lean_dec(v___x_1397_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1402_; 
if (v_isShared_1400_ == 0)
{
lean_ctor_set(v___x_1399_, 0, v___x_1394_);
v___x_1402_ = v___x_1399_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v___x_1394_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
}
else
{
return v___x_1397_;
}
}
else
{
lean_object* v_a_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1413_; 
lean_dec(v_a_1390_);
v_a_1406_ = lean_ctor_get(v___x_1391_, 0);
v_isSharedCheck_1413_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1408_ = v___x_1391_;
v_isShared_1409_ = v_isSharedCheck_1413_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_a_1406_);
lean_dec(v___x_1391_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1413_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1411_; 
if (v_isShared_1409_ == 0)
{
v___x_1411_ = v___x_1408_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_a_1406_);
v___x_1411_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
return v___x_1411_;
}
}
}
}
else
{
lean_object* v_a_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1421_; 
lean_dec(v_fileName_1387_);
lean_dec_ref(v_input_1386_);
v_a_1414_ = lean_ctor_get(v___x_1389_, 0);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1389_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1416_ = v___x_1389_;
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_a_1414_);
lean_dec(v___x_1389_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1419_; 
if (v_isShared_1417_ == 0)
{
v___x_1419_ = v___x_1416_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_a_1414_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_printImportSrcs_0interp(lean_interpreter_value* stack)
{
lean_object* v_input_1386_ = stack[0].m_obj;
lean_object* v_fileName_1387_ = stack[1].m_obj;
lean_object* v_res_1422_;
v_res_1422_ = l_Lean_Elab_printImportSrcs(v_input_1386_, v_fileName_1387_);
stack->m_obj
 = v_res_1422_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_printImportSrcs___boxed(lean_object* v_input_1423_, lean_object* v_fileName_1424_, lean_object* v_a_1425_){
_start:
{
lean_object* v_res_1426_; 
v_res_1426_ = l_Lean_Elab_printImportSrcs(v_input_1423_, v_fileName_1424_);
return v_res_1426_;
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

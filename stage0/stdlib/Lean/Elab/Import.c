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
v___x_17_ = l_Array_instInhabited___redArg();
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
lean_object* v___x_66_; lean_object* v_v_67_; lean_object* v___x_68_; lean_object* v_bs_x27_69_; lean_object* v___y_71_; lean_object* v___y_77_; uint8_t v___y_78_; uint8_t v___y_79_; lean_object* v___y_80_; uint8_t v___y_81_; lean_object* v___y_86_; uint8_t v___y_87_; lean_object* v___y_88_; lean_object* v___y_89_; uint8_t v___y_90_; uint8_t v___x_92_; 
v___x_66_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__4));
v_v_67_ = lean_array_uget(v_bs_64_, v_i_63_);
v___x_68_ = lean_unsigned_to_nat(0u);
v_bs_x27_69_ = lean_array_uset(v_bs_64_, v_i_63_, v___x_68_);
lean_inc(v_v_67_);
v___x_92_ = l_Lean_Syntax_isOfKind(v_v_67_, v___x_66_);
if (v___x_92_ == 0)
{
lean_object* v___x_93_; lean_object* v___x_94_; 
lean_dec(v_v_67_);
v___x_93_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8);
v___x_94_ = l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__1(v___x_93_);
v___y_71_ = v___x_94_;
goto v___jp_70_;
}
else
{
lean_object* v___y_96_; lean_object* v___y_97_; lean_object* v_allTk_98_; lean_object* v___x_108_; lean_object* v___y_110_; lean_object* v_metaTk_111_; lean_object* v_publicTk_127_; lean_object* v___x_141_; uint8_t v___x_142_; 
v___x_108_ = lean_unsigned_to_nat(1u);
v___x_141_ = l_Lean_Syntax_getArg(v_v_67_, v___x_68_);
v___x_142_ = l_Lean_Syntax_isNone(v___x_141_);
if (v___x_142_ == 0)
{
uint8_t v___x_143_; 
lean_inc(v___x_141_);
v___x_143_ = l_Lean_Syntax_matchesNull(v___x_141_, v___x_108_);
if (v___x_143_ == 0)
{
lean_object* v___x_144_; lean_object* v___x_145_; 
lean_dec(v___x_141_);
lean_dec(v_v_67_);
v___x_144_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8);
v___x_145_ = l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__1(v___x_144_);
v___y_71_ = v___x_145_;
goto v___jp_70_;
}
else
{
lean_object* v___x_146_; lean_object* v___x_147_; uint8_t v___x_148_; 
v___x_146_ = l_Lean_Syntax_getArg(v___x_141_, v___x_68_);
lean_dec(v___x_141_);
v___x_147_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__14));
lean_inc(v___x_146_);
v___x_148_ = l_Lean_Syntax_isOfKind(v___x_146_, v___x_147_);
if (v___x_148_ == 0)
{
lean_object* v___x_149_; lean_object* v___x_150_; 
lean_dec(v___x_146_);
lean_dec(v_v_67_);
v___x_149_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8);
v___x_150_ = l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__1(v___x_149_);
v___y_71_ = v___x_150_;
goto v___jp_70_;
}
else
{
lean_object* v_publicTk_151_; lean_object* v___x_152_; 
v_publicTk_151_ = l_Lean_Syntax_getArg(v___x_146_, v___x_68_);
lean_dec(v___x_146_);
v___x_152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_152_, 0, v_publicTk_151_);
v_publicTk_127_ = v___x_152_;
goto v___jp_126_;
}
}
}
else
{
lean_object* v___x_153_; 
lean_dec(v___x_141_);
v___x_153_ = lean_box(0);
v_publicTk_127_ = v___x_153_;
goto v___jp_126_;
}
v___jp_95_:
{
lean_object* v___x_99_; lean_object* v___x_100_; uint8_t v___x_101_; 
v___x_99_ = lean_unsigned_to_nat(5u);
v___x_100_ = l_Lean_Syntax_getArg(v_v_67_, v___x_99_);
v___x_101_ = l_Lean_Syntax_matchesNull(v___x_100_, v___x_68_);
if (v___x_101_ == 0)
{
lean_object* v___x_102_; lean_object* v___x_103_; 
lean_dec(v_allTk_98_);
lean_dec(v___y_97_);
lean_dec(v___y_96_);
lean_dec(v_v_67_);
v___x_102_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8);
v___x_103_ = l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__1(v___x_102_);
v___y_71_ = v___x_103_;
goto v___jp_70_;
}
else
{
lean_object* v___x_104_; lean_object* v_n_105_; lean_object* v___x_106_; 
v___x_104_ = lean_unsigned_to_nat(4u);
v_n_105_ = l_Lean_Syntax_getArg(v_v_67_, v___x_104_);
lean_dec(v_v_67_);
v___x_106_ = l_Lean_TSyntax_getId(v_n_105_);
lean_dec(v_n_105_);
if (lean_obj_tag(v_allTk_98_) == 0)
{
uint8_t v___x_107_; 
v___x_107_ = 0;
v___y_86_ = v___x_106_;
v___y_87_ = v___x_101_;
v___y_88_ = v___y_96_;
v___y_89_ = v___y_97_;
v___y_90_ = v___x_107_;
goto v___jp_85_;
}
else
{
lean_dec_ref_known(v_allTk_98_, 1);
v___y_86_ = v___x_106_;
v___y_87_ = v___x_101_;
v___y_88_ = v___y_96_;
v___y_89_ = v___y_97_;
v___y_90_ = v___x_101_;
goto v___jp_85_;
}
}
}
v___jp_109_:
{
lean_object* v___x_112_; lean_object* v___x_113_; uint8_t v___x_114_; 
v___x_112_ = lean_unsigned_to_nat(3u);
v___x_113_ = l_Lean_Syntax_getArg(v_v_67_, v___x_112_);
v___x_114_ = l_Lean_Syntax_isNone(v___x_113_);
if (v___x_114_ == 0)
{
uint8_t v___x_115_; 
lean_inc(v___x_113_);
v___x_115_ = l_Lean_Syntax_matchesNull(v___x_113_, v___x_108_);
if (v___x_115_ == 0)
{
lean_object* v___x_116_; lean_object* v___x_117_; 
lean_dec(v___x_113_);
lean_dec(v_metaTk_111_);
lean_dec(v___y_110_);
lean_dec(v_v_67_);
v___x_116_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8);
v___x_117_ = l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__1(v___x_116_);
v___y_71_ = v___x_117_;
goto v___jp_70_;
}
else
{
lean_object* v___x_118_; lean_object* v___x_119_; uint8_t v___x_120_; 
v___x_118_ = l_Lean_Syntax_getArg(v___x_113_, v___x_68_);
lean_dec(v___x_113_);
v___x_119_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__10));
lean_inc(v___x_118_);
v___x_120_ = l_Lean_Syntax_isOfKind(v___x_118_, v___x_119_);
if (v___x_120_ == 0)
{
lean_object* v___x_121_; lean_object* v___x_122_; 
lean_dec(v___x_118_);
lean_dec(v_metaTk_111_);
lean_dec(v___y_110_);
lean_dec(v_v_67_);
v___x_121_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8);
v___x_122_ = l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__1(v___x_121_);
v___y_71_ = v___x_122_;
goto v___jp_70_;
}
else
{
lean_object* v_allTk_123_; lean_object* v___x_124_; 
v_allTk_123_ = l_Lean_Syntax_getArg(v___x_118_, v___x_68_);
lean_dec(v___x_118_);
v___x_124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_124_, 0, v_allTk_123_);
v___y_96_ = v_metaTk_111_;
v___y_97_ = v___y_110_;
v_allTk_98_ = v___x_124_;
goto v___jp_95_;
}
}
}
else
{
lean_object* v___x_125_; 
lean_dec(v___x_113_);
v___x_125_ = lean_box(0);
v___y_96_ = v_metaTk_111_;
v___y_97_ = v___y_110_;
v_allTk_98_ = v___x_125_;
goto v___jp_95_;
}
}
v___jp_126_:
{
lean_object* v___x_128_; uint8_t v___x_129_; 
v___x_128_ = l_Lean_Syntax_getArg(v_v_67_, v___x_108_);
v___x_129_ = l_Lean_Syntax_isNone(v___x_128_);
if (v___x_129_ == 0)
{
uint8_t v___x_130_; 
lean_inc(v___x_128_);
v___x_130_ = l_Lean_Syntax_matchesNull(v___x_128_, v___x_108_);
if (v___x_130_ == 0)
{
lean_object* v___x_131_; lean_object* v___x_132_; 
lean_dec(v___x_128_);
lean_dec(v_publicTk_127_);
lean_dec(v_v_67_);
v___x_131_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8);
v___x_132_ = l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__1(v___x_131_);
v___y_71_ = v___x_132_;
goto v___jp_70_;
}
else
{
lean_object* v___x_133_; lean_object* v___x_134_; uint8_t v___x_135_; 
v___x_133_ = l_Lean_Syntax_getArg(v___x_128_, v___x_68_);
lean_dec(v___x_128_);
v___x_134_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__12));
lean_inc(v___x_133_);
v___x_135_ = l_Lean_Syntax_isOfKind(v___x_133_, v___x_134_);
if (v___x_135_ == 0)
{
lean_object* v___x_136_; lean_object* v___x_137_; 
lean_dec(v___x_133_);
lean_dec(v_publicTk_127_);
lean_dec(v_v_67_);
v___x_136_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8);
v___x_137_ = l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__1(v___x_136_);
v___y_71_ = v___x_137_;
goto v___jp_70_;
}
else
{
lean_object* v_metaTk_138_; lean_object* v___x_139_; 
v_metaTk_138_ = l_Lean_Syntax_getArg(v___x_133_, v___x_68_);
lean_dec(v___x_133_);
v___x_139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_139_, 0, v_metaTk_138_);
v___y_110_ = v_publicTk_127_;
v_metaTk_111_ = v___x_139_;
goto v___jp_109_;
}
}
}
else
{
lean_object* v___x_140_; 
lean_dec(v___x_128_);
v___x_140_ = lean_box(0);
v___y_110_ = v_publicTk_127_;
v_metaTk_111_ = v___x_140_;
goto v___jp_109_;
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
if (lean_obj_tag(v___y_80_) == 0)
{
uint8_t v___x_82_; lean_object* v___x_83_; 
v___x_82_ = 0;
v___x_83_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_83_, 0, v___y_77_);
lean_ctor_set_uint8(v___x_83_, sizeof(void*)*1, v___y_79_);
lean_ctor_set_uint8(v___x_83_, sizeof(void*)*1 + 1, v___y_81_);
lean_ctor_set_uint8(v___x_83_, sizeof(void*)*1 + 2, v___x_82_);
v___y_71_ = v___x_83_;
goto v___jp_70_;
}
else
{
lean_object* v___x_84_; 
lean_dec_ref_known(v___y_80_, 1);
v___x_84_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_84_, 0, v___y_77_);
lean_ctor_set_uint8(v___x_84_, sizeof(void*)*1, v___y_79_);
lean_ctor_set_uint8(v___x_84_, sizeof(void*)*1 + 1, v___y_81_);
lean_ctor_set_uint8(v___x_84_, sizeof(void*)*1 + 2, v___y_78_);
v___y_71_ = v___x_84_;
goto v___jp_70_;
}
}
v___jp_85_:
{
if (lean_obj_tag(v___y_89_) == 0)
{
if (lean_obj_tag(v_moduleTk_60_) == 0)
{
v___y_77_ = v___y_86_;
v___y_78_ = v___y_87_;
v___y_79_ = v___y_90_;
v___y_80_ = v___y_88_;
v___y_81_ = v___y_87_;
goto v___jp_76_;
}
else
{
uint8_t v___x_91_; 
v___x_91_ = 0;
v___y_77_ = v___y_86_;
v___y_78_ = v___y_87_;
v___y_79_ = v___y_90_;
v___y_80_ = v___y_88_;
v___y_81_ = v___x_91_;
goto v___jp_76_;
}
}
else
{
lean_dec_ref_known(v___y_89_, 1);
v___y_77_ = v___y_86_;
v___y_78_ = v___y_87_;
v___y_79_ = v___y_90_;
v___y_80_ = v___y_88_;
v___y_81_ = v___x_61_;
goto v___jp_76_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___boxed(lean_object* v_moduleTk_154_, lean_object* v___x_155_, lean_object* v_sz_156_, lean_object* v_i_157_, lean_object* v_bs_158_){
_start:
{
uint8_t v___x_1479__boxed_159_; size_t v_sz_boxed_160_; size_t v_i_boxed_161_; lean_object* v_res_162_; 
v___x_1479__boxed_159_ = lean_unbox(v___x_155_);
v_sz_boxed_160_ = lean_unbox_usize(v_sz_156_);
lean_dec(v_sz_156_);
v_i_boxed_161_ = lean_unbox_usize(v_i_157_);
lean_dec(v_i_157_);
v_res_162_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2(v_moduleTk_154_, v___x_1479__boxed_159_, v_sz_boxed_160_, v_i_boxed_161_, v_bs_158_);
lean_dec(v_moduleTk_154_);
return v_res_162_;
}
}
static lean_object* _init_l_Lean_Elab_HeaderSyntax_imports___closed__2(void){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_169_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__7));
v___x_170_ = lean_unsigned_to_nat(9u);
v___x_171_ = lean_unsigned_to_nat(41u);
v___x_172_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__6));
v___x_173_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__5));
v___x_174_ = l_mkPanicMessageWithDecl(v___x_173_, v___x_172_, v___x_171_, v___x_170_, v___x_169_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_HeaderSyntax_imports(lean_object* v_stx_192_, uint8_t v_includeInit_193_){
_start:
{
lean_object* v___x_194_; uint8_t v___x_195_; lean_object* v___y_197_; lean_object* v___y_198_; lean_object* v___y_199_; 
v___x_194_ = ((lean_object*)(l_Lean_Elab_HeaderSyntax_imports___closed__1));
lean_inc(v_stx_192_);
v___x_195_ = l_Lean_Syntax_isOfKind(v_stx_192_, v___x_194_);
if (v___x_195_ == 0)
{
lean_object* v___x_204_; lean_object* v___x_205_; 
lean_dec(v_stx_192_);
v___x_204_ = lean_obj_once(&l_Lean_Elab_HeaderSyntax_imports___closed__2, &l_Lean_Elab_HeaderSyntax_imports___closed__2_once, _init_l_Lean_Elab_HeaderSyntax_imports___closed__2);
v___x_205_ = l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__0(v___x_204_);
return v___x_205_;
}
else
{
lean_object* v___x_206_; lean_object* v___y_208_; lean_object* v___y_209_; lean_object* v___y_212_; lean_object* v_preludeTk_213_; lean_object* v_moduleTk_225_; lean_object* v___x_240_; uint8_t v___x_241_; 
v___x_206_ = lean_unsigned_to_nat(0u);
v___x_240_ = l_Lean_Syntax_getArg(v_stx_192_, v___x_206_);
v___x_241_ = l_Lean_Syntax_isNone(v___x_240_);
if (v___x_241_ == 0)
{
lean_object* v___x_242_; uint8_t v___x_243_; 
v___x_242_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_240_);
v___x_243_ = l_Lean_Syntax_matchesNull(v___x_240_, v___x_242_);
if (v___x_243_ == 0)
{
lean_object* v___x_244_; lean_object* v___x_245_; 
lean_dec(v___x_240_);
lean_dec(v_stx_192_);
v___x_244_ = lean_obj_once(&l_Lean_Elab_HeaderSyntax_imports___closed__2, &l_Lean_Elab_HeaderSyntax_imports___closed__2_once, _init_l_Lean_Elab_HeaderSyntax_imports___closed__2);
v___x_245_ = l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__0(v___x_244_);
return v___x_245_;
}
else
{
lean_object* v___x_246_; lean_object* v___x_247_; uint8_t v___x_248_; 
v___x_246_ = l_Lean_Syntax_getArg(v___x_240_, v___x_206_);
lean_dec(v___x_240_);
v___x_247_ = ((lean_object*)(l_Lean_Elab_HeaderSyntax_imports___closed__9));
lean_inc(v___x_246_);
v___x_248_ = l_Lean_Syntax_isOfKind(v___x_246_, v___x_247_);
if (v___x_248_ == 0)
{
lean_object* v___x_249_; lean_object* v___x_250_; 
lean_dec(v___x_246_);
lean_dec(v_stx_192_);
v___x_249_ = lean_obj_once(&l_Lean_Elab_HeaderSyntax_imports___closed__2, &l_Lean_Elab_HeaderSyntax_imports___closed__2_once, _init_l_Lean_Elab_HeaderSyntax_imports___closed__2);
v___x_250_ = l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__0(v___x_249_);
return v___x_250_;
}
else
{
lean_object* v_moduleTk_251_; lean_object* v___x_252_; 
v_moduleTk_251_ = l_Lean_Syntax_getArg(v___x_246_, v___x_206_);
lean_dec(v___x_246_);
v___x_252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_252_, 0, v_moduleTk_251_);
v_moduleTk_225_ = v___x_252_;
goto v___jp_224_;
}
}
}
else
{
lean_object* v___x_253_; 
lean_dec(v___x_240_);
v___x_253_ = lean_box(0);
v_moduleTk_225_ = v___x_253_;
goto v___jp_224_;
}
v___jp_207_:
{
lean_object* v___x_210_; 
v___x_210_ = ((lean_object*)(l_Lean_Elab_HeaderSyntax_imports___closed__3));
v___y_197_ = v___y_208_;
v___y_198_ = v___y_209_;
v___y_199_ = v___x_210_;
goto v___jp_196_;
}
v___jp_211_:
{
lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v_importsStx_216_; 
v___x_214_ = lean_unsigned_to_nat(2u);
v___x_215_ = l_Lean_Syntax_getArg(v_stx_192_, v___x_214_);
lean_dec(v_stx_192_);
v_importsStx_216_ = l_Lean_Syntax_getArgs(v___x_215_);
lean_dec(v___x_215_);
if (lean_obj_tag(v_preludeTk_213_) == 0)
{
if (v_includeInit_193_ == 0)
{
v___y_208_ = v___y_212_;
v___y_209_ = v_importsStx_216_;
goto v___jp_207_;
}
else
{
lean_object* v___x_217_; uint8_t v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_217_ = ((lean_object*)(l_Lean_Elab_HeaderSyntax_imports___closed__5));
v___x_218_ = 0;
v___x_219_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_219_, 0, v___x_217_);
lean_ctor_set_uint8(v___x_219_, sizeof(void*)*1, v___x_218_);
lean_ctor_set_uint8(v___x_219_, sizeof(void*)*1 + 1, v___x_195_);
lean_ctor_set_uint8(v___x_219_, sizeof(void*)*1 + 2, v___x_218_);
v___x_220_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_220_, 0, v___x_217_);
lean_ctor_set_uint8(v___x_220_, sizeof(void*)*1, v___x_218_);
lean_ctor_set_uint8(v___x_220_, sizeof(void*)*1 + 1, v___x_195_);
lean_ctor_set_uint8(v___x_220_, sizeof(void*)*1 + 2, v___x_195_);
v___x_221_ = lean_mk_empty_array_with_capacity(v___x_214_);
v___x_222_ = lean_array_push(v___x_221_, v___x_219_);
v___x_223_ = lean_array_push(v___x_222_, v___x_220_);
v___y_197_ = v___y_212_;
v___y_198_ = v_importsStx_216_;
v___y_199_ = v___x_223_;
goto v___jp_196_;
}
}
else
{
lean_dec_ref_known(v_preludeTk_213_, 1);
v___y_208_ = v___y_212_;
v___y_209_ = v_importsStx_216_;
goto v___jp_207_;
}
}
v___jp_224_:
{
lean_object* v___x_226_; lean_object* v___x_227_; uint8_t v___x_228_; 
v___x_226_ = lean_unsigned_to_nat(1u);
v___x_227_ = l_Lean_Syntax_getArg(v_stx_192_, v___x_226_);
v___x_228_ = l_Lean_Syntax_isNone(v___x_227_);
if (v___x_228_ == 0)
{
uint8_t v___x_229_; 
lean_inc(v___x_227_);
v___x_229_ = l_Lean_Syntax_matchesNull(v___x_227_, v___x_226_);
if (v___x_229_ == 0)
{
lean_object* v___x_230_; lean_object* v___x_231_; 
lean_dec(v___x_227_);
lean_dec(v_moduleTk_225_);
lean_dec(v_stx_192_);
v___x_230_ = lean_obj_once(&l_Lean_Elab_HeaderSyntax_imports___closed__2, &l_Lean_Elab_HeaderSyntax_imports___closed__2_once, _init_l_Lean_Elab_HeaderSyntax_imports___closed__2);
v___x_231_ = l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__0(v___x_230_);
return v___x_231_;
}
else
{
lean_object* v___x_232_; lean_object* v___x_233_; uint8_t v___x_234_; 
v___x_232_ = l_Lean_Syntax_getArg(v___x_227_, v___x_206_);
lean_dec(v___x_227_);
v___x_233_ = ((lean_object*)(l_Lean_Elab_HeaderSyntax_imports___closed__7));
lean_inc(v___x_232_);
v___x_234_ = l_Lean_Syntax_isOfKind(v___x_232_, v___x_233_);
if (v___x_234_ == 0)
{
lean_object* v___x_235_; lean_object* v___x_236_; 
lean_dec(v___x_232_);
lean_dec(v_moduleTk_225_);
lean_dec(v_stx_192_);
v___x_235_ = lean_obj_once(&l_Lean_Elab_HeaderSyntax_imports___closed__2, &l_Lean_Elab_HeaderSyntax_imports___closed__2_once, _init_l_Lean_Elab_HeaderSyntax_imports___closed__2);
v___x_236_ = l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__0(v___x_235_);
return v___x_236_;
}
else
{
lean_object* v_preludeTk_237_; lean_object* v___x_238_; 
v_preludeTk_237_ = l_Lean_Syntax_getArg(v___x_232_, v___x_206_);
lean_dec(v___x_232_);
v___x_238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_238_, 0, v_preludeTk_237_);
v___y_212_ = v_moduleTk_225_;
v_preludeTk_213_ = v___x_238_;
goto v___jp_211_;
}
}
}
else
{
lean_object* v___x_239_; 
lean_dec(v___x_227_);
v___x_239_ = lean_box(0);
v___y_212_ = v_moduleTk_225_;
v_preludeTk_213_ = v___x_239_;
goto v___jp_211_;
}
}
}
v___jp_196_:
{
size_t v_sz_200_; size_t v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v_sz_200_ = lean_array_size(v___y_198_);
v___x_201_ = ((size_t)0ULL);
v___x_202_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2(v___y_197_, v___x_195_, v_sz_200_, v___x_201_, v___y_198_);
lean_dec(v___y_197_);
v___x_203_ = l_Array_append___redArg(v___y_199_, v___x_202_);
lean_dec_ref(v___x_202_);
return v___x_203_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_HeaderSyntax_imports___boxed(lean_object* v_stx_254_, lean_object* v_includeInit_255_){
_start:
{
uint8_t v_includeInit_boxed_256_; lean_object* v_res_257_; 
v_includeInit_boxed_256_ = lean_unbox(v_includeInit_255_);
v_res_257_ = l_Lean_Elab_HeaderSyntax_imports(v_stx_254_, v_includeInit_boxed_256_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_HeaderSyntax_toModuleHeader(lean_object* v_stx_258_){
_start:
{
uint8_t v___x_259_; lean_object* v___x_260_; uint8_t v___x_261_; lean_object* v___x_262_; 
v___x_259_ = 1;
lean_inc(v_stx_258_);
v___x_260_ = l_Lean_Elab_HeaderSyntax_imports(v_stx_258_, v___x_259_);
v___x_261_ = l_Lean_Elab_HeaderSyntax_isModule(v_stx_258_);
lean_dec(v_stx_258_);
v___x_262_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_262_, 0, v___x_260_);
lean_ctor_set_uint8(v___x_262_, sizeof(void*)*1, v___x_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_headerToImports(lean_object* v_stx_263_, uint8_t v_includeInit_264_){
_start:
{
lean_object* v___x_265_; 
v___x_265_ = l_Lean_Elab_HeaderSyntax_imports(v_stx_263_, v_includeInit_264_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_headerToImports___boxed(lean_object* v_stx_266_, lean_object* v_includeInit_267_){
_start:
{
uint8_t v_includeInit_boxed_268_; lean_object* v_res_269_; 
v_includeInit_boxed_268_ = lean_unbox(v_includeInit_267_);
v_res_269_ = l_Lean_Elab_headerToImports(v_stx_266_, v_includeInit_boxed_268_);
return v_res_269_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_checkDeprecatedImports_spec__0(lean_object* v_opts_270_, lean_object* v_opt_271_){
_start:
{
lean_object* v_name_272_; lean_object* v_defValue_273_; lean_object* v_map_274_; lean_object* v___x_275_; 
v_name_272_ = lean_ctor_get(v_opt_271_, 0);
v_defValue_273_ = lean_ctor_get(v_opt_271_, 1);
v_map_274_ = lean_ctor_get(v_opts_270_, 0);
v___x_275_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_274_, v_name_272_);
if (lean_obj_tag(v___x_275_) == 0)
{
uint8_t v___x_276_; 
v___x_276_ = lean_unbox(v_defValue_273_);
return v___x_276_;
}
else
{
lean_object* v_val_277_; 
v_val_277_ = lean_ctor_get(v___x_275_, 0);
lean_inc(v_val_277_);
lean_dec_ref_known(v___x_275_, 1);
if (lean_obj_tag(v_val_277_) == 1)
{
uint8_t v_v_278_; 
v_v_278_ = lean_ctor_get_uint8(v_val_277_, 0);
lean_dec_ref_known(v_val_277_, 0);
return v_v_278_;
}
else
{
uint8_t v___x_279_; 
lean_dec(v_val_277_);
v___x_279_ = lean_unbox(v_defValue_273_);
return v___x_279_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_checkDeprecatedImports_spec__0___boxed(lean_object* v_opts_280_, lean_object* v_opt_281_){
_start:
{
uint8_t v_res_282_; lean_object* v_r_283_; 
v_res_282_ = l_Lean_Option_get___at___00Lean_Elab_checkDeprecatedImports_spec__0(v_opts_280_, v_opt_281_);
lean_dec_ref(v_opt_281_);
lean_dec_ref(v_opts_280_);
v_r_283_ = lean_box(v_res_282_);
return v_r_283_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_spec__2___redArg(lean_object* v_s_284_, lean_object* v_a_285_, uint8_t v_b_286_){
_start:
{
uint8_t v___x_287_; 
v___x_287_ = 0;
switch(lean_obj_tag(v_a_285_))
{
case 0:
{
lean_object* v_pos_288_; lean_object* v_startInclusive_289_; lean_object* v_endExclusive_290_; lean_object* v___x_291_; uint8_t v_decide_292_; 
v_pos_288_ = lean_ctor_get(v_a_285_, 0);
lean_inc(v_pos_288_);
lean_dec_ref_known(v_a_285_, 1);
v_startInclusive_289_ = lean_ctor_get(v_s_284_, 1);
v_endExclusive_290_ = lean_ctor_get(v_s_284_, 2);
v___x_291_ = lean_nat_sub(v_endExclusive_290_, v_startInclusive_289_);
v_decide_292_ = lean_nat_dec_eq(v_pos_288_, v___x_291_);
lean_dec(v___x_291_);
lean_dec(v_pos_288_);
if (v_decide_292_ == 0)
{
uint8_t v___x_293_; 
v___x_293_ = 1;
return v___x_293_;
}
else
{
return v_decide_292_;
}
}
case 1:
{
lean_object* v_pos_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_307_; 
v_pos_294_ = lean_ctor_get(v_a_285_, 0);
v_isSharedCheck_307_ = !lean_is_exclusive(v_a_285_);
if (v_isSharedCheck_307_ == 0)
{
v___x_296_ = v_a_285_;
v_isShared_297_ = v_isSharedCheck_307_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_pos_294_);
lean_dec(v_a_285_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_307_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v_str_298_; lean_object* v_startInclusive_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_304_; 
v_str_298_ = lean_ctor_get(v_s_284_, 0);
v_startInclusive_299_ = lean_ctor_get(v_s_284_, 1);
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
v_a_285_ = v___x_304_;
v_b_286_ = v___x_287_;
goto _start;
}
}
}
case 2:
{
lean_object* v_needle_308_; lean_object* v_table_309_; lean_object* v_stackPos_310_; lean_object* v_needlePos_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_366_; 
v_needle_308_ = lean_ctor_get(v_a_285_, 0);
v_table_309_ = lean_ctor_get(v_a_285_, 1);
v_stackPos_310_ = lean_ctor_get(v_a_285_, 2);
v_needlePos_311_ = lean_ctor_get(v_a_285_, 3);
v_isSharedCheck_366_ = !lean_is_exclusive(v_a_285_);
if (v_isSharedCheck_366_ == 0)
{
v___x_313_ = v_a_285_;
v_isShared_314_ = v_isSharedCheck_366_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_needlePos_311_);
lean_inc(v_stackPos_310_);
lean_inc(v_table_309_);
lean_inc(v_needle_308_);
lean_dec(v_a_285_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_366_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v_str_315_; lean_object* v_startInclusive_316_; lean_object* v_endExclusive_317_; lean_object* v_str_318_; lean_object* v_startInclusive_319_; lean_object* v_endExclusive_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; uint8_t v___x_325_; 
v_str_315_ = lean_ctor_get(v_needle_308_, 0);
v_startInclusive_316_ = lean_ctor_get(v_needle_308_, 1);
v_endExclusive_317_ = lean_ctor_get(v_needle_308_, 2);
v_str_318_ = lean_ctor_get(v_s_284_, 0);
v_startInclusive_319_ = lean_ctor_get(v_s_284_, 1);
v_endExclusive_320_ = lean_ctor_get(v_s_284_, 2);
v___x_321_ = lean_nat_sub(v_stackPos_310_, v_needlePos_311_);
v___x_322_ = lean_nat_sub(v_endExclusive_317_, v_startInclusive_316_);
v___x_323_ = lean_nat_add(v___x_321_, v___x_322_);
v___x_324_ = lean_nat_sub(v_endExclusive_320_, v_startInclusive_319_);
v___x_325_ = lean_nat_dec_le(v___x_323_, v___x_324_);
lean_dec(v___x_323_);
if (v___x_325_ == 0)
{
lean_object* v___x_326_; lean_object* v___x_327_; uint8_t v___x_328_; 
lean_dec(v___x_322_);
lean_del_object(v___x_313_);
lean_dec(v_needlePos_311_);
lean_dec(v_stackPos_310_);
lean_dec_ref(v_table_309_);
lean_dec_ref(v_needle_308_);
v___x_326_ = lean_unsigned_to_nat(1u);
v___x_327_ = lean_nat_add(v___x_321_, v___x_326_);
lean_dec(v___x_321_);
v___x_328_ = lean_nat_dec_le(v___x_327_, v___x_324_);
lean_dec(v___x_324_);
lean_dec(v___x_327_);
if (v___x_328_ == 0)
{
return v_b_286_;
}
else
{
lean_object* v___x_329_; 
v___x_329_ = lean_box(3);
v_a_285_ = v___x_329_;
v_b_286_ = v___x_287_;
goto _start;
}
}
else
{
lean_object* v___x_331_; uint8_t v_stackByte_332_; lean_object* v___x_333_; uint8_t v_patByte_334_; uint8_t v___x_335_; 
lean_dec(v___x_324_);
lean_dec(v___x_321_);
v___x_331_ = lean_nat_add(v_startInclusive_319_, v_stackPos_310_);
v_stackByte_332_ = lean_string_get_byte_fast(v_str_318_, v___x_331_);
v___x_333_ = lean_nat_add(v_startInclusive_316_, v_needlePos_311_);
v_patByte_334_ = lean_string_get_byte_fast(v_str_315_, v___x_333_);
v___x_335_ = lean_uint8_dec_eq(v_stackByte_332_, v_patByte_334_);
if (v___x_335_ == 0)
{
lean_object* v___x_336_; uint8_t v_decide_337_; 
lean_dec(v___x_322_);
v___x_336_ = lean_unsigned_to_nat(0u);
v_decide_337_ = lean_nat_dec_eq(v_needlePos_311_, v___x_336_);
if (v_decide_337_ == 0)
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v_newNeedlePos_340_; uint8_t v___x_341_; 
v___x_338_ = lean_unsigned_to_nat(1u);
v___x_339_ = lean_nat_sub(v_needlePos_311_, v___x_338_);
lean_dec(v_needlePos_311_);
v_newNeedlePos_340_ = lean_array_fget_borrowed(v_table_309_, v___x_339_);
lean_dec(v___x_339_);
v___x_341_ = lean_nat_dec_eq(v_newNeedlePos_340_, v___x_336_);
if (v___x_341_ == 0)
{
lean_object* v___x_343_; 
lean_inc(v_newNeedlePos_340_);
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 3, v_newNeedlePos_340_);
v___x_343_ = v___x_313_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_needle_308_);
lean_ctor_set(v_reuseFailAlloc_345_, 1, v_table_309_);
lean_ctor_set(v_reuseFailAlloc_345_, 2, v_stackPos_310_);
lean_ctor_set(v_reuseFailAlloc_345_, 3, v_newNeedlePos_340_);
v___x_343_ = v_reuseFailAlloc_345_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
v_a_285_ = v___x_343_;
v_b_286_ = v___x_287_;
goto _start;
}
}
else
{
lean_object* v_nextStackPos_346_; lean_object* v___x_348_; 
v_nextStackPos_346_ = l_String_Slice_posGE___redArg(v_s_284_, v_stackPos_310_);
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 3, v___x_336_);
lean_ctor_set(v___x_313_, 2, v_nextStackPos_346_);
v___x_348_ = v___x_313_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_needle_308_);
lean_ctor_set(v_reuseFailAlloc_350_, 1, v_table_309_);
lean_ctor_set(v_reuseFailAlloc_350_, 2, v_nextStackPos_346_);
lean_ctor_set(v_reuseFailAlloc_350_, 3, v___x_336_);
v___x_348_ = v_reuseFailAlloc_350_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
v_a_285_ = v___x_348_;
v_b_286_ = v___x_287_;
goto _start;
}
}
}
else
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v_nextStackPos_353_; lean_object* v___x_355_; 
lean_dec(v_needlePos_311_);
v___x_351_ = lean_unsigned_to_nat(1u);
v___x_352_ = lean_nat_add(v_stackPos_310_, v___x_351_);
lean_dec(v_stackPos_310_);
v_nextStackPos_353_ = l_String_Slice_posGE___redArg(v_s_284_, v___x_352_);
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 3, v___x_336_);
lean_ctor_set(v___x_313_, 2, v_nextStackPos_353_);
v___x_355_ = v___x_313_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_needle_308_);
lean_ctor_set(v_reuseFailAlloc_357_, 1, v_table_309_);
lean_ctor_set(v_reuseFailAlloc_357_, 2, v_nextStackPos_353_);
lean_ctor_set(v_reuseFailAlloc_357_, 3, v___x_336_);
v___x_355_ = v_reuseFailAlloc_357_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
v_a_285_ = v___x_355_;
v_b_286_ = v___x_287_;
goto _start;
}
}
}
else
{
lean_object* v___x_358_; lean_object* v_nextNeedlePos_359_; uint8_t v_decide_360_; 
v___x_358_ = lean_unsigned_to_nat(1u);
v_nextNeedlePos_359_ = lean_nat_add(v_needlePos_311_, v___x_358_);
lean_dec(v_needlePos_311_);
v_decide_360_ = lean_nat_dec_eq(v_nextNeedlePos_359_, v___x_322_);
lean_dec(v___x_322_);
if (v_decide_360_ == 0)
{
lean_object* v_nextStackPos_361_; lean_object* v___x_363_; 
v_nextStackPos_361_ = lean_nat_add(v_stackPos_310_, v___x_358_);
lean_dec(v_stackPos_310_);
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 3, v_nextNeedlePos_359_);
lean_ctor_set(v___x_313_, 2, v_nextStackPos_361_);
v___x_363_ = v___x_313_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_needle_308_);
lean_ctor_set(v_reuseFailAlloc_365_, 1, v_table_309_);
lean_ctor_set(v_reuseFailAlloc_365_, 2, v_nextStackPos_361_);
lean_ctor_set(v_reuseFailAlloc_365_, 3, v_nextNeedlePos_359_);
v___x_363_ = v_reuseFailAlloc_365_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
v_a_285_ = v___x_363_;
goto _start;
}
}
else
{
lean_dec(v_nextNeedlePos_359_);
lean_del_object(v___x_313_);
lean_dec(v_stackPos_310_);
lean_dec_ref(v_table_309_);
lean_dec_ref(v_needle_308_);
return v_decide_360_;
}
}
}
}
}
default: 
{
return v_b_286_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_spec__2___redArg___boxed(lean_object* v_s_367_, lean_object* v_a_368_, lean_object* v_b_369_){
_start:
{
uint8_t v_b_boxed_370_; uint8_t v_res_371_; lean_object* v_r_372_; 
v_b_boxed_370_ = lean_unbox(v_b_369_);
v_res_371_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_spec__2___redArg(v_s_367_, v_a_368_, v_b_boxed_370_);
lean_dec_ref(v_s_367_);
v_r_372_ = lean_box(v_res_371_);
return v_r_372_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__2(void){
_start:
{
lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_378_ = ((lean_object*)(l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__1));
v___x_379_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_378_);
return v___x_379_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__3(void){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_380_ = lean_unsigned_to_nat(0u);
v___x_381_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__2, &l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__2_once, _init_l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__2);
v___x_382_ = ((lean_object*)(l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__1));
v___x_383_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_383_, 0, v___x_382_);
lean_ctor_set(v___x_383_, 1, v___x_381_);
lean_ctor_set(v___x_383_, 2, v___x_380_);
lean_ctor_set(v___x_383_, 3, v___x_380_);
return v___x_383_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2(lean_object* v_s_384_){
_start:
{
lean_object* v___x_385_; uint8_t v___x_386_; uint8_t v___x_387_; 
v___x_385_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__3, &l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__3_once, _init_l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__3);
v___x_386_ = 0;
v___x_387_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_spec__2___redArg(v_s_384_, v___x_385_, v___x_386_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___boxed(lean_object* v_s_388_){
_start:
{
uint8_t v_res_389_; lean_object* v_r_390_; 
v_res_389_ = l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2(v_s_388_);
lean_dec_ref(v_s_388_);
v_r_390_ = lean_box(v_res_389_);
return v_r_390_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkDeprecatedImports_spec__3(lean_object* v_as_391_, size_t v_sz_392_, size_t v_i_393_, lean_object* v_b_394_){
_start:
{
lean_object* v_a_396_; uint8_t v___x_400_; 
v___x_400_ = lean_usize_dec_lt(v_i_393_, v_sz_392_);
if (v___x_400_ == 0)
{
return v_b_394_;
}
else
{
lean_object* v_fst_401_; lean_object* v_snd_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_477_; 
v_fst_401_ = lean_ctor_get(v_b_394_, 0);
v_snd_402_ = lean_ctor_get(v_b_394_, 1);
v_isSharedCheck_477_ = !lean_is_exclusive(v_b_394_);
if (v_isSharedCheck_477_ == 0)
{
v___x_404_ = v_b_394_;
v_isShared_405_ = v_isSharedCheck_477_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_snd_402_);
lean_inc(v_fst_401_);
lean_dec(v_b_394_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_477_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_406_; lean_object* v_a_407_; lean_object* v___y_409_; lean_object* v_ignoreDeprecatedImports_410_; uint8_t v___x_422_; 
v___x_406_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__4));
v_a_407_ = lean_array_uget_borrowed(v_as_391_, v_i_393_);
lean_inc(v_a_407_);
v___x_422_ = l_Lean_Syntax_isOfKind(v_a_407_, v___x_406_);
if (v___x_422_ == 0)
{
lean_object* v___x_423_; 
lean_del_object(v___x_404_);
v___x_423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_423_, 0, v_fst_401_);
lean_ctor_set(v___x_423_, 1, v_snd_402_);
v_a_396_ = v___x_423_;
goto v___jp_395_;
}
else
{
lean_object* v___x_424_; lean_object* v___x_449_; lean_object* v___x_469_; uint8_t v___x_470_; 
v___x_424_ = lean_unsigned_to_nat(0u);
v___x_449_ = lean_unsigned_to_nat(1u);
v___x_469_ = l_Lean_Syntax_getArg(v_a_407_, v___x_424_);
v___x_470_ = l_Lean_Syntax_isNone(v___x_469_);
if (v___x_470_ == 0)
{
uint8_t v___x_471_; 
lean_inc(v___x_469_);
v___x_471_ = l_Lean_Syntax_matchesNull(v___x_469_, v___x_449_);
if (v___x_471_ == 0)
{
lean_object* v___x_472_; 
lean_dec(v___x_469_);
lean_del_object(v___x_404_);
v___x_472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_472_, 0, v_fst_401_);
lean_ctor_set(v___x_472_, 1, v_snd_402_);
v_a_396_ = v___x_472_;
goto v___jp_395_;
}
else
{
lean_object* v___x_473_; lean_object* v___x_474_; uint8_t v___x_475_; 
v___x_473_ = l_Lean_Syntax_getArg(v___x_469_, v___x_424_);
lean_dec(v___x_469_);
v___x_474_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__14));
v___x_475_ = l_Lean_Syntax_isOfKind(v___x_473_, v___x_474_);
if (v___x_475_ == 0)
{
lean_object* v___x_476_; 
lean_del_object(v___x_404_);
v___x_476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_476_, 0, v_fst_401_);
lean_ctor_set(v___x_476_, 1, v_snd_402_);
v_a_396_ = v___x_476_;
goto v___jp_395_;
}
else
{
goto v___jp_460_;
}
}
}
else
{
lean_dec(v___x_469_);
goto v___jp_460_;
}
v___jp_425_:
{
lean_object* v___x_426_; lean_object* v___x_427_; uint8_t v___x_428_; 
v___x_426_ = lean_unsigned_to_nat(5u);
v___x_427_ = l_Lean_Syntax_getArg(v_a_407_, v___x_426_);
v___x_428_ = l_Lean_Syntax_matchesNull(v___x_427_, v___x_424_);
if (v___x_428_ == 0)
{
lean_object* v___x_429_; 
lean_del_object(v___x_404_);
v___x_429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_429_, 0, v_fst_401_);
lean_ctor_set(v___x_429_, 1, v_snd_402_);
v_a_396_ = v___x_429_;
goto v___jp_395_;
}
else
{
lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_430_ = lean_unsigned_to_nat(4u);
v___x_431_ = l_Lean_Syntax_getArg(v_a_407_, v___x_430_);
v___x_432_ = l_Lean_Syntax_getTrailing_x3f(v_a_407_);
if (lean_obj_tag(v___x_432_) == 0)
{
v___y_409_ = v___x_431_;
v_ignoreDeprecatedImports_410_ = v_fst_401_;
goto v___jp_408_;
}
else
{
lean_object* v_val_433_; lean_object* v_str_434_; lean_object* v_startPos_435_; lean_object* v_stopPos_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_448_; 
v_val_433_ = lean_ctor_get(v___x_432_, 0);
lean_inc(v_val_433_);
lean_dec_ref_known(v___x_432_, 1);
v_str_434_ = lean_ctor_get(v_val_433_, 0);
v_startPos_435_ = lean_ctor_get(v_val_433_, 1);
v_stopPos_436_ = lean_ctor_get(v_val_433_, 2);
v_isSharedCheck_448_ = !lean_is_exclusive(v_val_433_);
if (v_isSharedCheck_448_ == 0)
{
v___x_438_ = v_val_433_;
v_isShared_439_ = v_isSharedCheck_448_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_stopPos_436_);
lean_inc(v_startPos_435_);
lean_inc(v_str_434_);
lean_dec(v_val_433_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_448_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_443_; 
v___x_440_ = lean_string_utf8_extract(v_str_434_, v_startPos_435_, v_stopPos_436_);
lean_dec(v_stopPos_436_);
lean_dec(v_startPos_435_);
lean_dec_ref(v_str_434_);
v___x_441_ = lean_string_utf8_byte_size(v___x_440_);
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 2, v___x_441_);
lean_ctor_set(v___x_438_, 1, v___x_424_);
lean_ctor_set(v___x_438_, 0, v___x_440_);
v___x_443_ = v___x_438_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v___x_440_);
lean_ctor_set(v_reuseFailAlloc_447_, 1, v___x_424_);
lean_ctor_set(v_reuseFailAlloc_447_, 2, v___x_441_);
v___x_443_ = v_reuseFailAlloc_447_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
uint8_t v___x_444_; 
v___x_444_ = l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2(v___x_443_);
lean_dec_ref(v___x_443_);
if (v___x_444_ == 0)
{
v___y_409_ = v___x_431_;
v_ignoreDeprecatedImports_410_ = v_fst_401_;
goto v___jp_408_;
}
else
{
lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_445_ = l_Lean_TSyntax_getId(v___x_431_);
v___x_446_ = l_Lean_NameSet_insert(v_fst_401_, v___x_445_);
v___y_409_ = v___x_431_;
v_ignoreDeprecatedImports_410_ = v___x_446_;
goto v___jp_408_;
}
}
}
}
}
}
v___jp_450_:
{
lean_object* v___x_451_; lean_object* v___x_452_; uint8_t v___x_453_; 
v___x_451_ = lean_unsigned_to_nat(3u);
v___x_452_ = l_Lean_Syntax_getArg(v_a_407_, v___x_451_);
v___x_453_ = l_Lean_Syntax_isNone(v___x_452_);
if (v___x_453_ == 0)
{
uint8_t v___x_454_; 
lean_inc(v___x_452_);
v___x_454_ = l_Lean_Syntax_matchesNull(v___x_452_, v___x_449_);
if (v___x_454_ == 0)
{
lean_object* v___x_455_; 
lean_dec(v___x_452_);
lean_del_object(v___x_404_);
v___x_455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_455_, 0, v_fst_401_);
lean_ctor_set(v___x_455_, 1, v_snd_402_);
v_a_396_ = v___x_455_;
goto v___jp_395_;
}
else
{
lean_object* v___x_456_; lean_object* v___x_457_; uint8_t v___x_458_; 
v___x_456_ = l_Lean_Syntax_getArg(v___x_452_, v___x_424_);
lean_dec(v___x_452_);
v___x_457_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__10));
v___x_458_ = l_Lean_Syntax_isOfKind(v___x_456_, v___x_457_);
if (v___x_458_ == 0)
{
lean_object* v___x_459_; 
lean_del_object(v___x_404_);
v___x_459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_459_, 0, v_fst_401_);
lean_ctor_set(v___x_459_, 1, v_snd_402_);
v_a_396_ = v___x_459_;
goto v___jp_395_;
}
else
{
goto v___jp_425_;
}
}
}
else
{
lean_dec(v___x_452_);
goto v___jp_425_;
}
}
v___jp_460_:
{
lean_object* v___x_461_; uint8_t v___x_462_; 
v___x_461_ = l_Lean_Syntax_getArg(v_a_407_, v___x_449_);
v___x_462_ = l_Lean_Syntax_isNone(v___x_461_);
if (v___x_462_ == 0)
{
uint8_t v___x_463_; 
lean_inc(v___x_461_);
v___x_463_ = l_Lean_Syntax_matchesNull(v___x_461_, v___x_449_);
if (v___x_463_ == 0)
{
lean_object* v___x_464_; 
lean_dec(v___x_461_);
lean_del_object(v___x_404_);
v___x_464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_464_, 0, v_fst_401_);
lean_ctor_set(v___x_464_, 1, v_snd_402_);
v_a_396_ = v___x_464_;
goto v___jp_395_;
}
else
{
lean_object* v___x_465_; lean_object* v___x_466_; uint8_t v___x_467_; 
v___x_465_ = l_Lean_Syntax_getArg(v___x_461_, v___x_424_);
lean_dec(v___x_461_);
v___x_466_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__12));
v___x_467_ = l_Lean_Syntax_isOfKind(v___x_465_, v___x_466_);
if (v___x_467_ == 0)
{
lean_object* v___x_468_; 
lean_del_object(v___x_404_);
v___x_468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_468_, 0, v_fst_401_);
lean_ctor_set(v___x_468_, 1, v_snd_402_);
v_a_396_ = v___x_468_;
goto v___jp_395_;
}
else
{
goto v___jp_450_;
}
}
}
else
{
lean_dec(v___x_461_);
goto v___jp_450_;
}
}
}
v___jp_408_:
{
uint8_t v___x_411_; lean_object* v___x_412_; 
v___x_411_ = 0;
v___x_412_ = l_Lean_Syntax_getPos_x3f(v_a_407_, v___x_411_);
if (lean_obj_tag(v___x_412_) == 1)
{
lean_object* v_val_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_417_; 
v_val_413_ = lean_ctor_get(v___x_412_, 0);
lean_inc(v_val_413_);
lean_dec_ref_known(v___x_412_, 1);
v___x_414_ = l_Lean_TSyntax_getId(v___y_409_);
lean_dec(v___y_409_);
v___x_415_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_414_, v_val_413_, v_snd_402_);
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 1, v___x_415_);
lean_ctor_set(v___x_404_, 0, v_ignoreDeprecatedImports_410_);
v___x_417_ = v___x_404_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_ignoreDeprecatedImports_410_);
lean_ctor_set(v_reuseFailAlloc_418_, 1, v___x_415_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
v_a_396_ = v___x_417_;
goto v___jp_395_;
}
}
else
{
lean_object* v___x_420_; 
lean_dec(v___x_412_);
lean_dec(v___y_409_);
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 0, v_ignoreDeprecatedImports_410_);
v___x_420_ = v___x_404_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_ignoreDeprecatedImports_410_);
lean_ctor_set(v_reuseFailAlloc_421_, 1, v_snd_402_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
v_a_396_ = v___x_420_;
goto v___jp_395_;
}
}
}
}
}
v___jp_395_:
{
size_t v___x_397_; size_t v___x_398_; 
v___x_397_ = ((size_t)1ULL);
v___x_398_ = lean_usize_add(v_i_393_, v___x_397_);
v_i_393_ = v___x_398_;
v_b_394_ = v_a_396_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkDeprecatedImports_spec__3___boxed(lean_object* v_as_478_, lean_object* v_sz_479_, lean_object* v_i_480_, lean_object* v_b_481_){
_start:
{
size_t v_sz_boxed_482_; size_t v_i_boxed_483_; lean_object* v_res_484_; 
v_sz_boxed_482_ = lean_unbox_usize(v_sz_479_);
lean_dec(v_sz_479_);
v_i_boxed_483_ = lean_unbox_usize(v_i_480_);
lean_dec(v_i_480_);
v_res_484_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkDeprecatedImports_spec__3(v_as_478_, v_sz_boxed_482_, v_i_boxed_483_, v_b_481_);
lean_dec_ref(v_as_478_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4_spec__5(lean_object* v_o_488_, lean_object* v_k_489_, uint8_t v_v_490_){
_start:
{
lean_object* v_map_491_; uint8_t v_hasTrace_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_506_; 
v_map_491_ = lean_ctor_get(v_o_488_, 0);
v_hasTrace_492_ = lean_ctor_get_uint8(v_o_488_, sizeof(void*)*1);
v_isSharedCheck_506_ = !lean_is_exclusive(v_o_488_);
if (v_isSharedCheck_506_ == 0)
{
v___x_494_ = v_o_488_;
v_isShared_495_ = v_isSharedCheck_506_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_map_491_);
lean_dec(v_o_488_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_506_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_496_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_496_, 0, v_v_490_);
lean_inc(v_k_489_);
v___x_497_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_489_, v___x_496_, v_map_491_);
if (v_hasTrace_492_ == 0)
{
lean_object* v___x_498_; uint8_t v___x_499_; lean_object* v___x_501_; 
v___x_498_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4_spec__5___closed__1));
v___x_499_ = l_Lean_Name_isPrefixOf(v___x_498_, v_k_489_);
lean_dec(v_k_489_);
if (v_isShared_495_ == 0)
{
lean_ctor_set(v___x_494_, 0, v___x_497_);
v___x_501_ = v___x_494_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v___x_497_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
lean_ctor_set_uint8(v___x_501_, sizeof(void*)*1, v___x_499_);
return v___x_501_;
}
}
else
{
lean_object* v___x_504_; 
lean_dec(v_k_489_);
if (v_isShared_495_ == 0)
{
lean_ctor_set(v___x_494_, 0, v___x_497_);
v___x_504_ = v___x_494_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v___x_497_);
lean_ctor_set_uint8(v_reuseFailAlloc_505_, sizeof(void*)*1, v_hasTrace_492_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4_spec__5___boxed(lean_object* v_o_507_, lean_object* v_k_508_, lean_object* v_v_509_){
_start:
{
uint8_t v_v_boxed_510_; lean_object* v_res_511_; 
v_v_boxed_510_ = lean_unbox(v_v_509_);
v_res_511_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4_spec__5(v_o_507_, v_k_508_, v_v_boxed_510_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4(lean_object* v_opts_512_, lean_object* v_opt_513_, uint8_t v_val_514_){
_start:
{
lean_object* v_name_515_; lean_object* v___x_516_; 
v_name_515_ = lean_ctor_get(v_opt_513_, 0);
lean_inc(v_name_515_);
lean_dec_ref(v_opt_513_);
v___x_516_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4_spec__5(v_opts_512_, v_name_515_, v_val_514_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4___boxed(lean_object* v_opts_517_, lean_object* v_opt_518_, lean_object* v_val_519_){
_start:
{
uint8_t v_val_boxed_520_; lean_object* v_res_521_; 
v_val_boxed_520_ = lean_unbox(v_val_519_);
v_res_521_ = l_Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4(v_opts_517_, v_opt_518_, v_val_boxed_520_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1(lean_object* v_ignoreDeprecatedImports_527_, lean_object* v_env_528_, lean_object* v_inputCtx_529_, lean_object* v_importPositions_530_, lean_object* v_startPos_531_, lean_object* v_as_532_, size_t v_i_533_, size_t v_stop_534_, lean_object* v_b_535_){
_start:
{
lean_object* v___y_537_; uint8_t v___x_541_; 
v___x_541_ = lean_usize_dec_eq(v_i_533_, v_stop_534_);
if (v___x_541_ == 0)
{
lean_object* v___x_542_; lean_object* v_module_543_; uint8_t v___x_544_; 
v___x_542_ = lean_array_uget_borrowed(v_as_532_, v_i_533_);
v_module_543_ = lean_ctor_get(v___x_542_, 0);
v___x_544_ = l_Lean_NameSet_contains(v_ignoreDeprecatedImports_527_, v_module_543_);
if (v___x_544_ == 0)
{
lean_object* v___x_545_; 
v___x_545_ = l_Lean_Environment_getModuleIdx_x3f(v_env_528_, v_module_543_);
if (lean_obj_tag(v___x_545_) == 0)
{
v___y_537_ = v_b_535_;
goto v___jp_536_;
}
else
{
lean_object* v_val_546_; lean_object* v___x_547_; 
v_val_546_ = lean_ctor_get(v___x_545_, 0);
lean_inc(v_val_546_);
lean_dec_ref_known(v___x_545_, 1);
v___x_547_ = l_Lean_Environment_getDeprecatedModuleByIdx_x3f(v_env_528_, v_val_546_);
if (lean_obj_tag(v___x_547_) == 0)
{
lean_dec(v_val_546_);
v___y_537_ = v_b_535_;
goto v___jp_536_;
}
else
{
lean_object* v_val_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_571_; 
v_val_548_ = lean_ctor_get(v___x_547_, 0);
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_547_);
if (v_isSharedCheck_571_ == 0)
{
v___x_550_ = v___x_547_;
v_isShared_551_ = v_isSharedCheck_571_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_val_548_);
lean_dec(v___x_547_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_571_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___y_553_; lean_object* v___x_569_; 
v___x_569_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_importPositions_530_, v_module_543_);
if (lean_obj_tag(v___x_569_) == 0)
{
lean_inc(v_startPos_531_);
v___y_553_ = v_startPos_531_;
goto v___jp_552_;
}
else
{
lean_object* v_val_570_; 
v_val_570_ = lean_ctor_get(v___x_569_, 0);
lean_inc(v_val_570_);
lean_dec_ref_known(v___x_569_, 1);
v___y_553_ = v_val_570_;
goto v___jp_552_;
}
v___jp_552_:
{
lean_object* v_fileName_554_; lean_object* v_fileMap_555_; lean_object* v___x_556_; lean_object* v___x_557_; uint8_t v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_563_; 
v_fileName_554_ = lean_ctor_get(v_inputCtx_529_, 1);
v_fileMap_555_ = lean_ctor_get(v_inputCtx_529_, 2);
lean_inc_ref(v_fileMap_555_);
v___x_556_ = l_Lean_FileMap_toPosition(v_fileMap_555_, v___y_553_);
lean_dec(v___y_553_);
v___x_557_ = lean_box(0);
v___x_558_ = 1;
v___x_559_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___closed__0));
v___x_560_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___closed__2));
lean_inc(v_module_543_);
v___x_561_ = l_Lean_formatDeprecatedModuleWarning(v_env_528_, v_val_546_, v_module_543_, v_val_548_);
lean_dec(v_val_546_);
if (v_isShared_551_ == 0)
{
lean_ctor_set_tag(v___x_550_, 3);
lean_ctor_set(v___x_550_, 0, v___x_561_);
v___x_563_ = v___x_550_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v___x_561_);
v___x_563_ = v_reuseFailAlloc_568_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_564_ = l_Lean_MessageData_ofFormat(v___x_563_);
v___x_565_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_565_, 0, v___x_560_);
lean_ctor_set(v___x_565_, 1, v___x_564_);
lean_inc_ref(v_fileName_554_);
v___x_566_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_566_, 0, v_fileName_554_);
lean_ctor_set(v___x_566_, 1, v___x_556_);
lean_ctor_set(v___x_566_, 2, v___x_557_);
lean_ctor_set(v___x_566_, 3, v___x_559_);
lean_ctor_set(v___x_566_, 4, v___x_565_);
lean_ctor_set_uint8(v___x_566_, sizeof(void*)*5, v___x_544_);
lean_ctor_set_uint8(v___x_566_, sizeof(void*)*5 + 1, v___x_558_);
lean_ctor_set_uint8(v___x_566_, sizeof(void*)*5 + 2, v___x_544_);
v___x_567_ = l_Lean_MessageLog_add(v___x_566_, v_b_535_);
v___y_537_ = v___x_567_;
goto v___jp_536_;
}
}
}
}
}
}
else
{
v___y_537_ = v_b_535_;
goto v___jp_536_;
}
}
else
{
lean_dec(v_startPos_531_);
lean_dec_ref(v_inputCtx_529_);
return v_b_535_;
}
v___jp_536_:
{
size_t v___x_538_; size_t v___x_539_; 
v___x_538_ = ((size_t)1ULL);
v___x_539_ = lean_usize_add(v_i_533_, v___x_538_);
v_i_533_ = v___x_539_;
v_b_535_ = v___y_537_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___boxed(lean_object* v_ignoreDeprecatedImports_572_, lean_object* v_env_573_, lean_object* v_inputCtx_574_, lean_object* v_importPositions_575_, lean_object* v_startPos_576_, lean_object* v_as_577_, lean_object* v_i_578_, lean_object* v_stop_579_, lean_object* v_b_580_){
_start:
{
size_t v_i_boxed_581_; size_t v_stop_boxed_582_; lean_object* v_res_583_; 
v_i_boxed_581_ = lean_unbox_usize(v_i_578_);
lean_dec(v_i_578_);
v_stop_boxed_582_ = lean_unbox_usize(v_stop_579_);
lean_dec(v_stop_579_);
v_res_583_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1(v_ignoreDeprecatedImports_572_, v_env_573_, v_inputCtx_574_, v_importPositions_575_, v_startPos_576_, v_as_577_, v_i_boxed_581_, v_stop_boxed_582_, v_b_580_);
lean_dec_ref(v_as_577_);
lean_dec(v_importPositions_575_);
lean_dec_ref(v_env_573_);
lean_dec(v_ignoreDeprecatedImports_572_);
return v_res_583_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedImports___closed__0(void){
_start:
{
lean_object* v_importPositions_584_; lean_object* v_ignoreDeprecatedImports_585_; lean_object* v___x_586_; 
v_importPositions_584_ = lean_box(1);
v_ignoreDeprecatedImports_585_ = l_Lean_NameSet_empty;
v___x_586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_586_, 0, v_ignoreDeprecatedImports_585_);
lean_ctor_set(v___x_586_, 1, v_importPositions_584_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedImports(lean_object* v_env_587_, lean_object* v_imports_588_, lean_object* v_opts_589_, lean_object* v_inputCtx_590_, lean_object* v_startPos_591_, lean_object* v_messages_592_, lean_object* v_headerStx_x3f_593_, lean_object* v_origHeaderStx_x3f_594_){
_start:
{
lean_object* v_opts_596_; lean_object* v_ignoreDeprecatedImports_597_; lean_object* v_importPositions_598_; lean_object* v_ignoreDeprecatedImports_607_; lean_object* v_importPositions_608_; lean_object* v___y_610_; lean_object* v_opts_611_; lean_object* v___y_619_; lean_object* v___y_620_; lean_object* v___y_621_; lean_object* v___y_645_; lean_object* v___y_646_; lean_object* v___y_647_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v_moduleTk_650_; lean_object* v_val_660_; 
v_ignoreDeprecatedImports_607_ = l_Lean_NameSet_empty;
v_importPositions_608_ = lean_box(1);
if (lean_obj_tag(v_origHeaderStx_x3f_594_) == 0)
{
if (lean_obj_tag(v_headerStx_x3f_593_) == 1)
{
lean_object* v_val_677_; 
v_val_677_ = lean_ctor_get(v_headerStx_x3f_593_, 0);
lean_inc(v_val_677_);
lean_dec_ref_known(v_headerStx_x3f_593_, 1);
v_val_660_ = v_val_677_;
goto v___jp_659_;
}
else
{
lean_dec(v_headerStx_x3f_593_);
v_opts_596_ = v_opts_589_;
v_ignoreDeprecatedImports_597_ = v_ignoreDeprecatedImports_607_;
v_importPositions_598_ = v_importPositions_608_;
goto v___jp_595_;
}
}
else
{
lean_object* v_val_678_; 
lean_dec(v_headerStx_x3f_593_);
v_val_678_ = lean_ctor_get(v_origHeaderStx_x3f_594_, 0);
lean_inc(v_val_678_);
lean_dec_ref_known(v_origHeaderStx_x3f_594_, 1);
v_val_660_ = v_val_678_;
goto v___jp_659_;
}
v___jp_595_:
{
lean_object* v___x_599_; uint8_t v___x_600_; 
v___x_599_ = l_Lean_linter_deprecated_module;
v___x_600_ = l_Lean_Option_get___at___00Lean_Elab_checkDeprecatedImports_spec__0(v_opts_596_, v___x_599_);
lean_dec_ref(v_opts_596_);
if (v___x_600_ == 0)
{
lean_dec(v_importPositions_598_);
lean_dec(v_ignoreDeprecatedImports_597_);
lean_dec(v_startPos_591_);
lean_dec_ref(v_inputCtx_590_);
return v_messages_592_;
}
else
{
lean_object* v___x_601_; lean_object* v___x_602_; uint8_t v___x_603_; 
v___x_601_ = lean_unsigned_to_nat(0u);
v___x_602_ = lean_array_get_size(v_imports_588_);
v___x_603_ = lean_nat_dec_lt(v___x_601_, v___x_602_);
if (v___x_603_ == 0)
{
lean_dec(v_importPositions_598_);
lean_dec(v_ignoreDeprecatedImports_597_);
lean_dec(v_startPos_591_);
lean_dec_ref(v_inputCtx_590_);
return v_messages_592_;
}
else
{
size_t v___x_604_; size_t v___x_605_; lean_object* v___x_606_; 
v___x_604_ = ((size_t)0ULL);
v___x_605_ = lean_usize_of_nat(v___x_602_);
v___x_606_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1(v_ignoreDeprecatedImports_597_, v_env_587_, v_inputCtx_590_, v_importPositions_598_, v_startPos_591_, v_imports_588_, v___x_604_, v___x_605_, v_messages_592_);
lean_dec(v_importPositions_598_);
lean_dec(v_ignoreDeprecatedImports_597_);
return v___x_606_;
}
}
}
v___jp_609_:
{
lean_object* v___x_612_; size_t v_sz_613_; size_t v___x_614_; lean_object* v___x_615_; lean_object* v_fst_616_; lean_object* v_snd_617_; 
v___x_612_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedImports___closed__0, &l_Lean_Elab_checkDeprecatedImports___closed__0_once, _init_l_Lean_Elab_checkDeprecatedImports___closed__0);
v_sz_613_ = lean_array_size(v___y_610_);
v___x_614_ = ((size_t)0ULL);
v___x_615_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkDeprecatedImports_spec__3(v___y_610_, v_sz_613_, v___x_614_, v___x_612_);
lean_dec_ref(v___y_610_);
v_fst_616_ = lean_ctor_get(v___x_615_, 0);
lean_inc(v_fst_616_);
v_snd_617_ = lean_ctor_get(v___x_615_, 1);
lean_inc(v_snd_617_);
lean_dec_ref(v___x_615_);
v_opts_596_ = v_opts_611_;
v_ignoreDeprecatedImports_597_ = v_fst_616_;
v_importPositions_598_ = v_snd_617_;
goto v___jp_595_;
}
v___jp_618_:
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v_importsStx_624_; 
v___x_622_ = lean_unsigned_to_nat(2u);
v___x_623_ = l_Lean_Syntax_getArg(v___y_621_, v___x_622_);
lean_dec(v___y_621_);
v_importsStx_624_ = l_Lean_Syntax_getArgs(v___x_623_);
lean_dec(v___x_623_);
if (lean_obj_tag(v___y_619_) == 0)
{
lean_dec(v___y_620_);
v___y_610_ = v_importsStx_624_;
v_opts_611_ = v_opts_589_;
goto v___jp_609_;
}
else
{
lean_object* v_val_625_; lean_object* v___x_626_; 
v_val_625_ = lean_ctor_get(v___y_619_, 0);
lean_inc(v_val_625_);
lean_dec_ref_known(v___y_619_, 1);
v___x_626_ = l_Lean_Syntax_getTrailing_x3f(v_val_625_);
lean_dec(v_val_625_);
if (lean_obj_tag(v___x_626_) == 0)
{
lean_dec(v___y_620_);
v___y_610_ = v_importsStx_624_;
v_opts_611_ = v_opts_589_;
goto v___jp_609_;
}
else
{
lean_object* v_val_627_; lean_object* v_str_628_; lean_object* v_startPos_629_; lean_object* v_stopPos_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_643_; 
v_val_627_ = lean_ctor_get(v___x_626_, 0);
lean_inc(v_val_627_);
lean_dec_ref_known(v___x_626_, 1);
v_str_628_ = lean_ctor_get(v_val_627_, 0);
v_startPos_629_ = lean_ctor_get(v_val_627_, 1);
v_stopPos_630_ = lean_ctor_get(v_val_627_, 2);
v_isSharedCheck_643_ = !lean_is_exclusive(v_val_627_);
if (v_isSharedCheck_643_ == 0)
{
v___x_632_ = v_val_627_;
v_isShared_633_ = v_isSharedCheck_643_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_stopPos_630_);
lean_inc(v_startPos_629_);
lean_inc(v_str_628_);
lean_dec(v_val_627_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_643_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_637_; 
v___x_634_ = lean_string_utf8_extract(v_str_628_, v_startPos_629_, v_stopPos_630_);
lean_dec(v_stopPos_630_);
lean_dec(v_startPos_629_);
lean_dec_ref(v_str_628_);
v___x_635_ = lean_string_utf8_byte_size(v___x_634_);
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 2, v___x_635_);
lean_ctor_set(v___x_632_, 1, v___y_620_);
lean_ctor_set(v___x_632_, 0, v___x_634_);
v___x_637_ = v___x_632_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v___x_634_);
lean_ctor_set(v_reuseFailAlloc_642_, 1, v___y_620_);
lean_ctor_set(v_reuseFailAlloc_642_, 2, v___x_635_);
v___x_637_ = v_reuseFailAlloc_642_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
uint8_t v___x_638_; 
v___x_638_ = l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2(v___x_637_);
lean_dec_ref(v___x_637_);
if (v___x_638_ == 0)
{
v___y_610_ = v_importsStx_624_;
v_opts_611_ = v_opts_589_;
goto v___jp_609_;
}
else
{
lean_object* v___x_639_; uint8_t v___x_640_; lean_object* v_opts_641_; 
v___x_639_ = l_Lean_linter_deprecated_module;
v___x_640_ = 0;
v_opts_641_ = l_Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4(v_opts_589_, v___x_639_, v___x_640_);
v___y_610_ = v_importsStx_624_;
v_opts_611_ = v_opts_641_;
goto v___jp_609_;
}
}
}
}
}
}
v___jp_644_:
{
lean_object* v___x_651_; lean_object* v___x_652_; uint8_t v___x_653_; 
v___x_651_ = lean_unsigned_to_nat(1u);
v___x_652_ = l_Lean_Syntax_getArg(v___y_649_, v___x_651_);
v___x_653_ = l_Lean_Syntax_isNone(v___x_652_);
if (v___x_653_ == 0)
{
uint8_t v___x_654_; 
lean_inc(v___x_652_);
v___x_654_ = l_Lean_Syntax_matchesNull(v___x_652_, v___x_651_);
if (v___x_654_ == 0)
{
lean_dec(v___x_652_);
lean_dec(v_moduleTk_650_);
lean_dec(v___y_649_);
lean_dec(v___y_648_);
v_opts_596_ = v_opts_589_;
v_ignoreDeprecatedImports_597_ = v_ignoreDeprecatedImports_607_;
v_importPositions_598_ = v_importPositions_608_;
goto v___jp_595_;
}
else
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; uint8_t v___x_658_; 
v___x_655_ = l_Lean_Syntax_getArg(v___x_652_, v___y_648_);
lean_dec(v___x_652_);
v___x_656_ = ((lean_object*)(l_Lean_Elab_HeaderSyntax_imports___closed__6));
lean_inc_ref(v___y_645_);
lean_inc_ref(v___y_646_);
lean_inc_ref(v___y_647_);
v___x_657_ = l_Lean_Name_mkStr4(v___y_647_, v___y_646_, v___y_645_, v___x_656_);
v___x_658_ = l_Lean_Syntax_isOfKind(v___x_655_, v___x_657_);
lean_dec(v___x_657_);
if (v___x_658_ == 0)
{
lean_dec(v_moduleTk_650_);
lean_dec(v___y_649_);
lean_dec(v___y_648_);
v_opts_596_ = v_opts_589_;
v_ignoreDeprecatedImports_597_ = v_ignoreDeprecatedImports_607_;
v_importPositions_598_ = v_importPositions_608_;
goto v___jp_595_;
}
else
{
v___y_619_ = v_moduleTk_650_;
v___y_620_ = v___y_648_;
v___y_621_ = v___y_649_;
goto v___jp_618_;
}
}
}
else
{
lean_dec(v___x_652_);
v___y_619_ = v_moduleTk_650_;
v___y_620_ = v___y_648_;
v___y_621_ = v___y_649_;
goto v___jp_618_;
}
}
v___jp_659_:
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; uint8_t v___x_665_; 
v___x_661_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__0));
v___x_662_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__1));
v___x_663_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__2));
v___x_664_ = ((lean_object*)(l_Lean_Elab_HeaderSyntax_imports___closed__1));
lean_inc(v_val_660_);
v___x_665_ = l_Lean_Syntax_isOfKind(v_val_660_, v___x_664_);
if (v___x_665_ == 0)
{
lean_dec(v_val_660_);
v_opts_596_ = v_opts_589_;
v_ignoreDeprecatedImports_597_ = v_ignoreDeprecatedImports_607_;
v_importPositions_598_ = v_importPositions_608_;
goto v___jp_595_;
}
else
{
lean_object* v___x_666_; lean_object* v___x_667_; uint8_t v___x_668_; 
v___x_666_ = lean_unsigned_to_nat(0u);
v___x_667_ = l_Lean_Syntax_getArg(v_val_660_, v___x_666_);
v___x_668_ = l_Lean_Syntax_isNone(v___x_667_);
if (v___x_668_ == 0)
{
lean_object* v___x_669_; uint8_t v___x_670_; 
v___x_669_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_667_);
v___x_670_ = l_Lean_Syntax_matchesNull(v___x_667_, v___x_669_);
if (v___x_670_ == 0)
{
lean_dec(v___x_667_);
lean_dec(v_val_660_);
v_opts_596_ = v_opts_589_;
v_ignoreDeprecatedImports_597_ = v_ignoreDeprecatedImports_607_;
v_importPositions_598_ = v_importPositions_608_;
goto v___jp_595_;
}
else
{
lean_object* v___x_671_; lean_object* v___x_672_; uint8_t v___x_673_; 
v___x_671_ = l_Lean_Syntax_getArg(v___x_667_, v___x_666_);
lean_dec(v___x_667_);
v___x_672_ = ((lean_object*)(l_Lean_Elab_HeaderSyntax_imports___closed__9));
lean_inc(v___x_671_);
v___x_673_ = l_Lean_Syntax_isOfKind(v___x_671_, v___x_672_);
if (v___x_673_ == 0)
{
lean_dec(v___x_671_);
lean_dec(v_val_660_);
v_opts_596_ = v_opts_589_;
v_ignoreDeprecatedImports_597_ = v_ignoreDeprecatedImports_607_;
v_importPositions_598_ = v_importPositions_608_;
goto v___jp_595_;
}
else
{
lean_object* v_moduleTk_674_; lean_object* v___x_675_; 
v_moduleTk_674_ = l_Lean_Syntax_getArg(v___x_671_, v___x_666_);
lean_dec(v___x_671_);
v___x_675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_675_, 0, v_moduleTk_674_);
v___y_645_ = v___x_663_;
v___y_646_ = v___x_662_;
v___y_647_ = v___x_661_;
v___y_648_ = v___x_666_;
v___y_649_ = v_val_660_;
v_moduleTk_650_ = v___x_675_;
goto v___jp_644_;
}
}
}
else
{
lean_object* v___x_676_; 
lean_dec(v___x_667_);
v___x_676_ = lean_box(0);
v___y_645_ = v___x_663_;
v___y_646_ = v___x_662_;
v___y_647_ = v___x_661_;
v___y_648_ = v___x_666_;
v___y_649_ = v_val_660_;
v_moduleTk_650_ = v___x_676_;
goto v___jp_644_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedImports___boxed(lean_object* v_env_679_, lean_object* v_imports_680_, lean_object* v_opts_681_, lean_object* v_inputCtx_682_, lean_object* v_startPos_683_, lean_object* v_messages_684_, lean_object* v_headerStx_x3f_685_, lean_object* v_origHeaderStx_x3f_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_Lean_Elab_checkDeprecatedImports(v_env_679_, v_imports_680_, v_opts_681_, v_inputCtx_682_, v_startPos_683_, v_messages_684_, v_headerStx_x3f_685_, v_origHeaderStx_x3f_686_);
lean_dec_ref(v_imports_680_);
lean_dec_ref(v_env_679_);
return v_res_687_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_spec__2(lean_object* v_s_688_, lean_object* v_inst_689_, lean_object* v_R_690_, lean_object* v_a_691_, uint8_t v_b_692_, lean_object* v_c_693_){
_start:
{
uint8_t v___x_694_; 
v___x_694_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_spec__2___redArg(v_s_688_, v_a_691_, v_b_692_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_spec__2___boxed(lean_object* v_s_695_, lean_object* v_inst_696_, lean_object* v_R_697_, lean_object* v_a_698_, lean_object* v_b_699_, lean_object* v_c_700_){
_start:
{
uint8_t v_b_boxed_701_; uint8_t v_res_702_; lean_object* v_r_703_; 
v_b_boxed_701_ = lean_unbox(v_b_699_);
v_res_702_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_spec__2(v_s_695_, v_inst_696_, v_R_697_, v_a_698_, v_b_boxed_701_, v_c_700_);
lean_dec_ref(v_s_695_);
v_r_703_ = lean_box(v_res_702_);
return v_r_703_;
}
}
static lean_object* _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_704_; lean_object* v___x_705_; 
v___x_704_ = 33;
v___x_705_ = lean_box_uint32(v___x_704_);
return v___x_705_;
}
}
static lean_object* _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__2(void){
_start:
{
uint32_t v___x_706_; lean_object* v___x_707_; 
v___x_706_ = 42;
v___x_707_ = lean_box_uint32(v___x_706_);
return v___x_707_;
}
}
static lean_object* _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__3(void){
_start:
{
uint32_t v___x_708_; lean_object* v___x_709_; 
v___x_708_ = 63;
v___x_709_ = lean_box_uint32(v___x_708_);
return v___x_709_;
}
}
static lean_object* _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__4(void){
_start:
{
uint32_t v___x_710_; lean_object* v___x_711_; 
v___x_710_ = 124;
v___x_711_ = lean_box_uint32(v___x_710_);
return v___x_711_;
}
}
static lean_object* _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__5(void){
_start:
{
uint32_t v___x_712_; lean_object* v___x_713_; 
v___x_712_ = 34;
v___x_713_ = lean_box_uint32(v___x_712_);
return v___x_713_;
}
}
static lean_object* _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__6(void){
_start:
{
uint32_t v___x_714_; lean_object* v___x_715_; 
v___x_714_ = 62;
v___x_715_ = lean_box_uint32(v___x_714_);
return v___x_715_;
}
}
static lean_object* _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__7(void){
_start:
{
uint32_t v___x_716_; lean_object* v___x_717_; 
v___x_716_ = 60;
v___x_717_ = lean_box_uint32(v___x_716_);
return v___x_717_;
}
}
static lean_object* _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0(void){
_start:
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_718_ = lean_unsigned_to_nat(7u);
v___x_719_ = lean_mk_empty_array_with_capacity(v___x_718_);
v___x_720_ = l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__7;
v___x_721_ = lean_array_push(v___x_719_, v___x_720_);
v___x_722_ = l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__6;
v___x_723_ = lean_array_push(v___x_721_, v___x_722_);
v___x_724_ = l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__5;
v___x_725_ = lean_array_push(v___x_723_, v___x_724_);
v___x_726_ = l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__4;
v___x_727_ = lean_array_push(v___x_725_, v___x_726_);
v___x_728_ = l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__3;
v___x_729_ = lean_array_push(v___x_727_, v___x_728_);
v___x_730_ = l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__2;
v___x_731_ = lean_array_push(v___x_729_, v___x_730_);
v___x_732_ = l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__1;
v___x_733_ = lean_array_push(v___x_731_, v___x_732_);
return v___x_733_;
}
}
static lean_object* _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars(void){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = lean_obj_once(&l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0, &l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0_once, _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__0(lean_object* v_s_822_, lean_object* v_p_823_){
_start:
{
lean_object* v___y_825_; lean_object* v___y_826_; uint32_t v___y_830_; lean_object* v___x_842_; uint8_t v_decide_843_; 
v___x_842_ = lean_string_utf8_byte_size(v_s_822_);
v_decide_843_ = lean_nat_dec_eq(v_p_823_, v___x_842_);
if (v_decide_843_ == 0)
{
uint32_t v___x_844_; uint32_t v___x_845_; uint8_t v___x_846_; 
v___x_844_ = lean_string_utf8_get_fast(v_s_822_, v_p_823_);
v___x_845_ = 97;
v___x_846_ = lean_uint32_dec_le(v___x_845_, v___x_844_);
if (v___x_846_ == 0)
{
v___y_830_ = v___x_844_;
goto v___jp_829_;
}
else
{
uint32_t v___x_847_; uint8_t v___x_848_; 
v___x_847_ = 122;
v___x_848_ = lean_uint32_dec_le(v___x_844_, v___x_847_);
if (v___x_848_ == 0)
{
v___y_830_ = v___x_844_;
goto v___jp_829_;
}
else
{
uint32_t v___x_849_; uint32_t v___x_850_; 
v___x_849_ = 4294967264;
v___x_850_ = lean_uint32_add(v___x_844_, v___x_849_);
v___y_830_ = v___x_850_;
goto v___jp_829_;
}
}
}
else
{
lean_dec(v_p_823_);
return v_s_822_;
}
v___jp_824_:
{
lean_object* v___x_827_; 
v___x_827_ = lean_nat_add(v_p_823_, v___y_826_);
lean_dec(v_p_823_);
v_s_822_ = v___y_825_;
v_p_823_ = v___x_827_;
goto _start;
}
v___jp_829_:
{
lean_object* v___x_831_; uint32_t v___x_832_; uint8_t v___x_833_; 
lean_inc(v_p_823_);
v___x_831_ = lean_string_utf8_set(v_s_822_, v_p_823_, v___y_830_);
v___x_832_ = 127;
v___x_833_ = lean_uint32_dec_le(v___y_830_, v___x_832_);
if (v___x_833_ == 0)
{
uint32_t v___x_834_; uint8_t v___x_835_; 
v___x_834_ = 2047;
v___x_835_ = lean_uint32_dec_le(v___y_830_, v___x_834_);
if (v___x_835_ == 0)
{
uint32_t v___x_836_; uint8_t v___x_837_; 
v___x_836_ = 65535;
v___x_837_ = lean_uint32_dec_le(v___y_830_, v___x_836_);
if (v___x_837_ == 0)
{
lean_object* v___x_838_; 
v___x_838_ = lean_unsigned_to_nat(4u);
v___y_825_ = v___x_831_;
v___y_826_ = v___x_838_;
goto v___jp_824_;
}
else
{
lean_object* v___x_839_; 
v___x_839_ = lean_unsigned_to_nat(3u);
v___y_825_ = v___x_831_;
v___y_826_ = v___x_839_;
goto v___jp_824_;
}
}
else
{
lean_object* v___x_840_; 
v___x_840_ = lean_unsigned_to_nat(2u);
v___y_825_ = v___x_831_;
v___y_826_ = v___x_840_;
goto v___jp_824_;
}
}
else
{
lean_object* v___x_841_; 
v___x_841_ = lean_unsigned_to_nat(1u);
v___y_825_ = v___x_831_;
v___y_826_ = v___x_841_;
goto v___jp_824_;
}
}
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2_spec__3___redArg(lean_object* v_s_851_, uint32_t v_a_852_, lean_object* v_a_853_, uint8_t v_b_854_){
_start:
{
lean_object* v_str_855_; lean_object* v_startInclusive_856_; lean_object* v_endExclusive_857_; lean_object* v___x_858_; uint8_t v_decide_859_; 
v_str_855_ = lean_ctor_get(v_s_851_, 0);
v_startInclusive_856_ = lean_ctor_get(v_s_851_, 1);
v_endExclusive_857_ = lean_ctor_get(v_s_851_, 2);
v___x_858_ = lean_nat_sub(v_endExclusive_857_, v_startInclusive_856_);
v_decide_859_ = lean_nat_dec_eq(v_a_853_, v___x_858_);
lean_dec(v___x_858_);
if (v_decide_859_ == 0)
{
lean_object* v___x_860_; uint32_t v___x_861_; uint8_t v___x_862_; 
v___x_860_ = lean_nat_add(v_startInclusive_856_, v_a_853_);
lean_dec(v_a_853_);
v___x_861_ = lean_string_utf8_get_fast(v_str_855_, v___x_860_);
v___x_862_ = lean_uint32_dec_eq(v___x_861_, v_a_852_);
if (v___x_862_ == 0)
{
lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_863_ = lean_string_utf8_next_fast(v_str_855_, v___x_860_);
lean_dec(v___x_860_);
v___x_864_ = lean_nat_sub(v___x_863_, v_startInclusive_856_);
v_a_853_ = v___x_864_;
v_b_854_ = v___x_862_;
goto _start;
}
else
{
lean_dec(v___x_860_);
return v___x_862_;
}
}
else
{
lean_dec(v_a_853_);
return v_b_854_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2_spec__3___redArg___boxed(lean_object* v_s_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_b_869_){
_start:
{
uint32_t v_a_boxed_870_; uint8_t v_b_boxed_871_; uint8_t v_res_872_; lean_object* v_r_873_; 
v_a_boxed_870_ = lean_unbox_uint32(v_a_867_);
lean_dec(v_a_867_);
v_b_boxed_871_ = lean_unbox(v_b_869_);
v_res_872_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2_spec__3___redArg(v_s_866_, v_a_boxed_870_, v_a_868_, v_b_boxed_871_);
lean_dec_ref(v_s_866_);
v_r_873_ = lean_box(v_res_872_);
return v_r_873_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2(uint32_t v_a_874_, lean_object* v_s_875_){
_start:
{
lean_object* v_searcher_876_; uint8_t v___x_877_; uint8_t v___x_878_; 
v_searcher_876_ = lean_unsigned_to_nat(0u);
v___x_877_ = 0;
v___x_878_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2_spec__3___redArg(v_s_875_, v_a_874_, v_searcher_876_, v___x_877_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2___boxed(lean_object* v_a_879_, lean_object* v_s_880_){
_start:
{
uint32_t v_a_boxed_881_; uint8_t v_res_882_; lean_object* v_r_883_; 
v_a_boxed_881_ = lean_unbox_uint32(v_a_879_);
lean_dec(v_a_879_);
v_res_882_ = l_String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2(v_a_boxed_881_, v_s_880_);
lean_dec_ref(v_s_880_);
v_r_883_ = lean_box(v_res_882_);
return v_r_883_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__3(lean_object* v_comp_887_, lean_object* v_as_888_, size_t v_sz_889_, size_t v_i_890_, lean_object* v_b_891_){
_start:
{
uint8_t v___x_892_; 
v___x_892_ = lean_usize_dec_lt(v_i_890_, v_sz_889_);
if (v___x_892_ == 0)
{
lean_dec_ref(v_comp_887_);
lean_inc_ref(v_b_891_);
return v_b_891_;
}
else
{
lean_object* v___x_893_; lean_object* v_a_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; uint32_t v___x_898_; uint8_t v___x_899_; 
v___x_893_ = lean_box(0);
v_a_894_ = lean_array_uget_borrowed(v_as_888_, v_i_890_);
v___x_895_ = lean_unsigned_to_nat(0u);
v___x_896_ = lean_string_utf8_byte_size(v_comp_887_);
lean_inc_ref(v_comp_887_);
v___x_897_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_897_, 0, v_comp_887_);
lean_ctor_set(v___x_897_, 1, v___x_895_);
lean_ctor_set(v___x_897_, 2, v___x_896_);
v___x_898_ = lean_unbox_uint32(v_a_894_);
v___x_899_ = l_String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2(v___x_898_, v___x_897_);
lean_dec_ref_known(v___x_897_, 3);
if (v___x_899_ == 0)
{
lean_object* v___x_900_; size_t v___x_901_; size_t v___x_902_; 
v___x_900_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__3___closed__0));
v___x_901_ = ((size_t)1ULL);
v___x_902_ = lean_usize_add(v_i_890_, v___x_901_);
v_i_890_ = v___x_902_;
v_b_891_ = v___x_900_;
goto _start;
}
else
{
lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
lean_dec_ref(v_comp_887_);
lean_inc(v_a_894_);
v___x_904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_904_, 0, v_a_894_);
v___x_905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_905_, 0, v___x_904_);
v___x_906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_906_, 0, v___x_905_);
lean_ctor_set(v___x_906_, 1, v___x_893_);
return v___x_906_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__3___boxed(lean_object* v_comp_907_, lean_object* v_as_908_, lean_object* v_sz_909_, lean_object* v_i_910_, lean_object* v_b_911_){
_start:
{
size_t v_sz_boxed_912_; size_t v_i_boxed_913_; lean_object* v_res_914_; 
v_sz_boxed_912_ = lean_unbox_usize(v_sz_909_);
lean_dec(v_sz_909_);
v_i_boxed_913_ = lean_unbox_usize(v_i_910_);
lean_dec(v_i_910_);
v_res_914_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__3(v_comp_907_, v_as_908_, v_sz_boxed_912_, v_i_boxed_913_, v_b_911_);
lean_dec_ref(v_b_911_);
lean_dec_ref(v_as_908_);
return v_res_914_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__1_spec__1(lean_object* v_a_915_, lean_object* v_as_916_, size_t v_i_917_, size_t v_stop_918_){
_start:
{
uint8_t v___x_919_; 
v___x_919_ = lean_usize_dec_eq(v_i_917_, v_stop_918_);
if (v___x_919_ == 0)
{
lean_object* v___x_920_; uint8_t v___x_921_; 
v___x_920_ = lean_array_uget_borrowed(v_as_916_, v_i_917_);
v___x_921_ = lean_string_dec_eq(v_a_915_, v___x_920_);
if (v___x_921_ == 0)
{
size_t v___x_922_; size_t v___x_923_; 
v___x_922_ = ((size_t)1ULL);
v___x_923_ = lean_usize_add(v_i_917_, v___x_922_);
v_i_917_ = v___x_923_;
goto _start;
}
else
{
return v___x_921_;
}
}
else
{
uint8_t v___x_925_; 
v___x_925_ = 0;
return v___x_925_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__1_spec__1___boxed(lean_object* v_a_926_, lean_object* v_as_927_, lean_object* v_i_928_, lean_object* v_stop_929_){
_start:
{
size_t v_i_boxed_930_; size_t v_stop_boxed_931_; uint8_t v_res_932_; lean_object* v_r_933_; 
v_i_boxed_930_ = lean_unbox_usize(v_i_928_);
lean_dec(v_i_928_);
v_stop_boxed_931_ = lean_unbox_usize(v_stop_929_);
lean_dec(v_stop_929_);
v_res_932_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__1_spec__1(v_a_926_, v_as_927_, v_i_boxed_930_, v_stop_boxed_931_);
lean_dec_ref(v_as_927_);
lean_dec_ref(v_a_926_);
v_r_933_ = lean_box(v_res_932_);
return v_r_933_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__1(lean_object* v_as_934_, lean_object* v_a_935_){
_start:
{
lean_object* v___x_936_; lean_object* v___x_937_; uint8_t v___x_938_; 
v___x_936_ = lean_unsigned_to_nat(0u);
v___x_937_ = lean_array_get_size(v_as_934_);
v___x_938_ = lean_nat_dec_lt(v___x_936_, v___x_937_);
if (v___x_938_ == 0)
{
return v___x_938_;
}
else
{
size_t v___x_939_; size_t v___x_940_; uint8_t v___x_941_; 
v___x_939_ = ((size_t)0ULL);
v___x_940_ = lean_usize_of_nat(v___x_937_);
v___x_941_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__1_spec__1(v_a_935_, v_as_934_, v___x_939_, v___x_940_);
return v___x_941_;
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__1___boxed(lean_object* v_as_942_, lean_object* v_a_943_){
_start:
{
uint8_t v_res_944_; lean_object* v_r_945_; 
v_res_944_ = l_Array_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__1(v_as_942_, v_a_943_);
lean_dec_ref(v_a_943_);
lean_dec_ref(v_as_942_);
v_r_945_ = lean_box(v_res_944_);
return v_r_945_;
}
}
static size_t _init_l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__0(void){
_start:
{
lean_object* v___x_946_; size_t v_sz_947_; 
v___x_946_ = l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars;
v_sz_947_ = lean_array_size(v___x_946_);
return v_sz_947_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability(lean_object* v_comp_952_){
_start:
{
lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; uint8_t v___x_956_; 
v___x_953_ = ((lean_object*)(l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames));
v___x_954_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_comp_952_);
v___x_955_ = l_String_mapAux___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__0(v_comp_952_, v___x_954_);
v___x_956_ = l_Array_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__1(v___x_953_, v___x_955_);
lean_dec_ref(v___x_955_);
if (v___x_956_ == 0)
{
lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; size_t v_sz_960_; size_t v___x_961_; lean_object* v___x_962_; lean_object* v_fst_963_; 
v___x_957_ = l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars;
v___x_958_ = lean_box(0);
v___x_959_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__3___closed__0));
v_sz_960_ = lean_usize_once(&l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__0, &l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__0_once, _init_l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__0);
v___x_961_ = ((size_t)0ULL);
v___x_962_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__3(v_comp_952_, v___x_957_, v_sz_960_, v___x_961_, v___x_959_);
v_fst_963_ = lean_ctor_get(v___x_962_, 0);
lean_inc(v_fst_963_);
lean_dec_ref(v___x_962_);
if (lean_obj_tag(v_fst_963_) == 0)
{
return v___x_958_;
}
else
{
lean_object* v_val_964_; 
v_val_964_ = lean_ctor_get(v_fst_963_, 0);
lean_inc(v_val_964_);
lean_dec_ref_known(v_fst_963_, 1);
if (lean_obj_tag(v_val_964_) == 1)
{
lean_object* v_val_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_979_; 
v_val_965_ = lean_ctor_get(v_val_964_, 0);
v_isSharedCheck_979_ = !lean_is_exclusive(v_val_964_);
if (v_isSharedCheck_979_ == 0)
{
v___x_967_ = v_val_964_;
v_isShared_968_ = v_isSharedCheck_979_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_val_965_);
lean_dec(v_val_964_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_979_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___x_969_; lean_object* v___x_970_; uint32_t v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_977_; 
v___x_969_ = ((lean_object*)(l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__1));
v___x_970_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___closed__0));
v___x_971_ = lean_unbox_uint32(v_val_965_);
lean_dec(v_val_965_);
v___x_972_ = lean_string_push(v___x_970_, v___x_971_);
v___x_973_ = lean_string_append(v___x_969_, v___x_972_);
lean_dec_ref(v___x_972_);
v___x_974_ = ((lean_object*)(l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__2));
v___x_975_ = lean_string_append(v___x_973_, v___x_974_);
if (v_isShared_968_ == 0)
{
lean_ctor_set(v___x_967_, 0, v___x_975_);
v___x_977_ = v___x_967_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v___x_975_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
}
else
{
lean_dec(v_val_964_);
return v___x_958_;
}
}
}
else
{
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_980_ = ((lean_object*)(l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__3));
v___x_981_ = lean_string_append(v___x_980_, v_comp_952_);
lean_dec_ref(v_comp_952_);
v___x_982_ = ((lean_object*)(l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__4));
v___x_983_ = lean_string_append(v___x_981_, v___x_982_);
v___x_984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_984_, 0, v___x_983_);
return v___x_984_;
}
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2_spec__3(lean_object* v_s_985_, uint32_t v_a_986_, lean_object* v_inst_987_, lean_object* v_R_988_, lean_object* v_a_989_, uint8_t v_b_990_, lean_object* v_c_991_){
_start:
{
uint8_t v___x_992_; 
v___x_992_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2_spec__3___redArg(v_s_985_, v_a_986_, v_a_989_, v_b_990_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2_spec__3___boxed(lean_object* v_s_993_, lean_object* v_a_994_, lean_object* v_inst_995_, lean_object* v_R_996_, lean_object* v_a_997_, lean_object* v_b_998_, lean_object* v_c_999_){
_start:
{
uint32_t v_a_boxed_1000_; uint8_t v_b_boxed_1001_; uint8_t v_res_1002_; lean_object* v_r_1003_; 
v_a_boxed_1000_ = lean_unbox_uint32(v_a_994_);
lean_dec(v_a_994_);
v_b_boxed_1001_ = lean_unbox(v_b_998_);
v_res_1002_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2_spec__3(v_s_993_, v_a_boxed_1000_, v_inst_995_, v_R_996_, v_a_997_, v_b_boxed_1001_, v_c_999_);
lean_dec_ref(v_s_993_);
v_r_1003_ = lean_box(v_res_1002_);
return v_r_1003_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_checkModuleNamePortability_go(lean_object* v_mainModule_1006_, lean_object* v_inputCtx_1007_, lean_object* v_startPos_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_){
_start:
{
switch(lean_obj_tag(v_a_1009_))
{
case 0:
{
lean_dec_ref(v_inputCtx_1007_);
lean_dec(v_mainModule_1006_);
return v_a_1010_;
}
case 1:
{
lean_object* v_pre_1011_; lean_object* v_str_1012_; lean_object* v___x_1013_; 
v_pre_1011_ = lean_ctor_get(v_a_1009_, 0);
lean_inc(v_pre_1011_);
v_str_1012_ = lean_ctor_get(v_a_1009_, 1);
lean_inc_ref(v_str_1012_);
lean_dec_ref_known(v_a_1009_, 2);
v___x_1013_ = l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability(v_str_1012_);
if (lean_obj_tag(v___x_1013_) == 0)
{
v_a_1009_ = v_pre_1011_;
goto _start;
}
else
{
lean_object* v_val_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1040_; 
v_val_1015_ = lean_ctor_get(v___x_1013_, 0);
v_isSharedCheck_1040_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1017_ = v___x_1013_;
v_isShared_1018_ = v_isSharedCheck_1040_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_val_1015_);
lean_dec(v___x_1013_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1040_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v_fileName_1019_; lean_object* v_fileMap_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; uint8_t v___x_1023_; uint8_t v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; uint8_t v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1034_; 
v_fileName_1019_ = lean_ctor_get(v_inputCtx_1007_, 1);
v_fileMap_1020_ = lean_ctor_get(v_inputCtx_1007_, 2);
lean_inc_ref(v_fileMap_1020_);
v___x_1021_ = l_Lean_FileMap_toPosition(v_fileMap_1020_, v_startPos_1008_);
v___x_1022_ = lean_box(0);
v___x_1023_ = 0;
v___x_1024_ = 2;
v___x_1025_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___closed__0));
v___x_1026_ = ((lean_object*)(l___private_Lean_Elab_Import_0__Lean_Elab_checkModuleNamePortability_go___closed__0));
v___x_1027_ = 1;
lean_inc(v_mainModule_1006_);
v___x_1028_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mainModule_1006_, v___x_1027_);
v___x_1029_ = lean_string_append(v___x_1026_, v___x_1028_);
lean_dec_ref(v___x_1028_);
v___x_1030_ = ((lean_object*)(l___private_Lean_Elab_Import_0__Lean_Elab_checkModuleNamePortability_go___closed__1));
v___x_1031_ = lean_string_append(v___x_1029_, v___x_1030_);
v___x_1032_ = lean_string_append(v___x_1031_, v_val_1015_);
lean_dec(v_val_1015_);
if (v_isShared_1018_ == 0)
{
lean_ctor_set_tag(v___x_1017_, 3);
lean_ctor_set(v___x_1017_, 0, v___x_1032_);
v___x_1034_ = v___x_1017_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v___x_1032_);
v___x_1034_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1035_ = l_Lean_MessageData_ofFormat(v___x_1034_);
lean_inc_ref(v_fileName_1019_);
v___x_1036_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1036_, 0, v_fileName_1019_);
lean_ctor_set(v___x_1036_, 1, v___x_1021_);
lean_ctor_set(v___x_1036_, 2, v___x_1022_);
lean_ctor_set(v___x_1036_, 3, v___x_1025_);
lean_ctor_set(v___x_1036_, 4, v___x_1035_);
lean_ctor_set_uint8(v___x_1036_, sizeof(void*)*5, v___x_1023_);
lean_ctor_set_uint8(v___x_1036_, sizeof(void*)*5 + 1, v___x_1024_);
lean_ctor_set_uint8(v___x_1036_, sizeof(void*)*5 + 2, v___x_1023_);
v___x_1037_ = l_Lean_MessageLog_add(v___x_1036_, v_a_1010_);
v_a_1009_ = v_pre_1011_;
v_a_1010_ = v___x_1037_;
goto _start;
}
}
}
}
default: 
{
lean_object* v_pre_1041_; 
v_pre_1041_ = lean_ctor_get(v_a_1009_, 0);
lean_inc(v_pre_1041_);
lean_dec_ref_known(v_a_1009_, 2);
v_a_1009_ = v_pre_1041_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_checkModuleNamePortability_go___boxed(lean_object* v_mainModule_1043_, lean_object* v_inputCtx_1044_, lean_object* v_startPos_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l___private_Lean_Elab_Import_0__Lean_Elab_checkModuleNamePortability_go(v_mainModule_1043_, v_inputCtx_1044_, v_startPos_1045_, v_a_1046_, v_a_1047_);
lean_dec(v_startPos_1045_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkModuleNamePortability(lean_object* v_mainModule_1049_, lean_object* v_inputCtx_1050_, lean_object* v_startPos_1051_, lean_object* v_messages_1052_){
_start:
{
lean_object* v___x_1053_; 
lean_inc(v_mainModule_1049_);
v___x_1053_ = l___private_Lean_Elab_Import_0__Lean_Elab_checkModuleNamePortability_go(v_mainModule_1049_, v_inputCtx_1050_, v_startPos_1051_, v_mainModule_1049_, v_messages_1052_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkModuleNamePortability___boxed(lean_object* v_mainModule_1054_, lean_object* v_inputCtx_1055_, lean_object* v_startPos_1056_, lean_object* v_messages_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l_Lean_Elab_checkModuleNamePortability(v_mainModule_1054_, v_inputCtx_1055_, v_startPos_1056_, v_messages_1057_);
lean_dec(v_startPos_1056_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_processHeaderCore___lam__0(lean_object* v_package_x3f_1059_, lean_object* v_ps_1060_){
_start:
{
lean_object* v_importedEntries_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1068_; 
v_importedEntries_1061_ = lean_ctor_get(v_ps_1060_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v_ps_1060_);
if (v_isSharedCheck_1068_ == 0)
{
lean_object* v_unused_1069_; 
v_unused_1069_ = lean_ctor_get(v_ps_1060_, 1);
lean_dec(v_unused_1069_);
v___x_1063_ = v_ps_1060_;
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_importedEntries_1061_);
lean_dec(v_ps_1060_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1066_; 
if (v_isShared_1064_ == 0)
{
lean_ctor_set(v___x_1063_, 1, v_package_x3f_1059_);
v___x_1066_ = v___x_1063_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_importedEntries_1061_);
lean_ctor_set(v_reuseFailAlloc_1067_, 1, v_package_x3f_1059_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_processHeaderCore(lean_object* v_startPos_1070_, lean_object* v_imports_1071_, uint8_t v_isModule_1072_, lean_object* v_opts_1073_, lean_object* v_messages_1074_, lean_object* v_inputCtx_1075_, uint32_t v_trustLevel_1076_, lean_object* v_plugins_1077_, uint8_t v_leakEnv_1078_, lean_object* v_mainModule_1079_, lean_object* v_package_x3f_1080_, lean_object* v_arts_1081_, lean_object* v_headerStx_x3f_1082_, lean_object* v_origHeaderStx_x3f_1083_){
_start:
{
lean_object* v___y_1086_; lean_object* v___y_1087_; lean_object* v___f_1092_; lean_object* v_fst_1094_; lean_object* v_snd_1095_; uint8_t v___x_1106_; uint8_t v___y_1108_; 
v___f_1092_ = lean_alloc_closure((void*)(l_Lean_Elab_processHeaderCore___lam__0), 2, 1);
lean_closure_set(v___f_1092_, 0, v_package_x3f_1080_);
v___x_1106_ = 1;
if (v_isModule_1072_ == 0)
{
uint8_t v___x_1141_; 
v___x_1141_ = 2;
v___y_1108_ = v___x_1141_;
goto v___jp_1107_;
}
else
{
lean_object* v___x_1142_; uint8_t v___x_1143_; 
v___x_1142_ = l_Lean_Elab_inServer;
v___x_1143_ = l_Lean_Option_get___at___00Lean_Elab_checkDeprecatedImports_spec__0(v_opts_1073_, v___x_1142_);
if (v___x_1143_ == 0)
{
uint8_t v___x_1144_; 
v___x_1144_ = 0;
v___y_1108_ = v___x_1144_;
goto v___jp_1107_;
}
else
{
uint8_t v___x_1145_; 
v___x_1145_ = 1;
v___y_1108_ = v___x_1145_;
goto v___jp_1107_;
}
}
v___jp_1085_:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
lean_inc(v_startPos_1070_);
lean_inc_ref(v_inputCtx_1075_);
v___x_1088_ = l_Lean_Elab_checkDeprecatedImports(v___y_1087_, v_imports_1071_, v_opts_1073_, v_inputCtx_1075_, v_startPos_1070_, v___y_1086_, v_headerStx_x3f_1082_, v_origHeaderStx_x3f_1083_);
lean_dec_ref(v_imports_1071_);
lean_inc(v_mainModule_1079_);
v___x_1089_ = l___private_Lean_Elab_Import_0__Lean_Elab_checkModuleNamePortability_go(v_mainModule_1079_, v_inputCtx_1075_, v_startPos_1070_, v_mainModule_1079_, v___x_1088_);
lean_dec(v_startPos_1070_);
v___x_1090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1090_, 0, v___y_1087_);
lean_ctor_set(v___x_1090_, 1, v___x_1089_);
v___x_1091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1090_);
return v___x_1091_;
}
v___jp_1093_:
{
lean_object* v___x_1096_; lean_object* v_toEnvExtension_1097_; lean_object* v_asyncMode_1098_; uint8_t v_logWrites_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; uint8_t v___x_1102_; 
v___x_1096_ = l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
v_toEnvExtension_1097_ = lean_ctor_get(v___x_1096_, 0);
v_asyncMode_1098_ = lean_ctor_get(v_toEnvExtension_1097_, 2);
v_logWrites_1099_ = lean_ctor_get_uint8(v_toEnvExtension_1097_, sizeof(void*)*6);
lean_inc(v_mainModule_1079_);
v___x_1100_ = l_Lean_Environment_setMainModule(v_fst_1094_, v_mainModule_1079_);
v___x_1101_ = lean_box(0);
v___x_1102_ = 1;
if (v_logWrites_1099_ == 0)
{
lean_object* v___x_1103_; 
lean_inc_ref(v_toEnvExtension_1097_);
v___x_1103_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1097_, v___x_1100_, v___f_1092_, v_asyncMode_1098_, v___x_1101_, v___x_1102_);
v___y_1086_ = v_snd_1095_;
v___y_1087_ = v___x_1103_;
goto v___jp_1085_;
}
else
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
lean_inc_ref_n(v_toEnvExtension_1097_, 2);
v___x_1104_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1097_, v___x_1100_);
lean_dec_ref(v___x_1100_);
v___x_1105_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1097_, v___x_1104_, v___f_1092_, v_asyncMode_1098_, v___x_1101_, v___x_1102_);
v___y_1086_ = v_snd_1095_;
v___y_1087_ = v___x_1105_;
goto v___jp_1085_;
}
}
v___jp_1107_:
{
lean_object* v___x_1109_; 
lean_inc_ref(v_opts_1073_);
lean_inc_ref(v_imports_1071_);
v___x_1109_ = l_Lean_importModules(v_imports_1071_, v_opts_1073_, v_trustLevel_1076_, v_plugins_1077_, v_leakEnv_1078_, v___x_1106_, v___y_1108_, v_arts_1081_);
if (lean_obj_tag(v___x_1109_) == 0)
{
lean_object* v_a_1110_; 
v_a_1110_ = lean_ctor_get(v___x_1109_, 0);
lean_inc(v_a_1110_);
lean_dec_ref_known(v___x_1109_, 1);
v_fst_1094_ = v_a_1110_;
v_snd_1095_ = v_messages_1074_;
goto v___jp_1093_;
}
else
{
lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1140_; 
v_a_1111_ = lean_ctor_get(v___x_1109_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1109_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1113_ = v___x_1109_;
v_isShared_1114_ = v_isSharedCheck_1140_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_a_1111_);
lean_dec(v___x_1109_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1140_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
uint32_t v___x_1115_; lean_object* v___x_1116_; 
v___x_1115_ = 0;
v___x_1116_ = l_Lean_mkEmptyEnvironment(v___x_1115_);
if (lean_obj_tag(v___x_1116_) == 0)
{
lean_object* v_a_1117_; lean_object* v_fileName_1118_; lean_object* v_fileMap_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; uint8_t v___x_1122_; uint8_t v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1127_; 
v_a_1117_ = lean_ctor_get(v___x_1116_, 0);
lean_inc(v_a_1117_);
lean_dec_ref_known(v___x_1116_, 1);
v_fileName_1118_ = lean_ctor_get(v_inputCtx_1075_, 1);
v_fileMap_1119_ = lean_ctor_get(v_inputCtx_1075_, 2);
lean_inc_ref(v_fileMap_1119_);
v___x_1120_ = l_Lean_FileMap_toPosition(v_fileMap_1119_, v_startPos_1070_);
v___x_1121_ = lean_box(0);
v___x_1122_ = 0;
v___x_1123_ = 2;
v___x_1124_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___closed__0));
v___x_1125_ = lean_io_error_to_string(v_a_1111_);
if (v_isShared_1114_ == 0)
{
lean_ctor_set_tag(v___x_1113_, 3);
lean_ctor_set(v___x_1113_, 0, v___x_1125_);
v___x_1127_ = v___x_1113_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v___x_1125_);
v___x_1127_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1128_ = l_Lean_MessageData_ofFormat(v___x_1127_);
lean_inc_ref(v_fileName_1118_);
v___x_1129_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1129_, 0, v_fileName_1118_);
lean_ctor_set(v___x_1129_, 1, v___x_1120_);
lean_ctor_set(v___x_1129_, 2, v___x_1121_);
lean_ctor_set(v___x_1129_, 3, v___x_1124_);
lean_ctor_set(v___x_1129_, 4, v___x_1128_);
lean_ctor_set_uint8(v___x_1129_, sizeof(void*)*5, v___x_1122_);
lean_ctor_set_uint8(v___x_1129_, sizeof(void*)*5 + 1, v___x_1123_);
lean_ctor_set_uint8(v___x_1129_, sizeof(void*)*5 + 2, v___x_1122_);
v___x_1130_ = l_Lean_MessageLog_add(v___x_1129_, v_messages_1074_);
v_fst_1094_ = v_a_1117_;
v_snd_1095_ = v___x_1130_;
goto v___jp_1093_;
}
}
else
{
lean_object* v_a_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1139_; 
lean_del_object(v___x_1113_);
lean_dec(v_a_1111_);
lean_dec_ref(v___f_1092_);
lean_dec(v_origHeaderStx_x3f_1083_);
lean_dec(v_headerStx_x3f_1082_);
lean_dec(v_mainModule_1079_);
lean_dec_ref(v_inputCtx_1075_);
lean_dec_ref(v_messages_1074_);
lean_dec_ref(v_opts_1073_);
lean_dec_ref(v_imports_1071_);
lean_dec(v_startPos_1070_);
v_a_1132_ = lean_ctor_get(v___x_1116_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v___x_1116_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1134_ = v___x_1116_;
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_a_1132_);
lean_dec(v___x_1116_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1137_; 
if (v_isShared_1135_ == 0)
{
v___x_1137_ = v___x_1134_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_a_1132_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_processHeaderCore___boxed(lean_object* v_startPos_1146_, lean_object* v_imports_1147_, lean_object* v_isModule_1148_, lean_object* v_opts_1149_, lean_object* v_messages_1150_, lean_object* v_inputCtx_1151_, lean_object* v_trustLevel_1152_, lean_object* v_plugins_1153_, lean_object* v_leakEnv_1154_, lean_object* v_mainModule_1155_, lean_object* v_package_x3f_1156_, lean_object* v_arts_1157_, lean_object* v_headerStx_x3f_1158_, lean_object* v_origHeaderStx_x3f_1159_, lean_object* v_a_1160_){
_start:
{
uint8_t v_isModule_boxed_1161_; uint32_t v_trustLevel_boxed_1162_; uint8_t v_leakEnv_boxed_1163_; lean_object* v_res_1164_; 
v_isModule_boxed_1161_ = lean_unbox(v_isModule_1148_);
v_trustLevel_boxed_1162_ = lean_unbox_uint32(v_trustLevel_1152_);
lean_dec(v_trustLevel_1152_);
v_leakEnv_boxed_1163_ = lean_unbox(v_leakEnv_1154_);
v_res_1164_ = l_Lean_Elab_processHeaderCore(v_startPos_1146_, v_imports_1147_, v_isModule_boxed_1161_, v_opts_1149_, v_messages_1150_, v_inputCtx_1151_, v_trustLevel_boxed_1162_, v_plugins_1153_, v_leakEnv_boxed_1163_, v_mainModule_1155_, v_package_x3f_1156_, v_arts_1157_, v_headerStx_x3f_1158_, v_origHeaderStx_x3f_1159_);
return v_res_1164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_processHeader(lean_object* v_header_1165_, lean_object* v_opts_1166_, lean_object* v_messages_1167_, lean_object* v_inputCtx_1168_, uint32_t v_trustLevel_1169_, lean_object* v_plugins_1170_, uint8_t v_leakEnv_1171_, lean_object* v_mainModule_1172_){
_start:
{
lean_object* v___x_1174_; uint8_t v___x_1175_; lean_object* v___x_1176_; uint8_t v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1174_ = l_Lean_Elab_HeaderSyntax_startPos(v_header_1165_);
v___x_1175_ = 1;
lean_inc(v_header_1165_);
v___x_1176_ = l_Lean_Elab_HeaderSyntax_imports(v_header_1165_, v___x_1175_);
v___x_1177_ = l_Lean_Elab_HeaderSyntax_isModule(v_header_1165_);
v___x_1178_ = lean_box(0);
v___x_1179_ = lean_box(1);
v___x_1180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1180_, 0, v_header_1165_);
v___x_1181_ = l_Lean_Elab_processHeaderCore(v___x_1174_, v___x_1176_, v___x_1177_, v_opts_1166_, v_messages_1167_, v_inputCtx_1168_, v_trustLevel_1169_, v_plugins_1170_, v_leakEnv_1171_, v_mainModule_1172_, v___x_1178_, v___x_1179_, v___x_1180_, v___x_1178_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_processHeader___boxed(lean_object* v_header_1182_, lean_object* v_opts_1183_, lean_object* v_messages_1184_, lean_object* v_inputCtx_1185_, lean_object* v_trustLevel_1186_, lean_object* v_plugins_1187_, lean_object* v_leakEnv_1188_, lean_object* v_mainModule_1189_, lean_object* v_a_1190_){
_start:
{
uint32_t v_trustLevel_boxed_1191_; uint8_t v_leakEnv_boxed_1192_; lean_object* v_res_1193_; 
v_trustLevel_boxed_1191_ = lean_unbox_uint32(v_trustLevel_1186_);
lean_dec(v_trustLevel_1186_);
v_leakEnv_boxed_1192_ = lean_unbox(v_leakEnv_1188_);
v_res_1193_ = l_Lean_Elab_processHeader(v_header_1182_, v_opts_1183_, v_messages_1184_, v_inputCtx_1185_, v_trustLevel_boxed_1191_, v_plugins_1187_, v_leakEnv_boxed_1192_, v_mainModule_1189_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_parseImports(lean_object* v_input_1195_, lean_object* v_fileName_1196_){
_start:
{
lean_object* v___y_1199_; 
if (lean_obj_tag(v_fileName_1196_) == 0)
{
lean_object* v___x_1244_; 
v___x_1244_ = ((lean_object*)(l_Lean_Elab_parseImports___closed__0));
v___y_1199_ = v___x_1244_;
goto v___jp_1198_;
}
else
{
lean_object* v_val_1245_; 
v_val_1245_ = lean_ctor_get(v_fileName_1196_, 0);
lean_inc(v_val_1245_);
lean_dec_ref_known(v_fileName_1196_, 1);
v___y_1199_ = v_val_1245_;
goto v___jp_1198_;
}
v___jp_1198_:
{
uint8_t v___x_1200_; lean_object* v___x_1201_; lean_object* v_inputCtx_1202_; lean_object* v___x_1203_; 
v___x_1200_ = 1;
v___x_1201_ = lean_string_utf8_byte_size(v_input_1195_);
v_inputCtx_1202_ = l_Lean_Parser_mkInputContext___redArg(v_input_1195_, v___y_1199_, v___x_1200_, v___x_1201_);
lean_inc_ref(v_inputCtx_1202_);
v___x_1203_ = l_Lean_Parser_parseHeader(v_inputCtx_1202_);
if (lean_obj_tag(v___x_1203_) == 0)
{
lean_object* v_a_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1235_; 
v_a_1204_ = lean_ctor_get(v___x_1203_, 0);
v_isSharedCheck_1235_ = !lean_is_exclusive(v___x_1203_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1206_ = v___x_1203_;
v_isShared_1207_ = v_isSharedCheck_1235_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_a_1204_);
lean_dec(v___x_1203_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1235_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v_snd_1208_; lean_object* v_fst_1209_; lean_object* v_fst_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1233_; 
v_snd_1208_ = lean_ctor_get(v_a_1204_, 1);
lean_inc(v_snd_1208_);
v_fst_1209_ = lean_ctor_get(v_snd_1208_, 0);
lean_inc(v_fst_1209_);
v_fst_1210_ = lean_ctor_get(v_a_1204_, 0);
v_isSharedCheck_1233_ = !lean_is_exclusive(v_a_1204_);
if (v_isSharedCheck_1233_ == 0)
{
lean_object* v_unused_1234_; 
v_unused_1234_ = lean_ctor_get(v_a_1204_, 1);
lean_dec(v_unused_1234_);
v___x_1212_ = v_a_1204_;
v_isShared_1213_ = v_isSharedCheck_1233_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_fst_1210_);
lean_dec(v_a_1204_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1233_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v_snd_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1231_; 
v_snd_1214_ = lean_ctor_get(v_snd_1208_, 1);
v_isSharedCheck_1231_ = !lean_is_exclusive(v_snd_1208_);
if (v_isSharedCheck_1231_ == 0)
{
lean_object* v_unused_1232_; 
v_unused_1232_ = lean_ctor_get(v_snd_1208_, 0);
lean_dec(v_unused_1232_);
v___x_1216_ = v_snd_1208_;
v_isShared_1217_ = v_isSharedCheck_1231_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_snd_1214_);
lean_dec(v_snd_1208_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1231_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v_fileMap_1218_; lean_object* v_pos_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1223_; 
v_fileMap_1218_ = lean_ctor_get(v_inputCtx_1202_, 2);
lean_inc_ref(v_fileMap_1218_);
lean_dec_ref(v_inputCtx_1202_);
v_pos_1219_ = lean_ctor_get(v_fst_1209_, 0);
lean_inc(v_pos_1219_);
lean_dec(v_fst_1209_);
v___x_1220_ = l_Lean_Elab_HeaderSyntax_imports(v_fst_1210_, v___x_1200_);
v___x_1221_ = l_Lean_FileMap_toPosition(v_fileMap_1218_, v_pos_1219_);
lean_dec(v_pos_1219_);
if (v_isShared_1217_ == 0)
{
lean_ctor_set(v___x_1216_, 0, v___x_1221_);
v___x_1223_ = v___x_1216_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v___x_1221_);
lean_ctor_set(v_reuseFailAlloc_1230_, 1, v_snd_1214_);
v___x_1223_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
lean_object* v___x_1225_; 
if (v_isShared_1213_ == 0)
{
lean_ctor_set(v___x_1212_, 1, v___x_1223_);
lean_ctor_set(v___x_1212_, 0, v___x_1220_);
v___x_1225_ = v___x_1212_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v___x_1220_);
lean_ctor_set(v_reuseFailAlloc_1229_, 1, v___x_1223_);
v___x_1225_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
lean_object* v___x_1227_; 
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 0, v___x_1225_);
v___x_1227_ = v___x_1206_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v___x_1225_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1243_; 
lean_dec_ref(v_inputCtx_1202_);
v_a_1236_ = lean_ctor_get(v___x_1203_, 0);
v_isSharedCheck_1243_ = !lean_is_exclusive(v___x_1203_);
if (v_isSharedCheck_1243_ == 0)
{
v___x_1238_ = v___x_1203_;
v_isShared_1239_ = v_isSharedCheck_1243_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_a_1236_);
lean_dec(v___x_1203_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1243_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v___x_1241_; 
if (v_isShared_1239_ == 0)
{
v___x_1241_ = v___x_1238_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v_a_1236_);
v___x_1241_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
return v___x_1241_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_parseImports___boxed(lean_object* v_input_1246_, lean_object* v_fileName_1247_, lean_object* v_a_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l_Lean_Elab_parseImports(v_input_1246_, v_fileName_1247_);
return v_res_1249_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00Lean_Elab_printImports_spec__0_spec__0(lean_object* v_s_1250_){
_start:
{
lean_object* v___x_1252_; lean_object* v_putStr_1253_; lean_object* v___x_1254_; 
v___x_1252_ = lean_get_stdout();
v_putStr_1253_ = lean_ctor_get(v___x_1252_, 4);
lean_inc_ref(v_putStr_1253_);
lean_dec_ref(v___x_1252_);
v___x_1254_ = lean_apply_2(v_putStr_1253_, v_s_1250_, lean_box(0));
return v___x_1254_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00Lean_Elab_printImports_spec__0_spec__0___boxed(lean_object* v_s_1255_, lean_object* v_a_1256_){
_start:
{
lean_object* v_res_1257_; 
v_res_1257_ = l_IO_print___at___00IO_println___at___00Lean_Elab_printImports_spec__0_spec__0(v_s_1255_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00Lean_Elab_printImports_spec__0(lean_object* v_s_1258_){
_start:
{
uint32_t v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1260_ = 10;
v___x_1261_ = lean_string_push(v_s_1258_, v___x_1260_);
v___x_1262_ = l_IO_print___at___00IO_println___at___00Lean_Elab_printImports_spec__0_spec__0(v___x_1261_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00Lean_Elab_printImports_spec__0___boxed(lean_object* v_s_1263_, lean_object* v_a_1264_){
_start:
{
lean_object* v_res_1265_; 
v_res_1265_ = l_IO_println___at___00Lean_Elab_printImports_spec__0(v_s_1263_);
return v_res_1265_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImports_spec__1(lean_object* v_as_1266_, size_t v_sz_1267_, size_t v_i_1268_, lean_object* v_b_1269_){
_start:
{
uint8_t v___x_1271_; 
v___x_1271_ = lean_usize_dec_lt(v_i_1268_, v_sz_1267_);
if (v___x_1271_ == 0)
{
lean_object* v___x_1272_; 
v___x_1272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1272_, 0, v_b_1269_);
return v___x_1272_;
}
else
{
lean_object* v_a_1273_; lean_object* v_module_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
v_a_1273_ = lean_array_uget_borrowed(v_as_1266_, v_i_1268_);
v_module_1274_ = lean_ctor_get(v_a_1273_, 0);
v___x_1275_ = lean_box(0);
lean_inc(v_module_1274_);
v___x_1276_ = l_Lean_findOLean(v_module_1274_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v_a_1277_; lean_object* v___x_1278_; 
v_a_1277_ = lean_ctor_get(v___x_1276_, 0);
lean_inc(v_a_1277_);
lean_dec_ref_known(v___x_1276_, 1);
v___x_1278_ = l_IO_println___at___00Lean_Elab_printImports_spec__0(v_a_1277_);
if (lean_obj_tag(v___x_1278_) == 0)
{
size_t v___x_1279_; size_t v___x_1280_; 
lean_dec_ref_known(v___x_1278_, 1);
v___x_1279_ = ((size_t)1ULL);
v___x_1280_ = lean_usize_add(v_i_1268_, v___x_1279_);
v_i_1268_ = v___x_1280_;
v_b_1269_ = v___x_1275_;
goto _start;
}
else
{
return v___x_1278_;
}
}
else
{
lean_object* v_a_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1289_; 
v_a_1282_ = lean_ctor_get(v___x_1276_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1284_ = v___x_1276_;
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_a_1282_);
lean_dec(v___x_1276_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___x_1287_; 
if (v_isShared_1285_ == 0)
{
v___x_1287_ = v___x_1284_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_a_1282_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
return v___x_1287_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImports_spec__1___boxed(lean_object* v_as_1290_, lean_object* v_sz_1291_, lean_object* v_i_1292_, lean_object* v_b_1293_, lean_object* v___y_1294_){
_start:
{
size_t v_sz_boxed_1295_; size_t v_i_boxed_1296_; lean_object* v_res_1297_; 
v_sz_boxed_1295_ = lean_unbox_usize(v_sz_1291_);
lean_dec(v_sz_1291_);
v_i_boxed_1296_ = lean_unbox_usize(v_i_1292_);
lean_dec(v_i_1292_);
v_res_1297_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImports_spec__1(v_as_1290_, v_sz_boxed_1295_, v_i_boxed_1296_, v_b_1293_);
lean_dec_ref(v_as_1290_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_printImports(lean_object* v_input_1298_, lean_object* v_fileName_1299_){
_start:
{
lean_object* v___x_1301_; 
v___x_1301_ = l_Lean_Elab_parseImports(v_input_1298_, v_fileName_1299_);
if (lean_obj_tag(v___x_1301_) == 0)
{
lean_object* v_a_1302_; lean_object* v_fst_1303_; lean_object* v___x_1304_; size_t v_sz_1305_; size_t v___x_1306_; lean_object* v___x_1307_; 
v_a_1302_ = lean_ctor_get(v___x_1301_, 0);
lean_inc(v_a_1302_);
lean_dec_ref_known(v___x_1301_, 1);
v_fst_1303_ = lean_ctor_get(v_a_1302_, 0);
lean_inc(v_fst_1303_);
lean_dec(v_a_1302_);
v___x_1304_ = lean_box(0);
v_sz_1305_ = lean_array_size(v_fst_1303_);
v___x_1306_ = ((size_t)0ULL);
v___x_1307_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImports_spec__1(v_fst_1303_, v_sz_1305_, v___x_1306_, v___x_1304_);
lean_dec(v_fst_1303_);
if (lean_obj_tag(v___x_1307_) == 0)
{
lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1314_; 
v_isSharedCheck_1314_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1314_ == 0)
{
lean_object* v_unused_1315_; 
v_unused_1315_ = lean_ctor_get(v___x_1307_, 0);
lean_dec(v_unused_1315_);
v___x_1309_ = v___x_1307_;
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
else
{
lean_dec(v___x_1307_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1312_; 
if (v_isShared_1310_ == 0)
{
lean_ctor_set(v___x_1309_, 0, v___x_1304_);
v___x_1312_ = v___x_1309_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v___x_1304_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
return v___x_1312_;
}
}
}
else
{
return v___x_1307_;
}
}
else
{
lean_object* v_a_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1323_; 
v_a_1316_ = lean_ctor_get(v___x_1301_, 0);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1301_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1318_ = v___x_1301_;
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_a_1316_);
lean_dec(v___x_1301_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1321_; 
if (v_isShared_1319_ == 0)
{
v___x_1321_ = v___x_1318_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_a_1316_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
return v___x_1321_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_printImports___boxed(lean_object* v_input_1324_, lean_object* v_fileName_1325_, lean_object* v_a_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = l_Lean_Elab_printImports(v_input_1324_, v_fileName_1325_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImportSrcs_spec__0(lean_object* v_a_1328_, lean_object* v_as_1329_, size_t v_sz_1330_, size_t v_i_1331_, lean_object* v_b_1332_){
_start:
{
uint8_t v___x_1334_; 
v___x_1334_ = lean_usize_dec_lt(v_i_1331_, v_sz_1330_);
if (v___x_1334_ == 0)
{
lean_object* v___x_1335_; 
lean_dec(v_a_1328_);
v___x_1335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1335_, 0, v_b_1332_);
return v___x_1335_;
}
else
{
lean_object* v_a_1336_; lean_object* v_module_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; 
v_a_1336_ = lean_array_uget_borrowed(v_as_1329_, v_i_1331_);
v_module_1337_ = lean_ctor_get(v_a_1336_, 0);
v___x_1338_ = lean_box(0);
lean_inc(v_module_1337_);
lean_inc(v_a_1328_);
v___x_1339_ = l_Lean_findLean(v_a_1328_, v_module_1337_);
if (lean_obj_tag(v___x_1339_) == 0)
{
lean_object* v_a_1340_; lean_object* v___x_1341_; 
v_a_1340_ = lean_ctor_get(v___x_1339_, 0);
lean_inc(v_a_1340_);
lean_dec_ref_known(v___x_1339_, 1);
v___x_1341_ = l_IO_println___at___00Lean_Elab_printImports_spec__0(v_a_1340_);
if (lean_obj_tag(v___x_1341_) == 0)
{
size_t v___x_1342_; size_t v___x_1343_; 
lean_dec_ref_known(v___x_1341_, 1);
v___x_1342_ = ((size_t)1ULL);
v___x_1343_ = lean_usize_add(v_i_1331_, v___x_1342_);
v_i_1331_ = v___x_1343_;
v_b_1332_ = v___x_1338_;
goto _start;
}
else
{
lean_dec(v_a_1328_);
return v___x_1341_;
}
}
else
{
lean_object* v_a_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1352_; 
lean_dec(v_a_1328_);
v_a_1345_ = lean_ctor_get(v___x_1339_, 0);
v_isSharedCheck_1352_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1347_ = v___x_1339_;
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_a_1345_);
lean_dec(v___x_1339_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___x_1350_; 
if (v_isShared_1348_ == 0)
{
v___x_1350_ = v___x_1347_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v_a_1345_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
return v___x_1350_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImportSrcs_spec__0___boxed(lean_object* v_a_1353_, lean_object* v_as_1354_, lean_object* v_sz_1355_, lean_object* v_i_1356_, lean_object* v_b_1357_, lean_object* v___y_1358_){
_start:
{
size_t v_sz_boxed_1359_; size_t v_i_boxed_1360_; lean_object* v_res_1361_; 
v_sz_boxed_1359_ = lean_unbox_usize(v_sz_1355_);
lean_dec(v_sz_1355_);
v_i_boxed_1360_ = lean_unbox_usize(v_i_1356_);
lean_dec(v_i_1356_);
v_res_1361_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImportSrcs_spec__0(v_a_1353_, v_as_1354_, v_sz_boxed_1359_, v_i_boxed_1360_, v_b_1357_);
lean_dec_ref(v_as_1354_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_printImportSrcs(lean_object* v_input_1362_, lean_object* v_fileName_1363_){
_start:
{
lean_object* v___x_1365_; 
v___x_1365_ = l_Lean_getSrcSearchPath();
if (lean_obj_tag(v___x_1365_) == 0)
{
lean_object* v_a_1366_; lean_object* v___x_1367_; 
v_a_1366_ = lean_ctor_get(v___x_1365_, 0);
lean_inc(v_a_1366_);
lean_dec_ref_known(v___x_1365_, 1);
v___x_1367_ = l_Lean_Elab_parseImports(v_input_1362_, v_fileName_1363_);
if (lean_obj_tag(v___x_1367_) == 0)
{
lean_object* v_a_1368_; lean_object* v_fst_1369_; lean_object* v___x_1370_; size_t v_sz_1371_; size_t v___x_1372_; lean_object* v___x_1373_; 
v_a_1368_ = lean_ctor_get(v___x_1367_, 0);
lean_inc(v_a_1368_);
lean_dec_ref_known(v___x_1367_, 1);
v_fst_1369_ = lean_ctor_get(v_a_1368_, 0);
lean_inc(v_fst_1369_);
lean_dec(v_a_1368_);
v___x_1370_ = lean_box(0);
v_sz_1371_ = lean_array_size(v_fst_1369_);
v___x_1372_ = ((size_t)0ULL);
v___x_1373_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImportSrcs_spec__0(v_a_1366_, v_fst_1369_, v_sz_1371_, v___x_1372_, v___x_1370_);
lean_dec(v_fst_1369_);
if (lean_obj_tag(v___x_1373_) == 0)
{
lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1380_; 
v_isSharedCheck_1380_ = !lean_is_exclusive(v___x_1373_);
if (v_isSharedCheck_1380_ == 0)
{
lean_object* v_unused_1381_; 
v_unused_1381_ = lean_ctor_get(v___x_1373_, 0);
lean_dec(v_unused_1381_);
v___x_1375_ = v___x_1373_;
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
else
{
lean_dec(v___x_1373_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1378_; 
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 0, v___x_1370_);
v___x_1378_ = v___x_1375_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v___x_1370_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
return v___x_1378_;
}
}
}
else
{
return v___x_1373_;
}
}
else
{
lean_object* v_a_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1389_; 
lean_dec(v_a_1366_);
v_a_1382_ = lean_ctor_get(v___x_1367_, 0);
v_isSharedCheck_1389_ = !lean_is_exclusive(v___x_1367_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1384_ = v___x_1367_;
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_a_1382_);
lean_dec(v___x_1367_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1387_; 
if (v_isShared_1385_ == 0)
{
v___x_1387_ = v___x_1384_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v_a_1382_);
v___x_1387_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
return v___x_1387_;
}
}
}
}
else
{
lean_object* v_a_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1397_; 
lean_dec(v_fileName_1363_);
lean_dec_ref(v_input_1362_);
v_a_1390_ = lean_ctor_get(v___x_1365_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1392_ = v___x_1365_;
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_a_1390_);
lean_dec(v___x_1365_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1395_; 
if (v_isShared_1393_ == 0)
{
v___x_1395_ = v___x_1392_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v_a_1390_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_printImportSrcs___boxed(lean_object* v_input_1398_, lean_object* v_fileName_1399_, lean_object* v_a_1400_){
_start:
{
lean_object* v_res_1401_; 
v_res_1401_ = l_Lean_Elab_printImportSrcs(v_input_1398_, v_fileName_1399_);
return v_res_1401_;
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

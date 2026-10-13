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
lean_object* v___x_66_; lean_object* v_v_67_; lean_object* v___x_68_; lean_object* v_bs_x27_69_; lean_object* v___y_71_; lean_object* v___y_77_; lean_object* v___y_78_; uint8_t v___y_79_; uint8_t v___y_80_; uint8_t v___y_81_; lean_object* v___y_86_; lean_object* v___y_87_; uint8_t v___y_88_; uint8_t v___y_89_; uint8_t v___y_90_; lean_object* v___y_92_; lean_object* v___y_93_; lean_object* v___y_94_; uint8_t v___y_95_; uint8_t v___y_96_; uint8_t v___x_98_; 
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
v___y_92_ = v___x_112_;
v___y_93_ = v___y_102_;
v___y_94_ = v___y_103_;
v___y_95_ = v___x_107_;
v___y_96_ = v___x_113_;
goto v___jp_91_;
}
else
{
lean_dec_ref_known(v_allTk_104_, 1);
v___y_92_ = v___x_112_;
v___y_93_ = v___y_102_;
v___y_94_ = v___y_103_;
v___y_95_ = v___x_107_;
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
if (lean_obj_tag(v___y_78_) == 0)
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
lean_dec_ref_known(v___y_78_, 1);
v___x_84_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_84_, 0, v___y_77_);
lean_ctor_set_uint8(v___x_84_, sizeof(void*)*1, v___y_79_);
lean_ctor_set_uint8(v___x_84_, sizeof(void*)*1 + 1, v___y_81_);
lean_ctor_set_uint8(v___x_84_, sizeof(void*)*1 + 2, v___y_80_);
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
v___y_81_ = v___y_89_;
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
if (lean_obj_tag(v___y_94_) == 0)
{
uint8_t v___x_97_; 
v___x_97_ = 0;
v___y_86_ = v___y_92_;
v___y_87_ = v___y_93_;
v___y_88_ = v___y_96_;
v___y_89_ = v___y_95_;
v___y_90_ = v___x_97_;
goto v___jp_85_;
}
else
{
lean_dec_ref_known(v___y_94_, 1);
if (v___y_95_ == 0)
{
v___y_86_ = v___y_92_;
v___y_87_ = v___y_93_;
v___y_88_ = v___y_96_;
v___y_89_ = v___y_95_;
v___y_90_ = v___y_95_;
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
uint8_t v___x_1475__boxed_165_; size_t v_sz_boxed_166_; size_t v_i_boxed_167_; lean_object* v_res_168_; 
v___x_1475__boxed_165_ = lean_unbox(v___x_161_);
v_sz_boxed_166_ = lean_unbox_usize(v_sz_162_);
lean_dec(v_sz_162_);
v_i_boxed_167_ = lean_unbox_usize(v_i_163_);
lean_dec(v_i_163_);
v_res_168_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2(v_moduleTk_160_, v___x_1475__boxed_165_, v_sz_boxed_166_, v_i_boxed_167_, v_bs_164_);
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
v___y_214_ = v_importsStx_222_;
v___y_215_ = v___y_218_;
goto v___jp_213_;
}
else
{
if (v_includeInit_199_ == 0)
{
v___y_214_ = v_importsStx_222_;
v___y_215_ = v___y_218_;
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
v___y_203_ = v_importsStx_222_;
v___y_204_ = v___y_218_;
v___y_205_ = v___x_229_;
goto v___jp_202_;
}
}
}
else
{
lean_dec_ref_known(v_preludeTk_219_, 1);
v___y_214_ = v_importsStx_222_;
v___y_215_ = v___y_218_;
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
v_sz_206_ = lean_array_size(v___y_203_);
v___x_207_ = ((size_t)0ULL);
v___x_208_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2(v___y_204_, v___x_201_, v_sz_206_, v___x_207_, v___y_203_);
lean_dec(v___y_204_);
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
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__2(void){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = ((lean_object*)(l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__1));
v___x_385_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_384_);
return v___x_385_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__3(void){
_start:
{
lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_386_ = lean_unsigned_to_nat(0u);
v___x_387_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__2, &l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__2_once, _init_l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__2);
v___x_388_ = ((lean_object*)(l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__1));
v___x_389_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_389_, 0, v___x_388_);
lean_ctor_set(v___x_389_, 1, v___x_387_);
lean_ctor_set(v___x_389_, 2, v___x_386_);
lean_ctor_set(v___x_389_, 3, v___x_386_);
return v___x_389_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2(lean_object* v_s_390_){
_start:
{
lean_object* v___x_391_; uint8_t v___x_392_; uint8_t v___x_393_; 
v___x_391_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__3, &l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__3_once, _init_l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__3);
v___x_392_ = 0;
v___x_393_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_spec__2___redArg(v_s_390_, v___x_391_, v___x_392_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___boxed(lean_object* v_s_394_){
_start:
{
uint8_t v_res_395_; lean_object* v_r_396_; 
v_res_395_ = l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2(v_s_394_);
lean_dec_ref(v_s_394_);
v_r_396_ = lean_box(v_res_395_);
return v_r_396_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkDeprecatedImports_spec__3(lean_object* v_as_397_, size_t v_sz_398_, size_t v_i_399_, lean_object* v_b_400_){
_start:
{
lean_object* v_a_402_; uint8_t v___x_406_; 
v___x_406_ = lean_usize_dec_lt(v_i_399_, v_sz_398_);
if (v___x_406_ == 0)
{
return v_b_400_;
}
else
{
lean_object* v_fst_407_; lean_object* v_snd_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_483_; 
v_fst_407_ = lean_ctor_get(v_b_400_, 0);
v_snd_408_ = lean_ctor_get(v_b_400_, 1);
v_isSharedCheck_483_ = !lean_is_exclusive(v_b_400_);
if (v_isSharedCheck_483_ == 0)
{
v___x_410_ = v_b_400_;
v_isShared_411_ = v_isSharedCheck_483_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_snd_408_);
lean_inc(v_fst_407_);
lean_dec(v_b_400_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_483_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v___x_412_; lean_object* v_a_413_; lean_object* v___y_415_; lean_object* v_ignoreDeprecatedImports_416_; uint8_t v___x_428_; 
v___x_412_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__4));
v_a_413_ = lean_array_uget_borrowed(v_as_397_, v_i_399_);
lean_inc(v_a_413_);
v___x_428_ = l_Lean_Syntax_isOfKind(v_a_413_, v___x_412_);
if (v___x_428_ == 0)
{
lean_object* v___x_429_; 
lean_del_object(v___x_410_);
v___x_429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_429_, 0, v_fst_407_);
lean_ctor_set(v___x_429_, 1, v_snd_408_);
v_a_402_ = v___x_429_;
goto v___jp_401_;
}
else
{
lean_object* v___x_430_; lean_object* v___x_455_; lean_object* v___x_475_; uint8_t v___x_476_; 
v___x_430_ = lean_unsigned_to_nat(0u);
v___x_455_ = lean_unsigned_to_nat(1u);
v___x_475_ = l_Lean_Syntax_getArg(v_a_413_, v___x_430_);
v___x_476_ = l_Lean_Syntax_isNone(v___x_475_);
if (v___x_476_ == 0)
{
uint8_t v___x_477_; 
lean_inc(v___x_475_);
v___x_477_ = l_Lean_Syntax_matchesNull(v___x_475_, v___x_455_);
if (v___x_477_ == 0)
{
lean_object* v___x_478_; 
lean_dec(v___x_475_);
lean_del_object(v___x_410_);
v___x_478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_478_, 0, v_fst_407_);
lean_ctor_set(v___x_478_, 1, v_snd_408_);
v_a_402_ = v___x_478_;
goto v___jp_401_;
}
else
{
lean_object* v___x_479_; lean_object* v___x_480_; uint8_t v___x_481_; 
v___x_479_ = l_Lean_Syntax_getArg(v___x_475_, v___x_430_);
lean_dec(v___x_475_);
v___x_480_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__14));
v___x_481_ = l_Lean_Syntax_isOfKind(v___x_479_, v___x_480_);
if (v___x_481_ == 0)
{
lean_object* v___x_482_; 
lean_del_object(v___x_410_);
v___x_482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_482_, 0, v_fst_407_);
lean_ctor_set(v___x_482_, 1, v_snd_408_);
v_a_402_ = v___x_482_;
goto v___jp_401_;
}
else
{
goto v___jp_466_;
}
}
}
else
{
lean_dec(v___x_475_);
goto v___jp_466_;
}
v___jp_431_:
{
lean_object* v___x_432_; lean_object* v___x_433_; uint8_t v___x_434_; 
v___x_432_ = lean_unsigned_to_nat(5u);
v___x_433_ = l_Lean_Syntax_getArg(v_a_413_, v___x_432_);
v___x_434_ = l_Lean_Syntax_matchesNull(v___x_433_, v___x_430_);
if (v___x_434_ == 0)
{
lean_object* v___x_435_; 
lean_del_object(v___x_410_);
v___x_435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_435_, 0, v_fst_407_);
lean_ctor_set(v___x_435_, 1, v_snd_408_);
v_a_402_ = v___x_435_;
goto v___jp_401_;
}
else
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_436_ = lean_unsigned_to_nat(4u);
v___x_437_ = l_Lean_Syntax_getArg(v_a_413_, v___x_436_);
v___x_438_ = l_Lean_Syntax_getTrailing_x3f(v_a_413_);
if (lean_obj_tag(v___x_438_) == 0)
{
v___y_415_ = v___x_437_;
v_ignoreDeprecatedImports_416_ = v_fst_407_;
goto v___jp_414_;
}
else
{
lean_object* v_val_439_; lean_object* v_str_440_; lean_object* v_startPos_441_; lean_object* v_stopPos_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_454_; 
v_val_439_ = lean_ctor_get(v___x_438_, 0);
lean_inc(v_val_439_);
lean_dec_ref_known(v___x_438_, 1);
v_str_440_ = lean_ctor_get(v_val_439_, 0);
v_startPos_441_ = lean_ctor_get(v_val_439_, 1);
v_stopPos_442_ = lean_ctor_get(v_val_439_, 2);
v_isSharedCheck_454_ = !lean_is_exclusive(v_val_439_);
if (v_isSharedCheck_454_ == 0)
{
v___x_444_ = v_val_439_;
v_isShared_445_ = v_isSharedCheck_454_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_stopPos_442_);
lean_inc(v_startPos_441_);
lean_inc(v_str_440_);
lean_dec(v_val_439_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_454_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_449_; 
v___x_446_ = lean_string_utf8_extract(v_str_440_, v_startPos_441_, v_stopPos_442_);
lean_dec(v_stopPos_442_);
lean_dec(v_startPos_441_);
lean_dec_ref(v_str_440_);
v___x_447_ = lean_string_utf8_byte_size(v___x_446_);
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 2, v___x_447_);
lean_ctor_set(v___x_444_, 1, v___x_430_);
lean_ctor_set(v___x_444_, 0, v___x_446_);
v___x_449_ = v___x_444_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v___x_446_);
lean_ctor_set(v_reuseFailAlloc_453_, 1, v___x_430_);
lean_ctor_set(v_reuseFailAlloc_453_, 2, v___x_447_);
v___x_449_ = v_reuseFailAlloc_453_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
uint8_t v___x_450_; 
v___x_450_ = l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2(v___x_449_);
lean_dec_ref(v___x_449_);
if (v___x_450_ == 0)
{
v___y_415_ = v___x_437_;
v_ignoreDeprecatedImports_416_ = v_fst_407_;
goto v___jp_414_;
}
else
{
lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_451_ = l_Lean_TSyntax_getId(v___x_437_);
v___x_452_ = l_Lean_NameSet_insert(v_fst_407_, v___x_451_);
v___y_415_ = v___x_437_;
v_ignoreDeprecatedImports_416_ = v___x_452_;
goto v___jp_414_;
}
}
}
}
}
}
v___jp_456_:
{
lean_object* v___x_457_; lean_object* v___x_458_; uint8_t v___x_459_; 
v___x_457_ = lean_unsigned_to_nat(3u);
v___x_458_ = l_Lean_Syntax_getArg(v_a_413_, v___x_457_);
v___x_459_ = l_Lean_Syntax_isNone(v___x_458_);
if (v___x_459_ == 0)
{
uint8_t v___x_460_; 
lean_inc(v___x_458_);
v___x_460_ = l_Lean_Syntax_matchesNull(v___x_458_, v___x_455_);
if (v___x_460_ == 0)
{
lean_object* v___x_461_; 
lean_dec(v___x_458_);
lean_del_object(v___x_410_);
v___x_461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_461_, 0, v_fst_407_);
lean_ctor_set(v___x_461_, 1, v_snd_408_);
v_a_402_ = v___x_461_;
goto v___jp_401_;
}
else
{
lean_object* v___x_462_; lean_object* v___x_463_; uint8_t v___x_464_; 
v___x_462_ = l_Lean_Syntax_getArg(v___x_458_, v___x_430_);
lean_dec(v___x_458_);
v___x_463_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__10));
v___x_464_ = l_Lean_Syntax_isOfKind(v___x_462_, v___x_463_);
if (v___x_464_ == 0)
{
lean_object* v___x_465_; 
lean_del_object(v___x_410_);
v___x_465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_465_, 0, v_fst_407_);
lean_ctor_set(v___x_465_, 1, v_snd_408_);
v_a_402_ = v___x_465_;
goto v___jp_401_;
}
else
{
goto v___jp_431_;
}
}
}
else
{
lean_dec(v___x_458_);
goto v___jp_431_;
}
}
v___jp_466_:
{
lean_object* v___x_467_; uint8_t v___x_468_; 
v___x_467_ = l_Lean_Syntax_getArg(v_a_413_, v___x_455_);
v___x_468_ = l_Lean_Syntax_isNone(v___x_467_);
if (v___x_468_ == 0)
{
uint8_t v___x_469_; 
lean_inc(v___x_467_);
v___x_469_ = l_Lean_Syntax_matchesNull(v___x_467_, v___x_455_);
if (v___x_469_ == 0)
{
lean_object* v___x_470_; 
lean_dec(v___x_467_);
lean_del_object(v___x_410_);
v___x_470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_470_, 0, v_fst_407_);
lean_ctor_set(v___x_470_, 1, v_snd_408_);
v_a_402_ = v___x_470_;
goto v___jp_401_;
}
else
{
lean_object* v___x_471_; lean_object* v___x_472_; uint8_t v___x_473_; 
v___x_471_ = l_Lean_Syntax_getArg(v___x_467_, v___x_430_);
lean_dec(v___x_467_);
v___x_472_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__12));
v___x_473_ = l_Lean_Syntax_isOfKind(v___x_471_, v___x_472_);
if (v___x_473_ == 0)
{
lean_object* v___x_474_; 
lean_del_object(v___x_410_);
v___x_474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_474_, 0, v_fst_407_);
lean_ctor_set(v___x_474_, 1, v_snd_408_);
v_a_402_ = v___x_474_;
goto v___jp_401_;
}
else
{
goto v___jp_456_;
}
}
}
else
{
lean_dec(v___x_467_);
goto v___jp_456_;
}
}
}
v___jp_414_:
{
uint8_t v___x_417_; lean_object* v___x_418_; 
v___x_417_ = 0;
v___x_418_ = l_Lean_Syntax_getPos_x3f(v_a_413_, v___x_417_);
if (lean_obj_tag(v___x_418_) == 1)
{
lean_object* v_val_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_423_; 
v_val_419_ = lean_ctor_get(v___x_418_, 0);
lean_inc(v_val_419_);
lean_dec_ref_known(v___x_418_, 1);
v___x_420_ = l_Lean_TSyntax_getId(v___y_415_);
lean_dec(v___y_415_);
v___x_421_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_420_, v_val_419_, v_snd_408_);
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 1, v___x_421_);
lean_ctor_set(v___x_410_, 0, v_ignoreDeprecatedImports_416_);
v___x_423_ = v___x_410_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_ignoreDeprecatedImports_416_);
lean_ctor_set(v_reuseFailAlloc_424_, 1, v___x_421_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
v_a_402_ = v___x_423_;
goto v___jp_401_;
}
}
else
{
lean_object* v___x_426_; 
lean_dec(v___x_418_);
lean_dec(v___y_415_);
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 0, v_ignoreDeprecatedImports_416_);
v___x_426_ = v___x_410_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v_ignoreDeprecatedImports_416_);
lean_ctor_set(v_reuseFailAlloc_427_, 1, v_snd_408_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
v_a_402_ = v___x_426_;
goto v___jp_401_;
}
}
}
}
}
v___jp_401_:
{
size_t v___x_403_; size_t v___x_404_; 
v___x_403_ = ((size_t)1ULL);
v___x_404_ = lean_usize_add(v_i_399_, v___x_403_);
v_i_399_ = v___x_404_;
v_b_400_ = v_a_402_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkDeprecatedImports_spec__3___boxed(lean_object* v_as_484_, lean_object* v_sz_485_, lean_object* v_i_486_, lean_object* v_b_487_){
_start:
{
size_t v_sz_boxed_488_; size_t v_i_boxed_489_; lean_object* v_res_490_; 
v_sz_boxed_488_ = lean_unbox_usize(v_sz_485_);
lean_dec(v_sz_485_);
v_i_boxed_489_ = lean_unbox_usize(v_i_486_);
lean_dec(v_i_486_);
v_res_490_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkDeprecatedImports_spec__3(v_as_484_, v_sz_boxed_488_, v_i_boxed_489_, v_b_487_);
lean_dec_ref(v_as_484_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4_spec__5(lean_object* v_o_494_, lean_object* v_k_495_, uint8_t v_v_496_){
_start:
{
lean_object* v_map_497_; uint8_t v_hasTrace_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_512_; 
v_map_497_ = lean_ctor_get(v_o_494_, 0);
v_hasTrace_498_ = lean_ctor_get_uint8(v_o_494_, sizeof(void*)*1);
v_isSharedCheck_512_ = !lean_is_exclusive(v_o_494_);
if (v_isSharedCheck_512_ == 0)
{
v___x_500_ = v_o_494_;
v_isShared_501_ = v_isSharedCheck_512_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_map_497_);
lean_dec(v_o_494_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_512_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_502_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_502_, 0, v_v_496_);
lean_inc(v_k_495_);
v___x_503_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_495_, v___x_502_, v_map_497_);
if (v_hasTrace_498_ == 0)
{
lean_object* v___x_504_; uint8_t v___x_505_; lean_object* v___x_507_; 
v___x_504_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4_spec__5___closed__1));
v___x_505_ = l_Lean_Name_isPrefixOf(v___x_504_, v_k_495_);
lean_dec(v_k_495_);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 0, v___x_503_);
v___x_507_ = v___x_500_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v___x_503_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
lean_ctor_set_uint8(v___x_507_, sizeof(void*)*1, v___x_505_);
return v___x_507_;
}
}
else
{
lean_object* v___x_510_; 
lean_dec(v_k_495_);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 0, v___x_503_);
v___x_510_ = v___x_500_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v___x_503_);
lean_ctor_set_uint8(v_reuseFailAlloc_511_, sizeof(void*)*1, v_hasTrace_498_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4_spec__5___boxed(lean_object* v_o_513_, lean_object* v_k_514_, lean_object* v_v_515_){
_start:
{
uint8_t v_v_boxed_516_; lean_object* v_res_517_; 
v_v_boxed_516_ = lean_unbox(v_v_515_);
v_res_517_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4_spec__5(v_o_513_, v_k_514_, v_v_boxed_516_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4(lean_object* v_opts_518_, lean_object* v_opt_519_, uint8_t v_val_520_){
_start:
{
lean_object* v_name_521_; lean_object* v___x_522_; 
v_name_521_ = lean_ctor_get(v_opt_519_, 0);
lean_inc(v_name_521_);
lean_dec_ref(v_opt_519_);
v___x_522_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4_spec__5(v_opts_518_, v_name_521_, v_val_520_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4___boxed(lean_object* v_opts_523_, lean_object* v_opt_524_, lean_object* v_val_525_){
_start:
{
uint8_t v_val_boxed_526_; lean_object* v_res_527_; 
v_val_boxed_526_ = lean_unbox(v_val_525_);
v_res_527_ = l_Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4(v_opts_523_, v_opt_524_, v_val_boxed_526_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1(lean_object* v_ignoreDeprecatedImports_533_, lean_object* v_env_534_, lean_object* v_inputCtx_535_, lean_object* v_importPositions_536_, lean_object* v_startPos_537_, lean_object* v_as_538_, size_t v_i_539_, size_t v_stop_540_, lean_object* v_b_541_){
_start:
{
lean_object* v___y_543_; uint8_t v___x_547_; 
v___x_547_ = lean_usize_dec_eq(v_i_539_, v_stop_540_);
if (v___x_547_ == 0)
{
lean_object* v___x_548_; lean_object* v_module_549_; uint8_t v___x_550_; 
v___x_548_ = lean_array_uget_borrowed(v_as_538_, v_i_539_);
v_module_549_ = lean_ctor_get(v___x_548_, 0);
v___x_550_ = l_Lean_NameSet_contains(v_ignoreDeprecatedImports_533_, v_module_549_);
if (v___x_550_ == 0)
{
lean_object* v___x_551_; 
v___x_551_ = l_Lean_Environment_getModuleIdx_x3f(v_env_534_, v_module_549_);
if (lean_obj_tag(v___x_551_) == 0)
{
v___y_543_ = v_b_541_;
goto v___jp_542_;
}
else
{
lean_object* v_val_552_; lean_object* v___x_553_; 
v_val_552_ = lean_ctor_get(v___x_551_, 0);
lean_inc(v_val_552_);
lean_dec_ref_known(v___x_551_, 1);
v___x_553_ = l_Lean_Environment_getDeprecatedModuleByIdx_x3f(v_env_534_, v_val_552_);
if (lean_obj_tag(v___x_553_) == 0)
{
lean_dec(v_val_552_);
v___y_543_ = v_b_541_;
goto v___jp_542_;
}
else
{
lean_object* v_val_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_577_; 
v_val_554_ = lean_ctor_get(v___x_553_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_577_ == 0)
{
v___x_556_ = v___x_553_;
v_isShared_557_ = v_isSharedCheck_577_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_val_554_);
lean_dec(v___x_553_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_577_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___y_559_; lean_object* v___x_575_; 
v___x_575_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_importPositions_536_, v_module_549_);
if (lean_obj_tag(v___x_575_) == 0)
{
lean_inc(v_startPos_537_);
v___y_559_ = v_startPos_537_;
goto v___jp_558_;
}
else
{
lean_object* v_val_576_; 
v_val_576_ = lean_ctor_get(v___x_575_, 0);
lean_inc(v_val_576_);
lean_dec_ref_known(v___x_575_, 1);
v___y_559_ = v_val_576_;
goto v___jp_558_;
}
v___jp_558_:
{
lean_object* v_fileName_560_; lean_object* v_fileMap_561_; lean_object* v___x_562_; lean_object* v___x_563_; uint8_t v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_569_; 
v_fileName_560_ = lean_ctor_get(v_inputCtx_535_, 1);
v_fileMap_561_ = lean_ctor_get(v_inputCtx_535_, 2);
lean_inc_ref(v_fileMap_561_);
v___x_562_ = l_Lean_FileMap_toPosition(v_fileMap_561_, v___y_559_);
lean_dec(v___y_559_);
v___x_563_ = lean_box(0);
v___x_564_ = 1;
v___x_565_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___closed__0));
v___x_566_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___closed__2));
lean_inc(v_module_549_);
v___x_567_ = l_Lean_formatDeprecatedModuleWarning(v_env_534_, v_val_552_, v_module_549_, v_val_554_);
lean_dec(v_val_552_);
if (v_isShared_557_ == 0)
{
lean_ctor_set_tag(v___x_556_, 3);
lean_ctor_set(v___x_556_, 0, v___x_567_);
v___x_569_ = v___x_556_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v___x_567_);
v___x_569_ = v_reuseFailAlloc_574_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_570_ = l_Lean_MessageData_ofFormat(v___x_569_);
v___x_571_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_571_, 0, v___x_566_);
lean_ctor_set(v___x_571_, 1, v___x_570_);
lean_inc_ref(v_fileName_560_);
v___x_572_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_572_, 0, v_fileName_560_);
lean_ctor_set(v___x_572_, 1, v___x_562_);
lean_ctor_set(v___x_572_, 2, v___x_563_);
lean_ctor_set(v___x_572_, 3, v___x_565_);
lean_ctor_set(v___x_572_, 4, v___x_571_);
lean_ctor_set_uint8(v___x_572_, sizeof(void*)*5, v___x_550_);
lean_ctor_set_uint8(v___x_572_, sizeof(void*)*5 + 1, v___x_564_);
lean_ctor_set_uint8(v___x_572_, sizeof(void*)*5 + 2, v___x_550_);
v___x_573_ = l_Lean_MessageLog_add(v___x_572_, v_b_541_);
v___y_543_ = v___x_573_;
goto v___jp_542_;
}
}
}
}
}
}
else
{
v___y_543_ = v_b_541_;
goto v___jp_542_;
}
}
else
{
lean_dec(v_startPos_537_);
lean_dec_ref(v_inputCtx_535_);
return v_b_541_;
}
v___jp_542_:
{
size_t v___x_544_; size_t v___x_545_; 
v___x_544_ = ((size_t)1ULL);
v___x_545_ = lean_usize_add(v_i_539_, v___x_544_);
v_i_539_ = v___x_545_;
v_b_541_ = v___y_543_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___boxed(lean_object* v_ignoreDeprecatedImports_578_, lean_object* v_env_579_, lean_object* v_inputCtx_580_, lean_object* v_importPositions_581_, lean_object* v_startPos_582_, lean_object* v_as_583_, lean_object* v_i_584_, lean_object* v_stop_585_, lean_object* v_b_586_){
_start:
{
size_t v_i_boxed_587_; size_t v_stop_boxed_588_; lean_object* v_res_589_; 
v_i_boxed_587_ = lean_unbox_usize(v_i_584_);
lean_dec(v_i_584_);
v_stop_boxed_588_ = lean_unbox_usize(v_stop_585_);
lean_dec(v_stop_585_);
v_res_589_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1(v_ignoreDeprecatedImports_578_, v_env_579_, v_inputCtx_580_, v_importPositions_581_, v_startPos_582_, v_as_583_, v_i_boxed_587_, v_stop_boxed_588_, v_b_586_);
lean_dec_ref(v_as_583_);
lean_dec(v_importPositions_581_);
lean_dec_ref(v_env_579_);
lean_dec(v_ignoreDeprecatedImports_578_);
return v_res_589_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedImports___closed__0(void){
_start:
{
lean_object* v_importPositions_590_; lean_object* v_ignoreDeprecatedImports_591_; lean_object* v___x_592_; 
v_importPositions_590_ = lean_box(1);
v_ignoreDeprecatedImports_591_ = l_Lean_NameSet_empty;
v___x_592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_592_, 0, v_ignoreDeprecatedImports_591_);
lean_ctor_set(v___x_592_, 1, v_importPositions_590_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedImports(lean_object* v_env_593_, lean_object* v_imports_594_, lean_object* v_opts_595_, lean_object* v_inputCtx_596_, lean_object* v_startPos_597_, lean_object* v_messages_598_, lean_object* v_headerStx_x3f_599_, lean_object* v_origHeaderStx_x3f_600_){
_start:
{
lean_object* v_opts_602_; lean_object* v_ignoreDeprecatedImports_603_; lean_object* v_importPositions_604_; lean_object* v_ignoreDeprecatedImports_617_; lean_object* v_importPositions_618_; lean_object* v___y_620_; lean_object* v_opts_621_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___y_655_; lean_object* v___y_656_; lean_object* v___y_657_; lean_object* v___y_658_; lean_object* v___y_659_; lean_object* v_moduleTk_660_; lean_object* v_val_670_; 
v_ignoreDeprecatedImports_617_ = l_Lean_NameSet_empty;
v_importPositions_618_ = lean_box(1);
if (lean_obj_tag(v_origHeaderStx_x3f_600_) == 0)
{
if (lean_obj_tag(v_headerStx_x3f_599_) == 1)
{
lean_object* v_val_687_; 
v_val_687_ = lean_ctor_get(v_headerStx_x3f_599_, 0);
lean_inc(v_val_687_);
lean_dec_ref_known(v_headerStx_x3f_599_, 1);
v_val_670_ = v_val_687_;
goto v___jp_669_;
}
else
{
lean_dec(v_headerStx_x3f_599_);
v_opts_602_ = v_opts_595_;
v_ignoreDeprecatedImports_603_ = v_ignoreDeprecatedImports_617_;
v_importPositions_604_ = v_importPositions_618_;
goto v___jp_601_;
}
}
else
{
lean_object* v_val_688_; 
lean_dec(v_headerStx_x3f_599_);
v_val_688_ = lean_ctor_get(v_origHeaderStx_x3f_600_, 0);
lean_inc(v_val_688_);
lean_dec_ref_known(v_origHeaderStx_x3f_600_, 1);
v_val_670_ = v_val_688_;
goto v___jp_669_;
}
v___jp_601_:
{
lean_object* v___x_605_; uint8_t v___x_606_; 
v___x_605_ = l_Lean_linter_deprecated_module;
v___x_606_ = l_Lean_Option_get___at___00Lean_Elab_checkDeprecatedImports_spec__0(v_opts_602_, v___x_605_);
lean_dec_ref(v_opts_602_);
if (v___x_606_ == 0)
{
lean_dec(v_importPositions_604_);
lean_dec(v_ignoreDeprecatedImports_603_);
lean_dec(v_startPos_597_);
lean_dec_ref(v_inputCtx_596_);
return v_messages_598_;
}
else
{
lean_object* v___x_607_; lean_object* v___x_608_; uint8_t v___x_609_; 
v___x_607_ = lean_unsigned_to_nat(0u);
v___x_608_ = lean_array_get_size(v_imports_594_);
v___x_609_ = lean_nat_dec_lt(v___x_607_, v___x_608_);
if (v___x_609_ == 0)
{
lean_dec(v_importPositions_604_);
lean_dec(v_ignoreDeprecatedImports_603_);
lean_dec(v_startPos_597_);
lean_dec_ref(v_inputCtx_596_);
return v_messages_598_;
}
else
{
uint8_t v___x_610_; 
v___x_610_ = lean_nat_dec_le(v___x_608_, v___x_608_);
if (v___x_610_ == 0)
{
if (v___x_609_ == 0)
{
lean_dec(v_importPositions_604_);
lean_dec(v_ignoreDeprecatedImports_603_);
lean_dec(v_startPos_597_);
lean_dec_ref(v_inputCtx_596_);
return v_messages_598_;
}
else
{
size_t v___x_611_; size_t v___x_612_; lean_object* v___x_613_; 
v___x_611_ = ((size_t)0ULL);
v___x_612_ = lean_usize_of_nat(v___x_608_);
v___x_613_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1(v_ignoreDeprecatedImports_603_, v_env_593_, v_inputCtx_596_, v_importPositions_604_, v_startPos_597_, v_imports_594_, v___x_611_, v___x_612_, v_messages_598_);
lean_dec(v_importPositions_604_);
lean_dec(v_ignoreDeprecatedImports_603_);
return v___x_613_;
}
}
else
{
size_t v___x_614_; size_t v___x_615_; lean_object* v___x_616_; 
v___x_614_ = ((size_t)0ULL);
v___x_615_ = lean_usize_of_nat(v___x_608_);
v___x_616_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1(v_ignoreDeprecatedImports_603_, v_env_593_, v_inputCtx_596_, v_importPositions_604_, v_startPos_597_, v_imports_594_, v___x_614_, v___x_615_, v_messages_598_);
lean_dec(v_importPositions_604_);
lean_dec(v_ignoreDeprecatedImports_603_);
return v___x_616_;
}
}
}
}
v___jp_619_:
{
lean_object* v___x_622_; size_t v_sz_623_; size_t v___x_624_; lean_object* v___x_625_; lean_object* v_fst_626_; lean_object* v_snd_627_; 
v___x_622_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedImports___closed__0, &l_Lean_Elab_checkDeprecatedImports___closed__0_once, _init_l_Lean_Elab_checkDeprecatedImports___closed__0);
v_sz_623_ = lean_array_size(v___y_620_);
v___x_624_ = ((size_t)0ULL);
v___x_625_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkDeprecatedImports_spec__3(v___y_620_, v_sz_623_, v___x_624_, v___x_622_);
lean_dec_ref(v___y_620_);
v_fst_626_ = lean_ctor_get(v___x_625_, 0);
lean_inc(v_fst_626_);
v_snd_627_ = lean_ctor_get(v___x_625_, 1);
lean_inc(v_snd_627_);
lean_dec_ref(v___x_625_);
v_opts_602_ = v_opts_621_;
v_ignoreDeprecatedImports_603_ = v_fst_626_;
v_importPositions_604_ = v_snd_627_;
goto v___jp_601_;
}
v___jp_628_:
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v_importsStx_634_; 
v___x_632_ = lean_unsigned_to_nat(2u);
v___x_633_ = l_Lean_Syntax_getArg(v___y_629_, v___x_632_);
lean_dec(v___y_629_);
v_importsStx_634_ = l_Lean_Syntax_getArgs(v___x_633_);
lean_dec(v___x_633_);
if (lean_obj_tag(v___y_631_) == 0)
{
lean_dec(v___y_630_);
v___y_620_ = v_importsStx_634_;
v_opts_621_ = v_opts_595_;
goto v___jp_619_;
}
else
{
lean_object* v_val_635_; lean_object* v___x_636_; 
v_val_635_ = lean_ctor_get(v___y_631_, 0);
lean_inc(v_val_635_);
lean_dec_ref_known(v___y_631_, 1);
v___x_636_ = l_Lean_Syntax_getTrailing_x3f(v_val_635_);
lean_dec(v_val_635_);
if (lean_obj_tag(v___x_636_) == 0)
{
lean_dec(v___y_630_);
v___y_620_ = v_importsStx_634_;
v_opts_621_ = v_opts_595_;
goto v___jp_619_;
}
else
{
lean_object* v_val_637_; lean_object* v_str_638_; lean_object* v_startPos_639_; lean_object* v_stopPos_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_653_; 
v_val_637_ = lean_ctor_get(v___x_636_, 0);
lean_inc(v_val_637_);
lean_dec_ref_known(v___x_636_, 1);
v_str_638_ = lean_ctor_get(v_val_637_, 0);
v_startPos_639_ = lean_ctor_get(v_val_637_, 1);
v_stopPos_640_ = lean_ctor_get(v_val_637_, 2);
v_isSharedCheck_653_ = !lean_is_exclusive(v_val_637_);
if (v_isSharedCheck_653_ == 0)
{
v___x_642_ = v_val_637_;
v_isShared_643_ = v_isSharedCheck_653_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_stopPos_640_);
lean_inc(v_startPos_639_);
lean_inc(v_str_638_);
lean_dec(v_val_637_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_653_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_647_; 
v___x_644_ = lean_string_utf8_extract(v_str_638_, v_startPos_639_, v_stopPos_640_);
lean_dec(v_stopPos_640_);
lean_dec(v_startPos_639_);
lean_dec_ref(v_str_638_);
v___x_645_ = lean_string_utf8_byte_size(v___x_644_);
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 2, v___x_645_);
lean_ctor_set(v___x_642_, 1, v___y_630_);
lean_ctor_set(v___x_642_, 0, v___x_644_);
v___x_647_ = v___x_642_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v___x_644_);
lean_ctor_set(v_reuseFailAlloc_652_, 1, v___y_630_);
lean_ctor_set(v_reuseFailAlloc_652_, 2, v___x_645_);
v___x_647_ = v_reuseFailAlloc_652_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
uint8_t v___x_648_; 
v___x_648_ = l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2(v___x_647_);
lean_dec_ref(v___x_647_);
if (v___x_648_ == 0)
{
v___y_620_ = v_importsStx_634_;
v_opts_621_ = v_opts_595_;
goto v___jp_619_;
}
else
{
lean_object* v___x_649_; uint8_t v___x_650_; lean_object* v_opts_651_; 
v___x_649_ = l_Lean_linter_deprecated_module;
v___x_650_ = 0;
v_opts_651_ = l_Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4(v_opts_595_, v___x_649_, v___x_650_);
v___y_620_ = v_importsStx_634_;
v_opts_621_ = v_opts_651_;
goto v___jp_619_;
}
}
}
}
}
}
v___jp_654_:
{
lean_object* v___x_661_; lean_object* v___x_662_; uint8_t v___x_663_; 
v___x_661_ = lean_unsigned_to_nat(1u);
v___x_662_ = l_Lean_Syntax_getArg(v___y_657_, v___x_661_);
v___x_663_ = l_Lean_Syntax_isNone(v___x_662_);
if (v___x_663_ == 0)
{
uint8_t v___x_664_; 
lean_inc(v___x_662_);
v___x_664_ = l_Lean_Syntax_matchesNull(v___x_662_, v___x_661_);
if (v___x_664_ == 0)
{
lean_dec(v___x_662_);
lean_dec(v_moduleTk_660_);
lean_dec(v___y_658_);
lean_dec(v___y_657_);
v_opts_602_ = v_opts_595_;
v_ignoreDeprecatedImports_603_ = v_ignoreDeprecatedImports_617_;
v_importPositions_604_ = v_importPositions_618_;
goto v___jp_601_;
}
else
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; uint8_t v___x_668_; 
v___x_665_ = l_Lean_Syntax_getArg(v___x_662_, v___y_658_);
lean_dec(v___x_662_);
v___x_666_ = ((lean_object*)(l_Lean_Elab_HeaderSyntax_imports___closed__6));
lean_inc_ref(v___y_659_);
lean_inc_ref(v___y_656_);
lean_inc_ref(v___y_655_);
v___x_667_ = l_Lean_Name_mkStr4(v___y_655_, v___y_656_, v___y_659_, v___x_666_);
v___x_668_ = l_Lean_Syntax_isOfKind(v___x_665_, v___x_667_);
lean_dec(v___x_667_);
if (v___x_668_ == 0)
{
lean_dec(v_moduleTk_660_);
lean_dec(v___y_658_);
lean_dec(v___y_657_);
v_opts_602_ = v_opts_595_;
v_ignoreDeprecatedImports_603_ = v_ignoreDeprecatedImports_617_;
v_importPositions_604_ = v_importPositions_618_;
goto v___jp_601_;
}
else
{
v___y_629_ = v___y_657_;
v___y_630_ = v___y_658_;
v___y_631_ = v_moduleTk_660_;
goto v___jp_628_;
}
}
}
else
{
lean_dec(v___x_662_);
v___y_629_ = v___y_657_;
v___y_630_ = v___y_658_;
v___y_631_ = v_moduleTk_660_;
goto v___jp_628_;
}
}
v___jp_669_:
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; uint8_t v___x_675_; 
v___x_671_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__0));
v___x_672_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__1));
v___x_673_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__2));
v___x_674_ = ((lean_object*)(l_Lean_Elab_HeaderSyntax_imports___closed__1));
lean_inc(v_val_670_);
v___x_675_ = l_Lean_Syntax_isOfKind(v_val_670_, v___x_674_);
if (v___x_675_ == 0)
{
lean_dec(v_val_670_);
v_opts_602_ = v_opts_595_;
v_ignoreDeprecatedImports_603_ = v_ignoreDeprecatedImports_617_;
v_importPositions_604_ = v_importPositions_618_;
goto v___jp_601_;
}
else
{
lean_object* v___x_676_; lean_object* v___x_677_; uint8_t v___x_678_; 
v___x_676_ = lean_unsigned_to_nat(0u);
v___x_677_ = l_Lean_Syntax_getArg(v_val_670_, v___x_676_);
v___x_678_ = l_Lean_Syntax_isNone(v___x_677_);
if (v___x_678_ == 0)
{
lean_object* v___x_679_; uint8_t v___x_680_; 
v___x_679_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_677_);
v___x_680_ = l_Lean_Syntax_matchesNull(v___x_677_, v___x_679_);
if (v___x_680_ == 0)
{
lean_dec(v___x_677_);
lean_dec(v_val_670_);
v_opts_602_ = v_opts_595_;
v_ignoreDeprecatedImports_603_ = v_ignoreDeprecatedImports_617_;
v_importPositions_604_ = v_importPositions_618_;
goto v___jp_601_;
}
else
{
lean_object* v___x_681_; lean_object* v___x_682_; uint8_t v___x_683_; 
v___x_681_ = l_Lean_Syntax_getArg(v___x_677_, v___x_676_);
lean_dec(v___x_677_);
v___x_682_ = ((lean_object*)(l_Lean_Elab_HeaderSyntax_imports___closed__9));
lean_inc(v___x_681_);
v___x_683_ = l_Lean_Syntax_isOfKind(v___x_681_, v___x_682_);
if (v___x_683_ == 0)
{
lean_dec(v___x_681_);
lean_dec(v_val_670_);
v_opts_602_ = v_opts_595_;
v_ignoreDeprecatedImports_603_ = v_ignoreDeprecatedImports_617_;
v_importPositions_604_ = v_importPositions_618_;
goto v___jp_601_;
}
else
{
lean_object* v_moduleTk_684_; lean_object* v___x_685_; 
v_moduleTk_684_ = l_Lean_Syntax_getArg(v___x_681_, v___x_676_);
lean_dec(v___x_681_);
v___x_685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_685_, 0, v_moduleTk_684_);
v___y_655_ = v___x_671_;
v___y_656_ = v___x_672_;
v___y_657_ = v_val_670_;
v___y_658_ = v___x_676_;
v___y_659_ = v___x_673_;
v_moduleTk_660_ = v___x_685_;
goto v___jp_654_;
}
}
}
else
{
lean_object* v___x_686_; 
lean_dec(v___x_677_);
v___x_686_ = lean_box(0);
v___y_655_ = v___x_671_;
v___y_656_ = v___x_672_;
v___y_657_ = v_val_670_;
v___y_658_ = v___x_676_;
v___y_659_ = v___x_673_;
v_moduleTk_660_ = v___x_686_;
goto v___jp_654_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedImports___boxed(lean_object* v_env_689_, lean_object* v_imports_690_, lean_object* v_opts_691_, lean_object* v_inputCtx_692_, lean_object* v_startPos_693_, lean_object* v_messages_694_, lean_object* v_headerStx_x3f_695_, lean_object* v_origHeaderStx_x3f_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l_Lean_Elab_checkDeprecatedImports(v_env_689_, v_imports_690_, v_opts_691_, v_inputCtx_692_, v_startPos_693_, v_messages_694_, v_headerStx_x3f_695_, v_origHeaderStx_x3f_696_);
lean_dec_ref(v_imports_690_);
lean_dec_ref(v_env_689_);
return v_res_697_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_spec__2(lean_object* v_s_698_, lean_object* v_inst_699_, lean_object* v_R_700_, lean_object* v_a_701_, uint8_t v_b_702_, lean_object* v_c_703_){
_start:
{
uint8_t v___x_704_; 
v___x_704_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_spec__2___redArg(v_s_698_, v_a_701_, v_b_702_);
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_spec__2___boxed(lean_object* v_s_705_, lean_object* v_inst_706_, lean_object* v_R_707_, lean_object* v_a_708_, lean_object* v_b_709_, lean_object* v_c_710_){
_start:
{
uint8_t v_b_boxed_711_; uint8_t v_res_712_; lean_object* v_r_713_; 
v_b_boxed_711_ = lean_unbox(v_b_709_);
v_res_712_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_spec__2(v_s_705_, v_inst_706_, v_R_707_, v_a_708_, v_b_boxed_711_, v_c_710_);
lean_dec_ref(v_s_705_);
v_r_713_ = lean_box(v_res_712_);
return v_r_713_;
}
}
static lean_object* _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_714_; lean_object* v___x_715_; 
v___x_714_ = 33;
v___x_715_ = lean_box_uint32(v___x_714_);
return v___x_715_;
}
}
static lean_object* _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__2(void){
_start:
{
uint32_t v___x_716_; lean_object* v___x_717_; 
v___x_716_ = 42;
v___x_717_ = lean_box_uint32(v___x_716_);
return v___x_717_;
}
}
static lean_object* _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__3(void){
_start:
{
uint32_t v___x_718_; lean_object* v___x_719_; 
v___x_718_ = 63;
v___x_719_ = lean_box_uint32(v___x_718_);
return v___x_719_;
}
}
static lean_object* _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__4(void){
_start:
{
uint32_t v___x_720_; lean_object* v___x_721_; 
v___x_720_ = 124;
v___x_721_ = lean_box_uint32(v___x_720_);
return v___x_721_;
}
}
static lean_object* _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__5(void){
_start:
{
uint32_t v___x_722_; lean_object* v___x_723_; 
v___x_722_ = 34;
v___x_723_ = lean_box_uint32(v___x_722_);
return v___x_723_;
}
}
static lean_object* _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__6(void){
_start:
{
uint32_t v___x_724_; lean_object* v___x_725_; 
v___x_724_ = 62;
v___x_725_ = lean_box_uint32(v___x_724_);
return v___x_725_;
}
}
static lean_object* _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__7(void){
_start:
{
uint32_t v___x_726_; lean_object* v___x_727_; 
v___x_726_ = 60;
v___x_727_ = lean_box_uint32(v___x_726_);
return v___x_727_;
}
}
static lean_object* _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0(void){
_start:
{
lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_728_ = lean_unsigned_to_nat(7u);
v___x_729_ = lean_mk_empty_array_with_capacity(v___x_728_);
v___x_730_ = l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__7;
v___x_731_ = lean_array_push(v___x_729_, v___x_730_);
v___x_732_ = l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__6;
v___x_733_ = lean_array_push(v___x_731_, v___x_732_);
v___x_734_ = l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__5;
v___x_735_ = lean_array_push(v___x_733_, v___x_734_);
v___x_736_ = l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__4;
v___x_737_ = lean_array_push(v___x_735_, v___x_736_);
v___x_738_ = l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__3;
v___x_739_ = lean_array_push(v___x_737_, v___x_738_);
v___x_740_ = l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__2;
v___x_741_ = lean_array_push(v___x_739_, v___x_740_);
v___x_742_ = l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__1;
v___x_743_ = lean_array_push(v___x_741_, v___x_742_);
return v___x_743_;
}
}
static lean_object* _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars(void){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = lean_obj_once(&l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0, &l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0_once, _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__0(lean_object* v_s_832_, lean_object* v_p_833_){
_start:
{
lean_object* v___y_835_; lean_object* v___y_836_; uint32_t v___y_840_; lean_object* v___x_852_; uint8_t v_decide_853_; 
v___x_852_ = lean_string_utf8_byte_size(v_s_832_);
v_decide_853_ = lean_nat_dec_eq(v_p_833_, v___x_852_);
if (v_decide_853_ == 0)
{
uint32_t v___x_854_; uint32_t v___x_855_; uint8_t v___x_856_; 
v___x_854_ = lean_string_utf8_get_fast(v_s_832_, v_p_833_);
v___x_855_ = 97;
v___x_856_ = lean_uint32_dec_le(v___x_855_, v___x_854_);
if (v___x_856_ == 0)
{
v___y_840_ = v___x_854_;
goto v___jp_839_;
}
else
{
uint32_t v___x_857_; uint8_t v___x_858_; 
v___x_857_ = 122;
v___x_858_ = lean_uint32_dec_le(v___x_854_, v___x_857_);
if (v___x_858_ == 0)
{
v___y_840_ = v___x_854_;
goto v___jp_839_;
}
else
{
uint32_t v___x_859_; uint32_t v___x_860_; 
v___x_859_ = 4294967264;
v___x_860_ = lean_uint32_add(v___x_854_, v___x_859_);
v___y_840_ = v___x_860_;
goto v___jp_839_;
}
}
}
else
{
lean_dec(v_p_833_);
return v_s_832_;
}
v___jp_834_:
{
lean_object* v___x_837_; 
v___x_837_ = lean_nat_add(v_p_833_, v___y_836_);
lean_dec(v_p_833_);
v_s_832_ = v___y_835_;
v_p_833_ = v___x_837_;
goto _start;
}
v___jp_839_:
{
lean_object* v___x_841_; uint32_t v___x_842_; uint8_t v___x_843_; 
lean_inc(v_p_833_);
v___x_841_ = lean_string_utf8_set(v_s_832_, v_p_833_, v___y_840_);
v___x_842_ = 127;
v___x_843_ = lean_uint32_dec_le(v___y_840_, v___x_842_);
if (v___x_843_ == 0)
{
uint32_t v___x_844_; uint8_t v___x_845_; 
v___x_844_ = 2047;
v___x_845_ = lean_uint32_dec_le(v___y_840_, v___x_844_);
if (v___x_845_ == 0)
{
uint32_t v___x_846_; uint8_t v___x_847_; 
v___x_846_ = 65535;
v___x_847_ = lean_uint32_dec_le(v___y_840_, v___x_846_);
if (v___x_847_ == 0)
{
lean_object* v___x_848_; 
v___x_848_ = lean_unsigned_to_nat(4u);
v___y_835_ = v___x_841_;
v___y_836_ = v___x_848_;
goto v___jp_834_;
}
else
{
lean_object* v___x_849_; 
v___x_849_ = lean_unsigned_to_nat(3u);
v___y_835_ = v___x_841_;
v___y_836_ = v___x_849_;
goto v___jp_834_;
}
}
else
{
lean_object* v___x_850_; 
v___x_850_ = lean_unsigned_to_nat(2u);
v___y_835_ = v___x_841_;
v___y_836_ = v___x_850_;
goto v___jp_834_;
}
}
else
{
lean_object* v___x_851_; 
v___x_851_ = lean_unsigned_to_nat(1u);
v___y_835_ = v___x_841_;
v___y_836_ = v___x_851_;
goto v___jp_834_;
}
}
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2_spec__3___redArg(lean_object* v_s_861_, uint32_t v_a_862_, lean_object* v_a_863_, uint8_t v_b_864_){
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2_spec__3___redArg___boxed(lean_object* v_s_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_b_879_){
_start:
{
uint32_t v_a_boxed_880_; uint8_t v_b_boxed_881_; uint8_t v_res_882_; lean_object* v_r_883_; 
v_a_boxed_880_ = lean_unbox_uint32(v_a_877_);
lean_dec(v_a_877_);
v_b_boxed_881_ = lean_unbox(v_b_879_);
v_res_882_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2_spec__3___redArg(v_s_876_, v_a_boxed_880_, v_a_878_, v_b_boxed_881_);
lean_dec_ref(v_s_876_);
v_r_883_ = lean_box(v_res_882_);
return v_r_883_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2(uint32_t v_a_884_, lean_object* v_s_885_){
_start:
{
lean_object* v_searcher_886_; uint8_t v___x_887_; uint8_t v___x_888_; 
v_searcher_886_ = lean_unsigned_to_nat(0u);
v___x_887_ = 0;
v___x_888_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2_spec__3___redArg(v_s_885_, v_a_884_, v_searcher_886_, v___x_887_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2___boxed(lean_object* v_a_889_, lean_object* v_s_890_){
_start:
{
uint32_t v_a_boxed_891_; uint8_t v_res_892_; lean_object* v_r_893_; 
v_a_boxed_891_ = lean_unbox_uint32(v_a_889_);
lean_dec(v_a_889_);
v_res_892_ = l_String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2(v_a_boxed_891_, v_s_890_);
lean_dec_ref(v_s_890_);
v_r_893_ = lean_box(v_res_892_);
return v_r_893_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__3(lean_object* v_comp_897_, lean_object* v_as_898_, size_t v_sz_899_, size_t v_i_900_, lean_object* v_b_901_){
_start:
{
uint8_t v___x_902_; 
v___x_902_ = lean_usize_dec_lt(v_i_900_, v_sz_899_);
if (v___x_902_ == 0)
{
lean_dec_ref(v_comp_897_);
lean_inc_ref(v_b_901_);
return v_b_901_;
}
else
{
lean_object* v___x_903_; lean_object* v_a_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; uint32_t v___x_908_; uint8_t v___x_909_; 
v___x_903_ = lean_box(0);
v_a_904_ = lean_array_uget_borrowed(v_as_898_, v_i_900_);
v___x_905_ = lean_unsigned_to_nat(0u);
v___x_906_ = lean_string_utf8_byte_size(v_comp_897_);
lean_inc_ref(v_comp_897_);
v___x_907_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_907_, 0, v_comp_897_);
lean_ctor_set(v___x_907_, 1, v___x_905_);
lean_ctor_set(v___x_907_, 2, v___x_906_);
v___x_908_ = lean_unbox_uint32(v_a_904_);
v___x_909_ = l_String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2(v___x_908_, v___x_907_);
lean_dec_ref_known(v___x_907_, 3);
if (v___x_909_ == 0)
{
lean_object* v___x_910_; size_t v___x_911_; size_t v___x_912_; 
v___x_910_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__3___closed__0));
v___x_911_ = ((size_t)1ULL);
v___x_912_ = lean_usize_add(v_i_900_, v___x_911_);
v_i_900_ = v___x_912_;
v_b_901_ = v___x_910_;
goto _start;
}
else
{
lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; 
lean_dec_ref(v_comp_897_);
lean_inc(v_a_904_);
v___x_914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_914_, 0, v_a_904_);
v___x_915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_915_, 0, v___x_914_);
v___x_916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_916_, 0, v___x_915_);
lean_ctor_set(v___x_916_, 1, v___x_903_);
return v___x_916_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__3___boxed(lean_object* v_comp_917_, lean_object* v_as_918_, lean_object* v_sz_919_, lean_object* v_i_920_, lean_object* v_b_921_){
_start:
{
size_t v_sz_boxed_922_; size_t v_i_boxed_923_; lean_object* v_res_924_; 
v_sz_boxed_922_ = lean_unbox_usize(v_sz_919_);
lean_dec(v_sz_919_);
v_i_boxed_923_ = lean_unbox_usize(v_i_920_);
lean_dec(v_i_920_);
v_res_924_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__3(v_comp_917_, v_as_918_, v_sz_boxed_922_, v_i_boxed_923_, v_b_921_);
lean_dec_ref(v_b_921_);
lean_dec_ref(v_as_918_);
return v_res_924_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__1_spec__1(lean_object* v_a_925_, lean_object* v_as_926_, size_t v_i_927_, size_t v_stop_928_){
_start:
{
uint8_t v___x_929_; 
v___x_929_ = lean_usize_dec_eq(v_i_927_, v_stop_928_);
if (v___x_929_ == 0)
{
lean_object* v___x_930_; uint8_t v___x_931_; 
v___x_930_ = lean_array_uget_borrowed(v_as_926_, v_i_927_);
v___x_931_ = lean_string_dec_eq(v_a_925_, v___x_930_);
if (v___x_931_ == 0)
{
size_t v___x_932_; size_t v___x_933_; 
v___x_932_ = ((size_t)1ULL);
v___x_933_ = lean_usize_add(v_i_927_, v___x_932_);
v_i_927_ = v___x_933_;
goto _start;
}
else
{
return v___x_931_;
}
}
else
{
uint8_t v___x_935_; 
v___x_935_ = 0;
return v___x_935_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__1_spec__1___boxed(lean_object* v_a_936_, lean_object* v_as_937_, lean_object* v_i_938_, lean_object* v_stop_939_){
_start:
{
size_t v_i_boxed_940_; size_t v_stop_boxed_941_; uint8_t v_res_942_; lean_object* v_r_943_; 
v_i_boxed_940_ = lean_unbox_usize(v_i_938_);
lean_dec(v_i_938_);
v_stop_boxed_941_ = lean_unbox_usize(v_stop_939_);
lean_dec(v_stop_939_);
v_res_942_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__1_spec__1(v_a_936_, v_as_937_, v_i_boxed_940_, v_stop_boxed_941_);
lean_dec_ref(v_as_937_);
lean_dec_ref(v_a_936_);
v_r_943_ = lean_box(v_res_942_);
return v_r_943_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__1(lean_object* v_as_944_, lean_object* v_a_945_){
_start:
{
lean_object* v___x_946_; lean_object* v___x_947_; uint8_t v___x_948_; 
v___x_946_ = lean_unsigned_to_nat(0u);
v___x_947_ = lean_array_get_size(v_as_944_);
v___x_948_ = lean_nat_dec_lt(v___x_946_, v___x_947_);
if (v___x_948_ == 0)
{
return v___x_948_;
}
else
{
if (v___x_948_ == 0)
{
return v___x_948_;
}
else
{
size_t v___x_949_; size_t v___x_950_; uint8_t v___x_951_; 
v___x_949_ = ((size_t)0ULL);
v___x_950_ = lean_usize_of_nat(v___x_947_);
v___x_951_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__1_spec__1(v_a_945_, v_as_944_, v___x_949_, v___x_950_);
return v___x_951_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__1___boxed(lean_object* v_as_952_, lean_object* v_a_953_){
_start:
{
uint8_t v_res_954_; lean_object* v_r_955_; 
v_res_954_ = l_Array_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__1(v_as_952_, v_a_953_);
lean_dec_ref(v_a_953_);
lean_dec_ref(v_as_952_);
v_r_955_ = lean_box(v_res_954_);
return v_r_955_;
}
}
static size_t _init_l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__0(void){
_start:
{
lean_object* v___x_956_; size_t v_sz_957_; 
v___x_956_ = l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars;
v_sz_957_ = lean_array_size(v___x_956_);
return v_sz_957_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability(lean_object* v_comp_962_){
_start:
{
lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; uint8_t v___x_966_; 
v___x_963_ = ((lean_object*)(l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames));
v___x_964_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_comp_962_);
v___x_965_ = l_String_mapAux___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__0(v_comp_962_, v___x_964_);
v___x_966_ = l_Array_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__1(v___x_963_, v___x_965_);
lean_dec_ref(v___x_965_);
if (v___x_966_ == 0)
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; size_t v_sz_970_; size_t v___x_971_; lean_object* v___x_972_; lean_object* v_fst_973_; 
v___x_967_ = l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars;
v___x_968_ = lean_box(0);
v___x_969_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__3___closed__0));
v_sz_970_ = lean_usize_once(&l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__0, &l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__0_once, _init_l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__0);
v___x_971_ = ((size_t)0ULL);
v___x_972_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__3(v_comp_962_, v___x_967_, v_sz_970_, v___x_971_, v___x_969_);
v_fst_973_ = lean_ctor_get(v___x_972_, 0);
lean_inc(v_fst_973_);
lean_dec_ref(v___x_972_);
if (lean_obj_tag(v_fst_973_) == 0)
{
return v___x_968_;
}
else
{
lean_object* v_val_974_; 
v_val_974_ = lean_ctor_get(v_fst_973_, 0);
lean_inc(v_val_974_);
lean_dec_ref_known(v_fst_973_, 1);
if (lean_obj_tag(v_val_974_) == 1)
{
lean_object* v_val_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_989_; 
v_val_975_ = lean_ctor_get(v_val_974_, 0);
v_isSharedCheck_989_ = !lean_is_exclusive(v_val_974_);
if (v_isSharedCheck_989_ == 0)
{
v___x_977_ = v_val_974_;
v_isShared_978_ = v_isSharedCheck_989_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_val_975_);
lean_dec(v_val_974_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_989_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_979_; lean_object* v___x_980_; uint32_t v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_987_; 
v___x_979_ = ((lean_object*)(l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__1));
v___x_980_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___closed__0));
v___x_981_ = lean_unbox_uint32(v_val_975_);
lean_dec(v_val_975_);
v___x_982_ = lean_string_push(v___x_980_, v___x_981_);
v___x_983_ = lean_string_append(v___x_979_, v___x_982_);
lean_dec_ref(v___x_982_);
v___x_984_ = ((lean_object*)(l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__2));
v___x_985_ = lean_string_append(v___x_983_, v___x_984_);
if (v_isShared_978_ == 0)
{
lean_ctor_set(v___x_977_, 0, v___x_985_);
v___x_987_ = v___x_977_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v___x_985_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
}
else
{
lean_dec(v_val_974_);
return v___x_968_;
}
}
}
else
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_990_ = ((lean_object*)(l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__3));
v___x_991_ = lean_string_append(v___x_990_, v_comp_962_);
lean_dec_ref(v_comp_962_);
v___x_992_ = ((lean_object*)(l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__4));
v___x_993_ = lean_string_append(v___x_991_, v___x_992_);
v___x_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_994_, 0, v___x_993_);
return v___x_994_;
}
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2_spec__3(lean_object* v_s_995_, uint32_t v_a_996_, lean_object* v_inst_997_, lean_object* v_R_998_, lean_object* v_a_999_, uint8_t v_b_1000_, lean_object* v_c_1001_){
_start:
{
uint8_t v___x_1002_; 
v___x_1002_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2_spec__3___redArg(v_s_995_, v_a_996_, v_a_999_, v_b_1000_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2_spec__3___boxed(lean_object* v_s_1003_, lean_object* v_a_1004_, lean_object* v_inst_1005_, lean_object* v_R_1006_, lean_object* v_a_1007_, lean_object* v_b_1008_, lean_object* v_c_1009_){
_start:
{
uint32_t v_a_boxed_1010_; uint8_t v_b_boxed_1011_; uint8_t v_res_1012_; lean_object* v_r_1013_; 
v_a_boxed_1010_ = lean_unbox_uint32(v_a_1004_);
lean_dec(v_a_1004_);
v_b_boxed_1011_ = lean_unbox(v_b_1008_);
v_res_1012_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2_spec__3(v_s_1003_, v_a_boxed_1010_, v_inst_1005_, v_R_1006_, v_a_1007_, v_b_boxed_1011_, v_c_1009_);
lean_dec_ref(v_s_1003_);
v_r_1013_ = lean_box(v_res_1012_);
return v_r_1013_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_checkModuleNamePortability_go(lean_object* v_mainModule_1016_, lean_object* v_inputCtx_1017_, lean_object* v_startPos_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_){
_start:
{
switch(lean_obj_tag(v_a_1019_))
{
case 0:
{
lean_dec_ref(v_inputCtx_1017_);
lean_dec(v_mainModule_1016_);
return v_a_1020_;
}
case 1:
{
lean_object* v_pre_1021_; lean_object* v_str_1022_; lean_object* v___x_1023_; 
v_pre_1021_ = lean_ctor_get(v_a_1019_, 0);
lean_inc(v_pre_1021_);
v_str_1022_ = lean_ctor_get(v_a_1019_, 1);
lean_inc_ref(v_str_1022_);
lean_dec_ref_known(v_a_1019_, 2);
v___x_1023_ = l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability(v_str_1022_);
if (lean_obj_tag(v___x_1023_) == 0)
{
v_a_1019_ = v_pre_1021_;
goto _start;
}
else
{
lean_object* v_val_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1050_; 
v_val_1025_ = lean_ctor_get(v___x_1023_, 0);
v_isSharedCheck_1050_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1027_ = v___x_1023_;
v_isShared_1028_ = v_isSharedCheck_1050_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_val_1025_);
lean_dec(v___x_1023_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1050_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v_fileName_1029_; lean_object* v_fileMap_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; uint8_t v___x_1033_; uint8_t v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; uint8_t v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1044_; 
v_fileName_1029_ = lean_ctor_get(v_inputCtx_1017_, 1);
v_fileMap_1030_ = lean_ctor_get(v_inputCtx_1017_, 2);
lean_inc_ref(v_fileMap_1030_);
v___x_1031_ = l_Lean_FileMap_toPosition(v_fileMap_1030_, v_startPos_1018_);
v___x_1032_ = lean_box(0);
v___x_1033_ = 0;
v___x_1034_ = 2;
v___x_1035_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___closed__0));
v___x_1036_ = ((lean_object*)(l___private_Lean_Elab_Import_0__Lean_Elab_checkModuleNamePortability_go___closed__0));
v___x_1037_ = 1;
lean_inc(v_mainModule_1016_);
v___x_1038_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mainModule_1016_, v___x_1037_);
v___x_1039_ = lean_string_append(v___x_1036_, v___x_1038_);
lean_dec_ref(v___x_1038_);
v___x_1040_ = ((lean_object*)(l___private_Lean_Elab_Import_0__Lean_Elab_checkModuleNamePortability_go___closed__1));
v___x_1041_ = lean_string_append(v___x_1039_, v___x_1040_);
v___x_1042_ = lean_string_append(v___x_1041_, v_val_1025_);
lean_dec(v_val_1025_);
if (v_isShared_1028_ == 0)
{
lean_ctor_set_tag(v___x_1027_, 3);
lean_ctor_set(v___x_1027_, 0, v___x_1042_);
v___x_1044_ = v___x_1027_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v___x_1042_);
v___x_1044_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1045_ = l_Lean_MessageData_ofFormat(v___x_1044_);
lean_inc_ref(v_fileName_1029_);
v___x_1046_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1046_, 0, v_fileName_1029_);
lean_ctor_set(v___x_1046_, 1, v___x_1031_);
lean_ctor_set(v___x_1046_, 2, v___x_1032_);
lean_ctor_set(v___x_1046_, 3, v___x_1035_);
lean_ctor_set(v___x_1046_, 4, v___x_1045_);
lean_ctor_set_uint8(v___x_1046_, sizeof(void*)*5, v___x_1033_);
lean_ctor_set_uint8(v___x_1046_, sizeof(void*)*5 + 1, v___x_1034_);
lean_ctor_set_uint8(v___x_1046_, sizeof(void*)*5 + 2, v___x_1033_);
v___x_1047_ = l_Lean_MessageLog_add(v___x_1046_, v_a_1020_);
v_a_1019_ = v_pre_1021_;
v_a_1020_ = v___x_1047_;
goto _start;
}
}
}
}
default: 
{
lean_object* v_pre_1051_; 
v_pre_1051_ = lean_ctor_get(v_a_1019_, 0);
lean_inc(v_pre_1051_);
lean_dec_ref_known(v_a_1019_, 2);
v_a_1019_ = v_pre_1051_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Import_0__Lean_Elab_checkModuleNamePortability_go___boxed(lean_object* v_mainModule_1053_, lean_object* v_inputCtx_1054_, lean_object* v_startPos_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l___private_Lean_Elab_Import_0__Lean_Elab_checkModuleNamePortability_go(v_mainModule_1053_, v_inputCtx_1054_, v_startPos_1055_, v_a_1056_, v_a_1057_);
lean_dec(v_startPos_1055_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkModuleNamePortability(lean_object* v_mainModule_1059_, lean_object* v_inputCtx_1060_, lean_object* v_startPos_1061_, lean_object* v_messages_1062_){
_start:
{
lean_object* v___x_1063_; 
lean_inc(v_mainModule_1059_);
v___x_1063_ = l___private_Lean_Elab_Import_0__Lean_Elab_checkModuleNamePortability_go(v_mainModule_1059_, v_inputCtx_1060_, v_startPos_1061_, v_mainModule_1059_, v_messages_1062_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkModuleNamePortability___boxed(lean_object* v_mainModule_1064_, lean_object* v_inputCtx_1065_, lean_object* v_startPos_1066_, lean_object* v_messages_1067_){
_start:
{
lean_object* v_res_1068_; 
v_res_1068_ = l_Lean_Elab_checkModuleNamePortability(v_mainModule_1064_, v_inputCtx_1065_, v_startPos_1066_, v_messages_1067_);
lean_dec(v_startPos_1066_);
return v_res_1068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_processHeaderCore___lam__0(lean_object* v_package_x3f_1069_, lean_object* v_ps_1070_){
_start:
{
lean_object* v_importedEntries_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1078_; 
v_importedEntries_1071_ = lean_ctor_get(v_ps_1070_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v_ps_1070_);
if (v_isSharedCheck_1078_ == 0)
{
lean_object* v_unused_1079_; 
v_unused_1079_ = lean_ctor_get(v_ps_1070_, 1);
lean_dec(v_unused_1079_);
v___x_1073_ = v_ps_1070_;
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_importedEntries_1071_);
lean_dec(v_ps_1070_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1076_; 
if (v_isShared_1074_ == 0)
{
lean_ctor_set(v___x_1073_, 1, v_package_x3f_1069_);
v___x_1076_ = v___x_1073_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v_importedEntries_1071_);
lean_ctor_set(v_reuseFailAlloc_1077_, 1, v_package_x3f_1069_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_processHeaderCore(lean_object* v_startPos_1080_, lean_object* v_imports_1081_, uint8_t v_isModule_1082_, lean_object* v_opts_1083_, lean_object* v_messages_1084_, lean_object* v_inputCtx_1085_, uint32_t v_trustLevel_1086_, lean_object* v_plugins_1087_, uint8_t v_leakEnv_1088_, lean_object* v_mainModule_1089_, lean_object* v_package_x3f_1090_, lean_object* v_arts_1091_, lean_object* v_headerStx_x3f_1092_, lean_object* v_origHeaderStx_x3f_1093_){
_start:
{
lean_object* v___y_1096_; lean_object* v___y_1097_; lean_object* v___f_1102_; lean_object* v_fst_1104_; lean_object* v_snd_1105_; uint8_t v___x_1116_; uint8_t v___y_1118_; 
v___f_1102_ = lean_alloc_closure((void*)(l_Lean_Elab_processHeaderCore___lam__0), 2, 1);
lean_closure_set(v___f_1102_, 0, v_package_x3f_1090_);
v___x_1116_ = 1;
if (v_isModule_1082_ == 0)
{
uint8_t v___x_1151_; 
v___x_1151_ = 2;
v___y_1118_ = v___x_1151_;
goto v___jp_1117_;
}
else
{
lean_object* v___x_1152_; uint8_t v___x_1153_; 
v___x_1152_ = l_Lean_Elab_inServer;
v___x_1153_ = l_Lean_Option_get___at___00Lean_Elab_checkDeprecatedImports_spec__0(v_opts_1083_, v___x_1152_);
if (v___x_1153_ == 0)
{
uint8_t v___x_1154_; 
v___x_1154_ = 0;
v___y_1118_ = v___x_1154_;
goto v___jp_1117_;
}
else
{
uint8_t v___x_1155_; 
v___x_1155_ = 1;
v___y_1118_ = v___x_1155_;
goto v___jp_1117_;
}
}
v___jp_1095_:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
lean_inc(v_startPos_1080_);
lean_inc_ref(v_inputCtx_1085_);
v___x_1098_ = l_Lean_Elab_checkDeprecatedImports(v___y_1097_, v_imports_1081_, v_opts_1083_, v_inputCtx_1085_, v_startPos_1080_, v___y_1096_, v_headerStx_x3f_1092_, v_origHeaderStx_x3f_1093_);
lean_dec_ref(v_imports_1081_);
lean_inc(v_mainModule_1089_);
v___x_1099_ = l___private_Lean_Elab_Import_0__Lean_Elab_checkModuleNamePortability_go(v_mainModule_1089_, v_inputCtx_1085_, v_startPos_1080_, v_mainModule_1089_, v___x_1098_);
lean_dec(v_startPos_1080_);
v___x_1100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1100_, 0, v___y_1097_);
lean_ctor_set(v___x_1100_, 1, v___x_1099_);
v___x_1101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1100_);
return v___x_1101_;
}
v___jp_1103_:
{
lean_object* v___x_1106_; lean_object* v_toEnvExtension_1107_; lean_object* v_asyncMode_1108_; uint8_t v_logWrites_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; uint8_t v___x_1112_; 
v___x_1106_ = l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
v_toEnvExtension_1107_ = lean_ctor_get(v___x_1106_, 0);
v_asyncMode_1108_ = lean_ctor_get(v_toEnvExtension_1107_, 2);
v_logWrites_1109_ = lean_ctor_get_uint8(v_toEnvExtension_1107_, sizeof(void*)*6);
lean_inc(v_mainModule_1089_);
v___x_1110_ = l_Lean_Environment_setMainModule(v_fst_1104_, v_mainModule_1089_);
v___x_1111_ = lean_box(0);
v___x_1112_ = 1;
if (v_logWrites_1109_ == 0)
{
lean_object* v___x_1113_; 
lean_inc_ref(v_toEnvExtension_1107_);
v___x_1113_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1107_, v___x_1110_, v___f_1102_, v_asyncMode_1108_, v___x_1111_, v___x_1112_);
v___y_1096_ = v_snd_1105_;
v___y_1097_ = v___x_1113_;
goto v___jp_1095_;
}
else
{
lean_object* v___x_1114_; lean_object* v___x_1115_; 
lean_inc_ref_n(v_toEnvExtension_1107_, 2);
v___x_1114_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1107_, v___x_1110_);
lean_dec_ref(v___x_1110_);
v___x_1115_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1107_, v___x_1114_, v___f_1102_, v_asyncMode_1108_, v___x_1111_, v___x_1112_);
v___y_1096_ = v_snd_1105_;
v___y_1097_ = v___x_1115_;
goto v___jp_1095_;
}
}
v___jp_1117_:
{
lean_object* v___x_1119_; 
lean_inc_ref(v_opts_1083_);
lean_inc_ref(v_imports_1081_);
v___x_1119_ = l_Lean_importModules(v_imports_1081_, v_opts_1083_, v_trustLevel_1086_, v_plugins_1087_, v_leakEnv_1088_, v___x_1116_, v___y_1118_, v_arts_1091_);
if (lean_obj_tag(v___x_1119_) == 0)
{
lean_object* v_a_1120_; 
v_a_1120_ = lean_ctor_get(v___x_1119_, 0);
lean_inc(v_a_1120_);
lean_dec_ref_known(v___x_1119_, 1);
v_fst_1104_ = v_a_1120_;
v_snd_1105_ = v_messages_1084_;
goto v___jp_1103_;
}
else
{
lean_object* v_a_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1150_; 
v_a_1121_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1150_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1123_ = v___x_1119_;
v_isShared_1124_ = v_isSharedCheck_1150_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_a_1121_);
lean_dec(v___x_1119_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1150_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
uint32_t v___x_1125_; lean_object* v___x_1126_; 
v___x_1125_ = 0;
v___x_1126_ = l_Lean_mkEmptyEnvironment(v___x_1125_);
if (lean_obj_tag(v___x_1126_) == 0)
{
lean_object* v_a_1127_; lean_object* v_fileName_1128_; lean_object* v_fileMap_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; uint8_t v___x_1132_; uint8_t v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1137_; 
v_a_1127_ = lean_ctor_get(v___x_1126_, 0);
lean_inc(v_a_1127_);
lean_dec_ref_known(v___x_1126_, 1);
v_fileName_1128_ = lean_ctor_get(v_inputCtx_1085_, 1);
v_fileMap_1129_ = lean_ctor_get(v_inputCtx_1085_, 2);
lean_inc_ref(v_fileMap_1129_);
v___x_1130_ = l_Lean_FileMap_toPosition(v_fileMap_1129_, v_startPos_1080_);
v___x_1131_ = lean_box(0);
v___x_1132_ = 0;
v___x_1133_ = 2;
v___x_1134_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___closed__0));
v___x_1135_ = lean_io_error_to_string(v_a_1121_);
if (v_isShared_1124_ == 0)
{
lean_ctor_set_tag(v___x_1123_, 3);
lean_ctor_set(v___x_1123_, 0, v___x_1135_);
v___x_1137_ = v___x_1123_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v___x_1135_);
v___x_1137_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1138_ = l_Lean_MessageData_ofFormat(v___x_1137_);
lean_inc_ref(v_fileName_1128_);
v___x_1139_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1139_, 0, v_fileName_1128_);
lean_ctor_set(v___x_1139_, 1, v___x_1130_);
lean_ctor_set(v___x_1139_, 2, v___x_1131_);
lean_ctor_set(v___x_1139_, 3, v___x_1134_);
lean_ctor_set(v___x_1139_, 4, v___x_1138_);
lean_ctor_set_uint8(v___x_1139_, sizeof(void*)*5, v___x_1132_);
lean_ctor_set_uint8(v___x_1139_, sizeof(void*)*5 + 1, v___x_1133_);
lean_ctor_set_uint8(v___x_1139_, sizeof(void*)*5 + 2, v___x_1132_);
v___x_1140_ = l_Lean_MessageLog_add(v___x_1139_, v_messages_1084_);
v_fst_1104_ = v_a_1127_;
v_snd_1105_ = v___x_1140_;
goto v___jp_1103_;
}
}
else
{
lean_object* v_a_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1149_; 
lean_del_object(v___x_1123_);
lean_dec(v_a_1121_);
lean_dec_ref(v___f_1102_);
lean_dec(v_origHeaderStx_x3f_1093_);
lean_dec(v_headerStx_x3f_1092_);
lean_dec(v_mainModule_1089_);
lean_dec_ref(v_inputCtx_1085_);
lean_dec_ref(v_messages_1084_);
lean_dec_ref(v_opts_1083_);
lean_dec_ref(v_imports_1081_);
lean_dec(v_startPos_1080_);
v_a_1142_ = lean_ctor_get(v___x_1126_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1144_ = v___x_1126_;
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_a_1142_);
lean_dec(v___x_1126_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1147_; 
if (v_isShared_1145_ == 0)
{
v___x_1147_ = v___x_1144_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_a_1142_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_processHeaderCore___boxed(lean_object* v_startPos_1156_, lean_object* v_imports_1157_, lean_object* v_isModule_1158_, lean_object* v_opts_1159_, lean_object* v_messages_1160_, lean_object* v_inputCtx_1161_, lean_object* v_trustLevel_1162_, lean_object* v_plugins_1163_, lean_object* v_leakEnv_1164_, lean_object* v_mainModule_1165_, lean_object* v_package_x3f_1166_, lean_object* v_arts_1167_, lean_object* v_headerStx_x3f_1168_, lean_object* v_origHeaderStx_x3f_1169_, lean_object* v_a_1170_){
_start:
{
uint8_t v_isModule_boxed_1171_; uint32_t v_trustLevel_boxed_1172_; uint8_t v_leakEnv_boxed_1173_; lean_object* v_res_1174_; 
v_isModule_boxed_1171_ = lean_unbox(v_isModule_1158_);
v_trustLevel_boxed_1172_ = lean_unbox_uint32(v_trustLevel_1162_);
lean_dec(v_trustLevel_1162_);
v_leakEnv_boxed_1173_ = lean_unbox(v_leakEnv_1164_);
v_res_1174_ = l_Lean_Elab_processHeaderCore(v_startPos_1156_, v_imports_1157_, v_isModule_boxed_1171_, v_opts_1159_, v_messages_1160_, v_inputCtx_1161_, v_trustLevel_boxed_1172_, v_plugins_1163_, v_leakEnv_boxed_1173_, v_mainModule_1165_, v_package_x3f_1166_, v_arts_1167_, v_headerStx_x3f_1168_, v_origHeaderStx_x3f_1169_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_processHeader(lean_object* v_header_1175_, lean_object* v_opts_1176_, lean_object* v_messages_1177_, lean_object* v_inputCtx_1178_, uint32_t v_trustLevel_1179_, lean_object* v_plugins_1180_, uint8_t v_leakEnv_1181_, lean_object* v_mainModule_1182_){
_start:
{
lean_object* v___x_1184_; uint8_t v___x_1185_; lean_object* v___x_1186_; uint8_t v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1184_ = l_Lean_Elab_HeaderSyntax_startPos(v_header_1175_);
v___x_1185_ = 1;
lean_inc(v_header_1175_);
v___x_1186_ = l_Lean_Elab_HeaderSyntax_imports(v_header_1175_, v___x_1185_);
v___x_1187_ = l_Lean_Elab_HeaderSyntax_isModule(v_header_1175_);
v___x_1188_ = lean_box(0);
v___x_1189_ = lean_box(1);
v___x_1190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1190_, 0, v_header_1175_);
v___x_1191_ = l_Lean_Elab_processHeaderCore(v___x_1184_, v___x_1186_, v___x_1187_, v_opts_1176_, v_messages_1177_, v_inputCtx_1178_, v_trustLevel_1179_, v_plugins_1180_, v_leakEnv_1181_, v_mainModule_1182_, v___x_1188_, v___x_1189_, v___x_1190_, v___x_1188_);
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_processHeader___boxed(lean_object* v_header_1192_, lean_object* v_opts_1193_, lean_object* v_messages_1194_, lean_object* v_inputCtx_1195_, lean_object* v_trustLevel_1196_, lean_object* v_plugins_1197_, lean_object* v_leakEnv_1198_, lean_object* v_mainModule_1199_, lean_object* v_a_1200_){
_start:
{
uint32_t v_trustLevel_boxed_1201_; uint8_t v_leakEnv_boxed_1202_; lean_object* v_res_1203_; 
v_trustLevel_boxed_1201_ = lean_unbox_uint32(v_trustLevel_1196_);
lean_dec(v_trustLevel_1196_);
v_leakEnv_boxed_1202_ = lean_unbox(v_leakEnv_1198_);
v_res_1203_ = l_Lean_Elab_processHeader(v_header_1192_, v_opts_1193_, v_messages_1194_, v_inputCtx_1195_, v_trustLevel_boxed_1201_, v_plugins_1197_, v_leakEnv_boxed_1202_, v_mainModule_1199_);
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_parseImports(lean_object* v_input_1205_, lean_object* v_fileName_1206_){
_start:
{
lean_object* v___y_1209_; 
if (lean_obj_tag(v_fileName_1206_) == 0)
{
lean_object* v___x_1254_; 
v___x_1254_ = ((lean_object*)(l_Lean_Elab_parseImports___closed__0));
v___y_1209_ = v___x_1254_;
goto v___jp_1208_;
}
else
{
lean_object* v_val_1255_; 
v_val_1255_ = lean_ctor_get(v_fileName_1206_, 0);
lean_inc(v_val_1255_);
lean_dec_ref_known(v_fileName_1206_, 1);
v___y_1209_ = v_val_1255_;
goto v___jp_1208_;
}
v___jp_1208_:
{
uint8_t v___x_1210_; lean_object* v___x_1211_; lean_object* v_inputCtx_1212_; lean_object* v___x_1213_; 
v___x_1210_ = 1;
v___x_1211_ = lean_string_utf8_byte_size(v_input_1205_);
v_inputCtx_1212_ = l_Lean_Parser_mkInputContext___redArg(v_input_1205_, v___y_1209_, v___x_1210_, v___x_1211_);
lean_inc_ref(v_inputCtx_1212_);
v___x_1213_ = l_Lean_Parser_parseHeader(v_inputCtx_1212_);
if (lean_obj_tag(v___x_1213_) == 0)
{
lean_object* v_a_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1245_; 
v_a_1214_ = lean_ctor_get(v___x_1213_, 0);
v_isSharedCheck_1245_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1216_ = v___x_1213_;
v_isShared_1217_ = v_isSharedCheck_1245_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_a_1214_);
lean_dec(v___x_1213_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1245_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v_snd_1218_; lean_object* v_fst_1219_; lean_object* v_fst_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1243_; 
v_snd_1218_ = lean_ctor_get(v_a_1214_, 1);
lean_inc(v_snd_1218_);
v_fst_1219_ = lean_ctor_get(v_snd_1218_, 0);
lean_inc(v_fst_1219_);
v_fst_1220_ = lean_ctor_get(v_a_1214_, 0);
v_isSharedCheck_1243_ = !lean_is_exclusive(v_a_1214_);
if (v_isSharedCheck_1243_ == 0)
{
lean_object* v_unused_1244_; 
v_unused_1244_ = lean_ctor_get(v_a_1214_, 1);
lean_dec(v_unused_1244_);
v___x_1222_ = v_a_1214_;
v_isShared_1223_ = v_isSharedCheck_1243_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_fst_1220_);
lean_dec(v_a_1214_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1243_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v_snd_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1241_; 
v_snd_1224_ = lean_ctor_get(v_snd_1218_, 1);
v_isSharedCheck_1241_ = !lean_is_exclusive(v_snd_1218_);
if (v_isSharedCheck_1241_ == 0)
{
lean_object* v_unused_1242_; 
v_unused_1242_ = lean_ctor_get(v_snd_1218_, 0);
lean_dec(v_unused_1242_);
v___x_1226_ = v_snd_1218_;
v_isShared_1227_ = v_isSharedCheck_1241_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_snd_1224_);
lean_dec(v_snd_1218_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1241_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v_fileMap_1228_; lean_object* v_pos_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1233_; 
v_fileMap_1228_ = lean_ctor_get(v_inputCtx_1212_, 2);
lean_inc_ref(v_fileMap_1228_);
lean_dec_ref(v_inputCtx_1212_);
v_pos_1229_ = lean_ctor_get(v_fst_1219_, 0);
lean_inc(v_pos_1229_);
lean_dec(v_fst_1219_);
v___x_1230_ = l_Lean_Elab_HeaderSyntax_imports(v_fst_1220_, v___x_1210_);
v___x_1231_ = l_Lean_FileMap_toPosition(v_fileMap_1228_, v_pos_1229_);
lean_dec(v_pos_1229_);
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 0, v___x_1231_);
v___x_1233_ = v___x_1226_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v___x_1231_);
lean_ctor_set(v_reuseFailAlloc_1240_, 1, v_snd_1224_);
v___x_1233_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
lean_object* v___x_1235_; 
if (v_isShared_1223_ == 0)
{
lean_ctor_set(v___x_1222_, 1, v___x_1233_);
lean_ctor_set(v___x_1222_, 0, v___x_1230_);
v___x_1235_ = v___x_1222_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v___x_1230_);
lean_ctor_set(v_reuseFailAlloc_1239_, 1, v___x_1233_);
v___x_1235_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
lean_object* v___x_1237_; 
if (v_isShared_1217_ == 0)
{
lean_ctor_set(v___x_1216_, 0, v___x_1235_);
v___x_1237_ = v___x_1216_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v___x_1235_);
v___x_1237_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
return v___x_1237_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1253_; 
lean_dec_ref(v_inputCtx_1212_);
v_a_1246_ = lean_ctor_get(v___x_1213_, 0);
v_isSharedCheck_1253_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1248_ = v___x_1213_;
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_a_1246_);
lean_dec(v___x_1213_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1251_; 
if (v_isShared_1249_ == 0)
{
v___x_1251_ = v___x_1248_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v_a_1246_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
return v___x_1251_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_parseImports___boxed(lean_object* v_input_1256_, lean_object* v_fileName_1257_, lean_object* v_a_1258_){
_start:
{
lean_object* v_res_1259_; 
v_res_1259_ = l_Lean_Elab_parseImports(v_input_1256_, v_fileName_1257_);
return v_res_1259_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00Lean_Elab_printImports_spec__0_spec__0(lean_object* v_s_1260_){
_start:
{
lean_object* v___x_1262_; lean_object* v_putStr_1263_; lean_object* v___x_1264_; 
v___x_1262_ = lean_get_stdout();
v_putStr_1263_ = lean_ctor_get(v___x_1262_, 4);
lean_inc_ref(v_putStr_1263_);
lean_dec_ref(v___x_1262_);
v___x_1264_ = lean_apply_2(v_putStr_1263_, v_s_1260_, lean_box(0));
return v___x_1264_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00Lean_Elab_printImports_spec__0_spec__0___boxed(lean_object* v_s_1265_, lean_object* v_a_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l_IO_print___at___00IO_println___at___00Lean_Elab_printImports_spec__0_spec__0(v_s_1265_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00Lean_Elab_printImports_spec__0(lean_object* v_s_1268_){
_start:
{
uint32_t v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1270_ = 10;
v___x_1271_ = lean_string_push(v_s_1268_, v___x_1270_);
v___x_1272_ = l_IO_print___at___00IO_println___at___00Lean_Elab_printImports_spec__0_spec__0(v___x_1271_);
return v___x_1272_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00Lean_Elab_printImports_spec__0___boxed(lean_object* v_s_1273_, lean_object* v_a_1274_){
_start:
{
lean_object* v_res_1275_; 
v_res_1275_ = l_IO_println___at___00Lean_Elab_printImports_spec__0(v_s_1273_);
return v_res_1275_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImports_spec__1(lean_object* v_as_1276_, size_t v_sz_1277_, size_t v_i_1278_, lean_object* v_b_1279_){
_start:
{
uint8_t v___x_1281_; 
v___x_1281_ = lean_usize_dec_lt(v_i_1278_, v_sz_1277_);
if (v___x_1281_ == 0)
{
lean_object* v___x_1282_; 
v___x_1282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1282_, 0, v_b_1279_);
return v___x_1282_;
}
else
{
lean_object* v_a_1283_; lean_object* v_module_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; 
v_a_1283_ = lean_array_uget_borrowed(v_as_1276_, v_i_1278_);
v_module_1284_ = lean_ctor_get(v_a_1283_, 0);
v___x_1285_ = lean_box(0);
lean_inc(v_module_1284_);
v___x_1286_ = l_Lean_findOLean(v_module_1284_);
if (lean_obj_tag(v___x_1286_) == 0)
{
lean_object* v_a_1287_; lean_object* v___x_1288_; 
v_a_1287_ = lean_ctor_get(v___x_1286_, 0);
lean_inc(v_a_1287_);
lean_dec_ref_known(v___x_1286_, 1);
v___x_1288_ = l_IO_println___at___00Lean_Elab_printImports_spec__0(v_a_1287_);
if (lean_obj_tag(v___x_1288_) == 0)
{
size_t v___x_1289_; size_t v___x_1290_; 
lean_dec_ref_known(v___x_1288_, 1);
v___x_1289_ = ((size_t)1ULL);
v___x_1290_ = lean_usize_add(v_i_1278_, v___x_1289_);
v_i_1278_ = v___x_1290_;
v_b_1279_ = v___x_1285_;
goto _start;
}
else
{
return v___x_1288_;
}
}
else
{
lean_object* v_a_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1299_; 
v_a_1292_ = lean_ctor_get(v___x_1286_, 0);
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1294_ = v___x_1286_;
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_a_1292_);
lean_dec(v___x_1286_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1297_; 
if (v_isShared_1295_ == 0)
{
v___x_1297_ = v___x_1294_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_a_1292_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImports_spec__1___boxed(lean_object* v_as_1300_, lean_object* v_sz_1301_, lean_object* v_i_1302_, lean_object* v_b_1303_, lean_object* v___y_1304_){
_start:
{
size_t v_sz_boxed_1305_; size_t v_i_boxed_1306_; lean_object* v_res_1307_; 
v_sz_boxed_1305_ = lean_unbox_usize(v_sz_1301_);
lean_dec(v_sz_1301_);
v_i_boxed_1306_ = lean_unbox_usize(v_i_1302_);
lean_dec(v_i_1302_);
v_res_1307_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImports_spec__1(v_as_1300_, v_sz_boxed_1305_, v_i_boxed_1306_, v_b_1303_);
lean_dec_ref(v_as_1300_);
return v_res_1307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_printImports(lean_object* v_input_1308_, lean_object* v_fileName_1309_){
_start:
{
lean_object* v___x_1311_; 
v___x_1311_ = l_Lean_Elab_parseImports(v_input_1308_, v_fileName_1309_);
if (lean_obj_tag(v___x_1311_) == 0)
{
lean_object* v_a_1312_; lean_object* v_fst_1313_; lean_object* v___x_1314_; size_t v_sz_1315_; size_t v___x_1316_; lean_object* v___x_1317_; 
v_a_1312_ = lean_ctor_get(v___x_1311_, 0);
lean_inc(v_a_1312_);
lean_dec_ref_known(v___x_1311_, 1);
v_fst_1313_ = lean_ctor_get(v_a_1312_, 0);
lean_inc(v_fst_1313_);
lean_dec(v_a_1312_);
v___x_1314_ = lean_box(0);
v_sz_1315_ = lean_array_size(v_fst_1313_);
v___x_1316_ = ((size_t)0ULL);
v___x_1317_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImports_spec__1(v_fst_1313_, v_sz_1315_, v___x_1316_, v___x_1314_);
lean_dec(v_fst_1313_);
if (lean_obj_tag(v___x_1317_) == 0)
{
lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1324_; 
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1324_ == 0)
{
lean_object* v_unused_1325_; 
v_unused_1325_ = lean_ctor_get(v___x_1317_, 0);
lean_dec(v_unused_1325_);
v___x_1319_ = v___x_1317_;
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
else
{
lean_dec(v___x_1317_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1322_; 
if (v_isShared_1320_ == 0)
{
lean_ctor_set(v___x_1319_, 0, v___x_1314_);
v___x_1322_ = v___x_1319_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v___x_1314_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
else
{
return v___x_1317_;
}
}
else
{
lean_object* v_a_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1333_; 
v_a_1326_ = lean_ctor_get(v___x_1311_, 0);
v_isSharedCheck_1333_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1328_ = v___x_1311_;
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_a_1326_);
lean_dec(v___x_1311_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1331_; 
if (v_isShared_1329_ == 0)
{
v___x_1331_ = v___x_1328_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_a_1326_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_printImports___boxed(lean_object* v_input_1334_, lean_object* v_fileName_1335_, lean_object* v_a_1336_){
_start:
{
lean_object* v_res_1337_; 
v_res_1337_ = l_Lean_Elab_printImports(v_input_1334_, v_fileName_1335_);
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImportSrcs_spec__0(lean_object* v_a_1338_, lean_object* v_as_1339_, size_t v_sz_1340_, size_t v_i_1341_, lean_object* v_b_1342_){
_start:
{
uint8_t v___x_1344_; 
v___x_1344_ = lean_usize_dec_lt(v_i_1341_, v_sz_1340_);
if (v___x_1344_ == 0)
{
lean_object* v___x_1345_; 
lean_dec(v_a_1338_);
v___x_1345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1345_, 0, v_b_1342_);
return v___x_1345_;
}
else
{
lean_object* v_a_1346_; lean_object* v_module_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
v_a_1346_ = lean_array_uget_borrowed(v_as_1339_, v_i_1341_);
v_module_1347_ = lean_ctor_get(v_a_1346_, 0);
v___x_1348_ = lean_box(0);
lean_inc(v_module_1347_);
lean_inc(v_a_1338_);
v___x_1349_ = l_Lean_findLean(v_a_1338_, v_module_1347_);
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_object* v_a_1350_; lean_object* v___x_1351_; 
v_a_1350_ = lean_ctor_get(v___x_1349_, 0);
lean_inc(v_a_1350_);
lean_dec_ref_known(v___x_1349_, 1);
v___x_1351_ = l_IO_println___at___00Lean_Elab_printImports_spec__0(v_a_1350_);
if (lean_obj_tag(v___x_1351_) == 0)
{
size_t v___x_1352_; size_t v___x_1353_; 
lean_dec_ref_known(v___x_1351_, 1);
v___x_1352_ = ((size_t)1ULL);
v___x_1353_ = lean_usize_add(v_i_1341_, v___x_1352_);
v_i_1341_ = v___x_1353_;
v_b_1342_ = v___x_1348_;
goto _start;
}
else
{
lean_dec(v_a_1338_);
return v___x_1351_;
}
}
else
{
lean_object* v_a_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1362_; 
lean_dec(v_a_1338_);
v_a_1355_ = lean_ctor_get(v___x_1349_, 0);
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1357_ = v___x_1349_;
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_a_1355_);
lean_dec(v___x_1349_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1360_; 
if (v_isShared_1358_ == 0)
{
v___x_1360_ = v___x_1357_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_a_1355_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImportSrcs_spec__0___boxed(lean_object* v_a_1363_, lean_object* v_as_1364_, lean_object* v_sz_1365_, lean_object* v_i_1366_, lean_object* v_b_1367_, lean_object* v___y_1368_){
_start:
{
size_t v_sz_boxed_1369_; size_t v_i_boxed_1370_; lean_object* v_res_1371_; 
v_sz_boxed_1369_ = lean_unbox_usize(v_sz_1365_);
lean_dec(v_sz_1365_);
v_i_boxed_1370_ = lean_unbox_usize(v_i_1366_);
lean_dec(v_i_1366_);
v_res_1371_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImportSrcs_spec__0(v_a_1363_, v_as_1364_, v_sz_boxed_1369_, v_i_boxed_1370_, v_b_1367_);
lean_dec_ref(v_as_1364_);
return v_res_1371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_printImportSrcs(lean_object* v_input_1372_, lean_object* v_fileName_1373_){
_start:
{
lean_object* v___x_1375_; 
v___x_1375_ = l_Lean_getSrcSearchPath();
if (lean_obj_tag(v___x_1375_) == 0)
{
lean_object* v_a_1376_; lean_object* v___x_1377_; 
v_a_1376_ = lean_ctor_get(v___x_1375_, 0);
lean_inc(v_a_1376_);
lean_dec_ref_known(v___x_1375_, 1);
v___x_1377_ = l_Lean_Elab_parseImports(v_input_1372_, v_fileName_1373_);
if (lean_obj_tag(v___x_1377_) == 0)
{
lean_object* v_a_1378_; lean_object* v_fst_1379_; lean_object* v___x_1380_; size_t v_sz_1381_; size_t v___x_1382_; lean_object* v___x_1383_; 
v_a_1378_ = lean_ctor_get(v___x_1377_, 0);
lean_inc(v_a_1378_);
lean_dec_ref_known(v___x_1377_, 1);
v_fst_1379_ = lean_ctor_get(v_a_1378_, 0);
lean_inc(v_fst_1379_);
lean_dec(v_a_1378_);
v___x_1380_ = lean_box(0);
v_sz_1381_ = lean_array_size(v_fst_1379_);
v___x_1382_ = ((size_t)0ULL);
v___x_1383_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImportSrcs_spec__0(v_a_1376_, v_fst_1379_, v_sz_1381_, v___x_1382_, v___x_1380_);
lean_dec(v_fst_1379_);
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1390_; 
v_isSharedCheck_1390_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1390_ == 0)
{
lean_object* v_unused_1391_; 
v_unused_1391_ = lean_ctor_get(v___x_1383_, 0);
lean_dec(v_unused_1391_);
v___x_1385_ = v___x_1383_;
v_isShared_1386_ = v_isSharedCheck_1390_;
goto v_resetjp_1384_;
}
else
{
lean_dec(v___x_1383_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1390_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v___x_1388_; 
if (v_isShared_1386_ == 0)
{
lean_ctor_set(v___x_1385_, 0, v___x_1380_);
v___x_1388_ = v___x_1385_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v___x_1380_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
return v___x_1388_;
}
}
}
else
{
return v___x_1383_;
}
}
else
{
lean_object* v_a_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1399_; 
lean_dec(v_a_1376_);
v_a_1392_ = lean_ctor_get(v___x_1377_, 0);
v_isSharedCheck_1399_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1394_ = v___x_1377_;
v_isShared_1395_ = v_isSharedCheck_1399_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_a_1392_);
lean_dec(v___x_1377_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1399_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1397_; 
if (v_isShared_1395_ == 0)
{
v___x_1397_ = v___x_1394_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v_a_1392_);
v___x_1397_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
return v___x_1397_;
}
}
}
}
else
{
lean_object* v_a_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1407_; 
lean_dec(v_fileName_1373_);
lean_dec_ref(v_input_1372_);
v_a_1400_ = lean_ctor_get(v___x_1375_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1402_ = v___x_1375_;
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_a_1400_);
lean_dec(v___x_1375_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1405_; 
if (v_isShared_1403_ == 0)
{
v___x_1405_ = v___x_1402_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v_a_1400_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_printImportSrcs___boxed(lean_object* v_input_1408_, lean_object* v_fileName_1409_, lean_object* v_a_1410_){
_start:
{
lean_object* v_res_1411_; 
v_res_1411_ = l_Lean_Elab_printImportSrcs(v_input_1408_, v_fileName_1409_);
return v_res_1411_;
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

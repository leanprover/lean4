// Lean compiler output
// Module: Lean.Elab.Import
// Imports: public import Lean.Parser.Module meta import Lean.Parser.Module import Lean.Compiler.ModPkgExt public import Lean.DeprecatedModule
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
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
lean_object* l_Lean_Syntax_getTrailing_x3f(lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_String_instDecidableLtRaw___aux__1(lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
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
lean_object* l_Lean_importModules(lean_object*, lean_object*, uint32_t, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*);
lean_object* lean_mk_empty_environment(uint32_t);
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
lean_dec_ref(v___x_3_);
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
v___x_38_ = lean_unsigned_to_nat(37u);
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
lean_object* v___x_66_; lean_object* v_v_67_; lean_object* v___x_68_; lean_object* v_bs_x27_69_; lean_object* v___y_71_; lean_object* v___y_77_; uint8_t v___y_78_; uint8_t v___y_79_; lean_object* v___y_80_; uint8_t v___y_81_; lean_object* v___y_86_; uint8_t v___y_87_; uint8_t v___y_88_; lean_object* v___y_89_; uint8_t v___y_90_; lean_object* v___y_92_; lean_object* v___y_93_; uint8_t v___y_94_; lean_object* v___y_95_; uint8_t v___y_96_; uint8_t v___x_98_; 
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
v___y_94_ = v___x_107_;
v___y_95_ = v___y_103_;
v___y_96_ = v___x_113_;
goto v___jp_91_;
}
else
{
lean_dec_ref(v_allTk_104_);
v___y_92_ = v___x_112_;
v___y_93_ = v___y_102_;
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
v___y_102_ = v___y_116_;
v___y_103_ = v_metaTk_117_;
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
v___y_102_ = v___y_116_;
v___y_103_ = v_metaTk_117_;
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
if (lean_obj_tag(v___y_80_) == 0)
{
uint8_t v___x_82_; lean_object* v___x_83_; 
v___x_82_ = 0;
v___x_83_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_83_, 0, v___y_77_);
lean_ctor_set_uint8(v___x_83_, sizeof(void*)*1, v___y_78_);
lean_ctor_set_uint8(v___x_83_, sizeof(void*)*1 + 1, v___y_81_);
lean_ctor_set_uint8(v___x_83_, sizeof(void*)*1 + 2, v___x_82_);
v___y_71_ = v___x_83_;
goto v___jp_70_;
}
else
{
lean_object* v___x_84_; 
lean_dec_ref(v___y_80_);
v___x_84_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_84_, 0, v___y_77_);
lean_ctor_set_uint8(v___x_84_, sizeof(void*)*1, v___y_78_);
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
if (lean_obj_tag(v___y_93_) == 0)
{
uint8_t v___x_97_; 
v___x_97_ = 0;
v___y_86_ = v___y_92_;
v___y_87_ = v___y_96_;
v___y_88_ = v___y_94_;
v___y_89_ = v___y_95_;
v___y_90_ = v___x_97_;
goto v___jp_85_;
}
else
{
lean_dec_ref(v___y_93_);
if (v___y_94_ == 0)
{
v___y_86_ = v___y_92_;
v___y_87_ = v___y_96_;
v___y_88_ = v___y_94_;
v___y_89_ = v___y_95_;
v___y_90_ = v___y_94_;
goto v___jp_85_;
}
else
{
v___y_77_ = v___y_92_;
v___y_78_ = v___y_96_;
v___y_79_ = v___y_94_;
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
uint8_t v___x_3695__boxed_165_; size_t v_sz_boxed_166_; size_t v_i_boxed_167_; lean_object* v_res_168_; 
v___x_3695__boxed_165_ = lean_unbox(v___x_161_);
v_sz_boxed_166_ = lean_unbox_usize(v_sz_162_);
lean_dec(v_sz_162_);
v_i_boxed_167_ = lean_unbox_usize(v_i_163_);
lean_dec(v_i_163_);
v_res_168_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2(v_moduleTk_160_, v___x_3695__boxed_165_, v_sz_boxed_166_, v_i_boxed_167_, v_bs_164_);
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
v___x_177_ = lean_unsigned_to_nat(38u);
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
lean_object* v___x_212_; lean_object* v___y_214_; lean_object* v___y_215_; lean_object* v___y_218_; lean_object* v___y_219_; lean_object* v_preludeTk_220_; lean_object* v_moduleTk_230_; lean_object* v___x_245_; uint8_t v___x_246_; 
v___x_212_ = lean_unsigned_to_nat(0u);
v___x_245_ = l_Lean_Syntax_getArg(v_stx_198_, v___x_212_);
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
lean_dec(v_stx_198_);
v___x_249_ = lean_obj_once(&l_Lean_Elab_HeaderSyntax_imports___closed__2, &l_Lean_Elab_HeaderSyntax_imports___closed__2_once, _init_l_Lean_Elab_HeaderSyntax_imports___closed__2);
v___x_250_ = l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__0(v___x_249_);
return v___x_250_;
}
else
{
lean_object* v___x_251_; lean_object* v___x_252_; uint8_t v___x_253_; 
v___x_251_ = l_Lean_Syntax_getArg(v___x_245_, v___x_212_);
lean_dec(v___x_245_);
v___x_252_ = ((lean_object*)(l_Lean_Elab_HeaderSyntax_imports___closed__9));
lean_inc(v___x_251_);
v___x_253_ = l_Lean_Syntax_isOfKind(v___x_251_, v___x_252_);
if (v___x_253_ == 0)
{
lean_object* v___x_254_; lean_object* v___x_255_; 
lean_dec(v___x_251_);
lean_dec(v_stx_198_);
v___x_254_ = lean_obj_once(&l_Lean_Elab_HeaderSyntax_imports___closed__2, &l_Lean_Elab_HeaderSyntax_imports___closed__2_once, _init_l_Lean_Elab_HeaderSyntax_imports___closed__2);
v___x_255_ = l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__0(v___x_254_);
return v___x_255_;
}
else
{
lean_object* v_moduleTk_256_; lean_object* v___x_257_; 
v_moduleTk_256_ = l_Lean_Syntax_getArg(v___x_251_, v___x_212_);
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
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v_importsStx_223_; 
v___x_221_ = lean_unsigned_to_nat(2u);
v___x_222_ = l_Lean_Syntax_getArg(v_stx_198_, v___x_221_);
lean_dec(v_stx_198_);
v_importsStx_223_ = l_Lean_Syntax_getArgs(v___x_222_);
lean_dec(v___x_222_);
if (lean_obj_tag(v_preludeTk_220_) == 0)
{
if (v___x_201_ == 0)
{
v___y_214_ = v___y_218_;
v___y_215_ = v_importsStx_223_;
goto v___jp_213_;
}
else
{
if (v_includeInit_199_ == 0)
{
v___y_214_ = v___y_218_;
v___y_215_ = v_importsStx_223_;
goto v___jp_213_;
}
else
{
lean_object* v___x_224_; uint8_t v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_224_ = ((lean_object*)(l_Lean_Elab_HeaderSyntax_imports___closed__5));
v___x_225_ = 0;
v___x_226_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_226_, 0, v___x_224_);
lean_ctor_set_uint8(v___x_226_, sizeof(void*)*1, v___x_225_);
lean_ctor_set_uint8(v___x_226_, sizeof(void*)*1 + 1, v___x_201_);
lean_ctor_set_uint8(v___x_226_, sizeof(void*)*1 + 2, v___x_225_);
v___x_227_ = lean_mk_empty_array_with_capacity(v___y_219_);
v___x_228_ = lean_array_push(v___x_227_, v___x_226_);
v___y_203_ = v___y_218_;
v___y_204_ = v_importsStx_223_;
v___y_205_ = v___x_228_;
goto v___jp_202_;
}
}
}
else
{
lean_dec_ref(v_preludeTk_220_);
v___y_214_ = v___y_218_;
v___y_215_ = v_importsStx_223_;
goto v___jp_213_;
}
}
v___jp_229_:
{
lean_object* v___x_231_; lean_object* v___x_232_; uint8_t v___x_233_; 
v___x_231_ = lean_unsigned_to_nat(1u);
v___x_232_ = l_Lean_Syntax_getArg(v_stx_198_, v___x_231_);
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
lean_dec(v_stx_198_);
v___x_235_ = lean_obj_once(&l_Lean_Elab_HeaderSyntax_imports___closed__2, &l_Lean_Elab_HeaderSyntax_imports___closed__2_once, _init_l_Lean_Elab_HeaderSyntax_imports___closed__2);
v___x_236_ = l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__0(v___x_235_);
return v___x_236_;
}
else
{
lean_object* v___x_237_; lean_object* v___x_238_; uint8_t v___x_239_; 
v___x_237_ = l_Lean_Syntax_getArg(v___x_232_, v___x_212_);
lean_dec(v___x_232_);
v___x_238_ = ((lean_object*)(l_Lean_Elab_HeaderSyntax_imports___closed__7));
lean_inc(v___x_237_);
v___x_239_ = l_Lean_Syntax_isOfKind(v___x_237_, v___x_238_);
if (v___x_239_ == 0)
{
lean_object* v___x_240_; lean_object* v___x_241_; 
lean_dec(v___x_237_);
lean_dec(v_moduleTk_230_);
lean_dec(v_stx_198_);
v___x_240_ = lean_obj_once(&l_Lean_Elab_HeaderSyntax_imports___closed__2, &l_Lean_Elab_HeaderSyntax_imports___closed__2_once, _init_l_Lean_Elab_HeaderSyntax_imports___closed__2);
v___x_241_ = l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__0(v___x_240_);
return v___x_241_;
}
else
{
lean_object* v_preludeTk_242_; lean_object* v___x_243_; 
v_preludeTk_242_ = l_Lean_Syntax_getArg(v___x_237_, v___x_212_);
lean_dec(v___x_237_);
v___x_243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_243_, 0, v_preludeTk_242_);
v___y_218_ = v_moduleTk_230_;
v___y_219_ = v___x_231_;
v_preludeTk_220_ = v___x_243_;
goto v___jp_217_;
}
}
}
else
{
lean_object* v___x_244_; 
lean_dec(v___x_232_);
v___x_244_ = lean_box(0);
v___y_218_ = v_moduleTk_230_;
v___y_219_ = v___x_231_;
v_preludeTk_220_ = v___x_244_;
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
lean_dec_ref(v___x_280_);
if (lean_obj_tag(v_val_282_) == 1)
{
uint8_t v_v_283_; 
v_v_283_ = lean_ctor_get_uint8(v_val_282_, 0);
lean_dec_ref(v_val_282_);
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
lean_dec_ref(v_a_290_);
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
v___x_326_ = l_String_instDecidableLtRaw___aux__1(v_basePos_321_, v___x_324_);
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
lean_dec_ref(v___x_411_);
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
lean_dec_ref(v___x_525_);
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
lean_object* v_opts_568_; lean_object* v_ignoreDeprecatedImports_569_; lean_object* v_ignoreDeprecatedImports_582_; lean_object* v___y_584_; lean_object* v_opts_585_; lean_object* v___y_590_; lean_object* v___y_591_; lean_object* v___y_592_; lean_object* v___y_616_; lean_object* v___y_617_; lean_object* v___y_618_; lean_object* v___y_619_; lean_object* v___y_620_; lean_object* v_moduleTk_621_; lean_object* v_val_631_; 
v_ignoreDeprecatedImports_582_ = l_Lean_NameSet_empty;
if (lean_obj_tag(v_origHeaderStx_x3f_566_) == 0)
{
if (lean_obj_tag(v_headerStx_x3f_565_) == 1)
{
lean_object* v_val_648_; 
v_val_648_ = lean_ctor_get(v_headerStx_x3f_565_, 0);
lean_inc(v_val_648_);
lean_dec_ref(v_headerStx_x3f_565_);
v_val_631_ = v_val_648_;
goto v___jp_630_;
}
else
{
lean_dec(v_headerStx_x3f_565_);
v_opts_568_ = v_opts_561_;
v_ignoreDeprecatedImports_569_ = v_ignoreDeprecatedImports_582_;
goto v___jp_567_;
}
}
else
{
lean_object* v_val_649_; 
lean_dec(v_headerStx_x3f_565_);
v_val_649_ = lean_ctor_get(v_origHeaderStx_x3f_566_, 0);
lean_inc(v_val_649_);
lean_dec_ref(v_origHeaderStx_x3f_566_);
v_val_631_ = v_val_649_;
goto v___jp_630_;
}
v___jp_567_:
{
lean_object* v___x_570_; uint8_t v___x_571_; 
v___x_570_ = l_Lean_linter_deprecated_module;
v___x_571_ = l_Lean_Option_get___at___00Lean_Elab_checkDeprecatedImports_spec__0(v_opts_568_, v___x_570_);
lean_dec_ref(v_opts_568_);
if (v___x_571_ == 0)
{
lean_dec(v_ignoreDeprecatedImports_569_);
lean_dec_ref(v_inputCtx_562_);
return v_messages_564_;
}
else
{
lean_object* v___x_572_; lean_object* v___x_573_; uint8_t v___x_574_; 
v___x_572_ = lean_unsigned_to_nat(0u);
v___x_573_ = lean_array_get_size(v_imports_560_);
v___x_574_ = lean_nat_dec_lt(v___x_572_, v___x_573_);
if (v___x_574_ == 0)
{
lean_dec(v_ignoreDeprecatedImports_569_);
lean_dec_ref(v_inputCtx_562_);
return v_messages_564_;
}
else
{
uint8_t v___x_575_; 
v___x_575_ = lean_nat_dec_le(v___x_573_, v___x_573_);
if (v___x_575_ == 0)
{
if (v___x_574_ == 0)
{
lean_dec(v_ignoreDeprecatedImports_569_);
lean_dec_ref(v_inputCtx_562_);
return v_messages_564_;
}
else
{
size_t v___x_576_; size_t v___x_577_; lean_object* v___x_578_; 
v___x_576_ = ((size_t)0ULL);
v___x_577_ = lean_usize_of_nat(v___x_573_);
v___x_578_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1(v_ignoreDeprecatedImports_569_, v_env_559_, v_inputCtx_562_, v_startPos_563_, v_imports_560_, v___x_576_, v___x_577_, v_messages_564_);
lean_dec(v_ignoreDeprecatedImports_569_);
return v___x_578_;
}
}
else
{
size_t v___x_579_; size_t v___x_580_; lean_object* v___x_581_; 
v___x_579_ = ((size_t)0ULL);
v___x_580_ = lean_usize_of_nat(v___x_573_);
v___x_581_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1(v_ignoreDeprecatedImports_569_, v_env_559_, v_inputCtx_562_, v_startPos_563_, v_imports_560_, v___x_579_, v___x_580_, v_messages_564_);
lean_dec(v_ignoreDeprecatedImports_569_);
return v___x_581_;
}
}
}
}
v___jp_583_:
{
size_t v_sz_586_; size_t v___x_587_; lean_object* v___x_588_; 
v_sz_586_ = lean_array_size(v___y_584_);
v___x_587_ = ((size_t)0ULL);
v___x_588_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkDeprecatedImports_spec__3(v___y_584_, v_sz_586_, v___x_587_, v_ignoreDeprecatedImports_582_);
lean_dec_ref(v___y_584_);
v_opts_568_ = v_opts_585_;
v_ignoreDeprecatedImports_569_ = v___x_588_;
goto v___jp_567_;
}
v___jp_589_:
{
lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v_importsStx_595_; 
v___x_593_ = lean_unsigned_to_nat(2u);
v___x_594_ = l_Lean_Syntax_getArg(v___y_591_, v___x_593_);
lean_dec(v___y_591_);
v_importsStx_595_ = l_Lean_Syntax_getArgs(v___x_594_);
lean_dec(v___x_594_);
if (lean_obj_tag(v___y_590_) == 0)
{
lean_dec(v___y_592_);
v___y_584_ = v_importsStx_595_;
v_opts_585_ = v_opts_561_;
goto v___jp_583_;
}
else
{
lean_object* v_val_596_; lean_object* v___x_597_; 
v_val_596_ = lean_ctor_get(v___y_590_, 0);
lean_inc(v_val_596_);
lean_dec_ref(v___y_590_);
v___x_597_ = l_Lean_Syntax_getTrailing_x3f(v_val_596_);
lean_dec(v_val_596_);
if (lean_obj_tag(v___x_597_) == 0)
{
lean_dec(v___y_592_);
v___y_584_ = v_importsStx_595_;
v_opts_585_ = v_opts_561_;
goto v___jp_583_;
}
else
{
lean_object* v_val_598_; lean_object* v_str_599_; lean_object* v_startPos_600_; lean_object* v_stopPos_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_614_; 
v_val_598_ = lean_ctor_get(v___x_597_, 0);
lean_inc(v_val_598_);
lean_dec_ref(v___x_597_);
v_str_599_ = lean_ctor_get(v_val_598_, 0);
v_startPos_600_ = lean_ctor_get(v_val_598_, 1);
v_stopPos_601_ = lean_ctor_get(v_val_598_, 2);
v_isSharedCheck_614_ = !lean_is_exclusive(v_val_598_);
if (v_isSharedCheck_614_ == 0)
{
v___x_603_ = v_val_598_;
v_isShared_604_ = v_isSharedCheck_614_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_stopPos_601_);
lean_inc(v_startPos_600_);
lean_inc(v_str_599_);
lean_dec(v_val_598_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_614_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_608_; 
v___x_605_ = lean_string_utf8_extract(v_str_599_, v_startPos_600_, v_stopPos_601_);
lean_dec(v_stopPos_601_);
lean_dec(v_startPos_600_);
lean_dec_ref(v_str_599_);
v___x_606_ = lean_string_utf8_byte_size(v___x_605_);
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 2, v___x_606_);
lean_ctor_set(v___x_603_, 1, v___y_592_);
lean_ctor_set(v___x_603_, 0, v___x_605_);
v___x_608_ = v___x_603_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_605_);
lean_ctor_set(v_reuseFailAlloc_613_, 1, v___y_592_);
lean_ctor_set(v_reuseFailAlloc_613_, 2, v___x_606_);
v___x_608_ = v_reuseFailAlloc_613_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
uint8_t v___x_609_; 
v___x_609_ = l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2(v___x_608_);
lean_dec_ref(v___x_608_);
if (v___x_609_ == 0)
{
v___y_584_ = v_importsStx_595_;
v_opts_585_ = v_opts_561_;
goto v___jp_583_;
}
else
{
lean_object* v___x_610_; uint8_t v___x_611_; lean_object* v_opts_612_; 
v___x_610_ = l_Lean_linter_deprecated_module;
v___x_611_ = 0;
v_opts_612_ = l_Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4(v_opts_561_, v___x_610_, v___x_611_);
v___y_584_ = v_importsStx_595_;
v_opts_585_ = v_opts_612_;
goto v___jp_583_;
}
}
}
}
}
}
v___jp_615_:
{
lean_object* v___x_622_; lean_object* v___x_623_; uint8_t v___x_624_; 
v___x_622_ = lean_unsigned_to_nat(1u);
v___x_623_ = l_Lean_Syntax_getArg(v___y_618_, v___x_622_);
v___x_624_ = l_Lean_Syntax_isNone(v___x_623_);
if (v___x_624_ == 0)
{
uint8_t v___x_625_; 
lean_inc(v___x_623_);
v___x_625_ = l_Lean_Syntax_matchesNull(v___x_623_, v___x_622_);
if (v___x_625_ == 0)
{
lean_dec(v___x_623_);
lean_dec(v_moduleTk_621_);
lean_dec(v___y_619_);
lean_dec(v___y_618_);
v_opts_568_ = v_opts_561_;
v_ignoreDeprecatedImports_569_ = v_ignoreDeprecatedImports_582_;
goto v___jp_567_;
}
else
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; uint8_t v___x_629_; 
v___x_626_ = l_Lean_Syntax_getArg(v___x_623_, v___y_619_);
lean_dec(v___x_623_);
v___x_627_ = ((lean_object*)(l_Lean_Elab_HeaderSyntax_imports___closed__6));
lean_inc_ref(v___y_620_);
lean_inc_ref(v___y_616_);
lean_inc_ref(v___y_617_);
v___x_628_ = l_Lean_Name_mkStr4(v___y_617_, v___y_616_, v___y_620_, v___x_627_);
v___x_629_ = l_Lean_Syntax_isOfKind(v___x_626_, v___x_628_);
lean_dec(v___x_628_);
if (v___x_629_ == 0)
{
lean_dec(v_moduleTk_621_);
lean_dec(v___y_619_);
lean_dec(v___y_618_);
v_opts_568_ = v_opts_561_;
v_ignoreDeprecatedImports_569_ = v_ignoreDeprecatedImports_582_;
goto v___jp_567_;
}
else
{
v___y_590_ = v_moduleTk_621_;
v___y_591_ = v___y_618_;
v___y_592_ = v___y_619_;
goto v___jp_589_;
}
}
}
else
{
lean_dec(v___x_623_);
v___y_590_ = v_moduleTk_621_;
v___y_591_ = v___y_618_;
v___y_592_ = v___y_619_;
goto v___jp_589_;
}
}
v___jp_630_:
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; uint8_t v___x_636_; 
v___x_632_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__0));
v___x_633_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__1));
v___x_634_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__2));
v___x_635_ = ((lean_object*)(l_Lean_Elab_HeaderSyntax_imports___closed__1));
lean_inc(v_val_631_);
v___x_636_ = l_Lean_Syntax_isOfKind(v_val_631_, v___x_635_);
if (v___x_636_ == 0)
{
lean_dec(v_val_631_);
v_opts_568_ = v_opts_561_;
v_ignoreDeprecatedImports_569_ = v_ignoreDeprecatedImports_582_;
goto v___jp_567_;
}
else
{
lean_object* v___x_637_; lean_object* v___x_638_; uint8_t v___x_639_; 
v___x_637_ = lean_unsigned_to_nat(0u);
v___x_638_ = l_Lean_Syntax_getArg(v_val_631_, v___x_637_);
v___x_639_ = l_Lean_Syntax_isNone(v___x_638_);
if (v___x_639_ == 0)
{
lean_object* v___x_640_; uint8_t v___x_641_; 
v___x_640_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_638_);
v___x_641_ = l_Lean_Syntax_matchesNull(v___x_638_, v___x_640_);
if (v___x_641_ == 0)
{
lean_dec(v___x_638_);
lean_dec(v_val_631_);
v_opts_568_ = v_opts_561_;
v_ignoreDeprecatedImports_569_ = v_ignoreDeprecatedImports_582_;
goto v___jp_567_;
}
else
{
lean_object* v___x_642_; lean_object* v___x_643_; uint8_t v___x_644_; 
v___x_642_ = l_Lean_Syntax_getArg(v___x_638_, v___x_637_);
lean_dec(v___x_638_);
v___x_643_ = ((lean_object*)(l_Lean_Elab_HeaderSyntax_imports___closed__9));
lean_inc(v___x_642_);
v___x_644_ = l_Lean_Syntax_isOfKind(v___x_642_, v___x_643_);
if (v___x_644_ == 0)
{
lean_dec(v___x_642_);
lean_dec(v_val_631_);
v_opts_568_ = v_opts_561_;
v_ignoreDeprecatedImports_569_ = v_ignoreDeprecatedImports_582_;
goto v___jp_567_;
}
else
{
lean_object* v_moduleTk_645_; lean_object* v___x_646_; 
v_moduleTk_645_ = l_Lean_Syntax_getArg(v___x_642_, v___x_637_);
lean_dec(v___x_642_);
v___x_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_646_, 0, v_moduleTk_645_);
v___y_616_ = v___x_633_;
v___y_617_ = v___x_632_;
v___y_618_ = v_val_631_;
v___y_619_ = v___x_637_;
v___y_620_ = v___x_634_;
v_moduleTk_621_ = v___x_646_;
goto v___jp_615_;
}
}
}
else
{
lean_object* v___x_647_; 
lean_dec(v___x_638_);
v___x_647_ = lean_box(0);
v___y_616_ = v___x_633_;
v___y_617_ = v___x_632_;
v___y_618_ = v_val_631_;
v___y_619_ = v___x_637_;
v___y_620_ = v___x_634_;
v_moduleTk_621_ = v___x_647_;
goto v___jp_615_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedImports___boxed(lean_object* v_env_650_, lean_object* v_imports_651_, lean_object* v_opts_652_, lean_object* v_inputCtx_653_, lean_object* v_startPos_654_, lean_object* v_messages_655_, lean_object* v_headerStx_x3f_656_, lean_object* v_origHeaderStx_x3f_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l_Lean_Elab_checkDeprecatedImports(v_env_650_, v_imports_651_, v_opts_652_, v_inputCtx_653_, v_startPos_654_, v_messages_655_, v_headerStx_x3f_656_, v_origHeaderStx_x3f_657_);
lean_dec(v_startPos_654_);
lean_dec_ref(v_imports_651_);
lean_dec_ref(v_env_650_);
return v_res_658_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_spec__2(lean_object* v_s_659_, lean_object* v_inst_660_, lean_object* v_R_661_, lean_object* v_a_662_, uint8_t v_b_663_, lean_object* v_c_664_){
_start:
{
uint8_t v___x_665_; 
v___x_665_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_spec__2___redArg(v_s_659_, v_a_662_, v_b_663_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_spec__2___boxed(lean_object* v_s_666_, lean_object* v_inst_667_, lean_object* v_R_668_, lean_object* v_a_669_, lean_object* v_b_670_, lean_object* v_c_671_){
_start:
{
uint8_t v_b_boxed_672_; uint8_t v_res_673_; lean_object* v_r_674_; 
v_b_boxed_672_ = lean_unbox(v_b_670_);
v_res_673_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_spec__2(v_s_666_, v_inst_667_, v_R_668_, v_a_669_, v_b_boxed_672_, v_c_671_);
lean_dec_ref(v_s_666_);
v_r_674_ = lean_box(v_res_673_);
return v_r_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_processHeaderCore(lean_object* v_startPos_675_, lean_object* v_imports_676_, uint8_t v_isModule_677_, lean_object* v_opts_678_, lean_object* v_messages_679_, lean_object* v_inputCtx_680_, uint32_t v_trustLevel_681_, lean_object* v_plugins_682_, uint8_t v_leakEnv_683_, lean_object* v_mainModule_684_, lean_object* v_package_x3f_685_, lean_object* v_arts_686_, lean_object* v_headerStx_x3f_687_, lean_object* v_origHeaderStx_x3f_688_){
_start:
{
lean_object* v_fst_691_; lean_object* v_snd_692_; uint8_t v___x_699_; uint8_t v___y_701_; 
v___x_699_ = 1;
if (v_isModule_677_ == 0)
{
uint8_t v___x_734_; 
v___x_734_ = 2;
v___y_701_ = v___x_734_;
goto v___jp_700_;
}
else
{
lean_object* v___x_735_; uint8_t v___x_736_; 
v___x_735_ = l_Lean_Elab_inServer;
v___x_736_ = l_Lean_Option_get___at___00Lean_Elab_checkDeprecatedImports_spec__0(v_opts_678_, v___x_735_);
if (v___x_736_ == 0)
{
uint8_t v___x_737_; 
v___x_737_ = 0;
v___y_701_ = v___x_737_;
goto v___jp_700_;
}
else
{
uint8_t v___x_738_; 
v___x_738_ = 1;
v___y_701_ = v___x_738_;
goto v___jp_700_;
}
}
v___jp_690_:
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_693_ = l_Lean_Environment_setMainModule(v_fst_691_, v_mainModule_684_);
v___x_694_ = l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
v___x_695_ = l_Lean_PersistentEnvExtension_setState___redArg(v___x_694_, v___x_693_, v_package_x3f_685_);
v___x_696_ = l_Lean_Elab_checkDeprecatedImports(v___x_695_, v_imports_676_, v_opts_678_, v_inputCtx_680_, v_startPos_675_, v_snd_692_, v_headerStx_x3f_687_, v_origHeaderStx_x3f_688_);
lean_dec_ref(v_imports_676_);
v___x_697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_697_, 0, v___x_695_);
lean_ctor_set(v___x_697_, 1, v___x_696_);
v___x_698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_698_, 0, v___x_697_);
return v___x_698_;
}
v___jp_700_:
{
lean_object* v___x_702_; 
lean_inc_ref(v_opts_678_);
lean_inc_ref(v_imports_676_);
v___x_702_ = l_Lean_importModules(v_imports_676_, v_opts_678_, v_trustLevel_681_, v_plugins_682_, v_leakEnv_683_, v___x_699_, v___y_701_, v_arts_686_);
if (lean_obj_tag(v___x_702_) == 0)
{
lean_object* v_a_703_; 
v_a_703_ = lean_ctor_get(v___x_702_, 0);
lean_inc(v_a_703_);
lean_dec_ref(v___x_702_);
v_fst_691_ = v_a_703_;
v_snd_692_ = v_messages_679_;
goto v___jp_690_;
}
else
{
lean_object* v_a_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_733_; 
v_a_704_ = lean_ctor_get(v___x_702_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_733_ == 0)
{
v___x_706_ = v___x_702_;
v_isShared_707_ = v_isSharedCheck_733_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_a_704_);
lean_dec(v___x_702_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_733_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
uint32_t v___x_708_; lean_object* v___x_709_; 
v___x_708_ = 0;
v___x_709_ = lean_mk_empty_environment(v___x_708_);
if (lean_obj_tag(v___x_709_) == 0)
{
lean_object* v_a_710_; lean_object* v_fileName_711_; lean_object* v_fileMap_712_; lean_object* v___x_713_; lean_object* v___x_714_; uint8_t v___x_715_; uint8_t v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_720_; 
v_a_710_ = lean_ctor_get(v___x_709_, 0);
lean_inc(v_a_710_);
lean_dec_ref(v___x_709_);
v_fileName_711_ = lean_ctor_get(v_inputCtx_680_, 1);
v_fileMap_712_ = lean_ctor_get(v_inputCtx_680_, 2);
lean_inc_ref(v_fileMap_712_);
v___x_713_ = l_Lean_FileMap_toPosition(v_fileMap_712_, v_startPos_675_);
v___x_714_ = lean_box(0);
v___x_715_ = 0;
v___x_716_ = 2;
v___x_717_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___closed__0));
v___x_718_ = lean_io_error_to_string(v_a_704_);
if (v_isShared_707_ == 0)
{
lean_ctor_set_tag(v___x_706_, 3);
lean_ctor_set(v___x_706_, 0, v___x_718_);
v___x_720_ = v___x_706_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v___x_718_);
v___x_720_ = v_reuseFailAlloc_724_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_721_ = l_Lean_MessageData_ofFormat(v___x_720_);
lean_inc_ref(v_fileName_711_);
v___x_722_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_722_, 0, v_fileName_711_);
lean_ctor_set(v___x_722_, 1, v___x_713_);
lean_ctor_set(v___x_722_, 2, v___x_714_);
lean_ctor_set(v___x_722_, 3, v___x_717_);
lean_ctor_set(v___x_722_, 4, v___x_721_);
lean_ctor_set_uint8(v___x_722_, sizeof(void*)*5, v___x_715_);
lean_ctor_set_uint8(v___x_722_, sizeof(void*)*5 + 1, v___x_716_);
lean_ctor_set_uint8(v___x_722_, sizeof(void*)*5 + 2, v___x_715_);
v___x_723_ = l_Lean_MessageLog_add(v___x_722_, v_messages_679_);
v_fst_691_ = v_a_710_;
v_snd_692_ = v___x_723_;
goto v___jp_690_;
}
}
else
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_732_; 
lean_del_object(v___x_706_);
lean_dec(v_a_704_);
lean_dec(v_origHeaderStx_x3f_688_);
lean_dec(v_headerStx_x3f_687_);
lean_dec(v_package_x3f_685_);
lean_dec(v_mainModule_684_);
lean_dec_ref(v_inputCtx_680_);
lean_dec_ref(v_messages_679_);
lean_dec_ref(v_opts_678_);
lean_dec_ref(v_imports_676_);
v_a_725_ = lean_ctor_get(v___x_709_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_732_ == 0)
{
v___x_727_ = v___x_709_;
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___x_709_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_730_; 
if (v_isShared_728_ == 0)
{
v___x_730_ = v___x_727_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_a_725_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_processHeaderCore___boxed(lean_object* v_startPos_739_, lean_object* v_imports_740_, lean_object* v_isModule_741_, lean_object* v_opts_742_, lean_object* v_messages_743_, lean_object* v_inputCtx_744_, lean_object* v_trustLevel_745_, lean_object* v_plugins_746_, lean_object* v_leakEnv_747_, lean_object* v_mainModule_748_, lean_object* v_package_x3f_749_, lean_object* v_arts_750_, lean_object* v_headerStx_x3f_751_, lean_object* v_origHeaderStx_x3f_752_, lean_object* v_a_753_){
_start:
{
uint8_t v_isModule_boxed_754_; uint32_t v_trustLevel_boxed_755_; uint8_t v_leakEnv_boxed_756_; lean_object* v_res_757_; 
v_isModule_boxed_754_ = lean_unbox(v_isModule_741_);
v_trustLevel_boxed_755_ = lean_unbox_uint32(v_trustLevel_745_);
lean_dec(v_trustLevel_745_);
v_leakEnv_boxed_756_ = lean_unbox(v_leakEnv_747_);
v_res_757_ = l_Lean_Elab_processHeaderCore(v_startPos_739_, v_imports_740_, v_isModule_boxed_754_, v_opts_742_, v_messages_743_, v_inputCtx_744_, v_trustLevel_boxed_755_, v_plugins_746_, v_leakEnv_boxed_756_, v_mainModule_748_, v_package_x3f_749_, v_arts_750_, v_headerStx_x3f_751_, v_origHeaderStx_x3f_752_);
lean_dec(v_startPos_739_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_processHeader(lean_object* v_header_758_, lean_object* v_opts_759_, lean_object* v_messages_760_, lean_object* v_inputCtx_761_, uint32_t v_trustLevel_762_, lean_object* v_plugins_763_, uint8_t v_leakEnv_764_, lean_object* v_mainModule_765_){
_start:
{
lean_object* v___x_767_; uint8_t v___x_768_; lean_object* v___x_769_; uint8_t v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_767_ = l_Lean_Elab_HeaderSyntax_startPos(v_header_758_);
v___x_768_ = 1;
lean_inc(v_header_758_);
v___x_769_ = l_Lean_Elab_HeaderSyntax_imports(v_header_758_, v___x_768_);
v___x_770_ = l_Lean_Elab_HeaderSyntax_isModule(v_header_758_);
v___x_771_ = lean_box(0);
v___x_772_ = lean_box(1);
v___x_773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_773_, 0, v_header_758_);
v___x_774_ = l_Lean_Elab_processHeaderCore(v___x_767_, v___x_769_, v___x_770_, v_opts_759_, v_messages_760_, v_inputCtx_761_, v_trustLevel_762_, v_plugins_763_, v_leakEnv_764_, v_mainModule_765_, v___x_771_, v___x_772_, v___x_773_, v___x_771_);
lean_dec(v___x_767_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_processHeader___boxed(lean_object* v_header_775_, lean_object* v_opts_776_, lean_object* v_messages_777_, lean_object* v_inputCtx_778_, lean_object* v_trustLevel_779_, lean_object* v_plugins_780_, lean_object* v_leakEnv_781_, lean_object* v_mainModule_782_, lean_object* v_a_783_){
_start:
{
uint32_t v_trustLevel_boxed_784_; uint8_t v_leakEnv_boxed_785_; lean_object* v_res_786_; 
v_trustLevel_boxed_784_ = lean_unbox_uint32(v_trustLevel_779_);
lean_dec(v_trustLevel_779_);
v_leakEnv_boxed_785_ = lean_unbox(v_leakEnv_781_);
v_res_786_ = l_Lean_Elab_processHeader(v_header_775_, v_opts_776_, v_messages_777_, v_inputCtx_778_, v_trustLevel_boxed_784_, v_plugins_780_, v_leakEnv_boxed_785_, v_mainModule_782_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_parseImports(lean_object* v_input_788_, lean_object* v_fileName_789_){
_start:
{
lean_object* v___y_792_; 
if (lean_obj_tag(v_fileName_789_) == 0)
{
lean_object* v___x_837_; 
v___x_837_ = ((lean_object*)(l_Lean_Elab_parseImports___closed__0));
v___y_792_ = v___x_837_;
goto v___jp_791_;
}
else
{
lean_object* v_val_838_; 
v_val_838_ = lean_ctor_get(v_fileName_789_, 0);
lean_inc(v_val_838_);
lean_dec_ref(v_fileName_789_);
v___y_792_ = v_val_838_;
goto v___jp_791_;
}
v___jp_791_:
{
uint8_t v___x_793_; lean_object* v___x_794_; lean_object* v_inputCtx_795_; lean_object* v___x_796_; 
v___x_793_ = 1;
v___x_794_ = lean_string_utf8_byte_size(v_input_788_);
v_inputCtx_795_ = l_Lean_Parser_mkInputContext___redArg(v_input_788_, v___y_792_, v___x_793_, v___x_794_);
lean_inc_ref(v_inputCtx_795_);
v___x_796_ = l_Lean_Parser_parseHeader(v_inputCtx_795_);
if (lean_obj_tag(v___x_796_) == 0)
{
lean_object* v_a_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_828_; 
v_a_797_ = lean_ctor_get(v___x_796_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_828_ == 0)
{
v___x_799_ = v___x_796_;
v_isShared_800_ = v_isSharedCheck_828_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_a_797_);
lean_dec(v___x_796_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_828_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v_snd_801_; lean_object* v_fst_802_; lean_object* v_fst_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_826_; 
v_snd_801_ = lean_ctor_get(v_a_797_, 1);
lean_inc(v_snd_801_);
v_fst_802_ = lean_ctor_get(v_snd_801_, 0);
lean_inc(v_fst_802_);
v_fst_803_ = lean_ctor_get(v_a_797_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v_a_797_);
if (v_isSharedCheck_826_ == 0)
{
lean_object* v_unused_827_; 
v_unused_827_ = lean_ctor_get(v_a_797_, 1);
lean_dec(v_unused_827_);
v___x_805_ = v_a_797_;
v_isShared_806_ = v_isSharedCheck_826_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_fst_803_);
lean_dec(v_a_797_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_826_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v_snd_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_824_; 
v_snd_807_ = lean_ctor_get(v_snd_801_, 1);
v_isSharedCheck_824_ = !lean_is_exclusive(v_snd_801_);
if (v_isSharedCheck_824_ == 0)
{
lean_object* v_unused_825_; 
v_unused_825_ = lean_ctor_get(v_snd_801_, 0);
lean_dec(v_unused_825_);
v___x_809_ = v_snd_801_;
v_isShared_810_ = v_isSharedCheck_824_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_snd_807_);
lean_dec(v_snd_801_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_824_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v_fileMap_811_; lean_object* v_pos_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_816_; 
v_fileMap_811_ = lean_ctor_get(v_inputCtx_795_, 2);
lean_inc_ref(v_fileMap_811_);
lean_dec_ref(v_inputCtx_795_);
v_pos_812_ = lean_ctor_get(v_fst_802_, 0);
lean_inc(v_pos_812_);
lean_dec(v_fst_802_);
v___x_813_ = l_Lean_Elab_HeaderSyntax_imports(v_fst_803_, v___x_793_);
v___x_814_ = l_Lean_FileMap_toPosition(v_fileMap_811_, v_pos_812_);
lean_dec(v_pos_812_);
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 0, v___x_814_);
v___x_816_ = v___x_809_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v___x_814_);
lean_ctor_set(v_reuseFailAlloc_823_, 1, v_snd_807_);
v___x_816_ = v_reuseFailAlloc_823_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
lean_object* v___x_818_; 
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 1, v___x_816_);
lean_ctor_set(v___x_805_, 0, v___x_813_);
v___x_818_ = v___x_805_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_813_);
lean_ctor_set(v_reuseFailAlloc_822_, 1, v___x_816_);
v___x_818_ = v_reuseFailAlloc_822_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
lean_object* v___x_820_; 
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 0, v___x_818_);
v___x_820_ = v___x_799_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v___x_818_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_836_; 
lean_dec_ref(v_inputCtx_795_);
v_a_829_ = lean_ctor_get(v___x_796_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_836_ == 0)
{
v___x_831_ = v___x_796_;
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___x_796_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_834_; 
if (v_isShared_832_ == 0)
{
v___x_834_ = v___x_831_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_a_829_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_parseImports___boxed(lean_object* v_input_839_, lean_object* v_fileName_840_, lean_object* v_a_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l_Lean_Elab_parseImports(v_input_839_, v_fileName_840_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00Lean_Elab_printImports_spec__0_spec__0(lean_object* v_s_843_){
_start:
{
lean_object* v___x_845_; lean_object* v_putStr_846_; lean_object* v___x_847_; 
v___x_845_ = lean_get_stdout();
v_putStr_846_ = lean_ctor_get(v___x_845_, 4);
lean_inc_ref(v_putStr_846_);
lean_dec_ref(v___x_845_);
v___x_847_ = lean_apply_2(v_putStr_846_, v_s_843_, lean_box(0));
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00Lean_Elab_printImports_spec__0_spec__0___boxed(lean_object* v_s_848_, lean_object* v_a_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l_IO_print___at___00IO_println___at___00Lean_Elab_printImports_spec__0_spec__0(v_s_848_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00Lean_Elab_printImports_spec__0(lean_object* v_s_851_){
_start:
{
uint32_t v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_853_ = 10;
v___x_854_ = lean_string_push(v_s_851_, v___x_853_);
v___x_855_ = l_IO_print___at___00IO_println___at___00Lean_Elab_printImports_spec__0_spec__0(v___x_854_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00Lean_Elab_printImports_spec__0___boxed(lean_object* v_s_856_, lean_object* v_a_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l_IO_println___at___00Lean_Elab_printImports_spec__0(v_s_856_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImports_spec__1(lean_object* v_as_859_, size_t v_sz_860_, size_t v_i_861_, lean_object* v_b_862_){
_start:
{
uint8_t v___x_864_; 
v___x_864_ = lean_usize_dec_lt(v_i_861_, v_sz_860_);
if (v___x_864_ == 0)
{
lean_object* v___x_865_; 
v___x_865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_865_, 0, v_b_862_);
return v___x_865_;
}
else
{
lean_object* v_a_866_; lean_object* v_module_867_; lean_object* v___x_868_; 
v_a_866_ = lean_array_uget_borrowed(v_as_859_, v_i_861_);
v_module_867_ = lean_ctor_get(v_a_866_, 0);
lean_inc(v_module_867_);
v___x_868_ = l_Lean_findOLean(v_module_867_);
if (lean_obj_tag(v___x_868_) == 0)
{
lean_object* v_a_869_; lean_object* v___x_870_; 
v_a_869_ = lean_ctor_get(v___x_868_, 0);
lean_inc(v_a_869_);
lean_dec_ref(v___x_868_);
v___x_870_ = l_IO_println___at___00Lean_Elab_printImports_spec__0(v_a_869_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v___x_871_; size_t v___x_872_; size_t v___x_873_; 
lean_dec_ref(v___x_870_);
v___x_871_ = lean_box(0);
v___x_872_ = ((size_t)1ULL);
v___x_873_ = lean_usize_add(v_i_861_, v___x_872_);
v_i_861_ = v___x_873_;
v_b_862_ = v___x_871_;
goto _start;
}
else
{
return v___x_870_;
}
}
else
{
lean_object* v_a_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_882_; 
v_a_875_ = lean_ctor_get(v___x_868_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_882_ == 0)
{
v___x_877_ = v___x_868_;
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_a_875_);
lean_dec(v___x_868_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_880_; 
if (v_isShared_878_ == 0)
{
v___x_880_ = v___x_877_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v_a_875_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImports_spec__1___boxed(lean_object* v_as_883_, lean_object* v_sz_884_, lean_object* v_i_885_, lean_object* v_b_886_, lean_object* v___y_887_){
_start:
{
size_t v_sz_boxed_888_; size_t v_i_boxed_889_; lean_object* v_res_890_; 
v_sz_boxed_888_ = lean_unbox_usize(v_sz_884_);
lean_dec(v_sz_884_);
v_i_boxed_889_ = lean_unbox_usize(v_i_885_);
lean_dec(v_i_885_);
v_res_890_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImports_spec__1(v_as_883_, v_sz_boxed_888_, v_i_boxed_889_, v_b_886_);
lean_dec_ref(v_as_883_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_printImports(lean_object* v_input_891_, lean_object* v_fileName_892_){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = l_Lean_Elab_parseImports(v_input_891_, v_fileName_892_);
if (lean_obj_tag(v___x_894_) == 0)
{
lean_object* v_a_895_; lean_object* v_fst_896_; lean_object* v___x_897_; size_t v_sz_898_; size_t v___x_899_; lean_object* v___x_900_; 
v_a_895_ = lean_ctor_get(v___x_894_, 0);
lean_inc(v_a_895_);
lean_dec_ref(v___x_894_);
v_fst_896_ = lean_ctor_get(v_a_895_, 0);
lean_inc(v_fst_896_);
lean_dec(v_a_895_);
v___x_897_ = lean_box(0);
v_sz_898_ = lean_array_size(v_fst_896_);
v___x_899_ = ((size_t)0ULL);
v___x_900_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImports_spec__1(v_fst_896_, v_sz_898_, v___x_899_, v___x_897_);
lean_dec(v_fst_896_);
if (lean_obj_tag(v___x_900_) == 0)
{
lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_907_; 
v_isSharedCheck_907_ = !lean_is_exclusive(v___x_900_);
if (v_isSharedCheck_907_ == 0)
{
lean_object* v_unused_908_; 
v_unused_908_ = lean_ctor_get(v___x_900_, 0);
lean_dec(v_unused_908_);
v___x_902_ = v___x_900_;
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
else
{
lean_dec(v___x_900_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_905_; 
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 0, v___x_897_);
v___x_905_ = v___x_902_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v___x_897_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
}
else
{
return v___x_900_;
}
}
else
{
lean_object* v_a_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_916_; 
v_a_909_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_916_ == 0)
{
v___x_911_ = v___x_894_;
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_a_909_);
lean_dec(v___x_894_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v___x_914_; 
if (v_isShared_912_ == 0)
{
v___x_914_ = v___x_911_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_a_909_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_printImports___boxed(lean_object* v_input_917_, lean_object* v_fileName_918_, lean_object* v_a_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l_Lean_Elab_printImports(v_input_917_, v_fileName_918_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImportSrcs_spec__0(lean_object* v_a_921_, lean_object* v_as_922_, size_t v_sz_923_, size_t v_i_924_, lean_object* v_b_925_){
_start:
{
uint8_t v___x_927_; 
v___x_927_ = lean_usize_dec_lt(v_i_924_, v_sz_923_);
if (v___x_927_ == 0)
{
lean_object* v___x_928_; 
lean_dec(v_a_921_);
v___x_928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_928_, 0, v_b_925_);
return v___x_928_;
}
else
{
lean_object* v_a_929_; lean_object* v_module_930_; lean_object* v___x_931_; 
v_a_929_ = lean_array_uget_borrowed(v_as_922_, v_i_924_);
v_module_930_ = lean_ctor_get(v_a_929_, 0);
lean_inc(v_module_930_);
lean_inc(v_a_921_);
v___x_931_ = l_Lean_findLean(v_a_921_, v_module_930_);
if (lean_obj_tag(v___x_931_) == 0)
{
lean_object* v_a_932_; lean_object* v___x_933_; 
v_a_932_ = lean_ctor_get(v___x_931_, 0);
lean_inc(v_a_932_);
lean_dec_ref(v___x_931_);
v___x_933_ = l_IO_println___at___00Lean_Elab_printImports_spec__0(v_a_932_);
if (lean_obj_tag(v___x_933_) == 0)
{
lean_object* v___x_934_; size_t v___x_935_; size_t v___x_936_; 
lean_dec_ref(v___x_933_);
v___x_934_ = lean_box(0);
v___x_935_ = ((size_t)1ULL);
v___x_936_ = lean_usize_add(v_i_924_, v___x_935_);
v_i_924_ = v___x_936_;
v_b_925_ = v___x_934_;
goto _start;
}
else
{
lean_dec(v_a_921_);
return v___x_933_;
}
}
else
{
lean_object* v_a_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_945_; 
lean_dec(v_a_921_);
v_a_938_ = lean_ctor_get(v___x_931_, 0);
v_isSharedCheck_945_ = !lean_is_exclusive(v___x_931_);
if (v_isSharedCheck_945_ == 0)
{
v___x_940_ = v___x_931_;
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_a_938_);
lean_dec(v___x_931_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_943_; 
if (v_isShared_941_ == 0)
{
v___x_943_ = v___x_940_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v_a_938_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImportSrcs_spec__0___boxed(lean_object* v_a_946_, lean_object* v_as_947_, lean_object* v_sz_948_, lean_object* v_i_949_, lean_object* v_b_950_, lean_object* v___y_951_){
_start:
{
size_t v_sz_boxed_952_; size_t v_i_boxed_953_; lean_object* v_res_954_; 
v_sz_boxed_952_ = lean_unbox_usize(v_sz_948_);
lean_dec(v_sz_948_);
v_i_boxed_953_ = lean_unbox_usize(v_i_949_);
lean_dec(v_i_949_);
v_res_954_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImportSrcs_spec__0(v_a_946_, v_as_947_, v_sz_boxed_952_, v_i_boxed_953_, v_b_950_);
lean_dec_ref(v_as_947_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_printImportSrcs(lean_object* v_input_955_, lean_object* v_fileName_956_){
_start:
{
lean_object* v___x_958_; 
v___x_958_ = l_Lean_getSrcSearchPath();
if (lean_obj_tag(v___x_958_) == 0)
{
lean_object* v_a_959_; lean_object* v___x_960_; 
v_a_959_ = lean_ctor_get(v___x_958_, 0);
lean_inc(v_a_959_);
lean_dec_ref(v___x_958_);
v___x_960_ = l_Lean_Elab_parseImports(v_input_955_, v_fileName_956_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v_a_961_; lean_object* v_fst_962_; lean_object* v___x_963_; size_t v_sz_964_; size_t v___x_965_; lean_object* v___x_966_; 
v_a_961_ = lean_ctor_get(v___x_960_, 0);
lean_inc(v_a_961_);
lean_dec_ref(v___x_960_);
v_fst_962_ = lean_ctor_get(v_a_961_, 0);
lean_inc(v_fst_962_);
lean_dec(v_a_961_);
v___x_963_ = lean_box(0);
v_sz_964_ = lean_array_size(v_fst_962_);
v___x_965_ = ((size_t)0ULL);
v___x_966_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImportSrcs_spec__0(v_a_959_, v_fst_962_, v_sz_964_, v___x_965_, v___x_963_);
lean_dec(v_fst_962_);
if (lean_obj_tag(v___x_966_) == 0)
{
lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_973_; 
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_973_ == 0)
{
lean_object* v_unused_974_; 
v_unused_974_ = lean_ctor_get(v___x_966_, 0);
lean_dec(v_unused_974_);
v___x_968_ = v___x_966_;
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
else
{
lean_dec(v___x_966_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_971_; 
if (v_isShared_969_ == 0)
{
lean_ctor_set(v___x_968_, 0, v___x_963_);
v___x_971_ = v___x_968_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v___x_963_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
else
{
return v___x_966_;
}
}
else
{
lean_object* v_a_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_982_; 
lean_dec(v_a_959_);
v_a_975_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_982_ == 0)
{
v___x_977_ = v___x_960_;
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_a_975_);
lean_dec(v___x_960_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_980_; 
if (v_isShared_978_ == 0)
{
v___x_980_ = v___x_977_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_a_975_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
}
}
else
{
lean_object* v_a_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_990_; 
lean_dec(v_fileName_956_);
lean_dec_ref(v_input_955_);
v_a_983_ = lean_ctor_get(v___x_958_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_990_ == 0)
{
v___x_985_ = v___x_958_;
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_a_983_);
lean_dec(v___x_958_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_988_; 
if (v_isShared_986_ == 0)
{
v___x_988_ = v___x_985_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_a_983_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_printImportSrcs___boxed(lean_object* v_input_991_, lean_object* v_fileName_992_, lean_object* v_a_993_){
_start:
{
lean_object* v_res_994_; 
v_res_994_ = l_Lean_Elab_printImportSrcs(v_input_991_, v_fileName_992_);
return v_res_994_;
}
}
lean_object* runtime_initialize_Lean_Parser_Module(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_ModPkgExt(uint8_t builtin);
lean_object* runtime_initialize_Lean_DeprecatedModule(uint8_t builtin);
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

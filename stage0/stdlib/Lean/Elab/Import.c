// Lean compiler output
// Module: Lean.Elab.Import
// Imports: public import Lean.Parser.Module meta import Lean.Parser.Module import Lean.Compiler.ModPkgExt
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
lean_object* lean_panic_fn(lean_object*, lean_object*);
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
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_get_stdout();
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_findOLean(lean_object*);
lean_object* l_Lean_Environment_setMainModule(lean_object*, lean_object*);
extern lean_object* l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
lean_object* l_Lean_PersistentEnvExtension_setState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_importModules(lean_object*, lean_object*, uint32_t, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*);
lean_object* lean_mk_empty_environment(uint32_t);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_inServer;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_processHeaderCore_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_processHeaderCore_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_processHeaderCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Elab_processHeaderCore___closed__0 = (const lean_object*)&l_Lean_Elab_processHeaderCore___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_processHeaderCore(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_processHeaderCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_20_ = lean_panic_fn(v___x_19_, v_msg_18_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__1(lean_object* v_msg_21_){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_22_ = l_Lean_instInhabitedImport_default;
v___x_23_ = lean_panic_fn(v___x_22_, v_msg_21_);
return v___x_23_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8(void){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_36_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__7));
v___x_37_ = lean_unsigned_to_nat(13u);
v___x_38_ = lean_unsigned_to_nat(36u);
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
lean_object* v___x_66_; lean_object* v_v_67_; lean_object* v___x_68_; lean_object* v_bs_x27_69_; lean_object* v___y_71_; uint8_t v___y_77_; lean_object* v___y_78_; uint8_t v___y_79_; lean_object* v___y_80_; uint8_t v___y_81_; lean_object* v___y_86_; uint8_t v___y_87_; uint8_t v___y_88_; lean_object* v___y_89_; uint8_t v___y_90_; lean_object* v___y_92_; uint8_t v___y_93_; lean_object* v___y_94_; lean_object* v___y_95_; uint8_t v___y_96_; uint8_t v___x_98_; 
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
v___y_93_ = v___x_107_;
v___y_94_ = v___y_102_;
v___y_95_ = v___y_103_;
v___y_96_ = v___x_113_;
goto v___jp_91_;
}
else
{
lean_dec_ref(v_allTk_104_);
v___y_92_ = v___x_112_;
v___y_93_ = v___x_107_;
v___y_94_ = v___y_102_;
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
if (lean_obj_tag(v___y_80_) == 0)
{
uint8_t v___x_82_; lean_object* v___x_83_; 
v___x_82_ = 0;
v___x_83_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_83_, 0, v___y_78_);
lean_ctor_set_uint8(v___x_83_, sizeof(void*)*1, v___y_79_);
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
lean_ctor_set(v___x_84_, 0, v___y_78_);
lean_ctor_set_uint8(v___x_84_, sizeof(void*)*1, v___y_79_);
lean_ctor_set_uint8(v___x_84_, sizeof(void*)*1 + 1, v___y_81_);
lean_ctor_set_uint8(v___x_84_, sizeof(void*)*1 + 2, v___y_77_);
v___y_71_ = v___x_84_;
goto v___jp_70_;
}
}
v___jp_85_:
{
if (lean_obj_tag(v_moduleTk_60_) == 0)
{
v___y_77_ = v___y_87_;
v___y_78_ = v___y_86_;
v___y_79_ = v___y_88_;
v___y_80_ = v___y_89_;
v___y_81_ = v___y_87_;
goto v___jp_76_;
}
else
{
v___y_77_ = v___y_87_;
v___y_78_ = v___y_86_;
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
v___y_88_ = v___y_96_;
v___y_89_ = v___y_94_;
v___y_90_ = v___x_97_;
goto v___jp_85_;
}
else
{
lean_dec_ref(v___y_95_);
if (v___y_93_ == 0)
{
v___y_86_ = v___y_92_;
v___y_87_ = v___y_93_;
v___y_88_ = v___y_96_;
v___y_89_ = v___y_94_;
v___y_90_ = v___y_93_;
goto v___jp_85_;
}
else
{
v___y_77_ = v___y_93_;
v___y_78_ = v___y_92_;
v___y_79_ = v___y_96_;
v___y_80_ = v___y_94_;
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
uint8_t v___x_3694__boxed_165_; size_t v_sz_boxed_166_; size_t v_i_boxed_167_; lean_object* v_res_168_; 
v___x_3694__boxed_165_ = lean_unbox(v___x_161_);
v_sz_boxed_166_ = lean_unbox_usize(v_sz_162_);
lean_dec(v_sz_162_);
v_i_boxed_167_ = lean_unbox_usize(v_i_163_);
lean_dec(v_i_163_);
v_res_168_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2(v_moduleTk_160_, v___x_3694__boxed_165_, v_sz_boxed_166_, v_i_boxed_167_, v_bs_164_);
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
v___x_177_ = lean_unsigned_to_nat(37u);
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
v___y_214_ = v_importsStx_223_;
v___y_215_ = v___y_219_;
goto v___jp_213_;
}
else
{
if (v_includeInit_199_ == 0)
{
v___y_214_ = v_importsStx_223_;
v___y_215_ = v___y_219_;
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
v___x_227_ = lean_mk_empty_array_with_capacity(v___y_218_);
v___x_228_ = lean_array_push(v___x_227_, v___x_226_);
v___y_203_ = v_importsStx_223_;
v___y_204_ = v___y_219_;
v___y_205_ = v___x_228_;
goto v___jp_202_;
}
}
}
else
{
lean_dec_ref(v_preludeTk_220_);
v___y_214_ = v_importsStx_223_;
v___y_215_ = v___y_219_;
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
v___y_218_ = v___x_231_;
v___y_219_ = v_moduleTk_230_;
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
v___y_218_ = v___x_231_;
v___y_219_ = v_moduleTk_230_;
v_preludeTk_220_ = v___x_244_;
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
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_processHeaderCore_spec__0(lean_object* v_opts_275_, lean_object* v_opt_276_){
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_processHeaderCore_spec__0___boxed(lean_object* v_opts_285_, lean_object* v_opt_286_){
_start:
{
uint8_t v_res_287_; lean_object* v_r_288_; 
v_res_287_ = l_Lean_Option_get___at___00Lean_Elab_processHeaderCore_spec__0(v_opts_285_, v_opt_286_);
lean_dec_ref(v_opt_286_);
lean_dec_ref(v_opts_285_);
v_r_288_ = lean_box(v_res_287_);
return v_r_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_processHeaderCore(lean_object* v_startPos_290_, lean_object* v_imports_291_, uint8_t v_isModule_292_, lean_object* v_opts_293_, lean_object* v_messages_294_, lean_object* v_inputCtx_295_, uint32_t v_trustLevel_296_, lean_object* v_plugins_297_, uint8_t v_leakEnv_298_, lean_object* v_mainModule_299_, lean_object* v_package_x3f_300_, lean_object* v_arts_301_){
_start:
{
lean_object* v_fst_304_; lean_object* v_snd_305_; uint8_t v___x_311_; uint8_t v___y_313_; 
v___x_311_ = 1;
if (v_isModule_292_ == 0)
{
uint8_t v___x_346_; 
v___x_346_ = 2;
v___y_313_ = v___x_346_;
goto v___jp_312_;
}
else
{
lean_object* v___x_347_; uint8_t v___x_348_; 
v___x_347_ = l_Lean_Elab_inServer;
v___x_348_ = l_Lean_Option_get___at___00Lean_Elab_processHeaderCore_spec__0(v_opts_293_, v___x_347_);
if (v___x_348_ == 0)
{
uint8_t v___x_349_; 
v___x_349_ = 0;
v___y_313_ = v___x_349_;
goto v___jp_312_;
}
else
{
uint8_t v___x_350_; 
v___x_350_ = 1;
v___y_313_ = v___x_350_;
goto v___jp_312_;
}
}
v___jp_303_:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_306_ = l_Lean_Environment_setMainModule(v_fst_304_, v_mainModule_299_);
v___x_307_ = l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
v___x_308_ = l_Lean_PersistentEnvExtension_setState___redArg(v___x_307_, v___x_306_, v_package_x3f_300_);
v___x_309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_309_, 0, v___x_308_);
lean_ctor_set(v___x_309_, 1, v_snd_305_);
v___x_310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_310_, 0, v___x_309_);
return v___x_310_;
}
v___jp_312_:
{
lean_object* v___x_314_; 
v___x_314_ = l_Lean_importModules(v_imports_291_, v_opts_293_, v_trustLevel_296_, v_plugins_297_, v_leakEnv_298_, v___x_311_, v___y_313_, v_arts_301_);
if (lean_obj_tag(v___x_314_) == 0)
{
lean_object* v_a_315_; 
lean_dec_ref(v_inputCtx_295_);
v_a_315_ = lean_ctor_get(v___x_314_, 0);
lean_inc(v_a_315_);
lean_dec_ref(v___x_314_);
v_fst_304_ = v_a_315_;
v_snd_305_ = v_messages_294_;
goto v___jp_303_;
}
else
{
lean_object* v_a_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_345_; 
v_a_316_ = lean_ctor_get(v___x_314_, 0);
v_isSharedCheck_345_ = !lean_is_exclusive(v___x_314_);
if (v_isSharedCheck_345_ == 0)
{
v___x_318_ = v___x_314_;
v_isShared_319_ = v_isSharedCheck_345_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_a_316_);
lean_dec(v___x_314_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_345_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
uint32_t v___x_320_; lean_object* v___x_321_; 
v___x_320_ = 0;
v___x_321_ = lean_mk_empty_environment(v___x_320_);
if (lean_obj_tag(v___x_321_) == 0)
{
lean_object* v_a_322_; lean_object* v_fileName_323_; lean_object* v_fileMap_324_; lean_object* v___x_325_; lean_object* v___x_326_; uint8_t v___x_327_; uint8_t v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_332_; 
v_a_322_ = lean_ctor_get(v___x_321_, 0);
lean_inc(v_a_322_);
lean_dec_ref(v___x_321_);
v_fileName_323_ = lean_ctor_get(v_inputCtx_295_, 1);
lean_inc_ref(v_fileName_323_);
v_fileMap_324_ = lean_ctor_get(v_inputCtx_295_, 2);
lean_inc_ref(v_fileMap_324_);
lean_dec_ref(v_inputCtx_295_);
v___x_325_ = l_Lean_FileMap_toPosition(v_fileMap_324_, v_startPos_290_);
v___x_326_ = lean_box(0);
v___x_327_ = 0;
v___x_328_ = 2;
v___x_329_ = ((lean_object*)(l_Lean_Elab_processHeaderCore___closed__0));
v___x_330_ = lean_io_error_to_string(v_a_316_);
if (v_isShared_319_ == 0)
{
lean_ctor_set_tag(v___x_318_, 3);
lean_ctor_set(v___x_318_, 0, v___x_330_);
v___x_332_ = v___x_318_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v___x_330_);
v___x_332_ = v_reuseFailAlloc_336_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_333_ = l_Lean_MessageData_ofFormat(v___x_332_);
v___x_334_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_334_, 0, v_fileName_323_);
lean_ctor_set(v___x_334_, 1, v___x_325_);
lean_ctor_set(v___x_334_, 2, v___x_326_);
lean_ctor_set(v___x_334_, 3, v___x_329_);
lean_ctor_set(v___x_334_, 4, v___x_333_);
lean_ctor_set_uint8(v___x_334_, sizeof(void*)*5, v___x_327_);
lean_ctor_set_uint8(v___x_334_, sizeof(void*)*5 + 1, v___x_328_);
lean_ctor_set_uint8(v___x_334_, sizeof(void*)*5 + 2, v___x_327_);
v___x_335_ = l_Lean_MessageLog_add(v___x_334_, v_messages_294_);
v_fst_304_ = v_a_322_;
v_snd_305_ = v___x_335_;
goto v___jp_303_;
}
}
else
{
lean_object* v_a_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_344_; 
lean_del_object(v___x_318_);
lean_dec(v_a_316_);
lean_dec(v_package_x3f_300_);
lean_dec(v_mainModule_299_);
lean_dec_ref(v_inputCtx_295_);
lean_dec_ref(v_messages_294_);
v_a_337_ = lean_ctor_get(v___x_321_, 0);
v_isSharedCheck_344_ = !lean_is_exclusive(v___x_321_);
if (v_isSharedCheck_344_ == 0)
{
v___x_339_ = v___x_321_;
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_a_337_);
lean_dec(v___x_321_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_342_; 
if (v_isShared_340_ == 0)
{
v___x_342_ = v___x_339_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v_a_337_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_processHeaderCore___boxed(lean_object* v_startPos_351_, lean_object* v_imports_352_, lean_object* v_isModule_353_, lean_object* v_opts_354_, lean_object* v_messages_355_, lean_object* v_inputCtx_356_, lean_object* v_trustLevel_357_, lean_object* v_plugins_358_, lean_object* v_leakEnv_359_, lean_object* v_mainModule_360_, lean_object* v_package_x3f_361_, lean_object* v_arts_362_, lean_object* v_a_363_){
_start:
{
uint8_t v_isModule_boxed_364_; uint32_t v_trustLevel_boxed_365_; uint8_t v_leakEnv_boxed_366_; lean_object* v_res_367_; 
v_isModule_boxed_364_ = lean_unbox(v_isModule_353_);
v_trustLevel_boxed_365_ = lean_unbox_uint32(v_trustLevel_357_);
lean_dec(v_trustLevel_357_);
v_leakEnv_boxed_366_ = lean_unbox(v_leakEnv_359_);
v_res_367_ = l_Lean_Elab_processHeaderCore(v_startPos_351_, v_imports_352_, v_isModule_boxed_364_, v_opts_354_, v_messages_355_, v_inputCtx_356_, v_trustLevel_boxed_365_, v_plugins_358_, v_leakEnv_boxed_366_, v_mainModule_360_, v_package_x3f_361_, v_arts_362_);
lean_dec(v_startPos_351_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_processHeader(lean_object* v_header_368_, lean_object* v_opts_369_, lean_object* v_messages_370_, lean_object* v_inputCtx_371_, uint32_t v_trustLevel_372_, lean_object* v_plugins_373_, uint8_t v_leakEnv_374_, lean_object* v_mainModule_375_){
_start:
{
lean_object* v___x_377_; uint8_t v___x_378_; lean_object* v___x_379_; uint8_t v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_377_ = l_Lean_Elab_HeaderSyntax_startPos(v_header_368_);
v___x_378_ = 1;
lean_inc(v_header_368_);
v___x_379_ = l_Lean_Elab_HeaderSyntax_imports(v_header_368_, v___x_378_);
v___x_380_ = l_Lean_Elab_HeaderSyntax_isModule(v_header_368_);
lean_dec(v_header_368_);
v___x_381_ = lean_box(0);
v___x_382_ = lean_box(1);
v___x_383_ = l_Lean_Elab_processHeaderCore(v___x_377_, v___x_379_, v___x_380_, v_opts_369_, v_messages_370_, v_inputCtx_371_, v_trustLevel_372_, v_plugins_373_, v_leakEnv_374_, v_mainModule_375_, v___x_381_, v___x_382_);
lean_dec(v___x_377_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_processHeader___boxed(lean_object* v_header_384_, lean_object* v_opts_385_, lean_object* v_messages_386_, lean_object* v_inputCtx_387_, lean_object* v_trustLevel_388_, lean_object* v_plugins_389_, lean_object* v_leakEnv_390_, lean_object* v_mainModule_391_, lean_object* v_a_392_){
_start:
{
uint32_t v_trustLevel_boxed_393_; uint8_t v_leakEnv_boxed_394_; lean_object* v_res_395_; 
v_trustLevel_boxed_393_ = lean_unbox_uint32(v_trustLevel_388_);
lean_dec(v_trustLevel_388_);
v_leakEnv_boxed_394_ = lean_unbox(v_leakEnv_390_);
v_res_395_ = l_Lean_Elab_processHeader(v_header_384_, v_opts_385_, v_messages_386_, v_inputCtx_387_, v_trustLevel_boxed_393_, v_plugins_389_, v_leakEnv_boxed_394_, v_mainModule_391_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_parseImports(lean_object* v_input_397_, lean_object* v_fileName_398_){
_start:
{
lean_object* v___y_401_; 
if (lean_obj_tag(v_fileName_398_) == 0)
{
lean_object* v___x_446_; 
v___x_446_ = ((lean_object*)(l_Lean_Elab_parseImports___closed__0));
v___y_401_ = v___x_446_;
goto v___jp_400_;
}
else
{
lean_object* v_val_447_; 
v_val_447_ = lean_ctor_get(v_fileName_398_, 0);
lean_inc(v_val_447_);
lean_dec_ref(v_fileName_398_);
v___y_401_ = v_val_447_;
goto v___jp_400_;
}
v___jp_400_:
{
uint8_t v___x_402_; lean_object* v___x_403_; lean_object* v_inputCtx_404_; lean_object* v___x_405_; 
v___x_402_ = 1;
v___x_403_ = lean_string_utf8_byte_size(v_input_397_);
v_inputCtx_404_ = l_Lean_Parser_mkInputContext___redArg(v_input_397_, v___y_401_, v___x_402_, v___x_403_);
lean_inc_ref(v_inputCtx_404_);
v___x_405_ = l_Lean_Parser_parseHeader(v_inputCtx_404_);
if (lean_obj_tag(v___x_405_) == 0)
{
lean_object* v_a_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_437_; 
v_a_406_ = lean_ctor_get(v___x_405_, 0);
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_405_);
if (v_isSharedCheck_437_ == 0)
{
v___x_408_ = v___x_405_;
v_isShared_409_ = v_isSharedCheck_437_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_a_406_);
lean_dec(v___x_405_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_437_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v_snd_410_; lean_object* v_fst_411_; lean_object* v_fst_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_435_; 
v_snd_410_ = lean_ctor_get(v_a_406_, 1);
lean_inc(v_snd_410_);
v_fst_411_ = lean_ctor_get(v_snd_410_, 0);
lean_inc(v_fst_411_);
v_fst_412_ = lean_ctor_get(v_a_406_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v_a_406_);
if (v_isSharedCheck_435_ == 0)
{
lean_object* v_unused_436_; 
v_unused_436_ = lean_ctor_get(v_a_406_, 1);
lean_dec(v_unused_436_);
v___x_414_ = v_a_406_;
v_isShared_415_ = v_isSharedCheck_435_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_fst_412_);
lean_dec(v_a_406_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_435_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v_snd_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_433_; 
v_snd_416_ = lean_ctor_get(v_snd_410_, 1);
v_isSharedCheck_433_ = !lean_is_exclusive(v_snd_410_);
if (v_isSharedCheck_433_ == 0)
{
lean_object* v_unused_434_; 
v_unused_434_ = lean_ctor_get(v_snd_410_, 0);
lean_dec(v_unused_434_);
v___x_418_ = v_snd_410_;
v_isShared_419_ = v_isSharedCheck_433_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_snd_416_);
lean_dec(v_snd_410_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_433_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v_fileMap_420_; lean_object* v_pos_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_425_; 
v_fileMap_420_ = lean_ctor_get(v_inputCtx_404_, 2);
lean_inc_ref(v_fileMap_420_);
lean_dec_ref(v_inputCtx_404_);
v_pos_421_ = lean_ctor_get(v_fst_411_, 0);
lean_inc(v_pos_421_);
lean_dec(v_fst_411_);
v___x_422_ = l_Lean_Elab_HeaderSyntax_imports(v_fst_412_, v___x_402_);
v___x_423_ = l_Lean_FileMap_toPosition(v_fileMap_420_, v_pos_421_);
lean_dec(v_pos_421_);
if (v_isShared_419_ == 0)
{
lean_ctor_set(v___x_418_, 0, v___x_423_);
v___x_425_ = v___x_418_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v___x_423_);
lean_ctor_set(v_reuseFailAlloc_432_, 1, v_snd_416_);
v___x_425_ = v_reuseFailAlloc_432_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
lean_object* v___x_427_; 
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 1, v___x_425_);
lean_ctor_set(v___x_414_, 0, v___x_422_);
v___x_427_ = v___x_414_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v___x_422_);
lean_ctor_set(v_reuseFailAlloc_431_, 1, v___x_425_);
v___x_427_ = v_reuseFailAlloc_431_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
lean_object* v___x_429_; 
if (v_isShared_409_ == 0)
{
lean_ctor_set(v___x_408_, 0, v___x_427_);
v___x_429_ = v___x_408_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v___x_427_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_445_; 
lean_dec_ref(v_inputCtx_404_);
v_a_438_ = lean_ctor_get(v___x_405_, 0);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_405_);
if (v_isSharedCheck_445_ == 0)
{
v___x_440_ = v___x_405_;
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_a_438_);
lean_dec(v___x_405_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_443_; 
if (v_isShared_441_ == 0)
{
v___x_443_ = v___x_440_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_a_438_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_parseImports___boxed(lean_object* v_input_448_, lean_object* v_fileName_449_, lean_object* v_a_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Lean_Elab_parseImports(v_input_448_, v_fileName_449_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00Lean_Elab_printImports_spec__0_spec__0(lean_object* v_s_452_){
_start:
{
lean_object* v___x_454_; lean_object* v_putStr_455_; lean_object* v___x_456_; 
v___x_454_ = lean_get_stdout();
v_putStr_455_ = lean_ctor_get(v___x_454_, 4);
lean_inc_ref(v_putStr_455_);
lean_dec_ref(v___x_454_);
v___x_456_ = lean_apply_2(v_putStr_455_, v_s_452_, lean_box(0));
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00Lean_Elab_printImports_spec__0_spec__0___boxed(lean_object* v_s_457_, lean_object* v_a_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_IO_print___at___00IO_println___at___00Lean_Elab_printImports_spec__0_spec__0(v_s_457_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00Lean_Elab_printImports_spec__0(lean_object* v_s_460_){
_start:
{
uint32_t v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_462_ = 10;
v___x_463_ = lean_string_push(v_s_460_, v___x_462_);
v___x_464_ = l_IO_print___at___00IO_println___at___00Lean_Elab_printImports_spec__0_spec__0(v___x_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00Lean_Elab_printImports_spec__0___boxed(lean_object* v_s_465_, lean_object* v_a_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_IO_println___at___00Lean_Elab_printImports_spec__0(v_s_465_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImports_spec__1(lean_object* v_as_468_, size_t v_sz_469_, size_t v_i_470_, lean_object* v_b_471_){
_start:
{
uint8_t v___x_473_; 
v___x_473_ = lean_usize_dec_lt(v_i_470_, v_sz_469_);
if (v___x_473_ == 0)
{
lean_object* v___x_474_; 
v___x_474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_474_, 0, v_b_471_);
return v___x_474_;
}
else
{
lean_object* v_a_475_; lean_object* v_module_476_; lean_object* v___x_477_; 
v_a_475_ = lean_array_uget_borrowed(v_as_468_, v_i_470_);
v_module_476_ = lean_ctor_get(v_a_475_, 0);
lean_inc(v_module_476_);
v___x_477_ = l_Lean_findOLean(v_module_476_);
if (lean_obj_tag(v___x_477_) == 0)
{
lean_object* v_a_478_; lean_object* v___x_479_; 
v_a_478_ = lean_ctor_get(v___x_477_, 0);
lean_inc(v_a_478_);
lean_dec_ref(v___x_477_);
v___x_479_ = l_IO_println___at___00Lean_Elab_printImports_spec__0(v_a_478_);
if (lean_obj_tag(v___x_479_) == 0)
{
lean_object* v___x_480_; size_t v___x_481_; size_t v___x_482_; 
lean_dec_ref(v___x_479_);
v___x_480_ = lean_box(0);
v___x_481_ = ((size_t)1ULL);
v___x_482_ = lean_usize_add(v_i_470_, v___x_481_);
v_i_470_ = v___x_482_;
v_b_471_ = v___x_480_;
goto _start;
}
else
{
return v___x_479_;
}
}
else
{
lean_object* v_a_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_491_; 
v_a_484_ = lean_ctor_get(v___x_477_, 0);
v_isSharedCheck_491_ = !lean_is_exclusive(v___x_477_);
if (v_isSharedCheck_491_ == 0)
{
v___x_486_ = v___x_477_;
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_a_484_);
lean_dec(v___x_477_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_489_; 
if (v_isShared_487_ == 0)
{
v___x_489_ = v___x_486_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v_a_484_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
return v___x_489_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImports_spec__1___boxed(lean_object* v_as_492_, lean_object* v_sz_493_, lean_object* v_i_494_, lean_object* v_b_495_, lean_object* v___y_496_){
_start:
{
size_t v_sz_boxed_497_; size_t v_i_boxed_498_; lean_object* v_res_499_; 
v_sz_boxed_497_ = lean_unbox_usize(v_sz_493_);
lean_dec(v_sz_493_);
v_i_boxed_498_ = lean_unbox_usize(v_i_494_);
lean_dec(v_i_494_);
v_res_499_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImports_spec__1(v_as_492_, v_sz_boxed_497_, v_i_boxed_498_, v_b_495_);
lean_dec_ref(v_as_492_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_printImports(lean_object* v_input_500_, lean_object* v_fileName_501_){
_start:
{
lean_object* v___x_503_; 
v___x_503_ = l_Lean_Elab_parseImports(v_input_500_, v_fileName_501_);
if (lean_obj_tag(v___x_503_) == 0)
{
lean_object* v_a_504_; lean_object* v_fst_505_; lean_object* v___x_506_; size_t v_sz_507_; size_t v___x_508_; lean_object* v___x_509_; 
v_a_504_ = lean_ctor_get(v___x_503_, 0);
lean_inc(v_a_504_);
lean_dec_ref(v___x_503_);
v_fst_505_ = lean_ctor_get(v_a_504_, 0);
lean_inc(v_fst_505_);
lean_dec(v_a_504_);
v___x_506_ = lean_box(0);
v_sz_507_ = lean_array_size(v_fst_505_);
v___x_508_ = ((size_t)0ULL);
v___x_509_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImports_spec__1(v_fst_505_, v_sz_507_, v___x_508_, v___x_506_);
lean_dec(v_fst_505_);
if (lean_obj_tag(v___x_509_) == 0)
{
lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_516_; 
v_isSharedCheck_516_ = !lean_is_exclusive(v___x_509_);
if (v_isSharedCheck_516_ == 0)
{
lean_object* v_unused_517_; 
v_unused_517_ = lean_ctor_get(v___x_509_, 0);
lean_dec(v_unused_517_);
v___x_511_ = v___x_509_;
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
else
{
lean_dec(v___x_509_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_514_; 
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 0, v___x_506_);
v___x_514_ = v___x_511_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v___x_506_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
else
{
return v___x_509_;
}
}
else
{
lean_object* v_a_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_525_; 
v_a_518_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_525_ == 0)
{
v___x_520_ = v___x_503_;
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_a_518_);
lean_dec(v___x_503_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_523_; 
if (v_isShared_521_ == 0)
{
v___x_523_ = v___x_520_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_a_518_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_printImports___boxed(lean_object* v_input_526_, lean_object* v_fileName_527_, lean_object* v_a_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l_Lean_Elab_printImports(v_input_526_, v_fileName_527_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImportSrcs_spec__0(lean_object* v_a_530_, lean_object* v_as_531_, size_t v_sz_532_, size_t v_i_533_, lean_object* v_b_534_){
_start:
{
uint8_t v___x_536_; 
v___x_536_ = lean_usize_dec_lt(v_i_533_, v_sz_532_);
if (v___x_536_ == 0)
{
lean_object* v___x_537_; 
lean_dec(v_a_530_);
v___x_537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_537_, 0, v_b_534_);
return v___x_537_;
}
else
{
lean_object* v_a_538_; lean_object* v_module_539_; lean_object* v___x_540_; 
v_a_538_ = lean_array_uget_borrowed(v_as_531_, v_i_533_);
v_module_539_ = lean_ctor_get(v_a_538_, 0);
lean_inc(v_module_539_);
lean_inc(v_a_530_);
v___x_540_ = l_Lean_findLean(v_a_530_, v_module_539_);
if (lean_obj_tag(v___x_540_) == 0)
{
lean_object* v_a_541_; lean_object* v___x_542_; 
v_a_541_ = lean_ctor_get(v___x_540_, 0);
lean_inc(v_a_541_);
lean_dec_ref(v___x_540_);
v___x_542_ = l_IO_println___at___00Lean_Elab_printImports_spec__0(v_a_541_);
if (lean_obj_tag(v___x_542_) == 0)
{
lean_object* v___x_543_; size_t v___x_544_; size_t v___x_545_; 
lean_dec_ref(v___x_542_);
v___x_543_ = lean_box(0);
v___x_544_ = ((size_t)1ULL);
v___x_545_ = lean_usize_add(v_i_533_, v___x_544_);
v_i_533_ = v___x_545_;
v_b_534_ = v___x_543_;
goto _start;
}
else
{
lean_dec(v_a_530_);
return v___x_542_;
}
}
else
{
lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_554_; 
lean_dec(v_a_530_);
v_a_547_ = lean_ctor_get(v___x_540_, 0);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_540_);
if (v_isSharedCheck_554_ == 0)
{
v___x_549_ = v___x_540_;
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_dec(v___x_540_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_552_; 
if (v_isShared_550_ == 0)
{
v___x_552_ = v___x_549_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_a_547_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImportSrcs_spec__0___boxed(lean_object* v_a_555_, lean_object* v_as_556_, lean_object* v_sz_557_, lean_object* v_i_558_, lean_object* v_b_559_, lean_object* v___y_560_){
_start:
{
size_t v_sz_boxed_561_; size_t v_i_boxed_562_; lean_object* v_res_563_; 
v_sz_boxed_561_ = lean_unbox_usize(v_sz_557_);
lean_dec(v_sz_557_);
v_i_boxed_562_ = lean_unbox_usize(v_i_558_);
lean_dec(v_i_558_);
v_res_563_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImportSrcs_spec__0(v_a_555_, v_as_556_, v_sz_boxed_561_, v_i_boxed_562_, v_b_559_);
lean_dec_ref(v_as_556_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_printImportSrcs(lean_object* v_input_564_, lean_object* v_fileName_565_){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = l_Lean_getSrcSearchPath();
if (lean_obj_tag(v___x_567_) == 0)
{
lean_object* v_a_568_; lean_object* v___x_569_; 
v_a_568_ = lean_ctor_get(v___x_567_, 0);
lean_inc(v_a_568_);
lean_dec_ref(v___x_567_);
v___x_569_ = l_Lean_Elab_parseImports(v_input_564_, v_fileName_565_);
if (lean_obj_tag(v___x_569_) == 0)
{
lean_object* v_a_570_; lean_object* v_fst_571_; lean_object* v___x_572_; size_t v_sz_573_; size_t v___x_574_; lean_object* v___x_575_; 
v_a_570_ = lean_ctor_get(v___x_569_, 0);
lean_inc(v_a_570_);
lean_dec_ref(v___x_569_);
v_fst_571_ = lean_ctor_get(v_a_570_, 0);
lean_inc(v_fst_571_);
lean_dec(v_a_570_);
v___x_572_ = lean_box(0);
v_sz_573_ = lean_array_size(v_fst_571_);
v___x_574_ = ((size_t)0ULL);
v___x_575_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImportSrcs_spec__0(v_a_568_, v_fst_571_, v_sz_573_, v___x_574_, v___x_572_);
lean_dec(v_fst_571_);
if (lean_obj_tag(v___x_575_) == 0)
{
lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_582_; 
v_isSharedCheck_582_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_582_ == 0)
{
lean_object* v_unused_583_; 
v_unused_583_ = lean_ctor_get(v___x_575_, 0);
lean_dec(v_unused_583_);
v___x_577_ = v___x_575_;
v_isShared_578_ = v_isSharedCheck_582_;
goto v_resetjp_576_;
}
else
{
lean_dec(v___x_575_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_582_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___x_580_; 
if (v_isShared_578_ == 0)
{
lean_ctor_set(v___x_577_, 0, v___x_572_);
v___x_580_ = v___x_577_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v___x_572_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
return v___x_580_;
}
}
}
else
{
return v___x_575_;
}
}
else
{
lean_object* v_a_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_591_; 
lean_dec(v_a_568_);
v_a_584_ = lean_ctor_get(v___x_569_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_591_ == 0)
{
v___x_586_ = v___x_569_;
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_a_584_);
lean_dec(v___x_569_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_589_; 
if (v_isShared_587_ == 0)
{
v___x_589_ = v___x_586_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_a_584_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
}
}
else
{
lean_object* v_a_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_599_; 
lean_dec(v_fileName_565_);
lean_dec_ref(v_input_564_);
v_a_592_ = lean_ctor_get(v___x_567_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_567_);
if (v_isSharedCheck_599_ == 0)
{
v___x_594_ = v___x_567_;
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_a_592_);
lean_dec(v___x_567_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_597_; 
if (v_isShared_595_ == 0)
{
v___x_597_ = v___x_594_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_a_592_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_printImportSrcs___boxed(lean_object* v_input_600_, lean_object* v_fileName_601_, lean_object* v_a_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l_Lean_Elab_printImportSrcs(v_input_600_, v_fileName_601_);
return v_res_603_;
}
}
lean_object* runtime_initialize_Lean_Parser_Module(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_ModPkgExt(uint8_t builtin);
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

// Lean compiler output
// Module: LeanChecker
// Imports: public import Init public meta import Init public import Lean.CoreM public import Lean.Replay public import Lake.Load.Manifest public import LeanExport.Parse
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
uint8_t l_Lean_instOrdOLeanLevel_ord(uint8_t, uint8_t);
lean_object* l_List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_IO_println___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__3(lean_object*);
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t);
lean_object* lean_stream_of_handle(lean_object*);
lean_object* l_LeanExport_parseStream(lean_object*);
lean_object* l_Lean_mkEmptyEnvironment(uint32_t);
lean_object* lean_elab_environment_to_kernel_env(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Kernel_Environment_replay(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Lemmas______macroRules__Std__DTreeMap__Internal__Impl__tacticSimp__to__model_x5b___x5dUsing____1_spec__1___redArg(lean_object*, lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
uint8_t l_Lean_instBEqConstantInfo_beq(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lake_Manifest_load_x3f(lean_object*);
lean_object* l_Lean_Name_capitalize(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_task_get_own(lean_object*);
lean_object* l_IO_eprintln___at___00__private_Init_System_IO_0__IO_eprintlnAux_spec__0(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_findOLean(lean_object*);
uint8_t l_System_FilePath_pathExists(lean_object*);
extern lean_object* l_Lean_instInhabitedImportState_default;
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_importModulesCore(lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_finalizeImport(lean_object*, lean_object*, lean_object*, uint32_t, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_environment_free_regions(lean_object*);
lean_object* l_Lean_readModuleDataParts(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_OLeanLevel_adjustFileName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_constants(lean_object*);
lean_object* l_Lean_withImportModules___redArg(lean_object*, lean_object*, lean_object*, uint32_t);
lean_object* lean_io_as_task(lean_object*, lean_object*);
extern lean_object* l_Lean_searchPathRef;
lean_object* l_Lean_SearchPath_findAllWithExt(lean_object*, lean_object*);
lean_object* l_Lean_searchModuleNameOfFileName(lean_object*, lean_object*);
uint8_t l_List_elem___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__1(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_List_toString___at___00Lean_Environment_AddConstAsyncResult_commitConst_spec__1(lean_object*);
lean_object* l_Lean_findSysroot(lean_object*);
lean_object* l_Lean_initSearchPath(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_String_toName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_elem___at___00Lean_isAutoDeclOrPrivate__Internal_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_println(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_println___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00replayFromImports_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00replayFromImports_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_replayFromImports___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_replayFromImports___closed__0;
static lean_once_cell_t l_replayFromImports___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_replayFromImports___closed__1;
static const lean_string_object l_replayFromImports___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "failed to read module data"};
static const lean_object* l_replayFromImports___closed__2 = (const lean_object*)&l_replayFromImports___closed__2_value;
static const lean_ctor_object l_replayFromImports___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_replayFromImports___closed__2_value)}};
static const lean_object* l_replayFromImports___closed__3 = (const lean_object*)&l_replayFromImports___closed__3_value;
static const lean_string_object l_replayFromImports___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "object file '"};
static const lean_object* l_replayFromImports___closed__4 = (const lean_object*)&l_replayFromImports___closed__4_value;
static const lean_string_object l_replayFromImports___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "' of module "};
static const lean_object* l_replayFromImports___closed__5 = (const lean_object*)&l_replayFromImports___closed__5_value;
static const lean_string_object l_replayFromImports___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " does not exist"};
static const lean_object* l_replayFromImports___closed__6 = (const lean_object*)&l_replayFromImports___closed__6_value;
LEAN_EXPORT lean_object* l_replayFromImports(lean_object*);
LEAN_EXPORT lean_object* l_replayFromImports___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_replayFromFresh___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_replayFromFresh___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_replayFromFresh___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_replayFromFresh___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_replayFromFresh___closed__0 = (const lean_object*)&l_replayFromFresh___closed__0_value;
LEAN_EXPORT lean_object* l_replayFromFresh(lean_object*);
LEAN_EXPORT lean_object* l_replayFromFresh___boxed(lean_object*, lean_object*);
static const lean_string_object l_getCurrentModule___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "lake-manifest.json"};
static const lean_object* l_getCurrentModule___closed__0 = (const lean_object*)&l_getCurrentModule___closed__0_value;
LEAN_EXPORT lean_object* l_getCurrentModule();
LEAN_EXPORT lean_object* l_getCurrentModule___boxed(lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00checkExport_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Quotient constant mismatch on: "};
static const lean_object* l_List_forIn_x27_loop___at___00checkExport_spec__1___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00checkExport_spec__1___redArg___closed__0_value;
static const lean_string_object l_List_forIn_x27_loop___at___00checkExport_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "Could not find quotient constant in final kernel env: "};
static const lean_object* l_List_forIn_x27_loop___at___00checkExport_spec__1___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00checkExport_spec__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkExport_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkExport_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00checkExport_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00checkExport_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_checkExport___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Exactly one export file expected but got: "};
static const lean_object* l_checkExport___closed__0 = (const lean_object*)&l_checkExport___closed__0_value;
static const lean_string_object l_checkExport___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Lean default kernel rejects the solution: "};
static const lean_object* l_checkExport___closed__1 = (const lean_object*)&l_checkExport___closed__1_value;
static const lean_string_object l_checkExport___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Quot"};
static const lean_object* l_checkExport___closed__2 = (const lean_object*)&l_checkExport___closed__2_value;
static const lean_string_object l_checkExport___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l_checkExport___closed__3 = (const lean_object*)&l_checkExport___closed__3_value;
static const lean_ctor_object l_checkExport___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_checkExport___closed__2_value),LEAN_SCALAR_PTR_LITERAL(91, 127, 250, 116, 111, 99, 160, 200)}};
static const lean_ctor_object l_checkExport___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_checkExport___closed__4_value_aux_0),((lean_object*)&l_checkExport___closed__3_value),LEAN_SCALAR_PTR_LITERAL(255, 113, 137, 82, 82, 132, 58, 248)}};
static const lean_object* l_checkExport___closed__4 = (const lean_object*)&l_checkExport___closed__4_value;
static const lean_string_object l_checkExport___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lift"};
static const lean_object* l_checkExport___closed__5 = (const lean_object*)&l_checkExport___closed__5_value;
static const lean_ctor_object l_checkExport___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_checkExport___closed__2_value),LEAN_SCALAR_PTR_LITERAL(91, 127, 250, 116, 111, 99, 160, 200)}};
static const lean_ctor_object l_checkExport___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_checkExport___closed__6_value_aux_0),((lean_object*)&l_checkExport___closed__5_value),LEAN_SCALAR_PTR_LITERAL(91, 125, 38, 34, 222, 200, 201, 80)}};
static const lean_object* l_checkExport___closed__6 = (const lean_object*)&l_checkExport___closed__6_value;
static const lean_string_object l_checkExport___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ind"};
static const lean_object* l_checkExport___closed__7 = (const lean_object*)&l_checkExport___closed__7_value;
static const lean_ctor_object l_checkExport___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_checkExport___closed__2_value),LEAN_SCALAR_PTR_LITERAL(91, 127, 250, 116, 111, 99, 160, 200)}};
static const lean_ctor_object l_checkExport___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_checkExport___closed__8_value_aux_0),((lean_object*)&l_checkExport___closed__7_value),LEAN_SCALAR_PTR_LITERAL(150, 213, 121, 152, 109, 27, 137, 60)}};
static const lean_object* l_checkExport___closed__8 = (const lean_object*)&l_checkExport___closed__8_value;
static const lean_ctor_object l_checkExport___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_checkExport___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_checkExport___closed__9 = (const lean_object*)&l_checkExport___closed__9_value;
static const lean_ctor_object l_checkExport___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_checkExport___closed__6_value),((lean_object*)&l_checkExport___closed__9_value)}};
static const lean_object* l_checkExport___closed__10 = (const lean_object*)&l_checkExport___closed__10_value;
static const lean_ctor_object l_checkExport___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_checkExport___closed__4_value),((lean_object*)&l_checkExport___closed__10_value)}};
static const lean_object* l_checkExport___closed__11 = (const lean_object*)&l_checkExport___closed__11_value;
static const lean_string_object l_checkExport___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Lean default kernel accepts the solution"};
static const lean_object* l_checkExport___closed__12 = (const lean_object*)&l_checkExport___closed__12_value;
static const lean_ctor_object l_checkExport___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_checkExport___closed__2_value),LEAN_SCALAR_PTR_LITERAL(91, 127, 250, 116, 111, 99, 160, 200)}};
static const lean_object* l_checkExport___closed__13 = (const lean_object*)&l_checkExport___closed__13_value;
static const lean_ctor_object l_checkExport___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_checkExport___closed__13_value),((lean_object*)&l_checkExport___closed__11_value)}};
static const lean_object* l_checkExport___closed__14 = (const lean_object*)&l_checkExport___closed__14_value;
static const lean_string_object l_checkExport___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Quotient post-check rejects the solution: "};
static const lean_object* l_checkExport___closed__15 = (const lean_object*)&l_checkExport___closed__15_value;
LEAN_EXPORT lean_object* l_checkExport___boxed__const__1;
LEAN_EXPORT lean_object* l_checkExport___boxed__const__2;
LEAN_EXPORT lean_object* l_checkExport(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_checkExport___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkExport_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkExport_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00checkOlean_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "leanchecker found a problem in "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00checkOlean_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00checkOlean_spec__3___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00checkOlean_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "replaying "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00checkOlean_spec__3___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00checkOlean_spec__3___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00checkOlean_spec__3(uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00checkOlean_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__2___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_mapM_loop___at___00checkOlean_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Could not resolve module: "};
static const lean_object* l_List_mapM_loop___at___00checkOlean_spec__5___closed__0 = (const lean_object*)&l_List_mapM_loop___at___00checkOlean_spec__5___closed__0_value;
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00checkOlean_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00checkOlean_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00checkOlean_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00checkOlean_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00checkOlean_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "olean"};
static const lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__1___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00checkOlean_spec__1___redArg___closed__0_value;
static const lean_string_object l_List_forIn_x27_loop___at___00checkOlean_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Could not find any oleans for: "};
static const lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__1___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00checkOlean_spec__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00checkOlean_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = " with --fresh"};
static const lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__4___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00checkOlean_spec__4___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__4___redArg(uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_checkOlean___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_checkOlean___closed__0 = (const lean_object*)&l_checkOlean___closed__0_value;
static const lean_string_object l_checkOlean___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "--fresh flag is only valid when specifying a single module:\n"};
static const lean_object* l_checkOlean___closed__1 = (const lean_object*)&l_checkOlean___closed__1_value;
static const lean_string_object l_checkOlean___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_checkOlean___closed__2 = (const lean_object*)&l_checkOlean___closed__2_value;
LEAN_EXPORT lean_object* l_checkOlean(lean_object*, uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_checkOlean___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__4(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_partition_loop___at___00main_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_List_partition_loop___at___00main_spec__0___closed__0 = (const lean_object*)&l_List_partition_loop___at___00main_spec__0___closed__0_value;
static lean_once_cell_t l_List_partition_loop___at___00main_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_partition_loop___at___00main_spec__0___closed__1;
LEAN_EXPORT lean_object* l_List_partition_loop___at___00main_spec__0(lean_object*, lean_object*);
static const lean_ctor_object l_main___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_main___closed__0 = (const lean_object*)&l_main___closed__0_value;
static const lean_string_object l_main___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "--fresh"};
static const lean_object* l_main___closed__1 = (const lean_object*)&l_main___closed__1_value;
static const lean_string_object l_main___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "--silent"};
static const lean_object* l_main___closed__2 = (const lean_object*)&l_main___closed__2_value;
static const lean_string_object l_main___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "--from-export"};
static const lean_object* l_main___closed__3 = (const lean_object*)&l_main___closed__3_value;
static const lean_string_object l_main___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-v"};
static const lean_object* l_main___closed__4 = (const lean_object*)&l_main___closed__4_value;
static const lean_string_object l_main___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "--verbose"};
static const lean_object* l_main___closed__5 = (const lean_object*)&l_main___closed__5_value;
LEAN_EXPORT lean_object* _lean_main(lean_object*);
LEAN_EXPORT lean_object* l_main___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_println(lean_object* v_msg_1_, uint8_t v_silent_2_){
_start:
{
if (v_silent_2_ == 0)
{
lean_object* v___x_4_; 
v___x_4_ = l_IO_println___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__3(v_msg_1_);
return v___x_4_;
}
else
{
lean_object* v___x_5_; lean_object* v___x_6_; 
lean_dec_ref(v_msg_1_);
v___x_5_ = lean_box(0);
v___x_6_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
}
LEAN_EXPORT lean_object* l_println___boxed(lean_object* v_msg_7_, lean_object* v_silent_8_, lean_object* v_a_9_){
_start:
{
uint8_t v_silent_boxed_10_; lean_object* v_res_11_; 
v_silent_boxed_10_ = lean_unbox(v_silent_8_);
v_res_11_ = l_println(v_msg_7_, v_silent_boxed_10_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00replayFromImports_spec__0(lean_object* v_as_12_, size_t v_sz_13_, size_t v_i_14_, lean_object* v_b_15_){
_start:
{
uint8_t v___x_17_; 
v___x_17_ = lean_usize_dec_lt(v_i_14_, v_sz_13_);
if (v___x_17_ == 0)
{
lean_object* v___x_18_; 
v___x_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_18_, 0, v_b_15_);
return v___x_18_;
}
else
{
lean_object* v_snd_19_; lean_object* v_fst_20_; lean_object* v___x_22_; uint8_t v_isShared_23_; uint8_t v_isSharedCheck_53_; 
v_snd_19_ = lean_ctor_get(v_b_15_, 1);
v_fst_20_ = lean_ctor_get(v_b_15_, 0);
v_isSharedCheck_53_ = !lean_is_exclusive(v_b_15_);
if (v_isSharedCheck_53_ == 0)
{
v___x_22_ = v_b_15_;
v_isShared_23_ = v_isSharedCheck_53_;
goto v_resetjp_21_;
}
else
{
lean_inc(v_snd_19_);
lean_inc(v_fst_20_);
lean_dec(v_b_15_);
v___x_22_ = lean_box(0);
v_isShared_23_ = v_isSharedCheck_53_;
goto v_resetjp_21_;
}
v_resetjp_21_:
{
lean_object* v_array_24_; lean_object* v_start_25_; lean_object* v_stop_26_; uint8_t v___x_27_; 
v_array_24_ = lean_ctor_get(v_snd_19_, 0);
v_start_25_ = lean_ctor_get(v_snd_19_, 1);
v_stop_26_ = lean_ctor_get(v_snd_19_, 2);
v___x_27_ = lean_nat_dec_lt(v_start_25_, v_stop_26_);
if (v___x_27_ == 0)
{
lean_object* v___x_29_; 
if (v_isShared_23_ == 0)
{
v___x_29_ = v___x_22_;
goto v_reusejp_28_;
}
else
{
lean_object* v_reuseFailAlloc_31_; 
v_reuseFailAlloc_31_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_31_, 0, v_fst_20_);
lean_ctor_set(v_reuseFailAlloc_31_, 1, v_snd_19_);
v___x_29_ = v_reuseFailAlloc_31_;
goto v_reusejp_28_;
}
v_reusejp_28_:
{
lean_object* v___x_30_; 
v___x_30_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_30_, 0, v___x_29_);
return v___x_30_;
}
}
else
{
lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_49_; 
lean_inc(v_stop_26_);
lean_inc(v_start_25_);
lean_inc_ref(v_array_24_);
v_isSharedCheck_49_ = !lean_is_exclusive(v_snd_19_);
if (v_isSharedCheck_49_ == 0)
{
lean_object* v_unused_50_; lean_object* v_unused_51_; lean_object* v_unused_52_; 
v_unused_50_ = lean_ctor_get(v_snd_19_, 2);
lean_dec(v_unused_50_);
v_unused_51_ = lean_ctor_get(v_snd_19_, 1);
lean_dec(v_unused_51_);
v_unused_52_ = lean_ctor_get(v_snd_19_, 0);
lean_dec(v_unused_52_);
v___x_33_ = v_snd_19_;
v_isShared_34_ = v_isSharedCheck_49_;
goto v_resetjp_32_;
}
else
{
lean_dec(v_snd_19_);
v___x_33_ = lean_box(0);
v_isShared_34_ = v_isSharedCheck_49_;
goto v_resetjp_32_;
}
v_resetjp_32_:
{
lean_object* v_a_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_40_; 
v_a_35_ = lean_array_uget_borrowed(v_as_12_, v_i_14_);
v___x_36_ = lean_array_fget(v_array_24_, v_start_25_);
v___x_37_ = lean_unsigned_to_nat(1u);
v___x_38_ = lean_nat_add(v_start_25_, v___x_37_);
lean_dec(v_start_25_);
if (v_isShared_34_ == 0)
{
lean_ctor_set(v___x_33_, 1, v___x_38_);
v___x_40_ = v___x_33_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_48_; 
v_reuseFailAlloc_48_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_48_, 0, v_array_24_);
lean_ctor_set(v_reuseFailAlloc_48_, 1, v___x_38_);
lean_ctor_set(v_reuseFailAlloc_48_, 2, v_stop_26_);
v___x_40_ = v_reuseFailAlloc_48_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
lean_object* v___x_41_; lean_object* v___x_43_; 
lean_inc(v_a_35_);
v___x_41_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1___redArg(v_fst_20_, v_a_35_, v___x_36_);
if (v_isShared_23_ == 0)
{
lean_ctor_set(v___x_22_, 1, v___x_40_);
lean_ctor_set(v___x_22_, 0, v___x_41_);
v___x_43_ = v___x_22_;
goto v_reusejp_42_;
}
else
{
lean_object* v_reuseFailAlloc_47_; 
v_reuseFailAlloc_47_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_47_, 0, v___x_41_);
lean_ctor_set(v_reuseFailAlloc_47_, 1, v___x_40_);
v___x_43_ = v_reuseFailAlloc_47_;
goto v_reusejp_42_;
}
v_reusejp_42_:
{
size_t v___x_44_; size_t v___x_45_; 
v___x_44_ = ((size_t)1ULL);
v___x_45_ = lean_usize_add(v_i_14_, v___x_44_);
v_i_14_ = v___x_45_;
v_b_15_ = v___x_43_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00replayFromImports_spec__0___boxed(lean_object* v_as_54_, lean_object* v_sz_55_, lean_object* v_i_56_, lean_object* v_b_57_, lean_object* v___y_58_){
_start:
{
size_t v_sz_boxed_59_; size_t v_i_boxed_60_; lean_object* v_res_61_; 
v_sz_boxed_59_ = lean_unbox_usize(v_sz_55_);
lean_dec(v_sz_55_);
v_i_boxed_60_ = lean_unbox_usize(v_i_56_);
lean_dec(v_i_56_);
v_res_61_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00replayFromImports_spec__0(v_as_54_, v_sz_boxed_59_, v_i_boxed_60_, v_b_57_);
lean_dec_ref(v_as_54_);
return v_res_61_;
}
}
static lean_object* _init_l_replayFromImports___closed__0(void){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_62_ = lean_box(0);
v___x_63_ = lean_unsigned_to_nat(16u);
v___x_64_ = lean_mk_array(v___x_63_, v___x_62_);
return v___x_64_;
}
}
static uint8_t _init_l_replayFromImports___closed__1(void){
_start:
{
uint8_t v___x_65_; uint8_t v___x_66_; 
v___x_65_ = 2;
v___x_66_ = l_Lean_instOrdOLeanLevel_ord(v___x_65_, v___x_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_replayFromImports(lean_object* v_module_73_){
_start:
{
lean_object* v___x_75_; 
lean_inc(v_module_73_);
v___x_75_ = l_Lean_findOLean(v_module_73_);
if (lean_obj_tag(v___x_75_) == 0)
{
lean_object* v_a_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_201_; 
v_a_76_ = lean_ctor_get(v___x_75_, 0);
v_isSharedCheck_201_ = !lean_is_exclusive(v___x_75_);
if (v_isSharedCheck_201_ == 0)
{
v___x_78_ = v___x_75_;
v_isShared_79_ = v_isSharedCheck_201_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_a_76_);
lean_dec(v___x_75_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_201_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
uint8_t v___x_80_; lean_object* v___y_82_; uint8_t v___y_83_; lean_object* v___y_84_; lean_object* v___y_85_; lean_object* v___y_86_; lean_object* v___y_87_; uint8_t v___y_88_; uint8_t v___y_89_; lean_object* v_fnames_150_; 
v___x_80_ = l_System_FilePath_pathExists(v_a_76_);
if (v___x_80_ == 0)
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; uint8_t v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_188_; 
v___x_177_ = ((lean_object*)(l_replayFromImports___closed__4));
v___x_178_ = lean_string_append(v___x_177_, v_a_76_);
lean_dec(v_a_76_);
v___x_179_ = ((lean_object*)(l_replayFromImports___closed__5));
v___x_180_ = lean_string_append(v___x_178_, v___x_179_);
v___x_181_ = 1;
v___x_182_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_73_, v___x_181_);
v___x_183_ = lean_string_append(v___x_180_, v___x_182_);
lean_dec_ref(v___x_182_);
v___x_184_ = ((lean_object*)(l_replayFromImports___closed__6));
v___x_185_ = lean_string_append(v___x_183_, v___x_184_);
v___x_186_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_186_, 0, v___x_185_);
if (v_isShared_79_ == 0)
{
lean_ctor_set_tag(v___x_78_, 1);
lean_ctor_set(v___x_78_, 0, v___x_186_);
v___x_188_ = v___x_78_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v___x_186_);
v___x_188_ = v_reuseFailAlloc_189_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
return v___x_188_;
}
}
else
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; uint8_t v___x_193_; lean_object* v___x_194_; uint8_t v___x_195_; 
lean_del_object(v___x_78_);
lean_dec(v_module_73_);
v___x_190_ = lean_unsigned_to_nat(1u);
v___x_191_ = lean_mk_empty_array_with_capacity(v___x_190_);
lean_inc_n(v_a_76_, 2);
v___x_192_ = lean_array_push(v___x_191_, v_a_76_);
v___x_193_ = 1;
v___x_194_ = l_Lean_OLeanLevel_adjustFileName(v_a_76_, v___x_193_);
v___x_195_ = l_System_FilePath_pathExists(v___x_194_);
if (v___x_195_ == 0)
{
lean_dec_ref(v___x_194_);
lean_dec(v_a_76_);
v_fnames_150_ = v___x_192_;
goto v___jp_149_;
}
else
{
uint8_t v___x_196_; lean_object* v___x_197_; uint8_t v___x_198_; lean_object* v___x_199_; 
v___x_196_ = 2;
v___x_197_ = l_Lean_OLeanLevel_adjustFileName(v_a_76_, v___x_196_);
v___x_198_ = l_System_FilePath_pathExists(v___x_197_);
v___x_199_ = lean_array_push(v___x_192_, v___x_194_);
if (v___x_198_ == 0)
{
lean_dec_ref(v___x_197_);
v_fnames_150_ = v___x_199_;
goto v___jp_149_;
}
else
{
lean_object* v___x_200_; 
v___x_200_ = lean_array_push(v___x_199_, v___x_197_);
v_fnames_150_ = v___x_200_;
goto v___jp_149_;
}
}
}
v___jp_81_:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v_imports_92_; lean_object* v___x_93_; 
v___x_90_ = l_Lean_instInhabitedImportState_default;
v___x_91_ = lean_st_mk_ref(v___x_90_);
v_imports_92_ = lean_ctor_get(v___y_87_, 0);
lean_inc_ref(v_imports_92_);
lean_dec_ref(v___y_87_);
lean_inc(v___y_85_);
v___x_93_ = l_Lean_importModulesCore(v_imports_92_, v___y_88_, v___y_85_, v___y_89_, v___y_83_, v___x_91_);
if (lean_obj_tag(v___x_93_) == 0)
{
lean_object* v___x_94_; lean_object* v___x_95_; uint32_t v___x_96_; lean_object* v___x_97_; 
lean_dec_ref_known(v___x_93_, 1);
v___x_94_ = lean_st_ref_get(v___x_91_);
lean_dec(v___x_91_);
v___x_95_ = l_Lean_Options_empty;
v___x_96_ = 0;
v___x_97_ = l_Lean_finalizeImport(v___x_94_, v_imports_92_, v___x_95_, v___x_96_, v___y_83_, v___y_83_, v___y_88_, v___x_80_, v___y_83_);
lean_dec(v___x_94_);
if (lean_obj_tag(v___x_97_) == 0)
{
lean_object* v_a_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v_fst_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_139_; 
v_a_98_ = lean_ctor_get(v___x_97_, 0);
lean_inc(v_a_98_);
lean_dec_ref_known(v___x_97_, 1);
v___x_99_ = lean_unsigned_to_nat(1u);
v___x_100_ = lean_nat_sub(v___y_82_, v___x_99_);
lean_dec(v___y_82_);
v___x_101_ = lean_array_fget(v___y_86_, v___x_100_);
lean_dec(v___x_100_);
lean_dec_ref(v___y_86_);
v_fst_102_ = lean_ctor_get(v___x_101_, 0);
v_isSharedCheck_139_ = !lean_is_exclusive(v___x_101_);
if (v_isSharedCheck_139_ == 0)
{
lean_object* v_unused_140_; 
v_unused_140_ = lean_ctor_get(v___x_101_, 1);
lean_dec(v_unused_140_);
v___x_104_ = v___x_101_;
v_isShared_105_ = v_isSharedCheck_139_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_fst_102_);
lean_dec(v___x_101_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_139_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v_constNames_106_; lean_object* v_constants_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_113_; 
v_constNames_106_ = lean_ctor_get(v_fst_102_, 1);
lean_inc_ref(v_constNames_106_);
v_constants_107_ = lean_ctor_get(v_fst_102_, 2);
lean_inc_ref(v_constants_107_);
lean_dec(v_fst_102_);
v___x_108_ = lean_obj_once(&l_replayFromImports___closed__0, &l_replayFromImports___closed__0_once, _init_l_replayFromImports___closed__0);
lean_inc(v___y_84_);
v___x_109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_109_, 0, v___y_84_);
lean_ctor_set(v___x_109_, 1, v___x_108_);
v___x_110_ = lean_array_get_size(v_constants_107_);
v___x_111_ = l_Array_toSubarray___redArg(v_constants_107_, v___y_84_, v___x_110_);
if (v_isShared_105_ == 0)
{
lean_ctor_set(v___x_104_, 1, v___x_111_);
lean_ctor_set(v___x_104_, 0, v___x_109_);
v___x_113_ = v___x_104_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v___x_109_);
lean_ctor_set(v_reuseFailAlloc_138_, 1, v___x_111_);
v___x_113_ = v_reuseFailAlloc_138_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
size_t v_sz_114_; size_t v___x_115_; lean_object* v___x_116_; 
v_sz_114_ = lean_array_size(v_constNames_106_);
v___x_115_ = ((size_t)0ULL);
v___x_116_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00replayFromImports_spec__0(v_constNames_106_, v_sz_114_, v___x_115_, v___x_113_);
lean_dec_ref(v_constNames_106_);
if (lean_obj_tag(v___x_116_) == 0)
{
lean_object* v_a_117_; lean_object* v_fst_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v_a_117_ = lean_ctor_get(v___x_116_, 0);
lean_inc(v_a_117_);
lean_dec_ref_known(v___x_116_, 1);
v_fst_118_ = lean_ctor_get(v_a_117_, 0);
lean_inc(v_fst_118_);
lean_dec(v_a_117_);
lean_inc(v_a_98_);
v___x_119_ = lean_elab_environment_to_kernel_env(v_a_98_);
v___x_120_ = l_Lean_Kernel_Environment_replay(v_fst_118_, v___x_119_);
lean_dec(v_fst_118_);
if (lean_obj_tag(v___x_120_) == 0)
{
lean_object* v___x_121_; 
lean_dec_ref_known(v___x_120_, 1);
v___x_121_ = lean_environment_free_regions(v_a_98_);
return v___x_121_;
}
else
{
lean_object* v_a_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_129_; 
lean_dec(v_a_98_);
v_a_122_ = lean_ctor_get(v___x_120_, 0);
v_isSharedCheck_129_ = !lean_is_exclusive(v___x_120_);
if (v_isSharedCheck_129_ == 0)
{
v___x_124_ = v___x_120_;
v_isShared_125_ = v_isSharedCheck_129_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_a_122_);
lean_dec(v___x_120_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_129_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___x_127_; 
if (v_isShared_125_ == 0)
{
v___x_127_ = v___x_124_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v_a_122_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
return v___x_127_;
}
}
}
}
else
{
lean_object* v_a_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_137_; 
lean_dec(v_a_98_);
v_a_130_ = lean_ctor_get(v___x_116_, 0);
v_isSharedCheck_137_ = !lean_is_exclusive(v___x_116_);
if (v_isSharedCheck_137_ == 0)
{
v___x_132_ = v___x_116_;
v_isShared_133_ = v_isSharedCheck_137_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_a_130_);
lean_dec(v___x_116_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_137_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v___x_135_; 
if (v_isShared_133_ == 0)
{
v___x_135_ = v___x_132_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v_a_130_);
v___x_135_ = v_reuseFailAlloc_136_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
return v___x_135_;
}
}
}
}
}
}
else
{
lean_object* v_a_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_148_; 
lean_dec_ref(v___y_86_);
lean_dec(v___y_84_);
lean_dec(v___y_82_);
v_a_141_ = lean_ctor_get(v___x_97_, 0);
v_isSharedCheck_148_ = !lean_is_exclusive(v___x_97_);
if (v_isSharedCheck_148_ == 0)
{
v___x_143_ = v___x_97_;
v_isShared_144_ = v_isSharedCheck_148_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_a_141_);
lean_dec(v___x_97_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_148_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___x_146_; 
if (v_isShared_144_ == 0)
{
v___x_146_ = v___x_143_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v_a_141_);
v___x_146_ = v_reuseFailAlloc_147_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
return v___x_146_;
}
}
}
}
else
{
lean_dec_ref(v_imports_92_);
lean_dec(v___x_91_);
lean_dec_ref(v___y_86_);
lean_dec(v___y_84_);
lean_dec(v___y_82_);
return v___x_93_;
}
}
v___jp_149_:
{
lean_object* v___x_151_; 
v___x_151_ = l_Lean_readModuleDataParts(v_fnames_150_);
lean_dec_ref(v_fnames_150_);
if (lean_obj_tag(v___x_151_) == 0)
{
lean_object* v_a_152_; lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_168_; 
v_a_152_ = lean_ctor_get(v___x_151_, 0);
v_isSharedCheck_168_ = !lean_is_exclusive(v___x_151_);
if (v_isSharedCheck_168_ == 0)
{
v___x_154_ = v___x_151_;
v_isShared_155_ = v_isSharedCheck_168_;
goto v_resetjp_153_;
}
else
{
lean_inc(v_a_152_);
lean_dec(v___x_151_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_168_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
lean_object* v___x_156_; lean_object* v___x_157_; uint8_t v___x_158_; 
v___x_156_ = lean_array_get_size(v_a_152_);
v___x_157_ = lean_unsigned_to_nat(0u);
v___x_158_ = lean_nat_dec_eq(v___x_156_, v___x_157_);
if (v___x_158_ == 0)
{
lean_object* v___x_159_; lean_object* v_fst_160_; uint8_t v___x_161_; lean_object* v___x_162_; uint8_t v___x_163_; 
lean_del_object(v___x_154_);
v___x_159_ = lean_array_fget_borrowed(v_a_152_, v___x_157_);
v_fst_160_ = lean_ctor_get(v___x_159_, 0);
lean_inc(v_fst_160_);
v___x_161_ = 2;
v___x_162_ = lean_box(1);
v___x_163_ = lean_uint8_once(&l_replayFromImports___closed__1, &l_replayFromImports___closed__1_once, _init_l_replayFromImports___closed__1);
if (v___x_163_ == 0)
{
v___y_82_ = v___x_156_;
v___y_83_ = v___x_158_;
v___y_84_ = v___x_157_;
v___y_85_ = v___x_162_;
v___y_86_ = v_a_152_;
v___y_87_ = v_fst_160_;
v___y_88_ = v___x_161_;
v___y_89_ = v___x_80_;
goto v___jp_81_;
}
else
{
v___y_82_ = v___x_156_;
v___y_83_ = v___x_158_;
v___y_84_ = v___x_157_;
v___y_85_ = v___x_162_;
v___y_86_ = v_a_152_;
v___y_87_ = v_fst_160_;
v___y_88_ = v___x_161_;
v___y_89_ = v___x_158_;
goto v___jp_81_;
}
}
else
{
lean_object* v___x_164_; lean_object* v___x_166_; 
lean_dec(v_a_152_);
v___x_164_ = ((lean_object*)(l_replayFromImports___closed__3));
if (v_isShared_155_ == 0)
{
lean_ctor_set_tag(v___x_154_, 1);
lean_ctor_set(v___x_154_, 0, v___x_164_);
v___x_166_ = v___x_154_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v___x_164_);
v___x_166_ = v_reuseFailAlloc_167_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
return v___x_166_;
}
}
}
}
else
{
lean_object* v_a_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_176_; 
v_a_169_ = lean_ctor_get(v___x_151_, 0);
v_isSharedCheck_176_ = !lean_is_exclusive(v___x_151_);
if (v_isSharedCheck_176_ == 0)
{
v___x_171_ = v___x_151_;
v_isShared_172_ = v_isSharedCheck_176_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_a_169_);
lean_dec(v___x_151_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_176_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v___x_174_; 
if (v_isShared_172_ == 0)
{
v___x_174_ = v___x_171_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v_a_169_);
v___x_174_ = v_reuseFailAlloc_175_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
return v___x_174_;
}
}
}
}
}
}
else
{
lean_object* v_a_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_209_; 
lean_dec(v_module_73_);
v_a_202_ = lean_ctor_get(v___x_75_, 0);
v_isSharedCheck_209_ = !lean_is_exclusive(v___x_75_);
if (v_isSharedCheck_209_ == 0)
{
v___x_204_ = v___x_75_;
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_a_202_);
lean_dec(v___x_75_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_207_; 
if (v_isShared_205_ == 0)
{
v___x_207_ = v___x_204_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v_a_202_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
return v___x_207_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_replayFromImports___boxed(lean_object* v_module_210_, lean_object* v_a_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l_replayFromImports(v_module_210_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l_replayFromFresh___lam__0(lean_object* v_env_213_){
_start:
{
uint32_t v___x_215_; lean_object* v___x_216_; 
v___x_215_ = 0;
v___x_216_ = l_Lean_mkEmptyEnvironment(v___x_215_);
if (lean_obj_tag(v___x_216_) == 0)
{
lean_object* v_a_217_; lean_object* v___x_218_; lean_object* v_map_u2081_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v_a_217_ = lean_ctor_get(v___x_216_, 0);
lean_inc(v_a_217_);
lean_dec_ref_known(v___x_216_, 1);
v___x_218_ = l_Lean_Environment_constants(v_env_213_);
v_map_u2081_219_ = lean_ctor_get(v___x_218_, 0);
lean_inc_ref(v_map_u2081_219_);
lean_dec_ref(v___x_218_);
v___x_220_ = lean_elab_environment_to_kernel_env(v_a_217_);
v___x_221_ = l_Lean_Kernel_Environment_replay(v_map_u2081_219_, v___x_220_);
lean_dec_ref(v_map_u2081_219_);
if (lean_obj_tag(v___x_221_) == 0)
{
lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_229_; 
v_isSharedCheck_229_ = !lean_is_exclusive(v___x_221_);
if (v_isSharedCheck_229_ == 0)
{
lean_object* v_unused_230_; 
v_unused_230_ = lean_ctor_get(v___x_221_, 0);
lean_dec(v_unused_230_);
v___x_223_ = v___x_221_;
v_isShared_224_ = v_isSharedCheck_229_;
goto v_resetjp_222_;
}
else
{
lean_dec(v___x_221_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_229_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___x_225_; lean_object* v___x_227_; 
v___x_225_ = lean_box(0);
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 0, v___x_225_);
v___x_227_ = v___x_223_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v___x_225_);
v___x_227_ = v_reuseFailAlloc_228_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
return v___x_227_;
}
}
}
else
{
lean_object* v_a_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_238_; 
v_a_231_ = lean_ctor_get(v___x_221_, 0);
v_isSharedCheck_238_ = !lean_is_exclusive(v___x_221_);
if (v_isSharedCheck_238_ == 0)
{
v___x_233_ = v___x_221_;
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_a_231_);
lean_dec(v___x_221_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v___x_236_; 
if (v_isShared_234_ == 0)
{
v___x_236_ = v___x_233_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v_a_231_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
}
}
else
{
lean_object* v_a_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_246_; 
lean_dec_ref(v_env_213_);
v_a_239_ = lean_ctor_get(v___x_216_, 0);
v_isSharedCheck_246_ = !lean_is_exclusive(v___x_216_);
if (v_isSharedCheck_246_ == 0)
{
v___x_241_ = v___x_216_;
v_isShared_242_ = v_isSharedCheck_246_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_a_239_);
lean_dec(v___x_216_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_246_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___x_244_; 
if (v_isShared_242_ == 0)
{
v___x_244_ = v___x_241_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v_a_239_);
v___x_244_ = v_reuseFailAlloc_245_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
return v___x_244_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_replayFromFresh___lam__0___boxed(lean_object* v_env_247_, lean_object* v___y_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l_replayFromFresh___lam__0(v_env_247_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_replayFromFresh(lean_object* v_module_251_){
_start:
{
lean_object* v___f_253_; uint8_t v___x_254_; uint8_t v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; uint32_t v___x_261_; lean_object* v___x_262_; 
v___f_253_ = ((lean_object*)(l_replayFromFresh___closed__0));
v___x_254_ = 0;
v___x_255_ = 1;
v___x_256_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_256_, 0, v_module_251_);
lean_ctor_set_uint8(v___x_256_, sizeof(void*)*1, v___x_254_);
lean_ctor_set_uint8(v___x_256_, sizeof(void*)*1 + 1, v___x_255_);
lean_ctor_set_uint8(v___x_256_, sizeof(void*)*1 + 2, v___x_254_);
v___x_257_ = lean_unsigned_to_nat(1u);
v___x_258_ = lean_mk_empty_array_with_capacity(v___x_257_);
v___x_259_ = lean_array_push(v___x_258_, v___x_256_);
v___x_260_ = l_Lean_Options_empty;
v___x_261_ = 0;
v___x_262_ = l_Lean_withImportModules___redArg(v___x_259_, v___x_260_, v___f_253_, v___x_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_replayFromFresh___boxed(lean_object* v_module_263_, lean_object* v_a_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_replayFromFresh(v_module_263_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l_getCurrentModule(){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_268_ = ((lean_object*)(l_getCurrentModule___closed__0));
v___x_269_ = l_Lake_Manifest_load_x3f(v___x_268_);
if (lean_obj_tag(v___x_269_) == 0)
{
lean_object* v_a_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_284_; 
v_a_270_ = lean_ctor_get(v___x_269_, 0);
v_isSharedCheck_284_ = !lean_is_exclusive(v___x_269_);
if (v_isSharedCheck_284_ == 0)
{
v___x_272_ = v___x_269_;
v_isShared_273_ = v_isSharedCheck_284_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_a_270_);
lean_dec(v___x_269_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_284_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
if (lean_obj_tag(v_a_270_) == 0)
{
lean_object* v___x_274_; lean_object* v___x_276_; 
v___x_274_ = lean_box(0);
if (v_isShared_273_ == 0)
{
lean_ctor_set(v___x_272_, 0, v___x_274_);
v___x_276_ = v___x_272_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v___x_274_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
else
{
lean_object* v_val_278_; lean_object* v_name_279_; lean_object* v___x_280_; lean_object* v___x_282_; 
v_val_278_ = lean_ctor_get(v_a_270_, 0);
lean_inc(v_val_278_);
lean_dec_ref_known(v_a_270_, 1);
v_name_279_ = lean_ctor_get(v_val_278_, 0);
lean_inc(v_name_279_);
lean_dec(v_val_278_);
v___x_280_ = l_Lean_Name_capitalize(v_name_279_);
if (v_isShared_273_ == 0)
{
lean_ctor_set(v___x_272_, 0, v___x_280_);
v___x_282_ = v___x_272_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v___x_280_);
v___x_282_ = v_reuseFailAlloc_283_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
return v___x_282_;
}
}
}
}
else
{
lean_object* v_a_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_292_; 
v_a_285_ = lean_ctor_get(v___x_269_, 0);
v_isSharedCheck_292_ = !lean_is_exclusive(v___x_269_);
if (v_isSharedCheck_292_ == 0)
{
v___x_287_ = v___x_269_;
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_a_285_);
lean_dec(v___x_269_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_290_; 
if (v_isShared_288_ == 0)
{
v___x_290_ = v___x_287_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v_a_285_);
v___x_290_ = v_reuseFailAlloc_291_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
return v___x_290_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_getCurrentModule___boxed(lean_object* v_a_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_getCurrentModule();
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkExport_spec__1___redArg(lean_object* v___x_297_, lean_object* v_a_298_, lean_object* v_as_x27_299_, lean_object* v_b_300_){
_start:
{
if (lean_obj_tag(v_as_x27_299_) == 0)
{
lean_object* v___x_302_; 
lean_dec_ref(v_a_298_);
v___x_302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_302_, 0, v_b_300_);
return v___x_302_;
}
else
{
lean_object* v_head_303_; lean_object* v_tail_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
v_head_303_ = lean_ctor_get(v_as_x27_299_, 0);
v_tail_304_ = lean_ctor_get(v_as_x27_299_, 1);
v___x_305_ = lean_box(0);
v___x_306_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Lemmas______macroRules__Std__DTreeMap__Internal__Impl__tacticSimp__to__model_x5b___x5dUsing____1_spec__1___redArg(v___x_297_, v_head_303_);
if (lean_obj_tag(v___x_306_) == 1)
{
lean_object* v_val_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_337_; 
v_val_307_ = lean_ctor_get(v___x_306_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v___x_306_);
if (v_isSharedCheck_337_ == 0)
{
v___x_309_ = v___x_306_;
v_isShared_310_ = v_isSharedCheck_337_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_val_307_);
lean_dec(v___x_306_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_337_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_311_; 
lean_inc(v_head_303_);
lean_inc_ref(v_a_298_);
v___x_311_ = lean_environment_find(v_a_298_, v_head_303_);
if (lean_obj_tag(v___x_311_) == 1)
{
lean_object* v_val_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_328_; 
v_val_312_ = lean_ctor_get(v___x_311_, 0);
v_isSharedCheck_328_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_328_ == 0)
{
v___x_314_ = v___x_311_;
v_isShared_315_ = v_isSharedCheck_328_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_val_312_);
lean_dec(v___x_311_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_328_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
uint8_t v___x_316_; 
v___x_316_ = l_Lean_instBEqConstantInfo_beq(v_val_307_, v_val_312_);
lean_dec(v_val_312_);
lean_dec(v_val_307_);
if (v___x_316_ == 0)
{
uint8_t v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_322_; 
lean_dec_ref(v_a_298_);
v___x_317_ = 1;
v___x_318_ = ((lean_object*)(l_List_forIn_x27_loop___at___00checkExport_spec__1___redArg___closed__0));
lean_inc(v_head_303_);
v___x_319_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_303_, v___x_317_);
v___x_320_ = lean_string_append(v___x_318_, v___x_319_);
lean_dec_ref(v___x_319_);
if (v_isShared_315_ == 0)
{
lean_ctor_set_tag(v___x_314_, 18);
lean_ctor_set(v___x_314_, 0, v___x_320_);
v___x_322_ = v___x_314_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v___x_320_);
v___x_322_ = v_reuseFailAlloc_326_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
lean_object* v___x_324_; 
if (v_isShared_310_ == 0)
{
lean_ctor_set(v___x_309_, 0, v___x_322_);
v___x_324_ = v___x_309_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v___x_322_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
else
{
lean_del_object(v___x_314_);
lean_del_object(v___x_309_);
v_as_x27_299_ = v_tail_304_;
v_b_300_ = v___x_305_;
goto _start;
}
}
}
else
{
lean_object* v___x_329_; uint8_t v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_334_; 
lean_dec(v___x_311_);
lean_dec(v_val_307_);
lean_dec_ref(v_a_298_);
v___x_329_ = ((lean_object*)(l_List_forIn_x27_loop___at___00checkExport_spec__1___redArg___closed__1));
v___x_330_ = 1;
lean_inc(v_head_303_);
v___x_331_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_303_, v___x_330_);
v___x_332_ = lean_string_append(v___x_329_, v___x_331_);
lean_dec_ref(v___x_331_);
if (v_isShared_310_ == 0)
{
lean_ctor_set_tag(v___x_309_, 18);
lean_ctor_set(v___x_309_, 0, v___x_332_);
v___x_334_ = v___x_309_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v___x_332_);
v___x_334_ = v_reuseFailAlloc_336_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
lean_object* v___x_335_; 
v___x_335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
return v___x_335_;
}
}
}
}
else
{
lean_dec(v___x_306_);
v_as_x27_299_ = v_tail_304_;
v_b_300_ = v___x_305_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkExport_spec__1___redArg___boxed(lean_object* v___x_339_, lean_object* v_a_340_, lean_object* v_as_x27_341_, lean_object* v_b_342_, lean_object* v___y_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l_List_forIn_x27_loop___at___00checkExport_spec__1___redArg(v___x_339_, v_a_340_, v_as_x27_341_, v_b_342_);
lean_dec(v_as_x27_341_);
lean_dec_ref(v___x_339_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00checkExport_spec__0(lean_object* v_x_345_, lean_object* v_x_346_){
_start:
{
if (lean_obj_tag(v_x_346_) == 0)
{
return v_x_345_;
}
else
{
lean_object* v_head_347_; lean_object* v_tail_348_; lean_object* v___x_349_; 
v_head_347_ = lean_ctor_get(v_x_346_, 0);
v_tail_348_ = lean_ctor_get(v_x_346_, 1);
v___x_349_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg(v_x_345_, v_head_347_);
v_x_345_ = v___x_349_;
v_x_346_ = v_tail_348_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00checkExport_spec__0___boxed(lean_object* v_x_351_, lean_object* v_x_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_List_foldl___at___00checkExport_spec__0(v_x_351_, v_x_352_);
lean_dec(v_x_352_);
return v_res_353_;
}
}
static lean_object* _init_l_checkExport___boxed__const__1(void){
_start:
{
uint32_t v___x_385_; lean_object* v___x_386_; 
v___x_385_ = 1;
v___x_386_ = lean_box_uint32(v___x_385_);
return v___x_386_;
}
}
static lean_object* _init_l_checkExport___boxed__const__2(void){
_start:
{
uint32_t v___x_387_; lean_object* v___x_388_; 
v___x_387_ = 0;
v___x_388_ = lean_box_uint32(v___x_387_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_checkExport(lean_object* v_args_389_, uint8_t v_silent_390_){
_start:
{
lean_object* v_a_399_; 
if (lean_obj_tag(v_args_389_) == 1)
{
lean_object* v_tail_421_; 
v_tail_421_ = lean_ctor_get(v_args_389_, 1);
if (lean_obj_tag(v_tail_421_) == 0)
{
lean_object* v_head_422_; uint8_t v___x_423_; lean_object* v___x_424_; 
v_head_422_ = lean_ctor_get(v_args_389_, 0);
v___x_423_ = 0;
v___x_424_ = lean_io_prim_handle_mk(v_head_422_, v___x_423_);
if (lean_obj_tag(v___x_424_) == 0)
{
lean_object* v_a_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v_a_425_ = lean_ctor_get(v___x_424_, 0);
lean_inc(v_a_425_);
lean_dec_ref_known(v___x_424_, 1);
v___x_426_ = lean_stream_of_handle(v_a_425_);
v___x_427_ = l_LeanExport_parseStream(v___x_426_);
if (lean_obj_tag(v___x_427_) == 0)
{
lean_object* v_a_428_; uint32_t v___x_429_; lean_object* v___x_430_; 
v_a_428_ = lean_ctor_get(v___x_427_, 0);
lean_inc(v_a_428_);
lean_dec_ref_known(v___x_427_, 1);
v___x_429_ = 0;
v___x_430_ = l_Lean_mkEmptyEnvironment(v___x_429_);
if (lean_obj_tag(v___x_430_) == 0)
{
lean_object* v_a_431_; lean_object* v_constMap_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v_a_431_ = lean_ctor_get(v___x_430_, 0);
lean_inc(v_a_431_);
lean_dec_ref_known(v___x_430_, 1);
v_constMap_432_ = lean_ctor_get(v_a_428_, 0);
lean_inc_ref_n(v_constMap_432_, 2);
lean_dec(v_a_428_);
v___x_433_ = lean_elab_environment_to_kernel_env(v_a_431_);
v___x_434_ = ((lean_object*)(l_checkExport___closed__11));
v___x_435_ = l_List_foldl___at___00checkExport_spec__0(v_constMap_432_, v___x_434_);
v___x_436_ = l_Lean_Kernel_Environment_replay(v___x_435_, v___x_433_);
lean_dec_ref(v___x_435_);
if (lean_obj_tag(v___x_436_) == 0)
{
lean_object* v_a_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v_a_437_ = lean_ctor_get(v___x_436_, 0);
lean_inc(v_a_437_);
lean_dec_ref_known(v___x_436_, 1);
v___x_438_ = ((lean_object*)(l_checkExport___closed__12));
v___x_439_ = l_println(v___x_438_, v_silent_390_);
if (lean_obj_tag(v___x_439_) == 0)
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
lean_dec_ref_known(v___x_439_, 1);
v___x_440_ = ((lean_object*)(l_checkExport___closed__14));
v___x_441_ = lean_box(0);
v___x_442_ = l_List_forIn_x27_loop___at___00checkExport_spec__1___redArg(v_constMap_432_, v_a_437_, v___x_440_, v___x_441_);
lean_dec_ref(v_constMap_432_);
if (lean_obj_tag(v___x_442_) == 0)
{
lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_450_; 
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_450_ == 0)
{
lean_object* v_unused_451_; 
v_unused_451_ = lean_ctor_get(v___x_442_, 0);
lean_dec(v_unused_451_);
v___x_444_ = v___x_442_;
v_isShared_445_ = v_isSharedCheck_450_;
goto v_resetjp_443_;
}
else
{
lean_dec(v___x_442_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_450_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_446_; lean_object* v___x_448_; 
v___x_446_ = l_checkExport___boxed__const__2;
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 0, v___x_446_);
v___x_448_ = v___x_444_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v___x_446_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
}
else
{
lean_object* v_a_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v_a_452_ = lean_ctor_get(v___x_442_, 0);
lean_inc(v_a_452_);
lean_dec_ref_known(v___x_442_, 1);
v___x_453_ = ((lean_object*)(l_checkExport___closed__15));
v___x_454_ = lean_io_error_to_string(v_a_452_);
v___x_455_ = lean_string_append(v___x_453_, v___x_454_);
lean_dec_ref(v___x_454_);
v___x_456_ = l_println(v___x_455_, v_silent_390_);
if (lean_obj_tag(v___x_456_) == 0)
{
lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_464_; 
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_456_);
if (v_isSharedCheck_464_ == 0)
{
lean_object* v_unused_465_; 
v_unused_465_ = lean_ctor_get(v___x_456_, 0);
lean_dec(v_unused_465_);
v___x_458_ = v___x_456_;
v_isShared_459_ = v_isSharedCheck_464_;
goto v_resetjp_457_;
}
else
{
lean_dec(v___x_456_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_464_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___x_460_; lean_object* v___x_462_; 
v___x_460_ = l_checkExport___boxed__const__1;
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 0, v___x_460_);
v___x_462_ = v___x_458_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v___x_460_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
else
{
lean_object* v_a_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_473_; 
v_a_466_ = lean_ctor_get(v___x_456_, 0);
v_isSharedCheck_473_ = !lean_is_exclusive(v___x_456_);
if (v_isSharedCheck_473_ == 0)
{
v___x_468_ = v___x_456_;
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_a_466_);
lean_dec(v___x_456_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_471_; 
if (v_isShared_469_ == 0)
{
v___x_471_ = v___x_468_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v_a_466_);
v___x_471_ = v_reuseFailAlloc_472_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
return v___x_471_;
}
}
}
}
}
else
{
lean_object* v_a_474_; 
lean_dec(v_a_437_);
lean_dec_ref(v_constMap_432_);
v_a_474_ = lean_ctor_get(v___x_439_, 0);
lean_inc(v_a_474_);
lean_dec_ref_known(v___x_439_, 1);
v_a_399_ = v_a_474_;
goto v___jp_398_;
}
}
else
{
lean_object* v_a_475_; 
lean_dec_ref(v_constMap_432_);
v_a_475_ = lean_ctor_get(v___x_436_, 0);
lean_inc(v_a_475_);
lean_dec_ref_known(v___x_436_, 1);
v_a_399_ = v_a_475_;
goto v___jp_398_;
}
}
else
{
lean_object* v_a_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_483_; 
lean_dec(v_a_428_);
v_a_476_ = lean_ctor_get(v___x_430_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v___x_430_);
if (v_isSharedCheck_483_ == 0)
{
v___x_478_ = v___x_430_;
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_a_476_);
lean_dec(v___x_430_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_481_; 
if (v_isShared_479_ == 0)
{
v___x_481_ = v___x_478_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v_a_476_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
}
}
else
{
lean_object* v_a_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_491_; 
v_a_484_ = lean_ctor_get(v___x_427_, 0);
v_isSharedCheck_491_ = !lean_is_exclusive(v___x_427_);
if (v_isSharedCheck_491_ == 0)
{
v___x_486_ = v___x_427_;
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_a_484_);
lean_dec(v___x_427_);
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
else
{
lean_object* v_a_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_499_; 
v_a_492_ = lean_ctor_get(v___x_424_, 0);
v_isSharedCheck_499_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_499_ == 0)
{
v___x_494_ = v___x_424_;
v_isShared_495_ = v_isSharedCheck_499_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_a_492_);
lean_dec(v___x_424_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_499_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v___x_497_; 
if (v_isShared_495_ == 0)
{
v___x_497_ = v___x_494_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v_a_492_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
}
}
}
}
else
{
goto v___jp_392_;
}
}
else
{
goto v___jp_392_;
}
v___jp_392_:
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_393_ = ((lean_object*)(l_checkExport___closed__0));
v___x_394_ = l_List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1(v_args_389_);
v___x_395_ = lean_string_append(v___x_393_, v___x_394_);
lean_dec_ref(v___x_394_);
v___x_396_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_396_, 0, v___x_395_);
v___x_397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_397_, 0, v___x_396_);
return v___x_397_;
}
v___jp_398_:
{
lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_400_ = ((lean_object*)(l_checkExport___closed__1));
v___x_401_ = lean_io_error_to_string(v_a_399_);
v___x_402_ = lean_string_append(v___x_400_, v___x_401_);
lean_dec_ref(v___x_401_);
v___x_403_ = l_println(v___x_402_, v_silent_390_);
if (lean_obj_tag(v___x_403_) == 0)
{
lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_411_; 
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_411_ == 0)
{
lean_object* v_unused_412_; 
v_unused_412_ = lean_ctor_get(v___x_403_, 0);
lean_dec(v_unused_412_);
v___x_405_ = v___x_403_;
v_isShared_406_ = v_isSharedCheck_411_;
goto v_resetjp_404_;
}
else
{
lean_dec(v___x_403_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_411_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_407_; lean_object* v___x_409_; 
v___x_407_ = l_checkExport___boxed__const__1;
if (v_isShared_406_ == 0)
{
lean_ctor_set(v___x_405_, 0, v___x_407_);
v___x_409_ = v___x_405_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_407_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
}
else
{
lean_object* v_a_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_420_; 
v_a_413_ = lean_ctor_get(v___x_403_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_420_ == 0)
{
v___x_415_ = v___x_403_;
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_a_413_);
lean_dec(v___x_403_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_418_; 
if (v_isShared_416_ == 0)
{
v___x_418_ = v___x_415_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_a_413_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_checkExport___boxed(lean_object* v_args_500_, lean_object* v_silent_501_, lean_object* v_a_502_){
_start:
{
uint8_t v_silent_boxed_503_; lean_object* v_res_504_; 
v_silent_boxed_503_ = lean_unbox(v_silent_501_);
v_res_504_ = l_checkExport(v_args_500_, v_silent_boxed_503_);
lean_dec(v_args_500_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkExport_spec__1(lean_object* v___x_505_, lean_object* v_a_506_, lean_object* v_as_507_, lean_object* v_as_x27_508_, lean_object* v_b_509_, lean_object* v_a_510_){
_start:
{
lean_object* v___x_512_; 
v___x_512_ = l_List_forIn_x27_loop___at___00checkExport_spec__1___redArg(v___x_505_, v_a_506_, v_as_x27_508_, v_b_509_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkExport_spec__1___boxed(lean_object* v___x_513_, lean_object* v_a_514_, lean_object* v_as_515_, lean_object* v_as_x27_516_, lean_object* v_b_517_, lean_object* v_a_518_, lean_object* v___y_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_List_forIn_x27_loop___at___00checkExport_spec__1(v___x_513_, v_a_514_, v_as_515_, v_as_x27_516_, v_b_517_, v_a_518_);
lean_dec(v_as_x27_516_);
lean_dec(v_as_515_);
lean_dec_ref(v___x_513_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00checkOlean_spec__3(uint8_t v_verbose_523_, uint8_t v_silent_524_, lean_object* v_as_525_, size_t v_sz_526_, size_t v_i_527_, lean_object* v_b_528_){
_start:
{
uint8_t v___x_530_; 
v___x_530_ = lean_usize_dec_lt(v_i_527_, v_sz_526_);
if (v___x_530_ == 0)
{
lean_object* v___x_531_; 
v___x_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_531_, 0, v_b_528_);
return v___x_531_;
}
else
{
lean_object* v_a_532_; lean_object* v_fst_533_; lean_object* v_snd_534_; lean_object* v___x_535_; 
v_a_532_ = lean_array_uget_borrowed(v_as_525_, v_i_527_);
v_fst_533_ = lean_ctor_get(v_a_532_, 0);
v_snd_534_ = lean_ctor_get(v_a_532_, 1);
v___x_535_ = lean_box(0);
if (v_verbose_523_ == 0)
{
goto v___jp_536_;
}
else
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_554_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00checkOlean_spec__3___closed__1));
lean_inc(v_fst_533_);
v___x_555_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_533_, v_verbose_523_);
v___x_556_ = lean_string_append(v___x_554_, v___x_555_);
lean_dec_ref(v___x_555_);
v___x_557_ = l_println(v___x_556_, v_silent_524_);
if (lean_obj_tag(v___x_557_) == 0)
{
lean_dec_ref_known(v___x_557_, 1);
goto v___jp_536_;
}
else
{
return v___x_557_;
}
}
v___jp_536_:
{
lean_object* v___x_537_; 
lean_inc(v_snd_534_);
v___x_537_ = lean_task_get_own(v_snd_534_);
if (lean_obj_tag(v___x_537_) == 0)
{
lean_object* v_a_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v_a_538_ = lean_ctor_get(v___x_537_, 0);
lean_inc(v_a_538_);
lean_dec_ref_known(v___x_537_, 1);
v___x_539_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00checkOlean_spec__3___closed__0));
lean_inc(v_fst_533_);
v___x_540_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_533_, v___x_530_);
v___x_541_ = lean_string_append(v___x_539_, v___x_540_);
lean_dec_ref(v___x_540_);
v___x_542_ = l_IO_eprintln___at___00__private_Init_System_IO_0__IO_eprintlnAux_spec__0(v___x_541_);
if (lean_obj_tag(v___x_542_) == 0)
{
lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_549_; 
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_542_);
if (v_isSharedCheck_549_ == 0)
{
lean_object* v_unused_550_; 
v_unused_550_ = lean_ctor_get(v___x_542_, 0);
lean_dec(v_unused_550_);
v___x_544_ = v___x_542_;
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
else
{
lean_dec(v___x_542_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_547_; 
if (v_isShared_545_ == 0)
{
lean_ctor_set_tag(v___x_544_, 1);
lean_ctor_set(v___x_544_, 0, v_a_538_);
v___x_547_ = v___x_544_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_a_538_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
}
else
{
lean_dec(v_a_538_);
return v___x_542_;
}
}
else
{
size_t v___x_551_; size_t v___x_552_; 
lean_dec(v___x_537_);
v___x_551_ = ((size_t)1ULL);
v___x_552_ = lean_usize_add(v_i_527_, v___x_551_);
v_i_527_ = v___x_552_;
v_b_528_ = v___x_535_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00checkOlean_spec__3___boxed(lean_object* v_verbose_558_, lean_object* v_silent_559_, lean_object* v_as_560_, lean_object* v_sz_561_, lean_object* v_i_562_, lean_object* v_b_563_, lean_object* v___y_564_){
_start:
{
uint8_t v_verbose_boxed_565_; uint8_t v_silent_boxed_566_; size_t v_sz_boxed_567_; size_t v_i_boxed_568_; lean_object* v_res_569_; 
v_verbose_boxed_565_ = lean_unbox(v_verbose_558_);
v_silent_boxed_566_ = lean_unbox(v_silent_559_);
v_sz_boxed_567_ = lean_unbox_usize(v_sz_561_);
lean_dec(v_sz_561_);
v_i_boxed_568_ = lean_unbox_usize(v_i_562_);
lean_dec(v_i_562_);
v_res_569_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00checkOlean_spec__3(v_verbose_boxed_565_, v_silent_boxed_566_, v_as_560_, v_sz_boxed_567_, v_i_boxed_568_, v_b_563_);
lean_dec_ref(v_as_560_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__2___redArg___lam__0(lean_object* v_head_570_){
_start:
{
lean_object* v___x_572_; 
v___x_572_ = l_replayFromImports(v_head_570_);
if (lean_obj_tag(v___x_572_) == 0)
{
lean_object* v_a_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_580_; 
v_a_573_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_580_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_580_ == 0)
{
v___x_575_ = v___x_572_;
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_a_573_);
lean_dec(v___x_572_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_578_; 
if (v_isShared_576_ == 0)
{
lean_ctor_set_tag(v___x_575_, 1);
v___x_578_ = v___x_575_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v_a_573_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
}
else
{
lean_object* v_a_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_588_; 
v_a_581_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_588_ == 0)
{
v___x_583_ = v___x_572_;
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_a_581_);
lean_dec(v___x_572_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_586_; 
if (v_isShared_584_ == 0)
{
lean_ctor_set_tag(v___x_583_, 0);
v___x_586_ = v___x_583_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_a_581_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__2___redArg___lam__0___boxed(lean_object* v_head_589_, lean_object* v___y_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_List_forIn_x27_loop___at___00checkOlean_spec__2___redArg___lam__0(v_head_589_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__2___redArg(lean_object* v_as_x27_592_, lean_object* v_b_593_){
_start:
{
if (lean_obj_tag(v_as_x27_592_) == 0)
{
lean_object* v___x_595_; 
v___x_595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_595_, 0, v_b_593_);
return v___x_595_;
}
else
{
lean_object* v_head_596_; lean_object* v_tail_597_; lean_object* v___f_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v_head_596_ = lean_ctor_get(v_as_x27_592_, 0);
v_tail_597_ = lean_ctor_get(v_as_x27_592_, 1);
lean_inc_n(v_head_596_, 2);
v___f_598_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00checkOlean_spec__2___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_598_, 0, v_head_596_);
v___x_599_ = lean_unsigned_to_nat(0u);
v___x_600_ = lean_io_as_task(v___f_598_, v___x_599_);
v___x_601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_601_, 0, v_head_596_);
lean_ctor_set(v___x_601_, 1, v___x_600_);
v___x_602_ = lean_array_push(v_b_593_, v___x_601_);
v_as_x27_592_ = v_tail_597_;
v_b_593_ = v___x_602_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__2___redArg___boxed(lean_object* v_as_x27_604_, lean_object* v_b_605_, lean_object* v___y_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l_List_forIn_x27_loop___at___00checkOlean_spec__2___redArg(v_as_x27_604_, v_b_605_);
lean_dec(v_as_x27_604_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00checkOlean_spec__5(lean_object* v_x_609_, lean_object* v_x_610_){
_start:
{
if (lean_obj_tag(v_x_609_) == 0)
{
lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_612_ = l_List_reverse___redArg(v_x_610_);
v___x_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_613_, 0, v___x_612_);
return v___x_613_;
}
else
{
lean_object* v_head_614_; lean_object* v_tail_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_629_; 
v_head_614_ = lean_ctor_get(v_x_609_, 0);
v_tail_615_ = lean_ctor_get(v_x_609_, 1);
v_isSharedCheck_629_ = !lean_is_exclusive(v_x_609_);
if (v_isSharedCheck_629_ == 0)
{
v___x_617_ = v_x_609_;
v_isShared_618_ = v_isSharedCheck_629_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_tail_615_);
lean_inc(v_head_614_);
lean_dec(v_x_609_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_629_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_619_; uint8_t v___x_620_; 
lean_inc(v_head_614_);
v___x_619_ = l_String_toName(v_head_614_);
v___x_620_ = l_Lean_Name_isAnonymous(v___x_619_);
if (v___x_620_ == 0)
{
lean_object* v___x_622_; 
lean_dec(v_head_614_);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 1, v_x_610_);
lean_ctor_set(v___x_617_, 0, v___x_619_);
v___x_622_ = v___x_617_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v___x_619_);
lean_ctor_set(v_reuseFailAlloc_624_, 1, v_x_610_);
v___x_622_ = v_reuseFailAlloc_624_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
v_x_609_ = v_tail_615_;
v_x_610_ = v___x_622_;
goto _start;
}
}
else
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
lean_dec(v___x_619_);
lean_del_object(v___x_617_);
lean_dec(v_tail_615_);
lean_dec(v_x_610_);
v___x_625_ = ((lean_object*)(l_List_mapM_loop___at___00checkOlean_spec__5___closed__0));
v___x_626_ = lean_string_append(v___x_625_, v_head_614_);
lean_dec(v_head_614_);
v___x_627_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
v___x_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
return v___x_628_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00checkOlean_spec__5___boxed(lean_object* v_x_630_, lean_object* v_x_631_, lean_object* v___y_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l_List_mapM_loop___at___00checkOlean_spec__5(v_x_630_, v_x_631_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00checkOlean_spec__0(lean_object* v_val_634_, lean_object* v_a_635_, uint8_t v_fresh_636_, lean_object* v_as_637_, size_t v_sz_638_, size_t v_i_639_, lean_object* v_b_640_){
_start:
{
lean_object* v_a_643_; uint8_t v___x_647_; 
v___x_647_ = lean_usize_dec_lt(v_i_639_, v_sz_638_);
if (v___x_647_ == 0)
{
lean_object* v___x_648_; 
v___x_648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_648_, 0, v_b_640_);
return v___x_648_;
}
else
{
lean_object* v_a_649_; lean_object* v___x_650_; 
v_a_649_ = lean_array_uget_borrowed(v_as_637_, v_i_639_);
lean_inc(v_a_649_);
v___x_650_ = l_Lean_searchModuleNameOfFileName(v_a_649_, v_val_634_);
if (lean_obj_tag(v___x_650_) == 0)
{
lean_object* v_a_651_; lean_object* v___y_653_; 
v_a_651_ = lean_ctor_get(v___x_650_, 0);
lean_inc(v_a_651_);
lean_dec_ref_known(v___x_650_, 1);
if (lean_obj_tag(v_a_651_) == 1)
{
lean_object* v_fst_656_; lean_object* v_snd_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_671_; 
v_fst_656_ = lean_ctor_get(v_b_640_, 0);
v_snd_657_ = lean_ctor_get(v_b_640_, 1);
v_isSharedCheck_671_ = !lean_is_exclusive(v_b_640_);
if (v_isSharedCheck_671_ == 0)
{
v___x_659_ = v_b_640_;
v_isShared_660_ = v_isSharedCheck_671_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_snd_657_);
lean_inc(v_fst_656_);
lean_dec(v_b_640_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_671_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v_val_661_; 
v_val_661_ = lean_ctor_get(v_a_651_, 0);
lean_inc(v_val_661_);
lean_dec_ref_known(v_a_651_, 1);
if (v_fresh_636_ == 0)
{
uint8_t v___x_670_; 
v___x_670_ = l_Lean_Name_isPrefixOf(v_a_635_, v_val_661_);
if (v___x_670_ == 0)
{
goto v___jp_665_;
}
else
{
lean_del_object(v___x_659_);
lean_dec(v_snd_657_);
goto v___jp_662_;
}
}
else
{
goto v___jp_665_;
}
v___jp_662_:
{
uint8_t v___x_663_; 
v___x_663_ = l_List_elem___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__1(v_val_661_, v_fst_656_);
if (v___x_663_ == 0)
{
lean_object* v___x_664_; 
v___x_664_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_664_, 0, v_val_661_);
lean_ctor_set(v___x_664_, 1, v_fst_656_);
v___y_653_ = v___x_664_;
goto v___jp_652_;
}
else
{
lean_dec(v_val_661_);
v___y_653_ = v_fst_656_;
goto v___jp_652_;
}
}
v___jp_665_:
{
uint8_t v___x_666_; 
v___x_666_ = lean_name_eq(v_a_635_, v_val_661_);
if (v___x_666_ == 0)
{
lean_object* v___x_668_; 
lean_dec(v_val_661_);
if (v_isShared_660_ == 0)
{
v___x_668_ = v___x_659_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_fst_656_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v_snd_657_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
v_a_643_ = v___x_668_;
goto v___jp_642_;
}
}
else
{
lean_del_object(v___x_659_);
lean_dec(v_snd_657_);
goto v___jp_662_;
}
}
}
}
else
{
lean_object* v_fst_672_; lean_object* v_snd_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_680_; 
lean_dec(v_a_651_);
v_fst_672_ = lean_ctor_get(v_b_640_, 0);
v_snd_673_ = lean_ctor_get(v_b_640_, 1);
v_isSharedCheck_680_ = !lean_is_exclusive(v_b_640_);
if (v_isSharedCheck_680_ == 0)
{
v___x_675_ = v_b_640_;
v_isShared_676_ = v_isSharedCheck_680_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_snd_673_);
lean_inc(v_fst_672_);
lean_dec(v_b_640_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_680_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_678_; 
if (v_isShared_676_ == 0)
{
v___x_678_ = v___x_675_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_fst_672_);
lean_ctor_set(v_reuseFailAlloc_679_, 1, v_snd_673_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
v_a_643_ = v___x_678_;
goto v___jp_642_;
}
}
}
v___jp_652_:
{
lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_654_ = lean_box(v___x_647_);
v___x_655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_655_, 0, v___y_653_);
lean_ctor_set(v___x_655_, 1, v___x_654_);
v_a_643_ = v___x_655_;
goto v___jp_642_;
}
}
else
{
lean_object* v_a_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_688_; 
lean_dec_ref(v_b_640_);
v_a_681_ = lean_ctor_get(v___x_650_, 0);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_688_ == 0)
{
v___x_683_ = v___x_650_;
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_a_681_);
lean_dec(v___x_650_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v___x_686_; 
if (v_isShared_684_ == 0)
{
v___x_686_ = v___x_683_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_a_681_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
}
v___jp_642_:
{
size_t v___x_644_; size_t v___x_645_; 
v___x_644_ = ((size_t)1ULL);
v___x_645_ = lean_usize_add(v_i_639_, v___x_644_);
v_i_639_ = v___x_645_;
v_b_640_ = v_a_643_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00checkOlean_spec__0___boxed(lean_object* v_val_689_, lean_object* v_a_690_, lean_object* v_fresh_691_, lean_object* v_as_692_, lean_object* v_sz_693_, lean_object* v_i_694_, lean_object* v_b_695_, lean_object* v___y_696_){
_start:
{
uint8_t v_fresh_boxed_697_; size_t v_sz_boxed_698_; size_t v_i_boxed_699_; lean_object* v_res_700_; 
v_fresh_boxed_697_ = lean_unbox(v_fresh_691_);
v_sz_boxed_698_ = lean_unbox_usize(v_sz_693_);
lean_dec(v_sz_693_);
v_i_boxed_699_ = lean_unbox_usize(v_i_694_);
lean_dec(v_i_694_);
v_res_700_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00checkOlean_spec__0(v_val_689_, v_a_690_, v_fresh_boxed_697_, v_as_692_, v_sz_boxed_698_, v_i_boxed_699_, v_b_695_);
lean_dec_ref(v_as_692_);
lean_dec(v_a_690_);
lean_dec(v_val_689_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__1___redArg(lean_object* v_val_703_, uint8_t v_fresh_704_, lean_object* v_as_x27_705_, lean_object* v_b_706_){
_start:
{
if (lean_obj_tag(v_as_x27_705_) == 0)
{
lean_object* v___x_708_; 
v___x_708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_708_, 0, v_b_706_);
return v___x_708_;
}
else
{
lean_object* v_head_709_; lean_object* v_tail_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v_head_709_ = lean_ctor_get(v_as_x27_705_, 0);
v_tail_710_ = lean_ctor_get(v_as_x27_705_, 1);
v___x_711_ = ((lean_object*)(l_List_forIn_x27_loop___at___00checkOlean_spec__1___redArg___closed__0));
v___x_712_ = l_Lean_SearchPath_findAllWithExt(v_val_703_, v___x_711_);
if (lean_obj_tag(v___x_712_) == 0)
{
lean_object* v_a_713_; uint8_t v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; size_t v_sz_717_; size_t v___x_718_; lean_object* v___x_719_; 
v_a_713_ = lean_ctor_get(v___x_712_, 0);
lean_inc(v_a_713_);
lean_dec_ref_known(v___x_712_, 1);
v___x_714_ = 0;
v___x_715_ = lean_box(v___x_714_);
v___x_716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_716_, 0, v_b_706_);
lean_ctor_set(v___x_716_, 1, v___x_715_);
v_sz_717_ = lean_array_size(v_a_713_);
v___x_718_ = ((size_t)0ULL);
v___x_719_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00checkOlean_spec__0(v_val_703_, v_head_709_, v_fresh_704_, v_a_713_, v_sz_717_, v___x_718_, v___x_716_);
lean_dec(v_a_713_);
if (lean_obj_tag(v___x_719_) == 0)
{
lean_object* v_a_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_736_; 
v_a_720_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_736_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_736_ == 0)
{
v___x_722_ = v___x_719_;
v_isShared_723_ = v_isSharedCheck_736_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_a_720_);
lean_dec(v___x_719_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_736_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v_snd_724_; uint8_t v___x_725_; 
v_snd_724_ = lean_ctor_get(v_a_720_, 1);
v___x_725_ = lean_unbox(v_snd_724_);
if (v___x_725_ == 0)
{
uint8_t v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_732_; 
lean_dec(v_a_720_);
v___x_726_ = 1;
v___x_727_ = ((lean_object*)(l_List_forIn_x27_loop___at___00checkOlean_spec__1___redArg___closed__1));
lean_inc(v_head_709_);
v___x_728_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_709_, v___x_726_);
v___x_729_ = lean_string_append(v___x_727_, v___x_728_);
lean_dec_ref(v___x_728_);
v___x_730_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_730_, 0, v___x_729_);
if (v_isShared_723_ == 0)
{
lean_ctor_set_tag(v___x_722_, 1);
lean_ctor_set(v___x_722_, 0, v___x_730_);
v___x_732_ = v___x_722_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v___x_730_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
else
{
lean_object* v_fst_734_; 
lean_del_object(v___x_722_);
v_fst_734_ = lean_ctor_get(v_a_720_, 0);
lean_inc(v_fst_734_);
lean_dec(v_a_720_);
v_as_x27_705_ = v_tail_710_;
v_b_706_ = v_fst_734_;
goto _start;
}
}
}
else
{
lean_object* v_a_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_744_; 
v_a_737_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_744_ == 0)
{
v___x_739_ = v___x_719_;
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_a_737_);
lean_dec(v___x_719_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_742_; 
if (v_isShared_740_ == 0)
{
v___x_742_ = v___x_739_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_a_737_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
}
else
{
lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_752_; 
lean_dec(v_b_706_);
v_a_745_ = lean_ctor_get(v___x_712_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_752_ == 0)
{
v___x_747_ = v___x_712_;
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_a_745_);
lean_dec(v___x_712_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_750_; 
if (v_isShared_748_ == 0)
{
v___x_750_ = v___x_747_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_a_745_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__1___redArg___boxed(lean_object* v_val_753_, lean_object* v_fresh_754_, lean_object* v_as_x27_755_, lean_object* v_b_756_, lean_object* v___y_757_){
_start:
{
uint8_t v_fresh_boxed_758_; lean_object* v_res_759_; 
v_fresh_boxed_758_ = lean_unbox(v_fresh_754_);
v_res_759_ = l_List_forIn_x27_loop___at___00checkOlean_spec__1___redArg(v_val_753_, v_fresh_boxed_758_, v_as_x27_755_, v_b_756_);
lean_dec(v_as_x27_755_);
lean_dec(v_val_753_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__4___redArg(uint8_t v_verbose_761_, uint8_t v_silent_762_, lean_object* v_as_x27_763_, lean_object* v_b_764_){
_start:
{
if (lean_obj_tag(v_as_x27_763_) == 0)
{
lean_object* v___x_766_; 
v___x_766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_766_, 0, v_b_764_);
return v___x_766_;
}
else
{
lean_object* v_head_767_; lean_object* v_tail_768_; lean_object* v___x_769_; 
v_head_767_ = lean_ctor_get(v_as_x27_763_, 0);
v_tail_768_ = lean_ctor_get(v_as_x27_763_, 1);
v___x_769_ = lean_box(0);
if (v_verbose_761_ == 0)
{
goto v___jp_770_;
}
else
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_773_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00checkOlean_spec__3___closed__1));
lean_inc(v_head_767_);
v___x_774_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_767_, v_verbose_761_);
v___x_775_ = lean_string_append(v___x_773_, v___x_774_);
lean_dec_ref(v___x_774_);
v___x_776_ = ((lean_object*)(l_List_forIn_x27_loop___at___00checkOlean_spec__4___redArg___closed__0));
v___x_777_ = lean_string_append(v___x_775_, v___x_776_);
v___x_778_ = l_println(v___x_777_, v_silent_762_);
if (lean_obj_tag(v___x_778_) == 0)
{
lean_dec_ref_known(v___x_778_, 1);
goto v___jp_770_;
}
else
{
return v___x_778_;
}
}
v___jp_770_:
{
lean_object* v___x_771_; 
lean_inc(v_head_767_);
v___x_771_ = l_replayFromFresh(v_head_767_);
if (lean_obj_tag(v___x_771_) == 0)
{
lean_dec_ref_known(v___x_771_, 1);
v_as_x27_763_ = v_tail_768_;
v_b_764_ = v___x_769_;
goto _start;
}
else
{
return v___x_771_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__4___redArg___boxed(lean_object* v_verbose_779_, lean_object* v_silent_780_, lean_object* v_as_x27_781_, lean_object* v_b_782_, lean_object* v___y_783_){
_start:
{
uint8_t v_verbose_boxed_784_; uint8_t v_silent_boxed_785_; lean_object* v_res_786_; 
v_verbose_boxed_784_ = lean_unbox(v_verbose_779_);
v_silent_boxed_785_ = lean_unbox(v_silent_780_);
v_res_786_ = l_List_forIn_x27_loop___at___00checkOlean_spec__4___redArg(v_verbose_boxed_784_, v_silent_boxed_785_, v_as_x27_781_, v_b_782_);
lean_dec(v_as_x27_781_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l_checkOlean(lean_object* v_args_791_, uint8_t v_fresh_792_, uint8_t v_verbose_793_, uint8_t v_silent_794_){
_start:
{
lean_object* v_targets_800_; lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_862_ = ((lean_object*)(l_checkOlean___closed__2));
v___x_863_ = l_Lean_findSysroot(v___x_862_);
if (lean_obj_tag(v___x_863_) == 0)
{
lean_object* v_a_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
v_a_864_ = lean_ctor_get(v___x_863_, 0);
lean_inc(v_a_864_);
lean_dec_ref_known(v___x_863_, 1);
v___x_865_ = lean_box(0);
v___x_866_ = l_Lean_initSearchPath(v_a_864_, v___x_865_);
if (lean_obj_tag(v___x_866_) == 0)
{
lean_dec_ref_known(v___x_866_, 1);
if (lean_obj_tag(v_args_791_) == 0)
{
lean_object* v___x_867_; 
v___x_867_ = l_getCurrentModule();
if (lean_obj_tag(v___x_867_) == 0)
{
lean_object* v_a_868_; lean_object* v___x_869_; 
v_a_868_ = lean_ctor_get(v___x_867_, 0);
lean_inc(v_a_868_);
lean_dec_ref_known(v___x_867_, 1);
v___x_869_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_869_, 0, v_a_868_);
lean_ctor_set(v___x_869_, 1, v___x_865_);
v_targets_800_ = v___x_869_;
goto v___jp_799_;
}
else
{
lean_object* v_a_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_877_; 
v_a_870_ = lean_ctor_get(v___x_867_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_877_ == 0)
{
v___x_872_ = v___x_867_;
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_a_870_);
lean_dec(v___x_867_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_875_; 
if (v_isShared_873_ == 0)
{
v___x_875_ = v___x_872_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_a_870_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
}
else
{
lean_object* v___x_878_; 
v___x_878_ = l_List_mapM_loop___at___00checkOlean_spec__5(v_args_791_, v___x_865_);
if (lean_obj_tag(v___x_878_) == 0)
{
lean_object* v_a_879_; 
v_a_879_ = lean_ctor_get(v___x_878_, 0);
lean_inc(v_a_879_);
lean_dec_ref_known(v___x_878_, 1);
v_targets_800_ = v_a_879_;
goto v___jp_799_;
}
else
{
lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_887_; 
v_a_880_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_887_ == 0)
{
v___x_882_ = v___x_878_;
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v___x_878_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_885_; 
if (v_isShared_883_ == 0)
{
v___x_885_ = v___x_882_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_a_880_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
}
}
else
{
lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_895_; 
lean_dec(v_args_791_);
v_a_888_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_895_ == 0)
{
v___x_890_ = v___x_866_;
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_dec(v___x_866_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_893_; 
if (v_isShared_891_ == 0)
{
v___x_893_ = v___x_890_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_a_888_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
}
else
{
lean_object* v_a_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_903_; 
lean_dec(v_args_791_);
v_a_896_ = lean_ctor_get(v___x_863_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_903_ == 0)
{
v___x_898_ = v___x_863_;
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_a_896_);
lean_dec(v___x_863_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v___x_901_; 
if (v_isShared_899_ == 0)
{
v___x_901_ = v___x_898_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_a_896_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
}
v___jp_796_:
{
lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_797_ = l_checkExport___boxed__const__2;
v___x_798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_798_, 0, v___x_797_);
return v___x_798_;
}
v___jp_799_:
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_801_ = l_Lean_searchPathRef;
v___x_802_ = lean_st_ref_get(v___x_801_);
v___x_803_ = lean_box(0);
v___x_804_ = l_List_forIn_x27_loop___at___00checkOlean_spec__1___redArg(v___x_802_, v_fresh_792_, v_targets_800_, v___x_803_);
lean_dec(v_targets_800_);
lean_dec(v___x_802_);
if (lean_obj_tag(v___x_804_) == 0)
{
if (v_fresh_792_ == 0)
{
lean_object* v_a_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
v_a_805_ = lean_ctor_get(v___x_804_, 0);
lean_inc(v_a_805_);
lean_dec_ref_known(v___x_804_, 1);
v___x_806_ = ((lean_object*)(l_checkOlean___closed__0));
v___x_807_ = l_List_forIn_x27_loop___at___00checkOlean_spec__2___redArg(v_a_805_, v___x_806_);
lean_dec(v_a_805_);
if (lean_obj_tag(v___x_807_) == 0)
{
lean_object* v_a_808_; lean_object* v___x_809_; size_t v_sz_810_; size_t v___x_811_; lean_object* v___x_812_; 
v_a_808_ = lean_ctor_get(v___x_807_, 0);
lean_inc(v_a_808_);
lean_dec_ref_known(v___x_807_, 1);
v___x_809_ = lean_box(0);
v_sz_810_ = lean_array_size(v_a_808_);
v___x_811_ = ((size_t)0ULL);
v___x_812_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00checkOlean_spec__3(v_verbose_793_, v_silent_794_, v_a_808_, v_sz_810_, v___x_811_, v___x_809_);
lean_dec(v_a_808_);
if (lean_obj_tag(v___x_812_) == 0)
{
lean_dec_ref_known(v___x_812_, 1);
goto v___jp_796_;
}
else
{
lean_object* v_a_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_820_; 
v_a_813_ = lean_ctor_get(v___x_812_, 0);
v_isSharedCheck_820_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_820_ == 0)
{
v___x_815_ = v___x_812_;
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_a_813_);
lean_dec(v___x_812_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_818_; 
if (v_isShared_816_ == 0)
{
v___x_818_ = v___x_815_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v_a_813_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
}
}
else
{
lean_object* v_a_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_828_; 
v_a_821_ = lean_ctor_get(v___x_807_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_828_ == 0)
{
v___x_823_ = v___x_807_;
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_a_821_);
lean_dec(v___x_807_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_826_; 
if (v_isShared_824_ == 0)
{
v___x_826_ = v___x_823_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_a_821_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
}
}
else
{
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_853_; 
v_a_829_ = lean_ctor_get(v___x_804_, 0);
v_isSharedCheck_853_ = !lean_is_exclusive(v___x_804_);
if (v_isSharedCheck_853_ == 0)
{
v___x_831_ = v___x_804_;
v_isShared_832_ = v_isSharedCheck_853_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___x_804_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_853_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_833_; lean_object* v___x_834_; uint8_t v___x_835_; 
v___x_833_ = l_List_lengthTR___redArg(v_a_829_);
v___x_834_ = lean_unsigned_to_nat(1u);
v___x_835_ = lean_nat_dec_eq(v___x_833_, v___x_834_);
lean_dec(v___x_833_);
if (v___x_835_ == 0)
{
lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_841_; 
v___x_836_ = ((lean_object*)(l_checkOlean___closed__1));
v___x_837_ = l_List_toString___at___00Lean_Environment_AddConstAsyncResult_commitConst_spec__1(v_a_829_);
v___x_838_ = lean_string_append(v___x_836_, v___x_837_);
lean_dec_ref(v___x_837_);
v___x_839_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_839_, 0, v___x_838_);
if (v_isShared_832_ == 0)
{
lean_ctor_set_tag(v___x_831_, 1);
lean_ctor_set(v___x_831_, 0, v___x_839_);
v___x_841_ = v___x_831_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v___x_839_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
else
{
lean_object* v___x_843_; lean_object* v___x_844_; 
lean_del_object(v___x_831_);
v___x_843_ = lean_box(0);
v___x_844_ = l_List_forIn_x27_loop___at___00checkOlean_spec__4___redArg(v_verbose_793_, v_silent_794_, v_a_829_, v___x_843_);
lean_dec(v_a_829_);
if (lean_obj_tag(v___x_844_) == 0)
{
lean_dec_ref_known(v___x_844_, 1);
goto v___jp_796_;
}
else
{
lean_object* v_a_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_852_; 
v_a_845_ = lean_ctor_get(v___x_844_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_852_ == 0)
{
v___x_847_ = v___x_844_;
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_a_845_);
lean_dec(v___x_844_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_850_; 
if (v_isShared_848_ == 0)
{
v___x_850_ = v___x_847_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_a_845_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_861_; 
v_a_854_ = lean_ctor_get(v___x_804_, 0);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_804_);
if (v_isSharedCheck_861_ == 0)
{
v___x_856_ = v___x_804_;
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_a_854_);
lean_dec(v___x_804_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_859_; 
if (v_isShared_857_ == 0)
{
v___x_859_ = v___x_856_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_a_854_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_checkOlean___boxed(lean_object* v_args_904_, lean_object* v_fresh_905_, lean_object* v_verbose_906_, lean_object* v_silent_907_, lean_object* v_a_908_){
_start:
{
uint8_t v_fresh_boxed_909_; uint8_t v_verbose_boxed_910_; uint8_t v_silent_boxed_911_; lean_object* v_res_912_; 
v_fresh_boxed_909_ = lean_unbox(v_fresh_905_);
v_verbose_boxed_910_ = lean_unbox(v_verbose_906_);
v_silent_boxed_911_ = lean_unbox(v_silent_907_);
v_res_912_ = l_checkOlean(v_args_904_, v_fresh_boxed_909_, v_verbose_boxed_910_, v_silent_boxed_911_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__1(lean_object* v_val_913_, uint8_t v_fresh_914_, lean_object* v_as_915_, lean_object* v_as_x27_916_, lean_object* v_b_917_, lean_object* v_a_918_){
_start:
{
lean_object* v___x_920_; 
v___x_920_ = l_List_forIn_x27_loop___at___00checkOlean_spec__1___redArg(v_val_913_, v_fresh_914_, v_as_x27_916_, v_b_917_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__1___boxed(lean_object* v_val_921_, lean_object* v_fresh_922_, lean_object* v_as_923_, lean_object* v_as_x27_924_, lean_object* v_b_925_, lean_object* v_a_926_, lean_object* v___y_927_){
_start:
{
uint8_t v_fresh_boxed_928_; lean_object* v_res_929_; 
v_fresh_boxed_928_ = lean_unbox(v_fresh_922_);
v_res_929_ = l_List_forIn_x27_loop___at___00checkOlean_spec__1(v_val_921_, v_fresh_boxed_928_, v_as_923_, v_as_x27_924_, v_b_925_, v_a_926_);
lean_dec(v_as_x27_924_);
lean_dec(v_as_923_);
lean_dec(v_val_921_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__2(lean_object* v_as_930_, lean_object* v_as_x27_931_, lean_object* v_b_932_, lean_object* v_a_933_){
_start:
{
lean_object* v___x_935_; 
v___x_935_ = l_List_forIn_x27_loop___at___00checkOlean_spec__2___redArg(v_as_x27_931_, v_b_932_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__2___boxed(lean_object* v_as_936_, lean_object* v_as_x27_937_, lean_object* v_b_938_, lean_object* v_a_939_, lean_object* v___y_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l_List_forIn_x27_loop___at___00checkOlean_spec__2(v_as_936_, v_as_x27_937_, v_b_938_, v_a_939_);
lean_dec(v_as_x27_937_);
lean_dec(v_as_936_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__4(uint8_t v_verbose_942_, uint8_t v_silent_943_, lean_object* v_as_944_, lean_object* v_as_x27_945_, lean_object* v_b_946_, lean_object* v_a_947_){
_start:
{
lean_object* v___x_949_; 
v___x_949_ = l_List_forIn_x27_loop___at___00checkOlean_spec__4___redArg(v_verbose_942_, v_silent_943_, v_as_x27_945_, v_b_946_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__4___boxed(lean_object* v_verbose_950_, lean_object* v_silent_951_, lean_object* v_as_952_, lean_object* v_as_x27_953_, lean_object* v_b_954_, lean_object* v_a_955_, lean_object* v___y_956_){
_start:
{
uint8_t v_verbose_boxed_957_; uint8_t v_silent_boxed_958_; lean_object* v_res_959_; 
v_verbose_boxed_957_ = lean_unbox(v_verbose_950_);
v_silent_boxed_958_ = lean_unbox(v_silent_951_);
v_res_959_ = l_List_forIn_x27_loop___at___00checkOlean_spec__4(v_verbose_boxed_957_, v_silent_boxed_958_, v_as_952_, v_as_x27_953_, v_b_954_, v_a_955_);
lean_dec(v_as_x27_953_);
lean_dec(v_as_952_);
return v_res_959_;
}
}
static lean_object* _init_l_List_partition_loop___at___00main_spec__0___closed__1(void){
_start:
{
lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_961_ = ((lean_object*)(l_List_partition_loop___at___00main_spec__0___closed__0));
v___x_962_ = lean_string_utf8_byte_size(v___x_961_);
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l_List_partition_loop___at___00main_spec__0(lean_object* v_a_963_, lean_object* v_a_964_){
_start:
{
if (lean_obj_tag(v_a_963_) == 0)
{
lean_object* v_fst_965_; lean_object* v_snd_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_975_; 
v_fst_965_ = lean_ctor_get(v_a_964_, 0);
v_snd_966_ = lean_ctor_get(v_a_964_, 1);
v_isSharedCheck_975_ = !lean_is_exclusive(v_a_964_);
if (v_isSharedCheck_975_ == 0)
{
v___x_968_ = v_a_964_;
v_isShared_969_ = v_isSharedCheck_975_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_snd_966_);
lean_inc(v_fst_965_);
lean_dec(v_a_964_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_975_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_973_; 
v___x_970_ = l_List_reverse___redArg(v_fst_965_);
v___x_971_ = l_List_reverse___redArg(v_snd_966_);
if (v_isShared_969_ == 0)
{
lean_ctor_set(v___x_968_, 1, v___x_971_);
lean_ctor_set(v___x_968_, 0, v___x_970_);
v___x_973_ = v___x_968_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v___x_970_);
lean_ctor_set(v_reuseFailAlloc_974_, 1, v___x_971_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
}
else
{
lean_object* v_head_976_; lean_object* v_tail_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_1004_; 
v_head_976_ = lean_ctor_get(v_a_963_, 0);
v_tail_977_ = lean_ctor_get(v_a_963_, 1);
v_isSharedCheck_1004_ = !lean_is_exclusive(v_a_963_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_979_ = v_a_963_;
v_isShared_980_ = v_isSharedCheck_1004_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_tail_977_);
lean_inc(v_head_976_);
lean_dec(v_a_963_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_1004_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v_fst_981_; lean_object* v_snd_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_1003_; 
v_fst_981_ = lean_ctor_get(v_a_964_, 0);
v_snd_982_ = lean_ctor_get(v_a_964_, 1);
v_isSharedCheck_1003_ = !lean_is_exclusive(v_a_964_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_984_ = v_a_964_;
v_isShared_985_ = v_isSharedCheck_1003_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_snd_982_);
lean_inc(v_fst_981_);
lean_dec(v_a_964_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_1003_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; uint8_t v___x_997_; 
v___x_994_ = ((lean_object*)(l_List_partition_loop___at___00main_spec__0___closed__0));
v___x_995_ = lean_string_utf8_byte_size(v_head_976_);
v___x_996_ = lean_obj_once(&l_List_partition_loop___at___00main_spec__0___closed__1, &l_List_partition_loop___at___00main_spec__0___closed__1_once, _init_l_List_partition_loop___at___00main_spec__0___closed__1);
v___x_997_ = lean_nat_dec_le(v___x_996_, v___x_995_);
if (v___x_997_ == 0)
{
goto v___jp_986_;
}
else
{
lean_object* v___x_998_; uint8_t v___x_999_; 
v___x_998_ = lean_unsigned_to_nat(0u);
v___x_999_ = lean_string_memcmp(v_head_976_, v___x_994_, v___x_998_, v___x_998_, v___x_996_);
if (v___x_999_ == 0)
{
goto v___jp_986_;
}
else
{
lean_object* v___x_1000_; lean_object* v___x_1001_; 
lean_del_object(v___x_984_);
lean_del_object(v___x_979_);
v___x_1000_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1000_, 0, v_head_976_);
lean_ctor_set(v___x_1000_, 1, v_fst_981_);
v___x_1001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_1000_);
lean_ctor_set(v___x_1001_, 1, v_snd_982_);
v_a_963_ = v_tail_977_;
v_a_964_ = v___x_1001_;
goto _start;
}
}
v___jp_986_:
{
lean_object* v___x_988_; 
if (v_isShared_980_ == 0)
{
lean_ctor_set(v___x_979_, 1, v_snd_982_);
v___x_988_ = v___x_979_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_head_976_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v_snd_982_);
v___x_988_ = v_reuseFailAlloc_993_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
lean_object* v___x_990_; 
if (v_isShared_985_ == 0)
{
lean_ctor_set(v___x_984_, 1, v___x_988_);
v___x_990_ = v___x_984_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_fst_981_);
lean_ctor_set(v_reuseFailAlloc_992_, 1, v___x_988_);
v___x_990_ = v_reuseFailAlloc_992_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
v_a_963_ = v_tail_977_;
v_a_964_ = v___x_990_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* _lean_main(lean_object* v_args_1012_){
_start:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v_fst_1016_; lean_object* v_snd_1017_; uint8_t v___y_1019_; lean_object* v___x_1025_; uint8_t v___x_1026_; 
v___x_1014_ = ((lean_object*)(l_main___closed__0));
v___x_1015_ = l_List_partition_loop___at___00main_spec__0(v_args_1012_, v___x_1014_);
v_fst_1016_ = lean_ctor_get(v___x_1015_, 0);
lean_inc(v_fst_1016_);
v_snd_1017_ = lean_ctor_get(v___x_1015_, 1);
lean_inc(v_snd_1017_);
lean_dec_ref(v___x_1015_);
v___x_1025_ = ((lean_object*)(l_main___closed__3));
v___x_1026_ = l_List_elem___at___00Lean_isAutoDeclOrPrivate__Internal_spec__0(v___x_1025_, v_fst_1016_);
if (v___x_1026_ == 0)
{
lean_object* v___x_1027_; uint8_t v___x_1028_; 
v___x_1027_ = ((lean_object*)(l_main___closed__4));
v___x_1028_ = l_List_elem___at___00Lean_isAutoDeclOrPrivate__Internal_spec__0(v___x_1027_, v_fst_1016_);
if (v___x_1028_ == 0)
{
lean_object* v___x_1029_; uint8_t v___x_1030_; 
v___x_1029_ = ((lean_object*)(l_main___closed__5));
v___x_1030_ = l_List_elem___at___00Lean_isAutoDeclOrPrivate__Internal_spec__0(v___x_1029_, v_fst_1016_);
v___y_1019_ = v___x_1030_;
goto v___jp_1018_;
}
else
{
v___y_1019_ = v___x_1028_;
goto v___jp_1018_;
}
}
else
{
lean_object* v___x_1031_; uint8_t v___x_1032_; lean_object* v___x_1033_; 
v___x_1031_ = ((lean_object*)(l_main___closed__2));
v___x_1032_ = l_List_elem___at___00Lean_isAutoDeclOrPrivate__Internal_spec__0(v___x_1031_, v_fst_1016_);
lean_dec(v_fst_1016_);
v___x_1033_ = l_checkExport(v_snd_1017_, v___x_1032_);
lean_dec(v_snd_1017_);
return v___x_1033_;
}
v___jp_1018_:
{
lean_object* v___x_1020_; uint8_t v___x_1021_; lean_object* v___x_1022_; uint8_t v___x_1023_; lean_object* v___x_1024_; 
v___x_1020_ = ((lean_object*)(l_main___closed__1));
v___x_1021_ = l_List_elem___at___00Lean_isAutoDeclOrPrivate__Internal_spec__0(v___x_1020_, v_fst_1016_);
v___x_1022_ = ((lean_object*)(l_main___closed__2));
v___x_1023_ = l_List_elem___at___00Lean_isAutoDeclOrPrivate__Internal_spec__0(v___x_1022_, v_fst_1016_);
lean_dec(v_fst_1016_);
v___x_1024_ = l_checkOlean(v_snd_1017_, v___x_1021_, v___y_1019_, v___x_1023_);
return v___x_1024_;
}
}
}
LEAN_EXPORT lean_object* l_main___boxed(lean_object* v_args_1034_, lean_object* v_a_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = _lean_main(v_args_1034_);
return v_res_1036_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Lean_CoreM(uint8_t builtin);
lean_object* initialize_Lean_Replay(uint8_t builtin);
lean_object* initialize_Lake_Load_Manifest(uint8_t builtin);
lean_object* initialize_LeanExport_Parse(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_LeanChecker(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
lean_initialize();
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Replay(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Manifest(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LeanExport_Parse(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_checkExport___boxed__const__1 = _init_l_checkExport___boxed__const__1();
lean_mark_persistent(l_checkExport___boxed__const__1);
l_checkExport___boxed__const__2 = _init_l_checkExport___boxed__const__2();
lean_mark_persistent(l_checkExport___boxed__const__2);
return lean_io_result_mk_ok(lean_box(0));
}
char ** lean_setup_args(int argc, char ** argv);
#if defined(WIN32) || defined(_WIN32)
#include <windows.h>
#endif
lean_object* run_main(int argc, char ** argv) {
    lean_object* in = lean_box(0);
    int i = argc;
    while (i > 1) {
      lean_object* n;
      i--;
      n = lean_alloc_ctor(1,2,0); lean_ctor_set(n, 0, lean_mk_string(argv[i])); lean_ctor_set(n, 1, in);
      in = n;
    }
    return _lean_main(in);
}
int main(int argc, char ** argv) {
#if defined(WIN32) || defined(_WIN32)
  SetErrorMode(SEM_FAILCRITICALERRORS);
  SetConsoleOutputCP(CP_UTF8);
#endif
  lean_object* res;
  argv = lean_setup_args(argc, argv);
  res = initialize_LeanChecker(1 /* builtin */);
  lean_io_mark_end_initialization();
  if (lean_io_result_is_ok(res)) {
    lean_dec_ref(res);
    lean_init_task_manager();
    res = lean_run_main(&run_main, argc, argv);
  }
  lean_finalize_task_manager();
  if (lean_io_result_is_ok(res)) {
    int ret = lean_unbox_uint32(lean_io_result_get_value(res));
    lean_dec_ref(res);
    return ret;
  } else {
    lean_io_result_show_error(res);
    lean_dec_ref(res);
    return 1;
  }
}
#ifdef __cplusplus
}
#endif

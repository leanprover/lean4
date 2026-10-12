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
uint8_t l_List_elem___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_4052238930____hygCtx___hyg_2__spec__1(lean_object*, lean_object*);
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
lean_object* l_println(lean_object* v_msg_1_, uint8_t v_silent_2_){
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
LEAN_EXPORT void l_println_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1_ = stack[0].m_obj;
uint8_t v_silent_2_ = stack[1].m_num;
lean_object* v_res_7_;
v_res_7_ = l_println(v_msg_1_, v_silent_2_);
stack->m_obj
 = v_res_7_;
}
LEAN_EXPORT lean_object* l_println___boxed(lean_object* v_msg_8_, lean_object* v_silent_9_, lean_object* v_a_10_){
_start:
{
uint8_t v_silent_boxed_11_; lean_object* v_res_12_; 
v_silent_boxed_11_ = lean_unbox(v_silent_9_);
v_res_12_ = l_println(v_msg_8_, v_silent_boxed_11_);
return v_res_12_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00replayFromImports_spec__0(lean_object* v_as_13_, size_t v_sz_14_, size_t v_i_15_, lean_object* v_b_16_){
_start:
{
uint8_t v___x_18_; 
v___x_18_ = lean_usize_dec_lt(v_i_15_, v_sz_14_);
if (v___x_18_ == 0)
{
lean_object* v___x_19_; 
v___x_19_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_19_, 0, v_b_16_);
return v___x_19_;
}
else
{
lean_object* v_snd_20_; lean_object* v_fst_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_54_; 
v_snd_20_ = lean_ctor_get(v_b_16_, 1);
v_fst_21_ = lean_ctor_get(v_b_16_, 0);
v_isSharedCheck_54_ = !lean_is_exclusive(v_b_16_);
if (v_isSharedCheck_54_ == 0)
{
v___x_23_ = v_b_16_;
v_isShared_24_ = v_isSharedCheck_54_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_snd_20_);
lean_inc(v_fst_21_);
lean_dec(v_b_16_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_54_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v_array_25_; lean_object* v_start_26_; lean_object* v_stop_27_; uint8_t v___x_28_; 
v_array_25_ = lean_ctor_get(v_snd_20_, 0);
v_start_26_ = lean_ctor_get(v_snd_20_, 1);
v_stop_27_ = lean_ctor_get(v_snd_20_, 2);
v___x_28_ = lean_nat_dec_lt(v_start_26_, v_stop_27_);
if (v___x_28_ == 0)
{
lean_object* v___x_30_; 
if (v_isShared_24_ == 0)
{
v___x_30_ = v___x_23_;
goto v_reusejp_29_;
}
else
{
lean_object* v_reuseFailAlloc_32_; 
v_reuseFailAlloc_32_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_32_, 0, v_fst_21_);
lean_ctor_set(v_reuseFailAlloc_32_, 1, v_snd_20_);
v___x_30_ = v_reuseFailAlloc_32_;
goto v_reusejp_29_;
}
v_reusejp_29_:
{
lean_object* v___x_31_; 
v___x_31_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_31_, 0, v___x_30_);
return v___x_31_;
}
}
else
{
lean_object* v___x_34_; uint8_t v_isShared_35_; uint8_t v_isSharedCheck_50_; 
lean_inc(v_stop_27_);
lean_inc(v_start_26_);
lean_inc_ref(v_array_25_);
v_isSharedCheck_50_ = !lean_is_exclusive(v_snd_20_);
if (v_isSharedCheck_50_ == 0)
{
lean_object* v_unused_51_; lean_object* v_unused_52_; lean_object* v_unused_53_; 
v_unused_51_ = lean_ctor_get(v_snd_20_, 2);
lean_dec(v_unused_51_);
v_unused_52_ = lean_ctor_get(v_snd_20_, 1);
lean_dec(v_unused_52_);
v_unused_53_ = lean_ctor_get(v_snd_20_, 0);
lean_dec(v_unused_53_);
v___x_34_ = v_snd_20_;
v_isShared_35_ = v_isSharedCheck_50_;
goto v_resetjp_33_;
}
else
{
lean_dec(v_snd_20_);
v___x_34_ = lean_box(0);
v_isShared_35_ = v_isSharedCheck_50_;
goto v_resetjp_33_;
}
v_resetjp_33_:
{
lean_object* v_a_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_41_; 
v_a_36_ = lean_array_uget_borrowed(v_as_13_, v_i_15_);
v___x_37_ = lean_array_fget(v_array_25_, v_start_26_);
v___x_38_ = lean_unsigned_to_nat(1u);
v___x_39_ = lean_nat_add(v_start_26_, v___x_38_);
lean_dec(v_start_26_);
if (v_isShared_35_ == 0)
{
lean_ctor_set(v___x_34_, 1, v___x_39_);
v___x_41_ = v___x_34_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_49_; 
v_reuseFailAlloc_49_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_49_, 0, v_array_25_);
lean_ctor_set(v_reuseFailAlloc_49_, 1, v___x_39_);
lean_ctor_set(v_reuseFailAlloc_49_, 2, v_stop_27_);
v___x_41_ = v_reuseFailAlloc_49_;
goto v_reusejp_40_;
}
v_reusejp_40_:
{
lean_object* v___x_42_; lean_object* v___x_44_; 
lean_inc(v_a_36_);
v___x_42_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1___redArg(v_fst_21_, v_a_36_, v___x_37_);
if (v_isShared_24_ == 0)
{
lean_ctor_set(v___x_23_, 1, v___x_41_);
lean_ctor_set(v___x_23_, 0, v___x_42_);
v___x_44_ = v___x_23_;
goto v_reusejp_43_;
}
else
{
lean_object* v_reuseFailAlloc_48_; 
v_reuseFailAlloc_48_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_48_, 0, v___x_42_);
lean_ctor_set(v_reuseFailAlloc_48_, 1, v___x_41_);
v___x_44_ = v_reuseFailAlloc_48_;
goto v_reusejp_43_;
}
v_reusejp_43_:
{
size_t v___x_45_; size_t v___x_46_; 
v___x_45_ = ((size_t)1ULL);
v___x_46_ = lean_usize_add(v_i_15_, v___x_45_);
v_i_15_ = v___x_46_;
v_b_16_ = v___x_44_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00replayFromImports_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_13_ = stack[0].m_obj;
size_t v_sz_14_ = stack[1].m_num;
size_t v_i_15_ = stack[2].m_num;
lean_object* v_b_16_ = stack[3].m_obj;
lean_object* v_res_55_;
v_res_55_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00replayFromImports_spec__0(v_as_13_, v_sz_14_, v_i_15_, v_b_16_);
stack->m_obj
 = v_res_55_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00replayFromImports_spec__0___boxed(lean_object* v_as_56_, lean_object* v_sz_57_, lean_object* v_i_58_, lean_object* v_b_59_, lean_object* v___y_60_){
_start:
{
size_t v_sz_boxed_61_; size_t v_i_boxed_62_; lean_object* v_res_63_; 
v_sz_boxed_61_ = lean_unbox_usize(v_sz_57_);
lean_dec(v_sz_57_);
v_i_boxed_62_ = lean_unbox_usize(v_i_58_);
lean_dec(v_i_58_);
v_res_63_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00replayFromImports_spec__0(v_as_56_, v_sz_boxed_61_, v_i_boxed_62_, v_b_59_);
lean_dec_ref(v_as_56_);
return v_res_63_;
}
}
static lean_object* _init_l_replayFromImports___closed__0(void){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_64_ = lean_box(0);
v___x_65_ = lean_unsigned_to_nat(16u);
v___x_66_ = lean_mk_array(v___x_65_, v___x_64_);
return v___x_66_;
}
}
static uint8_t _init_l_replayFromImports___closed__1(void){
_start:
{
uint8_t v___x_67_; uint8_t v___x_68_; 
v___x_67_ = 2;
v___x_68_ = l_Lean_instOrdOLeanLevel_ord(v___x_67_, v___x_67_);
return v___x_68_;
}
}
lean_object* l_replayFromImports(lean_object* v_module_75_){
_start:
{
lean_object* v___x_77_; 
lean_inc(v_module_75_);
v___x_77_ = l_Lean_findOLean(v_module_75_);
if (lean_obj_tag(v___x_77_) == 0)
{
lean_object* v_a_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_203_; 
v_a_78_ = lean_ctor_get(v___x_77_, 0);
v_isSharedCheck_203_ = !lean_is_exclusive(v___x_77_);
if (v_isSharedCheck_203_ == 0)
{
v___x_80_ = v___x_77_;
v_isShared_81_ = v_isSharedCheck_203_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_a_78_);
lean_dec(v___x_77_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_203_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
uint8_t v___x_82_; uint8_t v___y_84_; lean_object* v___y_85_; lean_object* v___y_86_; lean_object* v___y_87_; lean_object* v___y_88_; uint8_t v___y_89_; lean_object* v___y_90_; uint8_t v___y_91_; lean_object* v_fnames_151_; 
v___x_82_ = l_System_FilePath_pathExists(v_a_78_);
if (v___x_82_ == 0)
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; uint8_t v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_190_; 
v___x_179_ = ((lean_object*)(l_replayFromImports___closed__4));
v___x_180_ = lean_string_append(v___x_179_, v_a_78_);
lean_dec(v_a_78_);
v___x_181_ = ((lean_object*)(l_replayFromImports___closed__5));
v___x_182_ = lean_string_append(v___x_180_, v___x_181_);
v___x_183_ = 1;
v___x_184_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_75_, v___x_183_);
v___x_185_ = lean_string_append(v___x_182_, v___x_184_);
lean_dec_ref(v___x_184_);
v___x_186_ = ((lean_object*)(l_replayFromImports___closed__6));
v___x_187_ = lean_string_append(v___x_185_, v___x_186_);
v___x_188_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_188_, 0, v___x_187_);
if (v_isShared_81_ == 0)
{
lean_ctor_set_tag(v___x_80_, 1);
lean_ctor_set(v___x_80_, 0, v___x_188_);
v___x_190_ = v___x_80_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v___x_188_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
else
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; uint8_t v___x_195_; lean_object* v___x_196_; uint8_t v___x_197_; 
lean_del_object(v___x_80_);
lean_dec(v_module_75_);
v___x_192_ = lean_unsigned_to_nat(1u);
v___x_193_ = lean_mk_empty_array_with_capacity(v___x_192_);
lean_inc_n(v_a_78_, 2);
v___x_194_ = lean_array_push(v___x_193_, v_a_78_);
v___x_195_ = 1;
v___x_196_ = l_Lean_OLeanLevel_adjustFileName(v_a_78_, v___x_195_);
v___x_197_ = l_System_FilePath_pathExists(v___x_196_);
if (v___x_197_ == 0)
{
lean_dec_ref(v___x_196_);
lean_dec(v_a_78_);
v_fnames_151_ = v___x_194_;
goto v___jp_150_;
}
else
{
lean_object* v___x_198_; uint8_t v___x_199_; lean_object* v___x_200_; uint8_t v___x_201_; 
v___x_198_ = lean_array_push(v___x_194_, v___x_196_);
v___x_199_ = 2;
v___x_200_ = l_Lean_OLeanLevel_adjustFileName(v_a_78_, v___x_199_);
v___x_201_ = l_System_FilePath_pathExists(v___x_200_);
if (v___x_201_ == 0)
{
lean_dec_ref(v___x_200_);
v_fnames_151_ = v___x_198_;
goto v___jp_150_;
}
else
{
lean_object* v___x_202_; 
v___x_202_ = lean_array_push(v___x_198_, v___x_200_);
v_fnames_151_ = v___x_202_;
goto v___jp_150_;
}
}
}
v___jp_83_:
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_92_ = l_Lean_instInhabitedImportState_default;
v___x_93_ = lean_st_mk_ref(v___x_92_);
lean_inc(v___y_86_);
v___x_94_ = l_Lean_importModulesCore(v___y_90_, v___y_89_, v___y_86_, v___y_91_, v___y_84_, v___x_93_);
if (lean_obj_tag(v___x_94_) == 0)
{
lean_object* v___x_95_; lean_object* v___x_96_; uint32_t v___x_97_; lean_object* v___x_98_; 
lean_dec_ref_known(v___x_94_, 1);
v___x_95_ = lean_st_ref_get(v___x_93_);
lean_dec(v___x_93_);
v___x_96_ = l_Lean_Options_empty;
v___x_97_ = 0;
v___x_98_ = l_Lean_finalizeImport(v___x_95_, v___y_90_, v___x_96_, v___x_97_, v___y_84_, v___y_84_, v___y_89_, v___x_82_, v___y_84_);
lean_dec(v___x_95_);
if (lean_obj_tag(v___x_98_) == 0)
{
lean_object* v_a_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v_fst_103_; lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_140_; 
v_a_99_ = lean_ctor_get(v___x_98_, 0);
lean_inc(v_a_99_);
lean_dec_ref_known(v___x_98_, 1);
v___x_100_ = lean_unsigned_to_nat(1u);
v___x_101_ = lean_nat_sub(v___y_87_, v___x_100_);
lean_dec(v___y_87_);
v___x_102_ = lean_array_fget(v___y_85_, v___x_101_);
lean_dec(v___x_101_);
lean_dec_ref(v___y_85_);
v_fst_103_ = lean_ctor_get(v___x_102_, 0);
v_isSharedCheck_140_ = !lean_is_exclusive(v___x_102_);
if (v_isSharedCheck_140_ == 0)
{
lean_object* v_unused_141_; 
v_unused_141_ = lean_ctor_get(v___x_102_, 1);
lean_dec(v_unused_141_);
v___x_105_ = v___x_102_;
v_isShared_106_ = v_isSharedCheck_140_;
goto v_resetjp_104_;
}
else
{
lean_inc(v_fst_103_);
lean_dec(v___x_102_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_140_;
goto v_resetjp_104_;
}
v_resetjp_104_:
{
lean_object* v_constNames_107_; lean_object* v_constants_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_114_; 
v_constNames_107_ = lean_ctor_get(v_fst_103_, 1);
lean_inc_ref(v_constNames_107_);
v_constants_108_ = lean_ctor_get(v_fst_103_, 2);
lean_inc_ref(v_constants_108_);
lean_dec(v_fst_103_);
v___x_109_ = lean_obj_once(&l_replayFromImports___closed__0, &l_replayFromImports___closed__0_once, _init_l_replayFromImports___closed__0);
lean_inc(v___y_88_);
v___x_110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_110_, 0, v___y_88_);
lean_ctor_set(v___x_110_, 1, v___x_109_);
v___x_111_ = lean_array_get_size(v_constants_108_);
v___x_112_ = l_Array_toSubarray___redArg(v_constants_108_, v___y_88_, v___x_111_);
if (v_isShared_106_ == 0)
{
lean_ctor_set(v___x_105_, 1, v___x_112_);
lean_ctor_set(v___x_105_, 0, v___x_110_);
v___x_114_ = v___x_105_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v___x_110_);
lean_ctor_set(v_reuseFailAlloc_139_, 1, v___x_112_);
v___x_114_ = v_reuseFailAlloc_139_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
size_t v_sz_115_; size_t v___x_116_; lean_object* v___x_117_; 
v_sz_115_ = lean_array_size(v_constNames_107_);
v___x_116_ = ((size_t)0ULL);
v___x_117_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00replayFromImports_spec__0(v_constNames_107_, v_sz_115_, v___x_116_, v___x_114_);
lean_dec_ref(v_constNames_107_);
if (lean_obj_tag(v___x_117_) == 0)
{
lean_object* v_a_118_; lean_object* v_fst_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v_a_118_ = lean_ctor_get(v___x_117_, 0);
lean_inc(v_a_118_);
lean_dec_ref_known(v___x_117_, 1);
v_fst_119_ = lean_ctor_get(v_a_118_, 0);
lean_inc(v_fst_119_);
lean_dec(v_a_118_);
lean_inc(v_a_99_);
v___x_120_ = lean_elab_environment_to_kernel_env(v_a_99_);
v___x_121_ = l_Lean_Kernel_Environment_replay(v_fst_119_, v___x_120_);
lean_dec(v_fst_119_);
if (lean_obj_tag(v___x_121_) == 0)
{
lean_object* v___x_122_; 
lean_dec_ref_known(v___x_121_, 1);
v___x_122_ = lean_environment_free_regions(v_a_99_);
return v___x_122_;
}
else
{
lean_object* v_a_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_130_; 
lean_dec(v_a_99_);
v_a_123_ = lean_ctor_get(v___x_121_, 0);
v_isSharedCheck_130_ = !lean_is_exclusive(v___x_121_);
if (v_isSharedCheck_130_ == 0)
{
v___x_125_ = v___x_121_;
v_isShared_126_ = v_isSharedCheck_130_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_a_123_);
lean_dec(v___x_121_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_130_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_128_; 
if (v_isShared_126_ == 0)
{
v___x_128_ = v___x_125_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v_a_123_);
v___x_128_ = v_reuseFailAlloc_129_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
return v___x_128_;
}
}
}
}
else
{
lean_object* v_a_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_138_; 
lean_dec(v_a_99_);
v_a_131_ = lean_ctor_get(v___x_117_, 0);
v_isSharedCheck_138_ = !lean_is_exclusive(v___x_117_);
if (v_isSharedCheck_138_ == 0)
{
v___x_133_ = v___x_117_;
v_isShared_134_ = v_isSharedCheck_138_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_a_131_);
lean_dec(v___x_117_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_138_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v___x_136_; 
if (v_isShared_134_ == 0)
{
v___x_136_ = v___x_133_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v_a_131_);
v___x_136_ = v_reuseFailAlloc_137_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
return v___x_136_;
}
}
}
}
}
}
else
{
lean_object* v_a_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_149_; 
lean_dec(v___y_88_);
lean_dec(v___y_87_);
lean_dec_ref(v___y_85_);
v_a_142_ = lean_ctor_get(v___x_98_, 0);
v_isSharedCheck_149_ = !lean_is_exclusive(v___x_98_);
if (v_isSharedCheck_149_ == 0)
{
v___x_144_ = v___x_98_;
v_isShared_145_ = v_isSharedCheck_149_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_a_142_);
lean_dec(v___x_98_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_149_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
lean_object* v___x_147_; 
if (v_isShared_145_ == 0)
{
v___x_147_ = v___x_144_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v_a_142_);
v___x_147_ = v_reuseFailAlloc_148_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
return v___x_147_;
}
}
}
}
else
{
lean_dec(v___x_93_);
lean_dec_ref(v___y_90_);
lean_dec(v___y_88_);
lean_dec(v___y_87_);
lean_dec_ref(v___y_85_);
return v___x_94_;
}
}
v___jp_150_:
{
lean_object* v___x_152_; 
v___x_152_ = l_Lean_readModuleDataParts(v_fnames_151_);
lean_dec_ref(v_fnames_151_);
if (lean_obj_tag(v___x_152_) == 0)
{
lean_object* v_a_153_; lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_170_; 
v_a_153_ = lean_ctor_get(v___x_152_, 0);
v_isSharedCheck_170_ = !lean_is_exclusive(v___x_152_);
if (v_isSharedCheck_170_ == 0)
{
v___x_155_ = v___x_152_;
v_isShared_156_ = v_isSharedCheck_170_;
goto v_resetjp_154_;
}
else
{
lean_inc(v_a_153_);
lean_dec(v___x_152_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_170_;
goto v_resetjp_154_;
}
v_resetjp_154_:
{
lean_object* v___x_157_; lean_object* v___x_158_; uint8_t v___x_159_; 
v___x_157_ = lean_array_get_size(v_a_153_);
v___x_158_ = lean_unsigned_to_nat(0u);
v___x_159_ = lean_nat_dec_eq(v___x_157_, v___x_158_);
if (v___x_159_ == 0)
{
lean_object* v___x_160_; lean_object* v_fst_161_; lean_object* v_imports_162_; uint8_t v___x_163_; lean_object* v___x_164_; uint8_t v___x_165_; 
lean_del_object(v___x_155_);
v___x_160_ = lean_array_fget_borrowed(v_a_153_, v___x_158_);
v_fst_161_ = lean_ctor_get(v___x_160_, 0);
v_imports_162_ = lean_ctor_get(v_fst_161_, 0);
lean_inc_ref(v_imports_162_);
v___x_163_ = 2;
v___x_164_ = lean_box(1);
v___x_165_ = lean_uint8_once(&l_replayFromImports___closed__1, &l_replayFromImports___closed__1_once, _init_l_replayFromImports___closed__1);
if (v___x_165_ == 0)
{
v___y_84_ = v___x_159_;
v___y_85_ = v_a_153_;
v___y_86_ = v___x_164_;
v___y_87_ = v___x_157_;
v___y_88_ = v___x_158_;
v___y_89_ = v___x_163_;
v___y_90_ = v_imports_162_;
v___y_91_ = v___x_82_;
goto v___jp_83_;
}
else
{
v___y_84_ = v___x_159_;
v___y_85_ = v_a_153_;
v___y_86_ = v___x_164_;
v___y_87_ = v___x_157_;
v___y_88_ = v___x_158_;
v___y_89_ = v___x_163_;
v___y_90_ = v_imports_162_;
v___y_91_ = v___x_159_;
goto v___jp_83_;
}
}
else
{
lean_object* v___x_166_; lean_object* v___x_168_; 
lean_dec(v_a_153_);
v___x_166_ = ((lean_object*)(l_replayFromImports___closed__3));
if (v_isShared_156_ == 0)
{
lean_ctor_set_tag(v___x_155_, 1);
lean_ctor_set(v___x_155_, 0, v___x_166_);
v___x_168_ = v___x_155_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v___x_166_);
v___x_168_ = v_reuseFailAlloc_169_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
return v___x_168_;
}
}
}
}
else
{
lean_object* v_a_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_178_; 
v_a_171_ = lean_ctor_get(v___x_152_, 0);
v_isSharedCheck_178_ = !lean_is_exclusive(v___x_152_);
if (v_isSharedCheck_178_ == 0)
{
v___x_173_ = v___x_152_;
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_a_171_);
lean_dec(v___x_152_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___x_176_; 
if (v_isShared_174_ == 0)
{
v___x_176_ = v___x_173_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v_a_171_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
}
}
}
}
}
}
else
{
lean_object* v_a_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_211_; 
lean_dec(v_module_75_);
v_a_204_ = lean_ctor_get(v___x_77_, 0);
v_isSharedCheck_211_ = !lean_is_exclusive(v___x_77_);
if (v_isSharedCheck_211_ == 0)
{
v___x_206_ = v___x_77_;
v_isShared_207_ = v_isSharedCheck_211_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_a_204_);
lean_dec(v___x_77_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_211_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v___x_209_; 
if (v_isShared_207_ == 0)
{
v___x_209_ = v___x_206_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v_a_204_);
v___x_209_ = v_reuseFailAlloc_210_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
return v___x_209_;
}
}
}
}
}
LEAN_EXPORT void l_replayFromImports_0interp(lean_interpreter_value* stack)
{
lean_object* v_module_75_ = stack[0].m_obj;
lean_object* v_res_212_;
v_res_212_ = l_replayFromImports(v_module_75_);
stack->m_obj
 = v_res_212_;
}
LEAN_EXPORT lean_object* l_replayFromImports___boxed(lean_object* v_module_213_, lean_object* v_a_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_replayFromImports(v_module_213_);
return v_res_215_;
}
}
lean_object* l_replayFromFresh___lam__0(lean_object* v_env_216_){
_start:
{
uint32_t v___x_218_; lean_object* v___x_219_; 
v___x_218_ = 0;
v___x_219_ = l_Lean_mkEmptyEnvironment(v___x_218_);
if (lean_obj_tag(v___x_219_) == 0)
{
lean_object* v_a_220_; lean_object* v___x_221_; lean_object* v_map_u2081_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
v_a_220_ = lean_ctor_get(v___x_219_, 0);
lean_inc(v_a_220_);
lean_dec_ref_known(v___x_219_, 1);
v___x_221_ = l_Lean_Environment_constants(v_env_216_);
v_map_u2081_222_ = lean_ctor_get(v___x_221_, 0);
lean_inc_ref(v_map_u2081_222_);
lean_dec_ref(v___x_221_);
v___x_223_ = lean_elab_environment_to_kernel_env(v_a_220_);
v___x_224_ = lean_box(0);
v___x_225_ = l_Lean_Kernel_Environment_replay(v_map_u2081_222_, v___x_223_);
lean_dec_ref(v_map_u2081_222_);
if (lean_obj_tag(v___x_225_) == 0)
{
lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_232_; 
v_isSharedCheck_232_ = !lean_is_exclusive(v___x_225_);
if (v_isSharedCheck_232_ == 0)
{
lean_object* v_unused_233_; 
v_unused_233_ = lean_ctor_get(v___x_225_, 0);
lean_dec(v_unused_233_);
v___x_227_ = v___x_225_;
v_isShared_228_ = v_isSharedCheck_232_;
goto v_resetjp_226_;
}
else
{
lean_dec(v___x_225_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_232_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___x_230_; 
if (v_isShared_228_ == 0)
{
lean_ctor_set(v___x_227_, 0, v___x_224_);
v___x_230_ = v___x_227_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v___x_224_);
v___x_230_ = v_reuseFailAlloc_231_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
return v___x_230_;
}
}
}
else
{
lean_object* v_a_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_241_; 
v_a_234_ = lean_ctor_get(v___x_225_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v___x_225_);
if (v_isSharedCheck_241_ == 0)
{
v___x_236_ = v___x_225_;
v_isShared_237_ = v_isSharedCheck_241_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_a_234_);
lean_dec(v___x_225_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_241_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v___x_239_; 
if (v_isShared_237_ == 0)
{
v___x_239_ = v___x_236_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_a_234_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
}
}
else
{
lean_object* v_a_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_249_; 
lean_dec_ref(v_env_216_);
v_a_242_ = lean_ctor_get(v___x_219_, 0);
v_isSharedCheck_249_ = !lean_is_exclusive(v___x_219_);
if (v_isSharedCheck_249_ == 0)
{
v___x_244_ = v___x_219_;
v_isShared_245_ = v_isSharedCheck_249_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_a_242_);
lean_dec(v___x_219_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_249_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v___x_247_; 
if (v_isShared_245_ == 0)
{
v___x_247_ = v___x_244_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v_a_242_);
v___x_247_ = v_reuseFailAlloc_248_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
return v___x_247_;
}
}
}
}
}
LEAN_EXPORT void l_replayFromFresh___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_216_ = stack[0].m_obj;
lean_object* v_res_250_;
v_res_250_ = l_replayFromFresh___lam__0(v_env_216_);
stack->m_obj
 = v_res_250_;
}
LEAN_EXPORT lean_object* l_replayFromFresh___lam__0___boxed(lean_object* v_env_251_, lean_object* v___y_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_replayFromFresh___lam__0(v_env_251_);
return v_res_253_;
}
}
lean_object* l_replayFromFresh(lean_object* v_module_255_){
_start:
{
lean_object* v___f_257_; uint8_t v___x_258_; uint8_t v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; uint32_t v___x_265_; lean_object* v___x_266_; 
v___f_257_ = ((lean_object*)(l_replayFromFresh___closed__0));
v___x_258_ = 0;
v___x_259_ = 1;
v___x_260_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_260_, 0, v_module_255_);
lean_ctor_set_uint8(v___x_260_, sizeof(void*)*1, v___x_258_);
lean_ctor_set_uint8(v___x_260_, sizeof(void*)*1 + 1, v___x_259_);
lean_ctor_set_uint8(v___x_260_, sizeof(void*)*1 + 2, v___x_258_);
v___x_261_ = lean_unsigned_to_nat(1u);
v___x_262_ = lean_mk_empty_array_with_capacity(v___x_261_);
v___x_263_ = lean_array_push(v___x_262_, v___x_260_);
v___x_264_ = l_Lean_Options_empty;
v___x_265_ = 0;
v___x_266_ = l_Lean_withImportModules___redArg(v___x_263_, v___x_264_, v___f_257_, v___x_265_);
return v___x_266_;
}
}
LEAN_EXPORT void l_replayFromFresh_0interp(lean_interpreter_value* stack)
{
lean_object* v_module_255_ = stack[0].m_obj;
lean_object* v_res_267_;
v_res_267_ = l_replayFromFresh(v_module_255_);
stack->m_obj
 = v_res_267_;
}
LEAN_EXPORT lean_object* l_replayFromFresh___boxed(lean_object* v_module_268_, lean_object* v_a_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_replayFromFresh(v_module_268_);
return v_res_270_;
}
}
lean_object* l_getCurrentModule(){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_273_ = ((lean_object*)(l_getCurrentModule___closed__0));
v___x_274_ = l_Lake_Manifest_load_x3f(v___x_273_);
if (lean_obj_tag(v___x_274_) == 0)
{
lean_object* v_a_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_289_; 
v_a_275_ = lean_ctor_get(v___x_274_, 0);
v_isSharedCheck_289_ = !lean_is_exclusive(v___x_274_);
if (v_isSharedCheck_289_ == 0)
{
v___x_277_ = v___x_274_;
v_isShared_278_ = v_isSharedCheck_289_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_a_275_);
lean_dec(v___x_274_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_289_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
if (lean_obj_tag(v_a_275_) == 0)
{
lean_object* v___x_279_; lean_object* v___x_281_; 
v___x_279_ = lean_box(0);
if (v_isShared_278_ == 0)
{
lean_ctor_set(v___x_277_, 0, v___x_279_);
v___x_281_ = v___x_277_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v___x_279_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
else
{
lean_object* v_val_283_; lean_object* v_name_284_; lean_object* v___x_285_; lean_object* v___x_287_; 
v_val_283_ = lean_ctor_get(v_a_275_, 0);
lean_inc(v_val_283_);
lean_dec_ref_known(v_a_275_, 1);
v_name_284_ = lean_ctor_get(v_val_283_, 0);
lean_inc(v_name_284_);
lean_dec(v_val_283_);
v___x_285_ = l_Lean_Name_capitalize(v_name_284_);
if (v_isShared_278_ == 0)
{
lean_ctor_set(v___x_277_, 0, v___x_285_);
v___x_287_ = v___x_277_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v___x_285_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
}
}
}
}
else
{
lean_object* v_a_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_297_; 
v_a_290_ = lean_ctor_get(v___x_274_, 0);
v_isSharedCheck_297_ = !lean_is_exclusive(v___x_274_);
if (v_isSharedCheck_297_ == 0)
{
v___x_292_ = v___x_274_;
v_isShared_293_ = v_isSharedCheck_297_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_a_290_);
lean_dec(v___x_274_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_297_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___x_295_; 
if (v_isShared_293_ == 0)
{
v___x_295_ = v___x_292_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v_a_290_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
}
}
}
LEAN_EXPORT void l_getCurrentModule_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_298_;
v_res_298_ = l_getCurrentModule();
stack->m_obj
 = v_res_298_;
}
LEAN_EXPORT lean_object* l_getCurrentModule___boxed(lean_object* v_a_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_getCurrentModule();
return v_res_300_;
}
}
lean_object* l_List_forIn_x27_loop___at___00checkExport_spec__1___redArg(lean_object* v___x_303_, lean_object* v_a_304_, lean_object* v_as_x27_305_, lean_object* v_b_306_){
_start:
{
if (lean_obj_tag(v_as_x27_305_) == 0)
{
lean_object* v___x_308_; 
lean_dec_ref(v_a_304_);
v___x_308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_308_, 0, v_b_306_);
return v___x_308_;
}
else
{
lean_object* v_head_309_; lean_object* v_tail_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v_head_309_ = lean_ctor_get(v_as_x27_305_, 0);
v_tail_310_ = lean_ctor_get(v_as_x27_305_, 1);
v___x_311_ = lean_box(0);
v___x_312_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Lemmas______macroRules__Std__DTreeMap__Internal__Impl__tacticSimp__to__model_x5b___x5dUsing____1_spec__1___redArg(v___x_303_, v_head_309_);
if (lean_obj_tag(v___x_312_) == 1)
{
lean_object* v_val_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_343_; 
v_val_313_ = lean_ctor_get(v___x_312_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v___x_312_);
if (v_isSharedCheck_343_ == 0)
{
v___x_315_ = v___x_312_;
v_isShared_316_ = v_isSharedCheck_343_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_val_313_);
lean_dec(v___x_312_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_343_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_317_; 
lean_inc(v_head_309_);
lean_inc_ref(v_a_304_);
v___x_317_ = lean_environment_find(v_a_304_, v_head_309_);
if (lean_obj_tag(v___x_317_) == 1)
{
lean_object* v_val_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_334_; 
v_val_318_ = lean_ctor_get(v___x_317_, 0);
v_isSharedCheck_334_ = !lean_is_exclusive(v___x_317_);
if (v_isSharedCheck_334_ == 0)
{
v___x_320_ = v___x_317_;
v_isShared_321_ = v_isSharedCheck_334_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_val_318_);
lean_dec(v___x_317_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_334_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
uint8_t v___x_322_; 
v___x_322_ = l_Lean_instBEqConstantInfo_beq(v_val_313_, v_val_318_);
lean_dec(v_val_318_);
lean_dec(v_val_313_);
if (v___x_322_ == 0)
{
uint8_t v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_328_; 
lean_dec_ref(v_a_304_);
v___x_323_ = 1;
v___x_324_ = ((lean_object*)(l_List_forIn_x27_loop___at___00checkExport_spec__1___redArg___closed__0));
lean_inc(v_head_309_);
v___x_325_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_309_, v___x_323_);
v___x_326_ = lean_string_append(v___x_324_, v___x_325_);
lean_dec_ref(v___x_325_);
if (v_isShared_321_ == 0)
{
lean_ctor_set_tag(v___x_320_, 18);
lean_ctor_set(v___x_320_, 0, v___x_326_);
v___x_328_ = v___x_320_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v___x_326_);
v___x_328_ = v_reuseFailAlloc_332_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
lean_object* v___x_330_; 
if (v_isShared_316_ == 0)
{
lean_ctor_set(v___x_315_, 0, v___x_328_);
v___x_330_ = v___x_315_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v___x_328_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
}
else
{
lean_del_object(v___x_320_);
lean_del_object(v___x_315_);
v_as_x27_305_ = v_tail_310_;
v_b_306_ = v___x_311_;
goto _start;
}
}
}
else
{
lean_object* v___x_335_; uint8_t v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_340_; 
lean_dec(v___x_317_);
lean_dec(v_val_313_);
lean_dec_ref(v_a_304_);
v___x_335_ = ((lean_object*)(l_List_forIn_x27_loop___at___00checkExport_spec__1___redArg___closed__1));
v___x_336_ = 1;
lean_inc(v_head_309_);
v___x_337_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_309_, v___x_336_);
v___x_338_ = lean_string_append(v___x_335_, v___x_337_);
lean_dec_ref(v___x_337_);
if (v_isShared_316_ == 0)
{
lean_ctor_set_tag(v___x_315_, 18);
lean_ctor_set(v___x_315_, 0, v___x_338_);
v___x_340_ = v___x_315_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v___x_338_);
v___x_340_ = v_reuseFailAlloc_342_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
lean_object* v___x_341_; 
v___x_341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_341_, 0, v___x_340_);
return v___x_341_;
}
}
}
}
else
{
lean_dec(v___x_312_);
v_as_x27_305_ = v_tail_310_;
v_b_306_ = v___x_311_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00checkExport_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_303_ = stack[0].m_obj;
lean_object* v_a_304_ = stack[1].m_obj;
lean_object* v_as_x27_305_ = stack[2].m_obj;
lean_object* v_b_306_ = stack[3].m_obj;
lean_object* v_res_345_;
v_res_345_ = l_List_forIn_x27_loop___at___00checkExport_spec__1___redArg(v___x_303_, v_a_304_, v_as_x27_305_, v_b_306_);
stack->m_obj
 = v_res_345_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkExport_spec__1___redArg___boxed(lean_object* v___x_346_, lean_object* v_a_347_, lean_object* v_as_x27_348_, lean_object* v_b_349_, lean_object* v___y_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_List_forIn_x27_loop___at___00checkExport_spec__1___redArg(v___x_346_, v_a_347_, v_as_x27_348_, v_b_349_);
lean_dec(v_as_x27_348_);
lean_dec_ref(v___x_346_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00checkExport_spec__0(lean_object* v_x_352_, lean_object* v_x_353_){
_start:
{
if (lean_obj_tag(v_x_353_) == 0)
{
return v_x_352_;
}
else
{
lean_object* v_head_354_; lean_object* v_tail_355_; lean_object* v___x_356_; 
v_head_354_ = lean_ctor_get(v_x_353_, 0);
v_tail_355_ = lean_ctor_get(v_x_353_, 1);
v___x_356_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg(v_x_352_, v_head_354_);
v_x_352_ = v___x_356_;
v_x_353_ = v_tail_355_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00checkExport_spec__0___boxed(lean_object* v_x_358_, lean_object* v_x_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l_List_foldl___at___00checkExport_spec__0(v_x_358_, v_x_359_);
lean_dec(v_x_359_);
return v_res_360_;
}
}
static lean_object* _init_l_checkExport___boxed__const__1(void){
_start:
{
uint32_t v___x_392_; lean_object* v___x_393_; 
v___x_392_ = 1;
v___x_393_ = lean_box_uint32(v___x_392_);
return v___x_393_;
}
}
static lean_object* _init_l_checkExport___boxed__const__2(void){
_start:
{
uint32_t v___x_394_; lean_object* v___x_395_; 
v___x_394_ = 0;
v___x_395_ = lean_box_uint32(v___x_394_);
return v___x_395_;
}
}
lean_object* l_checkExport(lean_object* v_args_396_, uint8_t v_silent_397_){
_start:
{
lean_object* v_a_406_; 
if (lean_obj_tag(v_args_396_) == 1)
{
lean_object* v_tail_428_; 
v_tail_428_ = lean_ctor_get(v_args_396_, 1);
if (lean_obj_tag(v_tail_428_) == 0)
{
lean_object* v_head_429_; uint8_t v___x_430_; lean_object* v___x_431_; 
v_head_429_ = lean_ctor_get(v_args_396_, 0);
v___x_430_ = 0;
v___x_431_ = lean_io_prim_handle_mk(v_head_429_, v___x_430_);
if (lean_obj_tag(v___x_431_) == 0)
{
lean_object* v_a_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
v_a_432_ = lean_ctor_get(v___x_431_, 0);
lean_inc(v_a_432_);
lean_dec_ref_known(v___x_431_, 1);
v___x_433_ = lean_stream_of_handle(v_a_432_);
v___x_434_ = l_LeanExport_parseStream(v___x_433_);
if (lean_obj_tag(v___x_434_) == 0)
{
lean_object* v_a_435_; uint32_t v___x_436_; lean_object* v___x_437_; 
v_a_435_ = lean_ctor_get(v___x_434_, 0);
lean_inc(v_a_435_);
lean_dec_ref_known(v___x_434_, 1);
v___x_436_ = 0;
v___x_437_ = l_Lean_mkEmptyEnvironment(v___x_436_);
if (lean_obj_tag(v___x_437_) == 0)
{
lean_object* v_a_438_; lean_object* v_constMap_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v_a_438_ = lean_ctor_get(v___x_437_, 0);
lean_inc(v_a_438_);
lean_dec_ref_known(v___x_437_, 1);
v_constMap_439_ = lean_ctor_get(v_a_435_, 0);
lean_inc_ref_n(v_constMap_439_, 2);
lean_dec(v_a_435_);
v___x_440_ = lean_elab_environment_to_kernel_env(v_a_438_);
v___x_441_ = ((lean_object*)(l_checkExport___closed__11));
v___x_442_ = l_List_foldl___at___00checkExport_spec__0(v_constMap_439_, v___x_441_);
v___x_443_ = l_Lean_Kernel_Environment_replay(v___x_442_, v___x_440_);
lean_dec_ref(v___x_442_);
if (lean_obj_tag(v___x_443_) == 0)
{
lean_object* v_a_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v_a_444_ = lean_ctor_get(v___x_443_, 0);
lean_inc(v_a_444_);
lean_dec_ref_known(v___x_443_, 1);
v___x_445_ = ((lean_object*)(l_checkExport___closed__12));
v___x_446_ = l_println(v___x_445_, v_silent_397_);
if (lean_obj_tag(v___x_446_) == 0)
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
lean_dec_ref_known(v___x_446_, 1);
v___x_447_ = ((lean_object*)(l_checkExport___closed__14));
v___x_448_ = lean_box(0);
v___x_449_ = l_List_forIn_x27_loop___at___00checkExport_spec__1___redArg(v_constMap_439_, v_a_444_, v___x_447_, v___x_448_);
lean_dec_ref(v_constMap_439_);
if (lean_obj_tag(v___x_449_) == 0)
{
lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_457_; 
v_isSharedCheck_457_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_457_ == 0)
{
lean_object* v_unused_458_; 
v_unused_458_ = lean_ctor_get(v___x_449_, 0);
lean_dec(v_unused_458_);
v___x_451_ = v___x_449_;
v_isShared_452_ = v_isSharedCheck_457_;
goto v_resetjp_450_;
}
else
{
lean_dec(v___x_449_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_457_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_453_; lean_object* v___x_455_; 
v___x_453_ = l_checkExport___boxed__const__2;
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 0, v___x_453_);
v___x_455_ = v___x_451_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v___x_453_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
}
else
{
lean_object* v_a_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v_a_459_ = lean_ctor_get(v___x_449_, 0);
lean_inc(v_a_459_);
lean_dec_ref_known(v___x_449_, 1);
v___x_460_ = ((lean_object*)(l_checkExport___closed__15));
v___x_461_ = lean_io_error_to_string(v_a_459_);
v___x_462_ = lean_string_append(v___x_460_, v___x_461_);
lean_dec_ref(v___x_461_);
v___x_463_ = l_println(v___x_462_, v_silent_397_);
if (lean_obj_tag(v___x_463_) == 0)
{
lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_471_; 
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_463_);
if (v_isSharedCheck_471_ == 0)
{
lean_object* v_unused_472_; 
v_unused_472_ = lean_ctor_get(v___x_463_, 0);
lean_dec(v_unused_472_);
v___x_465_ = v___x_463_;
v_isShared_466_ = v_isSharedCheck_471_;
goto v_resetjp_464_;
}
else
{
lean_dec(v___x_463_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_471_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_467_; lean_object* v___x_469_; 
v___x_467_ = l_checkExport___boxed__const__1;
if (v_isShared_466_ == 0)
{
lean_ctor_set(v___x_465_, 0, v___x_467_);
v___x_469_ = v___x_465_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v___x_467_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
}
else
{
lean_object* v_a_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_480_; 
v_a_473_ = lean_ctor_get(v___x_463_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v___x_463_);
if (v_isSharedCheck_480_ == 0)
{
v___x_475_ = v___x_463_;
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_a_473_);
lean_dec(v___x_463_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_478_; 
if (v_isShared_476_ == 0)
{
v___x_478_ = v___x_475_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_a_473_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
}
}
}
else
{
lean_object* v_a_481_; 
lean_dec(v_a_444_);
lean_dec_ref(v_constMap_439_);
v_a_481_ = lean_ctor_get(v___x_446_, 0);
lean_inc(v_a_481_);
lean_dec_ref_known(v___x_446_, 1);
v_a_406_ = v_a_481_;
goto v___jp_405_;
}
}
else
{
lean_object* v_a_482_; 
lean_dec_ref(v_constMap_439_);
v_a_482_ = lean_ctor_get(v___x_443_, 0);
lean_inc(v_a_482_);
lean_dec_ref_known(v___x_443_, 1);
v_a_406_ = v_a_482_;
goto v___jp_405_;
}
}
else
{
lean_object* v_a_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_490_; 
lean_dec(v_a_435_);
v_a_483_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_490_ == 0)
{
v___x_485_ = v___x_437_;
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_a_483_);
lean_dec(v___x_437_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_488_; 
if (v_isShared_486_ == 0)
{
v___x_488_ = v___x_485_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v_a_483_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
}
}
else
{
lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_498_; 
v_a_491_ = lean_ctor_get(v___x_434_, 0);
v_isSharedCheck_498_ = !lean_is_exclusive(v___x_434_);
if (v_isSharedCheck_498_ == 0)
{
v___x_493_ = v___x_434_;
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_a_491_);
lean_dec(v___x_434_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_496_; 
if (v_isShared_494_ == 0)
{
v___x_496_ = v___x_493_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_a_491_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
}
else
{
lean_object* v_a_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_506_; 
v_a_499_ = lean_ctor_get(v___x_431_, 0);
v_isSharedCheck_506_ = !lean_is_exclusive(v___x_431_);
if (v_isSharedCheck_506_ == 0)
{
v___x_501_ = v___x_431_;
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_a_499_);
lean_dec(v___x_431_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_504_; 
if (v_isShared_502_ == 0)
{
v___x_504_ = v___x_501_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v_a_499_);
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
else
{
goto v___jp_399_;
}
}
else
{
goto v___jp_399_;
}
v___jp_399_:
{
lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_400_ = ((lean_object*)(l_checkExport___closed__0));
v___x_401_ = l_List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1(v_args_396_);
v___x_402_ = lean_string_append(v___x_400_, v___x_401_);
lean_dec_ref(v___x_401_);
v___x_403_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_403_, 0, v___x_402_);
v___x_404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
return v___x_404_;
}
v___jp_405_:
{
lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_407_ = ((lean_object*)(l_checkExport___closed__1));
v___x_408_ = lean_io_error_to_string(v_a_406_);
v___x_409_ = lean_string_append(v___x_407_, v___x_408_);
lean_dec_ref(v___x_408_);
v___x_410_ = l_println(v___x_409_, v_silent_397_);
if (lean_obj_tag(v___x_410_) == 0)
{
lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_418_; 
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_410_);
if (v_isSharedCheck_418_ == 0)
{
lean_object* v_unused_419_; 
v_unused_419_ = lean_ctor_get(v___x_410_, 0);
lean_dec(v_unused_419_);
v___x_412_ = v___x_410_;
v_isShared_413_ = v_isSharedCheck_418_;
goto v_resetjp_411_;
}
else
{
lean_dec(v___x_410_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_418_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_414_; lean_object* v___x_416_; 
v___x_414_ = l_checkExport___boxed__const__1;
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 0, v___x_414_);
v___x_416_ = v___x_412_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v___x_414_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
else
{
lean_object* v_a_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_427_; 
v_a_420_ = lean_ctor_get(v___x_410_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v___x_410_);
if (v_isSharedCheck_427_ == 0)
{
v___x_422_ = v___x_410_;
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_a_420_);
lean_dec(v___x_410_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_425_; 
if (v_isShared_423_ == 0)
{
v___x_425_ = v___x_422_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v_a_420_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
return v___x_425_;
}
}
}
}
}
}
LEAN_EXPORT void l_checkExport_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_396_ = stack[0].m_obj;
uint8_t v_silent_397_ = stack[1].m_num;
lean_object* v_res_507_;
v_res_507_ = l_checkExport(v_args_396_, v_silent_397_);
stack->m_obj
 = v_res_507_;
}
LEAN_EXPORT lean_object* l_checkExport___boxed(lean_object* v_args_508_, lean_object* v_silent_509_, lean_object* v_a_510_){
_start:
{
uint8_t v_silent_boxed_511_; lean_object* v_res_512_; 
v_silent_boxed_511_ = lean_unbox(v_silent_509_);
v_res_512_ = l_checkExport(v_args_508_, v_silent_boxed_511_);
lean_dec(v_args_508_);
return v_res_512_;
}
}
lean_object* l_List_forIn_x27_loop___at___00checkExport_spec__1(lean_object* v___x_513_, lean_object* v_a_514_, lean_object* v_as_515_, lean_object* v_as_x27_516_, lean_object* v_b_517_, lean_object* v_a_518_){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = l_List_forIn_x27_loop___at___00checkExport_spec__1___redArg(v___x_513_, v_a_514_, v_as_x27_516_, v_b_517_);
return v___x_520_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00checkExport_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_513_ = stack[0].m_obj;
lean_object* v_a_514_ = stack[1].m_obj;
lean_object* v_as_515_ = stack[2].m_obj;
lean_object* v_as_x27_516_ = stack[3].m_obj;
lean_object* v_b_517_ = stack[4].m_obj;
lean_object* v_res_521_;
v_res_521_ = l_List_forIn_x27_loop___at___00checkExport_spec__1(v___x_513_, v_a_514_, v_as_515_, v_as_x27_516_, v_b_517_, lean_box(0));
stack->m_obj
 = v_res_521_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkExport_spec__1___boxed(lean_object* v___x_522_, lean_object* v_a_523_, lean_object* v_as_524_, lean_object* v_as_x27_525_, lean_object* v_b_526_, lean_object* v_a_527_, lean_object* v___y_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l_List_forIn_x27_loop___at___00checkExport_spec__1(v___x_522_, v_a_523_, v_as_524_, v_as_x27_525_, v_b_526_, v_a_527_);
lean_dec(v_as_x27_525_);
lean_dec(v_as_524_);
lean_dec_ref(v___x_522_);
return v_res_529_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00checkOlean_spec__3(uint8_t v_verbose_532_, uint8_t v_silent_533_, lean_object* v_as_534_, size_t v_sz_535_, size_t v_i_536_, lean_object* v_b_537_){
_start:
{
uint8_t v___x_539_; 
v___x_539_ = lean_usize_dec_lt(v_i_536_, v_sz_535_);
if (v___x_539_ == 0)
{
lean_object* v___x_540_; 
v___x_540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_540_, 0, v_b_537_);
return v___x_540_;
}
else
{
lean_object* v_a_541_; lean_object* v_fst_542_; lean_object* v_snd_543_; lean_object* v___x_544_; 
v_a_541_ = lean_array_uget_borrowed(v_as_534_, v_i_536_);
v_fst_542_ = lean_ctor_get(v_a_541_, 0);
v_snd_543_ = lean_ctor_get(v_a_541_, 1);
v___x_544_ = lean_box(0);
if (v_verbose_532_ == 0)
{
goto v___jp_545_;
}
else
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_563_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00checkOlean_spec__3___closed__1));
lean_inc(v_fst_542_);
v___x_564_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_542_, v_verbose_532_);
v___x_565_ = lean_string_append(v___x_563_, v___x_564_);
lean_dec_ref(v___x_564_);
v___x_566_ = l_println(v___x_565_, v_silent_533_);
if (lean_obj_tag(v___x_566_) == 0)
{
lean_dec_ref_known(v___x_566_, 1);
goto v___jp_545_;
}
else
{
return v___x_566_;
}
}
v___jp_545_:
{
lean_object* v___x_546_; 
lean_inc(v_snd_543_);
v___x_546_ = lean_task_get_own(v_snd_543_);
if (lean_obj_tag(v___x_546_) == 0)
{
lean_object* v_a_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v_a_547_ = lean_ctor_get(v___x_546_, 0);
lean_inc(v_a_547_);
lean_dec_ref_known(v___x_546_, 1);
v___x_548_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00checkOlean_spec__3___closed__0));
lean_inc(v_fst_542_);
v___x_549_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_542_, v___x_539_);
v___x_550_ = lean_string_append(v___x_548_, v___x_549_);
lean_dec_ref(v___x_549_);
v___x_551_ = l_IO_eprintln___at___00__private_Init_System_IO_0__IO_eprintlnAux_spec__0(v___x_550_);
if (lean_obj_tag(v___x_551_) == 0)
{
lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_558_; 
v_isSharedCheck_558_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_558_ == 0)
{
lean_object* v_unused_559_; 
v_unused_559_ = lean_ctor_get(v___x_551_, 0);
lean_dec(v_unused_559_);
v___x_553_ = v___x_551_;
v_isShared_554_ = v_isSharedCheck_558_;
goto v_resetjp_552_;
}
else
{
lean_dec(v___x_551_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_558_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v___x_556_; 
if (v_isShared_554_ == 0)
{
lean_ctor_set_tag(v___x_553_, 1);
lean_ctor_set(v___x_553_, 0, v_a_547_);
v___x_556_ = v___x_553_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v_a_547_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
}
else
{
lean_dec(v_a_547_);
return v___x_551_;
}
}
else
{
size_t v___x_560_; size_t v___x_561_; 
lean_dec(v___x_546_);
v___x_560_ = ((size_t)1ULL);
v___x_561_ = lean_usize_add(v_i_536_, v___x_560_);
v_i_536_ = v___x_561_;
v_b_537_ = v___x_544_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00checkOlean_spec__3_0interp(lean_interpreter_value* stack)
{
uint8_t v_verbose_532_ = stack[0].m_num;
uint8_t v_silent_533_ = stack[1].m_num;
lean_object* v_as_534_ = stack[2].m_obj;
size_t v_sz_535_ = stack[3].m_num;
size_t v_i_536_ = stack[4].m_num;
lean_object* v_b_537_ = stack[5].m_obj;
lean_object* v_res_567_;
v_res_567_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00checkOlean_spec__3(v_verbose_532_, v_silent_533_, v_as_534_, v_sz_535_, v_i_536_, v_b_537_);
stack->m_obj
 = v_res_567_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00checkOlean_spec__3___boxed(lean_object* v_verbose_568_, lean_object* v_silent_569_, lean_object* v_as_570_, lean_object* v_sz_571_, lean_object* v_i_572_, lean_object* v_b_573_, lean_object* v___y_574_){
_start:
{
uint8_t v_verbose_boxed_575_; uint8_t v_silent_boxed_576_; size_t v_sz_boxed_577_; size_t v_i_boxed_578_; lean_object* v_res_579_; 
v_verbose_boxed_575_ = lean_unbox(v_verbose_568_);
v_silent_boxed_576_ = lean_unbox(v_silent_569_);
v_sz_boxed_577_ = lean_unbox_usize(v_sz_571_);
lean_dec(v_sz_571_);
v_i_boxed_578_ = lean_unbox_usize(v_i_572_);
lean_dec(v_i_572_);
v_res_579_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00checkOlean_spec__3(v_verbose_boxed_575_, v_silent_boxed_576_, v_as_570_, v_sz_boxed_577_, v_i_boxed_578_, v_b_573_);
lean_dec_ref(v_as_570_);
return v_res_579_;
}
}
lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__2___redArg___lam__0(lean_object* v_head_580_){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = l_replayFromImports(v_head_580_);
if (lean_obj_tag(v___x_582_) == 0)
{
lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_590_; 
v_a_583_ = lean_ctor_get(v___x_582_, 0);
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_590_ == 0)
{
v___x_585_ = v___x_582_;
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_dec(v___x_582_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_588_; 
if (v_isShared_586_ == 0)
{
lean_ctor_set_tag(v___x_585_, 1);
v___x_588_ = v___x_585_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_a_583_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
else
{
lean_object* v_a_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_598_; 
v_a_591_ = lean_ctor_get(v___x_582_, 0);
v_isSharedCheck_598_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_598_ == 0)
{
v___x_593_ = v___x_582_;
v_isShared_594_ = v_isSharedCheck_598_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_a_591_);
lean_dec(v___x_582_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_598_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_596_; 
if (v_isShared_594_ == 0)
{
lean_ctor_set_tag(v___x_593_, 0);
v___x_596_ = v___x_593_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_a_591_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00checkOlean_spec__2___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_head_580_ = stack[0].m_obj;
lean_object* v_res_599_;
v_res_599_ = l_List_forIn_x27_loop___at___00checkOlean_spec__2___redArg___lam__0(v_head_580_);
stack->m_obj
 = v_res_599_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__2___redArg___lam__0___boxed(lean_object* v_head_600_, lean_object* v___y_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_List_forIn_x27_loop___at___00checkOlean_spec__2___redArg___lam__0(v_head_600_);
return v_res_602_;
}
}
lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__2___redArg(lean_object* v_as_x27_603_, lean_object* v_b_604_){
_start:
{
if (lean_obj_tag(v_as_x27_603_) == 0)
{
lean_object* v___x_606_; 
v___x_606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_606_, 0, v_b_604_);
return v___x_606_;
}
else
{
lean_object* v_head_607_; lean_object* v_tail_608_; lean_object* v___f_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
v_head_607_ = lean_ctor_get(v_as_x27_603_, 0);
v_tail_608_ = lean_ctor_get(v_as_x27_603_, 1);
lean_inc_n(v_head_607_, 2);
v___f_609_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00checkOlean_spec__2___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_609_, 0, v_head_607_);
v___x_610_ = lean_unsigned_to_nat(0u);
v___x_611_ = lean_io_as_task(v___f_609_, v___x_610_);
v___x_612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_612_, 0, v_head_607_);
lean_ctor_set(v___x_612_, 1, v___x_611_);
v___x_613_ = lean_array_push(v_b_604_, v___x_612_);
v_as_x27_603_ = v_tail_608_;
v_b_604_ = v___x_613_;
goto _start;
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00checkOlean_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_x27_603_ = stack[0].m_obj;
lean_object* v_b_604_ = stack[1].m_obj;
lean_object* v_res_615_;
v_res_615_ = l_List_forIn_x27_loop___at___00checkOlean_spec__2___redArg(v_as_x27_603_, v_b_604_);
stack->m_obj
 = v_res_615_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__2___redArg___boxed(lean_object* v_as_x27_616_, lean_object* v_b_617_, lean_object* v___y_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l_List_forIn_x27_loop___at___00checkOlean_spec__2___redArg(v_as_x27_616_, v_b_617_);
lean_dec(v_as_x27_616_);
return v_res_619_;
}
}
lean_object* l_List_mapM_loop___at___00checkOlean_spec__5(lean_object* v_x_621_, lean_object* v_x_622_){
_start:
{
if (lean_obj_tag(v_x_621_) == 0)
{
lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_624_ = l_List_reverse___redArg(v_x_622_);
v___x_625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_625_, 0, v___x_624_);
return v___x_625_;
}
else
{
lean_object* v_head_626_; lean_object* v_tail_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_641_; 
v_head_626_ = lean_ctor_get(v_x_621_, 0);
v_tail_627_ = lean_ctor_get(v_x_621_, 1);
v_isSharedCheck_641_ = !lean_is_exclusive(v_x_621_);
if (v_isSharedCheck_641_ == 0)
{
v___x_629_ = v_x_621_;
v_isShared_630_ = v_isSharedCheck_641_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_tail_627_);
lean_inc(v_head_626_);
lean_dec(v_x_621_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_641_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_631_; uint8_t v___x_632_; 
lean_inc(v_head_626_);
v___x_631_ = l_String_toName(v_head_626_);
v___x_632_ = l_Lean_Name_isAnonymous(v___x_631_);
if (v___x_632_ == 0)
{
lean_object* v___x_634_; 
lean_dec(v_head_626_);
if (v_isShared_630_ == 0)
{
lean_ctor_set(v___x_629_, 1, v_x_622_);
lean_ctor_set(v___x_629_, 0, v___x_631_);
v___x_634_ = v___x_629_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v___x_631_);
lean_ctor_set(v_reuseFailAlloc_636_, 1, v_x_622_);
v___x_634_ = v_reuseFailAlloc_636_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
v_x_621_ = v_tail_627_;
v_x_622_ = v___x_634_;
goto _start;
}
}
else
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
lean_dec(v___x_631_);
lean_del_object(v___x_629_);
lean_dec(v_tail_627_);
lean_dec(v_x_622_);
v___x_637_ = ((lean_object*)(l_List_mapM_loop___at___00checkOlean_spec__5___closed__0));
v___x_638_ = lean_string_append(v___x_637_, v_head_626_);
lean_dec(v_head_626_);
v___x_639_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_639_, 0, v___x_638_);
v___x_640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_640_, 0, v___x_639_);
return v___x_640_;
}
}
}
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00checkOlean_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_621_ = stack[0].m_obj;
lean_object* v_x_622_ = stack[1].m_obj;
lean_object* v_res_642_;
v_res_642_ = l_List_mapM_loop___at___00checkOlean_spec__5(v_x_621_, v_x_622_);
stack->m_obj
 = v_res_642_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00checkOlean_spec__5___boxed(lean_object* v_x_643_, lean_object* v_x_644_, lean_object* v___y_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_List_mapM_loop___at___00checkOlean_spec__5(v_x_643_, v_x_644_);
return v_res_646_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00checkOlean_spec__0(lean_object* v_val_647_, lean_object* v_a_648_, uint8_t v_fresh_649_, lean_object* v_as_650_, size_t v_sz_651_, size_t v_i_652_, lean_object* v_b_653_){
_start:
{
lean_object* v_a_656_; uint8_t v___x_660_; 
v___x_660_ = lean_usize_dec_lt(v_i_652_, v_sz_651_);
if (v___x_660_ == 0)
{
lean_object* v___x_661_; 
v___x_661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_661_, 0, v_b_653_);
return v___x_661_;
}
else
{
lean_object* v_fst_662_; lean_object* v_snd_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_693_; 
v_fst_662_ = lean_ctor_get(v_b_653_, 0);
v_snd_663_ = lean_ctor_get(v_b_653_, 1);
v_isSharedCheck_693_ = !lean_is_exclusive(v_b_653_);
if (v_isSharedCheck_693_ == 0)
{
v___x_665_ = v_b_653_;
v_isShared_666_ = v_isSharedCheck_693_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_snd_663_);
lean_inc(v_fst_662_);
lean_dec(v_b_653_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_693_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v_a_667_; lean_object* v___x_668_; 
v_a_667_ = lean_array_uget_borrowed(v_as_650_, v_i_652_);
lean_inc(v_a_667_);
v___x_668_ = l_Lean_searchModuleNameOfFileName(v_a_667_, v_val_647_);
if (lean_obj_tag(v___x_668_) == 0)
{
lean_object* v_a_669_; lean_object* v___y_671_; 
v_a_669_ = lean_ctor_get(v___x_668_, 0);
lean_inc(v_a_669_);
lean_dec_ref_known(v___x_668_, 1);
if (lean_obj_tag(v_a_669_) == 1)
{
lean_object* v_val_676_; 
v_val_676_ = lean_ctor_get(v_a_669_, 0);
lean_inc(v_val_676_);
lean_dec_ref_known(v_a_669_, 1);
if (v_fresh_649_ == 0)
{
uint8_t v___x_683_; 
v___x_683_ = l_Lean_Name_isPrefixOf(v_a_648_, v_val_676_);
if (v___x_683_ == 0)
{
goto v___jp_680_;
}
else
{
lean_dec(v_snd_663_);
goto v___jp_677_;
}
}
else
{
goto v___jp_680_;
}
v___jp_677_:
{
uint8_t v___x_678_; 
v___x_678_ = l_List_elem___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_4052238930____hygCtx___hyg_2__spec__1(v_val_676_, v_fst_662_);
if (v___x_678_ == 0)
{
lean_object* v___x_679_; 
v___x_679_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_679_, 0, v_val_676_);
lean_ctor_set(v___x_679_, 1, v_fst_662_);
v___y_671_ = v___x_679_;
goto v___jp_670_;
}
else
{
lean_dec(v_val_676_);
v___y_671_ = v_fst_662_;
goto v___jp_670_;
}
}
v___jp_680_:
{
uint8_t v___x_681_; 
v___x_681_ = lean_name_eq(v_a_648_, v_val_676_);
if (v___x_681_ == 0)
{
lean_object* v___x_682_; 
lean_dec(v_val_676_);
lean_del_object(v___x_665_);
v___x_682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_682_, 0, v_fst_662_);
lean_ctor_set(v___x_682_, 1, v_snd_663_);
v_a_656_ = v___x_682_;
goto v___jp_655_;
}
else
{
lean_dec(v_snd_663_);
goto v___jp_677_;
}
}
}
else
{
lean_object* v___x_684_; 
lean_dec(v_a_669_);
lean_del_object(v___x_665_);
v___x_684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_684_, 0, v_fst_662_);
lean_ctor_set(v___x_684_, 1, v_snd_663_);
v_a_656_ = v___x_684_;
goto v___jp_655_;
}
v___jp_670_:
{
lean_object* v___x_672_; lean_object* v___x_674_; 
v___x_672_ = lean_box(v___x_660_);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 1, v___x_672_);
lean_ctor_set(v___x_665_, 0, v___y_671_);
v___x_674_ = v___x_665_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v___y_671_);
lean_ctor_set(v_reuseFailAlloc_675_, 1, v___x_672_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
v_a_656_ = v___x_674_;
goto v___jp_655_;
}
}
}
else
{
lean_object* v_a_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_692_; 
lean_del_object(v___x_665_);
lean_dec(v_snd_663_);
lean_dec(v_fst_662_);
v_a_685_ = lean_ctor_get(v___x_668_, 0);
v_isSharedCheck_692_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_692_ == 0)
{
v___x_687_ = v___x_668_;
v_isShared_688_ = v_isSharedCheck_692_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_a_685_);
lean_dec(v___x_668_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_692_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v___x_690_; 
if (v_isShared_688_ == 0)
{
v___x_690_ = v___x_687_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v_a_685_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
return v___x_690_;
}
}
}
}
}
v___jp_655_:
{
size_t v___x_657_; size_t v___x_658_; 
v___x_657_ = ((size_t)1ULL);
v___x_658_ = lean_usize_add(v_i_652_, v___x_657_);
v_i_652_ = v___x_658_;
v_b_653_ = v_a_656_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00checkOlean_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_647_ = stack[0].m_obj;
lean_object* v_a_648_ = stack[1].m_obj;
uint8_t v_fresh_649_ = stack[2].m_num;
lean_object* v_as_650_ = stack[3].m_obj;
size_t v_sz_651_ = stack[4].m_num;
size_t v_i_652_ = stack[5].m_num;
lean_object* v_b_653_ = stack[6].m_obj;
lean_object* v_res_694_;
v_res_694_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00checkOlean_spec__0(v_val_647_, v_a_648_, v_fresh_649_, v_as_650_, v_sz_651_, v_i_652_, v_b_653_);
stack->m_obj
 = v_res_694_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00checkOlean_spec__0___boxed(lean_object* v_val_695_, lean_object* v_a_696_, lean_object* v_fresh_697_, lean_object* v_as_698_, lean_object* v_sz_699_, lean_object* v_i_700_, lean_object* v_b_701_, lean_object* v___y_702_){
_start:
{
uint8_t v_fresh_boxed_703_; size_t v_sz_boxed_704_; size_t v_i_boxed_705_; lean_object* v_res_706_; 
v_fresh_boxed_703_ = lean_unbox(v_fresh_697_);
v_sz_boxed_704_ = lean_unbox_usize(v_sz_699_);
lean_dec(v_sz_699_);
v_i_boxed_705_ = lean_unbox_usize(v_i_700_);
lean_dec(v_i_700_);
v_res_706_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00checkOlean_spec__0(v_val_695_, v_a_696_, v_fresh_boxed_703_, v_as_698_, v_sz_boxed_704_, v_i_boxed_705_, v_b_701_);
lean_dec_ref(v_as_698_);
lean_dec(v_a_696_);
lean_dec(v_val_695_);
return v_res_706_;
}
}
lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__1___redArg(lean_object* v_val_709_, uint8_t v_fresh_710_, lean_object* v_as_x27_711_, lean_object* v_b_712_){
_start:
{
if (lean_obj_tag(v_as_x27_711_) == 0)
{
lean_object* v___x_714_; 
v___x_714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_714_, 0, v_b_712_);
return v___x_714_;
}
else
{
lean_object* v_head_715_; lean_object* v_tail_716_; uint8_t v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v_head_715_ = lean_ctor_get(v_as_x27_711_, 0);
v_tail_716_ = lean_ctor_get(v_as_x27_711_, 1);
v___x_717_ = 0;
v___x_718_ = ((lean_object*)(l_List_forIn_x27_loop___at___00checkOlean_spec__1___redArg___closed__0));
v___x_719_ = l_Lean_SearchPath_findAllWithExt(v_val_709_, v___x_718_);
if (lean_obj_tag(v___x_719_) == 0)
{
lean_object* v_a_720_; lean_object* v___x_721_; lean_object* v___x_722_; size_t v_sz_723_; size_t v___x_724_; lean_object* v___x_725_; 
v_a_720_ = lean_ctor_get(v___x_719_, 0);
lean_inc(v_a_720_);
lean_dec_ref_known(v___x_719_, 1);
v___x_721_ = lean_box(v___x_717_);
v___x_722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_722_, 0, v_b_712_);
lean_ctor_set(v___x_722_, 1, v___x_721_);
v_sz_723_ = lean_array_size(v_a_720_);
v___x_724_ = ((size_t)0ULL);
v___x_725_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00checkOlean_spec__0(v_val_709_, v_head_715_, v_fresh_710_, v_a_720_, v_sz_723_, v___x_724_, v___x_722_);
lean_dec(v_a_720_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v_a_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_742_; 
v_a_726_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_742_ == 0)
{
v___x_728_ = v___x_725_;
v_isShared_729_ = v_isSharedCheck_742_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_a_726_);
lean_dec(v___x_725_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_742_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v_snd_730_; uint8_t v___x_731_; 
v_snd_730_ = lean_ctor_get(v_a_726_, 1);
v___x_731_ = lean_unbox(v_snd_730_);
if (v___x_731_ == 0)
{
uint8_t v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_738_; 
lean_dec(v_a_726_);
v___x_732_ = 1;
v___x_733_ = ((lean_object*)(l_List_forIn_x27_loop___at___00checkOlean_spec__1___redArg___closed__1));
lean_inc(v_head_715_);
v___x_734_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_715_, v___x_732_);
v___x_735_ = lean_string_append(v___x_733_, v___x_734_);
lean_dec_ref(v___x_734_);
v___x_736_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_736_, 0, v___x_735_);
if (v_isShared_729_ == 0)
{
lean_ctor_set_tag(v___x_728_, 1);
lean_ctor_set(v___x_728_, 0, v___x_736_);
v___x_738_ = v___x_728_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v___x_736_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
return v___x_738_;
}
}
else
{
lean_object* v_fst_740_; 
lean_del_object(v___x_728_);
v_fst_740_ = lean_ctor_get(v_a_726_, 0);
lean_inc(v_fst_740_);
lean_dec(v_a_726_);
v_as_x27_711_ = v_tail_716_;
v_b_712_ = v_fst_740_;
goto _start;
}
}
}
else
{
lean_object* v_a_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_750_; 
v_a_743_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_750_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_750_ == 0)
{
v___x_745_ = v___x_725_;
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_a_743_);
lean_dec(v___x_725_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_748_; 
if (v_isShared_746_ == 0)
{
v___x_748_ = v___x_745_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v_a_743_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
}
}
else
{
lean_object* v_a_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_758_; 
lean_dec(v_b_712_);
v_a_751_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_758_ == 0)
{
v___x_753_ = v___x_719_;
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_a_751_);
lean_dec(v___x_719_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_756_; 
if (v_isShared_754_ == 0)
{
v___x_756_ = v___x_753_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_a_751_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00checkOlean_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_709_ = stack[0].m_obj;
uint8_t v_fresh_710_ = stack[1].m_num;
lean_object* v_as_x27_711_ = stack[2].m_obj;
lean_object* v_b_712_ = stack[3].m_obj;
lean_object* v_res_759_;
v_res_759_ = l_List_forIn_x27_loop___at___00checkOlean_spec__1___redArg(v_val_709_, v_fresh_710_, v_as_x27_711_, v_b_712_);
stack->m_obj
 = v_res_759_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__1___redArg___boxed(lean_object* v_val_760_, lean_object* v_fresh_761_, lean_object* v_as_x27_762_, lean_object* v_b_763_, lean_object* v___y_764_){
_start:
{
uint8_t v_fresh_boxed_765_; lean_object* v_res_766_; 
v_fresh_boxed_765_ = lean_unbox(v_fresh_761_);
v_res_766_ = l_List_forIn_x27_loop___at___00checkOlean_spec__1___redArg(v_val_760_, v_fresh_boxed_765_, v_as_x27_762_, v_b_763_);
lean_dec(v_as_x27_762_);
lean_dec(v_val_760_);
return v_res_766_;
}
}
lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__4___redArg(uint8_t v_verbose_768_, uint8_t v_silent_769_, lean_object* v_as_x27_770_, lean_object* v_b_771_){
_start:
{
if (lean_obj_tag(v_as_x27_770_) == 0)
{
lean_object* v___x_773_; 
v___x_773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_773_, 0, v_b_771_);
return v___x_773_;
}
else
{
lean_object* v_head_774_; lean_object* v_tail_775_; lean_object* v___x_776_; 
v_head_774_ = lean_ctor_get(v_as_x27_770_, 0);
v_tail_775_ = lean_ctor_get(v_as_x27_770_, 1);
v___x_776_ = lean_box(0);
if (v_verbose_768_ == 0)
{
goto v___jp_777_;
}
else
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_780_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00checkOlean_spec__3___closed__1));
lean_inc(v_head_774_);
v___x_781_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_774_, v_verbose_768_);
v___x_782_ = lean_string_append(v___x_780_, v___x_781_);
lean_dec_ref(v___x_781_);
v___x_783_ = ((lean_object*)(l_List_forIn_x27_loop___at___00checkOlean_spec__4___redArg___closed__0));
v___x_784_ = lean_string_append(v___x_782_, v___x_783_);
v___x_785_ = l_println(v___x_784_, v_silent_769_);
if (lean_obj_tag(v___x_785_) == 0)
{
lean_dec_ref_known(v___x_785_, 1);
goto v___jp_777_;
}
else
{
return v___x_785_;
}
}
v___jp_777_:
{
lean_object* v___x_778_; 
lean_inc(v_head_774_);
v___x_778_ = l_replayFromFresh(v_head_774_);
if (lean_obj_tag(v___x_778_) == 0)
{
lean_dec_ref_known(v___x_778_, 1);
v_as_x27_770_ = v_tail_775_;
v_b_771_ = v___x_776_;
goto _start;
}
else
{
return v___x_778_;
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00checkOlean_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_verbose_768_ = stack[0].m_num;
uint8_t v_silent_769_ = stack[1].m_num;
lean_object* v_as_x27_770_ = stack[2].m_obj;
lean_object* v_b_771_ = stack[3].m_obj;
lean_object* v_res_786_;
v_res_786_ = l_List_forIn_x27_loop___at___00checkOlean_spec__4___redArg(v_verbose_768_, v_silent_769_, v_as_x27_770_, v_b_771_);
stack->m_obj
 = v_res_786_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__4___redArg___boxed(lean_object* v_verbose_787_, lean_object* v_silent_788_, lean_object* v_as_x27_789_, lean_object* v_b_790_, lean_object* v___y_791_){
_start:
{
uint8_t v_verbose_boxed_792_; uint8_t v_silent_boxed_793_; lean_object* v_res_794_; 
v_verbose_boxed_792_ = lean_unbox(v_verbose_787_);
v_silent_boxed_793_ = lean_unbox(v_silent_788_);
v_res_794_ = l_List_forIn_x27_loop___at___00checkOlean_spec__4___redArg(v_verbose_boxed_792_, v_silent_boxed_793_, v_as_x27_789_, v_b_790_);
lean_dec(v_as_x27_789_);
return v_res_794_;
}
}
lean_object* l_checkOlean(lean_object* v_args_799_, uint8_t v_fresh_800_, uint8_t v_verbose_801_, uint8_t v_silent_802_){
_start:
{
lean_object* v_targets_808_; lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_870_ = ((lean_object*)(l_checkOlean___closed__2));
v___x_871_ = l_Lean_findSysroot(v___x_870_);
if (lean_obj_tag(v___x_871_) == 0)
{
lean_object* v_a_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
v_a_872_ = lean_ctor_get(v___x_871_, 0);
lean_inc(v_a_872_);
lean_dec_ref_known(v___x_871_, 1);
v___x_873_ = lean_box(0);
v___x_874_ = l_Lean_initSearchPath(v_a_872_, v___x_873_);
if (lean_obj_tag(v___x_874_) == 0)
{
lean_dec_ref_known(v___x_874_, 1);
if (lean_obj_tag(v_args_799_) == 0)
{
lean_object* v___x_875_; 
v___x_875_ = l_getCurrentModule();
if (lean_obj_tag(v___x_875_) == 0)
{
lean_object* v_a_876_; lean_object* v___x_877_; 
v_a_876_ = lean_ctor_get(v___x_875_, 0);
lean_inc(v_a_876_);
lean_dec_ref_known(v___x_875_, 1);
v___x_877_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_877_, 0, v_a_876_);
lean_ctor_set(v___x_877_, 1, v___x_873_);
v_targets_808_ = v___x_877_;
goto v___jp_807_;
}
else
{
lean_object* v_a_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_885_; 
v_a_878_ = lean_ctor_get(v___x_875_, 0);
v_isSharedCheck_885_ = !lean_is_exclusive(v___x_875_);
if (v_isSharedCheck_885_ == 0)
{
v___x_880_ = v___x_875_;
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_a_878_);
lean_dec(v___x_875_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_883_; 
if (v_isShared_881_ == 0)
{
v___x_883_ = v___x_880_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_a_878_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
}
}
else
{
lean_object* v___x_886_; 
v___x_886_ = l_List_mapM_loop___at___00checkOlean_spec__5(v_args_799_, v___x_873_);
if (lean_obj_tag(v___x_886_) == 0)
{
lean_object* v_a_887_; 
v_a_887_ = lean_ctor_get(v___x_886_, 0);
lean_inc(v_a_887_);
lean_dec_ref_known(v___x_886_, 1);
v_targets_808_ = v_a_887_;
goto v___jp_807_;
}
else
{
lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_895_; 
v_a_888_ = lean_ctor_get(v___x_886_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_886_);
if (v_isSharedCheck_895_ == 0)
{
v___x_890_ = v___x_886_;
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_dec(v___x_886_);
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
}
else
{
lean_object* v_a_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_903_; 
lean_dec(v_args_799_);
v_a_896_ = lean_ctor_get(v___x_874_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_874_);
if (v_isSharedCheck_903_ == 0)
{
v___x_898_ = v___x_874_;
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_a_896_);
lean_dec(v___x_874_);
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
}
else
{
lean_object* v_a_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_911_; 
lean_dec(v_args_799_);
v_a_904_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_911_ == 0)
{
v___x_906_ = v___x_871_;
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_a_904_);
lean_dec(v___x_871_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_909_; 
if (v_isShared_907_ == 0)
{
v___x_909_ = v___x_906_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v_a_904_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
v___jp_804_:
{
lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_805_ = l_checkExport___boxed__const__2;
v___x_806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_806_, 0, v___x_805_);
return v___x_806_;
}
v___jp_807_:
{
lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_809_ = lean_box(0);
v___x_810_ = l_Lean_searchPathRef;
v___x_811_ = lean_st_ref_get(v___x_810_);
v___x_812_ = l_List_forIn_x27_loop___at___00checkOlean_spec__1___redArg(v___x_811_, v_fresh_800_, v_targets_808_, v___x_809_);
lean_dec(v_targets_808_);
lean_dec(v___x_811_);
if (lean_obj_tag(v___x_812_) == 0)
{
if (v_fresh_800_ == 0)
{
lean_object* v_a_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
v_a_813_ = lean_ctor_get(v___x_812_, 0);
lean_inc(v_a_813_);
lean_dec_ref_known(v___x_812_, 1);
v___x_814_ = ((lean_object*)(l_checkOlean___closed__0));
v___x_815_ = l_List_forIn_x27_loop___at___00checkOlean_spec__2___redArg(v_a_813_, v___x_814_);
lean_dec(v_a_813_);
if (lean_obj_tag(v___x_815_) == 0)
{
lean_object* v_a_816_; lean_object* v___x_817_; size_t v_sz_818_; size_t v___x_819_; lean_object* v___x_820_; 
v_a_816_ = lean_ctor_get(v___x_815_, 0);
lean_inc(v_a_816_);
lean_dec_ref_known(v___x_815_, 1);
v___x_817_ = lean_box(0);
v_sz_818_ = lean_array_size(v_a_816_);
v___x_819_ = ((size_t)0ULL);
v___x_820_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00checkOlean_spec__3(v_verbose_801_, v_silent_802_, v_a_816_, v_sz_818_, v___x_819_, v___x_817_);
lean_dec(v_a_816_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_dec_ref_known(v___x_820_, 1);
goto v___jp_804_;
}
else
{
lean_object* v_a_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_828_; 
v_a_821_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_828_ == 0)
{
v___x_823_ = v___x_820_;
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_a_821_);
lean_dec(v___x_820_);
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
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_836_; 
v_a_829_ = lean_ctor_get(v___x_815_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_815_);
if (v_isSharedCheck_836_ == 0)
{
v___x_831_ = v___x_815_;
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___x_815_);
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
else
{
lean_object* v_a_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_861_; 
v_a_837_ = lean_ctor_get(v___x_812_, 0);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_861_ == 0)
{
v___x_839_ = v___x_812_;
v_isShared_840_ = v_isSharedCheck_861_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_a_837_);
lean_dec(v___x_812_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_861_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_841_; lean_object* v___x_842_; uint8_t v___x_843_; 
v___x_841_ = l_List_lengthTR___redArg(v_a_837_);
v___x_842_ = lean_unsigned_to_nat(1u);
v___x_843_ = lean_nat_dec_eq(v___x_841_, v___x_842_);
lean_dec(v___x_841_);
if (v___x_843_ == 0)
{
lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_849_; 
v___x_844_ = ((lean_object*)(l_checkOlean___closed__1));
v___x_845_ = l_List_toString___at___00Lean_Environment_AddConstAsyncResult_commitConst_spec__1(v_a_837_);
v___x_846_ = lean_string_append(v___x_844_, v___x_845_);
lean_dec_ref(v___x_845_);
v___x_847_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_847_, 0, v___x_846_);
if (v_isShared_840_ == 0)
{
lean_ctor_set_tag(v___x_839_, 1);
lean_ctor_set(v___x_839_, 0, v___x_847_);
v___x_849_ = v___x_839_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v___x_847_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
else
{
lean_object* v___x_851_; lean_object* v___x_852_; 
lean_del_object(v___x_839_);
v___x_851_ = lean_box(0);
v___x_852_ = l_List_forIn_x27_loop___at___00checkOlean_spec__4___redArg(v_verbose_801_, v_silent_802_, v_a_837_, v___x_851_);
lean_dec(v_a_837_);
if (lean_obj_tag(v___x_852_) == 0)
{
lean_dec_ref_known(v___x_852_, 1);
goto v___jp_804_;
}
else
{
lean_object* v_a_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_860_; 
v_a_853_ = lean_ctor_get(v___x_852_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_860_ == 0)
{
v___x_855_ = v___x_852_;
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_a_853_);
lean_dec(v___x_852_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_858_; 
if (v_isShared_856_ == 0)
{
v___x_858_ = v___x_855_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_a_853_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_869_; 
v_a_862_ = lean_ctor_get(v___x_812_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_869_ == 0)
{
v___x_864_ = v___x_812_;
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_a_862_);
lean_dec(v___x_812_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_867_; 
if (v_isShared_865_ == 0)
{
v___x_867_ = v___x_864_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_a_862_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
}
}
}
LEAN_EXPORT void l_checkOlean_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_799_ = stack[0].m_obj;
uint8_t v_fresh_800_ = stack[1].m_num;
uint8_t v_verbose_801_ = stack[2].m_num;
uint8_t v_silent_802_ = stack[3].m_num;
lean_object* v_res_912_;
v_res_912_ = l_checkOlean(v_args_799_, v_fresh_800_, v_verbose_801_, v_silent_802_);
stack->m_obj
 = v_res_912_;
}
LEAN_EXPORT lean_object* l_checkOlean___boxed(lean_object* v_args_913_, lean_object* v_fresh_914_, lean_object* v_verbose_915_, lean_object* v_silent_916_, lean_object* v_a_917_){
_start:
{
uint8_t v_fresh_boxed_918_; uint8_t v_verbose_boxed_919_; uint8_t v_silent_boxed_920_; lean_object* v_res_921_; 
v_fresh_boxed_918_ = lean_unbox(v_fresh_914_);
v_verbose_boxed_919_ = lean_unbox(v_verbose_915_);
v_silent_boxed_920_ = lean_unbox(v_silent_916_);
v_res_921_ = l_checkOlean(v_args_913_, v_fresh_boxed_918_, v_verbose_boxed_919_, v_silent_boxed_920_);
return v_res_921_;
}
}
lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__1(lean_object* v_val_922_, uint8_t v_fresh_923_, lean_object* v_as_924_, lean_object* v_as_x27_925_, lean_object* v_b_926_, lean_object* v_a_927_){
_start:
{
lean_object* v___x_929_; 
v___x_929_ = l_List_forIn_x27_loop___at___00checkOlean_spec__1___redArg(v_val_922_, v_fresh_923_, v_as_x27_925_, v_b_926_);
return v___x_929_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00checkOlean_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_922_ = stack[0].m_obj;
uint8_t v_fresh_923_ = stack[1].m_num;
lean_object* v_as_924_ = stack[2].m_obj;
lean_object* v_as_x27_925_ = stack[3].m_obj;
lean_object* v_b_926_ = stack[4].m_obj;
lean_object* v_res_930_;
v_res_930_ = l_List_forIn_x27_loop___at___00checkOlean_spec__1(v_val_922_, v_fresh_923_, v_as_924_, v_as_x27_925_, v_b_926_, lean_box(0));
stack->m_obj
 = v_res_930_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__1___boxed(lean_object* v_val_931_, lean_object* v_fresh_932_, lean_object* v_as_933_, lean_object* v_as_x27_934_, lean_object* v_b_935_, lean_object* v_a_936_, lean_object* v___y_937_){
_start:
{
uint8_t v_fresh_boxed_938_; lean_object* v_res_939_; 
v_fresh_boxed_938_ = lean_unbox(v_fresh_932_);
v_res_939_ = l_List_forIn_x27_loop___at___00checkOlean_spec__1(v_val_931_, v_fresh_boxed_938_, v_as_933_, v_as_x27_934_, v_b_935_, v_a_936_);
lean_dec(v_as_x27_934_);
lean_dec(v_as_933_);
lean_dec(v_val_931_);
return v_res_939_;
}
}
lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__2(lean_object* v_as_940_, lean_object* v_as_x27_941_, lean_object* v_b_942_, lean_object* v_a_943_){
_start:
{
lean_object* v___x_945_; 
v___x_945_ = l_List_forIn_x27_loop___at___00checkOlean_spec__2___redArg(v_as_x27_941_, v_b_942_);
return v___x_945_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00checkOlean_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_940_ = stack[0].m_obj;
lean_object* v_as_x27_941_ = stack[1].m_obj;
lean_object* v_b_942_ = stack[2].m_obj;
lean_object* v_res_946_;
v_res_946_ = l_List_forIn_x27_loop___at___00checkOlean_spec__2(v_as_940_, v_as_x27_941_, v_b_942_, lean_box(0));
stack->m_obj
 = v_res_946_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__2___boxed(lean_object* v_as_947_, lean_object* v_as_x27_948_, lean_object* v_b_949_, lean_object* v_a_950_, lean_object* v___y_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l_List_forIn_x27_loop___at___00checkOlean_spec__2(v_as_947_, v_as_x27_948_, v_b_949_, v_a_950_);
lean_dec(v_as_x27_948_);
lean_dec(v_as_947_);
return v_res_952_;
}
}
lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__4(uint8_t v_verbose_953_, uint8_t v_silent_954_, lean_object* v_as_955_, lean_object* v_as_x27_956_, lean_object* v_b_957_, lean_object* v_a_958_){
_start:
{
lean_object* v___x_960_; 
v___x_960_ = l_List_forIn_x27_loop___at___00checkOlean_spec__4___redArg(v_verbose_953_, v_silent_954_, v_as_x27_956_, v_b_957_);
return v___x_960_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00checkOlean_spec__4_0interp(lean_interpreter_value* stack)
{
uint8_t v_verbose_953_ = stack[0].m_num;
uint8_t v_silent_954_ = stack[1].m_num;
lean_object* v_as_955_ = stack[2].m_obj;
lean_object* v_as_x27_956_ = stack[3].m_obj;
lean_object* v_b_957_ = stack[4].m_obj;
lean_object* v_res_961_;
v_res_961_ = l_List_forIn_x27_loop___at___00checkOlean_spec__4(v_verbose_953_, v_silent_954_, v_as_955_, v_as_x27_956_, v_b_957_, lean_box(0));
stack->m_obj
 = v_res_961_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__4___boxed(lean_object* v_verbose_962_, lean_object* v_silent_963_, lean_object* v_as_964_, lean_object* v_as_x27_965_, lean_object* v_b_966_, lean_object* v_a_967_, lean_object* v___y_968_){
_start:
{
uint8_t v_verbose_boxed_969_; uint8_t v_silent_boxed_970_; lean_object* v_res_971_; 
v_verbose_boxed_969_ = lean_unbox(v_verbose_962_);
v_silent_boxed_970_ = lean_unbox(v_silent_963_);
v_res_971_ = l_List_forIn_x27_loop___at___00checkOlean_spec__4(v_verbose_boxed_969_, v_silent_boxed_970_, v_as_964_, v_as_x27_965_, v_b_966_, v_a_967_);
lean_dec(v_as_x27_965_);
lean_dec(v_as_964_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l_List_partition_loop___at___00main_spec__0(lean_object* v_a_973_, lean_object* v_a_974_){
_start:
{
if (lean_obj_tag(v_a_973_) == 0)
{
lean_object* v_fst_975_; lean_object* v_snd_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_985_; 
v_fst_975_ = lean_ctor_get(v_a_974_, 0);
v_snd_976_ = lean_ctor_get(v_a_974_, 1);
v_isSharedCheck_985_ = !lean_is_exclusive(v_a_974_);
if (v_isSharedCheck_985_ == 0)
{
v___x_978_ = v_a_974_;
v_isShared_979_ = v_isSharedCheck_985_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_snd_976_);
lean_inc(v_fst_975_);
lean_dec(v_a_974_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_985_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_983_; 
v___x_980_ = l_List_reverse___redArg(v_fst_975_);
v___x_981_ = l_List_reverse___redArg(v_snd_976_);
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 1, v___x_981_);
lean_ctor_set(v___x_978_, 0, v___x_980_);
v___x_983_ = v___x_978_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v___x_980_);
lean_ctor_set(v_reuseFailAlloc_984_, 1, v___x_981_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
}
else
{
lean_object* v_head_986_; lean_object* v_tail_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_1014_; 
v_head_986_ = lean_ctor_get(v_a_973_, 0);
v_tail_987_ = lean_ctor_get(v_a_973_, 1);
v_isSharedCheck_1014_ = !lean_is_exclusive(v_a_973_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_989_ = v_a_973_;
v_isShared_990_ = v_isSharedCheck_1014_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_tail_987_);
lean_inc(v_head_986_);
lean_dec(v_a_973_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_1014_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v_fst_991_; lean_object* v_snd_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_1013_; 
v_fst_991_ = lean_ctor_get(v_a_974_, 0);
v_snd_992_ = lean_ctor_get(v_a_974_, 1);
v_isSharedCheck_1013_ = !lean_is_exclusive(v_a_974_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_994_ = v_a_974_;
v_isShared_995_ = v_isSharedCheck_1013_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_snd_992_);
lean_inc(v_fst_991_);
lean_dec(v_a_974_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_1013_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; uint8_t v___x_1006_; 
v___x_1004_ = lean_string_utf8_byte_size(v_head_986_);
v___x_1005_ = lean_unsigned_to_nat(1u);
v___x_1006_ = lean_nat_dec_le(v___x_1005_, v___x_1004_);
if (v___x_1006_ == 0)
{
goto v___jp_996_;
}
else
{
lean_object* v___x_1007_; lean_object* v___x_1008_; uint8_t v___x_1009_; 
v___x_1007_ = ((lean_object*)(l_List_partition_loop___at___00main_spec__0___closed__0));
v___x_1008_ = lean_unsigned_to_nat(0u);
v___x_1009_ = lean_string_memcmp(v_head_986_, v___x_1007_, v___x_1008_, v___x_1008_, v___x_1005_);
if (v___x_1009_ == 0)
{
goto v___jp_996_;
}
else
{
lean_object* v___x_1010_; lean_object* v___x_1011_; 
lean_del_object(v___x_994_);
lean_del_object(v___x_989_);
v___x_1010_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1010_, 0, v_head_986_);
lean_ctor_set(v___x_1010_, 1, v_fst_991_);
v___x_1011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1010_);
lean_ctor_set(v___x_1011_, 1, v_snd_992_);
v_a_973_ = v_tail_987_;
v_a_974_ = v___x_1011_;
goto _start;
}
}
v___jp_996_:
{
lean_object* v___x_998_; 
if (v_isShared_990_ == 0)
{
lean_ctor_set(v___x_989_, 1, v_snd_992_);
v___x_998_ = v___x_989_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_head_986_);
lean_ctor_set(v_reuseFailAlloc_1003_, 1, v_snd_992_);
v___x_998_ = v_reuseFailAlloc_1003_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
lean_object* v___x_1000_; 
if (v_isShared_995_ == 0)
{
lean_ctor_set(v___x_994_, 1, v___x_998_);
v___x_1000_ = v___x_994_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_fst_991_);
lean_ctor_set(v_reuseFailAlloc_1002_, 1, v___x_998_);
v___x_1000_ = v_reuseFailAlloc_1002_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
v_a_973_ = v_tail_987_;
v_a_974_ = v___x_1000_;
goto _start;
}
}
}
}
}
}
}
}
lean_object* _lean_main(lean_object* v_args_1022_){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v_fst_1026_; lean_object* v_snd_1027_; uint8_t v___y_1029_; lean_object* v___x_1035_; uint8_t v___x_1036_; 
v___x_1024_ = ((lean_object*)(l_main___closed__0));
v___x_1025_ = l_List_partition_loop___at___00main_spec__0(v_args_1022_, v___x_1024_);
v_fst_1026_ = lean_ctor_get(v___x_1025_, 0);
lean_inc(v_fst_1026_);
v_snd_1027_ = lean_ctor_get(v___x_1025_, 1);
lean_inc(v_snd_1027_);
lean_dec_ref(v___x_1025_);
v___x_1035_ = ((lean_object*)(l_main___closed__3));
v___x_1036_ = l_List_elem___at___00Lean_isAutoDeclOrPrivate__Internal_spec__0(v___x_1035_, v_fst_1026_);
if (v___x_1036_ == 0)
{
lean_object* v___x_1037_; uint8_t v___x_1038_; 
v___x_1037_ = ((lean_object*)(l_main___closed__4));
v___x_1038_ = l_List_elem___at___00Lean_isAutoDeclOrPrivate__Internal_spec__0(v___x_1037_, v_fst_1026_);
if (v___x_1038_ == 0)
{
lean_object* v___x_1039_; uint8_t v___x_1040_; 
v___x_1039_ = ((lean_object*)(l_main___closed__5));
v___x_1040_ = l_List_elem___at___00Lean_isAutoDeclOrPrivate__Internal_spec__0(v___x_1039_, v_fst_1026_);
v___y_1029_ = v___x_1040_;
goto v___jp_1028_;
}
else
{
v___y_1029_ = v___x_1038_;
goto v___jp_1028_;
}
}
else
{
lean_object* v___x_1041_; uint8_t v___x_1042_; lean_object* v___x_1043_; 
v___x_1041_ = ((lean_object*)(l_main___closed__2));
v___x_1042_ = l_List_elem___at___00Lean_isAutoDeclOrPrivate__Internal_spec__0(v___x_1041_, v_fst_1026_);
lean_dec(v_fst_1026_);
v___x_1043_ = l_checkExport(v_snd_1027_, v___x_1042_);
lean_dec(v_snd_1027_);
return v___x_1043_;
}
v___jp_1028_:
{
lean_object* v___x_1030_; uint8_t v___x_1031_; lean_object* v___x_1032_; uint8_t v___x_1033_; lean_object* v___x_1034_; 
v___x_1030_ = ((lean_object*)(l_main___closed__1));
v___x_1031_ = l_List_elem___at___00Lean_isAutoDeclOrPrivate__Internal_spec__0(v___x_1030_, v_fst_1026_);
v___x_1032_ = ((lean_object*)(l_main___closed__2));
v___x_1033_ = l_List_elem___at___00Lean_isAutoDeclOrPrivate__Internal_spec__0(v___x_1032_, v_fst_1026_);
lean_dec(v_fst_1026_);
v___x_1034_ = l_checkOlean(v_snd_1027_, v___x_1031_, v___y_1029_, v___x_1033_);
return v___x_1034_;
}
}
}
LEAN_EXPORT void _lean_main_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_1022_ = stack[0].m_obj;
lean_object* v_res_1044_;
v_res_1044_ = _lean_main(v_args_1022_);
stack->m_obj
 = v_res_1044_;
}
LEAN_EXPORT lean_object* l_main___boxed(lean_object* v_args_1045_, lean_object* v_a_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = _lean_main(v_args_1045_);
return v_res_1047_;
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

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
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_thunk_get_own(lean_object*);
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
lean_object* lean_task_get_own(lean_object*);
lean_object* l_IO_eprintln___at___00__private_Init_System_IO_0__IO_eprintlnAux_spec__0(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00replayFromFresh_spec__0_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1_spec__2___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00replayFromFresh_spec__0_spec__0_spec__1_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1_spec__2___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00replayFromFresh_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00replayFromFresh_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__2___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00replayFromFresh_spec__0_spec__0_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__2___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00replayFromFresh_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00replayFromFresh_spec__0(lean_object*, lean_object*);
static lean_once_cell_t l_replayFromFresh___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_replayFromFresh___lam__0___closed__0;
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
uint8_t v___x_80_; uint8_t v___y_82_; lean_object* v___y_83_; uint8_t v___y_84_; lean_object* v___y_85_; lean_object* v___y_86_; lean_object* v___y_87_; lean_object* v___y_88_; uint8_t v___y_89_; lean_object* v_fnames_149_; 
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
v_fnames_149_ = v___x_192_;
goto v___jp_148_;
}
else
{
lean_object* v___x_196_; uint8_t v___x_197_; lean_object* v___x_198_; uint8_t v___x_199_; 
v___x_196_ = lean_array_push(v___x_192_, v___x_194_);
v___x_197_ = 2;
v___x_198_ = l_Lean_OLeanLevel_adjustFileName(v_a_76_, v___x_197_);
v___x_199_ = l_System_FilePath_pathExists(v___x_198_);
if (v___x_199_ == 0)
{
lean_dec_ref(v___x_198_);
v_fnames_149_ = v___x_196_;
goto v___jp_148_;
}
else
{
lean_object* v___x_200_; 
v___x_200_ = lean_array_push(v___x_196_, v___x_198_);
v_fnames_149_ = v___x_200_;
goto v___jp_148_;
}
}
}
v___jp_81_:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_90_ = l_Lean_instInhabitedImportState_default;
v___x_91_ = lean_st_mk_ref(v___x_90_);
lean_inc(v___y_88_);
v___x_92_ = l_Lean_importModulesCore(v___y_85_, v___y_84_, v___y_88_, v___y_89_, v___y_82_, v___x_91_);
if (lean_obj_tag(v___x_92_) == 0)
{
lean_object* v___x_93_; lean_object* v___x_94_; uint32_t v___x_95_; lean_object* v___x_96_; 
lean_dec_ref_known(v___x_92_, 1);
v___x_93_ = lean_st_ref_get(v___x_91_);
lean_dec(v___x_91_);
v___x_94_ = l_Lean_Options_empty;
v___x_95_ = 0;
v___x_96_ = l_Lean_finalizeImport(v___x_93_, v___y_85_, v___x_94_, v___x_95_, v___y_82_, v___y_82_, v___y_84_, v___x_80_, v___y_82_);
if (lean_obj_tag(v___x_96_) == 0)
{
lean_object* v_a_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v_fst_101_; lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_138_; 
v_a_97_ = lean_ctor_get(v___x_96_, 0);
lean_inc(v_a_97_);
lean_dec_ref_known(v___x_96_, 1);
v___x_98_ = lean_unsigned_to_nat(1u);
v___x_99_ = lean_nat_sub(v___y_87_, v___x_98_);
lean_dec(v___y_87_);
v___x_100_ = lean_array_fget(v___y_83_, v___x_99_);
lean_dec(v___x_99_);
lean_dec_ref(v___y_83_);
v_fst_101_ = lean_ctor_get(v___x_100_, 0);
v_isSharedCheck_138_ = !lean_is_exclusive(v___x_100_);
if (v_isSharedCheck_138_ == 0)
{
lean_object* v_unused_139_; 
v_unused_139_ = lean_ctor_get(v___x_100_, 1);
lean_dec(v_unused_139_);
v___x_103_ = v___x_100_;
v_isShared_104_ = v_isSharedCheck_138_;
goto v_resetjp_102_;
}
else
{
lean_inc(v_fst_101_);
lean_dec(v___x_100_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_138_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
lean_object* v_constNames_105_; lean_object* v_constants_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_112_; 
v_constNames_105_ = lean_ctor_get(v_fst_101_, 1);
lean_inc_ref(v_constNames_105_);
v_constants_106_ = lean_ctor_get(v_fst_101_, 2);
lean_inc_ref(v_constants_106_);
lean_dec(v_fst_101_);
v___x_107_ = lean_obj_once(&l_replayFromImports___closed__0, &l_replayFromImports___closed__0_once, _init_l_replayFromImports___closed__0);
lean_inc(v___y_86_);
v___x_108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_108_, 0, v___y_86_);
lean_ctor_set(v___x_108_, 1, v___x_107_);
v___x_109_ = lean_array_get_size(v_constants_106_);
v___x_110_ = l_Array_toSubarray___redArg(v_constants_106_, v___y_86_, v___x_109_);
if (v_isShared_104_ == 0)
{
lean_ctor_set(v___x_103_, 1, v___x_110_);
lean_ctor_set(v___x_103_, 0, v___x_108_);
v___x_112_ = v___x_103_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v___x_108_);
lean_ctor_set(v_reuseFailAlloc_137_, 1, v___x_110_);
v___x_112_ = v_reuseFailAlloc_137_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
size_t v_sz_113_; size_t v___x_114_; lean_object* v___x_115_; 
v_sz_113_ = lean_array_size(v_constNames_105_);
v___x_114_ = ((size_t)0ULL);
v___x_115_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00replayFromImports_spec__0(v_constNames_105_, v_sz_113_, v___x_114_, v___x_112_);
lean_dec_ref(v_constNames_105_);
if (lean_obj_tag(v___x_115_) == 0)
{
lean_object* v_a_116_; lean_object* v_fst_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v_a_116_ = lean_ctor_get(v___x_115_, 0);
lean_inc(v_a_116_);
lean_dec_ref_known(v___x_115_, 1);
v_fst_117_ = lean_ctor_get(v_a_116_, 0);
lean_inc(v_fst_117_);
lean_dec(v_a_116_);
lean_inc(v_a_97_);
v___x_118_ = lean_elab_environment_to_kernel_env(v_a_97_);
v___x_119_ = l_Lean_Kernel_Environment_replay(v_fst_117_, v___x_118_);
lean_dec(v_fst_117_);
if (lean_obj_tag(v___x_119_) == 0)
{
lean_object* v___x_120_; 
lean_dec_ref_known(v___x_119_, 1);
v___x_120_ = lean_environment_free_regions(v_a_97_);
return v___x_120_;
}
else
{
lean_object* v_a_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_128_; 
lean_dec(v_a_97_);
v_a_121_ = lean_ctor_get(v___x_119_, 0);
v_isSharedCheck_128_ = !lean_is_exclusive(v___x_119_);
if (v_isSharedCheck_128_ == 0)
{
v___x_123_ = v___x_119_;
v_isShared_124_ = v_isSharedCheck_128_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_a_121_);
lean_dec(v___x_119_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_128_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_126_; 
if (v_isShared_124_ == 0)
{
v___x_126_ = v___x_123_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v_a_121_);
v___x_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
return v___x_126_;
}
}
}
}
else
{
lean_object* v_a_129_; lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_136_; 
lean_dec(v_a_97_);
v_a_129_ = lean_ctor_get(v___x_115_, 0);
v_isSharedCheck_136_ = !lean_is_exclusive(v___x_115_);
if (v_isSharedCheck_136_ == 0)
{
v___x_131_ = v___x_115_;
v_isShared_132_ = v_isSharedCheck_136_;
goto v_resetjp_130_;
}
else
{
lean_inc(v_a_129_);
lean_dec(v___x_115_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_136_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
lean_object* v___x_134_; 
if (v_isShared_132_ == 0)
{
v___x_134_ = v___x_131_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v_a_129_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
return v___x_134_;
}
}
}
}
}
}
else
{
lean_object* v_a_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_147_; 
lean_dec(v___y_87_);
lean_dec(v___y_86_);
lean_dec_ref(v___y_83_);
v_a_140_ = lean_ctor_get(v___x_96_, 0);
v_isSharedCheck_147_ = !lean_is_exclusive(v___x_96_);
if (v_isSharedCheck_147_ == 0)
{
v___x_142_ = v___x_96_;
v_isShared_143_ = v_isSharedCheck_147_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_a_140_);
lean_dec(v___x_96_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_147_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v___x_145_; 
if (v_isShared_143_ == 0)
{
v___x_145_ = v___x_142_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_a_140_);
v___x_145_ = v_reuseFailAlloc_146_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
return v___x_145_;
}
}
}
}
else
{
lean_dec(v___x_91_);
lean_dec(v___y_87_);
lean_dec(v___y_86_);
lean_dec_ref(v___y_85_);
lean_dec_ref(v___y_83_);
return v___x_92_;
}
}
v___jp_148_:
{
lean_object* v___x_150_; 
v___x_150_ = l_Lean_readModuleDataParts(v_fnames_149_);
lean_dec_ref(v_fnames_149_);
if (lean_obj_tag(v___x_150_) == 0)
{
lean_object* v_a_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_168_; 
v_a_151_ = lean_ctor_get(v___x_150_, 0);
v_isSharedCheck_168_ = !lean_is_exclusive(v___x_150_);
if (v_isSharedCheck_168_ == 0)
{
v___x_153_ = v___x_150_;
v_isShared_154_ = v_isSharedCheck_168_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_a_151_);
lean_dec(v___x_150_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_168_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_155_; lean_object* v___x_156_; uint8_t v___x_157_; 
v___x_155_ = lean_array_get_size(v_a_151_);
v___x_156_ = lean_unsigned_to_nat(0u);
v___x_157_ = lean_nat_dec_eq(v___x_155_, v___x_156_);
if (v___x_157_ == 0)
{
lean_object* v___x_158_; lean_object* v_fst_159_; lean_object* v_imports_160_; uint8_t v___x_161_; lean_object* v___x_162_; uint8_t v___x_163_; 
lean_del_object(v___x_153_);
v___x_158_ = lean_array_fget_borrowed(v_a_151_, v___x_156_);
v_fst_159_ = lean_ctor_get(v___x_158_, 0);
v_imports_160_ = lean_ctor_get(v_fst_159_, 0);
lean_inc_ref(v_imports_160_);
v___x_161_ = 2;
v___x_162_ = lean_box(1);
v___x_163_ = lean_uint8_once(&l_replayFromImports___closed__1, &l_replayFromImports___closed__1_once, _init_l_replayFromImports___closed__1);
if (v___x_163_ == 0)
{
v___y_82_ = v___x_157_;
v___y_83_ = v_a_151_;
v___y_84_ = v___x_161_;
v___y_85_ = v_imports_160_;
v___y_86_ = v___x_156_;
v___y_87_ = v___x_155_;
v___y_88_ = v___x_162_;
v___y_89_ = v___x_80_;
goto v___jp_81_;
}
else
{
v___y_82_ = v___x_157_;
v___y_83_ = v_a_151_;
v___y_84_ = v___x_161_;
v___y_85_ = v_imports_160_;
v___y_86_ = v___x_156_;
v___y_87_ = v___x_155_;
v___y_88_ = v___x_162_;
v___y_89_ = v___x_157_;
goto v___jp_81_;
}
}
else
{
lean_object* v___x_164_; lean_object* v___x_166_; 
lean_dec(v_a_151_);
v___x_164_ = ((lean_object*)(l_replayFromImports___closed__3));
if (v_isShared_154_ == 0)
{
lean_ctor_set_tag(v___x_153_, 1);
lean_ctor_set(v___x_153_, 0, v___x_164_);
v___x_166_ = v___x_153_;
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
v_a_169_ = lean_ctor_get(v___x_150_, 0);
v_isSharedCheck_176_ = !lean_is_exclusive(v___x_150_);
if (v_isSharedCheck_176_ == 0)
{
v___x_171_ = v___x_150_;
v_isShared_172_ = v_isSharedCheck_176_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_a_169_);
lean_dec(v___x_150_);
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
LEAN_EXPORT lean_object* l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00replayFromFresh_spec__0_spec__0_spec__1(lean_object* v_t_213_, lean_object* v_init_214_){
_start:
{
switch(lean_obj_tag(v_t_213_))
{
case 0:
{
lean_object* v_key_215_; lean_object* v_val_216_; lean_object* v___x_217_; 
v_key_215_ = lean_ctor_get(v_t_213_, 0);
lean_inc(v_key_215_);
v_val_216_ = lean_ctor_get(v_t_213_, 1);
lean_inc(v_val_216_);
lean_dec_ref_known(v_t_213_, 2);
v___x_217_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1___redArg(v_init_214_, v_key_215_, v_val_216_);
return v___x_217_;
}
case 1:
{
lean_object* v_children_218_; lean_object* v___x_219_; lean_object* v___x_220_; uint8_t v___x_221_; 
v_children_218_ = lean_ctor_get(v_t_213_, 1);
lean_inc_ref(v_children_218_);
lean_dec_ref_known(v_t_213_, 2);
v___x_219_ = lean_unsigned_to_nat(0u);
v___x_220_ = lean_array_get_size(v_children_218_);
v___x_221_ = lean_nat_dec_lt(v___x_219_, v___x_220_);
if (v___x_221_ == 0)
{
lean_dec_ref(v_children_218_);
return v_init_214_;
}
else
{
size_t v___x_222_; size_t v___x_223_; lean_object* v___x_224_; 
v___x_222_ = ((size_t)0ULL);
v___x_223_ = lean_usize_of_nat(v___x_220_);
v___x_224_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1_spec__2___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00replayFromFresh_spec__0_spec__0_spec__1_spec__2(v_children_218_, v___x_222_, v___x_223_, v_init_214_);
lean_dec_ref(v_children_218_);
return v___x_224_;
}
}
default: 
{
lean_object* v_key_225_; lean_object* v_val_226_; lean_object* v_children_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; uint8_t v___x_231_; 
v_key_225_ = lean_ctor_get(v_t_213_, 0);
lean_inc(v_key_225_);
v_val_226_ = lean_ctor_get(v_t_213_, 1);
lean_inc(v_val_226_);
v_children_227_ = lean_ctor_get(v_t_213_, 2);
lean_inc_ref(v_children_227_);
lean_dec_ref_known(v_t_213_, 3);
v___x_228_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1___redArg(v_init_214_, v_key_225_, v_val_226_);
v___x_229_ = lean_unsigned_to_nat(0u);
v___x_230_ = lean_array_get_size(v_children_227_);
v___x_231_ = lean_nat_dec_lt(v___x_229_, v___x_230_);
if (v___x_231_ == 0)
{
lean_dec_ref(v_children_227_);
return v___x_228_;
}
else
{
size_t v___x_232_; size_t v___x_233_; lean_object* v___x_234_; 
v___x_232_ = ((size_t)0ULL);
v___x_233_ = lean_usize_of_nat(v___x_230_);
v___x_234_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1_spec__2___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00replayFromFresh_spec__0_spec__0_spec__1_spec__2(v_children_227_, v___x_232_, v___x_233_, v___x_228_);
lean_dec_ref(v_children_227_);
return v___x_234_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1_spec__2___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00replayFromFresh_spec__0_spec__0_spec__1_spec__2(lean_object* v_as_235_, size_t v_i_236_, size_t v_stop_237_, lean_object* v_b_238_){
_start:
{
uint8_t v___x_239_; 
v___x_239_ = lean_usize_dec_eq(v_i_236_, v_stop_237_);
if (v___x_239_ == 0)
{
lean_object* v___x_240_; lean_object* v___x_241_; size_t v___x_242_; size_t v___x_243_; 
v___x_240_ = lean_array_uget_borrowed(v_as_235_, v_i_236_);
lean_inc(v___x_240_);
v___x_241_ = l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00replayFromFresh_spec__0_spec__0_spec__1(v___x_240_, v_b_238_);
v___x_242_ = ((size_t)1ULL);
v___x_243_ = lean_usize_add(v_i_236_, v___x_242_);
v_i_236_ = v___x_243_;
v_b_238_ = v___x_241_;
goto _start;
}
else
{
return v_b_238_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1_spec__2___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00replayFromFresh_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_as_245_, lean_object* v_i_246_, lean_object* v_stop_247_, lean_object* v_b_248_){
_start:
{
size_t v_i_boxed_249_; size_t v_stop_boxed_250_; lean_object* v_res_251_; 
v_i_boxed_249_ = lean_unbox_usize(v_i_246_);
lean_dec(v_i_246_);
v_stop_boxed_250_ = lean_unbox_usize(v_stop_247_);
lean_dec(v_stop_247_);
v_res_251_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1_spec__2___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00replayFromFresh_spec__0_spec__0_spec__1_spec__2(v_as_245_, v_i_boxed_249_, v_stop_boxed_250_, v_b_248_);
lean_dec_ref(v_as_245_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00replayFromFresh_spec__0_spec__0(lean_object* v_t_252_, lean_object* v_init_253_){
_start:
{
switch(lean_obj_tag(v_t_252_))
{
case 0:
{
lean_object* v_tree_254_; lean_object* v___x_255_; 
v_tree_254_ = lean_ctor_get(v_t_252_, 1);
lean_inc_ref(v_tree_254_);
lean_dec_ref_known(v_t_252_, 2);
v___x_255_ = l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00replayFromFresh_spec__0_spec__0_spec__1(v_tree_254_, v_init_253_);
return v___x_255_;
}
case 1:
{
lean_object* v_key_256_; lean_object* v_entry_x3f_257_; lean_object* v_children_258_; lean_object* v_s_260_; 
v_key_256_ = lean_ctor_get(v_t_252_, 0);
lean_inc(v_key_256_);
v_entry_x3f_257_ = lean_ctor_get(v_t_252_, 1);
lean_inc(v_entry_x3f_257_);
v_children_258_ = lean_ctor_get(v_t_252_, 2);
lean_inc_ref(v_children_258_);
lean_dec_ref_known(v_t_252_, 3);
if (lean_obj_tag(v_entry_x3f_257_) == 1)
{
lean_object* v_val_267_; lean_object* v_fst_268_; lean_object* v___x_269_; 
v_val_267_ = lean_ctor_get(v_entry_x3f_257_, 0);
lean_inc(v_val_267_);
lean_dec_ref_known(v_entry_x3f_257_, 1);
v_fst_268_ = lean_ctor_get(v_val_267_, 0);
lean_inc(v_fst_268_);
lean_dec(v_val_267_);
v___x_269_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1___redArg(v_init_253_, v_key_256_, v_fst_268_);
v_s_260_ = v___x_269_;
goto v___jp_259_;
}
else
{
lean_dec(v_entry_x3f_257_);
lean_dec(v_key_256_);
v_s_260_ = v_init_253_;
goto v___jp_259_;
}
v___jp_259_:
{
lean_object* v___x_261_; lean_object* v___x_262_; uint8_t v___x_263_; 
v___x_261_ = lean_unsigned_to_nat(0u);
v___x_262_ = lean_array_get_size(v_children_258_);
v___x_263_ = lean_nat_dec_lt(v___x_261_, v___x_262_);
if (v___x_263_ == 0)
{
lean_dec_ref(v_children_258_);
return v_s_260_;
}
else
{
size_t v___x_264_; size_t v___x_265_; lean_object* v___x_266_; 
v___x_264_ = ((size_t)0ULL);
v___x_265_ = lean_usize_of_nat(v___x_262_);
v___x_266_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__2___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00replayFromFresh_spec__0_spec__0_spec__2(v_children_258_, v___x_264_, v___x_265_, v_s_260_);
lean_dec_ref(v_children_258_);
return v___x_266_;
}
}
}
default: 
{
lean_object* v_key_270_; lean_object* v_entry_x3f_271_; lean_object* v_children_272_; lean_object* v_s_274_; 
v_key_270_ = lean_ctor_get(v_t_252_, 0);
lean_inc(v_key_270_);
v_entry_x3f_271_ = lean_ctor_get(v_t_252_, 1);
lean_inc(v_entry_x3f_271_);
v_children_272_ = lean_ctor_get(v_t_252_, 2);
lean_inc_ref(v_children_272_);
lean_dec_ref_known(v_t_252_, 3);
if (lean_obj_tag(v_entry_x3f_271_) == 1)
{
lean_object* v_val_282_; lean_object* v_fst_283_; lean_object* v___x_284_; 
v_val_282_ = lean_ctor_get(v_entry_x3f_271_, 0);
lean_inc(v_val_282_);
lean_dec_ref_known(v_entry_x3f_271_, 1);
v_fst_283_ = lean_ctor_get(v_val_282_, 0);
lean_inc(v_fst_283_);
lean_dec(v_val_282_);
v___x_284_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1___redArg(v_init_253_, v_key_270_, v_fst_283_);
v_s_274_ = v___x_284_;
goto v___jp_273_;
}
else
{
lean_dec(v_entry_x3f_271_);
lean_dec(v_key_270_);
v_s_274_ = v_init_253_;
goto v___jp_273_;
}
v___jp_273_:
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; uint8_t v___x_278_; 
v___x_275_ = lean_thunk_get_own(v_children_272_);
lean_dec_ref(v_children_272_);
v___x_276_ = lean_unsigned_to_nat(0u);
v___x_277_ = lean_array_get_size(v___x_275_);
v___x_278_ = lean_nat_dec_lt(v___x_276_, v___x_277_);
if (v___x_278_ == 0)
{
lean_dec(v___x_275_);
return v_s_274_;
}
else
{
size_t v___x_279_; size_t v___x_280_; lean_object* v___x_281_; 
v___x_279_ = ((size_t)0ULL);
v___x_280_ = lean_usize_of_nat(v___x_277_);
v___x_281_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__2___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00replayFromFresh_spec__0_spec__0_spec__2(v___x_275_, v___x_279_, v___x_280_, v_s_274_);
lean_dec(v___x_275_);
return v___x_281_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__2___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00replayFromFresh_spec__0_spec__0_spec__2(lean_object* v_as_285_, size_t v_i_286_, size_t v_stop_287_, lean_object* v_b_288_){
_start:
{
uint8_t v___x_289_; 
v___x_289_ = lean_usize_dec_eq(v_i_286_, v_stop_287_);
if (v___x_289_ == 0)
{
lean_object* v___x_290_; lean_object* v___x_291_; size_t v___x_292_; size_t v___x_293_; 
v___x_290_ = lean_array_uget_borrowed(v_as_285_, v_i_286_);
lean_inc(v___x_290_);
v___x_291_ = l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00replayFromFresh_spec__0_spec__0(v___x_290_, v_b_288_);
v___x_292_ = ((size_t)1ULL);
v___x_293_ = lean_usize_add(v_i_286_, v___x_292_);
v_i_286_ = v___x_293_;
v_b_288_ = v___x_291_;
goto _start;
}
else
{
return v_b_288_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__2___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00replayFromFresh_spec__0_spec__0_spec__2___boxed(lean_object* v_as_295_, lean_object* v_i_296_, lean_object* v_stop_297_, lean_object* v_b_298_){
_start:
{
size_t v_i_boxed_299_; size_t v_stop_boxed_300_; lean_object* v_res_301_; 
v_i_boxed_299_ = lean_unbox_usize(v_i_296_);
lean_dec(v_i_296_);
v_stop_boxed_300_ = lean_unbox_usize(v_stop_297_);
lean_dec(v_stop_297_);
v_res_301_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__2___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00replayFromFresh_spec__0_spec__0_spec__2(v_as_295_, v_i_boxed_299_, v_stop_boxed_300_, v_b_298_);
lean_dec_ref(v_as_295_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00replayFromFresh_spec__0(lean_object* v_t_302_, lean_object* v_init_303_){
_start:
{
lean_object* v_tree_304_; lean_object* v___x_305_; 
v_tree_304_ = lean_ctor_get(v_t_302_, 1);
lean_inc_ref(v_tree_304_);
lean_dec_ref(v_t_302_);
v___x_305_ = l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00replayFromFresh_spec__0_spec__0(v_tree_304_, v_init_303_);
return v___x_305_;
}
}
static lean_object* _init_l_replayFromFresh___lam__0___closed__0(void){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_306_ = lean_obj_once(&l_replayFromImports___closed__0, &l_replayFromImports___closed__0_once, _init_l_replayFromImports___closed__0);
v___x_307_ = lean_unsigned_to_nat(0u);
v___x_308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_308_, 0, v___x_307_);
lean_ctor_set(v___x_308_, 1, v___x_306_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_replayFromFresh___lam__0(lean_object* v_env_309_){
_start:
{
lean_object* v___x_311_; lean_object* v_map_u2081_312_; lean_object* v___x_313_; lean_object* v_imported_314_; uint32_t v___x_315_; lean_object* v___x_316_; 
v___x_311_ = l_Lean_Environment_constants(v_env_309_);
v_map_u2081_312_ = lean_ctor_get(v___x_311_, 0);
lean_inc_ref(v_map_u2081_312_);
lean_dec_ref(v___x_311_);
v___x_313_ = lean_obj_once(&l_replayFromFresh___lam__0___closed__0, &l_replayFromFresh___lam__0___closed__0_once, _init_l_replayFromFresh___lam__0___closed__0);
v_imported_314_ = l_Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00replayFromFresh_spec__0(v_map_u2081_312_, v___x_313_);
v___x_315_ = 0;
v___x_316_ = l_Lean_mkEmptyEnvironment(v___x_315_);
if (lean_obj_tag(v___x_316_) == 0)
{
lean_object* v_a_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v_a_317_ = lean_ctor_get(v___x_316_, 0);
lean_inc(v_a_317_);
lean_dec_ref_known(v___x_316_, 1);
v___x_318_ = lean_elab_environment_to_kernel_env(v_a_317_);
v___x_319_ = lean_box(0);
v___x_320_ = l_Lean_Kernel_Environment_replay(v_imported_314_, v___x_318_);
lean_dec_ref(v_imported_314_);
if (lean_obj_tag(v___x_320_) == 0)
{
lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_327_; 
v_isSharedCheck_327_ = !lean_is_exclusive(v___x_320_);
if (v_isSharedCheck_327_ == 0)
{
lean_object* v_unused_328_; 
v_unused_328_ = lean_ctor_get(v___x_320_, 0);
lean_dec(v_unused_328_);
v___x_322_ = v___x_320_;
v_isShared_323_ = v_isSharedCheck_327_;
goto v_resetjp_321_;
}
else
{
lean_dec(v___x_320_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_327_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v___x_325_; 
if (v_isShared_323_ == 0)
{
lean_ctor_set(v___x_322_, 0, v___x_319_);
v___x_325_ = v___x_322_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v___x_319_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
}
else
{
lean_object* v_a_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_336_; 
v_a_329_ = lean_ctor_get(v___x_320_, 0);
v_isSharedCheck_336_ = !lean_is_exclusive(v___x_320_);
if (v_isSharedCheck_336_ == 0)
{
v___x_331_ = v___x_320_;
v_isShared_332_ = v_isSharedCheck_336_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_a_329_);
lean_dec(v___x_320_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_336_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_334_; 
if (v_isShared_332_ == 0)
{
v___x_334_ = v___x_331_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v_a_329_);
v___x_334_ = v_reuseFailAlloc_335_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
return v___x_334_;
}
}
}
}
else
{
lean_object* v_a_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_344_; 
lean_dec_ref(v_imported_314_);
v_a_337_ = lean_ctor_get(v___x_316_, 0);
v_isSharedCheck_344_ = !lean_is_exclusive(v___x_316_);
if (v_isSharedCheck_344_ == 0)
{
v___x_339_ = v___x_316_;
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_a_337_);
lean_dec(v___x_316_);
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
LEAN_EXPORT lean_object* l_replayFromFresh___lam__0___boxed(lean_object* v_env_345_, lean_object* v___y_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_replayFromFresh___lam__0(v_env_345_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l_replayFromFresh(lean_object* v_module_349_){
_start:
{
lean_object* v___f_351_; uint8_t v___x_352_; uint8_t v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; uint32_t v___x_359_; lean_object* v___x_360_; 
v___f_351_ = ((lean_object*)(l_replayFromFresh___closed__0));
v___x_352_ = 0;
v___x_353_ = 1;
v___x_354_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_354_, 0, v_module_349_);
lean_ctor_set_uint8(v___x_354_, sizeof(void*)*1, v___x_352_);
lean_ctor_set_uint8(v___x_354_, sizeof(void*)*1 + 1, v___x_353_);
lean_ctor_set_uint8(v___x_354_, sizeof(void*)*1 + 2, v___x_352_);
v___x_355_ = lean_unsigned_to_nat(1u);
v___x_356_ = lean_mk_empty_array_with_capacity(v___x_355_);
v___x_357_ = lean_array_push(v___x_356_, v___x_354_);
v___x_358_ = l_Lean_Options_empty;
v___x_359_ = 0;
v___x_360_ = l_Lean_withImportModules___redArg(v___x_357_, v___x_358_, v___f_351_, v___x_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_replayFromFresh___boxed(lean_object* v_module_361_, lean_object* v_a_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_replayFromFresh(v_module_361_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_getCurrentModule(){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = ((lean_object*)(l_getCurrentModule___closed__0));
v___x_367_ = l_Lake_Manifest_load_x3f(v___x_366_);
if (lean_obj_tag(v___x_367_) == 0)
{
lean_object* v_a_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_382_; 
v_a_368_ = lean_ctor_get(v___x_367_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_367_);
if (v_isSharedCheck_382_ == 0)
{
v___x_370_ = v___x_367_;
v_isShared_371_ = v_isSharedCheck_382_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_a_368_);
lean_dec(v___x_367_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_382_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
if (lean_obj_tag(v_a_368_) == 0)
{
lean_object* v___x_372_; lean_object* v___x_374_; 
v___x_372_ = lean_box(0);
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 0, v___x_372_);
v___x_374_ = v___x_370_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v___x_372_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
else
{
lean_object* v_val_376_; lean_object* v_name_377_; lean_object* v___x_378_; lean_object* v___x_380_; 
v_val_376_ = lean_ctor_get(v_a_368_, 0);
lean_inc(v_val_376_);
lean_dec_ref_known(v_a_368_, 1);
v_name_377_ = lean_ctor_get(v_val_376_, 0);
lean_inc(v_name_377_);
lean_dec(v_val_376_);
v___x_378_ = l_Lean_Name_capitalize(v_name_377_);
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 0, v___x_378_);
v___x_380_ = v___x_370_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v___x_378_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
}
else
{
lean_object* v_a_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_390_; 
v_a_383_ = lean_ctor_get(v___x_367_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_367_);
if (v_isSharedCheck_390_ == 0)
{
v___x_385_ = v___x_367_;
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_a_383_);
lean_dec(v___x_367_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_388_; 
if (v_isShared_386_ == 0)
{
v___x_388_ = v___x_385_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_a_383_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_getCurrentModule___boxed(lean_object* v_a_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_getCurrentModule();
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkExport_spec__1___redArg(lean_object* v___x_395_, lean_object* v_a_396_, lean_object* v_as_x27_397_, lean_object* v_b_398_){
_start:
{
if (lean_obj_tag(v_as_x27_397_) == 0)
{
lean_object* v___x_400_; 
lean_dec_ref(v_a_396_);
v___x_400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_400_, 0, v_b_398_);
return v___x_400_;
}
else
{
lean_object* v_head_401_; lean_object* v_tail_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v_head_401_ = lean_ctor_get(v_as_x27_397_, 0);
v_tail_402_ = lean_ctor_get(v_as_x27_397_, 1);
v___x_403_ = lean_box(0);
v___x_404_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Lemmas______macroRules__Std__DTreeMap__Internal__Impl__tacticSimp__to__model_x5b___x5dUsing____1_spec__1___redArg(v___x_395_, v_head_401_);
if (lean_obj_tag(v___x_404_) == 1)
{
lean_object* v_val_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_435_; 
v_val_405_ = lean_ctor_get(v___x_404_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v___x_404_);
if (v_isSharedCheck_435_ == 0)
{
v___x_407_ = v___x_404_;
v_isShared_408_ = v_isSharedCheck_435_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_val_405_);
lean_dec(v___x_404_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_435_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_409_; 
lean_inc(v_head_401_);
lean_inc_ref(v_a_396_);
v___x_409_ = lean_environment_find(v_a_396_, v_head_401_);
if (lean_obj_tag(v___x_409_) == 1)
{
lean_object* v_val_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_426_; 
v_val_410_ = lean_ctor_get(v___x_409_, 0);
v_isSharedCheck_426_ = !lean_is_exclusive(v___x_409_);
if (v_isSharedCheck_426_ == 0)
{
v___x_412_ = v___x_409_;
v_isShared_413_ = v_isSharedCheck_426_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_val_410_);
lean_dec(v___x_409_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_426_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
uint8_t v___x_414_; 
v___x_414_ = l_Lean_instBEqConstantInfo_beq(v_val_405_, v_val_410_);
lean_dec(v_val_410_);
lean_dec(v_val_405_);
if (v___x_414_ == 0)
{
uint8_t v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_420_; 
lean_dec_ref(v_a_396_);
v___x_415_ = 1;
v___x_416_ = ((lean_object*)(l_List_forIn_x27_loop___at___00checkExport_spec__1___redArg___closed__0));
lean_inc(v_head_401_);
v___x_417_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_401_, v___x_415_);
v___x_418_ = lean_string_append(v___x_416_, v___x_417_);
lean_dec_ref(v___x_417_);
if (v_isShared_413_ == 0)
{
lean_ctor_set_tag(v___x_412_, 18);
lean_ctor_set(v___x_412_, 0, v___x_418_);
v___x_420_ = v___x_412_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v___x_418_);
v___x_420_ = v_reuseFailAlloc_424_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
lean_object* v___x_422_; 
if (v_isShared_408_ == 0)
{
lean_ctor_set(v___x_407_, 0, v___x_420_);
v___x_422_ = v___x_407_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v___x_420_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
return v___x_422_;
}
}
}
else
{
lean_del_object(v___x_412_);
lean_del_object(v___x_407_);
v_as_x27_397_ = v_tail_402_;
v_b_398_ = v___x_403_;
goto _start;
}
}
}
else
{
lean_object* v___x_427_; uint8_t v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_432_; 
lean_dec(v___x_409_);
lean_dec(v_val_405_);
lean_dec_ref(v_a_396_);
v___x_427_ = ((lean_object*)(l_List_forIn_x27_loop___at___00checkExport_spec__1___redArg___closed__1));
v___x_428_ = 1;
lean_inc(v_head_401_);
v___x_429_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_401_, v___x_428_);
v___x_430_ = lean_string_append(v___x_427_, v___x_429_);
lean_dec_ref(v___x_429_);
if (v_isShared_408_ == 0)
{
lean_ctor_set_tag(v___x_407_, 18);
lean_ctor_set(v___x_407_, 0, v___x_430_);
v___x_432_ = v___x_407_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v___x_430_);
v___x_432_ = v_reuseFailAlloc_434_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
lean_object* v___x_433_; 
v___x_433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_433_, 0, v___x_432_);
return v___x_433_;
}
}
}
}
else
{
lean_dec(v___x_404_);
v_as_x27_397_ = v_tail_402_;
v_b_398_ = v___x_403_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkExport_spec__1___redArg___boxed(lean_object* v___x_437_, lean_object* v_a_438_, lean_object* v_as_x27_439_, lean_object* v_b_440_, lean_object* v___y_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_List_forIn_x27_loop___at___00checkExport_spec__1___redArg(v___x_437_, v_a_438_, v_as_x27_439_, v_b_440_);
lean_dec(v_as_x27_439_);
lean_dec_ref(v___x_437_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00checkExport_spec__0(lean_object* v_x_443_, lean_object* v_x_444_){
_start:
{
if (lean_obj_tag(v_x_444_) == 0)
{
return v_x_443_;
}
else
{
lean_object* v_head_445_; lean_object* v_tail_446_; lean_object* v___x_447_; 
v_head_445_ = lean_ctor_get(v_x_444_, 0);
v_tail_446_ = lean_ctor_get(v_x_444_, 1);
v___x_447_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg(v_x_443_, v_head_445_);
v_x_443_ = v___x_447_;
v_x_444_ = v_tail_446_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00checkExport_spec__0___boxed(lean_object* v_x_449_, lean_object* v_x_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_List_foldl___at___00checkExport_spec__0(v_x_449_, v_x_450_);
lean_dec(v_x_450_);
return v_res_451_;
}
}
static lean_object* _init_l_checkExport___boxed__const__1(void){
_start:
{
uint32_t v___x_483_; lean_object* v___x_484_; 
v___x_483_ = 1;
v___x_484_ = lean_box_uint32(v___x_483_);
return v___x_484_;
}
}
static lean_object* _init_l_checkExport___boxed__const__2(void){
_start:
{
uint32_t v___x_485_; lean_object* v___x_486_; 
v___x_485_ = 0;
v___x_486_ = lean_box_uint32(v___x_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_checkExport(lean_object* v_args_487_, uint8_t v_silent_488_){
_start:
{
lean_object* v_a_497_; 
if (lean_obj_tag(v_args_487_) == 1)
{
lean_object* v_tail_519_; 
v_tail_519_ = lean_ctor_get(v_args_487_, 1);
if (lean_obj_tag(v_tail_519_) == 0)
{
lean_object* v_head_520_; uint8_t v___x_521_; lean_object* v___x_522_; 
v_head_520_ = lean_ctor_get(v_args_487_, 0);
v___x_521_ = 0;
v___x_522_ = lean_io_prim_handle_mk(v_head_520_, v___x_521_);
if (lean_obj_tag(v___x_522_) == 0)
{
lean_object* v_a_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v_a_523_ = lean_ctor_get(v___x_522_, 0);
lean_inc(v_a_523_);
lean_dec_ref_known(v___x_522_, 1);
v___x_524_ = lean_stream_of_handle(v_a_523_);
v___x_525_ = l_LeanExport_parseStream(v___x_524_);
if (lean_obj_tag(v___x_525_) == 0)
{
lean_object* v_a_526_; uint32_t v___x_527_; lean_object* v___x_528_; 
v_a_526_ = lean_ctor_get(v___x_525_, 0);
lean_inc(v_a_526_);
lean_dec_ref_known(v___x_525_, 1);
v___x_527_ = 0;
v___x_528_ = l_Lean_mkEmptyEnvironment(v___x_527_);
if (lean_obj_tag(v___x_528_) == 0)
{
lean_object* v_a_529_; lean_object* v_constMap_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v_a_529_ = lean_ctor_get(v___x_528_, 0);
lean_inc(v_a_529_);
lean_dec_ref_known(v___x_528_, 1);
v_constMap_530_ = lean_ctor_get(v_a_526_, 0);
lean_inc_ref_n(v_constMap_530_, 2);
lean_dec(v_a_526_);
v___x_531_ = lean_elab_environment_to_kernel_env(v_a_529_);
v___x_532_ = ((lean_object*)(l_checkExport___closed__11));
v___x_533_ = l_List_foldl___at___00checkExport_spec__0(v_constMap_530_, v___x_532_);
v___x_534_ = l_Lean_Kernel_Environment_replay(v___x_533_, v___x_531_);
lean_dec_ref(v___x_533_);
if (lean_obj_tag(v___x_534_) == 0)
{
lean_object* v_a_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v_a_535_ = lean_ctor_get(v___x_534_, 0);
lean_inc(v_a_535_);
lean_dec_ref_known(v___x_534_, 1);
v___x_536_ = ((lean_object*)(l_checkExport___closed__12));
v___x_537_ = l_println(v___x_536_, v_silent_488_);
if (lean_obj_tag(v___x_537_) == 0)
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
lean_dec_ref_known(v___x_537_, 1);
v___x_538_ = ((lean_object*)(l_checkExport___closed__14));
v___x_539_ = lean_box(0);
v___x_540_ = l_List_forIn_x27_loop___at___00checkExport_spec__1___redArg(v_constMap_530_, v_a_535_, v___x_538_, v___x_539_);
lean_dec_ref(v_constMap_530_);
if (lean_obj_tag(v___x_540_) == 0)
{
lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_548_; 
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_540_);
if (v_isSharedCheck_548_ == 0)
{
lean_object* v_unused_549_; 
v_unused_549_ = lean_ctor_get(v___x_540_, 0);
lean_dec(v_unused_549_);
v___x_542_ = v___x_540_;
v_isShared_543_ = v_isSharedCheck_548_;
goto v_resetjp_541_;
}
else
{
lean_dec(v___x_540_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_548_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_544_; lean_object* v___x_546_; 
v___x_544_ = l_checkExport___boxed__const__2;
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 0, v___x_544_);
v___x_546_ = v___x_542_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v___x_544_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
else
{
lean_object* v_a_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
v_a_550_ = lean_ctor_get(v___x_540_, 0);
lean_inc(v_a_550_);
lean_dec_ref_known(v___x_540_, 1);
v___x_551_ = ((lean_object*)(l_checkExport___closed__15));
v___x_552_ = lean_io_error_to_string(v_a_550_);
v___x_553_ = lean_string_append(v___x_551_, v___x_552_);
lean_dec_ref(v___x_552_);
v___x_554_ = l_println(v___x_553_, v_silent_488_);
if (lean_obj_tag(v___x_554_) == 0)
{
lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_562_; 
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_562_ == 0)
{
lean_object* v_unused_563_; 
v_unused_563_ = lean_ctor_get(v___x_554_, 0);
lean_dec(v_unused_563_);
v___x_556_ = v___x_554_;
v_isShared_557_ = v_isSharedCheck_562_;
goto v_resetjp_555_;
}
else
{
lean_dec(v___x_554_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_562_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_558_; lean_object* v___x_560_; 
v___x_558_ = l_checkExport___boxed__const__1;
if (v_isShared_557_ == 0)
{
lean_ctor_set(v___x_556_, 0, v___x_558_);
v___x_560_ = v___x_556_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v___x_558_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
}
else
{
lean_object* v_a_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_571_; 
v_a_564_ = lean_ctor_get(v___x_554_, 0);
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_571_ == 0)
{
v___x_566_ = v___x_554_;
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_a_564_);
lean_dec(v___x_554_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_569_; 
if (v_isShared_567_ == 0)
{
v___x_569_ = v___x_566_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_a_564_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
}
}
}
}
}
else
{
lean_object* v_a_572_; 
lean_dec(v_a_535_);
lean_dec_ref(v_constMap_530_);
v_a_572_ = lean_ctor_get(v___x_537_, 0);
lean_inc(v_a_572_);
lean_dec_ref_known(v___x_537_, 1);
v_a_497_ = v_a_572_;
goto v___jp_496_;
}
}
else
{
lean_object* v_a_573_; 
lean_dec_ref(v_constMap_530_);
v_a_573_ = lean_ctor_get(v___x_534_, 0);
lean_inc(v_a_573_);
lean_dec_ref_known(v___x_534_, 1);
v_a_497_ = v_a_573_;
goto v___jp_496_;
}
}
else
{
lean_object* v_a_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_581_; 
lean_dec(v_a_526_);
v_a_574_ = lean_ctor_get(v___x_528_, 0);
v_isSharedCheck_581_ = !lean_is_exclusive(v___x_528_);
if (v_isSharedCheck_581_ == 0)
{
v___x_576_ = v___x_528_;
v_isShared_577_ = v_isSharedCheck_581_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_a_574_);
lean_dec(v___x_528_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_581_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_579_; 
if (v_isShared_577_ == 0)
{
v___x_579_ = v___x_576_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v_a_574_);
v___x_579_ = v_reuseFailAlloc_580_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
return v___x_579_;
}
}
}
}
else
{
lean_object* v_a_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_589_; 
v_a_582_ = lean_ctor_get(v___x_525_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_589_ == 0)
{
v___x_584_ = v___x_525_;
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_a_582_);
lean_dec(v___x_525_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_587_; 
if (v_isShared_585_ == 0)
{
v___x_587_ = v___x_584_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_a_582_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
}
}
else
{
lean_object* v_a_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_597_; 
v_a_590_ = lean_ctor_get(v___x_522_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_597_ == 0)
{
v___x_592_ = v___x_522_;
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_a_590_);
lean_dec(v___x_522_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_595_; 
if (v_isShared_593_ == 0)
{
v___x_595_ = v___x_592_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_a_590_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
}
}
else
{
goto v___jp_490_;
}
}
else
{
goto v___jp_490_;
}
v___jp_490_:
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_491_ = ((lean_object*)(l_checkExport___closed__0));
v___x_492_ = l_List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1(v_args_487_);
v___x_493_ = lean_string_append(v___x_491_, v___x_492_);
lean_dec_ref(v___x_492_);
v___x_494_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_494_, 0, v___x_493_);
v___x_495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
return v___x_495_;
}
v___jp_496_:
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_498_ = ((lean_object*)(l_checkExport___closed__1));
v___x_499_ = lean_io_error_to_string(v_a_497_);
v___x_500_ = lean_string_append(v___x_498_, v___x_499_);
lean_dec_ref(v___x_499_);
v___x_501_ = l_println(v___x_500_, v_silent_488_);
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_509_; 
v_isSharedCheck_509_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_509_ == 0)
{
lean_object* v_unused_510_; 
v_unused_510_ = lean_ctor_get(v___x_501_, 0);
lean_dec(v_unused_510_);
v___x_503_ = v___x_501_;
v_isShared_504_ = v_isSharedCheck_509_;
goto v_resetjp_502_;
}
else
{
lean_dec(v___x_501_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_509_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_505_; lean_object* v___x_507_; 
v___x_505_ = l_checkExport___boxed__const__1;
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 0, v___x_505_);
v___x_507_ = v___x_503_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v___x_505_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
}
else
{
lean_object* v_a_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_518_; 
v_a_511_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_518_ == 0)
{
v___x_513_ = v___x_501_;
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_a_511_);
lean_dec(v___x_501_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_516_; 
if (v_isShared_514_ == 0)
{
v___x_516_ = v___x_513_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_a_511_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_checkExport___boxed(lean_object* v_args_598_, lean_object* v_silent_599_, lean_object* v_a_600_){
_start:
{
uint8_t v_silent_boxed_601_; lean_object* v_res_602_; 
v_silent_boxed_601_ = lean_unbox(v_silent_599_);
v_res_602_ = l_checkExport(v_args_598_, v_silent_boxed_601_);
lean_dec(v_args_598_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkExport_spec__1(lean_object* v___x_603_, lean_object* v_a_604_, lean_object* v_as_605_, lean_object* v_as_x27_606_, lean_object* v_b_607_, lean_object* v_a_608_){
_start:
{
lean_object* v___x_610_; 
v___x_610_ = l_List_forIn_x27_loop___at___00checkExport_spec__1___redArg(v___x_603_, v_a_604_, v_as_x27_606_, v_b_607_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkExport_spec__1___boxed(lean_object* v___x_611_, lean_object* v_a_612_, lean_object* v_as_613_, lean_object* v_as_x27_614_, lean_object* v_b_615_, lean_object* v_a_616_, lean_object* v___y_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_List_forIn_x27_loop___at___00checkExport_spec__1(v___x_611_, v_a_612_, v_as_613_, v_as_x27_614_, v_b_615_, v_a_616_);
lean_dec(v_as_x27_614_);
lean_dec(v_as_613_);
lean_dec_ref(v___x_611_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00checkOlean_spec__3(uint8_t v_verbose_621_, uint8_t v_silent_622_, lean_object* v_as_623_, size_t v_sz_624_, size_t v_i_625_, lean_object* v_b_626_){
_start:
{
uint8_t v___x_628_; 
v___x_628_ = lean_usize_dec_lt(v_i_625_, v_sz_624_);
if (v___x_628_ == 0)
{
lean_object* v___x_629_; 
v___x_629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_629_, 0, v_b_626_);
return v___x_629_;
}
else
{
lean_object* v_a_630_; lean_object* v_fst_631_; lean_object* v_snd_632_; lean_object* v___x_633_; 
v_a_630_ = lean_array_uget_borrowed(v_as_623_, v_i_625_);
v_fst_631_ = lean_ctor_get(v_a_630_, 0);
v_snd_632_ = lean_ctor_get(v_a_630_, 1);
v___x_633_ = lean_box(0);
if (v_verbose_621_ == 0)
{
goto v___jp_634_;
}
else
{
lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_652_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00checkOlean_spec__3___closed__1));
lean_inc(v_fst_631_);
v___x_653_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_631_, v_verbose_621_);
v___x_654_ = lean_string_append(v___x_652_, v___x_653_);
lean_dec_ref(v___x_653_);
v___x_655_ = l_println(v___x_654_, v_silent_622_);
if (lean_obj_tag(v___x_655_) == 0)
{
lean_dec_ref_known(v___x_655_, 1);
goto v___jp_634_;
}
else
{
return v___x_655_;
}
}
v___jp_634_:
{
lean_object* v___x_635_; 
lean_inc(v_snd_632_);
v___x_635_ = lean_task_get_own(v_snd_632_);
if (lean_obj_tag(v___x_635_) == 0)
{
lean_object* v_a_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v_a_636_ = lean_ctor_get(v___x_635_, 0);
lean_inc(v_a_636_);
lean_dec_ref_known(v___x_635_, 1);
v___x_637_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00checkOlean_spec__3___closed__0));
lean_inc(v_fst_631_);
v___x_638_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_631_, v___x_628_);
v___x_639_ = lean_string_append(v___x_637_, v___x_638_);
lean_dec_ref(v___x_638_);
v___x_640_ = l_IO_eprintln___at___00__private_Init_System_IO_0__IO_eprintlnAux_spec__0(v___x_639_);
if (lean_obj_tag(v___x_640_) == 0)
{
lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_647_; 
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_640_);
if (v_isSharedCheck_647_ == 0)
{
lean_object* v_unused_648_; 
v_unused_648_ = lean_ctor_get(v___x_640_, 0);
lean_dec(v_unused_648_);
v___x_642_ = v___x_640_;
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
else
{
lean_dec(v___x_640_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_645_; 
if (v_isShared_643_ == 0)
{
lean_ctor_set_tag(v___x_642_, 1);
lean_ctor_set(v___x_642_, 0, v_a_636_);
v___x_645_ = v___x_642_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_a_636_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
else
{
lean_dec(v_a_636_);
return v___x_640_;
}
}
else
{
size_t v___x_649_; size_t v___x_650_; 
lean_dec(v___x_635_);
v___x_649_ = ((size_t)1ULL);
v___x_650_ = lean_usize_add(v_i_625_, v___x_649_);
v_i_625_ = v___x_650_;
v_b_626_ = v___x_633_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00checkOlean_spec__3___boxed(lean_object* v_verbose_656_, lean_object* v_silent_657_, lean_object* v_as_658_, lean_object* v_sz_659_, lean_object* v_i_660_, lean_object* v_b_661_, lean_object* v___y_662_){
_start:
{
uint8_t v_verbose_boxed_663_; uint8_t v_silent_boxed_664_; size_t v_sz_boxed_665_; size_t v_i_boxed_666_; lean_object* v_res_667_; 
v_verbose_boxed_663_ = lean_unbox(v_verbose_656_);
v_silent_boxed_664_ = lean_unbox(v_silent_657_);
v_sz_boxed_665_ = lean_unbox_usize(v_sz_659_);
lean_dec(v_sz_659_);
v_i_boxed_666_ = lean_unbox_usize(v_i_660_);
lean_dec(v_i_660_);
v_res_667_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00checkOlean_spec__3(v_verbose_boxed_663_, v_silent_boxed_664_, v_as_658_, v_sz_boxed_665_, v_i_boxed_666_, v_b_661_);
lean_dec_ref(v_as_658_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__2___redArg___lam__0(lean_object* v_head_668_){
_start:
{
lean_object* v___x_670_; 
v___x_670_ = l_replayFromImports(v_head_668_);
if (lean_obj_tag(v___x_670_) == 0)
{
lean_object* v_a_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_678_; 
v_a_671_ = lean_ctor_get(v___x_670_, 0);
v_isSharedCheck_678_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_678_ == 0)
{
v___x_673_ = v___x_670_;
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_a_671_);
lean_dec(v___x_670_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_676_; 
if (v_isShared_674_ == 0)
{
lean_ctor_set_tag(v___x_673_, 1);
v___x_676_ = v___x_673_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_a_671_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
}
else
{
lean_object* v_a_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_686_; 
v_a_679_ = lean_ctor_get(v___x_670_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_686_ == 0)
{
v___x_681_ = v___x_670_;
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_a_679_);
lean_dec(v___x_670_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_684_; 
if (v_isShared_682_ == 0)
{
lean_ctor_set_tag(v___x_681_, 0);
v___x_684_ = v___x_681_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_a_679_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__2___redArg___lam__0___boxed(lean_object* v_head_687_, lean_object* v___y_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_List_forIn_x27_loop___at___00checkOlean_spec__2___redArg___lam__0(v_head_687_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__2___redArg(lean_object* v_as_x27_690_, lean_object* v_b_691_){
_start:
{
if (lean_obj_tag(v_as_x27_690_) == 0)
{
lean_object* v___x_693_; 
v___x_693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_693_, 0, v_b_691_);
return v___x_693_;
}
else
{
lean_object* v_head_694_; lean_object* v_tail_695_; lean_object* v___f_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v_head_694_ = lean_ctor_get(v_as_x27_690_, 0);
v_tail_695_ = lean_ctor_get(v_as_x27_690_, 1);
lean_inc_n(v_head_694_, 2);
v___f_696_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00checkOlean_spec__2___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_696_, 0, v_head_694_);
v___x_697_ = lean_unsigned_to_nat(0u);
v___x_698_ = lean_io_as_task(v___f_696_, v___x_697_);
v___x_699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_699_, 0, v_head_694_);
lean_ctor_set(v___x_699_, 1, v___x_698_);
v___x_700_ = lean_array_push(v_b_691_, v___x_699_);
v_as_x27_690_ = v_tail_695_;
v_b_691_ = v___x_700_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__2___redArg___boxed(lean_object* v_as_x27_702_, lean_object* v_b_703_, lean_object* v___y_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l_List_forIn_x27_loop___at___00checkOlean_spec__2___redArg(v_as_x27_702_, v_b_703_);
lean_dec(v_as_x27_702_);
return v_res_705_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00checkOlean_spec__5(lean_object* v_x_707_, lean_object* v_x_708_){
_start:
{
if (lean_obj_tag(v_x_707_) == 0)
{
lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_710_ = l_List_reverse___redArg(v_x_708_);
v___x_711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_711_, 0, v___x_710_);
return v___x_711_;
}
else
{
lean_object* v_head_712_; lean_object* v_tail_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_727_; 
v_head_712_ = lean_ctor_get(v_x_707_, 0);
v_tail_713_ = lean_ctor_get(v_x_707_, 1);
v_isSharedCheck_727_ = !lean_is_exclusive(v_x_707_);
if (v_isSharedCheck_727_ == 0)
{
v___x_715_ = v_x_707_;
v_isShared_716_ = v_isSharedCheck_727_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_tail_713_);
lean_inc(v_head_712_);
lean_dec(v_x_707_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_727_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v___x_717_; uint8_t v___x_718_; 
lean_inc(v_head_712_);
v___x_717_ = l_String_toName(v_head_712_);
v___x_718_ = l_Lean_Name_isAnonymous(v___x_717_);
if (v___x_718_ == 0)
{
lean_object* v___x_720_; 
lean_dec(v_head_712_);
if (v_isShared_716_ == 0)
{
lean_ctor_set(v___x_715_, 1, v_x_708_);
lean_ctor_set(v___x_715_, 0, v___x_717_);
v___x_720_ = v___x_715_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v___x_717_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v_x_708_);
v___x_720_ = v_reuseFailAlloc_722_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
v_x_707_ = v_tail_713_;
v_x_708_ = v___x_720_;
goto _start;
}
}
else
{
lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
lean_dec(v___x_717_);
lean_del_object(v___x_715_);
lean_dec(v_tail_713_);
lean_dec(v_x_708_);
v___x_723_ = ((lean_object*)(l_List_mapM_loop___at___00checkOlean_spec__5___closed__0));
v___x_724_ = lean_string_append(v___x_723_, v_head_712_);
lean_dec(v_head_712_);
v___x_725_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_725_, 0, v___x_724_);
v___x_726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_726_, 0, v___x_725_);
return v___x_726_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00checkOlean_spec__5___boxed(lean_object* v_x_728_, lean_object* v_x_729_, lean_object* v___y_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l_List_mapM_loop___at___00checkOlean_spec__5(v_x_728_, v_x_729_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00checkOlean_spec__0(lean_object* v_val_732_, lean_object* v_a_733_, uint8_t v_fresh_734_, lean_object* v_as_735_, size_t v_sz_736_, size_t v_i_737_, lean_object* v_b_738_){
_start:
{
lean_object* v_a_741_; uint8_t v___x_745_; 
v___x_745_ = lean_usize_dec_lt(v_i_737_, v_sz_736_);
if (v___x_745_ == 0)
{
lean_object* v___x_746_; 
v___x_746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_746_, 0, v_b_738_);
return v___x_746_;
}
else
{
lean_object* v_fst_747_; lean_object* v_snd_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_778_; 
v_fst_747_ = lean_ctor_get(v_b_738_, 0);
v_snd_748_ = lean_ctor_get(v_b_738_, 1);
v_isSharedCheck_778_ = !lean_is_exclusive(v_b_738_);
if (v_isSharedCheck_778_ == 0)
{
v___x_750_ = v_b_738_;
v_isShared_751_ = v_isSharedCheck_778_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_snd_748_);
lean_inc(v_fst_747_);
lean_dec(v_b_738_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_778_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v_a_752_; lean_object* v___x_753_; 
v_a_752_ = lean_array_uget_borrowed(v_as_735_, v_i_737_);
lean_inc(v_a_752_);
v___x_753_ = l_Lean_searchModuleNameOfFileName(v_a_752_, v_val_732_);
if (lean_obj_tag(v___x_753_) == 0)
{
lean_object* v_a_754_; lean_object* v___y_756_; 
v_a_754_ = lean_ctor_get(v___x_753_, 0);
lean_inc(v_a_754_);
lean_dec_ref_known(v___x_753_, 1);
if (lean_obj_tag(v_a_754_) == 1)
{
lean_object* v_val_761_; 
v_val_761_ = lean_ctor_get(v_a_754_, 0);
lean_inc(v_val_761_);
lean_dec_ref_known(v_a_754_, 1);
if (v_fresh_734_ == 0)
{
uint8_t v___x_768_; 
v___x_768_ = l_Lean_Name_isPrefixOf(v_a_733_, v_val_761_);
if (v___x_768_ == 0)
{
goto v___jp_765_;
}
else
{
lean_dec(v_snd_748_);
goto v___jp_762_;
}
}
else
{
goto v___jp_765_;
}
v___jp_762_:
{
uint8_t v___x_763_; 
v___x_763_ = l_List_elem___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_4052238930____hygCtx___hyg_2__spec__1(v_val_761_, v_fst_747_);
if (v___x_763_ == 0)
{
lean_object* v___x_764_; 
v___x_764_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_764_, 0, v_val_761_);
lean_ctor_set(v___x_764_, 1, v_fst_747_);
v___y_756_ = v___x_764_;
goto v___jp_755_;
}
else
{
lean_dec(v_val_761_);
v___y_756_ = v_fst_747_;
goto v___jp_755_;
}
}
v___jp_765_:
{
uint8_t v___x_766_; 
v___x_766_ = lean_name_eq(v_a_733_, v_val_761_);
if (v___x_766_ == 0)
{
lean_object* v___x_767_; 
lean_dec(v_val_761_);
lean_del_object(v___x_750_);
v___x_767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_767_, 0, v_fst_747_);
lean_ctor_set(v___x_767_, 1, v_snd_748_);
v_a_741_ = v___x_767_;
goto v___jp_740_;
}
else
{
lean_dec(v_snd_748_);
goto v___jp_762_;
}
}
}
else
{
lean_object* v___x_769_; 
lean_dec(v_a_754_);
lean_del_object(v___x_750_);
v___x_769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_769_, 0, v_fst_747_);
lean_ctor_set(v___x_769_, 1, v_snd_748_);
v_a_741_ = v___x_769_;
goto v___jp_740_;
}
v___jp_755_:
{
lean_object* v___x_757_; lean_object* v___x_759_; 
v___x_757_ = lean_box(v___x_745_);
if (v_isShared_751_ == 0)
{
lean_ctor_set(v___x_750_, 1, v___x_757_);
lean_ctor_set(v___x_750_, 0, v___y_756_);
v___x_759_ = v___x_750_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v___y_756_);
lean_ctor_set(v_reuseFailAlloc_760_, 1, v___x_757_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
v_a_741_ = v___x_759_;
goto v___jp_740_;
}
}
}
else
{
lean_object* v_a_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_777_; 
lean_del_object(v___x_750_);
lean_dec(v_snd_748_);
lean_dec(v_fst_747_);
v_a_770_ = lean_ctor_get(v___x_753_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_777_ == 0)
{
v___x_772_ = v___x_753_;
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_a_770_);
lean_dec(v___x_753_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_775_; 
if (v_isShared_773_ == 0)
{
v___x_775_ = v___x_772_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_a_770_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
}
}
}
v___jp_740_:
{
size_t v___x_742_; size_t v___x_743_; 
v___x_742_ = ((size_t)1ULL);
v___x_743_ = lean_usize_add(v_i_737_, v___x_742_);
v_i_737_ = v___x_743_;
v_b_738_ = v_a_741_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00checkOlean_spec__0___boxed(lean_object* v_val_779_, lean_object* v_a_780_, lean_object* v_fresh_781_, lean_object* v_as_782_, lean_object* v_sz_783_, lean_object* v_i_784_, lean_object* v_b_785_, lean_object* v___y_786_){
_start:
{
uint8_t v_fresh_boxed_787_; size_t v_sz_boxed_788_; size_t v_i_boxed_789_; lean_object* v_res_790_; 
v_fresh_boxed_787_ = lean_unbox(v_fresh_781_);
v_sz_boxed_788_ = lean_unbox_usize(v_sz_783_);
lean_dec(v_sz_783_);
v_i_boxed_789_ = lean_unbox_usize(v_i_784_);
lean_dec(v_i_784_);
v_res_790_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00checkOlean_spec__0(v_val_779_, v_a_780_, v_fresh_boxed_787_, v_as_782_, v_sz_boxed_788_, v_i_boxed_789_, v_b_785_);
lean_dec_ref(v_as_782_);
lean_dec(v_a_780_);
lean_dec(v_val_779_);
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__1___redArg(lean_object* v_val_793_, uint8_t v_fresh_794_, lean_object* v_as_x27_795_, lean_object* v_b_796_){
_start:
{
if (lean_obj_tag(v_as_x27_795_) == 0)
{
lean_object* v___x_798_; 
v___x_798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_798_, 0, v_b_796_);
return v___x_798_;
}
else
{
lean_object* v_head_799_; lean_object* v_tail_800_; uint8_t v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v_head_799_ = lean_ctor_get(v_as_x27_795_, 0);
v_tail_800_ = lean_ctor_get(v_as_x27_795_, 1);
v___x_801_ = 0;
v___x_802_ = ((lean_object*)(l_List_forIn_x27_loop___at___00checkOlean_spec__1___redArg___closed__0));
v___x_803_ = l_Lean_SearchPath_findAllWithExt(v_val_793_, v___x_802_);
if (lean_obj_tag(v___x_803_) == 0)
{
lean_object* v_a_804_; lean_object* v___x_805_; lean_object* v___x_806_; size_t v_sz_807_; size_t v___x_808_; lean_object* v___x_809_; 
v_a_804_ = lean_ctor_get(v___x_803_, 0);
lean_inc(v_a_804_);
lean_dec_ref_known(v___x_803_, 1);
v___x_805_ = lean_box(v___x_801_);
v___x_806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_806_, 0, v_b_796_);
lean_ctor_set(v___x_806_, 1, v___x_805_);
v_sz_807_ = lean_array_size(v_a_804_);
v___x_808_ = ((size_t)0ULL);
v___x_809_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00checkOlean_spec__0(v_val_793_, v_head_799_, v_fresh_794_, v_a_804_, v_sz_807_, v___x_808_, v___x_806_);
lean_dec(v_a_804_);
if (lean_obj_tag(v___x_809_) == 0)
{
lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_826_; 
v_a_810_ = lean_ctor_get(v___x_809_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_826_ == 0)
{
v___x_812_ = v___x_809_;
v_isShared_813_ = v_isSharedCheck_826_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v___x_809_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_826_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v_snd_814_; uint8_t v___x_815_; 
v_snd_814_ = lean_ctor_get(v_a_810_, 1);
v___x_815_ = lean_unbox(v_snd_814_);
if (v___x_815_ == 0)
{
uint8_t v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_822_; 
lean_dec(v_a_810_);
v___x_816_ = 1;
v___x_817_ = ((lean_object*)(l_List_forIn_x27_loop___at___00checkOlean_spec__1___redArg___closed__1));
lean_inc(v_head_799_);
v___x_818_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_799_, v___x_816_);
v___x_819_ = lean_string_append(v___x_817_, v___x_818_);
lean_dec_ref(v___x_818_);
v___x_820_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_820_, 0, v___x_819_);
if (v_isShared_813_ == 0)
{
lean_ctor_set_tag(v___x_812_, 1);
lean_ctor_set(v___x_812_, 0, v___x_820_);
v___x_822_ = v___x_812_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v___x_820_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
else
{
lean_object* v_fst_824_; 
lean_del_object(v___x_812_);
v_fst_824_ = lean_ctor_get(v_a_810_, 0);
lean_inc(v_fst_824_);
lean_dec(v_a_810_);
v_as_x27_795_ = v_tail_800_;
v_b_796_ = v_fst_824_;
goto _start;
}
}
}
else
{
lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_834_; 
v_a_827_ = lean_ctor_get(v___x_809_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_834_ == 0)
{
v___x_829_ = v___x_809_;
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_809_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_832_; 
if (v_isShared_830_ == 0)
{
v___x_832_ = v___x_829_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_a_827_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
}
else
{
lean_object* v_a_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_842_; 
lean_dec(v_b_796_);
v_a_835_ = lean_ctor_get(v___x_803_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_842_ == 0)
{
v___x_837_ = v___x_803_;
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_a_835_);
lean_dec(v___x_803_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_840_; 
if (v_isShared_838_ == 0)
{
v___x_840_ = v___x_837_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_a_835_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__1___redArg___boxed(lean_object* v_val_843_, lean_object* v_fresh_844_, lean_object* v_as_x27_845_, lean_object* v_b_846_, lean_object* v___y_847_){
_start:
{
uint8_t v_fresh_boxed_848_; lean_object* v_res_849_; 
v_fresh_boxed_848_ = lean_unbox(v_fresh_844_);
v_res_849_ = l_List_forIn_x27_loop___at___00checkOlean_spec__1___redArg(v_val_843_, v_fresh_boxed_848_, v_as_x27_845_, v_b_846_);
lean_dec(v_as_x27_845_);
lean_dec(v_val_843_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__4___redArg(uint8_t v_verbose_851_, uint8_t v_silent_852_, lean_object* v_as_x27_853_, lean_object* v_b_854_){
_start:
{
if (lean_obj_tag(v_as_x27_853_) == 0)
{
lean_object* v___x_856_; 
v___x_856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_856_, 0, v_b_854_);
return v___x_856_;
}
else
{
lean_object* v_head_857_; lean_object* v_tail_858_; lean_object* v___x_859_; 
v_head_857_ = lean_ctor_get(v_as_x27_853_, 0);
v_tail_858_ = lean_ctor_get(v_as_x27_853_, 1);
v___x_859_ = lean_box(0);
if (v_verbose_851_ == 0)
{
goto v___jp_860_;
}
else
{
lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_863_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00checkOlean_spec__3___closed__1));
lean_inc(v_head_857_);
v___x_864_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_857_, v_verbose_851_);
v___x_865_ = lean_string_append(v___x_863_, v___x_864_);
lean_dec_ref(v___x_864_);
v___x_866_ = ((lean_object*)(l_List_forIn_x27_loop___at___00checkOlean_spec__4___redArg___closed__0));
v___x_867_ = lean_string_append(v___x_865_, v___x_866_);
v___x_868_ = l_println(v___x_867_, v_silent_852_);
if (lean_obj_tag(v___x_868_) == 0)
{
lean_dec_ref_known(v___x_868_, 1);
goto v___jp_860_;
}
else
{
return v___x_868_;
}
}
v___jp_860_:
{
lean_object* v___x_861_; 
lean_inc(v_head_857_);
v___x_861_ = l_replayFromFresh(v_head_857_);
if (lean_obj_tag(v___x_861_) == 0)
{
lean_dec_ref_known(v___x_861_, 1);
v_as_x27_853_ = v_tail_858_;
v_b_854_ = v___x_859_;
goto _start;
}
else
{
return v___x_861_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__4___redArg___boxed(lean_object* v_verbose_869_, lean_object* v_silent_870_, lean_object* v_as_x27_871_, lean_object* v_b_872_, lean_object* v___y_873_){
_start:
{
uint8_t v_verbose_boxed_874_; uint8_t v_silent_boxed_875_; lean_object* v_res_876_; 
v_verbose_boxed_874_ = lean_unbox(v_verbose_869_);
v_silent_boxed_875_ = lean_unbox(v_silent_870_);
v_res_876_ = l_List_forIn_x27_loop___at___00checkOlean_spec__4___redArg(v_verbose_boxed_874_, v_silent_boxed_875_, v_as_x27_871_, v_b_872_);
lean_dec(v_as_x27_871_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l_checkOlean(lean_object* v_args_881_, uint8_t v_fresh_882_, uint8_t v_verbose_883_, uint8_t v_silent_884_){
_start:
{
lean_object* v_targets_890_; lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_952_ = ((lean_object*)(l_checkOlean___closed__2));
v___x_953_ = l_Lean_findSysroot(v___x_952_);
if (lean_obj_tag(v___x_953_) == 0)
{
lean_object* v_a_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
v_a_954_ = lean_ctor_get(v___x_953_, 0);
lean_inc(v_a_954_);
lean_dec_ref_known(v___x_953_, 1);
v___x_955_ = lean_box(0);
v___x_956_ = l_Lean_initSearchPath(v_a_954_, v___x_955_);
if (lean_obj_tag(v___x_956_) == 0)
{
lean_dec_ref_known(v___x_956_, 1);
if (lean_obj_tag(v_args_881_) == 0)
{
lean_object* v___x_957_; 
v___x_957_ = l_getCurrentModule();
if (lean_obj_tag(v___x_957_) == 0)
{
lean_object* v_a_958_; lean_object* v___x_959_; 
v_a_958_ = lean_ctor_get(v___x_957_, 0);
lean_inc(v_a_958_);
lean_dec_ref_known(v___x_957_, 1);
v___x_959_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_959_, 0, v_a_958_);
lean_ctor_set(v___x_959_, 1, v___x_955_);
v_targets_890_ = v___x_959_;
goto v___jp_889_;
}
else
{
lean_object* v_a_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_967_; 
v_a_960_ = lean_ctor_get(v___x_957_, 0);
v_isSharedCheck_967_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_967_ == 0)
{
v___x_962_ = v___x_957_;
v_isShared_963_ = v_isSharedCheck_967_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_a_960_);
lean_dec(v___x_957_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_967_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v___x_965_; 
if (v_isShared_963_ == 0)
{
v___x_965_ = v___x_962_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_a_960_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
}
}
else
{
lean_object* v___x_968_; 
v___x_968_ = l_List_mapM_loop___at___00checkOlean_spec__5(v_args_881_, v___x_955_);
if (lean_obj_tag(v___x_968_) == 0)
{
lean_object* v_a_969_; 
v_a_969_ = lean_ctor_get(v___x_968_, 0);
lean_inc(v_a_969_);
lean_dec_ref_known(v___x_968_, 1);
v_targets_890_ = v_a_969_;
goto v___jp_889_;
}
else
{
lean_object* v_a_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_977_; 
v_a_970_ = lean_ctor_get(v___x_968_, 0);
v_isSharedCheck_977_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_977_ == 0)
{
v___x_972_ = v___x_968_;
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_a_970_);
lean_dec(v___x_968_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_975_; 
if (v_isShared_973_ == 0)
{
v___x_975_ = v___x_972_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v_a_970_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
}
}
}
else
{
lean_object* v_a_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_985_; 
lean_dec(v_args_881_);
v_a_978_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_985_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_985_ == 0)
{
v___x_980_ = v___x_956_;
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_a_978_);
lean_dec(v___x_956_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_983_; 
if (v_isShared_981_ == 0)
{
v___x_983_ = v___x_980_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v_a_978_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
}
}
else
{
lean_object* v_a_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_993_; 
lean_dec(v_args_881_);
v_a_986_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_993_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_993_ == 0)
{
v___x_988_ = v___x_953_;
v_isShared_989_ = v_isSharedCheck_993_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_a_986_);
lean_dec(v___x_953_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_993_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_991_; 
if (v_isShared_989_ == 0)
{
v___x_991_ = v___x_988_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_a_986_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
return v___x_991_;
}
}
}
v___jp_886_:
{
lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_887_ = l_checkExport___boxed__const__2;
v___x_888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_888_, 0, v___x_887_);
return v___x_888_;
}
v___jp_889_:
{
lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_891_ = lean_box(0);
v___x_892_ = l_Lean_searchPathRef;
v___x_893_ = lean_st_ref_get(v___x_892_);
v___x_894_ = l_List_forIn_x27_loop___at___00checkOlean_spec__1___redArg(v___x_893_, v_fresh_882_, v_targets_890_, v___x_891_);
lean_dec(v_targets_890_);
lean_dec(v___x_893_);
if (lean_obj_tag(v___x_894_) == 0)
{
if (v_fresh_882_ == 0)
{
lean_object* v_a_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v_a_895_ = lean_ctor_get(v___x_894_, 0);
lean_inc(v_a_895_);
lean_dec_ref_known(v___x_894_, 1);
v___x_896_ = ((lean_object*)(l_checkOlean___closed__0));
v___x_897_ = l_List_forIn_x27_loop___at___00checkOlean_spec__2___redArg(v_a_895_, v___x_896_);
lean_dec(v_a_895_);
if (lean_obj_tag(v___x_897_) == 0)
{
lean_object* v_a_898_; lean_object* v___x_899_; size_t v_sz_900_; size_t v___x_901_; lean_object* v___x_902_; 
v_a_898_ = lean_ctor_get(v___x_897_, 0);
lean_inc(v_a_898_);
lean_dec_ref_known(v___x_897_, 1);
v___x_899_ = lean_box(0);
v_sz_900_ = lean_array_size(v_a_898_);
v___x_901_ = ((size_t)0ULL);
v___x_902_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00checkOlean_spec__3(v_verbose_883_, v_silent_884_, v_a_898_, v_sz_900_, v___x_901_, v___x_899_);
lean_dec(v_a_898_);
if (lean_obj_tag(v___x_902_) == 0)
{
lean_dec_ref_known(v___x_902_, 1);
goto v___jp_886_;
}
else
{
lean_object* v_a_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_910_; 
v_a_903_ = lean_ctor_get(v___x_902_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_910_ == 0)
{
v___x_905_ = v___x_902_;
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_a_903_);
lean_dec(v___x_902_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_908_; 
if (v_isShared_906_ == 0)
{
v___x_908_ = v___x_905_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_a_903_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
}
}
else
{
lean_object* v_a_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_918_; 
v_a_911_ = lean_ctor_get(v___x_897_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_918_ == 0)
{
v___x_913_ = v___x_897_;
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_a_911_);
lean_dec(v___x_897_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_916_; 
if (v_isShared_914_ == 0)
{
v___x_916_ = v___x_913_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_a_911_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
}
}
else
{
lean_object* v_a_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_943_; 
v_a_919_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_943_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_943_ == 0)
{
v___x_921_ = v___x_894_;
v_isShared_922_ = v_isSharedCheck_943_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_a_919_);
lean_dec(v___x_894_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_943_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_923_; lean_object* v___x_924_; uint8_t v___x_925_; 
v___x_923_ = l_List_lengthTR___redArg(v_a_919_);
v___x_924_ = lean_unsigned_to_nat(1u);
v___x_925_ = lean_nat_dec_eq(v___x_923_, v___x_924_);
lean_dec(v___x_923_);
if (v___x_925_ == 0)
{
lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_931_; 
v___x_926_ = ((lean_object*)(l_checkOlean___closed__1));
v___x_927_ = l_List_toString___at___00Lean_Environment_AddConstAsyncResult_commitConst_spec__1(v_a_919_);
v___x_928_ = lean_string_append(v___x_926_, v___x_927_);
lean_dec_ref(v___x_927_);
v___x_929_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_929_, 0, v___x_928_);
if (v_isShared_922_ == 0)
{
lean_ctor_set_tag(v___x_921_, 1);
lean_ctor_set(v___x_921_, 0, v___x_929_);
v___x_931_ = v___x_921_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v___x_929_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
else
{
lean_object* v___x_933_; lean_object* v___x_934_; 
lean_del_object(v___x_921_);
v___x_933_ = lean_box(0);
v___x_934_ = l_List_forIn_x27_loop___at___00checkOlean_spec__4___redArg(v_verbose_883_, v_silent_884_, v_a_919_, v___x_933_);
lean_dec(v_a_919_);
if (lean_obj_tag(v___x_934_) == 0)
{
lean_dec_ref_known(v___x_934_, 1);
goto v___jp_886_;
}
else
{
lean_object* v_a_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_942_; 
v_a_935_ = lean_ctor_get(v___x_934_, 0);
v_isSharedCheck_942_ = !lean_is_exclusive(v___x_934_);
if (v_isSharedCheck_942_ == 0)
{
v___x_937_ = v___x_934_;
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_a_935_);
lean_dec(v___x_934_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v___x_940_; 
if (v_isShared_938_ == 0)
{
v___x_940_ = v___x_937_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_a_935_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_951_; 
v_a_944_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_951_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_951_ == 0)
{
v___x_946_ = v___x_894_;
v_isShared_947_ = v_isSharedCheck_951_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_a_944_);
lean_dec(v___x_894_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_951_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___x_949_; 
if (v_isShared_947_ == 0)
{
v___x_949_ = v___x_946_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_a_944_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_checkOlean___boxed(lean_object* v_args_994_, lean_object* v_fresh_995_, lean_object* v_verbose_996_, lean_object* v_silent_997_, lean_object* v_a_998_){
_start:
{
uint8_t v_fresh_boxed_999_; uint8_t v_verbose_boxed_1000_; uint8_t v_silent_boxed_1001_; lean_object* v_res_1002_; 
v_fresh_boxed_999_ = lean_unbox(v_fresh_995_);
v_verbose_boxed_1000_ = lean_unbox(v_verbose_996_);
v_silent_boxed_1001_ = lean_unbox(v_silent_997_);
v_res_1002_ = l_checkOlean(v_args_994_, v_fresh_boxed_999_, v_verbose_boxed_1000_, v_silent_boxed_1001_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__1(lean_object* v_val_1003_, uint8_t v_fresh_1004_, lean_object* v_as_1005_, lean_object* v_as_x27_1006_, lean_object* v_b_1007_, lean_object* v_a_1008_){
_start:
{
lean_object* v___x_1010_; 
v___x_1010_ = l_List_forIn_x27_loop___at___00checkOlean_spec__1___redArg(v_val_1003_, v_fresh_1004_, v_as_x27_1006_, v_b_1007_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__1___boxed(lean_object* v_val_1011_, lean_object* v_fresh_1012_, lean_object* v_as_1013_, lean_object* v_as_x27_1014_, lean_object* v_b_1015_, lean_object* v_a_1016_, lean_object* v___y_1017_){
_start:
{
uint8_t v_fresh_boxed_1018_; lean_object* v_res_1019_; 
v_fresh_boxed_1018_ = lean_unbox(v_fresh_1012_);
v_res_1019_ = l_List_forIn_x27_loop___at___00checkOlean_spec__1(v_val_1011_, v_fresh_boxed_1018_, v_as_1013_, v_as_x27_1014_, v_b_1015_, v_a_1016_);
lean_dec(v_as_x27_1014_);
lean_dec(v_as_1013_);
lean_dec(v_val_1011_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__2(lean_object* v_as_1020_, lean_object* v_as_x27_1021_, lean_object* v_b_1022_, lean_object* v_a_1023_){
_start:
{
lean_object* v___x_1025_; 
v___x_1025_ = l_List_forIn_x27_loop___at___00checkOlean_spec__2___redArg(v_as_x27_1021_, v_b_1022_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__2___boxed(lean_object* v_as_1026_, lean_object* v_as_x27_1027_, lean_object* v_b_1028_, lean_object* v_a_1029_, lean_object* v___y_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l_List_forIn_x27_loop___at___00checkOlean_spec__2(v_as_1026_, v_as_x27_1027_, v_b_1028_, v_a_1029_);
lean_dec(v_as_x27_1027_);
lean_dec(v_as_1026_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__4(uint8_t v_verbose_1032_, uint8_t v_silent_1033_, lean_object* v_as_1034_, lean_object* v_as_x27_1035_, lean_object* v_b_1036_, lean_object* v_a_1037_){
_start:
{
lean_object* v___x_1039_; 
v___x_1039_ = l_List_forIn_x27_loop___at___00checkOlean_spec__4___redArg(v_verbose_1032_, v_silent_1033_, v_as_x27_1035_, v_b_1036_);
return v___x_1039_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__4___boxed(lean_object* v_verbose_1040_, lean_object* v_silent_1041_, lean_object* v_as_1042_, lean_object* v_as_x27_1043_, lean_object* v_b_1044_, lean_object* v_a_1045_, lean_object* v___y_1046_){
_start:
{
uint8_t v_verbose_boxed_1047_; uint8_t v_silent_boxed_1048_; lean_object* v_res_1049_; 
v_verbose_boxed_1047_ = lean_unbox(v_verbose_1040_);
v_silent_boxed_1048_ = lean_unbox(v_silent_1041_);
v_res_1049_ = l_List_forIn_x27_loop___at___00checkOlean_spec__4(v_verbose_boxed_1047_, v_silent_boxed_1048_, v_as_1042_, v_as_x27_1043_, v_b_1044_, v_a_1045_);
lean_dec(v_as_x27_1043_);
lean_dec(v_as_1042_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l_List_partition_loop___at___00main_spec__0(lean_object* v_a_1051_, lean_object* v_a_1052_){
_start:
{
if (lean_obj_tag(v_a_1051_) == 0)
{
lean_object* v_fst_1053_; lean_object* v_snd_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1063_; 
v_fst_1053_ = lean_ctor_get(v_a_1052_, 0);
v_snd_1054_ = lean_ctor_get(v_a_1052_, 1);
v_isSharedCheck_1063_ = !lean_is_exclusive(v_a_1052_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1056_ = v_a_1052_;
v_isShared_1057_ = v_isSharedCheck_1063_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_snd_1054_);
lean_inc(v_fst_1053_);
lean_dec(v_a_1052_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1063_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1061_; 
v___x_1058_ = l_List_reverse___redArg(v_fst_1053_);
v___x_1059_ = l_List_reverse___redArg(v_snd_1054_);
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 1, v___x_1059_);
lean_ctor_set(v___x_1056_, 0, v___x_1058_);
v___x_1061_ = v___x_1056_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v___x_1058_);
lean_ctor_set(v_reuseFailAlloc_1062_, 1, v___x_1059_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
else
{
lean_object* v_head_1064_; lean_object* v_tail_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1092_; 
v_head_1064_ = lean_ctor_get(v_a_1051_, 0);
v_tail_1065_ = lean_ctor_get(v_a_1051_, 1);
v_isSharedCheck_1092_ = !lean_is_exclusive(v_a_1051_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1067_ = v_a_1051_;
v_isShared_1068_ = v_isSharedCheck_1092_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_tail_1065_);
lean_inc(v_head_1064_);
lean_dec(v_a_1051_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1092_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v_fst_1069_; lean_object* v_snd_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1091_; 
v_fst_1069_ = lean_ctor_get(v_a_1052_, 0);
v_snd_1070_ = lean_ctor_get(v_a_1052_, 1);
v_isSharedCheck_1091_ = !lean_is_exclusive(v_a_1052_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1072_ = v_a_1052_;
v_isShared_1073_ = v_isSharedCheck_1091_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_snd_1070_);
lean_inc(v_fst_1069_);
lean_dec(v_a_1052_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1091_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; uint8_t v___x_1084_; 
v___x_1082_ = lean_string_utf8_byte_size(v_head_1064_);
v___x_1083_ = lean_unsigned_to_nat(1u);
v___x_1084_ = lean_nat_dec_le(v___x_1083_, v___x_1082_);
if (v___x_1084_ == 0)
{
goto v___jp_1074_;
}
else
{
lean_object* v___x_1085_; lean_object* v___x_1086_; uint8_t v___x_1087_; 
v___x_1085_ = ((lean_object*)(l_List_partition_loop___at___00main_spec__0___closed__0));
v___x_1086_ = lean_unsigned_to_nat(0u);
v___x_1087_ = lean_string_memcmp(v_head_1064_, v___x_1085_, v___x_1086_, v___x_1086_, v___x_1083_);
if (v___x_1087_ == 0)
{
goto v___jp_1074_;
}
else
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
lean_del_object(v___x_1072_);
lean_del_object(v___x_1067_);
v___x_1088_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1088_, 0, v_head_1064_);
lean_ctor_set(v___x_1088_, 1, v_fst_1069_);
v___x_1089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1088_);
lean_ctor_set(v___x_1089_, 1, v_snd_1070_);
v_a_1051_ = v_tail_1065_;
v_a_1052_ = v___x_1089_;
goto _start;
}
}
v___jp_1074_:
{
lean_object* v___x_1076_; 
if (v_isShared_1068_ == 0)
{
lean_ctor_set(v___x_1067_, 1, v_snd_1070_);
v___x_1076_ = v___x_1067_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v_head_1064_);
lean_ctor_set(v_reuseFailAlloc_1081_, 1, v_snd_1070_);
v___x_1076_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
lean_object* v___x_1078_; 
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 1, v___x_1076_);
v___x_1078_ = v___x_1072_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_fst_1069_);
lean_ctor_set(v_reuseFailAlloc_1080_, 1, v___x_1076_);
v___x_1078_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
v_a_1051_ = v_tail_1065_;
v_a_1052_ = v___x_1078_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* _lean_main(lean_object* v_args_1100_){
_start:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v_fst_1104_; lean_object* v_snd_1105_; uint8_t v___y_1107_; lean_object* v___x_1113_; uint8_t v___x_1114_; 
v___x_1102_ = ((lean_object*)(l_main___closed__0));
v___x_1103_ = l_List_partition_loop___at___00main_spec__0(v_args_1100_, v___x_1102_);
v_fst_1104_ = lean_ctor_get(v___x_1103_, 0);
lean_inc(v_fst_1104_);
v_snd_1105_ = lean_ctor_get(v___x_1103_, 1);
lean_inc(v_snd_1105_);
lean_dec_ref(v___x_1103_);
v___x_1113_ = ((lean_object*)(l_main___closed__3));
v___x_1114_ = l_List_elem___at___00Lean_isAutoDeclOrPrivate__Internal_spec__0(v___x_1113_, v_fst_1104_);
if (v___x_1114_ == 0)
{
lean_object* v___x_1115_; uint8_t v___x_1116_; 
v___x_1115_ = ((lean_object*)(l_main___closed__4));
v___x_1116_ = l_List_elem___at___00Lean_isAutoDeclOrPrivate__Internal_spec__0(v___x_1115_, v_fst_1104_);
if (v___x_1116_ == 0)
{
lean_object* v___x_1117_; uint8_t v___x_1118_; 
v___x_1117_ = ((lean_object*)(l_main___closed__5));
v___x_1118_ = l_List_elem___at___00Lean_isAutoDeclOrPrivate__Internal_spec__0(v___x_1117_, v_fst_1104_);
v___y_1107_ = v___x_1118_;
goto v___jp_1106_;
}
else
{
v___y_1107_ = v___x_1116_;
goto v___jp_1106_;
}
}
else
{
lean_object* v___x_1119_; uint8_t v___x_1120_; lean_object* v___x_1121_; 
v___x_1119_ = ((lean_object*)(l_main___closed__2));
v___x_1120_ = l_List_elem___at___00Lean_isAutoDeclOrPrivate__Internal_spec__0(v___x_1119_, v_fst_1104_);
lean_dec(v_fst_1104_);
v___x_1121_ = l_checkExport(v_snd_1105_, v___x_1120_);
lean_dec(v_snd_1105_);
return v___x_1121_;
}
v___jp_1106_:
{
lean_object* v___x_1108_; uint8_t v___x_1109_; lean_object* v___x_1110_; uint8_t v___x_1111_; lean_object* v___x_1112_; 
v___x_1108_ = ((lean_object*)(l_main___closed__1));
v___x_1109_ = l_List_elem___at___00Lean_isAutoDeclOrPrivate__Internal_spec__0(v___x_1108_, v_fst_1104_);
v___x_1110_ = ((lean_object*)(l_main___closed__2));
v___x_1111_ = l_List_elem___at___00Lean_isAutoDeclOrPrivate__Internal_spec__0(v___x_1110_, v_fst_1104_);
lean_dec(v_fst_1104_);
v___x_1112_ = l_checkOlean(v_snd_1105_, v___x_1109_, v___y_1107_, v___x_1111_);
return v___x_1112_;
}
}
}
LEAN_EXPORT lean_object* l_main___boxed(lean_object* v_args_1122_, lean_object* v_a_1123_){
_start:
{
lean_object* v_res_1124_; 
v_res_1124_ = _lean_main(v_args_1122_);
return v_res_1124_;
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

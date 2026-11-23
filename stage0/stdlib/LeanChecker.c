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
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0___redArg(lean_object*, lean_object*);
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_environment_free_regions(lean_object*);
lean_object* l_Lean_readModuleDataParts(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_instOrdOLeanLevel_ord(uint8_t, uint8_t);
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
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00replayFromImports_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "module "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00replayFromImports_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00replayFromImports_spec__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00replayFromImports_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = " declares '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00replayFromImports_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00replayFromImports_spec__0___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00replayFromImports_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "' more than once"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00replayFromImports_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00replayFromImports_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00replayFromImports_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00replayFromImports_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_replayFromImports___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " has "};
static const lean_object* l_replayFromImports___closed__0 = (const lean_object*)&l_replayFromImports___closed__0_value;
static const lean_string_object l_replayFromImports___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = " constant names but "};
static const lean_object* l_replayFromImports___closed__1 = (const lean_object*)&l_replayFromImports___closed__1_value;
static const lean_string_object l_replayFromImports___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = " constants"};
static const lean_object* l_replayFromImports___closed__2 = (const lean_object*)&l_replayFromImports___closed__2_value;
static lean_once_cell_t l_replayFromImports___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_replayFromImports___closed__3;
static lean_once_cell_t l_replayFromImports___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_replayFromImports___closed__4;
static const lean_string_object l_replayFromImports___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "failed to read module data"};
static const lean_object* l_replayFromImports___closed__5 = (const lean_object*)&l_replayFromImports___closed__5_value;
static const lean_ctor_object l_replayFromImports___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_replayFromImports___closed__5_value)}};
static const lean_object* l_replayFromImports___closed__6 = (const lean_object*)&l_replayFromImports___closed__6_value;
static const lean_string_object l_replayFromImports___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "object file '"};
static const lean_object* l_replayFromImports___closed__7 = (const lean_object*)&l_replayFromImports___closed__7_value;
static const lean_string_object l_replayFromImports___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "' of module "};
static const lean_object* l_replayFromImports___closed__8 = (const lean_object*)&l_replayFromImports___closed__8_value;
static const lean_string_object l_replayFromImports___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " does not exist"};
static const lean_object* l_replayFromImports___closed__9 = (const lean_object*)&l_replayFromImports___closed__9_value;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00replayFromImports_spec__0(lean_object* v_module_15_, lean_object* v_as_16_, size_t v_sz_17_, size_t v_i_18_, lean_object* v_b_19_){
_start:
{
uint8_t v___x_21_; 
v___x_21_ = lean_usize_dec_lt(v_i_18_, v_sz_17_);
if (v___x_21_ == 0)
{
lean_object* v___x_22_; 
lean_dec(v_module_15_);
v___x_22_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_22_, 0, v_b_19_);
return v___x_22_;
}
else
{
lean_object* v_snd_23_; lean_object* v_fst_24_; lean_object* v___x_26_; uint8_t v_isShared_27_; uint8_t v_isSharedCheck_69_; 
v_snd_23_ = lean_ctor_get(v_b_19_, 1);
v_fst_24_ = lean_ctor_get(v_b_19_, 0);
v_isSharedCheck_69_ = !lean_is_exclusive(v_b_19_);
if (v_isSharedCheck_69_ == 0)
{
v___x_26_ = v_b_19_;
v_isShared_27_ = v_isSharedCheck_69_;
goto v_resetjp_25_;
}
else
{
lean_inc(v_snd_23_);
lean_inc(v_fst_24_);
lean_dec(v_b_19_);
v___x_26_ = lean_box(0);
v_isShared_27_ = v_isSharedCheck_69_;
goto v_resetjp_25_;
}
v_resetjp_25_:
{
lean_object* v_array_28_; lean_object* v_start_29_; lean_object* v_stop_30_; uint8_t v___x_31_; 
v_array_28_ = lean_ctor_get(v_snd_23_, 0);
v_start_29_ = lean_ctor_get(v_snd_23_, 1);
v_stop_30_ = lean_ctor_get(v_snd_23_, 2);
v___x_31_ = lean_nat_dec_lt(v_start_29_, v_stop_30_);
if (v___x_31_ == 0)
{
lean_object* v___x_33_; 
lean_dec(v_module_15_);
if (v_isShared_27_ == 0)
{
v___x_33_ = v___x_26_;
goto v_reusejp_32_;
}
else
{
lean_object* v_reuseFailAlloc_35_; 
v_reuseFailAlloc_35_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_35_, 0, v_fst_24_);
lean_ctor_set(v_reuseFailAlloc_35_, 1, v_snd_23_);
v___x_33_ = v_reuseFailAlloc_35_;
goto v_reusejp_32_;
}
v_reusejp_32_:
{
lean_object* v___x_34_; 
v___x_34_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_34_, 0, v___x_33_);
return v___x_34_;
}
}
else
{
lean_object* v___x_37_; uint8_t v_isShared_38_; uint8_t v_isSharedCheck_65_; 
lean_inc(v_stop_30_);
lean_inc(v_start_29_);
lean_inc_ref(v_array_28_);
v_isSharedCheck_65_ = !lean_is_exclusive(v_snd_23_);
if (v_isSharedCheck_65_ == 0)
{
lean_object* v_unused_66_; lean_object* v_unused_67_; lean_object* v_unused_68_; 
v_unused_66_ = lean_ctor_get(v_snd_23_, 2);
lean_dec(v_unused_66_);
v_unused_67_ = lean_ctor_get(v_snd_23_, 1);
lean_dec(v_unused_67_);
v_unused_68_ = lean_ctor_get(v_snd_23_, 0);
lean_dec(v_unused_68_);
v___x_37_ = v_snd_23_;
v_isShared_38_ = v_isSharedCheck_65_;
goto v_resetjp_36_;
}
else
{
lean_dec(v_snd_23_);
v___x_37_ = lean_box(0);
v_isShared_38_ = v_isSharedCheck_65_;
goto v_resetjp_36_;
}
v_resetjp_36_:
{
lean_object* v_a_39_; uint8_t v___x_40_; 
v_a_39_ = lean_array_uget_borrowed(v_as_16_, v_i_18_);
v___x_40_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0___redArg(v_fst_24_, v_a_39_);
if (v___x_40_ == 0)
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_45_; 
v___x_41_ = lean_array_fget(v_array_28_, v_start_29_);
v___x_42_ = lean_unsigned_to_nat(1u);
v___x_43_ = lean_nat_add(v_start_29_, v___x_42_);
lean_dec(v_start_29_);
if (v_isShared_38_ == 0)
{
lean_ctor_set(v___x_37_, 1, v___x_43_);
v___x_45_ = v___x_37_;
goto v_reusejp_44_;
}
else
{
lean_object* v_reuseFailAlloc_53_; 
v_reuseFailAlloc_53_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_53_, 0, v_array_28_);
lean_ctor_set(v_reuseFailAlloc_53_, 1, v___x_43_);
lean_ctor_set(v_reuseFailAlloc_53_, 2, v_stop_30_);
v___x_45_ = v_reuseFailAlloc_53_;
goto v_reusejp_44_;
}
v_reusejp_44_:
{
lean_object* v___x_46_; lean_object* v___x_48_; 
lean_inc(v_a_39_);
v___x_46_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1___redArg(v_fst_24_, v_a_39_, v___x_41_);
if (v_isShared_27_ == 0)
{
lean_ctor_set(v___x_26_, 1, v___x_45_);
lean_ctor_set(v___x_26_, 0, v___x_46_);
v___x_48_ = v___x_26_;
goto v_reusejp_47_;
}
else
{
lean_object* v_reuseFailAlloc_52_; 
v_reuseFailAlloc_52_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_52_, 0, v___x_46_);
lean_ctor_set(v_reuseFailAlloc_52_, 1, v___x_45_);
v___x_48_ = v_reuseFailAlloc_52_;
goto v_reusejp_47_;
}
v_reusejp_47_:
{
size_t v___x_49_; size_t v___x_50_; 
v___x_49_ = ((size_t)1ULL);
v___x_50_ = lean_usize_add(v_i_18_, v___x_49_);
v_i_18_ = v___x_50_;
v_b_19_ = v___x_48_;
goto _start;
}
}
}
else
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
lean_del_object(v___x_37_);
lean_dec(v_stop_30_);
lean_dec(v_start_29_);
lean_dec_ref(v_array_28_);
lean_del_object(v___x_26_);
lean_dec(v_fst_24_);
v___x_54_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00replayFromImports_spec__0___closed__0));
v___x_55_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_15_, v___x_40_);
v___x_56_ = lean_string_append(v___x_54_, v___x_55_);
lean_dec_ref(v___x_55_);
v___x_57_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00replayFromImports_spec__0___closed__1));
v___x_58_ = lean_string_append(v___x_56_, v___x_57_);
lean_inc(v_a_39_);
v___x_59_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_39_, v___x_40_);
v___x_60_ = lean_string_append(v___x_58_, v___x_59_);
lean_dec_ref(v___x_59_);
v___x_61_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00replayFromImports_spec__0___closed__2));
v___x_62_ = lean_string_append(v___x_60_, v___x_61_);
v___x_63_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_63_, 0, v___x_62_);
v___x_64_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_64_, 0, v___x_63_);
return v___x_64_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00replayFromImports_spec__0___boxed(lean_object* v_module_70_, lean_object* v_as_71_, lean_object* v_sz_72_, lean_object* v_i_73_, lean_object* v_b_74_, lean_object* v___y_75_){
_start:
{
size_t v_sz_boxed_76_; size_t v_i_boxed_77_; lean_object* v_res_78_; 
v_sz_boxed_76_ = lean_unbox_usize(v_sz_72_);
lean_dec(v_sz_72_);
v_i_boxed_77_ = lean_unbox_usize(v_i_73_);
lean_dec(v_i_73_);
v_res_78_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00replayFromImports_spec__0(v_module_70_, v_as_71_, v_sz_boxed_76_, v_i_boxed_77_, v_b_74_);
lean_dec_ref(v_as_71_);
return v_res_78_;
}
}
static lean_object* _init_l_replayFromImports___closed__3(void){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_82_ = lean_box(0);
v___x_83_ = lean_unsigned_to_nat(16u);
v___x_84_ = lean_mk_array(v___x_83_, v___x_82_);
return v___x_84_;
}
}
static uint8_t _init_l_replayFromImports___closed__4(void){
_start:
{
uint8_t v___x_85_; uint8_t v___x_86_; 
v___x_85_ = 2;
v___x_86_ = l_Lean_instOrdOLeanLevel_ord(v___x_85_, v___x_85_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_replayFromImports(lean_object* v_module_93_){
_start:
{
lean_object* v___x_95_; 
lean_inc(v_module_93_);
v___x_95_ = l_Lean_findOLean(v_module_93_);
if (lean_obj_tag(v___x_95_) == 0)
{
lean_object* v_a_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_251_; 
v_a_96_ = lean_ctor_get(v___x_95_, 0);
v_isSharedCheck_251_ = !lean_is_exclusive(v___x_95_);
if (v_isSharedCheck_251_ == 0)
{
v___x_98_ = v___x_95_;
v_isShared_99_ = v_isSharedCheck_251_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_a_96_);
lean_dec(v___x_95_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_251_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
uint8_t v___x_100_; lean_object* v___y_102_; lean_object* v___y_103_; uint8_t v___y_104_; uint8_t v___y_105_; lean_object* v___y_106_; lean_object* v___y_107_; lean_object* v___y_108_; uint8_t v___y_109_; lean_object* v_fnames_199_; 
v___x_100_ = l_System_FilePath_pathExists(v_a_96_);
if (v___x_100_ == 0)
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; uint8_t v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_238_; 
v___x_227_ = ((lean_object*)(l_replayFromImports___closed__7));
v___x_228_ = lean_string_append(v___x_227_, v_a_96_);
lean_dec(v_a_96_);
v___x_229_ = ((lean_object*)(l_replayFromImports___closed__8));
v___x_230_ = lean_string_append(v___x_228_, v___x_229_);
v___x_231_ = 1;
v___x_232_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_93_, v___x_231_);
v___x_233_ = lean_string_append(v___x_230_, v___x_232_);
lean_dec_ref(v___x_232_);
v___x_234_ = ((lean_object*)(l_replayFromImports___closed__9));
v___x_235_ = lean_string_append(v___x_233_, v___x_234_);
v___x_236_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
if (v_isShared_99_ == 0)
{
lean_ctor_set_tag(v___x_98_, 1);
lean_ctor_set(v___x_98_, 0, v___x_236_);
v___x_238_ = v___x_98_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v___x_236_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
return v___x_238_;
}
}
else
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; uint8_t v___x_243_; lean_object* v___x_244_; uint8_t v___x_245_; 
lean_del_object(v___x_98_);
v___x_240_ = lean_unsigned_to_nat(1u);
v___x_241_ = lean_mk_empty_array_with_capacity(v___x_240_);
lean_inc_n(v_a_96_, 2);
v___x_242_ = lean_array_push(v___x_241_, v_a_96_);
v___x_243_ = 1;
v___x_244_ = l_Lean_OLeanLevel_adjustFileName(v_a_96_, v___x_243_);
v___x_245_ = l_System_FilePath_pathExists(v___x_244_);
if (v___x_245_ == 0)
{
lean_dec_ref(v___x_244_);
lean_dec(v_a_96_);
v_fnames_199_ = v___x_242_;
goto v___jp_198_;
}
else
{
lean_object* v___x_246_; uint8_t v___x_247_; lean_object* v___x_248_; uint8_t v___x_249_; 
v___x_246_ = lean_array_push(v___x_242_, v___x_244_);
v___x_247_ = 2;
v___x_248_ = l_Lean_OLeanLevel_adjustFileName(v_a_96_, v___x_247_);
v___x_249_ = l_System_FilePath_pathExists(v___x_248_);
if (v___x_249_ == 0)
{
lean_dec_ref(v___x_248_);
v_fnames_199_ = v___x_246_;
goto v___jp_198_;
}
else
{
lean_object* v___x_250_; 
v___x_250_ = lean_array_push(v___x_246_, v___x_248_);
v_fnames_199_ = v___x_250_;
goto v___jp_198_;
}
}
}
v___jp_101_:
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_110_ = l_Lean_instInhabitedImportState_default;
v___x_111_ = lean_st_mk_ref(v___x_110_);
lean_inc(v___y_106_);
v___x_112_ = l_Lean_importModulesCore(v___y_103_, v___y_104_, v___y_106_, v___y_109_, v___y_105_, v___x_111_);
if (lean_obj_tag(v___x_112_) == 0)
{
lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_196_; 
v_isSharedCheck_196_ = !lean_is_exclusive(v___x_112_);
if (v_isSharedCheck_196_ == 0)
{
lean_object* v_unused_197_; 
v_unused_197_ = lean_ctor_get(v___x_112_, 0);
lean_dec(v_unused_197_);
v___x_114_ = v___x_112_;
v_isShared_115_ = v_isSharedCheck_196_;
goto v_resetjp_113_;
}
else
{
lean_dec(v___x_112_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_196_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v___x_116_; lean_object* v___x_117_; uint32_t v___x_118_; lean_object* v___x_119_; 
v___x_116_ = lean_st_ref_get(v___x_111_);
lean_dec(v___x_111_);
v___x_117_ = l_Lean_Options_empty;
v___x_118_ = 0;
v___x_119_ = l_Lean_finalizeImport(v___x_116_, v___y_103_, v___x_117_, v___x_118_, v___y_105_, v___y_105_, v___y_104_, v___x_100_, v___y_105_);
if (lean_obj_tag(v___x_119_) == 0)
{
lean_object* v_a_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_187_; 
v_a_120_ = lean_ctor_get(v___x_119_, 0);
v_isSharedCheck_187_ = !lean_is_exclusive(v___x_119_);
if (v_isSharedCheck_187_ == 0)
{
v___x_122_ = v___x_119_;
v_isShared_123_ = v_isSharedCheck_187_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_a_120_);
lean_dec(v___x_119_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_187_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v_fst_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_185_; 
v___x_124_ = lean_unsigned_to_nat(1u);
v___x_125_ = lean_nat_sub(v___y_107_, v___x_124_);
lean_dec(v___y_107_);
v___x_126_ = lean_array_fget(v___y_102_, v___x_125_);
lean_dec(v___x_125_);
lean_dec_ref(v___y_102_);
v_fst_127_ = lean_ctor_get(v___x_126_, 0);
v_isSharedCheck_185_ = !lean_is_exclusive(v___x_126_);
if (v_isSharedCheck_185_ == 0)
{
lean_object* v_unused_186_; 
v_unused_186_ = lean_ctor_get(v___x_126_, 1);
lean_dec(v_unused_186_);
v___x_129_ = v___x_126_;
v_isShared_130_ = v_isSharedCheck_185_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_fst_127_);
lean_dec(v___x_126_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_185_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v_constNames_131_; lean_object* v_constants_132_; lean_object* v___x_133_; lean_object* v___x_134_; uint8_t v___x_135_; 
v_constNames_131_ = lean_ctor_get(v_fst_127_, 1);
lean_inc_ref(v_constNames_131_);
v_constants_132_ = lean_ctor_get(v_fst_127_, 2);
lean_inc_ref(v_constants_132_);
lean_dec(v_fst_127_);
v___x_133_ = lean_array_get_size(v_constNames_131_);
v___x_134_ = lean_array_get_size(v_constants_132_);
v___x_135_ = lean_nat_dec_eq(v___x_133_, v___x_134_);
if (v___x_135_ == 0)
{
lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_150_; 
lean_dec_ref(v_constants_132_);
lean_dec_ref(v_constNames_131_);
lean_del_object(v___x_129_);
lean_dec(v_a_120_);
lean_dec(v___y_108_);
v___x_136_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00replayFromImports_spec__0___closed__0));
v___x_137_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_93_, v___x_100_);
v___x_138_ = lean_string_append(v___x_136_, v___x_137_);
lean_dec_ref(v___x_137_);
v___x_139_ = ((lean_object*)(l_replayFromImports___closed__0));
v___x_140_ = lean_string_append(v___x_138_, v___x_139_);
v___x_141_ = l_Nat_reprFast(v___x_133_);
v___x_142_ = lean_string_append(v___x_140_, v___x_141_);
lean_dec_ref(v___x_141_);
v___x_143_ = ((lean_object*)(l_replayFromImports___closed__1));
v___x_144_ = lean_string_append(v___x_142_, v___x_143_);
v___x_145_ = l_Nat_reprFast(v___x_134_);
v___x_146_ = lean_string_append(v___x_144_, v___x_145_);
lean_dec_ref(v___x_145_);
v___x_147_ = ((lean_object*)(l_replayFromImports___closed__2));
v___x_148_ = lean_string_append(v___x_146_, v___x_147_);
if (v_isShared_115_ == 0)
{
lean_ctor_set_tag(v___x_114_, 18);
lean_ctor_set(v___x_114_, 0, v___x_148_);
v___x_150_ = v___x_114_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v___x_148_);
v___x_150_ = v_reuseFailAlloc_154_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
lean_object* v___x_152_; 
if (v_isShared_123_ == 0)
{
lean_ctor_set_tag(v___x_122_, 1);
lean_ctor_set(v___x_122_, 0, v___x_150_);
v___x_152_ = v___x_122_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v___x_150_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
return v___x_152_;
}
}
}
else
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_159_; 
lean_del_object(v___x_122_);
lean_del_object(v___x_114_);
v___x_155_ = lean_obj_once(&l_replayFromImports___closed__3, &l_replayFromImports___closed__3_once, _init_l_replayFromImports___closed__3);
lean_inc(v___y_108_);
v___x_156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_156_, 0, v___y_108_);
lean_ctor_set(v___x_156_, 1, v___x_155_);
v___x_157_ = l_Array_toSubarray___redArg(v_constants_132_, v___y_108_, v___x_134_);
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 1, v___x_157_);
lean_ctor_set(v___x_129_, 0, v___x_156_);
v___x_159_ = v___x_129_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v___x_156_);
lean_ctor_set(v_reuseFailAlloc_184_, 1, v___x_157_);
v___x_159_ = v_reuseFailAlloc_184_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
size_t v_sz_160_; size_t v___x_161_; lean_object* v___x_162_; 
v_sz_160_ = lean_array_size(v_constNames_131_);
v___x_161_ = ((size_t)0ULL);
v___x_162_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00replayFromImports_spec__0(v_module_93_, v_constNames_131_, v_sz_160_, v___x_161_, v___x_159_);
lean_dec_ref(v_constNames_131_);
if (lean_obj_tag(v___x_162_) == 0)
{
lean_object* v_a_163_; lean_object* v_fst_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v_a_163_ = lean_ctor_get(v___x_162_, 0);
lean_inc(v_a_163_);
lean_dec_ref_known(v___x_162_, 1);
v_fst_164_ = lean_ctor_get(v_a_163_, 0);
lean_inc(v_fst_164_);
lean_dec(v_a_163_);
lean_inc(v_a_120_);
v___x_165_ = lean_elab_environment_to_kernel_env(v_a_120_);
v___x_166_ = l_Lean_Kernel_Environment_replay(v_fst_164_, v___x_165_);
lean_dec(v_fst_164_);
if (lean_obj_tag(v___x_166_) == 0)
{
lean_object* v___x_167_; 
lean_dec_ref_known(v___x_166_, 1);
v___x_167_ = lean_environment_free_regions(v_a_120_);
return v___x_167_;
}
else
{
lean_object* v_a_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_175_; 
lean_dec(v_a_120_);
v_a_168_ = lean_ctor_get(v___x_166_, 0);
v_isSharedCheck_175_ = !lean_is_exclusive(v___x_166_);
if (v_isSharedCheck_175_ == 0)
{
v___x_170_ = v___x_166_;
v_isShared_171_ = v_isSharedCheck_175_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_a_168_);
lean_dec(v___x_166_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_175_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v___x_173_; 
if (v_isShared_171_ == 0)
{
v___x_173_ = v___x_170_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v_a_168_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
return v___x_173_;
}
}
}
}
else
{
lean_object* v_a_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_183_; 
lean_dec(v_a_120_);
v_a_176_ = lean_ctor_get(v___x_162_, 0);
v_isSharedCheck_183_ = !lean_is_exclusive(v___x_162_);
if (v_isSharedCheck_183_ == 0)
{
v___x_178_ = v___x_162_;
v_isShared_179_ = v_isSharedCheck_183_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_a_176_);
lean_dec(v___x_162_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_183_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___x_181_; 
if (v_isShared_179_ == 0)
{
v___x_181_ = v___x_178_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v_a_176_);
v___x_181_ = v_reuseFailAlloc_182_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
return v___x_181_;
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_195_; 
lean_del_object(v___x_114_);
lean_dec(v___y_108_);
lean_dec(v___y_107_);
lean_dec_ref(v___y_102_);
lean_dec(v_module_93_);
v_a_188_ = lean_ctor_get(v___x_119_, 0);
v_isSharedCheck_195_ = !lean_is_exclusive(v___x_119_);
if (v_isSharedCheck_195_ == 0)
{
v___x_190_ = v___x_119_;
v_isShared_191_ = v_isSharedCheck_195_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_a_188_);
lean_dec(v___x_119_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_195_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v___x_193_; 
if (v_isShared_191_ == 0)
{
v___x_193_ = v___x_190_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v_a_188_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
}
}
}
else
{
lean_dec(v___x_111_);
lean_dec(v___y_108_);
lean_dec(v___y_107_);
lean_dec_ref(v___y_103_);
lean_dec_ref(v___y_102_);
lean_dec(v_module_93_);
return v___x_112_;
}
}
v___jp_198_:
{
lean_object* v___x_200_; 
v___x_200_ = l_Lean_readModuleDataParts(v_fnames_199_);
lean_dec_ref(v_fnames_199_);
if (lean_obj_tag(v___x_200_) == 0)
{
lean_object* v_a_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_218_; 
v_a_201_ = lean_ctor_get(v___x_200_, 0);
v_isSharedCheck_218_ = !lean_is_exclusive(v___x_200_);
if (v_isSharedCheck_218_ == 0)
{
v___x_203_ = v___x_200_;
v_isShared_204_ = v_isSharedCheck_218_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_a_201_);
lean_dec(v___x_200_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_218_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_205_; lean_object* v___x_206_; uint8_t v___x_207_; 
v___x_205_ = lean_array_get_size(v_a_201_);
v___x_206_ = lean_unsigned_to_nat(0u);
v___x_207_ = lean_nat_dec_eq(v___x_205_, v___x_206_);
if (v___x_207_ == 0)
{
lean_object* v___x_208_; lean_object* v_fst_209_; lean_object* v_imports_210_; uint8_t v___x_211_; lean_object* v___x_212_; uint8_t v___x_213_; 
lean_del_object(v___x_203_);
v___x_208_ = lean_array_fget_borrowed(v_a_201_, v___x_206_);
v_fst_209_ = lean_ctor_get(v___x_208_, 0);
v_imports_210_ = lean_ctor_get(v_fst_209_, 0);
lean_inc_ref(v_imports_210_);
v___x_211_ = 2;
v___x_212_ = lean_box(1);
v___x_213_ = lean_uint8_once(&l_replayFromImports___closed__4, &l_replayFromImports___closed__4_once, _init_l_replayFromImports___closed__4);
if (v___x_213_ == 0)
{
v___y_102_ = v_a_201_;
v___y_103_ = v_imports_210_;
v___y_104_ = v___x_211_;
v___y_105_ = v___x_207_;
v___y_106_ = v___x_212_;
v___y_107_ = v___x_205_;
v___y_108_ = v___x_206_;
v___y_109_ = v___x_100_;
goto v___jp_101_;
}
else
{
v___y_102_ = v_a_201_;
v___y_103_ = v_imports_210_;
v___y_104_ = v___x_211_;
v___y_105_ = v___x_207_;
v___y_106_ = v___x_212_;
v___y_107_ = v___x_205_;
v___y_108_ = v___x_206_;
v___y_109_ = v___x_207_;
goto v___jp_101_;
}
}
else
{
lean_object* v___x_214_; lean_object* v___x_216_; 
lean_dec(v_a_201_);
lean_dec(v_module_93_);
v___x_214_ = ((lean_object*)(l_replayFromImports___closed__6));
if (v_isShared_204_ == 0)
{
lean_ctor_set_tag(v___x_203_, 1);
lean_ctor_set(v___x_203_, 0, v___x_214_);
v___x_216_ = v___x_203_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v___x_214_);
v___x_216_ = v_reuseFailAlloc_217_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
return v___x_216_;
}
}
}
}
else
{
lean_object* v_a_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_226_; 
lean_dec(v_module_93_);
v_a_219_ = lean_ctor_get(v___x_200_, 0);
v_isSharedCheck_226_ = !lean_is_exclusive(v___x_200_);
if (v_isSharedCheck_226_ == 0)
{
v___x_221_ = v___x_200_;
v_isShared_222_ = v_isSharedCheck_226_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_a_219_);
lean_dec(v___x_200_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_226_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
lean_object* v___x_224_; 
if (v_isShared_222_ == 0)
{
v___x_224_ = v___x_221_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v_a_219_);
v___x_224_ = v_reuseFailAlloc_225_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
return v___x_224_;
}
}
}
}
}
}
else
{
lean_object* v_a_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_259_; 
lean_dec(v_module_93_);
v_a_252_ = lean_ctor_get(v___x_95_, 0);
v_isSharedCheck_259_ = !lean_is_exclusive(v___x_95_);
if (v_isSharedCheck_259_ == 0)
{
v___x_254_ = v___x_95_;
v_isShared_255_ = v_isSharedCheck_259_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_a_252_);
lean_dec(v___x_95_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_259_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_257_; 
if (v_isShared_255_ == 0)
{
v___x_257_ = v___x_254_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v_a_252_);
v___x_257_ = v_reuseFailAlloc_258_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
return v___x_257_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_replayFromImports___boxed(lean_object* v_module_260_, lean_object* v_a_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_replayFromImports(v_module_260_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00replayFromFresh_spec__0_spec__0_spec__1(lean_object* v_t_263_, lean_object* v_init_264_){
_start:
{
switch(lean_obj_tag(v_t_263_))
{
case 0:
{
lean_object* v_key_265_; lean_object* v_val_266_; lean_object* v___x_267_; 
v_key_265_ = lean_ctor_get(v_t_263_, 0);
lean_inc(v_key_265_);
v_val_266_ = lean_ctor_get(v_t_263_, 1);
lean_inc(v_val_266_);
lean_dec_ref_known(v_t_263_, 2);
v___x_267_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1___redArg(v_init_264_, v_key_265_, v_val_266_);
return v___x_267_;
}
case 1:
{
lean_object* v_children_268_; lean_object* v___x_269_; lean_object* v___x_270_; uint8_t v___x_271_; 
v_children_268_ = lean_ctor_get(v_t_263_, 1);
lean_inc_ref(v_children_268_);
lean_dec_ref_known(v_t_263_, 2);
v___x_269_ = lean_unsigned_to_nat(0u);
v___x_270_ = lean_array_get_size(v_children_268_);
v___x_271_ = lean_nat_dec_lt(v___x_269_, v___x_270_);
if (v___x_271_ == 0)
{
lean_dec_ref(v_children_268_);
return v_init_264_;
}
else
{
size_t v___x_272_; size_t v___x_273_; lean_object* v___x_274_; 
v___x_272_ = ((size_t)0ULL);
v___x_273_ = lean_usize_of_nat(v___x_270_);
v___x_274_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1_spec__2___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00replayFromFresh_spec__0_spec__0_spec__1_spec__2(v_children_268_, v___x_272_, v___x_273_, v_init_264_);
lean_dec_ref(v_children_268_);
return v___x_274_;
}
}
default: 
{
lean_object* v_key_275_; lean_object* v_val_276_; lean_object* v_children_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; uint8_t v___x_281_; 
v_key_275_ = lean_ctor_get(v_t_263_, 0);
lean_inc(v_key_275_);
v_val_276_ = lean_ctor_get(v_t_263_, 1);
lean_inc(v_val_276_);
v_children_277_ = lean_ctor_get(v_t_263_, 2);
lean_inc_ref(v_children_277_);
lean_dec_ref_known(v_t_263_, 3);
v___x_278_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1___redArg(v_init_264_, v_key_275_, v_val_276_);
v___x_279_ = lean_unsigned_to_nat(0u);
v___x_280_ = lean_array_get_size(v_children_277_);
v___x_281_ = lean_nat_dec_lt(v___x_279_, v___x_280_);
if (v___x_281_ == 0)
{
lean_dec_ref(v_children_277_);
return v___x_278_;
}
else
{
size_t v___x_282_; size_t v___x_283_; lean_object* v___x_284_; 
v___x_282_ = ((size_t)0ULL);
v___x_283_ = lean_usize_of_nat(v___x_280_);
v___x_284_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1_spec__2___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00replayFromFresh_spec__0_spec__0_spec__1_spec__2(v_children_277_, v___x_282_, v___x_283_, v___x_278_);
lean_dec_ref(v_children_277_);
return v___x_284_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1_spec__2___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00replayFromFresh_spec__0_spec__0_spec__1_spec__2(lean_object* v_as_285_, size_t v_i_286_, size_t v_stop_287_, lean_object* v_b_288_){
_start:
{
uint8_t v___x_289_; 
v___x_289_ = lean_usize_dec_eq(v_i_286_, v_stop_287_);
if (v___x_289_ == 0)
{
lean_object* v___x_290_; lean_object* v___x_291_; size_t v___x_292_; size_t v___x_293_; 
v___x_290_ = lean_array_uget_borrowed(v_as_285_, v_i_286_);
lean_inc(v___x_290_);
v___x_291_ = l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00replayFromFresh_spec__0_spec__0_spec__1(v___x_290_, v_b_288_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1_spec__2___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00replayFromFresh_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_as_295_, lean_object* v_i_296_, lean_object* v_stop_297_, lean_object* v_b_298_){
_start:
{
size_t v_i_boxed_299_; size_t v_stop_boxed_300_; lean_object* v_res_301_; 
v_i_boxed_299_ = lean_unbox_usize(v_i_296_);
lean_dec(v_i_296_);
v_stop_boxed_300_ = lean_unbox_usize(v_stop_297_);
lean_dec(v_stop_297_);
v_res_301_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1_spec__2___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00replayFromFresh_spec__0_spec__0_spec__1_spec__2(v_as_295_, v_i_boxed_299_, v_stop_boxed_300_, v_b_298_);
lean_dec_ref(v_as_295_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00replayFromFresh_spec__0_spec__0(lean_object* v_t_302_, lean_object* v_init_303_){
_start:
{
switch(lean_obj_tag(v_t_302_))
{
case 0:
{
lean_object* v_tree_304_; lean_object* v___x_305_; 
v_tree_304_ = lean_ctor_get(v_t_302_, 1);
lean_inc_ref(v_tree_304_);
lean_dec_ref_known(v_t_302_, 2);
v___x_305_ = l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__1___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00replayFromFresh_spec__0_spec__0_spec__1(v_tree_304_, v_init_303_);
return v___x_305_;
}
case 1:
{
lean_object* v_key_306_; lean_object* v_entry_x3f_307_; lean_object* v_children_308_; lean_object* v_s_310_; 
v_key_306_ = lean_ctor_get(v_t_302_, 0);
lean_inc(v_key_306_);
v_entry_x3f_307_ = lean_ctor_get(v_t_302_, 1);
lean_inc(v_entry_x3f_307_);
v_children_308_ = lean_ctor_get(v_t_302_, 2);
lean_inc_ref(v_children_308_);
lean_dec_ref_known(v_t_302_, 3);
if (lean_obj_tag(v_entry_x3f_307_) == 1)
{
lean_object* v_val_317_; lean_object* v_fst_318_; lean_object* v___x_319_; 
v_val_317_ = lean_ctor_get(v_entry_x3f_307_, 0);
lean_inc(v_val_317_);
lean_dec_ref_known(v_entry_x3f_307_, 1);
v_fst_318_ = lean_ctor_get(v_val_317_, 0);
lean_inc(v_fst_318_);
lean_dec(v_val_317_);
v___x_319_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1___redArg(v_init_303_, v_key_306_, v_fst_318_);
v_s_310_ = v___x_319_;
goto v___jp_309_;
}
else
{
lean_dec(v_entry_x3f_307_);
lean_dec(v_key_306_);
v_s_310_ = v_init_303_;
goto v___jp_309_;
}
v___jp_309_:
{
lean_object* v___x_311_; lean_object* v___x_312_; uint8_t v___x_313_; 
v___x_311_ = lean_unsigned_to_nat(0u);
v___x_312_ = lean_array_get_size(v_children_308_);
v___x_313_ = lean_nat_dec_lt(v___x_311_, v___x_312_);
if (v___x_313_ == 0)
{
lean_dec_ref(v_children_308_);
return v_s_310_;
}
else
{
size_t v___x_314_; size_t v___x_315_; lean_object* v___x_316_; 
v___x_314_ = ((size_t)0ULL);
v___x_315_ = lean_usize_of_nat(v___x_312_);
v___x_316_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__2___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00replayFromFresh_spec__0_spec__0_spec__2(v_children_308_, v___x_314_, v___x_315_, v_s_310_);
lean_dec_ref(v_children_308_);
return v___x_316_;
}
}
}
default: 
{
lean_object* v_key_320_; lean_object* v_entry_x3f_321_; lean_object* v_children_322_; lean_object* v_s_324_; 
v_key_320_ = lean_ctor_get(v_t_302_, 0);
lean_inc(v_key_320_);
v_entry_x3f_321_ = lean_ctor_get(v_t_302_, 1);
lean_inc(v_entry_x3f_321_);
v_children_322_ = lean_ctor_get(v_t_302_, 2);
lean_inc_ref(v_children_322_);
lean_dec_ref_known(v_t_302_, 3);
if (lean_obj_tag(v_entry_x3f_321_) == 1)
{
lean_object* v_val_332_; lean_object* v_fst_333_; lean_object* v___x_334_; 
v_val_332_ = lean_ctor_get(v_entry_x3f_321_, 0);
lean_inc(v_val_332_);
lean_dec_ref_known(v_entry_x3f_321_, 1);
v_fst_333_ = lean_ctor_get(v_val_332_, 0);
lean_inc(v_fst_333_);
lean_dec(v_val_332_);
v___x_334_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1___redArg(v_init_303_, v_key_320_, v_fst_333_);
v_s_324_ = v___x_334_;
goto v___jp_323_;
}
else
{
lean_dec(v_entry_x3f_321_);
lean_dec(v_key_320_);
v_s_324_ = v_init_303_;
goto v___jp_323_;
}
v___jp_323_:
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; uint8_t v___x_328_; 
v___x_325_ = lean_thunk_get_own(v_children_322_);
lean_dec_ref(v_children_322_);
v___x_326_ = lean_unsigned_to_nat(0u);
v___x_327_ = lean_array_get_size(v___x_325_);
v___x_328_ = lean_nat_dec_lt(v___x_326_, v___x_327_);
if (v___x_328_ == 0)
{
lean_dec(v___x_325_);
return v_s_324_;
}
else
{
size_t v___x_329_; size_t v___x_330_; lean_object* v___x_331_; 
v___x_329_ = ((size_t)0ULL);
v___x_330_ = lean_usize_of_nat(v___x_327_);
v___x_331_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__2___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00replayFromFresh_spec__0_spec__0_spec__2(v___x_325_, v___x_329_, v___x_330_, v_s_324_);
lean_dec(v___x_325_);
return v___x_331_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__2___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00replayFromFresh_spec__0_spec__0_spec__2(lean_object* v_as_335_, size_t v_i_336_, size_t v_stop_337_, lean_object* v_b_338_){
_start:
{
uint8_t v___x_339_; 
v___x_339_ = lean_usize_dec_eq(v_i_336_, v_stop_337_);
if (v___x_339_ == 0)
{
lean_object* v___x_340_; lean_object* v___x_341_; size_t v___x_342_; size_t v___x_343_; 
v___x_340_ = lean_array_uget_borrowed(v_as_335_, v_i_336_);
lean_inc(v___x_340_);
v___x_341_ = l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00replayFromFresh_spec__0_spec__0(v___x_340_, v_b_338_);
v___x_342_ = ((size_t)1ULL);
v___x_343_ = lean_usize_add(v_i_336_, v___x_342_);
v_i_336_ = v___x_343_;
v_b_338_ = v___x_341_;
goto _start;
}
else
{
return v_b_338_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__2___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00replayFromFresh_spec__0_spec__0_spec__2___boxed(lean_object* v_as_345_, lean_object* v_i_346_, lean_object* v_stop_347_, lean_object* v_b_348_){
_start:
{
size_t v_i_boxed_349_; size_t v_stop_boxed_350_; lean_object* v_res_351_; 
v_i_boxed_349_ = lean_unbox_usize(v_i_346_);
lean_dec(v_i_346_);
v_stop_boxed_350_ = lean_unbox_usize(v_stop_347_);
lean_dec(v_stop_347_);
v_res_351_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0_spec__2___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00replayFromFresh_spec__0_spec__0_spec__2(v_as_345_, v_i_boxed_349_, v_stop_boxed_350_, v_b_348_);
lean_dec_ref(v_as_345_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00replayFromFresh_spec__0(lean_object* v_t_352_, lean_object* v_init_353_){
_start:
{
lean_object* v_tree_354_; lean_object* v___x_355_; 
v_tree_354_ = lean_ctor_get(v_t_352_, 1);
lean_inc_ref(v_tree_354_);
lean_dec_ref(v_t_352_);
v___x_355_ = l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0_spec__0___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00replayFromFresh_spec__0_spec__0(v_tree_354_, v_init_353_);
return v___x_355_;
}
}
static lean_object* _init_l_replayFromFresh___lam__0___closed__0(void){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_356_ = lean_obj_once(&l_replayFromImports___closed__3, &l_replayFromImports___closed__3_once, _init_l_replayFromImports___closed__3);
v___x_357_ = lean_unsigned_to_nat(0u);
v___x_358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
lean_ctor_set(v___x_358_, 1, v___x_356_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_replayFromFresh___lam__0(lean_object* v_env_359_){
_start:
{
lean_object* v___x_361_; lean_object* v_map_u2081_362_; lean_object* v___x_363_; lean_object* v_imported_364_; uint32_t v___x_365_; lean_object* v___x_366_; 
v___x_361_ = l_Lean_Environment_constants(v_env_359_);
v_map_u2081_362_ = lean_ctor_get(v___x_361_, 0);
lean_inc_ref(v_map_u2081_362_);
lean_dec_ref(v___x_361_);
v___x_363_ = lean_obj_once(&l_replayFromFresh___lam__0___closed__0, &l_replayFromFresh___lam__0___closed__0_once, _init_l_replayFromFresh___lam__0___closed__0);
v_imported_364_ = l_Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___at___00replayFromFresh_spec__0(v_map_u2081_362_, v___x_363_);
v___x_365_ = 0;
v___x_366_ = l_Lean_mkEmptyEnvironment(v___x_365_);
if (lean_obj_tag(v___x_366_) == 0)
{
lean_object* v_a_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v_a_367_ = lean_ctor_get(v___x_366_, 0);
lean_inc(v_a_367_);
lean_dec_ref_known(v___x_366_, 1);
v___x_368_ = lean_elab_environment_to_kernel_env(v_a_367_);
v___x_369_ = lean_box(0);
v___x_370_ = l_Lean_Kernel_Environment_replay(v_imported_364_, v___x_368_);
lean_dec_ref(v_imported_364_);
if (lean_obj_tag(v___x_370_) == 0)
{
lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_377_; 
v_isSharedCheck_377_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_377_ == 0)
{
lean_object* v_unused_378_; 
v_unused_378_ = lean_ctor_get(v___x_370_, 0);
lean_dec(v_unused_378_);
v___x_372_ = v___x_370_;
v_isShared_373_ = v_isSharedCheck_377_;
goto v_resetjp_371_;
}
else
{
lean_dec(v___x_370_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_377_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_375_; 
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 0, v___x_369_);
v___x_375_ = v___x_372_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v___x_369_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
return v___x_375_;
}
}
}
else
{
lean_object* v_a_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_386_; 
v_a_379_ = lean_ctor_get(v___x_370_, 0);
v_isSharedCheck_386_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_386_ == 0)
{
v___x_381_ = v___x_370_;
v_isShared_382_ = v_isSharedCheck_386_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_a_379_);
lean_dec(v___x_370_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_386_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v___x_384_; 
if (v_isShared_382_ == 0)
{
v___x_384_ = v___x_381_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v_a_379_);
v___x_384_ = v_reuseFailAlloc_385_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
return v___x_384_;
}
}
}
}
else
{
lean_object* v_a_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_394_; 
lean_dec_ref(v_imported_364_);
v_a_387_ = lean_ctor_get(v___x_366_, 0);
v_isSharedCheck_394_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_394_ == 0)
{
v___x_389_ = v___x_366_;
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_a_387_);
lean_dec(v___x_366_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_392_; 
if (v_isShared_390_ == 0)
{
v___x_392_ = v___x_389_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v_a_387_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
return v___x_392_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_replayFromFresh___lam__0___boxed(lean_object* v_env_395_, lean_object* v___y_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_replayFromFresh___lam__0(v_env_395_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_replayFromFresh(lean_object* v_module_399_){
_start:
{
lean_object* v___f_401_; uint8_t v___x_402_; uint8_t v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; uint32_t v___x_409_; lean_object* v___x_410_; 
v___f_401_ = ((lean_object*)(l_replayFromFresh___closed__0));
v___x_402_ = 0;
v___x_403_ = 1;
v___x_404_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_404_, 0, v_module_399_);
lean_ctor_set_uint8(v___x_404_, sizeof(void*)*1, v___x_402_);
lean_ctor_set_uint8(v___x_404_, sizeof(void*)*1 + 1, v___x_403_);
lean_ctor_set_uint8(v___x_404_, sizeof(void*)*1 + 2, v___x_402_);
v___x_405_ = lean_unsigned_to_nat(1u);
v___x_406_ = lean_mk_empty_array_with_capacity(v___x_405_);
v___x_407_ = lean_array_push(v___x_406_, v___x_404_);
v___x_408_ = l_Lean_Options_empty;
v___x_409_ = 0;
v___x_410_ = l_Lean_withImportModules___redArg(v___x_407_, v___x_408_, v___f_401_, v___x_409_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_replayFromFresh___boxed(lean_object* v_module_411_, lean_object* v_a_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_replayFromFresh(v_module_411_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_getCurrentModule(){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_416_ = ((lean_object*)(l_getCurrentModule___closed__0));
v___x_417_ = l_Lake_Manifest_load_x3f(v___x_416_);
if (lean_obj_tag(v___x_417_) == 0)
{
lean_object* v_a_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_432_; 
v_a_418_ = lean_ctor_get(v___x_417_, 0);
v_isSharedCheck_432_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_432_ == 0)
{
v___x_420_ = v___x_417_;
v_isShared_421_ = v_isSharedCheck_432_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_a_418_);
lean_dec(v___x_417_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_432_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
if (lean_obj_tag(v_a_418_) == 0)
{
lean_object* v___x_422_; lean_object* v___x_424_; 
v___x_422_ = lean_box(0);
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 0, v___x_422_);
v___x_424_ = v___x_420_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v___x_422_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
else
{
lean_object* v_val_426_; lean_object* v_name_427_; lean_object* v___x_428_; lean_object* v___x_430_; 
v_val_426_ = lean_ctor_get(v_a_418_, 0);
lean_inc(v_val_426_);
lean_dec_ref_known(v_a_418_, 1);
v_name_427_ = lean_ctor_get(v_val_426_, 0);
lean_inc(v_name_427_);
lean_dec(v_val_426_);
v___x_428_ = l_Lean_Name_capitalize(v_name_427_);
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 0, v___x_428_);
v___x_430_ = v___x_420_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v___x_428_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
return v___x_430_;
}
}
}
}
else
{
lean_object* v_a_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_440_; 
v_a_433_ = lean_ctor_get(v___x_417_, 0);
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_440_ == 0)
{
v___x_435_ = v___x_417_;
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_a_433_);
lean_dec(v___x_417_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_438_; 
if (v_isShared_436_ == 0)
{
v___x_438_ = v___x_435_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v_a_433_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_getCurrentModule___boxed(lean_object* v_a_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_getCurrentModule();
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkExport_spec__1___redArg(lean_object* v___x_445_, lean_object* v_a_446_, lean_object* v_as_x27_447_, lean_object* v_b_448_){
_start:
{
if (lean_obj_tag(v_as_x27_447_) == 0)
{
lean_object* v___x_450_; 
lean_dec_ref(v_a_446_);
v___x_450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_450_, 0, v_b_448_);
return v___x_450_;
}
else
{
lean_object* v_head_451_; lean_object* v_tail_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v_head_451_ = lean_ctor_get(v_as_x27_447_, 0);
v_tail_452_ = lean_ctor_get(v_as_x27_447_, 1);
v___x_453_ = lean_box(0);
v___x_454_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Lemmas______macroRules__Std__DTreeMap__Internal__Impl__tacticSimp__to__model_x5b___x5dUsing____1_spec__1___redArg(v___x_445_, v_head_451_);
if (lean_obj_tag(v___x_454_) == 1)
{
lean_object* v_val_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_485_; 
v_val_455_ = lean_ctor_get(v___x_454_, 0);
v_isSharedCheck_485_ = !lean_is_exclusive(v___x_454_);
if (v_isSharedCheck_485_ == 0)
{
v___x_457_ = v___x_454_;
v_isShared_458_ = v_isSharedCheck_485_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_val_455_);
lean_dec(v___x_454_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_485_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_459_; 
lean_inc(v_head_451_);
lean_inc_ref(v_a_446_);
v___x_459_ = lean_environment_find(v_a_446_, v_head_451_);
if (lean_obj_tag(v___x_459_) == 1)
{
lean_object* v_val_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_476_; 
v_val_460_ = lean_ctor_get(v___x_459_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v___x_459_);
if (v_isSharedCheck_476_ == 0)
{
v___x_462_ = v___x_459_;
v_isShared_463_ = v_isSharedCheck_476_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_val_460_);
lean_dec(v___x_459_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_476_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
uint8_t v___x_464_; 
v___x_464_ = l_Lean_instBEqConstantInfo_beq(v_val_455_, v_val_460_);
lean_dec(v_val_460_);
lean_dec(v_val_455_);
if (v___x_464_ == 0)
{
uint8_t v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_470_; 
lean_dec_ref(v_a_446_);
v___x_465_ = 1;
v___x_466_ = ((lean_object*)(l_List_forIn_x27_loop___at___00checkExport_spec__1___redArg___closed__0));
lean_inc(v_head_451_);
v___x_467_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_451_, v___x_465_);
v___x_468_ = lean_string_append(v___x_466_, v___x_467_);
lean_dec_ref(v___x_467_);
if (v_isShared_463_ == 0)
{
lean_ctor_set_tag(v___x_462_, 18);
lean_ctor_set(v___x_462_, 0, v___x_468_);
v___x_470_ = v___x_462_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v___x_468_);
v___x_470_ = v_reuseFailAlloc_474_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
lean_object* v___x_472_; 
if (v_isShared_458_ == 0)
{
lean_ctor_set(v___x_457_, 0, v___x_470_);
v___x_472_ = v___x_457_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v___x_470_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
}
else
{
lean_del_object(v___x_462_);
lean_del_object(v___x_457_);
v_as_x27_447_ = v_tail_452_;
v_b_448_ = v___x_453_;
goto _start;
}
}
}
else
{
lean_object* v___x_477_; uint8_t v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_482_; 
lean_dec(v___x_459_);
lean_dec(v_val_455_);
lean_dec_ref(v_a_446_);
v___x_477_ = ((lean_object*)(l_List_forIn_x27_loop___at___00checkExport_spec__1___redArg___closed__1));
v___x_478_ = 1;
lean_inc(v_head_451_);
v___x_479_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_451_, v___x_478_);
v___x_480_ = lean_string_append(v___x_477_, v___x_479_);
lean_dec_ref(v___x_479_);
if (v_isShared_458_ == 0)
{
lean_ctor_set_tag(v___x_457_, 18);
lean_ctor_set(v___x_457_, 0, v___x_480_);
v___x_482_ = v___x_457_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v___x_480_);
v___x_482_ = v_reuseFailAlloc_484_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
lean_object* v___x_483_; 
v___x_483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
return v___x_483_;
}
}
}
}
else
{
lean_dec(v___x_454_);
v_as_x27_447_ = v_tail_452_;
v_b_448_ = v___x_453_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkExport_spec__1___redArg___boxed(lean_object* v___x_487_, lean_object* v_a_488_, lean_object* v_as_x27_489_, lean_object* v_b_490_, lean_object* v___y_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_List_forIn_x27_loop___at___00checkExport_spec__1___redArg(v___x_487_, v_a_488_, v_as_x27_489_, v_b_490_);
lean_dec(v_as_x27_489_);
lean_dec_ref(v___x_487_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00checkExport_spec__0(lean_object* v_x_493_, lean_object* v_x_494_){
_start:
{
if (lean_obj_tag(v_x_494_) == 0)
{
return v_x_493_;
}
else
{
lean_object* v_head_495_; lean_object* v_tail_496_; lean_object* v___x_497_; 
v_head_495_ = lean_ctor_get(v_x_494_, 0);
v_tail_496_ = lean_ctor_get(v_x_494_, 1);
v___x_497_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg(v_x_493_, v_head_495_);
v_x_493_ = v___x_497_;
v_x_494_ = v_tail_496_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00checkExport_spec__0___boxed(lean_object* v_x_499_, lean_object* v_x_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_List_foldl___at___00checkExport_spec__0(v_x_499_, v_x_500_);
lean_dec(v_x_500_);
return v_res_501_;
}
}
static lean_object* _init_l_checkExport___boxed__const__1(void){
_start:
{
uint32_t v___x_533_; lean_object* v___x_534_; 
v___x_533_ = 1;
v___x_534_ = lean_box_uint32(v___x_533_);
return v___x_534_;
}
}
static lean_object* _init_l_checkExport___boxed__const__2(void){
_start:
{
uint32_t v___x_535_; lean_object* v___x_536_; 
v___x_535_ = 0;
v___x_536_ = lean_box_uint32(v___x_535_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_checkExport(lean_object* v_args_537_, uint8_t v_silent_538_){
_start:
{
lean_object* v_a_547_; 
if (lean_obj_tag(v_args_537_) == 1)
{
lean_object* v_tail_569_; 
v_tail_569_ = lean_ctor_get(v_args_537_, 1);
if (lean_obj_tag(v_tail_569_) == 0)
{
lean_object* v_head_570_; uint8_t v___x_571_; lean_object* v___x_572_; 
v_head_570_ = lean_ctor_get(v_args_537_, 0);
v___x_571_ = 0;
v___x_572_ = lean_io_prim_handle_mk(v_head_570_, v___x_571_);
if (lean_obj_tag(v___x_572_) == 0)
{
lean_object* v_a_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v_a_573_ = lean_ctor_get(v___x_572_, 0);
lean_inc(v_a_573_);
lean_dec_ref_known(v___x_572_, 1);
v___x_574_ = lean_stream_of_handle(v_a_573_);
v___x_575_ = l_LeanExport_parseStream(v___x_574_);
if (lean_obj_tag(v___x_575_) == 0)
{
lean_object* v_a_576_; uint32_t v___x_577_; lean_object* v___x_578_; 
v_a_576_ = lean_ctor_get(v___x_575_, 0);
lean_inc(v_a_576_);
lean_dec_ref_known(v___x_575_, 1);
v___x_577_ = 0;
v___x_578_ = l_Lean_mkEmptyEnvironment(v___x_577_);
if (lean_obj_tag(v___x_578_) == 0)
{
lean_object* v_a_579_; lean_object* v_constMap_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v_a_579_ = lean_ctor_get(v___x_578_, 0);
lean_inc(v_a_579_);
lean_dec_ref_known(v___x_578_, 1);
v_constMap_580_ = lean_ctor_get(v_a_576_, 0);
lean_inc_ref_n(v_constMap_580_, 2);
lean_dec(v_a_576_);
v___x_581_ = lean_elab_environment_to_kernel_env(v_a_579_);
v___x_582_ = ((lean_object*)(l_checkExport___closed__11));
v___x_583_ = l_List_foldl___at___00checkExport_spec__0(v_constMap_580_, v___x_582_);
v___x_584_ = l_Lean_Kernel_Environment_replay(v___x_583_, v___x_581_);
lean_dec_ref(v___x_583_);
if (lean_obj_tag(v___x_584_) == 0)
{
lean_object* v_a_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v_a_585_ = lean_ctor_get(v___x_584_, 0);
lean_inc(v_a_585_);
lean_dec_ref_known(v___x_584_, 1);
v___x_586_ = ((lean_object*)(l_checkExport___closed__12));
v___x_587_ = l_println(v___x_586_, v_silent_538_);
if (lean_obj_tag(v___x_587_) == 0)
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
lean_dec_ref_known(v___x_587_, 1);
v___x_588_ = ((lean_object*)(l_checkExport___closed__14));
v___x_589_ = lean_box(0);
v___x_590_ = l_List_forIn_x27_loop___at___00checkExport_spec__1___redArg(v_constMap_580_, v_a_585_, v___x_588_, v___x_589_);
lean_dec_ref(v_constMap_580_);
if (lean_obj_tag(v___x_590_) == 0)
{
lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_598_; 
v_isSharedCheck_598_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_598_ == 0)
{
lean_object* v_unused_599_; 
v_unused_599_ = lean_ctor_get(v___x_590_, 0);
lean_dec(v_unused_599_);
v___x_592_ = v___x_590_;
v_isShared_593_ = v_isSharedCheck_598_;
goto v_resetjp_591_;
}
else
{
lean_dec(v___x_590_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_598_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_594_; lean_object* v___x_596_; 
v___x_594_ = l_checkExport___boxed__const__2;
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 0, v___x_594_);
v___x_596_ = v___x_592_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v___x_594_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
}
else
{
lean_object* v_a_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
v_a_600_ = lean_ctor_get(v___x_590_, 0);
lean_inc(v_a_600_);
lean_dec_ref_known(v___x_590_, 1);
v___x_601_ = ((lean_object*)(l_checkExport___closed__15));
v___x_602_ = lean_io_error_to_string(v_a_600_);
v___x_603_ = lean_string_append(v___x_601_, v___x_602_);
lean_dec_ref(v___x_602_);
v___x_604_ = l_println(v___x_603_, v_silent_538_);
if (lean_obj_tag(v___x_604_) == 0)
{
lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_612_; 
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_612_ == 0)
{
lean_object* v_unused_613_; 
v_unused_613_ = lean_ctor_get(v___x_604_, 0);
lean_dec(v_unused_613_);
v___x_606_ = v___x_604_;
v_isShared_607_ = v_isSharedCheck_612_;
goto v_resetjp_605_;
}
else
{
lean_dec(v___x_604_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_612_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_608_; lean_object* v___x_610_; 
v___x_608_ = l_checkExport___boxed__const__1;
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 0, v___x_608_);
v___x_610_ = v___x_606_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v___x_608_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
}
else
{
lean_object* v_a_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_621_; 
v_a_614_ = lean_ctor_get(v___x_604_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_621_ == 0)
{
v___x_616_ = v___x_604_;
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_a_614_);
lean_dec(v___x_604_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___x_619_; 
if (v_isShared_617_ == 0)
{
v___x_619_ = v___x_616_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_a_614_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
}
}
}
else
{
lean_object* v_a_622_; 
lean_dec(v_a_585_);
lean_dec_ref(v_constMap_580_);
v_a_622_ = lean_ctor_get(v___x_587_, 0);
lean_inc(v_a_622_);
lean_dec_ref_known(v___x_587_, 1);
v_a_547_ = v_a_622_;
goto v___jp_546_;
}
}
else
{
lean_object* v_a_623_; 
lean_dec_ref(v_constMap_580_);
v_a_623_ = lean_ctor_get(v___x_584_, 0);
lean_inc(v_a_623_);
lean_dec_ref_known(v___x_584_, 1);
v_a_547_ = v_a_623_;
goto v___jp_546_;
}
}
else
{
lean_object* v_a_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_631_; 
lean_dec(v_a_576_);
v_a_624_ = lean_ctor_get(v___x_578_, 0);
v_isSharedCheck_631_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_631_ == 0)
{
v___x_626_ = v___x_578_;
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_a_624_);
lean_dec(v___x_578_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_629_; 
if (v_isShared_627_ == 0)
{
v___x_629_ = v___x_626_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_a_624_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
}
}
else
{
lean_object* v_a_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_639_; 
v_a_632_ = lean_ctor_get(v___x_575_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_639_ == 0)
{
v___x_634_ = v___x_575_;
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_a_632_);
lean_dec(v___x_575_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_637_; 
if (v_isShared_635_ == 0)
{
v___x_637_ = v___x_634_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_a_632_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
}
else
{
lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_647_; 
v_a_640_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_647_ == 0)
{
v___x_642_ = v___x_572_;
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v___x_572_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_645_; 
if (v_isShared_643_ == 0)
{
v___x_645_ = v___x_642_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_a_640_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
}
else
{
goto v___jp_540_;
}
}
else
{
goto v___jp_540_;
}
v___jp_540_:
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_541_ = ((lean_object*)(l_checkExport___closed__0));
v___x_542_ = l_List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1(v_args_537_);
v___x_543_ = lean_string_append(v___x_541_, v___x_542_);
lean_dec_ref(v___x_542_);
v___x_544_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
v___x_545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_545_, 0, v___x_544_);
return v___x_545_;
}
v___jp_546_:
{
lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_548_ = ((lean_object*)(l_checkExport___closed__1));
v___x_549_ = lean_io_error_to_string(v_a_547_);
v___x_550_ = lean_string_append(v___x_548_, v___x_549_);
lean_dec_ref(v___x_549_);
v___x_551_ = l_println(v___x_550_, v_silent_538_);
if (lean_obj_tag(v___x_551_) == 0)
{
lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_559_; 
v_isSharedCheck_559_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_559_ == 0)
{
lean_object* v_unused_560_; 
v_unused_560_ = lean_ctor_get(v___x_551_, 0);
lean_dec(v_unused_560_);
v___x_553_ = v___x_551_;
v_isShared_554_ = v_isSharedCheck_559_;
goto v_resetjp_552_;
}
else
{
lean_dec(v___x_551_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_559_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v___x_555_; lean_object* v___x_557_; 
v___x_555_ = l_checkExport___boxed__const__1;
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 0, v___x_555_);
v___x_557_ = v___x_553_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v___x_555_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
return v___x_557_;
}
}
}
else
{
lean_object* v_a_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_568_; 
v_a_561_ = lean_ctor_get(v___x_551_, 0);
v_isSharedCheck_568_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_568_ == 0)
{
v___x_563_ = v___x_551_;
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_a_561_);
lean_dec(v___x_551_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_566_; 
if (v_isShared_564_ == 0)
{
v___x_566_ = v___x_563_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_a_561_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
return v___x_566_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_checkExport___boxed(lean_object* v_args_648_, lean_object* v_silent_649_, lean_object* v_a_650_){
_start:
{
uint8_t v_silent_boxed_651_; lean_object* v_res_652_; 
v_silent_boxed_651_ = lean_unbox(v_silent_649_);
v_res_652_ = l_checkExport(v_args_648_, v_silent_boxed_651_);
lean_dec(v_args_648_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkExport_spec__1(lean_object* v___x_653_, lean_object* v_a_654_, lean_object* v_as_655_, lean_object* v_as_x27_656_, lean_object* v_b_657_, lean_object* v_a_658_){
_start:
{
lean_object* v___x_660_; 
v___x_660_ = l_List_forIn_x27_loop___at___00checkExport_spec__1___redArg(v___x_653_, v_a_654_, v_as_x27_656_, v_b_657_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkExport_spec__1___boxed(lean_object* v___x_661_, lean_object* v_a_662_, lean_object* v_as_663_, lean_object* v_as_x27_664_, lean_object* v_b_665_, lean_object* v_a_666_, lean_object* v___y_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l_List_forIn_x27_loop___at___00checkExport_spec__1(v___x_661_, v_a_662_, v_as_663_, v_as_x27_664_, v_b_665_, v_a_666_);
lean_dec(v_as_x27_664_);
lean_dec(v_as_663_);
lean_dec_ref(v___x_661_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00checkOlean_spec__3(uint8_t v_verbose_671_, uint8_t v_silent_672_, lean_object* v_as_673_, size_t v_sz_674_, size_t v_i_675_, lean_object* v_b_676_){
_start:
{
uint8_t v___x_678_; 
v___x_678_ = lean_usize_dec_lt(v_i_675_, v_sz_674_);
if (v___x_678_ == 0)
{
lean_object* v___x_679_; 
v___x_679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_679_, 0, v_b_676_);
return v___x_679_;
}
else
{
lean_object* v_a_680_; lean_object* v_fst_681_; lean_object* v_snd_682_; lean_object* v___x_683_; 
v_a_680_ = lean_array_uget_borrowed(v_as_673_, v_i_675_);
v_fst_681_ = lean_ctor_get(v_a_680_, 0);
v_snd_682_ = lean_ctor_get(v_a_680_, 1);
v___x_683_ = lean_box(0);
if (v_verbose_671_ == 0)
{
goto v___jp_684_;
}
else
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_702_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00checkOlean_spec__3___closed__1));
lean_inc(v_fst_681_);
v___x_703_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_681_, v_verbose_671_);
v___x_704_ = lean_string_append(v___x_702_, v___x_703_);
lean_dec_ref(v___x_703_);
v___x_705_ = l_println(v___x_704_, v_silent_672_);
if (lean_obj_tag(v___x_705_) == 0)
{
lean_dec_ref_known(v___x_705_, 1);
goto v___jp_684_;
}
else
{
return v___x_705_;
}
}
v___jp_684_:
{
lean_object* v___x_685_; 
lean_inc(v_snd_682_);
v___x_685_ = lean_task_get_own(v_snd_682_);
if (lean_obj_tag(v___x_685_) == 0)
{
lean_object* v_a_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
v_a_686_ = lean_ctor_get(v___x_685_, 0);
lean_inc(v_a_686_);
lean_dec_ref_known(v___x_685_, 1);
v___x_687_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00checkOlean_spec__3___closed__0));
lean_inc(v_fst_681_);
v___x_688_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_681_, v___x_678_);
v___x_689_ = lean_string_append(v___x_687_, v___x_688_);
lean_dec_ref(v___x_688_);
v___x_690_ = l_IO_eprintln___at___00__private_Init_System_IO_0__IO_eprintlnAux_spec__0(v___x_689_);
if (lean_obj_tag(v___x_690_) == 0)
{
lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_697_; 
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_690_);
if (v_isSharedCheck_697_ == 0)
{
lean_object* v_unused_698_; 
v_unused_698_ = lean_ctor_get(v___x_690_, 0);
lean_dec(v_unused_698_);
v___x_692_ = v___x_690_;
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
else
{
lean_dec(v___x_690_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_695_; 
if (v_isShared_693_ == 0)
{
lean_ctor_set_tag(v___x_692_, 1);
lean_ctor_set(v___x_692_, 0, v_a_686_);
v___x_695_ = v___x_692_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_a_686_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
}
else
{
lean_dec(v_a_686_);
return v___x_690_;
}
}
else
{
size_t v___x_699_; size_t v___x_700_; 
lean_dec(v___x_685_);
v___x_699_ = ((size_t)1ULL);
v___x_700_ = lean_usize_add(v_i_675_, v___x_699_);
v_i_675_ = v___x_700_;
v_b_676_ = v___x_683_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00checkOlean_spec__3___boxed(lean_object* v_verbose_706_, lean_object* v_silent_707_, lean_object* v_as_708_, lean_object* v_sz_709_, lean_object* v_i_710_, lean_object* v_b_711_, lean_object* v___y_712_){
_start:
{
uint8_t v_verbose_boxed_713_; uint8_t v_silent_boxed_714_; size_t v_sz_boxed_715_; size_t v_i_boxed_716_; lean_object* v_res_717_; 
v_verbose_boxed_713_ = lean_unbox(v_verbose_706_);
v_silent_boxed_714_ = lean_unbox(v_silent_707_);
v_sz_boxed_715_ = lean_unbox_usize(v_sz_709_);
lean_dec(v_sz_709_);
v_i_boxed_716_ = lean_unbox_usize(v_i_710_);
lean_dec(v_i_710_);
v_res_717_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00checkOlean_spec__3(v_verbose_boxed_713_, v_silent_boxed_714_, v_as_708_, v_sz_boxed_715_, v_i_boxed_716_, v_b_711_);
lean_dec_ref(v_as_708_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__2___redArg___lam__0(lean_object* v_head_718_){
_start:
{
lean_object* v___x_720_; 
v___x_720_ = l_replayFromImports(v_head_718_);
if (lean_obj_tag(v___x_720_) == 0)
{
lean_object* v_a_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_728_; 
v_a_721_ = lean_ctor_get(v___x_720_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_728_ == 0)
{
v___x_723_ = v___x_720_;
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_a_721_);
lean_dec(v___x_720_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_726_; 
if (v_isShared_724_ == 0)
{
lean_ctor_set_tag(v___x_723_, 1);
v___x_726_ = v___x_723_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_a_721_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
return v___x_726_;
}
}
}
else
{
lean_object* v_a_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_736_; 
v_a_729_ = lean_ctor_get(v___x_720_, 0);
v_isSharedCheck_736_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_736_ == 0)
{
v___x_731_ = v___x_720_;
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_a_729_);
lean_dec(v___x_720_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_734_; 
if (v_isShared_732_ == 0)
{
lean_ctor_set_tag(v___x_731_, 0);
v___x_734_ = v___x_731_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_a_729_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__2___redArg___lam__0___boxed(lean_object* v_head_737_, lean_object* v___y_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_List_forIn_x27_loop___at___00checkOlean_spec__2___redArg___lam__0(v_head_737_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__2___redArg(lean_object* v_as_x27_740_, lean_object* v_b_741_){
_start:
{
if (lean_obj_tag(v_as_x27_740_) == 0)
{
lean_object* v___x_743_; 
v___x_743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_743_, 0, v_b_741_);
return v___x_743_;
}
else
{
lean_object* v_head_744_; lean_object* v_tail_745_; lean_object* v___f_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
v_head_744_ = lean_ctor_get(v_as_x27_740_, 0);
v_tail_745_ = lean_ctor_get(v_as_x27_740_, 1);
lean_inc_n(v_head_744_, 2);
v___f_746_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00checkOlean_spec__2___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_746_, 0, v_head_744_);
v___x_747_ = lean_unsigned_to_nat(0u);
v___x_748_ = lean_io_as_task(v___f_746_, v___x_747_);
v___x_749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_749_, 0, v_head_744_);
lean_ctor_set(v___x_749_, 1, v___x_748_);
v___x_750_ = lean_array_push(v_b_741_, v___x_749_);
v_as_x27_740_ = v_tail_745_;
v_b_741_ = v___x_750_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__2___redArg___boxed(lean_object* v_as_x27_752_, lean_object* v_b_753_, lean_object* v___y_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l_List_forIn_x27_loop___at___00checkOlean_spec__2___redArg(v_as_x27_752_, v_b_753_);
lean_dec(v_as_x27_752_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00checkOlean_spec__5(lean_object* v_x_757_, lean_object* v_x_758_){
_start:
{
if (lean_obj_tag(v_x_757_) == 0)
{
lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_760_ = l_List_reverse___redArg(v_x_758_);
v___x_761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_761_, 0, v___x_760_);
return v___x_761_;
}
else
{
lean_object* v_head_762_; lean_object* v_tail_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_777_; 
v_head_762_ = lean_ctor_get(v_x_757_, 0);
v_tail_763_ = lean_ctor_get(v_x_757_, 1);
v_isSharedCheck_777_ = !lean_is_exclusive(v_x_757_);
if (v_isSharedCheck_777_ == 0)
{
v___x_765_ = v_x_757_;
v_isShared_766_ = v_isSharedCheck_777_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_tail_763_);
lean_inc(v_head_762_);
lean_dec(v_x_757_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_777_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_767_; uint8_t v___x_768_; 
lean_inc(v_head_762_);
v___x_767_ = l_String_toName(v_head_762_);
v___x_768_ = l_Lean_Name_isAnonymous(v___x_767_);
if (v___x_768_ == 0)
{
lean_object* v___x_770_; 
lean_dec(v_head_762_);
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 1, v_x_758_);
lean_ctor_set(v___x_765_, 0, v___x_767_);
v___x_770_ = v___x_765_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v___x_767_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v_x_758_);
v___x_770_ = v_reuseFailAlloc_772_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
v_x_757_ = v_tail_763_;
v_x_758_ = v___x_770_;
goto _start;
}
}
else
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
lean_dec(v___x_767_);
lean_del_object(v___x_765_);
lean_dec(v_tail_763_);
lean_dec(v_x_758_);
v___x_773_ = ((lean_object*)(l_List_mapM_loop___at___00checkOlean_spec__5___closed__0));
v___x_774_ = lean_string_append(v___x_773_, v_head_762_);
lean_dec(v_head_762_);
v___x_775_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_775_, 0, v___x_774_);
v___x_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_776_, 0, v___x_775_);
return v___x_776_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00checkOlean_spec__5___boxed(lean_object* v_x_778_, lean_object* v_x_779_, lean_object* v___y_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l_List_mapM_loop___at___00checkOlean_spec__5(v_x_778_, v_x_779_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00checkOlean_spec__0(lean_object* v_val_782_, lean_object* v_a_783_, uint8_t v_fresh_784_, lean_object* v_as_785_, size_t v_sz_786_, size_t v_i_787_, lean_object* v_b_788_){
_start:
{
lean_object* v_a_791_; uint8_t v___x_795_; 
v___x_795_ = lean_usize_dec_lt(v_i_787_, v_sz_786_);
if (v___x_795_ == 0)
{
lean_object* v___x_796_; 
v___x_796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_796_, 0, v_b_788_);
return v___x_796_;
}
else
{
lean_object* v_fst_797_; lean_object* v_snd_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_828_; 
v_fst_797_ = lean_ctor_get(v_b_788_, 0);
v_snd_798_ = lean_ctor_get(v_b_788_, 1);
v_isSharedCheck_828_ = !lean_is_exclusive(v_b_788_);
if (v_isSharedCheck_828_ == 0)
{
v___x_800_ = v_b_788_;
v_isShared_801_ = v_isSharedCheck_828_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_snd_798_);
lean_inc(v_fst_797_);
lean_dec(v_b_788_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_828_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v_a_802_; lean_object* v___x_803_; 
v_a_802_ = lean_array_uget_borrowed(v_as_785_, v_i_787_);
lean_inc(v_a_802_);
v___x_803_ = l_Lean_searchModuleNameOfFileName(v_a_802_, v_val_782_);
if (lean_obj_tag(v___x_803_) == 0)
{
lean_object* v_a_804_; lean_object* v___y_806_; 
v_a_804_ = lean_ctor_get(v___x_803_, 0);
lean_inc(v_a_804_);
lean_dec_ref_known(v___x_803_, 1);
if (lean_obj_tag(v_a_804_) == 1)
{
lean_object* v_val_811_; 
v_val_811_ = lean_ctor_get(v_a_804_, 0);
lean_inc(v_val_811_);
lean_dec_ref_known(v_a_804_, 1);
if (v_fresh_784_ == 0)
{
uint8_t v___x_818_; 
v___x_818_ = l_Lean_Name_isPrefixOf(v_a_783_, v_val_811_);
if (v___x_818_ == 0)
{
goto v___jp_815_;
}
else
{
lean_dec(v_snd_798_);
goto v___jp_812_;
}
}
else
{
goto v___jp_815_;
}
v___jp_812_:
{
uint8_t v___x_813_; 
v___x_813_ = l_List_elem___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_4052238930____hygCtx___hyg_2__spec__1(v_val_811_, v_fst_797_);
if (v___x_813_ == 0)
{
lean_object* v___x_814_; 
v___x_814_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_814_, 0, v_val_811_);
lean_ctor_set(v___x_814_, 1, v_fst_797_);
v___y_806_ = v___x_814_;
goto v___jp_805_;
}
else
{
lean_dec(v_val_811_);
v___y_806_ = v_fst_797_;
goto v___jp_805_;
}
}
v___jp_815_:
{
uint8_t v___x_816_; 
v___x_816_ = lean_name_eq(v_a_783_, v_val_811_);
if (v___x_816_ == 0)
{
lean_object* v___x_817_; 
lean_dec(v_val_811_);
lean_del_object(v___x_800_);
v___x_817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_817_, 0, v_fst_797_);
lean_ctor_set(v___x_817_, 1, v_snd_798_);
v_a_791_ = v___x_817_;
goto v___jp_790_;
}
else
{
lean_dec(v_snd_798_);
goto v___jp_812_;
}
}
}
else
{
lean_object* v___x_819_; 
lean_dec(v_a_804_);
lean_del_object(v___x_800_);
v___x_819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_819_, 0, v_fst_797_);
lean_ctor_set(v___x_819_, 1, v_snd_798_);
v_a_791_ = v___x_819_;
goto v___jp_790_;
}
v___jp_805_:
{
lean_object* v___x_807_; lean_object* v___x_809_; 
v___x_807_ = lean_box(v___x_795_);
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 1, v___x_807_);
lean_ctor_set(v___x_800_, 0, v___y_806_);
v___x_809_ = v___x_800_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v___y_806_);
lean_ctor_set(v_reuseFailAlloc_810_, 1, v___x_807_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
v_a_791_ = v___x_809_;
goto v___jp_790_;
}
}
}
else
{
lean_object* v_a_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_827_; 
lean_del_object(v___x_800_);
lean_dec(v_snd_798_);
lean_dec(v_fst_797_);
v_a_820_ = lean_ctor_get(v___x_803_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_827_ == 0)
{
v___x_822_ = v___x_803_;
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_a_820_);
lean_dec(v___x_803_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_825_; 
if (v_isShared_823_ == 0)
{
v___x_825_ = v___x_822_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_a_820_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
}
}
}
v___jp_790_:
{
size_t v___x_792_; size_t v___x_793_; 
v___x_792_ = ((size_t)1ULL);
v___x_793_ = lean_usize_add(v_i_787_, v___x_792_);
v_i_787_ = v___x_793_;
v_b_788_ = v_a_791_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00checkOlean_spec__0___boxed(lean_object* v_val_829_, lean_object* v_a_830_, lean_object* v_fresh_831_, lean_object* v_as_832_, lean_object* v_sz_833_, lean_object* v_i_834_, lean_object* v_b_835_, lean_object* v___y_836_){
_start:
{
uint8_t v_fresh_boxed_837_; size_t v_sz_boxed_838_; size_t v_i_boxed_839_; lean_object* v_res_840_; 
v_fresh_boxed_837_ = lean_unbox(v_fresh_831_);
v_sz_boxed_838_ = lean_unbox_usize(v_sz_833_);
lean_dec(v_sz_833_);
v_i_boxed_839_ = lean_unbox_usize(v_i_834_);
lean_dec(v_i_834_);
v_res_840_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00checkOlean_spec__0(v_val_829_, v_a_830_, v_fresh_boxed_837_, v_as_832_, v_sz_boxed_838_, v_i_boxed_839_, v_b_835_);
lean_dec_ref(v_as_832_);
lean_dec(v_a_830_);
lean_dec(v_val_829_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__1___redArg(lean_object* v_val_843_, uint8_t v_fresh_844_, lean_object* v_as_x27_845_, lean_object* v_b_846_){
_start:
{
if (lean_obj_tag(v_as_x27_845_) == 0)
{
lean_object* v___x_848_; 
v___x_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_848_, 0, v_b_846_);
return v___x_848_;
}
else
{
lean_object* v_head_849_; lean_object* v_tail_850_; uint8_t v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
v_head_849_ = lean_ctor_get(v_as_x27_845_, 0);
v_tail_850_ = lean_ctor_get(v_as_x27_845_, 1);
v___x_851_ = 0;
v___x_852_ = ((lean_object*)(l_List_forIn_x27_loop___at___00checkOlean_spec__1___redArg___closed__0));
v___x_853_ = l_Lean_SearchPath_findAllWithExt(v_val_843_, v___x_852_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_object* v_a_854_; lean_object* v___x_855_; lean_object* v___x_856_; size_t v_sz_857_; size_t v___x_858_; lean_object* v___x_859_; 
v_a_854_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_a_854_);
lean_dec_ref_known(v___x_853_, 1);
v___x_855_ = lean_box(v___x_851_);
v___x_856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_856_, 0, v_b_846_);
lean_ctor_set(v___x_856_, 1, v___x_855_);
v_sz_857_ = lean_array_size(v_a_854_);
v___x_858_ = ((size_t)0ULL);
v___x_859_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00checkOlean_spec__0(v_val_843_, v_head_849_, v_fresh_844_, v_a_854_, v_sz_857_, v___x_858_, v___x_856_);
lean_dec(v_a_854_);
if (lean_obj_tag(v___x_859_) == 0)
{
lean_object* v_a_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_876_; 
v_a_860_ = lean_ctor_get(v___x_859_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_876_ == 0)
{
v___x_862_ = v___x_859_;
v_isShared_863_ = v_isSharedCheck_876_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_a_860_);
lean_dec(v___x_859_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_876_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v_snd_864_; uint8_t v___x_865_; 
v_snd_864_ = lean_ctor_get(v_a_860_, 1);
v___x_865_ = lean_unbox(v_snd_864_);
if (v___x_865_ == 0)
{
uint8_t v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_872_; 
lean_dec(v_a_860_);
v___x_866_ = 1;
v___x_867_ = ((lean_object*)(l_List_forIn_x27_loop___at___00checkOlean_spec__1___redArg___closed__1));
lean_inc(v_head_849_);
v___x_868_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_849_, v___x_866_);
v___x_869_ = lean_string_append(v___x_867_, v___x_868_);
lean_dec_ref(v___x_868_);
v___x_870_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_870_, 0, v___x_869_);
if (v_isShared_863_ == 0)
{
lean_ctor_set_tag(v___x_862_, 1);
lean_ctor_set(v___x_862_, 0, v___x_870_);
v___x_872_ = v___x_862_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v___x_870_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
else
{
lean_object* v_fst_874_; 
lean_del_object(v___x_862_);
v_fst_874_ = lean_ctor_get(v_a_860_, 0);
lean_inc(v_fst_874_);
lean_dec(v_a_860_);
v_as_x27_845_ = v_tail_850_;
v_b_846_ = v_fst_874_;
goto _start;
}
}
}
else
{
lean_object* v_a_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_884_; 
v_a_877_ = lean_ctor_get(v___x_859_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_884_ == 0)
{
v___x_879_ = v___x_859_;
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_a_877_);
lean_dec(v___x_859_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_882_; 
if (v_isShared_880_ == 0)
{
v___x_882_ = v___x_879_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_a_877_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
}
else
{
lean_object* v_a_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_892_; 
lean_dec(v_b_846_);
v_a_885_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_892_ == 0)
{
v___x_887_ = v___x_853_;
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_a_885_);
lean_dec(v___x_853_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_890_; 
if (v_isShared_888_ == 0)
{
v___x_890_ = v___x_887_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_a_885_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__1___redArg___boxed(lean_object* v_val_893_, lean_object* v_fresh_894_, lean_object* v_as_x27_895_, lean_object* v_b_896_, lean_object* v___y_897_){
_start:
{
uint8_t v_fresh_boxed_898_; lean_object* v_res_899_; 
v_fresh_boxed_898_ = lean_unbox(v_fresh_894_);
v_res_899_ = l_List_forIn_x27_loop___at___00checkOlean_spec__1___redArg(v_val_893_, v_fresh_boxed_898_, v_as_x27_895_, v_b_896_);
lean_dec(v_as_x27_895_);
lean_dec(v_val_893_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__4___redArg(uint8_t v_verbose_901_, uint8_t v_silent_902_, lean_object* v_as_x27_903_, lean_object* v_b_904_){
_start:
{
if (lean_obj_tag(v_as_x27_903_) == 0)
{
lean_object* v___x_906_; 
v___x_906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_906_, 0, v_b_904_);
return v___x_906_;
}
else
{
lean_object* v_head_907_; lean_object* v_tail_908_; lean_object* v___x_909_; 
v_head_907_ = lean_ctor_get(v_as_x27_903_, 0);
v_tail_908_ = lean_ctor_get(v_as_x27_903_, 1);
v___x_909_ = lean_box(0);
if (v_verbose_901_ == 0)
{
goto v___jp_910_;
}
else
{
lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_913_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00checkOlean_spec__3___closed__1));
lean_inc(v_head_907_);
v___x_914_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_907_, v_verbose_901_);
v___x_915_ = lean_string_append(v___x_913_, v___x_914_);
lean_dec_ref(v___x_914_);
v___x_916_ = ((lean_object*)(l_List_forIn_x27_loop___at___00checkOlean_spec__4___redArg___closed__0));
v___x_917_ = lean_string_append(v___x_915_, v___x_916_);
v___x_918_ = l_println(v___x_917_, v_silent_902_);
if (lean_obj_tag(v___x_918_) == 0)
{
lean_dec_ref_known(v___x_918_, 1);
goto v___jp_910_;
}
else
{
return v___x_918_;
}
}
v___jp_910_:
{
lean_object* v___x_911_; 
lean_inc(v_head_907_);
v___x_911_ = l_replayFromFresh(v_head_907_);
if (lean_obj_tag(v___x_911_) == 0)
{
lean_dec_ref_known(v___x_911_, 1);
v_as_x27_903_ = v_tail_908_;
v_b_904_ = v___x_909_;
goto _start;
}
else
{
return v___x_911_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__4___redArg___boxed(lean_object* v_verbose_919_, lean_object* v_silent_920_, lean_object* v_as_x27_921_, lean_object* v_b_922_, lean_object* v___y_923_){
_start:
{
uint8_t v_verbose_boxed_924_; uint8_t v_silent_boxed_925_; lean_object* v_res_926_; 
v_verbose_boxed_924_ = lean_unbox(v_verbose_919_);
v_silent_boxed_925_ = lean_unbox(v_silent_920_);
v_res_926_ = l_List_forIn_x27_loop___at___00checkOlean_spec__4___redArg(v_verbose_boxed_924_, v_silent_boxed_925_, v_as_x27_921_, v_b_922_);
lean_dec(v_as_x27_921_);
return v_res_926_;
}
}
LEAN_EXPORT lean_object* l_checkOlean(lean_object* v_args_931_, uint8_t v_fresh_932_, uint8_t v_verbose_933_, uint8_t v_silent_934_){
_start:
{
lean_object* v_targets_940_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1002_ = ((lean_object*)(l_checkOlean___closed__2));
v___x_1003_ = l_Lean_findSysroot(v___x_1002_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_a_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
lean_inc(v_a_1004_);
lean_dec_ref_known(v___x_1003_, 1);
v___x_1005_ = lean_box(0);
v___x_1006_ = l_Lean_initSearchPath(v_a_1004_, v___x_1005_);
if (lean_obj_tag(v___x_1006_) == 0)
{
lean_dec_ref_known(v___x_1006_, 1);
if (lean_obj_tag(v_args_931_) == 0)
{
lean_object* v___x_1007_; 
v___x_1007_ = l_getCurrentModule();
if (lean_obj_tag(v___x_1007_) == 0)
{
lean_object* v_a_1008_; lean_object* v___x_1009_; 
v_a_1008_ = lean_ctor_get(v___x_1007_, 0);
lean_inc(v_a_1008_);
lean_dec_ref_known(v___x_1007_, 1);
v___x_1009_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1009_, 0, v_a_1008_);
lean_ctor_set(v___x_1009_, 1, v___x_1005_);
v_targets_940_ = v___x_1009_;
goto v___jp_939_;
}
else
{
lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1017_; 
v_a_1010_ = lean_ctor_get(v___x_1007_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1012_ = v___x_1007_;
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_dec(v___x_1007_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___x_1015_; 
if (v_isShared_1013_ == 0)
{
v___x_1015_ = v___x_1012_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_a_1010_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
}
}
else
{
lean_object* v___x_1018_; 
v___x_1018_ = l_List_mapM_loop___at___00checkOlean_spec__5(v_args_931_, v___x_1005_);
if (lean_obj_tag(v___x_1018_) == 0)
{
lean_object* v_a_1019_; 
v_a_1019_ = lean_ctor_get(v___x_1018_, 0);
lean_inc(v_a_1019_);
lean_dec_ref_known(v___x_1018_, 1);
v_targets_940_ = v_a_1019_;
goto v___jp_939_;
}
else
{
lean_object* v_a_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1027_; 
v_a_1020_ = lean_ctor_get(v___x_1018_, 0);
v_isSharedCheck_1027_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_1022_ = v___x_1018_;
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_a_1020_);
lean_dec(v___x_1018_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___x_1025_; 
if (v_isShared_1023_ == 0)
{
v___x_1025_ = v___x_1022_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v_a_1020_);
v___x_1025_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
return v___x_1025_;
}
}
}
}
}
else
{
lean_object* v_a_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1035_; 
lean_dec(v_args_931_);
v_a_1028_ = lean_ctor_get(v___x_1006_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_1006_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1030_ = v___x_1006_;
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_a_1028_);
lean_dec(v___x_1006_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1033_; 
if (v_isShared_1031_ == 0)
{
v___x_1033_ = v___x_1030_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v_a_1028_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
}
}
}
}
else
{
lean_object* v_a_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1043_; 
lean_dec(v_args_931_);
v_a_1036_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1038_ = v___x_1003_;
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_a_1036_);
lean_dec(v___x_1003_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1041_; 
if (v_isShared_1039_ == 0)
{
v___x_1041_ = v___x_1038_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_a_1036_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
v___jp_936_:
{
lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_937_ = l_checkExport___boxed__const__2;
v___x_938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_938_, 0, v___x_937_);
return v___x_938_;
}
v___jp_939_:
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_941_ = lean_box(0);
v___x_942_ = l_Lean_searchPathRef;
v___x_943_ = lean_st_ref_get(v___x_942_);
v___x_944_ = l_List_forIn_x27_loop___at___00checkOlean_spec__1___redArg(v___x_943_, v_fresh_932_, v_targets_940_, v___x_941_);
lean_dec(v_targets_940_);
lean_dec(v___x_943_);
if (lean_obj_tag(v___x_944_) == 0)
{
if (v_fresh_932_ == 0)
{
lean_object* v_a_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
v_a_945_ = lean_ctor_get(v___x_944_, 0);
lean_inc(v_a_945_);
lean_dec_ref_known(v___x_944_, 1);
v___x_946_ = ((lean_object*)(l_checkOlean___closed__0));
v___x_947_ = l_List_forIn_x27_loop___at___00checkOlean_spec__2___redArg(v_a_945_, v___x_946_);
lean_dec(v_a_945_);
if (lean_obj_tag(v___x_947_) == 0)
{
lean_object* v_a_948_; lean_object* v___x_949_; size_t v_sz_950_; size_t v___x_951_; lean_object* v___x_952_; 
v_a_948_ = lean_ctor_get(v___x_947_, 0);
lean_inc(v_a_948_);
lean_dec_ref_known(v___x_947_, 1);
v___x_949_ = lean_box(0);
v_sz_950_ = lean_array_size(v_a_948_);
v___x_951_ = ((size_t)0ULL);
v___x_952_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00checkOlean_spec__3(v_verbose_933_, v_silent_934_, v_a_948_, v_sz_950_, v___x_951_, v___x_949_);
lean_dec(v_a_948_);
if (lean_obj_tag(v___x_952_) == 0)
{
lean_dec_ref_known(v___x_952_, 1);
goto v___jp_936_;
}
else
{
lean_object* v_a_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_960_; 
v_a_953_ = lean_ctor_get(v___x_952_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_960_ == 0)
{
v___x_955_ = v___x_952_;
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_a_953_);
lean_dec(v___x_952_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_958_; 
if (v_isShared_956_ == 0)
{
v___x_958_ = v___x_955_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_a_953_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
return v___x_958_;
}
}
}
}
else
{
lean_object* v_a_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_968_; 
v_a_961_ = lean_ctor_get(v___x_947_, 0);
v_isSharedCheck_968_ = !lean_is_exclusive(v___x_947_);
if (v_isSharedCheck_968_ == 0)
{
v___x_963_ = v___x_947_;
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_a_961_);
lean_dec(v___x_947_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___x_966_; 
if (v_isShared_964_ == 0)
{
v___x_966_ = v___x_963_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_a_961_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
return v___x_966_;
}
}
}
}
else
{
lean_object* v_a_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_993_; 
v_a_969_ = lean_ctor_get(v___x_944_, 0);
v_isSharedCheck_993_ = !lean_is_exclusive(v___x_944_);
if (v_isSharedCheck_993_ == 0)
{
v___x_971_ = v___x_944_;
v_isShared_972_ = v_isSharedCheck_993_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_a_969_);
lean_dec(v___x_944_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_993_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_973_; lean_object* v___x_974_; uint8_t v___x_975_; 
v___x_973_ = l_List_lengthTR___redArg(v_a_969_);
v___x_974_ = lean_unsigned_to_nat(1u);
v___x_975_ = lean_nat_dec_eq(v___x_973_, v___x_974_);
lean_dec(v___x_973_);
if (v___x_975_ == 0)
{
lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_981_; 
v___x_976_ = ((lean_object*)(l_checkOlean___closed__1));
v___x_977_ = l_List_toString___at___00Lean_Environment_AddConstAsyncResult_commitConst_spec__1(v_a_969_);
v___x_978_ = lean_string_append(v___x_976_, v___x_977_);
lean_dec_ref(v___x_977_);
v___x_979_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_979_, 0, v___x_978_);
if (v_isShared_972_ == 0)
{
lean_ctor_set_tag(v___x_971_, 1);
lean_ctor_set(v___x_971_, 0, v___x_979_);
v___x_981_ = v___x_971_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v___x_979_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
else
{
lean_object* v___x_983_; lean_object* v___x_984_; 
lean_del_object(v___x_971_);
v___x_983_ = lean_box(0);
v___x_984_ = l_List_forIn_x27_loop___at___00checkOlean_spec__4___redArg(v_verbose_933_, v_silent_934_, v_a_969_, v___x_983_);
lean_dec(v_a_969_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_dec_ref_known(v___x_984_, 1);
goto v___jp_936_;
}
else
{
lean_object* v_a_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_992_; 
v_a_985_ = lean_ctor_get(v___x_984_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_992_ == 0)
{
v___x_987_ = v___x_984_;
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_a_985_);
lean_dec(v___x_984_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_990_; 
if (v_isShared_988_ == 0)
{
v___x_990_ = v___x_987_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v_a_985_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1001_; 
v_a_994_ = lean_ctor_get(v___x_944_, 0);
v_isSharedCheck_1001_ = !lean_is_exclusive(v___x_944_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_996_ = v___x_944_;
v_isShared_997_ = v_isSharedCheck_1001_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_a_994_);
lean_dec(v___x_944_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1001_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v___x_999_; 
if (v_isShared_997_ == 0)
{
v___x_999_ = v___x_996_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v_a_994_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_checkOlean___boxed(lean_object* v_args_1044_, lean_object* v_fresh_1045_, lean_object* v_verbose_1046_, lean_object* v_silent_1047_, lean_object* v_a_1048_){
_start:
{
uint8_t v_fresh_boxed_1049_; uint8_t v_verbose_boxed_1050_; uint8_t v_silent_boxed_1051_; lean_object* v_res_1052_; 
v_fresh_boxed_1049_ = lean_unbox(v_fresh_1045_);
v_verbose_boxed_1050_ = lean_unbox(v_verbose_1046_);
v_silent_boxed_1051_ = lean_unbox(v_silent_1047_);
v_res_1052_ = l_checkOlean(v_args_1044_, v_fresh_boxed_1049_, v_verbose_boxed_1050_, v_silent_boxed_1051_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__1(lean_object* v_val_1053_, uint8_t v_fresh_1054_, lean_object* v_as_1055_, lean_object* v_as_x27_1056_, lean_object* v_b_1057_, lean_object* v_a_1058_){
_start:
{
lean_object* v___x_1060_; 
v___x_1060_ = l_List_forIn_x27_loop___at___00checkOlean_spec__1___redArg(v_val_1053_, v_fresh_1054_, v_as_x27_1056_, v_b_1057_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__1___boxed(lean_object* v_val_1061_, lean_object* v_fresh_1062_, lean_object* v_as_1063_, lean_object* v_as_x27_1064_, lean_object* v_b_1065_, lean_object* v_a_1066_, lean_object* v___y_1067_){
_start:
{
uint8_t v_fresh_boxed_1068_; lean_object* v_res_1069_; 
v_fresh_boxed_1068_ = lean_unbox(v_fresh_1062_);
v_res_1069_ = l_List_forIn_x27_loop___at___00checkOlean_spec__1(v_val_1061_, v_fresh_boxed_1068_, v_as_1063_, v_as_x27_1064_, v_b_1065_, v_a_1066_);
lean_dec(v_as_x27_1064_);
lean_dec(v_as_1063_);
lean_dec(v_val_1061_);
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__2(lean_object* v_as_1070_, lean_object* v_as_x27_1071_, lean_object* v_b_1072_, lean_object* v_a_1073_){
_start:
{
lean_object* v___x_1075_; 
v___x_1075_ = l_List_forIn_x27_loop___at___00checkOlean_spec__2___redArg(v_as_x27_1071_, v_b_1072_);
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__2___boxed(lean_object* v_as_1076_, lean_object* v_as_x27_1077_, lean_object* v_b_1078_, lean_object* v_a_1079_, lean_object* v___y_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l_List_forIn_x27_loop___at___00checkOlean_spec__2(v_as_1076_, v_as_x27_1077_, v_b_1078_, v_a_1079_);
lean_dec(v_as_x27_1077_);
lean_dec(v_as_1076_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__4(uint8_t v_verbose_1082_, uint8_t v_silent_1083_, lean_object* v_as_1084_, lean_object* v_as_x27_1085_, lean_object* v_b_1086_, lean_object* v_a_1087_){
_start:
{
lean_object* v___x_1089_; 
v___x_1089_ = l_List_forIn_x27_loop___at___00checkOlean_spec__4___redArg(v_verbose_1082_, v_silent_1083_, v_as_x27_1085_, v_b_1086_);
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00checkOlean_spec__4___boxed(lean_object* v_verbose_1090_, lean_object* v_silent_1091_, lean_object* v_as_1092_, lean_object* v_as_x27_1093_, lean_object* v_b_1094_, lean_object* v_a_1095_, lean_object* v___y_1096_){
_start:
{
uint8_t v_verbose_boxed_1097_; uint8_t v_silent_boxed_1098_; lean_object* v_res_1099_; 
v_verbose_boxed_1097_ = lean_unbox(v_verbose_1090_);
v_silent_boxed_1098_ = lean_unbox(v_silent_1091_);
v_res_1099_ = l_List_forIn_x27_loop___at___00checkOlean_spec__4(v_verbose_boxed_1097_, v_silent_boxed_1098_, v_as_1092_, v_as_x27_1093_, v_b_1094_, v_a_1095_);
lean_dec(v_as_x27_1093_);
lean_dec(v_as_1092_);
return v_res_1099_;
}
}
LEAN_EXPORT lean_object* l_List_partition_loop___at___00main_spec__0(lean_object* v_a_1101_, lean_object* v_a_1102_){
_start:
{
if (lean_obj_tag(v_a_1101_) == 0)
{
lean_object* v_fst_1103_; lean_object* v_snd_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1113_; 
v_fst_1103_ = lean_ctor_get(v_a_1102_, 0);
v_snd_1104_ = lean_ctor_get(v_a_1102_, 1);
v_isSharedCheck_1113_ = !lean_is_exclusive(v_a_1102_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1106_ = v_a_1102_;
v_isShared_1107_ = v_isSharedCheck_1113_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_snd_1104_);
lean_inc(v_fst_1103_);
lean_dec(v_a_1102_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1113_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1111_; 
v___x_1108_ = l_List_reverse___redArg(v_fst_1103_);
v___x_1109_ = l_List_reverse___redArg(v_snd_1104_);
if (v_isShared_1107_ == 0)
{
lean_ctor_set(v___x_1106_, 1, v___x_1109_);
lean_ctor_set(v___x_1106_, 0, v___x_1108_);
v___x_1111_ = v___x_1106_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v___x_1108_);
lean_ctor_set(v_reuseFailAlloc_1112_, 1, v___x_1109_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
}
else
{
lean_object* v_head_1114_; lean_object* v_tail_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1142_; 
v_head_1114_ = lean_ctor_get(v_a_1101_, 0);
v_tail_1115_ = lean_ctor_get(v_a_1101_, 1);
v_isSharedCheck_1142_ = !lean_is_exclusive(v_a_1101_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1117_ = v_a_1101_;
v_isShared_1118_ = v_isSharedCheck_1142_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_tail_1115_);
lean_inc(v_head_1114_);
lean_dec(v_a_1101_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1142_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v_fst_1119_; lean_object* v_snd_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1141_; 
v_fst_1119_ = lean_ctor_get(v_a_1102_, 0);
v_snd_1120_ = lean_ctor_get(v_a_1102_, 1);
v_isSharedCheck_1141_ = !lean_is_exclusive(v_a_1102_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1122_ = v_a_1102_;
v_isShared_1123_ = v_isSharedCheck_1141_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_snd_1120_);
lean_inc(v_fst_1119_);
lean_dec(v_a_1102_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1141_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; uint8_t v___x_1134_; 
v___x_1132_ = lean_string_utf8_byte_size(v_head_1114_);
v___x_1133_ = lean_unsigned_to_nat(1u);
v___x_1134_ = lean_nat_dec_le(v___x_1133_, v___x_1132_);
if (v___x_1134_ == 0)
{
goto v___jp_1124_;
}
else
{
lean_object* v___x_1135_; lean_object* v___x_1136_; uint8_t v___x_1137_; 
v___x_1135_ = ((lean_object*)(l_List_partition_loop___at___00main_spec__0___closed__0));
v___x_1136_ = lean_unsigned_to_nat(0u);
v___x_1137_ = lean_string_memcmp(v_head_1114_, v___x_1135_, v___x_1136_, v___x_1136_, v___x_1133_);
if (v___x_1137_ == 0)
{
goto v___jp_1124_;
}
else
{
lean_object* v___x_1138_; lean_object* v___x_1139_; 
lean_del_object(v___x_1122_);
lean_del_object(v___x_1117_);
v___x_1138_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1138_, 0, v_head_1114_);
lean_ctor_set(v___x_1138_, 1, v_fst_1119_);
v___x_1139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1138_);
lean_ctor_set(v___x_1139_, 1, v_snd_1120_);
v_a_1101_ = v_tail_1115_;
v_a_1102_ = v___x_1139_;
goto _start;
}
}
v___jp_1124_:
{
lean_object* v___x_1126_; 
if (v_isShared_1118_ == 0)
{
lean_ctor_set(v___x_1117_, 1, v_snd_1120_);
v___x_1126_ = v___x_1117_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_head_1114_);
lean_ctor_set(v_reuseFailAlloc_1131_, 1, v_snd_1120_);
v___x_1126_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
lean_object* v___x_1128_; 
if (v_isShared_1123_ == 0)
{
lean_ctor_set(v___x_1122_, 1, v___x_1126_);
v___x_1128_ = v___x_1122_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v_fst_1119_);
lean_ctor_set(v_reuseFailAlloc_1130_, 1, v___x_1126_);
v___x_1128_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
v_a_1101_ = v_tail_1115_;
v_a_1102_ = v___x_1128_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* _lean_main(lean_object* v_args_1150_){
_start:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v_fst_1154_; lean_object* v_snd_1155_; uint8_t v___y_1157_; lean_object* v___x_1163_; uint8_t v___x_1164_; 
v___x_1152_ = ((lean_object*)(l_main___closed__0));
v___x_1153_ = l_List_partition_loop___at___00main_spec__0(v_args_1150_, v___x_1152_);
v_fst_1154_ = lean_ctor_get(v___x_1153_, 0);
lean_inc(v_fst_1154_);
v_snd_1155_ = lean_ctor_get(v___x_1153_, 1);
lean_inc(v_snd_1155_);
lean_dec_ref(v___x_1153_);
v___x_1163_ = ((lean_object*)(l_main___closed__3));
v___x_1164_ = l_List_elem___at___00Lean_isAutoDeclOrPrivate__Internal_spec__0(v___x_1163_, v_fst_1154_);
if (v___x_1164_ == 0)
{
lean_object* v___x_1165_; uint8_t v___x_1166_; 
v___x_1165_ = ((lean_object*)(l_main___closed__4));
v___x_1166_ = l_List_elem___at___00Lean_isAutoDeclOrPrivate__Internal_spec__0(v___x_1165_, v_fst_1154_);
if (v___x_1166_ == 0)
{
lean_object* v___x_1167_; uint8_t v___x_1168_; 
v___x_1167_ = ((lean_object*)(l_main___closed__5));
v___x_1168_ = l_List_elem___at___00Lean_isAutoDeclOrPrivate__Internal_spec__0(v___x_1167_, v_fst_1154_);
v___y_1157_ = v___x_1168_;
goto v___jp_1156_;
}
else
{
v___y_1157_ = v___x_1166_;
goto v___jp_1156_;
}
}
else
{
lean_object* v___x_1169_; uint8_t v___x_1170_; lean_object* v___x_1171_; 
v___x_1169_ = ((lean_object*)(l_main___closed__2));
v___x_1170_ = l_List_elem___at___00Lean_isAutoDeclOrPrivate__Internal_spec__0(v___x_1169_, v_fst_1154_);
lean_dec(v_fst_1154_);
v___x_1171_ = l_checkExport(v_snd_1155_, v___x_1170_);
lean_dec(v_snd_1155_);
return v___x_1171_;
}
v___jp_1156_:
{
lean_object* v___x_1158_; uint8_t v___x_1159_; lean_object* v___x_1160_; uint8_t v___x_1161_; lean_object* v___x_1162_; 
v___x_1158_ = ((lean_object*)(l_main___closed__1));
v___x_1159_ = l_List_elem___at___00Lean_isAutoDeclOrPrivate__Internal_spec__0(v___x_1158_, v_fst_1154_);
v___x_1160_ = ((lean_object*)(l_main___closed__2));
v___x_1161_ = l_List_elem___at___00Lean_isAutoDeclOrPrivate__Internal_spec__0(v___x_1160_, v_fst_1154_);
lean_dec(v_fst_1154_);
v___x_1162_ = l_checkOlean(v_snd_1155_, v___x_1159_, v___y_1157_, v___x_1161_);
return v___x_1162_;
}
}
}
LEAN_EXPORT lean_object* l_main___boxed(lean_object* v_args_1172_, lean_object* v_a_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = _lean_main(v_args_1172_);
return v_res_1174_;
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
